// clang-format off

const char *usage =
"usage: cdcl-sat [ <option> ... ] [ <dimacs> ]\n"
"\n"
"where '<option>' can be one of the following\n"
"\n"
"  -h | --help        print this command line option summary\n"
#ifdef LOGGING
"  -l | --logging     print very verbose logging information\n"
#endif
"  -q | --quiet       do not print any messages\n"
"  -n | --no-witness  do not print witness if satisfiable\n"
"  -v | --verbose     print verbose messages\n"
"\n"
"  -c <limit>         set conflict limit\n"
"\n"
"and '<dimacs>' is the input file in DIMACS format.  The solver\n"
"reads from '<stdin>' if no input file is specified.\n";

// clang-format on

#include <algorithm>
#include <cassert>
#include <climits>
#include <csignal>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

// Linux/Unix system specific.

#include <sys/resource.h>
#include <sys/time.h>

// Global options accessible through the command line.

static bool witness = true;

static int verbosity; // -1=quiet, 0=normal, 1=verbose, INT_MAX=logging

// Clause data structure.

struct Clause {
  //#ifndef NDEBUG
  size_t id; // For debugging.
             //#endif
  unsigned size;
  int literals[];

  // The following two functions allow simple ranged-based for-loop
  // iteration over Clause literals with the following idiom:
  //
  //   Clause *c = ...
  //   for (auto lit : *c)
  //     do_something_with (lit);
  //
  int *begin() { return literals; }
  int *end() { return literals + size; }
};

static int variables;       // Variable range: 1 .. <variables>.
static signed char *values; // Assignment 0=unassigned, -1=false, 1=true.
static unsigned *levels;    // Maps variables to their level.
static Clause **reasons;    // Reasons of forced assignments.

static std::vector<int> analyzed; // Variables analyzed and thus stamped.
static size_t *stamped;           // Maps variables to used time stamps.

static std::vector<Clause *> clauses;
static std::vector<Clause *> *matrix;

static Clause *empty_clause; // Empty clause found.

// Using a fixed size trail makes propagation and backtracking faster.

static int *trail;      // The start of the assigned literals.
static int *assigned;   // The end of the assigned literals.
static int *propagated; // The end of the propagated literals.

static std::vector<int *> control;

static unsigned level; // Decision level.

// Conflict limit.

static size_t limit = -1; // Extends to 'MAX_SIZE_T' ('size_t' unsigned).

// Statistics:

static size_t added;        // Number of added clauses.
static size_t conflicts;    // Number of conflicts.
static size_t backjumps;    // Number of backjumped levels.
static size_t decisions;    // Number of decisions.
static size_t propagations; // Number of propagated literals.
static size_t reports;      // Number of calls to 'report'.
static int fixed;           // Number of root-level assigned variables.

// Get process-time of this process.  This is not portable to Windows but
// should work on other Unixes such as MacOS as is.

static double process_time(void) {
  struct rusage u;
  double res;
  if (getrusage(RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

// Report progress once in a while.

static void report(char type) {
  if (verbosity < 0)
    return;
  if (!(reports++ % 20))
    printf("c\n"
           "c              decisions              variables\n"
           "c   seconds                 conflicts           remaining\n"
           "c\n");
  int remaining = variables - fixed;
  printf("c %c %7.2f %12zu %12zu %9d %3.0f%%\n", type, process_time(),
         decisions, conflicts, remaining,
         variables ? 100.0 * remaining / variables : 0);
  fflush(stdout);
}

// Generates nice compiler warnings if format string does not fit arguments.

static void message(const char *, ...) __attribute__((format(printf, 1, 2)));
static void die(const char *, ...) __attribute__((format(printf, 1, 2)));

static void parse_error(const char *fmt, ...)
    __attribute__((format(printf, 1, 2)));

#ifdef LOGGING

static void debug(const char *, ...) __attribute__((format(printf, 1, 2)));

static void debug(Clause *, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static bool logging() { return verbosity == INT_MAX; }

// Print debugging message if '--debug' is used.  This is only enabled
// if the solver is configured with './configure --logging' (which is the
// default for './configure --debug').  Even if logging code is included
// this way, it still needs to be enabled at run-time through '-l'.

static char debug_buffer[4][32];
static size_t next_debug_buffer;

// Get a statically allocate string buffer.
// Used here only for printing literals.

static char *debug_string(void) {
  char *res = debug_buffer[next_debug_buffer++];
  if (next_debug_buffer == sizeof debug_buffer / sizeof *debug_buffer)
    next_debug_buffer = 0;
  return res;
}

static char *debug(int lit) {
  if (!logging())
    return 0;
  char *res = debug_string();
  sprintf(res, "%d", lit);
  int value = values[lit];
  if (value) {
    size_t len = strlen(res);
    size_t remaining = sizeof debug_buffer[0] - len;
    snprintf(res + len, remaining, "@%u=%d", levels[abs(lit)], value);
  }
  assert(strlen(res) <= sizeof debug_buffer[0]);
  return res;
}

static void debug_prefix(void) { printf("c DEBUG %u ", level); }

static void debug_suffix(void) {
  fputc('\n', stdout);
  fflush(stdout);
}

static void debug(const char *fmt, ...) {
  if (!logging())
    return;
  debug_prefix();
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  debug_suffix();
}

static void debug(Clause *c, const char *fmt, ...) {
  if (!logging())
    return;
  debug_prefix();
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  printf(" size %u clause[%zu]", c->size, c->id);
  for (auto lit : *c)
    printf(" %s", debug(lit));
  debug_suffix();
}

#else

#define debug(...)                                                             \
  do {                                                                         \
  } while (0)

#endif

// Print message to '<stdout>' and flush it.

static void message(const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static void line() {
  if (verbosity < 0)
    return;
  fputs("c\n", stdout);
  fflush(stdout);
}

static void verbose(const char *fmt, ...) {
  if (verbosity <= 0)
    return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

// Print error message and 'die'.

static void die(const char *fmt, ...) {
  fprintf(stderr, "cdcl-sat: error: ");
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void initialize(void) {
  assert(variables < INT_MAX);
  unsigned size = variables + 1;

  unsigned twice = 2 * size;

  values = new signed char[twice]();
  matrix = new std::vector<Clause *>[twice];

  levels = new unsigned[size];
  stamped = new size_t[size]();
  reasons = new Clause *[size];

  // We subtract 'variables' in order to be able to access
  // the arrays with a negative index (valid in C/C++).

  matrix += variables;
  values += variables;

  propagated = assigned = trail = new int[size];

  assert(!level);
}

static void delete_clause(Clause *c) {
  debug(c, "delete");
  delete[] c;
}

static void release(void) {
  for (auto c : clauses)
    delete_clause(c);

  delete[] trail;

  matrix -= variables;
  values -= variables;

  delete[] matrix;
  delete[] values;

  delete[] levels;
  delete[] stamped;
}

static bool satisfied(Clause *c) {
  for (auto lit : *c)
    if (values[lit] > 0)
      return true;
  return false;
}

static bool satisfied() {
  assert(propagated == assigned);
  return assigned - trail == variables;
}

// after values[lit] == -1:
static void fixWatch(int lit) {
  // get all clauses with our now false lit
  const auto &occurrences = matrix[lit];
  for (auto c : occurrences) {
    // only two lits, can't swap anything:
    if (c->size < 3)
      continue;
    // get index of lit in c
    int index = 0;
    for (auto l : *c) {
      if (l == (lit))
        break;
      index++;
    }
    // literal is not watched:
    if (index > 1)
      continue;
    // else it is watched, swap if possible:
    int nonFalseIndex = -1;
    for (int i = 2; i < c->size; i++) {
      if (values[c->literals[i]] > -1) {
        nonFalseIndex = i;
        break;
      }
    }
    if (nonFalseIndex > -1) {
      c->literals[index] = c->literals[nonFalseIndex];
      c->literals[nonFalseIndex] = (lit);
    }
  }
}

static void assign(int lit, Clause *reason) {
  debug("assign %s", debug(lit));
  assert(lit);
  assert(!values[lit]);
  assert(!values[-lit]);
  values[lit] = 1;
  values[-lit] = -1;
  int idx = abs(lit);
  levels[idx] = level;
  reasons[idx] = reason;
  *assigned++ = lit;
  // fix clauses for watches - move false literals away if possible
  fixWatch(-lit);
  if (!level)
    fixed++;
}

static void connect_literal(int lit, Clause *c) {
  debug(c, "connecting %s to", debug(lit));
  matrix[lit].push_back(c);
}

static Clause *add_clause(std::vector<int> &literals) {
  size_t size = literals.size();
  size_t bytes = sizeof(struct Clause) + size * sizeof(int);
  Clause *c = (Clause *)new char[bytes];

  assert(size <= UINT_MAX);
#ifndef NDEBUG
  c->id = added;
#endif
  added++;

  c->size = size;

  int *q = c->literals;
  for (auto lit : literals)
    *q++ = lit;

  debug(c, "new");

  clauses.push_back(c); // Save it on global stack of clauses.

  // Connect the literals of the clause in the matrix.

  for (auto lit : *c)
    connect_literal(lit, c);

  // Handle the special case of empty and unit clauses.

  if (!size) {
    debug(c, "parsed empty clause");
    empty_clause = c;
  } else if (size == 1) {
    int unit = literals[0];
    signed char value = values[unit];
    if (!value)
      assign(unit, 0);
    else if (value < 0) {
      debug(c, "inconsistent unit clause");
      empty_clause = c;
    }
  }

  return c;
}

static const char *file_name;
static bool close_file;
static FILE *file;

static void parse_error(const char *fmt, ...) {
  fprintf(stderr, "cdcl-sat: parse error in '%s': ", file_name);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void parse(void) {
  int ch;
  while ((ch = getc(file)) == 'c') {
    while ((ch = getc(file)) != '\n')
      if (ch == EOF)
        parse_error("end-of-file in comment");
  }
  if (ch != 'p')
    parse_error("expected 'c' or 'p'");
  int clauses;
  if (fscanf(file, " cnf %d %d", &variables, &clauses) != 2 || variables < 0 ||
      variables >= INT_MAX || clauses < 0 || clauses >= INT_MAX)
    parse_error("invalid header");
  message("parsed header 'p cnf %d %d'", variables, clauses);
  initialize();
  std::vector<int> clause;
  int lit = 0, parsed = 0;
  size_t literals = 0;
  while (fscanf(file, "%d", &lit) == 1) {
    if (parsed == clauses)
      parse_error("too many clauses");
    if (lit == INT_MIN || abs(lit) > variables)
      parse_error("invalid literal '%d'", lit);
    if (lit) {
      clause.push_back(lit);
      literals++;
    } else {
      add_clause(clause);
      clause.clear();
      parsed++;
    }
  }
  if (lit)
    parse_error("terminating zero missing");
  if (parsed != clauses)
    parse_error("clause missing");
  if (close_file)
    fclose(file);
  verbose("parsed %zu literals in %d clauses", literals, parsed);
}

// Return 'false' if propagation detects an empty clause otherwise if it
// completes propagating all literals since the last time it was called
// without finding an empty clause it returns 'true'.  Beside finding
// conflicts propagating a literal also detects unit clauses and
// then assign the forced literal by that unit clause.

static Clause *propagate(void) {
  while (propagated != assigned) {
    propagations++;
    int lit = *propagated++;
    debug("propagating %d", lit);
    const auto &occurrences = matrix[-lit];

    // First two literals of each clause are watched
    for (auto c : occurrences) {
      int watch1 = c->literals[0];
      int watch2 = watch1;
      if (c->size > 1) {
        watch2 = c->literals[1];
      }
      // if both are false we have a conflict
      if (values[watch1] < 0 && values[watch2] < 0) {
        conflicts++;
        return c;
      }
      // if one is true we can continue with the next clause
      if (values[watch1] > 0 || values[watch2] > 0) {
        continue;
      }
      // if one is false we have the forcing case
      if (values[watch1] < 0 != values[watch2] < 0) {
        int unit = watch1;
        if (values[watch1] < 0)
          unit = watch2;
        assign(unit, c);
      }
      // else the watched literals are both non-false and we continue with the
      // next clause
    }
  }
  return 0;
}

static bool is_power_of_two(size_t n) { return n && !(n & (n - 1)); }

static int searched = 1;

static void decide(void) {
  decisions++;
  while (assert(searched <= variables), values[searched])
    searched++;
  level++;
  debug("decide %d", searched);
  control.push_back(assigned);
  stamped[searched] = 0;
  assign(searched, 0);
  if (is_power_of_two(decisions))
    report('d');
}

static void unassign(int lit) {
  debug("unassign %s", debug(lit));
  assert(lit);
  assert(values[lit] == 1);
  assert(values[-lit] == -1);
  values[lit] = values[-lit] = 0;
  int tmp = abs(lit);
  if (tmp < searched)
    searched = tmp;
}

static void backtrack(unsigned new_level) {
  assert(new_level < level);
  int *before = control[new_level];
  while (assigned != before)
    unassign(*--assigned);
  control.resize(new_level);
  propagated = before;
  level = new_level;
}

static void analyze_literal(int lit, int &current, int &lower) {
  int idx = abs(lit);
  assert(values[lit]);
  unsigned int lvl = levels[idx];

  // analyzed or root level decision
  if (!lvl || stamped[idx] == conflicts)
    return;

  debug("analyzing literal %s", debug(lit));
  assert(values[lit] < 0);

  // stamp literal
  stamped[idx] = conflicts;

  if (lvl == level)
    // increment count of stamped literals on current level
    current++;
  else
    // increment count of stamped literals on lower level
    lower++;
}

static void analyze(Clause *c) {
  debug(c, "analyzing conflict %zu", conflicts);

  // the learned clause
  std::vector<int> learned;
  // the backjump level
  unsigned backjump = 0;
  // trail traversal pointer
  int *copy = assigned - 1;

  // counts stamped on current level
  int current = 0;
  // counts stamped literals on lower level
  int lower = 0;

  for (auto lit : *c)
    analyze_literal(lit, current, lower);

  // go over stamped literals on current level
  // by traversing trail
  // until one is left (the uip)
  while (current > 1) {
    int lit = *copy--;
    unsigned idx = abs(lit);

    if (stamped[idx] == conflicts) {
      // recurse if reason is non null
      Clause *reason = reasons[idx];

      if (reason)
        for (auto lit : *reason)
          analyze_literal(lit, current, lower);

      // decrement count
      current--;
    }
  }

  // skip non stamped literals on current level
  while (stamped[abs(*copy)] != conflicts)
    copy--;

  // the last one is uip
  int uip = *copy--;

  // go over stamped literals on lower level
  while (lower) {
    int lit = *copy--;
    unsigned idx = abs(lit);

    if (stamped[idx] == conflicts) {
      // add to learned clause
      learned.push_back(-lit);

      // update backjump level
      unsigned lvl = levels[idx];
      if (lvl > backjump)
        backjump = lvl;

      // decrement counter
      lower--;
    }
  }

  // Simple minimization
  for (auto lit : learned) {
    unsigned idx = abs(lit);
    Clause *reason = reasons[idx];
    if (reason) {
      bool minimize = true;
      for (auto other : *reason) {
        if (idx != abs(other)) {
          if (std::find(learned.begin(), learned.end(), other) ==
              learned.end()) {
            minimize = false;
            break;
          }
        }
      }
      if (minimize)
        learned.erase(std::remove(learned.begin(), learned.end(), lit),
                      learned.end());
    }
  }

  // add the uip to the clause
  learned.push_back(-uip);

  // backjump
  backtrack(backjump);

  // add learned clause if it is not unit clause
  if (learned.size() > 1) {
    Clause *clause = add_clause(learned);
    debug(clause, "learned clause");
    assign(-uip, clause);
  } else
    assign(-uip, 0);

  // increment only for actual backjumps
  if (backjump < level - 1)
    backjumps++;
}

// The SAT competition standardized exit codes (the 'exit (code)' or 'return
// res' in 'main').  All other exit codes denote unsolved or error.

static const int unknown = 0;        // Unsolved exit code.
static const int satisfiable = 10;   // Exit code for satisfiable and
static const int unsatisfiable = 20; // unsatisfiable formulas.

// if conflicts reach the restartLimit we restart
// after that the limit is multiplied by the factor following a geometric
// sequence
static int restartLimit = 10;
static const int factor = 2;

static int solve(void) {
  if (empty_clause)
    return unsatisfiable;
  for (;;) {
    Clause *conflict = propagate();
    if (conflict) {
      if (!level)
        return unsatisfiable;
      if (conflicts >= restartLimit) {
        // If conflicts reach restart limit we backtrack to level 0 and increase
        // the limit
        restartLimit *= factor;
        backtrack(0);
      } else
        analyze(conflict);
    } else if (satisfied())
      return satisfiable;
    else if (conflicts >= limit)
      return unknown;
    else
      decide();
  }
}

// Checking the model on the original formula is extremely useful for
// testing and debugging.  This 'checker' aborts if an unsatisfied clause is
// found and prints the clause on '<stderr>' for debugging purposes.

static void check_model(void) {
  debug("checking model");
  for (auto c : clauses) {
    if (satisfied(c))
      continue;
    fputs("cdcl-sat: unsatisfied clause:\n", stderr);
    for (auto lit : *c)
      fprintf(stderr, "%d ", lit);
    fputs("0\n", stderr);
    fflush(stderr);
    abort();
    exit(1);
  }
}

// Printing the model in the format of the SAT competition, e.g.,
//
//   v -1 2 3 0
//
// Always prints a full assignments even if not all values are set.

static void print_model(void) {
  printf("v ");
  for (int idx = 1; idx <= variables; idx++) {
    if (values[idx] < 0)
      printf("-");
    printf("%d ", idx);
  }
  printf("0\n");
}

static double average(double a, double b) { return b ? a / b : 0; }
static double percent(double a, double b) { return average(100 * a, b); }

// The main function expects at most one argument which is then considered
// as the path to a DIMACS file. Without argument the solver reads from
// '<stdin>' (the standard input connected for instance to the terminal).

static void print_statistics() {
  if (verbosity < 0)
    return;
  printf("c\n");
  double t = process_time();
  printf("c %-15s %16zu %12.2f per second\n", "conflicts:", conflicts,
         average(conflicts, t));
  printf("c %-15s %16zu %12.2f per second\n", "decisions:", decisions,
         average(decisions, t));
  printf("c %-15s %16zu %12.2f %% conflicts\n", "backjumps:", backjumps,
         percent(backjumps, conflicts));
  printf("c %-15s %16zu %12.2f million per second\n",
         "propagations:", propagations, average(propagations * 1e-6, t));
  printf("c\n");
  printf("c %-15s %16.2f seconds\n", "process-time:", t);
  printf("c\n");
}

// We have global signal handlers for printing statistics even if
// interrupted or some other error occurs.

static volatile int caught_signal;

struct {
  int sig;
  void (*saved)(int);
} handler[] = {{SIGABRT, 0}, {SIGINT, 0}, {SIGSEGV, 0}, {SIGTERM, 0}};

static const size_t size_handlers = sizeof handler / sizeof *handler;

static void reset_signal_handlers() {
  for (size_t i = 0; i != size_handlers; i++)
    signal(handler[i].sig, handler[i].saved);
}

static void catch_signal(int sig) {
  if (caught_signal)
    return;
  reset_signal_handlers();
  caught_signal = sig;
  line();
  message("caught signal %d", sig);
  print_statistics();
  message("raising signal %d", sig);
  raise(sig);
}

static void set_signal_handlers() {
  for (size_t i = 0; i != size_handlers; i++)
    handler[i].saved = signal(handler[i].sig, catch_signal);
}

#include "config.hpp"

int main(int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h") || !strcmp(arg, "--help")) {
      fputs(usage, stdout);
      exit(0);
    } else if (!strcmp(arg, "-l") || !strcmp(arg, "--logging"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      die("compiled without logging code (use './configure --logging')");
#endif
    else if (!strcmp(arg, "-q") || !strcmp(arg, "--quiet"))
      verbosity = -1;
    else if (!strcmp(arg, "-v") || !strcmp(arg, "--verbose"))
      verbosity = 1;
    else if (!strcmp(arg, "-n") || !strcmp(arg, "--no-witness"))
      witness = false;
    else if (!strcmp(arg, "-c")) {
      if (++i == argc)
        die("argument to '-c' missing");
      limit = atol(argv[i]);
    } else if (arg[0] == '-')
      die("invalid option '%s' (try '-h')", arg);
    else if (file_name)
      die("too many arguments '%s' and '%s' (try '-h')", file_name, arg);
    else
      file_name = arg;
  }

  if (!file_name) {
    file_name = "<stdin>";
    assert(!close_file);
    file = stdin;
  } else if (!(file = fopen(file_name, "r")))
    die("could not open and read '%s'", file_name);
  else
    close_file = true;

  message("CDCL SAT Solver");
  line();
  message("Copyright (c) 2022-2023");
  message("Version %s %s", VERSION, GITID);
  message("Compiled with '%s'", BUILD);
  line();
  message("reading from '%s'", file_name);

  set_signal_handlers();

  parse();

  verbose("solving with conflict limit %zu", limit);

  report('*');
  int res = solve();
  report(res == 10 ? '1' : res == 20 ? '0' : '?');
  line();

  if (res == 10) {
    check_model();
    printf("s SATISFIABLE\n");
    if (witness)
      print_model();
  } else if (res == 20)
    printf("s UNSATISFIABLE\n");

  release();
  reset_signal_handlers();

  print_statistics();
  message("exit code %d", res);

  return res;
}
