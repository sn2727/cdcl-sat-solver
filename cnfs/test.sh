#!/bin/sh

solver="babysat"

if [ ! -x $solver ]
then
  echo "test.sh: error: could not find '$solver'"
  exit 1
fi

run () {
  expected=$1
  name=cnfs/$2
  log=$name.log
  err=$name.err
  cnf=$name.cnf
  rm -f $log $err
  cmd="./$solver $cnf"
  echo $cmd
  $cmd 1>$log 2>$err
  status=$?
  if [ ! "$status" = "$expected" ]
  then
    echo "test.sh: error: '$cmd' exit status '$status' (expected '$expected')"
    exit 1
  fi
}

run 20 false
run 10 true

run 10 unit1
run 10 unit2
run 10 unit3
run 10 unit4
run 20 unit5
run 20 unit6
run 10 unit7
run 20 unit8
run 20 unit9

run 20 full1
run 20 full2
run 20 full3
run 20 full4

run 20 add4
run 20 add8

run 10 prime4
run 10 prime9
run 10 prime25
run 10 prime49
run 10 prime121
run 10 prime169
run 10 prime289
run 10 prime361
run 10 prime529
run 10 prime841
run 10 prime961
run 10 prime1849
run 10 prime1369
run 10 prime1681
run 10 prime2209

#run 20 add16
#run 20 add32
#run 20 add64
#run 20 add128

run 20 prime65537

# This is a harder one
#
#run 20 prime4294967297
