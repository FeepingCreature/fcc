#!/bin/sh
PASS=0
FAIL=0
TOTAL=0
FAILSTR=""
export TESTSUITE="y"
for file in $(ls *.nt)
do
  TOTAL=$(($TOTAL + 1))
  fcc -run $file >/dev/null
  res=$?
  if [ "$res" -eq "0" ]
  then
    PASS=$(($PASS + 1))
    echo -n "."
  else
    FAIL=$(($FAIL + 1))
    FAILSTR="$FAILSTR $file";
    echo -n "!"
  fi
done
echo "Pass: $PASS / $TOTAL"
echo "Fail: $FAIL / $TOTAL $FAILSTR"
