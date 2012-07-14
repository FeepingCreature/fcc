#!/bin/sh
PASS=0
FAIL=0
TOTAL=0
FAILSTR=""
export TESTSUITE="y"
for file in $(ls *.nt)
do
  TOTAL=$(($TOTAL + 1))
  set +m
  exec 3>&2
  exec 2>/dev/null
  fcc -run $file >/dev/null
  res=$?
  exec 2>&3
  exec 3>&-
  if [ "$res" -ne "0" ]; then res=1; fi # normalize
  expectfail=0
  if [[ "$file" == *fail* ]]; then expectfail=1; fi
  let res=$res^$expectfail;
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
echo
echo "Pass: $PASS / $TOTAL"
echo "Fail: $FAIL / $TOTAL $FAILSTR"
