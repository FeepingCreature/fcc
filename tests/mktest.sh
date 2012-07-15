#!/bin/sh
COUNT=1
while [ -e "test$COUNT.nt" -o -e "test${COUNT}fail.nt" ]; do COUNT=$((COUNT+1)); done
FILE="test$COUNT.nt"
echo "module test$COUNT;

void main() {
}" > $FILE
joe $FILE
fcc -run $FILE
