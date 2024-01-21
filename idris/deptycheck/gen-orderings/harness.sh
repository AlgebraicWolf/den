#!/usr/bin/env bash

GEN_TIMEOUT=60

fuel=1
rc=0

echo "fuel,len,expr,time"

while [[ $rc -eq true ]]; do
  out=$(timeout "$GEN_TIMEOUT" gtime -f ",%e" build/exec/gen-orderings "$fuel" 2>&1)
  rc=$?

  if [[ $rc -eq true ]]; then
    echo "$fuel,$out"
  fi

  fuel=$(($fuel + 1))
done
