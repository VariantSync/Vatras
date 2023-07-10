#!/bin/bash
names=("Paul" "Bittner" "Alex" "Schult" "Jeff" "Young" "Parisa" "Ataei" "Eric" "Walking" "Martin" "Erwig" "Leo" "Teixeira" "Thomas" "Thüm" "VariantSync" "Ulm" "OSU" "Oregon" "GPCE")
for name in "${names[@]}";
do
  # -I ignores binary files
  grep -r -n -I \
    --exclude-dir=_build \
    --exclude-dir=.git \
    --exclude-dir=agda-stdlib \
    --exclude=check-anonymity.sh \
    $name
done

