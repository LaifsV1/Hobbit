#!/bin/bash

TIMEFORMAT=%R

echo "" > results.txt

for d in */ ;
do

    echo $d >> results.txt
    
    (time timeout 5s ./syteci -chc $d/prog1.ml $d/prog2.ml | timeout 5s z3 -in) >> results.txt 2>&1
    echo "*********" >> results.txt
    
done
