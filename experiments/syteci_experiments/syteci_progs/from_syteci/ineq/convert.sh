#!/bin/bash

echo "" > results.txt

for d in */ ;
do

    f=${d/\//}
    cat $f/prog1.ml <(echo '|||') $f/prog2.ml > $f.bils
    
done
