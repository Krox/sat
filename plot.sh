#!/bin/bash

filename=`tempfile`
first=1
for f in *.timing
do
	if [ $first -eq 1 ]
	then
		first=0
		echo plot \"$f\" using 1 title \"$f\" >> $filename
	else
		echo replot \"$f\" using 1 title \"$f\" >> $filename
	fi
done

cat $filename | gnuplot -p
