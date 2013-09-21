#!/bin/bash

#list=`find ./sat-2002-beta/generated/gen-1/ -type f`
list=`find ./sat-2002-beta/generated/gen-1/gen-1.[1-5] -type f`
#list=`find ./sat-2002-beta/submitted -type f`

solver="bin/sat"


tmp=`tempfile`
timeTmp=`tempfile`

echo "0.0" > $tmp

for file in $list
do
	timeout 1s /usr/bin/time -f "%U" -o $timeTmp $solver $file  #2>&1
	if [ $? -eq 0 ]
	then
	   cat $timeTmp >> $tmp
	fi
done

timing_filename=`date +%F_%R.timing`
sort < $tmp > $timing_filename
rm $tmp
rm $timeTmp

echo timing saved as $timing_filename

./plot.sh
