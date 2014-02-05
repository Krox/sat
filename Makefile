
all : bin/sat
.PHONY : bin/sat # 'sat' is the actual filename, but make doesn't know its dependencies
bin/sat :
	rdmd --build-only -O -inline -g -debug -I../jive -ofbin/sat sat/main.d
