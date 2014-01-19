
all : bin/sat
.PHONY : bin/sat # 'sat' is the actual filename, but make doesn't know its dependencies
bin/sat :
	rdmd --build-only -O -g -debug -ofbin/sat sat/main.d
