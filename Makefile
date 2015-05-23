
all : bin/sat
.PHONY : bin/sat # 'sat' is the actual filename, but make doesn't know its dependencies
bin/sat :
	rdmd -O3 --oq --compiler=ldc2 --build-only -I../jive -ofbin/sat sat/main.d
