
all : bin/sat
.PHONY : bin/sat # 'sat' is the actual filename, but make doesn't know its dependencies
bin/sat :
	rdmd -O3 --oq --build-only -I../jive -I../math -I../algo -ofbin/sat sat/main.d
