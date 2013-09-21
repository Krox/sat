
modules = main jive/array sat solver clause
objs = $(patsubst %, obj/%.o, $(modules))
source = $(patsubst %, %.d, $(modules))

all : bin/sat
cleanall: clean

obj/%.o : %.d
	dmd -g -O -debug -c -of$@ $<
	#dmd -O -g -release -c -of$@ $<

bin/sat : $(objs)
	g++ -o $@ $^ -lphobos2 -lpthread -lrt

clean :
	rm -fr obj/* bin/*

