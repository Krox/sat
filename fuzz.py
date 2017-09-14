#!/usr/bin/env python3
from subprocess import call

for i in range(0, 1000):
	print("fuzzing seed", i)
	cnfFile = open('tmp.cnf', 'w')
	logFile = open('tmp.log', 'w')

	#r = call(['../cnf-utils/cnf-fuzz-biere', str(i)], stdout=cnfFile)
	r = call(['../cnf-utils/cnf-fuzz-brummayer.py', '-s', str(i)], stdout=cnfFile)
	if r != 0: raise "fuzzer failed"
	cnfFile.close()

	r = call(['bin/sat', 'tmp.cnf', 'tmp.sol'])
	if r == 10:
		print("satisfiable")
		r = call(['bin/sat', '-c', 'tmp.cnf', 'tmp.sol'], stdout=logFile)
		if r == 0: print("checked")
		else: raise "INVALID SOLUTION"
	elif r == 20:
		print("unsat")
		r = call(['./cryptominisat', 'tmp.cnf'], stdout=logFile)
		if r == 20: print("checked")
		else: raise "INVALID UNSAT"
	else: raise "INVALID RETURN VALUE"
