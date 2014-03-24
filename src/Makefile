stdlib=$(HOME)/tmp/Agda2/std-lib/src

typecheck : 
	agda -i. -i$(stdlib) Everything.agda +RTS -M1g 

profile :
	-rm -rf *.agdai 
	time agda -i. -i$(stdlib) -v profile:7 Everything.agda +RTS -M1g -s

debug : 
	agda -i. -i$(stdlib) -v term.matrices:40 Everything.agda +RTS -M1.5g

# EOF