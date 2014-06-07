stdlib=$(HOME)/tmp/Agda2/std-lib/src
dest=$(HOME)/public_html/guarded-normalization

publish :
	time agda -i. -i$(stdlib) --html --html-dir=$(dest) Everything.agda +RTS -M1.5g -s -RTS 

typecheck : 
	agda -i. -i$(stdlib) Everything.agda +RTS -M1g 

profile :
	-rm -rf *.agdai 
	time agda -i. -i$(stdlib) -v profile:7 Everything.agda +RTS -M1g -s

debug : 
	agda -i. -i$(stdlib) -v term.matrices:40 Everything.agda +RTS -M1.5g

# EOF