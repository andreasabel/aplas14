# Makefile for contnorm

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { doi }' 
catcfg=sed -e "s/%.*//g" <
pdflatex=pdflatex
# pdflatex=xelatex
stdlib=$(HOME)/tmp/Agda2/std-lib/src

bibliography=all.bib
sedfile=postprocess.sed

stylefile=latex/agda.sty
files=byhand.bib intro.tex syntax.tex strongnormalization.tex soundnessproof.tex concl.tex SizedInfiniteTypes.tex Terms.tex Substitution.tex NReduction.tex sn.tex \
      TermShape.tex SN.tex IndRen.tex AntiRename.tex SAT.tex Soundness.tex SNtosn.tex \
  $(stylefile)

default : aplas14.pdf

all : default ship

ship : $(destdir)/aplas14.pdf  $(destdir)/aplas14.lagda 

$(destdir)/aplas14.pdf : aplas14.pdf
	cp -p $< $@

$(destdir)/aplas14.lagda : aplas14.lagda
	cp -p $< $@

pack : aplas14.zip

aplas14.zip : aplas14.tex aplas14.bbl latex/agda.sty textgreek.sty $(files) # auto-aplas14.bib byhand.bib eptcs.cls eptcs.bst
	zip $@ $^

# aplas14
##################################################################

%.tex : latex/%.tex $(sedfile)  
	sed --file=$(sedfile) < $< > $@

latex/%.tex : %.lagda
	agda --latex -i. -i$(stdlib) $<

# aplas14.pdf : aplas14.lagda
#	pdflatex $<

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
aplas14_aux : aplas14.tex $(files)
	-$(pdflatex) aplas14.tex;
	touch $@;

# then, run bibtex
aplas14.bbl : aplas14_aux auto-aplas14.bib 
	-bibtex aplas14;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
aplas14.pdf : aplas14.bbl
	-$(pdflatex) aplas14.tex;
	$(pdflatex) aplas14.tex;

# auto-aplas14.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-aplas14.bib : aplas14_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x aplas14.aux -i $(bibliography) >> $@;
endif
endif


# EOF
