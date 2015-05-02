HEAPS = /home/unruh/.isabelle/Isabelle2014/heaps/polyml-5.5.2_x86-linux
BROWSER_INFO = /home/unruh/.isabelle/Isabelle2014/browser_info/Unsorted/EasyCrypt
HEAP = $(HEAPS)/EasyCrypt

def :
	error

heap $(HEAP) : ROOT *.thy 
	/opt/Isabelle/bin/isabelle build -b -d . EasyCrypt 
	ls -lh $(BROWSER_INFO)/document.pdf

HOL-EC-Prereqs : ROOT
	/opt/Isabelle/bin/isabelle build -b -d . HOL-EC-Prereqs


HOL-EC-Core : ROOT
	/opt/Isabelle/bin/isabelle build -b -d . HOL-EC-Core

theories.pdf session.graph: ROOT *.thy *.tex
	/opt/Isabelle/bin/isabelle build -d . EasyCrypt
	ls -lh $(BROWSER_INFO)/document.pdf
	cp $(BROWSER_INFO)/document.pdf theories.pdf
	cp $(BROWSER_INFO)/session.graph .

ROOT: *.thy Makefile
	perl -i~ -p -e 'if (/theories\s*\(\*EC_THYS\*\)/) { $$_ = "  theories (*EC_THYS*) ".join(" ",grep { $$_ ne "Example" && $$_ ne "Tmp_Print_Sorry" && $$_ ne "Scratch" } map { s/\.thy$$//; $$_ } <*.thy>)."\n" }' ROOT

graph: session.graph
	/opt/Isabelle/bin/isabelle browser session.graph 

testsuite.py : tests.py tests/*.thy
	python tests.py

test: testsuite.py tests.py
	cricket-unittest &

get_eisbach :
	hg clone https://bitbucket.org/makarius/method_definition eisbach
