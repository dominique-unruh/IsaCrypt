# sudo apt-get install idle-python2.7 
# sudo pip install Pyro4 cricket  

HEAPS = /home/unruh/.isabelle/Isabelle2014/heaps/polyml-5.5.2_x86-linux
BROWSER_INFO = /home/unruh/.isabelle/Isabelle2014/browser_info/Unsorted/EasyCrypt
HEAP = $(HEAPS)/IsaCrypt

def :
	error

heap $(HEAP) : ROOT *.thy 
	/opt/Isabelle2015/bin/isabelle build -b -d . -v IsaCrypt
	ls -lh $(BROWSER_INFO)/document.pdf

IsaCrypt-Prereqs : ROOT
	/opt/Isabelle/bin/isabelle build -b -d . -v IsaCrypt-Prereqs


IsaCrypt-Core : ROOT
	/opt/Isabelle/bin/isabelle build -b -d . -v IsaCrypt-Core

theories.pdf session.graph: ROOT *.thy *.tex
	/opt/Isabelle/bin/isabelle build -d . -v EasyCrypt
	ls -lh $(BROWSER_INFO)/document.pdf
	cp $(BROWSER_INFO)/document.pdf theories.pdf
	cp $(BROWSER_INFO)/session.graph .

ROOT: *.thy Makefile
	perl -i~ -p -e 'if (/theories\s*\(\*ISACRYPT_THYS\*\)/) { $$_ = "  theories (*ISACRYPT_THYS*) ".join(" ",grep { $$_ ne "Example" && $$_ ne "Tmp_Print_Sorry" && $$_ ne "Scratch" && $$_ ne "Scratch2" && $$_ ne "Scratch3" } map { s/\.thy$$//; $$_ } <*.thy>)."\n" }' ROOT

graph: session.graph
	/opt/Isabelle/bin/isabelle browser session.graph 

testsuite.py : tests.py tests/*.thy
	python3 tests.py

test: testsuite.py tests.py
	cricket-unittest &

test_with_docker: testsuite.py tests.py
	ISABELLE_DOCKER=1 python3 testsuite.py dummy.test_succeed

test_shutdown :
	python tests.py ISABELLE_SERVER_SHUTDOWN

make-docker :
	cd misc/docker-prereqs/ && ./make-docker
