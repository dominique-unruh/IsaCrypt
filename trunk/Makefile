
BROWSER_INFO = /home/unruh/.isabelle/Isabelle2014/browser_info/Unsorted/EasyCrypt

session : ROOT *.thy 
	/opt/Isabelle/bin/isabelle build -b -d . -v EasyCrypt 
	ls -lh $(BROWSER_INFO)/document.pdf

theories.pdf session.graph: ROOT *.thy *.tex
	/opt/Isabelle/bin/isabelle build -d . -v EasyCrypt
	ls -lh $(BROWSER_INFO)/document.pdf
	cp $(BROWSER_INFO)/document.pdf theories.pdf
	cp $(BROWSER_INFO)/session.graph .

ROOT: *.thy Makefile
	perl -i~ -p -e 'if (/theories/ && !/document/) { $$_ = "  theories ".join(" ",grep { $$_ ne "Example" } map { s/\.thy$$//; $$_ } <*.thy>)."\n" }' ROOT

graph: session.graph
	/opt/Isabelle/bin/isabelle browser session.graph 
