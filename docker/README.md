## Examples:

Test whether the heap `IsaCrypt` in the present directory (a ROOT file is needed) builds correctly, using precompiled logic HOL:
```
./docker-runx unruh/isabelle:hol isabelle build -d . IsaCrypt
```

Run the Isabelle jEdit GUI (on the theory Test.thy in the current directory), using logic HOL-Multivariate_Analysis:
```
./docker-runx unruh/isabelle:multivariate isabelle jedit Test.thy
```
This only works under X11 (assuming a standard location for the .Xauthority file)

