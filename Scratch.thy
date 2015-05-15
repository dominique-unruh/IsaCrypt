theory Scratch
imports Main "~~/src/HOL/Library/FSet" Lazy_Sequence Universe
begin

definition "testpt (x::_::prog_type) = True"

codatatype 'a test = A "'a set" | B "'a test fset"
print_theorems!
term Rep_test
typ "int lazy_sequence"

end
