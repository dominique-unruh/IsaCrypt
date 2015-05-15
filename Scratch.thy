theory Scratch
imports Main
begin

definition "f = (%x::'a set. x)"
definition "g == undefined::('a*'a) set"

(*typedef 'a iset = "UNIV::'a set" by auto*)
typedecl 'a iset

bnf "'a set"
  map: "%f (s::'a set). (f`s::' set)"
  bd: natLeq
  wits: "{}"
sorry

bnf "'a iset" map: "(%x::'a iset. x)" bd: "undefined::(nat*nat) set"
sorry

  unfolding f_def apply auto
  unfolding Grp_def apply auto
  unfolding g_def
sorry
  using natLeq_cinfinite apply auto
  using natLeq_card_order apply auto
  done

codatatype 'a test = A "'a set" | B "'a test set"
print_theorems!
term Rep_test
typ "int lazy_sequence"

end
