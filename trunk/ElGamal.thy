theory ElGamal
imports Hoare_Tactics Modules
begin

default_sort prog_type

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,power}" (* generator *)
  and q::nat (* group order *)
begin

moduletype DDH_Adv attach g where
  "guess" :: "('G*'G*'G*unit,bool) procedure"
moduletype DDH_Game attach g where
  "main" :: "('G*'G*'G*unit,bool) procedure"
end

abbreviation "x == LVariable ''x'' :: nat variable"
abbreviation "y == LVariable ''y'' :: nat variable "
abbreviation "z == LVariable ''z'' :: nat variable"
abbreviation "b == LVariable ''b'' :: bool variable"
abbreviation "pk == LVariable ''pk'' :: 'pk variable"
abbreviation "sk == LVariable ''sk'' :: 'sk variable"
abbreviation "m0 == LVariable ''m0'' :: 'm variable"
abbreviation "m1 == LVariable ''m1'' :: 'm variable"
abbreviation "b' == LVariable ''b_'' :: bool variable"
abbreviation "tmp == LVariable ''tmp''"

(*
record Adversary =
  Adv_guess :: "(G*G*G*unit,bool) procedure"

record DDH_Game =
  DDH_main :: "(unit,bool) procedure"
*)

(* Hack for typechecking to go through *)
definition (in group) "A_guess == undefined ::  ('G \<times> 'G \<times> 'G \<times> unit, bool) procedure"

definition (in group) "DDH0_main = 
  proc () {
    x <- uniform {0..<q};
    y <- uniform {0..<q};
    b := call A_guess (g^x, g^y, g^(x*y));
    return True
  }"

definition (in group) DDH0 :: module where
"DDH0 == Abs_module \<lparr> mr_module_args=[''A'' \<mapsto> DDH_Adv],
                   mr_procs=[[''main''] \<mapsto> mk_procedure_untyped DDH0_main] \<rparr>"

definition (in group) "DDH1_main = 
  proc () {
    x <- uniform {0..<q};
    y <- uniform {0..<q};
    z <- uniform {0..<q}; 
    b := call A_guess (g^x, g^y, g^z);
    return True 
  }"

definition (in group) DDH1 :: module where
"DDH1 == Abs_module \<lparr> mr_module_args=[''A'' \<mapsto> DDH_Adv],
                   mr_procs=[[''main''] \<mapsto> mk_procedure_untyped DDH1_main] \<rparr>"


locale encscheme =
  fixes stone :: "('pk::prog_type*'sk::prog_type*'m::prog_type*'c::prog_type)itself"
begin

moduletype EncScheme attach stone where
    kg :: "(unit,'pk*'sk) procedure"
and enc :: "('pk*'m*unit, 'c::prog_type) procedure"
and dec :: "('sk*'c::prog_type*unit, 'm) procedure"

moduletype CPA_Adv(S:EncScheme) where
     choose :: "('pk*unit,'m*'m) procedure"
and "guess" :: "('c*unit,bool) procedure"

end

term encscheme.EncScheme

(* Hack for typechecking to go through *)
definition (in encscheme) "A_choose == undefined :: ('pk*unit,'m*'m) procedure"
definition (in encscheme) "A_guess == undefined :: ('c*unit,bool) procedure"
definition (in encscheme) "S_kg == undefined :: (unit,'pk*'sk)procedure"
definition (in encscheme) "S_enc == undefined :: ('pk*'m*unit,'c)procedure"

abbreviation "c == LVariable ''c'' :: 'c variable"

definition (in encscheme) 
 "CPA_main = ignore stone (proc () { 
    tmp := call S_kg();
    pk := fst (tmp::'pk*'sk);
    sk := snd (tmp::'pk*'sk);
    tmp := call A_choose(pk);
    m0 := fst (tmp::'m*'m);
    m1 := snd (tmp::'m*'m);
    b <- uniform UNIV;
    c := call S_enc(pk, if b then m1 else m0);
    b' := call A_guess(c);
    return (b'=b)
  })"

definition (in encscheme) CPA :: module where
"CPA == ignore stone (Abs_module \<lparr> mr_module_args=[''A'' \<mapsto> CPA_Adv, ''S'' \<mapsto> EncScheme],
                   mr_procs=[[''main''] \<mapsto> mk_procedure_untyped CPA_main] \<rparr>)"

end
