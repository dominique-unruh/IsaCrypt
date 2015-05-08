theory ElGamal
imports Hoare_Tactics Procs_Typed
begin

default_sort prog_type

(* TODO: get ride of these *)
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
abbreviation "c == LVariable ''c'' :: 'c variable"

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,power,prog_type}" (* generator *)
  and q::nat (* group order *)
begin

type_synonym 'g DDH_Adv = "('g*'g*'g*unit,bool) procedure"
type_synonym 'g DDH_Game = "(unit,bool) procedure"


definition_by_specification DDH0 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "procfun_apply DDH0 A = 
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      b := call A (g^x, g^y, g^(x*y));
      return True
    }"

definition_by_specification DDH1 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "procfun_apply DDH1 A = 
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      z <- uniform {0..<q};
      b := call A (g^x, g^y, g^z);
      return True
    }"
end

(* (keygen,enc,dec) *)
type_synonym ('pk,'sk,'m,'c) EncScheme = 
 "(unit,'pk*'sk) procedure *
  ('pk*'m*unit, 'c) procedure *
  ('sk*'c*unit, 'm) procedure"


(* (choose,guess) *)
type_synonym ('pk,'sk,'m,'c) CPA_Adv = 
 "('pk*unit,'m*'m) procedure *
  ('c*unit,bool) procedure"

type_synonym CPA_Game = "(unit,bool)procedure"

definition_by_specification CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> CPA_Game" where
 "procfun_apply CPA_main ((kg,enc,dec),(Achoose,Aguess)) = 
  proc () { 
    tmp := call kg();
    pk := fst (tmp::'pk*'sk);
    sk := snd (tmp::'pk*'sk);
    tmp := call Achoose(pk);
    m0 := fst (tmp::'m*'m);
    m1 := snd (tmp::'m*'m);
    b <- uniform UNIV;
    c := call enc(pk, if b then m1 else m0);
    b' := call Aguess(c);
    return (b'=b)
  }"

end
