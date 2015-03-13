theory ElGamal
imports Hoare_Tactics Modules
begin

type_synonym G = nat
consts g :: G
consts q :: nat
consts p :: nat

abbreviation "x == LVariable ''x'' :: nat variable"
abbreviation "y == LVariable ''y'' :: nat variable "
abbreviation "z == LVariable ''z'' :: nat variable"
abbreviation "b == LVariable ''b'' :: bool variable"
abbreviation "c == LVariable ''c'' :: nat variable"
abbreviation "pk == LVariable ''pk''"
abbreviation "sk == LVariable ''sk''"
abbreviation "m0 == LVariable ''m0''"
abbreviation "m1 == LVariable ''m1''"
abbreviation "b' == LVariable ''b_'' :: bool variable"
abbreviation "tmp == LVariable ''tmp''"

moduletype DDH_Adv where
  "guess" :: "(G*G*G*unit,bool) procedure"

record Adversary =
  Adv_guess :: "(G*G*G*unit,bool) procedure"

moduletype DDH_Game where
  "main" :: "(G*G*G*unit,bool) procedure"

record DDH_Game =
  DDH_main :: "(unit,bool) procedure"

definition "DDH0 A = (let
  main = proc () { x <- uniform {0..<q}; y <- uniform {0..<q}; b := call (Adv_guess A) (g^x mod p, g^y mod p, g^(x*y) mod p); return True }
in
  \<lparr> DDH_main=main \<rparr>)
"

definition "DDH1 A = (let
  main = proc () { x <- uniform {0..<q}; y <- uniform {0..<q}; z <- uniform {0..<q}; b := call (Adv_guess A) (g^x mod p, g^y mod p, g^z mod p); return True }
in
  \<lparr> DDH_main=main \<rparr>)
"

typedecl pk
typedecl sk
typedecl m
typedecl c

moduletype EncScheme where
    kg :: "(unit,pk*sk) procedure"
and enc :: "(pk*m*unit, c) procedure"
and dec :: "(sk*c*unit, m) procedure"


record ('pk,'sk,'m,'c) Scheme = 
  kg :: "(unit,'pk*'sk) procedure"
  enc :: "('pk*'m*unit,'c) procedure"
  dec :: "('sk*'c*unit, 'm) procedure"

moduletype CPA_Adv where
     choose :: "(pk*unit,m*m) procedure"
and "guess" :: "(c*unit,bool) procedure"

record ('pk,'sk,'m,'c) Adv =
  choose :: "('pk*unit,'m*'m) procedure"
  aguess :: "('c*unit,bool) procedure"

record CPA_Game =
  CPA_main :: "(unit,bool) procedure"

definition "CPA S A :: CPA_Game == (let
  main = proc () { 
    tmp := call (kg S)();
    pk := fst tmp;
    sk := snd tmp;
    tmp := call (choose A)(pk);
    m0 := fst tmp;
    m1 := snd tmp;
    b <- uniform UNIV;
    c := call (enc S)(pk, if b then m1 else m0);
    b' := call (aguess A)(c);
    return (b'=b)
  } in
  \<lparr> CPA_main=main \<rparr>)"

end
