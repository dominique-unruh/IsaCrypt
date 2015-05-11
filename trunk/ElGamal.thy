theory ElGamal
imports Hoare_Tactics Procs_Typed
begin

default_sort prog_type

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
      local x y b;
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      b := call A (g^x, g^y, g^(x*y));
      return True
    }"

definition_by_specification DDH1 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "procfun_apply DDH1 A = 
    proc () {
      local x y z b;
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

declare[[eta_contract=false]]

(* TODO: get rid of those *)
abbreviation "b == LVariable ''b'' :: bool variable"
abbreviation "b' == LVariable ''b_'' :: bool variable"


definition_by_specification CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> CPA_Game" where
 "procfun_apply CPA_main ((kg,enc,dec),(Achoose,Aguess)) = 
  proc () { 
    local pk sk m0 m1 b c b' tmp1 tmp2;
    tmp1 := call kg();
    pk := fst (tmp1::'pk*'sk);
    sk := snd (tmp1::'pk*'sk);
    tmp2 := call Achoose(pk);
    m0 := fst (tmp2::'m*'m);
    m1 := snd (tmp2::'m*'m);
    b <- uniform UNIV;
    c := call enc(pk, if b then m1 else m0);
    b' := call Aguess(c);
    return (b'=b) (* WARNING: return statement is not included in "local" *)
  }"

end
