theory ElGamal
imports Hoare_Tactics Procs_Typed Tactic_Inline Lang_Simplifier
keywords "module_type" :: thy_decl
begin

subsection {* General setup *}

default_sort prog_type

class ab_group_mult = inverse + ab_semigroup_mult + monoid_mult +
  assumes left_inverse [simp]: "(inverse a) * a = 1"

lemma (in ab_group_mult) right_inverse [simp]: "a * inverse a = 1"
  by (subst mult_commute, simp)

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,inverse,power,ab_group_mult}" (* generator *)
  and q::nat (* group order *)

subsection {* DDH *}

type_synonym 'g DDH_Adv = "('g*'g*'g*unit,bool) procedure"
type_synonym 'g DDH_Game = "(unit,bool) procedure"

procedure (in group) DDH0 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "DDH0 <$> A = 
    LOCAL x y b.
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      b := call A (g^x, g^y, g^(x*y));
      return True
    }"

procedure (in group) DDH1 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "DDH1 <$> A = 
    LOCAL x y z b.
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      z <- uniform {0..<q};
      b := call A (g^x, g^y, g^z);
      return True
    }"

subsection {* Declaring module type EncScheme *}

ML {*
fun declare_module_type_cmd name tparams procedures lthy =
  let val tparams = map (apsnd (Typedecl.read_constraint lthy)) tparams
      (* val lthy = fold (Variable.declare_typ o TFree) tparams lthy *)
      val tparams = map (Proof_Context.check_tfree lthy) tparams
      val procedureTs = Syntax.read_typs lthy (map (fn (_, T, _) => T) procedures)
      val procedureBindings = map (fn (bind,_,_) => bind) procedures
      val procedures = ListPair.zip (procedureBindings, procedureTs)
      val spec = { name = name, type_params = tparams, procedures = procedures }
(*
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    val params' = map (Proof_Context.check_tfree ctxt3) params;
*)
  in
  Procs_Typed.declare_module_type spec lthy
  end
*}


ML {*
Outer_Syntax.local_theory @{command_keyword module_type} "define a module type"
    (Parse.type_args_constrained -- Parse.binding -- (@{keyword "="} |-- Scan.repeat1 Parse.const_binding)
    >> (fn ((tparams,binding), procedures) => declare_module_type_cmd binding tparams procedures))
*}


module_type ('pk,'sk,'m,'c) EncScheme =
  keygen :: "(unit,'pk*'sk) procedure"
  enc :: "('pk*'m*unit, 'c) procedure"
  dec :: "('sk*'c*unit, 'm option) procedure"



subsection {* Declaring module type CPA *}

module_type ('pk,'sk,'m,'c) CPA_Adv =
  pick    :: "('pk*unit,'m*'m) procedure"
  "guess" :: "('c*unit,bool) procedure"


procedure CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> (unit,bool)procedure" where
 "CPA_main <$> (E,A) = 
  LOCAL pk sk m0 m1 b c b' tmp1 tmp2.
  proc () {
    tmp1 := call keygen<$>E();
    pk := fst tmp1;
    sk := snd tmp1;
    tmp2 := call pick<$>A(pk);
    m0 := fst tmp2;
    m1 := snd tmp2;
    b <- uniform UNIV;
    c := call enc<$>E(pk, if b then m1 else m0);
    b' := call guess<$>A(c);
    return b'=b
  }"

subsection {* ElGamal *}

definition (in group) ElGamal :: "('G,nat,'G,'G\<times>'G) EncScheme" where
 "ElGamal = LOCAL pk m0 c sk sk' y gm gy.
   Abs_EncScheme (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
                  proc(pk,m0) { y <- uniform {0..<q}; return (g^y, pk^y * m0) },
                  proc(sk',c) { gy := fst c; gm := snd c; return Some (gm * inverse (gy^sk')) })"


procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_*unit,bool)procedure" where
  "Correctness <$> E = LOCAL m1 m2 succ pksk c1.
  proc(m1) {
    pksk := call keygen<$>E ();
    c1 := call enc<$>E (fst pksk, m1);
    m2 := call dec<$>E (snd pksk, c1);
    succ := (m2 = Some m1);
    return succ
  }"


local_setup {* Procs_Typed.register_procedure_thm @{thm Correctness_def} *}

context group begin

schematic_lemma keygen_def': "keygen<$>ElGamal = ?x"
  unfolding ElGamal_def by simp
local_setup {* Procs_Typed.register_procedure_thm @{thm keygen_def'} *}


schematic_lemma enc_def': "enc<$>ElGamal = ?x"
  unfolding ElGamal_def by simp
local_setup {* Procs_Typed.register_procedure_thm @{thm enc_def'} *}

schematic_lemma dec_def': "dec<$>ElGamal = ?x"
  unfolding ElGamal_def by simp
local_setup {* Procs_Typed.register_procedure_thm @{thm dec_def'} *}

lemma correctness:
  shows "LOCAL succ0. hoare {True} succ0 := call Correctness <$> ElGamal(m) {succ0}"
apply (inline "Correctness<$>ElGamal")
apply (inline "keygen<$>ElGamal")
apply (inline "dec<$>ElGamal")
apply (inline "enc<$>ElGamal")
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat]) 
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

end (* context group *)




end (* theory *)
