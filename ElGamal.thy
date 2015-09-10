theory ElGamal
imports Hoare_Tactics Procs_Typed Tactic_Inline Lang_Simplifier
begin

definition "HIDDEN_EQ = op="
lemma HIDDEN_EQ_refl: "HIDDEN_EQ x x" unfolding HIDDEN_EQ_def ..
lemma HIDDEN_EQ_procargs:
  shows "HIDDEN_EQ procargvars_empty procargvars_empty"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (procargvars_add (LVariable x) a) (procargvars_add (LVariable x) b)"
unfolding HIDDEN_EQ_def by auto
lemma HIDDEN_EQ_varset:
  fixes x x' y y'
  defines "x == mk_variable_untyped (LVariable x')"
  defines "y == mk_variable_untyped (Variable y')"
  shows "HIDDEN_EQ {} {}"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (Set.insert x a) (Set.insert x b)"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (Set.insert y a) (Set.insert y b)"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ a' b' \<Longrightarrow> HIDDEN_EQ (a \<union> a') (b \<union> b')"
unfolding HIDDEN_EQ_def by auto
lemma HIDDEN_EQ_I': "HIDDEN_EQ a b \<Longrightarrow> a==b" by (simp add: HIDDEN_EQ_def)
lemma HIDDEN_EQ_D': "a==b \<Longrightarrow> HIDDEN_EQ a b" by (simp add: HIDDEN_EQ_def)

lemma vars_proc_global_inter_vu_global: 
  "set (vars_proc_global f) \<inter> Collect vu_global = set (vars_proc_global f)"
unfolding vars_proc_global_def by auto

lemma filter_locals1: "Set.filter (\<lambda>x. \<not> vu_global x) (insert (mk_variable_untyped (LVariable x :: 'a::prog_type variable)) V)
  = insert (mk_variable_untyped (LVariable x :: 'a variable)) (Set.filter (\<lambda>x. \<not> vu_global x) V)"
  by auto
lemma filter_locals2: "Set.filter (\<lambda>x. \<not> vu_global x) (insert (mk_variable_untyped (Variable x :: 'a::prog_type variable)) V)
  = Set.filter (\<lambda>x. \<not> vu_global x) V"
  by auto
lemma filter_locals3: "Set.filter (\<lambda>x. \<not> vu_global x) (set (vars_proc_global f)) = {}"
  using vars_proc_global_inter_vu_global by fastforce 

ML {* Option.map *}

ML {*

*}


default_sort prog_type

class ab_group_mult = inverse + ab_semigroup_mult + monoid_mult +
  assumes left_inverse [simp]: "(inverse a) * a = 1"

lemma (in ab_group_mult) right_inverse [simp]: "a * inverse a = 1"
  by (subst mult_commute, simp)

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,inverse,power,ab_group_mult}" (* generator *)
  and q::nat (* group order *)


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

declare[[show_types=false]]
thm group.DDH0_def

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

type_synonym ('pk,'sk,'m,'c) EncScheme_rep = 
 "(unit,'pk*'sk) procedure *
  ('pk*'m*unit, 'c) procedure *
  ('sk*'c*unit, 'm option) procedure"

typedef ('pk,'sk,'m,'c) EncScheme = "UNIV::('pk,'sk,'m,'c) EncScheme_rep set" ..
lemma Abs_EncScheme_inverse: "Rep_EncScheme (Abs_EncScheme x) = x"
  by (rule Abs_EncScheme_inverse, simp)

instantiation EncScheme :: (prog_type,prog_type,prog_type,prog_type)procedure_functor begin
definition "procedure_functor_type (_::('a,'b,'c,'d) EncScheme itself) == procedure_functor_type (TYPE(('a,'b,'c,'d) EncScheme_rep))"
definition "procedure_functor_mk_untyped x == procedure_functor_mk_untyped (Rep_EncScheme x)"
definition "procedure_functor_mk_typed' p == Abs_EncScheme (procedure_functor_mk_typed' p)"
instance 
  apply intro_classes
  close (unfold procedure_functor_mk_untyped_EncScheme_def procedure_functor_type_EncScheme_def, fact procedure_functor_welltyped)
  close (unfold procedure_functor_mk_untyped_EncScheme_def, fact procedure_functor_beta_reduced)
  close (unfold procedure_functor_mk_untyped_EncScheme_def procedure_functor_mk_typed'_EncScheme_def procedure_functor_type_EncScheme_def Abs_EncScheme_inverse,
         fact procedure_functor_mk_typed_inverse')
  apply (unfold procedure_functor_mk_typed'_EncScheme_def procedure_functor_mk_untyped_EncScheme_def Rep_EncScheme_inverse procedure_functor_mk_untyped_inverse')
  by (fact refl)
end

definition Rep_EncScheme' :: "('pk,'sk,'m,'c) EncScheme =proc=> ('pk,'sk,'m,'c) EncScheme_rep" where
  "Rep_EncScheme' = Abs_procfun (ProcAbs (ProcRef 0))"
lemma Rep_EncScheme': "procfun_apply Rep_EncScheme' = Rep_EncScheme"
  apply (rule ext)
  unfolding Rep_EncScheme'_def procfun_apply_def procedure_functor_mk_untyped_EncScheme_def
            procedure_functor_mk_untyped_procfun_def apply_procedure_def
  apply (subst Abs_procfun_inverse; simp?)
   apply (auto simp: wt_ProcAbs_iff wt_ProcRef_iff)
   unfolding procedure_functor_type_EncScheme_def
   close simp
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcRef_iff)
   close (fact procedure_functor_welltyped)
  by simp

definition Abs_EncScheme' :: "('pk,'sk,'m,'c) EncScheme_rep =proc=> ('pk,'sk,'m,'c) EncScheme" where
  "Abs_EncScheme' = Abs_procfun (ProcAbs (ProcRef 0))"
lemma Abs_EncScheme': "procfun_apply Abs_EncScheme' = Abs_EncScheme"
  apply (rule ext)
  unfolding Abs_EncScheme'_def procfun_apply_def procedure_functor_mk_untyped_EncScheme_def
            procedure_functor_mk_untyped_procfun_def apply_procedure_def
  apply (subst Abs_procfun_inverse; simp?)
   apply (auto simp: wt_ProcAbs_iff wt_ProcRef_iff)
   unfolding procedure_functor_type_EncScheme_def
   close simp
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcRef_iff)
   close (fact procedure_functor_welltyped)
  apply simp
  by (simp add: procedure_functor_mk_typed'_EncScheme_def procedure_functor_mk_typed_def)


definition "keygen = procfun_compose <$> fst_procfun <$> Rep_EncScheme'"
definition "enc = procfun_compose <$> fst_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"
definition "dec = procfun_compose <$> snd_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"

lemma keygen[simp]: "keygen <$> (Abs_EncScheme (x,y,z)) = x"
  unfolding keygen_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun by simp
lemma enc[simp]: "enc <$> (Abs_EncScheme (x,y,z)) = y"
  unfolding enc_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun snd_procfun by simp
lemma dec[simp]: "dec <$> (Abs_EncScheme (x,y,z)) = z"
  unfolding dec_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun snd_procfun by simp


(* (choose,guess) *)
type_synonym ('pk,'sk,'m,'c) CPA_Adv = 
 "('pk*unit,'m*'m) procedure *
  ('c*unit,bool) procedure"

type_synonym CPA_Game = "(unit,bool)procedure"

declare[[show_types=false]]

procedure CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> CPA_Game" where
 "CPA_main <$> (E,(Achoose,Aguess)) = 
  LOCAL pk sk m0 m1 b c b' tmp1 tmp2.
  proc () {
    tmp1 := call keygen<$>E();
    pk := fst tmp1;
    sk := snd tmp1;
    tmp2 := call Achoose(pk);
    m0 := fst tmp2;
    m1 := snd tmp2;
    b <- uniform UNIV;
    c := call enc<$>E(pk, if b then m1 else m0);
    b' := call Aguess(c);
    return b'=b
  }"

definition (in group) ElGamal :: "('G,nat,'G,'G\<times>'G) EncScheme" where
 "ElGamal = LOCAL pk m0 c sk sk' y gm gy.
   Abs_EncScheme (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
                  proc(pk,m0) { y <- uniform {0..<q}; return (g^y, pk^y * m0) },
                  proc(sk',c) { gy := fst c; gm := snd c; return Some (gm * inverse (gy^sk')) })"

(*
module Correctness (S:Scheme) = {
  proc main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext option;

    (pk, sk) = S.kg();
    c        = S.enc(pk, m);
    m'       = S.dec(sk, c); 
    return (m' = Some m);
  }
}.
*)

lemma set_filter_empty: "Set.filter f {} = {}" by auto
lemma set_filter_union: "Set.filter f (x\<union>y) = Set.filter f x \<union> Set.filter f y" by auto
(*lemma HIDDEN_EQ_set_filter: "HIDDEN_EQ (set (vars_proc_global p)) x \<Longrightarrow> 
  HIDDEN_EQ (Set.filter (\<lambda>x\<Colon>variable_untyped. \<not> vu_global x) (set (vars_proc_global p))) x"
by (simp add: set_filter_vars_proc_global) *)
lemma HIDDEN_EQ_set_filter: "HIDDEN_EQ (Set.filter (\<lambda>x\<Colon>variable_untyped. \<not> vu_global x) (set (vars_proc_global p))) {}"
  unfolding HIDDEN_EQ_def vars_proc_global_def by auto

procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_*unit,bool)procedure" where
  "Correctness <$> E = LOCAL m1 m2 succ pksk c1.
  proc(m1) {
    pksk := call keygen<$>E();
    c1 := call enc<$>E(fst pksk, m1);
    m2 := call dec<$>E(snd pksk, c1);
    succ := (m2 = Some m1);
    return succ
  }"

(*lemma h1: "scheme = (fst scheme, fst (snd scheme), snd (snd scheme))" by auto*)
lemma h1: "scheme = Abs_EncScheme (keygen<$>scheme, enc<$>scheme, dec<$>scheme)"
  apply (subst (1 2 3 4) Rep_EncScheme_inverse[of scheme, symmetric])
  by (cases "Rep_EncScheme scheme", simp)

(* TODO: create those automatically *)
schematic_lemma Correctness_body [procedure_info]: "p_body (Correctness <$> scheme) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma Correctness_return [procedure_info]: "p_return (Correctness <$> scheme) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma Correctness_args [procedure_info]: "p_args (Correctness <$> scheme) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_def by (simp?, rule HIDDEN_EQ_procargs)+
schematic_lemma Correctness_body_vars [procedure_info]: "
  \<lbrakk> set (vars_proc_global (keygen<$>scheme)) == ?v1; set (vars_proc_global (enc<$>scheme)) == ?v2; 
    set (vars_proc_global (dec<$>scheme)) == ?v3\<rbrakk>
  \<Longrightarrow> set (vars (p_body (Correctness<$>scheme))) == ?b"
  apply (subst h1) apply (drule HIDDEN_EQ_D')+ apply (rule HIDDEN_EQ_I')
  unfolding Correctness_body apply simp_all by (rule HIDDEN_EQ_varset; simp?)+
schematic_lemma Correctness_return_vars [procedure_info]: "set (e_vars (p_return (Correctness<$>scheme))) == ?b"
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_return by (simp?, rule HIDDEN_EQ_varset)+
schematic_lemma Correctness_body_local_vars [procedure_info]: "set (local_vars (p_body (Correctness<$>scheme))) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I')
  unfolding local_vars_def filter_set[symmetric] apply (subst Correctness_body_vars)
  unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty set_filter_union
  apply simp_all by (rule HIDDEN_EQ_varset HIDDEN_EQ_set_filter; simp?)+

ML {* fun pull_pattern thm = thm |> Thm.concl_of |> Logic.dest_equals |> fst |> Term.dest_comb |> snd |> 
  Thm.global_cterm_of (Thm.theory_of_thm thm)
*}

ML {*
fun quick_reg [args,body,return,return_vars,body_local_vars] = 
  let val pattern = pull_pattern args
      val name = Procs_Typed.procedure_head_of (Thm.term_of pattern)
      val info : Procs_Typed.procedure_info = {
         pattern = pattern,
         args = SOME args,
         body = SOME body,
         return = SOME return,
         return_vars = SOME return_vars,
         body_local_vars = SOME body_local_vars
      }
  in
    Procs_Typed.register_procedure name info
  end
  | quick_reg _ = error "quick_reg"
  *}

local_setup {* quick_reg @{thms Correctness_args Correctness_body Correctness_return Correctness_return_vars Correctness_body_local_vars} *}

(*
local_setup {*
  let val Const(name,_) = @{term Correctness}
      val info : Procs_Typed.procedure_info = {
         pattern = pull_pattern @{thm Correctness_args},
         args = SOME @{thm Correctness_args},
         body = SOME @{thm Correctness_body},
         return = SOME @{thm Correctness_return},
         return_vars = SOME @{thm Correctness_return_vars},
         body_local_vars = SOME @{thm Correctness_body_local_vars}
      }
  in
    Procs_Typed.register_procedure name info
  end
*}*)

ML {* fun valOf (SOME x) = x | valOf NONE = error "NONE" *}

ML {* Procs_Typed.get_procedure_info @{context} true @{term "Correctness <$> x"} |> #args |> valOf *}


context group begin
schematic_lemma kg_body [procedure_info]: "p_body (keygen<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma kg_return [procedure_info]: "p_return (keygen<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma kg_args [procedure_info]: "p_args (keygen<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def by (simp, rule HIDDEN_EQ_procargs)+
schematic_lemma kg_body_vars [procedure_info]: "set (vars (p_body (keygen<$>ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_body ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma kg_return_vars [procedure_info]: "set (e_vars (p_return (keygen<$>ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_return ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma kg_body_local_vars [procedure_info]: "set (local_vars (p_body (keygen<$>ElGamal))) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding local_vars_def filter_set[symmetric] apply (subst kg_body_vars)
 unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty
 by (rule HIDDEN_EQ_varset)+

local_setup {* quick_reg @{thms kg_args kg_body kg_return kg_return_vars kg_body_local_vars} *}


schematic_lemma enc_args [procedure_info]: "p_args (enc<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (rule HIDDEN_EQ_procargs)+
schematic_lemma enc_body_vars [procedure_info]: "set (vars (p_body (enc<$>ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_body ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma enc_body_local_vars [procedure_info]: "set (local_vars (p_body (enc<$>ElGamal))) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding local_vars_def filter_set[symmetric] apply (subst enc_body_vars)
 unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty
 by (rule HIDDEN_EQ_varset)+
schematic_lemma enc_return_vars [procedure_info]: "set (e_vars (p_return (enc<$>ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_return ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma enc_body [procedure_info]: "p_body (enc<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma enc_return [procedure_info]: "p_return (enc<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)

local_setup {* quick_reg @{thms enc_args enc_body enc_return enc_return_vars enc_body_local_vars} *}

schematic_lemma dec_args [procedure_info]: "p_args (dec<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (rule HIDDEN_EQ_procargs)+
schematic_lemma dec_body_vars [procedure_info]: "set (vars (p_body (dec<$>ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_body ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma dec_body_local_vars [procedure_info]: "set (local_vars (p_body (dec<$>ElGamal))) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding local_vars_def filter_set[symmetric] apply (subst dec_body_vars)
 unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty
 by (rule HIDDEN_EQ_varset)+
schematic_lemma dec_return_vars [procedure_info]: "set (e_vars (p_return (dec<$>ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_return ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma dec_body [procedure_info]: "p_body (dec<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma dec_return [procedure_info]: "p_return (dec<$>ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)

local_setup {* quick_reg @{thms dec_args dec_body dec_return dec_return_vars dec_body_local_vars} *}

end

lemma (in group) correctness:
  shows "LOCAL succ0. hoare {True} succ0 := call Correctness <$> ElGamal(m) {succ0}"
apply (inline "Correctness<$>ElGamal")
apply (inline "keygen<$>ElGamal")
apply (inline "dec<$>ElGamal")
apply (inline "enc<$>ElGamal")
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat]) 
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

end
