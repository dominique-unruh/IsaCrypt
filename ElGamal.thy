theory ElGamal
imports Hoare_Tactics Procs_Typed Tactic_Inline Lang_Simplifier
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

lemma Rep_ModuleType'_template:
  fixes Rep' :: "'abs::procedure_functor =proc=> 'rep::procedure_functor"
    and Rep :: "'abs::procedure_functor \<Rightarrow> 'rep::procedure_functor"
  assumes Rep'_def: "Rep' \<equiv> Abs_procfun (ProcAbs (ProcRef 0))"
  assumes procedure_functor_mk_untyped_abs_def: 
    "procedure_functor_mk_untyped \<equiv> \<lambda>x\<Colon>'abs. procedure_functor_mk_untyped (Rep x)"
  assumes procedure_functor_type_abs_def:
    "procedure_functor_type \<equiv> \<lambda>_\<Colon>'abs itself. procedure_functor_type TYPE('rep)"
  shows "procfun_apply Rep' = Rep"
apply (rule ext)
unfolding Rep'_def procfun_apply_def procedure_functor_mk_untyped_abs_def
          procedure_functor_mk_untyped_procfun_def apply_procedure_def
apply (subst Abs_procfun_inverse, simp)
 apply (auto simp: wt_ProcAbs_iff wt_ProcRef_iff)
 unfolding procedure_functor_type_abs_def
 close simp
apply (subst beta_reduce_beta)
  close (auto simp: wt_ProcRef_iff)
 close (fact procedure_functor_welltyped)
by simp

lemma Abs_ModuleType'_template:
  fixes Abs' :: "'rep::procedure_functor =proc=> 'abs::procedure_functor"
    and Abs :: "'rep::procedure_functor \<Rightarrow> 'abs::procedure_functor"
  assumes Abs'_def: "Abs' \<equiv> Abs_procfun (ProcAbs (ProcRef 0))"
  assumes procedure_functor_mk_typed'_abs_def: 
    "procedure_functor_mk_typed' \<equiv> \<lambda>p. Abs (procedure_functor_mk_typed' p)"
  assumes procedure_functor_type_abs_def:
    "procedure_functor_type \<equiv> \<lambda>_\<Colon>'abs itself. procedure_functor_type TYPE('rep)"
  shows "procfun_apply Abs' = Abs"
apply (rule ext)
unfolding Abs'_def procfun_apply_def 
          procedure_functor_mk_untyped_procfun_def apply_procedure_def
apply (subst Abs_procfun_inverse; simp?)
 apply (auto simp: wt_ProcAbs_iff wt_ProcRef_iff)
 unfolding procedure_functor_type_abs_def
 close simp
apply (subst beta_reduce_beta)
  close (auto simp: wt_ProcRef_iff)
 close (fact procedure_functor_welltyped)
by (simp add: procedure_functor_mk_typed'_abs_def procedure_functor_mk_typed_def)


(* Hack to allow to state lemma OFCLASS_procedure_functor_class_I. Is there a cleaner way? *)
ML {*  
  val consts_to_unconstrain = [@{const_name procedure_functor_type},
                               @{const_name procedure_functor_mk_untyped},
                               @{const_name procedure_functor_mk_typed'}
                               ];
  val consts_orig_constraints = map (Sign.the_const_constraint @{theory}) consts_to_unconstrain
*}
setup {*
  fold (fn c => fn thy => Sign.add_const_constraint (c,NONE) thy) consts_to_unconstrain
*}


lemma OFCLASS_procedure_functor_class_I: 
  fixes Rep :: "'t::type \<Rightarrow> 'rep::procedure_functor"
    and Abs :: "'rep \<Rightarrow> 't"
  assumes type_def: "procedure_functor_type == \<lambda>x::'t itself. procedure_functor_type (TYPE('rep))"
  assumes mk_untyped_def: "procedure_functor_mk_untyped == \<lambda>x::'t. procedure_functor_mk_untyped (Rep x)"
  assumes mk_typed_def: "procedure_functor_mk_typed' == \<lambda>p. Abs (procedure_functor_mk_typed' p)"
  assumes Abs_inverse: "\<And>y. y\<in>UNIV \<Longrightarrow> Rep (Abs y) = y"
  assumes Rep_inverse: "\<And>x. Abs (Rep x) = x"
  shows "OFCLASS('t, procedure_functor_class)"
apply (intro_classes)
using[[show_consts]]
close (unfold mk_untyped_def type_def, fact procedure_functor_welltyped)
close (unfold mk_untyped_def, fact procedure_functor_beta_reduced)
close (unfold mk_untyped_def mk_typed_def type_def Abs_inverse[OF UNIV_I], fact procedure_functor_mk_typed_inverse')
apply (unfold mk_typed_def mk_untyped_def Rep_inverse procedure_functor_mk_untyped_inverse')
by (fact refl)


(* Recover stored type constraints *)
setup {*
  fold2 (fn c => fn T => fn thy => Sign.add_const_constraint (c,SOME (Logic.unvarifyT_global T)) thy)
      consts_to_unconstrain consts_orig_constraints
*}



ML {*
fun instantiate_type_copy_procedure_functor bind abs_type_name tparams rep_type AbsF RepF Abs_inverse Rep_inverse thy 
  : (thm*thm*thm) * theory
=
  let (* Declaring: instantiation ModuleType :: (prog_type,prog_type)procedure_functor_type *)
      val lthy = Class.instantiation ([abs_type_name], tparams, @{sort procedure_functor}) thy

      val abs_type = Type(abs_type_name,map TFree tparams)

      (* Declaring: definition "procedure_functor_type_AbsType (x::('a,'b) AbsType itself) == procedure_functor_type (TYPE(RepType))" *)
      val pftype_bind = Binding.prefix_name "procedure_functor_type_" bind
      val ((_,(_,pftype_def)),lthy) = Local_Theory.define
          ((pftype_bind,NoSyn), 
           ((Thm.def_binding pftype_bind,[]),
             @{termx "\<lambda>_::?'abs_type itself. procedure_functor_type (TYPE(?'rep_type::procedure_functor))"})) lthy

      (* Declaring: definition "procedure_functor_mk_untyped_AbsType x == procedure_functor_mk_untyped (Rep x)" *)
      val pfmkuntyped_bind = Binding.prefix_name "procedure_functor_mk_untyped_" bind
      val ((_,(_,pfmkuntyped_def)),lthy) = Local_Theory.define
          ((pfmkuntyped_bind,NoSyn), 
           ((Thm.def_binding pfmkuntyped_bind,[]),
             @{termx "\<lambda>x::?'abs_type. procedure_functor_mk_untyped (?RepF x :: ?'rep_type::procedure_functor)"})) lthy

      (* Declaring: definition "procedure_functor_mk_typed'_AbsType p == Abs (procedure_functor_mk_typed' p)" *)
      val pfmktyped_bind = Binding.prefix_name "procedure_functor_mk_typed'_" bind
      val ((_,(_,pfmktyped_def)),lthy) = Local_Theory.define
          ((pfmktyped_bind,NoSyn), 
           ((Thm.def_binding pfmktyped_bind,[]),
             @{termx "\<lambda>p. ?AbsF (procedure_functor_mk_typed' p :: ?'rep_type::procedure_functor) :: 'abs_type"})) lthy

      val export_target = Proof_Context.init_global thy
      fun export thm = Proof_Context.export lthy export_target [thm] |> hd

      (* Declaring: instance apply (rule OFCLASS_procedure_functor_class_I)
                             apply (fact procedure_functor_type_AbsType_def)
                             apply (fact procedure_functor_mk_untyped_AbsType_def)
                             apply (fact procedure_functor_mk_typed'_AbsType_def)
                             apply (fact Abs_inverse apply (fact Rep_inverse) *)

      val pftype_def = export pftype_def
      val pfmktyped_def = export pfmktyped_def
      val pfmkuntyped_def = export pfmkuntyped_def

      fun instance_tac ctx = 
        rtac @{thm OFCLASS_procedure_functor_class_I} 1
            THEN solve_tac ctx [pftype_def] 1
            THEN solve_tac ctx [pfmkuntyped_def] 1
            THEN solve_tac ctx [pfmktyped_def] 1
            THEN solve_tac ctx [Abs_inverse] 1
            THEN solve_tac ctx [Rep_inverse] 1
      val thy = Class.prove_instantiation_exit instance_tac lthy
in ((pftype_def,pfmkuntyped_def,pfmktyped_def),thy) end *}



ML {*
type module_type_spec = {
  name : binding,
  type_params : (string*sort) list,
  procedures : (binding * typ) list
}
*}


ML {*
val EncScheme_spec = {
  name = @{binding EncScheme},
  type_params = [("'pk",@{sort prog_type}),
                 ("'sk",@{sort prog_type}),
                 ("'m",@{sort prog_type}),
                 ("'c",@{sort prog_type})],
  procedures = [(@{binding keygen}, @{typ "(unit,'pk*'sk) procedure"}),
                (@{binding enc}, @{typ "('pk*'m*unit, 'c) procedure"}),
                (@{binding dec}, @{typ "('sk*'c*unit, 'm option) procedure"})]
}
*}

ML {*
(* Example: spec = {name = @{binding ModuleType},
                    type_params = [("'a",@{sort prog_type}), ("'b",@{sort prog_type})],
                    procedures = [(@{binding proc1}, @{typ "(unit,unit) procedure"}),
                                  (@{binding proc2}, @{typ "(unit,'b) procedure"})]} *)

fun declare_module_type (spec:module_type_spec) lthy =
  let val rep_binding = Binding.suffix_name "_rep" (#name spec)
      val tparams = map fst (#type_params spec)
      val proctypes = map snd (#procedures spec)
      val proctypes_tuple = HOLogic.mk_tupleT proctypes

      val lthy_start = lthy

      (* Declaring: type_synonym ('a,'b) ModuleType_rep = "(unit,unit) procedure * (unit,'b) procedure" *)
      val (rep_type_name,lthy) = Typedecl.abbrev (rep_binding,tparams,NoSyn) proctypes_tuple lthy
      val rep_type = Type(rep_type_name, map TFree (#type_params spec))

      (* Declaring: typedef ('a,'b) ModuleType = "UNIV :: ('a::prog_type,'b::prog_type) ModuleType_rep set" *)
      val typedef_repset = HOLogic.mk_UNIV (rep_type)
      val ((abs_type_name,typedef_info),lthy) = 
          Typedef.add_typedef false (#name spec, #type_params spec, NoSyn)
              typedef_repset NONE (K (rtac @{thm UNIV_witness} 1)) lthy
      val abs_type = Type(abs_type_name, map TFree (#type_params spec))

      fun export thm = Proof_Context.export lthy lthy_start [thm] |> hd

      (* Declaring: instantiation ModuleType = (...)procedure_type begin ... end *)
      val inst_global : theory -> (thm*thm*thm)*theory = instantiate_type_copy_procedure_functor 
          (#name spec) abs_type_name (#type_params spec) rep_type
          (Const(#Abs_name (fst typedef_info), rep_type --> abs_type))
          (Const(#Rep_name (fst typedef_info), abs_type --> rep_type))
          (#Abs_inverse (snd typedef_info) |> export) (#Rep_inverse (snd typedef_info) |> export)
      val ((pftype_def,pfmkuntyped_def,pfmktyped_def),lthy) = Local_Theory.background_theory_result inst_global lthy

      (* Declaring: definition Abs_ModuleType' :: "('a,'b) ModuleType_rep =proc=> ('a,'b) ModuleType" where
                    "Abs_ModuleType' = Abs_procfun (ProcAbs (ProcRef 0))" *)
      val Abs_MT_bind = #name spec |> Binding.prefix_name "Abs_" |> Binding.suffix_name "'"
      val ((_,(_,Abs_MT_def)),lthy) = Local_Theory.define
          ((Abs_MT_bind,NoSyn), 
           ((Thm.def_binding Abs_MT_bind,[]),
             @{termx "Abs_procfun (ProcAbs (ProcRef 0)) 
                 :: ?'rep_type::procedure_functor =proc=> ?'abs_type::procedure_functor"})) lthy

      (* Declaring: definition Rep_ModuleType' :: "('a,'b) ModuleType_rep =proc=> ('a,'b) ModuleType" where
                    "Rep_ModuleType' = Rep_procfun (ProcRep (ProcRef 0))" *)
      val Rep_MT_bind = #name spec |> Binding.prefix_name "Rep_" |> Binding.suffix_name "'"
      val ((_,(_,Rep_MT_def)),lthy) = Local_Theory.define
          ((Rep_MT_bind,NoSyn), 
           ((Thm.def_binding Rep_MT_bind,[]),
             @{termx "Abs_procfun (ProcAbs (ProcRef 0)) 
                 :: ?'abs_type::procedure_functor =proc=> ?'rep_type::procedure_functor"})) lthy

      (* Declaring: lemma Rep_ModuleType': "procfun_apply Rep_ModuleType' = Rep_moduleType" *) 
      val Rep_MT_thm = @{thm Rep_ModuleType'_template} OF [Rep_MT_def] OF [pfmkuntyped_def] OF [pftype_def]
      val (_,lthy) = Local_Theory.note ((Rep_MT_bind,@{attributes [simp]}),[Rep_MT_thm]) lthy

      (* Declaring: lemma Abs_ModuleType': "procfun_apply Rep_ModuleType' = Rep_moduleType" *) 
      val Abs_MT_thm = @{thm Abs_ModuleType'_template} OF [Abs_MT_def] OF [pfmktyped_def] OF [pftype_def]
      val (_,lthy) = Local_Theory.note ((Abs_MT_bind,@{attributes [simp]}),[Abs_MT_thm]) lthy


(* val _ = Rep_MT_def
  |> Display.string_of_thm lthy |> writeln *)
val t1 = @{thm Rep_ModuleType'_template} OF [Rep_MT_def] OF [pfmkuntyped_def] OF [pftype_def]
val _ = t1  |> Display.string_of_thm lthy |> writeln

  in  lthy  end
*}

local_setup "declare_module_type EncScheme_spec"


(* type_synonym ('pk,'sk,'m,'c) EncScheme_rep = 
 "(unit,'pk*'sk) procedure *
  ('pk*'m*unit, 'c) procedure *
  ('sk*'c*unit, 'm option) procedure"
 *)


(* declare[[show_sorts]]
typedef ('pk,'sk,'m,'c) EncScheme = "UNIV::('pk,'sk,'m,'c) EncScheme_rep set" ..
print_theorems
lemma Abs_EncScheme_inverse: "Rep_EncScheme (Abs_EncScheme x) = x"
  by (rule Abs_EncScheme_inverse, simp)
 *)


(* setup {*
instantiate_type_copy_procedure_functor @{binding EncScheme} 
  @{type_name EncScheme}
  (#type_params EncScheme_spec)
  @{typ "('pk,'sk,'m,'c)EncScheme_rep"}
  @{term "Abs_EncScheme :: _ => ('pk,'sk,'m,'c)EncScheme"} @{term "Rep_EncScheme :: ('pk,'sk,'m,'c)EncScheme => _"}
  @{thm Abs_EncScheme_inverse} @{thm Rep_EncScheme_inverse}
*}
 *)

thm procedure_functor_type_EncScheme_def

(*
instantiation EncScheme :: (prog_type,prog_type,prog_type,prog_type)procedure_functor begin
definition "procedure_functor_type_EncScheme (_::('xxx,'b,'c,'d) EncScheme itself) == procedure_functor_type (TYPE(('xxx,'b,'c,'d) EncScheme_rep))"
print_theorems
definition "procedure_functor_mk_untyped x == procedure_functor_mk_untyped (Rep_EncScheme x)"
definition "procedure_functor_mk_typed' p == Abs_EncScheme (procedure_functor_mk_typed' p)"
instance 
  apply intro_classes
  close (unfold procedure_functor_mk_untyped_EncScheme_def procedure_functor_type_EncScheme_def, fact procedure_functor_welltyped)
  close (unfold procedure_functor_mk_untyped_EncScheme_def, fact procedure_functor_beta_reduced)
  close (unfold procedure_functor_mk_untyped_EncScheme_def procedure_functor_mk_typed'_EncScheme_def procedure_functor_type_EncScheme_def Abs_EncScheme_inverse[OF UNIV_I],
         fact procedure_functor_mk_typed_inverse')
  apply (unfold procedure_functor_mk_typed'_EncScheme_def procedure_functor_mk_untyped_EncScheme_def Rep_EncScheme_inverse procedure_functor_mk_untyped_inverse')
  by (fact refl)
end *)

(* definition Rep_EncScheme' :: "('pk,'sk,'m,'c) EncScheme =proc=> ('pk,'sk,'m,'c) EncScheme_rep" where
  "Rep_EncScheme' = Abs_procfun (ProcAbs (ProcRef 0))" *)


thm Rep_EncScheme'
thm Abs_EncScheme'
(*lemmas Rep_EncScheme' = Rep_ModuleType'_template[OF Rep_EncScheme'_def, OF procedure_functor_mk_untyped_EncScheme_def,
                               OF procedure_functor_type_EncScheme_def]*)
(*lemmas Abs_EncScheme' = Abs_ModuleType'_template[OF Abs_EncScheme'_def, OF procedure_functor_mk_typed'_EncScheme_def,
                               OF procedure_functor_type_EncScheme_def]*)

(* lemma Rep_EncScheme': "procfun_apply Rep_EncScheme' = Rep_EncScheme"
  apply (rule ext)
  unfolding Rep_EncScheme'_def procfun_apply_def procedure_functor_mk_untyped_EncScheme_def
            procedure_functor_mk_untyped_procfun_def apply_procedure_def
  apply (subst Abs_procfun_inverse, simp?)
   apply (auto simp: wt_ProcAbs_iff wt_ProcRef_iff)
   unfolding procedure_functor_type_EncScheme_def
   close simp
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcRef_iff)
   close (fact procedure_functor_welltyped)
  by simp
 *)


(* definition Abs_EncScheme' :: "('pk,'sk,'m,'c) EncScheme_rep =proc=> ('pk,'sk,'m,'c) EncScheme" where
  "Abs_EncScheme' = Abs_procfun (ProcAbs (ProcRef 0))" *)
(* lemma Abs_EncScheme': "procfun_apply Abs_EncScheme' = Abs_EncScheme"
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
  by (simp add: procedure_functor_mk_typed'_EncScheme_def procedure_functor_mk_typed_def) *)


definition "keygen = procfun_compose <$> fst_procfun <$> Rep_EncScheme'"
definition "enc = procfun_compose <$> fst_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"
definition "dec = procfun_compose <$> snd_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"

lemma keygen[simp]: "keygen <$> (Abs_EncScheme (x,y,z)) = x"
  unfolding keygen_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse[OF UNIV_I] fst_procfun by simp
lemma enc[simp]: "enc <$> (Abs_EncScheme (x,y,z)) = y"
  unfolding enc_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse[OF UNIV_I] fst_procfun snd_procfun by simp
lemma dec[simp]: "dec <$> (Abs_EncScheme (x,y,z)) = z"
  unfolding dec_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse[OF UNIV_I] fst_procfun snd_procfun by simp

subsection {* Declaring module type CPA *}

(* (choose,guess) *)
type_synonym ('pk,'sk,'m,'c) CPA_Adv = 
 "('pk*unit,'m*'m) procedure *
  ('c*unit,bool) procedure"

type_synonym CPA_Game = "(unit,bool)procedure"

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

subsection {* ElGamal *}

definition (in group) ElGamal :: "('G,nat,'G,'G\<times>'G) EncScheme" where
 "ElGamal = LOCAL pk m0 c sk sk' y gm gy.
   Abs_EncScheme (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
                  proc(pk,m0) { y <- uniform {0..<q}; return (g^y, pk^y * m0) },
                  proc(sk',c) { gy := fst c; gm := snd c; return Some (gm * inverse (gy^sk')) })"


procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_*unit,bool)procedure" where
  "Correctness <$> E = LOCAL m1 m2 succ pksk c1.
  proc(m1) {
    pksk := call keygen<$>E();
    c1 := call enc<$>E(fst pksk, m1);
    m2 := call dec<$>E(snd pksk, c1);
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
