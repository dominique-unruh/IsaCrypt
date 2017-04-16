theory ElGamal
imports Hoare_Tactics Procs_Typed Tactic_Inline Lang_Simplifier RHL_Typed Callproc ML_Term LangSyntax2
begin

(* Working EC version with elgamal.ec:
  47f69a002b66340bb3b4967b46973670a0e46750 (2015-10-16)  
*)

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

type_synonym Game = "(unit,bool) procedure"
type_synonym 'g DDH_Adv = "('g*'g*'g,bool) procedure"

procedure (in group) DDH0 :: "'G DDH_Adv =proc=> Game" where
  "DDH0 <$> A = 
    PR \<open>proc () {
      x <$ uniform {0..<q};
      y <$ uniform {0..<q};
      b <@ A (g^x, g^y, g^(x*y));
      return b
    }\<close>"

procedure (in group) DDH1 :: "'G DDH_Adv =proc=> Game" where
  "DDH1 <$> A = 
    PR \<open>proc () {
      x <$ uniform {0..<q};
      y <$ uniform {0..<q};
      z <$ uniform {0..<q};
      b <@ A (g^x, g^y, g^z);
      return b
    }\<close>"

subsection {* PKE definitions *}

module_type ('pk,'sk,'m,'c) EncScheme =
  keygen :: "(unit,'pk*'sk) procedure"
  enc :: "('pk*'m, 'c) procedure"
  dec :: "('sk*'c, 'm option) procedure"
(*setup {*
  Lang_Syntax2.insert_field_selector_thy "keygen" @{type_name EncScheme} @{const_name keygen}
  #> Lang_Syntax2.insert_field_selector_thy "enc" @{type_name EncScheme} @{const_name enc}
  #> Lang_Syntax2.insert_field_selector_thy "dec" @{type_name EncScheme} @{const_name dec}
*}*)
  

(*module_type ('pk,'sk,'m,'c) Adversary =
  choos :: "('pk,'m*'m)procedure" 
  "guess" :: "('c,bool)procedure"

procedure CPA :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) Adversary =proc=> Game" where
  "CPA<$>(E,A) = LOCAL pk sk m0 m1 c b b'. proc() {
    (pk, sk) <@ keygen<$>E();
    (m0, m1) <@ choos<$>A(pk);
    b        <- uniform UNIV;
    c        <@ enc<$>E(pk, if b then m1 else m0);
    b'       <@ guess<$>A(c);
    return (b' = b)
  }"*)

subsection {* Declaring CPA game *}

module_type ('pk,'sk,'m,'c) CPA_Adv =
  pick    :: "('pk,'m*'m) procedure"
  "guess" :: "('c,bool) procedure"
(* setup {* declare_method_field_selector @{binding pick} *} *)
  
  (*
setup {*
  Lang_Syntax2.insert_field_selector_thy "pick" @{type_name CPA_Adv} @{const_name pick}
  #> Lang_Syntax2.insert_field_selector_thy "guess" @{type_name CPA_Adv} @{const_name guess}
*}*)
  
  
term "(E::(_,_,_,_)CPA_Adv) .pick"


    
procedure CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> (unit,bool)procedure" where
 "CPA_main <$> (E,A) = 
  PR \<open>proc () {
    (pk,sk) <@ E.keygen ();
    (m0,m1) <@ A.pick (pk);
    b <$ uniform UNIV;
    c <@ E.enc(pk, if b then m1 else m0);
    b' <@ A.guess (c);
    return b'=b
  }\<close>"

subsection {* ElGamal *}

(* These should be generated by module_type EncScheme *)

lemma aux1 [reduce_procfun.safe]:
  assumes "schematic=Abs_EncScheme(A,B,C)"
  assumes "A=Y"
  shows "EncScheme.keygen<$>schematic = Y"
using assms by simp

lemma aux2 [reduce_procfun.safe]:
  assumes "schematic=Abs_EncScheme(A,B,C)"
  assumes "B=Y"
  shows "EncScheme.enc<$>schematic = Y"
using assms by simp

lemma aux3 [reduce_procfun.safe]:
  assumes "schematic=Abs_EncScheme(A,B,C)"
  assumes "C=Y"
  shows "EncScheme.dec<$>schematic = Y"
using assms by simp

procedure (in group) ElGamal :: "('G, nat, 'G, 'G\<times>'G) EncScheme" where
    "EncScheme.keygen<$>ElGamal = PR \<open>proc() { sk <$ uniform {0..<q}; return (g^sk, sk) }\<close>"
| "EncScheme.enc<$>ElGamal = PR \<open>proc(pk,m) { y <$ uniform {0..<q}; return (g^y, pk^y * m) }\<close>"
| "EncScheme.dec<$>ElGamal = PR \<open>proc(sk,(c1,c2)) { gy := c1; gm := c2; return Some (gm * inverse (gy^sk)) }\<close>"

procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_,bool)procedure" where
  "Correctness <$> E = 
  PR \<open>proc(m) {
    (pk,sk) <@ E.keygen ();
    c <@ E.enc (pk, m);
    m2 <@ E.dec (sk, c);
    return (m2 = Some m)
  }\<close>"

context group begin

lemma correctness:
  defines "G = Correctness <$> ElGamal"
  shows "hoare {True} succ0 <@ G(m) {succ0}"
apply (inline "Correctness<$>ElGamal")
apply (inline "keygen<$>ElGamal")
apply (inline "dec<$>ElGamal")
apply (inline "enc<$>ElGamal")
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat])
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

(* sorry (* "uncommented for speed" *) *)
  
type_synonym 'g ElGamal_Adv = "('g, nat, 'g, 'g\<times>'g) CPA_Adv"

procedure DDHAdv :: "'G ElGamal_Adv =proc=> 'G DDH_Adv" where
  "DDHAdv <$> A = PR\<open>
    proc (gx, gy, gz) {
      (m0, m1) <@ A.pick(gx);
      b  <$ uniform UNIV;
      b' <@ A.guess(gy, gz * (if b then m1 else m0));
      return b' = b
  }\<close>"



(* TODO move, add syntax *)
definition "game_probability game args mem E == 
  LOCAL res. 
  probability 
    (denotation (callproc (variable_pattern res) game (const_expression args)) mem)
    {m. E (memory_lookup m res)}"

(* TODO move *)
(* TODO: correct precondition (refer only to globals of p1,p2) *)
lemma byequiv_rule:
  assumes "LOCAL res1 res2. hoare {&1=m \<and> &2=m} (res1 <@ p1(a1)) ~ (res2 <@ p2(a2)) {E (res1)\<^sub>1 \<longleftrightarrow> F (res2)\<^sub>2}"
  shows "game_probability p1 a1 m E = game_probability p2 a2 m F" 
proof - 
  let ?res1 = "LOCAL res1. (res1 :: 'a variable)"
  let ?res2 = "LOCAL res2. (res2 :: 'c variable)"
  let ?res1' = "LOCAL res. (res :: 'a variable)"
  let ?res2' = "LOCAL res. (res :: 'c variable)"
  let ?pr1 = "PROGRAM[ ?res1 <@ p1(a1) ]"
  let ?pr2 = "PROGRAM[ ?res2 <@ p2(a2) ]"
  obtain \<mu> where fst: "apply_to_distr fst \<mu> = denotation ?pr1 m"
             and snd: "apply_to_distr snd \<mu> = denotation ?pr2 m"
             and supp: "\<And>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<Longrightarrow> E (memory_lookup m1' ?res1) = F (memory_lookup m2' ?res2)"
    using assms unfolding rhoare_def program_def by auto
  have "game_probability p1 a1 m E = probability (denotation PROGRAM[ ?res1' <@ p1(a1) ] m) {m. E (memory_lookup m ?res1')}" 
    unfolding game_probability_def program_def by simp
  also have "\<dots> = probability (denotation ?pr1 m) {m. E (memory_lookup m ?res1)}"
    sorry
  also have "... = probability (apply_to_distr fst \<mu>) {m. E (memory_lookup m ?res1)}"
    unfolding fst by simp
  also have "\<dots> = probability \<mu> {m12. E (memory_lookup (fst m12) ?res1)}"
    unfolding probability_apply_to_distr by simp
  also have "\<dots> = probability \<mu> {m12. F (memory_lookup (snd m12) ?res2)}"
    apply (rule probability_cong)
    using supp by auto
  also have "... = probability (apply_to_distr snd \<mu>) {m. F (memory_lookup m ?res2)}"
    unfolding probability_apply_to_distr by simp
  also have "\<dots> = probability (denotation ?pr2 m) {m. F (memory_lookup m ?res2)}"
    unfolding snd by simp
  also have "\<dots> = probability (denotation PROGRAM[ ?res2' <@ p2(a2) ] m) {m. F (memory_lookup m ?res2')}" 
    sorry
  also have "\<dots> = game_probability p2 a2 m F"
    unfolding game_probability_def program_def by simp

  finally show ?thesis by assumption
qed  

(* TODO move *)
lemma denotation_eq_rule_left:
  assumes "denotation d = denotation c"
  assumes "rhoare P c e Q"
  shows   "rhoare P d e Q"
using assms unfolding rhoare_def by auto

(* TODO move *)
lemma lang_simp_assign_ignore [lang_simp]: "fun_equiv denotation (assign ignore_pattern e) Lang_Typed.skip"
  sorry

lemma LVariable_notin_write_vars_proc_global [simp]: "mk_variable_untyped (LVariable x) \<notin> set (write_vars_proc_global f)" sorry
lemma LVariable_notin_vars_proc_global [simp]: "mk_variable_untyped (LVariable x) \<notin> set (vars_proc_global f)" sorry

(* abbreviation "res == LVariable ''res''"
abbreviation "args == LVariable ''args''" *)

(* TODO: define product_type on untyped level *)
(* TODO define pair pattern on untyped level *)
(*definition pair_pattern_untyped :: "pattern_untyped \<Rightarrow> pattern_untyped \<Rightarrow> pattern_untyped" where
  "pair_pattern_untyped p1 p2 = Abs_pattern_untyped 
  \<lparr> pur_var_getters=(map (\<lambda>(v,g). (v,g o fst o inv val_prod_embedding)) (pu_var_getters p1))
                  @ (map (\<lambda>(v,g). (v,g o snd o inv val_prod_embedding)) (pu_var_getters p2)),
    pur_type=Type TYPE('a::prog_type*'b::prog_type) \<rparr>) :: ('a*'b) pattern) \<rparr>"
lemma Rep_pair_pattern': "Rep_pattern (pair_pattern x y) = pair_pattern_untyped (Rep_pattern x) (Rep_pattern y)"
  sorry*)

(* fun list_pattern_untyped :: "variable_untyped list \<Rightarrow> pattern_untyped" where
  "list_pattern_untyped [] = pattern_ignore unit_type"
| "list_pattern_untyped (x#xs) = pair_pattern_untyped (pattern_1var x) (list_pattern_untyped xs)" *)

(*
lemma list_pattern_untyped_nil: "list_pattern_untyped [] = Rep_pattern unit_pattern"
  apply simp apply (subst Rep_pattern_untyped_inject[symmetric]) unfolding Rep_unit_pattern Rep_pattern_ignore by (auto simp: Type_def unit_type_def)
lemma list_pattern_untyped_cons: "list_pattern_untyped (mk_variable_untyped x # xs)
     = Rep_pattern (pair_pattern (variable_pattern x) (Abs_pattern (list_pattern_untyped xs)))"
  apply simp unfolding Rep_pair_pattern Rep_variable_pattern
  apply (subst Abs_pattern_inverse) apply simp
sorry
*)

(* abbreviation "list_pattern xs == Abs_pattern (list_pattern_untyped xs)"

abbreviation "x1 == LVariable ''x1'' :: int variable"
abbreviation "x2 == LVariable ''x2'' :: bool variable"
abbreviation "x3 == LVariable ''x3'' :: (nat\<Rightarrow>nat) variable"

lemma t1: "pattern_ignore unit_type = Rep_pattern unit_pattern" 
  apply (rule Rep_pattern_untyped_inject[THEN iffD1])
  unfolding Rep_unit_pattern Rep_pattern_ignore
  by (simp add: Type_def unit_type_def) 

lemma "list_pattern [mk_variable_untyped x1, mk_variable_untyped x2, mk_variable_untyped x3] = 
(pair_pattern (variable_pattern x1) (pair_pattern (variable_pattern x2) (pair_pattern (variable_pattern x3) unit_pattern)))"
using[[show_consts]]
  by (simp add: t1 Rep_variable_pattern[symmetric] Rep_pair_pattern[symmetric] Rep_pattern_inverse) *)


(*
{P} f ~ g {Q}
{A} p ~ q {  P{y_1/arg_1, y_2/arg_2}  /\  
      \forall gR,gL,yL,yR.   Q{gL/glob f1,gR/glob f2,yL/res_1,yR/res_2}
                                ==> B{gL/glob f1,gR/glob f2,yL/x_1,yR/x_2}  }
-----------------------------------------------
{A} p;x=f(y) ~ q;x=f(y) {B}  
*)



lemma cpa_ddh0:
  "game_probability (CPA_main<$>(ElGamal,A)) () m (\<lambda>res. res)
 = game_probability (DDH0<$>(DDHAdv<$>A)) () m (\<lambda>res. res)"

apply (rule byequiv_rule)
apply (inline "CPA_main<$>(ElGamal,A)")
apply (inline "DDH0<$>(DDHAdv<$>A)")
apply (inline "keygen <$> ElGamal")
apply (inline "enc <$> ElGamal")
apply (inline "DDHAdv<$>A")
apply simp


find_theorems "fun_equiv denotation (assign (?x) ?e) Lang_Typed.skip"
(*
pre = (glob A){2} = (glob A){m} /\ (glob A){1} = (glob A){m}

sk0 <$ FDistr.dt            (1)  x <$ FDistr.dt                        
(pk, sk) <- (g ^ sk0, sk0)  (2)  y <$ FDistr.dt                        
(m0, m1) <@ A.choose(pk)    (3)  gx <- g ^ x                           
b <$ {0,1}                  (4)  gy <- g ^ y                           
pk0 <- pk                   (5)  gz <- g ^ (x * y)                     
m <- b ? m1 : m0            (6)  (m0, m1) <@ A.choose(gx)              
y <$ FDistr.dt              (7)  b0 <$ {0,1}                           
c <- (g ^ y, pk0 ^ y * m)   (8)  b' <@ A.guess(gy, gz * (b0 ? m1 : m0))
b' <@ A.guess(c)            (9)  b <- b' = b0                          

post = (b'{1} = b{1}) = b{2}
*)

apply (rule denotation_eq_rule_left) apply (tactic \<open>Hoare_Tactics.swap_tac @{context} ([10],6) 4 false 1\<close>) (* TODO right numbers *)
apply simp

(*
pre = (glob A){2} = (glob A){m} /\ (glob A){1} = (glob A){m}

sk0 <$ FDistr.dt            (1)  x <$ FDistr.dt                        
y <$ FDistr.dt              (2)  y <$ FDistr.dt                        
(pk, sk) <- (g ^ sk0, sk0)  (3)  gx <- g ^ x                           
(m0, m1) <@ A.choose(pk)    (4)  gy <- g ^ y                           
b <$ {0,1}                  (5)  gz <- g ^ (x * y)                     
pk0 <- pk                   (6)  (m0, m1) <@ A.choose(gx)              
m <- b ? m1 : m0            (7)  b0 <$ {0,1}                           
c <- (g ^ y, pk0 ^ y * m)   (8)  b' <@ A.guess(gy, gz * (b0 ? m1 : m0))
b' <@ A.guess(c)            (9)  b <- b' = b0                          

post = (b'{1} = b{1}) = b{2}
*)

apply wp
apply simp?

(*
pre = (glob A){2} = (glob A){m} /\ (glob A){1} = (glob A){m}

sk0 <$ FDistr.dt            (1)  x <$ FDistr.dt                        
y <$ FDistr.dt              (2)  y <$ FDistr.dt                        
(pk, sk) <- (g ^ sk0, sk0)  (3)  gx <- g ^ x                           
(m0, m1) <@ A.choose(pk)    (4)  gy <- g ^ y                           
b <$ {0,1}                  (5)  gz <- g ^ (x * y)                     
pk0 <- pk                   (6)  (m0, m1) <@ A.choose(gx)              
m <- b ? m1 : m0            (7)  b0 <$ {0,1}                           
c <- (g ^ y, pk0 ^ y * m)   (8)  b' <@ A.guess(gy, gz * (b0 ? m1 : m0))
b' <@ A.guess(c)            (9)                                        

post = (b'{1} = b{1}) = (b'{2} = b0{2})
*)

(* apply (rule callproc_split_result[where ?x1.0="LVariable ''res''" and ?x2.0="LVariable ''res''"])
  close (tactic \<open>Tactic_Inline.assertion_footprint_tac @{context} 1\<close>; simp)
 close (tactic \<open>Tactic_Inline.assertion_footprint_tac @{context} 1\<close>; simp) *)

apply (rule callproc_split_args[where ?x1.0="LVariable ''args''" and ?x2.0="LVariable ''args''"])
      close (tactic \<open>Tactic_Inline.assertion_footprint_tac @{context} 1\<close>; simp)
     close (tactic \<open>Tactic_Inline.assertion_footprint_tac @{context} 1\<close>; simp)
    close 4

apply (rule call_rule_abstract[where globals_f="remdups (vars_proc_global (guess <$> A))"])
close 
using write_vars_proc_global_subset_vars_proc_global close
close
close
close
close
close
close


(* 
  local lemma cpa_ddh0 &m: 
      Pr[CPA(ElGamal,A).main() @ &m : res] =
      Pr[DDH0(DDHAdv(A)).main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 7 -5.
    auto;call (_:true);auto;call (_:true);auto;progress;smt.
  qed.

  local module Gb = {
    proc main () : bool = {
      var x, y, z, m0, m1, b, b';
      x  = $FDistr.dt;
      y  = $FDistr.dt;
      (m0,m1) = A.choose(g^x);
      z  = $FDistr.dt;
      b' = A.guess(g^y, g^z);
      b  = ${0,1};
      return b' = b;
    }
  }.

  local lemma ddh1_gb &m: 
      Pr[DDH1(DDHAdv(A)).main() @ &m : res] = 
      Pr[Gb.main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 3 2;swap{1} [5..6] 2;swap{2} 6 -2.
    auto;call (_:true);wp.
    rnd (fun z, z + log(if b then m1 else m0){2}) 
        (fun z, z - log(if b then m1 else m0){2}).
    auto;call (_:true);auto;progress; (algebra || smt).
  qed.

  axiom Ac_l : islossless A.choose.
  axiom Ag_l : islossless A.guess.

  local lemma Gb_half &m: 
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
    byphoare => //;proc.
    rnd  ((=) b')=> //=.
    call Ag_l;auto;call Ac_l;auto;progress;smt. 
  qed.

  lemma conclusion &m :
    `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r | =
    `| Pr[DDH0(DDHAdv(A)).main() @ &m : res] -  
         Pr[DDH1(DDHAdv(A)).main() @ &m : res] |. 
  proof.
   by rewrite (cpa_ddh0 &m) (ddh1_gb &m) (Gb_half &m).
  qed.
*)

end (* context: group *)

end (* theory *)
