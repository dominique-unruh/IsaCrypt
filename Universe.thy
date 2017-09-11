theory Universe
imports Main BNF_Cardinal_Order_Relation Misc Tools TermX_Antiquot "HOL-Library.Nat_Bijection" "HOL-Library.Rewrite" "HOL-ZF.HOLZF"
begin

(* For proving instances of types declared with 
  "datatype" (not "datatype_new"), see, e.g., "char"

  For proving instances of types declared with 
  "typedef", see, e.g., "ell1"
*)
                                       
(* definition "powertower t == \<forall>n. \<exists>i. inj_on i (Pow (t n)) \<and> i ` (Pow (t n)) \<subseteq> t (Suc n)" *)

    

lemma ZF_Pow_explode: "Pow (explode z) = explode ` explode (Power z)"
proof (rule; rule)
  fix x assume "x \<in> Pow (explode z)" 
  hence "x \<subseteq> explode z" by simp
      
  hence "y \<in> (explode z)" if "y \<in> x" for y  
    using that by blast
  hence yz: "Elem y z" if "y \<in> x" for y
    by (simp add: explode_Elem that) 
      
  define y where "y = Replacement z (\<lambda>t. if (t \<in> x) then Some t else None)"
  have xy: "x = explode y"
    unfolding y_def explode_def Replacement
    using yz by auto 
  have "Elem y (Power z)"
    unfolding y_def
    using Power xy y_def explode_Elem subset_def yz by force
      
  with xy show "x \<in> explode ` explode (Power z)" 
    apply (subst explode_def) by auto
next
  fix x assume "x \<in> explode ` explode (Power z)"
  thus "x \<in> Pow (explode z)"
    using Power explode_Elem subset_def by auto
qed

  
typedef val = "{(x,n) | x n. Elem x ((Power ^^ n) Inf)}" 
  apply (rule exI[of _ "(Empty,0)"])
  by (simp add: Infinity)
(*
Alternatively, val can be axiomatized as follows, which is weaker than the ZF axioms 
(the axiomatization below is implied by existence of a smaller cardinal, namely beth_\<omega>)

typedecl val
axiomatization val_powertower :: "nat \<Rightarrow> val set" where
    val_powertower: "\<exists>i. inj_on i (Pow (val_powertower n)) \<and> i ` (Pow (val_powertower n)) \<subseteq> val_powertower (Suc n)"
and val_powertower_disjoint: "x \<in> val_powertower n \<Longrightarrow> x \<in> val_powertower m \<Longrightarrow> n=m"
and val_powertower_nat: "\<exists>n (i::nat\<Rightarrow>val). inj i \<and> range i \<subseteq> val_powertower n" 
and val_powertower_all: "(\<Union>n. val_powertower n) = UNIV"
*)

    
setup_lifting type_definition_val
definition "val_powertower n = {Abs_val (x,n) | x. Elem x ((Power ^^ n) Inf)}"
lemma val_powertower: "\<exists>i. inj_on i (Pow (val_powertower n)) \<and> i ` (Pow (val_powertower n)) \<subseteq> val_powertower (Suc n)"
proof -
  define D0 where "D0 = Pow (val_powertower n)"
  define i0 where "i0 x = Rep_val ` x" for x
  have "inj_on i0 D0"
    by (metis Rep_val_inverse \<open>i0 \<equiv> op ` Rep_val\<close> inj_on_image inj_on_inverseI)
  define D1 where "D1 = i0 ` D0"
  have D1: "D1 = Pow {(x,n) | x. Elem x ((Power ^^ n) Inf)}" 
    unfolding D1_def i0_def D0_def val_powertower_def
    apply (subst image_Pow_surj) apply rule
    apply (subst image_Collect)
    by (metis (no_types, hide_lams) Domainp.cases Rep_val_inverse cr_val_def val.domain_eq val.pcr_cr_eq)
  define i1 where i1_def: "i1 x = fst ` x" for x :: "(ZF*nat) set"
  have "inj_on i1 D1"
    apply (rule inj_onI) unfolding i1_def D1 
    apply auto
    apply (smt \<open>i1 \<equiv> op ` fst\<close> contra_subsetD fst_conv imageI image_iff mem_Collect_eq old.prod.exhaust prod.inject)
    by (smt \<open>i1 \<equiv> op ` fst\<close> contra_subsetD fst_conv imageI image_iff mem_Collect_eq old.prod.exhaust prod.inject)

  define D2 where "D2 = i1 ` D1" 
  have "D2 = Pow (explode ((Power ^^ n) Inf))"
    unfolding D2_def i1_def D1 explode_def
    apply (subst image_Pow_surj) apply rule
    apply (subst image_Collect) by auto
  hence D2: "D2 = explode ` explode ((Power ^^ Suc n) Inf)"
    unfolding ZF_Pow_explode by simp
      
  define i2 where "i2 = implode"
  have "inj_on i2 D2"
    apply (rule inj_onI) unfolding D2 i2_def by auto

  define D3 where "D3 = i2 ` D2"
  have D3: "D3 = explode ((Power ^^ Suc n) Inf)"
    unfolding D3_def D2 i2_def  image_comp o_def  by simp
  define i3 where "i3 z = Abs_val (z, Suc n)" for z
  have "inj_on i3 D3"
    apply (rule inj_onI)
    unfolding i3_def
    by (metis D3 Domainp.cases Rep_val_inverse cr_val_def explode_Elem prod.sel(1) val.domain_eq val.pcr_cr_eq)
      
  define D4 where "D4 = i3 ` D3" 
  have D4: "D4 = val_powertower (Suc n)" 
    unfolding val_powertower_def D4_def D3 i3_def
    by (simp add: explode_def image_Collect)
      
  define i where "i = i3 o i2 o i1 o i0"
  have inj_i: "inj_on i D0" 
    unfolding i_def 
    apply (rule comp_inj_on, fact \<open>inj_on i0 D0\<close>)
    unfolding D1_def[symmetric]
    apply (rule comp_inj_on, fact \<open>inj_on i1 D1\<close>)
    unfolding D2_def[symmetric]
    apply (rule comp_inj_on, fact \<open>inj_on i2 D2\<close>)
    unfolding D3_def[symmetric]
    by (fact \<open>inj_on i3 D3\<close>)
      
  have i_D0: "i ` D0 = D4" 
    unfolding D4_def D3_def D2_def D1_def i_def by auto
      
  show ?thesis
    apply (rule exI[of _ i])
    using D0_def inj_i i_D0 D4
    by auto
qed
  
lemma val_powertower_disjoint: "x \<in> val_powertower n \<Longrightarrow> x \<in> val_powertower m \<Longrightarrow> n=m"
  using type_definition.Abs_inject type_definition_val val_powertower_def by fastforce
  
lemma val_powertower_nat: "\<exists>n (i::nat\<Rightarrow>val). inj i \<and> range i \<subseteq> val_powertower n"
proof - 
  define i where "i m = Abs_val (nat2Nat m, 0)" for m
  have "inj i" 
    apply (rule injI) unfolding i_def
    apply (subst (asm) Abs_val_inject)
      apply (simp add: Elem_nat2Nat_inf)
     apply (simp add: Elem_nat2Nat_inf)
    by (meson injD inj_nat2Nat old.prod.inject)
      
  moreover have "range i \<subseteq> val_powertower 0"
    unfolding val_powertower_def i_def by auto
      
  ultimately show ?thesis
    by auto
qed
  
lemma val_powertower_all: "(\<Union>n. val_powertower n) = UNIV"
  unfolding val_powertower_def
  apply auto
  by (smt Rep_val Rep_val_inverse mem_Collect_eq)


instantiation val :: equal begin
definition "equal_val (v::val) w = (v=w)"
instance apply intro_classes
  by (simp add: equal_val_def)
end

(* definition "small_cardinal (_::'a itself) = (\<exists>t n (i::'a\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n)" *)

class prog_type = default +
  fixes embedding' :: "('a \<Rightarrow> val) \<times> nat"
  assumes embedding'_range: "range (fst embedding') \<subseteq> val_powertower (snd embedding')"
  assumes inj_embedding': "inj (fst embedding')"
  (* assumes small_cardinal: "\<exists>t n. powertower t \<and> range embedding \<subseteq> t n" *)

definition embedding'_default :: "('a\<Rightarrow>val) \<times> nat" where 
  "embedding'_default == (SOME fn. inj (fst fn) \<and> range (fst fn) \<subseteq> val_powertower (snd fn))"

definition "embedding = fst embedding'" 
(* definition embedding :: "'a::prog_type \<Rightarrow> val" where
  "embedding == (SOME f::'a\<Rightarrow>val. inj f)" *)

lemma embedding_inv [simp]: "(embedding x = embedding y) = (x = y)"
  using inj_embedding' unfolding embedding_def inj_on_def by auto

lemma embedding_inv' [simp]: "inv embedding (embedding x) = x"
  by (metis embedding_inv f_inv_into_f range_eqI)
  
type_synonym 'a val_embedding = "('a\<Rightarrow>val)\<times>nat"

instantiation "nat" :: prog_type begin
definition "(embedding'::nat val_embedding) = embedding'_default"
instance proof (intro_classes, goal_cases)
case 1
  let ?e = "embedding'::nat val_embedding"
  from val_powertower_nat obtain f::"nat\<Rightarrow>val" and n where inj: "inj f" and range: "range f \<subseteq> val_powertower n" by auto
  have theses: "inj (fst ?e) \<and> range (fst ?e) \<subseteq> val_powertower (snd ?e)"
    unfolding embedding'_nat_def embedding'_default_def 
    apply (rule someI[where P="\<lambda>fn. inj (fst fn) \<and> range (fst fn) \<subseteq> val_powertower (snd fn)" and x="(f,n)"])
    using inj range by auto
  thus ?case by simp
case 2 show ?case using theses by simp
qed
end

lemma prog_type_classI':
  assumes "inj (f::'a\<Rightarrow>'b::prog_type)"
  shows "range (fst (embedding'_default::'a val_embedding)) \<subseteq> val_powertower (snd (embedding'_default::'a val_embedding))" and "inj (fst (embedding'_default::'a val_embedding))"
proof -
(*   obtain n where range: "range (embedding::'b\<Rightarrow>val) \<subseteq> val_powertower n"
    using embedding_range by auto *)
  let ?e = "(\<lambda>x. fst embedding' (f x), snd (embedding'::'b val_embedding))"
  let ?e' = "embedding'_default :: 'a val_embedding"
  have theses: "inj (fst ?e) \<and> range (fst ?e) \<subseteq> val_powertower (snd ?e)"
    using assms[THEN injD] embedding'_range inj_embedding'[THEN injD] unfolding inj_on_def apply auto by blast
  have "inj (fst ?e') \<and> range (fst ?e') \<subseteq> val_powertower (snd ?e')"
    unfolding embedding'_default_def 
    apply (rule someI[where P="\<lambda>f. inj (fst f) \<and> range (fst f) \<subseteq> val_powertower (snd f)"])
    by (fact theses)
  then show "range (fst ?e') \<subseteq> val_powertower (snd (embedding'_default::'a val_embedding))" 
       and "inj (fst (embedding'_default::'a val_embedding))"
     by auto
qed

(* Hack to allow to state lemma prog_type_classI. Is there a cleaner way? *)
ML {*  
  val consts_to_unconstrain = [@{const_name embedding'}]
  val consts_orig_constraints = map (Sign.the_const_constraint @{theory}) consts_to_unconstrain
*}
setup {*
  fold (fn c => fn thy => Sign.add_const_constraint (c,NONE) thy) consts_to_unconstrain
*}

lemma prog_type_classI:
  assumes emb: "(embedding'::'a val_embedding) = embedding'_default"
  assumes inj: "inj (f::'a\<Rightarrow>'b::prog_type)"
  shows "OFCLASS('a, prog_type_class)"
apply intro_classes using prog_type_classI'[OF inj] unfolding emb by auto

(* Recover stored type constraints *)
setup {*
  fold2 (fn c => fn T => fn thy => Sign.add_const_constraint (c,SOME (Logic.unvarifyT_global T)) thy)
      consts_to_unconstrain consts_orig_constraints
*}

definition val_powertower_level :: "val \<Rightarrow> nat" where
  "val_powertower_level x = (SOME n. x \<in> val_powertower n)"
lemma val_powertower_level: "x \<in> val_powertower (val_powertower_level x)"
  unfolding val_powertower_level_def apply (rule someI_ex)
  using val_powertower_all by auto

definition val_set_embedding :: "nat \<Rightarrow> val set \<Rightarrow> val" where
  "val_set_embedding n = (SOME f. inj_on f (Pow (val_powertower n)) \<and> f ` Pow (val_powertower n) \<subseteq> val_powertower (Suc n))"
(* definition val_set_embedding_level :: "nat \<Rightarrow> nat" where
  "val_set_embedding_level n == (SOME m. \<forall>x. x \<subseteq> val_powertower n \<longrightarrow> val_set_embedding x \<in> val_powertower m)" *)

lemma val_set_embedding_inj: "inj_on (val_set_embedding n) (Pow (val_powertower n))" (is ?thesis1)
  and val_set_embedding_range: "x \<subseteq> val_powertower n \<Longrightarrow> (val_set_embedding n) x \<in> val_powertower (Suc n)" (is "PROP ?thesis2")
proof -
  obtain f where "inj_on f (Pow (val_powertower n)) \<and> f ` Pow (val_powertower n) \<subseteq> val_powertower (Suc n)"
    apply atomize_elim using val_powertower by simp
  hence "inj_on f (Pow (val_powertower n)) \<and> f ` Pow (val_powertower n) \<subseteq> val_powertower (Suc n)"
    by auto
  hence "inj_on (val_set_embedding n) (Pow (val_powertower n)) \<and> (val_set_embedding n) ` Pow (val_powertower n) \<subseteq> val_powertower (Suc n)"
    unfolding val_set_embedding_def by (rule someI[where P="\<lambda>f. inj_on f (Pow (val_powertower n)) \<and> f ` Pow (val_powertower n) \<subseteq> val_powertower (Suc n)"])
  thus ?thesis1 and "PROP ?thesis2" by auto
qed

instantiation set :: (prog_type) prog_type begin
definition "(embedding' :: 'a set val_embedding) = 
  (\<lambda>M. val_set_embedding (snd (embedding'::'a val_embedding)) (fst (embedding'::'a val_embedding) ` M), 
        Suc (snd (embedding'::'a val_embedding)))"
instance proof
  let ?ea = "embedding' :: 'a val_embedding"
  let ?e = "embedding' :: 'a set val_embedding"
  show "range (fst ?e) \<subseteq> val_powertower (snd ?e)"
    unfolding embedding'_set_def apply auto
    apply (rule val_set_embedding_range[where n="snd ?ea"])
    using embedding'_range by auto
  show "inj (fst ?e)"
    unfolding embedding'_set_def  
    apply simp apply (rule injI)
    apply (frule val_set_embedding_inj[THEN inj_onD])
      using embedding'_range image_subsetI apply auto[2]
    using inj_embedding'[THEN injD] by auto
qed
end

(*instantiation set :: (prog_type) prog_type begin
definition "(embedding :: 'a set \<Rightarrow> val) = embedding_default"
instance proof
  obtain n where range: "range (embedding::'a\<Rightarrow>val) \<subseteq> val_powertower n"
    using embedding_range by auto

  obtain i2::"val set\<Rightarrow>val" where i2inj: "inj_on i2 (Pow (val_powertower n))" 
                                       and i2rng: "i2 ` Pow(val_powertower n) \<subseteq> val_powertower (Suc n)"
    using val_powertower by blast
  define i3 where "i3 \<equiv> \<lambda>s::'a set. i2 (embedding ` s)"
  have "inj i3"
  proof (rule injI, unfold i3_def)
    fix x y :: "'a set"
    from inj_embedding have i: "embedding ` x = embedding ` y \<Longrightarrow> x = y"
      by (metis inj_image_eq_iff)
    show "i2 (embedding ` x) = i2 (embedding ` y) \<Longrightarrow> x = y"
      apply (rule i)
      apply (subst inj_on_eq_iff[symmetric, where f=i2 and A="Pow(val_powertower n)"])
      using i2inj range by auto
  qed
  have i3rng: "range i3 \<subseteq> val_powertower (Suc n)"
  proof (unfold i3_def, auto)
    fix s :: "'a set"
    have "embedding ` s \<in> Pow (val_powertower n)" using range by auto
    hence "i2 (embedding ` s) \<in> i2 ` (Pow (val_powertower n))" by auto
    with i2rng show "i2 (embedding ` s) \<in> val_powertower (Suc n)" by auto
  qed

  let ?e = "embedding::'a set\<Rightarrow>_"
  have ex_emb: "inj i3 \<and> (\<exists>n. range i3 \<subseteq> val_powertower n)"
    using i3rng `inj i3` by auto
  have "inj ?e \<and> (\<exists>n. range ?e \<subseteq> val_powertower n)"
    unfolding embedding_set_def embedding_default_def 
    apply (rule someI[where P="\<lambda>f. inj f \<and> (\<exists>n. range f \<subseteq> val_powertower n)"])
    using ex_emb by simp
  (* thus "inj (embedding::'a set \<Rightarrow> val)" by simp *)
  thus "\<exists>n. range (embedding::'a set\<Rightarrow>val) \<subseteq> val_powertower n"
   and "inj (embedding::'a set\<Rightarrow>val)"  by auto
qed
end*)

instantiation bool :: prog_type begin
definition "(embedding' :: bool val_embedding) = embedding'_default"
instance apply (rule prog_type_classI[OF embedding'_bool_def, of "\<lambda>b. if b then 0 else Suc 0"])
  apply (rule injI)
  by (case_tac x, case_tac y, auto)
end

(* TODO needed? *)
lemma ordered_cardinals: "(\<exists>i::'a\<Rightarrow>'b. inj i) \<or> (\<exists>j::'b\<Rightarrow>'a. inj j)"
proof -
  have leq: "ordLeq2 (card_of (Inl ` UNIV :: ('a+'b)set)) (card_of (Inr ` UNIV :: ('a+'b)set)) \<or>
        ordLeq2 (card_of (Inr ` UNIV :: ('a+'b)set)) (card_of (Inl ` UNIV :: ('a+'b)set))"
        by (rule ordLeq_total, rule card_of_Well_order, rule card_of_Well_order)
  show ?thesis proof (rule leq[THEN disjE], fold card_of_ordLeq)
    assume "\<exists>f::'a+'b \<Rightarrow> 'a+'b. inj_on f (range Inl) \<and> f ` range Inl \<subseteq> range Inr"
    then obtain f::"'a+'b \<Rightarrow> 'a+'b" where finj: "inj_on f (range Inl)" and frng: "f ` range Inl \<subseteq> range Inr" by auto
    define i where "i == \<lambda>x. case f (Inl x) of Inr y \<Rightarrow> y"
    have "inj i" proof (rule injI, unfold i_def) 
      fix x y assume eq:"(case f (Inl x) of Inr y \<Rightarrow> y) = (case f (Inl y) of Inr y \<Rightarrow> y)"
      from frng obtain x' where x': "f (Inl x) = Inr x'" by blast
      from frng obtain y' where y': "f (Inl y) = Inr y'" by blast
      from eq have "f (Inl x) = f (Inl y)" unfolding x' y' by simp
      with finj have "Inl x = Inl y" unfolding inj_on_def by simp
      thus "x = y" by auto
    qed
    thus ?thesis by auto
  next
    assume "\<exists>f::'a+'b \<Rightarrow> 'a+'b. inj_on f (range Inr) \<and> f ` range Inr \<subseteq> range Inl"
    then obtain f::"'a+'b \<Rightarrow> 'a+'b" where finj: "inj_on f (range Inr)" and frng: "f ` range Inr \<subseteq> range Inl" by auto
    define j where "j == \<lambda>x. case f (Inr x) of Inl y \<Rightarrow> y"
    have "inj j" proof (rule injI, unfold j_def) 
      fix x y assume eq:"(case f (Inr x) of Inl y \<Rightarrow> y) = (case f (Inr y) of Inl y \<Rightarrow> y)"
      from frng obtain x' where x': "f (Inr x) = Inl x'" by blast
      from frng obtain y' where y': "f (Inr y) = Inl y'" by blast
      from eq have "f (Inr x) = f (Inr y)" unfolding x' y' by simp
      with finj have "Inr x = Inr y" unfolding inj_on_def by simp
      thus "x = y" by auto
    qed
    thus ?thesis by auto
  qed
qed

function val_embed_up :: "nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> val" where
  "val_embed_up n n x = x"
| "m > n \<Longrightarrow> val_embed_up n m x = val_set_embedding (m-1) {val_embed_up n (m-1) x}"
| "m < n \<Longrightarrow> val_embed_up n m x = undefined"
apply auto apply atomize_elim by auto
termination by lexicographic_order


lemma range_val_embed_up: 
  "m\<ge>n \<Longrightarrow> x \<in> val_powertower n \<Longrightarrow> val_embed_up n m x \<in> val_powertower m"
proof (induction "m-n" arbitrary: m)
case 0 thus ?case by simp
next case (Suc m_n)
  from Suc have "m > n" by auto
  hence m: "m = Suc (m - Suc 0)" by auto
  show ?case
    apply (simp add: \<open>m > n\<close>)
    apply (subst m, rule val_set_embedding_range)
    using Suc by simp
qed

lemma inj_val_embed_up: 
  "m\<ge>n \<Longrightarrow> val_embed_up n m x = val_embed_up n m y \<Longrightarrow>
       x \<in> val_powertower n \<Longrightarrow> y \<in> val_powertower n \<Longrightarrow> x = y"
proof (induction "m-n" arbitrary: m)
case 0 thus ?case by simp
next case (Suc m_n)
  from Suc have "m > n" by auto
  with Suc.prems have set: "val_set_embedding (m-1) {val_embed_up n (m-1) x} = val_set_embedding (m-1) {val_embed_up n (m-1) y}" by auto
  have "{val_embed_up n (m-1) x} = {val_embed_up n (m-1) y}"
    apply (rule val_set_embedding_inj[THEN inj_onD, of "m-1"])
      using set close
    using range_val_embed_up Suc.hyps Suc.prems by auto
  with Suc.hyps(1)[of "m-1"] show ?case apply auto
    by (metis One_nat_def Suc.hyps(2) Suc.prems(3) Suc.prems(4) Suc_diff_Suc \<open>n < m\<close> diff_Suc_1 le_add1 less_imp_Suc_add)
qed

definition val_sum_embedding :: "nat \<Rightarrow> nat \<Rightarrow> val+val \<Rightarrow> val" where
  "val_sum_embedding n m x = (let mn = prod_encode (n,m) in val_set_embedding (Suc mn) (val_set_embedding mn ` 
      (case x of Inl a \<Rightarrow> {{val_embed_up n mn a}} | Inr b \<Rightarrow> {{val_embed_up m mn b},{}})))"
lemma inj_val_sum_embedding: "inj_on (val_sum_embedding n m) (val_powertower n <+> val_powertower m)"
  and range_val_sum_embedding: "x \<in> val_powertower n <+> val_powertower m 
              \<Longrightarrow> val_sum_embedding n m x \<in> val_powertower (prod_encode (n,m) + 2)"
proof -
  have range2: "\<And>x. x \<in> val_powertower n <+> val_powertower m \<Longrightarrow>
           (case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
           \<subseteq> Pow (val_powertower (prod_encode(n,m)))" 
    apply auto 
     close (rule range_val_embed_up, auto intro: le_prod_encode_1)
    by (rule range_val_embed_up, auto intro: le_prod_encode_2)
  have range1: "\<And>x. x \<in> val_powertower n <+> val_powertower m \<Longrightarrow>
           val_set_embedding (prod_encode(n,m)) `
           (case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} 
                   | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
           \<in> Pow (val_powertower (Suc (prod_encode(n,m))))" 
    apply (simp add: image_subset_iff, rule ballI)
    apply (rule val_set_embedding_range)
    using range2 by auto
  have range2: "(case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} 
                         | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
                   \<subseteq> Pow (val_powertower (prod_encode(n,m)))" 
           if "x \<in> val_powertower n <+> val_powertower m" for x
    apply (cases x; simp)
     apply (rule range_val_embed_up) using le_prod_encode_1 that close 2
    apply (rule range_val_embed_up) using le_prod_encode_2 that by auto
  have inj1: "\<And>xa xb. val_embed_up n (prod_encode(n,m)) xa = val_embed_up n (prod_encode(n,m)) xb \<Longrightarrow>
             xa \<in> val_powertower n \<Longrightarrow> xb \<in> val_powertower n \<Longrightarrow> xa = xb" using inj_val_embed_up
    using le_prod_encode_1 by blast
  have inj2: "\<And>ya yb. {{val_embed_up m (prod_encode(n,m)) ya}, {}} = {{val_embed_up m (prod_encode(n,m)) yb}, {}} \<Longrightarrow>
             ya \<in> val_powertower m \<Longrightarrow> yb \<in> val_powertower m \<Longrightarrow> ya = yb"
    by (metis doubleton_eq_iff inj_val_embed_up le_prod_encode_2)
  show "val_sum_embedding n m x \<in> val_powertower (prod_encode(n,m) + 2)"
          if "x \<in> val_powertower n <+> val_powertower m" 
    unfolding val_sum_embedding_def Let_def apply simp
    apply (rule val_set_embedding_range)
    apply (rule image_subset_iff[THEN iffD2, rule_format])
    apply (rule val_set_embedding_range)
    apply (cases x, auto)
     apply (rule range_val_embed_up) using le_prod_encode_1 that close 2
    apply (rule range_val_embed_up) using le_prod_encode_2 that by auto
  show "inj_on (val_sum_embedding n m) (val_powertower n <+> val_powertower m)"
    apply (rule inj_onI) unfolding val_sum_embedding_def Let_def
    apply (subst (asm) val_set_embedding_inj[THEN inj_on_eq_iff])
      close (rule range1, simp)
     close (rule range1, simp)
    apply (subst (asm) val_set_embedding_inj[THEN inj_on_image_eq_iff])
      close (rule range2, simp)
     close (rule range2, simp)
    by (auto intro: inj1 inj2)
qed

instantiation sum :: (prog_type,prog_type) prog_type begin
definition "(embedding' :: ('a+'b) val_embedding) = 
  (\<lambda>x. val_sum_embedding (snd (embedding'::'a val_embedding)) (snd (embedding'::'b val_embedding))
    (map_sum (fst embedding') (fst embedding') x), 
  prod_encode (snd (embedding'::'a val_embedding), snd (embedding'::'b val_embedding)) + 2)"
instance proof (intro_classes, goal_cases)
case 1
  show ?case unfolding embedding'_sum_def 
    apply auto apply (rule range_val_sum_embedding[simplified])
    apply (case_tac xa) using embedding'_range by auto
case 2
  show ?case unfolding embedding'_sum_def
    apply (rule injI) apply simp 
    apply (drule_tac inj_val_sum_embedding[THEN inj_onD])
    unfolding map_sum_def
      close (case_tac x; auto intro!: embedding'_range[unfolded image_subset_iff, rule_format]) 
     close (case_tac y; auto intro!: embedding'_range[unfolded image_subset_iff, rule_format]) 
    apply (case_tac x; case_tac y; simp)
    using inj_embedding'[THEN injD] by auto
qed
end

(*instantiation sum :: (prog_type,prog_type) prog_type begin
instance proof (intro_classes, cases "\<exists>i::'a\<Rightarrow>'b. inj i")
case True
  then obtain i::"'a\<Rightarrow>'b" where "inj i" by auto
  define i2 where "i2 \<equiv> \<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{i a}} | Inr b \<Rightarrow> {{b},{}}"
  have "inj i2" apply (rule injI) unfolding i2_def 
    apply (case_tac x, case_tac y, auto)
    apply (metis `inj i` inj_eq)
    by (case_tac y, auto)
  hence "\<exists>f::'a+'b\<Rightarrow>'b set set. inj f"
    by (rule exI[of _ i2])
  thus "\<exists>t n (i::'a+'b\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    by (rule prog_type_classI')
next 
case False
  with ordered_cardinals obtain i::"'b\<Rightarrow>'a" where "inj i" by auto
  define i2 where "i2 \<equiv> \<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{a},{}} | Inr b \<Rightarrow> {{i b}}"
  have "inj i2" apply (rule injI) unfolding i2_def 
    apply (case_tac x, case_tac y, auto)
    apply (case_tac y, auto)
    by (metis `inj i` inj_eq)
  hence "\<exists>f::'a+'b\<Rightarrow>'a set set. inj f"
    by (rule exI[of _ i2])
  thus "\<exists>t n (i::'a+'b\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    by (rule prog_type_classI')
qed
end*)

definition val_prod_embedding' :: "nat \<Rightarrow> nat \<Rightarrow> val*val \<Rightarrow> val" where
  "val_prod_embedding' n m x = val_set_embedding (prod_encode(n,m) + 2) (val_sum_embedding n m ` {Inl (fst x), Inr (snd x)})"
lemma inj_val_prod_embedding': "inj_on (val_prod_embedding' n m) (val_powertower n \<times> val_powertower m)" (is ?inj)
  and range_val_prod_embedding': "x \<in> val_powertower n \<times> val_powertower m \<Longrightarrow> val_prod_embedding' n m x \<in> val_powertower (prod_encode(n,m) + 3)" (is "?assm \<Longrightarrow> ?range")
proof -
  have range1: "val_sum_embedding n m ` {Inl (fst x), Inr (snd x)} \<in> Pow (val_powertower (prod_encode (n, m) + 2))" 
               if "x \<in> val_powertower n \<times> val_powertower m" for x
    apply auto
     apply (rule range_val_sum_embedding[simplified])
     using that close
    apply (rule range_val_sum_embedding[simplified])
    using that by auto
  have inj1: "inj_on (val_sum_embedding n m) ({Inl (fst x), Inr (snd x)} \<union> {Inl (fst y), Inr (snd y)})" 
             if "x \<in> val_powertower n \<times> val_powertower m" and "y \<in> val_powertower n \<times> val_powertower m" for x y
    apply (rule inj_onI)
    apply (drule inj_val_sum_embedding[THEN inj_onD])
    using that by auto
  show ?inj
    apply (rule inj_onI)
    unfolding val_prod_embedding'_def
    apply (drule val_set_embedding_inj[THEN inj_onD])
      using range1 close 2
    apply (subst (asm) inj_on_Un_image_eq_iff[where f="val_sum_embedding n m"])
     using inj1 close
    by force
  assume ?assm
  show ?range
    unfolding val_prod_embedding'_def
    apply (rewrite at "_ + 3" to "Suc (_ + 2)" eq_reflection) close
    apply (rule val_set_embedding_range)
    using range1[OF `?assm`] by auto
qed

definition val_prod_embedding :: "val\<times>val \<Rightarrow> val" where
  "val_prod_embedding xy = val_prod_embedding' (val_powertower_level (fst xy)) (val_powertower_level (snd xy)) xy"
(* Could be made injective on all val\<times>val, by fixing a monotone nat\<Rightarrow>nat\<Rightarrow>nat: prod_encode *)
lemma inj_val_prod_embedding: "inj val_prod_embedding"
proof (rule injI)
  fix x y :: "val\<times>val"
  assume emb_eq: "val_prod_embedding x = val_prod_embedding y"

  obtain x1 x2 where x: "x=(x1,x2)" by (atomize_elim, auto)
  define n1 n2 
    where "n1 == val_powertower_level x1"
      and "n2 == val_powertower_level x2"
  have "x1 \<in> val_powertower n1"  
   and "x2 \<in> val_powertower n2" unfolding n1_def n2_def by (simp_all add: val_powertower_level) 
  hence x_tower: "x \<in> val_powertower n1 \<times> val_powertower n2" unfolding x by auto
  hence emb_x: "val_prod_embedding' n1 n2 x \<in> val_powertower (prod_encode(n1,n2) + 3)"
    by (rule range_val_prod_embedding')

  obtain y1 y2 where y: "y=(y1,y2)" by (atomize_elim, auto)
  define m1 m2
    where "m1 == val_powertower_level y1"
      and "m2 == val_powertower_level y2"
  have "y1 \<in> val_powertower m1"  
   and "y2 \<in> val_powertower m2" unfolding m1_def m2_def by (simp_all add: val_powertower_level) 
  hence y_tower: "y \<in> val_powertower m1 \<times> val_powertower m2" unfolding y by auto
  hence emb_y: "val_prod_embedding' m1 m2 y \<in> val_powertower (prod_encode(m1,m2) + 3)"
    by (rule range_val_prod_embedding')

  have emb_eq': "val_prod_embedding' n1 n2 x = val_prod_embedding' m1 m2 y"
    using emb_eq unfolding val_prod_embedding_def x y n1_def n2_def m1_def m2_def
    by simp

  from emb_x emb_y have "prod_encode(n1,n2) + 3 = prod_encode(m1,m2) + 3"
    unfolding emb_eq' by (rule val_powertower_disjoint)
  hence eq1: "n1 = m1" and eq2: "n2 = m2"
    by (simp_all add: prod_encode_eq) 

  show "x=y"
    apply (rule inj_val_prod_embedding'[THEN inj_onD])
    using emb_eq' eq1 eq2 x_tower y_tower by auto
qed

lemma range_val_prod_embedding: 
  assumes "x \<in> val_powertower n \<times> val_powertower m"
  shows "val_prod_embedding x \<in> val_powertower (prod_encode(n,m) + 3)"
proof -
  obtain x1 x2 where x: "x=(x1,x2)" by (atomize_elim,auto)
  have n: "n = val_powertower_level x1"
    using assms unfolding x
    using val_powertower_disjoint val_powertower_level by auto
  have m: "m = val_powertower_level x2"
    using assms unfolding x
    using val_powertower_disjoint val_powertower_level by auto
  show ?thesis
    unfolding val_prod_embedding_def 
    using range_val_prod_embedding'[OF assms] 
    unfolding x n m by simp
qed

instantiation prod :: (prog_type,prog_type) prog_type begin
definition "(embedding' :: ('a\<times>'b) val_embedding) = 
  (\<lambda>x. val_prod_embedding (map_prod (fst embedding') (fst embedding') x), 
  prod_encode (snd (embedding'::'a val_embedding), snd (embedding'::'b val_embedding)) + 3)"
instance proof
  let ?e = "embedding'::('a\<times>'b)val_embedding"
  show "range (fst ?e) \<subseteq> val_powertower (snd ?e)"
    apply auto unfolding embedding'_prod_def apply simp
    apply (rule range_val_prod_embedding) apply auto
    using embedding'_range by auto
  show "inj (fst ?e)"
    apply (rule injI)
    unfolding embedding'_prod_def apply simp
    apply (frule inj_val_prod_embedding[THEN injD])
    by (auto simp: inj_embedding' inj_eq)
qed
end

(* instance apply (rule prog_type_classI)
  apply (rule exI[where x="\<lambda>(x::'a,y::'b). {Inl x,Inr y}"])
  apply (rule injI)
  by (case_tac x, case_tac y, auto)
end *)



instantiation "fun" :: (prog_type,prog_type)prog_type begin
definition "(embedding' :: ('a\<Rightarrow>'b) val_embedding) = embedding'_default"
instance apply (rule prog_type_classI[OF embedding'_fun_def, of "\<lambda>f. {(x,f x)| x. True}"])
  by (rule injI, auto)
end

instantiation list :: (prog_type) prog_type begin
definition "(embedding' :: 'a list val_embedding) = embedding'_default"
instance apply (rule prog_type_classI[OF embedding'_list_def, of "\<lambda>l. (length l, nth l)"])
  by (rule injI, metis nth_equalityI old.prod.inject)
end

local_setup {* 
  Local_Theory.define ((@{binding embedding'_UNCONSTRAINED},NoSyn),((@{binding embedding'_UNCONSTRAINED_def},[]),
      Const(@{const_name embedding'},@{typ "'a val_embedding"}))) #> snd
*}

lemma OFCLASS_prog_type_typedef[unfolded embedding'_UNCONSTRAINED_def]:
  fixes Rep::"'a\<Rightarrow>'b::prog_type"
  assumes emb: "(embedding'_UNCONSTRAINED :: 'a val_embedding) \<equiv> (fst embedding' o Rep, snd (embedding'::'b val_embedding))"
  assumes inj: "\<And>x y. (Rep x = Rep y) = (x = y)" 
  shows "OFCLASS('a,prog_type_class)"
proof (intro_classes, fold embedding'_UNCONSTRAINED_def)
  let ?e = "embedding'_UNCONSTRAINED :: 'a val_embedding"
  show "range (fst ?e) \<subseteq> val_powertower (snd ?e)"
    unfolding emb apply simp using embedding'_range by auto
  have "inj Rep" apply (rule injI) using inj by simp
  show "inj (fst ?e)"
    unfolding emb using inj inj_embedding' `inj Rep` by (auto intro: inj_comp)
qed


(*instantiation int::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_int_inject]) end *)

(*
instantiation rat::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_rat_inject]) end
  
instantiation real::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_real_inject]) end
*)

subsection {* Automatically instantiate new types (defined via typedef) *}

ML {*
fun instantiate_prog_type tycon thy =
let val arity = Sign.arity_number thy tycon
    val sorts = replicate arity @{sort "prog_type"}
    val vs = Name.invent_names Name.context "'a" sorts
    val tycon_info = 
      case Typedef.get_info_global thy tycon of
        [info] => info
      | [] => error (tycon^" not defined by typedef")
      | _ => error ("Typedef.get_info_global thy \""^tycon^"\" returns several items")
    val Rep_inject = #Rep_inject (snd tycon_info)
    val rep_type = #rep_type (fst tycon_info)
    val abs_type = #abs_type (fst tycon_info)
    val Rep = Const(#Rep_name (fst tycon_info), abs_type --> rep_type)
    (* val inst_type = Type(tycon,map TFree vs) *)
    val OFCLASS_prog_type_typedef = @{thm OFCLASS_prog_type_typedef} (* Global_Theory.get_thm thy "Universe.OFCLASS_prog_type_typedef" *)
    val lthy = Class.instantiation ([tycon],vs,@{sort "prog_type"}) thy

    val bind = Binding.suffix_name ("_"^(List.last (Long_Name.explode tycon))) @{binding embedding'}
    val rhs = @{termx "(fst embedding' \<circ> (?Rep::?'abs_type::prog_type\<Rightarrow>?'rep_type::prog_type), snd (embedding'::?'rep_type val_embedding))"}
    val ((_,(_,emb_thm)),lthy) = Local_Theory.define ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) lthy
    val emb_thm_global = Proof_Context.export lthy (lthy |> Proof_Context.theory_of |> Proof_Context.init_global) [emb_thm] |> hd

    val OFCLASS_thm = OFCLASS_prog_type_typedef OF [emb_thm_global,Rep_inject]
    val thy = Class.prove_instantiation_exit (fn _ => resolve0_tac [OFCLASS_thm] 1) lthy
in
thy
end;

fun try_instantiate_prog_type tycon thy =
  instantiate_prog_type tycon thy
  handle ERROR _ => (tracing ("Did not instantiate "^tycon^" :: prog_type"); thy)
       | THM _ => (tracing ("Did not instantiate "^tycon^" :: prog_type"); thy);
*}

(* typedef 'a bla = "UNIV::'a set" by auto
(* TODO remove *)
setup {* instantiate_prog_type @{type_name "bla"} *}
 *)

setup {* Typedef.interpretation (Local_Theory.background_theory o try_instantiate_prog_type) *}

subsection {* Instantiation for types not handled by automated mechanism *}

(*instantiation option :: (prog_type)prog_type begin
instance apply (rule prog_type_classI, rule exI[where x="\<lambda>x. case x of Some x \<Rightarrow> Inl x | None \<Rightarrow> Inr ()"])
proof (rule injI) (* Sledgehammer proof *)
  fix x :: "'a option" and y :: "'a option"
  assume a1: "(case x of None \<Rightarrow> Inr () | Some f \<Rightarrow> Inl f) = (case y of None \<Rightarrow> Inr () | Some f \<Rightarrow> Inl f)"
  then obtain esk3\<^sub>1 :: "'a option \<Rightarrow> 'a" where "y = x \<or> None = x \<or> y = None" by (metis option.case(2) option.exhaust sum.sel(1))
  thus "x = y" using a1 by (metis (no_types) Inr_not_Inl option.case_eq_if)
qed
end*)

(*instantiation distr::(prog_type)prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_distr_inject]) end*)

(*instantiation nibble::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_nibble_inject]) end*)

(*instantiation char :: prog_type begin
instance apply (rule prog_type_classI, rule exI[where x=Rep_char])
  by (metis Rep_char_inverse injI)
end*)

end
