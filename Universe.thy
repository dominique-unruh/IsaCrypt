theory Universe
imports Main BNF_Cardinal_Order_Relation Misc Tools TermX_Antiquot Nat_Bijection
begin

(* For proving instances of types declared with 
  "datatype" (not "datatype_new"), see, e.g., "char"

  For proving instances of types declared with 
  "typedef", see, e.g., "ell1"
*)
                                       
(* definition "powertower t == \<forall>n. \<exists>i. inj_on i (Pow (t n)) \<and> i ` (Pow (t n)) \<subseteq> t (Suc n)" *)

typedecl val
axiomatization val_powertower :: "nat \<Rightarrow> val set" where
    val_powertower: "\<exists>i. inj_on i (Pow (val_powertower n)) \<and> i ` (Pow (val_powertower n)) \<subseteq> val_powertower (Suc n)"
and val_powertower_disjoint: "x \<in> val_powertower n \<Longrightarrow> x \<in> val_powertower m \<Longrightarrow> n=m"
and val_powertower_nat: "\<exists>n (i::nat\<Rightarrow>val). inj i \<and> range i \<subseteq> val_powertower n" 
and val_powertower_all: "(\<Union>n. val_powertower n) = UNIV"

instantiation val :: equal begin
definition "equal_val (v::val) w = (v=w)"
instance apply intro_classes by (simp add: equal_val_def)
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
  def i3 == "\<lambda>s::'a set. i2 (embedding ` s)"
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
    def i == "\<lambda>x. case f (Inl x) of Inr y \<Rightarrow> y"
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
    def j == "\<lambda>x. case f (Inr x) of Inl y \<Rightarrow> y"
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

lemma inj_val_embed_up: 
  "m\<ge>n \<Longrightarrow> val_embed_up n m xa = val_embed_up n m xb \<Longrightarrow>
       xa \<in> val_powertower n \<Longrightarrow> xb \<in> val_powertower n \<Longrightarrow> xa = xb"
sorry

definition val_sum_embedding :: "nat \<Rightarrow> nat \<Rightarrow> val+val \<Rightarrow> val" where
  "val_sum_embedding n m x = (let mn = prod_encode (n,m) in val_set_embedding (Suc mn) (val_set_embedding mn ` 
      (case x of Inl a \<Rightarrow> {{val_embed_up n mn a}} | Inr b \<Rightarrow> {{val_embed_up m mn b},{}})))"
lemma inj_val_sum_embedding: "inj_on (val_sum_embedding n m) (val_powertower n <+> val_powertower m)"
  and range_val_sum_embedding: "x \<in> val_powertower n <+> val_powertower m 
              \<Longrightarrow> val_sum_embedding n m x \<in> val_powertower (prod_encode (n,m) + 2)"
proof -
  have range1: "\<And>x. x \<in> val_powertower n <+> val_powertower m \<Longrightarrow>
           val_set_embedding (prod_encode(n,m)) `
           (case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} 
                   | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
           \<in> Pow (val_powertower (Suc (prod_encode(n,m))))" sorry
  have range2: "\<And>x. x \<in> val_powertower n <+> val_powertower m \<Longrightarrow>
           (case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
           \<subseteq> Pow (val_powertower (prod_encode(n,m)))" sorry
  have inj1: "\<And>xa xb. val_embed_up n (prod_encode(n,m)) xa = val_embed_up n (prod_encode(n,m)) xb \<Longrightarrow>
             xa \<in> val_powertower n \<Longrightarrow> xb \<in> val_powertower n \<Longrightarrow> xa = xb" using inj_val_embed_up
    using le_prod_encode_1 by blast
  have inj2: "\<And>ya yb. {{val_embed_up m (prod_encode(n,m)) ya}, {}} = {{val_embed_up m (prod_encode(n,m)) yb}, {}} \<Longrightarrow>
             ya \<in> val_powertower m \<Longrightarrow> yb \<in> val_powertower m \<Longrightarrow> ya = yb"
    by (metis doubleton_eq_iff inj_val_embed_up le_prod_encode_2)
  show "x \<in> val_powertower n <+> val_powertower m \<Longrightarrow> val_sum_embedding n m x \<in> val_powertower (prod_encode(n,m) + 2)" sorry
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
instance sorry
end

(*instantiation sum :: (prog_type,prog_type) prog_type begin
instance proof (intro_classes, cases "\<exists>i::'a\<Rightarrow>'b. inj i")
case True
  then obtain i::"'a\<Rightarrow>'b" where "inj i" by auto
  def i2 == "\<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{i a}} | Inr b \<Rightarrow> {{b},{}}"
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
  def i2 == "\<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{a},{}} | Inr b \<Rightarrow> {{i b}}"
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
lemma inj_val_prod_embedding': "inj_on (val_prod_embedding' n m) (val_powertower n \<times> val_powertower m)"
  and range_val_prod_embedding': "x \<in> val_powertower n \<times> val_powertower m \<Longrightarrow> val_prod_embedding' n m x \<in> val_powertower (prod_encode(n,m) + 3)"
sorry

definition val_prod_embedding :: "val\<times>val \<Rightarrow> val" where
  "val_prod_embedding xy = val_prod_embedding' (val_powertower_level (fst xy)) (val_powertower_level (snd xy)) xy"
(* Could be made injective on all val\<times>val, by fixing a monotone nat\<Rightarrow>nat\<Rightarrow>nat: prod_encode *)
lemma inj_val_prod_embedding: "inj val_prod_embedding"
proof (rule injI)
  fix x y :: "val\<times>val"
  assume emb_eq: "val_prod_embedding x = val_prod_embedding y"

  obtain x1 x2 where x: "x=(x1,x2)" by (atomize_elim, auto)
  def n1 == "val_powertower_level x1"
  def n2 == "val_powertower_level x2"
  have "x1 \<in> val_powertower n1"  
   and "x2 \<in> val_powertower n2" unfolding n1_def n2_def by (simp_all add: val_powertower_level) 
  hence x_tower: "x \<in> val_powertower n1 \<times> val_powertower n2" unfolding x by auto
  hence emb_x: "val_prod_embedding' n1 n2 x \<in> val_powertower (prod_encode(n1,n2) + 3)"
    by (rule range_val_prod_embedding')

  obtain y1 y2 where y: "y=(y1,y2)" by (atomize_elim, auto)
  def m1 == "val_powertower_level y1"
  def m2 == "val_powertower_level y2"
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
