theory Universe
imports Main Ell1
begin
                                       
definition "powertower t == \<forall>n. \<exists>i. inj_on i (Pow (t n)) \<and> i ` (Pow (t n)) \<subseteq> t (Suc n)"

typedecl val;
axiomatization where
  powertower_nat: "\<exists>t n (i::nat\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n" 

instantiation val :: equal begin
definition "equal_val (v::val) w = (v=w)"
instance apply intro_classes by (simp add: equal_val_def)
end

class prog_type = default +
  assumes small_cardinal: "\<exists>t n (i::'a\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"

definition embedding :: "'a::prog_type \<Rightarrow> val" where
  "embedding == (SOME f::'a\<Rightarrow>val. inj f)"

lemma embedding_inv [simp]: "(embedding x = embedding y) = (x = y)"
  apply (rule inj_eq) unfolding embedding_def
  apply (rule someI_ex[of "\<lambda>f. inj f"]) using small_cardinal
  by auto

instantiation "nat" :: prog_type begin
instance apply intro_classes using powertower_nat by auto
end

lemma prog_type_classI':
  assumes "\<exists>f::'a\<Rightarrow>'b::prog_type. inj f"
  shows "\<exists>t n (i::'a\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
proof -
  obtain t n and i::"'b\<Rightarrow>val" where "powertower t" and "inj i" and "range i \<subseteq> t n"
    using small_cardinal by auto
  obtain f::"'a\<Rightarrow>'b" where "inj f" using assms by auto
  show "\<exists>t n (i::'a\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    apply (rule exI[where x=t])
    apply (rule exI[where x=n])
    apply (rule exI[where x="i o f"], auto) 
    apply (fact `powertower t`)
    apply (metis (mono_tags, hide_lams) `inj i` `inj f` comp_apply injI inj_eq)
    by (metis `range i \<subseteq> t n` range_eqI subsetCE)
qed 

instantiation set :: (prog_type) prog_type begin
instance proof
  obtain t n and i::"'a\<Rightarrow>val" where pow: "powertower t" and "inj i" and irng: "range i \<subseteq> t n"
    using small_cardinal by auto
  from pow obtain i2::"val set\<Rightarrow>val" where i2inj: "inj_on i2 (Pow (t n))" and i2rng: "i2 ` Pow(t n) \<subseteq> t (Suc n)"
    unfolding powertower_def by blast
  def i3 == "\<lambda>s. i2 (i ` s)"
  have "inj i3"
  proof (rule injI, unfold i3_def)
    fix x y 
    from `inj i` have i: "i ` x = i ` y \<Longrightarrow> x = y"
      by (metis inj_image_eq_iff)
    show "i2 (i ` x) = i2 (i ` y) \<Longrightarrow> x = y"
      apply (rule i)
      apply (subst inj_on_eq_iff[symmetric, where f=i2 and A="Pow(t n)"])
      using i2inj apply simp_all
      by (metis Pow_UNIV Pow_iff image_Pow_surj image_iff irng subset_UNIV subset_trans)+
  qed
  have i3rng: "range i3 \<subseteq> t (Suc n)"
  proof (unfold i3_def, auto)
    fix s
    have "i ` s \<in> Pow (t n)" using irng by auto
    hence "i2 (i ` s) \<in> i2 ` (Pow (t n))" by auto
    with i2rng show "i2 (i ` s) \<in> t (Suc n)" by auto
  qed
  show "\<exists>t n (i::'a set\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    apply (rule exI)+
    apply (rule conjI, fact pow)
    apply (rule conjI, fact `inj i3`)
    by (fact i3rng)    
qed
end

lemma prog_type_classI:
  assumes "\<exists>f::'a\<Rightarrow>'b::prog_type. inj f"
  shows "OFCLASS('a, prog_type_class)"
apply intro_classes using assms by (rule prog_type_classI')

instantiation unit :: prog_type begin;
instance apply (rule prog_type_classI) by (rule exI, rule injI, simp)
end

instantiation bool :: prog_type begin
instance apply (rule prog_type_classI, rule exI[where x="\<lambda>b. if b then 0 else Suc 0"])
  apply (rule injI)
  by (case_tac x, case_tac y, auto)
end

lemma ordered_cardinals: "(\<exists>i::'a\<Rightarrow>'b. inj i) \<or> (\<exists>j::'b\<Rightarrow>'a. inj j)"
  sorry (* card_of_ordLeq BNF_Cardinal_Order_Relation *)

instantiation sum :: (prog_type,prog_type) prog_type begin
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
end

instantiation prod :: (prog_type,prog_type) prog_type begin
instance apply (rule prog_type_classI)
  apply (rule exI[where x="\<lambda>(x::'a,y::'b). {Inl x,Inr y}"])
  apply (rule injI)
  by (case_tac x, case_tac y, auto)
end


instantiation "fun" :: (prog_type,prog_type)prog_type begin;
instance
  apply (rule prog_type_classI)
  apply (rule exI[where x="\<lambda>f. {(x,f x)| x. True}"])
  by (rule injI, auto)
end

instantiation int :: prog_type begin;
instance
  apply (rule prog_type_classI)
  apply (rule exI[where x="\<lambda>n. if n \<ge> 0 then Inl (nat n) else Inr (nat (-n))"])
  apply (rule injI)
  by (metis Inl_Inr_False int_nat_eq minus_minus minus_zero nat_0 nat_0_iff nat_int neg_le_iff_le sum.inject(1) sum.inject(2))
end

instantiation rat :: prog_type begin
instance apply (rule prog_type_classI) apply (rule exI[where x=Rep_rat])
  by (metis Rep_rat_inverse inj_on_def)
end

instantiation real :: prog_type begin
instance apply (rule prog_type_classI)
  apply (rule exI[where x=Rep_real])
  by (metis Rep_real_inverse inj_on_inverseI)
end

instantiation "distr" :: (prog_type)prog_type begin
instance apply (rule prog_type_classI, rule exI[where x="Rep_distr"])
  by (metis Rep_distr_inverse injI)
end


end

