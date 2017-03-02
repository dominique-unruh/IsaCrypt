theory Misc
imports Main Extended_Real_Limits Tools
begin

instantiation "fun" :: (type,zero) zero begin
definition "0 = (\<lambda>x. 0)"
instance ..
end
instantiation "fun" :: (type,plus) plus begin
definition "f + g = (\<lambda>x. f x + g x)"
instance ..
end
instantiation "fun" :: (type,semigroup_add) semigroup_add begin
instance proof
  fix a b c :: "'a\<Rightarrow>'b"
  show "a + b + c = a + (b + c)"
    unfolding plus_fun_def by (rule ext, rule add.assoc)
qed
end
instantiation "fun" :: (type,ab_semigroup_add) ab_semigroup_add begin
instance proof
  fix a b :: "'a\<Rightarrow>'b"
  show "a + b = b + a"
    unfolding plus_fun_def by (rule ext, rule add.commute)
qed
end
instantiation "fun" :: (type,comm_monoid_add) comm_monoid_add begin
instance proof
  fix a :: "'a\<Rightarrow>'b"
  show "0 + a = a"
    unfolding plus_fun_def zero_fun_def by (rule ext, rule add.left_neutral)
qed
end

instantiation bool :: default begin
definition "default_bool = False"
instance by standard
end

lemma setsum_apply: 
  assumes "finite N"
  shows "(\<Sum>n\<in>N. f n) x = (\<Sum>n\<in>N. f n x)"
using assms apply (induction N)
by (auto simp: zero_fun_def plus_fun_def)

lemma SUP_Suc:
  fixes f :: "nat \<Rightarrow> 'a::complete_lattice"
  assumes "mono f"
  shows "(SUP n. f n) = (SUP n. f (Suc n))"
using assms
by (smt SUP_eq bex_UNIV monoD mono_iff_le_Suc order_refl)

lemma mono_apply: 
  assumes "mono f" and "mono g" 
  shows "mono (\<lambda>n. f (g n))"
by (meson assms(1) assms(2) mono_def)

lemma mono_funD: "\<And>x. mono f \<Longrightarrow> mono (\<lambda>i. f i x)"
  unfolding mono_def le_fun_def by auto
lemma mono_funI: "(\<And>x. mono (\<lambda>i. f i x)) \<Longrightarrow> mono f"
  unfolding mono_def le_fun_def by auto

instantiation prod :: (default,default) default begin
definition "default_prod = (default,default)"
instance by intro_classes
end

lemma SUP_multc_ennreal:
  fixes a::"_ \<Rightarrow> ennreal"
  assumes finite: "b < \<infinity>" and notempty: "A \<noteq> {}"
  shows "(SUP i:A. a i*b) = (SUP i:A. a i)*b"
proof (rule SUP_eqI)
  fix i assume "i\<in>A"
  hence "a i \<le> (SUP i:A. a i)"
    by (simp add: SUP_upper)
  thus "a i * b \<le> (SUP i:A. a i) * b"
    by (simp add: mult_right_mono)
next
  fix y assume bound: "\<And>i. i \<in> A \<Longrightarrow> a i * b \<le> y"
  show "(SUP i:A. a i) * b \<le> y" 
  proof (cases "b=0") 
    assume "b=0"
    with bound notempty have "y \<ge> 0" by auto
    with `b=0` show ?thesis by auto
  next
    assume "b\<noteq>0" (* with pos have pos': "b>0" *)
      (* using gr_zeroI by blastx *)
    define y' where "y' == y / b"
    with bound finite `b\<noteq>0` have "\<And>i. i \<in> A \<Longrightarrow> a i \<le> y'"
      using leD le_less_linear
      using divide_less_ennreal by fastforce
    hence "(SUP i:A. a i) \<le> y'" 
      by (simp add: SUP_least)
    thus ?thesis
      unfolding y'_def using finite `b\<noteq>0`
      using divide_less_ennreal leD by fastforce
  qed
qed

lemma SUP_ennreal_mult_left:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "I \<noteq> {}"
  shows "(SUP i:I. c * f i) = c * (SUP i:I. f i)"
    proof (cases "(SUP i: I. f i) = 0")
  case True
  then have "\<And>i. i \<in> I \<Longrightarrow> f i = 0"
    by (metis SUP_upper le_zero_eq)
  with True show ?thesis
    by simp
next
  case False
  then show ?thesis
    apply (subst continuous_at_Sup_mono[where f="\<lambda>x. c * x"])
        using sup_continuous_mono sup_continuous_mult_left_ennreal' close blast
       using sup_continuous_at_left sup_continuous_mult_left_ennreal' close blast
      using assms by auto
qed


lemma sums_ennreal_positive:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "f sums (SUP n. \<Sum>i<n. f i)"
proof -
  have "incseq (\<lambda>i. \<Sum>j=0..<i. f j)"
    using add_mono
    by (auto intro!: incseq_SucI)
  from LIMSEQ_SUP[OF this]
  show ?thesis unfolding sums_def
    by (simp add: atLeast0LessThan)
qed


lemma suminf_ennreal_eq_SUP:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "(\<Sum>x. f x) = (SUP n. \<Sum>i<n. f i)"
  using sums_ennreal_positive[of f, THEN sums_unique]
  thm sums_ereal_positive
  by simp


lemma suminf_upper_ennreal:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "(\<Sum>n<N. f n) \<le> (\<Sum>n. f n)"
  unfolding suminf_ennreal_eq_SUP
  by (auto intro: complete_lattice_class.SUP_upper)


end
