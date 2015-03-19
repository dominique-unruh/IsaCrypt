theory Setsum_Infinite
imports Main Topological_Spaces Extended_Sorry
begin

typedef 'a finite_set = "{S::'a set. finite S}" by auto
definition fset :: "'a finite_set \<Rightarrow> 'a set" where
  "fset S = Rep_finite_set S";

instantiation finite_set :: (type) order
begin
definition less_eq_finite_set where "A \<le> B \<longleftrightarrow> fset A \<le> fset B"
definition less_finite_set where "A < B \<longleftrightarrow> fset A < fset B"
instance 
apply intro_classes
apply (metis less_eq_finite_set_def less_finite_set_def less_le_not_le)
apply (metis less_eq_finite_set_def order_refl)
apply (metis le_iff_inf le_infI2 less_eq_finite_set_def)
by (metis fset_def Rep_finite_set_inject eq_iff less_eq_finite_set_def)
end

instantiation finite_set :: (type) semilattice_inf begin
definition inf_finite_set where "inf A B = Abs_finite_set (inf (fset A) (fset B))"
instance 
  apply intro_classes
  apply (unfold inf_finite_set_def less_eq_finite_set_def fset_def)
  apply (metis Abs_finite_set_inverse Int_lower1 Rep_finite_set finite_Int mem_Collect_eq)
  apply (metis Abs_finite_set_inverse Int_lower1 Rep_finite_set finite_Int inf_commute mem_Collect_eq)
  by (metis Abs_finite_set_inverse Rep_finite_set finite_Int le_inf_iff mem_Collect_eq)
end

instantiation finite_set :: (type) semilattice_sup begin
definition sup_finite_set where "sup A B = Abs_finite_set (sup (fset A) (fset B))"
instance
  apply intro_classes
  apply (unfold sup_finite_set_def less_eq_finite_set_def fset_def)
  apply (metis Abs_finite_set_inverse Rep_finite_set finite_Un mem_Collect_eq sup_ge1)
  apply (metis Abs_finite_set_inverse Rep_finite_set finite_Un mem_Collect_eq sup.commute sup_ge1)
  by (metis Abs_finite_set_inverse Rep_finite_set mem_Collect_eq rev_finite_subset sup.boundedI)
end

instantiation finite_set :: (type) distrib_lattice begin
instance apply intro_classes
  apply (unfold sup_finite_set_def inf_finite_set_def fset_def)
  apply (subst Abs_finite_set_inverse)
  apply (metis Rep_finite_set finite_Int mem_Collect_eq)
  by (metis Abs_finite_set_inverse Rep_finite_set finite_Un mem_Collect_eq sup_inf_distrib1)
end

instantiation finite_set :: (type) bounded_lattice_bot
begin
definition bot_finite_set where "bot = Abs_finite_set bot"
instance
by (intro_classes, metis (mono_tags, hide_lams) Abs_finite_set_inverse fset_def bot_finite_set_def equals0D finite.emptyI less_eq_finite_set_def mem_Collect_eq subsetI)
end;

instantiation finite_set :: (type) minus
begin
definition minus_finite_set where "A - B = Abs_finite_set (fset A - fset B)"
instance ..
end;



definition SetSums_to :: "('a \<Rightarrow> 'b::{t2_space,comm_monoid_add}) \<Rightarrow> ('a set) \<Rightarrow> 'b \<Rightarrow> bool" where
  "SetSums_to f A b = ((\<lambda>S. setsum f (A \<inter> fset S)) ---> b) (at_top) ";

definition SetSums :: "('a \<Rightarrow> 'b::{t2_space,comm_monoid_add}) \<Rightarrow> ('a set) \<Rightarrow> bool" where
  "SetSums f A = (\<exists>b. SetSums_to f A b)";

definition SetSum :: "('a \<Rightarrow> 'b::{t2_space,comm_monoid_add}) \<Rightarrow> ('a set) \<Rightarrow> 'b" where
  "SetSum f A = (THE b. SetSums_to f A b)";

lemma at_top_neq_bot_finite_set: "(at_top::'a finite_set filter) \<noteq> bot"
unfolding at_top_def
unfolding filter_eq_iff
apply (subst eventually_INF_base)
apply auto
apply (metis sup.cobounded2 sup_ge1)
by (metis not_empty_eq_Ici_eq_empty principal_eq_bot_iff trivial_limit_def)

lemma setsum_def_alt: "SetSums_to f A b \<longleftrightarrow> (\<forall>U. open U \<longrightarrow> b \<in> U \<longrightarrow> (\<exists>B0. finite B0 \<and> (\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U)))"
proof -
  have setsums_unfold: "SetSums_to f A b \<longleftrightarrow> 
        (\<forall>U. open U \<longrightarrow> b \<in> U \<longrightarrow> (\<exists>B0. \<forall>B\<in>{B0..}. setsum f (A \<inter> fset B) \<in> U))"
    unfolding SetSums_to_def trivial_limit_def tendsto_def at_top_def 
    apply (subst eventually_INF_base)
    apply (metis empty_not_UNIV)
    apply (metis UNIV_I atLeast_subset_iff le_inf_iff principal_le_iff sup.cobounded2 sup_ge1)
    unfolding eventually_principal
    by simp;
  have dir1: "\<And>U. (\<exists>B0. \<forall>B\<in>{B0..}. setsum f (A \<inter> fset B) \<in> U) \<Longrightarrow>
             (\<exists>B0. finite B0 \<and> (\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U))" 
  proof -
    fix U
    assume "\<exists>B0. \<forall>B\<in>{B0..}. setsum f (A \<inter> fset B) \<in> U"
    then obtain B0' where B0': "\<forall>B'\<in>{B0'..}. setsum f (A \<inter> fset B') \<in> U" by auto
    def B0 == "fset B0'"
    have "finite B0" by (metis B0_def fset_def Rep_finite_set mem_Collect_eq) 
    have "\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U" 
    proof (rule,rule)
      fix B::"'a set" assume finB: "finite B" and B_B0: "B\<in>{B0..}"
      def B' == "Abs_finite_set B"
      from B0' have "setsum f (A \<inter> fset B') \<in> U"
        by (metis Abs_finite_set_inverse B'_def B0_def B_B0 fset_def atLeast_iff finB less_eq_finite_set_def mem_Collect_eq)
      with fset_def finB B'_def show "setsum f (A \<inter> B) \<in> U"
        by (metis Abs_finite_set_inverse mem_Collect_eq) 
    qed
  with `finite B0` show "\<exists>B0. finite B0 \<and> (\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U)" by auto
  qed
  have dir2: "\<And>U. (\<exists>B0. finite B0 \<and> (\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U)) \<Longrightarrow>
             (\<exists>B0'. \<forall>B'\<in>{B0'..}. setsum f (A \<inter> fset B') \<in> U)"
  proof -
    fix U assume "\<exists>B0. finite B0 \<and> (\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U)"
    then obtain B0 where finB0: "finite B0" and B_B0: "\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U" by auto
    def B0' == "Abs_finite_set B0"
    have "\<forall>B'\<in>{B0'..}. setsum f (A \<inter> fset B') \<in> U"
      by (metis Abs_finite_set_cases Abs_finite_set_inverse B0'_def B_B0 fset_def atLeast_def finB0 less_eq_finite_set_def mem_Collect_eq) 
    thus "\<exists>B0'. \<forall>B'\<in>{B0'..}. setsum f (A \<inter> fset B') \<in> U" ..
  qed
  from dir1 dir2 have dir12: "\<And>U. (\<exists>B0. \<forall>B\<in>{B0..}. setsum f (A \<inter> fset B) \<in> U) \<longleftrightarrow>
             (\<exists>B0. finite B0 \<and> (\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U))" ..
  from setsums_unfold show "SetSums_to f A b \<longleftrightarrow> (\<forall>U. open U \<longrightarrow> b \<in> U \<longrightarrow> (\<exists>B0. finite B0 \<and> (\<forall>B\<in>{B0..}. finite B \<longrightarrow> setsum f (A \<inter> B) \<in> U)))"
    unfolding dir12 .
qed

lemma setsum_0: "SetSums_to (\<lambda>x. 0) UNIV 0"
  by (auto simp: setsum_def_alt)

end
