theory Hoare_Typed
imports Lang_Typed Hoare_Untyped
begin

section {* Concrete syntax *}

syntax "_hoare" :: "(memory \<Rightarrow> bool) \<Rightarrow> program_syntax \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> term"
          ("hoare {(_)}/ (2_)/ {(_)}")
syntax "_memory" :: memory ("&m")

parse_translation {*
  let
  fun trans_assert _ _ m (Const("_var_access",_)$v) =
             Const(@{const_syntax memory_lookup},dummyT) $ Bound m $ v
    | trans_assert ctx known m (Const("_memory",_)) = Bound m
    | trans_assert ctx known m (v as Free(vn,_)) =
          if is_program_variable ctx (!known) vn then
             Const(@{const_syntax memory_lookup},dummyT) $ Bound m $ v
          else v
    | trans_assert ctx known m (Const("_constrain",_)$p$_) = trans_assert ctx known m p
    | trans_assert ctx known m (p$q) = trans_assert ctx known m p $ trans_assert ctx known m q
    | trans_assert ctx known m (Abs(n,T,t)) = Abs(n,T,trans_assert ctx known (m+1) t)
    | trans_assert _ _ _ e = e

  fun trans_assert' _ _ (e as Abs _) = e
    | trans_assert' _ _ (e as Const("_constrainAbs",_) $ Abs _ $ _) = e
    | trans_assert' ctx known e =
        let val e = trans_assert ctx known 0 e
        in Abs("mem",dummyT,e) end

  fun trans_hoare ctx P c Q =
    let val known = Unsynchronized.ref []
        val c = translate_program ctx known c
        val P = (trans_assert' ctx known P)
        val Q = trans_assert' ctx known Q
    in Const(@{const_syntax Hoare_Untyped.hoare},dummyT) $ P $ c $ Q end
  in
    [("_hoare", fn ctx => fn [P,c,Q] => trans_hoare ctx P c Q)]
  end
*}

print_translation {*
  let
    fun trans_hoare_back ctx P c Q =
      Const("_hoare",dummyT) $ P $ translate_program_back ctx c $ Q
  in
    [(@{const_syntax hoare}, fn ctx => fn [P,c,Q] => trans_hoare_back ctx P c Q)]
  end
*}

section {* Rules *}

lemma assign_rule:
  fixes P Q c x
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update m x (e_fun e m))"
  shows "hoare {P &m} x := \<guillemotleft>e\<guillemotright> {Q &m}"
  unfolding assign_def
  apply (rule assign_rule)
  using assms unfolding memory_update_def by auto

lemma while_rule:
  fixes P Q I c e
  assumes "hoare {I &m \<and> e_fun e &m} \<guillemotleft>p\<guillemotright> {I &m}"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. \<not> e_fun e m \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare {P &m} while (\<guillemotleft>e\<guillemotright>) \<guillemotleft>p\<guillemotright> {Q &m}"
  unfolding while_def 
  apply (rule while_rule[where I=I])
  using assms unfolding e_fun_bool_untyped.

lemma iftrue_rule:
  fixes P Q I e p1 p2
  assumes "hoare {P &m} \<guillemotleft>p1\<guillemotright> {Q &m}"
          "\<forall>m. P m \<longrightarrow> e_fun e m"
  shows "hoare {P &m} if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>p1\<guillemotright> else \<guillemotleft>p2\<guillemotright> {Q &m}"
  unfolding ifte_def 
  apply (rule iftrue_rule)
  using assms by auto

lemma iffalse_rule:
  fixes P Q I e p1 p2
  assumes "hoare {P &m} \<guillemotleft>p2\<guillemotright> {Q &m}"
          "\<forall>m. P m \<longrightarrow> \<not> e_fun e m"
  shows "hoare {P &m}   if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>p1\<guillemotright> else \<guillemotleft>p2\<guillemotright>   {Q &m}"
  unfolding ifte_def 
  apply (rule iffalse_rule)
  using assms by auto

text {* The following rules from Hoare_Untyped also directly apply to typed Hoare triples\<in>

- seq_rule
- true_rule
- skip_rule
- conseq_rule
- case_rule
*}

end
