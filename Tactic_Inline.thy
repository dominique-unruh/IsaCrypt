theory Tactic_Inline
imports RHL_Typed Hoare_Tactics Procs_Typed Legacy_Char
begin

(*definition "HIDDEN_EQ = op="
lemma HIDDEN_EQ_refl: "HIDDEN_EQ x x" unfolding HIDDEN_EQ_def ..
lemma HIDDEN_EQ_I': "HIDDEN_EQ a b \<Longrightarrow> a==b" by (simp add: HIDDEN_EQ_def)
lemma HIDDEN_EQ_ok:
  shows "HIDDEN_EQ procargvars_empty procargvars_empty" 
  and   "HIDDEN_EQ v w \<Longrightarrow> HIDDEN_EQ (procargvars_add (LVariable n) v) (procargvars_add (LVariable n) w)"
  and   "HIDDEN_EQ v w \<Longrightarrow> HIDDEN_EQ (procargvars_add (Variable n) v) (procargvars_add (Variable n) w)"
unfolding HIDDEN_EQ_def by simp_all *)
 
(* lemma obs_eq'_rename_variables_proc:
  assumes "obs_eq' V (callproc x (rename_local_variables_proc ren prc) args) body"
  shows "obs_eq' V (callproc x prc args) body"
using assms unfolding obs_eq'_def obs_eq_def rhoare_def denotation_callproc_rename_local_variables_proc .

thm obs_eq'_rename_variables_proc[of _ _ "[]"]
 *)

locale callproc_conditions_simp begin

(* TODO remove ? *)
definition "filter_global' == filter vu_global"
definition "filter_local' == filter (\<lambda>x. \<not> vu_global x)"


lemma local_variable_name_renaming_nil: "local_variable_name_renaming [] ` x == x" 
  unfolding local_variable_name_renaming_def[THEN ext] by auto

(* lemma local_variable_name_renaming2: "local_variable_name_renaming (a#b) ` X == local_variable_name_renaming b ` local_variable_name_renaming1 a ` X" 
  unfolding local_variable_name_renaming_def
  by (simp add: o_def image_image) *)

lemma local_variable_name_renaming_union: "local_variable_name_renaming (a#b) ` (A \<union> B) == local_variable_name_renaming (a#b) ` A \<union> local_variable_name_renaming (a#b) ` B"
  by (simp add: image_Un)

lemma local_variable_name_renaming_insert: "local_variable_name_renaming (a#b) ` (insert x X) == insert (local_variable_name_renaming (a#b) x) (local_variable_name_renaming (a#b) ` X)"
  by simp

lemma local_variable_name_renaming_set: "local_variable_name_renaming (a#b) ` (set X) == set (map (local_variable_name_renaming (a#b)) X)"
  by simp

lemma local_variable_name_renaming_cons: "map (local_variable_name_renaming (a#b)) (x#X) == local_variable_name_renaming (a#b) x # map (local_variable_name_renaming (a#b)) X"
  by simp

lemma local_variable_name_renaming_nil2: "map (local_variable_name_renaming R) [] == []"
  by simp


lemma callproc_goal4: "local_variable_name_renaming ren ` filter_global X \<subseteq> Y \<union> Collect vu_global"
  unfolding filter_global_def by auto

(*lemma callproc_conditions_simp1b: "local_variable_name_renaming ren ` filter_global X \<subseteq> Y \<union> Collect vu_global == True"
  apply (rule eq_reflection) unfolding filter_global_def by auto

lemma callproc_conditions_simp1c: "local_variable_name_renaming1 ren ` filter_global X \<subseteq> Y \<union> Collect vu_global == True"
  apply (rule eq_reflection)
  by (auto simp: filter_global_def local_variable_name_renaming1_fix_globals)*)

lemma filter_global': "filter_global (set X) == set (filter_global' X)"
  unfolding filter_global_def filter_global'_def by simp

lemma filter_local': "filter_local (set X) == set (filter_local' X)"
  unfolding filter_local_def filter_local'_def by simp

lemma filter_global'_nil: "filter_global' [] == []"
  unfolding filter_global'_def by simp
lemma filter_global_empty: "filter_global {} == {}"
  unfolding filter_global_def by simp


lemma filter_global'_cons1: "filter_global' (mk_variable_untyped (Variable n :: 'a::prog_type variable) # X) ==
                             mk_variable_untyped (Variable n :: 'a variable) # filter_global' X"
  unfolding filter_global'_def by auto 
lemma filter_global_insert1: "filter_global (insert (mk_variable_untyped (Variable n :: 'a::prog_type variable)) X) ==
                             insert (mk_variable_untyped (Variable n :: 'a variable)) (filter_global X)"
  apply (rule eq_reflection) unfolding filter_global_def by auto 

lemma filter_global'_cons2: "filter_global' (mk_variable_untyped (LVariable n :: 'a::prog_type variable) # X) ==
                             filter_global' X"
  unfolding filter_global'_def by auto 
lemma filter_global_insert2: "filter_global (insert (mk_variable_untyped (LVariable n :: 'a::prog_type variable)) X) ==
                             filter_global X"
  apply (rule eq_reflection) unfolding filter_global_def by auto 

lemma filter_local'_nil: "filter_local' [] == []"
  unfolding filter_local'_def by simp
(* lemma filter_local_empty: "filter_local {} == {}"
  unfolding filter_local_def by simp *)

lemma filter_local'_cons1: "filter_local' (mk_variable_untyped (LVariable n :: 'a::prog_type variable) # X) ==
                             mk_variable_untyped (LVariable n :: 'a variable) # filter_local' X"
  unfolding filter_local'_def by auto 
(* lemma filter_local_insert1: "filter_local (insert (mk_variable_untyped (LVariable n :: 'a::prog_type variable)) X) ==
                             insert (mk_variable_untyped (LVariable n :: 'a variable)) (filter_local X)"
  unfolding filter_local_def apply auto
  by (smt Collect_cong LVariable_local insert_Collect)  *)

lemma filter_local'_cons2: "filter_local' (mk_variable_untyped (Variable n :: 'a::prog_type variable) # X) ==
                             filter_local' X"
  unfolding filter_local'_def by auto 
(* lemma filter_local_insert2: "filter_local (insert (mk_variable_untyped (Variable n :: 'a::prog_type variable)) X) ==
                             filter_local X"
  unfolding filter_local_def by auto  *)

lemma filter_local_union: "filter_local (X \<union> Y) == filter_local X \<union> filter_local Y"
  apply (rule eq_reflection) unfolding filter_local_def by auto

lemma filter_local_insert1: "filter_local (insert (mk_variable_untyped (LVariable n :: 'a::prog_type variable)) X) == 
      insert (mk_variable_untyped (LVariable n :: 'a::prog_type variable)) (filter_local X)"
  apply (rule eq_reflection) unfolding filter_local_def by auto
  
lemma filter_local_insert2: "filter_local (insert (mk_variable_untyped (Variable n)) X) == filter_local X"
  apply (rule eq_reflection) unfolding filter_local_def by auto
  
lemma filter_local_empty: "filter_local {} == {}"
  apply (rule eq_reflection) unfolding filter_local_def by auto

lemma local_variable_name_renaming_same: 
  "local_variable_name_renaming ((a,b)#X) (mk_variable_untyped (LVariable a :: 'a::prog_type variable))
      == local_variable_name_renaming X (mk_variable_untyped (LVariable b :: 'a variable))"
  by (subst Rep_rename_local_variables_var[symmetric], simp)

lemma local_variable_name_renaming_id: 
  "local_variable_name_renaming [] x == x"
  unfolding local_variable_name_renaming_def by simp

lemma local_variable_name_renaming_notsame: 
  assumes "a\<noteq>x" and "b\<noteq>x"
  shows "local_variable_name_renaming ((a,b)#X) (mk_variable_untyped (LVariable x :: 'a::prog_type variable))
      == local_variable_name_renaming X (mk_variable_untyped (LVariable x :: 'a variable))"
  apply (subst Rep_rename_local_variables_var[symmetric])
  apply (subst rename_local_variables_var_notsame)
  using assms by simp_all

(* lemmas callproc_conditions_simp =  
  filter_global' filter_global'_cons1 filter_global'_cons2
  filter_global'_nil filter_local_union filter_local' vars_variable_pattern[THEN eq_reflection]
  filter_local'_cons1 filter_local'_cons2 filter_local'_nil filter_local_insert1
  filter_local_empty local_variable_name_renaming_insert local_variable_name_renaming_union
  local_variable_name_renaming_nil local_variable_name_renaming_same image_empty[THEN eq_reflection]
  vars_unit_pattern[THEN eq_reflection] vars_pair_pattern[THEN eq_reflection] 
  append_Cons[THEN eq_reflection] append_Nil[THEN eq_reflection]
  rename_local_variables_pattern_id[THEN eq_reflection] local_variable_name_renaming_id
  local_variable_name_renaming_set local_variable_name_renaming_cons 
  local_variable_name_renaming_nil2 local_variable_name_renaming_notsame

 *)



end

ML_file "tactic_inline.ML"
                                                                    
method_setup inline = {*
  Args.term >> (fn proc => fn ctx => (METHOD (fn facts => Tactic_Inline.inline_tac ctx facts proc 1)))
*} "inlines procedure body"

end