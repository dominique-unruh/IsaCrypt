theory Scratch
imports Main Procs_Typed
begin


abbreviation "gX == Variable ''gX'' :: int variable"

(*
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
lemma set_filter_empty: "Set.filter f {} = {}" by auto
lemma set_filter_union: "Set.filter f (x\<union>y) = Set.filter f x \<union> Set.filter f y" by auto
*)

lemma vars_proc_global_locals: "{x \<in> set (vars_proc_global p). \<not> vu_global x} = {}"
  unfolding vars_proc_global_def by auto

default_sort prog_type

procedure testproc where
  "testproc <$> abc = LOCAL a x. proc(a) { gX := $x; return $x }" 

lemma mk_procthm_body:
  assumes "p = \<lparr>p_body = body, p_args = x, p_return = y\<rparr>"
  shows "p_body p == body" 
using assms by simp

lemma mk_procthm_return:
  assumes "p = \<lparr>p_body = body, p_args = x, p_return = ret\<rparr>"
  shows "p_return p == ret" 
using assms by simp

lemma mk_procthm_args:
  assumes "p = \<lparr>p_body = body, p_args = args, p_return = ret\<rparr>"
  shows "p_args p == args" 
using assms by simp

lemmas return = mk_procthm_return[OF testproc_def]

ML "open Conv"
ML {*
val unfold_return = Conv.top_sweep_conv (K (Conv.rewr_conv @{thm return})) @{context};;
val simp = Simplifier.rewrite @{context};;
val c = unfold_return then_conv simp;;
@{cterm "set (e_vars (p_return (testproc<$>abc)))"} |> c *}

thm testproc_def
thm mk_procthm_body[OF testproc_def]
thm testproc_def[THEN mk_procthm_body]
thm mk_procthm_return[OF testproc_def]

find_theorems "_=_ \<Longrightarrow> _==_"

thm local_vars_def[THEN eq_reflection]

ML {*
fun register_procedure_thm thm lthy = 
  let val body = thm RS @{thm mk_procthm_body}
      val return = thm RS @{thm mk_procthm_return}
      val args = thm RS @{thm mk_procthm_args}
      fun unfold th = top_sweep_conv (K (rewr_conv th)) lthy
      val pattern = body |> Thm.concl_of |> Logic.dest_equals |> fst |> Term.dest_comb |> snd
      val return_vars = @{termx "set (e_vars (p_return (?pattern::(?'a::procargs, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold return then_conv Simplifier.rewrite lthy)
(*      val body_vars = @{termx "set (vars (p_body (?pattern::(?'a::procargs, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold body then_conv Simplifier.rewrite lthy) *)
      val simpset = lthy addsimps @{thms vars_proc_global_locals}
      val body_local_vars = @{termx "set (local_vars (p_body (?pattern::(?'a::procargs, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold body
                then_conv unfold @{thm local_vars_def[THEN eq_reflection]} 
                then_conv Simplifier.rewrite simpset)
      val name = Procs_Typed.procedure_head_of pattern
  in
  Procs_Typed.register_procedure name {
    pattern=Thm.cterm_of lthy pattern,
    body=SOME body, return=SOME return, args=SOME args,
    body_local_vars=SOME body_local_vars, return_vars=SOME return_vars
  } lthy
  end
*}

local_setup {* register_procedure_thm @{thm testproc_def} *}

ML {* Procs_Typed.get_procedure_info @{context} true @{term "testproc <$> x"} *}

end