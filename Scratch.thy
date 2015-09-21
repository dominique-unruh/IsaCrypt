theory Scratch
imports Lang_Typed
begin

term "proc() { skip; return 1 }"
term "proc(a) { skip; return 1 }"
term "proc(a,b,c) { skip; return 1 }"
term "PROGRAM [ x := call f() ]"                        
term "PROGRAM [ (x,y) := call f(1) ]"
term "PROGRAM [ x := call f(1,2) ]"

class testclass =
  fixes hmpf :: "'a"
  assumes finite_UNIV': "finite (UNIV \<Colon> 'a set)"
print_theorems

locale xxx begin

typedef 'a x = "UNIV::'a set" ..

lemma tc: "class.testclass TYPE('a::finite xxx.x)"
  sorry

lemma tc2: "OFCLASS('a::finite xxx.x, testclass_class)"
  apply (rule Scratch.class.Scratch.testclass.of_class.intro)
  by (fact tc)

ML {*
fun inst thy =
  let fun tac ctx = print_tac ctx "goal" 
              THEN rtac @{thm tc2} 1
      val lthy = Class.instantiation ([@{type_name xxx.x}], [("'a",@{sort finite})], @{sort testclass}) thy
      val thy = Class.prove_instantiation_exit tac lthy
  in
  thy
  end
*}

declare[[show_sorts=true]]
local_setup "Local_Theory.background_theory inst"

end


lemma "OFCLASS(xxx.x, testclass_class)"
  by (tactic \<open>rtac @{thm Scratch.class.Scratch.testclass.of_class.intro} 1\<close>)

instantiation xxx.x :: testclass begin
instance by intro_classes
end

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


default_sort prog_type

procedure testproc where
  "testproc <$> abc = LOCAL a x. proc(a) { gX := $x; return $x }" 



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
*}


local_setup {* Procs_Typed.register_procedure_thm @{thm testproc_def} *}

ML {* Procs_Typed.get_procedure_info @{context} true @{term "testproc <$> x"} *}

end