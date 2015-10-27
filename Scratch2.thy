theory Scratch2
imports RHL_Typed Hoare_Tactics Procs_Typed Tactic_Inline 
begin

ML {* @{term "1==1"} *}


ML "Binding.empty"

local_setup {*
fn ctx => 
let val tac = ALLGOALS (simp_tac ctx)
    val method : Method.text = tac
                 |> SIMPLE_METHOD |> K |> Method.Basic
    fun eq_sch n t = Logic.mk_implies (Logic.mk_equals (Free(n,@{typ int}), Var((n,0),@{typ int})), t)
    val st = Proof.theorem NONE (fn thms => fn ctx => (@{print} thms; ctx)) 
      [[(eq_sch "X" @{prop "X==1+0+0::int"},[])],[(eq_sch "X" @{prop "X==1+0::int"},[])]] ctx
    val st' = Proof.apply method st |> Seq.hd
    val ctx = Proof.global_done_proof st'
in
ctx
end
*}

schematic_lemma
  assumes "X = ?X"
  shows "X = 1"
  and "X = 2"

end
