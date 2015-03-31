theory TermX_Antiquot
imports Main
begin

ML_file "termx_antiquot.ML"

setup {* ML_Antiquotation.inline @{binding termx} TermX_Antiquot.termx_antiquot *}

setup {* ML_Antiquotation.inline @{binding typx} TermX_Antiquot.typx_antiquot *}

typedecl int 
typedecl 'a list

consts XXX :: "'a \<Rightarrow> 'b \<Rightarrow> int"

declare[[ML_exception_trace=false]]

class test1
class test2


(*
typedecl int
ML {* let val x = @{term "xx::int"} val a = @{typ "int"} in cterm_of @{theory} @{termx "x==?x::?'a"} end *}

ML {*
local
val src = "@{termx \"?x::?'x.1==y\"}"
val ((_,body),_) = ML_Context.eval_antiquotes (ML_Lex.read @{here} src, @{here}) (SOME (Context.Proof @{context}))
in
(*val _ = writeln (ML_Lex.flatten env) *)
val _ = writeln (ML_Lex.flatten body)
end
*}
*)


end
