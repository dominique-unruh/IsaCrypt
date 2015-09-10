theory Scratch
imports Main Hoare_Typed
begin

ML {*
  structure Data = Generic_Data
  (type T = thm option
   val empty = NONE
   val extend = I
   fun merge (x,y) = case x of SOME _ => x | NONE => y)

fun update t = 
  let fun decl phi = Data.put (SOME (Morphism.thm phi t))
  in
  Local_Theory.declaration {pervasive=true, syntax=false} decl 
  end

val lookup = Data.get o Context.Proof
*}

ML_val {* lookup @{context} *}

locale hello = fixes x::int
  begin

definition "bla == x"

local_setup {*
  update @{thm bla_def}
*}


ML {* lookup @{context} *}

end

ML {* lookup @{context} *}  

end