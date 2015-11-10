theory Scratch2
imports Procs_Typed
keywords "module" :: thy_decl
     and "end_module" :: thy_decl
begin

print_commands
    
ML {*
type module = {
  name : string list
}

fun module_name ({name=name, ...} : module) = String.concatWith "." (rev name)
*}


ML {*
structure ModuleData = Generic_Data
  (type T = module list
   val empty = []
   val extend = I
   fun merge (_,_) = error ("ModuleData.merge"))
*}
                                             
ML {*

fun begin_module1 (name:string) lthy : local_theory =
  let val _ = @{print} name
      val _ = @{print} lthy
      val module_stack = ModuleData.get (Context.Proof lthy)
      val full_name = case module_stack of [] => [name] | {name=n,...}::_ => name::n
      val new_module = {name=full_name}
      val lthy = ModuleData.map (fn d => new_module::d) (Context.Proof lthy) |> Context.proof_of
  in
  lthy
  end

fun begin_module (name:string) =
  let fun begin stack = 
        let val full_name = case stack of [] => [name] | {name=n,...}::_ => name::n
            val new_module = {name=full_name}
        in new_module::stack end
  in
  Local_Theory.declaration {pervasive=true, syntax=false}
  (fn _ => ModuleData.map begin)
  end

fun end_module lthy =
  let fun endmod [] = error "end_module: no matching module command"
        | endmod (_::rest) = rest
  in
  Local_Theory.declaration {pervasive=true, syntax=false} (fn _ => ModuleData.map endmod) lthy
  end

val _ =
  Outer_Syntax.command @{command_keyword module} "Defines a new module"
    (Parse.name --| Parse.begin
      >> (fn name => Toplevel.local_theory NONE NONE (begin_module name)))
val _ =
  Outer_Syntax.command @{command_keyword end_module} "Finished a module definition"
    (Scan.succeed (Toplevel.local_theory NONE NONE end_module))
*}

module hello begin
module hey begin

end_module
end_module

ML {* ModuleData.get (Context.Proof @{context}) |> hd *}

definition "hello = 3"

end

thm hello_def

module_type MT =
  proc1 :: "(unit,unit) procedure"



locale module =
  fixes M :: MT
begin

definition test1 where
  "test1 = LOCAL (x::unit variable). proc () { x := call proc1<$>M (); return () }"

term test1

ML {* @{term "Scratch.module.test1"} *}

ML {* Syntax.string_of_term @{context} (Const(@{const_name Scratch.module.test1},
  @{typ "(unit, unit) procedure \<Rightarrow> (unit, unit) procedure"}))
|> writeln *}

thm test1_def

find_theorems test1

ML Specification.definition_cmd

ML {* @{term test1} *}

procedure test where
  "test <$> MX = LOCAL x. proc () { x := call proc1<$>MX(); return () }"

term Scratch.module.test
term local.test

end


thm module.test1_def
thm module.test_def

end