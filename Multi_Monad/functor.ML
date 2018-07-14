structure Functor = struct

type functr = {
  name: binding,
  tycon: typ, (* With dummyT for the type argument *)
  operations: cterm Symtab.table,
  laws: thm Symtab.table
}

type template = {
  name: binding,
  operations: (string*typ) list,
  laws: (string*term) list
}

type data = {
  (* Invariants: Binding.name_of (#name (Symtab.lookup templates x)) = x *)
  templates: template Symtab.table,
  (* Invariants: Binding.name_of (#name (Symtab.lookup functors x)) = x *)
  functors: functr Symtab.table
}

structure Data = Generic_Data
(
  type T = data
  val empty = {templates=Symtab.empty, functors=Symtab.empty}
  val extend = I
  fun merge (data1, data2) = 
    {templates=Symtab.merge (K true) (#templates data1, #templates data2),
      functors=Symtab.merge (K true) (#functors data1, #functors data2)}
);

fun add_template_map (template:template) ({templates,functors}:data) : data = 
  {templates=Symtab.update_new (#name template |> Binding.name_of, template) templates, functors=functors}

fun add_template_global template = 
  Context.theory_map (Data.map (add_template_map template))

fun add_functor_map (functr:functr) ({functors,templates}:data) : data =
  {templates=templates, functors=Symtab.update_new (#name functr |> Binding.name_of, functr) functors}

fun add_functor_global name tycon (operations:(string*term) list) thy = let
  fun mk_op (n,t) = (n, Thm.global_cterm_of thy t)
  val functr = {name=name, operations=operations |> map mk_op |> Symtab.make, laws=Symtab.empty} : functr
  in Context.theory_map (Data.map (add_functor_map functr)) end

fun print_templates ctx = let
  val templates = Context.Proof ctx |> Data.get |> #templates |> Symtab.dest
  fun print_template (_,template:template) = let
    val _ = #name template |> Binding.print |> writeln
    val _ = #operations template |> app (writeln o Syntax.string_of_term ctx o Const)
    val _ = #laws template |> app (fn (name,prop) => name ^ ": " ^ Syntax.string_of_term ctx prop |> writeln)
    in () end
  val _ = app print_template templates
in () end

end
