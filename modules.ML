(** Module types **)

type module_type_spec_raw = 
  { mt_name: binding,
    mt_args: (binding*string) list,
    mt_proctypes: (binding*string) list,
    mt_touching: string option
  };
type module_type_spec = 
  { mt_name: binding,
    mt_const: term option,
    mt_args: (string*term) list,
    mt_touching: term option,
    mt_proctypes: (binding*string list*typ) list,
    mt_def_thm : thm option,
    mt_getter_def_thms : (binding*string list*term*typ*thm) list
  };


fun mk_id n = HOLogic.mk_list @{typ string} (map HOLogic.mk_string n)

local
fun optionT t = Type(@{type_name option},[t]);
fun Some x = let val t = fastype_of x in Const(@{const_name Some},t --> optionT t) $ x end

fun fun_upd f x y = 
  let val tx = fastype_of x
      val ty = fastype_of y 
  in
  Const(@{const_name fun_upd}, (tx --> ty) --> tx --> ty --> (tx --> ty)) $ f $ x $ y
  end                   

fun empty_map t1 t2 = Abs ("x", t1, Const (@{const_name None}, optionT t2))
in
fun alist_to_HOL_map t1 t2 l = fold (fn (x,y) => fn m => 
  fun_upd m x (Some y)) l (empty_map t1 t2);
end;

local
fun procedure_type pt =
  Const (@{const_name procedure_type}, Term.itselfT pt --> @{typ procedure_type}) $
     Const(@{const_name Pure.type}, Term.itselfT pt);

in
fun mk_module_type (spec:module_type_spec) =
(* TODO: check if names unique *)
let val args = alist_to_HOL_map @{typ string} @{typ module_type}
               (map (fn (n,mt) => (HOLogic.mk_string n,mt)) (#mt_args spec))
    val procT = #mt_proctypes spec |>
                map (fn (_,n,pt) => (mk_id n, procedure_type pt)) |>
                alist_to_HOL_map @{typ "string list"} @{typ procedure_type}
    val mt = @{term ModuleType} $ args $ procT
    val mt = if #mt_touching spec = NONE then mt
             else Const(@{const_name ignore},fastype_of (the (#mt_touching spec)) --> @{typ module_type} --> @{typ module_type})
                  $ the (#mt_touching spec) $ mt
in
  mt
end 
end

fun update_mt_def_thm ({mt_name,mt_args,mt_proctypes,mt_def_thm=_,mt_getter_def_thms,mt_const,mt_touching}:module_type_spec) mt_def_thm =
   {mt_name=mt_name,mt_args=mt_args,mt_proctypes=mt_proctypes,mt_def_thm=mt_def_thm,mt_getter_def_thms=mt_getter_def_thms,mt_const=mt_const,mt_touching=mt_touching}
fun update_mt_const ({mt_name,mt_args,mt_proctypes,mt_def_thm,mt_getter_def_thms,mt_const=_,mt_touching}:module_type_spec) mt_const =
   {mt_name=mt_name,mt_args=mt_args,mt_proctypes=mt_proctypes,mt_def_thm=mt_def_thm,mt_getter_def_thms=mt_getter_def_thms,mt_const=mt_const,mt_touching=mt_touching}
fun update_mt_getter_def_thms ({mt_name,mt_args,mt_proctypes,mt_def_thm,mt_getter_def_thms=_,mt_const,mt_touching}:module_type_spec) mt_getter_def_thms =
   {mt_name=mt_name,mt_args=mt_args,mt_proctypes=mt_proctypes,mt_def_thm=mt_def_thm,mt_getter_def_thms=mt_getter_def_thms,mt_const=mt_const,mt_touching=mt_touching}


fun read_term_T ctx T term = Syntax.parse_term ctx term 
                             |> Type.constraint T
                             |> Syntax.check_term ctx

val parse_module_subtyping = Parse.$$$ ":" || (Parse.$$$ "<" --| Parse.$$$ ":")

(* Parses (A<:MT1,B<:MT2,...)  --or A:MT1 etc*)
val parse_module_type_args : (binding*string) list parser = 
  Parse.$$$ "(" |-- Parse.!!! (Parse.enum "," (Parse.binding --| parse_module_subtyping -- Parse.term)) --| Parse.$$$ ")"

(* Parses "name(A<:MT1,B<:MT2,...) where a :: type" *)
val parse_module_type : module_type_spec_raw parser = 
  Parse.binding -- (* moduletype MT *) 
  Scan.optional parse_module_type_args [] -- (* (A<:MT) *)
  Scan.option (@{keyword "attach"} |-- Parse.!!! Parse.term) --
  (@{keyword "where"} |-- (Parse.and_list (Parse.binding --| Parse.$$$ "::" -- Parse.typ)))
  >> (fn (((name,args),touching),procs) => { mt_name=name, mt_proctypes=procs, mt_args=args, mt_touching=touching });

fun module_type_spec_process 
    ({mt_name=name, mt_args=args, mt_proctypes=procs, mt_touching=touching}:module_type_spec_raw) 
    lthy : module_type_spec =
{mt_name=name, 
 mt_args=map (fn (n,t) => (Binding.name_of n,read_term_T lthy @{typ module_type} t)) args,
 mt_proctypes=map (fn (n,t) => (n,Long_Name.explode (Binding.name_of n), Syntax.read_typ lthy t)) procs,
 mt_def_thm=NONE, mt_getter_def_thms=[], mt_const=NONE,
 mt_touching=Option.map (Syntax.read_term lthy) (touching)
}

(* TODO: Should replace . by _ in getter_name? *)
fun mk_getter_name (mt:module_type_spec) name = 
Binding.qualify true (Binding.name_of(#mt_name mt)) name


fun getter_lemma_prop (_:local_theory) (mt:module_type_spec) (_,name,getter_const,procT,_) = 
  let val prem = @{term "has_module_type M"} $ the (#mt_const mt)
      val lhs = @{term "get_proc_in_module M"} $ mk_id name
      val rhs = @{term "Some::procedure_rep\<Rightarrow>_"} $ (Const(@{const_name mk_procedure_untyped}, procT--> @{typ procedure_rep}) $ (getter_const $ @{term "M::module"}))
      val concl = @{term "op= :: procedure_rep option \<Rightarrow> _ \<Rightarrow> _"} $ lhs $ rhs
      val prop = @{term "op==>"} $ HOLogic.mk_Trueprop prem $ HOLogic.mk_Trueprop concl
(*        val prop = cterm_of (Proof_Context.theory_of lthy) prop *)
  in
    prop
  end;

fun getter_lemma_tac mt getter_def {context=ctx,...} = 
  Raw_Simplifier.rewrite_goal_tac ctx [getter_def] 1
  THEN print_tac ctx "after: unfold getter_def"
  THEN rtac @{thm get_proc_in_module'} 1
  THEN print_tac ctx "after: get_proc_in_module'"
  THEN Raw_Simplifier.rewrite_goal_tac ctx [#mt_def_thm mt |> the] 1
  THEN print_tac ctx "after: unfold MT_def"
  THEN atac 1
  THEN print_tac ctx "after: assumption"
  THEN simp_tac ctx 1
  THEN print_tac ctx "after: simp"

fun getter_lemma_thm (getter as (bind,_,_,_,def_thm)) (lthy,mt) = 
  let val prop = getter_lemma_prop lthy mt getter
      val thm = Goal.prove lthy ["M"] [] prop (getter_lemma_tac mt def_thm)
      val thm_name = mk_getter_name mt bind
      val (_,lthy:local_theory) = Local_Theory.note ((thm_name,[]),[thm]) lthy
  in
  (lthy,mt)
  end;

(* For debugging purposes only *)
val last_defined_module_type = Unsynchronized.ref NONE

fun define_module_type_getter (name_bind, name:string list, procT) 
                              (lthy, mt:module_type_spec) : (local_theory*module_type_spec)=
  let val getter_name = mk_getter_name mt name_bind
      val getter_def = Const(@{const_name get_proc_in_module'},@{typ id} --> @{typ module} --> procT)
                       $ mk_id name
      val ((getter_const,(_,thm)),lthy) = Local_Theory.define ((getter_name, NoSyn),
          ((Thm.def_binding getter_name,[]), getter_def)) lthy
      val mt : module_type_spec = update_mt_getter_def_thms mt ((name_bind,name,getter_const,procT,thm) :: #mt_getter_def_thms mt)
  in (lthy,mt) end

fun define_module_type (spec_raw:module_type_spec_raw) lthy =
  let val mt = module_type_spec_process spec_raw lthy
      val ((const,(_,thm)),lthy) = Local_Theory.define ((#mt_name mt, NoSyn), 
                           ((Binding.suffix_name "_def_raw" (#mt_name mt),[]), mk_module_type mt)) lthy 
      val thm = Simplifier.rewrite_rule lthy @{thms ignore_def} thm
      val _ = @{print} thm
      val (_,lthy) = Local_Theory.note ((Thm.def_binding (#mt_name mt),[]),[thm]) lthy
      val mt : module_type_spec = update_mt_def_thm mt (SOME thm)
      val mt : module_type_spec = update_mt_const mt (SOME const)
      val (lthy,mt) = if (#mt_args mt=[]) 
                      then fold define_module_type_getter (#mt_proctypes mt) (lthy,mt) 
                      else (lthy,mt)
      val (lthy,mt) = if (#mt_args mt=[])
                      then fold getter_lemma_thm (#mt_getter_def_thms mt) (lthy,mt)
                      else (lthy,mt)
      val _ = (last_defined_module_type := SOME mt)
  in
  lthy
  end;


Outer_Syntax.local_theory @{command_spec "moduletype"} "Declares a module type"
  (parse_module_type >> define_module_type)

