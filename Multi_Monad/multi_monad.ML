structure Multi_Monad = struct

type entry = {
  tycon: typ,
  return: cterm,
  bind: cterm,
  return_left: thm,
  return_right: thm,
  bind_comp: thm
};

structure Data = Generic_Data
(
  type T = entry Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
);

fun mk_all name T body = Logic.all_const T $ (Abs(name,T,body))
fun mk_alls [] body = body
  | mk_alls ((name,T)::rest) body = mk_all name T (mk_alls rest body)

(* From functor.ML *)                    
fun term_with_typ ctxt T t =
  Envir.subst_term_types (Sign.typ_match (Proof_Context.theory_of ctxt) (fastype_of t, T) Vartab.empty) t
  handle TYPE_MATCH =>
    raise TYPE ("Term can not be instantiated with right type", [T], [t])

fun generalize t = let
  val tfrees = Term.add_tfrees t [] |> map fst
  in Term_Subst.generalize (tfrees,[]) 0 t end

fun subst_dummyT (Type("dummy",_)) T = T
  | subst_dummyT (Type(n,Ts)) T = Type(n,map (fn T' => subst_dummyT T' T) Ts)
  | subst_dummyT T _ = T

fun monad_cmd (name, raw_tycon, raw_return, raw_bind) lthy  = let
  (* val tycon = Proof_Context.read_type_name {proper=true, strict=true} lthy raw_tycon |> dest_Type |> fst *)
  val tycon = Proof_Context.read_typ lthy raw_tycon |> @{print}
  val return = Syntax.read_term lthy raw_return |> generalize
  val bind = Syntax.read_term lthy raw_bind |> generalize
  val return_ct = Thm.cterm_of lthy return
  val bind_ct = Thm.cterm_of lthy bind
  val sort = @{sort type}
  val [aT,bT,cT] = Variable.invent_types [sort,sort,sort] lthy |> fst |> map TFree
  fun m T = subst_dummyT tycon T
  (* val aMT = Type(tycon,[aT]) *)
  (* val bMT = Type(tycon,[bT]) *)
  fun invent n = Name.invent (Variable.names_of lthy) n 1 |> hd
  val x = Free (invent "x",aT)
  val f = Free (invent "f",aT-->m bT) |> @{print}
  val g = Free (invent "g",bT-->m cT)
  val mm = Free (invent "m",m aT)
  val return_a = term_with_typ lthy (aT-->m aT) return 
  val bind_a_b = term_with_typ lthy (m aT-->(aT-->m bT)-->m bT) bind
  val bind_a_a = term_with_typ lthy (m aT-->(aT-->m aT)-->m aT) bind
  val bind_b_c = term_with_typ lthy (m bT-->(bT-->m cT)-->m cT) bind
  val bind_a_c = term_with_typ lthy (m aT-->(aT-->m cT)-->m cT) bind
  val return_left = HOLogic.mk_eq (bind_a_b $ (return_a $ x) $ f, f $ x) |> HOLogic.mk_Trueprop
  val return_right = HOLogic.mk_eq (bind_a_a $ mm $ return_a, mm) |> HOLogic.mk_Trueprop
  val bind_comp = HOLogic.mk_eq (
      bind_b_c $ (bind_a_b $ mm $ f) $ g,
      bind_a_c $ mm $ (absfree (dest_Free x) (bind_b_c $ (f $ x) $ g))
    ) |> HOLogic.mk_Trueprop
  val _ = Thm.cterm_of lthy return_left |> @{print}
  fun after_qed [[return_left_thm, return_right_thm, bind_comp_thm]] lthy = let
    (* val _ = @{print} return_left_thm *)
    fun map_symtab phi context = let
      val entry = {
        tycon = tycon, return = Morphism.cterm phi return_ct, bind = Morphism.cterm phi bind_ct,
        return_left = Morphism.thm phi return_left_thm,
        return_right = Morphism.thm phi return_right_thm,
        bind_comp = Morphism.thm phi bind_comp_thm }
      in (Data.map (Symtab.update_new (Binding.name_of name, entry)) context) end
    val lthy = Local_Theory.declaration {syntax=false, pervasive=false} map_symtab lthy
    (* val _ = Context.Proof lthy |> Data.get |> Symtab.dest |> @{print} *)
    in
      lthy
    end
    | after_qed _ _ = raise ERROR "monad_cmd: internal error"
  val lthy = Proof.theorem NONE after_qed [map (fn t => (t, []))  [return_left,return_right,bind_comp]] lthy
  in
    lthy
  end

fun print_functors ctx = 
  (Symtab.dest (Data.get (Context.Proof ctx)) |> @{print}; ())
  
val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword monad}
    "register a monad"
    (((Parse.binding --| @{keyword ":"}) -- Parse.type_const -- Parse.term -- Parse.term) 
        >> (fn (((name,tycon),return),bind) => monad_cmd (name,tycon,return,bind)))


end