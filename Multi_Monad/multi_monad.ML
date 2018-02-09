structure Multi_Monad = struct

type entry = { 
  tycon: xstring,
  return: cterm,
  bind: cterm,
  return_left: thm
};

structure Data = Generic_Data
(
  type T = entry Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
);

fun monad_cmd (raw_tycon, raw_return, raw_bind) lthy  = let
  val tycon = Proof_Context.read_type_name {proper=true, strict=true} lthy raw_tycon |> dest_Type |> fst
  val return = Syntax.read_term lthy raw_return
  val bind = Syntax.read_term lthy raw_bind
  val return_ct = Thm.cterm_of lthy return
  val bind_ct = Thm.cterm_of lthy bind
  val aT = @{typ 'a}
  val bT = @{typ 'b}
  val aMT = Type(tycon,[aT])
  val bMT = Type(tycon,[bT])
  val return_left = Logic.all_const aT $ Abs("x",aT, Logic.all_const (aT-->bMT) $ Abs("f",aT-->bMT, HOLogic.mk_Trueprop (
        HOLogic.mk_eq (bind $ (return $ Bound 1) $ Bound 0, Bound 0 $ Bound 1))))
  val return_right = Logic.all_const aT
  val _ = Thm.cterm_of lthy return_left |> @{print}
  fun after_qed [[return_left_thm]] lthy = let
    (* val _ = @{print} return_left_thm *)
    fun map_symtab phi context = let
      val entry = { tycon = tycon, return = Morphism.cterm phi return_ct, bind = Morphism.cterm phi bind_ct,
        return_left = Morphism.thm phi return_left_thm }
      in (Data.map (Symtab.update_new (tycon, entry)) context) end
    val lthy = Local_Theory.declaration {syntax=false, pervasive=false} map_symtab lthy
    val _ = Context.Proof lthy |> Data.get |> Symtab.dest |> @{print}
    in
      lthy
    end
    | after_qed _ _ = raise ERROR "internal error"
  val lthy = Proof.theorem NONE after_qed (map (fn t => [(t, [])]) [return_left]) lthy
  in
    lthy
  end

fun print_functors ctx = 
  (Symtab.dest (Data.get (Context.Proof ctx)) |> @{print}; ())
  
val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword monad}
    "register a monad"
    ((Parse.type_const -- Parse.term -- Parse.term) 
        >> (fn ((tycon,return),bind) => monad_cmd (tycon,return,bind)))


end