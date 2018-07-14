structure Do_Notation = struct

type monad = {bind : term, return : term}


structure Data = Generic_Data
(
  type T = monad Name_Space.table
  val empty = Name_Space.empty_table "monad"
  val extend = I
  val merge = Name_Space.merge_tables
);

fun add_monad' ctx binding monad table =
  Name_Space.define ctx false (binding,monad) table |> snd

fun add_monad_global binding monad thy = 
  Context.theory_map (Data.map (add_monad' (Context.Theory thy) binding monad)) thy

fun map_monad phi {bind,return} : monad = {bind=Morphism.term phi bind, return=Morphism.term phi return}

fun add_monad binding monad lthy =
  Local_Theory.declaration {syntax=false, pervasive=false} (fn phi => fn context => 
    Data.map (add_monad' context binding (map_monad phi monad)) context) lthy

(* val monad_table : monad Name_Space.table = Name_Space.empty_table "monad"
|> add_monad @{binding list} {bind = Const(@{const_name List.bind},dummyT),
                              return = Abs ("", dummyT, Const(@{const_name Cons},dummyT) $ Bound 0 $ Const (@{const_name Nil},dummyT))}
 *)

(* fun get_bind ctx name = Name_Space.get monad_table name |> #bind *)

fun lookup_monad ctx n pos = Name_Space.check (Context.Proof ctx) (Data.get (Context.Proof ctx)) (n,@{print} pos)
fun lookup_monad_term ctx (Free(n,_)) = (@{print}1;lookup_monad ctx n Position.none)
  | lookup_monad_term ctx (Const ("_constrain", _) $ Free (n, _) $ typ) = (
    case Term_Position.decode_position typ of
      SOME (pos, _) => lookup_monad ctx n pos
    | NONE => lookup_monad ctx n Position.none)
  | lookup_monad_term _ t = raise TERM ("lookup_monad_term", [t])

fun dummifyT ctx (T as TFree(n,_)) = 
    (case Variable.def_sort ctx (n,~1) of SOME _ => T | NONE => dummyT)
  | dummifyT _ (TVar _) = dummyT
  | dummifyT ctx (Type(n,Ts)) = Type(n,map (dummifyT ctx) Ts)
fun dummify ctx (Free(n,T)) = Free(n,dummifyT ctx T)
  | dummify ctx (Const(n,T)) = Const(n,dummifyT ctx T)
  | dummify ctx (Var(n,T)) = Var(n,dummifyT ctx T)
  | dummify ctx (t$u) = dummify ctx t $ dummify ctx u
  | dummify ctx (Abs(n,T,t)) = Abs(n,dummifyT ctx T,dummify ctx t)
  | dummify _ (t as Bound _) = t


end