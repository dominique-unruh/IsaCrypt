structure Lang_Syntax =
struct

(* Parser for programs *)

  fun get_var_name (Free(v,_)) = v
    | get_var_name (Const("_constrain",_)$p$_) = get_var_name p
    | get_var_name v = raise (TERM ("not a variable",[v]))

  fun add_var known (Free(v,_)) = (if not (member (op=) (!known) v) then known := v :: !known else ())
    | add_var known (Const("_constrain",_)$p$_) = add_var known p
    | add_var _ _ = ()

  fun is_program_variable ctx (v:string list) (c:string) = 
        if member (op=) v c then true
        else
          (case Proof_Context.read_const {proper = true, strict = false} ctx c of
             Const(_,Type(@{type_name variable},_)) => true
           | _ => false)
          handle ERROR _ => false

  local
  (* known = known variables names *)
  fun get_variable_names' _ _ l (Const("_var_access",_)$v) = 
        (case v of (Const("_constrain",_) $ (v' as Free(vn,_)) $ _) => (vn,v')::l
                 | (Const("_constrain",_) $ v' $ _) => ("var",v')::l
                 | v' => ("var",v')::l)
    | get_variable_names' ctx known l (v as Free(vn,_)) = if is_program_variable ctx (!known) vn then (vn,v)::l else l
    | get_variable_names' ctx known l (Const("_constrain",_)$p$_) = get_variable_names' ctx known l p
    | get_variable_names' ctx known l (p$q) = let val l'=get_variable_names' ctx known l p in get_variable_names' ctx known l' q end
    | get_variable_names' ctx known l (Abs(_,_,t)) = get_variable_names' ctx known l t
    | get_variable_names' _ _ l _ = l
  fun get_variable_names ctx known e = distinct (op=) (get_variable_names' ctx known [] e)

  fun replace_variable i v e =
    if e=v then Bound i else case e of
      (Const("_var_access",_) $ e) => replace_variable i v e
    | e$f => replace_variable i v e $ replace_variable i v f
    | Abs(n,T,t) => Abs(n,T,replace_variable (i+1) v t)
    | e => e

  fun abstract_variable (vn,v) e = Abs(vn,dummyT,replace_variable 0 v e)
  fun apply_expression (_,v) e = Const(@{const_name apply_expression},dummyT) $ e $ v


  in

  fun translate_expression ctx known (e:term) = 
    let val vars = get_variable_names ctx known e
        val rev_vars = rev vars
        val e = fold abstract_variable rev_vars e
        val e = Const(@{const_name const_expression},dummyT) $ e
        val e = fold apply_expression vars e
    in e end


  fun translate_program (ctx:Proof.context) known (p:term) =
    let fun trargs (Const("_procedure_call_args_none",_)) = Const(@{const_name procargs_empty},dummyT)
          | trargs (Const("_procedure_call_args_single",_)$x) = 
              (Const(@{const_name procargs_add},dummyT) $ translate_expression ctx known x $ Const(@{const_name procargs_empty},dummyT))
          | trargs (Const("_procedure_call_args_cons",_)$x$xs) = 
              (Const(@{const_name procargs_add},dummyT) $ translate_expression ctx known x $ trargs xs)
          | trargs t = raise (TERM ("trargs",[t]))
        fun trans (Const("_assign",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax assign},dummyT) $ x $ translate_expression ctx known e)
          | trans (Const("_assign_quote",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax assign},dummyT) $ x $ e)
          | trans (Const("_sample",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax sample},dummyT) $ x $ translate_expression ctx known e)
          | trans (Const("_sample_quote",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax sample},dummyT) $ x $ e)
          | trans (Const("_label",_) $ Free(l,_) $ p) = 
                Const(@{const_syntax label},dummyT) $ HOLogic.mk_string l $ trans p
          | trans (Const("_label",_) $ (Const("_constrain",_)$Free(l,_)$_) $ p) = 
                Const(@{const_syntax label},dummyT) $ HOLogic.mk_string l $ trans p
          | trans (Const("_label",_) $ l $ _) = raise (ERROR ("Label must be just an identifier, not "^(@{make_string} l)))
          | trans (Const("_quote",_) $ p) = p
          | trans (Const("_while",_) $ e $ p) =
                 Const(@{const_syntax while},dummyT) $ (translate_expression ctx known e) $ trans p
          | trans (Const("_while_quote",_) $ e $ p) =
                 Const(@{const_syntax while},dummyT) $ e $ trans p
          | trans (Const("_ifthen",_) $ e $ p) =
                 Const(@{const_syntax ifte},dummyT) $ (translate_expression ctx known e) $ trans p $ Const(@{const_syntax skip},dummyT) 
          | trans (Const("_ifte",_) $ e $ p $ q) =
                 Const(@{const_syntax ifte},dummyT) $ (translate_expression ctx known e) $ trans p $ trans q
          | trans (Const("_ifthen_quote",_) $ e $ p) =
                 Const(@{const_syntax ifte},dummyT) $ e $ trans p $ Const(@{const_syntax skip},dummyT) 
          | trans (Const("_ifte_quote",_) $ e $ p $ q) =
                 Const(@{const_syntax ifte},dummyT) $ e $ trans p $ trans q
          | trans (Const("_seq",_) $ p1 $ p2) =
                Const(@{const_syntax seq},dummyT) $ trans p1 $ trans p2
          | trans (Const("_skip",_)) = Const(@{const_syntax skip},dummyT)
          | trans (Const("_callproc",_) $ x $ f $ args) = (add_var known x;
                Const(@{const_syntax callproc},dummyT) $ x $ f $ trargs args)
(*          | trans (Const("_local_var",_) $ v $ body) = (add_var v;
                Const(@{const_name HOL.Let},dummyT) $
                (Const(@{const_name LVariable},dummyT) $ get_var_name v)
                --- Abs(abstract body over v) --- *)
          | trans p = raise ERROR ("Invalid program fragment "^(@{make_string} p))
    in trans p end
  end

(* Printer for programs *)

local
fun dest_nibble t =
  let fun err () = raise TERM ("dest_nibble", [t]) in
    (case try (unprefix "\<^const>String.nibble.Nibble" o fst o Term.dest_Const) t of
      NONE => err ()
    | SOME c =>
        if size c <> 1 then err ()
        else if "0" <= c andalso c <= "9" then ord c - ord "0"
        else if "A" <= c andalso c <= "F" then ord c - ord "A" + 10
        else err ())
  end;

fun dest_char (Const (@{const_syntax String.char.Char}, _) $ t $ u) =
       dest_nibble t * 16 + dest_nibble u
     | dest_char t = raise TERM ("dest_char", [t]);

fun dest_list (Const(@{const_syntax List.list.Nil}, _)) = []
  | dest_list (Const(@{const_syntax List.list.Cons}, _) $ t $ u) = t :: dest_list u
  | dest_list t = raise TERM ("dest_list", [t]);

val dest_string = implode o map (chr o dest_char) o dest_list;


    fun translate_expression_back (Const(@{const_syntax const_expression},_) $ e) = e
      | translate_expression_back (Const(@{const_syntax apply_expression},_) $ e $ x) =
            Term.betapply (translate_expression_back e, Const("_var_access",dummyT) $ x)
      | translate_expression_back _ = (raise (ERROR ("translate_expression_back: error")))
  in
  fun translate_program_back _ p = 
    let fun trans (Const(@{const_syntax skip},_)) = Const("_skip",dummyT)
          | trans (Const(@{const_syntax assign},_)$x$e) =
               (Const("_assign",dummyT) $ x $ translate_expression_back e
                handle ERROR _ => Const("_assign_quote",dummyT) $ x $ e)
          | trans (Const(@{const_syntax sample},_)$x$e) =
               (Const("_sample",dummyT) $ x $ translate_expression_back e
                handle ERROR _ => Const("_sample_quote",dummyT) $ x $ e)
          | trans (Const(@{const_syntax label},_)$l$p) =
               Const("_label",dummyT) $ Free(dest_string l,dummyT) $ trans p
          | trans (Const(@{const_syntax while},_)$e$p) =
               (Const("_while",dummyT) $ translate_expression_back e $ trans p
                handle ERROR _ => Const("_while_quote",dummyT) $ e $ trans p)
          | trans (Const(@{const_syntax ifte},_)$e$p$Const(@{const_syntax skip},_)) =
               (Const("_ifthen",dummyT) $ translate_expression_back e $ trans p
                handle ERROR _ => Const("_ifthen_quote",dummyT) $ e $ trans p)
          | trans (Const(@{const_syntax ifte},_)$e$p$q) =
               (Const("_ifte",dummyT) $ translate_expression_back e $ trans p $ trans q
                handle ERROR _ => Const("_ifte_quote",dummyT) $ e $ trans p $ trans q)
          | trans (Const(@{const_syntax seq},_)$p$q) =
               Const("_seq",dummyT) $ trans p $ trans q
          | trans p = Const("_quote",dummyT) $ p
    in trans p end
  end

end
