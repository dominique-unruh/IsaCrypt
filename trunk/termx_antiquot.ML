structure TermX_Antiquot =
struct

val termx_parser = Args.context -- Scan.lift (
Args.name_inner_syntax
-- Scan.optional (@{keyword "where"} |-- Scan.repeat1 Args.name_inner_syntax) []
--| Scan.ahead Parse.eof)

val typx_parser = Args.context -- Scan.lift Args.name_inner_syntax

val print_pair = ML_Syntax.print_pair
val print_string = ML_Syntax.print_string
val print_list = ML_Syntax.print_list
val print_int = ML_Syntax.print_int
val print_indexname = ML_Syntax.print_indexname
val print_sort = ML_Syntax.print_sort

fun strip_prime str = (@{assert} (String.sub(str,0) = #"'"); String.extract(str,1,NONE))
       
fun print_typ (Type arg) = "Term.Type " ^ print_pair print_string (print_list print_typ) arg
  | print_typ (TFree arg) = "Term.TFree " ^ print_pair print_string print_sort arg
  | print_typ (t as TVar ((n,0),_)) = 
      (let val n = strip_prime n
       in if ML_Syntax.is_identifier n then "("^n^":typ)" (* TODO check sort? *)
          else raise (TYPE("schematic type variables must be valid ML identifiers",[t],[])) end)
  | print_typ (t as TVar ((n,1),_)) = 
      (let val n = strip_prime n
       in if ML_Syntax.is_identifier n then ML_Syntax.atomic("fastype_of "^n) (* TODO check sort? *)
          else raise (TYPE("schematic type variables must be valid ML identifiers",[t],[])) end)
  | print_typ (t as TVar _) = raise (TYPE("must not have schematic type variables with index !=0",[t],[]))

fun print_term (Const arg) = "Term.Const " ^ print_pair print_string print_typ arg
  | print_term (Free arg) = "Term.Free " ^ print_pair print_string print_typ arg
  | print_term (t as Var ((n,0),_)) = if ML_Syntax.is_identifier n then "("^n^":term)" (* TODO check type? *)
                                      else raise (TERM("schematic variables must be valid ML identifiers",[t]))
  | print_term (t as Var _) = raise (TERM ("must not have schematic variables with index !=0",[t]))
  | print_term (Bound i) = "Term.Bound " ^ print_int i
  | print_term (Abs (s, T, t)) =
      "Term.Abs (" ^ print_string s ^ ", " ^ print_typ T ^ ", " ^ print_term t ^ ")"
  | print_term (t1 $ t2) = "Term.$ " ^ print_pair print_term print_term (t1, t2);

fun typx (ctx,str) =
  let val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
      val typ = Syntax.read_typ ctx str
  in
  print_typ typ |> ML_Syntax.atomic
  end

val typx_antiquot = typx_parser >> typx

fun termx (ctx,(str,abbrevs)) =
  let val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
      val abbrevs = abbrevs |> map (Syntax.read_typ ctx)
                    |> map dest_funT |> map (apfst (fst o dest_TVar))
      val trm = Syntax.parse_term ctx str
      val trm = (fold (fn subst => Term.subst_TVars [subst]) abbrevs) trm
      val trm = Syntax.check_term ctx trm
      val trm_ML = print_term trm |> ML_Syntax.atomic
      val case_ML = fold (fn ((v,_),T) => fn ML => 
             "case "^strip_prime v^":typ of "^print_typ T^" => "^ML^" | _ => raise(TYPE("^
              ML_Syntax.print_string("cannot match "^strip_prime v^" as \""^(Syntax.pretty_typ ctx T |> Pretty.string_of)^"\"")^",["^strip_prime v^":typ],[]))")
             (rev abbrevs) trm_ML |> ML_Syntax.atomic
  in
  case_ML
  end

val termx_antiquot = termx_parser >> termx

end
