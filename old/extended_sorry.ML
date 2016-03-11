structure Extended_Sorry =
struct

type annotation = {
  thy:theory,
  prop:term,
  message:string option,
  position:Position.T
};

fun annotate_prop (annot:annotation) : cterm =
  let val annot_prop = #prop annot
      val annot_pos = #position annot |> Term_Position.encode |> HOLogic.mk_string
      val annot_msg = case #message annot of NONE => @{term "None::string option"} | SOME msg => @{term "Some::string\<Rightarrow>_"} $ HOLogic.mk_string msg
      val generalized_prop = Var (("A", 0), propT)
  in
  Logic.implies $ (HOLogic.mk_Trueprop (@{term ANNOTATION} $ annot_prop $ annot_msg $ annot_pos)) $ generalized_prop |>
  Thm.global_cterm_of (#thy annot)
  end;

val (_, make_thm_cterm_annot) =
  Context.>>>
    (Context.map_theory_result (Thm.add_oracle (Binding.make ("skip_proof", @{here}), annotate_prop)));

fun make_thm_annot annot = make_thm_cterm_annot annot OF @{thms ANNOTATION};

fun cheat_tac_annot msg pos i st =
  SUBGOAL (fn (goal,i) =>
    resolve0_tac [make_thm_annot {thy=Thm.theory_of_thm st, prop=goal, position=pos, message=msg}] i) i st;

fun direct_oracles_of_proof _ _ _ MinProof = ()
  | direct_oracles_of_proof found thy Hs (AbsP(_,t,prf)) =
        direct_oracles_of_proof found thy (t::Hs) prf
  | direct_oracles_of_proof found thy Hs (Abst(_,_,prf)) =
        direct_oracles_of_proof found thy Hs prf
  | direct_oracles_of_proof (_,found_ora) _ _ (Oracle(name,trm,_)) =
        found_ora := (name,trm) :: !found_ora
  | direct_oracles_of_proof (found_thm,_) _ _ (PThm (ser,((name,term,_),body))) =
        found_thm := (ser,name,term,body) :: !found_thm
  | direct_oracles_of_proof found thy Hs (prf%_) = 
        direct_oracles_of_proof found thy Hs prf
  | direct_oracles_of_proof found thy Hs (prf%%prf') = 
        (direct_oracles_of_proof found thy Hs prf; direct_oracles_of_proof found thy Hs prf')
  | direct_oracles_of_proof _ _ _ (PAxm _) = ()
  | direct_oracles_of_proof _ _ _ (PBound _) = ()
  | direct_oracles_of_proof _ _ _ (Hyp _) = ()
  | direct_oracles_of_proof _ _ _ (Promise _) = ()
  | direct_oracles_of_proof found thy Hs (OfClass (T,c)) =
      let val proofs = ProofRewriteRules.mk_of_sort_proof thy Hs (T,[c]) in
      map (direct_oracles_of_proof found thy Hs) proofs; () end

fun direct_oracles_of_pbody (found_thm,found_ora) thy prop (PBody {oracles, thms, proof}) =
  let val _ = found_thm := map (fn (ser,(name,term,body)) => (ser,name,term,body)) thms @ !found_thm
      val _ = found_ora := oracles @ !found_ora
      val proof = Reconstruct.reconstruct_proof thy prop proof
                  handle ERROR _ => proof
      val _ = direct_oracles_of_proof (found_thm,found_ora) thy [] proof
  in () end

fun direct_oracles_of_thm thy (_,_,prop,body) =
  let val found_thm = Unsynchronized.ref []
      val found_ora = Unsynchronized.ref []
      val _ = direct_oracles_of_pbody (found_thm,found_ora) thy prop (Future.join body)
  in
    (!found_thm,!found_ora)
  end

fun get_thm thm : int * string * term * proof_body future = 
  let fun g (PThm (ser,((name,prop,_),body))) = (ser,name,prop,body)
        | g (p%%_) = g p
        | g (p%_) = g p
        | g prf = (@{print} prf; error "unsup2")
  in
  case Thm.proof_body_of thm of
    PBody {proof, ...} => g proof
  end

fun oracles_of' (thy:theory) seen found path (ser,name,prop,body) =
  if Inttab.defined (!seen) ser then ()
  else let val _ = seen := Inttab.update (ser,()) (!seen)
(*	   val _ = @{print} ("new",ser,name,path) *)
           val path = name::path
           val (thms,oras) = direct_oracles_of_thm thy (ser,name,prop,body)
           val _ = if null oras then () else found := (path, Ord_List.make Proofterm.oracle_ord oras) :: !found
           val _ = map (oracles_of' thy seen found path) thms
       in () end

fun oracles_of thms =
  let val found = Unsynchronized.ref []
      val seen = Unsynchronized.ref Inttab.empty
      val _ = map (fn thm => oracles_of' (Thm.theory_of_thm thm) seen found [] (get_thm thm)) thms
  in rev (!found) end

(*
local
fun ora_of thy seen (PBody {oracles, thms, proof}) found path = 
  let val found = if null oracles then found else (path,oracles)::found
      val (found,seen) = fold (ora_of'' thy path) thms (found,seen)
      val (found,seen) = ora_of' thy seen proof found path
  in
  (found,seen)
  end
and ora_of'' (thy:theory) path (i,(name,_,body)) (found,seen) =
                               if Inttab.defined seen i then (found,seen)
                               else (ora_of thy (Inttab.update (i,()) seen) (Future.join body) found (name::path))
and ora_of' (_:theory) seen (MinProof) found _ = (found,seen)
  | ora_of' thy seen (AbsP(_,_,proof)) found path = ora_of' thy seen proof found path
  | ora_of' thy seen (Abst(_,_,proof)) found path = ora_of' thy seen proof found path
  | ora_of' _ seen (PAxm _) found _ = (found,seen)
  | ora_of' thy seen (PThm (ser,((name,_,_),body))) found path = ora_of'' thy path (ser,(name,Bound 0,body)) (found,seen)
  | ora_of' thy seen (p1 %% p2) found path = let val (found,seen) = ora_of' thy seen p1 found path in
                                         ora_of' thy seen p2 found path end
  | ora_of' thy seen (proof % _) found path = ora_of' thy seen proof found path
  | ora_of' thy seen (OfClass (T,c)) found path =
    let val proofs = ProofRewriteRules.mk_of_sort_proof thy [] (T,[c]) in
      fold (fn prf => fn (found,seen) => ora_of' thy seen prf found path) proofs (found,seen) end
  | ora_of' _ seen (PBound _) found _ = (found,seen)
  | ora_of' _ seen (Oracle (name,trm,_)) found path = (("???"::path,[(name,trm)])::found,seen)
  | ora_of' _ _ proof _ _ = (@{print} proof; error "unsup")
in
fun all_oracles_of thms = 
  let val (found,_) = fold (fn thm => fn (found,seen) => ora_of (Thm.theory_of_thm thm) seen (Thm.proof_body_of thm) found []) 
                         thms ([], Inttab.empty)
  in rev found end
fun all_oracles_of_classes thy = 
  let val arities = thy |> Sign.tsig_of |> Type.rep_tsig |> #classes |> snd |> Sorts.arities_of |> Symtab.dest_list
      val arity_proofs = map (fn (tyco,(cls,Ss)) => (@{make_string} (tyco,Ss,cls), Proofterm.arity_proof thy (tyco,Ss,cls))
                              handle ERROR msg => (writeln msg; (msg,MinProof))) arities
      val (found,_) = fold (fn (msg,proof) => fn (found,seen) => 
                            case proof of 
                              PThm (_,(_,body)) => (ora_of thy seen (Future.join body) found ["[instantiation]"])
                            | MinProof => (found,seen)
                            | _ => error ("nyi " ^ @{make_string} proof ^ "  " ^ msg))
                         arity_proofs ([],Inttab.empty)
  in rev found end
end
*)

fun markup_thm_name ctx name =
  let val namespace = Global_Theory.facts_of (Proof_Context.theory_of ctx) |> Facts.space_of
      val (markup,name) = Name_Space.markup_extern ctx namespace name
  in
  Markup.markup markup name  
  end;

type print_annotated_conf = {
  show_empty: bool,
  show_oracles: bool
};

val print_annotated_conf_default = {
  show_empty=false,
  show_oracles=false
};

fun set_show_oracles ({show_empty, ...}:print_annotated_conf) b
   = {show_empty=show_empty, show_oracles=b};

fun print_annotated_oracles (conf:print_annotated_conf) ctx thms =
  let fun render_annot prop msg pos = 
         let val prop_str = Syntax.pretty_term ctx prop |> Pretty.string_of
             val msg_str = (case msg of Const(@{const_name None},_) => ""
                                      | Const(@{const_name Some},_)$str => "\<open>"^HOLogic.dest_string str^"\<close> "
                                      | t => raise (TERM("parsing annotation, message",[t])))
             val pos = pos |> HOLogic.dest_string |> Term_Position.decode |> the
             val pos_str = Markup.markup (Markup.properties (Position.properties_of pos) Markup.position) "[here]"
         in
          msg_str ^ prop_str ^ " " ^ pos_str
         end
      fun extract_annot trm = 
        Logic.dest_implies trm |> fst
        |> HOLogic.dest_Trueprop
        |> (fn (Const(@{const_name ANNOTATION},_)$prop$msg$pos) => render_annot prop msg pos | t => raise (TERM("parsing annotation",[t])))
        handle TERM _ => "[use ML {* proofs := 1 *} to get data]"
      fun ora_to_str (name,term) = 
        if name="Extended_Sorry.skip_proof" then "  SORRY: "^(term |> extract_annot)
        else if name="Pure.skip_proof" then "  sorry"
        else "  "^name^": "^(Syntax.pretty_term ctx term |> Pretty.string_of)
      fun path_to_str path = 
        let val path = if #show_empty conf
                       then map (fn "" => "<anonymous>" | x => x) path
                       else filter (fn x=>x<>"") path
            val path = map (markup_thm_name ctx) path
            val path = rev path
        in String.concatWith " > " path end
      fun thm_to_str (path,oras) =
        (path_to_str path)::(map ora_to_str oras)
      val oracles = oracles_of thms
      (*val oracles = if #show_oracles conf
                    then oracles @ all_oracles_of_classes (Proof_Context.theory_of ctx)
                    else oracles*)
  in
  oracles |> map thm_to_str |> List.concat |> String.concatWith "\n" |> writeln
  end;

val _ = let
fun print thms ctxt =
  (Attrib.eval_thms ctxt thms |> (print_annotated_oracles print_annotated_conf_default ctxt); ctxt)
fun print_ora _ ctxt =
  (print_annotated_oracles (set_show_oracles print_annotated_conf_default true) ctxt []; ctxt)
in
Outer_Syntax.local_theory @{command_keyword print_sorry}
"show all occurrences of sorry (and other oracles)"
((Parse.reserved "classes" >> print_ora)
  || (Parse.xthms1 >> print))
end;


(** Method sorry **)

fun cheating msg pos ctxt int = METHOD (fn _ => fn st =>
  (if int orelse Config.get ctxt quick_and_dirty then ()
  else warning "Cheating outside quick_and_dirty mode!";
  ALLGOALS (cheat_tac_annot msg pos) st))
  
fun sorry_text msg pos int = Method.Basic (fn ctxt => cheating msg pos ctxt int);

fun proof_global_skip_proof msg pos int state =
  Proof.global_terminal_proof ((sorry_text msg pos int, Position.no_range), NONE) state before
  Skip_Proof.report (Proof.context_of state);
fun proof_local_skip_proof msg pos int state =
  Proof.local_terminal_proof ((sorry_text msg pos int, Position.no_range), NONE) state before
  Skip_Proof.report (Proof.context_of state);

fun local_skip_proof msg pos = Toplevel.proof' (proof_local_skip_proof msg pos);
fun global_skip_proof msg pos = Toplevel.end_proof (proof_global_skip_proof msg pos);
fun skip_proof msg pos = (local_skip_proof msg pos) o (global_skip_proof msg pos);

fun parse_position toks = (Token.pos_of (hd toks), toks);

val _ = Outer_Syntax.command @{command_keyword SORRY} "skip proof (quick-and-dirty mode only!)"
    (parse_position -- Scan.option Parse.string >> (fn (pos,msg) => skip_proof msg pos));

end
