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
  cterm_of (#thy annot)
  end;

val (_, make_thm_cterm_annot) =
  Context.>>>
    (Context.map_theory_result (Thm.add_oracle (Binding.make ("skip_proof", @{here}), annotate_prop)));

fun make_thm_annot annot = make_thm_cterm_annot annot OF @{thms ANNOTATION};

fun cheat_tac_annot msg pos i st =
  SUBGOAL (fn (goal,i) =>
    rtac (make_thm_annot {thy=Thm.theory_of_thm st, prop=goal, position=pos, message=msg}) i) i st;

local
fun ora_of seen (PBody {oracles, thms, ...}) found path = 
  let val found = if null oracles then found else (path,oracles)::found
      val (found,seen) = fold (fn (i, (name,_,body)) => fn (found,seen) =>
                               if Inttab.defined seen i then (found,seen)
                               else (ora_of (Inttab.update (i,()) seen) (Future.join body) found (name::path)))
                         thms (found,seen)
  in
  (found,seen)
  end
in
fun all_oracles_of thms = 
  let val (found,_) = fold (fn thm => fn (found,seen) => ora_of seen (Thm.proof_body_of thm) found []) 
                         thms ([], Inttab.empty)
  in rev found end
fun all_oracles_of_classes thy = 
  let val arities = thy |> Sign.tsig_of |> Type.rep_tsig |> #classes |> snd |> Sorts.arities_of |> Symtab.dest_list
      val arity_proofs = map (fn (tyco,(cls,Ss)) => Proofterm.arity_proof thy (tyco,Ss,cls)
                              handle ERROR msg => (writeln msg; MinProof)) arities
      val (found,_) = fold (fn proof => fn (found,seen) => 
                            case proof of 
                              PThm (_,(_,body)) => (ora_of seen (Future.join body) found ["[instantiation]"])
                            | _ => (found,seen))
                         arity_proofs ([],Inttab.empty)
  in rev found end
end

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
         let val prop_str = Syntax.pretty_term ctx prop |> Pretty.str_of
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
        if name="Extended_Sorry.skip_proof" then "  sorry: "^(term |> extract_annot)
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
      val oracles = all_oracles_of thms
      val oracles = if #show_oracles conf
                    then oracles @ all_oracles_of_classes (Proof_Context.theory_of ctx)
                    else oracles
  in
  oracles |> map thm_to_str |> List.concat |> String.concatWith "\n" |> writeln
  end;

val _ = let
fun print thms ctxt =
  (Attrib.eval_thms ctxt thms |> (print_annotated_oracles print_annotated_conf_default ctxt); ctxt)
fun print_ora _ ctxt =
  (print_annotated_oracles (set_show_oracles print_annotated_conf_default true) ctxt []; ctxt)
in
Outer_Syntax.local_theory @{command_spec "print_sorry"}
"show all occurrences of sorry (and other oracles)"
((Parse.reserved "classes" >> print_ora)
  || (Parse_Spec.xthms1 >> print))
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

val _ = Outer_Syntax.command @{command_spec "SORRY"} "skip proof (quick-and-dirty mode only!)"
    (parse_position -- Scan.option Parse.string >> (fn (pos,msg) => skip_proof msg pos));

end
