theory Wlog
imports Main
keywords "wlog" :: "prf_script"
begin


ML {*
fun ren_frees [] = I
  | ren_frees pairs =
      let fun substf u =
            case u of Abs(a,T,t) => Abs(a, T, substf t)
                    | t$u' => substf t $ substf u'
                    | Free(n,T) => (case AList.lookup (op=) pairs n of
                                      SOME n' => Free(n',T)
                                    | NONE => u)
                    | _ => u
      in  substf  end;
*}

ML {*
fun get_fixes ctx =
    let val fixes = Variable.dest_fixes ctx
        val (constr,_) = Variable.constraints_of ctx
    in map (fn (int,ext) => case Vartab.lookup constr (ext,~1) of NONE => error "no constraint" | SOME T => (int,ext,T)) fixes end
*}

ML {*
fun wlog (newassm_name,newassm) (fixes:(binding*string*typ) list) (thesis:term) (assms:(string*thm list)list) int state =
  let (*val fixes = get_fixes (Proof.context_of state)*)
                                              
      val flat_assms = assms |> map snd |> List.concat |> map Thm.prop_of
      val hyp = Logic.list_implies (newassm :: flat_assms, thesis)
      val hyp = fold (fn (_,a,T) => fn t => Logic.all_const T $ (Term.absfree (a,T) t)) fixes hyp
val _ = @{print} fixes
      val state = Proof.presume [] [] [((@{binding hypothesis},[]),[(hyp,[])])] state

      fun after_qed (_(*ctx*),_) state = 
      let val let_bindings = Variable.binds_of (Proof.context_of state) |> Vartab.dest
          val state = Proof.next_block state
          val (fixed,state) = Proof.map_context_result (Proof_Context.add_fixes (map (fn (a,_,T) => (a,SOME T,NoSyn)) fixes)) state
          val rename_fixed = ren_frees (map2 (fn (_,a,_) => fn b => (a,b)) fixes fixed)
          val state = fold (fn (name,(_,t)) => Proof.map_context (Variable.bind_term (name,rename_fixed t))) let_bindings state
          val state = Proof.map_context (Variable.bind_term (("wlog_goal",0),rename_fixed thesis)) state
          val state = fold (fn (name,assm) => fn state => 
                        Proof.assume [] [] [((Binding.name name,[]),map (fn t => (rename_fixed (Thm.prop_of t),[])) assm)] state) assms state
          val state = Proof.assume [] [] [((newassm_name,[]),[(rename_fixed newassm,[])])] state (* Should be last to override "this" *)
          (* TODO: define assms to contain all assumptions (carried over and new) *)
      in state end

      val (_,state) = Proof.show true NONE after_qed [] [] [(Thm.empty_binding,[(thesis,[])])] int state
      (* val state = Proof.local_skip_proof int state *)
  in state end
*}

ML {*
fun wlog_cmd ((bind,stmt) : Binding.binding * string) (* New assumptions added wlog *)
             (fixes : binding list) (* Variables to be generalized *)
             (goal : string) (* Current goal *)
             (assms : (Facts.ref * Token.src list) list) (* Assumptions to keep *)
             int state =
  let val ctx = Proof.context_of state
(*       val (bind,stmt) = case error "xxx" of
                            [((bind,[]),[(stmt,[])])] => 
                              let val ctx = Proof.context_of state
                                  val stmt = Syntax.read_prop ctx stmt
                              in (bind,stmt) end
                          | _ => error "wlog: some unsupported case -> add proper error message" *)
      val stmt = Syntax.read_prop ctx stmt                                 
      val assms' = map (fn (fact,_) => (Facts.name_of_ref fact, Proof_Context.get_fact ctx fact)) assms
      val goal' = Syntax.read_prop ctx goal
      val constr = Variable.constraints_of ctx |> #1
      val fixes' = map (fn b => let val SOME internal = Variable.lookup_fixed ctx (Binding.name_of b)
                                    val SOME T = Vartab.lookup constr (internal,~1)
                                in (b,internal,T) end) fixes
      val _ = @{print} assms
  in wlog (bind,stmt) fixes' goal' assms' int state end                 

val wlog_parser = (Scan.optional (Parse.binding --| Parse.$$$ ":") Binding.empty -- Parse.prop) -- 
                  (@{keyword "for"} |-- Scan.repeat Parse.binding) --
                  (@{keyword "shows"} |-- Parse.prop) --
                  (@{keyword "assumes"} |-- Parse.xthms1) --
                  (@{keyword "imports"} |-- Scan.repeat Parse.binding)

val _ =
  Outer_Syntax.command @{command_keyword wlog} "TODO"
    (wlog_parser >> (fn ((((stmt,fixes),goal),assms),imports) => Toplevel.proof' (wlog_cmd stmt fixes goal assms)));
*}

lemma
  fixes a b :: nat
  assumes bla: "True"
  assumes neq: "a \<noteq> b"
  shows "a+b \<ge> 1"
proof -

  fix x::int fix x::nat 
  ML_prf {*
  val a =   Variable.lookup_fixed @{context} "x" |> Option.valOf
  val b =  Vartab.lookup (Variable.constraints_of @{context} |> fst) (a,~1)
  *}

  have neq2: "a>b\<or>b>a" using neq bla by auto 
  have comm: "1 \<le> a + b \<Longrightarrow> 1 \<le> b + a" for a b :: nat by auto

  ML_prf {* val ctx1 = @{context} *}
  ML_prf {* val neq2 = @{thm neq2} *}

  let ?a = a

  wlog neq3: "b\<noteq>a" for x shows "a+b\<ge>(1::nat)" assumes neq imports neq2
    apply (rule hypothesis)
    using neq by auto

  ML_prf {* val ctx2 = @{context} *}

  wlog geq: "a > b" for a b shows ?thesis assumes neq3  imports neq2
    apply (cases "a>b")
     apply (rule hypothesis; simp)
    apply (subst add.commute)
     apply (rule hypothesis)
       using neq apply simp
      using neq apply simp
     (* using neq3 by simp *)
  by (tactic \<open>ALLGOALS (K all_tac)\<close>)

  note assms = neq neq3

ML_prf {*
(* Given a theorem thm, replaces all occurrences of "fixes" by "fixed".
   For any hypothesis of thm that is not a fact in the context "ctx", a premise is added to the theorem.
   (Thus, the resulting theorem will be valid in "ctx") *)
fun translate_thm ctx fixes fixed thm = 
  let val hyps = Thm.chyps_of thm
      val thm = fold_rev Thm.implies_intr hyps thm
      val idx = Thm.maxidx_of thm + 1
      val thm = Thm.generalize ([],map #2 fixes) idx thm
      val thm = Thm.instantiate ([],map2 (fn (_,n,T) => fn m => (((n,idx),T),Thm.cterm_of ctx (Free(m,T)))) fixes fixed) thm
      val facts = Proof_Context.facts_of ctx
      fun mk_hypnew hyp =
        let val chyp = Thm.cterm_of ctx hyp
            val hyp_thm = Thm.trivial chyp
            val candidates = Facts.could_unify facts hyp
            fun try_cand cand fallback = hyp_thm OF [cand] handle THM _ => fallback
        in fold try_cand candidates hyp_thm end
      val prems = take (length hyps) (Thm.prems_of thm)
      val hypsnew = map mk_hypnew prems
      val thm = thm OF hypsnew
   in thm end
*}

  ML_prf {*
    val fixes = [("xxx","a",@{typ nat}),("yyy","b",@{typ nat})]
    val fixed = ["aa__","ba__"]
    val neq2' = translate_thm @{context} fixes fixed neq2
  *}
  have "b<a\<or>a<b" apply (tactic \<open>resolve_tac @{context} [neq2'] 1\<close>) using assms by auto



  wlog tmp: "a=a" for a b shows ?thesis assumes neq geq imports neq2
    using hypothesis neq geq by metis

  from geq have "a \<ge> 1" by auto

  then show "1 \<le> a + b" by auto
qed
