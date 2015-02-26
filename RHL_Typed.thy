theory RHL_Typed
imports RHL_Untyped Lang_Typed
begin

section {* Definition *}

definition rhoare :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation c1 m1
        \<and> apply_to_distr snd \<mu> = denotation c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))";

lemma rhoare_untyped: "rhoare P c1 c2 Q = rhoare_untyped P (mk_program_untyped c1) (mk_program_untyped c2) Q"
  unfolding rhoare_def rhoare_untyped_def denotation_def ..

section {* Concrete syntax *}

syntax "_rhoare" :: "(memory \<Rightarrow> bool) \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> term"
          ("hoare {(_)}/ (2_) ~ (2_)/ {(_)}")
syntax "_memory" :: memory ("&m")
syntax "_memory1" :: memory ("&1")
syntax "_memory2" :: memory ("&2")
syntax "_select_memory1" :: "'a \<Rightarrow> 'a" ("_\<^sub>1" [1000] 1000)
syntax "_select_memory2" :: "'a \<Rightarrow> 'a" ("_\<^sub>2" [1000] 1000)

parse_translation {*
  let
  fun pickmem m NONE = raise (ERROR "Specify left/right memory!")
    | pickmem m (SOME true) = Bound 1
    | pickmem m (SOME false) = Bound 0

  fun trans_assert _ _ m lr (Const("_var_access",_)$v) =
             Const(@{const_syntax memory_lookup},dummyT) $ pickmem m lr $ v
    | trans_assert ctx known m lr (Const("_select_memory1",_)$p) = trans_assert ctx known m (SOME true) p
    | trans_assert ctx known m lr (Const("_select_memory2",_)$p) = trans_assert ctx known m (SOME false) p
    | trans_assert ctx known m lr (Const("_memory",_)) = pickmem m lr
    | trans_assert ctx known m lr (Const("_memory1",_)) = Bound 1
    | trans_assert ctx known m lr (Const("_memory2",_)) = Bound 0
    | trans_assert ctx known m lr (v as Free(vn,_)) =
(* TODO: vn could be x\<^sub>1 or x\<^sub>2, this should be interpreted as "_select_memory1/2 x" if x is a variable *)
          if is_program_variable ctx (!known) vn then
             Const(@{const_syntax memory_lookup},dummyT) $ pickmem m lr $ v
          else v
    | trans_assert ctx known m lr (Const("_constrain",_)$p$_) = trans_assert ctx known m lr p
    | trans_assert ctx known m lr (p$q) = trans_assert ctx known m lr p $ trans_assert ctx known m lr q
    | trans_assert ctx known m lr (Abs(n,T,t)) = Abs(n,T,trans_assert ctx known (m+1) lr t)
    | trans_assert _ _ _ lr e = e

  fun trans_assert' _ _ (e as Abs _) = e
    | trans_assert' _ _ (e as Const("_constrainAbs",_) $ Abs _ $ _) = e
    | trans_assert' ctx known e =
        let val e = trans_assert ctx known 0 NONE e
        in Abs("mem1",dummyT,Abs("mem2",dummyT,e)) end

  fun trans_hoare ctx P c1 c2 Q =
    let val known = Unsynchronized.ref []
        val c1 = translate_program ctx known c1
        val c2 = translate_program ctx known c2
        val P = trans_assert' ctx known P
        val Q = trans_assert' ctx known Q
    in Const(@{const_syntax rhoare},dummyT) $ P $ c1 $ c2 $ Q end
  in
    [("_rhoare", fn ctx => fn [P,c1,c2,Q] => trans_hoare ctx P c1 c2 Q)]
  end
*}

(*
term "x\<^sub>a"
ML {* @{print} @{term x\<^sub>a} *}

consts x::"int variable"
consts f::"memory\<Rightarrow>memory"
term "hoare {(x)\<^sub>1 = undefined} skip ~ skip {undefined}"
*)

section {* Rules *}

(* TODO *)

end
