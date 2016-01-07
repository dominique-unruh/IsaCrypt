(* -*- mode: sml;-*- *)
structure RHoare_Syntax =
struct

  fun pickmem _ NONE = raise (ERROR "Specify left/right memory!")
    | pickmem m (SOME true) = Bound (m+1)
    | pickmem m (SOME false) = Bound m

  fun trans_assert _ _ m lr (Const("_var_access",_)$v) =
             Const(@{const_syntax memory_lookup},dummyT) $ pickmem m lr $ v
    | trans_assert ctx known m _ (Const("_select_memory1",_)$p) = trans_assert ctx known m (SOME true) p
    | trans_assert ctx known m _ (Const("_select_memory2",_)$p) = trans_assert ctx known m (SOME false) p
    | trans_assert _ _ m lr (Const("_memory",_)) = pickmem m lr
    | trans_assert _ _ m _ (Const("_memory1",_)) = Bound (m+1)
    | trans_assert _ _ m _ (Const("_memory2",_)) = Bound m
    | trans_assert ctx known m lr (v as Free(vn,_)) =
(* TODO: vn could be x\<^sub>1 or x\<^sub>2, this should be interpreted as "_select_memory1/2 x" if x is a variable *)
          if Lang_Syntax.is_program_variable ctx (!known) vn then
             Const(@{const_syntax memory_lookup},dummyT) $ pickmem m lr $ v
          else v
    | trans_assert ctx known m lr (Const("_constrain",_)$p$_) = trans_assert ctx known m lr p
    | trans_assert ctx known m lr (p$q) = trans_assert ctx known m lr p $ trans_assert ctx known m lr q
    | trans_assert ctx known m lr (Abs(n,T,t)) = Abs(n,T,trans_assert ctx known (m+1) lr t)
    | trans_assert _ _ _ _ (e as Var _) = e
    | trans_assert _ _ _ _ (e as Const _) = e
    | trans_assert _ _ m _ (e as Bound i) =
        if i>=m then raise (TERM ("unexpected bound index "^string_of_int i, [e])) else e

  fun trans_assert' _ _ (e as Abs _) = e
    | trans_assert' _ _ (e as Const("_constrainAbs",_) $ Abs _ $ _) = e
    | trans_assert' ctx known e =
        let val e = trans_assert ctx known 0 NONE e
        in Abs("mem1",dummyT,Abs("mem2",dummyT,e)) end

  fun trans_hoare ctx P c1 c2 Q =
    let val known = Unsynchronized.ref []
        val c1 = Lang_Syntax.translate_program ctx known c1
        val c2 = Lang_Syntax.translate_program ctx known c2
        val P = trans_assert' ctx known P
        val Q = trans_assert' ctx known Q
    in Const(@{const_syntax rhoare},dummyT) $ P $ c1 $ c2 $ Q end

end
