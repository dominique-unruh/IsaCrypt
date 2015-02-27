structure Hoare_Syntax =
struct

fun trans_assert _ _ m (Const("_var_access",_)$v) =
    Const(@{const_syntax memory_lookup},dummyT) $ Bound m $ v
| trans_assert _ _ m (Const("_memory",_)) = Bound m
| trans_assert ctx known m (v as Free(vn,_)) =
    if Lang_Syntax.is_program_variable ctx (!known) vn then
      Const(@{const_syntax memory_lookup},dummyT) $ Bound m $ v
    else v
| trans_assert ctx known m (Const("_constrain",_)$p$_) = trans_assert ctx known m p
| trans_assert ctx known m (p$q) = trans_assert ctx known m p $ trans_assert ctx known m q
| trans_assert ctx known m (Abs(n,T,t)) = Abs(n,T,trans_assert ctx known (m+1) t)
| trans_assert _ _ _ e = e

fun trans_assert' _ _ (e as Abs _) = e
  | trans_assert' _ _ (e as Const("_constrainAbs",_) $ Abs _ $ _) = e
  | trans_assert' ctx known e =
    let val e = trans_assert ctx known 0 e
    in Abs("mem",dummyT,e) end

fun trans_hoare ctx P c Q =
    let val known = Unsynchronized.ref []
        val c = Lang_Syntax.translate_program ctx known c
        val P = (trans_assert' ctx known P)
        val Q = trans_assert' ctx known Q
    in Const(@{const_syntax hoare},dummyT) $ P $ c $ Q end

fun trans_hoare_back ctx P c Q =
    Const("_hoare",dummyT) $ P $ Lang_Syntax.translate_program_back ctx c $ Q


end
