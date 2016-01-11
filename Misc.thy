theory Misc
imports Main
begin

instantiation "fun" :: (type,zero) zero begin
definition "0 = (\<lambda>x. 0)"
instance ..
end
instantiation "fun" :: (type,plus) plus begin
definition "f + g = (\<lambda>x. f x + g x)"
instance ..
end
instantiation "fun" :: (type,semigroup_add) semigroup_add begin
instance proof
  fix a b c :: "'a\<Rightarrow>'b"
  show "a + b + c = a + (b + c)"
    unfolding plus_fun_def by (rule ext, rule add.assoc)
qed
end
instantiation "fun" :: (type,ab_semigroup_add) ab_semigroup_add begin
instance proof
  fix a b :: "'a\<Rightarrow>'b"
  show "a + b = b + a"
    unfolding plus_fun_def by (rule ext, rule add.commute)
qed
end
instantiation "fun" :: (type,comm_monoid_add) comm_monoid_add begin
instance proof
  fix a :: "'a\<Rightarrow>'b"
  show "0 + a = a"
    unfolding plus_fun_def zero_fun_def by (rule ext, rule add.left_neutral)
qed
end

(* TODO move to Misc *)
lemma setsum_apply: 
  assumes "finite N"
  shows "(\<Sum>n\<in>N. f n) x = (\<Sum>n\<in>N. f n x)"
using assms apply (induction N)
by (auto simp: zero_fun_def plus_fun_def)

end
