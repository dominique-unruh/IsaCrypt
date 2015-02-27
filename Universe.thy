theory Universe
imports Main Ell1
begin

typedecl val;

axiomatization closed_val_set :: "val set \<Rightarrow> bool" where
    closed_val_set_infinite: "\<exists>f::nat\<Rightarrow>val. inj f \<and> closed_val_set (range f)"
and closed_val_set_power: "closed_val_set s \<Longrightarrow> \<exists>f. inj_on f (Pow s) \<and> closed_val_set(f ` (Pow s))"

instantiation val :: equal begin
definition "equal_val (v::val) w = (v=w)"
instance apply intro_classes by (simp add: equal_val_def)
end


class prog_type =
  default +
(*  fixes embedding :: "'a \<Rightarrow> val"
  fixes embedding_inv :: "val \<Rightarrow> 'a"
  assumes embedding_inv_embedding [simp]: "embedding_inv (embedding x) = x" *)
  assumes val_closed: "\<exists>(f::'a\<Rightarrow>val) s. inj f \<and> range f \<subseteq> s \<and> closed_val_set s";

definition embedding :: "'a::prog_type \<Rightarrow> val" where
  "embedding == (SOME f. \<exists>s. inj f \<and> range f \<subseteq> s \<and> closed_val_set s)"

lemma embedding_inv [simp]: "(embedding x = embedding y) = (x = y)"
  by (metis (erased, lifting) UNIV_I embedding_def image_eqI range_ex1_eq someI_ex val_closed)


instantiation "nat" :: prog_type begin
(*definition "embedding_nat == (SOME f::nat\<Rightarrow>val. inj f \<and> closed_val_set (range f))"
definition "embedding_inv_nat :: val\<Rightarrow>nat == inv embedding"*)
instance proof
  have some:"inj (embedding::nat\<Rightarrow>val) \<and> closed_val_set (range (embedding::nat\<Rightarrow>val))"
  unfolding embedding_nat_def apply (rule someI_ex[of "\<lambda>f. inj f \<and> closed_val_set (range f)"])
    by (rule closed_val_set_infinite)
  thus "\<And>x. embedding_inv (embedding x) = (x::nat)"
    by (smt2 embedding_inv_nat_def inv_f_eq)
  show "\<exists>s. range (embedding::nat\<Rightarrow>val) \<subseteq> s \<and> closed_val_set s"
    by (metis (mono_tags, hide_lams) some order_refl)
qed
end

definition "some_embedding (x::'b::prog_type itself) == embedding o (SOME f::'a\<Rightarrow>'b. inj f)"

lemma
(*  assumes "embedding::'a\<Rightarrow>val == some_embedding TYPE('b)"
  assumes "embedding_inv::'a\<Rightarrow>val == inv embedding" *)
  assumes "\<exists>f::'a\<Rightarrow>'b::prog_type. inj f"
  shows "OFCLASS('a, prog_type_class)"
proof 
    

instantiation "bool" :: prog_type begin
instance 
end

instantiation unit :: prog_type begin;
instance sorry
end;

instantiation int :: prog_type begin;
instance sorry
end;

instantiation "fun" :: (prog_type,prog_type)prog_type begin;
instance sorry
end;

instantiation "distr" :: (prog_type)prog_type begin
instance sorry
end;

end
