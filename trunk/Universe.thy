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
  fixes embedding :: "'a \<Rightarrow> val"
  fixes embedding_inv :: "val \<Rightarrow> 'a"
(*  fixes type_id :: "'a itself \<Rightarrow> typeID"*)
  assumes embedding_inv_embedding [simp]: "embedding_inv (embedding x) = x"
  assumes val_closed [simp]: "closed_val_set (range embedding)";

lemma embedding_inv [simp]: "(embedding x = embedding y) = (x = y)"
  by (metis embedding_inv_embedding)

instantiation "bool" :: prog_type begin
instance sorry
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
