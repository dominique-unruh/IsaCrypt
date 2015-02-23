theory Universe
imports Main Ell1
begin

typedecl val;
axiomatization closed_val_set :: "val set \<Rightarrow> bool" where
  closed_val_set_undefined: "closed_val_set {undefined}";

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
