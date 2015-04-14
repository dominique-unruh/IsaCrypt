(* @SUITE utils *)

theory close_keyword
imports Main "../Tools"
begin

lemma "1=1 \<and> 2=2"
  apply (rule conjI)
  close auto
  close auto
done

end
