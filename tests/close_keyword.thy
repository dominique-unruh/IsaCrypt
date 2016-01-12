(* @SUITE utils *)

theory close_keyword
imports Main "../Tools"
begin

lemma "1=1 \<and> 2=2"
  apply (rule conjI)
  close auto
  close auto
done

lemma "1=1 \<and> 2=2"
  apply (rule conjI)
  close
  close
done

lemma "1=1 \<and> 2=2"
  apply (rule conjI)
  close 2
done


lemma "1=1 \<and> 2=2"
  apply (rule conjI)
  close 2 simp+
done

end
