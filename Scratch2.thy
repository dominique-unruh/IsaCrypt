theory Scratch2
imports Main Tools
begin

ML Thy_Info.use_thy

lemma "1=1 \<and> 2=2"
 apply (rule conjI) 
  close simp
 close
done
 
end