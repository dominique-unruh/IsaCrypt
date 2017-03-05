theory Scratch
imports Complex_Main 
begin

lemma N_subseteq_R: "\<nat> \<subseteq> \<real>"
  unfolding Nats_def Reals_def 
proof 
  fix x::'a assume "x \<in> range of_nat" 
  then obtain n where x:"x = of_nat n" by auto
  define r::real where "r = of_nat n"
  have "of_real r = x" 
    unfolding x r_def by (fact of_real_of_nat_eq)
  then show "x \<in> range of_real" by auto
qed

(*
instantiation bool :: real_algebra_1 begin
definition "one_bool = True"
definition "zero_bool = False"
definition "times_bool = op \<and>"
definition "plus_bool = (op \<noteq> :: bool\<Rightarrow>_\<Rightarrow>_)"
definition "scaleR_bool r b = False"
*)    
  
lemma N_neq_R: "\<nat> \<noteq> \<real>"
proof (rule ccontr)
  assume "\<not> \<nat> \<noteq> (\<real>::'a set)" then have same:"\<nat> = (\<real>::'a set)" by auto      
  define half::'a where "half = of_real (1/2)"
  then have "half \<in> \<real>" unfolding Reals_def by auto
  then have "half \<in> \<nat>" using same by simp
  then obtain n where n:"half = of_nat n" unfolding Nats_def by auto
  have "(of_nat (2*n) :: 'a) = of_real 2 * of_real (of_nat n)" by simp
  also have "\<dots> = of_real 2 * half" unfolding n by auto
  also have "\<dots> = of_real (2*(1/2))" unfolding half_def of_real_mult by simp
  also have "\<dots> = of_nat 1" by auto
  finally have "2*n = 1" using of_nat_eq_iff by blast 
  then show "False" by auto
qed
  
lemma "\<nat> \<subset> \<real>"
  using N_subseteq_R N_neq_R by rule


ML {*
  (* In reality, this would of course be a much more complex parser. *)
  val my_parser : term parser = Parse.nat >> HOLogic.mk_nat
  
  (* This function should invoke my_parser to parse the content of cartouche.
     Parse errors should be properly reported (i.e., with red highlighting in
    jEdit etc. *)
  fun parse_cartouche ctx (cartouche:string) (pos:Position.T) : term = 
    (warning ("I should parse: " ^ cartouche ^ ". Returning arbitrary term instead"); @{term True})

  (* Modified from Cartouche_Examples.thy *)
  fun cartouche_tr (ctx:Proof.context) args =
      let fun err () = raise TERM ("cartouche_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ (parse_cartouche ctx s pos) $ p
            | NONE => err ())
        | _ => err ())
      end;
*}

syntax "_my_syntax" :: "cartouche_position \<Rightarrow> 'a" ("MY_")
parse_translation \<open>[(@{syntax_const "_my_syntax"}, cartouche_tr)]\<close>

term "(MY \<open>123\<close>, 3)" (* Should parse as (123,3) *)

end
