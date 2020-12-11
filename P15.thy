theory P15 imports Main begin

lemma "(\<exists> x. \<forall> y. P x y) \<longrightarrow>  (\<forall> y. \<exists> x. P x y)"
  apply (rule impI)
  apply (erule exE)
  apply (rule allI)
  apply (erule allE)
  apply (rule exI)
  apply assumption
  done
  
lemma "(\<forall> x. P x \<longrightarrow> Q) = ((\<exists> x. P x) \<longrightarrow> Q)"
  apply (rule iffI)

   apply (rule impI)
   apply (erule exE)
   apply (erule allE)
   apply (erule impE)
  apply assumption+

  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
  apply (rule exI)
   apply assumption+
  done

lemma "((\<forall> x. P x) \<and> (\<forall> x. Q x)) = (\<forall> x. (P x \<and> Q x))"
  apply (rule iffI)

   apply (erule conjE)
   apply (rule allI)
   apply (rule conjI)
    apply (erule allE)
    apply assumption
   apply (erule allE)+
   apply assumption

  apply (rule conjI)
   apply (rule allI)
   apply (erule allE)
   apply (erule conjE)
   apply assumption
   apply (rule allI)
   apply (erule allE)
   apply (erule conjE)
   apply assumption
  done

lemma "((\<forall> x. P x) \<or> (\<forall> x. Q x)) = (\<forall> x. (P x \<or> Q x))"
  nitpick
  oops

lemma "((\<exists> x. P x) \<or> (\<exists> x. Q x)) = (\<exists> x. (P x \<or> Q x))"
  apply (rule iffI)

   apply (erule disjE)
    apply (erule exE)
    apply (rule exI)
    apply (rule disjI1)
    apply assumption
   apply (erule exE)
   apply (rule exI)
   apply (rule disjI2)
   apply assumption

  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule exI)
   apply assumption

  apply (rule disjI2)
   apply (rule exI)
  apply assumption
  done

lemma "(\<forall> x. \<exists> y. P x y) \<longrightarrow> (\<exists> y. \<forall> x. P x y)"
  nitpick
  oops

lemma "(\<not> (\<forall> x. P x)) = (\<exists> x. \<not> P x)"
  apply (rule iffI)
  apply (rule classical)
   apply (erule notE)
   apply (rule allI)
   apply (rule classical)
   apply (erule notE)
   apply (rule exI)
   apply assumption

  apply (erule exE)
  apply (rule notI)
  apply (erule notE)
  apply (erule allE)
  apply assumption
  done

end