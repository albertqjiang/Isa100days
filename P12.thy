theory P12 imports Main begin

lemma I: "A \<longrightarrow> A"
  apply (rule impI)
  apply assumption
  done

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (rule conjI)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (rule disjI1)
  apply (erule conjE)
  apply assumption
  done

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
  apply (rule impI)
  apply (erule disjE)
   apply (erule disjE)
    apply (rule disjI1)
    apply assumption
   apply (rule disjI2)
   apply (rule disjI1)
   apply assumption
  apply (rule disjI2)
  apply (rule disjI2)
  apply assumption
  done

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
  apply (rule impI)
  apply (rule impI)
  apply assumption
  done

lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)
   apply (erule disjE)
  apply (rule conjI)
   apply assumption+
  apply (rule conjI)
    apply assumption+
  apply (rule disjI1)
  apply (erule conjE)
  apply assumption
  done

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (erule impE)+
    apply assumption+
  apply (erule mp)
  apply (erule impE)
   apply assumption+
  done

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (erule mp)
  apply (erule impE)
   apply assumption+
  done

lemma "\<not>\<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B\<longrightarrow> A)"
  apply (rule impI)+
  apply (rule classical)
  apply (erule notE)
  apply (erule impE)
   apply assumption+
  done

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI)+
  apply (rule classical)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
   apply assumption+
  done

lemma "A \<or> \<not> A"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
  apply (rule iffI)

  apply (rule classical)
  apply (erule notE)
  apply (rule conjI)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
   apply assumption

  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

end