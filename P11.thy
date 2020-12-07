theory P11 imports Main begin

lemma eq_conv: "(A=B) = ((A\<longrightarrow>B) \<and> (B\<longrightarrow>A))"
  by blast

lemma neg_conv: "\<not>A = (A\<longrightarrow>False)"
  by blast

lemma or_conv: "(A\<or>B) = ((A\<longrightarrow>False)\<longrightarrow>B)"
  by blast

lemma "A \<or> (B \<and> C) = A"
proof (simp only: eq_conv neg_conv or_conv)
  oops


end