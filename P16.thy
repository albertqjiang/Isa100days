theory P16 imports Main begin

lemma "\<forall> x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> \<exists> x. rich (father (father x)) \<and> rich x"
proof -
  assume "\<forall> x. \<not> rich x \<longrightarrow> rich (father x)"
  then obtain r where "rich r" by blast
  then show ?thesis using \<open>\<forall>x. \<not> rich x \<longrightarrow> rich (father x)\<close> by blast
qed

end