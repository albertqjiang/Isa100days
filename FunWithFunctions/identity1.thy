theory identity1 imports Complex_Main begin

theorem identity1: fixes f :: "nat \<Rightarrow> nat"
assumes fff: "\<And>n. f(f(n)) < f(Suc(n))"
shows "f(n) = n"
proof -
  { fix m n have key: "m \<ge> n \<Longrightarrow> f(m) \<ge> n"
  proof (induct n arbitrary: m)
  case 0
    then show ?case by simp
  next
    case (Suc n)
    print_facts
    hence "m - 1 \<ge> n" by auto
    hence "f (m-1) \<ge> n" using Suc.hyps by auto
    hence 1: "f (f (m-1)) \<ge> n" using Suc.hyps by auto
    have "f m > f (f (m-1))" using assms
      by (metis One_nat_def Suc.prems Suc_diff_Suc Suc_le_D diff_zero less_Suc_eq_0_disj)
    hence "f m > n" using 1 by auto
    then show ?case by auto
  qed }
  hence "\<And>n. f n \<ge> n" by simp
  hence "\<And>n. f (n+1) > f n"
    by (metis Suc_eq_plus1 \<open>\<And>na m. na \<le> m \<Longrightarrow> na \<le> f m\<close> discrete fff not_less_eq_eq)
  hence "f n < n + 1"
    by (metis Suc_eq_plus1 fff lift_Suc_mono_less_iff)
  then show ?thesis
    by (metis Suc_eq_plus1 \<open>\<And>n. n \<le> f n\<close> less_antisym not_le)
qed

end