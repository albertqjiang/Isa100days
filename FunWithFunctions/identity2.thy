theory identity2 imports Complex_Main HOL.Power begin

lemma identity2: fixes f :: "nat \<Rightarrow> nat"
assumes "f(k) = k" and "k \<ge> 2"
and f_times: "\<And>m n. f(m*n) = f(m)*f(n)"
and f_mono: "\<And>m n. m<n \<Longrightarrow> f m < f n"
shows "f(n) = n"
proof -
  have incr: "\<And>n. f(n+1) \<ge> f(n) + 1"
    using f_mono mono_nat_linear_lb by blast
  have add_m: "\<And>n m. m\<ge>0 \<Longrightarrow> f(n+m) \<ge> f(n) + m"
    using f_mono mono_nat_linear_lb incr by blast
  have leq_than_k: "\<And>m. m\<le>k \<Longrightarrow> f(m) = m"
  proof -
    have "\<And>m. m\<le>k \<Longrightarrow> k = m + (k-m)" by arith
    then show "\<And>m. m\<le>k \<Longrightarrow> f(m) = m" using add_m
    proof -
      fix m :: nat
      assume a1: "m \<le> k"
      assume "\<And>m. m \<le> k \<Longrightarrow> k = m + (k - m)"
      have "m + (k - m) = k" using a1 by presburger
      then show "f m = m"
        using a1 by (metis (no_types) Nat.le_diff_conv2 \<open>\<And>n m. 0 \<le> m \<Longrightarrow> f n + m \<le> f (n + m)\<close>
            add.commute add.left_neutral add_diff_cancel_right' add_leD1 assms(1) le_antisym)
    qed
  qed
  have 0: "f(0) = 0" using assms(2) by (simp add: leq_than_k)
  have 1: "f(1) = 1" using assms(2) by (simp add: leq_than_k)
  have 2: "f(2) = 2" using assms(2) by (simp add: leq_than_k)
  have two_power: "f ((2::nat) ^ n) = 2 ^ n"
  proof (induct n)
    case 0
    then show ?case using 1 by simp
  next
    case (Suc x)
    then show ?case using 2 f_times by auto
  qed
  have interval: "\<And>n1 n2. f(n1) = n1 \<Longrightarrow> f(n2) = n2 \<Longrightarrow> (\<And>p. p\<ge>n1 \<Longrightarrow> p\<le>n2 \<Longrightarrow> f(p) = p)"
    by (metis add.commute add_le_cancel_right add_m le_add_diff_inverse2 le_antisym zero_le)
  have u_bound: "\<exists>n2. 2^n2 \<ge> n" using self_le_ge2_pow by blast
  
  show ?thesis
  proof (cases "n\<ge>2")
    case True
    then have "n \<ge> 2^0" by simp
    have "f (2^0) = 2^0" using 1 by simp
    have "n \<le> 2^n" by simp
    have "f (2^n) = 2^n" using two_power by blast
    then show ?thesis using interval two_power
      using "2" True \<open>n \<le> 2 ^ n\<close> by blast
  next
    case False
    then show ?thesis using 0 1
      using assms(2) le_trans leq_than_k nat_le_linear by blast
  qed
qed

end