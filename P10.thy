theory P10 imports Main begin

fun sq :: "nat \<Rightarrow> nat" where
"sq 0 = 0" | "sq (Suc n) = (sq n) + n + (Suc n)"

theorem [simp]: "sq n = n * n"
  apply (induct n)
   apply auto
  done

lemma [simp]: "m\<le>n \<Longrightarrow> (Suc n - m) = (Suc (n - m))"
  apply (induct n)
   apply auto
  done

lemma aux[rule_format]: "\<forall>m. m <= n \<longrightarrow> sq n = ((n + (n-m))* m) + sq (n-m)"
  apply (induct_tac n, auto)
  apply (case_tac m, auto)
  done

theorem MM2: "100 \<le> n \<Longrightarrow> sq n = ((n + (n - 100))* 100) + sq (n - 100)"
  by (rule aux)

lemma binomial [simp]: "sq (a+b) = (sq a + sq b + 2 * a * b)"
  apply (induct a)
   apply auto
  done

theorem MM3: "sq((10 * n) + 5) = ((n * (Suc n)) * 100) + 25"
proof (induct n)
case 0
  then show ?case by simp
next
  case (Suc n)
  assume "sq (10 * n + 5) = n * Suc n * 100 + 25"
  have "sq (10 * Suc n + 5) = sq (10 * n + 10 + 5)" by simp
  also have "\<dots> = sq (10 * n + 15)" by (simp add: add.assoc)
  also have "\<dots> = (sq (10 * n) + sq 15 + (2 * (10 * n) * 15))" using P10.binomial by blast
  also have "\<dots> = ((10 * n * 10 * n) + sq 15 + (2 * (10 * n) * 15))" by simp
  also have "\<dots> = ((100 * n * n) + sq 15 + (2 * (10 * n) * 15))" by simp
  also have "\<dots> = ((100 * n * n) + 225 + (30 * (10 * n)))" by simp
  finally have "\<dots> = ((100 * n * n) + (300 * n) + 225)" by (simp add: add.assoc)
  hence 1: "sq (10 * Suc n + 5) = ((100 * n * n) + (300 * n) + 225)"
    using \<open>sq (10 * n + 10 + 5) = sq (10 * n + 15)\<close>
          \<open>sq (10 * n + 15) = sq (10 * n) + sq 15 + 2 * (10 * n) * 15\<close> by auto
  have "Suc n * Suc (Suc n) * 100 + 25 = (n+1) * (n+1+1) * 100 + 25" by simp
  also have "\<dots> = (n+1) * (n+2) * 100 + 25" by simp
  also have "\<dots> = (n*n + 3 * n + 2) * 100 + 25" by simp
  also have "\<dots> = (100 * n * n) + (300 * n) + 25 + 200" by simp
  finally have "\<dots> = ((100 * n * n) + 225 + (30 * (10 * n)))" by simp
  hence 2: "Suc n * Suc (Suc n) * 100 + 25 = ((100 * n * n) + 225 + (30 * (10 * n)))"
    by simp
  then show ?case using 1 2 by simp
qed

end