theory P9 imports Main begin

fun pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"pow x 0 = 1" | "pow x (Suc n) = (x * (pow x n))"

lemma pow_mul [simp]: "pow x m * pow x n = (pow x (m+n))"
  apply (induct n)
   apply auto
  done

theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
proof (induct n)
case 0
  thus ?case by simp
next
  case (Suc a)
  thus ?case
  proof -
    assume 1: "pow x (m * a) = pow (pow x m) a"
    have "pow (pow x m) (Suc a) = pow (pow x m) 1 * pow (pow x m) a" by simp
    also have "... = pow x (m * 1) * pow x (m * a)" using 1 by simp
    finally have "... = pow x (m * 1 + m * a)" by simp
    thus "pow x (m * Suc a) = pow (pow x m) (Suc a)" using 1 by simp
  qed
qed

fun sum :: "nat list \<Rightarrow> nat" where
"sum Nil = 0" | "sum (x # xs) = (x + sum xs)"

lemma [simp]: "sum (ns @ [a]) = a + (sum ns)"
  apply (induct ns)
   apply auto
  done

theorem sum_rev: "sum (rev ns) = sum ns"
  apply (induct ns)
   apply auto
  done

fun Sum :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"Sum f 0 = 0" | "Sum f (Suc n::nat) = f n + Sum f n"

theorem "Sum (\<lambda>i. f i + g i) k = Sum f k + Sum g k"
  apply (induct k)
   apply auto
  done

theorem "Sum f (k + l) = Sum f k + (if (l=0) then 0 else Sum (\<lambda>x. f (k+x)) l)"
  apply (induct l)
  apply auto
  done

theorem "Sum f k = sum (map f [0..<k])"
  apply (induct k)
   apply auto
  done

end