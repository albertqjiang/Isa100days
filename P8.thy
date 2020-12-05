theory P9 imports Main P6 begin
fun ListSum :: "nat list \<Rightarrow> nat" where
"ListSum Nil = 0" | "ListSum (x # xs) = (x + ListSum xs)"

lemma [simp]: "ListSum (xs @ ys) = (ListSum xs + ListSum ys)"
  apply (induct xs)
   apply auto
  done

theorem "2 * ListSum [0..<n+1] = n * (n + 1)"
  apply (induct n)
   apply auto
  done

theorem "ListSum (replicate n a) = n * a"
  apply (induct n)
   apply auto
  done

fun ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"ListSumTAux Nil a = a" | "ListSumTAux (x # xs) a = (ListSumTAux xs (x+a))"

fun ListSumT :: "nat list \<Rightarrow> nat" where
"ListSumT xs = ListSumTAux xs 0"

lemma move_a: "\<forall>a. \<forall>b. ListSumTAux xs (a + b) = (ListSumTAux (a # xs) b)"
  apply simp
  done

lemma [simp]: "\<forall>y. x + ListSumTAux xs y = ListSumTAux xs (x + y)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof -
    assume "\<forall>y. x + ListSumTAux xs y = ListSumTAux xs (x + y)"
    have 1: "x + ListSumTAux (a # xs) y = x + (ListSumTAux xs (a + y))" 
      using ListSumTAux.simps(2)
      by presburger
    then show ?thesis
      by (simp add: Cons.hyps add.left_commute)
      qed
qed

theorem "ListSum xs = ListSumT xs"
  apply (induct xs)
   apply auto
  done

end