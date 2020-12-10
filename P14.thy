theory P14 imports Main begin

primrec zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
zip1FstEmp: "zip1 Nil ys = ys" |
zip1Indt: "zip1 (x # xs) ys = x # (take 1 ys) @ (zip1 xs (drop 1 ys))"

primrec zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
zip2SndEmp: "zip2 xs Nil = xs" |
zip2Indt: "zip2 xs (y # ys) = (take 1 xs)@ [y] @ (zip2 (drop 1 xs) ys)"

fun zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"zipr Nil ys = ys" |
"zipr xs Nil = xs" |
"zipr (x # xs) (y # ys) = [x, y] @ (zipr xs ys)"

lemma [simp]: "zipr (a # xs) ys = a # (take 1 ys) @ (zipr xs (drop 1 ys))"
  apply (induct ys)
   apply auto
  apply (metis neq_Nil_conv zipr.simps(1) zipr.simps(2))
  done

lemma [simp]: "zip1 xs Nil = xs"
  apply (induct xs)
  apply auto
  done

lemma [simp]: "zip2 Nil ys = ys"
  apply (induct ys)
  apply auto
  done

lemma [simp]: "zipr xs Nil = xs"
  apply (induct xs)
  apply auto
  done

lemma "zip1 xs ys = zipr xs ys"
proof (induct ys arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  then show ?case
  proof (cases "xs = Nil")
    case True
  then show ?thesis by simp
  next
    case False
    then obtain a as where "xs = (a # as)"
      using list.exhaust_sel by blast
    then show ?thesis using Cons.hyps by simp
  qed
qed

lemma "zip2 xs ys = zipr xs ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  then show ?case
  proof (cases "ys = Nil")
    case True
  then show ?thesis by simp
  next
    case False
    then obtain a as where "ys = (a # as)"
      using list.exhaust_sel by blast
    then show ?thesis using Cons.hyps by simp
  qed
qed

lemma "\<lbrakk>length p = length u; length q = length v\<rbrakk> \<Longrightarrow> zipr (p@q) (u@v) = zipr p u @ zipr q v"
  apply (induct p arbitrary: u q v)
   apply auto
  done


end