theory P24 imports Main begin

primrec insort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
"insort x Nil = [x]" |
"insort x (y # ys) = (if (x < y) then ([x, y] @ ys) else (y # (insort x ys)))"

primrec sort :: "nat list \<Rightarrow> nat list" where
"sort Nil = Nil" |
"sort (x # xs) = (insort x (sort xs))"

primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"le n Nil = True" |
"le n (x # xs) = ((n \<le> x) \<and> (le n xs))"

primrec sorted :: "nat list \<Rightarrow> bool" where
"sorted Nil = True" |
"sorted (x # xs) = (if xs = Nil then True else ((x \<le> hd xs) \<and> sorted xs))"

lemma [simp]: "x \<le> y \<Longrightarrow> le y xs \<longrightarrow> le x xs"
  apply (rule impI)
  apply (induct xs)
   apply auto
  done

lemma [simp]: "P24.sorted xs \<Longrightarrow> P24.sorted (P24.insort a xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
  proof (cases xs)
    case Nil
  then show ?thesis by simp
  next
    case (Cons y ys)
    then show ?thesis
      using Cons.hyps Cons.prems by auto
  qed
qed

theorem "sorted (sort xs)"
  apply (induct xs)
   apply auto
  done

fun count :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"count xs n = length (filter (\<lambda>x. x=n) xs)"

lemma [simp]: "count (a # xs) x = (count xs x) + (if (x=a) then 1 else 0)"
  apply (induct xs)
   apply auto
  done

lemma insort_length[simp]: "count (insort a xs) x = (count xs x) + (if (x=a) then 1 else 0)"
  apply (induct xs arbitrary: a x)
   apply auto
  done

theorem "count (sort xs) x = count xs x"
proof (induct xs arbitrary: x)
case Nil
then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases "x=a")
    case True
    print_facts
    have "count (sort (a # xs)) x = (count (sort xs) x + 1)"
      using True insort_length by auto
    also have "\<dots> = (count xs x + 1)" using Cons.hyps by auto
    finally have 1: "count (P24.sort (a # xs)) x =(count xs x + 1)" by blast
    have "count (a # xs) x = (count xs x + 1)" using True by simp
    then show ?thesis using 1 by auto
  next
    case False
    have "count (sort (a # xs)) x = count (insort a (sort xs)) x" by simp
    also have "\<dots> = count (sort xs) x" using False insort_length by auto
    also have "\<dots> = count xs x" using Cons.hyps by simp
    finally have 1: "count (sort (a # xs)) x = count xs x" by blast
    have "count (a # xs) x = count xs x" using False by simp
    then show ?thesis using 1 by auto
  qed
qed



end