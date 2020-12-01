theory P5 imports Main begin

fun first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"first_pos P Nil = 0" | 
"first_pos P (x # xs) = (if (P x) then 0 else (Suc (first_pos P xs)))"

lemma "first_pos (\<lambda>x. x=3) [1::nat, 3, 5, 3, 1] = 1"
  apply simp
  done

lemma "first_pos (\<lambda>x. x>4) [1::nat, 3, 5, 3, 1] = 2"
  apply simp
  done

lemma "first_pos (\<lambda>x. (length x > 1)) [[], [1, 2], [3]] = 1"
  apply simp
  done

fun member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
"member Nil x = False" | "member (y # xs) x = (if (x=y) then True else (member xs x))"

lemma [simp]:"((first_pos P xs) = (length xs)) \<longrightarrow> \<not> (\<exists>x. member xs x \<and> P x)"
  apply (induct xs)
   apply auto
  done

lemma [simp]: "\<not> (\<exists>x. member xs x \<and> P x) \<longrightarrow> ((first_pos P xs) = (length xs))"
  apply (induct xs)
   apply auto
  done

theorem "((first_pos P xs) = (length xs)) \<longrightarrow> \<not> (\<exists>x. member xs x \<and> P x)"
  apply simp
  done

lemma "list_all (\<lambda> x. \<not> P x) (take (first_pos P xs) xs)"
  apply (induct xs)
   apply auto
  done

fun min :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"min m n = (if m \<le> n then m else n)"

fun max :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"max m n = (if m \<ge> n then m else n)"

theorem "first_pos (\<lambda> x. P x \<or> Q x) xs = (min (first_pos P xs) (first_pos Q xs))"
  apply (induct xs)
   apply auto
  done

theorem "first_pos (\<lambda> x. P x \<and> Q x) xs = (max (first_pos P xs) (first_pos Q xs))"
  nitpick
  oops

theorem "\<forall>x. (P x \<longrightarrow> (Q x)) \<Longrightarrow> ((first_pos P xs) \<ge> (first_pos Q xs))"
  apply (induct xs)
   apply auto
  done

fun count :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"count P Nil = 0" | 
"count P (x # xs) = (if (P x) then (Suc (count P xs)) else (count P xs))"

lemma [simp]: "count P (xs @ [a]) = (if (P a) then (Suc (count P xs)) else (count P xs))"
  apply (induct xs)
   apply auto
  done

theorem "count P xs = (count P (rev xs))"
  apply (induct xs)
   apply auto
  done

theorem "count P xs = (length (filter P xs))"
  apply (induct xs)
   apply auto
  done

end