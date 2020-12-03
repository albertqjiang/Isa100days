theory P7 imports Main begin

fun sum :: "nat list \<Rightarrow> nat" where
"sum Nil = 0" |
"sum (x # xs) = (x + (sum xs))"

fun flatten :: "'a list list \<Rightarrow> 'a list" where
"flatten Nil = Nil" |
"flatten (xs # xss) = xs @ (flatten xss)"

lemma "sum [2::nat, 4, 8] = 14"
  by simp

lemma "flatten [[2::nat, 3], [4, 5], [7, 9]] = [2::nat, 3, 4, 5, 7, 9]"
  by simp

lemma "length (flatten xs) = sum (map length xs)"
  apply (induct xs)
   apply auto
  done

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
  apply (induct xs)
   apply auto
  done

lemma flatten_append[simp]: "flatten (xs @ ys) = flatten xs @ flatten ys"
  apply (induct xs)
   apply auto
  done

lemma "flatten (map rev (rev xs)) = rev (flatten xs)"
  apply (induct xs)
   apply auto
  done

lemma "flatten (rev (map rev xs)) = rev (flatten xs)"
  apply (induct xs)
   apply auto
  done

lemma "list_all (list_all P) xs = list_all P (flatten xs)"
  apply (induct xs)
   apply auto
  done

lemma "flatten (rev xs) = flatten xs"
  nitpick
  oops

lemma [simp]: "sum (xs @ [x]) = x + (sum xs)"
  apply (induct xs)
   apply auto
  done

lemma "sum (rev xs) = sum xs"
  apply (induct xs)
   apply auto
  done

lemma "list_all (\<lambda>x. x\<ge>1) xs \<longrightarrow> length xs \<le> sum xs"
  apply (induct xs)
   apply auto
  done

fun list_exists:: "('a \<Rightarrow> bool) \<Rightarrow> ('a list) \<Rightarrow> bool" where
"list_exists P Nil = False" |
"list_exists P (x # xs) = (if (P x) then True else (list_exists P xs))"

lemma "list_exists (\<lambda> n. n < 3) [4::nat, 3, 7] = False"
  by simp

lemma "list_exists (\<lambda> n. n < 4) [4::nat, 3, 7] = True"
  by simp

lemma list_exists_append[simp]: "list_exists P (xs @ ys) = (list_exists P xs \<or> list_exists P ys)"
  apply (induct xs)
   apply auto
  done

lemma "list_exists (list_exists P) xs = list_exists P (flatten xs)"
  apply (induct xs)
   apply auto
  done

fun list_exists2:: "('a \<Rightarrow> bool) \<Rightarrow> ('a list) \<Rightarrow> bool" where
"list_exists2 P xs = (\<not> list_all (\<lambda>x. (\<not> P x)) xs)"

lemma list_exists_equ: "list_exists2 P xs = list_exists P xs"
  apply (induct xs)
   apply auto
  done

end