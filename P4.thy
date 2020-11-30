theory P4 imports Main
begin

fun alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"alls Q Nil = True" |
"alls Q (x # xs) = ((Q x) \<and> (alls Q xs))"

fun exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"exs Q Nil \<longleftrightarrow> False" |
"exs Q (x # xs) \<longleftrightarrow> (Q x) \<or> (exs Q xs)"

lemma "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
  apply (induct xs)
   apply auto
  done

lemma [simp]: "alls P (xs @ [x]) = (P x \<and> (alls P xs))"
  apply (induct xs)
   apply auto
  done

lemma [simp]: "exs P (xs @ [x]) = (P x \<or> (exs P xs))"
  apply (induct xs)
   apply auto
  done

lemma "alls P (rev xs) = alls P xs" 
proof (induct xs)
case Nil
  then show "alls P (rev []) = alls P []" by simp
next
case (Cons a xs)
  then show "alls P (rev (a # xs)) = alls P (a # xs)" by simp
qed

lemma "exs (\<lambda>x. P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
  nitpick
  oops

lemma "exs P (map f xs) = exs (P o f) xs"
  apply (induct xs)
   apply auto
  done

lemma "exs P (rev xs) = exs P xs"
  apply (induct xs)
   apply auto
  done

lemma "exs (\<lambda>x. P x \<or> Q x) xs = ((exs P xs) \<or> (exs Q xs))"
  apply (induct xs)
   apply auto
  done

lemma "exs P xs = (\<not>(alls (\<lambda>x. (\<not> P x)) xs))"
  apply (induct xs)
   apply auto
  done

fun is_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_in x Nil = False" | 
"is_in x (y # xs) = (if x=y then True else (is_in x xs))"

lemma "is_in a xs = (exs (\<lambda>x. a=x) xs)"
  apply (induct xs)
  apply auto
  done

fun nodups :: "'a list \<Rightarrow> bool" where
"nodups Nil = True" | "nodups (x # xs) = (\<not>(is_in x xs) \<and> (nodups xs))"

fun del_element :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"del_element x Nil = Nil" | 
"del_element x (y # xs) = (if x=y then (del_element x xs) else (y # (del_element x xs)))"

fun deldups :: "'a list \<Rightarrow> 'a list" where
"deldups Nil = Nil" | "deldups (x # xs) = (x # (del_element x (deldups xs)))"

lemma [simp]: "length (del_element x xs) \<le> length xs"
  apply (induct xs)
   apply auto
  done

lemma "length (deldups xs) <= length xs"
  apply (induct xs)
   apply auto
  sorry

end