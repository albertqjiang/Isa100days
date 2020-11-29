theory P3 imports Main
begin

fun replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
"replace x y Nil = Nil" | 
"(replace x y (Cons z xs)) = (if x=z then (Cons y (replace x y xs)) else (Cons z (replace x y xs)))"

lemma [simp]: "replace x y (zs @ [y]) = replace x y (zs @[x])"
  apply (induct zs)
   apply auto
  done

lemma [simp]: "replace x y (zs @ [x]) = replace x y zs @ [y]"
  apply (induct zs)
   apply auto
  done

lemma [simp]: "x \<noteq> a \<Longrightarrow> replace x y zs @ [a] = replace x y (zs @ [a])"
  apply (induct zs)
   apply auto
  done

theorem "rev(replace x y zs) = replace x y (rev zs)"
  apply (induct zs)
   apply auto
  done

lemma "replace x y (replace u v zs) = replace u v (replace x y zs)"
  nitpick
  oops

lemma "replace y z (replace x y zs) = replace x z zs"
  nitpick
  oops

fun del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"del1 x Nil = Nil" |
"del1 x (y # xs) = (if x=y then xs else (y # xs))"

fun delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"delall x Nil = Nil" |
"delall x (y # xs) = (if x=y then (delall x xs) else (y # (delall x xs)))"

theorem "del1 x (delall x xs) = delall x xs"
  apply (induct xs)
   apply auto
  done

theorem "delall x (delall x xs) = delall x xs"
  apply (induct xs)
   apply auto
  done

theorem "delall x (del1 x xs) = delall x xs"
  apply (induct xs)
   apply auto
  done

lemma "del1 x (del1 y zs) = del1 y (del1 x zs)"
  nitpick
  oops

lemma "delall x (del1 y zs) = del1 y (delall x zs)"
  nitpick
  oops

theorem "delall x (delall y xs) = delall y (delall x xs)"
  apply (induct xs)
   apply auto
  done

lemma "del1 y (replace x y xs) = del1 x xs"
  nitpick
  oops

lemma "delall y (replace x y xs) = delall x xs"
  nitpick
  oops

theorem "replace x y (delall x xs) = delall x xs"
  apply (induct xs)
   apply auto
  done

lemma "replace x y (delall z xs) = delall z (replace x y xs)"
  nitpick
  oops

lemma "rev(del1 x xs) = del1 x (rev xs)"
  nitpick
  oops

lemma [simp]: "delall x (xs @ [x]) = delall x xs"
  apply (induct xs)
  apply auto
  done

lemma [simp]: "x \<noteq> a \<Longrightarrow> delall x xs @ [a] = delall x (xs @ [a])"
  apply (induct xs)
   apply auto
  done

theorem "rev(delall x xs) = delall x (rev xs)"
  apply (induct xs)
   apply auto
  done

end

