theory P6 imports Main begin

fun occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"occurs x Nil = 0" | 
"occurs x (y # xs) = (if x=y then (Suc (occurs x xs)) else (occurs x xs))"

lemma [simp]: "occurs a (xs @ [b]) = (if (a=b) then (Suc (occurs a xs)) else (occurs a xs))"
  apply (induct xs)
  apply auto
  done

theorem "occurs a xs = occurs a (rev xs)"
  apply (induct xs)
   apply auto
  done

theorem "occurs a xs <= length xs"
  apply (induct xs)
  apply auto
  done

lemma "occurs a (map f xs) = occurs (f a) xs"
  nitpick
  oops

theorem "occurs a (filter P xs) = (occurs True (map (\<lambda>x. (P x \<and> (x=a))) xs))"
  apply (induct xs)
   apply auto
  done

fun remDups :: "'a list \<Rightarrow> 'a list" where
"remDups Nil = Nil" | 
"remDups (x # xs) = (if (occurs x xs > 0) then (remDups xs) else (x # (remDups xs)))"

theorem [simp]: "occurs x (remDups xs) = (if (occurs x xs > 0) then 1 else 0)"
  apply (induct xs)
   apply auto
  done

fun unique :: "'a list \<Rightarrow> bool" where
"unique Nil = True" |
"unique (x # xs) = (if (occurs x xs > 0) then False else (unique xs))"

theorem "unique (remDups xs)"
  apply (induct xs)
   apply auto
  done

end