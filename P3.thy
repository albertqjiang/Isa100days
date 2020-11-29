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

end

