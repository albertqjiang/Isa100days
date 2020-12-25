theory P26 imports Main begin

fun le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"le n Nil = True" |
"le n (x # xs) = (n\<le>x \<and> (le n xs))"

fun sorted :: "nat list \<Rightarrow> bool" where
"sorted Nil = True" |
"sorted (x # xs) = (le x xs \<and> (sorted xs))"

fun count :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"count Nil x = 0" |
"count (y # ys) x = (count ys x + (if x=y then 1 else 0))"

fun merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"merge xs Nil = xs" |
"merge Nil ys = ys" |
"merge (x # xs) (y # ys) = 
  (if x \<le> y then (x # (merge xs (y # ys))) 
  else (y # (merge (x # xs) ys)))"

fun msort :: "nat list \<Rightarrow> nat list" where
"msort Nil = Nil" |
"msort (x # Nil) = (x # Nil)" |
"msort xs = (merge (msort (take ((length xs) div 2) xs))
                   (msort (drop ((length xs) div 2) xs)))"

lemma [simp]: "x \<le> y \<Longrightarrow> le y xs \<Longrightarrow> le x xs"
  apply (induct xs)
  apply auto
  done

lemma [simp]: "le x (merge xs ys) = (le x xs \<and> le x ys)"
  apply (induct xs ys rule: merge.induct)
  apply auto
done

lemma [simp]: "sorted (merge xs ys) = (sorted xs \<and> sorted ys)"
  apply (induct xs ys rule: merge.induct)
    apply (auto simp add: linorder_not_le order_less_le)
  done

theorem "sorted (msort xs)"
  apply (induct xs rule: msort.induct)
    apply auto
  done

lemma [simp]: "count (merge xs ys) a = (count xs a) + (count ys a)"
  apply (induct xs ys rule: merge.induct)
    apply auto
  done

lemma [simp]: "count xs a + count ys a = (count (xs @ ys) a)"
  apply (induct xs)
   apply auto
  done

theorem "count (msort xs) x = count xs x"
  apply (induct xs rule: msort.induct)
    apply auto
  done

end