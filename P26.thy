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
"msort xs = (merge (take ((length xs) div 2) xs) (drop ((length xs) div 2) xs))"


end