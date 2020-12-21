theory P25 imports Main begin

datatype bintree = Tip | Node bintree nat bintree

fun tge :: "nat \<Rightarrow> bintree \<Rightarrow> bool" where
"tge n Tip = True" |
"tge n (Node l m r) = ((tge n l) \<and> (n \<ge> m) \<and> (tge n r))"

fun tle :: "nat \<Rightarrow> bintree \<Rightarrow> bool" where
"tle n Tip = True" |
"tle n (Node l m r) = ((tle n l) \<and> (n \<le> m) \<and> (tle n r))"

fun tsorted :: "bintree \<Rightarrow> bool" where
"tsorted Tip = True" |
"tsorted (Node l m r) = ((tsorted l) \<and> (tsorted r) \<and> (tge m l) \<and> (tle m r))"

fun ins :: "nat \<Rightarrow> bintree \<Rightarrow> bintree" where
"ins n Tip = (Node Tip n Tip)" |
"ins n (Node l m r) = (if (n \<le> m) then (Node (ins n l) m r) else (Node l m (ins n r)))"

definition tree_of :: "nat list \<Rightarrow> bintree" where
"tree_of xs = (foldr ins xs Tip)"

lemma tge_inva: "tge x xt \<Longrightarrow> a \<le> x \<Longrightarrow> tge x (ins a xt)"
  apply (induct xt)
   apply auto
  done

lemma tle_inva: "tle x xt \<Longrightarrow> \<not>(a \<le> x) \<Longrightarrow> tle x (ins a xt)"
  apply (induct xt)
   apply auto
  done

lemma [simp]: "tsorted xb \<Longrightarrow> tsorted (ins a xb)"
proof (induct xb arbitrary: a)
  case Tip
  then show ?case by simp
next
  case (Node xb1 x2 xb2)
  then show ?case
  proof (cases "a\<le>x2")
    case True
    print_facts
    have "tge x2 xb1" using Node.prems by simp
    have "ins a (Node xb1 x2 xb2) = (Node (ins a xb1) x2 xb2)"
      by (simp add: True)
    then have "tsorted (ins a (Node xb1 x2 xb2)) = tsorted (Node (ins a xb1) x2 xb2)" by simp
    also have "\<dots> = ((tsorted (ins a xb1)) \<and> (tsorted xb2) \<and> (tge x2 (ins a xb1)) \<and> (tle x2 xb2))"
      by simp
    also have "\<dots> = (tge x2 (ins a xb1))" using Node.hyps Node.prems by auto
    also have "\<dots> = True" using tge_inva True \<open>tge x2 xb1\<close> by blast
    finally have "tsorted (ins a (Node xb1 x2 xb2)) = True" by blast
    then show ?thesis by simp
  next
    case False
    have "tle x2 xb2" using Node.prems by simp
    have "ins a (Node xb1 x2 xb2) = (Node xb1 x2 (ins a xb2))" using False by simp
    then have "tsorted (ins a (Node xb1 x2 xb2)) = tsorted (Node xb1 x2 (ins a xb2))" by simp
    also have "\<dots> = ((tsorted xb1) \<and> (tsorted (ins a xb2)) \<and> (tge x2 xb1) \<and> (tle x2 (ins a xb2)))"
      by simp
    also have "\<dots> = (tle x2 (ins a xb2))" using Node.hyps Node.prems by auto
    also have "\<dots> = True" using tle_inva False \<open>tle x2 xb2\<close> by blast
    finally have "tsorted (ins a (Node xb1 x2 xb2))" by blast
    then show ?thesis by simp
  qed
qed

theorem [simp]: "tsorted (tree_of xs)"
  apply (induct xs)
   apply (auto simp add: tree_of_def)
  done

primrec count :: "nat list => nat => nat" where
"count [] y = 0" | 
"count (x#xs) y = (if x=y then Suc(count xs y) else count xs y)"

lemma [simp]: "count (a # xs) x = (count xs x) + (if (x=a) then 1 else 0)"
  apply (induct xs)
   apply auto
  done

fun tcount :: "bintree \<Rightarrow> nat \<Rightarrow> nat" where
"tcount Tip n = 0" |
"tcount (Node l x r) n = (tcount l n) + (tcount r n) + (if (x=n) then 1 else 0)"

lemma [simp]: "tcount (ins a xs) x = (tcount xs x) + (if x=a then 1 else 0)"
  apply (induct xs)
   apply auto
  done

lemma [simp]: "tcount (tree_of (a # xs)) x = (tcount (tree_of xs) x + (if (x=a) then 1 else 0))"
  apply (induct xs)
   apply (auto simp add: tree_of_def)
  done

theorem "tcount (tree_of xs) x = count xs x"
proof (induct xs)
case Nil
then show ?case by (simp add: tree_of_def)
next
  case (Cons a xs)
  then show ?case by simp
qed

primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"le n Nil = True" |
"le n (x # xs) = (n \<le> x \<and> le n xs)"

primrec ge :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"ge n Nil = True" | 
"ge n (x # xs) = (x \<le> n \<and> ge n xs)"

primrec sorted :: "nat list \<Rightarrow> bool" where
"sorted [] = True"
| "sorted (x#xs) = (le x xs & sorted xs)"

lemma [simp]: "le x (a@b) = (le x a \<and> le x b)"
  apply (induct a)
  apply auto
  done

lemma [simp]: "ge x (a@b) = (ge x a \<and> ge x b)"
  apply (induct a)
  apply auto
  done

lemma [simp]: "x \<le> y \<Longrightarrow> le y xs \<Longrightarrow> le x xs"
  apply (induct xs)
  apply auto
  done

lemma [simp]: "sorted (a@x#b) = (sorted a \<and> sorted b \<and> ge x a \<and> le x b)"
  apply (induct a)
  apply auto
  done

fun list_of :: "bintree \<Rightarrow> nat list" where
"list_of Tip = Nil" |
"list_of (Node l x r) = (list_of l) @ [x] @ (list_of r)"

lemma [simp]: "ge n (list_of t) = tge n t"
  apply (induct t)
  apply auto
  done

lemma [simp]: "le n (list_of t) = tle n t"
  apply (induct t)
   apply auto
  done

lemma [simp]: "sorted (list_of t) = tsorted t"
  apply (induct t)
  apply auto
  done

theorem "sorted (list_of (tree_of xs))"
  apply (induct xs)
   apply (auto simp add: tree_of_def)
  done

lemma count_append [simp]: "count (a@b) n = count a n + count b n"
  apply (induct a)
  apply auto
  done

lemma [simp]: "count (list_of b) n = tcount b n"
  apply (induct b)
  apply auto
  done

theorem "count (list_of (tree_of xs)) n = count xs n"
  apply (induct xs)
   apply (auto simp add: tree_of_def)
  done

end