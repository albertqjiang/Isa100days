theory P13 imports Main begin

fun list_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_union Nil xs = xs" | 
"list_union (y # ys) xs = 
(if (y \<in> (set xs)) 
  then (list_union ys xs) 
  else (y # list_union ys xs))"

lemma [simp]: "set (list_union xs ys) = set xs \<union> set ys"
proof (induct xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof -
    fix m
    assume 1: "set (list_union xs ys) = set xs \<union> set ys"
    thus "set (list_union (m # xs) ys) = set (m # xs) \<union> set ys"
    proof (cases "m \<in> set ys")
      case True
      hence "m \<in> (set xs \<union> set ys)" by simp
      hence "insert m (set xs \<union> set ys) = (set xs \<union> set ys)"
        by (simp add: insert_absorb)
      then show ?thesis using True
        by (simp add: Cons.hyps)
      next
        case False
        then show ?thesis by (simp add: Cons.hyps)
      qed
  qed
qed

lemma [simp]: "a \<notin> set xs \<Longrightarrow> a \<notin> set ys \<Longrightarrow> a \<notin> set (list_union xs ys)"
  by simp

lemma [rule_format]:
"distinct xs \<longrightarrow>  distinct ys \<longrightarrow> (distinct (list_union xs ys))"
proof (induct xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs) 
  have 1:"distinct (a # xs) \<Longrightarrow> a \<notin> (set xs)" by simp
  have 2: "distinct (a # xs) \<Longrightarrow> distinct xs" by simp
  then show ?case
  proof (cases "a \<in> set ys")
  case True
    then show ?thesis
      using Cons.hyps by auto
  next
    case False
    hence "list_union (a # xs) ys = a # list_union xs ys" by simp 
    then show ?thesis using Cons.hyps False 1 by auto
  qed
qed

lemma "((\<forall> x \<in> A. P x) \<and> (\<forall> x \<in> B. P x)) \<longrightarrow> (\<forall> x \<in> (A \<union> B). P x)"
  by auto

lemma "\<forall> x \<in> A. Q (f x) \<Longrightarrow> \<forall> y \<in> f ` A. Q y"
  by auto

end