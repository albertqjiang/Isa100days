theory P19 imports Main begin

primrec sum :: "nat list \<Rightarrow> nat" where
"sum [] = 0"
| "sum (x # xs) = x + sum xs"

lemma sum_foldr: "sum xs = foldr (+) xs 0"
  apply (induct xs)
   apply auto
  done

lemma length_foldr: "length xs = foldr (\<lambda> x res. 1 + res) xs 0"
  apply (induct xs)
   apply auto
  done

lemma "sum (map (\<lambda> x. x + 3) xs) = foldr (\<lambda>x y. x + y + 3) xs 0"
  apply (induct xs)
   apply auto
  done

lemma "foldr g (map f xs) a = foldr (\<lambda>x y. (g (f x) y)) xs a"
  apply (induct xs)
   apply auto
  done

primrec rev_acc :: "['a list, 'a list] \<Rightarrow> 'a list" where
"rev_acc [] ys = ys"
| "rev_acc (x#xs) ys = (rev_acc xs (x#ys))"

lemma none: "rev_acc xs ys = (rev_acc xs []) @ ys"
proof (induct xs arbitrary: ys)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis append.left_neutral append_Cons append_assoc rev_acc.simps(2))
qed

lemma rev_acc_foldl: "rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
proof (induct xs arbitrary: a)
case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

lemma sum_append [simp]: "sum (xs @ ys) = sum xs + sum ys"
  apply (induct xs arbitrary: ys)
   apply auto
  done

(* The defnition part is from the solution as I cbb *)
definition
left_neutral :: "['a \<Rightarrow> 'b \<Rightarrow> 'b, 'a] \<Rightarrow> bool" where
"left_neutral f a == (\<forall> x. (f a x = x))"

definition
assoc :: "['a \<Rightarrow> 'a \<Rightarrow> 'a] \<Rightarrow> bool" where
"assoc f == (\<forall> x y z. f (f x y) z = f x (f y z))"

lemma foldr_append:
"\<lbrakk> left_neutral f a; assoc f \<rbrakk> \<Longrightarrow> foldr f (xs @ ys) a = f (foldr f xs a)(foldr f ys a)"
  apply (induct xs)
   apply (auto simp add: left_neutral_def assoc_def)
  done

fun prod :: "nat list \<Rightarrow> nat" where
 "(prod xs) = (foldr (*) xs 1)"

lemma "prod (xs @ ys) = prod xs * prod ys"
  apply (simp add: prod_def)
  apply (metis List.foldr_append One_nat_def 
        P19.foldr_append assoc_def left_neutral_def mult.commute 
        mult.left_commute nat_mult_1)
  done

end