theory P21 imports Main begin

datatype tree = Tp | Nd tree tree

fun tips :: "tree \<Rightarrow> nat" where 
"tips Tp = 1" |
"tips (Nd l r) = tips l + tips r"

fun height :: "tree \<Rightarrow> nat" where
"height Tp = 0" |
"height (Nd l r) = 1 + max (height l) (height r)"

primrec cbt :: "nat \<Rightarrow> tree" where
"cbt 0 = Tp" |
"cbt (Suc n) = Nd (cbt n) (cbt n)"

fun iscbt :: "(tree \<Rightarrow> 'a) \<Rightarrow> tree \<Rightarrow> bool" where
"iscbt f Tp = True" |
"iscbt f (Nd l r) = (f l = f r \<and> iscbt f l \<and> iscbt f r)"

lemma [simp]: "iscbt height t \<Longrightarrow> tips t = 2 ^ (height t)"
  apply (induct t)
   apply auto
  done

theorem "iscbt height t = iscbt tips t"
  apply (induct t)
   apply auto
  done

lemma [simp]: "tips t = size t + 1"
  apply (induct t)
  apply auto
  done

theorem "(iscbt tips t = iscbt size t)"
  apply (induct t)
   apply auto
  done

theorem "iscbt height (cbt n)"
  apply (induct n)
   apply auto
  done

theorem "iscbt height t \<Longrightarrow> t = cbt (height t)"
  apply (induct t)
   apply auto
  done

theorem "iscbt (\<lambda>t. False) \<noteq> (iscbt size)"
  apply (rule notI)
  apply (metis add_cancel_right_left iscbt.simps(1) iscbt.simps(2) nat.distinct(1) 
        tree.size(3) tree.size(4))
  done


end