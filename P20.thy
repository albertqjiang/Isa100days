theory P20 imports Main begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

primrec preorder :: "'a tree \<Rightarrow> 'a list" where
"preorder Tip = Nil" |
"preorder (Node l x r) = x # (preorder l) @ (preorder r)"

primrec postorder :: "'a tree \<Rightarrow> 'a list" where
"postorder Tip = Nil" |
"postorder (Node l x r) = (postorder l) @ (postorder r) @ [x]"

primrec postorder_acc :: "'a tree \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"postorder_acc Tip xs = xs" |
"postorder_acc (Node l x r) xs = postorder_acc l (postorder_acc r (x # xs))"

lemma "postorder_acc t xs = (postorder t) @ xs"
  apply (induct t arbitrary: xs)
   apply auto
  done

primrec foldl_tree :: "('b => 'a => 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b" where
"foldl_tree f b Tip = b" |
"foldl_tree f b (Node l x r) = foldl_tree f (foldl_tree f (f b x) r) l"

lemma "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x. x # xs) a t"
  apply (induct t)
   apply auto
  done

primrec tree_sum :: "nat tree \<Rightarrow> nat" where
"tree_sum Tip = 0" |
"tree_sum (Node l x r) = x + (tree_sum l) + (tree_sum r)"

primrec list_sum :: "nat list \<Rightarrow> nat" where
"list_sum Nil = 0" |
"list_sum (x # xs) = x + list_sum xs"

lemma partition_sum: "list_sum (xs @ ys) = list_sum xs + list_sum ys"
  apply (induct xs)
   apply auto
  done

lemma "tree_sum t = list_sum (preorder t)"
  apply (induct t)
   apply (auto simp add: partition_sum)
  done

end