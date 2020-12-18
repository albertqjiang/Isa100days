theory P22 imports Main begin

datatype bdd = Leaf bool | Branch bdd bdd

primrec eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool" where
"eval p i (Leaf b) = b" |
"eval p i (Branch b1 b2) = (if (p i) then (eval p (i+1) b2) else (eval p (i+1) b1))"

primrec bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd" where
"bdd_unop f (Leaf b) = (Leaf (f b))" |
"bdd_unop f (Branch b1 b2) = (Branch (bdd_unop f b1) (bdd_unop f b2))"

primrec bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd" where
"bdd_binop f (Leaf b) c = bdd_unop (f b) c" |
"bdd_binop f (Branch b1 b2) c = (case c of
  Leaf x \<Rightarrow> Branch (bdd_binop f b1 (Leaf x)) (bdd_binop f b2 (Leaf x)) |
  Branch x1 x2 \<Rightarrow> Branch (bdd_binop f b1 x1) (bdd_binop f b2 x2))"

theorem bdd_unop_correctness : "\<forall>i. eval g i (bdd_unop f b) = f (eval g i b)"
  apply (induct b)
  apply auto
  done

theorem bdd_binop_correctness : "\<forall>i. eval g i (bdd_binop f b1 b2) = f (eval g i b1) (eval g i b2)"
  apply (induct b1 arbitrary: b2)
   apply (auto simp add: bdd_unop_correctness)
     apply (case_tac b2)
      apply auto
     apply (case_tac b2)
      apply auto
     apply (case_tac b2)
  apply auto
     apply (case_tac b2)
      apply auto
  done

definition bdd_and:: "bdd \<Rightarrow> bdd \<Rightarrow> bdd" where
"bdd_and \<equiv> bdd_binop (\<and>)"

definition bdd_or:: "bdd \<Rightarrow> bdd \<Rightarrow> bdd" where
"bdd_or \<equiv> bdd_binop (\<or>)"

definition bdd_not:: "bdd \<Rightarrow> bdd" where
"bdd_not \<equiv> bdd_unop (Not)"

definition bdd_xor:: "bdd \<Rightarrow> bdd \<Rightarrow> bdd" where
"bdd_xor \<equiv> bdd_binop (\<lambda>x y. (x \<and> (\<not> y)) \<or> (\<not>x \<and> y))"

lemma bdd_and_correctness: "eval p i (bdd_and b1 b2) = (eval p i b1 \<and> eval p i b2)"
  apply (auto simp add: bdd_and_def bdd_binop_correctness)
  done

lemma bdd_or_correctness: "eval p i (bdd_or b1 b2) = (eval p i b1 \<or> eval p i b2)"
  apply (auto simp add: bdd_or_def bdd_binop_correctness)
  done

lemma bdd_not_correctness: "eval p i (bdd_not b) = (\<not> (eval p i b))"
  apply (auto simp add: bdd_not_def bdd_unop_correctness)
  done

lemma bdd_xor_correctness: 
"eval p i (bdd_xor b1 b2) = (eval p i b1 \<and> (\<not> eval p i b2)) \<or> (\<not> eval p i b1 \<and> eval p i b2)"
  apply (auto simp add: bdd_xor_def bdd_binop_correctness)
  done

fun bdd_var :: "nat \<Rightarrow> bdd" where
  "bdd_var 0 = (Branch (Leaf False) (Leaf True))" |
  "bdd_var (Suc n) = (Branch (bdd_var n) (bdd_var n))"

theorem bdd_var_correctness:"\<forall>n. eval p n (bdd_var m) = p (m+n)"
  apply (induct m)
  apply auto
  done

datatype form = T | Var nat | And form form | Xor form form

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<equiv> (x \<and> \<not> y) \<or> (\<not> x \<and> y)"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where
  "evalf e T = True"
  | "evalf e (Var i) = e i"
  | "evalf e (And f1 f2) = (evalf e f1 \<and> evalf e f2)"
  | "evalf e (Xor f1 f2) = xor (evalf e f1) (evalf e f2)"

fun mk_bdd :: "form \<Rightarrow> bdd" where
"mk_bdd T = Leaf True" |
"mk_bdd (Var i) = bdd_var i" |
"mk_bdd (And f1 f2) = bdd_and (mk_bdd f1) (mk_bdd f2)" |
"mk_bdd (Xor f1 f2) = bdd_xor (mk_bdd f1) (mk_bdd f2)"

theorem mk_bdd_correct: "eval e 0 (mk_bdd f) = evalf e f"
  apply (induct f)
  using bdd_xor_correctness bdd_xor_def apply auto[1]
  apply (simp add: bdd_var_correctness)
  apply (simp add: bdd_and_correctness)
  apply (simp add: bdd_binop_correctness bdd_xor_def xor_def)
  done

end