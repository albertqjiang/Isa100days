theory P23 imports Main begin

datatype form = T | Var nat | And form form | Xor form form

definition
xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"xor x y \<equiv> (\<not> (x=y))"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where
"evalf p T = True" |
"evalf p (Var n) = p n" |
"evalf p (And f1 f2) = ((evalf p f1) \<and> (evalf p f2))" |
"evalf p (Xor f1 f2) = (xor (evalf p f1) (evalf p f2))"

primrec evalm :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool" where
"evalm p Nil = True" |
"evalm p (x # xs) = ((p x) \<and> (evalm p xs))"

primrec evalp :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool" where
"evalp p Nil = False" |
"evalp p (xs # xss) = (\<not>((evalm p xs) = (evalp p xss)))"

lemma "evalm (\<lambda>x. False) Nil = True"
  apply simp
  done

lemma "evalm (\<lambda>x. False) [1] = False"
  apply simp
  done

lemma "evalp (\<lambda>x. False) [] = False"
  apply simp
  done

lemma "evalp (\<lambda>x. False) [[1], [2]] = False"
  apply simp
  done

lemma "evalp (\<lambda>x. True) [[1], [2], [3]] = True"
  apply simp
  done

primrec mulpp :: "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list" where
"mulpp Nil qs = Nil" | 
"mulpp (p # ps) qs = (map (\<lambda>x. x @ p) qs @ (mulpp ps qs))"

primrec poly :: "form \<Rightarrow> nat list list" where
"poly T = [[]]" |
"poly (Var n) = [[n]]" |
"poly (And f1 f2) = mulpp (poly f1) (poly f2)" |
"poly (Xor f1 f2) = (poly f1 @ poly f2)"

lemma evalm_app: "evalm e (xs @ ys) = (evalm e xs \<and> evalm e ys)"
  apply (induct xs)
   apply auto
  done

lemma evalp_app: "evalp e (xs @ ys) = (xor (evalp e xs) (evalp e ys))"
  apply (induct xs)
   apply (auto simp add: xor_def)
done

theorem mulmp_correct: "evalp e (map (\<lambda>x. x @ m) p) = (evalm e m \<and> evalp e p)"
  apply (induct p)
  apply (auto simp add: xor_def evalm_app)
  done

theorem mulpp_correct: "evalp e (mulpp p q) = (evalp e p \<and> evalp e q)"
  apply (induct p)
   apply (auto simp add: xor_def mulmp_correct evalp_app)
done

theorem poly_correct: "evalf e f = evalp e (poly f)"
  apply (induct f)
  apply simp
  apply simp
  apply (simp add: mulpp_correct)
  apply (simp add: evalp_app)
  done

end