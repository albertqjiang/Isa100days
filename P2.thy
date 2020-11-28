theory P2
imports Main
begin

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list => 'a list => 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list => 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil x = Cons x Nil" |
"snoc (Cons y xs) x = (Cons y (snoc xs x))"

lemma [simp]: "app xs Nil = xs"
  apply (induct xs)
  apply (auto)
  done

lemma [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induct xs)
   apply auto
  done

lemma [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induct xs)
   apply (auto)
  done

lemma rev_rev: "rev (rev xs) = xs"
  apply (induct xs)
   apply (auto)
  done

lemma [simp]: "snoc xs x1 = app xs (Cons x1 Nil)"
  apply (induct xs)
   apply auto
  done

theorem rev_cons: "rev (Cons x xs) = snoc (rev xs) x"
  apply (induct xs)
   apply auto
  done
end
