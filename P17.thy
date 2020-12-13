theory P17 imports Main begin

datatype paren = leftP | rightP

lemma [simp]: "(x \<noteq> leftP) = (x = rightP) \<and> (x \<noteq> rightP) = (x = leftP)"
  by (case_tac x, auto)

inductive_set S :: "paren list set" where
S1: "Nil : S" |
S2: "w : S \<Longrightarrow> leftP # w @ [rightP] : S" |
S3: "w0 : S \<Longrightarrow> w1 : S \<Longrightarrow> w0 @ w1 : S"

declare S1 [iff] S2[intro!,simp]

inductive_set T :: "paren list set" where
T1: "Nil : T" |
T2: "v0 : T \<Longrightarrow> v1 : T \<Longrightarrow> v0 @ (leftP # v1 @ [rightP]) : T"

declare T1 [iff]

lemma T2S : "w : T \<Longrightarrow> w : S"
  apply (erule T.induct)
   apply simp
  apply (simp add: S.S3)
  done

lemma TT[simp]: "\<forall>v1. v0 : T \<Longrightarrow> v1 : T \<Longrightarrow> v0 @ v1 : T"
  apply (erule T.induct)
  apply auto
  apply (metis T.simps append_assoc)
  done

lemma S2T : assumes w: "w : S" shows "w : T"
  using w
proof (induct)
  case S1
  then show ?case by simp
next
  case (S2 w)
  then show ?case using T.T2 by force
next
  case (S3 w0 w1)
  then show ?case by simp
qed

fun paren_counter :: "paren list \<Rightarrow> int" where
"paren_counter Nil = 0" |
"paren_counter (x # xs) = (if (x=leftP) then (paren_counter xs + 1) else (paren_counter xs - 1))"

fun valid_paren :: "paren list \<Rightarrow> bool" where
"valid_paren xs = (if (paren_counter xs = 0) then True else False)"

lemma [simp]: "paren_counter (xs @ ys) = (paren_counter xs + paren_counter ys)"
  apply (induct xs)
   apply auto
  done

lemma S_valid:
  assumes w: "w : S" shows "valid_paren w"
  using w
proof (induct)
case S1
  then show ?case by simp
next
  case (S2 w)
  then show ?case by simp
next
  case (S3 w0 w1)
  then show ?case
  proof -
    assume 1: "valid_paren w0" "valid_paren w1"
    have 2: "paren_counter w0 = 0"
      by (meson S3.hyps(2) valid_paren.simps)
    also have 3: "paren_counter w1 = 0"
      by (meson S3.hyps(4) valid_paren.simps)
    hence "paren_counter (w0 @ w1) = 0" using 1 2 by simp
    thus ?thesis by simp
  qed
qed

end