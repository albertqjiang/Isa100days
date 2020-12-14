theory P18 imports Main begin

datatype 'a tree =
  Leaf ("\<langle>\<rangle>") |
  Node "'a tree" ("value": 'a) "'a tree" ("(1\<langle>_,/ _,/ _\<rangle>)")
datatype_compat tree

fun preOrder :: "'a tree \<Rightarrow> 'a list" where
"preOrder \<langle>\<rangle> = []" |
"preOrder \<langle>l, x, r\<rangle> = x # preOrder l @ preOrder r"

fun postOrder :: "'a tree \<Rightarrow> 'a list" where
"postOrder \<langle>\<rangle> = []" |
"postOrder \<langle>l, x, r\<rangle> = postOrder l @ postOrder r @ [x]"

fun inOrder :: "'a tree \<Rightarrow> 'a list" where
"inOrder \<langle>\<rangle> = []" |
"inOrder \<langle>l, x, r\<rangle> = inOrder l @ [x] @ inOrder r"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror \<langle>\<rangle> = \<langle>\<rangle>" |
"mirror \<langle>l, x, r\<rangle> = \<langle>mirror r, x, mirror l\<rangle>"

lemma "preOrder (mirror xt) = rev (preOrder xt)"
  nitpick
  oops

lemma "preOrder (mirror xt) = rev (postOrder xt)"
  apply (induct xt)
   apply auto
  done

lemma "preOrder (mirror xt) = rev (inOrder xt)"
  nitpick
  oops

lemma "postOrder (mirror xt) = rev (preOrder xt)"
  apply (induct xt)
   apply auto
  done

lemma "postOrder (mirror xt) = rev (postOrder xt)"
  nitpick
  oops

lemma "postOrder (mirror xt) = rev (inOrder xt)"
  nitpick
  oops

lemma "inOrder (mirror xt) = rev (preOrder xt)"
  nitpick
  oops

lemma "inOrder (mirror xt) = rev (postOrder xt)"
  nitpick
  oops

lemma "inOrder (mirror xt) = rev (inOrder xt)"
  apply (induct xt)
   apply auto
  done

fun root :: "'a tree \<Rightarrow> 'a" where
"root xt = (hd (preOrder xt))"

fun leftmost :: "'a tree \<Rightarrow> 'a" where
"leftmost xt = (hd (inOrder xt))"

fun rightmost :: "'a tree \<Rightarrow> 'a" where
"rightmost xt = (last (inOrder xt))"

theorem "last (inOrder xt) = rightmost xt"
  apply (induct xt)
   apply auto
  done

theorem "hd (inOrder xt) = leftmost xt"
  apply (induct xt)
   apply auto
  done

theorem "hd (preOrder xt) = last (postOrder xt)"
  nitpick
  oops

theorem "hd (preOrder xt) = root xt"
  apply (induct xt)
   apply auto
  done

theorem "hd (inOrder xt) = root xt"
  nitpick
  oops

theorem "last (postOrder xt) = root xt"
  nitpick
  oops

end