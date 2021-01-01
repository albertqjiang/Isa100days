theory NFA imports AutoProj begin

(*  The non-deterministic finite automaton takes two types, 
    the first one the type of states (finite), 
    and the second one the type of symbols (alphabet).
*)

type_synonym ('q, 'a)nfa = "('q \<Rightarrow> 'a \<Rightarrow> 'q set) * 'q * ('q \<Rightarrow> bool)"

fun run :: "('q, 'a)nfa \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q set" where
"run A s Nil = {s}" |
"run A s (x # xs) = \<Union> {(run A s' xs) | s'. s'\<in> (tri_f A s x)}"

definition accept :: "('q, 'a)nfa \<Rightarrow> 'a list \<Rightarrow> bool" where
"accept A seq = (\<exists>sf. (tri_t A sf) \<and> sf \<in> (run A (tri_s A) seq))"

lemma empty_seq[simp]: "run A s Nil = {s}"
  apply auto
  done

lemma single_seq[simp]: "run A s [x] = (tri_f A s x)"
  apply auto
  done

lemma concat_seq[simp]: "run A s (xs @ ys) = \<Union> {run A s' ys | s'. s' \<in> (run A s xs)}"
proof (induct xs arbitrary: ys s)
case Nil
  then show ?case by auto
next
  case (Cons a xs)
  print_facts
  have "run A s ((a # xs) @ ys) = \<Union> {(run A s' (xs @ ys)) | s'. s' \<in> (run A s [a])}" by auto
  also have "\<dots> = \<Union> { (\<Union>{(run A s'' ys) | s''. s''\<in> (run A s' xs)}) | s'. s' \<in> (run A s [a])}" 
    using Cons.hyps by auto
  also have "\<dots> = \<Union> { (run A s'' ys) | s''. s''\<in> (run A s ([a] @ xs))}" using Cons.hyps by auto
  finally have "run A s ((a # xs) @ ys) = \<Union> {run A s' ys |s'. s' \<in> run A s (a # xs)}" by auto
  then show ?case by auto
qed

end