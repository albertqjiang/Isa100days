theory DFA imports AutoProj begin

(*  The deterministic finite automaton takes two types, 
    the first one the type of states (finite), 
    and the second one the type of symbols (alphabet).
*)

type_synonym ('q, 'a)dfa = "('q \<Rightarrow> 'a \<Rightarrow> 'q) * 'q * ('q \<Rightarrow> bool)"

fun run :: "('q, 'a)dfa \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q" where
"run A s Nil = s" |
"run A s (x # xs) = run A (tri_f A s x) xs"

definition accept :: "('q, 'a)dfa \<Rightarrow> 'a list \<Rightarrow> bool" where
"accept A seq = (tri_t A) (run A (tri_s A) seq)"

lemma append_seq[simp]: "run A s (xs @ [x]) = tri_f A (run A s xs) x"
  apply (induct xs arbitrary: x s)
   apply auto
  done

lemma concat_seq[simp]: "run A s (xs @ ys) = run A (run A s xs) ys"
proof (induct ys arbitrary: xs s)
case Nil
  then show ?case by simp
next
  case (Cons a ys)
  have "run A s (xs @ a # ys) = run A s ((xs @ [a]) @ ys)" by auto
  also have "\<dots> = run A (run A s (xs @ [a])) ys" using Cons.hyps by blast
  finally have 1: "run A s (xs @ a # ys) = run A (run A s (xs @ [a])) ys" by blast
  have "run A (run A s xs) (a # ys) = run A (tri_f A (run A s xs) a) ys" by auto
  also have "\<dots> = run A (run A s (xs @ [a])) ys" by auto
  finally have "run A (run A s xs) (a # ys) = run A s (xs @ a # ys)" using 1 by auto
  then show ?case by auto
qed

end