theory DFA imports AutoProj begin

(*  The deterministic finite automaton takes two types, 
    the first one the type of states (finite), 
    and the second one the type of symbols (alphabet).
*)

type_synonym ('q, 'a)dfa = "('q \<Rightarrow> 'a \<Rightarrow> 'q) * 'q * ('q \<Rightarrow> bool)"

definition run :: "('q, 'a)dfa \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q" where
"(run A s seq) = foldl (tri_f A) s seq"

definition accept :: "('q, 'a)dfa \<Rightarrow> 'a list \<Rightarrow> bool" where
"accept A seq = (tri_t A) (run A (tri_s A) seq)"

lemma empty_seq[simp]: "run A s Nil = s"
  apply (simp add: run_def)
  done

lemma append_seq[simp]: "run A s (x # xs) = run A (tri_f A s x) xs"
  apply (simp add: run_def)
  done

lemma concat_seq[simp]: "run A s (xs @ ys) = run A (run A s xs) ys"
  apply (induct xs)
   apply (auto simp add: run_def)
  done

end