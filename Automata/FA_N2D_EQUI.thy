theory FA_N2D_EQUI 
  imports DFA NFA

begin

definition 
nfa2dfa :: "('q, 'a)nfa \<Rightarrow> ('q set, 'a)dfa" where
"nfa2dfa A = (
  \<lambda>S. \<lambda>a. \<Union>{tri_f A s a | s. s\<in>S},
  {tri_s A},
  \<lambda>S. (\<exists>s. s\<in>S \<and> tri_t A s)
)"

lemma run_inclusion[simp]:
"\<forall>s. NFA.run A s w = (DFA.run (nfa2dfa A) {s} w)"
  apply (induct w)
   apply (auto simp add: nfa2dfa_def)
  sorry

lemma equi:
"NFA.accept A w = DFA.accept (nfa2dfa A) w"
  apply (simp add: DFA.accept_def NFA.accept_def run_inclusion)
  apply (simp add: nfa2dfa_def)
  apply blast
  done

end