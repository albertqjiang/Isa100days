(*  Author:     Tobias Nipkow
    Copyright   1998 TUM

Is there an optimal order of arguments for `next'?
Currently we can have laws like `delta A (a#w) = delta A w o delta A a'
Otherwise we could have `acceps A == fin A o delta A (start A)'
and use foldl instead of foldl2.
*)


section "Projection functions for automata"

theory AutoProj
imports Main
begin

definition tri_f :: "'a * 'b * 'c \<Rightarrow> 'a" where "tri_f A = fst A"
definition tri_s :: "'a * 'b * 'c \<Rightarrow> 'b" where "tri_s A = fst(snd(A))"
definition tri_t :: "'a * 'b * 'c \<Rightarrow> 'c" where "tri_t A = snd(snd(A))"

lemma [simp]: "tri_f(q,d,f) = q"
by(simp add:tri_f_def)

lemma [simp]: "tri_s(q,d,f) = d"
by(simp add:tri_s_def)

lemma [simp]: "tri_t(q,d,f) = f"
by(simp add:tri_t_def)

end