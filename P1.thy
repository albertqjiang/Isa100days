theory P1
imports Main
begin
datatype nat = Zero | Suc nat
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add Zero n = n" |
  "add (Suc m) n = Suc(add m n)"

lemma add_02: "add m Zero = m"
  apply (induction m)
  apply (auto)
  done

lemma add_02_no_auto: "add m Zero = m"
  apply (induction m)
   apply simp
   apply simp
  done

end