theory P1
imports Nat
begin
datatype nat = 0 | Suc nat
fun add :: "nat ) nat ) nat" where
"add 0 n = n" j
"add (Suc m) n = Suc(add m n)"
end