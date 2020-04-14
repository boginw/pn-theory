theory pn
  imports Main
begin
  (* This is a comment *)

fun gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"gcd m n = (if n=0 then m else gcd n (m mod n))"

fun gcd1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"gcd1 m 0 = m" |
"gcd1 m n = gcd1 n (m mod n)"

fun gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"gcd2 m n = (case n=0 of True \<Rightarrow> m | False \<Rightarrow> gcd2 n (m mod n))"

lemma [simp]: "gcd m 0 = m"
apply(simp)
done

lemma [simp]: "n \<noteq> 0 \<Longrightarrow> gcd m n = gcd n (m mod n)"
apply(simp)
done
declare gcd.simps [simp del]

end