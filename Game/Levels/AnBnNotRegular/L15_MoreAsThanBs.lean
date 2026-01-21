import Game.Levels.AnBnNotRegular.L14_CountBInW

namespace Word

World "AnBnNotRegular"
Level 15
Title "More as than bs"

Introduction "In this level, you will prove that the pumped word contains more ```a```s than it
contains ```b```s."

/--
Given a word $z = a^n b^n$ and a decomposition ```z = (u ++ v) ++ w``` with
```k = length u + length v```, ```k ≤ n```, ```length (u ++ v) ≤ n```,
```length v ≥ 1```, and a pumped word ```z_pumped = (u ++ (replicateWord v 2)) ++ w```,
```more_as_than_bs``` shows that the pumped word contains more ```a```s than ```b```s.
-/
TheoremDoc Word.more_as_than_bs as "more_as_than_bs" in "Word"

/--
Adding a positive natural number to another natural number strictly increases it.

For natural numbers ```m``` and ```n``` with ```b > 0```, it asserts: ```m + n > n```
-/
TheoremDoc Nat.lt_add_of_pos_right as "Nat.lt_add_of_pos_right" in "Nat"

/--
Deduce a strict inequality from a successor-based inequality.

For natural numbers ```m``` and ```n```, it states that if the successor of
```m``` is less than or equal to ```n```: ```m + 1 ≤ n```.
-/
TheoremDoc Nat.lt_of_succ_le as "Nat.lt_of_succ_le" in "Nat"

Statement more_as_than_bs (u v w z z_pumped : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length (u ++ v))
(length_u_v_leq_n : length (u ++ v) ≤ n) (length_v_geq_1 : length v ≥ 1)
(h_z_pumped : z_pumped = (u ++ (replicateWord v 2)) ++ w) :
(countCharInWord Character.b z_pumped) < countCharInWord Character.a z_pumped := by
  rewrite [h_z_pumped]
  repeat rewrite [replicateWord]
  repeat rewrite [append_nil]
  repeat rewrite [count_char_in_append]
  Hint "As suggested in the previous level, you can pass all words, natural numbers and the
  hypotheses to the theorem as parameters to avoid repetitive proofs on correctness of all of them.
  This shortens your proof a lot."
  rewrite [count_a_in_u u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_b_in_u u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_a_in_v u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_b_in_v u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_a_in_w u v w z n k (z_eq := z_eq) (h_k := h_k) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_b_in_w u v w z n k (z_eq := z_eq) (h_k := h_k) (length_u_v_leq_n := length_u_v_leq_n)]
  repeat rewrite [Nat.zero_add]
  rewrite [number_of_as_in_pumped_word u v w z n (length_u_v_leq_n := length_u_v_leq_n)]
  apply Nat.lt_add_of_pos_right
  apply Nat.lt_of_succ_le
  rewrite [Nat.succ_eq_add_one]
  rewrite [Nat.zero_add]
  exact length_v_geq_1
  exact z_eq
  repeat simp [h_z]

Conclusion "Very good! Now, you will use this theorem in the final proof and show that $L = {a^n b^n
| n ≥ 0}$ is not regular."

NewTheorem Nat.lt_add_of_pos_right Nat.lt_of_succ_le
