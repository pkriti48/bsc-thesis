import Game.Levels.AnBnNotRegular.L10_LengthZEq2n

namespace Word

World "AnBnNotRegular"
Level 11
Title ""

Introduction ""

TheoremDoc Word.length_pumped_word as "length_pumped_word" in "Word"

Statement length_pumped_word (u v w z : Word) (n k : Nat)
(z_eq : z = (u ++ v) ++ w)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(k_leq_n : k ≤ n) (h_k : k = length u + length v) :
u.length + (v.length + v.length) + (w.length - n) = n + length v := by
  rewrite [<- Nat.add_sub_assoc]
  rewrite [<- Nat.add_left_comm]
  rewrite [Nat.add_assoc]
  rewrite [Nat.add_comm n]
  rewrite [<- length_append]
  rewrite [<- length_append]
  rewrite [<- z_eq]
  rewrite [Nat.add_sub_assoc]
  rewrite [Nat.add_left_cancel_iff]
  rewrite [h_z]
  rewrite [length_z_eq_2n]
  rewrite [two_mul]
  rewrite [Nat.add_sub_cancel]
  rfl
  rewrite [h_z]
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  apply Nat.le_add_right n n
  have length_w : length w = length z - k := by
    rewrite [z_eq]
    rewrite [h_k]
    repeat rewrite [length_append]
    rewrite [Nat.add_sub_cancel_left]
    rfl
  rewrite [length_w]
  rewrite [h_z]
  simp [length_z_eq_2n]
  rewrite [two_mul]
  rewrite [Nat.add_sub_assoc]
  apply Nat.le_add_right
  exact k_leq_n

Conclusion ""
