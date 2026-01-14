import Game.Levels.AnBnNotRegular.L08_CountAInV

namespace Word


World "AnBnNotRegular"
Level 9
Title ""

Introduction ""

TheoremDoc Word.count_b_in_v as "count_b_in_v" in "Word"

Statement count_b_in_v (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.b v = 0 := by
  rewrite [count_b_in_replicateChar_a]
  rfl
  exact Character.b
  intros char h
  apply char_elemOf_append_right (left := u) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply char_elemOf_replicateChar at h
  exact h

Conclusion ""
