import Game.Levels.AnBnNotRegular.L07_CountBInU

namespace Word

World "AnBnNotRegular"
Level 8
Title ""

Introduction ""

TheoremDoc Word.count_a_in_v as "count_a_in_v" in "Word"

Statement count_a_in_v (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.a v = length v := by
  rewrite [count_a_in_replicateChar_a]
  rfl
  exact Character.a
  intros char h
  apply char_elemOf_append_right (left := u) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply char_elemOf_replicateChar at h
  exact h

Conclusion ""
