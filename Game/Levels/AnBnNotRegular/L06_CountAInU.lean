import Game.Levels.AnBnNotRegular.L05_LeftEqReplicateCharA

namespace Word

World "AnBnNotRegular"
Level 6
Title ""

Introduction ""

TheoremDoc Word.count_a_in_u as "count_a_in_u" in "Word"

Statement count_a_in_u (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.a u = length u := by
  apply count_a_in_replicateChar_a
  exact Character.a
  intros char h
  apply char_elemOf_append_left (right := v ) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply char_elemOf_replicateChar at h
  exact h

Conclusion ""

