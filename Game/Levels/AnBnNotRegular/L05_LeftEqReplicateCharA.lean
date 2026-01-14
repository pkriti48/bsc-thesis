import Game.Levels.AnBnNotRegular.L04_TakeReplicateCharAppend

namespace Word

World "AnBnNotRegular"
Level 5
Title ""

Introduction ""

TheoremDoc Word.left_eq_replicateChar_a as "left_eq_replicateChar_a" in "AnBnNotRegular"

Statement left_eq_replicateChar_a (left right word : Word) (n : Nat)
(h_z : word = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : word = left ++ right)
(length_u_v_leq_n : length left ≤ n) :
left = replicateChar Character.a (length left) := by
  have helper := congrArg (fun f => take f (length left)) z_eq
  simp at helper
  simp [h_z] at helper
  rewrite [take_replicateChar_append (k_leq_n := length_u_v_leq_n)] at helper
  rewrite [helper]
  rewrite [take_append_left]
  rewrite [take_all]
  rfl
  rfl

Conclusion ""
