import Game.Levels.AnBnNotRegular.L11_LengthPumpedWord

namespace Word

World "AnBnNotRegular"
Level 12
Title ""

Introduction ""

TheoremDoc Word.w_eq_remaining_as_n_bs as "w_eq_remaining_as_n_bs" in "Word"

Statement w_eq_remaining_as_n_bs (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k) :
w = replicateChar Character.a (n - k) ++ replicateChar Character.b n := by
  have helper := congrArg (fun s => drop s k) z_eq
  simp at helper
  rewrite [h_z] at helper
  rewrite [drop_append_left] at helper
  rewrite [drop_replicateChar] at helper
  rewrite [helper]
  rewrite [drop_append_left]
  rewrite [drop_append_right]
  rewrite [h_k]
  rewrite [Nat.add_sub_cancel_left]
  rewrite [drop_all]
  rewrite [append]
  repeat rfl
  exact length_u_lt_k
  rewrite [h_k]
  rewrite [length_append]
  rfl
  exact k_leq_n
  rewrite [length_replicateChar]
  exact k_leq_n

Conclusion ""
