import Game.Levels.AnBnNotRegular.L11_LengthPumpedAn

namespace Word

World "AnBnNotRegular"
Level 12
Title "The Suffix w Contains All Remaining as And All bs"

Introduction "In this proof, you will show that decomposing a word $z = a^n b^n$ as  ```z =
(u ++ v) ++ w``` with ```k = length u + length v```, ```k ≤ n``` and ```length u < k```, the
suffix ```w```consists of exactly ```n - k``` replicas of ```a``` followed by ```n``` replicas
of ```b```."

/--
For a word $z = a^n b^n$, which is decomposed as ```z = (u ++ v) ++ w``` with
```k = length u + length v```, ```k ≤ n``` and ```length u < k```, the remaining
suffix ```w```consists of exactly ```n - k``` replicas of ```a``` followed by
```n``` replicas of ```b```.
-/
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

Conclusion "Using this theorem, will prove separately how many ```a```s and ```b```s occur in the
suffix ```w``` of ```z```."
