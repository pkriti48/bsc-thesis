import Game.Levels.AnBnNotRegular.L09_CountBInV

namespace Word

World "AnBnNotRegular"
Level 10
Title ""

Introduction ""

TheoremDoc Word.length_z_eq_2n as "length_z_eq_2n" in "Word"

Statement length_z_eq_2n (n : Nat) :
length (replicateChar Character.a n ++ replicateChar Character.b n) = 2 * n := by
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  rewrite [two_mul]
  rfl

Conclusion ""
