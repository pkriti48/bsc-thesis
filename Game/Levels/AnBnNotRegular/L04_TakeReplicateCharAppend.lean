import Game.Levels.AnBnNotRegular.L03_CountBInReplicateCharA

namespace Word

World "AnBnNotRegular"
Level 4
Title ""

Introduction ""

TheoremDoc Word.take_replicateChar_append as "take_replicateChar_append" in "AnBnNotRegular"

Statement take_replicateChar_append (n k : Nat) (k_leq_n : k ≤ n) :
take (replicateChar Character.a n ++ replicateChar Character.b n) k = replicateChar Character.a k := by
  rewrite [take_append_left]
  rewrite [take_replicateChar (h := k_leq_n)]
  rfl
  rewrite [length_replicateChar]
  exact k_leq_n

Conclusion ""

