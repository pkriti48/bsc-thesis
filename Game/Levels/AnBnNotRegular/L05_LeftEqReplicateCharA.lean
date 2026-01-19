import Game.Levels.AnBnNotRegular.L04_TakeReplicateCharAppend

namespace Word

World "AnBnNotRegular"
Level 5
Title "Any Prefix of Length at Most n in a Word z Is All a"

Introduction "In this level, you will prove that if a word consists of ```n``` replicas of
```a``` followed by ```n``` replicas of ```b```, and that word is written as ```left ++
right``` where the length of ```left``` is at most ```n```, then ```left``` must consist
only of ```a```s.
"

/--
This lemma states that if a word consists of ```n``` replicas of ```a``` followed
by ```n``` replicas of ```b```, and that word is written as `left ++ right` where
the length of ```left``` is at most ```n```, then ```left``` must consist only of
```a```s.
-/
TheoremDoc Word.left_eq_replicateChar_a as "left_eq_replicateChar_a" in "AnBnNotRegular"

/--
```congrArg``` carries equality through a function.

If two terms ```x``` and ```y``` are equal, then applying the same function ```f```
to both returns equal results. In other words, from ```x = y``` ```f x = f y``` is
derived.
-/
TacticDoc congrArg

Statement left_eq_replicateChar_a (left right word : Word) (n : Nat)
(h_z : word = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : word = left ++ right)
(length_left_leq_n : length left ≤ n) :
left = replicateChar Character.a (length left) := by
  have helper := congrArg (fun f => take f (length left)) z_eq
  simp at helper
  simp [h_z] at helper
  rewrite [take_replicateChar_append (k_leq_n := length_left_leq_n)] at helper
  rewrite [helper]
  rewrite [take_append_left]
  rewrite [take_all]
  rfl
  rfl

Conclusion "Well done! You are getting closer to the final proof! Let's move on to the next
proof!"

NewTactic congrArg
