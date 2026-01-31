import Game.Levels.AjBjNotRegular.L04_TakeKAsFromZ

namespace Word

World "AjBjNotRegular"
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
TheoremDoc Word.left_eq_replicateChar_a as "left_eq_replicateChar_a" in "AjBjNotRegular"

Statement left_eq_replicateChar_a (left right word : Word) (n : Nat)
(h_z : word = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : word = left ++ right)
(length_left_leq_n : length left ≤ n) :
left = replicateChar Character.a (length left) := by
  Hint "To prove this statement, start by deriving the fact that left can be retrieved from ```word
  = left ++ right``` by applying the ```take``` function to ```word```."
  Hint (hidden := true) "To derive this fact, you can write a helper theorem using the ```have``` tactic."
  have take_left : left = take word (length left) := by
    rewrite [z_eq]
    rewrite [take_append_left]
    rewrite [take_all]
    rfl
    rfl
  Hint "From here, the proof should be easy to solve using the theorems you have proven so far."
  rewrite [h_z] at take_left
  rewrite [take_k_as_from_z] at take_left
  exact take_left
  exact length_left_leq_n

Conclusion "Well done! You are getting closer to the final proof! Let's move on to the next
proof!"

NewTactic «have»
