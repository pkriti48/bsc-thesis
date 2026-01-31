import Game.Levels.AjBjNotRegular.L09_CountBInV

namespace Word

World "AjBjNotRegular"
Level 10
Title "Length of z Is 2 * n"

Introduction "In this proof, you will show that appending ```n``` replicas of ```b``` to ```n```
replicas of ```a``` means that the word has a length equal to ```2 * n``` since each individual word
has the length ```n```."

/--
Th word produced by appending ```n``` replicas of ```b``` to ```n```
replicas of ```a``` has the length ```2 * n```.
-/
TheoremDoc Word.length_z_eq_2n as "length_z_eq_2n" in "AjBjNotRegular"

/--
Multiplication by two is addition with itself.

For any natural number ```n```, multiplying ```n``` by ```2``` is
equal to adding ```n``` to itself, i.e. `2 * n = n + n`.
-/
TheoremDoc Nat.two_mul as "Nat.two_mul" in "Nat"

Statement length_z_eq_2n (n : Nat) :
length (replicateChar Character.a n ++ replicateChar Character.b n) = 2 * n := by
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  Hint (hidden := true) "To proceed from here, you are given a theorem stating that adding a number
  to itself is equal to multiplying the same number by 2. Use that!"
  rewrite [Nat.two_mul]
  rfl

Conclusion "Well done! Next, you'll show how the length of the pumped word is calculated."

NewTheorem Nat.two_mul
