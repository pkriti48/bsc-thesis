import Game.Levels.AppendAndConcat.L03_LengthAppend

namespace Word

World "AppendAndConcat"
Level 4
Title "Length of Character Replicas"

Introduction "The theorem ```length_replicateChar``` describes the length of a word created by
repeating a single character multiple times. It states that if a character ```char``` is
repeated ```n``` times using ```replicateChar```, the resulting word has length exactly ```n```."

/--
The length of a word formed by repeating a character.

For any character ```char``` and natural number ```n```, ```replicateChar char n```
produces a word consisting of ```n``` copies of ```char```. The length of this
word is exactly ```n```.
-/
TheoremDoc Word.length_replicateChar as "length_replicateChar" in "Word"

Statement length_replicateChar (char : Character) (n : Nat): length (replicateChar char n) = n := by
  Hint "Since you have to prove the statement for all possible lengths, you should start by induction
  on ```n```."
  induction n with
  | zero =>
    Hint "As you did in every proof so far, you should start by rewriting the function being used on
    the lowest layer of the term."
    rewrite [replicateChar]
    rewrite [length]
    rfl
  | succ k ih =>
    rewrite [replicateChar]
    rewrite [length]
    rewrite [ih]
    rewrite [add_comm]
    rfl

Conclusion "Very good! Let's move forward to the next level where you will show how how the length
of a word changes when it is repeated multiple times."

NewDefinition Word.replicateChar
