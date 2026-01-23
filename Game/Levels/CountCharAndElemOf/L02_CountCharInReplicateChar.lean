import Game.Levels.CountCharAndElemOf.L01_CountCharInAppend

namespace Word

World "CountCharAndElemOf"
Level 2
Title "Count Occurrences of a Character in Word Formed by a Character's Replicas"

Introduction "In the following, you will prove that the number of occurrences of a character
in a word formed by a character's replicas only depends on whether the character being counted
matches the replicated one. If the characters match, the count equals the number of repetitions;
otherwise, it is zero."


/--
For characters ```char``` and ```char_count``` and a natural number ```n```,
counting occurrences of ```char_count``` in ```replicateChar char n```
returns ```n``` if the two characters are equal, and ```0``` otherwise.
-/
TheoremDoc Word.count_char_in_replicateChar as "count_char_in_replicateChar" in "Word"

Statement count_char_in_replicateChar (char_count char : Character) (n : Nat) :
countCharInWord char_count (replicateChar char n) = (if char = char_count then n else 0) := by
  induction n with
  | zero =>
    rewrite [replicateChar]
    rewrite [countCharInWord]
    simp
  | succ k ih =>
    rewrite [replicateChar]
    rewrite [countCharInWord]
    rewrite [ih]
    Hint "You can ```split``` your current proof goal at this point. Then, you will prove the outcome
    for the two cases ```char = char_count``` and ```char ≠ char_count```."
    split
    rewrite [Nat.add_comm]
    rfl
    rewrite [Nat.add_zero]
    rfl

Conclusion "Well done! You just proved that a word formed by replicating a specific character
contains exactly as many occurrences of that character as its repetition count, and none of any
other character."

NewTactic split
