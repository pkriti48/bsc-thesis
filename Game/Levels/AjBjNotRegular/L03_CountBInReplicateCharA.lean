import Game.Levels.AjBjNotRegular.L02_CountAInReplicateCharA

namespace Word

World "AjBjNotRegular"
Level 3
Title "In a Word Formed by Only a, Counting b Returns 0"

Introduction "In the level, you will prove that if ```a``` occurs at every position of a word, then
the number of ```b``` in the word is equal to 0."

/--
If every character occurring in a word is ```a```, then the number of ```b```s in the
word is equal to the length of the word.
-/
TheoremDoc Word.count_b_in_replicateChar_a as "count_b_in_replicateChar_a" in "AjBjNotRegular"

Statement count_b_in_replicateChar_a {char : Character} {word : Word}
{h : ∀ char : Character, elemOf char word -> char = Character.a} :
countCharInWord Character.b word = 0 := by
  Hint "This proof is analogue to the proof for the theorem ```count_a_in_replicateChar_a```. So, if
  at any point, you do not know how to proceed, you can have a look at that proof."
  induction word with
  | nil =>
    rewrite [countCharInWord]
    rfl
  | cons head tail ih =>
    simp [elemOf] at h
    simp [h]
    simp [countCharInWord]
    rewrite [ih]
    rfl
    intros ch h_ch
    apply h
    right
    exact h_ch

Conclusion "Well done! With the previous statement and the one in this level you proved that, if a
word consists of only ```a```s then the count ```a```s in that word is equal to the length of that
word, which also results in the count ```b``` being 0 in that word."

NewDefinition Character.b
