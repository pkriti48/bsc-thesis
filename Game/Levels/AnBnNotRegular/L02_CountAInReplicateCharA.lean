import Game.Levels.AnBnNotRegular.L01_CountAEqCountBInLang

namespace Word

World "AnBnNotRegular"
Level 2
Title "In a Word Formed by Only a, Counting a Returns the Word’s Length"

Introduction "In this level, you will prove that if ```a``` occurs at every position of a word, then
the number of ```a``` in the word is equal to the length of the word."


/--
If every character occurring in a word is ```a```, then the number of ```a```s in the
word is equal to the length of the word.
-/
TheoremDoc Word.count_a_in_replicateChar_a as "count_a_in_replicateChar_a" in "AnBnNotRegular"

Statement count_a_in_replicateChar_a (char : Character) (word : Word)
(h : ∀ char : Character, elemOf char word -> char = Character.a) :
countCharInWord Character.a word = length word := by
  induction word with
  | nil =>
    rewrite [countCharInWord]
    rewrite [length]
    rfl
  | cons head tail ih =>
    simp [elemOf] at h
    have h_head : head = Character.a := by
      apply h
      simp
    simp [h_head]
    simp [countCharInWord]
    rewrite [ih]
    rewrite [length]
    rfl
    have h_tail : ∀ char, elemOf char tail → char = Character.a := by
      intros ch h_ch
      apply h
      right
      exact h_ch
    exact h_tail

Conclusion "Well done! Let's move forward to the next proof!"

NewTactic «have»
NewDefinition Character.a
