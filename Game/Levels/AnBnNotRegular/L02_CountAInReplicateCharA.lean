import Game.Levels.AnBnNotRegular.L01_CountAEqCountBInLang

namespace Word

World "AnBnNotRegular"
Level 2
Title ""

Introduction ""

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

Conclusion ""
