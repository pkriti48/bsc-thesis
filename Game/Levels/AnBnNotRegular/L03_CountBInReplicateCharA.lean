import Game.Levels.AnBnNotRegular.L02_CountAInReplicateCharA

namespace Word

World "AnBnNotRegular"
Level 3
Title ""

Introduction ""

Statement count_b_in_replicateChar_a {char : Character} {word : Word}
{h : ∀ char : Character, elemOf char word -> char = Character.a} :
countCharInWord Character.b word = 0 := by
  induction word with
  | nil =>
    rewrite [countCharInWord]
    rfl
  | cons head tail ih =>
    simp [elemOf] at h
    have h_head : head = Character.a := by
      apply h
      simp
    simp [h_head]
    simp [countCharInWord]
    rewrite [ih]
    rfl
    have h_tail : ∀ char, elemOf char tail → char = Character.a := by
      intros ch h_ch
      apply h
      right
      exact h_ch
    exact h_tail

Conclusion ""
