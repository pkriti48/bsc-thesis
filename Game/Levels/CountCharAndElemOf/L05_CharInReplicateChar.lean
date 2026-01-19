import Game.Levels.CountCharAndElemOf.L04_CharInAppendRight

namespace Word

World "CountCharAndElemOf"
Level 5
Title "All Characters in a Word Formed By Replicating a Characters are Same"

Introduction "In this level, you will show that if any character appears in a word formed by
```replicateChar input_char n```, then that character and ```input_char``` must be equal.

In other words, you will prove that a word made of repeating a specifif character cannot
contain any other character."

/--
For any character ```char```, if ```char``` appears in a word formed by repeating
```input_char``` exactly ```n``` times, then ```char``` must be equal to ```input_char```.
-/
TheoremDoc Word.char_elemOf_replicateChar as "char_elemOf_replicateChar" in "Word"

Statement char_elemOf_replicateChar {input_char : Character} {n : Nat} :
∀ char : Character, elemOf char (replicateChar input_char n) -> char = input_char := by
  intros char h
  induction n with
  | zero =>
    rewrite [replicateChar] at h
    exfalso
    apply h
  | succ =>
    rewrite [replicateChar] at h
    rewrite [elemOf] at h
    cases h with
    | inl input_char_eq_char =>
      rewrite [input_char_eq_char]
      rfl
    | inr char_in_tail =>
      rewrite [a]
      rfl
      exact char_in_tail

Conclusion "Well done! One more step closer to executing the pumping lemma on concrete languages.
Let's move on to the next and final world!"

NewTactic symm
