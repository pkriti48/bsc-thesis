import Game.Levels.AjBjNotRegular.L01_CountAEqCountBInLang

namespace Word

World "AjBjNotRegular"
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
    Hint (hidden := true) "If you do not know how to proceed from here, try using the ```simp```
    tactic. It will simplify your expression using all theorems that are available and applicable to
    your current proof goal along with the hypothesis ```h```."
    simp [h]
    simp [countCharInWord]
    rewrite [length]
    rewrite [ih]
    rfl
    Hint "If you carefully look at your current proof goal, it looks a lot like the hypothesis
    ```h```. In order to prove its correctness, simplify your current proof goal using ```intros```
    tactic."
    intros ch h_ch
    apply h
    right
    exact h_ch

Conclusion "Well done! Let's move forward to the next proof!"

NewDefinition Character.a
