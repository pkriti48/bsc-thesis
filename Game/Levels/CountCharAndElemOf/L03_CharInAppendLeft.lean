import Game.Levels.CountCharAndElemOf.L02_CountCharInReplicateChar

namespace Word

World "CountCharAndElemOf"
Level 3
Title "Element of First Word is Element of Appended Word"

Introduction "The following proof states that character membership is preserved when a word is appended
to another. Precisely, if a character appears in the left word, then it also appears in the word formed
by appending any right word to it."

/--
Character membership is preserved under append on the left.

If a character ```char``` appears in the word ```left```, then it also appears
in the appended word ```left ++ right``` for any word ```right```.
-/
TheoremDoc Word.char_elemOf_append_left as "char_elem_of_append_left" in "Word"

Statement char_elemOf_append_left (left right : Word) (char : Character) :
elemOf char left -> elemOf char (left ++ right) := by
  induction left generalizing right with
  | nil =>
    Hint "You can split the implication in the current expression by executing ```intros h```. This
    would create an induction hypothesis using the term on the left hand side of the ```->``` sign
    and keep the term on the right hand side of the ```->``` sign as your current proof goal."
    intros h
    Branch
      exfalso
      apply h
    cases h
  | cons head tail ih =>
    intros h
    cases h with
    | inl head_eq_char =>
      Hint "Since the ```elemOf``` function returns a clause of the form ```A ∨ B```, you can split
      it into two parts by using the keyword ```left``` or ```right``` and observe them individually."
      left
      exact head_eq_char
    | inr char_in_tail =>
      right
      apply ih at char_in_tail
      exact char_in_tail

Conclusion "Very good! Next, you will show the ```∈w``` property for any second word or right word in
the append function."

NewTactic intros left right
NewDefinition Word.elemOf
