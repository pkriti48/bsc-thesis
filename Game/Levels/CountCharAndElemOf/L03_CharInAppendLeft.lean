import Game.Levels.CountCharAndElemOf.L02_CountCharInReplicateChar

namespace Word

World "CountCharAndElemOf"
Level 3
Title "Element of Left Word is Element of Appended Word"

Introduction "The following proof states that character membership is preserved when a word is appended
to another. Precisely, if a character appears in the left word, then it also appears in the word formed
by appending any right word to it."

/--
Character membership is preserved under append on the left word.

If a character ```char``` appears in the word ```left```, then it also appears
in the appended word ```left ++ right``` for any word ```right```.
-/
TheoremDoc Word.char_elemOf_append_left as "char_elem_of_append_left" in "Word"

Statement char_elemOf_append_left (left right : Word) (char : Character) :
elemOf char left -> elemOf char (left ++ right) := by
  induction left generalizing right with
  | nil =>
    Hint "You can split the implication in the current expression by executing ```intros h```. This
    creates an induction hypothesis using the term on the left-hand side of the ```->``` sign and
    creates a proof goal out of the term on the right-hand side."
    intros h
    Branch
      exfalso
      apply h
    cases h
  | cons head tail ih =>
    intros h
    Hint "Now, you can proceed by simplifying your hypothesis ```h```. Any other simplification is
    currently not possible with the given theorems."
    simp [elemOf] at h
    Hint "If you now observe ```h```, you see that it is a clause of the form ```A ∨ B```. So, to
    prove the statement for all possible return values of ```elemOf```, you can proceed with
    executing the ```cases``` tactic with the hypothesis ```h```."
    cases h
    Hint "As you already observed in the previous steps, the ```elemOf``` function returns a clause
    of the form ```A ∨ B```. For your current proof goal, it means that you can access any of the
    clauses by using the respective tactics ```left``` or ```right``` and observe them individually."
    left
    exact h_1
    right
    apply ih at h_1
    exact h_1

Conclusion "Very good! Next, you will show the ```∈w``` property for any second word or right word in
the append function."

NewTactic intros exfalso left right
NewDefinition Word.elemOf
