import Game.Levels.CountCharAndElemOf.L03_CharInAppendLeft

namespace Word

World "CountCharAndElemOf"
Level 4
Title "Element of Second Word is Element of Appended Word"

Introduction "The goal of this level is to prove that if a character appears in the right word,
then it also appears in the word formed by appending this word to any other word."


/--
If a character ```char``` appears in the word ```right```, then it also appears
in the appended word ```left ++ right``` for any word ```left```.
-/
TheoremDoc Word.char_elemOf_append_right as "char_elemOf_append_right" in "Word"

Statement char_elemOf_append_right (left right : Word) (char : Character) :
elemOf char right -> elemOf char (left ++ right) := by
  induction left with intros h
  | nil =>
    rewrite [append]
    exact h
  | cons head tail ih =>
    rewrite [append]
    rewrite [elemOf]
    apply ih at h
    Hint "As you can observe in your current proof goal, the term on the right-hand side of the
    ```∨``` matches your induction hypothesis. So, you can retrieve it by using the keyword
    ```right``` and then proceed with the proof."
    right
    exact h

Conclusion "Very good! Now, let's proceed towards the last proof of this world!"
