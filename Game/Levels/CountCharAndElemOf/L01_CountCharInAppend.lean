import Game.Levels.TakeAndDrop

namespace Word

World "CountCharAndElemOf"
Level 1
Title "Count Occurrences of a Character in an Appended Word"

Introduction "The following statement ```count_char_in_append``` proves that the number of times a
character appears in the appended word is exactly the sum of its occurrences in each of the original
words."

/--
Counting characters distributes over word append.

For any character ```char``` and words ```word_1` and ```word_2```, the number of
occurrences of ```char``` in the appended word ```word_1 ++ word_2``` is the sum
of the numbers of occurrences of ```char``` in ```word_1``` and in ```word_2```.
-/
TheoremDoc Word.count_char_in_append as "count_char_in_append" in "Word"

Statement count_char_in_append (char : Character) (word_1 word_2 : Word) :
countCharInWord char (word_1 ++ word_2) = countCharInWord char word_1 + countCharInWord char word_2 := by
  induction word_1 generalizing word_2 with
  | nil =>
    rewrite [append]
    rewrite [countCharInWord]
    rewrite [zero_add]
    rfl
  | cons head tail ih =>
    simp [append]
    simp [countCharInWord]
    simp [ih]
    rewrite [add_assoc]
    rfl

Conclusion "Very good! You just how ```countCharInWord``` behaves in combination with the ```append```
function. Now, let's move over to showing the behavior of ```countCharInWord``` in combination with
```replicateChar```."

NewDefinition Word.countCharInWord
