import Game.MetaData

namespace Word

World "The Append and Concat World"
Level 1

Title "Append an Empty Word to a Non-Empty Word"

Introduction "In this level, you will prove that appending ```nil``` to a word results in the word itself."

Statement append_nil (word : Word) : (word ++ nil) = word := by
  induction word with
  | nil =>
    rewrite [append]
    rfl
  | cons head tail ih =>
    rewrite [append]
    rewrite [ih]
    rfl

NewTactic rewrite rfl induction
NewTheorem add_comm add_assoc
NewDefinition Word.concat

Conclusion "This last message appears if the level is solved."
