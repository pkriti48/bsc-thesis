import Game.Levels.CountCharAndElemOf

namespace Word

World "AjBjNotRegular"
Level 1
Title "The Number of as is Equal to the Number of bs in ajBjLang"

Introduction "In this level, you will prove that if any word is an element of the language
```ajBjLang```, then the number of occurrences of the character ```a``` equals the number of
occurrences of the character ```b``` in that word. This follows from the definition of
```ajBjLang```, where each word is constructed using an equal number of replicas of ```a```
followed by the same number of replicas of ```b```."

/--
This lemma states that if a word is an element of the language ```ajBjLang```, then the number of
occurrences of the character ```a``` equals the number of occurrences of the character ```b``` in
that word.
-/
TheoremDoc Word.count_a_eq_count_b as "count_a_eq_count_b" in "AjBjNotRegular"

Statement count_a_eq_count_b (word : Word) :
word ∈ ajBjLang.l -> countCharInWord Character.a word = countCharInWord Character.b word := by
  Hint "You can start by splitting the implication in your current proof using the ```intro```
  tactic. By doing this, you will obtain a hypothesis which corresponds to the term on the
  left-hand side of the ```->``` sign and your proof goal will correspond to the term on the
  right-hand side of the ```->``` sign."
  intro h
  Hint "Next, you can proceed by executing the ```cases``` tactic on your hypothesis introduced
  in the previous proof step. This will evaluate all possible values of the term in the hypothesis
  and close the unreachable goals automatically leaving you with a new hypothesis ```word =
  replicateChar Character.a _ ++ replicateChar Character.b _```, where ```_``` represents the
  number of replicas to be created."
  cases h
  rewrite [h_1]
  Hint "Try to remember, which of the theorems proven in the previous worlds is appropriate to
  proceed with the current proof goal."
  simp [count_char_in_append]
  repeat rewrite [count_char_in_replicateChar]
  Hint "Finally, you can simplify the current proof goal and complete the first proof in this
  world."
  simp

Conclusion "Well done! You just proved the first theorem, which is part of the final proof for the
fact that ```ajBjLang``` is not regular. Let's move on to the next proof."

NewTactic intro
NewDefinition Word.ajBjLang
