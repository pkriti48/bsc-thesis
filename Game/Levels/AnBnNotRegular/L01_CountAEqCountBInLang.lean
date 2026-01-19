import Game.Levels.CountCharAndElemOf

namespace Word

World "AnBnNotRegular"
Level 1
Title "The Number of as is Equal to the Number of bs in anBnLang"

Introduction "In this level, you will prove that if any word is an element of the language
```anBnLang```, then the number of occurrences of the character ```a``` equals the number of
occurrences of the character ```b``` in that word. This follows from the definition of
```anBnLang```, where each word is constructed using an equal number of replicas of ```a```
followed by the same number of replicas of ```b```."

/--
This lemma states that if a word is an element of the language ```anBnLang```, then the number of
occurrences of the character ```a``` equals the number of occurrences of the character ```b``` in
that word.
-/
TheoremDoc Word.count_a_eq_count_b as "count_a_eq_count_b" in "AnBnNotRegular"

Statement count_a_eq_count_b (word : Word) :
word ∈ anBnLang.l -> countCharInWord Character.a word = countCharInWord Character.b word := by
  intro h
  rcases h with ⟨n⟩
  rewrite [h]
  simp [count_char_in_append]
  repeat rewrite [count_char_in_replicateChar]
  simp

Conclusion "Well done! You just proved the first theorem, which is part of the final proof for the
fact that ```anBnLang``` is not regular. Let's move on to the next proof."

NewTactic intro rcases
NewDefinition Word.anBnLang
