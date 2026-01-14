import Game.Levels.CountCharAndElemOf

namespace Word

World "AnBnNotRegular"
Level 1
Title "The Number of ```A```s is Equal to the Number of ```B```s in ```anBnLang```"

Introduction ""

TheoremDoc Word.count_a_eq_count_b as "count_a_eq_count_b" in "AnBnLang"

Statement count_a_eq_count_b (word : Word) :
word ∈ anBnLang.l -> countCharInWord Character.a word = countCharInWord Character.b word := by
  intro h
  rcases h with ⟨n⟩
  rewrite [h]
  simp [count_char_in_append]
  repeat rewrite [count_char_in_replicateChar]
  simp

Conclusion ""
