import Game.Levels.AjBjNotRegular.L15_MoreAsThanBs

namespace Word

World "AjBjNotRegular"
Level 16
Title "AjBjLang is Not Regular"

Introduction "In this final level of the game, you will prove that the language $L = {a^j b^j | j
≥ 0}$ is not regular."

/--
This theorem states that the language $L = {a^j b^j | j ≥ 0}$ is not regular.
-/
TheoremDoc Word.aj_bj_not_regular as "aj_bj_not_regular" in "Word"

Statement aj_bj_not_regular : pumpingProperty ajBjLang → False := by
  Hint "You start by splitting your proof goal into the hypothesis ```pumpingProperty ajBjLang```
  and a proof goal ```False```. This is analogue to specifying 'proof by contradiction' in a
  pen-and-paper proof."
  intro h
  rewrite [pumpingProperty] at h
  Hint "As you can see, the hypothesis you created using ```intro``` is not in its simplest form
  yet. In order to simplify it further, remove all quantifiers you can."
  Hint "To remove the quantifiers, you can use the ```cases``` tactic and simplify the hypothesis
  manually as far as required/possible or you can use the ```rcases``` tactic which simplifies the
  hypothesis recursively as far as possible. When using ```rcases```, you can specify the names of
  the new hypothesis and expressions to be introduced. You could use the following names:  ```n```,
  ```h_n```, ```h_word```."
  rcases h with ⟨n, h_n, h_word⟩
  Hint "At this point, you choose your word ```z``` with that you are gonna prove that ```ajBjLang```
  is not regular."
  let z := replicateChar Character.a n ++ replicateChar Character.b n
  have z_in_lang : z ∈ ajBjLang.l := by
    unfold ajBjLang
    simp
    exists n
  have length_z : length z ≥ n := by
    simp [z]
    rewrite [length_z_eq_2n]
    simp [Nat.two_mul]
  Hint "Now, you decompose your word ```z``` as ```z = (u ++ v) ++ w```, by first introducing an
  auxiliary statement that feeds ```h_word``` with the word ```z``` you chose and the properties
  ```z_in_lang``` and ```length_z```. Then you can split the newly introduced logical statement into
  individual statements/hypotheses and proceed with the proof."
  have h := h_word z ⟨z_in_lang, length_z⟩
  rcases h with ⟨u, v, w, z_eq, length_u_v, length_v, pump_word⟩
  -- sodass |uv| ≤ n, ...
  let k := length (u ++ v)
  -- |v| ≥ 1 und u(v^i)w ∈ L für jedes i ∈ ℕ.
  -- Dann ist u = a^r, v = a^s mit r + s ≤ n, s ≥ 1 und w = (a^t)(b^n) mit r + s + t = n.
  -- Wenn wir nun i=2 wählen, gilt uv^2w = (a^r)(a^s)(a^s)(a^t)(b^n) ∉ L, da s ≥ 1.
  Hint "Next, you can introduce your pumped word, show that it is an element of ```ajBjLang``` and
  finally derive the contradiction."
  let z_pumped := (u ++ (replicateWord v 2)) ++ w
  have z_pumped_in_lang : z_pumped ∈ ajBjLang.l := by
    specialize pump_word 2
    simp [z_pumped]
    exact pump_word
  --Wir zeigen nun: |a| ≥ |b| mit |a| = n+s und |b| = n. Damit liegt z_pumped nicht in ajBjLang.
  apply count_a_eq_count_b at z_pumped_in_lang
  have z_pumped_not_in_lang : countCharInWord Character.b z_pumped < countCharInWord Character.a z_pumped := by
    apply more_as_than_bs u v w z z_pumped n k (z_eq := z_eq) (length_u_v_leq_n := length_u_v) (length_v_geq_1 := length_v)
    simp [z]
    simp [k]
    simp [z_pumped]
  linarith [z_pumped_in_lang, z_pumped_not_in_lang]

Conclusion "Well done! You did it! You proved that the language $L = {a^j b^j | j ≥ 0}$ is not
regular. By, now you should have understood how exactly the pumping lemma is built and how to use it
to prove that a language is not regular."

NewTactic «exists» «let» linarith rcases specialize unfold
NewDefinition Word.pumpingProperty
