import Game.Levels.AnBnNotRegular.L15_MoreAsThanBs

namespace Word

World "AnBnNotRegular"
Level 16
Title "AnBnLang is Not Regular"

Introduction "In this final level of the game, you will prove that the language $L = {a^n b^n | n
≥ 0}$ is not regular."

/--
This theorem states that the language $L = {a^n b^n | n ≥ 0}$ is not regular.
-/
TheoremDoc Word.an_bn_not_regular as "an_bn_not_regular" in "Word"

Statement an_bn_not_regular : ¬ pumpingProperty anBnLang := by
  -- wenn word in lang anbn dann folgt, dass die Anzahl von as und bs ist gleich
  intro h
  rewrite [pumpingProperty] at h
  -- Sei n ∈ ℕ ∧ n ≠ 0 beliebig.
  rcases h with ⟨n, h_n, h_word⟩
  -- Wir wählen z ∈ L als z = (a^n)(b^n) mit |z| ≥ n.
  let z := replicateChar Character.a n ++ replicateChar Character.b n
  have z_in_lang : z ∈ anBnLang.l := by
    unfold anBnLang
    simp
    exists n
  have length_z : length z ≥ n := by
    simp [z]
    rewrite [length_z_eq_2n]
    simp [Nat.two_mul]
  -- Sei z = uvw eine beliebige Zerlegung von z, ...
  have h := h_word z ⟨z_in_lang, length_z⟩
  rcases h with ⟨u, v, w, z_eq, length_u_v, length_v, pump_word⟩
  -- sodass |uv| ≤ n, ...
  let k := length u + length v
  have k_leq_n : k ≤ n := by
    simp [k]
    rewrite [<- length_append]
    exact length_u_v
  -- |v| ≥ 1 und u(v^i)w ∈ L für jedes i ∈ ℕ.
  -- Dann ist u = a^r, v = a^s mit r + s ≤ n, s ≥ 1 und w = (a^t)(b^n) mit r + s + t = n.
  -- Wenn wir nun i=2 wählen, gilt uv^2w = (a^r)(a^s)(a^s)(a^t)(b^n) ∉ L, da s ≥ 1.
  let z_pumped := (u ++ (replicateWord v 2)) ++ w
  have z_pumped_in_lang : z_pumped ∈ anBnLang.l := by
    specialize pump_word 2
    simp [z_pumped]
    exact pump_word
  --Wir zeigen nun: |a| ≥ |b| mit |a| = n+s und |b| = n. Damit liegt z_pumped nicht in anBnLang.
  apply count_a_eq_count_b at z_pumped_in_lang
  have z_pumped_not_in_lang : countCharInWord Character.b z_pumped < countCharInWord Character.a z_pumped := by
    apply more_as_than_bs u v w z z_pumped n k (z_eq := z_eq) (k_leq_n := k_leq_n) (length_u_v_leq_n := length_u_v) (length_v_geq_1 := length_v)
    simp [z]
    simp [k]
    simp [z_pumped]
  linarith [z_pumped_in_lang, z_pumped_not_in_lang]

Conclusion ""

NewTactic «exists» «let» linarith specialize unfold
NewDefinition Word.pumpingProperty
