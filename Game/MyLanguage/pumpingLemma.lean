import Game.MyLanguage.formalLanguage
import Game.MyLanguage.operations
import Game.MyLanguage.operationTheorems

namespace Word

def pumpingLemma (lang : Lang) :=
  ∃ (n : Nat) (H : n > 0),
  ∀ z : Word, z ∈ lang.l ∧ length z ≥ n →
  ∃ u v w : Word, z = append (append u v) w ∧
  length (append u v) ≤ n ∧
  length v ≥ 1 ∧
  ∀ (i : Nat), (append (append u (appendSelfNTimes v i)) w) ∈ lang.l

def anBnLang : Lang :=
  {l := { z | ∃ n : Nat, z = append (concatSelfNTimes Character.a n) (concatSelfNTimes Character.b n)}}

theorem lang_not_regular : ¬ pumpingLemma anBnLang := by
  intro h
  rewrite [pumpingLemma] at h
  -- Sei n ∈ ℕ ∧ n ≠ 0 beliebig.
  rcases h with ⟨n, h_n, h_word⟩
  -- Wir wählen z ∈ L als z = (a^n)(b^n) mit |z| ≥ n.
  let a_n := concatSelfNTimes Character.a n
  let b_n := concatSelfNTimes Character.b n
  let z := append a_n b_n
  have z_in_lang : z ∈ anBnLang.l := by
    unfold anBnLang
    simp
    exists n
  have length_z : length z ≥ n := by
    simp [z, a_n, b_n]
    rewrite [length_append]
    rewrite [length_concatSelfNTimes]
    rewrite [length_concatSelfNTimes]
    apply le_add_right
    rfl
  -- Sei z = uvw eine beliebige Zerlegung von z, ...
  have h := h_word z ⟨z_in_lang, length_z⟩
  rcases h with ⟨u, v, w, z_eq, length_u_v, length_v, pump_word⟩
  -- sodass |uv| ≤ n, ...
  let k := length u + length v
  have k_leq_n : k ≤ n := by
    simp [k]
    rewrite [<- length_append]
    exact length_u_v
  have u_v_eq_k_as : append u v = take a_n k := by
    have helper := congrArg (fun s => take s k) z_eq
    simp at helper
    rewrite [take_append_u_v_eq_take_u, take_append_u_v_eq_take_u] at helper
    rewrite [take_append] at helper
    rewrite [helper]
    rfl
    rewrite [length_append]
    simp [k]
    simp [a_n]
    rewrite [length_concatSelfNTimes]
    exact k_leq_n
  -- |v| ≥ 1 und u(v^i)w ∈ L für jedes i ∈ ℕ.
  have v_all_a : ∀ char : Character, inWord char v -> char = Character.a := by
    intros char h
    apply char_in_right_subset_is_in_append at h
    rewrite [u_v_eq_k_as] at h
    rewrite [take_concatSelfNTimes_n_k_eq_concatSelfNTimes_k] at h
    apply all_char_in_concatSelfNTimes_char at h
    exact h
    exact k_leq_n
  -- Dann ist u = a^r, v = a^s mit r + s ≤ n, s ≥ 1 und w = (a^t)(b^n) mit r + s + t = n.
  have length_z_eq_2n : length z = 2 * n := by
    simp [z, a_n, b_n]
    rewrite [length_append]
    rewrite [length_concatSelfNTimes, length_concatSelfNTimes]
    rewrite [<- two_mul]
    rfl
  have length_u_v_w_eq_2n : length u + length v + length w = 2 * n := by
    simp [<- length_z_eq_2n]
    simp [z_eq]
    rewrite [length_append, length_append]
    rfl
  -- Wenn wir nun i=2 wählen, gilt uv^2w = (a^r)(a^s)(a^s)(a^t)(b^n) ∉ L, da s ≥ 1.
  let z_pumped := append (append u (appendSelfNTimes v 2)) w
  have z_pumped_in_anBnLang : z_pumped ∈ anBnLang.l := by
    specialize pump_word 2
    simp [z_pumped]
    exact pump_word
  --Wir zeigen nun: |a| ≥ |b| mit |a| = n+s und |b| = n. Damit liegt z_pumped nicht in anBnLang.
  have more_as_than_bs_in_z_pumped : (length z_pumped) - (length b_n) ≥ 1 := by
    simp [z_pumped, b_n]
    simp [appendSelfNTimes]
    rewrite [append_nil]
    simp [length_append]
    rewrite [<- add_assoc]
    rewrite [Nat.add_assoc (length u + length v)]
    rewrite [<- Nat.add_comm (length w)]
    rewrite [<- Nat.add_assoc]
    simp [length_u_v_w_eq_2n]
    rewrite [length_concatSelfNTimes]
    rewrite [two_mul]
    rewrite [add_assoc]
    rewrite [Nat.add_sub_cancel_left]
    linarith
  have ⟨j, h_j⟩ := z_pumped_in_anBnLang
  have length_z_eq_length_z_pumped : 2 * n = 2 * j := by
    simp [<- length_z_eq_2n]
    simp [z_eq]
    simp [length_append]
    have length_z_pumped_eq_2j : length z_pumped = 2 * j := by
      simp [h_j]
      simp [length_append]
      simp [length_concatSelfNTimes]
      rewrite [<- two_mul]
      rfl
    have length_u_v_v_w_pumped_eq_2j : length u + length v + length v + length w = 2 * j := by
      simp [<- length_z_pumped_eq_2j]
      simp [z_pumped]
      simp [appendSelfNTimes]
      rewrite [append_nil]
      simp [length_append]
      rewrite [<- add_assoc]
      rfl
    simp [<- length_u_v_v_w_pumped_eq_2j]
    sorry
  sorry
