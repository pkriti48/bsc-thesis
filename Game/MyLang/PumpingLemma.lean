import Game.MyLang.OperationTheorems

namespace Word

def pumpingProperty (lang : Lang) :=
  ∃ (n : Nat) (H : n > 0),
  ∀ z : Word, z ∈ lang.l ∧ length z ≥ n →
  ∃ u v w : Word, z = ((u ++ v) ++ w) ∧
  length (u ++ v) ≤ n ∧
  length v ≥ 1 ∧
  ∀ (i : Nat), ((u ++ (replicateWord v i)) ++ w) ∈ lang.l

def anBnLang : Lang :=
  {l := { z | ∃ j : Nat, z = (replicateChar Character.a j) ++ (replicateChar Character.b j)}}

theorem count_a_eq_count_b_in_anBnLang {word : Word} :
word ∈ anBnLang.l -> countCharInWord Character.a word = countCharInWord Character.b word := by
  intro h
  rcases h with ⟨n⟩
  rewrite [h]
  simp [count_char_in_append]
  repeat rewrite [count_char_in_replicateChar]
  simp

theorem word_count_as {char : Character} {word : Word}
{h : ∀ char : Character, inWord char word -> char = Character.a} :
countCharInWord Character.a word = length word := by
  induction word with
  | nil =>
    rewrite [countCharInWord]
    rewrite [length]
    rfl
  | cons head tail ih =>
    simp [inWord] at h
    have h_head : head = Character.a := by
      apply h
      simp
    simp [h_head]
    simp [countCharInWord]
    rewrite [ih]
    rewrite [length]
    rfl
    have h_tail : ∀ char, inWord char tail → char = Character.a := by
      intros ch h_ch
      apply h
      apply Or.inr
      exact h_ch
    exact h_tail

theorem word_count_bs {char : Character} {word : Word}
{h : ∀ char : Character, inWord char word -> char = Character.a} :
countCharInWord Character.b word = 0 := by
  induction word with
  | nil =>
    rewrite [countCharInWord]
    rfl
  | cons head tail ih =>
    simp [inWord] at h
    have h_head : head = Character.a := by
      apply h
      simp
    simp [h_head]
    simp [countCharInWord]
    rewrite [ih]
    rfl
    have h_tail : ∀ char, inWord char tail → char = Character.a := by
      intros ch h_ch
      apply h
      apply Or.inr
      exact h_ch
    exact h_tail

theorem lang_not_regular : ¬ pumpingProperty anBnLang := by
  -- wenn word in lang anbn dann folgt, dass die Anzahl von as und bs ist gleich
  intro h
  rewrite [pumpingProperty] at h
  -- Sei n ∈ ℕ ∧ n ≠ 0 beliebig.
  rcases h with ⟨n, h_n, h_word⟩
  -- Wir wählen z ∈ L als z = (a^n)(b^n) mit |z| ≥ n.
  let a_n := replicateChar Character.a n
  let b_n := replicateChar Character.b n
  let z := a_n ++ b_n
  have z_in_lang : z ∈ anBnLang.l := by
    unfold anBnLang
    simp
    exists n
  have length_z : length z ≥ n := by
    simp [z, a_n, b_n]
    rewrite [length_append]
    rewrite [length_replicateChar]
    rewrite [length_replicateChar]
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
  have u_v_all_a : (u ++ v) = take a_n k := by
    have helper := congrArg (fun s => take s k) z_eq
    simp at helper
    rewrite [take_append_u_v_eq_take_u, take_append_u_v_eq_take_u] at helper
    rewrite [take_append] at helper
    rewrite [helper]
    rfl
    rewrite [length_append]
    simp [k]
    simp [a_n]
    rewrite [length_replicateChar]
    exact k_leq_n
  have length_w : length w = length z - k := by
      simp [z_eq, k]
      repeat rewrite [length_append]
      simp
  have length_u_lt_k : length u < k := by
    simp [k]
    rewrite [<- add_zero 1] at length_v
    rewrite [add_comm] at length_v
    rewrite [<- Nat.succ_eq_add_one] at length_v
    exact Nat.lt_of_succ_le length_v
  have w_eq_sub_n_k_as_n_bs : w = append (replicateChar Character.a (n - k)) b_n := by
    have helper := congrArg (fun s => drop s k) z_eq
    simp at helper
    simp [z] at helper
    simp [z, a_n, b_n] at z_eq
    rewrite [drop_append] at helper
    rewrite [drop_append] at helper
    rewrite [drop_append'] at helper
    have : k - length u = length v := by simp [k]
    simp [this] at helper
    have v_drop_all: drop v (length v) = nil := by
      apply drop_all
      rfl
    simp [v_drop_all] at helper
    rewrite [append] at helper
    simp [a_n] at helper
    rewrite [drop_replicateChar] at helper
    rewrite [helper]
    rfl
    exact k_leq_n
    exact length_u_lt_k
    simp [k]
    rewrite [length_append]
    rfl
    simp [a_n, k]
    rewrite [length_replicateChar]
    rewrite [<- length_append]
    exact length_u_v
  -- |v| ≥ 1 und u(v^i)w ∈ L für jedes i ∈ ℕ.
  have u_all_a : ∀ char : Character, inWord char u -> char = Character.a := by
    intros char h
    apply (char_in_left_subset_is_in_append (right := v)) at h
    rewrite [u_v_all_a] at h
    rewrite [take_replicateChar_n_k_eq_replicateChar_k] at h
    apply all_char_in_replicateChar_char at h
    exact h
    exact k_leq_n
  have v_all_a : ∀ char : Character, inWord char v -> char = Character.a := by
    intros char h
    apply (char_in_right_subset_is_in_append (left := u)) at h
    rewrite [u_v_all_a] at h
    rewrite [take_replicateChar_n_k_eq_replicateChar_k] at h
    apply all_char_in_replicateChar_char at h
    exact h
    exact k_leq_n
  -- Dann ist u = a^r, v = a^s mit r + s ≤ n, s ≥ 1 und w = (a^t)(b^n) mit r + s + t = n.
  have length_z_eq_2n : length z = 2 * n := by
    simp [z, a_n, b_n]
    rewrite [length_append]
    rewrite [length_replicateChar, length_replicateChar]
    rewrite [<- two_mul]
    rfl
  have length_u_v_w_eq_2n : length u + length v + length w = 2 * n := by
    simp [<- length_z_eq_2n]
    simp [z_eq]
    rewrite [length_append, length_append]
    rfl
  have length_w_eq_sub_length_z_k : length w = length z - k := by
    simp [z_eq]
    simp [length_append]
    simp [k]
  have length_w_geq_n : length w ≥ n := by
    rewrite [length_w_eq_sub_length_z_k]
    simp [length_z_eq_2n]
    have derive_n_leq_sub_2n_k := Nat.sub_le_sub_left k_leq_n (2 * n)
    rewrite [two_mul] at derive_n_leq_sub_2n_k
    simp at derive_n_leq_sub_2n_k
    rewrite [two_mul]
    exact derive_n_leq_sub_2n_k
  have w_count_as : countCharInWord Character.a w = length w - n := by
    simp [w_eq_sub_n_k_as_n_bs]
    rewrite [count_char_in_append]
    simp [count_char_in_replicateChar]
    rewrite [length_append]
    rewrite [length_replicateChar]
    simp [b_n]
    rewrite [length_replicateChar]
    simp [count_char_in_replicateChar]
  have w_count_bs : countCharInWord Character.b w = n := by
    simp [w_eq_sub_n_k_as_n_bs]
    rewrite [count_char_in_append]
    simp [b_n]
    simp [count_char_in_replicateChar]
  have v_count_as : countCharInWord Character.a v = length v := by
    rewrite [word_count_as]
    rfl
    exact Character.a
    exact v_all_a
  have v_count_bs : countCharInWord Character.b v = 0 := by
    rewrite [word_count_bs]
    rfl
    exact Character.b
    exact v_all_a
  have u_count_as : countCharInWord Character.a u = length u := by
    rewrite [word_count_as]
    rfl
    exact Character.a
    exact u_all_a
  have u_count_bs : countCharInWord Character.b u = 0 := by
    rewrite [word_count_bs]
    rfl
    exact Character.b
    exact u_all_a
  -- Wenn wir nun i=2 wählen, gilt uv^2w = (a^r)(a^s)(a^s)(a^t)(b^n) ∉ L, da s ≥ 1.
  let z_pumped := (u ++ (replicateWord v 2)) ++ w
  have z_pumped_in_lang : z_pumped ∈ anBnLang.l := by
    specialize pump_word 2
    simp [z_pumped]
    exact pump_word
  --Wir zeigen nun: |a| ≥ |b| mit |a| = n+s und |b| = n. Damit liegt z_pumped nicht in anBnLang.
  apply count_a_eq_count_b_in_anBnLang at z_pumped_in_lang
  have more_as_than_bs_in_z_pumped : (countCharInWord Character.b z_pumped) < countCharInWord Character.a z_pumped := by
    simp [z_pumped]
    repeat rewrite [replicateWord]
    repeat rewrite [append_nil]
    repeat rewrite [count_char_in_append]
    simp [w_count_as]
    simp [w_count_bs]
    simp [v_count_as]
    simp [v_count_bs]
    simp [u_count_as]
    simp [u_count_bs]
    have : u.length + (v.length + v.length) + (w.length - n) = n + length v := by
      rewrite [<- Nat.add_sub_assoc]
      rewrite [<- Nat.add_left_comm]
      rewrite [Nat.add_assoc]
      simp [length_u_v_w_eq_2n]
      rewrite [two_mul]
      rewrite [<- Nat.add_assoc]
      rewrite [Nat.add_sub_self_right]
      rewrite [add_comm]
      rfl
      exact length_w_geq_n
    simp [this]
    rewrite [<- add_zero 1] at length_v
    rewrite [add_comm] at length_v
    rewrite [<- Nat.succ_eq_add_one] at length_v
    exact Nat.lt_of_succ_le length_v
  linarith
