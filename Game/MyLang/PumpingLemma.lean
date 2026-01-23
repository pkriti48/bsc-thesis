import Game.MyLang.OperationTheorems

namespace Word

theorem count_a_eq_count_b_in_anBnLang {word : Word} :
word ∈ anBnLang.l -> countCharInWord Character.a word = countCharInWord Character.b word := by
  intro h
  rcases h with ⟨n⟩
  rewrite [h]
  simp [count_char_in_append]
  repeat rewrite [count_char_in_replicateChar]
  simp

theorem count_a_in_replicateChar_a {char : Character} {word : Word}
{h : ∀ char : Character, elemOf char word -> char = Character.a} :
countCharInWord Character.a word = length word := by
  induction word with
  | nil =>
    rewrite [countCharInWord]
    rewrite [length]
    rfl
  | cons head tail ih =>
    simp [elemOf] at h
    have h_head : head = Character.a := by
      apply h
      simp
    simp [h_head]
    simp [countCharInWord]
    rewrite [ih]
    rewrite [length]
    rfl
    have h_tail : ∀ char, elemOf char tail → char = Character.a := by
      intros ch h_ch
      apply h
      apply Or.inr
      exact h_ch
    exact h_tail

theorem count_b_in_replicateChar_a {char : Character} {word : Word}
{h : ∀ char : Character, elemOf char word -> char = Character.a} :
countCharInWord Character.b word = 0 := by
  induction word with
  | nil =>
    rewrite [countCharInWord]
    rfl
  | cons head tail ih =>
    simp [elemOf] at h
    have h_head : head = Character.a := by
      apply h
      simp
    simp [h_head]
    simp [countCharInWord]
    rewrite [ih]
    rfl
    have h_tail : ∀ char, elemOf char tail → char = Character.a := by
      intros ch h_ch
      apply h
      right
      exact h_ch
    exact h_tail

theorem take_replicateChar_append (n k : Nat) (k_leq_n : k ≤ n) :
take (replicateChar Character.a n ++ replicateChar Character.b n) k = replicateChar Character.a k := by
  rewrite [take_append_u_v_eq_take_u]
  rewrite [take_replicateChar_n_k_eq_replicateChar_k (h := k_leq_n)]
  rfl
  rewrite [length_replicateChar]
  exact k_leq_n

theorem take_all (word : Word) : take word (length word) = word := by
  induction word with
  | nil =>
    rewrite [length]
    rewrite [take]
    rfl
  | cons head tail ih =>
    rewrite [length]
    simp [take]
    exact ih

theorem left_eq_replicateChar_a (left right word : Word) (n : Nat)
(h_z : word = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : word = left ++ right)
(length_u_v_leq_n : length left ≤ n) :
left = replicateChar Character.a (length left) := by
  have helper := congrArg (fun f => take f (length left)) z_eq
  simp at helper
  simp [h_z] at helper
  rewrite [take_replicateChar_append (k_leq_n := length_u_v_leq_n)] at helper
  rewrite [helper]
  rewrite [take_append_u_v_eq_take_u]
  rewrite [take_all]
  rfl
  rfl

theorem count_char_in_u (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.a u = length u ∧ countCharInWord Character.b u = 0 := by
  constructor
  apply count_a_in_replicateChar_a
  exact Character.a
  intros char h
  apply char_in_left_subset_is_in_append (right := v) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply all_char_in_replicateChar_char at h
  exact h
  apply count_b_in_replicateChar_a
  exact Character.b
  intros char h
  apply char_in_left_subset_is_in_append (right := v) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply all_char_in_replicateChar_char at h
  exact h

theorem count_a_in_u (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.a u = length u := by
  apply count_a_in_replicateChar_a
  exact Character.a
  intros char h
  apply char_in_left_subset_is_in_append (right := v) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply all_char_in_replicateChar_char at h
  exact h

theorem count_b_in_u (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.b u = 0 := by
  rewrite [count_b_in_replicateChar_a]
  rfl
  exact Character.b
  intros char h
  apply char_in_left_subset_is_in_append (right := v) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply all_char_in_replicateChar_char at h
  exact h

theorem count_a_in_v (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.a v = length v := by
  rewrite [count_a_in_replicateChar_a]
  rfl
  exact Character.a
  intros char h
  apply char_in_right_subset_is_in_append (left := u) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply all_char_in_replicateChar_char at h
  exact h

theorem count_b_in_v (u v w z : Word) (n : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w)
(length_u_v_leq_n : length (u ++ v) ≤ n) :
countCharInWord Character.b v = 0 := by
  rewrite [count_b_in_replicateChar_a]
  rfl
  exact Character.b
  intros char h
  apply char_in_right_subset_is_in_append (left := u) at h
  rewrite [left_eq_replicateChar_a (u ++ v) w z n h_z z_eq length_u_v_leq_n] at h
  apply all_char_in_replicateChar_char at h
  exact h

theorem length_z_eq_2n (n : Nat) :
length (replicateChar Character.a n ++ replicateChar Character.b n) = 2 * n := by
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  rewrite [two_mul]
  rfl

theorem length_w (u v w z : Word) (k : Nat) (z_eq : z = (u ++ v) ++ w)
(h_k : k = length u + length v) : length w = length z - k := by
  rewrite [z_eq]
  rewrite [h_k]
  repeat rewrite [length_append]
  rewrite [Nat.add_sub_cancel_left]
  rfl

theorem length_pumped_word (u v w z : Word) (n k : Nat)
(z_eq : z = (u ++ v) ++ w)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(k_leq_n : k ≤ n) (h_k : k = length u + length v) :
u.length + (v.length + v.length) + (w.length - n) = n + length v := by
  rewrite [<- Nat.add_sub_assoc]
  rewrite [<- Nat.add_left_comm]
  rewrite [Nat.add_assoc]
  rewrite [Nat.add_comm n]
  rewrite [<- length_append]
  rewrite [<- length_append]
  rewrite [<- z_eq]
  rewrite [Nat.add_sub_assoc]
  rewrite [Nat.add_left_cancel_iff]
  rewrite [h_z]
  rewrite [length_z_eq_2n]
  rewrite [two_mul]
  rewrite [Nat.add_sub_cancel]
  rfl
  rewrite [h_z]
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  apply Nat.le_add_right n n
  rewrite [length_w u v w z k z_eq h_k]
  rewrite [h_z]
  simp [length_z_eq_2n]
  rewrite [two_mul]
  rewrite [Nat.add_sub_assoc]
  apply Nat.le_add_right
  exact k_leq_n

theorem w_eq_remaining_as_n_bs (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k) :
w = replicateChar Character.a (n - k) ++ replicateChar Character.b n := by
  have helper := congrArg (fun s => drop s k) z_eq
  simp at helper
  rewrite [h_z] at helper
  rewrite [drop_append] at helper
  rewrite [drop_replicateChar] at helper
  rewrite [helper]
  rewrite [drop_append]
  rewrite [drop_append']
  rewrite [h_k]
  rewrite [Nat.add_sub_cancel_left]
  rewrite [drop_all]
  rewrite [append]
  repeat rfl
  exact length_u_lt_k
  rewrite [h_k]
  rewrite [length_append]
  rfl
  exact k_leq_n
  rewrite [length_replicateChar]
  exact k_leq_n

theorem count_a_in_w (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k) :
countCharInWord Character.a w = length w - n := by
  rewrite [w_eq_remaining_as_n_bs u v w z n k h_z z_eq h_k k_leq_n length_u_lt_k]
  rewrite [count_char_in_append]
  simp [count_char_in_replicateChar]
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  rewrite [Nat.add_sub_assoc]
  rewrite [Nat.sub_self]
  rewrite [Nat.add_zero]
  repeat rfl

theorem count_b_in_w (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k) :
countCharInWord Character.b w = n := by
  rewrite [w_eq_remaining_as_n_bs u v w z n k h_z z_eq h_k k_leq_n length_u_lt_k]
  rewrite [count_char_in_append]
  simp [count_char_in_replicateChar]

theorem more_as_than_bs (u v w z z_pumped : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length u + length v)
(k_leq_n : k ≤ n) (length_u_lt_k : length u < k)
(length_u_v_leq_n : length (u ++ v) ≤ n) (length_v_geq_1 : length v ≥ 1)
(h_z_pumped : z_pumped = (u ++ (replicateWord v 2)) ++ w) : (countCharInWord Character.b z_pumped) < countCharInWord Character.a z_pumped := by
  rewrite [h_z_pumped]
  repeat rewrite [replicateWord]
  repeat rewrite [append_nil]
  repeat rewrite [count_char_in_append]
  rewrite [count_a_in_u u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_b_in_u u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_a_in_v u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_b_in_v u v w z n (z_eq := z_eq) (length_u_v_leq_n := length_u_v_leq_n)]
  rewrite [count_a_in_w u v w z n k (z_eq := z_eq) (length_u_lt_k := length_u_lt_k) (k_leq_n :=
  k_leq_n)]
  rewrite [count_b_in_w u v w z n k (z_eq := z_eq) (length_u_lt_k := length_u_lt_k) (k_leq_n :=
  k_leq_n)]
  repeat rewrite [zero_add]
  rewrite [length_pumped_word u v w z n k (k_leq_n := k_leq_n)]
  apply Nat.lt_add_of_pos_right
  rewrite [<- add_zero 1] at length_v_geq_1
  rewrite [add_comm] at length_v_geq_1
  rewrite [<- Nat.succ_eq_add_one] at length_v_geq_1
  exact Nat.lt_of_succ_le length_v_geq_1
  exact z_eq
  repeat simp [h_z, h_k]

theorem lang_not_regular : ¬ pumpingProperty anBnLang := by
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
    rewrite [length_2_replicas_with_n_char_eq_2n]
    simp [two_mul]
  -- Sei z = uvw eine beliebige Zerlegung von z, ...
  have h := h_word z ⟨z_in_lang, length_z⟩
  rcases h with ⟨u, v, w, z_eq, length_u_v, length_v, pump_word⟩
  -- sodass |uv| ≤ n, ...
  let k := length u + length v
  have k_leq_n : k ≤ n := by
    simp [k]
    rewrite [<- length_append]
    exact length_u_v
  have length_u_lt_k : length u < k := by
    simp [k]
    rewrite [<- Nat.add_zero 1] at length_v
    rewrite [Nat.add_comm] at length_v
    rewrite [<- Nat.succ_eq_add_one] at length_v
    exact Nat.lt_of_succ_le length_v
  -- |v| ≥ 1 und u(v^i)w ∈ L für jedes i ∈ ℕ.
  -- Dann ist u = a^r, v = a^s mit r + s ≤ n, s ≥ 1 und w = (a^t)(b^n) mit r + s + t = n.
  -- Wenn wir nun i=2 wählen, gilt uv^2w = (a^r)(a^s)(a^s)(a^t)(b^n) ∉ L, da s ≥ 1.
  let z_pumped := (u ++ (replicateWord v 2)) ++ w
  have z_pumped_in_lang : z_pumped ∈ anBnLang.l := by
    specialize pump_word 2
    simp [z_pumped]
    exact pump_word
  --Wir zeigen nun: |a| ≥ |b| mit |a| = n+s und |b| = n. Damit liegt z_pumped nicht in anBnLang.
  apply count_a_eq_count_b_in_anBnLang at z_pumped_in_lang
  have z_pumped_not_in_lang : countCharInWord Character.b z_pumped < countCharInWord Character.a z_pumped := by
    apply more_as_than_bs u v w z z_pumped n k (z_eq := z_eq) (k_leq_n := k_leq_n)
      (length_u_lt_k := length_u_lt_k) (length_u_v_leq_n := length_u_v) (length_v_geq_1 := length_v)
    simp [z]
    simp [k]
    simp [z_pumped]
  linarith [z_pumped_in_lang, z_pumped_not_in_lang]

