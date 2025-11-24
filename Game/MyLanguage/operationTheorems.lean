import Game.MyLanguage.formalLanguage
import Game.MyLanguage.operations

namespace Word

theorem length_append {word_1 : Word} {word_2 : Word } :
length (append word_1 word_2) = length word_1 + length word_2 := by
  induction word_1 with
  | nil =>
    rewrite [append, length]
    rewrite [add_comm, add_zero]
    rfl
  | cons =>
    rewrite [append, length, length]
    rewrite [a_ih, <- add_assoc]
    rfl

theorem append_nil {word : Word} : append word .nil = word := by
  induction word with
  | nil => rfl
  | cons =>
    rewrite [append, a_ih]
    rfl

theorem length_appendSelfNTimes {word : Word} {n : Nat} :
length (appendSelfNTimes word n) = Nat.mul (length word) n := by
  induction n with
  | zero =>
    rewrite [appendSelfNTimes]
    rewrite [length]
    rewrite [Nat.mul_eq]
    rewrite [Nat.mul_zero]
    rfl
  | succ k ih =>
    rewrite [appendSelfNTimes]
    rewrite [length_append]
    rewrite [Nat.mul_eq]
    rewrite [Nat.mul_succ]
    rewrite [ih]
    simp
    rewrite [add_comm]
    rfl

theorem length_concat {word : Word} {char : Character} :
length (concat word char) = (length word) + 1 := by
  induction word with
  | nil =>
    rewrite [concat, length, length, length]
    rewrite [add_zero, add_comm, add_zero]
    rfl
  | cons =>
    rewrite [concat, length, length]
    rewrite [a_ih, add_assoc]
    rfl

theorem length_concatSelfNTimes {char : Character} {n : Nat} :
length (concatSelfNTimes char n) = n := by
  induction n with
  | zero =>
    rewrite [concatSelfNTimes]
    rewrite [length]
    rfl
  | succ k ih =>
    rewrite [concatSelfNTimes]
    rewrite [length]
    rewrite [ih]
    rewrite [add_comm]
    rfl

theorem append_concatSelfNTimes {char : Character} {m n : Nat} :
append (concatSelfNTimes char m) (concatSelfNTimes char n) = concatSelfNTimes char (m + n) := by
induction m with
| zero =>
  rewrite [concatSelfNTimes]
  rewrite [append]
  rewrite [zero_add]
  rfl
| succ =>
  rewrite [concatSelfNTimes]
  rewrite [append]
  rewrite [a]
  rewrite [Nat.succ_add]
  rewrite [concatSelfNTimes]
  rfl

theorem char_in_left_subset_is_in_append {left right : Word} {char : Character} :
inWord char left -> inWord char (append left right) := by
  induction left generalizing right with intros h
  | nil =>
    exfalso
    apply h
  | cons head tail ih =>
    cases h with
    | inl head_eq_char =>
      left
      exact head_eq_char
    | inr char_in_tail =>
      right
      apply ih at char_in_tail
      exact char_in_tail

theorem char_in_right_subset_is_in_append {left right : Word} {char : Character} :
inWord char right -> inWord char (append left right) := by
  induction left generalizing right with intros h
  | nil =>
    rewrite [append]
    exact h
  | cons head tail ih =>
    rewrite [append]
    rewrite [inWord]
    apply Or.inr
    apply ih at h
    exact h

theorem all_char_in_concatSelfNTimes_char {input_char : Character} {n : Nat} :
∀ char : Character, inWord char (concatSelfNTimes input_char n) -> char = input_char := by
  intros char h
  induction n with
  | zero =>
    rewrite [concatSelfNTimes] at h
    exfalso
    apply h
  | succ =>
    rewrite [concatSelfNTimes] at h
    rewrite [inWord] at h
    cases h with
    | inl input_char_eq_char =>
      rewrite [input_char_eq_char]
      rfl
    | inr char_in_tail =>
      rewrite [a]
      rfl
      exact char_in_tail

theorem count_char_in_append {char : Character} {word1 word2 : Word} :
countCharInWord char (append word1 word2) = countCharInWord char word1 + countCharInWord char word2 := by
  induction word1 generalizing word2 with
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

theorem count_char_in_concatSelfNTimes {char_count char : Character} {n : Nat} :
countCharInWord char_count (concatSelfNTimes char n) = (if char = char_count then n else 0) := by
  induction n with
  | zero =>
    rewrite [concatSelfNTimes]
    rewrite [countCharInWord]
    simp
  | succ k ih =>
    rewrite [concatSelfNTimes]
    rewrite [countCharInWord]
    rewrite [ih]
    have h : (char = char_count) ∨ (char ≠ char_count) := Decidable.em (char = char_count)
    cases h with
    | inl left =>
      rewrite [left]
      simp
      rewrite [add_comm]
      rfl
    | inr right =>
      simp [right]

theorem length_take_drop {word : Word} {index : Nat} :
length (take word index) + length (drop word index) = length word := by
  induction word generalizing index with
  | nil =>
    simp [drop]
    cases index with
    | zero =>
      simp [take]
      simp [length]
    | succ =>
      simp [take]
      simp [length]
  | cons =>
    cases index with
    | zero =>
      simp [take]
      simp [drop]
      simp [length]
    | succ =>
      simp [take]
      simp [drop]
      simp [length]
      rewrite [add_assoc]
      simp [a_ih]

theorem append_take_drop {word : Word} {index : Nat} :
append (take word index) (drop word index) = word := by
  induction word generalizing index with
  | nil =>
    rewrite [drop]
    rewrite [ite_self]
    rewrite [append_nil]
    cases index with
    | zero =>
      rewrite [take]
      rewrite [ite_self]
      rfl
    | succ=> simp[take]
  | cons =>
    cases index with
    | zero =>
      simp [take]
      simp [drop]
      simp [append]
    | succ =>
      simp [take]
      simp [drop]
      simp [append]
      apply a_ih

theorem take_append {word1 word2 : Word} :
take (append word1 word2) (length word1 + length word2) = append word1 word2 := by
  induction word1 with
  | nil =>
    rewrite [append]
    rewrite [length]
    rewrite [zero_add]
    induction word2 with
    | nil =>
      rewrite [length]
      simp [take]
    | cons head tail ih  =>
      rewrite [length]
      simp [take]
      exact ih
  | cons head tail ih =>
    rewrite [append]
    rewrite [length]
    simp [take]
    rewrite [<- add_comm (length tail), add_comm]
    rewrite [<- add_assoc]
    simp
    rewrite [add_comm]
    exact ih

theorem take_append_u_v_eq_take_u {u v : Word} {index : Nat} {h : index ≤ length u} :
take (append u v) index = take u index := by
  induction u generalizing index with
  | nil =>
    rewrite [length, Nat.le_zero_eq] at h
    rewrite [h, append]
    simp [take]
  | cons char tail ih =>
    cases index with
    | zero => simp [take]
    | succ =>
      rewrite [length] at h
      simp [append, take]
      apply ih
      rewrite [<- Nat.succ_eq_add_one, <- Nat.add_comm, <- Nat.succ_eq_add_one] at h
      apply Nat.le_of_succ_le_succ
      exact h

theorem take_concatSelfNTimes_n_k_eq_concatSelfNTimes_k {char : Character} {length index : Nat}
{h : index ≤ length } : take (concatSelfNTimes char length) index = concatSelfNTimes char index := by
  induction length generalizing index with
  | zero =>
    rewrite [Nat.le_zero_eq] at h
    rewrite [h]
    rewrite [concatSelfNTimes]
    rfl
  | succ n ih =>
    cases index with
    | zero =>
      rewrite [concatSelfNTimes]
      simp [take]
    | succ =>
      rewrite [concatSelfNTimes]
      rewrite [concatSelfNTimes]
      simp [take]
      apply ih
      apply Nat.le_of_succ_le_succ
      rewrite [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      exact h

theorem drop_all {word : Word} {index : Nat} {h : index = length word} : drop word index = nil := by
  induction word generalizing index with
  | nil => simp [drop]
  | cons head tail ih =>
    rewrite [length] at h
    rewrite [h]
    simp [drop]
    rewrite [ih]
    rfl
    rfl

theorem drop_append {word1 word2 : Word} {index : Nat} {h : index ≤ length word1} :
drop (append word1 word2) index = append (drop word1 index) word2 := by
  induction word1 generalizing index with
  | nil =>
    rewrite [length, Nat.le_zero_eq] at h
    rewrite [h, append]
    simp [drop]
    rewrite [append]
    induction word2 with
    | nil => simp [drop]
    | cons head tail ih => simp [drop]
  | cons head tail ih =>
    rewrite [append]
    cases index with
    | zero =>
      simp [drop]
      rewrite [append]
      rfl
    | succ k =>
      simp [drop]
      rewrite [ih]
      rfl
      rewrite [length] at h
      rewrite [<- add_comm (length tail)] at h
      rewrite [<- Nat.succ_eq_add_one k, <- Nat.succ_eq_add_one (length tail)] at h
      simp at h
      exact h

theorem drop_append' {word1 word2 : Word} {index : Nat} {h : length word1 < index} :
drop (append word1 word2) index = drop word2 (index - length word1) := by
  induction word1 generalizing index with
  | nil =>
    rewrite [append]
    rewrite [length]
    rewrite [Nat.sub_zero]
    rfl
  | cons head tail ih =>
    cases index with
    | zero =>
      cases h
    | succ k =>
      rewrite [append]
      simp [drop]
      rewrite [ih]
      rewrite [length]
      rewrite [<- add_comm (length tail)]
      repeat rewrite [<- Nat.succ_eq_add_one]
      rewrite [Nat.succ_sub_succ]
      rfl
      rewrite [length] at h
      rewrite [<- add_comm (length tail)] at h
      simp at h
      exact h

theorem drop_concatSelfNTimes {char : Character} {length index : Nat} {h : index ≤ length} :
drop (concatSelfNTimes char length) index = concatSelfNTimes char (length - index) := by
  induction length generalizing index with
  | zero =>
    rewrite [Nat.le_zero_eq] at h
    rewrite [h]
    rewrite [Nat.sub_zero]
    rewrite [concatSelfNTimes]
    simp [drop]
  | succ k ih =>
    cases index with
    | zero =>
      rewrite [Nat.sub_zero]
      rewrite [concatSelfNTimes]
      simp [drop]
    | succ =>
      rewrite [Nat.add_sub_add_right]
      rewrite [concatSelfNTimes]
      simp [drop]
      rewrite [ih]
      rfl
      simp at h
      exact h

theorem length_splitAt {word : Word} {index : Nat} :
let splits := splitAt word index
length splits.fst + length splits.snd = length word := by
  simp
  induction word with
  | nil =>
    simp [splitAt]
    simp [length]
  | cons =>
    simp [splitAt]
    simp [length_take_drop]

theorem length_addCharAt {word : Word} {char : Character} {index : Nat}
{h : index ≤ length word} : length (addCharAt word char index) = length word + 1 := by
  induction word with
  | nil =>
    rewrite [addCharAt]
    simp [h.not_lt]
    rewrite [length]
    rewrite [length]
    rewrite [length]
    rewrite [add_comm]
    rfl
  | cons =>
    rewrite [addCharAt]
    simp [h.not_lt]
    simp [splitAt]
    rewrite [length_append]
    rewrite [length_concat]
    rewrite [add_right_comm]
    rewrite [length_take_drop]
    rfl
