import Mathlib

inductive Character where
  | a
  | b
  | c

def Character.toString (char : Character) : String :=
  match char with
    | a => "a"
    | b => "b"
    | c => "c"

namespace Word

inductive Word where
| nil : Word
| cons  : Character -> Word -> Word

def length (word : Word) : Nat :=
  match word with
  | .nil => 0
  | .cons _ tail => 1 + length tail

def append (word_1 : Word) (word_2 : Word) : Word :=
  match word_1 with
  | .nil => word_2
  | .cons head tail => .cons head (append tail word_2)

theorem length_append {word_1 : Word} {word_2 : Word } :
length (append word_1 word_2) = length word_1 + length word_2 := by
  induction word_1 with
  | nil => simp [append, length]
  | cons =>
    simp [append, length, a_ih]
    rewrite [<- add_assoc]
    rfl

theorem append_nil {word : Word} : append word .nil = word := by
  induction word with
  | nil => rfl
  | cons =>
    simp [append]
    exact a_ih

theorem append_assoc {word_1 word_2 word_3 : Word} :
append (append word_1 word_2) word_3 = append word_1 (append word_2 word_3) := by
  induction word_1 with
  | nil => simp [append]
  | cons =>
    simp [append]
    exact a_ih

def concat (word : Word) (char : Character) : Word :=
  match word with
  | .nil => .cons char .nil
  | .cons head tail => .cons head (concat tail char)

theorem length_concat {word : Word} {char : Character} :
length (concat word char) = (length word) + 1 := by
  induction word with
  | nil => simp [concat, length]
  | cons =>
    simp [concat, length, a_ih]
    rewrite [add_assoc]
    rfl

theorem concat_eq_append_one_char {word : Word} {char : Character} :
concat word char = append word (.cons char .nil) := by
  induction word with
  | nil => simp [concat, append]
  | cons =>
    simp [concat, append]
    exact a_ih

def take (word : Word) (index : Nat) : Word :=
  if index > 0 then
    match word, index with
    | _, Nat.zero => .nil
    | .nil, succ => .nil
    | .cons head tail, succ => .cons head (take (tail) (index - 1))
  else .nil

def drop (word : Word) (index : Nat) : Word :=
  if index > 0 then
    match word, index with
    | .nil, _ => .nil
    | .cons head tail, Nat.zero => word
    | .cons head tail, succ => drop tail (index - 1)
  else word

theorem length_take_drop_eq_length_word {word : Word} {index : Nat} :
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


theorem append_take_drop_eq_word {word : Word} {index : Nat} :
append (take word index) (drop word index) = word := by
  induction word generalizing index with
  | nil =>
    simp [drop]
    rewrite [append_nil]
    cases index with
    | zero => simp [take]
    | succ => simp [take]
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

theorem length_append_take_drop_eq_word {word : Word} {index : Nat} :
length (append (take word index) (drop word index)) = length word := by
  rewrite [append_take_drop_eq_word]
  rfl

def splitAt (word : Word) (index : Nat) : (Prod Word Word) :=
  match word with
  | .nil => (.nil, .nil)
  | _ => (take word index, drop word index)

theorem length_splitAt_eq_length_word {word : Word} {index : Nat} : let splits := splitAt word index
  length splits.fst + length splits.snd = length word := by
  simp
  induction word with
  | nil =>
    simp [splitAt]
    simp [length]
  | cons =>
    simp [splitAt]
    simp [length_take_drop_eq_length_word]

def addCharAt (word : Word) (char : Character) (index : Nat) : Word :=
  if index > length word then
    word
  else
    let splits := splitAt word index
    match word with
    | .nil => .cons char .nil
    | _ => append (concat splits.fst char) splits.snd

def removeCharAt (word : Word) (index : Nat) : Word :=
  if index > length word then
    word
  else
    match word with
    | .nil => word
    | .cons head tail => if index > 0 then
      .cons head (removeCharAt tail (index - 1))
      else tail

def toString (word : Word) : String :=
  match word with
  | .nil => ""
  | .cons head tail => (Character.toString head) ++ (toString tail)

end Word

structure Lang where
  l : Set Word
