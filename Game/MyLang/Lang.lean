import Mathlib

inductive Character where
  | a
  | b
  | c
  deriving BEq, DecidableEq

def Character.toString (char : Character) : String :=
  match char with
    | a => "a"
    | b => "b"
    | c => "c"

inductive Word where
| nil : Word
| cons  : Character -> Word -> Word

namespace Word

structure Lang where
  l : Set Word

def inWord (char : Character) (word : Word) : Prop :=
  match word with
  | .nil => False
  | .cons head tail => head = char ∨ (inWord char tail)

notation char "∈w" word => inWord char word

def length (word : Word) : Nat :=
  match word with
  | .nil => 0
  | .cons _ tail => 1 + length tail

def append (word_1 : Word) (word_2 : Word) : Word :=
  match word_1 with
  | .nil => word_2
  | .cons head tail => .cons head (append tail word_2)

notation word_1 " ++ " word_2 => append word_1 word_2

def replicateWord (word : Word) (n : Nat) : Word :=
  match n with
  | .zero => .nil
  | .succ k => word ++ (replicateWord word k)

def concat (word : Word) (char : Character) : Word :=
  match word with
  | .nil => .cons char .nil
  | .cons head tail => .cons head (concat tail char)

notation head "::" tail => concat head tail

def replicateChar (char : Character) (n : Nat): Word :=
  match n with
  | .zero => .nil
  | .succ k => Word.cons char (replicateChar char k)

def countCharInWord (char : Character) (word : Word) : Nat :=
  match word with
  | .nil => 0
  | .cons head tail => (if head = char then 1 else 0) + countCharInWord char tail

def take (word : Word) (index : Nat) : Word :=
  if index > 0 then
    match word, index with
    | _, Nat.zero => .nil
    | .nil, succ => .nil
    | .cons head tail, succ => .cons head (take tail (succ - 1))
  else .nil

def drop (word : Word) (index : Nat) : Word :=
  if index > 0 then
    match word, index with
    | .nil, _ => .nil
    | .cons head tail, Nat.zero => word
    | .cons head tail, succ => drop tail (succ - 1)
  else word

def splitAt (word : Word) (index : Nat) : (Prod Word Word) :=
  match word with
  | .nil => (.nil, .nil)
  | _ => (take word index, drop word index)

def addCharAt (word : Word) (char : Character) (index : Nat) : Word :=
  if index > length word then
    word
  else
    let splits := splitAt word index
    match word with
    | .nil => .cons char .nil
    | _ => (splits.fst :: char) ++ splits.snd

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
