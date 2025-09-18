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

def concat (word : Word) (char : Character) : Word :=
  match word with
  | .nil => .cons char .nil
  | .cons head tail => .cons head (concat tail char)

def toString (word : Word) : String :=
  match word with
  | .nil => ""
  | .cons head tail => (Character.toString head) ++ (toString tail)

private def splitAtAux (word_1 : Word) (word_2 : Word) (index : Nat) : (Prod Word Word) :=
  match word_2 with
  | .nil => (word_1, word_2)
  | .cons head tail => if index > 0 then
    splitAtAux (concat word_1 head) tail (index - 1)
    else (word_1, word_2)

def splitAt (word : Word) (index : Nat) : (Prod Word Word) :=
  match word with
  | .nil => (.nil, .nil)
  | _ => (splitAtAux .nil word index)

def addCharAt (word : Word) (char : Character) (index : Nat) : Word :=
  if index > length word then
    word
  else let
    splits := splitAt word index
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

end Word

structure Lang where
  l : Set Word
