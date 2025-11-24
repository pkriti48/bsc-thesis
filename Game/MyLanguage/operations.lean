import Game.MyLanguage.formalLanguage

namespace Word

def inWord (char : Character) (word : Word) : Prop :=
  match word with
  | .nil => False
  | .cons head tail => head = char ∨ (inWord char tail)

def length (word : Word) : Nat :=
  match word with
  | .nil => 0
  | .cons _ tail => 1 + length tail

def append (word_1 : Word) (word_2 : Word) : Word :=
  match word_1 with
  | .nil => word_2
  | .cons head tail => .cons head (append tail word_2)

def appendSelfNTimes (word : Word) (n : Nat) : Word :=
  match n with
  | .zero => .nil
  | .succ k => append word (appendSelfNTimes word k)

def concat (word : Word) (char : Character) : Word :=
  match word with
  | .nil => .cons char .nil
  | .cons head tail => .cons head (concat tail char)

def concatSelfNTimes (char : Character) (n : Nat): Word :=
  match n with
  | .zero => .nil
  | .succ k => Word.cons char (concatSelfNTimes char k)

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
