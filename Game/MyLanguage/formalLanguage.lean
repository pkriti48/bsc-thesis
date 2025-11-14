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
