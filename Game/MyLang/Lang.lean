import Mathlib

/--
```Character``` represents a single symbol in a finite alphabet.

This type defines a small, fixed set of characters that can be used to
construct words. Equality on ```Character``` is decidable and computable.
-/
inductive Character where
  /-- The character ```a```. -/
  | a
  /-- The character ```b```. -/
  | b
  /-- The character ```c```. -/
  | c
  deriving BEq, DecidableEq

/--
Convert a ```Character``` to its string representation.

This function maps each ```Character``` constructor to the corresponding
single-character ```String```.
-/
def Character.toString (char : Character) : String :=
  match char with
    | a => "a"
    | b => "b"
    | c => "c"

/--
```Word``` represents a finite sequence of ```Character```s.

It is structurally equivalent to a list of characters, but defined as a
separate type to give semantic meaning to character sequences.
-/
inductive Word where
/--
  The empty word.

  This constructor represents a word containing no characters.
  -/
| nil : Word

/--
  Prepend a ```Character``` to an existing ```Word```.

  ```cons char word``` represents the word whose first character is ```char```,
  followed by the characters of ```word```.
  -/
| cons  : Character -> Word -> Word

namespace Word

/--
```Lang``` represents a formal language over words.

A language is defined as a set of ```Word```s, allowing membership-based
reasoning about which words belong to the language.
-/
structure Lang where
  /-- The underlying set of words defining the language. -/
  l : Set Word

/--
Predicate stating whether a ```Character``` occurs in a ```Word```.

```elemOf char word``` holds if and only if ```char``` appears at least once in ```word```.

```elemOf char word``` can also be written as ```char ∈w word```.
-/
def elemOf (char : Character) (word : Word) : Prop :=
  match word with
  | .nil => False
  | .cons head tail => head = char ∨ (elemOf char tail)

/--
Notation for character membership in a word.
-/
notation char " ∈w " word => elemOf char word


/--
Compute the length of a ```Word```.

Returns the number of characters contained in the word.
-/
def length (word : Word) : Nat :=
  match word with
  | .nil => 0
  | .cons _ tail => 1 + length tail


/--
Append two words.

```append word_1 word_2``` produces a new word consisting of the characters of ```word_1```
followed by the characters of ```word_2```.

```append word_1 word_2``` can also be written as ```word_1 ++ word_2```.
-/
def append (word_1 : Word) (word_2 : Word) : Word :=
  match word_1 with
  | .nil => word_2
  | .cons head tail => .cons head (append tail word_2)

/--
Infix notation for the append function.
-/
notation word_1 " ++ " word_2 => append word_1 word_2


/--
Repeat a word ```n``` times.

```replicateWord word n``` appends ```word``` to itself ```n``` times.
-/
def replicateWord (word : Word) (n : Nat) : Word :=
  match n with
  | .zero => .nil
  | .succ k => word ++ (replicateWord word k)


/--
Concatenate a single ```Character``` to the end of a ```Word```.

```concat word char``` can be written as ```word :: char```.
-/
def concat (word : Word) (char : Character) : Word :=
  match word with
  | .nil => .cons char .nil
  | .cons head tail => .cons head (concat tail char)

/--
Infix notation for the concat function.
-/
notation head " :: " tail => concat head tail


/--
Create a word consisting of ```n``` repetitions of a single ```Character```.
-/
def replicateChar (char : Character) (n : Nat): Word :=
  match n with
  | .zero => .nil
  | .succ k => Word.cons char (replicateChar char k)


/--
Count the number of occurrences of a ```Character``` in a ```Word```.
-/
def countCharInWord (char : Character) (word : Word) : Nat :=
  match word with
  | .nil => 0
  | .cons head tail => (if head = char then 1 else 0) + countCharInWord char tail


/--
Take characters upto ```index``` of a ```Word```.

If ```index``` exceeds the length of the word, the entire word is returned.
-/
def take (word : Word) (index : Nat) : Word :=
  if index > 0 then
    match word, index with
    | _, Nat.zero => .nil
    | .nil, succ => .nil
    | .cons head tail, succ => .cons head (take tail (succ - 1))
  else .nil


/--
Drop the characters upto ```index``` of a ```Word```.

If ```index``` exceeds the length of the word, the empty word is returned.
-/
def drop (word : Word) (index : Nat) : Word :=
  if index > 0 then
    match word, index with
    | .nil, _ => .nil
    | .cons head tail, Nat.zero => word
    | .cons head tail, succ => drop tail (succ - 1)
  else word


/--
Split a ```Word``` at a given index.

Returns a pair ```(word_1, word_2)``` where ```word_1``` contains the characters
upto ```index``` and ```word_2``` contains the remaining characters.
-/
def splitAt (word : Word) (index : Nat) : (Prod Word Word) :=
  match word with
  | .nil => (.nil, .nil)
  | _ => (take word index, drop word index)


/--
Insert a ```Character``` into a ```Word``` at a given ```index```.

If the index exceeds the length of the word, the original word is returned.
-/
def addCharAt (word : Word) (char : Character) (index : Nat) : Word :=
  if index > length word then
    word
  else
    let splits := splitAt word index
    match word with
    | .nil => .cons char .nil
    | _ => (splits.fst :: char) ++ splits.snd


/--
Remove the character at a given ```index``` from a ```Word```.

If the index exceeds the length of the word, the original word is returned.
-/
def removeCharAt (word : Word) (index : Nat) : Word :=
  if index > length word then
    word
  else
    match word with
    | .nil => word
    | .cons head tail => if index > 0 then
      .cons head (removeCharAt tail (index - 1))
      else tail

/--
The pumping property for a language.

A language ```lang``` satisfies the pumping property if there exists a positive
integer ```n``` such that every word ```z``` in ```lang``` with length at least
```n``` can be written as ```z = u ++ v ++ w``` and fulfills the following:
1. The length of ```u ++ v``` is at most ```n```
2. The word ```v```` is non-empty
3. For any natural number ```i```, repeating ```v ``` ```i``` times within ```z```
results in a word that is still in the language: ```u ++ replicateWord v i ++ w ∈ lang.l```
-/
def pumpingProperty (lang : Lang) :=
  ∃ (n : Nat) (H : n > 0),
  ∀ z : Word, z ∈ lang.l ∧ length z ≥ n →
  ∃ u v w : Word, z = ((u ++ v) ++ w) ∧
  length (u ++ v) ≤ n ∧
  length v ≥ 1 ∧
  ∀ (i : Nat), ((u ++ (replicateWord v i)) ++ w) ∈ lang.l

/--
Convert a ```Word``` to its string representation.

Characters are converted using ```Character.toString``` and concatenated
in order.
-/
def toString (word : Word) : String :=
  match word with
  | .nil => ""
  | .cons head tail => (Character.toString head) ++ (toString tail)
