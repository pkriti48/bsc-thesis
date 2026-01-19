import Game.Levels.AnBnNotRegular.L10_LengthZEq2n

namespace Word

World "AnBnNotRegular"
Level 11
Title "Length of Pumped Word (i = 2) is (n + length v)"

Introduction "In this proof, you will show that after pumping the word $z = a^n b^n$, which is
decomposed as ```z = (u ++ v) ++ w```, using ```i = 2``` the number of ```a```s increases in
the word. To be specific, it increases by the factor equal to the length of the middle word
```v```. That means, the pumped word finally contains ```n + length v``` ```a```s."

/--
Pumping a word $z = a^n b^n$ using ```i = 2```, which is decomposed as
```z = (u ++ v) ++ w```, with ```k = length u + length v``` and ```k ≤ n```,
increases the number of ```a```s occurring in the word by the factor
```length v```. So, the final length of the prefix consisting of ```a```s
is ```n + length v```.
-/
TheoremDoc Word.length_pumped_word as "length_pumped_word" in "Word"

/--
Left-cancellation for addition.

For natural numbers ```m```, ```n```, and ```k```, adding the same
number ```m``` to both sides of an equality results in an equivalent
statement: ```m + n = m + k``` if and only if ```n = k```.
-/
TheoremDoc Nat.add_left_cancel_iff as "Nat.add_left_cancel_iff" in "Nat"

/--
States ommutativity on the left operands for addition on natural numbers.

For natural numbers ```m```, ```n```, and ```k```, it asserts that:
m + (n + k) = n + (m + k)
-/
TheoremDoc Nat.add_left_comm as "Nat.add_left_comm" in "Nat"

/--
States an associativity property involving addition and subtraction
for natural numbers.

For natural numbers ```m```, ```n```, and ```k``` with ```n ≤ m```, it
states that: m - n + k = m + k - n
-/
TheoremDoc Nat.add_sub_assoc as "Nat.add_sub_assoc" in "Nat"

/--
Adding a natural number and then subtracting the same number results in
the original number.

For natural numbers ```m``` and ```n``` with ```n ≤ m```, it asserts:
```(m + n) - n = m```
-/
TheoremDoc Nat.add_sub_cancel as "Nat.add_sub_cancel" in "Nat"

/--
Adding a natural number and then substracting the same number results in
the original number.

For natural number ```m``` and ```n``` with ```n ≤ m```, it asserts:
```(n + m) - n = m```
-/
TheoremDoc Nat.add_sub_cancel_left as "Nat.add_sub_cancel_left" in "Nat"

/--
Any natural number is less than or equal to itself plus another natural number.

For natural numbers ```m``` and ```n```, it asserts: ```m ≤ m + n```
-/
TheoremDoc Nat.le_add_right as "Nat.le_add_right" in "Nat"

Statement length_pumped_word (u v w z : Word) (n k : Nat)
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
  rewrite [Nat.two_mul]
  rewrite [Nat.add_sub_cancel]
  rfl
  rewrite [h_z]
  rewrite [length_append]
  repeat rewrite [length_replicateChar]
  apply Nat.le_add_right n n
  have length_w : length w = length z - k := by
    rewrite [z_eq]
    rewrite [h_k]
    repeat rewrite [length_append]
    rewrite [Nat.add_sub_cancel_left]
    rfl
  rewrite [length_w]
  rewrite [h_z]
  simp [length_z_eq_2n]
  rewrite [Nat.two_mul]
  rewrite [Nat.add_sub_assoc]
  apply Nat.le_add_right
  exact k_leq_n

Conclusion "Very good! You will use this theorem later on to show that the pumped word contains more
```a```s than the non pumped word ```z```."

NewTheorem Nat.add_left_cancel_iff Nat.add_left_comm Nat.add_sub_assoc Nat.add_sub_cancel Nat.add_sub_cancel_left Nat.le_add_right
