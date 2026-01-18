import Game.Levels.AppendAndConcat.L01_AppendNil

namespace Word

World "AppendAndConcat"
Level 2
Title "Prepending a Character Increases Word Length by One"

Introduction "In this level, you will prove that concatenating a character ```char``` to the
end of a ```word``` increases its length by one.

Specifically, the length of word :: char is equal to the length of word plus one.
"

/--
The length of a word after concatenating a character is the length of the word plus one.

For any ```word``` and character ```char```, ```length (concat word char) = length word + 1```.
This reflects the fact that concatenating a character to a word increases its length by one.
-/
TheoremDoc Word.length_concat as "length_concat" in "Word"

/--
Addition is associative.

For all natural numbers ```n```, ```m```, and ```k```, we have
```(n + m) + k = n + (m + k)```.
-/
TheoremDoc Nat.add_assoc as "Nat.add_assoc" in "Nat"

/--
Addition is commutative.

For all natural numbers ```n``` and ```m```, we have ```n + m = n + m```.
-/
TheoremDoc Nat.add_comm as "Nat.add_comm" in "Nat"

Statement length_concat (word : Word) (char : Character) : length (word :: char) = length word + 1 := by
  Hint (hidden := true) "Similar to the previous level, you should start with  induction on ```word```."
  induction word with
  | nil =>
    Hint "The term ```nil :: char``` in your current proof goal corresponds to concatenating a given
    character to the empty word ```nil```, this is a notation for writing ```concat nil char``` in
    user friendly way. So, you can simplify this expression by executing ```rewrite [concat]```."
    rewrite [concat]
    Hint "Basically you can memorize, that you start simplifying your expression from the most inner
    term as you can see here. You simplified the concatenation first and now you are gonna simplify
    the terms containing the ```length``` function. For that, you can simplify your current proof
    goal by rewriting the ```length``` function."
    Branch
      rewrite [length]
      rewrite [length]
      rewrite [length]
      Hint "You can also solve this step by using the ```repeat``` tactic. In your case,
      ```rewrite [length]``` is executed as often as it finds occurrences of the ```length```
      function, if you write: ```repeat rewrite [length]```. Generally, ```repeat``` executes the
      tactic it is given as often as it is possible for the given term."
    repeat rewrite [length]
    Hint "Now, you see very similar terms on both sides of the ```=``` sign but they are not equal
    yet. That means, you can not use the ```rfl``` tactic yet. To use the tactic, the expression
    has to have the form ```1 + 0 = 1 + 0```. Since you have an addition on both sides of the
    ```=``` sign, you can use the commutative property of the mathematical addition and proceed
    accordingly."
    Branch
      Branch
        apply Nat.add_comm
      rewrite [Nat.add_comm]
      rfl
    Hint "You can also use the ```simp``` tactic at this point."
    simp
  | cons head tail ih =>
    Hint "Now, you can simplify your current proof goal by rewriting the concatenation of a ```char```
    to a non-empty word."
    rewrite [concat]
    Hint "At this point, you have to simplify your current proof goal as much as you can by
    rewriting using the ```length``` function."
    repeat rewrite [length]
    rewrite [ih]
    Hint "Using the mathematical property of associativity, you can simplify the current expression
    and reach the equality between the expressions on both sides of the ```=``` sign."
    rewrite [Nat.add_assoc]
    rfl

Conclusion "Well done! You just demonstrated that extending a word by one character results in
a word whose length is precisely one greater than before. Let's move on to the next proof!"

NewTactic apply «repeat»
NewTheorem Nat.add_assoc Nat.add_comm
NewDefinition Word.concat Word.length
