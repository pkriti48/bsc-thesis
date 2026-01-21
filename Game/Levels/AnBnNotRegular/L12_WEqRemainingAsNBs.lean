import Game.Levels.AnBnNotRegular.L11_NumberOfAsInPumpedWord

namespace Word

World "AnBnNotRegular"
Level 12
Title "The Suffix w Contains All Remaining as And All bs"

Introduction "In this proof, you will show that decomposing a word $z = a^n b^n$ as  ```z =
(u ++ v) ++ w``` with ```k = length u + length v```, ```k ≤ n``` and ```length u < k```, the
suffix ```w```consists of exactly ```n - k``` replicas of ```a``` followed by ```n``` replicas
of ```b```."

/--
For a word $z = a^n b^n$, which is decomposed as ```z = (u ++ v) ++ w``` with
```k = length u + length v```, ```k ≤ n``` and ```length u < k```, the remaining
suffix ```w```consists of exactly ```n - k``` replicas of ```a``` followed by
```n``` replicas of ```b```.
-/
TheoremDoc Word.w_eq_remaining_as_n_bs as "w_eq_remaining_as_n_bs" in "Word"

Statement w_eq_remaining_as_n_bs (u v w z : Word) (n k : Nat)
(h_z : z = replicateChar Character.a n ++ replicateChar Character.b n)
(z_eq : z = (u ++ v) ++ w) (h_k : k = length (u ++ v))
(length_u_v_leq_n : length (u ++ v) ≤ n) :
w = replicateChar Character.a (n - k) ++ replicateChar Character.b n := by
  Hint "To retrieve an equality between the ```w``` and the term on the right-hand side of the
  ```=``` sign, you could start by introducing an auxiliary theorem, which states how the word
  ```w``` can be retrieved from the word ```z```. After that, the procedure is trivial."
  Hint (hidden := true) "If you do not know, how to retrieve the word ```w``` form the word ```z```,
  you can do that by dropping all the characters occurring before the word ```w```."
  have h_w : w = drop z k := by
    rewrite [z_eq]
    rewrite [drop_append_left]
    rewrite [h_k]
    rewrite [drop_all]
    rewrite [append]
    rfl
    rewrite [h_k]
    rfl
  rewrite [h_w]
  rewrite [h_z]
  rewrite [drop_append_left]
  rewrite [drop_replicateChar]
  rfl
  rewrite [h_k]
  exact length_u_v_leq_n
  rewrite [length_replicateChar]
  rewrite [h_k]
  exact length_u_v_leq_n

Conclusion "Using this theorem, will prove separately how many ```a```s and ```b```s occur in the
suffix ```w``` of ```z```."
