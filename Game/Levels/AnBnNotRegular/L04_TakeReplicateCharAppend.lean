import Game.Levels.AnBnNotRegular.L03_CountBInReplicateCharA

namespace Word

World "AnBnNotRegular"
Level 4
Title "The First k Characters of a Word z Are All a"

Introduction "In the following, you will show that for two characters ```a``` and ```b``` and two
natural numbers ```n``` and ```k```, if ```k ≤ n``` and a word consists of ```n``` replicas of
```a``` followed by ```n``` replicas of ```b```, then taking ```k``` characters from that word
results in ```k``` replicas of ```a```."

/--
For two characters ```a``` and ```b``` and two natural number ```n``` and ```k```
with ```k ≤ n```, if a word consists of ```n``` replicas of ```b``` appended to
```n``` replicas of ```a```, then taking ```k``` characters from that word results
in ```k``` replicas of ```a```.
-/
TheoremDoc Word.take_replicateChar_append as "take_replicateChar_append" in "AnBnNotRegular"

Statement take_replicateChar_append (n k : Nat) (k_leq_n : k ≤ n) :
take (replicateChar Character.a n ++ replicateChar Character.b n) k = replicateChar Character.a k := by
  rewrite [take_append_left]
  rewrite [take_replicateChar (h := k_leq_n)]
  rfl
  rewrite [length_replicateChar]
  exact k_leq_n

Conclusion "Very good! You just proved that the first ```k``` characters of the word, formed by
replicating ```a``` ```n``` times followed by ```n``` replicas of ```b```, are all ```a```s if
```k``` is less than ```n```."

