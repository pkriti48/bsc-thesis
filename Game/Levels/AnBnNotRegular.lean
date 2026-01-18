import Game.Levels.AnBnNotRegular.L01_CountAEqCountBInLang
import Game.Levels.AnBnNotRegular.L02_CountAInReplicateCharA
import Game.Levels.AnBnNotRegular.L03_CountBInReplicateCharA
import Game.Levels.AnBnNotRegular.L04_TakeReplicateCharAppend
import Game.Levels.AnBnNotRegular.L05_LeftEqReplicateCharA
import Game.Levels.AnBnNotRegular.L06_CountAInU
import Game.Levels.AnBnNotRegular.L07_CountBInU
import Game.Levels.AnBnNotRegular.L08_CountAInV
import Game.Levels.AnBnNotRegular.L09_CountBInV
import Game.Levels.AnBnNotRegular.L10_LengthZEq2n
import Game.Levels.AnBnNotRegular.L11_LengthPumpedWord
import Game.Levels.AnBnNotRegular.L12_WEqRemainingAsNBs
import Game.Levels.AnBnNotRegular.L13_CountAInW
import Game.Levels.AnBnNotRegular.L14_CountBInW
import Game.Levels.AnBnNotRegular.L15_MoreAsThanBs
import Game.Levels.AnBnNotRegular.L16_AnBnNotRegular

World "AnBnNotRegular"
Title "AnBn is Not Regular"

Introduction "Wuhuu! You have finally reached the final world of the game.

So far, you proved many theorem that will now come handy to prove that the language ```$L = {a^n b^n |
n ≥ 0}$``` is not regular.

You will start by proving that the count of ```a```s and ```b```s has to be the same in word if the
word is an element of the language L as defined above.

Then, you will proceed by proving that the number of ```a```s in a replica of ```a```s corresponds to
the word's length and the number of ```b```s in such a word is 0.

Following this, you will prove that applying the ```take``` function to any word ```replicateChar a n
++ replicateChar b n``` with the ```index``` set to ```k``` and ```k ≤ n``` corresponds to ```k```
replicas of the character  ```a```. Using this theorem, you will prove that ```(u ++ v) = replicateChar
a (length (u ++ v))``` and use this fact in the following proofs.

Next, you will prove how many ```a```s and ```b```s each occur in the words ```u``` and ```v``` with
```z = u ++ v ++ w``` and statements regarding the length of any word ```z``` and the pumped word.

Thereafter, you will prove that the word ```w``` consists of ```n - (length (u ++ v))``` ```a```s
and ```n``` ```b```s.

Then almost reaching the end, you will prove that the pumped word consists of more ```a```s than
```b```s and finally, you will show that the language ```$L = {a^n b^n | n ≥ 0}$``` is not regular.
"
