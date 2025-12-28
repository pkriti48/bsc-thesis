import Game.Levels.AppendAndConcat.L01_AppendNil
import Game.Levels.AppendAndConcat.L02_LengthConcat
import Game.Levels.AppendAndConcat.L03_LengthAppend
import Game.Levels.AppendAndConcat.L04_LengthReplicateChar
import Game.Levels.AppendAndConcat.L05_LengthReplicateWord
import Game.Levels.AppendAndConcat.L06_AppendReplicateChar

World "AppendAndConcat"
Title "The Append and Concat World"

Introduction "
Welcome to **The Append and Concat World**!

In this world, you will investigate properties of the functions ```append```, ```concat```,
```replicateChar```, and ```replicateWord```.

The first objective is to establish that appending the empty word ```nil``` to any word leaves
the word unchanged.

Next, you will analyze how the length of a word behaves under ```append``` and ```concat```,
formally proving the effect of combining words or adding a character to a word.

Finally, building upon these lemmas, you will prove the lengths of words formed by ```n```
repetitions of a character or ```n``` repetitions of a word, thereby formalizing the behavior
of repeated character or word constructions.

Let's get started!
"
