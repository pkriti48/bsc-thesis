import Game.Levels.AppendAndConcat.L01_AppendNil
import Game.Levels.AppendAndConcat.L02_LengthConcat
import Game.Levels.AppendAndConcat.L03_LengthAppend
import Game.Levels.AppendAndConcat.L04_LengthReplicateChar
import Game.Levels.AppendAndConcat.L05_LengthReplicateWord
import Game.Levels.AppendAndConcat.L06_AppendReplicateChar

World "AppendAndConcat"
Title "Append and Concat"

Introduction "
Welcome to **The Append and Concat World**!

In this world, you will investigate the properties of the functions ```append```, ```concat```,
```replicateChar```, and ```replicateWord```:
- The function ```append``` takes two words and produces a new word consisting of the characters
of the first word followed by the characters of the second word.
- ```concat``` adds a single character to the end of a word.
- ```replicateChar``` produces a new word by replicating a given character ```n``` times.
- ```replicateWord``` produces a new word by appending a given word to itself ```n``` times

The first objective of this world is to establish that appending the empty word ```nil```
to any word leaves that word unchanged.

Next, you will analyze how the length of a word behaves under ```append``` and ```concat```.

Finally, building upon these lemmas, you will prove the lengths of words formed using the functions
```replicateChar``` and ```replicateWord```.

Let's get started!
"
