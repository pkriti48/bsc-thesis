import Game.Levels.TakeAndDrop.L01_TakeAll
import Game.Levels.TakeAndDrop.L02_DropAll
import Game.Levels.TakeAndDrop.L03_TakeAppendLeft
import Game.Levels.TakeAndDrop.L04_DropAppendLeft
import Game.Levels.TakeAndDrop.L05_TakeAppendRight
import Game.Levels.TakeAndDrop.L06_DropAppendRight
import Game.Levels.TakeAndDrop.L07_TakeReplicateChar
import Game.Levels.TakeAndDrop.L08_DropReplicateChar

World "TakeAndDrop"
Title "Take and Drop"

Introduction "
Welcome to the second world of this game: **The Take and Drop World**!

Here, you will study the behavior of the functions ```take``` and ```drop``` on words and their
interaction with word appending.

The ```take``` function returns a prefix of a given word consisting of the character upto the
specified index, while the ```drop``` function returns a suffix of a given word consisting of the
characters starting at the given index.

You will start by proving, that the function ```take``` returns the word itself when the index
corresponds to the length of the given word. At the same time, with the same value for the index,
the drop function returns the empty word ```nil```.

Following this, you will analyze how ```take``` and ```drop``` behave when combined with the append
function:
- The prefix to be returned of a given word lies in ```word_1``` for ```word_1 ++ word_2```.
- The suffix to be returned of a given word lies in both ```word_1``` and ```word_2``` for ```word_1
++ word_2```.
- The prefix to be returned of a given word lies in both ```word_1``` and ```word_2``` for ```word_1
++ word_2```.
- The suffix to be returned of a given word lies in ```word_2``` for  ```word_1 ++ word_2```.

Lastly, you will analyze how ```take``` and ```drop``` behave when combined with the function
```replicateChar```.

Let's start!
"
