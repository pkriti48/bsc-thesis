import Game.Levels.TakeAndDrop.L01_TakeAll
import Game.Levels.TakeAndDrop.L02_DropAll
import Game.Levels.TakeAndDrop.L03_TakeAppendLeft
import Game.Levels.TakeAndDrop.L04_DropAppendLeft
import Game.Levels.TakeAndDrop.L05_TakeAppendRight
import Game.Levels.TakeAndDrop.L06_DropAppendRight
import Game.Levels.TakeAndDrop.L07_TakeReplicateChar
import Game.Levels.TakeAndDrop.L08_DropReplicateChar

World "TakeAndDrop"
Title "The Take and Drop World"

Introduction "
Welcome to the second world of this game: **The Take and Drop World**!

Here, you will study the behavior of the functions ```take``` and ```drop``` on words and their
interaction with word appending.

You will start by proving, that taking a number of characters equal to the length of a word
returns the word itself, while dropping the same number of characters results in ```nil```.

Next, you will analyze how ```take``` and ```drop``` behave on appended words, depending on
whether the index stays within the first word or goes beyond it.


"
