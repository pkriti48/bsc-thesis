import Game.Levels.AppendAndConcat.L01_AppendNil
import Game.Levels.AppendAndConcat.L02_LengthConcat
import Game.Levels.AppendAndConcat.L03_LengthAppend
import Game.Levels.AppendAndConcat.L04_LengthReplicateChar
import Game.Levels.AppendAndConcat.L05_LengthReplicateWord

World "AppendAndConcat"
Title "The Append and Concat World"

Introduction "
In the first world of the game, you will start by proving that appending the empty word ```nil```
to any ```word``` results in ```word```.

Then, you will prove how the length of a word is calculated when two words are connected using
```append``` or a character ```char``` is connected to a word using ```concat```.

Finally, building upon these lemmas, you will prove how the length of a word looks like when this
word corresponds to ```n``` replicas of a character ```char``` or ```n``` replicas of a word
```word```.

Let's get started!
"
