import Game.Levels.AppendAndConcat.L01_AppendNil
import Game.Levels.AppendAndConcat.L02_LengthConcat
import Game.Levels.AppendAndConcat.L03_LengthAppend
import Game.Levels.AppendAndConcat.L04_LengthReplicateChar
import Game.Levels.AppendAndConcat.L05_LengthReplicateWord

World "AppendAndConcat"
Title "The Append and Concat World"

Introduction "
In the first world of the game, you will prove some facts about the functions: ```append```,
```concat```, ```replicateChar``` and ```replicateWord```.

You will first prove that appending the empty word ```nil``` to any ```word``` results in
```word```.

Then, you will prove how the length of a word is calculated when two words are connected using
```append``` or a character ```char``` is connected to a word using ```concat```.

Finally, building upon these lemmas, you will show how the length of a word is influenced when
it consists of ```n``` replicas of a character ```char``` or ```n``` replicas of some ```word```.

Let's get started!
"
