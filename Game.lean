import Game.Levels.AppendAndConcat

-- Here's what we'll put on the title screen
Title "The Pumping Lemma Game"
Introduction
"
Welcome to the Pumping Lemma Game!

In this game, we build a definition of a language in terms of formal languages. For this language,
we prove various facts about appending two words or concating a character to a word, etc.
These lemmas are then used to build the Pumping Lemma for regular languages.
Finally, this Pumping Lemma is applied to some languages to show that those languages are not regular.

This game should help you to dig deep into the definition of the Pumping Lemma. It should help you
to understand the Pumping Lemma better by deriving several facts you might not think of when writing
the proof on paper.

Good luck and enjoy learning about the Pumping Lemma!
"

Info "
*Game Version: 1.0*

## Progress saving

The game stores your progress in your local browser storage.
If you delete it, your progress will be lost!

Warning: In most browsers, deleting cookies will also clear the local storage
(or \"local site data\"). Make sure to download your game progress first!
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "A playful way to learn about the Pumping Lemma"
CaptionLong "In this game, you prove some facts about the Language structure specifically defined
for this game and later on other facts about the Pumping Lemma. Finally, you use these lemmas to
prove that the provided examples fo languages are not regular languages."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
