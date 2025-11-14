import Game.Levels.DemoWorld

-- Here's what we'll put on the title screen
Title "The Pumping Lemma Game"
Introduction
"
Welcome to the Pumping Lemma Game!

In this game,
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
CaptionLong "In this game, you prove some facts about formal languages and regular languages later on. Finally, you prove some facts about the Pumping Lemma and use them to prove that the language a^nb^n is not regular."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
