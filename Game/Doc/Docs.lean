import GameServer.Commands
import Mathlib.Tactic

TacticDoc rewrite

/--
  TacticDoc rfl
  "
  ## Summary

  `rfl` proves goals of the form `X = X`.

  ## Details

  The `rfl` tactic closes goals of the form `A = B` where `A` and `B` have *exactly the same value*.

  ### Example

  If the current state of the proof looks as follows:
  ```
  Objects: a b c : ℕ
  Goal: a + (b + c) = a + (b + c)
  ```
  then `rfl` closes the goal.
  "

  `rfl` also closes the goal of the form `A = B` when `A` and `B` are not *exactly identical*
  but merely *definitionally equal*, e.g. ```a + 0 = a```.

-/
TacticDoc rfl

-- TacticDoc induction
TacticDoc induction
