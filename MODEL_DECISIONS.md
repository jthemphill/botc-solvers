# Model Decisions

## Puzzle 5a: You Only Guess Twice

- Added `Alsaahir` as a role class with Townsfolk metadata only. The Alsaahir ability is not modeled as a normal information claim because puzzle 5a asks for a public guess after solving the current worlds, not for a constraint that changes the pre-guess world set.
- Represented the Alsaahir guess as puzzle-specific post-processing in `possibleAlsaahirGuesses`. This keeps the core SAT model focused on legal worlds and lets the puzzle describe the decision policy: guess one candidate evil team; if the guess is wrong, the only remaining candidate is the answer.
- Modeled "no Outsiders in play" by including `Drunk` in the script with count `0`. This preserves the existing claim helper behavior for Townsfolk, which allows a claimed Townsfolk token to be an actual Drunk when the script permits it.

## Puzzle 5b: You Only Guess Twice

- Kept the Juggler's unused ability out of the SAT model for the same reason as Alsaahir: the legal worlds are determined before the public action, and the action is a decision tree over those worlds.
- Added `possibleJuggles` as puzzle-specific post-processing. It searches three public Juggler guesses and keeps plans where each possible count maps to exactly one demon/minion assignment.

## Puzzle 6: Super Marionette Bros

- Added `Pukka`, `No Dashii`, and `Vortox` as Demon role classes with metadata only. Their puzzle-specific mechanical effects are still encoded in the puzzle file because the existing role classes model information claims, not full night/action timing.
- Added `BOTCModel.allowPoisonInContext` so a puzzle can define its own poison source constraints without the model's default sober fallback forcing that context to false.
- Modeled Vortox as false information only for an actual, sober/healthy Townsfolk claim. Drunk, poisoned, Demon, and Marionette cases remain unconstrained because their shown information may be arbitrary.
- Modeled the Marionette as neighboring the Demon, but did not make Marionette information true. If the Marionette saw a Townsfolk token, that explains the role report but does not constrain the factual content of the information.
- Used the death record as a demon constraint: Fraser and Steph cannot be the Demon, and if the Demon is Pukka then Steph was the night-one poisoned player who died on night two.

## Puzzle 7: The Savant Strikes Back

- Added `Mutant`, `Shugenja`, and `Village Idiot` role classes. `Mutant` is metadata only; `Shugenja` and `Village Idiot` include their information predicates.
- Extended `addRoleClaim` with `extraPossibleActualRoles` so puzzle-specific madness cases can allow a non-Drunk good role to claim a Townsfolk token while keeping its information unconstrained.
- Disabled global role uniqueness only for puzzle 7, then re-applied at-most-one constraints to every role except `Village Idiot`. This models the Village Idiot setup without weakening uniqueness for the rest of the script.
- Modeled Fortune Teller red herring and the drunk extra Village Idiot locally in the puzzle file. They are setup state for this puzzle's statements, not general player roles.

## Puzzle 8: The Stitch-Up

- Reused the duplicate-role pattern for the Bootlegger rule "Every Townsfolk is a Seamstress": puzzle 8 disables global uniqueness and uses a script containing only `Seamstress` for Townsfolk.
- Used the existing `addPoisonerEffect` for night-one poisoning. The puzzle resolves the evil team, but not which evil player is the Imp versus the Poisoner.

## Puzzle 9: The New Acrobat

- Added `Po`, `Acrobat`, `Gambler`, and `Gossip` role classes with metadata only. Their death-trigger behavior is encoded in puzzle 9 because it depends on the public death timeline.
- Modeled the new Acrobat as a Townsfolk whose choices constrain Drunk status only when You are actually the Acrobat. If You is the Drunk, the claimed Acrobat ability is not trusted.
- Kept the SAT role assignment as the starting role assignment and added puzzle-local event constraints for night three: the Imp self-kills/starpasses, You dies from choosing the Drunk with Acrobat, and Oscar's true day-two Gossip statement accounts for the remaining death.
- Modeled the Po timing correction explicitly: if a Po is responsible for three night-three deaths, it must have charged on night two, so the night-two death would need to be Oscar's true day-one Gossip statement that Fraser was the Demon. This eliminates the static Po worlds.
- Puzzle 9 now resolves as Anna starting as the Imp and Hannah starting as the Goblin; Anna starpasses to Hannah on night three.

## Puzzle 10: Don't Overcook It

- Added `Ravenkeeper` as a Townsfolk role class with metadata only; the death-triggered information is encoded directly in puzzle 10 because it refers to Matthew's specific death.
- Reused Poisoner contexts to separate night-one setup information from night-two/day-two information after Josh was executed. If Josh is the Poisoner, night-two poisoning is inactive.
- Modeled Fortune Teller red herring locally again. The red herring is setup state tied to a Fortune Teller being in play, not a role assignment.
