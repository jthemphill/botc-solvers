# Puzzle 91 — Mixed Signals

The [archive](https://notquitetangible.blogspot.com/2024/11/clocktower-puzzle-archive.html) listed puzzle 91 as its latest entry on 29 September 2026. The transcription follows the [original image](../puzzle-images/puzzle-91-mixed-signals.png), downloaded from [Reddit's image host](https://i.redd.it/uj2pdylqvhrh1.png). Seating runs clockwise from Sarah.

[Original post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1wp6dy2/weekly_puzzle_91_mixed_signals/) · [Static mirror used](https://safereddit.com/r/BloodOnTheClocktower/comments/1wp6dy2/?limit=500&sort=old) · [Author confirmation](https://www.reddit.com/r/BloodOnTheClocktower/comments/1wp6dy2/comment/pbss82i/) · [Author's Nightwatchman clarification](https://www.reddit.com/r/BloodOnTheClocktower/comments/1wp6dy2/comment/pc08h7m/)

## Observations and assumptions

The document includes all five public deaths. Sarah's Philosopher choice, Sarah's and Charlotte's reported Nightwatchman targets, and Hannah's received signal occur on night 1. Hannah's Juggler result and your Town Crier result arrive on night 2. Josh receives his Sage information when he dies on night 2. Tim asks his Artist question on day 3.

Standard setup supplies eight-player counts, with the normal Fang Gu and Vigormortis Outsider modifiers. Your character is Town Crier. The source allows a living Mutant to claim a Townsfolk character with arbitrary information, but requires a dead Mutant to reveal its character. Accordingly, the three living claimants can be the Mutant; the dead claimants cannot. These restrictions come from the image, not the solution. All other role claims use the shared convention. No custom constraint fixes the evil team.

## Independent check of the answer

The author confirms Tim as Vortox, Fraser as Witch, and Charlotte as Mutant. All other players have their claimed characters. The fixture records only these initial characters.

- Sarah gains the Nightwatchman ability and chooses Hannah. The Vortox makes Hannah learn Charlotte instead of Sarah. Charlotte's own claimed action is a Mutant bluff.
- Tim and Fraser are adjacent. Aoife's distance of 3 is false.
- Only Aoife's character matches Hannah's three guesses, so Hannah's reported 0 is false.
- Fraser is a Minion who nominated, so your Town Crier no is false.
- Neither Charlotte nor Hannah is the Demon, so Josh's Sage information is false.
- Fraser curses himself and dies when he nominates. His Klutz report has no effect. Tim kills Josh and Hannah on the reported nights. Both executions kill good Townsfolk. Sarah, Charlotte, and Tim remain alive, and the game continues.

## Rule support

[Nightwatchman, revision 2827](https://wiki.bloodontheclocktower.com/index.php?title=Nightwatchman&oldid=2827), explicitly gives a Vortox example in which the chosen player learns a different source. [Vortox, revision 3017](https://wiki.bloodontheclocktower.com/index.php?title=Vortox&oldid=3017), changes Townsfolk information. [Philosopher, revision 2421](https://wiki.bloodontheclocktower.com/index.php?title=Philosopher&oldid=2421), grants the chosen ability while preserving the Philosopher's character and makes an existing holder drunk.

The engine now generates optional Nightwatchman choices, limits each player's use to once, and separates the recipient from the player shown. A poisoned or drunk source cannot send a signal; poison on the recipient does not disable the source's ability. A reported signal needs an actual source. Missing reports leave choices unknown. Duplicate reports describe the same action.

Rule tests cover legal and illegal signals, Vortox, Philosopher, poison, omitted choices, repeated uses, duplicate reports, redundant facts, and renaming with seating preserved. A small browser example covers entry, solving, editing, export, import, and removal of these fields.

The [existing engine limits](rules-first-engine.md#coverage-that-still-needs-migration) still apply. Nightwatchman actions use phase-level life state; this does not fully order deaths, poison changes, or ability acquisition within one night. Reacquiring a spent ability after a character change is not supported by the per-player use limit. The fixture verifies the initial assignment against the source; it does not certify every hidden history admitted by the engine.
