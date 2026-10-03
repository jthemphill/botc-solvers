# Puzzle 92 — Half Moon Rising

Transcribed from the [original image](../puzzle-images/puzzle-92-half-moon-rising.png), hosted at [Reddit](https://i.redd.it/8patvocsa1th1.png). Seating runs clockwise from Fraser.

[Original post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1wvqozt/weekly_puzzle_92_half_moon_rising/) · [Static mirror](https://safereddit.com/r/BloodOnTheClocktower/comments/1wvqozt/?limit=500&sort=old) · [Author confirmation](https://www.reddit.com/r/BloodOnTheClocktower/comments/1wvqozt/comment/pde1621/)

## Observations and puzzle assumptions

The document records both executions, the explicitly empty night 2 death report, and all three night 3 deaths. Aoife's two Chambermaid checks occur on nights 1 and 2. Matthew's Seamstress report has no explicit night in the image; the document places it on night 1. No alignment changes are possible on this script, so that placement does not change its content.

Standard eight-player setup supplies one Demon, one Minion, and one Outsider. The Drunk is the only Outsider on the script. Your possible characters are Pacifist and Drunk. Other claims use the shared honesty convention. No constraint fixes the evil team.

The source explicitly forbids killing already-dead players. `noKillSinking: true` records this puzzle assumption; it is not an official game rule. It excludes both previous-night corpses and players killed earlier that night from non-death Demon targets. Protected living players remain valid targets. Existing Gossip and Assassin death-source constraints already require distinct observed victims when they produce deaths.

## Independent solution

The author confirms Matthew as Zombuul, Charlotte as Assassin, and Olivia as Drunk. Everyone else has their claimed character. The fixture records these initial characters, independently of the solver's hidden choices.

A legal witness explains the death pattern: Fraser's execution prevents a Zombuul attack on night 2, and Sarah's first Gossip statement is false. Your Pacifist ability saves Aoife on day 2. On night 3, Matthew attacks himself and registers as dead, Charlotte kills Josh, and Sarah's true Gossip statement kills Aoife. Four players remain publicly alive, and the game continues.

Fraser has an evil neighbor on either side, so clockwise is valid. Aoife sees no wakes from Pacifist or Gambler on night 1, then sees the Assassin wake on night 2. Josh chooses neither Demon on either night. Olivia's wrong gamble causes no death because she is the Drunk. Matthew and Charlotte supply false information.

Po alternatives fail the combined information and death constraints. In particular, an exorcised Po does not choose nobody and therefore does not acquire a charge. A charge earned on an earlier night survives Exorcism.

## Rule checks and support limits

The Po transition follows [Po, revision 3104](https://wiki.bloodontheclocktower.com/index.php?title=Po&oldid=3104). The apparent death follows [Zombuul](https://wiki.bloodontheclocktower.com/Zombuul). Tests cover legal corpse targeting under normal rules, the puzzle's prohibition, earlier-night deaths, protected targets, Exorcist blocking and charge preservation, duplicate reports, redundant facts, and renaming with seating preserved. A small browser scenario covers the assumption control, solving, export, and import.

The [existing engine limits](rules-first-engine.md#coverage-that-still-needs-migration) still apply. Po choices are tracked across explicit night-death reports; omitted reports and drunk/poisoned choice histories are not fully modeled. Gossip and Assassin targeting remain death-source approximations outside this puzzle's no-sinking convention. Exact duplicate claim documents are collapsed; different reports of the same action are not fully canonicalized. This result verifies the initial assignment against the published answer and a legal witness, not every hidden history admitted by the engine.
