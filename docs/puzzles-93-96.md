# Puzzles 93, 95, and 96

The [puzzle archive](https://notquitetangible.blogspot.com/2024/11/clocktower-puzzle-archive.html) listed these three puzzles after puzzle 92 on 14 November 2026. Puzzle 94 is Clockdoku II and is not in the catalog. The images in `puzzle-images/` are the user-supplied originals. Seating runs clockwise from the top of each image.

The session could not reach Reddit or the official wiki. No author-confirmed solution was retrieved. Each fixture below comes from a hand derivation from the image and the rules, done separately from the solver. The solver then enumerated the same single assignment for each puzzle.

## 93 — A Study in Idiocy

[Post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1x0lotq) · [Image](../puzzle-images/puzzle-93-a-study-in-idiocy.webp)

Tim is the Imp, Aoife is the Xaan, and Hannah is the Mutant. Everyone else has their claimed character.

The document records the six deaths and all reports. The image lets a living Mutant claim a Townsfolk character, and makes a dead Mutant reveal itself. The shared claim convention now has this rule, so no claim lists possible characters for it. Hannah is the only living Townsfolk claimant, so only Hannah can be the Mutant. Your character is Village Idiot, as a given. No custom constraint is used.

Derivation:

- Hannah reports Sarah as the Spy on night 4. No script has four Outsiders, so night 4 is never the Xaan night. A truthful Hannah puts a Spy game on the table with Sarah as the Spy. That game needs Jasmine or Olivia as the Imp, and both die at night with no living Minion to continue the game. Hannah is therefore the Mutant or evil. Hannah as the Imp fails on the Village Idiot, Chambermaid, and Town Crier reports, so Hannah is the Mutant.
- A Spy game with Hannah as the Mutant needs two drunk Village Idiots. The Minion is the Xaan.
- The final Imp is Tim or Fraser. Both cannot be evil, because Aoife and Sarah would both need to be drunk on night 2. There are two Outsiders, so the Xaan poisons on night 2.
- Charlotte reports that neither Aoife nor Tim woke on night 1. If Charlotte is a good Chambermaid, both are evil: Tim is the Imp and Aoife is the Xaan. You are the drunk Village Idiot. Sarah's "Tim is good" comes on the poisoned night.
- If Charlotte is the Xaan, the Imp kills her on night 2. The Xaan poison stops when the Xaan dies, and the Demon acts before the Village Idiot. Aoife's night-2 "Jasmine is evil" is then false without poison, so Aoife and You would both be drunk. The same reasoning rejects a night-2 Imp starpass to the Xaan.

### Rule change

The engine kept the Xaan poison for the full night when the Demon killed the Xaan on night X. It returned three assignments for this puzzle. The Xaan activity now uses the same before-information death timing as the Poisoner. [Xaan, revision 3082](https://wiki.bloodontheclocktower.com/index.php?title=Xaan&oldid=3082), is the revision already cited by this repository; it was not fetched again in this session.

`src/builders/xaan.test.ts` covers a living Xaan, a Xaan killed on night X, a starpass on night X, renamed players with seating preserved, a duplicate death report, and redundant facts. These tests were written before the puzzle fixture and fail on the previous engine.

## 95 — Daylight Saving Time

[Post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1xexnjq/) · [Image](../puzzle-images/puzzle-95-daylight-saving-time.webp)

Sarah is the No Dashii and Tim is the Evil Twin. Everyone else has their claimed character.

Jasmine, Oscar, Tim, and Sarah are alive at the end. By the shared claim convention, each of them can be evil or the Mutant; this includes a Mutant that became the Fang Gu. No custom constraint is used. The image also lets a Sweetheart that became the Fang Gu hide its past. The document does not model that case, because it cannot occur: Charlotte's Sweetheart claim would then be false, and Charlotte can be neither the Demon, whose execution ends the game, nor the Evil Twin, who is Jasmine or Tim. Aoife's guesses are scored on night 2. Oscar asks his question on day 3.

Check of the assignment:

- Jasmine and Fraser are the nearest Townsfolk to Sarah, so both are poisoned. Jasmine's distance of 1 is false; the true distance from Sarah to Tim is 2. Fraser's two Mathematician numbers are not reliable.
- Tim is evil and Aoife is good, so your Seamstress result is true.
- None of Aoife's three guesses is correct.
- Charlotte is the Sweetheart. After her execution, Oscar is drunk, which explains the "No" to "Am I the Artist?".
- Sarah's two Town Crier reports are bluffs.
- Sarah kills You and Aoife. Neither twin is executed, and four players remain alive.

No engine change was needed.

## 96 — Goon with the Wind

[Post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1xvchi4/) · [Image](../puzzle-images/puzzle-96-goon-with-the-wind.webp)

Hannah is the Imp, Anna is the Poisoner, and Matthew is the Goon. Everyone else has their claimed character.

The image ties honesty to the alignment on day 4, which is the last phase of the timeline. The shared claim convention covers this: a Goon that claims another character is evil at the last phase. Hannah's Goon claim reports her alignment on each of the four nights. No custom constraint is used. The empty night-2 death report is explicit.

Check of the assignment:

- Anna poisons Dan on night 1, so the Chef's 0 is false. Hannah and Anna are neighbors.
- Sula's distance of 1, Oscar's Investigator result, your "Dan is good", and Tim's Artist answer are all true.
- Anna poisons You on nights 2 and 3. Your "Oscar is evil" and "Hannah is good" are false.
- On night 2, Hannah chooses Matthew. Hannah is the first to choose the Goon, so she is drunk and nobody dies. Matthew becomes evil and stays evil, so he may lie on day 4.
- Hannah kills Oscar and You. Matthew, Tim, and Hannah remain alive.

A second candidate has Matthew as the Imp, Anna as the Poisoner, and Hannah as an evil Goon. It needs a poisoned Village Idiot to choose the Goon on night 3 without changing her alignment. The engine treats a choice by a poisoned or drunk player as a choice, so Hannah becomes good and must then report truthfully. This reading gives the puzzle its single answer. The wiki ruling for this interaction was not retrieved.

### Player choices

A choice action is the one abstraction for a choice: an actor, a night, a list of candidates, a truth value for each candidate, and the least and greatest number of selections. An action with an `ability` is a choice of players that the actor makes at night with that character's ability. Witnesses show these actions, and the witness checker validates their counts.

- `src/model/nightOrder.ts` holds the night order of each character that chooses players or causes deaths at night.
- Each character registers its own choice actions. `src/builders/goon.ts` reads the actions that have an ability after the last one is registered; no character has Goon-specific registration.
- A character class can declare a night choice rule: the number of players, the nights, and a one-use limit. `src/builders/playerChoices.ts` makes the choice actions for each such character. A reported choice fixes the targets of its night. A night without a report has an unknown choice.

The Sailor, Innkeeper, Gambler, Acrobat, Snake Charmer, Monk, Exorcist, Professor, Ravenkeeper, Fortune Teller, Dreamer, Seamstress, Village Idiot, Butler, Chambermaid, and Witch use a night choice rule. The Poisoner, Widow, Pukka, Devil's Advocate, Godfather, Shabaloth, Assassin, Nightwatchman, Cerenovus, Pit-Hag, Lleech, and Barber have choice actions over the variables that they already had. The other Demons have one action for each night: a kill selects the victim, and a drunk or poisoned Demon selects a player with no effect.

Rule changes that result:

- The first player to choose the Goon is drunk, whatever character made the choice. A Poisoner or Widow that is drunk this way poisons nobody.
- A Demon can choose the Goon first. The Demon is then drunk and kills nobody that night, and the Goon becomes evil. The previous Demon-specific rule for a kill of the Goon is removed; it now follows from the Demon action.
- The Widow selection no longer depends on the Widow being sober, so a Widow can choose the Goon.
- A player that the Demon kills does not make a later choice that night.
- The Assassin choice was registered after the Goon rule ran and had no effect. The Goon rule now runs last.
- Demon kills used a default position after the Godfather. They now use their own positions.
- The shared claim convention now covers the Goon. A Goon that claims another character is evil at the last phase of the timeline. A Goon claim can report alignments at given times, and a Goon that is good at the last phase reports them correctly. The editor has controls for these reports.
- A good Goon could claim a Townsfolk character before this change. One existing test relied on that; its Goon now claims the Goon.

One existing test changed. It expected a Shabaloth kill of the Goon to be illegal when a Sailor made no report. A Sailor without a report has an unknown choice, so that history is legal. The test now uses a Sailor report of another player for the illegal case.

`src/builders/goon.test.ts` covers legal and illegal histories for these rules. One test runs for each character with a night choice rule and shows that its unreported choice can make it drunk only when a Goon is in play. Other tests cover reported choices, unknown nights, the night order, death before a choice, the one-use limit, renamed players with seating preserved, duplicate reports, and redundant facts. The night order follows the official night sheet from memory; the sheet and the [Goon](https://wiki.bloodontheclocktower.com/Goon) page revision were not retrieved.

## The Mutant in the claim convention

The images of puzzles 91, 93, and 95 state the same rule: a living Mutant claims a Townsfolk character with any information, and a dead Mutant reveals itself. The engine now applies this as the default for each claim without a list of possible characters. `src/builders/mutant.test.ts` covers legal and illegal claims, a list that replaces the default, renamed players, and a duplicate death report.

Twenty-two catalog documents had lists that the convention makes redundant. Those lists are removed, and every answer is unchanged.

- Most lists were equal to the engine default.
- Puzzles 53, 61, 65, 75, 79, and 82 let dead Townsfolk claimants be the Mutant. The repository owner confirmed that a dead Mutant always reveals itself, so those lists are removed also.
- The living Townsfolk claimants without a list in puzzles 11, 39, and 71 can now be the Mutant.

Puzzle 07 let only one living claimant be the Mutant, and it had the Drunk on its script. Its [image](../puzzle-images/puzzle-07-the-savant-strikes-back.webp) says that the Mutant is the only Outsider and that it claims a Townsfolk character. The document now has no Drunk and no lists except the given about You. Each Townsfolk claimant can be the Mutant, and the answer is unchanged.

Puzzle 11 had a list on Matthew's claims that let him be a starting Artist. Its [image](../puzzle-images/puzzle-11-false-is-the-new-black.webp) has Matthew claim a starting Seamstress, so a good Matthew cannot be a starting Artist. That list is removed, with the redundant `uniqueCharacters` setting, and the answer is unchanged. One list stays: Sula's Snake Charmer check is a second claim by a Philosopher, and its list names the characters that her Philosopher claim allows.

A list on You is a given about one player.

## Support limits

The [existing engine limits](rules-first-engine.md#coverage-that-still-needs-migration) still apply. In addition:

- Unknown choices are made only when a Goon is on the script, because the Goon is the only rule that reads them. These are the choices from night choice rules and the no-effect choice of a drunk or poisoned Demon. Actions over existing variables, which include Demon kills, are always registered and appear in every witness.
- These choices are not actions: the Kazali choice of Minions and the choices of a Lunatic. The Monk has a night choice rule but no claim type.
- A Fang Gu jump records the dead Fang Gu as the selection, not the Outsider that the Fang Gu chose.
- A Demon action selects only victims and no-effect targets. A sober Demon that chooses a dead or protected player has no selection.
- A drunk or poisoned player still chooses. A player that believes it has a character, such as the Drunk, does not choose.
- The first night uses the same order as other nights, except for the Lleech and the Butler.
- The Xaan death timing treats every Townsfolk as acting after the Demon. A Townsfolk that acts before the Demon on night X is still poisoned by the rules; no catalog puzzle needs this distinction.
- The fixtures check initial assignments against hand derivations. They do not certify every hidden history admitted by the model.
