# Puzzles 93, 95, and 96

The [puzzle archive](https://notquitetangible.blogspot.com/2024/11/clocktower-puzzle-archive.html) listed these three puzzles after puzzle 92 on 14 November 2026. Puzzle 94 is Clockdoku II and is not in the catalog. The images in `puzzle-images/` are the user-supplied originals. Seating runs clockwise from the top of each image.

The session could not reach Reddit or the official wiki. No author-confirmed solution was retrieved. Each fixture below comes from a hand derivation from the image and the rules, done separately from the solver. The solver then enumerated the same single assignment for each puzzle.

## 93 — A Study in Idiocy

[Post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1x0lotq) · [Image](../puzzle-images/puzzle-93-a-study-in-idiocy.webp)

Tim is the Imp, Aoife is the Xaan, and Hannah is the Mutant. Everyone else has their claimed character.

The document records the six deaths and all reports. The image lets a living Mutant claim a Townsfolk character, and makes a dead Mutant reveal itself. Hannah is the only living Townsfolk claimant, so only Hannah can be the Mutant. Your character is Village Idiot. No custom constraint is used.

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

Jasmine, Oscar, Tim, and Sarah are alive at the end. Each of them can be evil, the Mutant, or an Outsider that became the Fang Gu. One constraint records the image's rule that only an Outsider that became the Fang Gu may hide a starting Sweetheart. Aoife's guesses are scored on night 2. Oscar asks his question on day 3.

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

The image ties honesty to the alignment on day 4. Two constraints record this: a Goon that claims another character is evil on day 4, and Hannah's alignment history holds if she is good on day 4. The empty night-2 death report is explicit.

Check of the assignment:

- Anna poisons Dan on night 1, so the Chef's 0 is false. Hannah and Anna are neighbors.
- Sula's distance of 1, Oscar's Investigator result, your "Dan is good", and Tim's Artist answer are all true.
- Anna poisons You on nights 2 and 3. Your "Oscar is evil" and "Hannah is good" are false.
- On night 2, Hannah chooses Matthew. Hannah is the first to choose the Goon, so she is drunk and nobody dies. Matthew becomes evil and stays evil, so he may lie on day 4.
- Hannah kills Oscar and You. Matthew, Tim, and Hannah remain alive.

A second candidate has Matthew as the Imp, Anna as the Poisoner, and Hannah as an evil Goon. It needs a poisoned Village Idiot to choose the Goon on night 3 without changing her alignment. The engine treats a choice by a poisoned or drunk player as a choice, so Hannah becomes good and must then report truthfully. This reading gives the puzzle its single answer. The wiki ruling for this interaction was not retrieved.

### Rule changes

- The hidden Poisoner choice of each night is an ability target. A Poisoner that chooses the Goon first is drunk until dusk and poisons nobody.
- A Demon can choose the Goon first. The Demon is then drunk and kills nobody that night, and the Goon becomes evil. A Demon that chooses the Goon later kills it, as before.
- Reported Village Idiot and Seamstress choices are ability targets.
- The DSL function `alignment_at(player, Good | Evil, timing)` reads the alignment at a given time.

`src/builders/goon.test.ts` covers legal and illegal histories for each of these, the interaction between Poisoner and Village Idiot choices on one night, the change back to good, renamed players with seating preserved, duplicate reports, and redundant facts. These tests fail on the previous engine. The [Goon](https://wiki.bloodontheclocktower.com/Goon) page revision was not retrieved.

## Support limits

The [existing engine limits](rules-first-engine.md#coverage-that-still-needs-migration) still apply. In addition:

- Hidden Demon choices of the Goon cover Imp, Fang Gu, Vigormortis, No Dashii, and Vortox. Other Demons keep their existing target models.
- Only reported Seamstress and Village Idiot choices are ability targets. Unreported choices by these characters are not generated.
- The Xaan death timing treats every Townsfolk as acting after the Demon. A Townsfolk that acts before the Demon on night X is still poisoned by the rules; no catalog puzzle needs this distinction.
- The fixtures check initial assignments against hand derivations. They do not certify every hidden history admitted by the model.
