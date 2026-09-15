# Puzzles 87–89

The images in `puzzle-images/` are the user-supplied originals. Seating runs clockwise from the top. The documents use standard setup counts and include only reported information, deaths, and the source's role-reporting conventions.

## 87 — Freaky Friday

[Post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1vhyfy0/weekly_puzzle_87_freaky_friday/) · [Author confirmation](https://www.reddit.com/r/BloodOnTheClocktower/comments/1vhyfy0/comment/p294awr/)

Sarah starts as the No Dashii, and Aoife starts as the Witch. Charlotte is the Barber. After Charlotte dies on night 2, Sarah and Aoife swap characters. Aoife is the final Demon; Sarah is the final Witch. The solution fixture records initial characters, and a separate test requires the swap.

The final role reports encode the source's statement that good players truthfully report their roles. No player reports a swap. A living starting Mutant can retain its permitted Townsfolk bluff. These reports prevent unreported swaps of good players from explaining later poison. Tom's Artist question reads current characters on day 3.

## 88 — Lucky Saint

[Post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1w794un/weekly_puzzle_88_lucky_saint/) · [Author confirmation](https://www.reddit.com/r/BloodOnTheClocktower/comments/1w794un/comment/p7t7lt9/)

Charlotte is the Imp; Josh is the Poisoner. All other players have their claimed characters. Fraser is poisoned on night 1, Sarah on night 2, and Matt on night 4. The night-3 choice is not determined.

The night-4 Ravenkeeper result and day-4 Artist answer share one Poisoner choice. The failed Slayer shot occurs on day 4, after Matt's death.

## 89 — The Bigger Picture

[Post](https://www.reddit.com/r/BloodOnTheClocktower/comments/1wdjdua/weekly_puzzle_89_the_bigger_picture/)

Tim is the Vortox; Josh is the Witch. All other players have their claimed characters. This assignment has an independent check against the supplied image: Charlotte's distance of 1 is false, Aoife's question includes Tim as the Vortox, and Dan's Town Crier result is false because Josh nominated. Sarah's 0, 0, 1 readings are false for their respective malfunction counts. The Snake Charmer choices and Klutz choice do not provide Townsfolk information affected by Vortox.

The public search excerpt mentions a corrected image and the Vortox/Mathematician explanation. Reddit, two static mirrors, and the reader fallback blocked access to the full discussion. The transcription follows the supplied image, including “Witch or Vortox” in the Artist question; author confirmation was not retrieved for this puzzle.

## Rule changes and coverage

- [Barber, revision 1757](https://wiki.bloodontheclocktower.com/index.php?title=Barber&oldid=1757): one optional pair per reported Barber death; living and dead targets; alignment preservation; no other Demon as a target; current characters for later deaths and No Dashii poison.
- [Poisoner, revision 1737](https://wiki.bloodontheclocktower.com/index.php?title=Poisoner&oldid=1737): one target for the night and following day, with source loss ending poison.

Independent rule tests cover legal and illegal histories, poison movement, role reports, duplicate death reports, and renaming with seating preserved. Existing engine coverage limits still apply: phases do not fully order simultaneous character changes, newly acquired abilities, or all death and poison interactions. Barber transitions occur after the reported night death and before later information; combinations with other character-changing abilities need further ordering support.
