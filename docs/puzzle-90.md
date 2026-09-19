# Puzzle 90 — Last Liar Standing

The transcription follows the [user-supplied image](../puzzle-images/puzzle-90-last-liar-standing.jpg). Seating runs clockwise from Fraser. The [puzzle archive](https://notquitetangible.blogspot.com/2024/11/clocktower-puzzle-archive.html) did not yet list puzzle 90 when checked on 19 September 2026. Reddit search returned a login page, and two public mirrors blocked access. No author-confirmed solution was retrieved.

## Observations and conventions

The document includes the six public timeline events and all reported information. Dan's nomination kills Olivia before the day-1 execution. Jasmine's two Town Crier results refer to days 1 and 2 and arrive on nights 2 and 3. Anna guesses on day 1 and receives her result on night 2. Matt's checks run from night 1 through night 4.

Standard setup supplies one Imp, one Minion, and two Outsiders for nine players. The existing Xaan modifier permits other Outsider counts. The shared claim convention supplies honest good reports and different character claims for evil players. The only explicit restriction on actual characters is the image's Fortune Teller-or-Drunk perspective for You. The game continues after the final event.

## Independent check of the fixture

The solver enumerates one initial character assignment: Tom is the Imp, Olivia is the Spy, and Matt is the Drunk. Everyone else has their claimed character. The fixture records characters only, without fixing arbitrary hidden choices.

This assignment has a legal witness from the image and official rules:

- Dan and Matt supply the two Outsiders. Tom and Olivia supply the two evil characters, and each claims a different character.
- Olivia registers as the Drunk to Fraser's Librarian. The [Spy rules, revision 3013](https://wiki.bloodontheclocktower.com/index.php?title=Spy&oldid=3013), permit registration as a specific Outsider.
- Aoife's neighbors are Anna and Fraser, both good, so her Empath 0 is correct.
- Anna's Matt=Drunk guess is correct, and her Jasmine=Drunk guess is incorrect.
- Neither day's named nominators include the Minion. Tom is the Demon, so his day-2 nomination does not cause a Town Crier yes.
- Matt believes he is the Chambermaid and can receive all four reported numbers. The [Drunk rules](https://wiki.bloodontheclocktower.com/Drunk) allow false information for the believed Townsfolk character.
- Neither Anna nor Aoife is the Demon. Choose another good player, such as Dan, as the Fortune Teller's red herring to give You a no.
- Dan can kill Olivia with his nomination under the [Golem rules, revision 2912](https://wiki.bloodontheclocktower.com/index.php?title=Golem&oldid=2912). Tom can kill Aoife, Dan, and Jasmine on the reported nights. The two executions kill good Townsfolk. Fraser, Tom, and Matt remain alive after night 4.

No engine behavior changes are needed for this transcription. The solver's [existing coverage limits](rules-first-engine.md#coverage-that-still-needs-migration), including incomplete event ordering and character-change interactions, still apply. The fixture checks the initial assignment; it does not certify every hidden history admitted by the model.
