# Puzzle editor evaluation

The desktop editor opens on the circular puzzle overview. Each token shows the player and claimed character. Reports sit next to their players. Clicking a player opens a dismissible claim editor without resizing the circle. Public events, the remaining possible characters, and puzzle conventions appear below it.

The roster is a separate entry view. It supports direct name editing, character completion, and keyboard navigation. **Paste roster** accepts clockwise names, optionally paired with characters using `=` or spreadsheet tabs. It previews the player and claim counts before applying the input. Existing observations are preserved when new players are appended.

## Creation evaluations

`tests/e2e/manual-puzzle-entry.spec.ts` recreates all 91 supplied puzzles through the UI at both desktop and 390 × 844 phone widths and compares their exported documents with the existing puzzle inputs. The evaluation includes 730 seats and 834 source claims across puzzles with 6–15 players. It covers repeated reports, later character claims, public events, structured abilities, and custom statements. It does not generate new solution fixtures.

The revised entry path sets all player names with one field entry and two clicks. A player's first character claim takes one character-field edit, replacing the former character selection, player selection, and Add claim sequence. Further reports retain the detailed claim editor.

`tests/e2e/roster-workflow.spec.ts` checks the faster combined path: seven named characters, matching the reference puzzle's roster, require one multiline entry and two clicks. This creates the roster and claim forms; ability information, events, and remaining possible characters still need to be entered. The test also checks keyboard completion, invalid input, preservation of existing observations, phone layout, and opening and closing claim details.

These are UI action counts and automated correctness checks, not measurements of human completion time.

## Mobile creation

At phone width, selecting a player expands the report editor inside that player's card. The same editor works in the seating list and the entry roster. **Next player** opens the next card and brings its fields into view. **Done** collapses the fields and returns focus to the player's summary. A first character selection creates its report immediately; additional reports remain available inside the card.

Mobile form controls have 44-pixel minimum heights, text fields use 16-pixel type, and player choices have large labeled targets. Reports use the page's scroll area. The hidden-role picker supports multiple selections, character-type filters, and search. Roles required by existing observations remain locked. Its controls remain available in a short viewport.

`tests/e2e/mobile-workflow.spec.ts` recreates the seven-player reference puzzle using a prepared roster and the inline editor. The measured path uses **30 input actions: four text entries and 26 control actions**, excluding export, scrolling, keyboard focus, and preparation of the pasted text. The four entries are the title, roster, Investigator role, and Washerwoman role. The previous audited path used 35 actions with 12 text entries. This compares practical entry paths, not an isolated timing experiment: the revised path also skips unchanged defaults and relies on the existing Slayer event synchronization instead of entering the same death twice.

The mobile checks cover later reports, renaming, focus after closing, 320 × 480 and 390 × 480 viewports, and preserving observations when switching between phone and desktop layouts. These are Chromium viewport and touch-emulation checks; they do not measure physical phone keyboard behavior or human completion time.

## Overview evaluations

`tests/e2e/circle-layout.spec.ts` loads every catalog puzzle at 1440 × 1100 and checks that reports, tokens, player names, and the event history do not overlap. Motion is disabled to measure settled layouts. Long reports use the available horizontal space, and the event history moves down when a report needs more room. Circles with more than ten seats use outward-facing names and a complete report list below the circle.

The reference seven-player puzzle has an additional viewport check for its continuation convention. Mobile tests cover complete report text, long titles, seat reordering, and entry without horizontal scrolling.

## Reproduction

```sh
bun run test:unit
bun run typecheck
bun run build
bun run test:e2e
```

The solver's declared limitations remain visible in the results. Passing these UI checks establishes entry and display behavior; it does not establish complete character or interaction support in the engine.
