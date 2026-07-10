# BOTC puzzle-builder interface concepts

These concepts are based on the live app, the example-puzzle catalog, and `tests/e2e/manual-puzzle-entry.spec.ts`.

## Current workflow inventory

The manual-entry suite rebuilds all 85 example puzzles through the UI and verifies the exported JSON. A replacement interface must preserve:

- Puzzle title, player count, player names, clockwise seat order, and seat reordering.
- Script setup mode (`standard`, `none`, or `atheist`), unique-character rules, and searchable role add/remove controls.
- Seven timeline event types: execution, survived execution, night death, nomination death, Slayer shot, Witch curse, and Doomsayer death. Events may include timing, multiple players, and a caller.
- Player/claim selection and the dynamic editors for 55 claim types, including repeatable checks, guesses, nominations, statements, counts, roles, player sets, timing, advanced possible roles, and the Widow-call flag.
- Custom constraint expressions, example loading, JSON import/export, and solving.

The examples span 6–15 players, up to 18 script roles, and up to 14 claims. Fifteen examples use custom constraints.

## Streamlining principles

1. Keep the puzzle state visible while editing, but show only one focused editor at a time.
2. Make the primary path explicit: **Players → Script → Events → Claims → Solve**.
3. Let a seat click open its claim editor directly; retain a global claim list for scanning and reordering.
4. Replace drag-only timeline creation with an equally prominent **Add event** action. Drag and drop can remain a shortcut.
5. Use search-first role and claim pickers with recent/common suggestions.
6. Collapse advanced fields by default while keeping stable accessible labels for Playwright and assistive technology.
7. On phones, switch the large ring to a compact roster or scrollable mini-ring and open editors in a bottom sheet. Never preserve desktop minimum widths.
8. Keep `New`, `Examples`, `Import`, and `Export` in one overflow/project menu; keep `Solve` persistently visible.

## Concept A — Storyteller's Ledger

The recommended direction. Warm parchment and ink, but quieter and more product-like than the current page. A slim step rail replaces the large tab bar. The seating chart stays central, the timeline becomes a compact strip, and a contextual inspector edits the selected seat, event, role, or claim. Mobile uses a sticky five-step footer and a bottom-sheet inspector.

## Concept B — Midnight Grimoire

A compact dark interface for keyboard-heavy users. Search and command-palette interactions handle roles, claims, and players. The center combines a mini seating ring with an event stream; the right panel is a dense schema-driven form. Mobile becomes a single card stack with a sticky action dock.

## Concept C — Investigator's Pinboard

A visual clue-board direction. The seating ring is surrounded by concise claim cards, but cards snap into lanes and never overlap. The inspector uses large, friendly controls and color-coded evidence groups. Mobile replaces the canvas with a player roster and horizontal evidence cards.

## Image-generation prompt set

All three prompts use the current populated desktop UI as a structural reference, not as an edit target.

### A — Storyteller's Ledger

Use case: ui-mockup  
Asset type: responsive web-app concept board showing desktop and mobile  
Primary request: redesign the BOTC puzzle builder as a streamlined Storyteller's Ledger interface that can create a complete puzzle  
Input image: current populated desktop UI, structural reference only; redesign it rather than copying it  
Style/medium: shippable realistic product UI, warm parchment with crisp modern controls, restrained Blood on the Clocktower mystery atmosphere, not concept art  
Composition/framing: one large 1440px desktop screen plus one 390px phone screen on the same 16:9 presentation board  
Desktop structure: compact top bar with project menu and persistent Solve button; slim vertical step rail labeled Players, Script, Events, Claims, Solve; central seating ring for seven named players; compact timeline below; contextual right inspector editing Sula's Clockmaker claim  
Mobile structure: header, compact roster/mini-ring switch, claim summary cards, sticky five-step bottom navigation, bottom-sheet claim editor  
Text: "The Vortox Conjecture", "Players", "Script", "Events", "Claims", "Solve", "Sula", "Clockmaker", "Demon-minion distance", "Night 1"  
Constraints: practical responsive layout; no clipped content; no horizontal scrolling; accessible contrast; controls at least 44px on phone; preserve player, role, timeline, claim, constraint, import/export, example, and solve workflows; no watermark; no unrelated branding

### B — Midnight Grimoire

Use case: ui-mockup  
Asset type: responsive web-app concept board showing desktop and mobile  
Primary request: redesign the BOTC puzzle builder as a compact dark Midnight Grimoire workspace for fast keyboard and touch entry  
Input image: current populated desktop UI, structural reference only; redesign it rather than copying it  
Style/medium: shippable realistic product UI, deep navy-black surfaces, muted burgundy and cool blue alignment accents, subtle paper grain, crisp sans-serif typography  
Composition/framing: one large desktop screen and one phone screen on the same 16:9 presentation board  
Desktop structure: compact header with puzzle title and Solve; searchable command bar; collapsible left roster with seven players and claim badges; center mini seating ring plus chronological event stream; right focused claim form with repeatable fields; completion counters for Players, Script, Events, Claims  
Mobile structure: single-column player and event card stack; sticky action dock; search-first add button; full-width editor sheet  
Text: "The Vortox Conjecture", "Add role, claim, player, or event…", "7 Players", "10 Roles", "3 Events", "7 Claims", "Clockmaker", "Demon-minion distance", "Solve puzzle"  
Constraints: dense but calm; practical form controls; no clipped text; no horizontal scrolling; strong focus states; preserve every creation workflow; no watermark; no unrelated branding

### C — Investigator's Pinboard

Use case: ui-mockup  
Asset type: responsive web-app concept board showing desktop and mobile  
Primary request: redesign the BOTC puzzle builder as a clear Investigator's Pinboard where player claims and timeline evidence are easy to scan and edit  
Input image: current populated desktop UI, structural reference only; redesign it rather than copying it  
Style/medium: shippable realistic product UI, warm ivory canvas, dark ink, oxblood and cyan accents, subtle cork-and-paper cues used sparingly, modern typography  
Composition/framing: one large desktop screen and one phone screen on the same 16:9 presentation board  
Desktop structure: compact header; left setup checklist; central non-overlapping seating ring; claim cards snapped into a tidy evidence lane; horizontal day/night timeline; right inspector for the selected claim  
Mobile structure: player roster replaces the canvas; horizontally scrollable evidence cards; day/night timeline chips; bottom navigation and editor drawer  
Text: "The Vortox Conjecture", "Setup", "Players", "Evidence", "Timeline", "Claims", "Solve", "Sula — Clockmaker", "Night 1"  
Constraints: thematic without decorative clutter; no overlapping cards; no clipped content; accessible contrast; preserve complete puzzle creation; no watermark; no unrelated branding
