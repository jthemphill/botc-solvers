# Rules-first development

This solver must accept legal Blood on the Clocktower histories and reject illegal ones within its declared support scope.

Each puzzle describes a game that continues after its last event.

- Use [ASD-STE100 Issue 9](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf) for code comments. Write short sentences in the active voice. Describe what the code does. Use the same technical term for the same concept.
- Add code for current puzzle requirements. Add a setting only when supported puzzles need different values. Implement shared behavior directly.
- Use shared defaults to keep puzzle files small. Remove unused code when you simplify a feature.

- Keep official game rules, supplied observations, and puzzle assumptions separate. Cite the official rule and its revision when adding character behavior.
- For a rule repair, add a minimal legal witness, an illegal counterexample, and a relevant interaction test before consulting the puzzle solution fixtures.
- Never add a player/role restriction to recover a known solution count. Identify the illegal action or state in a counterexample first.
- Engine and DSL modules must not import examples, solution fixtures, or puzzle-specific names.
- Apply the shared puzzle convention to claims: good players report honestly, and evil players claim a different character. Game rules generate abilities, actions, character changes, and status effects.
- Missing observations mean unknown; an explicitly complete observation constrains all outcomes in its interval.
- Preserve state unless a rule changes it. Distinguish character, alignment, possessed abilities, shown token, and claimed character.
- Test renaming with seating preserved, redundant facts, duplicate reports of the same event, and both legal and illegal interactions.
- Compare puzzle conclusions separately from arbitrary hidden witnesses. Do not regenerate expected role assignments from the solver under test without an independent rule/source justification.
- Report incomplete character and interaction support. Do not describe a satisfiable approximation as a verified game history.
- Run unit tests, typechecking, and build checks for engine changes; run relevant browser tests for changes to the worker, schema, or UI.
- Cover editor controls and complete UI workflows with small browser examples. Keep exhaustive puzzle solution coverage in unit tests. Do not add a browser test for each puzzle.
