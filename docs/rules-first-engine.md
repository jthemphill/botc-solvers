# Rules-first engine migration

This change repairs independently reproduced rule failures. A satisfying assignment is a candidate under the encoded rules and supplied observations. The results show a brief coverage notice. The remaining rule gaps are listed below.

## Development contract

The review of `591d103` found that matching published role assignments could conceal invalid causal histories. In particular, `49f3d46` added answer fixtures alongside mechanics, `292b02e` explained Pit-Hag changes from claims rather than actions, and `4c1a2b5` made Shabaloth target generation depend on an empty death report. `77a8cd8` explicitly described compensating puzzle constraints hiding engine errors.

[AGENTS.md](../AGENTS.md) now requires source-backed legal, illegal and interaction cases before consulting puzzle answers, meaning-preserving transformations, and a dependency boundary between rules and fixtures. The corpus continues to assert the **same initial role assignments**. No `.solutions.json` files were regenerated. Poison and drunk witnesses are no longer treated as canonical answers; enumeration projects onto initial characters.

When an extra world appears, inspect its trace and locate the first illegal state or action. Repair that rule and demonstrate both rejection of the illegal history and retention of a legal neighboring history. A role exclusion justified only by a published answer is not a repair.

## State, actions and observations

`CharacterTrace` owns persistent character replacement. Queries distinguish initial, before-boundary and after-boundary character state. Frame constraints preserve characters between transitions. Acquired abilities, including Philosopher abilities, are separate from character identity and stop being possessed when their source character is lost.

Pit-Hag and Cerenovus choices are generated for each applicable modeled night, independently of claims. Pit-Hag picks one player and one character; an in-play character prevents replacement. Character changes preserve alignment. Demon creation is available as a cause of arbitrary deaths that night. Cerenovus has one player and good-character choice, rather than an unrestricted explanation for every changed report. Shabaloth always has two distinct choices on applicable nights, including dead targets. A complete death report constrains their consequences.

Claims do not create Pit-Hag or Cerenovus actions. Reports from a truthful starting character cannot silently remain valid after that character loses the reported ability. Dreamer reads the observed current character, and Juggler scores guesses against the previous day, before subsequent night changes.

The trace records character state at phase boundaries. Several abilities derive eligibility from public timeline entries. A missing death report leaves kills unconstrained. Later public-life calculations still use the reported deaths. Full night action order, independent life state, and victory resolution remain partial.

## Shared puzzle conventions and compatibility

All supported puzzles use one claim convention. Good players report honestly, subject to the modeled rules for false beliefs and false information. Evil players claim a different character. Explicit `possibleActualRoles` and custom constraints remain givens. The engine applies this convention to every puzzle. Each claim's source annotation identifies the origin of its generated constraints.

All puzzles describe games that are still ongoing at the end of the supplied timeline. Continuation is an invariant of the puzzle domain, so terminal Demon/Saint exclusions always apply and there is no input option to disable them. General victory resolution remains partial.

A `nightDeath` entry reports all deaths for its night; an empty list means zero deaths. An absent entry is unknown. The builder infers the final modeled phase from event times, report times, and default times for repeated checks.

Role claims refer to starting characters by default. An explicit `roleTiming`, such as `"day_2"`, refers to the character at that phase. Information uses its own report time. Optional source annotations identify the origins of claims and custom constraints.

The catalog migration preserves existing interpretations rather than inventing new observations:

1. The engine applies the shared claim convention and ongoing play to every catalog document.
2. Baseline role claims use the initial-character default; later character claims have an explicit phase.
3. Existing `.role`/`.type` paths in custom expressions now say `.initial_role`/`.initial_type`, retaining their pre-migration semantics. Ordinary new paths use the compilation context's time. This is a compatibility migration, not a fresh audit of every puzzle's prose.
4. Puzzle 11's `uniqueCharacters: false`, introduced in `49f3d46`, allowed two **starting Artists**. Its script has no rule permitting that setup. Normal initial uniqueness is restored. Philosopher can duplicate an ability without disabling character uniqueness; an independent regression demonstrates this distinction. The other explicitly unusual duplicate-character scenarios retain their settings.

Two old Shabaloth unit scenarios also needed legal second targets: one now includes an earlier execution of the bluffing Mastermind, and the Goon interaction includes an earlier dead player. Their original single-death nights with all other targets alive were not legal demonstrations of their intended interactions.

## DSL and solver

The existing parser now binds and checks into `TypedProgram`, whose operations are Boolean gates, cardinalities and typed domain queries with source spans. Only a successfully checked program lowers to SAT, so a late type error cannot leave partial constraints in a model. Structured character predicates and DSL operations share the model's temporal queries. Full migration of structured claims into the same IR is still outstanding.

Current `.role`, `.type`, forward joins and inverse joins use context time; `initial_role` and `initial_type` are explicit setup relations. `role_at` refers to character identity. Set equality compares set members. Mathematician aggregation occurs after all reports, so report order and expression spacing give the same result.

Mathematician records abnormality by player and interval, unions duplicate reports, includes the prior day for nighttime counts, and excludes the observer. The general `recordAbilityMalfunction` interface accepts non-information failures. Not all legacy actions emit such events yet, and unreported information is not fully generated.

`finalize()` closes the model once and returns a frozen CNF snapshot. Subsequent fact/rule mutations and new queries are rejected. `solve()` returns status, completion, stopping reason, projection, and variable/clause/build/search metrics. The legacy `solveAll()` wrapper throws on unknown instead of converting it to an empty solution set. Reaching a limit is conservatively incomplete, even if the limit happens to equal the true number of worlds.

Each emitted clause retains an origin. DSL operations include source spans. Other clauses identify their rule or report. SAT witness errors use these origins to identify the failing constraint.

Each SAT witness is checked against every emitted clause. Separately written imperative checks verify character persistence, conflicting replacements, snapshot completeness, and action choice counts/domains. These checks cover their named invariants; they are **not** an independent complete-game simulator.

Obsolete browser requests terminate the synchronous WASM worker and reject its pending promise. Worker failures also reject pending requests and allow subsequent recovery. Completed workers can be reused. Results show completion and coverage limits and expose character changes and hidden choices.

## Measurements and backend decision

Run `bun scripts/benchmark-engine.ts` for generated cases without puzzle fixtures. On this checkout's Mac, representative cold-run measurements were:

| Direct exact count | Variables | Clauses |
| ------------------ | --------: | ------: |
| 5 of 10            |        81 |     141 |
| 10 of 20           |       311 |     581 |
| 20 of 40           |     1,221 |   2,361 |
| 40 of 80           |     4,841 |   9,521 |

The reviewed direct 10-of-20 harness produced 335,921 clauses. The new sequential encoder is polynomial, and small at-most-one constraints retain a pairwise encoding. Exhaustive small-domain tests cover signed and repeated literals, bounds, and inactive guards.

The bundled Kissat adapter still creates/releases a solver for every query. Enumerating 256 binary role projections required 257 backend calls (about 50 ms in this generated small case). No incremental backend was substituted: the installed adapter exposes no supported incremental interface, and no alternative backend was available for a like-for-like measurement. A future comparison must preserve the same prepared CNF, projection, assumptions, witness validation, and interruption behavior; a claimed speedup from changing game constraints is not a solver benchmark.

## Coverage that still needs migration

The remaining coverage gaps include:

- A complete ordered wake/event kernel, independent actual/apparent life, and victory resolution remain to be implemented.
- Monk protection remains to be implemented.
- Shabaloth attack ordering, full resurrection interactions, Cerenovus madness executions, and newly acquired ability scheduling remain partial.
- Poisoning and drunkenness still use legacy source collections for many characters. Full source duration/termination migration and interactions with character replacement remain incomplete.
- Complete generated hidden actions and abnormality events for the rest of the registry, jinx coverage, a whole-game independent checker, and incremental-backend evaluation remain open work.

These are reported limitations, not exceptions to the rules-first acceptance criterion. Expand the tested scope one source-backed vertical slice at a time.

## Rule sources consulted

- [Pit-Hag, revision 2998](https://wiki.bloodontheclocktower.com/index.php?title=Pit-Hag&oldid=2998)
- [Shabaloth, revision 1790](https://wiki.bloodontheclocktower.com/index.php?title=Shabaloth&oldid=1790)
- [Hermit, revision 2805](https://wiki.bloodontheclocktower.com/index.php?title=Hermit&oldid=2805): intrinsic Drunk belief preserves other Outsider abilities; external impairment still matters.
- [Juggler, revision 2401](https://wiki.bloodontheclocktower.com/index.php?title=Juggler&oldid=2401)
- [Mathematician, revision 3109](https://wiki.bloodontheclocktower.com/index.php?title=Mathematician&oldid=3109)
- [Xaan, revision 3082](https://wiki.bloodontheclocktower.com/index.php?title=Xaan&oldid=3082): zero Outsiders means no poisoning night.
- [Setup, revision 1361](https://wiki.bloodontheclocktower.com/index.php?title=Setup&oldid=1361)
- [Philosopher](https://wiki.bloodontheclocktower.com/Philosopher), [Cerenovus](https://wiki.bloodontheclocktower.com/Cerenovus), [Spy](https://wiki.bloodontheclocktower.com/Spy), [States](https://wiki.bloodontheclocktower.com/States), [Rules Explanation](https://wiki.bloodontheclocktower.com/Rules_Explanation), consulted 6 September 2026.
