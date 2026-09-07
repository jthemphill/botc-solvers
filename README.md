# TypeScript BOTC Solver

Bun-based TypeScript port of the Python BOTC puzzle SAT solver.

Every puzzle describes an ongoing game. The solver always applies continuation constraints through the end of the supplied timeline.

All puzzles use the same claim convention: good players report honestly, and evil players claim a different character. Game rules account for false beliefs and false information. The solver infers the final modeled phase from the supplied events and reports.

```sh
bun install
bun run playwright:install
bun run test
bun run typecheck
```

`bun test` (or `bun run test:unit`) runs the unit tests in `src`, as configured in `bunfig.toml`.
`bun run test:e2e` runs the browser tests with Playwright and starts the Vite server automatically.
Run `bun run playwright:install` once to install Chromium before running browser tests.
`bun run test` runs both suites. The `run` keyword selects the package script instead of Bun's built-in test runner.

Browser tests cover editor behavior and complete user workflows:

- `manual-puzzle-entry.spec.ts` enters compact examples through the UI and checks their exported data. The claim cases cover every structured claim form, plus expressions and advanced fields. Separate desktop and mobile workflows create a puzzle, solve it with the real worker, change a report to make it unsatisfiable, correct it, and export/import it.
- `puzzle-display.spec.ts` checks example loading, result updates, claim summaries, death markers, mobile layout, and coverage notices.
- `seat-reorder.spec.ts` checks dragging, renaming, player counts, and timeline interaction.

Claim form cases test data entry; they are not assertions of legal game histories. The complete workflow uses a five-player puzzle with Chef, Empath, Soldier, Imp, and Scarlet Woman. Ben and Cara have the only Empath and Soldier claims. Ben's zero makes Ada the Chef, leaving Drew and Eve to exchange the two evil roles. No Drunk or Poisoner can invalidate those reports.

New puzzles get catalog and solution coverage in the Bun suite. Add browser cases when a change introduces editor behavior or a new user workflow. Do not add a browser test for each puzzle. For a focused run, use `bun run test:e2e -- tests/e2e/manual-puzzle-entry.spec.ts` or select a test with `--grep`.

[Rules-first architecture, compatibility migration, tested scope, and remaining work](docs/rules-first-engine.md).

Results distinguish incomplete enumeration and incomplete game-rule coverage. Listed characters are not necessarily fully implemented.

```sh
bun scripts/benchmark-engine.ts
bun run benchmark --runs 7 --output /tmp/botc-before.json
# After an engine change:
bun run benchmark --runs 7 --compare /tmp/botc-before.json --output /tmp/botc-after.json
```

The catalog benchmark fully enumerates all 91 existing puzzles, including the intro. It reports per-puzzle medians,
raw samples, formula sizes, and hashes of sorted initial role assignments. `--compare` fails if assignments or
enumeration status change. Use `--filter puzzle-82` for a focused run. One full warmup pass precedes three measured
passes by default; `--warmup` and `--runs` control those counts. Run benchmarks without concurrent tests or builds.
Backend time includes Kissat creation, clause loading, search, witness extraction, and release. Total time also
includes document validation, constraint construction, finalization, witness checks, and decoding. Runtime startup,
result hashing, and report output are excluded. Coverage limitations still apply to the enumerated worlds.

[SAT optimization benchmark and per-puzzle results](docs/sat-benchmark.md).
