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

[Rules-first architecture, compatibility migration, tested scope, and remaining work](docs/rules-first-engine.md).

Results distinguish incomplete enumeration and incomplete game-rule coverage. Listed characters are not necessarily fully implemented.

```sh
bun scripts/benchmark-engine.ts
```
