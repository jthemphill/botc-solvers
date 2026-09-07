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

[Rules-first architecture, compatibility migration, tested scope, and remaining work](docs/rules-first-engine.md).

Results distinguish incomplete enumeration and incomplete game-rule coverage. Listed characters are not necessarily fully implemented.

```sh
bun scripts/benchmark-engine.ts
```
