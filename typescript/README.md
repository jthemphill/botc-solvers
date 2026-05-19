# TypeScript BOTC Solver

Bun-based TypeScript port of the Python BOTC puzzle SAT solver.

```sh
bun install
bun test
bun run typecheck
```

The root `tsconfig.json` is a project-reference hub and checks no files directly. `tsconfig.browser.json` checks browser-safe solver code without Node/Bun ambient types, while `tsconfig.test.json` checks Bun tests and puzzle entrypoints with Bun types.

## SAT backend

`BOTCModel` defaults to the in-repo `DpllBackend`. It accepts CNF clauses and returns a satisfying assignment, which keeps the solver dependency-free and browser-safe.
