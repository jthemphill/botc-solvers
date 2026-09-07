import { expect, test } from "bun:test";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

test("rule code and the DSL cannot depend on puzzle data or expected answers", () => {
  for (const layer of ["model", "dsl", "builders"]) {
    const directory = join(import.meta.dir, "..", layer);
    for (const file of readdirSync(directory).filter((file) => file.endsWith(".ts") && !file.endsWith(".test.ts"))) {
      const source = readFileSync(join(directory, file), "utf8");
      for (const dependency of source.matchAll(/(?:from\s*|import\s*\(|require\s*\()\s*["']([^"']+)["']/g)) {
        expect(dependency[1], `${layer}/${file}`).not.toMatch(/examples|\.solutions|puzzleCatalog/);
      }
    }
  }
});
