import { expect, test } from "@playwright/test";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { validatePuzzleDoc } from "../../src/schema/validate";
import { comparableDoc, enterPuzzle, exportPuzzleDoc } from "./editor-helpers";

// This run builds each catalog puzzle in the editor and compares the export with the source document.
// It is slow, so it runs only on request: CATALOG_ENTRY=1 bun run test:e2e -- tests/e2e/catalog-entry.spec.ts
test.skip(process.env["CATALOG_ENTRY"] !== "1", "Set CATALOG_ENTRY=1 to build each catalog puzzle in the editor.");

const EXAMPLES = join(import.meta.dirname, "..", "..", "src", "examples");
const files = readdirSync(EXAMPLES).filter((file) => file.endsWith(".json") && !file.endsWith(".solutions.json"));

for (const file of files.sort()) {
  test(`builds ${file.replace(".json", "")} in the editor`, async ({ page }) => {
    test.setTimeout(45_000);
    const source: unknown = JSON.parse(readFileSync(join(EXAMPLES, file), "utf8"));
    const doc = JSON.parse(JSON.stringify(validatePuzzleDoc(source)));
    await enterPuzzle(page, doc);
    expect(comparableDoc(await exportPuzzleDoc(page))).toEqual(comparableDoc(doc));
  });
}
