import { createHash } from "node:crypto";
import { cpus } from "node:os";
import { parseArgs } from "node:util";
import { buildFromDoc } from "../src/builders/buildFromDoc";
import { PUZZLE_EXAMPLES } from "../src/examples/puzzleCatalog";
import { KissatBackend, type SatBackend } from "../src/model/sat";
import { validatePuzzleDoc } from "../src/schema/validate";

const { values } = parseArgs({
  args: Bun.argv.slice(2),
  options: {
    runs: { type: "string", default: "3" },
    warmup: { type: "string", default: "1" },
    filter: { type: "string", default: "" },
    output: { type: "string" },
    compare: { type: "string" },
  },
});
const runs = Number(values.runs);
const warmup = Number(values.warmup);
if (!Number.isInteger(runs) || runs < 1 || !Number.isInteger(warmup) || warmup < 0)
  throw new Error("Use a positive run count and a nonnegative warmup count.");
const examples = PUZZLE_EXAMPLES.filter(({ id }) => id.includes(values.filter));
if (examples.length === 0) throw new Error("No puzzles match the filter.");
const initializationStarted = performance.now();
const kissat = await KissatBackend.create();
const initializationMs = performance.now() - initializationStarted;
let backendMs = 0;
const backend: SatBackend = {
  async solve(problem) {
    const started = performance.now();
    const result = await kissat.solve(problem);
    backendMs += performance.now() - started;
    return result;
  },
};

async function measure(example: (typeof examples)[number]) {
  backendMs = 0;
  const started = performance.now();
  const doc = validatePuzzleDoc(example.data);
  const game = buildFromDoc(doc, backend);
  const buildMs = performance.now() - started;
  const report = await game.solve();
  const totalMs = performance.now() - started;
  if (!report.complete) throw new Error(`${example.id}: enumeration did not finish (${report.stopped}).`);
  const assignments = report.worlds.map((world) => JSON.stringify(doc.players.map((p) => world.actualRole(p))));
  assignments.sort();
  return {
    id: example.id,
    status: report.status,
    complete: report.complete,
    worlds: report.worlds.length,
    assignmentHash: createHash("sha256").update(JSON.stringify(assignments)).digest("hex"),
    buildMs,
    ...report.metrics,
    backendMs,
    totalMs,
  };
}

const samples: (Awaited<ReturnType<typeof measure>> & { run: number })[] = [];
for (let run = -warmup; run < runs; run += 1) {
  const started = performance.now();
  for (const example of examples) {
    const result = await measure(example);
    if (run >= 0) samples.push({ run: run + 1, ...result });
  }
  console.error(`${run < 0 ? "Warmup" : `Run ${run + 1}`}: ${(performance.now() - started).toFixed(0)} ms`);
}

function median(numbers: number[]): number {
  const sorted = [...numbers].sort((a, b) => a - b);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 ? sorted[middle]! : (sorted[middle - 1]! + sorted[middle]!) / 2;
}

const timingKeys = ["buildMs", "finalizeMs", "solveMs", "backendMs", "totalMs"] as const;
const results = examples.map(({ id }) => {
  const matching = samples.filter((sample) => sample.id === id);
  const { run: _, ...first } = matching[0]!;
  if (matching.some((sample) => sample.assignmentHash !== first.assignmentHash))
    throw new Error(`${id}: role assignments changed between runs.`);
  return { ...first, ...Object.fromEntries(timingKeys.map((key) => [key, median(matching.map((s) => s[key]))])) };
});
let comparison;
if (values.compare) {
  const reference = (await Bun.file(values.compare).json()) as { results: typeof results };
  const previous = new Map(reference.results.map((result) => [result.id, result]));
  comparison = results.map((result) => {
    const before = previous.get(result.id);
    if (!before) throw new Error(`${result.id}: missing from the comparison report.`);
    if (
      before.assignmentHash !== result.assignmentHash ||
      before.status !== result.status ||
      before.complete !== result.complete ||
      before.worlds !== result.worlds
    )
      throw new Error(`${result.id}: role assignments or enumeration status changed.`);
    return {
      id: result.id,
      totalSpeedup: before.totalMs / result.totalMs,
      backendSpeedup: before.backendMs / result.backendMs,
    };
  });
}
const report = {
  environment: { bun: Bun.version, platform: process.platform, arch: process.arch, cpu: cpus()[0]?.model },
  backend: "Bundled Kissat; a new solver for each backend call",
  runs,
  warmup,
  initializationMs,
  puzzleCount: examples.length,
  summary: {
    worlds: results.reduce((sum, result) => sum + result.worlds, 0),
    variables: results.reduce((sum, result) => sum + result.variables, 0),
    clauses: results.reduce((sum, result) => sum + result.clauses, 0),
    ...Object.fromEntries(timingKeys.map((key) => [key, results.reduce((sum, result) => sum + result[key], 0)])),
  },
  results,
  samples,
  comparison,
};
const json = JSON.stringify(report, null, 2) + "\n";
if (values.output) await Bun.write(values.output, json);
else console.log(json);
console.error(JSON.stringify(report.summary, null, 2));
