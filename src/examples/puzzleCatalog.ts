import generatedCatalog from "./puzzleCatalog.generated.json";
import puzzle01 from "./puzzle-01-sober-savant.json";
import puzzle05a from "./puzzle-05a-you-only-guess-twice.json";
import puzzle05b from "./puzzle-05b-you-only-guess-twice.json";
import puzzle34 from "./puzzle-34-the-vortox-conjecture.json";
import puzzleIntro from "./puzzle-intro-chef-empath.json";

export interface PuzzleExample {
  readonly id: string;
  readonly label: string;
  readonly data: unknown;
}

interface GeneratedCatalogEntry {
  readonly id: string;
  readonly label: string;
  readonly doc: unknown;
}

const HAND_AUTHORED_DOCS = new Map<string, unknown>([
  ["puzzle-01-sober-savant", puzzle01],
  ["puzzle-05a-you-only-guess-twice", puzzle05a],
  ["puzzle-05b-you-only-guess-twice", puzzle05b],
  ["puzzle-34-the-vortox-conjecture", puzzle34],
]);

function titleOf(data: unknown): string | undefined {
  return typeof data === "object" &&
    data !== null &&
    "title" in data &&
    typeof (data as { readonly title?: unknown }).title === "string"
    ? (data as { readonly title: string }).title
    : undefined;
}

const generatedExamples = (generatedCatalog as readonly GeneratedCatalogEntry[]).map((entry) => {
  const data = HAND_AUTHORED_DOCS.get(entry.id) ?? entry.doc;
  return {
    id: entry.id,
    label: titleOf(data) ?? entry.label,
    data,
  };
});

export const PUZZLE_EXAMPLES: readonly PuzzleExample[] = [
  { id: "intro", label: titleOf(puzzleIntro) ?? "Intro - Chef + Empath", data: puzzleIntro },
  ...generatedExamples,
];
