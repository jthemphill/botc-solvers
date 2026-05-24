import { useRef, type Dispatch } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { validatePuzzleDoc } from "../schema/validate";
import type { PuzzleAction } from "../state/puzzleDoc";
import puzzle01 from "../examples/puzzle-01-sober-savant.json";
import puzzle05a from "../examples/puzzle-05a-you-only-guess-twice.json";
import puzzle05b from "../examples/puzzle-05b-you-only-guess-twice.json";
import puzzleIntro from "../examples/puzzle-intro-chef-empath.json";

const EXAMPLES: Array<{ label: string; data: unknown }> = [
  { label: "Intro — Chef + Empath", data: puzzleIntro },
  { label: "Puzzle 1 — Sober Savant", data: puzzle01 },
  { label: "Puzzle 5a — You Only Guess Twice", data: puzzle05a },
  { label: "Puzzle 5b — You Only Guess Twice", data: puzzle05b },
];

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
  onError: (message: string | undefined) => void;
}

export function ImportExportBar({ doc, dispatch, onError }: Props) {
  const fileRef = useRef<HTMLInputElement>(null);

  const importFile = async (file: File) => {
    try {
      const text = await file.text();
      const parsed = validatePuzzleDoc(JSON.parse(text));
      dispatch({ type: "load", doc: parsed });
      onError(undefined);
    } catch (e) {
      onError(e instanceof Error ? e.message : String(e));
    }
  };

  const importData = (data: unknown) => {
    try {
      const parsed = validatePuzzleDoc(data);
      dispatch({ type: "load", doc: parsed });
      onError(undefined);
    } catch (e) {
      onError(e instanceof Error ? e.message : String(e));
    }
  };

  const exportFile = () => {
    const blob = new Blob([JSON.stringify(doc, null, 2)], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `${(doc.title ?? "puzzle").toLowerCase().replace(/[^a-z0-9]+/g, "-")}.json`;
    a.click();
    URL.revokeObjectURL(url);
  };

  return (
    <section className="panel">
      <h3>Import / Export</h3>
      <div className="row">
        <button onClick={() => fileRef.current?.click()}>Import JSON…</button>
        <input
          ref={fileRef}
          type="file"
          accept="application/json"
          style={{ display: "none" }}
          onChange={(e) => {
            const file = e.target.files?.[0];
            if (file) importFile(file);
            e.target.value = "";
          }}
        />
        <button onClick={exportFile}>Export JSON</button>
      </div>
      <div className="row">
        <span>Examples:</span>
        {EXAMPLES.map((ex) => (
          <button key={ex.label} onClick={() => importData(ex.data)}>
            {ex.label}
          </button>
        ))}
      </div>
    </section>
  );
}
