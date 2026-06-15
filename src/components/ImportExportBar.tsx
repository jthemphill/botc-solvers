import { useRef, type Dispatch } from "react";
import { PUZZLE_EXAMPLES } from "../examples/puzzleCatalog";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { validatePuzzleDoc } from "../schema/validate";
import type { PuzzleAction } from "../state/puzzleDoc";

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
    <section className="import-export-bar" aria-label="Import, export, and examples">
      <div className="toolbar-button-row">
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
      <div className="example-picker-row">
        <label>
          <span>Examples</span>
          <select
            aria-label="Load example puzzle"
            value=""
            onChange={(e) => {
              const example = PUZZLE_EXAMPLES.find((entry) => entry.id === e.target.value);
              if (example !== undefined) importData(example.data);
            }}
          >
            <option value="">Load puzzle...</option>
            {PUZZLE_EXAMPLES.map((example) => (
              <option key={example.id} value={example.id}>
                {example.label}
              </option>
            ))}
          </select>
        </label>
      </div>
    </section>
  );
}
