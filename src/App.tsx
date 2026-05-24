import { useReducer, useState } from "react";
import { FixedRolesEditor } from "./components/FixedRolesEditor";
import { ImportExportBar } from "./components/ImportExportBar";
import { PuzzleHeader } from "./components/PuzzleHeader";
import { ResultsView } from "./components/ResultsView";
import { SeatingChartEditor } from "./components/SeatingChartEditor";
import { ScriptPicker } from "./components/ScriptPicker";
import { initialDoc, reducer } from "./state/puzzleDoc";
import { useSolver } from "./state/useSolver";
import type { SerializableWorld } from "./worker/protocol";

export function App() {
  const [doc, dispatch] = useReducer(reducer, initialDoc);
  const [worlds, setWorlds] = useState<readonly SerializableWorld[] | undefined>(undefined);
  const [error, setError] = useState<string | undefined>(undefined);
  const { busy, solve } = useSolver();

  const handleSolve = async () => {
    setError(undefined);
    setWorlds(undefined);
    try {
      const result = await solve(doc);
      setWorlds(result);
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e));
    }
  };

  // Examples are served from the public folder copy below; copy synced from src/examples by Vite.
  // (See ImportExportBar — examples are fetched at runtime, not bundled.)

  return (
    <main className="app">
      <div style={{ display: "flex", flexDirection: "column", gap: "1rem" }}>
        <section className="panel">
          <h2>BOTC Puzzle Solver</h2>
          <PuzzleHeader doc={doc} dispatch={dispatch} />
          <div className="row">
            <button onClick={handleSolve} disabled={busy || doc.players.length === 0 || doc.script.length === 0}>
              {busy ? "Solving…" : "Solve"}
            </button>
          </div>
        </section>
        <ImportExportBar doc={doc} dispatch={dispatch} onError={setError} />
        <SeatingChartEditor doc={doc} dispatch={dispatch} />
        <ScriptPicker doc={doc} dispatch={dispatch} />
        <FixedRolesEditor doc={doc} dispatch={dispatch} />
      </div>
      <div style={{ display: "flex", flexDirection: "column", gap: "1rem" }}>
        <ResultsView worlds={worlds} error={error} />
      </div>
    </main>
  );
}
