import { useReducer, useState } from "react";
import { ClaimsEditor } from "./components/ClaimsEditor";
import { FixedRolesEditor } from "./components/FixedRolesEditor";
import { ImportExportBar } from "./components/ImportExportBar";
import { PuzzleHeader } from "./components/PuzzleHeader";
import { ResultsView } from "./components/ResultsView";
import { DrawWorkbench, PuzzleSheet } from "./components/SeatingChartEditor";
import { ScriptPicker } from "./components/ScriptPicker";
import { initialDoc, initialState, reducer } from "./state/puzzleDoc";
import { useSolver } from "./state/useSolver";

type WorkbenchTab = "draw" | "script" | "claims" | "solve";

const WORKBENCH_TABS: Array<{ id: WorkbenchTab; label: string; icon: string }> = [
  { id: "draw", label: "Draw", icon: "✎" },
  { id: "script", label: "Script", icon: "▦" },
  { id: "claims", label: "Claims", icon: "◈" },
  { id: "solve", label: "Solve", icon: "▶" },
];

export function App() {
  const [state, dispatch] = useReducer(reducer, initialState);
  const { doc, solveError, solveResult } = state;
  const [selectedIndex, setSelectedIndex] = useState(0);
  const [activeTab, setActiveTab] = useState<WorkbenchTab>("draw");
  const { busy, solve } = useSolver();

  const handleError = (message: string | undefined) => {
    dispatch(
      message === undefined
        ? { type: "solve", status: "cleared", doc }
        : { type: "solve", status: "failed", doc, message },
    );
  };

  const handleSolve = async () => {
    const solveDoc = doc;
    dispatch({ type: "solve", status: "started", doc: solveDoc });
    try {
      const result = await solve(solveDoc);
      dispatch({ type: "solve", status: "succeeded", doc: solveDoc, worlds: result });
    } catch (e) {
      dispatch({ type: "solve", status: "failed", doc: solveDoc, message: e instanceof Error ? e.message : String(e) });
    }
  };

  const handleNewPuzzle = () => {
    dispatch({ type: "load", doc: initialDoc });
    setSelectedIndex(0);
  };

  return (
    <main className="app-shell">
      <header className="app-chrome" aria-label="Application toolbar">
        <div className="brand-lockup">
          <span className="brand-mark" aria-hidden="true">
            ◫
          </span>
          <span>BOTC Puzzle Solver</span>
        </div>
        <ImportExportBar doc={doc} dispatch={dispatch} onError={handleError} />
        <div className="chrome-actions">
          <button type="button" onClick={handleNewPuzzle}>
            New Puzzle
          </button>
          <button
            type="button"
            className="primary-action"
            onClick={handleSolve}
            disabled={busy || doc.players.length === 0 || doc.script.length === 0}
          >
            {busy ? "Solving…" : "Solve"}
          </button>
        </div>
      </header>

      <div className="solver-workspace">
        <section className="puzzle-sheet" aria-label="Puzzle sheet editor">
          <div className="sheet-header">
            <PuzzleHeader doc={doc} dispatch={dispatch} />
          </div>
          <PuzzleSheet doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={setSelectedIndex} />
        </section>

        <aside className="workbench" aria-label="Puzzle workbench">
          <nav className="workbench-tabs" aria-label="Workbench sections">
            {WORKBENCH_TABS.map((tab) => (
              <button
                key={tab.id}
                type="button"
                className={activeTab === tab.id ? "active" : undefined}
                onClick={() => setActiveTab(tab.id)}
              >
                <span aria-hidden="true">{tab.icon}</span>
                {tab.label}
              </button>
            ))}
          </nav>
          <div className="workbench-body">
            {activeTab === "draw" && <DrawWorkbench doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} />}
            {activeTab === "script" && (
              <>
                <ScriptPicker doc={doc} dispatch={dispatch} />
                <FixedRolesEditor doc={doc} dispatch={dispatch} />
              </>
            )}
            {activeTab === "claims" && <ClaimsEditor doc={doc} dispatch={dispatch} />}
            {activeTab === "solve" && (
              <section className="panel solve-panel">
                <div className="solve-panel-header">
                  <div>
                    <h3>Solve Results</h3>
                    <span>
                      {doc.players.length} players · {doc.script.length} roles · {doc.claims.length} claims
                    </span>
                  </div>
                  <button
                    type="button"
                    className="primary-action"
                    onClick={handleSolve}
                    disabled={busy || doc.players.length === 0 || doc.script.length === 0}
                  >
                    {busy ? "Solving…" : "Solve"}
                  </button>
                </div>
                <ResultsView worlds={solveResult} players={doc.players} error={solveError} />
              </section>
            )}
          </div>
        </aside>
      </div>
    </main>
  );
}
