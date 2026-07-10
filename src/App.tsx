import { useEffect, useReducer, useState } from "react";
import { ConstraintsEditor } from "./components/ConstraintsEditor";
import { HiddenRolesEditor } from "./components/HiddenRolesEditor";
import { ImportExportBar } from "./components/ImportExportBar";
import { PuzzleHeader } from "./components/PuzzleHeader";
import { ResultsView } from "./components/ResultsView";
import { DrawWorkbench, PuzzleSheet } from "./components/SeatingChartEditor";
import { initialDoc, initialState, reducer } from "./state/puzzleDoc";
import { useSolver } from "./state/useSolver";

const SOLUTION_LIMIT = 10;
const SOLVE_DEBOUNCE_MS = 250;

export function App() {
  const [state, dispatch] = useReducer(reducer, initialState);
  const { doc, solveError, solveResult } = state;
  const [selectedIndex, setSelectedIndex] = useState(0);
  const { busy, solve } = useSolver();

  useEffect(() => {
    if (doc.players.length === 0 || doc.script.length === 0) {
      dispatch({ type: "solve", status: "cleared", doc });
      return;
    }

    let active = true;
    const timer = window.setTimeout(() => {
      dispatch({ type: "solve", status: "started", doc });
      void solve(doc, SOLUTION_LIMIT).then(
        (worlds) => {
          if (active) dispatch({ type: "solve", status: "succeeded", doc, worlds });
        },
        (error: unknown) => {
          if (!active) return;
          dispatch({
            type: "solve",
            status: "failed",
            doc,
            message: error instanceof Error ? error.message : String(error),
          });
        },
      );
    }, SOLVE_DEBOUNCE_MS);

    return () => {
      active = false;
      window.clearTimeout(timer);
    };
  }, [doc, solve]);

  const handleError = (message: string | undefined) => {
    dispatch(
      message === undefined
        ? { type: "solve", status: "cleared", doc }
        : { type: "solve", status: "failed", doc, message },
    );
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
          <span>BOTC Solver</span>
        </div>
        <ImportExportBar doc={doc} dispatch={dispatch} onError={handleError} />
        <div className="chrome-actions">
          <button type="button" onClick={handleNewPuzzle}>
            New Puzzle
          </button>
        </div>
      </header>

      <div className="solver-workspace">
        <section id="puzzle-editor" className="puzzle-sheet" aria-label="Puzzle sheet editor">
          <div className="sheet-header">
            <PuzzleHeader doc={doc} dispatch={dispatch} />
          </div>
          <PuzzleSheet doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={setSelectedIndex} />
        </section>

        <aside className="workbench" aria-label="Puzzle workbench">
          <div className="workbench-body workbench-stack">
            <HiddenRolesEditor doc={doc} dispatch={dispatch} />
            <DrawWorkbench doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={setSelectedIndex} />
            <ConstraintsEditor doc={doc} dispatch={dispatch} />
            <section id="solutions-panel" className="panel solve-panel" aria-label="Solutions">
              <div className="solve-panel-header">
                <div>
                  <h3>Solutions</h3>
                  <span>{busy ? "Finding solutions…" : "Updates automatically"}</span>
                </div>
                <span className={`solve-status${busy ? " busy" : ""}`} aria-live="polite">
                  {doc.players.length === 0 || doc.script.length === 0 ? "Incomplete" : busy ? "Working" : "Current"}
                </span>
              </div>
              <ResultsView
                worlds={solveResult}
                players={doc.players}
                error={solveError}
                busy={busy}
                limit={SOLUTION_LIMIT}
              />
            </section>
          </div>
        </aside>
      </div>
      <nav className="mobile-section-nav" aria-label="Mobile sections">
        <a href="#puzzle-editor">Puzzle</a>
        <a href="#claims-panel">Claims</a>
        <a href="#event-history">Timeline</a>
        <a href="#solutions-panel">Solutions</a>
      </nav>
    </main>
  );
}
