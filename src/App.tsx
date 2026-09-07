import styles from "./App.module.css";
import { useCallback, useEffect, useReducer, useState } from "react";
import { ConstraintsEditor } from "./components/ConstraintsEditor";
import { HiddenRolesEditor } from "./components/HiddenRolesEditor";
import { ImportExportBar } from "./components/ImportExportBar";
import { PuzzleHeader } from "./components/PuzzleHeader";
import { ResultsView } from "./components/ResultsView";
import { RosterEditor } from "./components/RosterEditor";
import { DrawWorkbench, PuzzleSheet } from "./components/SeatingChartEditor";
import { initialDoc, initialState, reducer } from "./state/puzzleDoc";
import { useSolver } from "./state/useSolver";

const SOLUTION_LIMIT = 10;
const SOLVE_DEBOUNCE_MS = 250;

export function App() {
  const [state, dispatch] = useReducer(reducer, initialState);
  const { doc, solveError, solveResult } = state;
  const [selectedIndex, setSelectedIndex] = useState(0);
  const [view, setView] = useState<"roster" | "seating">("seating");
  const [detailsOpen, setDetailsOpen] = useState(false);
  const [mobile, setMobile] = useState(() => window.matchMedia("(max-width: 760px)").matches);
  useEffect(() => {
    const query = window.matchMedia("(max-width: 760px)");
    const update = () => setMobile(query.matches);
    query.addEventListener("change", update);
    return () => query.removeEventListener("change", update);
  }, []);
  const selectPlayer = useCallback((index: number) => {
    setSelectedIndex(index);
    setDetailsOpen(true);
  }, []);
  const { busy, solve, cancel } = useSolver();

  useEffect(() => {
    if (doc.players.length === 0 || doc.script.length === 0) {
      dispatch({ type: "solve", status: "cleared", doc });
      return;
    }

    let active = true;
    const timer = window.setTimeout(() => {
      dispatch({ type: "solve", status: "started", doc });
      void solve(doc, SOLUTION_LIMIT).then(
        ({ worlds, summary }) => {
          if (active) dispatch({ type: "solve", status: "succeeded", doc, worlds, summary });
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
      cancel();
    };
  }, [doc, solve, cancel]);

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
    setView("seating");
    setDetailsOpen(false);
  };

  const renderMobileDetails = mobile
    ? (index: number) =>
        detailsOpen && index === selectedIndex ? (
          <DrawWorkbench
            inline
            doc={doc}
            dispatch={dispatch}
            selectedIndex={selectedIndex}
            onSelect={selectPlayer}
            onClose={() => setDetailsOpen(false)}
          />
        ) : null
    : undefined;

  return (
    <main className={`${styles.root} app-shell editor-redesign view-${view}`}>
      <header className="app-chrome" aria-label="Application toolbar">
        <div className="brand-lockup">
          <span className="brand-mark" aria-hidden="true">
            ◷
          </span>
          <span>
            Clocktower<span className="brand-subtitle">PUZZLE WORKSHOP</span>
          </span>
        </div>
        <ImportExportBar doc={doc} dispatch={dispatch} onError={handleError} />
        <div className="chrome-actions">
          <button type="button" onClick={handleNewPuzzle}>
            New Puzzle
          </button>
        </div>
      </header>
      <div className="workspace-heading">
        <PuzzleHeader doc={doc} dispatch={dispatch} />
        <a className="solution-jump" href="#solutions-panel">
          <span className={`status-dot${busy ? " busy" : ""}`} />
          {busy
            ? "Finding solutions…"
            : solveError
              ? "Check puzzle details"
              : solveResult
                ? `${solveResult.length}${state.solveSummary?.stopped === "limit" ? "+" : ""} possible solution${solveResult.length === 1 ? "" : "s"}`
                : "Ready when you are"}
          <span aria-hidden="true">↗</span>
        </a>
      </div>
      <div className="solver-workspace">
        <section id="puzzle-editor" className="puzzle-sheet" aria-label="Puzzle sheet editor">
          <div className="editor-view-toolbar">
            <div className="view-switch" aria-label="Editor view">
              <button type="button" aria-pressed={view === "roster"} onClick={() => setView("roster")}>
                Roster
              </button>
              <button type="button" aria-pressed={view === "seating"} onClick={() => setView("seating")}>
                Seating chart
              </button>
            </div>
            <div className="overview-actions">
              {view === "seating" && (
                <RosterEditor
                  compact
                  doc={doc}
                  dispatch={dispatch}
                  selectedIndex={selectedIndex}
                  onSelect={selectPlayer}
                />
              )}
              {view === "seating" && (
                <button type="button" onClick={() => setDetailsOpen((open) => !open)} aria-expanded={detailsOpen}>
                  Edit claims
                </button>
              )}
            </div>
          </div>
          {view === "roster" && (
            <RosterEditor
              doc={doc}
              dispatch={dispatch}
              selectedIndex={selectedIndex}
              onSelect={selectPlayer}
              renderDetails={renderMobileDetails}
            />
          )}
          <PuzzleSheet
            doc={doc}
            dispatch={dispatch}
            selectedIndex={selectedIndex}
            onSelect={setSelectedIndex}
            onEdit={selectPlayer}
            renderDetails={view === "seating" ? renderMobileDetails : undefined}
          />
          <HiddenRolesEditor doc={doc} dispatch={dispatch} />
          <div className="overview-conventions">
            <span>
              <strong>Puzzle convention</strong> Good players report honestly. Evil players claim a different character.
            </span>
            <span>The game continues after the last event.</span>
            {[
              ...new Set(
                doc.claims
                  .filter((claim) => claim.possibleActualRoles?.length)
                  .map((claim) => `${claim.name}: ${claim.possibleActualRoles!.join(" or ")}`),
              ),
            ].map((restriction) => (
              <span key={restriction}>
                <strong>Actual character</strong> {restriction}
              </span>
            ))}
          </div>
          <ConstraintsEditor doc={doc} dispatch={dispatch} />
        </section>

        {!mobile && (
          <aside
            className={`workbench${detailsOpen ? " inspector-open" : ""}`}
            aria-label="Puzzle workbench"
            onKeyDown={(event) => {
              if (event.key === "Escape") setDetailsOpen(false);
            }}
          >
            <button
              className="close-inspector"
              type="button"
              aria-label="Close claim editor"
              onClick={() => setDetailsOpen(false)}
            >
              Done <span aria-hidden="true">×</span>
            </button>
            <div className="workbench-body workbench-stack">
              <DrawWorkbench doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={selectPlayer} />
              <p className="convention-note">
                Puzzle convention: good players report honestly; evil players claim a different character. Add only the
                observations you know.
              </p>
            </div>
          </aside>
        )}
      </div>
      <section id="solutions-panel" className="panel solve-panel" aria-label="Solutions">
        <div className="solve-panel-header">
          <div>
            <h3>Solutions</h3>
            <span>{busy ? "Finding solutions…" : "Updates automatically"}</span>
          </div>
          <span className={`solve-status${busy ? " busy" : ""}`} aria-live="polite">
            {doc.players.length === 0 || doc.script.length === 0
              ? "Incomplete"
              : busy
                ? "Working"
                : solveError
                  ? "Needs attention"
                  : "Current"}
          </span>
        </div>
        <ResultsView
          worlds={solveResult}
          summary={state.solveSummary}
          players={doc.players}
          error={solveError}
          busy={busy}
          limit={SOLUTION_LIMIT}
        />
      </section>
      <nav className="mobile-section-nav" aria-label="Mobile sections">
        <a href="#puzzle-editor">Puzzle</a>
        <a href="#claims-panel" onClick={() => setDetailsOpen(true)}>
          Claims
        </a>
        <a href="#event-history">Timeline</a>
        <a href="#solutions-panel">Solutions</a>
      </nav>
    </main>
  );
}
