import { useEffect, useReducer, useState } from "react";
import { ConstraintsEditor } from "./components/ConstraintsEditor";
import { ImportExportBar } from "./components/ImportExportBar";
import { PuzzleHeader } from "./components/PuzzleHeader";
import { DrawWorkbench, PuzzleSheet } from "./components/SeatingChartEditor";
import { ScriptPicker } from "./components/ScriptPicker";
import { WorldsStrip } from "./components/WorldsStrip";
import { initialDoc, initialState, reducer } from "./state/puzzleDoc";
import { canSolve, useLiveSolve, LIVE_SOLVE_WORLD_LIMIT } from "./state/useLiveSolve";
import type { SerializableWorld } from "./worker/protocol";

export function App() {
  const [state, dispatch] = useReducer(reducer, initialState);
  const { doc, solveError, solveResult } = state;
  const [selectedIndex, setSelectedIndex] = useState(0);
  const [pinnedIndex, setPinnedIndex] = useState<number | undefined>(undefined);
  const [previewIndex, setPreviewIndex] = useState<number | undefined>(undefined);
  const { solving } = useLiveSolve(doc, dispatch);

  useEffect(() => {
    setPinnedIndex(undefined);
    setPreviewIndex(undefined);
  }, [doc]);

  const handleNewPuzzle = () => {
    dispatch({ type: "load", doc: initialDoc });
    setSelectedIndex(0);
  };

  const paintedWorld = paintedWorldFor(solveResult, previewIndex, pinnedIndex);

  return (
    <main className="app-shell">
      <header className="app-chrome" aria-label="Application toolbar">
        <div className="brand-lockup">
          <span className="brand-mark" aria-hidden="true">
            ◫
          </span>
          <span>BOTC Puzzle Solver</span>
        </div>
        <ImportExportBar
          doc={doc}
          dispatch={dispatch}
          onError={(message) =>
            dispatch(
              message === undefined
                ? { type: "solve", status: "cleared", doc }
                : { type: "solve", status: "failed", doc, message },
            )
          }
        />
        <div className="chrome-actions">
          <SolveStatusPill doc={doc} solving={solving} worlds={solveResult} error={solveError} />
          <button type="button" onClick={handleNewPuzzle}>
            New Puzzle
          </button>
        </div>
      </header>

      <div className="solver-workspace">
        <aside className="script-rail" aria-label="Script and constraints">
          <ScriptPicker doc={doc} dispatch={dispatch} />
          <ConstraintsEditor doc={doc} dispatch={dispatch} />
        </aside>

        <section className="puzzle-sheet" aria-label="Puzzle sheet editor">
          <div className="sheet-header">
            <PuzzleHeader doc={doc} dispatch={dispatch} />
          </div>
          <PuzzleSheet
            doc={doc}
            dispatch={dispatch}
            selectedIndex={selectedIndex}
            onSelect={setSelectedIndex}
            worlds={solveResult}
            paintedWorld={paintedWorld}
            solving={solving}
          />
        </section>

        <aside className="inspector" aria-label="Selected player inspector">
          <DrawWorkbench doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} />
        </aside>
      </div>

      <WorldsStrip
        worlds={solveResult}
        players={doc.players}
        error={solveError}
        pinnedIndex={pinnedIndex}
        onPin={setPinnedIndex}
        onPreview={setPreviewIndex}
      />
    </main>
  );
}

function paintedWorldFor(
  worlds: readonly SerializableWorld[] | undefined,
  previewIndex: number | undefined,
  pinnedIndex: number | undefined,
): SerializableWorld | undefined {
  if (worlds === undefined) return undefined;
  if (previewIndex !== undefined) return worlds[previewIndex];
  if (pinnedIndex !== undefined) return worlds[pinnedIndex];
  return worlds.length === 1 ? worlds[0] : undefined;
}

function SolveStatusPill({
  doc,
  solving,
  worlds,
  error,
}: {
  doc: Parameters<typeof canSolve>[0];
  solving: boolean;
  worlds: readonly SerializableWorld[] | undefined;
  error: string | undefined;
}) {
  if (!canSolve(doc)) {
    return (
      <span className="solve-pill idle" role="status">
        Add roles to solve
      </span>
    );
  }
  if (error !== undefined) {
    return (
      <span className="solve-pill failed" role="status">
        Solve failed
      </span>
    );
  }
  if (solving || worlds === undefined) {
    return (
      <span className="solve-pill solving" role="status">
        Solving…
      </span>
    );
  }
  if (worlds.length === 0) {
    return (
      <span className="solve-pill contradiction" role="status">
        No worlds
      </span>
    );
  }
  if (worlds.length === 1) {
    return (
      <span className="solve-pill solved" role="status">
        Solved · 1 world
      </span>
    );
  }
  const count = worlds.length >= LIVE_SOLVE_WORLD_LIMIT ? `${worlds.length}+` : worlds.length;
  return (
    <span className="solve-pill open" role="status">
      {count} worlds match
    </span>
  );
}
