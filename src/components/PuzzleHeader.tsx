import type { Dispatch } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function PuzzleHeader({ doc, dispatch }: Props) {
  return (
    <div className="puzzle-title-editor">
      <span className="puzzle-number">Puzzle Sheet</span>
      <label>
        <span className="sr-only">Title</span>
        <input
          className="title-input"
          type="text"
          value={doc.title ?? ""}
          onChange={(e) => dispatch({ type: "setTitle", title: e.target.value })}
        />
      </label>
      <span className="puzzle-counts">
        {doc.players.length} players · {doc.script.length} roles · {doc.claims.length} claims
      </span>
    </div>
  );
}
