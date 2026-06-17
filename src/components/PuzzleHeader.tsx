import type { CSSProperties, Dispatch } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function PuzzleHeader({ doc, dispatch }: Props) {
  const title = doc.title ?? "";
  const titleStyle = {
    "--title-scale": Math.min(1, 24 / Math.max(title.length, 1)).toFixed(3),
  } as CSSProperties;

  return (
    <div className="puzzle-title-editor">
      <span className="puzzle-number">Puzzle Sheet</span>
      <label>
        <span className="sr-only">Title</span>
        <input
          className="title-input"
          type="text"
          value={title}
          style={titleStyle}
          onChange={(e) => dispatch({ type: "setTitle", title: e.target.value })}
        />
      </label>
      <span className="puzzle-counts">
        {doc.players.length} players · {doc.script.length} roles · {doc.claims.length} claims
      </span>
    </div>
  );
}
