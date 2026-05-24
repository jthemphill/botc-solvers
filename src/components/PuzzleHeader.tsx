import type { Dispatch } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function PuzzleHeader({ doc, dispatch }: Props) {
  return (
    <div className="row">
      <label>
        Title{" "}
        <input
          type="text"
          value={doc.title ?? ""}
          onChange={(e) => dispatch({ type: "setTitle", title: e.target.value })}
          style={{ width: "20rem" }}
        />
      </label>
      <span style={{ opacity: 0.6 }}>
        {doc.players.length} players · {doc.script.length} roles · {doc.claims.length} claims
      </span>
    </div>
  );
}
