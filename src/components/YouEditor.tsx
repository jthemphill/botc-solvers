import type { Dispatch } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function YouEditor({ doc, dispatch }: Props) {
  const enabled = doc.you !== undefined;
  return (
    <section className="panel">
      <h3>Fix "You" role (optional)</h3>
      <label>
        <input
          type="checkbox"
          checked={enabled}
          onChange={(e) =>
            dispatch({
              type: "setYou",
              you: e.target.checked
                ? { name: doc.you?.name ?? doc.players[0] ?? "", role: doc.you?.role ?? doc.script[0] ?? "" }
                : undefined,
            })
          }
        />{" "}
        Fix one player's actual role
      </label>
      {enabled && doc.you && (
        <div className="field-grid">
          <span>Player</span>
          <select
            value={doc.you.name}
            onChange={(e) => dispatch({ type: "setYou", you: { ...doc.you!, name: e.target.value } })}
          >
            <option value="">—</option>
            {doc.players.map((p) => (
              <option key={p} value={p}>
                {p}
              </option>
            ))}
          </select>
          <span>Role</span>
          <select
            value={doc.you.role}
            onChange={(e) => dispatch({ type: "setYou", you: { ...doc.you!, role: e.target.value } })}
          >
            <option value="">—</option>
            {doc.script.map((r) => (
              <option key={r} value={r}>
                {r}
              </option>
            ))}
          </select>
        </div>
      )}
    </section>
  );
}
