import { useState, type Dispatch } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function PlayersEditor({ doc, dispatch }: Props) {
  const [draft, setDraft] = useState("");
  return (
    <section className="panel">
      <h3>Players (seating order)</h3>
      <div className="player-list">
        {doc.players.map((name, i) => (
          <div key={`${i}-${name}`} className="player-row">
            <input
              type="text"
              value={name}
              onChange={(e) => dispatch({ type: "renamePlayer", index: i, name: e.target.value })}
            />
            <div className="row">
              <button onClick={() => dispatch({ type: "movePlayer", index: i, direction: "up" })}>↑</button>
              <button onClick={() => dispatch({ type: "movePlayer", index: i, direction: "down" })}>↓</button>
            </div>
            <button onClick={() => dispatch({ type: "removePlayer", index: i })}>×</button>
          </div>
        ))}
      </div>
      <form
        className="row"
        onSubmit={(e) => {
          e.preventDefault();
          dispatch({ type: "addPlayer", name: draft });
          setDraft("");
        }}
      >
        <input type="text" placeholder="New player" value={draft} onChange={(e) => setDraft(e.target.value)} />
        <button type="submit">Add</button>
      </form>
    </section>
  );
}
