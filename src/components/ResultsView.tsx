import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import type { SerializableWorld } from "../worker/protocol";

interface Props {
  worlds: readonly SerializableWorld[] | undefined;
  players: readonly string[];
  error: string | undefined;
}

export function ResultsView({ worlds, players, error }: Props) {
  if (error)
    return (
      <div className="results-view">
        <pre className="error" style={{ whiteSpace: "pre-wrap" }}>
          {error}
        </pre>
      </div>
    );
  if (worlds === undefined)
    return (
      <div className="results-view empty-results">
        <p>Press Solve to compute satisfying worlds.</p>
      </div>
    );
  return (
    <div className="results-view">
      <div className="results-count">
        Satisfying worlds: <strong>{worlds.length}</strong>
      </div>
      {worlds.length === 0 && <p>No worlds — the constraints are unsatisfiable.</p>}
      {worlds.map((w, i) => (
        <article key={i} className="solution-card">
          <header>
            <strong>Solution {i + 1}</strong>
            <span>100%</span>
          </header>
          <div className="solution-strip">
            {players.map((player) => {
              const actual = w.actual.find(([p]) => p === player)?.[1];
              const apparent = w.apparent.find(([p]) => p === player)?.[1];
              const isLying = actual !== undefined && apparent !== undefined && actual !== apparent;
              const actualLabel = roleEmojiLabel(actual);
              const apparentLabel = roleEmojiLabel(apparent);
              return (
                <div
                  key={player}
                  className={`solution-token${isLying ? " lying" : ""}`}
                  title={isLying ? `Actual: ${actualLabel}; Claimed: ${apparentLabel}` : actualLabel}
                  aria-label={`${player}: ${actual ?? "Unknown"}${isLying ? `, claimed ${apparent}` : ""}`}
                >
                  <span className="solution-role" aria-hidden="true">
                    {roleEmoji(actual) ?? "?"}
                  </span>
                  <strong>{player}</strong>
                  <small>{actualLabel}</small>
                  <span className="solution-flags">
                    {w.poisoned.includes(player) && <span>Poisoned</span>}
                    {w.drunk.includes(player) && <span>Drunk</span>}
                  </span>
                </div>
              );
            })}
          </div>
        </article>
      ))}
    </div>
  );
}
