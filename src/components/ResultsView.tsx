import styles from "./ResultsView.module.css";
import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import type { SerializableWorld, SolveSummary } from "../worker/protocol";

interface Props {
  summary?: SolveSummary;
  worlds: readonly SerializableWorld[] | undefined;
  players: readonly string[];
  error: string | undefined;
  busy?: boolean;
  limit?: number;
}

export function ResultsView({ summary, worlds, players, error, busy = false, limit }: Props) {
  if (error)
    return (
      <div className={`${styles.root} results-view`}>
        <p className="error" role="alert">
          {error.split("\n")[0]}
        </p>
        {error.includes("\n") && (
          <details>
            <summary>Error details</summary>
            <pre className="error" style={{ whiteSpace: "pre-wrap" }}>
              {error}
            </pre>
          </details>
        )}
      </div>
    );
  if (worlds === undefined)
    return (
      <div className={`${styles.root} results-view empty-results`}>
        <p>{busy ? "Finding satisfying worlds…" : "Add a claimed or hidden role to generate solutions."}</p>
      </div>
    );
  return (
    <div className={`${styles.root} results-view`}>
      <div className="results-count">
        Satisfying worlds: <strong>{worlds.length}</strong>
      </div>
      {summary?.stopped === "limit" && limit !== undefined && (
        <p className="results-limit">Showing the first {limit} solutions. The puzzle may have more.</p>
      )}
      {summary?.status === "unknown" && <p role="status">Search incomplete: {summary.reason}</p>}
      {worlds.length === 0 && summary?.status !== "unknown" && (
        <p>No worlds — the encoded constraints are unsatisfiable.</p>
      )}
      {summary && (
        <>
          <p className="coverage-notice">
            Rule coverage is incomplete. Night action order, life state, and victory rules have partial support.
          </p>
          <p>{summary.complete ? "All initial character assignments enumerated." : "Enumeration incomplete."}</p>
          <details>
            <summary>Search details</summary>
            <p>
              {summary.metrics.variables.toLocaleString()} variables · {summary.metrics.clauses.toLocaleString()}{" "}
              clauses · {Math.round(summary.buildMs + summary.metrics.finalizeMs + summary.metrics.solveMs)} ms
            </p>
          </details>
        </>
      )}
      {worlds.map((w, i) => (
        <article key={i} className="solution-card">
          <header>
            <strong>Solution {i + 1}</strong>
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
          {w.trace && (
            <details>
              <summary>Character changes and hidden choices</summary>
              {w.trace.transitions.length === 0 ? (
                <p>No character changes.</p>
              ) : (
                <ul>
                  {w.trace.transitions.map((change, index) => (
                    <li key={index}>
                      {change.timing}: {change.player} becomes {change.character} ({change.rule})
                    </li>
                  ))}
                </ul>
              )}
              <ul>
                {w.actions
                  ?.filter((action) => action.active)
                  .map((action, index) => (
                    <li key={index}>
                      {action.timing}: {action.actor}, {action.rule} — {action.selected.join(", ")}
                    </li>
                  ))}
              </ul>
            </details>
          )}
        </article>
      ))}
    </div>
  );
}
