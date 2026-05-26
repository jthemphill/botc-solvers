import type { SerializableWorld } from "../worker/protocol";

interface Props {
  worlds: readonly SerializableWorld[] | undefined;
  error: string | undefined;
}

export function ResultsView({ worlds, error }: Props) {
  if (error)
    return (
      <section className="panel">
        <h3>Results</h3>
        <pre className="error" style={{ whiteSpace: "pre-wrap" }}>
          {error}
        </pre>
      </section>
    );
  if (worlds === undefined)
    return (
      <section className="panel">
        <h3>Results</h3>
        <p>Press Solve to compute satisfying worlds.</p>
      </section>
    );
  return (
    <section className="panel">
      <h3>Results — {worlds.length} satisfying world(s)</h3>
      {worlds.length === 0 && <p>No worlds — the constraints are unsatisfiable.</p>}
      {worlds.map((w, i) => (
        <div key={i}>
          <div className="world-header">World {i + 1}</div>
          <table className="results">
            <thead>
              <tr>
                <th>Player</th>
                <th>Actual</th>
                <th>Apparent</th>
                <th>Poisoned</th>
                <th>Drunk</th>
              </tr>
            </thead>
            <tbody>
              {w.players.map((player) => {
                const actual = w.actual.find(([p]) => p === player)?.[1];
                const apparent = w.apparent.find(([p]) => p === player)?.[1];
                return (
                  <tr key={player}>
                    <td>{player}</td>
                    <td>{actual}</td>
                    <td>{apparent && apparent !== actual ? apparent : ""}</td>
                    <td>{w.poisoned.includes(player) ? "✓" : ""}</td>
                    <td>{w.drunk.includes(player) ? "✓" : ""}</td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
      ))}
    </section>
  );
}
