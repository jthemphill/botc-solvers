import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import { LIVE_SOLVE_WORLD_LIMIT } from "../state/useLiveSolve";
import type { SerializableWorld } from "../worker/protocol";

interface Props {
  worlds: readonly SerializableWorld[] | undefined;
  players: readonly string[];
  error: string | undefined;
  pinnedIndex: number | undefined;
  onPin: (index: number | undefined) => void;
  onPreview: (index: number | undefined) => void;
}

export function WorldsStrip({ worlds, players, error, pinnedIndex, onPin, onPreview }: Props) {
  if (error !== undefined) {
    return (
      <section className="worlds-strip" aria-label="Satisfying worlds">
        <header className="worlds-strip-header">
          <h3>Worlds</h3>
          <span className="worlds-strip-note">Solve failed</span>
        </header>
        <pre className="error" style={{ whiteSpace: "pre-wrap" }}>
          {error}
        </pre>
      </section>
    );
  }

  if (worlds === undefined) {
    return (
      <section className="worlds-strip" aria-label="Satisfying worlds">
        <header className="worlds-strip-header">
          <h3>Worlds</h3>
          <span className="worlds-strip-note">
            Worlds that satisfy every claim appear here as you enter the puzzle.
          </span>
        </header>
      </section>
    );
  }

  const capped = worlds.length >= LIVE_SOLVE_WORLD_LIMIT;

  return (
    <section className="worlds-strip" aria-label="Satisfying worlds">
      <header className="worlds-strip-header">
        <h3>Worlds</h3>
        <span className="results-count">
          Satisfying worlds: <strong>{capped ? `${worlds.length}+` : worlds.length}</strong>
        </span>
        {worlds.length === 0 && <span className="worlds-strip-note">No worlds — the claims are contradictory.</span>}
        {capped && <span className="worlds-strip-note">Showing the first {LIVE_SOLVE_WORLD_LIMIT}.</span>}
        {pinnedIndex !== undefined && (
          <button type="button" className="unpin-button" onClick={() => onPin(undefined)}>
            Unpin world
          </button>
        )}
      </header>
      <div className="worlds-strip-cards">
        {worlds.map((world, index) => (
          <WorldCard
            key={index}
            world={world}
            index={index}
            players={players}
            pinned={index === pinnedIndex}
            onPin={() => onPin(index === pinnedIndex ? undefined : index)}
            onPreview={onPreview}
          />
        ))}
      </div>
    </section>
  );
}

function WorldCard({
  world,
  index,
  players,
  pinned,
  onPin,
  onPreview,
}: {
  world: SerializableWorld;
  index: number;
  players: readonly string[];
  pinned: boolean;
  onPin: () => void;
  onPreview: (index: number | undefined) => void;
}) {
  return (
    <article
      className={`solution-card${pinned ? " pinned" : ""}`}
      onMouseEnter={() => onPreview(index)}
      onMouseLeave={() => onPreview(undefined)}
    >
      <header>
        <strong>Solution {index + 1}</strong>
        <button
          type="button"
          className="pin-button"
          aria-pressed={pinned}
          onClick={onPin}
          title={pinned ? "Unpin this world" : "Pin this world onto the seating chart"}
        >
          {pinned ? "Pinned" : "Pin"}
        </button>
      </header>
      <div className="solution-strip">
        {players.map((player) => {
          const actual = world.actual.find(([p]) => p === player)?.[1];
          const apparent = world.apparent.find(([p]) => p === player)?.[1];
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
                {world.poisoned.includes(player) && <span>Poisoned</span>}
                {world.drunk.includes(player) && <span>Drunk</span>}
              </span>
            </div>
          );
        })}
      </div>
    </article>
  );
}
