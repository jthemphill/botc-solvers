import { useEffect, useState, type CSSProperties, type Dispatch } from "react";
import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import type { Claim, PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { CLAIM_TYPES, ClaimBody, makeEmptyClaim } from "./ClaimsEditor";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function SeatingChartEditor({ doc, dispatch }: Props) {
  const players = doc.players;
  const [selectedIndex, setSelectedIndex] = useState(0);
  const [newType, setNewType] = useState<Claim["type"]>("Investigator");

  useEffect(() => {
    if (selectedIndex >= players.length) setSelectedIndex(Math.max(0, players.length - 1));
  }, [players.length, selectedIndex]);

  const selectedName = players[selectedIndex];
  const selectedPlayerIndex = selectedName === undefined ? -1 : doc.players.indexOf(selectedName);
  const selectedClaims = selectedName === undefined ? [] : claimIndexesForPlayer(doc, selectedName);

  const leftNeighbor = selectedName === undefined ? undefined : players[(selectedIndex + 1) % players.length];
  const rightNeighbor =
    selectedName === undefined ? undefined : players[(selectedIndex - 1 + players.length) % players.length];

  const addClaim = () => {
    if (selectedName === undefined) return;
    dispatch({ type: "addClaim", claim: makeEmptyClaim(newType, selectedName) });
  };

  return (
    <section className="panel seating-panel">
      <div className="seating-header">
        <h3>Seating & Claims</h3>
        <label>
          Players
          <input
            type="number"
            min={0}
            max={20}
            value={doc.players.length}
            onChange={(event) => dispatch({ type: "setPlayerCount", count: Number(event.target.value) })}
          />
        </label>
      </div>
      <div className="seating-layout">
        <div className="seating-chart" aria-label="Clockwise seating chart">
          <div className="seating-ring" />
          {players.map((player, index) => {
            const roleClaims = claimIndexesForPlayer(doc, player);
            const roleLabels = roleClaims.map(([claim]) => roleEmojiLabel(claim.type));
            return (
              <button
                key={player}
                type="button"
                className={`seat-button${index === selectedIndex ? " selected" : ""}`}
                style={seatPosition(index, players.length)}
                onClick={() => setSelectedIndex(index)}
                aria-pressed={index === selectedIndex}
              >
                <span>{player}</span>
                <small
                  className="seat-role-claims"
                  aria-label={roleLabels.length === 0 ? "No claims" : `Claims: ${roleLabels.join(", ")}`}
                  title={roleLabels.join(", ")}
                >
                  {roleClaims.map(([claim, claimIndex]) => (
                    <span key={claimIndex} aria-hidden="true">
                      {roleEmoji(claim.type)}
                    </span>
                  ))}
                </small>
              </button>
            );
          })}
        </div>
        <aside className="seat-sidebar">
          {selectedName === undefined ? (
            <p>Add players to start entering seating and claims.</p>
          ) : (
            <>
              <div className="field-grid">
                <span>Seat</span>
                <strong>{selectedIndex + 1}</strong>
                <span>Name</span>
                <input
                  type="text"
                  value={selectedName}
                  disabled={selectedPlayerIndex === -1}
                  onChange={(event) =>
                    dispatch({ type: "renamePlayer", index: selectedPlayerIndex, name: event.target.value })
                  }
                />
                <span>Left</span>
                <strong>{leftNeighbor}</strong>
                <span>Right</span>
                <strong>{rightNeighbor}</strong>
              </div>
              <div className="claim-add-row">
                <select value={newType} onChange={(event) => setNewType(event.target.value as Claim["type"])}>
                  {CLAIM_TYPES.map((type) => (
                    <option key={type} value={type}>
                      {type}
                    </option>
                  ))}
                </select>
                <button type="button" onClick={addClaim}>
                  + Add claim
                </button>
              </div>
              <div className="selected-claims">
                {selectedClaims.length === 0 && <p>No claims for this player.</p>}
                {selectedClaims.map(([claim, index]) => (
                  <div key={index} className="claim-block">
                    <header>
                      <strong>{roleEmojiLabel(claim.type)}</strong>
                      <button type="button" onClick={() => dispatch({ type: "removeClaim", index })}>
                        Remove
                      </button>
                    </header>
                    <ClaimBody
                      doc={doc}
                      claim={claim}
                      onChange={(nextClaim) => dispatch({ type: "updateClaim", index, claim: nextClaim })}
                    />
                  </div>
                ))}
              </div>
            </>
          )}
        </aside>
      </div>
    </section>
  );
}

function claimIndexesForPlayer(doc: PuzzleDoc, player: string): Array<[Claim, number]> {
  return doc.claims.flatMap((claim, index) => (claim.name === player ? [[claim, index] as [Claim, number]] : []));
}

function seatPosition(index: number, count: number): CSSProperties {
  if (count === 0) return {};
  const angle = -90 + (index * 360) / count;
  const radians = (angle * Math.PI) / 180;
  const radius = 36;
  return {
    left: `${50 + Math.cos(radians) * radius}%`,
    top: `${50 + Math.sin(radians) * radius}%`,
  };
}
