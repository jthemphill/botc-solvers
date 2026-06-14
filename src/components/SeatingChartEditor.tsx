import { useEffect, useState, type CSSProperties, type Dispatch, type DragEvent } from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import type { Claim, PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { isHiddenScriptRole } from "../state/scriptRoles";
import { CLAIM_TYPES, ClaimBody, makeEmptyClaim } from "./ClaimsEditor";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

interface SharedProps extends Props {
  selectedIndex: number;
  onSelect: (index: number) => void;
}

export function SeatingChartEditor({ doc, dispatch }: Props) {
  const [selectedIndex, setSelectedIndex] = useState(0);
  return (
    <section className="seating-composer">
      <PuzzleSheet doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={setSelectedIndex} />
      <SelectedPlayerWorkbench
        doc={doc}
        dispatch={dispatch}
        selectedIndex={selectedIndex}
        onSelect={setSelectedIndex}
      />
    </section>
  );
}

export function PuzzleSheet({ doc, dispatch, selectedIndex, onSelect }: SharedProps) {
  const players = doc.players;
  const selectedName = players[selectedIndex];
  const roleCounts = countScriptRoles(doc.script);
  const [draggedIndex, setDraggedIndex] = useState<number | undefined>(undefined);

  useEffect(() => {
    if (selectedIndex >= players.length) onSelect(Math.max(0, players.length - 1));
  }, [onSelect, players.length, selectedIndex]);

  const startSeatDrag = (event: DragEvent<HTMLButtonElement>, index: number) => {
    setDraggedIndex(index);
    event.dataTransfer.effectAllowed = "move";
    event.dataTransfer.setData("text/plain", String(index));
  };

  const allowSeatDrop = (event: DragEvent<HTMLButtonElement>) => {
    event.preventDefault();
    event.dataTransfer.dropEffect = "move";
  };

  const dropSeat = (event: DragEvent<HTMLButtonElement>, toIndex: number) => {
    event.preventDefault();
    const dataIndex = Number(event.dataTransfer.getData("text/plain"));
    const fromIndex = Number.isInteger(dataIndex) ? dataIndex : draggedIndex;
    setDraggedIndex(undefined);
    if (fromIndex === undefined || fromIndex === toIndex) return;
    dispatch({ type: "movePlayerTo", fromIndex, toIndex });
    onSelect(toIndex);
  };

  return (
    <div className="sheet-content">
      <div className="sheet-tools">
        <label>
          Players
          <input
            type="number"
            min={0}
            max={20}
            value={players.length}
            onChange={(event) => dispatch({ type: "setPlayerCount", count: Number(event.target.value) })}
          />
        </label>
        <span>
          {doc.script.length} roles · {doc.claims.length} claims
        </span>
      </div>

      <div className="seating-chart" aria-label="Clockwise seating chart">
        <div className="seating-ring" />
        {players.map((player, index) => {
          const roleClaims = claimIndexesForPlayer(doc, player);
          const roleLabels = roleClaims.map(([claim]) => roleEmojiLabel(claim.type));
          const primaryClaim = roleClaims[0]?.[0];
          return (
            <button
              key={player}
              type="button"
              className={`seat-button${index === selectedIndex ? " selected" : ""}${
                index === draggedIndex ? " dragging" : ""
              }`}
              style={seatPosition(index, players.length)}
              draggable
              onDragStart={(event) => startSeatDrag(event, index)}
              onDragOver={allowSeatDrop}
              onDrop={(event) => dropSeat(event, index)}
              onDragEnd={() => setDraggedIndex(undefined)}
              onClick={() => onSelect(index)}
              aria-pressed={index === selectedIndex}
              aria-label={`Seat ${index + 1}: ${player}. Drag to reorder seats.`}
            >
              <span className="seat-token-icon" aria-hidden="true">
                {roleEmoji(primaryClaim?.type) ?? index + 1}
              </span>
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

        {players.length <= 10 &&
          players.map((player, index) => {
            const claim = claimIndexesForPlayer(doc, player)[0]?.[0];
            if (claim === undefined) return null;
            return (
              <button
                key={`${player}-callout`}
                type="button"
                className="claim-callout"
                style={calloutPosition(index, players.length)}
                onClick={() => onSelect(index)}
              >
                "{claimSummary(claim)}"
              </button>
            );
          })}

        <div className="center-timeline" aria-live="polite">
          <strong>{selectedName ?? "No player selected"}</strong>
          <span>Click tokens to edit claims</span>
        </div>
      </div>

      <div className="sheet-divider" />

      <div className="rules-strip" aria-label="Puzzle setup summary">
        <div className="notes-box">
          <strong>Notes</strong>
          <span>Use the workbench to add role stamps and claims.</span>
        </div>
        <div className="rules-summary">
          <h3>Rules</h3>
          <div className="rule-token-row">
            <RuleToken label="Townsfolk" count={roleCounts.townsfolk} />
            <RuleToken label="Outsider" count={roleCounts.outsider} />
            <RuleToken label="Minion" count={roleCounts.minion} tone="evil" />
            <RuleToken label="Demon" count={roleCounts.demon} tone="evil" />
          </div>
        </div>
        <div className="sheet-footnote">
          {players.length} players · {roleCounts.demon} demon · {roleCounts.minion} minion · {roleCounts.outsider}{" "}
          outsider
        </div>
      </div>
    </div>
  );
}

export function SelectedPlayerWorkbench({ doc, dispatch, selectedIndex, onSelect }: SharedProps) {
  const players = doc.players;
  const [newType, setNewType] = useState<Claim["type"]>("Investigator");
  const selectedName = players[selectedIndex];
  const selectedPlayerIndex = selectedName === undefined ? -1 : doc.players.indexOf(selectedName);
  const selectedClaims = selectedName === undefined ? [] : claimIndexesForPlayer(doc, selectedName);
  const leftNeighbor =
    selectedName === undefined || players.length === 0 ? undefined : players[(selectedIndex + 1) % players.length];
  const rightNeighbor =
    selectedName === undefined || players.length === 0
      ? undefined
      : players[(selectedIndex - 1 + players.length) % players.length];

  const addClaim = () => {
    if (selectedName === undefined) return;
    dispatch({ type: "addClaim", claim: makeEmptyClaim(newType, selectedName) });
  };

  const removeSelectedPlayer = () => {
    if (selectedPlayerIndex === -1) return;
    dispatch({ type: "removePlayer", index: selectedPlayerIndex });
    onSelect(Math.max(0, selectedPlayerIndex - 1));
  };

  return (
    <div className="draw-workbench">
      <section className="panel selected-player-panel">
        {selectedName === undefined ? (
          <p>Add players to start drawing the puzzle.</p>
        ) : (
          <>
            <header className="panel-heading-row">
              <div>
                <h3>Selected: {selectedName}</h3>
                <span>
                  Seat {selectedIndex + 1} · left {leftNeighbor ?? "-"} · right {rightNeighbor ?? "-"}
                </span>
              </div>
              <button type="button" onClick={() => onSelect(0)}>
                Clear
              </button>
            </header>

            <div className="field-grid selected-player-grid">
              <span>Name</span>
              <input
                type="text"
                value={selectedName}
                disabled={selectedPlayerIndex === -1}
                onChange={(event) =>
                  dispatch({ type: "renamePlayer", index: selectedPlayerIndex, name: event.target.value })
                }
              />
              <span>Danger</span>
              <button type="button" onClick={removeSelectedPlayer}>
                Remove seat
              </button>
            </div>
          </>
        )}
      </section>

      <section className="panel claims-panel">
        <header className="panel-heading-row">
          <div>
            <h3>Claims</h3>
            <span>{selectedClaims.length} for selected player</span>
          </div>
          <button type="button" onClick={addClaim} disabled={selectedName === undefined}>
            Add Claim
          </button>
        </header>
        <div className="claim-add-row">
          <select value={newType} onChange={(event) => setNewType(event.target.value as Claim["type"])}>
            {CLAIM_TYPES.map((type) => (
              <option key={type} value={type}>
                {type}
              </option>
            ))}
          </select>
        </div>
        <div className="selected-claims">
          {selectedName !== undefined && selectedClaims.length === 0 && <p>No claims for {selectedName}.</p>}
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
      </section>

      <HiddenRolesTray roles={doc.script} />
    </div>
  );
}

function HiddenRolesTray({ roles }: { roles: readonly string[] }) {
  const hiddenRoles = roles.filter(isHiddenScriptRole);

  return (
    <section className="panel hidden-role-tray">
      <header className="panel-heading-row">
        <div>
          <h3>Potential hidden roles</h3>
          <span>{hiddenRoles.length} roles</span>
        </div>
      </header>
      <div className="hidden-role-slots">
        {hiddenRoles.map((role) => (
          <div key={role} className="hidden-role-token">
            <span aria-hidden="true">{roleEmoji(role) ?? "?"}</span>
            <small>{role}</small>
          </div>
        ))}
        {Array.from({ length: Math.max(0, 5 - hiddenRoles.length) }, (_, index) => (
          <div key={`empty-${index}`} className="hidden-role-token empty" aria-label="Empty hidden-role slot">
            +
          </div>
        ))}
      </div>
    </section>
  );
}

function RuleToken({ label, count, tone = "good" }: { label: string; count: number; tone?: "good" | "evil" }) {
  return (
    <div className={`rule-token ${tone}`}>
      <strong>{count}</strong>
      <span>{label}</span>
    </div>
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

function calloutPosition(index: number, count: number): CSSProperties {
  if (count === 0) return {};
  const angle = -90 + (index * 360) / count;
  const radians = (angle * Math.PI) / 180;
  const radiusX = 50;
  const radiusY = 50;
  return {
    left: `${50 + Math.cos(radians) * radiusX}%`,
    top: `${50 + Math.sin(radians) * radiusY}%`,
  };
}

function claimSummary(claim: Claim): string {
  const customInfo = (claim.info ?? [])
    .map((info) => info.expression?.trim())
    .filter((text): text is string => Boolean(text));
  if (customInfo.length > 0) return customInfo.join("; ");

  switch (claim.type) {
    case "Chef":
      return `${claim.count} adjacent evil pair${claim.count === 1 ? "" : "s"}`;
    case "Empath":
      return `${claim.player ? `${claim.player}: ` : ""}${claim.count} evil neighbor${claim.count === 1 ? "" : "s"}`;
    case "Investigator": {
      const role = claim.role ?? claim.minionRole ?? "a Minion";
      return `${formatList(claim.among)} could be ${role}`;
    }
    case "Librarian":
      return claim.outsiderCount !== undefined
        ? `${claim.outsiderCount} Outsider${claim.outsiderCount === 1 ? "" : "s"}`
        : `${formatList(claim.among ?? [])} could be ${claim.role || "an Outsider"}`;
    case "Washerwoman":
      return `${formatList(claim.among)} could be ${claim.role || "a Townsfolk"}`;
    case "FortuneTeller": {
      const check = claim.checks[0];
      if (check === undefined) return "I checked nobody yet";
      return `${check.left} + ${check.right}: ${check.yes ? "yes" : "no"}`;
    }
    case "Undertaker":
      return `${claim.player || "Executed player"} was ${claim.role || "unknown"}`;
    case "Noble":
      return `${formatList(claim.oneEvilAmong ?? claim.among ?? [])}: ${claim.evilCount ?? 1} evil`;
    case "Steward":
      return `${claim.goodPlayer || "Someone"} is good`;
    case "Knight":
      return `${formatList(claim.noDemonAmong)} not Demon`;
    case "Seamstress":
      return `${formatPair(claim.among)} are ${claim.aligned ? "same" : "different"}`;
    case "Juggler":
      return `${Object.keys(claim.guesses).length} guesses, ${claim.correctCount ?? "?"} correct`;
    case "Dreamer":
      return `${claim.player || "Player"} is ${formatList(claim.roles)}`;
    case "Shugenja":
      return `Evil is ${claim.evilDirection}`;
    case "Clockmaker":
      return claim.distance === undefined
        ? "No Clockmaker number"
        : `Demon ${claim.distance} step${claim.distance === 1 ? "" : "s"} from Minion`;
    case "Mathematician":
      return (claim.malfunctions ?? []).length === 0
        ? "No malfunction counts"
        : (claim.malfunctions ?? [])
            .map((entry) => `${entry.count} malfunction${entry.count === 1 ? "" : "s"} (${timingLabel(entry.timing)})`)
            .join("; ");
    case "Sage":
      return `${formatList(claim.demonAmong ?? [])} is Demon`;
    case "Snake Charmer":
      return claim.checked ? `${claim.checked} is ${claim.demon ? "" : "not "}Demon` : "No check yet";
    case "VillageIdiot": {
      const check = claim.checks[0];
      if (check === undefined) return "No checks yet";
      return `${check.player}: ${check.good ? "good" : "evil"}`;
    }
    case "Balloonist":
      return `${claim.differentCharacterTypePairs.length} different-type pair${claim.differentCharacterTypePairs.length === 1 ? "" : "s"}`;
    case "Savant":
      return `${claim.statements[0]?.options.length ?? 0} Savant statements`;
    default:
      return `I am the ${claim.type}`;
  }
}

function formatList(values: readonly string[]): string {
  const visible = values.filter(Boolean);
  if (visible.length === 0) return "Someone";
  if (visible.length === 1) return visible[0] as string;
  if (visible.length === 2) return `${visible[0]} or ${visible[1]}`;
  return `${visible.slice(0, -1).join(", ")}, or ${visible[visible.length - 1]}`;
}

function formatPair(values: readonly string[]): string {
  const visible = values.filter(Boolean);
  if (visible.length === 2) return `${visible[0]} and ${visible[1]}`;
  return formatList(values);
}

function timingLabel(timing: string): string {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return timing;
  const [, period, number] = match;
  if (period === undefined || number === undefined) return timing;
  return `${period[0]?.toUpperCase()}${period.slice(1)} ${number}`;
}

function countScriptRoles(script: readonly string[]): Record<CharacterType, number> {
  const counts: Record<CharacterType, number> = {
    [CharacterType.Townsfolk]: 0,
    [CharacterType.Outsider]: 0,
    [CharacterType.Minion]: 0,
    [CharacterType.Demon]: 0,
  };
  for (const role of script) {
    const characterType = ROLE_CLASSES.get(role)?.characterType;
    if (characterType !== undefined) counts[characterType] += 1;
  }
  return counts;
}
