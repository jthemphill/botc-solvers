import { useEffect, useState, type CSSProperties, type Dispatch, type DragEvent } from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import { standardSetupCounts } from "../model/setup";
import type { Claim, PuzzleDoc, TimelineEventDoc } from "../schema/puzzleDoc";
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
  const setupCounts = countSetupRoles(doc);
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
          const deathMarker = deathMarkerForPlayer(doc.timeline, player);
          const deathClass = deathMarker === undefined ? undefined : deathMarkerClass(deathMarker);
          const deathLabel = deathMarker === undefined ? "" : `, ${deathMarkerLabel(deathMarker)}`;
          return (
            <button
              key={player}
              type="button"
              className={`seat-button${deathClass === undefined ? "" : ` death-${deathClass}`}${
                index === selectedIndex ? " selected" : ""
              }${index === draggedIndex ? " dragging" : ""}`}
              style={seatPosition(index, players.length)}
              draggable
              onDragStart={(event) => startSeatDrag(event, index)}
              onDragOver={allowSeatDrop}
              onDrop={(event) => dropSeat(event, index)}
              onDragEnd={() => setDraggedIndex(undefined)}
              onClick={() => onSelect(index)}
              aria-pressed={index === selectedIndex}
              aria-label={`Seat ${index + 1}: ${player}${deathLabel}. Drag to reorder seats.`}
            >
              {deathClass !== undefined && <span className={`seat-shroud ${deathClass}`} aria-hidden="true" />}
              <span className="seat-token-icon" aria-hidden="true">
                {roleEmoji(primaryClaim?.type) ?? index + 1}
              </span>
              <span className="seat-player-name">{player}</span>
              {deathMarker !== undefined && deathClass !== undefined && (
                <span className={`seat-death-badge ${deathClass}`} aria-hidden="true">
                  {timelineEventGlyph(deathMarker)}
                </span>
              )}
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

      {doc.timeline !== undefined && doc.timeline.length > 0 ? (
        <TimelineStrip timeline={doc.timeline} />
      ) : (
        <SetupStrip playerCount={players.length} setupCounts={setupCounts} />
      )}
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
    <div className={`rule-token ${tone}`} aria-label={`${count} ${label}`}>
      <strong>{count}</strong>
      <span>{label}</span>
    </div>
  );
}

function SetupStrip({ playerCount, setupCounts }: { playerCount: number; setupCounts: Record<CharacterType, number> }) {
  return (
    <div className="rules-strip" aria-label="Puzzle setup summary">
      <div className="notes-box">
        <strong>Notes</strong>
        <span>Use the workbench to add role stamps and claims.</span>
      </div>
      <div className="rules-summary">
        <h3>Setup</h3>
        <div className="rule-token-row">
          <RuleToken label="Townsfolk" count={setupCounts.townsfolk} />
          <RuleToken label="Outsider" count={setupCounts.outsider} />
          <RuleToken label="Minion" count={setupCounts.minion} tone="evil" />
          <RuleToken label="Demon" count={setupCounts.demon} tone="evil" />
        </div>
      </div>
      <div className="sheet-footnote">
        {playerCount} players · {setupCounts.demon} demon · {setupCounts.minion} minion · {setupCounts.outsider}{" "}
        outsider
      </div>
    </div>
  );
}

function TimelineStrip({ timeline }: { timeline: readonly TimelineEventDoc[] }) {
  const deathCount = timeline.reduce((sum, event) => sum + event.players.length, 0);
  return (
    <div className="timeline-strip" aria-label="Puzzle timeline">
      <div className="timeline-legend">
        <strong>Timeline</strong>
        <span>Deaths and executions</span>
      </div>
      <ol className="timeline-event-list">
        {timeline.map((event, index) => {
          const deathClass = deathMarkerClass(event.type);
          return (
            <li
              key={`${event.timing}-${event.type}-${index}`}
              className={`timeline-event ${deathClass}`}
              aria-label={`${timingLabel(event.timing)} ${timelineEventAction(event)}: ${event.players.join(", ")}`}
            >
              <span className={`timeline-node ${deathClass}`} aria-hidden="true">
                {timelineEventGlyph(event.type)}
              </span>
              <div>
                <strong>
                  {compactTimingLabel(event.timing)} {timelineEventAction(event)}
                </strong>
                <span>{formatList(event.players)}</span>
              </div>
            </li>
          );
        })}
      </ol>
      <div className="sheet-footnote">
        {deathCount} death{deathCount === 1 ? "" : "s"} tracked
      </div>
    </div>
  );
}

function claimIndexesForPlayer(doc: PuzzleDoc, player: string): Array<[Claim, number]> {
  return doc.claims.flatMap((claim, index) => (claim.name === player ? [[claim, index] as [Claim, number]] : []));
}

function deathMarkerForPlayer(timeline: PuzzleDoc["timeline"], player: string): TimelineEventDoc["type"] | undefined {
  const events = timeline ?? [];
  if (events.some((event) => event.type === "nominationDeath" && event.players.includes(player)))
    return "nominationDeath";
  if (events.some((event) => event.type === "execution" && event.players.includes(player))) return "execution";
  if (events.some((event) => event.type === "nightKill" && event.players.includes(player))) return "nightKill";
  return undefined;
}

function deathMarkerClass(type: TimelineEventDoc["type"]): "nomination-death" | "execution" | "night-kill" {
  if (type === "nominationDeath") return "nomination-death";
  return type === "execution" ? "execution" : "night-kill";
}

function deathMarkerLabel(type: TimelineEventDoc["type"]): string {
  if (type === "nominationDeath") return "died while nominating";
  return type === "execution" ? "executed" : "killed at night";
}

function timelineEventAction(event: TimelineEventDoc): string {
  if (event.type === "nominationDeath") return "Nomination Death";
  if (event.type === "execution") return "Execution";
  return event.players.length === 1 ? "Night Death" : "Night Deaths";
}

function timelineEventGlyph(type: TimelineEventDoc["type"]): string {
  if (type === "nominationDeath") return "!";
  if (type === "execution") return "X";
  return "N";
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

function compactTimingLabel(timing: string): string {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return timing;
  const [, period, number] = match;
  if (period === undefined || number === undefined) return timing;
  return `${period[0]?.toUpperCase()}${number}`;
}

function countSetupRoles(doc: PuzzleDoc): Record<CharacterType, number> {
  if (doc.setup === "none") return countScriptRoles(doc.script);
  try {
    return { ...standardSetupCounts(doc.players.length) };
  } catch {
    return countScriptRoles(doc.script);
  }
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
