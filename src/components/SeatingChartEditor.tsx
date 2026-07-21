import {
  useEffect,
  useRef,
  useState,
  type CSSProperties,
  type Dispatch,
  type KeyboardEvent,
  type PointerEvent,
} from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import { standardSetupCounts } from "../model/setup";
import {
  isTimelineDeathEvent,
  type Claim,
  type PuzzleDoc,
  type TimelineEventDoc,
  type TimelineEventType,
} from "../schema/puzzleDoc";
import { sortTimelineEvents, type PuzzleAction } from "../state/puzzleDoc";
import { ClaimBody, ClaimTypeahead, makeEmptyClaim } from "./ClaimsEditor";
import { claimSummary, compactTimingLabel, formatList, timingLabel } from "./claimSummary";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

interface SharedProps extends Props {
  selectedIndex: number;
  onSelect: (index: number) => void;
}

type DrawWorkbenchProps = SharedProps;

interface ClaimQuoteCard {
  readonly player: string;
  readonly playerIndex: number;
  readonly claimIndex: number;
  readonly roleLabel: string;
  readonly summary: string;
}

interface MobileDragPreview {
  readonly fromIndex: number;
  readonly toIndex: number;
  readonly offsetY: number;
  readonly rowHeight: number;
}

interface MobileDragOrigin {
  readonly fromIndex: number;
  readonly startY: number;
  readonly rows: readonly { readonly index: number; readonly centerY: number }[];
}

interface DesktopDragOrigin {
  readonly fromIndex: number;
  readonly startX: number;
  readonly startY: number;
  readonly seats: readonly { readonly index: number; readonly centerX: number; readonly centerY: number }[];
}

const DOUBLE_TAP_WINDOW_MS = 450;
const DESKTOP_DRAG_THRESHOLD_PX = 7;
const TIMELINE_DAY_OPTIONS = ["day_1", "day_2", "day_3", "day_4", "day_5"];
const TIMELINE_NIGHT_OPTIONS = ["night_1", "night_2", "night_3", "night_4", "night_5"];
const TIMELINE_EVENT_TYPE_OPTIONS: Array<{ type: TimelineEventType; label: string }> = [
  { type: "execution", label: "Execution" },
  { type: "survivedExecution", label: "Survived Execution" },
  { type: "nightDeath", label: "Night Death" },
  { type: "tinkerDeath", label: "Tinker Death" },
  { type: "resurrection", label: "Resurrection" },
  { type: "slayerShot", label: "Slayer Shot" },
  { type: "witchCurse", label: "Witch Curse" },
  { type: "nominationDeath", label: "Nomination Death" },
  { type: "doomsayerDeath", label: "Doomsayer Death" },
];

export function SeatingChartEditor({ doc, dispatch }: Props) {
  const [selectedIndex, setSelectedIndex] = useState(0);
  return (
    <section className="seating-composer">
      <PuzzleSheet doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={setSelectedIndex} />
      <DrawWorkbench doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={setSelectedIndex} />
    </section>
  );
}

export function PuzzleSheet({ doc, dispatch, selectedIndex, onSelect }: SharedProps) {
  const players = doc.players;
  const selectedName = players[selectedIndex];
  const setupCounts = countSetupRoles(doc);
  const timeline = doc.timeline ?? [];
  const [draggedIndex, setDraggedIndex] = useState<number | undefined>(undefined);
  const [desktopDropIndex, setDesktopDropIndex] = useState<number | undefined>(undefined);
  const [desktopDragOffset, setDesktopDragOffset] = useState({ x: 0, y: 0 });
  const [mobileDragPreview, setMobileDragPreview] = useState<MobileDragPreview | undefined>(undefined);
  const [editingIndex, setEditingIndex] = useState<number | undefined>(undefined);
  const [selectedTimelineIndex, setSelectedTimelineIndex] = useState<number | undefined>(undefined);
  const [eventComposer, setEventComposer] = useState<
    { readonly player: string; readonly type: TimelineEventType; readonly timing: string } | undefined
  >(undefined);
  const [draftName, setDraftName] = useState("");
  const [trashDropActive, setTrashDropActive] = useState(false);
  const lastSeatTap = useRef<{ index: number; time: number }>({ index: -1, time: 0 });
  const mobileDragOrigin = useRef<MobileDragOrigin | undefined>(undefined);
  const mobileDropIndex = useRef<number | undefined>(undefined);
  const desktopDragOrigin = useRef<DesktopDragOrigin | undefined>(undefined);
  const desktopDragActive = useRef(false);
  const desktopDropIndexRef = useRef<number | undefined>(undefined);
  const desktopTrashActive = useRef(false);
  const quoteCards = claimQuoteCardsForDoc(doc);
  const mergedQuoteCards = mergedQuoteCardsByPlayer(quoteCards);
  const chartQuoteCards = players.length <= 10 ? mergedQuoteCards : [];
  const quoteCardByPlayer = new Map(mergedQuoteCards.map((card) => [card.player, card] as const));

  useEffect(() => {
    if (selectedIndex >= players.length) onSelect(Math.max(0, players.length - 1));
  }, [onSelect, players.length, selectedIndex]);

  useEffect(() => {
    if (editingIndex !== undefined && editingIndex >= players.length) {
      setEditingIndex(undefined);
      setDraftName("");
    }
  }, [editingIndex, players.length]);

  useEffect(() => {
    if (selectedTimelineIndex !== undefined && selectedTimelineIndex >= timeline.length) {
      setSelectedTimelineIndex(timeline.length === 0 ? undefined : timeline.length - 1);
    }
  }, [selectedTimelineIndex, timeline.length]);

  const setTimeline = (next: PuzzleDoc["timeline"]) => {
    dispatch({ type: "setTimeline", timeline: next });
  };

  const updateTimelineEvent = (index: number, event: TimelineEventDoc) => {
    const nextTimeline = sortTimelineEvents(
      timeline.map((entry, eventIndex) => (eventIndex === index ? event : entry)),
    );
    setTimeline(nextTimeline);
    const nextIndex = nextTimeline.indexOf(event);
    setSelectedTimelineIndex(nextIndex === -1 ? undefined : nextIndex);
  };

  const removeTimelineEvent = (index: number) => {
    setTimeline(timeline.filter((_, eventIndex) => eventIndex !== index));
    setSelectedTimelineIndex((current) => {
      if (current === undefined) return undefined;
      if (current === index) return undefined;
      return current > index ? current - 1 : current;
    });
  };

  const appendTimelineEvent = (nextEvent: TimelineEventDoc) => {
    const nextTimeline = sortTimelineEvents([...timeline, nextEvent]);
    setTimeline(nextTimeline);
    const nextIndex = nextTimeline.indexOf(nextEvent);
    setSelectedTimelineIndex(nextIndex === -1 ? undefined : nextIndex);
  };

  const addTimelineEvent = (player = selectedName ?? players[0], type: TimelineEventType = "execution") => {
    if (player === undefined) return;
    const timing = defaultTimingForType(
      type,
      type === "nightDeath" ? nextTimelineTiming(timeline, "nightDeath") : nextTimelineTiming(timeline, "execution"),
    );
    appendTimelineEvent({ timing, type, players: [player] });
  };

  const openEventComposer = (player: string) => {
    setEventComposer({
      player,
      type: "execution",
      timing: nextTimelineTiming(timeline, "execution"),
    });
  };

  const commitEventComposer = () => {
    if (eventComposer === undefined) return;
    appendTimelineEvent({
      type: eventComposer.type,
      timing: eventComposer.timing,
      players: [eventComposer.player],
    });
    setEventComposer(undefined);
  };

  const beginRename = (index: number, name: string) => {
    setDraggedIndex(undefined);
    setDesktopDropIndex(undefined);
    setTrashDropActive(false);
    onSelect(index);
    setEditingIndex(index);
    setDraftName(name);
  };

  const commitRename = () => {
    if (editingIndex === undefined) return;
    const currentName = players[editingIndex];
    const nextName = draftName.trim();
    if (currentName !== undefined && nextName !== currentName) {
      dispatch({ type: "renamePlayer", index: editingIndex, name: nextName });
    }
    setEditingIndex(undefined);
    setDraftName("");
  };

  const cancelRename = () => {
    setEditingIndex(undefined);
    setDraftName("");
  };

  const clearDesktopSeatDrag = () => {
    desktopDragOrigin.current = undefined;
    desktopDragActive.current = false;
    desktopDropIndexRef.current = undefined;
    desktopTrashActive.current = false;
    setDraggedIndex(undefined);
    setDesktopDropIndex(undefined);
    setDesktopDragOffset({ x: 0, y: 0 });
    setTrashDropActive(false);
  };

  const startDesktopSeatDrag = (event: PointerEvent<HTMLElement>, index: number) => {
    if (editingIndex === index) return;
    const chart = event.currentTarget.closest<HTMLElement>(".seating-chart");
    if (chart === null) return;
    desktopDragOrigin.current = {
      fromIndex: index,
      startX: event.clientX,
      startY: event.clientY,
      seats: [...chart.querySelectorAll<HTMLElement>(".seat-button")].map((seat) => {
        const rect = seat.getBoundingClientRect();
        return {
          index: Number(seat.dataset.seatIndex),
          centerX: rect.left + rect.width / 2,
          centerY: rect.top + rect.height / 2,
        };
      }),
    };
    desktopDragActive.current = false;
    desktopDropIndexRef.current = index;
    desktopTrashActive.current = false;
  };

  const moveDesktopSeatDrag = (event: PointerEvent<HTMLElement>) => {
    const origin = desktopDragOrigin.current;
    if (origin === undefined) return;
    const offsetX = event.clientX - origin.startX;
    const offsetY = event.clientY - origin.startY;
    if (!desktopDragActive.current && Math.hypot(offsetX, offsetY) < DESKTOP_DRAG_THRESHOLD_PX) return;
    event.preventDefault();
    if (!desktopDragActive.current) {
      desktopDragActive.current = true;
      setDraggedIndex(origin.fromIndex);
      setDesktopDropIndex(origin.fromIndex);
    }
    setDesktopDragOffset({ x: offsetX, y: offsetY });

    const trashRect = document.querySelector<HTMLElement>(".seat-trash-zone")?.getBoundingClientRect();
    const overTrash =
      trashRect !== undefined &&
      event.clientX >= trashRect.left &&
      event.clientX <= trashRect.right &&
      event.clientY >= trashRect.top &&
      event.clientY <= trashRect.bottom;
    desktopTrashActive.current = overTrash;
    setTrashDropActive(overTrash);
    if (overTrash) return;

    const target = origin.seats.reduce<(typeof origin.seats)[number] | undefined>((closest, seat) => {
      if (closest === undefined) return seat;
      const distance = Math.hypot(seat.centerX - event.clientX, seat.centerY - event.clientY);
      const closestDistance = Math.hypot(closest.centerX - event.clientX, closest.centerY - event.clientY);
      return distance < closestDistance ? seat : closest;
    }, undefined);
    const toIndex = target?.index ?? origin.fromIndex;
    desktopDropIndexRef.current = toIndex;
    setDesktopDropIndex(toIndex);
  };

  const finishDesktopSeatDrag = (event: PointerEvent<HTMLElement>) => {
    const origin = desktopDragOrigin.current;
    if (origin === undefined) return;
    if (!desktopDragActive.current) {
      desktopDragOrigin.current = undefined;
      return;
    }
    event.preventDefault();
    moveDesktopSeatDrag(event);
    const fromIndex = origin.fromIndex;
    const toIndex = desktopDropIndexRef.current;
    const removePlayer = desktopTrashActive.current;
    clearDesktopSeatDrag();
    if (removePlayer) {
      dispatch({ type: "removePlayer", index: fromIndex });
      onSelect(Math.max(0, Math.min(fromIndex, players.length - 2)));
      return;
    }
    if (toIndex === undefined || fromIndex === toIndex || toIndex < 0 || toIndex >= players.length) return;
    dispatch({ type: "movePlayerTo", fromIndex, toIndex });
    onSelect(toIndex);
  };

  const startMobileSeatDrag = (event: PointerEvent<HTMLButtonElement>, index: number) => {
    if (editingIndex === index) return;
    event.preventDefault();
    const row = event.currentTarget.closest<HTMLElement>("[data-seat-index]");
    const list = row?.closest<HTMLElement>(".mobile-player-list");
    if (row === null || row === undefined || list === null || list === undefined) return;
    const rowRect = row.getBoundingClientRect();
    mobileDragOrigin.current = {
      fromIndex: index,
      startY: event.clientY,
      rows: [...list.querySelectorAll<HTMLElement>("[data-seat-index]")].map((entry) => {
        const rect = entry.getBoundingClientRect();
        return { index: Number(entry.dataset.seatIndex), centerY: rect.top + rect.height / 2 };
      }),
    };
    mobileDropIndex.current = index;
    setMobileDragPreview({ fromIndex: index, toIndex: index, offsetY: 0, rowHeight: rowRect.height });
    setDraggedIndex(index);
    setTrashDropActive(false);
  };

  const moveMobileSeatDrag = (event: PointerEvent<HTMLElement>) => {
    const origin = mobileDragOrigin.current;
    if (origin === undefined) return;
    event.preventDefault();
    const target = origin.rows.reduce<(typeof origin.rows)[number] | undefined>((closest, row) => {
      if (closest === undefined) return row;
      return Math.abs(row.centerY - event.clientY) < Math.abs(closest.centerY - event.clientY) ? row : closest;
    }, undefined);
    const toIndex = target?.index ?? origin.fromIndex;
    mobileDropIndex.current = toIndex;
    setMobileDragPreview((current) =>
      current === undefined ? current : { ...current, toIndex, offsetY: event.clientY - origin.startY },
    );
  };

  const clearMobileSeatDrag = () => {
    mobileDragOrigin.current = undefined;
    mobileDropIndex.current = undefined;
    setMobileDragPreview(undefined);
    setDraggedIndex(undefined);
  };

  const finishMobileSeatDrag = (event: PointerEvent<HTMLElement>) => {
    const origin = mobileDragOrigin.current;
    if (origin === undefined) return;
    event.preventDefault();
    moveMobileSeatDrag(event);
    const fromIndex = origin.fromIndex;
    const toIndex = mobileDropIndex.current;
    clearMobileSeatDrag();
    if (
      toIndex === undefined ||
      !Number.isInteger(toIndex) ||
      fromIndex === toIndex ||
      toIndex < 0 ||
      toIndex >= players.length
    )
      return;
    dispatch({ type: "movePlayerTo", fromIndex, toIndex });
    onSelect(toIndex);
  };

  const handleSeatPointerUp = (event: PointerEvent<HTMLDivElement>, index: number, player: string) => {
    if (desktopDragActive.current || event.pointerType === "mouse" || editingIndex === index) return;
    const now = Date.now();
    if (lastSeatTap.current.index === index && now - lastSeatTap.current.time <= DOUBLE_TAP_WINDOW_MS) {
      event.preventDefault();
      beginRename(index, player);
      lastSeatTap.current = { index: -1, time: 0 };
      return;
    }
    lastSeatTap.current = { index, time: now };
  };

  const handleSeatKeyDown = (event: KeyboardEvent<HTMLDivElement>, index: number, player: string) => {
    if (event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      onSelect(index);
    } else if (event.key === "F2") {
      event.preventDefault();
      beginRename(index, player);
    }
  };

  return (
    <div
      className="sheet-content"
      onPointerMove={moveDesktopSeatDrag}
      onPointerUp={finishDesktopSeatDrag}
      onPointerCancel={clearDesktopSeatDrag}
    >
      <div className="sheet-tools">
        <label>
          Players
          <PlayerCountInput value={players.length} onChange={(count) => dispatch({ type: "setPlayerCount", count })} />
        </label>
        <SetupCountSummary setupCounts={setupCounts} />
        {draggedIndex !== undefined && (
          <div
            className={`seat-trash-zone${trashDropActive ? " drop-target" : ""}`}
            aria-label="Trash zone for removing seats"
          >
            <span aria-hidden="true">×</span>
            <strong>Trash</strong>
          </div>
        )}
      </div>

      <section className="mobile-player-roster" aria-label="Players in seating order">
        <header>
          <div>
            <strong>Players</strong>
            <span>Drag to reorder</span>
          </div>
          <span>{players.length}</span>
        </header>
        <div
          className={`mobile-player-list${mobileDragPreview === undefined ? "" : " drag-active"}`}
          onPointerMove={moveMobileSeatDrag}
          onPointerUp={finishMobileSeatDrag}
          onPointerCancel={clearMobileSeatDrag}
        >
          {players.map((player, index) => {
            const card = quoteCardByPlayer.get(player);
            const primaryClaim = mostRecentClaim(claimIndexesForPlayer(doc, player));
            const deathMarker = deathMarkerForPlayer(doc.timeline, player);
            const deathClass = deathMarker === undefined ? undefined : deathMarkerClass(deathMarker);
            const deathIndex =
              deathMarker === undefined
                ? -1
                : timeline.findIndex(
                    (event) =>
                      event.type === deathMarker.type &&
                      event.timing === deathMarker.timing &&
                      event.players.includes(player),
                  );
            const isEditing = editingIndex === index;
            const dragDirection =
              mobileDragPreview === undefined || mobileDragPreview.fromIndex === mobileDragPreview.toIndex
                ? ""
                : mobileDragPreview.fromIndex < mobileDragPreview.toIndex
                  ? " down"
                  : " up";
            const shiftClass =
              mobileDragPreview === undefined || index === mobileDragPreview.fromIndex
                ? ""
                : mobileDragPreview.fromIndex < mobileDragPreview.toIndex &&
                    index > mobileDragPreview.fromIndex &&
                    index <= mobileDragPreview.toIndex
                  ? " shift-up"
                  : mobileDragPreview.fromIndex > mobileDragPreview.toIndex &&
                      index >= mobileDragPreview.toIndex &&
                      index < mobileDragPreview.fromIndex
                    ? " shift-down"
                    : "";
            const isDropTarget = mobileDragPreview !== undefined && index === mobileDragPreview.toIndex;
            const dragStyle =
              mobileDragPreview === undefined
                ? undefined
                : ({
                    "--mobile-drag-row-height": `${mobileDragPreview.rowHeight}px`,
                    "--mobile-drag-offset-y": `${mobileDragPreview.offsetY}px`,
                  } as CSSProperties);
            return (
              <article
                key={`${player}-mobile`}
                data-seat-index={index}
                data-drop-target={isDropTarget ? "true" : undefined}
                className={`mobile-player-row${index === selectedIndex ? " selected" : ""}${
                  index === draggedIndex ? " dragging" : ""
                }${shiftClass}${isDropTarget ? ` drop-target${dragDirection}` : ""}`}
                style={dragStyle}
              >
                <button
                  type="button"
                  className="mobile-drag-handle"
                  aria-label={`Reorder ${player}`}
                  title={`Drag to reorder ${player}`}
                  onPointerDown={(event) => startMobileSeatDrag(event, index)}
                >
                  ⋮⋮
                </button>
                <button
                  type="button"
                  className="mobile-player-main"
                  onClick={() => onSelect(index)}
                  onDoubleClick={() => beginRename(index, player)}
                  aria-label={`Player ${index + 1}: ${player}. Double-click to rename.`}
                >
                  <span className="mobile-player-role" aria-hidden="true">
                    {roleEmoji(primaryClaim?.type) ?? index + 1}
                  </span>
                  <span className="mobile-player-copy">
                    <span>
                      {isEditing ? (
                        <input
                          type="text"
                          value={draftName}
                          autoFocus
                          aria-label={`Rename ${player} on mobile`}
                          onFocus={(event) => event.currentTarget.select()}
                          onChange={(event) => setDraftName(event.target.value)}
                          onBlur={commitRename}
                          onClick={(event) => event.stopPropagation()}
                          onKeyDown={(event) => {
                            event.stopPropagation();
                            if (event.key === "Enter") commitRename();
                            if (event.key === "Escape") cancelRename();
                          }}
                        />
                      ) : (
                        <strong>{player}</strong>
                      )}
                      {card !== undefined && <em>{card.roleLabel}</em>}
                    </span>
                    <small>{card === undefined ? "No claim yet." : `“${card.summary}”`}</small>
                  </span>
                </button>
                <button
                  type="button"
                  className={`mobile-player-event${deathClass === undefined ? "" : ` ${deathClass}`}`}
                  aria-label={deathMarker === undefined ? `Add event for ${player}` : `Edit event for ${player}`}
                  onClick={() => {
                    onSelect(index);
                    if (deathIndex >= 0) setSelectedTimelineIndex(deathIndex);
                    else openEventComposer(player);
                  }}
                >
                  {deathMarker === undefined ? "+" : compactTimingLabel(deathMarker.timing)}
                </button>
              </article>
            );
          })}
        </div>
      </section>

      <div className="seating-chart" aria-label="Clockwise seating chart">
        <div className="seating-ring" />
        {draggedIndex !== undefined && desktopDropIndex !== undefined && draggedIndex !== desktopDropIndex && (
          <div
            className="seat-drop-placeholder"
            style={seatPosition(desktopDropIndex, players.length)}
            aria-hidden="true"
          />
        )}
        {players.map((player, index) => {
          const roleClaims = claimIndexesForPlayer(doc, player);
          const roleLabels = roleClaims.map(([claim]) => roleEmojiLabel(claim.type));
          const primaryClaim = mostRecentClaim(roleClaims);
          const deathMarker = deathMarkerForPlayer(doc.timeline, player);
          const deathClass = deathMarker === undefined ? undefined : deathMarkerClass(deathMarker);
          const deathLabel = deathMarker === undefined ? "" : `, ${deathMarkerLabel(deathMarker)}`;
          const isEditing = editingIndex === index;
          const previewIndex = previewSeatIndex(index, draggedIndex, desktopDropIndex);
          const seatStyle = {
            ...seatButtonStyle(previewIndex, players.length, player),
            ...(index === draggedIndex
              ? {
                  "--desktop-drag-x": `${desktopDragOffset.x}px`,
                  "--desktop-drag-y": `${desktopDragOffset.y}px`,
                }
              : {}),
          } as CSSProperties;
          return (
            <div
              key={player}
              data-seat-index={index}
              data-preview-index={previewIndex}
              className={`seat-button${deathClass === undefined ? "" : ` death-${deathClass}`}${
                index === selectedIndex ? " selected" : ""
              }${index === draggedIndex ? " dragging" : ""}${isEditing ? " editing" : ""}`}
              style={seatStyle}
              role="button"
              tabIndex={0}
              onPointerDown={(event) => startDesktopSeatDrag(event, index)}
              onClick={() => onSelect(index)}
              onDoubleClick={() => beginRename(index, player)}
              onPointerUp={(event) => handleSeatPointerUp(event, index, player)}
              onKeyDown={(event) => handleSeatKeyDown(event, index, player)}
              aria-pressed={index === selectedIndex}
              aria-label={`Seat ${index + 1}: ${player}${deathLabel}. Drag to reorder seats. Double-click to rename.`}
            >
              {deathClass !== undefined && <span className={`seat-shroud ${deathClass}`} aria-hidden="true" />}
              <span
                className="seat-token-icon"
                aria-label={
                  roleLabels.length === 0 ? "No claims" : `Primary claim: ${roleEmojiLabel(primaryClaim?.type)}`
                }
                title={roleLabels.join(", ")}
              >
                {roleEmoji(primaryClaim?.type) ?? index + 1}
              </span>
              {isEditing ? (
                <input
                  className="seat-name-input"
                  type="text"
                  value={draftName}
                  autoFocus
                  aria-label={`Rename ${player}`}
                  draggable={false}
                  onFocus={(event) => event.currentTarget.select()}
                  onChange={(event) => setDraftName(event.target.value)}
                  onBlur={commitRename}
                  onClick={(event) => event.stopPropagation()}
                  onDoubleClick={(event) => event.stopPropagation()}
                  onPointerUp={(event) => event.stopPropagation()}
                  onKeyDown={(event) => {
                    event.stopPropagation();
                    if (event.key === "Enter") {
                      event.preventDefault();
                      commitRename();
                    } else if (event.key === "Escape") {
                      event.preventDefault();
                      cancelRename();
                    }
                  }}
                />
              ) : (
                <span className="seat-player-name">{player}</span>
              )}
              {deathMarker !== undefined && deathClass !== undefined && (
                <span className={`seat-death-badge ${deathClass}`} aria-hidden="true">
                  {timelineEventGlyph(deathMarker)}
                </span>
              )}
            </div>
          );
        })}

        {chartQuoteCards.map((card) => (
          <button
            key={`${card.claimIndex}-${card.player}-callout`}
            type="button"
            className={`claim-callout${card.playerIndex === draggedIndex ? " dragging" : ""}`}
            style={calloutPosition(previewSeatIndex(card.playerIndex, draggedIndex, desktopDropIndex), players.length)}
            onClick={() => onSelect(card.playerIndex)}
          >
            "{card.summary}"
          </button>
        ))}

        <div className="center-timeline" aria-live="polite">
          <strong>{selectedName ?? "No player selected"}</strong>
          <span>Click tokens to edit claims</span>
        </div>
      </div>

      <ClaimQuoteDeck cards={quoteCards} onSelect={onSelect} />

      <div className="sheet-divider" />
      <TimelineStrip
        timeline={timeline}
        players={players}
        selectedIndex={selectedTimelineIndex}
        onSelect={setSelectedTimelineIndex}
        onUpdate={updateTimelineEvent}
        onRemove={removeTimelineEvent}
        onAdd={() => addTimelineEvent()}
      />

      {eventComposer !== undefined && (
        <div className="event-composer-backdrop" role="presentation" onClick={() => setEventComposer(undefined)}>
          <section
            className="event-composer-sheet"
            role="dialog"
            aria-modal="true"
            aria-labelledby="event-composer-title"
            onClick={(event) => event.stopPropagation()}
          >
            <header>
              <h3 id="event-composer-title">Add event for {eventComposer.player}</h3>
              <button type="button" aria-label="Close event editor" onClick={() => setEventComposer(undefined)}>
                ×
              </button>
            </header>
            <div className="event-quick-actions">
              <button
                type="button"
                className={eventComposer.type === "execution" ? "active" : undefined}
                onClick={() =>
                  setEventComposer({
                    ...eventComposer,
                    type: "execution",
                    timing: nextTimelineTiming(timeline, "execution"),
                  })
                }
              >
                <span aria-hidden="true">X</span>
                Executed
              </button>
              <button
                type="button"
                className={eventComposer.type === "nightDeath" ? "active" : undefined}
                onClick={() =>
                  setEventComposer({
                    ...eventComposer,
                    type: "nightDeath",
                    timing: nextTimelineTiming(timeline, "nightDeath"),
                  })
                }
              >
                <span aria-hidden="true">N</span>
                Killed at night
              </button>
              <button
                type="button"
                className={
                  eventComposer.type !== "execution" && eventComposer.type !== "nightDeath" ? "active" : undefined
                }
                onClick={() =>
                  setEventComposer({
                    ...eventComposer,
                    type: "witchCurse",
                    timing: defaultTimingForType("witchCurse", eventComposer.timing),
                  })
                }
              >
                <span aria-hidden="true">…</span>
                Other event
              </button>
            </div>
            <label>
              Cause
              <select
                value={eventComposer.type}
                onChange={(event) => {
                  const type = event.target.value as TimelineEventType;
                  setEventComposer({
                    ...eventComposer,
                    type,
                    timing: defaultTimingForType(type, eventComposer.timing),
                  });
                }}
              >
                {TIMELINE_EVENT_TYPE_OPTIONS.map((option) => (
                  <option key={option.type} value={option.type}>
                    {option.label}
                  </option>
                ))}
              </select>
            </label>
            <label>
              Timing
              <TimelineTimingSelect
                type={eventComposer.type}
                value={eventComposer.timing}
                onChange={(timing) => setEventComposer({ ...eventComposer, timing })}
              />
            </label>
            <button type="button" className="primary-action" onClick={commitEventComposer}>
              Add event
            </button>
          </section>
        </div>
      )}
    </div>
  );
}

function PlayerCountInput({ value, onChange }: { value: number; onChange: (value: number) => void }) {
  const [draft, setDraft] = useState(String(value));
  const [focused, setFocused] = useState(false);

  useEffect(() => {
    if (!focused) setDraft(String(value));
  }, [focused, value]);

  const commit = () => {
    setFocused(false);
    if (draft === "") {
      setDraft(String(value));
      return;
    }
    const next = Number(draft);
    if (Number.isFinite(next)) onChange(next);
    setDraft(String(Number.isFinite(next) ? Math.max(0, Math.floor(next)) : value));
  };

  return (
    <input
      id="player-count"
      name="player-count"
      type="number"
      min={0}
      max={20}
      value={draft}
      onFocus={() => setFocused(true)}
      onChange={(event) => {
        const nextDraft = event.target.value;
        if (nextDraft === "") {
          setDraft("");
          return;
        }
        const next = Number(nextDraft);
        if (!Number.isFinite(next)) {
          setDraft(nextDraft);
          return;
        }
        const normalized = Math.max(0, Math.floor(next));
        setDraft(String(normalized));
        onChange(normalized);
      }}
      onBlur={commit}
    />
  );
}

function ClaimQuoteDeck({ cards, onSelect }: { cards: readonly ClaimQuoteCard[]; onSelect: (index: number) => void }) {
  if (cards.length === 0) return null;

  return (
    <section className="claim-summary-deck" aria-label="Player claim summaries">
      <h3>Claims</h3>
      <div className="claim-summary-grid">
        {cards.map((card) => (
          <button
            key={`${card.claimIndex}-${card.player}-summary`}
            type="button"
            className="claim-summary-card"
            onClick={() => onSelect(card.playerIndex)}
          >
            <span className="claim-summary-meta">
              <strong>{card.player}</strong>
              <span>{card.roleLabel}</span>
            </span>
            <span className="claim-summary-text">"{card.summary}"</span>
          </button>
        ))}
      </div>
    </section>
  );
}

export function DrawWorkbench({ doc, dispatch, selectedIndex, onSelect }: DrawWorkbenchProps) {
  const players = doc.players;
  const [newType, setNewType] = useState<Claim["type"]>("Investigator");
  const selectedName = players[selectedIndex];
  const selectedClaims = selectedName === undefined ? [] : claimIndexesForPlayer(doc, selectedName);

  const addClaim = () => {
    if (selectedName === undefined) return;
    dispatch({ type: "addClaim", claim: makeEmptyClaim(newType, selectedName) });
  };

  return (
    <div className="draw-workbench">
      <section id="claims-panel" className="panel claims-panel">
        <header className="panel-heading-row">
          <div>
            <h3>Claims</h3>
            <span>{selectedClaims.length} for selected player</span>
          </div>
        </header>
        <div className="claim-add-row">
          <ClaimTypeahead value={newType} onChange={setNewType} />
          <select
            aria-label="Claiming player"
            value={selectedName ?? ""}
            onChange={(event) => onSelect(players.indexOf(event.target.value))}
          >
            <option value="">— player —</option>
            {players.map((player) => (
              <option key={player} value={player}>
                {player}
              </option>
            ))}
          </select>
          <button type="button" onClick={addClaim} disabled={selectedName === undefined}>
            + Add claim
          </button>
        </div>
        <div className="selected-claims">
          {selectedName !== undefined && selectedClaims.length === 0 && <p>No claims for {selectedName}.</p>}
          {selectedClaims.map(([claim, index]) => (
            <div key={index} className="claim-block">
              <header>
                <strong>
                  {claim.name} — {roleEmojiLabel(claim.type)}
                </strong>
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
    </div>
  );
}

function TimelineTimingSelect({
  type,
  value,
  onChange,
}: {
  type: TimelineEventType;
  value: string;
  onChange: (timing: string) => void;
}) {
  return (
    <select value={value} onChange={(event) => onChange(event.target.value)}>
      {timingOptionsForType(type, value).map((timing) => (
        <option key={timing} value={timing}>
          {timingLabel(timing)}
        </option>
      ))}
    </select>
  );
}

function TimelinePlayerPicker({
  players,
  value,
  onChange,
  maxSelections,
}: {
  players: readonly string[];
  value: readonly string[];
  onChange: (players: readonly string[]) => void;
  maxSelections?: number;
}) {
  const singleSelection = maxSelections === 1;
  return (
    <div className="timeline-player-picker">
      {players.map((player) => {
        const selected = value.includes(player);
        return (
          <label key={player}>
            <input
              type={singleSelection ? "radio" : "checkbox"}
              name={singleSelection ? "timeline-event-player" : undefined}
              checked={selected}
              onChange={(event) => {
                if (event.target.checked) {
                  if (singleSelection) onChange([player]);
                  else if (!selected && (maxSelections === undefined || value.length < maxSelections))
                    onChange([...value, player]);
                  return;
                }
                if (singleSelection) return;
                onChange(value.filter((name) => name !== player));
              }}
            />
            {player}
          </label>
        );
      })}
    </div>
  );
}

function defaultTimingForType(type: TimelineEventType, currentTiming: string): string {
  if (type === "tinkerDeath") return /^(night|day)_\d+$/.test(currentTiming) ? currentTiming : "day_1";
  if (type === "nightDeath" || type === "resurrection")
    return currentTiming.startsWith("night_") ? currentTiming : "night_2";
  return currentTiming.startsWith("day_") ? currentTiming : "day_1";
}

function timingOptionsForType(type: TimelineEventType, currentTiming: string): readonly string[] {
  const base =
    type === "tinkerDeath"
      ? [...TIMELINE_DAY_OPTIONS, ...TIMELINE_NIGHT_OPTIONS]
      : type === "nightDeath" || type === "resurrection"
        ? TIMELINE_NIGHT_OPTIONS
        : TIMELINE_DAY_OPTIONS;
  return base.includes(currentTiming) ? base : [currentTiming, ...base];
}

function normalizeTimelinePlayers(type: TimelineEventType, players: readonly string[]): readonly string[] {
  const uniquePlayers = players.filter((player, index) => players.indexOf(player) === index);
  return type === "nightDeath" ? uniquePlayers : uniquePlayers.slice(0, 1);
}

function nextTimelineTiming(
  timeline: readonly TimelineEventDoc[],
  type: Extract<TimelineEventType, "execution" | "nightDeath">,
): string {
  const prefix = type === "execution" ? "day" : "night";
  const fallback = type === "execution" ? 1 : 2;
  const latest = timeline.reduce((max, event) => {
    const match = new RegExp(`^${prefix}_(\\d+)$`).exec(event.timing);
    if (match === null) return max;
    return Math.max(max, Number(match[1]));
  }, 0);
  return `${prefix}_${Math.max(fallback, latest + 1)}`;
}

function SetupCountSummary({ setupCounts }: { setupCounts: Record<CharacterType, number> }) {
  return (
    <div className="setup-counts" aria-label="Setup role counts">
      <SetupCountPill label="Townsfolk" count={setupCounts.townsfolk} />
      <SetupCountPill label="Outsider" count={setupCounts.outsider} />
      <SetupCountPill label="Minion" count={setupCounts.minion} tone="evil" />
      <SetupCountPill label="Demon" count={setupCounts.demon} tone="evil" />
    </div>
  );
}

function SetupCountPill({ label, count, tone = "good" }: { label: string; count: number; tone?: "good" | "evil" }) {
  return (
    <span className={`setup-count-pill ${tone}`} aria-label={`${count} ${label}`}>
      <strong>{count}</strong>
      {label}
    </span>
  );
}

function TimelineStrip({
  timeline,
  players,
  selectedIndex,
  onSelect,
  onUpdate,
  onRemove,
  onAdd,
}: {
  timeline: readonly TimelineEventDoc[];
  players: readonly string[];
  selectedIndex: number | undefined;
  onSelect: (index: number | undefined) => void;
  onUpdate: (index: number, event: TimelineEventDoc) => void;
  onRemove: (index: number) => void;
  onAdd: () => void;
}) {
  const deathCount = timeline.reduce((sum, event) => sum + (isTimelineDeathEvent(event) ? event.players.length : 0), 0);
  const selectedEvent = selectedIndex === undefined ? undefined : timeline[selectedIndex];
  return (
    <div id="event-history" className="timeline-strip" aria-label="Puzzle timeline">
      <div className="timeline-main">
        <div className="timeline-legend">
          <div>
            <strong>Event history</strong>
            <span>
              {deathCount} death{deathCount === 1 ? "" : "s"} tracked
            </span>
          </div>
          <button type="button" onClick={onAdd} disabled={players.length === 0}>
            + Add event
          </button>
        </div>
        {timeline.length === 0 ? (
          <p className="timeline-empty">Add an execution, night death, or other public event.</p>
        ) : (
          <ol className="timeline-event-list">
            {timeline.map((event, index) => {
              const deathClass = deathMarkerClass(event);
              const selected = index === selectedIndex;
              return (
                <li key={`${event.timing}-${event.type}-${index}`} className={`timeline-event ${deathClass}`}>
                  <button
                    type="button"
                    className={selected ? "selected" : undefined}
                    aria-pressed={selected}
                    aria-label={`${timingLabel(event.timing)} ${timelineEventAction(event)}: ${event.players.join(", ")}`}
                    onClick={() => onSelect(selected ? undefined : index)}
                  >
                    <span className={`timeline-node ${deathClass}`} aria-hidden="true">
                      {timelineEventGlyph(event)}
                    </span>
                    <span className="timeline-event-card">
                      <strong>
                        {compactTimingLabel(event.timing)} {timelineEventAction(event)}
                      </strong>
                      <span>{formatList(event.players)}</span>
                    </span>
                  </button>
                </li>
              );
            })}
          </ol>
        )}

        {selectedEvent !== undefined && selectedIndex !== undefined && (
          <TimelineEventDetails
            event={selectedEvent}
            players={players}
            onChange={(event) => onUpdate(selectedIndex, event)}
            onRemove={() => onRemove(selectedIndex)}
          />
        )}
      </div>
    </div>
  );
}

function TimelineEventDetails({
  event,
  players,
  onChange,
  onRemove,
}: {
  event: TimelineEventDoc;
  players: readonly string[];
  onChange: (event: TimelineEventDoc) => void;
  onRemove: () => void;
}) {
  const setType = (type: TimelineEventType) => {
    onChange({
      ...event,
      type,
      timing: defaultTimingForType(type, event.timing),
      players: normalizeTimelinePlayers(type, event.players),
      caller: timelineEventHasCaller(type) ? event.caller : undefined,
      sourceActedBeforeDeath: type === "witchCurse" ? event.sourceActedBeforeDeath : undefined,
    });
  };

  return (
    <div className="timeline-event-details">
      <label>
        Cause
        <select value={event.type} onChange={(changeEvent) => setType(changeEvent.target.value as TimelineEventType)}>
          {TIMELINE_EVENT_TYPE_OPTIONS.map((option) => (
            <option key={option.type} value={option.type}>
              {option.label}
            </option>
          ))}
        </select>
      </label>
      <label>
        Timing
        <TimelineTimingSelect
          type={event.type}
          value={event.timing}
          onChange={(timing) => onChange({ ...event, timing })}
        />
      </label>
      <div className="timeline-detail-players">
        <span>Players</span>
        <TimelinePlayerPicker
          players={players}
          value={event.players}
          onChange={(nextPlayers) => onChange({ ...event, players: normalizeTimelinePlayers(event.type, nextPlayers) })}
          maxSelections={event.type === "nightDeath" ? undefined : 1}
        />
      </div>
      {timelineEventHasCaller(event.type) && (
        <label>
          Caller
          <select
            value={event.caller ?? ""}
            onChange={(changeEvent) => onChange({ ...event, caller: changeEvent.target.value || undefined })}
          >
            <option value="">-</option>
            {players.map((player) => (
              <option key={player} value={player}>
                {player}
              </option>
            ))}
          </select>
        </label>
      )}
      {event.type === "witchCurse" && (
        <label>
          <input
            type="checkbox"
            checked={event.sourceActedBeforeDeath ?? false}
            onChange={(changeEvent) =>
              onChange({ ...event, sourceActedBeforeDeath: changeEvent.target.checked || undefined })
            }
          />
          Curse set before Witch died
        </label>
      )}
      <button type="button" onClick={onRemove}>
        Remove Event
      </button>
    </div>
  );
}

function timelineEventHasCaller(type: TimelineEventType): boolean {
  return type === "doomsayerDeath" || type === "witchCurse" || type === "nominationDeath" || type === "slayerShot";
}

function claimIndexesForPlayer(doc: PuzzleDoc, player: string): Array<[Claim, number]> {
  return doc.claims.flatMap((claim, index) => (claim.name === player ? [[claim, index] as [Claim, number]] : []));
}

function mostRecentClaim(claims: Array<[Claim, number]>): Claim | undefined {
  return claims.reduce<[Claim, number] | undefined>(
    (latest, entry) => (latest === undefined || entry[1] > latest[1] ? entry : latest),
    undefined,
  )?.[0];
}

function claimQuoteCardsForDoc(doc: PuzzleDoc): ClaimQuoteCard[] {
  return doc.claims.flatMap((claim, claimIndex) => {
    const playerIndex = doc.players.indexOf(claim.name);
    if (playerIndex === -1) return [];
    return [
      {
        player: claim.name,
        playerIndex,
        claimIndex,
        roleLabel: roleEmojiLabel(claim.type),
        summary: claimSummary(claim),
      },
    ];
  });
}

function mergedQuoteCardsByPlayer(cards: readonly ClaimQuoteCard[]): ClaimQuoteCard[] {
  const mergedCards: ClaimQuoteCard[] = [];
  const cardIndexesByPlayer = new Map<string, number>();

  for (const card of cards) {
    const index = cardIndexesByPlayer.get(card.player);
    if (index === undefined) {
      cardIndexesByPlayer.set(card.player, mergedCards.length);
      mergedCards.push(card);
      continue;
    }

    const existing = mergedCards[index];
    if (existing === undefined) continue;
    const roleLabels = existing.roleLabel.split(", ");
    mergedCards[index] = {
      ...existing,
      roleLabel: roleLabels.includes(card.roleLabel) ? existing.roleLabel : `${existing.roleLabel}, ${card.roleLabel}`,
      summary: `${existing.summary}; ${card.summary}`,
    };
  }

  return mergedCards;
}

function deathMarkerForPlayer(timeline: PuzzleDoc["timeline"], player: string): TimelineEventDoc | undefined {
  const events = timeline ?? [];
  for (let index = events.length - 1; index >= 0; index -= 1) {
    const event = events[index] as TimelineEventDoc;
    if (!event.players.includes(player)) continue;
    if (event.type === "resurrection") return undefined;
    if (isTimelineDeathEvent(event)) return event;
  }
  return undefined;
}

function visibleTimelineEventType(event: TimelineEventDoc): TimelineEventDoc["type"] {
  return event.type;
}

function deathMarkerClass(
  event: TimelineEventDoc,
): "nomination-death" | "witch-curse" | "slayer-shot" | "execution" | "survived-execution" | "night-kill" {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "nomination-death";
  if (type === "witchCurse") return "witch-curse";
  if (type === "slayerShot") return "slayer-shot";
  if (type === "survivedExecution") return "survived-execution";
  if (type === "resurrection") return "survived-execution";
  return type === "execution" ? "execution" : "night-kill";
}

function deathMarkerLabel(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "died while nominating";
  if (type === "witchCurse") return "died to a Witch curse";
  if (type === "slayerShot") return "died to a Slayer shot";
  if (type === "survivedExecution") return "survived execution";
  if (type === "resurrection") return "resurrected";
  if (type === "execution") return "executed";
  if (type === "tinkerDeath") return "died to the Tinker ability";
  return "killed at night";
}

function timelineEventAction(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "Nomination Death";
  if (type === "witchCurse") return "Witch Curse";
  if (type === "slayerShot") return "Slayer Shot";
  if (type === "survivedExecution") return "Survived Execution";
  if (type === "resurrection") return "Resurrection";
  if (type === "execution") return "Execution";
  if (type === "tinkerDeath") return "Tinker Death";
  return event.players.length === 1 ? "Night Death" : "Night Deaths";
}

function timelineEventGlyph(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "!";
  if (type === "witchCurse") return "🪄";
  if (type === "slayerShot") return "🏹";
  if (type === "survivedExecution") return "S";
  if (type === "resurrection") return "↑";
  if (type === "execution") return "X";
  if (type === "tinkerDeath") return "T";
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

function previewSeatIndex(index: number, draggedIndex: number | undefined, dropIndex: number | undefined): number {
  if (draggedIndex === undefined || dropIndex === undefined || draggedIndex === dropIndex || index === draggedIndex)
    return index;
  if (draggedIndex < dropIndex && index > draggedIndex && index <= dropIndex) return index - 1;
  if (draggedIndex > dropIndex && index >= dropIndex && index < draggedIndex) return index + 1;
  return index;
}

function seatButtonStyle(index: number, count: number, player: string): CSSProperties {
  return {
    ...seatPosition(index, count),
    "--seat-name-scale": Math.min(1, 6.6 / Math.max(player.length, 1)).toFixed(3),
  } as CSSProperties;
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

function countSetupRoles(doc: PuzzleDoc): Record<CharacterType, number> {
  if (doc.setup === "none" || doc.setup === "atheist") return countScriptRoles(doc.script);
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
