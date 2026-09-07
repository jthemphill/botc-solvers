export type Timing = `night_${number}` | `day_${number}`;

export function night(number: number): Timing {
  if (!Number.isInteger(number) || number <= 0) throw new Error(`Night must be a positive integer: ${number}.`);
  return `night_${number}`;
}

export function day(number: number): Timing {
  if (!Number.isInteger(number) || number <= 0) throw new Error(`Day must be a positive integer: ${number}.`);
  return `day_${number}`;
}

export function timingOrder(timing: Timing): number {
  const match = /^(night|day)_([1-9]\d*)$/.exec(timing);
  if (match === null) throw new Error(`Invalid timing '${timing}'.`);
  return Number(match[2]) * 2 + (match[1] === "day" ? 1 : 0);
}

export function followingNight(timing: Timing): Timing | undefined {
  const match = /^day_(\d+)$/.exec(timing);
  if (match === null) return undefined;
  return `night_${Number(match[1]) + 1}` as Timing;
}

export function previousNight(timing: Timing): Timing | undefined {
  const match = /^night_(\d+)$/.exec(timing);
  if (match === null || Number(match[1]) <= 1) return undefined;
  return `night_${Number(match[1]) - 1}` as Timing;
}

export function previousDayForNight(timing: Timing): Timing | undefined {
  const match = /^night_(\d+)$/.exec(timing);
  if (match === null || Number(match[1]) <= 1) return undefined;
  return `day_${Number(match[1]) - 1}` as Timing;
}

export function healthTimingForDayAbility(timing: Timing): Timing {
  const match = /^day_(\d+)$/.exec(timing);
  return match === null ? timing : (`night_${Number(match[1])}` as Timing);
}
