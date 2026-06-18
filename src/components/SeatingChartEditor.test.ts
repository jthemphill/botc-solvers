import { describe, expect, test } from "bun:test";
import { claimSummary } from "./claimSummary";

describe("claimSummary", () => {
  test("summarizes Slayer no-kill shots with target and timing", () => {
    expect(claimSummary({ type: "Slayer", name: "Adam", timing: "day_3", target: "Matthew", killed: false })).toBe(
      "I shot Matthew on day 3 and nothing happened.",
    );
  });

  test("summarizes timed Empath neighbor pairs", () => {
    expect(
      claimSummary({
        type: "Empath",
        name: "Aoife",
        timing: "night_2",
        count: 1,
        neighbors: ["Adam", "Olivia"],
      }),
    ).toBe("N2: Adam + Olivia -> 1 evil");
  });

  test("summarizes every Fortune Teller check with timing", () => {
    expect(
      claimSummary({
        type: "FortuneTeller",
        name: "Olivia",
        checks: [
          { left: "Aoife", right: "Tim", yes: false, timing: "night_1" },
          { left: "Aoife", right: "Olivia", yes: false, timing: "night_2" },
        ],
      }),
    ).toBe("N1: Aoife + Tim -> no; N2: Aoife + Olivia -> no");
  });
});
