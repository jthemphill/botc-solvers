import { describe, expect, test } from "bun:test";
import { claimSummary } from "./claimSummary";

describe("claimSummary", () => {
  test("summarizes Slayer no-kill shots with target and timing", () => {
    expect(claimSummary({ type: "Slayer", name: "Adam", timing: "day_3", target: "Matthew", killed: false })).toBe(
      "I shot Matthew on day 3 and nothing happened.",
    );
  });

  test("summarizes timed Empath counts", () => {
    expect(
      claimSummary({
        type: "Empath",
        name: "Aoife",
        timing: "night_2",
        count: 1,
      }),
    ).toBe("N2: 1 evil neighbor");
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

  test("uses consistent role-info wording for top-three claims", () => {
    expect(claimSummary({ type: "Investigator", name: "You", role: "Poisoner", among: ["A", "B"] })).toBe(
      "A or B is the Poisoner.",
    );
    expect(claimSummary({ type: "Washerwoman", name: "You", role: "Chef", among: ["A", "B"] })).toBe(
      "A or B is the Chef.",
    );
    expect(claimSummary({ type: "Librarian", name: "You", role: "Drunk", among: ["A", "B"] })).toBe(
      "A or B is the Drunk.",
    );
  });
});
