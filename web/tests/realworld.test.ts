import { describe, expect, it } from "vitest";
import { describeInput, listWords, normalizeRealworld, pendingProjects } from "../lib/realworld";

describe("real-world results", () => {
  it("is empty, not an error, when the generated file is missing or malformed", () => {
    for (const raw of [null, undefined, 3, "x", [], { projects: "x" }]) {
      const rw = normalizeRealworld(raw);
      expect(rw.projects).toEqual([]);
      expect(pendingProjects(rw)).toEqual(["Spliit", "go-money", "moneyphp"]);
    }
  });

  it("keeps the readable projects of a partial file and orders them", () => {
    const rw = normalizeRealworld({
      generated: "2026-10-29",
      projects: [
        { key: "moneyphp", project: "moneyphp/money", versions: [{ tag: "v3.0.9", status: "buggy", cases: 10, violating_cases: 2, witness: null }] },
        { key: "go-money", project: "Rhymond/go-money", versions: [{ tag: "v1.0.6", status: "fixed", cases: 10, violating_cases: 0 }] },
        { key: "half-done", versions: [] },
        { project: "no key" },
      ],
    });
    expect(rw.projects.map((p) => p.name)).toEqual(["go-money", "moneyphp"]);
    expect(pendingProjects(rw)).toEqual(["Spliit"]);
    expect(rw.projects[1]!.versions[0]).toMatchObject({ tag: "v3.0.9", status: "buggy", violating_cases: 2, witness: null });
  });

  it("reads a witness and drops fields of the wrong type", () => {
    const rw = normalizeRealworld({
      projects: [
        {
          key: "go-money",
          versions: [
            {
              tag: "v1.0.5",
              cases: "many",
              by_requirement: { "REQ-SIGN": 3, bad: "x" },
              witness: { requirement: "REQ-SIGN", input: { amount: -2, n: 3 }, output: { shares: [1, 1, 0] }, proved_output: [-1, -1, 0], confirmed_in_lean: true },
            },
          ],
          lean_confirmation: { goals: 9, checked: 9 },
        },
      ],
    });
    const v = rw.projects[0]!.versions[0]!;
    expect(v.cases).toBeNull();
    expect(v.by_requirement).toEqual({ "REQ-SIGN": 3 });
    expect(v.witness?.output).toEqual({ shares: [1, 1, 0], failure: null });
    expect(rw.projects[0]!.leanConfirmation).toEqual({ goals: 9, checked: 9 });
  });

  it("describes inputs in words", () => {
    expect(describeInput({ amount: -2, n: 3 })).toBe("-2 split 3 ways");
    expect(describeInput({ amount: 5, ratios: [0, 7, 3] })).toBe("5 allocated by ratios 0, 7, 3");
    expect(describeInput({ expenses: [1] })).toBe('{"expenses":[1]}');
    expect(listWords(["Spliit", "go-money", "moneyphp"])).toBe("Spliit, go-money and moneyphp");
  });
});
