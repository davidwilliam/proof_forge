// The wins ledger as the pages read it: generated/wins.json, written by scripts/wins.mjs from
// results/wins/ledger.json. tests/wins.test.ts fails when the generated file is stale.

import data from "@/generated/wins.json";
import type { WinsData } from "./wins";

export const WINS = data as unknown as WinsData;
