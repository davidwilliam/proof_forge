# Independent developer trial

A developer who did not build ProofForge reproduces a Passport, sees two rejections, and
reads a Passport, starting from a clean machine with only the repository and its README.
The trial measures whether the published instructions and claims hold for someone else.

## Participant

- Has not worked on ProofForge and has not seen its development.
- Has Docker (8 GB of memory available to it), Python 3.12 or later and git. Lean
  experience is not required.
- Has about 60 to 90 minutes.

## Observer rules

- The observer gives repository access and this document, then does not help.
- If the participant is blocked for more than 10 minutes, the observer may help once
  per step. Each intervention is written down with the step, what was said and why.
- Nothing is fixed in the repository during the trial. Problems found are fixed afterwards
  and listed separately from the trial record.

## Steps

Record the start and end time of every step, and copy the full output of any command that
fails.

1. Clone the repository and build the pinned Lean image as the README describes.
2. Check the recorded Muse repair:
   `bin/proofforge check --candidate formal/evidence/muse-repair-002/Solution.lean --out repair.json`.
   Expected: `VERIFIED` for every requirement.
3. Reproduce it: `bin/proofforge verify repair.json --candidate formal/evidence/muse-repair-002/Solution.lean`.
   Expected: all hashes reproduced.
4. Check the seeded bulk-rounding candidate:
   `bin/proofforge check --candidate formal/attacks/g2_bulk_rounding.lean --out g2.json`.
   Expected: property tests pass, the proof check rejects `req_fair_shares`, and the status
   is `UNRESOLVED`. This candidate is a seeded example written for the demonstration; its
   counterexample is in `formal/attacks/g2_bulk_rounding.counterexample.json`.
5. Submit a correct repair together with a weakened copy of the specification. These
   commands change the conservation requirement from "total money is unchanged" (`=`) to
   "total money does not grow" (`≤`), which the one-cent bug satisfies:

   ```
   S=$(mktemp -d)
   mkdir -p "$S/candidate" "$S/spec/Payout"
   cp formal/evidence/muse-repair-002/Solution.lean "$S/candidate/"
   cp formal/spec/Payout/Spec.lean "$S/spec/Payout/"
   perl -pi -e 's/total \(step s r\)\.2 = total s/total (step s r).2 ≤ total s/' "$S/spec/Payout/Spec.lean"
   diff formal/spec/Payout/Spec.lean "$S/spec/Payout/Spec.lean"
   bin/proofforge check --candidate "$S"
   ```

   Expected: `diff` shows the one changed line, and the check exits 1 with
   `protected file modified: spec/Payout/Spec.lean`.
6. Open any Passport on the live demo (for example from the replay on its home page), use
   "Download passport.json" and "Download Solution.lean", put both files in the repository
   root and run `bin/proofforge verify passport.json --candidate Solution.lean`.
   Expected: `reproduced`, or, on a machine whose CPU architecture differs from the
   Passport's `linux/amd64`, `reproduced, except the executable hash`.
7. Open `repair.json` and answer, in your own words:
   - Which requirements are verified, and what does each one state?
   - What does the result rely on (the trust assumptions)?
   - Which part of the executable is tested but not proved?
   - What would you need to do to check this result on your own machine again?

## Questions after the trial

1. Where were the instructions wrong, missing or unclear?
2. Did any result differ from what this document says to expect?
3. Would a check like this be useful in a repository you work on? For which code, and what
   would stop you from using it?
4. Anything else.

## Record

The trial record has the participant's own answers, the step timings, every failed
command's output and every observer intervention, unedited. It is published only with the
participant's consent, and with their name only if they agree.
