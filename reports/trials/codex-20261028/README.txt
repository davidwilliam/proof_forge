ProofForge tester trial, 28 October 2026 (America/New_York)

Verdict: all substantive expectations in docs/TRIAL.md passed on commit
8fa5d2a745e15073f84dad5d94c56cde55d05442. No blocking product defect found.

Participant: Codex, accepted as a tester by the owner. The owner is recruiting
additional testers separately. This was a fresh clone on an existing Apple
Silicon Mac with Docker cache and GitHub authentication, not a cold machine.

Read trial.json for my own answers, exact command timings, findings and limits.
Raw command output is in the numbered logs, including expected rejections.
01-build-premature.log is a test-runner sequencing error, not a product defect.
Browser walk: three flows and 20 page/viewport/theme combinations passed.

Minor findings for the builder, fixed after the trial (T1 in 755457c, T2 in dc8b42a):
T1: --out repair.json still prints/embeds a passport.json reproduction command.
T2: Give non-Lean testers an exact scratch-spec mutation for step 5.
V1: The storyboard should say SOURCE hash matches; that is what the payout UI checks.

No product code was modified during the trial. Screenshots and capture material
were kept outside the repository; paths under that directory are written <trial>/.
Absolute paths and dashes in the logs were normalized with eval/normalize.py.

Measured elapsed times (seconds):
  1a clone: 64.78
  01-build: 5.4
  02-check-repair: 12.18
  03-reproduce-repair: 11.43
  04-seeded-rejection: 7.53
  05-protected-rejection: 4.36
  06-reproduce-download: 11.54

The browser Passport reproduced on ARM64 from a hosted AMD64 result: same
locked manifest, source, requirement statements and statuses; executable tests
passed after rebuilding. The executable hash was explicitly not compared.
