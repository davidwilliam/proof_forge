# Security policy

ProofForge is a judge: a VERIFIED Passport claims that a candidate proves every locked requirement
of its task. A flaw that lets a wrong candidate pass is the most important kind of report.

## In scope

- Soundness of the judge (`harness/`, `bin/proofforge`): a candidate accepted as VERIFIED while a
  requirement does not hold, a forbidden construct that passes the implementation scan, an axiom
  outside `propext`, `Quot.sound` and `Classical.choice` that passes the audit, or a change to a
  locked specification that is not detected.
- Passports: a Passport that `bin/proofforge verify` accepts although its hashes do not match the
  specification, the source or the executable.
- The pull request check (`.github/workflows/proofforge.yml`): a pull request that changes the
  verdict by editing the harness, the lock or the specification, or that runs code outside the
  pinned, network-less Lean image.
- The public API at https://proofforge.fly.dev and the site at https://proofforge.dev.

Out of scope: the incidents themselves (the ported code is vulnerable on purpose and each task's
README says how), and limits the repository already states under "What is proved and what is not"
in the README.

## Reporting

Report privately through GitHub: the repository's Security tab, "Report a vulnerability". Include
the task id, the candidate file and the Passport or command output. Please do not open a public
issue for a soundness flaw before it is fixed.
