# Audit invite — send-ready draft (S9, UNSENT)

Maintainer: replace each `[NAME]` slot and send. Everything else is
filled from the pinned commit. No personal data in this file — keep it
that way (names live in the sent mail only).

## Filled values (do not edit without re-pinning)

- Pinned commit: `f24ee3156dbda3df37a76568ceec645bf6f337b9`
  (`git log --oneline -1` on `origin/main` reads
  `f24ee31 S9 audit prep: packet refreshed, corpus-rot fixed, snapshot cut`).
- Snapshot: `.reports/regression/snapshot-20261125-150036.json`
  (2609 theorems, 844 pytest, 0/0/0 Lean, 0 sorry/stubs,
  cross-refs 2037/2037, `check.sh` 22/22 — all measured on the pin).
- Packet: `docs/AUDIT-PACKET-0.1.md` at the pinned commit.
- Send date (Week 0): 2026-11-26. Review window: 2026-11-27 →
  2026-12-18 (three weeks, findings due Friday). Week 4
  (collect/publish): week of 2026-12-19.
- CI on the pin: Nightly Full Build, success, on `f24ee31` exactly.

## Send checklist

- [ ] 2–3 reviewer names filled in below (profile: see invites doc —
      PL soundness reader, proof-engineering-at-scale reader, one
      tooling-comfortable reader; one cold/independent invite preferred).
- [ ] Each reviewer gets: this email + packet + snapshot JSON +
      findings template (all pinned above) + repo access (public read
      at the pinned commit suffices unless the reviewer needs more).
- [ ] Maintainer available for pipeline/orientation questions during
      Weeks 1–3, no steer on findings.
- [ ] Nothing merges to `main` that the review contests until S11
      adjudication closes (D3/D4 drafting stays deferred regardless).

## The email (one per reviewer)

> Subject: External review invite — Morph 0.1.0 soundness story
>
> Dear [NAME],
>
> We're inviting 2–3 reviewers for a public audit of Morph 0.1.0's
> verification story: a Lean 4 formalization (2,609 theorems, 0 sorry,
> 0 axioms, 0 build warnings) behind a small CLI
> (`eval/parse/check/run/fmt/doc/version`). Enclosed is the audit
> packet: scope, what is proved vs. trusted, known issues (including a
> resolved spec-overstatement case, #11, with refutations retained in
> history), and one-command reproduction. Review window is three weeks
> (2026-11-27 → 2026-12-18); findings are published with your
> permission (attributed or anonymous, your choice). Of particular
> value: (a) soundness-proof gaps, (b) spec claims that overstate,
> (c) anything the goldens pin that shouldn't be stable.
>
> Reviewing commit: `f24ee31`
> (`f24ee3156dbda3df37a76568ceec645bf6f337b9`).
> Evidence: `docs/AUDIT-PACKET-0.1.md` and
> `.reports/regression/snapshot-20261125-150036.json`, both at that
> commit. Repro from a clean checkout:
> `lake build Morph Morph.Tests`, `python3 -m pytest -q`,
> `bash tests/codegen/check.sh` (expect 22/22).
>
> One procedural note: per our release rules the 0.1.0 tag is cut
> only *after* the review closes. Before publication we will ask you
> to re-verify the tag against this pinned commit (packet unchanged,
> metrics reproduce).
>
> Findings template ( verdict per claim — holds / overstates / false /
> out of scope — plus repro steps or counterexample, plus severity:
> release-blocker / should-fix / note ).
>
> Thank you for considering it.

## After sending

Reply to the reviewer thread with the send date; S9 closes on send.
S10 opens when the first findings land (triage against the three
recorded provisional defaults first: scrub-in-`free`, D-9 supersede,
D-8 Reading A).
