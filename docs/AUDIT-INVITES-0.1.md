# Audit invitations — Morph 0.1.0 (DRAFT, UNSENT)

Sprint 9's hard gate. Nothing here has been sent; the maintainer sends it.
Enclosure: `docs/AUDIT-PACKET-0.1.md`.

## Reviewer profile (per LONGTERM_ROADMAP: 2–3 friendly reviewers)

- PL background: operational semantics, type soundness, or verified
  compilation — able to read Lean 4 and judge a Progress/Preservation claim.
- Verification background: proof engineering at scale — able to assess
  whether 2,081 theorems with 0 sorry/0 axioms actually cover the CLI
  surface, and to spot spec-vs-code gaps (cf. packet §3).
- One reviewer should be comfortable with the Python spec-lint tooling
  (or willing to treat it as out of scope explicitly).

Suggested sources: prior collaborators on the substitution/soundness work,
PL/verification contacts from the community, one cold invite to an
independent Lean practitioner. Names intentionally left blank — fill in.

## What each reviewer receives

1. `docs/AUDIT-PACKET-0.1.md` (scope, proof inventory, trust base, repro).
2. Repo access at the tagged release (`git tag 0.1.0` — cut before sending).
3. The regression snapshot JSON for the tag.
4. This timeline and the findings template below.

## Invite message (template)

> Subject: External review invite — Morph 0.1.0 soundness story
>
> We're inviting 2–3 reviewers for a public audit of Morph 0.1.0's
> verification story: a Lean 4 formalization (2,081 theorems, 0 sorry,
> 0 axioms, 0 build warnings) behind a small CLI
> (`eval/parse/check/run/fmt/doc/version`). Enclosed is the audit
> packet: scope, what is proved vs. trusted, known issues (including a
> resolved spec-overstatement case, #11, with refutations retained in
> history), and one-command reproduction. Review window is three weeks;
findings are
> published with your permission (attributed or anonymous, your choice).
> Of particular value: (a) soundness-proof gaps, (b) spec claims that
> overstate, (c) anything the goldens pin that shouldn't be stable.

## Timeline

- Week 0: tag 0.1.0, freeze packet, send invites with the materials above.
- Weeks 1–3: review window; maintainer available for pipeline/orientation
  questions, no steer on findings.
- Week 4: collect findings, publish (attributed or anonymous per reviewer),
  file follow-ups as spec contradictions or named future work.

## Findings template (sent with the invite)

- Claim reviewed (file/theorem/command):
- Verdict (holds / overstates / false / out of scope):
- Evidence (repro steps or counterexample):
- Severity suggestion (release-blocker / should-fix / note):
