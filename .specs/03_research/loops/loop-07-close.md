# Loop 07 close-out addendum

The lowerIn_correct proof is deferred to Loop 8+ with complete engineering
notes (see loop-07.md "Proof-engineering notes"). The blocker: Env.update
lacks usable equation lemmas for rw; the `cases hb : (dst == d)` + defeq-have
pattern works but the four write-lemma cases need careful simp-form tuning
per branch. The underlying design (strong agreement, let-lookup-shift,
write-avoidance via supply discipline, evalFuel monotone-success bridging)
is settled — the remaining work is purely mechanical simp-tactic engineering.
