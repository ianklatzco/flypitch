# Flypitch4 Validation

This directory collects validation notes for the Lean 4 `flypitch4` port.

The top-level `../VALIDATION.md` records the mechanical audit: build status,
axiom output, proof-hole search, and the committed cleanup of the collapse-side
nonsurjection proof.

The notes here focus on mathematical validation: whether the formal objects
match the intended CH-independence argument, where a port could accidentally
weaken the theorem, and which proof bridges deserve the most scrutiny.

## Notes

- `mathematical-audit.md`: math-facing audit of the theorem path, CH statement,
  forcing endpoints, and the collapse-side object bridge.

## Current Status

The strongest evidence gathered so far is:

- `independence_of_CH` builds from compiled Lean proof terms.
- `#print axioms independence_of_CH` reports only
  `[propext, Classical.choice, Quot.sound]`.
- The suspicious omega-to-aleph1 collapse contradiction is now isolated as
  `no_pset_surj_omega_aleph_one`.

The remaining higher-value work is not more grep output. It is statement
comparison: check that the Lean 4 theorem statements are mathematically as
strong as the Lean 3 originals at the CH endpoints and forcing bridges.
