# STLC metatheory (Agda)

Self-contained STLC developments, used as end-to-end tests for this MCP server
(written and machine-checked by driving the server's tools). No dependencies —
agda-stdlib 2.0 is incompatible with Agda 2.8, so everything is from scratch.

Verify any file with: `agda examples/<file>.agda` (exit 0, no unsolved metas).

| File | Result |
|------|--------|
| `STLC.agda` | Intrinsically-typed STLC; **type soundness** — `progress` (a closed well-typed term is a value or steps) with preservation holding by construction. |
| `Inference.agda` | A **sound and complete bidirectional type checker** — `synth`/`check` return `Dec`, so a `yes` is a typing derivation and a `no` is a proof of untypeability (decidability of typing). |
| `NbE.agda` | **Normalization by evaluation** — `nf`/`normalize` give a β-normal form for every term, plus `soundness`/`completeness` against a Kripke model (the Curry–Howard reading: STLC ≅ intuitionistic implication). |
