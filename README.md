# reviser

A reasonable-reflection artifact in the **belief-update** shape: a
system whose belief set evolves under proposer/gate control, with
each rung admitting a revision (or contraction or expansion)
operator whose **rationality** as an update rule is kernel-blessed
by an independent bundle of typed postulates.

> **Climber checks theory construction; defeater checks
> theory qualification; reviser checks belief revision.**

The proposer (an LLM, in the full version) does not propose new
beliefs as raw data. It proposes **revision *operators*** —
functions `op : BeliefSet → Formula → BeliefSet` together with
proofs that the operator satisfies the AGM rationality postulates.
The kernel admits or refuses based on whether the postulate bundle
type-checks. Admitted operators may be invoked at later rungs to
update the belief set; the tower captures the resulting epistemic
dynamics.

This is the LCF discipline applied not to proof construction nor to
proof-system construction nor to qualification, but to **rational
belief change** — the keynote architecture pushed one level of
abstraction up: the modification is itself a function with
typed-rationality content, and the gate checks the rationality of
the strategy, not just of a single move.

In the keynote portfolio:

| artifact | what the gate governs |
|---|---|
| lean-grey | evaluator modification |
| lean-green | causal `set!` on a heap cell |
| LeanDisco | discovery of theorems and heuristics |
| sc-mini | program-transformation rewrites |
| climber | the right to extend the proof system |
| defeater | the right to qualify conclusions |
| **reviser** | **the right to revise beliefs rationally** |

## The structural bet

Forty years of philosophical literature (Alchourrón-Gärdenfors-
Makinson 1985, Katsuno-Mendelzon 1991, Darwiche-Pearl 1997) has
characterized which belief-update operators count as *rational*
via postulates. We treat each postulate as a typed proof
obligation. An operator gets admitted iff its postulate bundle
type-checks against the kernel. Iterated revision becomes a tower.

The non-monotonicity here lives at a different layer than
defeater's: defeater's tower has stable rules but conclusions
that vanish when defeated. Reviser's tower has the *belief set
itself* shrink when retraction happens. **Defeater models what
gets inferred; reviser models what gets believed.** Two different
sites of non-monotonicity, both gated by typed certificates.

## Status

Built. Eight library files compile end-to-end on Lean 4.29.1 with
no `sorry` and no added axioms. Smoke executable runs and prints
the load-bearing theorem catalog.

## What lives here

- **`Reviser/Object.lean`** — the belief substrate.
  - `Belief`: `pos a` or `neg a` (atomic literal).
  - `BeliefSet := List Belief`.
  - `consistent`: no atom appears as both `pos` and `neg` — the
    decidable, finite substitute for deductive closure + ⊥.
  - `Belief.flip`: `pos a ↔ neg a`. Used by the consistency check.
  - `consistent_filter`: filtering preserves consistency.

- **`Reviser/Operator.lean`** — operators with rationality bundles.
  - `SoundRevision`: a proposed function plus AGM postulates —
    *success*, *inclusion*, *vacuity*, *consistency*. The kernel
    admits iff the bundle type-checks.
  - `SoundContraction`: contraction postulates — *inclusion*,
    *vacuity*, *success*, *recovery*.
  - `kernelRevise B b := (B.filter (· ≠ b.flip)) ++ [b]` — the
    *filter* is Levi's contraction step; the *append* is expansion.
  - `kernelContract B b := B.filter (· ≠ b)`.
  - `kernelRevision : SoundRevision`, `kernelContraction : SoundContraction` —
    canonical operators with all postulates discharged.

- **`Reviser/Identities.lean`** — classical AGM identities.
  - `levi_identity`: `kernelRevise B b = kernelContract B b.flip ++ [b]`.
    Provable by `rfl` — the Levi identity falls out of the
    definitions. The constructive form of `K * φ = (K - ¬φ) + φ`.
  - `harper_identity`: `x ∈ kernelContract B b ↔ x ∈ B ∧ x ∈ kernelRevise B b.flip`.
    The set-theoretic form of `K - φ = K ∩ (K * ¬φ)`.
  - `recovery_roundtrip`: every belief in `K` survives the
    contract-by-`b` then expand-by-`b` cycle. AGM Recovery
    realized constructively at the literal level.

- **`Reviser/Tower.lean`** — iterated revision as a tower.
  - `Step`: revision or contraction (each carrying its sound
    operator and target literal).
  - `applyStep_preserves_consistent`: each step preserves
    consistency.
  - `BeliefTower`: initial consistent belief set + finite step
    list.
  - `BeliefTower.beliefAt n`: fold of first `n` steps over
    initial.
  - `BeliefTower.consistency_preserved`: **headline metatheorem.**
    Every rung is consistent. The `consistency` postulate of each
    step's operator is what chains through.

- **`Reviser/Demo.lean`** — five-rung sequence with visible
  retraction.
  - Rung 0: `K = []`. Rung 1: revise `pos a`. Rung 2: revise
    `pos b`. Rung 3: revise `neg a` (retracts `pos a`). Rung 4:
    contract `neg a`.
  - Per-rung equality theorems (`rung0_eq` … `rung4_eq`),
    retraction witnesses (`rung3_retracts_pos_a`,
    `rung4_retracts_neg_a`), `demo_consistency`.

- **`Reviser/Science.lean`** — scientific theory revision narrative.
  - `K = [earthFlat]` → revise `shipsDisappearAtHorizon` → revise
    `¬earthFlat` (retraction) → revise `earthRound` → revise
    `satelliteImagery`.
  - Per-rung equality theorems plus `rung2_retracts_earthFlat`,
    `rung3_has_earthRound`, `science_consistency`.
  - The textbook narrative for AGM dynamics — initial conviction,
    evidence, theory abandonment, replacement, corroboration.

- **`Reviser/Iterated.lean`** — iterated revision and operator
  diversity.
  - `setEquiv`: equality up to set membership (the natural
    equality for AGM-style postulates that target *what is
    believed*, not how it's listed).
  - `kernelRevise_dp1`: `kernelRevise (kernelRevise B b) b ≈ kernelRevise B b`.
    Idempotence under `setEquiv` — the second revision adds a
    duplicate that set-equality washes out.
  - `pessimisticRevise B b := if b.flip ∈ B then [b] else B ++ [b]` —
    when conflict, drop everything; when no conflict, expand.
  - `pessimisticRevision : SoundRevision` — a SECOND AGM-rational
    operator with all four postulates discharged.
  - `pessimistic_disagrees_with_kernel`: on `[pos a, pos b] * neg a`,
    the two operators give different outputs (`[pos b, neg a]` vs
    `[neg a]`). **AGM doesn't determine the operator uniquely.**
  - `pessimistic_violates_dp2`: `pessimisticRevise` is AGM-rational
    yet fails Darwiche-Pearl's DP2 postulate. **AGM doesn't
    constrain iteration** — iterated revision (DP) is a strictly
    stronger theory. Concrete Lean witness, parallel to defeater's
    `Oscillate.lean` finding.

- **`Reviser/Counter.lean`** — non-monotonicity witnesses.
  - `belief_set_shrinks`: there exist rungs `m < n` and a belief
    that's in rung-`m`'s set but not in rung-`n`'s.
  - `rung4_smaller_than_rung2`: a length witness.
  - `reviser_nonmonotone`: every rung consistent yet the belief
    set is genuinely non-monotone in the rung index.

## Headline picture

```
              K₀ = []
              │
              │ rung 1: revise by pos a  (Vacuity: trivial expansion)
              ↓
              K₁ = {pos a}
              │
              │ rung 2: revise by pos b  (Vacuity: trivial expansion)
              ↓
              K₂ = {pos a, pos b}
              │
              │ rung 3: revise by neg a  (Levi: retract pos a, then add neg a)
              ↓
              K₃ = {pos b, neg a}        ← retraction visible
              │
              │ rung 4: contract neg a   (pure removal, no addition)
              ↓
              K₄ = {pos b}
```

Each rung's operator carries its postulate bundle — the kernel
checked the bundle at admission. The tower records the audit trail:
which operator at which rung, with what rationality theory.

## Relation to climber and defeater

| | climber | defeater | reviser |
|---|---|---|---|
| polarity | extending | qualifying | revising |
| modification | axiom-schema + soundness cert | exception-schema + defeasibility cert | *operator* + rationality bundle |
| substrate | derivation calculus | rules + facts → conclusions | belief set |
| headline | `climb_sound` | `rung_sound` | `consistency_preserved` |
| monotonicity | strictly monotone | non-monotone (rules blocked) | non-monotone (beliefs retracted) |
| non-monotonicity site | (none) | conclusion level | belief level |
| modification shape | static schema | static schema | dynamic operator |

Same kernel discipline (typed certificate, kernel admits or
refuses); three substrates; three polarities of modification. The
keynote's "the architecture is substrate-agnostic" claim becomes
a triad rather than a single example.

## What's novel about reviser specifically

1. **The modification is a *function*, not a schema.** Climber's
   `SoundExtension` and defeater's `SoundDefeater` carry static
   declarative content (a predicate on formulas, a trigger atom).
   Reviser's `SoundRevision` carries an actual function with its
   rationality theory. The proposer/gate pattern at the
   meta-operator level.

2. **The certificate is a *bundle of postulates*, not a single
   proof.** AGM's five-postulate characterization becomes a typed
   product. The kernel admits iff the whole bundle type-checks.

3. **The tower captures genuine epistemic dynamics.** Each rung
   is one belief-update step in time; the sequence is the agent's
   epistemic history. Connects to keynote §4.2 (semantics of
   evolving systems) directly — belief revision IS the textbook
   evolving system.

4. **Retraction is first-class.** Unlike climber (monotone), and
   distinct from defeater (where rules are stable but conclusions
   vary), reviser's belief set itself can shrink when revising by
   contradictory evidence. The Levi identity makes retraction
   automatic during revision; explicit `SoundContraction` is its
   sibling.

5. **AGM's underdetermination is constructive.** The postulates
   characterize a *class* of operators, not a unique one.
   `Iterated.lean` exhibits two AGM-rational operators
   (`kernelRevision` and `pessimisticRevision`) that disagree on
   the same input — and shows that the pessimistic one *violates*
   Darwiche-Pearl's DP2. The "AGM doesn't constrain iteration"
   point becomes a Lean witness, parallel to defeater's period-2
   oscillation: a structural counterexample showing the theory's
   limit.

## Scope (design choices made)

- **Atomic-literal substrate.** Beliefs are `pos a` / `neg a` for
  string atoms. No compound formulas. This sidesteps SAT-decidability
  in the kernel — every check is structural induction on a list.
- **Finite belief sets.** Belief sets are `List Belief`, not arbitrary
  closed sets of formulas. Deductive closure is finite-list
  closure (just the literals stored).
- **Single fixed proposer-side env.** No semantic interpretation; the
  postulates are all syntactic. This matches AGM's "syntactic"
  presentation rather than the model-theoretic (worlds-and-spheres)
  one.
- **Append-only tower history.** Rungs aren't deleted; later
  revisions can effectively undo earlier ones, but the rung
  structure remembers the full update history.

## Open questions

- **Full propositional substrate.** Move from atomic literals to
  arbitrary propositional formulas. Requires SAT-decidability and
  the AGM machinery for partial-meet contraction. Probably 2–3×
  the line count. Full DP3/DP4 require this — they reference
  `φ ∧ ψ` and entailment.
- **Representation theorem (Katsuno-Mendelzon 1991).** Show that
  AGM-rational revision operators correspond to total preorders on
  worlds. The bridge between syntactic postulates and semantic
  spheres-of-similarity. Hard but iconic.
- **Full Darwiche-Pearl postulates.** `Iterated.lean` proves DP1
  for `kernelRevise` and exhibits a DP2 violation by
  `pessimisticRevise`. DP3 and DP4 require compound formulas;
  fully formalizing the DP family would let us *gate* operators
  on iterated-revision rationality, not just AGM.
- **Connection to defeater.** Both are non-monotonic; both gate via
  typed certificates. Is there a translation between them? Can a
  reviser-tower simulate a defeater-tower or vice versa?
- **LLM proposer cascade.** The proposer's job is to propose
  `(op, postulate-bundle)` pairs. The kernel type-checks the bundle.
  An LLM proposer for revision operators — likely small, since the
  literature has standardized recipes — would close the proposer/
  gate loop.
