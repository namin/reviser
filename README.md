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

Sketch. The Lean code is to come; this README pins the shape so
we can react to it before any of it is built. Naming is
provisional — `reviser` parallels climber/defeater, but `agm`,
`revisor`, `believer` are alternatives.

## What will live here

- **`Reviser/Object.lean`** — the belief substrate.
  - `Belief`: `pos a` or `neg a` (atomic literal). The substrate
    is finite: belief sets are lists of literals, not arbitrary
    propositional formulas. This lets us avoid SAT-decidability
    in the kernel and gives all proofs structural shape.
  - `BeliefSet := List Belief`.
  - `consistent`: no atom appears as both `pos` and `neg`. The
    decidable, finite substitute for "deductively closed and
    not entailing ⊥."
  - `Belief.flip`: `pos a ↔ neg a`. The "negation" used by the
    consistency check.

- **`Reviser/Operator.lean`** — operators with rationality bundles.
  - `SoundRevision`: a proposed revision operator
    `op : BeliefSet → Belief → BeliefSet` plus its postulate
    bundle:
    - `success`: `b ∈ op B b`
    - `inclusion`: `op B b ⊆ B ∪ {b}` (no spurious additions)
    - `vacuity`: `b.flip ∉ B → op B b = B ∪ {b}` (no retraction
      when none is needed)
    - `consistency`: `consistent B → consistent (op B b)`
    - `extensionality`: equivalent inputs give equal outputs.
      (Trivial at the literal level — equality is decidable.)

  - `SoundContraction`: a proposed contraction operator with its
    own postulate bundle:
    - `inclusion`: `op B b ⊆ B` (only remove)
    - `vacuity`: `b ∉ B → op B b = B`
    - `success`: `b ∈ op B b → False` (b is removed)
    - `recovery`: `B ⊆ (op B b) ∪ {b}` (after contracting then
      re-adding, get back what you had)
    - `extensionality`.

  - `SoundExpansion`: trivial — just append. Included for
    symmetry; satisfies the trivial set of postulates by rfl.

  - `kernelRevision`: the *canonical* sound revision operator
    `λ B b => (B.filter (· ≠ b.flip)) ++ [b]`. The `filter`
    *is* the retraction; the `++` is the addition. All five
    postulates discharged by structural induction.

- **`Reviser/Tower.lean`** — iterated revision.
  - `BeliefTower`: an initial belief set (with consistency
    proof) plus a rung-indexed sequence of admitted update
    steps. Each step is one of `Revise op b`, `Contract op b`,
    `Expand b`.
  - `BeliefTower.beliefAt n`: the belief set after applying all
    steps up to rung n.
  - `rationality_preserved`: every rung's operator satisfies
    its postulate bundle (immediate from the structures'
    invariants).
  - `consistency_preserved`: **headline metatheorem.** If the
    initial belief set is consistent and every revision input
    is consistent, then every rung is consistent. By induction
    over rungs, applying each operator's `consistency`
    certificate.

- **`Reviser/Demo.lean`** — an end-to-end revision sequence with
  visible retraction.
  - Rung 0: `K = []`.
  - Rung 1: revise by `pos a` → `K = [pos a]`.
  - Rung 2: revise by `pos b` → `K = [pos a, pos b]`.
  - Rung 3: revise by `neg a` → `K = [pos b, neg a]` ← retraction!
  - Rung 4: contract `neg a` → `K = [pos b]` ← explicit retraction.
  - Theorems:
    - `rung3_retracts_a`: `pos a ∉ beliefAt tower 3`.
    - `rung4_pure_contraction`: `neg a ∉ beliefAt tower 4`.
    - `tower_consistency`: every rung is consistent.

- **`Reviser/Counter.lean`** — non-monotonicity witnesses.
  - `belief_set_size_decreases`: between rung 2 and rung 3, the
    belief set lost an element it gained at rung 1. Proof that
    revision is genuinely non-monotonic.
  - `retracted_then_added_back`: after revising by ¬a then
    revising by a again, the original `pos a` belief is back
    (modulo Recovery and Levi).
  - `iterated_revision_not_idempotent`: a sequence that exhibits
    why iterated revision is its own theory (DP postulates).

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
  the line count.
- **Representation theorem (Katsuno-Mendelzon 1991).** Show that
  AGM-rational revision operators correspond to total preorders on
  worlds. The bridge between syntactic postulates and semantic
  spheres-of-similarity. Hard but iconic.
- **Iterated revision (Darwiche-Pearl 1997).** AGM's six postulates
  don't constrain *iteration* enough; DP add four more for
  rational sequences. The tower naturally accommodates iteration —
  what does enforcing DP at the tower level look like?
- **Connection to defeater.** Both are non-monotonic; both gate via
  typed certificates. Is there a translation between them? Can a
  reviser-tower simulate a defeater-tower or vice versa?
- **LLM proposer cascade.** The proposer's job is to propose
  `(op, postulate-bundle)` pairs. The kernel type-checks the bundle.
  An LLM proposer for revision operators — likely small, since the
  literature has standardized recipes — would close the proposer/
  gate loop.
