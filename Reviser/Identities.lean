import Reviser.Operator

/-
  Reviser/Identities.lean — classical AGM identities.

  Three identities that connect revision and contraction:
    - Levi:    K * φ = (K - ¬φ) + φ
    - Harper:  K - φ = K ∩ (K * ¬φ)
    - Recovery roundtrip: every original belief survives the
      contract-then-expand cycle.

  All three drop out of the kernel definitions with one-step proofs.
  They are the canonical AGM connections, made constructive at the
  literal level.
-/

namespace Reviser

/-- **Levi identity** (constructive form): revising by `b` is the
    same as contracting by `b.flip` and appending `b`. The Levi
    identity says `K * φ = (K - ¬φ) + φ`; here both sides are
    definitionally the same list. -/
theorem levi_identity (B : BeliefSet) (b : Belief) :
    kernelRevise B b = kernelContract B b.flip ++ [b] := rfl

/-- **Harper identity** (set-theoretic form): an element `x` is in
    the contraction `K - b` iff it's in `K` and survives the
    revision by `¬b`. Equivalently `K - φ = K ∩ (K * ¬φ)`.

    At the literal level this is provable element-by-element: the
    right-hand side conjoins (∈ K) with (≠ b ∨ = b.flip), and the
    second disjunct already implies (≠ b) for consistent contexts. -/
theorem harper_identity (B : BeliefSet) (b : Belief) (x : Belief) :
    x ∈ kernelContract B b ↔ x ∈ B ∧ x ∈ kernelRevise B b.flip := by
  constructor
  · -- Forward: if x ∈ K - b, then x ∈ K and x ∈ K * ¬b.
    intro hx
    rw [kernelContract, List.mem_filter] at hx
    obtain ⟨hxB, hxne⟩ := hx
    rw [decide_eq_true_iff] at hxne
    refine ⟨hxB, ?_⟩
    -- Need: x ∈ kernelRevise B b.flip
    -- kernelRevise B b.flip = (B.filter (· ≠ b)) ++ [b.flip]
    rw [kernelRevise, List.mem_append, List.mem_filter]
    left
    refine ⟨hxB, ?_⟩
    rw [decide_eq_true_iff]
    -- need: x ≠ b.flip.flip = b
    rw [Belief.flip_flip]
    exact hxne
  · -- Backward: if x ∈ K and x ∈ K * ¬b, then x ∈ K - b.
    rintro ⟨hxB, hxRev⟩
    rw [kernelRevise, List.mem_append] at hxRev
    rw [kernelContract, List.mem_filter]
    refine ⟨hxB, ?_⟩
    rw [decide_eq_true_iff]
    -- Need: x ≠ b.
    cases hxRev with
    | inl hf =>
      rw [List.mem_filter] at hf
      have := hf.2
      rw [decide_eq_true_iff] at this
      rw [Belief.flip_flip] at this
      exact this
    | inr hsing =>
      rw [List.mem_singleton] at hsing
      rw [hsing]
      exact Belief.flip_ne b

/-- **Recovery roundtrip**: every belief in `K` is recovered after
    contracting by `b` and then expanding by `b` (i.e., appending
    `b` to the contraction). This is AGM Recovery realized
    constructively at the literal level — what the contraction
    threw away is restored by the expansion that follows. -/
theorem recovery_roundtrip (B : BeliefSet) (b : Belief) :
    ∀ x ∈ B, x ∈ kernelContract B b ++ [b] := by
  intro x hx
  cases kernelContract_recovery B b x hx with
  | inl hin => exact List.mem_append.mpr (.inl hin)
  | inr heq => exact List.mem_append.mpr (.inr (List.mem_singleton.mpr heq))

end Reviser
