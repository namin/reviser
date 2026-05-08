/-
  Reviser/Object.lean — the belief substrate.

  Atomic literals (positive or negative). A belief set is a list of
  literals — finite, syntactic, no deductive closure. Consistency
  is the decidable property: no atom appears as both `pos` and `neg`.

  Compound formulas would require SAT-decidability in the kernel and
  AGM's full partial-meet machinery. The atomic-literal substrate
  keeps every consistency check structural and gives every postulate
  a list-induction proof.
-/

namespace Reviser

abbrev Atom := String

/-- A belief: a positive literal `pos a` or a negative literal `neg a`. -/
inductive Belief where
  | pos (a : Atom)
  | neg (a : Atom)
  deriving Repr, DecidableEq

namespace Belief

/-- Negation on literals: `(pos a).flip = neg a` and vice versa. -/
def flip : Belief → Belief
  | .pos a => .neg a
  | .neg a => .pos a

@[simp] theorem flip_pos (a : Atom) : (Belief.pos a).flip = .neg a := rfl
@[simp] theorem flip_neg (a : Atom) : (Belief.neg a).flip = .pos a := rfl

@[simp] theorem flip_flip (b : Belief) : b.flip.flip = b := by
  cases b <;> rfl

theorem flip_ne (b : Belief) : b.flip ≠ b := by
  cases b <;> simp [flip]

end Belief

/-- A belief set: a finite list of literals. -/
abbrev BeliefSet := List Belief

/-- A belief set is *consistent* iff for every belief `b` in the set,
    its flip `b.flip` is not also in the set. Decidable; structural. -/
def consistent (B : BeliefSet) : Prop :=
  ∀ b ∈ B, b.flip ∉ B

theorem consistent_nil : consistent ([] : BeliefSet) := by
  intro b hb
  cases hb

/-- If a set is consistent and we filter, it stays consistent —
    filtering can only remove. -/
theorem consistent_filter (B : BeliefSet) (p : Belief → Bool)
    (h : consistent B) : consistent (B.filter p) := by
  intro b hb hflip
  rw [List.mem_filter] at hb hflip
  exact h b hb.1 hflip.1

end Reviser
