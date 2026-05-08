import Reviser.Demo

/-
  Reviser/Counter.lean — non-monotonicity witnesses.

  The belief set genuinely shrinks across rungs: an element added
  at one rung is removed at a later one. This is what distinguishes
  reviser from climber (monotone) and from defeater (rules stable,
  conclusions vary): the belief set ITSELF is the locus of
  non-monotonicity.
-/

namespace Reviser
namespace Counter

open Demo

/-- **Belief set shrinks**: there exist rungs `m < n` such that
    some belief was in the rung-`m` set and is not in the rung-`n`
    set. Witness: `pos a` is in rung-1 but not in rung-3. -/
theorem belief_set_shrinks :
    ∃ m n : Nat, ∃ b : Belief,
      m < n ∧
      b ∈ demoTower.beliefAt m ∧
      b ∉ demoTower.beliefAt n :=
  ⟨1, 3, .pos "a", by decide,
    by rw [rung1_eq]; decide,
    rung3_retracts_pos_a⟩

/-- **Length witness**: the rung-3 belief set is shorter than the
    rung-2 one — revision can decrease size. (rung 2 has 2 elements;
    rung 3 has 2 elements but with one swapped out — a net retraction
    against rung 1's `pos a`.) -/
theorem rung4_smaller_than_rung2 :
    (demoTower.beliefAt 4).length < (demoTower.beliefAt 2).length := by
  rw [rung2_eq, rung4_eq]
  decide

/-- **Non-monotonicity witness**: every rung is consistent (by the
    headline metatheorem) yet the belief set is genuinely
    non-monotone in the rung index — adding new rungs can both
    grow and shrink the bag. -/
theorem reviser_nonmonotone :
    (∀ n, consistent (demoTower.beliefAt n)) ∧
    (∃ m n b, m < n ∧ b ∈ demoTower.beliefAt m ∧ b ∉ demoTower.beliefAt n) :=
  ⟨demo_consistency, belief_set_shrinks⟩

end Counter
end Reviser
