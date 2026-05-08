import Reviser.Tower

/-
  Reviser/Demo.lean — five rungs of belief revision with visible
  retraction.

    Rung 0:  K = []
    Rung 1:  revise by pos a   → K = [pos a]
    Rung 2:  revise by pos b   → K = [pos a, pos b]
    Rung 3:  revise by neg a   → K = [pos b, neg a]   ← retraction
    Rung 4:  contract neg a    → K = [pos b]          ← explicit removal

  Each rung's belief set is computed by applying the canonical
  operator with its full postulate bundle. Per-rung equality
  theorems witness the state; `tower_consistency` is the headline
  metatheorem applied to this concrete tower.
-/

namespace Reviser
namespace Demo

/-- The demo tower: five rungs exercising revision and contraction.
    All operator admissions use the canonical kernel operators. -/
def demoTower : BeliefTower where
  initial := []
  initial_consistent := consistent_nil
  steps := [
    .revise kernelRevision (.pos "a"),
    .revise kernelRevision (.pos "b"),
    .revise kernelRevision (.neg "a"),
    .contract kernelContraction (.neg "a")
  ]

/-- **Rung 0**: empty belief set (the initial state). -/
theorem rung0_eq : demoTower.beliefAt 0 = [] := rfl

/-- **Rung 1**: revising by `pos a` from empty is just expansion
    (Vacuity applies — `neg a ∉ []`). -/
theorem rung1_eq : demoTower.beliefAt 1 = [.pos "a"] := rfl

/-- **Rung 2**: revising by `pos b` is again trivial expansion
    (no conflict with current beliefs). -/
theorem rung2_eq : demoTower.beliefAt 2 = [.pos "a", .pos "b"] := rfl

/-- **Rung 3**: revising by `neg a` triggers the Levi identity —
    `kernelRevise` filters out `pos a` (the conflict) and appends
    `neg a`. The retraction is visible as a list operation. -/
theorem rung3_eq : demoTower.beliefAt 3 = [.pos "b", .neg "a"] := rfl

/-- **Rung 4**: contracting by `neg a` removes it without adding
    anything. -/
theorem rung4_eq : demoTower.beliefAt 4 = [.pos "b"] := rfl

/-- **Retraction at rung 3**: `pos a` was concluded at rung 1 but
    is no longer in the belief set at rung 3. The Levi identity's
    contraction step did real work. -/
theorem rung3_retracts_pos_a : .pos "a" ∉ demoTower.beliefAt 3 := by
  rw [rung3_eq]
  decide

/-- **Pure contraction at rung 4**: `neg a` (added at rung 3) is
    explicitly removed at rung 4. -/
theorem rung4_retracts_neg_a : .neg "a" ∉ demoTower.beliefAt 4 := by
  rw [rung4_eq]
  decide

/-- **Tower consistency**: every rung's belief set is consistent.
    Direct corollary of `BeliefTower.consistency_preserved` on the
    concrete tower. -/
theorem demo_consistency : ∀ n, consistent (demoTower.beliefAt n) :=
  demoTower.consistency_preserved

end Demo
end Reviser
