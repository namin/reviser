import Reviser.Tower

/-
  Reviser/Science.lean — scientific theory revision narrative.

  A 5-rung sequence modeling belief change in light of evidence:

    rung 0:  initial conviction:    K = [earthFlat]
    rung 1:  observation:           revise by shipsDisappearAtHorizon
                                    → [earthFlat, shipsDisappearAtHorizon]
    rung 2:  theory abandonment:    revise by ¬earthFlat
                                    → [shipsDisappearAtHorizon, ¬earthFlat]
                                    ← retraction of earthFlat
    rung 3:  new theory:            revise by earthRound
                                    → [shipsDisappearAtHorizon, ¬earthFlat, earthRound]
    rung 4:  corroboration:         revise by satelliteImagery
                                    → [..., satelliteImagery]

  At rung 2, the agent retracts a previously-believed claim
  (earthFlat) in light of accumulating evidence. The Levi identity
  does the work — kernelRevise filters out the conflict and appends
  the new belief. Subsequent rungs add corroborating evidence
  without further retraction.
-/

namespace Reviser
namespace Science

/-- The scientific-theory-revision tower. -/
def scienceTower : BeliefTower where
  initial := [.pos "earthFlat"]
  initial_consistent := by
    intro b hb hflip
    rw [List.mem_singleton] at hb
    subst hb
    rw [List.mem_singleton] at hflip
    exact absurd hflip (by decide)
  steps := [
    .revise kernelRevision (.pos "shipsDisappearAtHorizon"),
    .revise kernelRevision (.neg "earthFlat"),
    .revise kernelRevision (.pos "earthRound"),
    .revise kernelRevision (.pos "satelliteImagery")
  ]

theorem rung0_eq : scienceTower.beliefAt 0 = [.pos "earthFlat"] := rfl

theorem rung1_eq :
    scienceTower.beliefAt 1 =
    [.pos "earthFlat", .pos "shipsDisappearAtHorizon"] := rfl

theorem rung2_eq :
    scienceTower.beliefAt 2 =
    [.pos "shipsDisappearAtHorizon", .neg "earthFlat"] := rfl

theorem rung3_eq :
    scienceTower.beliefAt 3 =
    [.pos "shipsDisappearAtHorizon", .neg "earthFlat", .pos "earthRound"] := rfl

theorem rung4_eq :
    scienceTower.beliefAt 4 =
    [.pos "shipsDisappearAtHorizon", .neg "earthFlat",
     .pos "earthRound", .pos "satelliteImagery"] := rfl

/-- **The retraction at rung 2**: `earthFlat` was the initial
    conviction, but is no longer in the belief set after the
    contrary evidence is admitted. -/
theorem rung2_retracts_earthFlat :
    .pos "earthFlat" ∉ scienceTower.beliefAt 2 := by
  rw [rung2_eq]; decide

/-- **Replacement at rung 3**: a new theory (`earthRound`) joins
    the belief set without conflict. The retracted `earthFlat`
    stays out. -/
theorem rung3_has_earthRound :
    .pos "earthRound" ∈ scienceTower.beliefAt 3 := by
  rw [rung3_eq]; decide

theorem rung3_still_retracts_earthFlat :
    .pos "earthFlat" ∉ scienceTower.beliefAt 3 := by
  rw [rung3_eq]; decide

/-- **Tower consistency**: every rung's belief set is consistent.
    The headline metatheorem applied to this concrete sequence —
    the operator's Consistency postulate is what chains through. -/
theorem science_consistency :
    ∀ n, consistent (scienceTower.beliefAt n) :=
  scienceTower.consistency_preserved

end Science
end Reviser
