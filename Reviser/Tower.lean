import Reviser.Operator

/-
  Reviser/Tower.lean — iterated revision as a tower.

  Each rung admits one update step (revision or contraction). The
  belief set at rung n is the result of folding the first n steps
  over the initial set. The headline `consistency_preserved`
  metatheorem says: a consistent initial set + admitted operators
  ⇒ every rung is consistent.

  Each step's `Sound...` operator carries its postulate bundle. The
  consistency-postulate is what `consistency_preserved` chains
  through the tower; the other postulates are checked at admission
  but don't enter the chained metatheorem.
-/

namespace Reviser

/-- A belief-update step: either a revision or a contraction. Each
    carries its sound operator (with the full postulate bundle) and
    the input literal. -/
inductive Step where
  | revise (op : SoundRevision) (b : Belief) : Step
  | contract (op : SoundContraction) (b : Belief) : Step

/-- Apply a single step to a belief set. -/
def applyStep (B : BeliefSet) : Step → BeliefSet
  | .revise op b => op.op B b
  | .contract op b => op.op B b

/-- Each step preserves consistency. The proof unpacks the operator's
    postulate bundle: the consistency postulate for revision; the
    inclusion postulate for contraction (only removes, can't break
    consistency that the input had). -/
theorem applyStep_preserves_consistent (B : BeliefSet) (step : Step)
    (h : consistent B) : consistent (applyStep B step) := by
  cases step with
  | revise op b => exact op.consistency B b h
  | contract op b =>
    intro x hx hflip
    have hx_in_B := op.inclusion B b x hx
    have hflip_in_B := op.inclusion B b x.flip hflip
    exact h x hx_in_B hflip_in_B

/-- A `BeliefTower`: an initial consistent belief set plus a finite
    sequence of admitted update steps. -/
structure BeliefTower where
  initial : BeliefSet
  initial_consistent : consistent initial
  steps : List Step

namespace BeliefTower

/-- The belief set at rung `n`: fold the first `n` steps over the
    initial set. For `n ≥ steps.length`, this gives the final state. -/
def beliefAt (T : BeliefTower) (n : Nat) : BeliefSet :=
  (T.steps.take n).foldl applyStep T.initial

@[simp] theorem beliefAt_zero (T : BeliefTower) :
    T.beliefAt 0 = T.initial := by
  show (T.steps.take 0).foldl applyStep T.initial = T.initial
  simp

end BeliefTower

/-- Folding `applyStep` preserves consistency. -/
theorem foldl_applyStep_consistent (B : BeliefSet) (steps : List Step)
    (h : consistent B) : consistent (steps.foldl applyStep B) := by
  induction steps generalizing B with
  | nil => exact h
  | cons step rest ih =>
    show consistent ((step :: rest).foldl applyStep B)
    show consistent (rest.foldl applyStep (applyStep B step))
    exact ih (applyStep B step) (applyStep_preserves_consistent B step h)

/-- **Headline metatheorem.** Every rung's belief set is consistent.
    By induction over the fold; each step's operator certificate
    discharges one consistency-preservation step. -/
theorem BeliefTower.consistency_preserved (T : BeliefTower) (n : Nat) :
    consistent (T.beliefAt n) := by
  show consistent ((T.steps.take n).foldl applyStep T.initial)
  exact foldl_applyStep_consistent T.initial _ T.initial_consistent

end Reviser
