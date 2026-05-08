import Reviser.Object

/-
  Reviser/Operator.lean — operators with rationality bundles.

  An operator carries its AGM-postulate proofs as a typed bundle.
  The kernel admits an operator iff the bundle type-checks. Each
  postulate is a proposition the proposer must discharge; the gate
  doesn't compute or search.

  At the atomic-literal level, AGM revision has a closed form
  (`kernelRevise`): filter out the conflicting literal, append the
  new one. The `filter` is the retraction (Levi's contraction step);
  the `++` is the addition (Levi's expansion step). Four postulates
  fall out by structural induction on the list.
-/

namespace Reviser

/-- A `SoundRevision` operator: a function with the AGM revision
    postulates as a typed bundle. -/
structure SoundRevision where
  /-- The proposed revision function. -/
  op : BeliefSet → Belief → BeliefSet
  /-- Success: `b ∈ op B b`. -/
  success : ∀ B b, b ∈ op B b
  /-- Inclusion: `op B b ⊆ B ∪ {b}` (no spurious additions). -/
  inclusion : ∀ B b, ∀ x ∈ op B b, x ∈ B ∨ x = b
  /-- Vacuity: if `b.flip ∉ B`, then `op B b = B ++ [b]`. -/
  vacuity : ∀ B b, b.flip ∉ B → op B b = B ++ [b]
  /-- Consistency: revising a consistent set yields a consistent set. -/
  consistency : ∀ B b, consistent B → consistent (op B b)

/-- A `SoundContraction` operator: AGM contraction postulates. -/
structure SoundContraction where
  op : BeliefSet → Belief → BeliefSet
  /-- Inclusion: `op B b ⊆ B` (only remove). -/
  inclusion : ∀ B b, ∀ x ∈ op B b, x ∈ B
  /-- Vacuity: if `b ∉ B`, then `op B b = B`. -/
  vacuity : ∀ B b, b ∉ B → op B b = B
  /-- Success: `b ∉ op B b` (the contracted belief is removed). -/
  success : ∀ B b, b ∉ op B b
  /-- Recovery: `B ⊆ (op B b) ∪ {b}` (after contracting then re-adding,
      we get back at least what we had). -/
  recovery : ∀ B b, ∀ x ∈ B, x ∈ op B b ∨ x = b

/-! ## Canonical operators

  At the atomic-literal level, AGM revision and contraction have
  closed forms — partial-meet collapses to single-element removal,
  because the only formula that conflicts with a literal `b` is its
  own flip `b.flip`. -/

/-- Canonical revision: filter out `b.flip` (the only conflict),
    then append `b`. -/
def kernelRevise (B : BeliefSet) (b : Belief) : BeliefSet :=
  (B.filter (fun x => decide (x ≠ b.flip))) ++ [b]

/-- Canonical contraction: filter out `b`. -/
def kernelContract (B : BeliefSet) (b : Belief) : BeliefSet :=
  B.filter (fun x => decide (x ≠ b))

/-! ## Postulates for `kernelRevise` -/

theorem kernelRevise_success (B : BeliefSet) (b : Belief) :
    b ∈ kernelRevise B b := by
  show b ∈ (B.filter _) ++ [b]
  apply List.mem_append.mpr
  exact .inr (List.mem_singleton.mpr rfl)

theorem kernelRevise_inclusion (B : BeliefSet) (b : Belief) :
    ∀ x ∈ kernelRevise B b, x ∈ B ∨ x = b := by
  intro x hx
  rw [kernelRevise, List.mem_append] at hx
  cases hx with
  | inl h =>
    rw [List.mem_filter] at h
    exact .inl h.1
  | inr h =>
    exact .inr (List.mem_singleton.mp h)

theorem kernelRevise_vacuity (B : BeliefSet) (b : Belief)
    (h : b.flip ∉ B) : kernelRevise B b = B ++ [b] := by
  show (B.filter _) ++ [b] = B ++ [b]
  congr 1
  apply List.filter_eq_self.mpr
  intro x hx
  rw [decide_eq_true_iff]
  intro heq
  subst heq
  exact h hx

theorem kernelRevise_consistency (B : BeliefSet) (b : Belief)
    (hB : consistent B) : consistent (kernelRevise B b) := by
  intro x hx hflip
  rw [kernelRevise, List.mem_append] at hx hflip
  cases hx with
  | inl hx_f =>
    rw [List.mem_filter] at hx_f
    cases hflip with
    | inl hflip_f =>
      rw [List.mem_filter] at hflip_f
      exact hB x hx_f.1 hflip_f.1
    | inr hflip_s =>
      have hxf : x.flip = b := List.mem_singleton.mp hflip_s
      have hxb : x = b.flip := by
        have := congrArg Belief.flip hxf
        rw [Belief.flip_flip] at this
        exact this
      subst hxb
      have := hx_f.2
      rw [decide_eq_true_iff] at this
      exact this rfl
  | inr hx_s =>
    have hxb : x = b := List.mem_singleton.mp hx_s
    rw [hxb] at hflip
    cases hflip with
    | inl hflip_f =>
      rw [List.mem_filter] at hflip_f
      have := hflip_f.2
      rw [decide_eq_true_iff] at this
      exact this rfl
    | inr hflip_s =>
      have : b.flip = b := List.mem_singleton.mp hflip_s
      exact Belief.flip_ne b this

/-- The canonical revision operator as a `SoundRevision`. -/
def kernelRevision : SoundRevision where
  op := kernelRevise
  success := kernelRevise_success
  inclusion := kernelRevise_inclusion
  vacuity := kernelRevise_vacuity
  consistency := kernelRevise_consistency

/-! ## Postulates for `kernelContract` -/

theorem kernelContract_inclusion (B : BeliefSet) (b : Belief) :
    ∀ x ∈ kernelContract B b, x ∈ B := by
  intro x hx
  rw [kernelContract, List.mem_filter] at hx
  exact hx.1

theorem kernelContract_vacuity (B : BeliefSet) (b : Belief)
    (h : b ∉ B) : kernelContract B b = B := by
  show B.filter _ = B
  apply List.filter_eq_self.mpr
  intro x hx
  rw [decide_eq_true_iff]
  intro heq
  subst heq
  exact h hx

theorem kernelContract_success (B : BeliefSet) (b : Belief) :
    b ∉ kernelContract B b := by
  intro h
  rw [kernelContract, List.mem_filter] at h
  have := h.2
  rw [decide_eq_true_iff] at this
  exact this rfl

theorem kernelContract_recovery (B : BeliefSet) (b : Belief) :
    ∀ x ∈ B, x ∈ kernelContract B b ∨ x = b := by
  intro x hx
  by_cases hxb : x = b
  · exact .inr hxb
  · left
    rw [kernelContract, List.mem_filter]
    refine ⟨hx, ?_⟩
    exact decide_eq_true_iff.mpr hxb

/-- The canonical contraction operator as a `SoundContraction`. -/
def kernelContraction : SoundContraction where
  op := kernelContract
  inclusion := kernelContract_inclusion
  vacuity := kernelContract_vacuity
  success := kernelContract_success
  recovery := kernelContract_recovery

end Reviser
