import Reviser.Operator

/-
  Reviser/Iterated.lean — iterated revision and operator diversity.

  AGM characterizes a *class* of rational revision operators, not a
  unique one. Two demonstrations here:

  1. **DP1 (idempotence)** — `kernelRevise` satisfies the
     Darwiche-Pearl iterated-revision idempotence postulate
     setEquiv-wise: revising by `b` twice is set-equivalent to
     revising once. The list-level proof carries a duplicate `b`
     that set-equality washes out.

  2. **Multi-operator divergence** — a *pessimistic* revision
     operator satisfies the same four AGM postulates as `kernelRevise`
     yet *disagrees* with it on specific inputs. AGM admits multiple
     rational choices.

  3. **Pessimistic violates DP2** — though AGM-rational, the
     pessimistic operator fails the Darwiche-Pearl postulate that
     constrains iterated revision. AGM doesn't imply DP; iterated
     revision is a strictly stronger theory.
-/

namespace Reviser

/-! ## Set-equivalence on belief sets -/

/-- Two belief sets are *set-equivalent* if they have the same
    members (ignoring order and multiplicity). The natural notion
    of equality for AGM-style postulates, which target what is
    *believed* rather than how it's listed. -/
def setEquiv (B B' : BeliefSet) : Prop := ∀ b, b ∈ B ↔ b ∈ B'

-- Avoid clashing with other `≈` instances; use `setEquiv` directly.

@[refl] theorem setEquiv_refl (B : BeliefSet) : setEquiv B B :=
  fun _ => Iff.rfl

theorem setEquiv_symm {B B' : BeliefSet} (h : setEquiv B B') : setEquiv B' B :=
  fun b => (h b).symm

theorem setEquiv_trans {B B' B'' : BeliefSet}
    (h : setEquiv B B') (h' : setEquiv B' B'') : setEquiv B B'' :=
  fun b => Iff.trans (h b) (h' b)

/-! ## DP1: idempotence of `kernelRevise`

  Revising by the same `b` twice is set-equivalent to revising
  once. The list-level second revision adds a duplicate `b`; set
  equivalence ignores it. -/

theorem kernelRevise_dp1 (B : BeliefSet) (b : Belief) :
    setEquiv (kernelRevise (kernelRevise B b) b) (kernelRevise B b) := by
  intro x
  constructor
  · intro hx
    rw [kernelRevise, List.mem_append] at hx
    cases hx with
    | inl h =>
      rw [List.mem_filter] at h
      exact h.1
    | inr h =>
      rw [List.mem_singleton] at h
      rw [h]
      exact kernelRevise_success B b
  · intro hx
    rw [kernelRevise, List.mem_append]
    by_cases hxb : x = b
    · right
      rw [hxb]
      exact List.mem_singleton.mpr rfl
    · left
      rw [List.mem_filter]
      refine ⟨hx, ?_⟩
      rw [decide_eq_true_iff]
      intro hxbf
      -- x = b.flip, but x ∈ kernelRevise B b. Contradiction.
      rw [hxbf] at hx
      rw [kernelRevise, List.mem_append] at hx
      cases hx with
      | inl hf =>
        rw [List.mem_filter] at hf
        have := hf.2
        rw [decide_eq_true_iff] at this
        exact this rfl
      | inr hsing =>
        rw [List.mem_singleton] at hsing
        exact Belief.flip_ne b hsing

/-! ## A second AGM-rational revision operator: `pessimisticRevise`

  When the new belief conflicts with `K`, drop everything and
  start over with `[b]`. When there is no conflict, expand. This
  is a "drastic" rational reviser — it satisfies all four AGM
  postulates yet disagrees with `kernelRevise` on conflict. -/

def pessimisticRevise (B : BeliefSet) (b : Belief) : BeliefSet :=
  if b.flip ∈ B then [b] else B ++ [b]

theorem pessimisticRevise_success (B : BeliefSet) (b : Belief) :
    b ∈ pessimisticRevise B b := by
  unfold pessimisticRevise
  by_cases h : b.flip ∈ B
  · simp [h]
  · simp [h]

theorem pessimisticRevise_inclusion (B : BeliefSet) (b : Belief) :
    ∀ x ∈ pessimisticRevise B b, x ∈ B ∨ x = b := by
  intro x hx
  unfold pessimisticRevise at hx
  by_cases h : b.flip ∈ B
  · simp [h] at hx
    exact .inr hx
  · simp [h] at hx
    cases hx with
    | inl hxB => exact .inl hxB
    | inr hxb => exact .inr hxb

theorem pessimisticRevise_vacuity (B : BeliefSet) (b : Belief)
    (h : b.flip ∉ B) : pessimisticRevise B b = B ++ [b] := by
  unfold pessimisticRevise
  simp [h]

theorem pessimisticRevise_consistency (B : BeliefSet) (b : Belief)
    (hB : consistent B) : consistent (pessimisticRevise B b) := by
  unfold pessimisticRevise
  by_cases h : b.flip ∈ B
  · simp [h]
    -- consistent [b]: trivial
    intro x hx hflip
    rw [List.mem_singleton] at hx hflip
    rw [hx] at hflip
    exact Belief.flip_ne b hflip
  · simp [h]
    -- consistent (B ++ [b])
    intro x hx hflip
    rw [List.mem_append] at hx hflip
    cases hx with
    | inl hxB =>
      cases hflip with
      | inl hflipB => exact hB x hxB hflipB
      | inr hflipS =>
        rw [List.mem_singleton] at hflipS
        have hxbf : x = b.flip := by
          have := congrArg Belief.flip hflipS
          rw [Belief.flip_flip] at this
          exact this
        rw [hxbf] at hxB
        exact h hxB
    | inr hxS =>
      rw [List.mem_singleton] at hxS
      rw [hxS] at hflip
      cases hflip with
      | inl hflipB => exact h hflipB
      | inr hflipS =>
        rw [List.mem_singleton] at hflipS
        exact Belief.flip_ne b hflipS

/-- The pessimistic operator as a `SoundRevision`. All four AGM
    postulates discharged. -/
def pessimisticRevision : SoundRevision where
  op := pessimisticRevise
  success := pessimisticRevise_success
  inclusion := pessimisticRevise_inclusion
  vacuity := pessimisticRevise_vacuity
  consistency := pessimisticRevise_consistency

/-! ## Multi-operator divergence

  On `K = [pos a, pos b]` revised by `neg a`:
    - `kernelRevise`     gives `[pos b, neg a]` (filters out pos a)
    - `pessimisticRevise` gives `[neg a]`        (drops everything)
  Both are AGM-rational, yet the conclusion sets differ. AGM does
  *not* determine the operator uniquely. -/

theorem pessimistic_disagrees_with_kernel :
    pessimisticRevise [.pos "a", .pos "b"] (.neg "a") ≠
    kernelRevise [.pos "a", .pos "b"] (.neg "a") := by
  decide

/-! ## Pessimistic violates DP2

  AGM's six postulates do not imply DP2 (revision by `¬φ` after
  `φ` collapses). The pessimistic operator is AGM-rational yet
  fails DP2 set-equivalently:

    pessimistic ([pos a, pos b] * neg a) * pos a
      = pessimistic [neg a] * pos a   -- inner conflict drops all
      = [pos a]                        -- inner conflict drops all again

    pessimistic [pos a, pos b] * pos a
      = [pos a, pos b, pos a]          -- no conflict, just expand

  The first contains only `pos a`; the second contains both `pos a`
  and `pos b`. Not set-equivalent.

  This is the keynote-relevant negative finding: AGM-rationality
  does *not* constrain iteration enough; iterated revision (DP) is
  a strictly stronger theory. -/

theorem pessimistic_violates_dp2 :
    ¬ setEquiv
        (pessimisticRevise (pessimisticRevise [.pos "a", .pos "b"] (.neg "a"))
          (.pos "a"))
        (pessimisticRevise [.pos "a", .pos "b"] (.pos "a")) := by
  intro h
  -- LHS = [pos a]; RHS = [pos a, pos b, pos a]. Specialize at pos b.
  have hb := h (.pos "b")
  -- hb : pos b ∈ [pos a] ↔ pos b ∈ [pos a, pos b, pos a]
  have hb_in_RHS : (.pos "b") ∈
      pessimisticRevise [.pos "a", .pos "b"] (.pos "a") := by decide
  have hb_in_LHS := hb.mpr hb_in_RHS
  exact absurd hb_in_LHS (by decide)

end Reviser
