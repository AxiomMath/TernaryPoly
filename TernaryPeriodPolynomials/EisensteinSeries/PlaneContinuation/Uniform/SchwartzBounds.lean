module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.TestFamilies

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformSchwartzBounds

variable {Domain Target : Type}
variable [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target] [NormedSpace ℂ Target] [SMulCommClass ℝ ℂ Target]

def Bounded (tests : Set (SchwartzMap Domain Target)) : Prop :=
  ∀ weight order : ℕ, ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ test ∈ tests, SchwartzMap.seminorm ℂ weight order test ≤ bound

theorem bounded_iff_vonN (tests : Set (SchwartzMap Domain Target)) :
    Bounded tests ↔ Bornology.IsVonNBounded ℂ tests := by
  rw [(schwartz_withSeminorms ℂ Domain Target).isVonNBounded_iff_seminorm_bounded]
  constructor
  · intro bounds ⟨weight, order⟩
    obtain ⟨bound, nonnegative, bounded⟩ := bounds weight order
    exact ⟨bound + 1, by linarith, fun test membership => lt_of_le_of_lt (bounded test membership) (by linarith)⟩
  · intro bounds weight order
    obtain ⟨bound, positive, bounded⟩ := bounds (weight, order)
    exact ⟨bound, positive.le, fun test membership => (bounded test membership).le⟩

theorem mono {tests smaller : Set (SchwartzMap Domain Target)} (bounded : Bounded tests) (subset : smaller ⊆ tests) :
    Bounded smaller := by
  intro weight order
  obtain ⟨bound, nonnegative, bounds⟩ := bounded weight order
  exact ⟨bound, nonnegative, fun test membership => bounds test (subset membership)⟩

theorem norm_pow_bound (tests : Set (SchwartzMap Domain Target)) (bounded : Bounded tests) (power : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ test ∈ tests, ∀ point : Domain, ‖point‖ ^ power * ‖test point‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounds⟩ := bounded power 0
  exact ⟨bound, nonnegative, fun test membership point =>
    (SchwartzMap.norm_pow_mul_le_seminorm ℂ test power point).trans (bounds test membership)⟩

theorem image {OtherDomain OtherTarget : Type}
    [NormedAddCommGroup OtherDomain] [NormedSpace ℝ OtherDomain]
    [NormedAddCommGroup OtherTarget] [NormedSpace ℝ OtherTarget]
    [NormedSpace ℂ OtherTarget] [SMulCommClass ℝ ℂ OtherTarget]
    (map : SchwartzMap Domain Target →L[ℂ] SchwartzMap OtherDomain OtherTarget)
    (tests : Set (SchwartzMap Domain Target)) (bounded : Bounded tests) : Bounded (map '' tests) :=
  (bounded_iff_vonN _).mpr (((bounded_iff_vonN tests).mp bounded).image map)

theorem image_family {Parameter : Type} (tests : Parameter → SchwartzMap Domain Target) (parameters : Set Parameter)
    (bounded : ∀ weight order : ℕ, ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameters,
      SchwartzMap.seminorm ℂ weight order (tests parameter) ≤ bound) :
    Bounded (tests '' parameters) := by
  intro weight order
  obtain ⟨bound, nonnegative, bounds⟩ := bounded weight order
  exact ⟨bound, nonnegative, fun _ ⟨parameter, membership, equality⟩ => equality ▸ bounds parameter membership⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformSchwartzBounds
