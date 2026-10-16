module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Central
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Cusp

@[expose] public section


/-!
# The scalar cuspidal fields for adelic lifts and their right translates

`IsCuspidalLike χ φ` bundles the four scalar fields `leftRational`, `central`, `bounded` and
`cuspidal` of `GeneralEisenstein.CuspidalRepresentation`.  It holds for every adelic lift
`adelicLift f`, is stable under right translation (so passes to the span of right translates)
and under linear combinations.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

/-- The scalar fields of `CuspidalRepresentation.realize v`, for a given central character. -/
structure IsCuspidalLike (χ : Adelesˣ →* ℂ) (φ : BinaryAdelicGL → ℂ) : Prop where
  leftRational : ∀ (γ : BinaryRationalGL) (x : BinaryAdelicGL),
    φ (GeneralLinearGroup.map rationalAdele γ * x) = φ x
  central : ∀ (t : Adelesˣ) (x : BinaryAdelicGL),
    φ (GeneralLinearGroup.scalar (Fin 2) t * x) = χ t * φ x
  bounded : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C
  cuspidal : ∀ g : BinaryAdelicGL,
    IntegrableOn (fun u => φ (binaryUnipotent u * g)) additiveDomain adeleMeasure ∧
      (∫ u in additiveDomain, φ (binaryUnipotent u * g) ∂adeleMeasure) = 0

namespace IsCuspidalLike

variable {χ : Adelesˣ →* ℂ} {φ ψ : BinaryAdelicGL → ℂ}

/-- Right translates inherit all four fields. -/
theorem translate (h : IsCuspidalLike χ φ) (g₀ : BinaryAdelicGL) :
    IsCuspidalLike χ (fun x => φ (x * g₀)) where
  leftRational γ x := by
    rw [mul_assoc]
    exact h.leftRational γ (x * g₀)
  central t x := by
    rw [mul_assoc]
    exact h.central t (x * g₀)
  bounded := by
    obtain ⟨C, hC⟩ := h.bounded
    exact ⟨C, fun x => hC _⟩
  cuspidal g := by
    simpa only [mul_assoc] using h.cuspidal (g * g₀)

theorem add (h : IsCuspidalLike χ φ) (h' : IsCuspidalLike χ ψ) :
    IsCuspidalLike χ (φ + ψ) where
  leftRational γ x := by
    simp only [Pi.add_apply, h.leftRational, h'.leftRational]
  central t x := by
    simp only [Pi.add_apply, h.central, h'.central, mul_add]
  bounded := by
    obtain ⟨C, hC⟩ := h.bounded
    obtain ⟨C', hC'⟩ := h'.bounded
    exact ⟨C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩
  cuspidal g := by
    obtain ⟨i1, z1⟩ := h.cuspidal g
    obtain ⟨i2, z2⟩ := h'.cuspidal g
    refine ⟨Integrable.add i1 i2, ?_⟩
    simp only [Pi.add_apply]
    rw [integral_add i1 i2, z1, z2, add_zero]

theorem smul (c : ℂ) (h : IsCuspidalLike χ φ) : IsCuspidalLike χ (c • φ) where
  leftRational γ x := by
    simp only [Pi.smul_apply, h.leftRational]
  central t x := by
    simp only [Pi.smul_apply, h.central, smul_eq_mul]
    ring
  bounded := by
    obtain ⟨C, hC⟩ := h.bounded
    refine ⟨‖c‖ * C, fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  cuspidal g := by
    obtain ⟨i1, z1⟩ := h.cuspidal g
    refine ⟨Integrable.const_mul i1 c, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, z1, mul_zero]

theorem zero : IsCuspidalLike χ (0 : BinaryAdelicGL → ℂ) where
  leftRational _ _ := rfl
  central _ _ := by simp
  bounded := ⟨0, fun x => by simp⟩
  cuspidal _ := ⟨integrableOn_zero, by simp⟩

end IsCuspidalLike

/-- The functions satisfying the four scalar fields with central character `χ`. -/
def cuspidalLikeSubmodule (χ : Adelesˣ →* ℂ) : Submodule ℂ (BinaryAdelicGL → ℂ) where
  carrier := {φ | IsCuspidalLike χ φ}
  add_mem' h h' := h.add h'
  zero_mem' := IsCuspidalLike.zero
  smul_mem' c _ h := h.smul c

/-- Every adelic lift of a weight-`k` cusp form of `Γ₁(3)` has the four scalar fields. -/
theorem adelicLift_isCuspidalLike {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    IsCuspidalLike (centralChar k) (adelicLift f) where
  leftRational := adelicLift_leftRational f
  central := adelicLift_central f
  bounded := adelicLift_bounded f
  cuspidal := adelicLift_cuspidal f

/-- The right translate `x ↦ φ_f (x g₀)` has the four scalar fields. -/
theorem adelicLift_translate_isCuspidalLike {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (g₀ : BinaryAdelicGL) :
    IsCuspidalLike (centralChar k) (fun x => adelicLift f (x * g₀)) :=
  (adelicLift_isCuspidalLike f).translate g₀

/-- The span of all right translates of lifts of weight-`k` cusp forms satisfies the fields. -/
theorem span_translates_le {k : ℤ} (S : Set (CuspForm binaryRealGammaOneThree k)) :
    Submodule.span ℂ {φ | ∃ f ∈ S, ∃ g₀ : BinaryAdelicGL, φ = fun x => adelicLift f (x * g₀)} ≤
      cuspidalLikeSubmodule (centralChar k) := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨f, -, g₀, rfl⟩
  exact adelicLift_translate_isCuspidalLike f g₀

end TernaryPeriodPolynomials.CuspIntegral
