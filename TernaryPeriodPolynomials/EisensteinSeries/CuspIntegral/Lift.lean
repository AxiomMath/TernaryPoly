module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Decomposition
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.RealLift

@[expose] public section


/-!
# The adelic lift of a `Γ₁(3)` cusp form

`adelicLift f g = liftReal f r` for any decomposition `g = γ r κ` with `γ ∈ GL₂(ℚ)`,
`r ∈ GL₂(ℝ)⁺`, `κ ∈ K'`; well defined by `isDecomp_eq` and `liftReal_gamma1`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

open Classical in
/-- The adelic lift of a weight-`k` cusp form for `Γ₁(3)`. -/
def adelicLift {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (g : BinaryAdelicGL) : ℂ :=
  if h : ∃ p : BinaryRationalGL × BinaryRealGL × BinaryFiniteGL, IsDecomp g p.1 p.2.1 p.2.2 then
    liftReal f h.choose.2.1
  else 0

theorem adelicLift_eq_of_isDecomp {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    {g : BinaryAdelicGL} {γ : BinaryRationalGL} {r : BinaryRealGL} {κ : BinaryFiniteGL}
    (h : IsDecomp g γ r κ) : adelicLift f g = liftReal f r := by
  have hex : ∃ p : BinaryRationalGL × BinaryRealGL × BinaryFiniteGL,
      IsDecomp g p.1 p.2.1 p.2.2 := ⟨(γ, r, κ), h⟩
  unfold adelicLift
  rw [dite_eq_left hex]
  have hc := hex.choose_spec
  obtain ⟨δ, hδ, -, hr⟩ := isDecomp_eq hc h
  rw [hr]
  exact (liftReal_gamma1 f δ hδ _ hc.1).symm

theorem adelicLift_eq {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (g : BinaryAdelicGL) :
    ∃ r : BinaryRealGL, 0 < (GeneralLinearGroup.det r : ℝˣ).val ∧
      adelicLift f g = liftReal f r := by
  obtain ⟨γ, r, κ, h⟩ := exists_isDecomp g
  exact ⟨r, h.1, adelicLift_eq_of_isDecomp f h⟩

theorem isDecomp_ratGL_mul {g : BinaryAdelicGL} {γ : BinaryRationalGL} {r : BinaryRealGL}
    {κ : BinaryFiniteGL} (h : IsDecomp g γ r κ) (γ' : BinaryRationalGL) :
    IsDecomp (ratGL γ' * g) (γ' * γ) r κ := by
  refine ⟨h.1, h.2.1, ?_⟩
  rw [map_mul, h.2.2, mul_assoc]

theorem isDecomp_mul_levelGroup {g : BinaryAdelicGL} {γ : BinaryRationalGL} {r : BinaryRealGL}
    {κ : BinaryFiniteGL} (h : IsDecomp g γ r κ) {κ' : BinaryFiniteGL} (hκ' : κ' ∈ levelGroup) :
    IsDecomp (g * finGL κ') γ r (κ * κ') := by
  refine ⟨h.1, Subgroup.mul_mem _ h.2.1 hκ', ?_⟩
  rw [map_mul, h.2.2, mul_assoc, mul_assoc]

/-- Left `GL₂(ℚ)`-invariance of the lift, in terms of `ratGL`. -/
theorem adelicLift_ratGL_mul {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (γ : BinaryRationalGL) (x : BinaryAdelicGL) :
    adelicLift f (ratGL γ * x) = adelicLift f x := by
  obtain ⟨γ₀, r, κ, h⟩ := exists_isDecomp x
  rw [adelicLift_eq_of_isDecomp f h]
  exact adelicLift_eq_of_isDecomp f (isDecomp_ratGL_mul h γ)

/-- Left `GL₂(ℚ)`-invariance of the lift. -/
theorem adelicLift_leftRational {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (γ : BinaryRationalGL) (x : BinaryAdelicGL) :
    adelicLift f (GeneralLinearGroup.map rationalAdele γ * x) = adelicLift f x :=
  adelicLift_ratGL_mul f γ x

/-- Right `K'`-invariance of the lift. -/
theorem adelicLift_mul_levelGroup {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (x : BinaryAdelicGL) {κ' : BinaryFiniteGL} (hκ' : κ' ∈ levelGroup) :
    adelicLift f (x * finGL κ') = adelicLift f x := by
  obtain ⟨γ₀, r, κ, h⟩ := exists_isDecomp x
  rw [adelicLift_eq_of_isDecomp f h]
  exact adelicLift_eq_of_isDecomp f (isDecomp_mul_levelGroup h hκ')

/-- Boundedness of the lift. -/
theorem adelicLift_bounded {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    ∃ C : ℝ, ∀ x, ‖adelicLift f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := liftReal_bounded f
  refine ⟨C, fun x => ?_⟩
  obtain ⟨r, hr, hx⟩ := adelicLift_eq f x
  rw [hx]
  exact hC r hr

/-- The lift is invariant on `GL₂(ℝ)⁺` and has the classical value `liftReal`. -/
theorem adelicLift_infGL {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) : adelicLift f (infGL r) = liftReal f r := by
  refine adelicLift_eq_of_isDecomp f (γ := 1) (κ := 1) ⟨hr, Subgroup.one_mem _, ?_⟩
  simp

end TernaryPeriodPolynomials.CuspIntegral
