module

public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.FiniteSpanBound
public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.RealShift
public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.CompactBound

@[expose] public section


/-!
# The uniform cusp bound for `K`-finite plane sections

If the right translates of a plane-induced section by a compact set `T ⊆ GL₃(ℝ)` lie in a
finite-dimensional space of plane-induced sections, then its Levi orbit functions are bounded
**uniformly** over `T`. This is the uniform cusp bound of the analytic arguments, for `K`-finite
sources, and it does not use any continuity of `realize`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein
open GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ} {D : InducingData n} {s : ℂ}

/-- The plane Levi orbit function of a section at a base point. -/
def planeOrbit (s : ℂ) (g₀ : AdelicGL) : (AdelicGL → ℂ) →ₗ[ℂ] (BinaryAdelicGL → ℂ) where
  toFun w A := normPower (GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 +
    inductionExponent .plane s)) * w (planeLevi A 1 * g₀)
  map_add' w w' := by funext A; simp [mul_add]
  map_smul' c w := by funext A; simp; ring

theorem cuspFunction_bounded (σ : CuspidalRepresentation) {φ : BinaryAdelicGL → ℂ}
    (hφ : φ ∈ cuspFunctions σ) : ∃ C : ℝ, ∀ A, ‖φ A‖ ≤ C := by
  obtain ⟨v, rfl⟩ := hφ
  exact σ.bounded v

/-- **Uniform Levi bound for `K`-finite plane sections.** -/
theorem kfinite_uniform_levi_bound {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (V : Submodule ℂ (AdelicGL → ℂ)) [FiniteDimensional ℂ V]
    (hVind : ∀ w ∈ V, IsInduced D .plane s w) {T : Set RealGL3} (hT : IsCompact T)
    (hV : ∀ k ∈ T, (fun z => f (z * atInfinity k)) ∈ V) (g₀ : AdelicGL) :
    ∃ C : ℝ, ∀ k ∈ T, ∀ A : BinaryAdelicGL,
      ‖normPower (GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2 + inductionExponent .plane s)) *
        f (planeLevi A 1 * g₀ * atInfinity k)‖ ≤ C := by
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let W : Submodule ℂ (BinaryAdelicGL → ℂ) := V.map (planeOrbit (n := n) s g₀)
  have hWmem : ∀ k : T, (planeOrbit (n := n) s g₀ (fun z => f (z * atInfinity k.val))) ∈ W :=
    fun k => Submodule.mem_map_of_mem (hV k.val k.property)
  have hWbdd : ∀ φ ∈ W, ∃ C : ℝ, ∀ A, ‖φ A‖ ≤ C := by
    rintro φ ⟨w, hw, rfl⟩
    exact cuspFunction_bounded D.cusp ((hVind w hw).2.2.2.2.2 g₀)
  have hcont : ∀ A, Continuous fun k : T =>
      planeOrbit (n := n) s g₀ (fun z => f (z * atInfinity k.val)) A := by
    intro A
    have hc := EisensteinRegularization.Helpers.induced_continuous hf
    exact continuous_const.mul (hc.comp (continuous_const.mul
      ((PlaneEisensteinContinuation.StageTranslation.atInfinity_continuous).comp
        continuous_subtype_val)))
  obtain ⟨C, hC⟩ := uniform_bound_of_finiteDimensional_span
    (fun k : T => planeOrbit (n := n) s g₀ (fun z => f (z * atInfinity k.val))) W hWmem hWbdd hcont
  exact ⟨C, fun k hk A => hC ⟨k, hk⟩ A⟩

end TernaryPeriodPolynomials.ArchimedeanConstant
