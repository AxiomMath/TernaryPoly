module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.SetupFromCusp
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.CuspDecay

@[expose] public section


/-!
# Injectivity of the seed map at level `Γ(N)`

**`seedMapInjective`**: `SeedMapInjective N n` (Eichler-Shimura injectivity of `S ⊕ \bar S → H¹_par(Γ(N), Sym^{n+1} ⊗ det⁻¹)`, face by face), for every `N ≠ 0` and every `n`, via Green's formula on a truncated fundamental domain of `SL₂(ℤ)` (Petersson/Haberland).

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

theorem cuspForm_eq_zero_of_cuspH {Λ : Subgroup (GL (Fin 2) ℝ)} {k : ℕ} (F : CuspForm Λ ((k + 3 : ℕ) : ℤ))
    (h : ∀ z : ℂ, 0 < z.im → cuspH Λ k F z = 0) : F = 0 := by
  ext τ
  have := h (τ : ℂ) τ.im_pos
  unfold cuspH at this
  rw [UpperHalfPlane.ofComplex_apply] at this
  simpa using this

theorem seedMapInjective (N : ℕ) [NeZero N] (n : ℕ) : SeedMapInjective N n := by
  intro f hf
  funext i
  have h0 := seedBoundary_zero_face N n f hf i
  obtain ⟨v, hv⟩ := hol_antihol_coboundary N n _ _ h0
  have S := setup_of_coboundary N n _ _ v hv
  have hdF := decays_cuspForm N n (f i false)
  have hdG := decays_cuspForm N n (f i true)
  have e1 := core_f S hdF hdG
  have e2 := core_g S hdF hdG
  funext b
  cases b
  · exact cuspForm_eq_zero_of_cuspH _ e1
  · exact cuspForm_eq_zero_of_cuspH _ e2

/-- **Canonicity of the line constant term, unconditionally** (`r_Q ℰ_P(ξ) = Tξ` for one linear `T` and every presentation of `ξ` by a
tuple of cusp forms): `classicalLine_of_seedInjective` with the proved injectivity of the seed map. -/
theorem classicalLine (N : ℕ) [NeZero N] (n : ℕ) (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ClassicalLineConstantTerm N n hn :=
  classicalLine_of_seedInjective N n hN hn (seedMapInjective N n)

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
