module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RationalKernel

@[expose] public section


/-!
# (B), step 2: decompositions `g_f = π κ` and the ratio of two of them

Formalized by Claude Sonnet 5.5.

* `PlaneDet π`: `π ∈ P(ℚ)` with `det π = 1` (the determinant-one rational plane parabolic, either sign of the bottom-right entry).
* `IsDecomp N g π κ`: `g = π κ` with `π` of that kind and `κ ∈ K(N)`.
* `decomp_ratio` (`N ≥ 3`): two decompositions of the same finite adele differ by an element of `Γ_P = Γ(N) ∩ P(ℤ)`: `π'⁻¹ π = w`, `w ∈ gammaNP N`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- The determinant-one rational plane parabolic (bottom row `(0, 0, c)`). -/
structure PlaneDet (π : GL3 ℚ) : Prop where
  mem : π ∈ planeParabolic ℚ
  det : π.val.det = 1

theorem PlaneDet.mul {π σ : GL3 ℚ} (hπ : PlaneDet π) (hσ : PlaneDet σ) : PlaneDet (π * σ) :=
  ⟨(planeParabolic ℚ).mul_mem hπ.mem hσ.mem, by rw [Units.val_mul, Matrix.det_mul, hπ.det, hσ.det, one_mul]⟩

theorem PlaneDet.inv {π : GL3 ℚ} (hπ : PlaneDet π) : PlaneDet π⁻¹ := by
  refine ⟨(planeParabolic ℚ).inv_mem hπ.mem, ?_⟩
  have := congrArg Matrix.det (Units.mul_inv π)
  rw [Matrix.det_mul, hπ.det, one_mul, Matrix.det_one] at this
  simpa using this

variable (N : ℕ) [NeZero N]

/-- A decomposition `g = π κ` of a finite adele, `π ∈ P⁺¹(ℚ)`, `κ ∈ K(N)`. -/
structure IsDecomp (g : FiniteGL) (π : GL3 ℚ) (κ : GL3 IntegralAdeles) : Prop where
  ppos : PlaneDet π
  ker : κ ∈ levelKernel N 3
  eq : g = rationalFinite π * GeneralLinearGroup.map integralEmbedding κ

/-- **Two decompositions of the same finite adele differ by `Γ_P`** (for `N ≥ 3`). -/
theorem decomp_ratio (hN : 3 ≤ N) {g : FiniteGL} {π π' : GL3 ℚ} {κ κ' : GL3 IntegralAdeles}
    (h : IsDecomp N g π κ) (h' : IsDecomp N g π' κ') :
    ∃ w : SL(3, ℤ), w ∈ gammaNP N ∧ π'⁻¹ * π = Matrix.SpecialLinearGroup.mapGL ℚ w := by
  have hpp : PlaneDet (π'⁻¹ * π) := h'.ppos.inv.mul h.ppos
  have hfin : rationalFinite (π'⁻¹ * π) = GeneralLinearGroup.map integralEmbedding (κ' * κ⁻¹) := by
    have e : rationalFinite π = rationalFinite π' * (GeneralLinearGroup.map integralEmbedding κ' *
        (GeneralLinearGroup.map integralEmbedding κ)⁻¹) := by
      have := h.eq.symm.trans h'.eq
      rw [← mul_assoc]
      exact eq_mul_inv_of_mul_eq this
    rw [map_mul, map_inv, e, map_mul, map_inv]
    simp
  obtain ⟨w, hwN, hw⟩ := gammaN_of_rat_levelKernel N (π'⁻¹ * π) hpp.det (κ' * κ⁻¹)
    ((levelKernel N 3).mul_mem h'.ker ((levelKernel N 3).inv_mem h.ker)) hfin
  have h20 : ((w : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) = 0 := by
    have := hw 2 0
    rw [hpp.mem.1] at this
    exact_mod_cast this
  have h21 : ((w : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℤ) = 0 := by
    have := hw 2 1
    rw [hpp.mem.2] at this
    exact_mod_cast this
  refine ⟨w, ⟨hwN, mem_planeStab_of_gammaN hN hwN h20 h21⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  exact (hw i j).symm

end TernaryPeriodPolynomials.Argument.FormClassK
