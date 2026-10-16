module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Reduction

@[expose] public section


/-!
# Lemma B.1: the fibre of `G(w,C) ↦ C` is the radical torus `ℝ²/ℤ²`

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3: "the fibre over `C` is parametrized by `w ∈ ℝ²`; the radical `ℤ²` acts by
translations of `w` with covolume one, and the Jacobian of `w ↦ Cw` is `det C > 0`".

* `Gmat_translate`: the integral radical element `p = (1 0; u 1)` acts on the fibre by the
  translation `w ↦ w + u`: `pᵗ G(w,C) p = G(w + u, C)`.
* `Gmat_col`: the off-diagonal column of `G(w,C)` is `C w`; its Jacobian (in the variable `w`) is
  `det C`, and for `C = C(t)`, `|t| ≤ 1/2`, this is `1 - t² > 0` (`jacobian_Ct_pos`).
* `torus_volume`: a fundamental domain of `ℤ² ⊂ ℝ²` has volume one (the torus `ℝ²/ℤ²`),
  `isAddFundamentalDomain_torus`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry

open Matrix MeasureTheory

/-- The integral radical translates the fibre coordinate `w`. -/
theorem Gmat_translate {C : Mat2} (hC : Cᵀ = C) (u : Fin 2 → ℤ) (w : Vec2) :
    (parab 1 u 1)ᵀ * Gmat w C * parab 1 u 1 = Gmat (w + intVec u) C := by
  have h := Gmat_equivariant hC 1 1 (by simp) (by simp) u 1 (Or.inl rfl) w (w + intVec u) (by
    simp [castMat, add_comm])
  rw [h]
  simp [castMat]

/-- The off-diagonal column of `G(w,C)` is `C w`, a linear function of `w` with determinant
`det C`. -/
theorem Gmat_col (w : Vec2) (C : Mat2) (i : Fin 2) : Gmat w C i.succ 0 = (C *ᵥ w) i := by
  fin_cases i <;> rfl

theorem Ct_det (t : ℝ) : (Ct t).det = 1 - t ^ 2 := by
  simp [Ct, Matrix.det_fin_two]
  ring

theorem jacobian_Ct_pos {t : ℝ} (ht : |t| ≤ 1 / 2) :
    0 < LinearMap.det (Matrix.toLin' (Ct t)) := by
  rw [LinearMap.det_toLin', Ct_det]
  have := abs_le.mp ht
  nlinarith

/-- The torus `ℝ²/ℤ²` of the radical: its standard fundamental domain has volume one. -/
theorem torus_volume :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2))) = 1 := by
  rw [ZSpan.volume_fundamentalDomain]
  have h : Matrix.of ⇑(Pi.basisFun ℝ (Fin 2)) = 1 := by
    ext i j
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  simp [h]

theorem isAddFundamentalDomain_torus :
    IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))))
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2))) volume :=
  ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin 2)) volume

end TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry
