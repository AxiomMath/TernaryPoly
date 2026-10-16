module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FhSL2Invariance
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.RationalIntegral
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof

@[expose] public section


/-!
# The adelic value `v_h` and its well-definedness (step (a)-independent part)

Formalized by Claude Haiku 5.5. Paper: `v_h(g_∞, g_f) = F_h(γ g_∞)` for `γ ∈ GL₂⁺(ℚ)` with `γ g_f ∈ GL₂(ℤ̂)`.

* `vhValue`: the value, total. It uses a chosen rational lattice reduction of `g_f`, supplied by
  `LatticeReductionExists` (`LatticeReductionProof.latticeReductionExists`, proved).
* `vhValue_eq_of_reduction`: for any reduction `r` of `g_f`, `v_h = F_h(r.γ g_∞)`.
* `vhValue_well_defined`: two reductions give the same value (independence of the choice),
  from step (b) (`reductions_differ`) and step (c) (`Fh_sl2_mul`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.RationalIntegral
open TernaryPeriodPolynomials.Argument.LatticeCounts.FhSL2Invariance
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof (latticeReductionExists)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue

/-- The value `v_h(g_∞, g_f) = F_h(γ g_∞)` for the chosen rational lattice reduction `γ` of `g_f`.
Total, since every `g_f` has a reduction (`latticeReductionExists`); independence of the choice is
`vhValue_eq_of_reduction` and `vhValue_well_defined`. -/
def vhValue (k : ℤ) (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k) (gInf : BinaryRealGL) (gf : BinaryFiniteGL) : ℂ :=
  Fh k ⇑h (binaryRationalReal (Classical.choice (latticeReductionExists gf)).γ * gInf)

/-- The real image of a rational matrix relation: `γ₂ = δ γ₁` over `ℚ` gives `γ₂ = δ γ₁`
over `ℝ` with `δ ∈ SL₂(ℤ)` mapped to `GL₂(ℝ)`. -/
theorem binaryRationalReal_rel {γ₁ γ₂ : BinaryRationalGL} (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : (γ₂.val : Matrix (Fin 2) (Fin 2) ℚ) = (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast) *
      γ₁.val) :
    binaryRationalReal γ₂ = sl2 δ * binaryRationalReal γ₁ := by
  have hsl : ((sl2 δ : GL (Fin 2) ℝ).val : Matrix (Fin 2) (Fin 2) ℝ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast) := by
    simp [sl2, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  apply Units.ext
  rw [Units.val_mul, hsl]
  show (γ₂.val : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) =
    (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast) * (γ₁.val).map (Rat.castHom ℝ)
  rw [h, Matrix.map_mul, Matrix.map_map]
  congr 1

/-- The determinant of the real image of a positive-determinant rational matrix is positive. -/
theorem det_binaryRationalReal_pos (γ : BinaryRationalGL) (hγ : 0 < (Matrix.GeneralLinearGroup.det γ).val) :
    0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal γ)).val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hmap : Matrix.det (binaryRationalReal γ : Matrix (Fin 2) (Fin 2) ℝ) =
      Rat.castHom ℝ (Matrix.det (γ.val : Matrix (Fin 2) (Fin 2) ℚ)) :=
    (RingHom.map_det (Rat.castHom ℝ) (γ.val : Matrix (Fin 2) (Fin 2) ℚ)).symm
  rw [hmap]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hγ
  exact (Rat.cast_pos).2 hγ

/-- For any rational lattice reduction `r` of `g_f`, `v_h(g_∞, g_f) = F_h(r.γ g_∞)`. -/
theorem vhValue_eq_of_reduction (k : ℤ) (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k) (gInf : BinaryRealGL)
    (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val) (gf : BinaryFiniteGL)
    (r : LatticeReduction gf) :
    vhValue k h gInf gf = Fh k ⇑h (binaryRationalReal r.γ * gInf) := by
  unfold vhValue
  obtain ⟨δ, hδ⟩ := reductions_differ gf r.γ (Classical.choice (latticeReductionExists gf)).γ
    r.integral (Classical.choice (latticeReductionExists gf)).integral r.det_pos
    (Classical.choice (latticeReductionExists gf)).det_pos
  rw [binaryRationalReal_rel δ hδ, mul_assoc]
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal r.γ * gInf)).val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos (det_binaryRationalReal_pos r.γ r.det_pos) hgInf
  exact Fh_sl2_mul (h := h) k δ _ hpos

/-- Well-definedness: two rational lattice reductions of the same `g_f` give the same `v_h`. -/
theorem vhValue_well_defined (k : ℤ) (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k) (gInf : BinaryRealGL)
    (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val) (gf : BinaryFiniteGL)
    (r s : LatticeReduction gf) :
    Fh k ⇑h (binaryRationalReal r.γ * gInf) = Fh k ⇑h (binaryRationalReal s.γ * gInf) := by
  rw [← vhValue_eq_of_reduction k h gInf hgInf gf r,
    ← vhValue_eq_of_reduction k h gInf hgInf gf s]

end TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
