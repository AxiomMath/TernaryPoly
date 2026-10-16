module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PlusGroup
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Data
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LinePeriod

@[expose] public section


/-!
# `Λ₁⁺` as a line parabolic group, and the pivot intertwiner of the coefficient representations (LS11b)

The pivot `Π = rationalGoodLine` (the permutation `e₁ ↔ e₃`) conjugates the good-line stabilizer `Λ₁ ∋ [[m, 0], [c, 1]]` (line `⟨e₃⟩`) to the line parabolic
`Π g Π = [[1, v], [0, lam]]` of the line `⟨e₁⟩` (`lam = J m J`, `v = (c₂, c₁)`), the model of the line seed.  `linePlusData : LineData Lam1Plus` is this pivoted
data, `lmat_linePlus : lmat g = Π g Π`, and `linePlusRepIso n` is the isomorphism of `Rep ℂ Λ₁⁺` between the geometric coefficient representation
(`rhoC` of `linePlusData`, i.e. `ρ(Π g Π)`) and the restriction of the library's coefficient representation `goodLineCoefficientRep n`, given by the involution `T = ρ(Π)`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction (dlIntPivot dlIntPivot_mul dl_pivot_mul_self)
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3S4c (SL2Z)

/-- `dlIntPivot` as a monoid homomorphism. -/
def pivotHom : GeneralLinearGroup (Fin 2) ℤ →* GeneralLinearGroup (Fin 2) ℤ where
  toFun := dlIntPivot
  map_one' := by
    unfold dlIntPivot
    rw [mul_one, dl_pivot_mul_self]
  map_mul' := dlIntPivot_mul

theorem pivotHom_entry (m : GeneralLinearGroup (Fin 2) ℤ) :
    ((pivotHom m : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ∧
    ((pivotHom m : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (m : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
    ((pivotHom m : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
    ((pivotHom m : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [pivotHom, dlIntPivot, binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem det_pivotHom (m : GeneralLinearGroup (Fin 2) ℤ) (hdet : GeneralLinearGroup.det m = 1) :
    GeneralLinearGroup.det (pivotHom m) = 1 := by
  simp only [pivotHom, MonoidHom.coe_mk, OneHom.coe_mk, dlIntPivot, map_mul, hdet, mul_one]
  rw [← map_mul]
  simp [dl_pivot_mul_self]

/-- The real Levi block of the pivoted data. -/
def linePlusLam : Lam1Plus →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map (Int.castRingHom ℝ)).comp (pivotHom.comp (goodLineLeviProjection.comp Lam1Plus.subtype))

/-- The real radical row of the pivoted data: the reversed bottom row. -/
def linePlusV (g : Lam1Plus) : Fin 2 → ℝ :=
  ![((((g : Lam1) : RationalGL3).val 2 1 : ℚ) : ℝ), ((((g : Lam1) : RationalGL3).val 2 0 : ℚ) : ℝ)]

theorem linePlusLam_entry (g : Lam1Plus) :
    ((linePlusLam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = ((((g : Lam1) : RationalGL3).val 1 1 : ℚ) : ℝ) ∧
    ((linePlusLam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = ((((g : Lam1) : RationalGL3).val 1 0 : ℚ) : ℝ) ∧
    ((linePlusLam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = ((((g : Lam1) : RationalGL3).val 0 1 : ℚ) : ℝ) ∧
    ((linePlusLam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = ((((g : Lam1) : RationalGL3).val 0 0 : ℚ) : ℝ) := by
  have h := (lam1_entries (g : Lam1)).2.2.2
  have p := pivotHom_entry (goodLineLeviProjection (g : Lam1))
  have e : ∀ i j, ((linePlusLam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (((pivotHom (goodLineLeviProjection (g : Lam1)) : GeneralLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) := fun i j => by
    simp [linePlusLam, GeneralLinearGroup.map_apply]
  have hr : ∀ i j : Fin 2, ((((goodLineLeviProjection (g : Lam1) : GeneralLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) = ((((g : Lam1) : RationalGL3).val i.castSucc j.castSucc : ℚ) : ℝ) :=
    fun i j => by
      have := congrArg (fun q : ℚ => (q : ℝ)) (h i j)
      simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, p.1]; exact hr 1 1
  · rw [e, p.2.1]; exact hr 1 0
  · rw [e, p.2.2.1]; exact hr 0 1
  · rw [e, p.2.2.2]; exact hr 0 0

/-- The line parabolic data of `Λ₁⁺` (after the pivot). -/
def linePlusData : LineData Lam1Plus where
  lam := linePlusLam
  v := linePlusV
  det_one g := by
    have hdet : GeneralLinearGroup.det (goodLineLeviProjection (g : Lam1)) = 1 := g.property
    simp only [linePlusLam, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [GeneralLinearGroup.map_det, det_pivotHom _ hdet, map_one]
  v_mul g h := by
    obtain ⟨-, -, hg22, -⟩ := lam1_entries (g : Lam1)
    obtain ⟨l00, l01, l10, l11⟩ := linePlusLam_entry h
    have hval : (((g * h : Lam1Plus) : Lam1) : RationalGL3).val =
        (((g : Lam1) : RationalGL3).val) * (((h : Lam1) : RationalGL3).val) := rfl
    funext i
    fin_cases i
    · simp only [linePlusV, Matrix.vecMul, dotProduct, Fin.sum_univ_two, l00, l10, hval,
        Matrix.mul_apply, Fin.sum_univ_three, hg22, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.add_apply, Fin.zero_eta, Fin.isValue]
      push_cast
      ring
    · simp only [linePlusV, Matrix.vecMul, dotProduct, Fin.sum_univ_two, l01, l11, hval,
        Matrix.mul_apply, Fin.sum_univ_three, hg22, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.add_apply, Fin.mk_one, Fin.isValue]
      push_cast
      ring

end TernaryPeriodPolynomials.Argument.LineSeed
