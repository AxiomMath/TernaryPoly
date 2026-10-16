module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.EdgeFinal
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FStar
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Reflection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LinePeriod
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityBoundary

@[expose] public section


/-!
# The edge of the reflection-invariant line seed is the classical period class (LS15a)

For a level-one cusp form `f` of weight `n + 3` (`n` odd) and the pivoted Levi block `pvSL m` of the Levi section of `m ∈ SL₂(ℤ)`, the cocycle `epsB f m` of the line seed
is the library's holomorphic period cocycle `c_f = classicalBinaryCocycle f (n+1) · 0` at `pvSL m` (`epsB_eq`), and the cocycle of the antiholomorphic seed of `f^*` is
`-R c_f` at `pvSL m` (`conjB_epsB_fStar`, `R` the parity reflection).  Hence the cocycle of the edge of `σ_f + (-1)ⁿ \overline{σ_{f^*}}` is `-6` times the `SL₂(ℤ)`-restriction
of the library's transported cocycle `dlCocycleOf n ψ_f` of the arithmetic parity-0 period cocycle (`edgeComb_eq`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein MvPolynomial Matrix CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses (binarySwap)
open TernaryPeriodPolynomials.SourceConstruction (dlIntPivot dlCocycleOf lineCocyclePhi)
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 conjB fStar momentPrim_fStar_hasDerivAt classicalBinaryCocycle_eq_eichlerCocycle modularCocycleReflection_classical)
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension (restriction restriction_intertwines)

/-- The `SL₂(ℤ)` element underlying the pivoted Levi block of the Levi section of `m`. -/
def pvSL (m : SpecialLinearGroup (Fin 2) ℤ) : SpecialLinearGroup (Fin 2) ℤ := linePlusSL (linePlusSectionS m)

theorem toGL_pvSL (m : SpecialLinearGroup (Fin 2) ℤ) :
    SpecialLinearGroup.toGL (pvSL m) = dlIntPivot (SpecialLinearGroup.toGL m) := by
  have h : goodLineLeviProjection ((linePlusSectionS m : Lam1Plus) : Lam1) = SpecialLinearGroup.toGL m :=
    goodLineLeviProjection_section _
  apply Units.ext
  change ((linePlusSL (linePlusSectionS m) : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    (((pivotHom (SpecialLinearGroup.toGL m)) : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [← h]
  rfl

theorem lam_section_eq (m : SpecialLinearGroup (Fin 2) ℤ) :
    linePlusData.lam (linePlusSectionS m) = SpecialLinearGroup.mapGL ℝ (pvSL m) :=
  linePlusLam_eq_mapGL _

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
  (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2)

/-- The library's holomorphic period cocycle of `f` (twist `0`), a binary form of degree `n + 1`. -/
def cB (m : SpecialLinearGroup (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) :=
  classicalBinaryCocycle f (n + 1) hw 0 m

/-- Its parity reflection. -/
def rB (m : SpecialLinearGroup (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) :=
  modularCocycleReflection (n + 1) 0 (classicalBinaryCocycle f (n + 1) hw 0) m

include hw in
theorem epsB_eq (m : SpecialLinearGroup (Fin 2) ℤ) :
    epsB f m = ((-1 : ℂ) ^ (n + 1)) • cB f hw (pvSL m) := by
  apply Subtype.ext
  have h := classicalBinaryCocycle_eq_eichlerCocycle f n hw 0 (momentPrim Lvl1 n f)
    (momentPrim_zero Lvl1 n f) (momentPrim_hasDerivAt Lvl1 n f) (pvSL m)
  rw [Submodule.coe_smul, smul_eq_C_mul]
  change eichlerCocycle n (momentPrim Lvl1 n f) (linePlusData.lam (linePlusSectionS m)) = _
  rw [lam_section_eq]
  have h' : (cB f hw (pvSL m)).val = C ((-1 : ℂ) ^ (n + 1)) *
      eichlerCocycle n (momentPrim Lvl1 n f) (SpecialLinearGroup.mapGL ℝ (pvSL m)) := h
  rw [h', ← mul_assoc, ← map_mul, ← mul_pow]
  norm_num

include hw in
theorem conjB_epsB_fStar (m : SpecialLinearGroup (Fin 2) ℤ) :
    conjB (epsB (fStar f) m) = -(((-1 : ℂ) ^ (n + 1)) • rB f hw (pvSL m)) := by
  apply Subtype.ext
  have h := modularCocycleReflection_classical f n hw 0 (momentPrim Lvl1 n f) (momentPrim Lvl1 n (fStar f))
    (momentPrim_zero Lvl1 n f) (momentPrim_zero Lvl1 n (fStar f)) (momentPrim_hasDerivAt Lvl1 n f)
    (fun j z hz => momentPrim_fStar_hasDerivAt f j z hz) (pvSL m)
  have h' : (rB f hw (pvSL m)).val = -(C ((-1 : ℂ) ^ (n + 1)) * MvPolynomial.map (starRingEnd ℂ)
      (eichlerCocycle n (momentPrim Lvl1 n (fStar f)) (SpecialLinearGroup.mapGL ℝ (pvSL m)))) := h
  have hs : ((-1 : ℂ) ^ (n + 1)) * ((-1 : ℂ) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; norm_num
  have hC : (C ((-1 : ℂ) ^ (n + 1)) : MvPolynomial (Fin 2) ℂ) * C ((-1 : ℂ) ^ (n + 1)) = 1 := by
    rw [← map_mul, hs, map_one]
  rw [Submodule.coe_neg, Submodule.coe_smul, smul_eq_C_mul, h']
  change MvPolynomial.map (starRingEnd ℂ)
      (eichlerCocycle n (momentPrim Lvl1 n (fStar f)) (linePlusData.lam (linePlusSectionS m))) = _
  rw [lam_section_eq]
  calc _ = (C ((-1 : ℂ) ^ (n + 1)) * C ((-1 : ℂ) ^ (n + 1))) * MvPolynomial.map (starRingEnd ℂ)
        (eichlerCocycle n (momentPrim Lvl1 n (fStar f)) (SpecialLinearGroup.mapGL ℝ (pvSL m))) := by rw [hC, one_mul]
    _ = _ := by ring

end

end TernaryPeriodPolynomials.Argument.LineSeed
