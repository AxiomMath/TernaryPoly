module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.ConstantTerm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedConj

@[expose] public section


/-!
# The antiholomorphic series at every plane cusp

The series of type `b = true` (antiholomorphic) is the coefficientwise complex conjugate of the series of
type `b = false` (`seriesFormK_true`). Conjugation `conjCLM` is a coefficient intertwiner commuting with
`ρ` (`intertwines_conj_rhoAt`, `conj_rhoOfSL_comm`), hence by `deRhamClass_twist` the constant term of the
antiholomorphic series at the cusp `h⁻¹ P h` is the conjugated transported seed class
(`constant_term_identity_cusp_conj`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology ContinuousAlternatingMap
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPoly.SmoothLocalDeRham
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothCoveringDeRham

section Conj

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h : SL(3, ℤ))

/-- The antiholomorphic series is the coefficientwise conjugate of the holomorphic one. -/
theorem seriesFormK_true (D : CuspData) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
    {F : Type*} [FunLike F UpperHalfPlane ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne]
    [Λ.IsArithmetic] (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)
    (y : Fin 5 → ℝ) (i j : Fin 5) :
    seriesFormK true D Γ n f y i j =
      MvPolynomial.map (starRingEnd ℂ) (seriesFormK false D Γ n f y i j) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_map, coeff_seriesFormK, coeff_seriesFormK]
  unfold seriesCoeffK
  have h1 : ∀ c, termFunK true D Γ n f c i j m y =
      Complex.conjCLE (termFunK false D Γ n f c i j m y) := by
    intro c
    have a := congrFun (termFunK_eq true D Γ n f c i j m) y
    have b := congrFun (termFunK_eq false D Γ n f c i j m) y
    rw [a]
    rw [b]
    simp [cxL_apply, cx]
  simp_rw [h1]
  exact (Complex.conjCLE.map_tsum).symm

omit [NeZero N] in
/-- Coefficient conjugation intertwines `ρ|_{Γ_{h⁻¹Ph}}` with itself. -/
theorem intertwines_conj_rhoAt : Intertwines (conjCLM n) (rhoAt N h n) (rhoAt N h n) := by
  intro p v
  apply Coef.toPoly_injective
  change Coef.toPoly (gammaRho (gammaN N) n (inclAt N h p) (conjCLM n v)) =
    Coef.toPoly (conjCLM n (gammaRho (gammaN N) n (inclAt N h p) v))
  rw [toPoly_gammaRho, conjCLM_apply, conjCLM_apply, Coef.toPoly_conjCoef, Coef.toPoly_conjCoef,
    toPoly_gammaRho, map_conj_rho]

theorem conj_rhoOfSL_comm (g : SL(3, ℤ)) :
    (conjCLM n).comp (rhoOfSL n g) = (rhoOfSL n g).comp (conjCLM n) := by
  ext q
  apply Coef.toPoly_injective
  simp only [ContinuousLinearMap.comp_apply, conjCLM_apply, Coef.toPoly_conjCoef,
    toPoly_rhoOfSL, map_conj_rho]

/-- The pullback of the antiholomorphic series to the boundary model of the cusp `h⁻¹Ph` is the
coefficientwise conjugate of the pullback of the holomorphic one. -/
theorem cuspFaceForm_true_eq_conj :
    ((cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h) (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h)) :
        ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
          Form (F := Coef n) faceSet 2) =
      ZigZag.twForm (conjCLM n) 2
        ((cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h) (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h)) :
            ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
              Form (F := Coef n) faceSet 2) := by
  apply Form.ext
  intro x hx
  rw [ZigZag.twForm_apply, coefficientFormMap_apply]
  apply ext2Face
  intro i j
  apply Coef.toPoly_injective
  show _ = Coef.toPoly (conjCLM n (_ ))
  have hbT := toPoly_cuspFaceForm_basis N h (planeEisensteinAtComponents true (CuspData.ofSL h)
    (gammaN N) (leviGroup N) n f hn (leviInCusp_gammaN N h)) hx i j
  have hbF := toPoly_cuspFaceForm_basis N h (planeEisensteinAtComponents false (CuspData.ofSL h)
    (gammaN N) (leviGroup N) n f hn (leviInCusp_gammaN N h)) hx i j
  rw [conjCLM_apply, Coef.toPoly_conjCoef, hbT]
  refine Eq.trans ?_ (congrArg (MvPolynomial.map (starRingEnd ℂ)) hbF.symm)
  simp only [_root_.map_sum, map_mul, MvPolynomial.map_C, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  show seriesFormK true (CuspData.ofSL h) (gammaN N) n f (cuspPt h x) a b =
    MvPolynomial.map (starRingEnd ℂ) (seriesFormK false (CuspData.ofSL h) (gammaN N) n f
      (cuspPt h x) a b)
  exact seriesFormK_true (CuspData.ofSL h) (gammaN N) (leviGroup N) n f _ a b

/-- The antiholomorphic seed at the plane cusp `h⁻¹ P h`. -/
def cuspSeedConjAt : ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n) :=
  twInv (intertwines_rhoAt N n h) (comapAt N n h
    (cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)))

omit [NeZero N] in
/-- The antiholomorphic seed at the cusp is the conjugate of the holomorphic one. -/
theorem cuspSeedConjAt_eq :
    ((cuspSeedConjAt N n f h : ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
      Form (F := Coef n) faceSet 2) =
      ZigZag.twForm (conjCLM n) 2 ((cuspSeedAt N n f h :
        ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
          Form (F := Coef n) faceSet 2) := by
  show ZigZag.twForm (rhoOfSL n h⁻¹) 2 (ZigZag.twForm (conjCLM n) 2 _) =
    ZigZag.twForm (conjCLM n) 2 (ZigZag.twForm (rhoOfSL n h⁻¹) 2 _)
  rw [← ZigZag.twForm_mul, ← ZigZag.twForm_mul, ← conj_rhoOfSL_comm]
  rfl

/-- **The constant term of the antiholomorphic series at the plane cusp `h⁻¹ P h` along its own face
is the antiholomorphic seed class at `h`.** -/
theorem constant_term_identity_cusp_conj (hN : 3 ≤ N) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h) (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (cuspSeedConjAt N n f h) := by
  have hC := intertwines_conj_rhoAt N n h
  have e1 : cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h) (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h)) =
      twInv hC (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h) (gammaN N)
        (leviGroup N) n f hn (leviInCusp_gammaN N h))) :=
    Subtype.ext (cuspFaceForm_true_eq_conj N n f hn h)
  have e2 : cuspSeedConjAt N n f h = twInv hC (cuspSeedAt N n f h) :=
    Subtype.ext (cuspSeedConjAt_eq N n f h)
  rw [e1, e2, deRhamClass_twist convex_faceSet faceSet_nonempty hC,
    deRhamClass_twist convex_faceSet faceSet_nonempty hC,
    constant_term_identity_cusp N n f h hn hN]

end Conj

end TernaryPeriodPolynomials.Argument.EisensteinClass
