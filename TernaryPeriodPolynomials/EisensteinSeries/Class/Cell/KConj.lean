module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KClass

@[expose] public section


/-!
# The antiholomorphic series at any cusp, restricted to the face of any cusp

The antiholomorphic series is the coefficientwise conjugate of the holomorphic one
(`seriesFormK_true`), so for every pair of cusps `h, h'` the class of its pullback to the face of `h` is
`conj` applied to the class of the holomorphic one (`deRhamClass_twist`, `T = conjCLM`), and the values
of `CellKClass` are conjugated: zero, the conjugate seed of `f|A`, or the seed of `(f|A)^*`.

Formalized by Claude Sonnet 5.5.
-/

open ContinuousAlternatingMap TernaryPoly.SmoothCoveringDeRham
open scoped MatrixGroups ContDiff
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section Conj

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h h' : SL(3, ℤ))

theorem conjCLM_conjCLM (q : Coef n) : conjCLM n (conjCLM n q) = q := by
  apply Coef.toPoly_injective
  rw [conjCLM_apply, conjCLM_apply, Coef.toPoly_conjCoef, Coef.toPoly_conjCoef,
    MvPolynomial.map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z; simp
  rw [this, MvPolynomial.map_id]

omit [NeZero N] in
/-- Conjugation twice is the identity on invariant closed forms. -/
theorem twInv_conj_conj (hC : Intertwines (conjCLM n) (rhoAt N h n) (rhoAt N h n))
    (X : ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
    twInv hC (twInv hC X) = X := by
  apply Subtype.ext
  rw [twInv_coe, twInv_coe]
  show ZigZag.twForm (conjCLM n) 2 (ZigZag.twForm (conjCLM n) 2 X.1) = X.1
  apply Form.ext
  intro x hx
  rw [ZigZag.twForm_apply, ZigZag.twForm_apply, coefficientFormMap_apply, coefficientFormMap_apply]
  apply ContinuousAlternatingMap.ext
  intro v
  exact conjCLM_conjCLM n _

/-- The antiholomorphic series pulled back to the face of any cusp is the coefficientwise conjugate of
the holomorphic one. -/
theorem cuspFaceForm_true_eq_conj_gen :
    ((cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h') (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h')) :
        ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
          Form (F := Coef n) faceSet 2) =
      ZigZag.twForm (conjCLM n) 2
        ((cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h')) :
            ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n)) :
              Form (F := Coef n) faceSet 2) := by
  apply Form.ext
  intro x hx
  rw [ZigZag.twForm_apply, coefficientFormMap_apply]
  apply ext2Face
  intro i j
  apply Coef.toPoly_injective
  show _ = Coef.toPoly (conjCLM n (_))
  have hbT := toPoly_cuspFaceForm_basis N h (planeEisensteinAtComponents true (CuspData.ofSL h')
    (gammaN N) (leviGroup N) n f hn (leviInCusp_gammaN N h')) hx i j
  have hbF := toPoly_cuspFaceForm_basis N h (planeEisensteinAtComponents false (CuspData.ofSL h')
    (gammaN N) (leviGroup N) n f hn (leviInCusp_gammaN N h')) hx i j
  rw [conjCLM_apply, Coef.toPoly_conjCoef, hbT]
  refine Eq.trans ?_ (congrArg (MvPolynomial.map (starRingEnd ℂ)) hbF.symm)
  simp only [_root_.map_sum, map_mul, MvPolynomial.map_C, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  show seriesFormK true (CuspData.ofSL h') (gammaN N) n f (cuspPt h x) a b =
    MvPolynomial.map (starRingEnd ℂ) (seriesFormK false (CuspData.ofSL h') (gammaN N) n f
      (cuspPt h x) a b)
  exact seriesFormK_true (CuspData.ofSL h') (gammaN N) (leviGroup N) n f _ a b

theorem faceClass_true_eq (hC : Intertwines (conjCLM n) (rhoAt N h n) (rhoAt N h n)) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) =
      (groupCohomology.map (MonoidHom.id _) (twMor hC) 2).hom
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
          (rhoAt N h n)
          (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
            (leviGroup N) n f hn (leviInCusp_gammaN N h')))) := by
  have e : cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h') (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h')) =
      twInv hC (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
        (leviGroup N) n f hn (leviInCusp_gammaN N h'))) :=
    Subtype.ext (cuspFaceForm_true_eq_conj_gen N n f hn h h')
  rw [e]
  exact deRhamClass_twist convex_faceSet faceSet_nonempty hC _

end Conj

section TrueValues

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h h' : SL(3, ℤ))

/-- **Antiholomorphic series, value: different orbits.** -/
theorem faceClass_true_none (hN : 3 ≤ N)
    (hnone : ∀ c : Ck N (h' * h⁻¹), ¬ IsCellK N (h' * h⁻¹) c) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) = 0 := by
  rw [faceClass_true_eq N n f hn h h' (intertwines_conj_rhoAt N n h),
    faceClass_none N n f hn h h' hN hnone, _root_.map_zero]

/-- **Antiholomorphic series, value for a cell of bottom entry `1`**: the transported conjugate seed
of `f|A`. -/
theorem faceClass_true_pos (hN : 3 ≤ N) {c₀ : Ck N (h' * h⁻¹)} (hc : IsCellK N (h' * h⁻¹) c₀)
    (h22 : ((cellMat N (h' * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (cuspSeedConjAt N n (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀)
          (cellMat_mem_planeStab N (h' * h⁻¹) hc h22)) f) h) := by
  have hC := intertwines_conj_rhoAt N n h
  rw [faceClass_true_eq N n f hn h h' hC, faceClass_pos N n f hn h h' hN hc h22,
    ← deRhamClass_twist convex_faceSet faceSet_nonempty hC]
  exact congrArg _ (Subtype.ext (cuspSeedConjAt_eq N n _ h)).symm

/-- **Antiholomorphic series, value for a cell of bottom entry `-1`**: the transported seed of
`(f|A)^*` (conjugation twice). -/
theorem faceClass_true_neg (hN : 3 ≤ N) {c₀ : Ck N (h' * h⁻¹)} (hc : IsCellK N (h' * h⁻¹) c₀)
    (h22 : ((cellMat N (h' * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents true (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (cuspSeedAt N n
          (fStarGen (leviGroup N) (leviGroup_J_stable N)
            (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀ * rPrime)
              (cellMat_mul_rPrime_mem N (h' * h⁻¹) hc h22)) f)) h) := by
  have hC := intertwines_conj_rhoAt N n h
  rw [faceClass_true_eq N n f hn h h' hC, faceClass_neg N n f hn h h' hN hc h22,
    ← deRhamClass_twist convex_faceSet faceSet_nonempty hC]
  refine congrArg _ ?_
  have e : cuspSeedConjAt N n (fStarGen (leviGroup N) (leviGroup_J_stable N)
            (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀ * rPrime)
              (cellMat_mul_rPrime_mem N (h' * h⁻¹) hc h22)) f)) h =
      twInv hC (cuspSeedAt N n (fStarGen (leviGroup N) (leviGroup_J_stable N)
            (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀ * rPrime)
              (cellMat_mul_rPrime_mem N (h' * h⁻¹) hc h22)) f)) h) :=
    Subtype.ext (cuspSeedConjAt_eq N n _ h)
  rw [e]
  exact twInv_conj_conj N n h hC _

end TrueValues

end TernaryPeriodPolynomials.Argument.EisensteinClass
