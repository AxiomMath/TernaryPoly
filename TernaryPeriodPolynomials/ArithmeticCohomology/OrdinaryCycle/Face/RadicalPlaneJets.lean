module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneDifferences

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RelativeEdgeCohomologyPolynomials

/-- Erasure commutes with differentiation in every retained coordinate. -/
theorem erase_pderiv_of_ne (i j : Fin 3) (hij : i≠j) (p : Poly) :
    erase i (pderiv j p)=pderiv j (erase i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [erase]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p k hp =>
    by_cases hki : k=i
    · subst k
      simp [erase,map_mul,hij]
    · by_cases hkj : k=j
      · subst k
        simp [erase,map_add,map_mul,hij.symm] at hp ⊢
        exact hp
      · simp [erase,map_mul,hki,hkj] at hp ⊢
        exact hp

/-- The first normal jet of a plane root substitution is its literal linear translation jet. -/
theorem plane_shearStep_normal_jet (i : Fin 2) (t : ℚ) (p : Poly) :
    erase 2 (pderiv 2 (shearStep i.castSucc 2 t p)) =
      erase 2 (pderiv 2 p)-C t*erase 2 (pderiv i.castSucc p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [shearStep]
  | add p q hp hq => simp only [map_add,hp,hq]; ring
  | mul_X p j hp =>
    have hi : i.castSucc≠(2 : Fin 3) := by fin_cases i <;> decide
    simp only [map_mul,pderiv_mul,map_add]
    simp only [erase_shearStep _ _ hi t]
    rw [hp]
    fin_cases i <;> fin_cases j <;>
      simp [shearStep,erase] <;> ring

/-- Closed actual plane differences induce a closed binary differential form. -/
theorem plane_pair_erased_closed (t : ℚ) (ht : t≠0) (a b : Poly)
    (hclosed : shearStep 0 2 t b-b=shearStep 1 2 t a-a) :
    pderiv 0 (erase 2 b)=pderiv 1 (erase 2 a) := by
  have h := congrArg (fun p => erase 2 (pderiv 2 p)) hclosed
  simp only [map_sub] at h
  have h0 := plane_shearStep_normal_jet 0 t b
  have h1 := plane_shearStep_normal_jet 1 t a
  change erase 2 (pderiv 2 (shearStep 0 2 t b))=erase 2 (pderiv 2 b)-C t*erase 2 (pderiv 0 b) at h0
  change erase 2 (pderiv 2 (shearStep 1 2 t a))=erase 2 (pderiv 2 a)-C t*erase 2 (pderiv 1 a) at h1
  rw [h0,h1] at h
  have he : C t*erase 2 (pderiv 0 b)=C t*erase 2 (pderiv 1 a) := by
    linear_combination -h
  have he' := (mul_left_cancel₀ (C_ne_zero.mpr ht)) he
  rwa [erase_pderiv_of_ne 2 0 (by decide),erase_pderiv_of_ne 2 1 (by decide)] at he'

end TernaryPoly.OrdinaryFaceRadical
