module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLineTodd
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLattice
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.FirstCohomology

@[expose] public section


open CategoryTheory MvPolynomial
noncomputable section
namespace TernaryPoly.RadicalFirstCohomology
open LatticeTopCohomology LatticeFirstCohomology RadicalFirstCohomologyLattice
open RadicalCoinvariantAlgebra RadicalFirstCohomologyTodd

/-- The explicit finite Todd equivalence on the two generator coordinates. -/
def linePairTodd (n : ℕ) : (Fin 2 → H n) ≃ₗ[ℚ] (Fin 2 → H n) :=
  LinearEquiv.piCongrRight (firstToddEquiv n)

/-- The actual degree-preserving negative line-root derivative. -/
def lineRootDerivative (n : ℕ) (j : Fin 2) : H n →ₗ[ℚ] H n :=
  (firstToddEquiv n j).toLinearMap.comp (difference n 0 j.succ)

@[simp] theorem lineRootDerivative_coe (n : ℕ) (j : Fin 2) (v : H n) :
    (lineRootDerivative n j v : Poly)= -(X j.succ)*pderiv 0 (v : Poly) :=
  firstTodd_difference n j v

/-- The line Koszul derivative differential in degree zero. -/
def lineDerivativePair (n : ℕ) : H n →ₗ[ℚ] (Fin 2 → H n) :=
  (linePairTodd n).toLinearMap.comp (differencePair (lineRep n))

@[simp] theorem lineDerivativePair_apply (n : ℕ) (v : H n) (j : Fin 2) :
    lineDerivativePair n v j=lineRootDerivative n j v := by
  fin_cases j
  · change firstToddEquiv n 0 ((lineRep n).ρ first v-v)=_
    rw [lineRep_first]
    rfl
  · change firstToddEquiv n 1 ((lineRep n).ρ second v-v)=_
    rw [lineRep_second]
    rfl

/-- The line Koszul derivative curl. -/
def lineDerivativeCurl (n : ℕ) : (Fin 2 → H n) →ₗ[ℚ] H n :=
  (lineRootDerivative n 0).comp (LinearMap.proj 1)-
    (lineRootDerivative n 1).comp (LinearMap.proj 0)

@[simp] theorem lineDerivativeCurl_coe (n : ℕ) (v : Fin 2 → H n) :
    (lineDerivativeCurl n v : Poly)=
      (-X 1)*pderiv 0 (v 1 : Poly)-(-X 2)*pderiv 0 (v 0 : Poly) := by
  change (lineRootDerivative n 0 (v 1) : Poly)-(lineRootDerivative n 1 (v 0) : Poly)=_
  rw [lineRootDerivative_coe,lineRootDerivative_coe]
  simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]

/-- The displayed derivative pair is actually closed. -/
theorem lineDerivativeCurl_pair (n : ℕ) (v : H n) :
    lineDerivativeCurl n (lineDerivativePair n v)=0 := by
  apply Subtype.ext
  rw [lineDerivativeCurl_coe,lineDerivativePair_apply,lineDerivativePair_apply,
    lineRootDerivative_coe,lineRootDerivative_coe]
  simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  simp only [pderiv_mul,map_neg,pderiv_X_of_ne (by decide : (2 : Fin 3)≠0),
    pderiv_X_of_ne (by decide : (1 : Fin 3)≠0),neg_zero,zero_mul,zero_add]
  change (-X 1)*((-X 2)*pderiv 0 (pderiv 0 (v : Poly)))-
    (-X 2)*((-X 1)*pderiv 0 (pderiv 0 (v : Poly)))=0
  ring

/-- The concrete closed derivative pairs. -/
abbrev lineDerivativeClosedPairs (n : ℕ) := LinearMap.ker (lineDerivativeCurl n)

def lineCommonDerivative (n : ℕ) : H n →ₗ[ℚ] lineDerivativeClosedPairs n :=
  (lineDerivativePair n).codRestrict _ (lineDerivativeCurl_pair n)

def lineDerivativeComplex (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.mk (ModuleCat.ofHom (lineDerivativePair n))
    (ModuleCat.ofHom (lineDerivativeCurl n)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact lineDerivativeCurl_pair n)

/-- The concrete kernel modulo the range of the common derivative map, using Mathlib's
bundled module structure for its literal kernel-and-quotient construction. -/
abbrev lineDerivativeQuotient (n : ℕ) : ModuleCat ℚ :=
  (lineDerivativeComplex n).moduleCatLeftHomologyData.H

/-- The finite Todd coordinate changes intertwine the full differentials, before taking kernels. -/
theorem lineTodd_curl_poly (a b : Poly) :
    ternaryTodd (X (0 : Fin 2)) (ternaryTodd (X (1 : Fin 2))
      (shear 0 1 b-b-(shear 0 2 a-a))) =
      (-X 1)*pderiv 0 (ternaryTodd (X (1 : Fin 2)) b)-
        (-X 2)*pderiv 0 (ternaryTodd (X (0 : Fin 2)) a) := by
  rw [firstTodd_sub,firstTodd_sub]
  have hs := firstTodd_shear 1 0 b
  have hd₀ := firstTodd_difference_poly 0 (ternaryTodd (X (1 : Fin 2)) b)
  have hd₁ := firstTodd_difference_poly 1 a
  have hx := firstTodd_X_mul 0 1 (pderiv 0 a)
  simp only [Fin.succ_zero_eq_one] at hs hd₀
  simp only [Fin.succ_one_eq_two] at hd₁ hx
  rw [firstTodd_sub 1 (shear 0 1 b) b,hs,hd₀,hd₁]
  simp only [neg_mul]
  rw [firstTodd_neg 0 (X 2*pderiv 0 a),hx,firstTodd_pderiv 0 a]

theorem lineTodd_curl (n : ℕ) (v : Fin 2 → H n) :
    firstToddEquiv n 0 (firstToddEquiv n 1 (curl (lineRep n) v)) =
      lineDerivativeCurl n (linePairTodd n v) := by
  apply Subtype.ext
  rw [firstToddEquiv_coe,firstToddEquiv_coe,lineDerivativeCurl_coe]
  change ternaryTodd (X (0 : Fin 2)) (ternaryTodd (X (1 : Fin 2))
    ((v 0 : Poly)+(((lineRep n).ρ first (v 1) : H n) : Poly)-
      (((lineRep n).ρ second (v 0) : H n) : Poly)-(v 1 : Poly))) = _
  rw [lineRep_first,lineRep_second]
  change ternaryTodd (X (0 : Fin 2)) (ternaryTodd (X (1 : Fin 2))
    ((v 0 : Poly)+shear 0 1 (v 1 : Poly)-shear 0 2 (v 0 : Poly)-(v 1 : Poly))) =
    (-X 1)*pderiv 0 (ternaryTodd (X (1 : Fin 2)) (v 1 : Poly))-
      (-X 2)*pderiv 0 (ternaryTodd (X (0 : Fin 2)) (v 0 : Poly))
  have he : (v 0 : Poly)+shear 0 1 (v 1 : Poly)-shear 0 2 (v 0 : Poly)-(v 1 : Poly)=
      shear 0 1 (v 1 : Poly)-(v 1 : Poly)-(shear 0 2 (v 0 : Poly)-(v 0 : Poly)) := by abel
  rw [he,lineTodd_curl_poly]

/-- An explicit finite Todd isomorphism from actual lattice differences to actual root derivatives. -/
def lineToddComplexIso (n : ℕ) : pairComplex (lineRep n) ≅ lineDerivativeComplex n :=
  ShortComplex.isoMk (Iso.refl _) (linePairTodd n).toModuleIso
    ((firstToddEquiv n 1).trans (firstToddEquiv n 0)).toModuleIso (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      rfl) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact (lineTodd_curl n v).symm)

/-- Genuine H¹ of the actual integral line lattice is the concrete closed root-derivative pair quotient. -/
def lineH1DerivativeQuotientIso (n : ℕ) :
    groupCohomology (lineRep n) 1 ≅ lineDerivativeQuotient n :=
  groupCohomologyIso (lineRep n) 1 resolution ≪≫
    (homComplex (lineRep n)).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (coordinateIso (lineRep n)) ≪≫
    ShortComplex.homologyMapIso (lineToddComplexIso n) ≪≫
    (lineDerivativeComplex n).moduleCatHomologyIso

end TernaryPoly.RadicalFirstCohomology
