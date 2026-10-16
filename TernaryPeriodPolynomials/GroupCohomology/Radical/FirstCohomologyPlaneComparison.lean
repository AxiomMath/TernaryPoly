module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlaneTodd
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLattice
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.FirstCohomology

@[expose] public section


open CategoryTheory MvPolynomial
noncomputable section
namespace TernaryPoly.RadicalFirstCohomology
open LatticeTopCohomology LatticeFirstCohomology RadicalFirstCohomologyLattice
open RadicalCoinvariantAlgebra RadicalFirstCohomologyTodd

def secondToddLinear : Poly →ₗ[ℚ] Poly :=
  S.toLinearMap.comp ((firstToddLinear (X (1 : Fin 2))).comp S.toLinearMap)

def secondToddMap (n : ℕ) : H n →ₗ[ℚ] H n where
  toFun f := ⟨secondTodd f,secondTodd_homogeneous f.property⟩
  map_add' f g := Subtype.ext (secondTodd_add f g)
  map_smul' r f := Subtype.ext (secondToddLinear.map_smul r f)

/-- The literal second-coordinate Todd map is an equivalence in each exact degree. -/
def secondToddEquiv (n : ℕ) : H n ≃ₗ[ℚ] H n := by
  letI : Module.Finite ℚ (H n) := Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℚ n)
  apply LinearEquiv.ofInjectiveEndo (secondToddMap n)
  intro f g h
  exact Subtype.ext (secondTodd_injective (congrArg Subtype.val h))

@[simp] theorem secondToddEquiv_coe (n : ℕ) (f : H n) :
    (secondToddEquiv n f : Poly)=secondTodd f := rfl

def planePairTodd (n : ℕ) : (Fin 2 → H n) ≃ₗ[ℚ] (Fin 2 → H n) :=
  LinearEquiv.piCongrRight (fun j => if j=0 then firstToddEquiv n 1 else secondToddEquiv n)

def planeFirstDerivative (n : ℕ) : H n →ₗ[ℚ] H n :=
  (firstToddEquiv n 1).toLinearMap.comp (difference n 0 2)

def planeSecondDerivative (n : ℕ) : H n →ₗ[ℚ] H n :=
  (secondToddEquiv n).toLinearMap.comp (difference n 1 2)

@[simp] theorem planeFirstDerivative_coe (n : ℕ) (v : H n) :
    (planeFirstDerivative n v : Poly)=(-X 2)*pderiv 0 (v : Poly) := by
  exact firstTodd_difference n 1 v

@[simp] theorem planeSecondDerivative_coe (n : ℕ) (v : H n) :
    (planeSecondDerivative n v : Poly)=(-X 2)*pderiv 1 (v : Poly) :=
  secondTodd_difference v

def planeDerivativePair (n : ℕ) : H n →ₗ[ℚ] (Fin 2 → H n) :=
  (planePairTodd n).toLinearMap.comp (differencePair (planeRep n))

@[simp] theorem planeDerivativePair_zero (n : ℕ) (v : H n) :
    planeDerivativePair n v 0=planeFirstDerivative n v := by
  change firstToddEquiv n 1 ((planeRep n).ρ first v-v)=_
  rw [planeRep_first]
  rfl

@[simp] theorem planeDerivativePair_one (n : ℕ) (v : H n) :
    planeDerivativePair n v 1=planeSecondDerivative n v := by
  change secondToddEquiv n ((planeRep n).ρ second v-v)=_
  rw [planeRep_second]
  rfl

def planeDerivativeCurl (n : ℕ) : (Fin 2 → H n) →ₗ[ℚ] H n :=
  (planeFirstDerivative n).comp (LinearMap.proj 1)-
    (planeSecondDerivative n).comp (LinearMap.proj 0)

@[simp] theorem planeDerivativeCurl_coe (n : ℕ) (v : Fin 2 → H n) :
    (planeDerivativeCurl n v : Poly)=
      (-X 2)*pderiv 0 (v 1 : Poly)-(-X 2)*pderiv 1 (v 0 : Poly) := by
  change (planeFirstDerivative n (v 1) : Poly)-(planeSecondDerivative n (v 0) : Poly)=_
  rw [planeFirstDerivative_coe,planeSecondDerivative_coe]

theorem planeDerivativeCurl_pair (n : ℕ) (v : H n) :
    planeDerivativeCurl n (planeDerivativePair n v)=0 := by
  apply Subtype.ext
  rw [planeDerivativeCurl_coe,planeDerivativePair_zero,planeDerivativePair_one,
    planeFirstDerivative_coe,planeSecondDerivative_coe]
  simp only [pderiv_mul,map_neg,pderiv_X_of_ne (by decide : (2 : Fin 3)≠0),
    pderiv_X_of_ne (by decide : (2 : Fin 3)≠1),neg_zero,zero_mul,zero_add]
  change (-X 2)*((-X 2)*pderiv 0 (pderiv 1 (v : Poly)))-
    (-X 2)*((-X 2)*pderiv 1 (pderiv 0 (v : Poly)))=0
  rw [MultivariateIntegral.pderiv_commute 0 1]
  exact sub_self _

abbrev planeDerivativeClosedPairs (n : ℕ) := LinearMap.ker (planeDerivativeCurl n)

def planeCommonDerivative (n : ℕ) : H n →ₗ[ℚ] planeDerivativeClosedPairs n :=
  (planeDerivativePair n).codRestrict _ (planeDerivativeCurl_pair n)

def planeDerivativeComplex (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.mk (ModuleCat.ofHom (planeDerivativePair n))
    (ModuleCat.ofHom (planeDerivativeCurl n)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact planeDerivativeCurl_pair n)

/-- The concrete kernel modulo the range of the common derivative map, using Mathlib's
bundled module structure for its literal kernel-and-quotient construction. -/
abbrev planeDerivativeQuotient (n : ℕ) : ModuleCat ℚ :=
  (planeDerivativeComplex n).moduleCatLeftHomologyData.H

theorem planeTodd_curl_poly (a b : Poly) :
    ternaryTodd (X (1 : Fin 2)) (secondTodd (shear 0 2 b-b-(shear 1 2 a-a))) =
      (-X 2)*pderiv 0 (secondTodd b)-
        (-X 2)*pderiv 1 (ternaryTodd (X (1 : Fin 2)) a) := by
  rw [secondTodd_sub,firstTodd_sub,secondTodd_sub,secondTodd_plane_shear]
  have hd := firstTodd_difference_poly 1 (secondTodd b)
  simp only [Fin.succ_one_eq_two] at hd
  rw [hd,secondTodd_difference,firstTodd_plane_root]

theorem planeTodd_curl (n : ℕ) (v : Fin 2 → H n) :
    firstToddEquiv n 1 (secondToddEquiv n (curl (planeRep n) v)) =
      planeDerivativeCurl n (planePairTodd n v) := by
  apply Subtype.ext
  rw [firstToddEquiv_coe,secondToddEquiv_coe,planeDerivativeCurl_coe]
  change ternaryTodd (X (1 : Fin 2)) (secondTodd
    ((v 0 : Poly)+(((planeRep n).ρ first (v 1) : H n) : Poly)-
      (((planeRep n).ρ second (v 0) : H n) : Poly)-(v 1 : Poly))) = _
  rw [planeRep_first,planeRep_second]
  change ternaryTodd (X (1 : Fin 2)) (secondTodd
    ((v 0 : Poly)+shear 0 2 (v 1 : Poly)-shear 1 2 (v 0 : Poly)-(v 1 : Poly))) =
    (-X 2)*pderiv 0 (secondTodd (v 1 : Poly))-
      (-X 2)*pderiv 1 (ternaryTodd (X (1 : Fin 2)) (v 0 : Poly))
  have he : (v 0 : Poly)+shear 0 2 (v 1 : Poly)-shear 1 2 (v 0 : Poly)-(v 1 : Poly)=
      shear 0 2 (v 1 : Poly)-(v 1 : Poly)-(shear 1 2 (v 0 : Poly)-(v 0 : Poly)) := by abel
  rw [he,planeTodd_curl_poly]

/-- The explicit finite Todd short-complex isomorphism for the plane radical. -/
def planeToddComplexIso (n : ℕ) : pairComplex (planeRep n) ≅ planeDerivativeComplex n :=
  ShortComplex.isoMk (Iso.refl _) (planePairTodd n).toModuleIso
    ((secondToddEquiv n).trans (firstToddEquiv n 1)).toModuleIso (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      rfl) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact (planeTodd_curl n v).symm)

/-- Genuine H¹ of the actual integral plane lattice is the concrete root-derivative pair quotient. -/
def planeH1DerivativeQuotientIso (n : ℕ) :
    groupCohomology (planeRep n) 1 ≅ planeDerivativeQuotient n :=
  groupCohomologyIso (planeRep n) 1 resolution ≪≫
    (homComplex (planeRep n)).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (coordinateIso (planeRep n)) ≪≫
    ShortComplex.homologyMapIso (planeToddComplexIso n) ≪≫
    (planeDerivativeComplex n).moduleCatHomologyIso

end TernaryPoly.RadicalFirstCohomology
