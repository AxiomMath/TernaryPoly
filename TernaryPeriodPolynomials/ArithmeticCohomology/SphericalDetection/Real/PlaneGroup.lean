module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerActions

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def linearEquivMultiplicativeHom {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] :
    (V ≃ₗ[R] V) →* MulAut (Multiplicative V) where
  toFun equivalence := AddEquiv.toMultiplicative equivalence.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

abbrev RealPlaneRadical := Multiplicative (Fin 2 → ℝ)

def realPlaneRadicalAction : BinaryRealGL →* MulAut RealPlaneRadical :=
  linearEquivMultiplicativeHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Fin 2 → ℝ)).toMonoidHom.comp
      GeneralLinearGroup.toLin.toMonoidHom)

theorem realPlaneRadicalAction_apply (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    (realPlaneRadicalAction matrix radical).toAdd = matrix.val.mulVec radical.toAdd := rfl

abbrev RealPlaneGroup := RealPlaneRadical ⋊[realPlaneRadicalAction] BinaryRealGL

def realPlaneRadicalMatrix : RealPlaneRadical →* RealGL3 where
  toFun radical := planeUnipotent (radical.toAdd 0) (radical.toAdd 1)
  map_one' := planeUnipotent_zero
  map_mul' first second := GeneralEisenstein.Adelic.planeUnipotent_add
    (first.toAdd 0) (first.toAdd 1) (second.toAdd 0) (second.toAdd 1)

def planeLeviOneHom {R : Type*} [CommRing R] : GeneralLinearGroup (Fin 2) R →* GL3 R where
  toFun matrix := planeLevi matrix 1
  map_one' := (planeLeviHom R).map_one
  map_mul' first second := by
    have equality := (planeLeviHom R).map_mul (first, 1) (second, 1)
    change planeLevi (first * second) (1 * 1) = planeLevi first 1 * planeLevi second 1 at equality
    rwa [one_mul] at equality

def realPlaneMatrix : RealPlaneGroup →* RealGL3 :=
  SemidirectProduct.lift realPlaneRadicalMatrix planeLeviOneHom (by
    intro matrix
    apply MonoidHom.ext
    intro radical
    change realPlaneRadicalMatrix (realPlaneRadicalAction matrix radical) =
      planeLevi matrix 1 * realPlaneRadicalMatrix radical * (planeLevi matrix 1)⁻¹
    rw [realPlaneRadicalMatrix, MonoidHom.coe_mk, OneHom.coe_mk,
      planeLevi_planeUnipotent_commute, mul_assoc, mul_inv_cancel, mul_one]
    change planeUnipotent ((realPlaneRadicalAction matrix radical).toAdd 0)
      ((realPlaneRadicalAction matrix radical).toAdd 1) = _
    rw [realPlaneRadicalAction_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two])

theorem realPlaneMatrix_apply (element : RealPlaneGroup) :
    realPlaneMatrix element = realPlaneRadicalMatrix element.left * planeLevi element.right 1 := rfl

theorem realPlaneMatrix_inl (radical : RealPlaneRadical) :
    realPlaneMatrix (SemidirectProduct.inl radical) = realPlaneRadicalMatrix radical := by
  change realPlaneRadicalMatrix radical * planeLeviOneHom 1 = _
  rw [map_one, mul_one]

theorem realPlaneMatrix_inr (matrix : BinaryRealGL) :
    realPlaneMatrix (SemidirectProduct.inr matrix) = planeLevi matrix 1 := by
  change realPlaneRadicalMatrix 1 * planeLevi matrix 1 = _
  rw [map_one, one_mul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
