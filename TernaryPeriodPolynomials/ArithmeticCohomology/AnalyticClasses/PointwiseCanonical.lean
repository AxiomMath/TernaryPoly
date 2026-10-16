module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.TwoCocycleEdgeAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneCuspidalAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBinaryLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalLeviCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperRadicalExponential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Representation

@[expose] public section


/-!
# The canonical relative cocycle of a pointwise binary cocycle

For a binary one-cocycle `N` of `GL₂(ℝ)` with values in *all* functions
`GL₂(𝔸) → Sym^{n+1}` (for the cohomological action `binaryAmbientRepresentation`), the formula
`Canon(p, q)(h) = ρ_U(x_p) μ(A_p x_q) (N(A_p)(h))` (`μ = realUpperBinaryValue`) defines an
inhomogeneous two-cocycle of the real plane group `ℝ² ⋊ GL₂(ℝ)` with values in functions
`GL₂(𝔸) → Sym^n`, for the pointwise version of `realPlaneCuspidalRep`. No regularity and no
cuspidality is used: this is pure algebra (the cocycle law of `μ` along the radical and its Levi
equivariance).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The pointwise real plane group action on functions `GL₂(𝔸) → Sym^n`. -/
def planeAmbientOperator (n : ℕ) (p : RealPlaneGroup) :
    Module.End ℂ (BinaryAdelicGL → HomogeneousPoly n) where
  toFun F h := realPlaneCuspidalTwist n p •
    realCoefficientComponent n trivialCharacter (realPlaneMatrix p) (F (h * realPlaneBinaryInput p))
  map_add' F G := by
    funext h
    simp only [Pi.add_apply, map_add, smul_add]
  map_smul' c F := by
    funext h
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_comm (realPlaneCuspidalTwist n p) c]

theorem planeAmbientOperator_apply (p : RealPlaneGroup) (F : BinaryAdelicGL → HomogeneousPoly n)
    (h : BinaryAdelicGL) :
    planeAmbientOperator n p F h = realPlaneCuspidalTwist n p •
      realCoefficientComponent n trivialCharacter (realPlaneMatrix p)
        (F (h * realPlaneBinaryInput p)) := rfl

/-- The pointwise real plane group representation. -/
def planeAmbientRepresentation (n : ℕ) :
    Representation ℂ RealPlaneGroup (BinaryAdelicGL → HomogeneousPoly n) where
  toFun := planeAmbientOperator n
  map_one' := by
    apply LinearMap.ext
    intro F
    funext h
    simp [planeAmbientOperator_apply]
  map_mul' p q := by
    apply LinearMap.ext
    intro F
    funext h
    simp only [planeAmbientOperator_apply, Module.End.mul_apply, map_mul, map_smul, smul_smul,
      mul_assoc]

theorem planeAmbientRepresentation_apply (p : RealPlaneGroup)
    (F : BinaryAdelicGL → HomogeneousPoly n) (h : BinaryAdelicGL) :
    planeAmbientRepresentation n p F h = realPlaneCuspidalTwist n p •
      realCoefficientComponent n trivialCharacter (realPlaneMatrix p)
        (F (h * realPlaneBinaryInput p)) := rfl

/-- The pointwise plane representation restricts to `realPlaneCuspidalRep`. -/
theorem realPlaneCuspidalRep_val (cusp : CuspidalRepresentation) (p : RealPlaneGroup)
    (values : cuspidalTensorValues cusp (HomogeneousPoly n)) :
    ((realPlaneCuspidalRep n cusp trivialCharacter).ρ p values).val =
      planeAmbientRepresentation n p values.val := rfl

/-- Pointwise binary one-cocycles. -/
def IsBinaryPointCocycle (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    Prop :=
  ∀ A C, N (A * C) = N A + binaryAmbientRepresentation n A (N C)

/-- **The canonical cochain** of a pointwise binary cocycle. -/
def pointCanonical (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (p q : RealPlaneGroup) : BinaryAdelicGL → HomogeneousPoly n :=
  fun h => (realUpperRadicalRep n).ρ p.left
    (realUpperBinaryValue n (realPlaneRadicalAction p.right q.left) (N p.right h))

theorem realPlaneCuspidalTwist_apply (p : RealPlaneGroup) :
    realPlaneCuspidalTwist n p =
      normPower (GeneralLinearGroup.det (atInfinity p.right)) (((n : ℂ) + 3) / 2) := rfl

theorem realPlaneBinaryInput_apply (p : RealPlaneGroup) :
    realPlaneBinaryInput p = atInfinity p.right := rfl

theorem realUpperRadicalRep_eq (z : RealPlaneRadical) :
    (realUpperRadicalRep n).ρ z =
      realCoefficientComponent n trivialCharacter (realPlaneRadicalMatrix z) :=
  rfl

theorem inr_mul_inl (A : BinaryRealGL) (y : RealPlaneRadical) :
    (SemidirectProduct.inr A * SemidirectProduct.inl y : RealPlaneGroup) =
      SemidirectProduct.inl (realPlaneRadicalAction A y) * SemidirectProduct.inr A := by
  ext <;> simp

theorem planeLevi_mul_radicalMatrix (A : BinaryRealGL) (y : RealPlaneRadical) :
    planeLevi A 1 * realPlaneRadicalMatrix y =
      realPlaneRadicalMatrix (realPlaneRadicalAction A y) * planeLevi A 1 := by
  have equality := congrArg realPlaneMatrix (inr_mul_inl A y)
  simpa only [map_mul, realPlaneMatrix_inl, realPlaneMatrix_inr] using equality

theorem planeLevi_upperBinaryValue (A : BinaryRealGL) (w : RealPlaneRadical)
    (P : Binary.HomogeneousPoly (n + 1)) :
    realCoefficientComponent n trivialCharacter (planeLevi A 1) (realUpperBinaryValue n w P) =
      realUpperBinaryValue n (realPlaneRadicalAction A w) (binaryCoefficient n A P) := by
  have equality := realUpperBinaryValue_levi n A (realPlaneRadicalAction A w) P
  have inverse : realRadicalInverseLevi A (realPlaneRadicalAction A w) = w := by
    change realPlaneRadicalAction A⁻¹ (realPlaneRadicalAction A w) = w
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  rw [inverse] at equality
  exact equality.symm

/-- The coefficient action of the plane matrix of `(x, A)` intertwines the radical action and `μ`
with the binary action. -/
theorem planeCoefficient_canonical (p : RealPlaneGroup) (y w : RealPlaneRadical)
    (P : Binary.HomogeneousPoly (n + 1)) :
    realCoefficientComponent n trivialCharacter (realPlaneMatrix p)
        ((realUpperRadicalRep n).ρ y (realUpperBinaryValue n w P)) =
      (realUpperRadicalRep n).ρ (p.left * realPlaneRadicalAction p.right y)
        (realUpperBinaryValue n (realPlaneRadicalAction p.right w)
          (binaryCoefficient n p.right P)) := by
  rw [realUpperRadicalRep_eq, realUpperRadicalRep_eq, realPlaneMatrix_apply,
    ← Module.End.mul_apply, ← map_mul, mul_assoc, planeLevi_mul_radicalMatrix, ← mul_assoc,
    map_mul, Module.End.mul_apply, planeLevi_upperBinaryValue]
  simp only [map_mul, Module.End.mul_apply]

/-- **The canonical cochain of a pointwise binary cocycle is a two-cocycle.** -/
theorem pointCanonical_cocycle
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (hN : IsBinaryPointCocycle N) (a b c : RealPlaneGroup) :
    planeAmbientRepresentation n a (pointCanonical N b c) - pointCanonical N (a * b) c +
      pointCanonical N a (b * c) - pointCanonical N a b = 0 := by
  funext h
  have law := realUpperBinaryValue_mul n (realPlaneRadicalAction a.right b.left)
    (realPlaneRadicalAction a.right (realPlaneRadicalAction b.right c.left)) (N a.right h)
  have action_mul :
      realPlaneRadicalAction a.right (b.left * realPlaneRadicalAction b.right c.left) =
      realPlaneRadicalAction a.right b.left *
        realPlaneRadicalAction a.right (realPlaneRadicalAction b.right c.left) := map_mul _ _ _
  have action_comp : realPlaneRadicalAction (a.right * b.right) c.left =
      realPlaneRadicalAction a.right (realPlaneRadicalAction b.right c.left) := by
    rw [map_mul]
    rfl
  have binary : binaryAmbientRepresentation n a.right (N b.right) h =
      realPlaneCuspidalTwist n a • binaryCoefficient n a.right
        (N b.right (h * realPlaneBinaryInput a)) := rfl
  have first : planeAmbientRepresentation n a (pointCanonical N b c) h =
      realPlaneCuspidalTwist n a •
        (realUpperRadicalRep n).ρ (a.left * realPlaneRadicalAction a.right b.left)
          (realUpperBinaryValue n
            (realPlaneRadicalAction a.right (realPlaneRadicalAction b.right c.left))
            (binaryCoefficient n a.right (N b.right (h * realPlaneBinaryInput a)))) := by
    rw [planeAmbientRepresentation_apply]
    unfold pointCanonical
    rw [planeCoefficient_canonical]
  have second : pointCanonical N (a * b) c h =
      (realUpperRadicalRep n).ρ (a.left * realPlaneRadicalAction a.right b.left)
        (realUpperBinaryValue n
          (realPlaneRadicalAction a.right (realPlaneRadicalAction b.right c.left))
          (N a.right h + realPlaneCuspidalTwist n a • binaryCoefficient n a.right
            (N b.right (h * realPlaneBinaryInput a)))) := by
    unfold pointCanonical
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, action_comp, hN, Pi.add_apply,
      binary]
  have third : pointCanonical N a (b * c) h =
      (realUpperRadicalRep n).ρ a.left
        ((realUpperRadicalRep n).ρ (realPlaneRadicalAction a.right b.left)
          (realUpperBinaryValue n
            (realPlaneRadicalAction a.right (realPlaneRadicalAction b.right c.left))
            (N a.right h)) +
          realUpperBinaryValue n (realPlaneRadicalAction a.right b.left) (N a.right h)) := by
    unfold pointCanonical
    rw [SemidirectProduct.mul_left, action_mul, law]
  have fourth : pointCanonical N a b h = (realUpperRadicalRep n).ρ a.left
      (realUpperBinaryValue n (realPlaneRadicalAction a.right b.left) (N a.right h)) := rfl
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
  rw [first, second, third, fourth]
  simp only [map_add, map_smul, map_mul, Module.End.mul_apply]
  abel

end TernaryPeriodPolynomials.AnalyticClasses
