module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.SourceControl
public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.PrimitiveControl
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.PlaneCanonicalPrimitive

@[expose] public section


/-!
# Control of the canonical binary relative cocycle

Two-cochains and one-cochains on the real plane group are *controlled* if their values along
continuous paths are controlled families. Codexiom's canonical binary relative cocycle of a
relative cocycle is assembled from finitely many values of the relative cocycle: the binary
coordinate of the mixed cocycle at a Levi element only involves the two lattice values of the
mixed cocycle (`realUpperCuspidalBinaryCoordinate_value`), the mixed cocycle is a difference of
two values of the relative cocycle, and the canonical cocycle applies a radical-polynomial linear
map and the radical action to the binary coordinate. Hence it is controlled whenever the relative
cocycle is; no derivative enters.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

variable {degree : ℕ} {cusp : CuspidalRepresentation}

/-- Two-cochains of the real plane group with controlled values along continuous paths. -/
def PairControlled (cusp : CuspidalRepresentation)
    (cochain : RealPlaneGroup × RealPlaneGroup → cuspidalTensorValues cusp (HomogeneousPoly
        degree)) :
    Prop :=
  ∀ (X : Type) [TopologicalSpace X] (p q : X → RealPlaneGroup), PlaneContinuous p →
    PlaneContinuous q → Controlled cusp (fun x => cochain (p x, q x))

/-- One-cochains of the real plane group with controlled values along continuous paths. -/
def OneControlled (cusp : CuspidalRepresentation)
    (cochain : RealPlaneGroup → cuspidalTensorValues cusp (HomogeneousPoly degree)) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (p : X → RealPlaneGroup), PlaneContinuous p →
    Controlled cusp (fun x => cochain (p x))

/-- Cochains on `GL₂(ℝ)` with controlled values along continuous paths. -/
def LeviControlled (cusp : CuspidalRepresentation)
    (cochain : BinaryRealGL → cuspidalTensorValues cusp (HomogeneousPoly degree)) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (B : X → BinaryRealGL), Continuous B →
    Controlled cusp (fun x => cochain (B x))

theorem PairControlled.add {first second : RealPlaneGroup × RealPlaneGroup →
      cuspidalTensorValues cusp (HomogeneousPoly degree)}
    (hfirst : PairControlled cusp first) (hsecond : PairControlled cusp second) :
    PairControlled cusp (fun pair => first pair + second pair) :=
  fun X _ p q hp hq => (hfirst X p q hp hq).add (hsecond X p q hp hq)

theorem PairControlled.sub {first second : RealPlaneGroup × RealPlaneGroup →
      cuspidalTensorValues cusp (HomogeneousPoly degree)}
    (hfirst : PairControlled cusp first) (hsecond : PairControlled cusp second) :
    PairControlled cusp (fun pair => first pair - second pair) :=
  fun X _ p q hp hq => (hfirst X p q hp hq).sub (hsecond X p q hp hq)

theorem OneControlled.add {first second : RealPlaneGroup → cuspidalTensorValues cusp
    (HomogeneousPoly degree)}
    (hfirst : OneControlled cusp first) (hsecond : OneControlled cusp second) :
    OneControlled cusp (fun element => first element + second element) :=
  fun X _ p hp => (hfirst X p hp).add (hsecond X p hp)

theorem OneControlled.sub {first second : RealPlaneGroup → cuspidalTensorValues cusp
    (HomogeneousPoly degree)}
    (hfirst : OneControlled cusp first) (hsecond : OneControlled cusp second) :
    OneControlled cusp (fun element => first element - second element) :=
  fun X _ p hp => (hfirst X p hp).sub (hsecond X p hp)

/-- **Coboundaries of controlled one-cochains are controlled.** -/
theorem twoBoundaryCycle_pairControlled
    {cochain : RealPlaneGroup → cuspidalTensorValues cusp (HomogeneousPoly degree)}
    (controlled : OneControlled cusp cochain) :
    PairControlled cusp (fun pair =>
      (twoBoundaryCycle (realPlaneCuspidalRep degree cusp trivialCharacter) cochain pair :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  intro X _ p q hp hq
  exact (((controlled X q hq).plane hp).sub (controlled X _ (hp.mul hq))).add (controlled X p hp)

section Radical

variable {X : Type} [TopologicalSpace X]

theorem planeContinuous_inlRadical {e : X → RealPlaneRadical} (he : Continuous (fun x => (e
    x).toAdd)) :
    PlaneContinuous (fun x => (SemidirectProduct.inl (e x) : RealPlaneGroup)) :=
  ⟨he, continuous_const⟩

theorem PlaneContinuous.left_inl {p : X → RealPlaneGroup} (hp : PlaneContinuous p) :
    PlaneContinuous (fun x => (SemidirectProduct.inl (p x).left : RealPlaneGroup)) :=
  ⟨hp.1, continuous_const⟩

theorem PlaneContinuous.right_inr {p : X → RealPlaneGroup} (hp : PlaneContinuous p) :
    PlaneContinuous (fun x => (SemidirectProduct.inr (p x).right : RealPlaneGroup)) :=
  planeContinuous_inr hp.2

theorem continuous_radicalAction {M : X → BinaryRealGL} (hM : Continuous M) {e : X →
    RealPlaneRadical}
    (he : Continuous (fun x => (e x).toAdd)) :
    Continuous (fun x => (realPlaneRadicalAction (M x) (e x)).toAdd) := by
  simp only [realPlaneRadicalAction_apply]
  exact Continuous.matrix_mulVec (Units.continuous_val.comp hM) he

theorem continuous_inverseLevi {M : X → BinaryRealGL} (hM : Continuous M) {e : X → RealPlaneRadical}
    (he : Continuous (fun x => (e x).toAdd)) :
    Continuous (fun x => (realRadicalInverseLevi (M x) (e x)).toAdd) :=
  continuous_radicalAction (hM.inv) he

/-- **Mixed cocycle values of a controlled relative cocycle are controlled.** -/
theorem mixedCocycle_controlled (cycle : RealPlaneRelative degree cusp)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree))))
    {M : X → BinaryRealGL} (hM : Continuous M) {e : X → RealPlaneRadical}
    (he : Continuous (fun x => (e x).toAdd)) :
    Controlled cusp (fun x => (realPlaneMixedCocycle degree cusp (M x) cycle (e x) :
      cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  simp only [realPlaneMixedCocycle_apply]
  exact (controlled X _ _ (planeContinuous_inr hM)
    (planeContinuous_inlRadical (continuous_inverseLevi hM he))).sub
    (controlled X _ _ (planeContinuous_inlRadical he) (planeContinuous_inr hM))

end Radical

section Binary

/-- Multiplication by a variable, raising the degree of binary homogeneous polynomials. -/
def binaryMulX (degree : ℕ) (i : Fin 2) :
    Binary.HomogeneousPoly degree →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  ((LinearMap.mulLeft ℂ (X i : MvPolynomial (Fin 2) ℂ)).comp
    (homogeneousSubmodule (Fin 2) ℂ degree).subtype).codRestrict _ (fun p =>
      (mem_homogeneousSubmodule _ _).mpr (by
        rw [add_comm]
        exact (isHomogeneous_X ℂ i).mul ((mem_homogeneousSubmodule _ _).mp p.property)))

/-- The coefficient map producing one half of the binary coordinate. -/
def binaryCoordinateMap (degree : ℕ) (i : Fin 2) :
    HomogeneousPoly degree →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  ((degree + 1 : ℂ)⁻¹ • binaryMulX degree i).comp (binaryHomogeneousRestrict degree)

/-- **The binary coordinate only uses the two lattice values.** -/
theorem realUpperCuspidalBinaryCoordinate_eq (cycle : groupCohomology.cocycles₁
    (realUpperCuspidalRep degree cusp)) :
    realUpperCuspidalBinaryCoordinate degree cusp cycle =
      cuspidalTensorMap cusp (binaryCoordinateMap degree 0) (cycle (realRadicalAxis 0 1)) +
        cuspidalTensorMap cusp (binaryCoordinateMap degree 1) (cycle (realRadicalAxis 1 1)) := by
  apply Subtype.ext
  funext argument
  apply Subtype.ext
  rw [realUpperCuspidalBinaryCoordinate_value, smul_add]
  rfl

variable {X : Type} [TopologicalSpace X]

theorem binaryCoordinate_controlled {cycle : X → groupCohomology.cocycles₁ (realUpperCuspidalRep
    degree cusp)}
    (first : Controlled cusp (fun x => (cycle x (realRadicalAxis 0 1) :
      cuspidalTensorValues cusp (HomogeneousPoly degree))))
    (second : Controlled cusp (fun x => (cycle x (realRadicalAxis 1 1) :
      cuspidalTensorValues cusp (HomogeneousPoly degree)))) :
    Controlled cusp (fun x => realUpperCuspidalBinaryCoordinate degree cusp (cycle x)) := by
  simp only [realUpperCuspidalBinaryCoordinate_eq]
  exact (first.map_const (homogeneousBasis degree) _).add (second.map_const (homogeneousBasis
      degree) _)

theorem realUpperBinaryValue_functional_continuous {e : X → RealPlaneRadical}
    (he : Continuous (fun x => (e x).toAdd)) (vector : Binary.HomogeneousPoly (degree + 1))
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    Continuous (fun x => functional (realUpperBinaryValue degree (e x) vector)) := by
  have matrices : Continuous (fun x => realPlaneRadicalMatrix (e x)) := by
    have := (planeContinuous_inlRadical he).matrix
    simpa only [realPlaneMatrix_inl] using this
  have key := realCoefficientComponent_functional_continuous (fun x => realPlaneRadicalMatrix (e x))
    matrices (binaryHomogeneousLift (degree + 1) vector)
    (functional.comp (homogeneousLastDivide degree))
  have equality : (fun x => functional (realUpperBinaryValue degree (e x) vector)) =
      fun x => functional (homogeneousLastDivide degree (binaryHomogeneousLift (degree + 1)
          vector)) -
        (functional.comp (homogeneousLastDivide degree))
          (realCoefficientComponent (degree + 1) trivialCharacter (realPlaneRadicalMatrix (e x))
            (binaryHomogeneousLift (degree + 1) vector)) := by
    funext x
    simp only [realUpperBinaryValue, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub]
    rfl
  rw [equality]
  exact continuous_const.sub key

/-- **The binary section along continuous radicals preserves control.** -/
theorem binarySection_controlled {values : X → cuspidalTensorValues cusp (Binary.HomogeneousPoly
    (degree + 1))}
    (controlled : Controlled cusp values) {e : X → RealPlaneRadical}
    (he : Continuous (fun x => (e x).toAdd)) :
    Controlled cusp (fun x => cuspidalTensorMap cusp (realUpperBinaryValue degree (e x)) (values
        x)) :=
  controlled.map (binaryHomogeneousBasis (degree + 1))
    (fun vector functional => realUpperBinaryValue_functional_continuous he vector functional)

end Binary

section Canonical

variable {index : Type} [Fintype index] (basis : Module.Basis index ℂ (HomogeneousPoly degree))

theorem realPlaneBinaryRelativeCycle_value (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle) (first second : RealPlaneGroup) :
    ((realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val (first, second) :
        cuspidalTensorValues cusp (HomogeneousPoly degree)) =
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl first.left)
        (cuspidalTensorMap cusp (realUpperBinaryValue degree (realPlaneRadicalAction first.right
            second.left))
          (realUpperCuspidalBinaryCoordinate degree cusp (realPlaneMixedCocycle degree cusp
              first.right cycle))) :=
  rfl

/-- **The canonical binary relative cocycle of a controlled relative cocycle is controlled.** -/
theorem realPlaneBinaryRelativeCycle_pairControlled (cycle : RealPlaneRelative degree cusp)
    (regular : RealPlaneRegular degree cusp basis cycle)
    (controlled : PairControlled cusp (fun pair =>
      (cycle.val pair : cuspidalTensorValues cusp (HomogeneousPoly degree)))) :
    PairControlled cusp (fun pair =>
      ((realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val pair :
        cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  intro X _ p q hp hq
  simp only [realPlaneBinaryRelativeCycle_value]
  apply Controlled.plane _ hp.left_inl
  apply binarySection_controlled _ (continuous_radicalAction hp.2 hq.1)
  exact binaryCoordinate_controlled
    (mixedCocycle_controlled cycle controlled hp.2 continuous_const)
    (mixedCocycle_controlled cycle controlled hp.2 continuous_const)

end Canonical

end TernaryPeriodPolynomials.EdgeControl
