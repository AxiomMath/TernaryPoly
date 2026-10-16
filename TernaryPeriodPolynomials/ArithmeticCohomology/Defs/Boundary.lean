module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.HomogeneousCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Automorphic
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section


/-!
# Whole arithmetic cohomology and maximal boundary coordinates

The flag modules below are coinduced modules. Shapiro's lemma identifies their
cohomology with the product over arithmetic orbits of rational maximal
parabolics, with the actual stabilizer coefficients. Global restriction is
induced by constant functions on flags. The spectral projection in the problem
is required on this whole space; it is not restricted to constructed sources.

We use these coordinates, not an identification of their direct product with
the full Borel--Serre boundary. The cuspidal associate pair is split off by the
Hecke projection, whose existence and uniqueness are part of the conclusion.
-/

noncomputable section
namespace GeneralEisenstein
open Matrix Adelic Homogeneous

abbrev RealGL3 := GeneralLinearGroup (Fin 3) ℝ

/-- Scalar extension of the coefficient action to the real group. -/
def realCoefficient (n : ℕ) : Representation ℂ RealGL3 (HomogeneousPoly n) :=
  (homogeneousAction n (-1)).comp (GeneralLinearGroup.map (algebraMap ℝ ℂ))

/-- The real determinant embedded as an idele. -/
def realUnitHom : ℝˣ →* Adelesˣ where
  toFun := realAdeleUnit
  map_one' := by apply Units.ext; rfl
  map_mul' a b := by
    apply Units.ext
    change (a.val * b.val, (1:FiniteAdeles)) = (a.val * b.val, (1:FiniteAdeles)*1)
    rw [one_mul]

/-- The fixed compatible component character comes from the rank-one block. -/
def componentCharacter (χ : RankOneCharacter) : RealGL3 →* ℂ :=
  χ.toMonoidHom.comp (realUnitHom.comp GeneralLinearGroup.det)

/-- Taking the specified component is equivalent to twisting the full-group
cochains by this sign character. Its value is ±1, hence equals its inverse. -/
def realCoefficientComponent (n : ℕ) (χ : RankOneCharacter) :
    Representation ℂ RealGL3 (HomogeneousPoly n) where
  toFun g := componentCharacter χ g • realCoefficient n g
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change componentCharacter χ (g*h) • realCoefficient n (g*h) v =
      componentCharacter χ g • realCoefficient n g
        (componentCharacter χ h • realCoefficient n h v)
    rw [map_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

/-- The rational action retains the determinant magnitude and the real sign separately. -/
def rationalCoefficientComponent (n : ℕ) (χ : RankOneCharacter) :
    Representation ℂ RationalGL3 (HomogeneousPoly n) :=
  (realCoefficientComponent n χ).comp (GeneralLinearGroup.map (algebraMap ℚ ℝ))

/-- The literal rational image of the congruence subgroup. -/
def rationalLevel : Subgroup RationalGL3 := rationalInclusion.range

/-- The two rational maximal-parabolic flag varieties. -/
inductive Side | plane | line
  deriving DecidableEq

def parabolic : Side → Subgroup RationalGL3
  | .plane => planeParabolic ℚ
  | .line => lineParabolic ℚ

abbrev Flags (s : Side) := RationalGL3 ⧸ parabolic s

/-- Functions on rational flags carry the natural coefficient-valued action. -/
def functionRepresentation {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (X : Type) [MulAction RationalGL3 X] :
    Representation ℂ RationalGL3 (X → V) where
  toFun g :=
    { toFun := fun f x => ρ g (f (g⁻¹ • x))
      map_add' := by intro f h; funext x; exact map_add (ρ g) _ _
      map_smul' := by intro a f; funext x; exact map_smul (ρ g) a _ }
  map_one' := by ext f x; simp
  map_mul' g h := by
    ext f x
    simp only [_root_.mul_inv_rev, mul_smul, map_mul, Module.End.mul_apply,
      LinearMap.coe_mk, AddHom.coe_mk]

/-- Specialization to a rational maximal-parabolic flag variety. -/
def flagRepresentation {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (s : Side) :=
  functionRepresentation ρ (Flags s)

abbrev WholeGlobalH2 (n : ℕ) (χ : RankOneCharacter) :=
  H2 rationalLevel (rationalCoefficientComponent n χ)

abbrev StratumH2 (n : ℕ) (χ : RankOneCharacter) (s : Side) :=
  H2 rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)

abbrev BoundaryCoordinates (n : ℕ) (χ : RankOneCharacter) :=
  StratumH2 n χ .plane × StratumH2 n χ .line

/-- Pulling a global cocycle back to each maximal stratum is literally constant on flags. -/
def restrictionCocycle (n : ℕ) (χ : RankOneCharacter) (s : Side)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) :=
  ⟨⟨fun x _ => c.val.val x, by
    intro γ x
    funext f
    exact c.val.property γ x⟩, by
    funext x f
    exact congrFun c.property x⟩

/-- Finite representatives for the actual double coset Γ g Γ / Γ. -/
structure HeckeCorrespondence where
  g : RationalGL3
  representatives : Finset RationalGL3
  inDoubleCoset : ∀ r ∈ representatives, ∃ a b : rationalLevel, r = a.val * g * b.val
  complete : ∀ a b : rationalLevel, ∃ r ∈ representatives,
    r⁻¹ * (a.val * g * b.val) ∈ rationalLevel
  disjoint : ∀ r ∈ representatives, ∀ t ∈ representatives,
    r⁻¹ * t ∈ rationalLevel → r = t

/-- The finite double-coset action in the ambient homogeneous resolution. -/
def heckeCochain {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (t : HeckeCorrespondence)
    (c : cochains rationalLevel ρ 2) (x : Fin 3 → RationalGL3) : V :=
  ∑ r ∈ t.representatives, ρ r (c.val (fun i => r⁻¹ * x i))

/-- A cohomology action must descend from that formula on every representative.
Its well-definedness is an output obligation, not a hypothesis of the theorem. -/
def RealizesHecke {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V)
    (T : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel ρ)) : Prop :=
  ∀ t c, ∃ z : cocycles rationalLevel ρ,
    (∀ x, z.val.val x = heckeCochain ρ t c.val x) ∧
    T t (classOf rationalLevel ρ c) = classOf rationalLevel ρ z

/-- The restriction map must be the descent of constant-on-flags restriction. -/
def RealizesRestriction (n : ℕ) (χ : RankOneCharacter)
    (r : WholeGlobalH2 n χ →ₗ[ℂ] BoundaryCoordinates n χ) : Prop :=
  ∀ c, r (classOf rationalLevel (rationalCoefficientComponent n χ) c) =
    (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane)
      (restrictionCocycle n χ .plane c),
     classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)
      (restrictionCocycle n χ .line c))

end GeneralEisenstein

end
