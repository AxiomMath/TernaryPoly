module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Groups
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.BinaryCoefficients
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section


/-!
# Independently specified cuspidal automorphic inducing data

The unitary constituent is supplied before the Eisenstein constructions. Its
smooth vectors are identified with actual scalar cuspidal automorphic functions;
the realization respects every adelic right translation. No boundary-image,
projector, dimension, or Eisenstein conclusion is an input field.
-/

noncomputable section
namespace GeneralEisenstein
open Matrix MeasureTheory Adelic

abbrev BinaryAdelicGL := GeneralLinearGroup (Fin 2) Adeles
abbrev BinaryRealGL := GeneralLinearGroup (Fin 2) ℝ
abbrev BinaryFiniteGL := GeneralLinearGroup (Fin 2) FiniteAdeles
abbrev BinaryRationalGL := GeneralLinearGroup (Fin 2) ℚ

/-- Complex norm powers use the positive global adelic norm and the real logarithm. -/
def normPower (t : Adelesˣ) (z : ℂ) : ℂ :=
  Complex.exp (z * (Real.log (adeleNorm t : ℝ) : ℂ))

/-- A unitary idele-class character with algebraic weight zero at infinity. -/
structure RankOneCharacter where
  toMonoidHom : Adelesˣ →* ℂ
  continuous : Continuous toMonoidHom
  unitary : ∀ t, ‖toMonoidHom t‖ = 1
  rational : ∀ q : ℚˣ, toMonoidHom (Units.map rationalAdele q) = 1
  positiveReal : ∀ t : ℝˣ, 0 < t.val → toMonoidHom (realAdeleUnit t) = 1

/-- Smooth archimedean vectors, smooth at the finite places as well. -/
def IsSmoothVector {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Representation ℂ BinaryAdelicGL H) (v : H) : Prop :=
  Smooth (fun x : Fin 1 → BinaryRealGL => π (atInfinity (x 0)) v) ∧
  ∃ U : Subgroup BinaryFiniteGL, IsOpen (U : Set BinaryFiniteGL) ∧
    IsCompact (U : Set BinaryFiniteGL) ∧ ∀ u : U, π (atFinite u.val) v = v

/-- A Hilbert realization of one irreducible unitary cuspidal automorphic representation.

`realize` is defined on exactly the smooth vectors. Cuspidality is the vanishing
of the actual adelic unipotent integral, with its specified measure.
-/
structure CuspidalRepresentation where
  H : Type
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  π : Representation ℂ BinaryAdelicGL H
  nontrivial : Nontrivial H
  unitary : ∀ g v, ‖π g v‖ = ‖v‖
  continuous : ∀ v, Continuous (fun g => π g v)
  irreducible : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
    (∀ g v, v ∈ W → π g v ∈ W) → W = ⊥ ∨ W = ⊤
  smooth : Submodule ℂ H
  smooth_exact : ∀ v, v ∈ smooth ↔ IsSmoothVector π v
  smooth_stable : ∀ g v, v ∈ smooth → π g v ∈ smooth
  realize : smooth →ₗ[ℂ] (BinaryAdelicGL → ℂ)
  injective : Function.Injective realize
  equivariant : ∀ g (v : smooth) x,
    realize ⟨π g v.val, smooth_stable g v.val v.property⟩ x = realize v (x*g)
  centralCharacter : Adelesˣ →* ℂ
  centralUnitary : ∀ t, ‖centralCharacter t‖ = 1
  central : ∀ t v x, realize v (GeneralLinearGroup.scalar (Fin 2) t * x) =
    centralCharacter t * realize v x
  leftRational : ∀ γ : BinaryRationalGL, ∀ v x,
    realize v (GeneralLinearGroup.map rationalAdele γ * x) = realize v x
  scalarSmooth : ∀ v g, Smooth (fun x : Fin 1 → BinaryRealGL =>
    realize v (g * atInfinity (x 0)))
  bounded : ∀ v, ∃ C : ℝ, ∀ x, ‖realize v x‖ ≤ C
  cuspidal : ∀ v g,
    IntegrableOn (fun u => realize v (binaryUnipotent u * g)) additiveDomain adeleMeasure ∧
    (∫ u in additiveDomain, realize v (binaryUnipotent u * g) ∂adeleMeasure) = 0

attribute [instance] CuspidalRepresentation.normed CuspidalRepresentation.inner
  CuspidalRepresentation.complete

/-- The actual smooth cusp-function constituent, with no restriction on conductor. -/
def cuspFunctions (D : CuspidalRepresentation) : Submodule ℂ (BinaryAdelicGL → ℂ) :=
  LinearMap.range D.realize

/-- Polynomial-valued cusp functions are the finite-dimensional coefficient tensor. -/
def BinaryValues (D : CuspidalRepresentation) (n : ℕ)
    (f : BinaryAdelicGL → Binary.HomogeneousPoly (n+1)) : Prop :=
  ∀ monomial : Fin 2 →₀ ℕ,
    (fun g => (f g).val.coeff monomial) ∈ cuspFunctions D

/-- The plane Levi coefficient is det^-1 Sym^(n+1)((C²)*), weight (-1,-n-2). -/
def binaryCoefficient (n : ℕ) (g : BinaryRealGL) :
    Module.End ℂ (Binary.HomogeneousPoly (n+1)) :=
  Binary.homogeneousAction (n+1) (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) g)

/-- The actual twisted right action, before imposing the cohomological condition. -/
def binaryCohomologicalAction (n : ℕ) (g : BinaryRealGL)
    (f : BinaryAdelicGL → Binary.HomogeneousPoly (n+1))
    (x : BinaryAdelicGL) : Binary.HomogeneousPoly (n+1) :=
  normPower (GeneralLinearGroup.det (atInfinity g)) (((n:ℂ)+3)/2) •
    binaryCoefficient n g (f (x * atInfinity g))

/-- Nonzero smooth continuous H¹ with the displayed algebraic coefficient.
The quantifier over all zero-cochains keeps the full incoming differential. -/
def Cohomological (D : CuspidalRepresentation) (n : ℕ) : Prop :=
  ∃ c : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n+1),
    (∀ g, BinaryValues D n (c g)) ∧
    (∀ monomial, ∃ v : (Fin 2 → BinaryRealGL) → D.smooth,
      Smooth (fun x => (v x).val) ∧ ∀ x A,
      D.realize (v x) A =
        (c (x 0) (A * atInfinity (x 1))).val.coeff monomial) ∧
    (∃ U : Subgroup BinaryFiniteGL, IsOpen (U : Set BinaryFiniteGL) ∧
      IsCompact (U : Set BinaryFiniteGL) ∧
      ∀ u : U, ∀ g x, c g (x * atFinite u.val) = c g x) ∧
    (∀ g h x, c (g*h) x = c g x + binaryCohomologicalAction n g (c h) x) ∧
    ¬ ∃ v : BinaryAdelicGL → Binary.HomogeneousPoly (n+1),
      BinaryValues D n v ∧ ∀ g x, c g x = binaryCohomologicalAction n g v x - v x

/-- The independently supplied inducing pair σ⊗χ.
Here σ is the unitary representation twisted by |det|^((n+3)/2), and χ has
weight zero. The associate side is forced by the normalized induction below. -/
structure InducingData (n : ℕ) where
  cusp : CuspidalRepresentation
  chi : RankOneCharacter
  cohomological : Cohomological cusp n

end GeneralEisenstein

end
