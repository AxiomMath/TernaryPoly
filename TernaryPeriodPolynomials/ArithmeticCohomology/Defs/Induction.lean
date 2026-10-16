module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Boundary
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section


/-!
# Normalized induction, Eisenstein holomorphy, and the standard integral

The deformation is δ_P^(1/2+s/3) σ⊗χ. Thus at s=-3/2 the plane
induction is unnormalized. The associate deformation is δ_Q^(1/2-s/3),
so its endpoint has GL_1 character χ|.|² and GL_2 twist σ|det|^-1.
The measures are Lebesgue measure at infinity and mass one on Z_p at finite
places. Meromorphic continuation is constrained by an equality in an actual
right half-plane, not an unconstrained function bearing the operator's name.
-/

noncomputable section
namespace GeneralEisenstein
open Matrix Adelic MeasureTheory Homogeneous

/-- The cohomological point in the specified normalized family. -/
def cohomologicalPoint : ℂ := -3/2

/-- The two actual modulus exponents. -/
def inductionExponent : Side → ℂ → ℂ
  | .plane, s => 1/2+s/3
  | .line, s => 1/2-s/3

/-- The GL_2 Levi block embedding for each side. -/
def binaryLevi (side : Side) (A : BinaryAdelicGL) : AdelicGL :=
  match side with
  | .plane => planeLevi A 1
  | .line => lineLevi 1 A

/-- The unitary-to-cohomological twist, including the modulus of induction. -/
def binaryInductionExponent (n : ℕ) (side : Side) (s : ℂ) : ℂ :=
  match side with
  | .plane => ((n:ℂ)+3)/2 + inductionExponent .plane s
  | .line => ((n:ℂ)+3)/2 - inductionExponent .line s

/-- Smoothness in the actual Hilbert globalization, expressed through the
injective automorphic realization. This excludes merely pointwise-smooth
families of cusp functions that do not define smooth induced vectors. -/
def HasSmoothCuspLift {n k : ℕ} (D : InducingData n) (side : Side) (s : ℂ)
    (f : (Fin k → RealGL3) → AdelicGL → ℂ) : Prop :=
  ∀ a, ∃ v : (Fin (k+1) → RealGL3) → D.cusp.smooth,
    Smooth (fun x => (v x).val) ∧
    ∀ x A, D.cusp.realize (v x) A =
      normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n side s) *
      f (fun i => x i.castSucc) (binaryLevi side A * (a * atInfinity (x (Fin.last k))))

/-- Smooth normalized induced sections in their scalar automorphic realization.
Every GL_2 orbit lies in the independently supplied cusp-function constituent. -/
def IsInduced {n : ℕ} (D : InducingData n) (side : Side) (s : ℂ)
    (f : AdelicGL → ℂ) : Prop :=
  (∀ g, Smooth (fun x : Fin 1 → RealGL3 => f (g * atInfinity (x 0)))) ∧
  (∀ k : finiteLevel, ∀ g, f (g * atFinite k.val) = f g) ∧
  HasSmoothCuspLift D side s (fun (_ : Fin 0 → RealGL3) => f) ∧
  match side with
  | .plane =>
    (∀ a b g, f (planeUnipotent a b * g) = f g) ∧
    (∀ t g, f (planeLevi 1 t * g) =
      D.chi.toMonoidHom t * normPower t (-2*inductionExponent .plane s) * f g) ∧
    (∀ g, (fun A : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det A) (-(((n:ℂ)+3)/2 + inductionExponent .plane s)) *
        f (planeLevi A 1 * g)) ∈ cuspFunctions D.cusp)
  | .line =>
    (∀ a b g, f (lineUnipotent a b * g) = f g) ∧
    (∀ t g, f (lineLevi t 1 * g) =
      D.chi.toMonoidHom t * normPower t (2*inductionExponent .line s) * f g) ∧
    (∀ g, (fun A : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det A) (-(((n:ℂ)+3)/2 - inductionExponent .line s)) *
        f (lineLevi 1 A * g)) ∈ cuspFunctions D.cusp)

/-- Flat sections fix the whole cusp-representation-valued compact realization.
Equality is required after evaluation at every GL_2 adele, not just at its
identity; fixing scalar values on the compact subgroup alone is insufficient. -/
def IsFlatSection {n : ℕ} (D : InducingData n) (F : ℂ → AdelicGL → ℂ) : Prop :=
  (∀ s, IsInduced D .plane s (F s)) ∧
  (∀ g, ∀ s, AnalyticAt ℂ (fun z => F z g) s) ∧
  (∀ s A k, inMaximalCompact k →
    normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n .plane s) *
      F s (planeLevi A 1 * k) =
    normPower (GeneralLinearGroup.det A)
      (-binaryInductionExponent n .plane cohomologicalPoint) *
      F cohomologicalPoint (planeLevi A 1 * k))

/-- Actual left cosets P(Q)\G(Q), represented by inverse right cosets. -/
def eisensteinSummand (F : ℂ → AdelicGL → ℂ) (s : ℂ) (g : AdelicGL)
    (q : Flags .plane) : ℂ :=
  F s (rationalGroup q.out⁻¹ * g)

/-- Meromorphic continuation of the actual plane Eisenstein sum. -/
def IsEisensteinContinuation (F E : ℂ → AdelicGL → ℂ) : Prop :=
  (∀ g s, MeromorphicAt (fun z => E z g) s) ∧
  ∃ R : ℝ, ∀ s : ℂ, R < s.re → ∀ g,
    HasSum (eisensteinSummand F s g) (E s g)

/-- Holomorphy of the plane Eisenstein operator at its cohomological point.
Flat extensions must exist for every section. No global cohomology or graph
condition appears here. -/
def PlaneEisensteinHolomorphic {n : ℕ} (D : InducingData n) : Prop :=
  (∀ f, IsInduced D .plane cohomologicalPoint f →
    ∃ F, IsFlatSection D F ∧ F cohomologicalPoint = f) ∧
  (∀ F, IsFlatSection D F → ∃ E,
    IsEisensteinContinuation F E ∧
    ∀ g, AnalyticAt ℂ (fun z => E z g) cohomologicalPoint)

/-- The standard integral is over the full adelic radical U_Q(A),
with exactly the associate Weyl matrix from the paper convention. -/
def standardIntegrand (F : ℂ → AdelicGL → ℂ) (s : ℂ) (g : AdelicGL)
    (u : Adeles × Adeles) : ℂ :=
  F s (weyl⁻¹ * lineUnipotent u.1 u.2 * g)

/-- Meromorphic continuation of the genuine convergent standard integral. -/
def IsStandardContinuation (F J : ℂ → AdelicGL → ℂ) : Prop :=
  (∀ g s, MeromorphicAt (fun z => J z g) s) ∧
  ∃ R : ℝ, ∀ s : ℂ, R < s.re → ∀ g,
    Integrable (standardIntegrand F s g) radicalMeasure ∧
    J s g = ∫ u, standardIntegrand F s g u ∂radicalMeasure

/-- All smooth homogeneous two-cocycles in the displayed induced representation.
We use the full smooth globalization, not a right-G(R)-unstable K-finite subset. -/
def IsSourceCocycle {n : ℕ} (D : InducingData n) (side : Side)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n) : Prop :=
  (∀ x m, IsInduced D side cohomologicalPoint
    (fun g => (c x g).val.coeff m)) ∧
  (∀ m, HasSmoothCuspLift D side cohomologicalPoint
    (fun x g => (c x g).val.coeff m)) ∧
  (∀ h x g, c (fun i => h * x i) g =
    realCoefficientComponent n D.chi h (c x (g * atInfinity h))) ∧
  (∀ x : Fin 4 → RealGL3, ∀ g,
    c ![x 1,x 2,x 3] g - c ![x 0,x 2,x 3] g +
      c ![x 0,x 1,x 3] g - c ![x 0,x 1,x 2] g = 0)

/-- Restriction/evaluation comparison, written before any choice of cohomology map.
Requiring the formula for every rational representative enforces independence
of flag representatives rather than hiding it behind a choice function. -/
def Evaluates {n : ℕ} (D : InducingData n) (side : Side)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)) :
    Prop :=
  ∀ x q, z.val.val x (QuotientGroup.mk q) =
    c (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup q⁻¹)

/-- The entire cuspidal constituent in maximal-stratum cohomology.
This takes all its smooth cohomological cocycles, not a selected polynomial
source or a preconstructed Eisenstein image. -/
def boundarySummand {n : ℕ} (D : InducingData n) (side : Side) :
    Submodule ℂ (StratumH2 n D.chi side) :=
  Submodule.span ℂ {a | ∃ c, IsSourceCocycle D side c ∧ ∃ z,
    Evaluates D side c z ∧ a = classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) z}

/-- Existence of the actual comparison for every source representative. -/
def SourceComparisonExists {n : ℕ} (D : InducingData n) : Prop :=
  ∀ side c, IsSourceCocycle D side c → ∃ z, Evaluates D side c z

/-- An operator on the full cuspidal summand realizes the standard operator only
if every source cocycle has a flat continuation and its integral descends to
exactly that operator. Construction and descent are required in the conclusion. -/
def RealizesStandard {n : ℕ} (D : InducingData n)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) : Prop :=
  ∀ c, IsSourceCocycle D .plane c → ∀ z, Evaluates D .plane c z →
    ∀ h : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z ∈ boundarySummand D .plane,
    ∃ (F J : ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n),
      (∀ x m, IsFlatSection D (fun s g => (F s x g).val.coeff m)) ∧
      F cohomologicalPoint = c ∧
      (∀ x m, IsStandardContinuation
        (fun s g => (F s x g).val.coeff m)
        (fun s g => (J s x g).val.coeff m)) ∧
      (∀ x g m, AnalyticAt ℂ
        (fun s => (J s x g).val.coeff m) cohomologicalPoint) ∧
      IsSourceCocycle D .line (J cohomologicalPoint) ∧
      ∃ z', Evaluates D .line (J cohomologicalPoint) z' ∧
        (T ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z,h⟩).val = classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z'

end GeneralEisenstein

end
