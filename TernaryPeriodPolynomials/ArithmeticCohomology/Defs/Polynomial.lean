module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.CuspidalBoundary
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.Ring.NamePowerVars

@[expose] public section


/-!
# The actual polynomial, restricted-building functional, and path class

All chains are finite chains on the rational incidence graph. The functional
is extended linearly to the ambient chain space only for convenience; its
values outside good cycles are never used in the path formula. Apartment
normalization and the Bernoulli mixed coordinate are literal formulas from
§4.1, including the minus sign of the mixed bar edge.
-/

noncomputable section
namespace GeneralEisenstein
open Matrix Homogeneous MvPolynomial

/-- Symmetric homogeneous solutions of the paper's polynomial relation. -/
def SymmetricSolution {n : ℕ} (f : HomogeneousPoly n) : Prop :=
  (∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => X (p i)) f.val = f.val) ∧
  f.val + bind₁ ![-X 1, X 0 - X 1, X 2] f.val +
    bind₁ ![X 1 - X 0, -X 0, X 2] f.val = 0

/-- The finite Bernoulli operator B(-t ∂_X); B₁=-1/2. -/
def bernoulliOperator (n : ℕ) (t p : Poly) : Poly :=
  ∑ r ∈ Finset.range (n+1), C ((bernoulli r : ℂ) / (r.factorial : ℂ)) *
    (-t)^r * ((fun p : Poly => pderiv 0 p)^[r]) p

/-- The paper's exact symmetric Bernoulli obstruction, equation Jdef. -/
def bernoulliObstruction {n : ℕ} (f : HomogeneousPoly n) : Poly :=
  let ψ₁ := bind₁ ![X 2 - 2*X 1, -X 0, X 0 - X 1] f.val
  let ψ₂ := ψ₁ - bind₁ ![X 2 - X 0, X 0 - 2*X 1, -X 1] f.val +
    bind₁ ![X 2 - 2*X 1, X 1 - X 0, X 0 - 2*X 1] f.val
  X 2 * bernoulliOperator n (X 1) ψ₁ - X 1 * bernoulliOperator n (X 2) ψ₂

abbrev BuildingVertices := Flags .plane ⊕ Flags .line
abbrev EdgeChains := Edges →₀ ℂ
abbrev VertexChains := BuildingVertices →₀ ℂ

/-- Edges are oriented from their line endpoint to their plane endpoint. -/
def chainBoundary : EdgeChains →ₗ[ℂ] VertexChains :=
  Finsupp.linearCombination ℂ (fun e =>
    Finsupp.single (Sum.inl (endpoint .plane e)) 1 -
      Finsupp.single (Sum.inr (endpoint .line e)) 1)

def translateChain (g : RationalGL3) : EdgeChains →ₗ[ℂ] EdgeChains :=
  Finsupp.lmapDomain ℂ ℂ (fun e => g • e)

def translateVertex (g : RationalGL3) : BuildingVertices → BuildingVertices
  | .inl q => .inl (g • q)
  | .inr q => .inr (g • q)

/-- The actual full subgraph on good vertices, inside the full incidence graph. -/
def GoodChain (c : EdgeChains) : Prop :=
  ∀ e ∈ c.support, GoodFlag .plane (endpoint .plane e) ∧
    GoodFlag .line (endpoint .line e)

def GoodCycle (c : EdgeChains) : Prop := chainBoundary c = 0 ∧ GoodChain c

def swapFirstTwo : RationalGL3 :=
  ⟨!![0,1,0;1,0,0;0,0,1], !![0,1,0;1,0,0;0,0,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def swapLastTwo : RationalGL3 :=
  ⟨!![1,0,0;0,0,1;0,1,0], !![1,0,0;0,0,1;0,1,0], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- The oriented hexagon A(v₁,v₂,v₃), for the columns of g. -/
def apartment (g : RationalGL3) : EdgeChains :=
  Finsupp.single (QuotientGroup.mk g) 1 -
    Finsupp.single (QuotientGroup.mk (g*swapFirstTwo)) 1 +
    Finsupp.single (QuotientGroup.mk (g*Adelic.weyl)) 1 -
    Finsupp.single (QuotientGroup.mk (g*Adelic.weyl*swapFirstTwo)) 1 +
    Finsupp.single (QuotientGroup.mk (g*Adelic.weyl^2)) 1 -
    Finsupp.single (QuotientGroup.mk (g*Adelic.weyl^2*swapFirstTwo)) 1

/-- Exact frame evaluation, with columns already signed to have last entry 1
modulo three. Extending F to other chains does not impose values there. -/
def IsPolynomialFunctional {n : ℕ} (f : HomogeneousPoly n)
    (F : EdgeChains →ₗ[ℂ] HomogeneousPoly n) : Prop :=
  (∀ g : rationalLevel, ∀ c, GoodCycle c →
    F (translateChain g.val c) = rationalCoefficientComponent n trivialCharacter g.val (F c)) ∧
  ∀ V : IntegralGL3, (∀ j, (V.val 2 j : ZMod 3) = 1) →
    (F (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) V))).val =
      C ((GeneralLinearGroup.det V : ℤ) : ℂ) *
        substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) V)⁻¹).val f.val

/-- The paper's base vertex G₀ = span(e₁,e₃), which is good. -/
def pathBase : BuildingVertices := .inl (QuotientGroup.mk swapLastTwo)

/-- Finite good chains from G₀ to gG₀; no connectivity assumption is supplied. -/
def IsPathFamily (τ : rationalLevel → EdgeChains) : Prop :=
  ∀ g, GoodChain (τ g) ∧ chainBoundary (τ g) =
    Finsupp.single (translateVertex g.val pathBase) 1 - Finsupp.single pathBase 1

/-- The actual path-defect cocycle, homogenized on arithmetic group vertices.
Its extension to ambient rational vertices represents the same ordinary H². -/
def RealizesPathClass {n : ℕ} (F : EdgeChains →ₗ[ℂ] HomogeneousPoly n)
    (τ : rationalLevel → EdgeChains)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∀ g₀ g₁ g₂ : rationalLevel,
    c.val.val ![g₀.val,g₁.val,g₂.val] =
      rationalCoefficientComponent n trivialCharacter g₀.val
        (F (τ (g₀⁻¹*g₁) + translateChain (g₀⁻¹*g₁).val (τ (g₁⁻¹*g₂)) - τ (g₀⁻¹*g₂)))

/-- The specified order-three generator of the bad-line binary Levi. -/
def binaryA : RationalGL3 :=
  ⟨!![1,0,0;0,1,-1;0,3,-2], !![1,0,0;0,-2,1;0,-3,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num, by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num⟩

def binaryB : RationalGL3 :=
  ⟨!![1,0,0;0,-1,0;0,-3,1], !![1,0,0;0,-1,0;0,-3,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def binaryR : RationalGL3 :=
  ⟨!![1,0,0;0,-1,0;0,0,1], !![1,0,0;0,-1,0;0,0,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- e(z)(l)(u) = z(l,l⁻¹ul)-z(u,l), with z(g,h)=c(1,g,gh). -/
def mixedBarEdge {n : ℕ}
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (l u : RationalGL3) : Poly :=
  (c.val.val ![1,l,u*l]).val - (c.val.val ![1,u,u*l]).val

/-- The literal Bernoulli contraction of both radical generators. -/
def mixedBernoulliCoordinate {n : ℕ}
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (l : RationalGL3) : Poly :=
  X 2 * bernoulliOperator n (X 1) (mixedBarEdge c l (Adelic.lineUnipotent 1 0)) -
    X 1 * bernoulliOperator n (X 2) (mixedBarEdge c l (Adelic.lineUnipotent 0 1))

/-- The literal integral block-diagonal Levi of the bad-line stabilizer. -/
def BadLineLevi (g : IntegralGL3) : Prop :=
  g ∈ arithmeticLevel ∧ g.val 0 1 = 0 ∧ g.val 0 2 = 0 ∧
    g.val 1 0 = 0 ∧ g.val 2 0 = 0

/-- The chosen path representative has zero pure radical and pure Levi parts.
Together with the mixed-edge comparison this records the (1,1) restriction,
without assuming a Hochschild–Serre dictionary supplied by a solver. -/
def PureMixedBadLine {n : ℕ}
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  (∀ s t s' t' : ℤ,
    c.val.val ![1, Adelic.lineUnipotent (s : ℚ) (t : ℚ),
      Adelic.lineUnipotent (s : ℚ) (t : ℚ) *
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ)] = 0) ∧
  ∀ l l' : IntegralGL3, BadLineLevi l → BadLineLevi l' →
    c.val.val ![1, GeneralLinearGroup.map (Int.castRingHom ℚ) l,
      GeneralLinearGroup.map (Int.castRingHom ℚ) (l*l')] = 0

/-- Construct the actual class, compare the exact signed Bernoulli coordinate,
prove innerness and good-cusp vanishing, and prove detection of the obstruction.
Neither an automorphic constituent nor an isomorphism is an input. -/
def PolynomialBoundaryBridge {n : ℕ} (f : HomogeneousPoly n) : Prop :=
  ∃ (F : EdgeChains →ₗ[ℂ] HomogeneousPoly n) (τ : rationalLevel → EdgeChains)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
    IsPolynomialFunctional f F ∧ IsPathFamily τ ∧ RealizesPathClass F τ c ∧
    (∀ τ' c', IsPathFamily τ' → RealizesPathClass F τ' c' →
      classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c' =
        classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) ∧
    GoodBoundaryVanishing n trivialCharacter (globalCoordinates n trivialCharacter c) ∧
    InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 ∧
    PureMixedBadLine c ∧
    mixedBernoulliCoordinate c binaryA = -bernoulliObstruction f ∧
    mixedBernoulliCoordinate c binaryB = 0 ∧ mixedBernoulliCoordinate c binaryR = 0 ∧
    ((globalCoordinates n trivialCharacter c).2 = 0 → bernoulliObstruction f = 0)

end GeneralEisenstein
end
