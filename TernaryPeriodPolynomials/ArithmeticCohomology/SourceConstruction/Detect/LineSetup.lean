module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineBoundaryNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2

@[expose] public section


/-!
# Cup products of two potentials on the good-line stabilizer

Let `Γ_L = flagArithmeticStabilizer .line (mk rationalGoodLine)` be the stabilizer of the good line
`⟨e₃⟩` in the arithmetic level group, `V = HomogeneousPoly n` the coefficient module (the group acts
by `rationalCoefficientComponent n trivialCharacter`) and `Q = Binary.HomogeneousPoly (n + 1)`.  The
group `Γ_L` is the split extension of `GL₂(ℤ)` (the Levi quotient
`π = goodLineLeviProjection : Γ_L → GL₂(ℤ)`) by the radical lattice `N = ℤ²` (embedded by
`goodLineRadicalInclusion` as the lower unipotents `lowerPlaneUnipotent (3 r₁) (3 r₂)`).  It acts on
`Q` through `π` by `arithmeticBinaryRep (n + 1) 0` (determinant twist `0`), and on `Hom(Q, V)` by
conjugation.

`LineCupData n` is the data of two potentials on the vertex set `GL₃(ℚ)`, in the frame of the good
line `⟨e₃⟩`:

* the Levi potential `a : GL₃(ℚ) → Q`, constant on the orbit of the base vertex `1` under the
  radical lattice (`a (u r) = a 1`);
* the radical potential `l : GL₃(ℚ) → Hom(Q, V)`, satisfying the cocycle law along the radical
  lattice: `l (u r · g) = lam r + u r · l g` for `g ∈ Γ_L`.

A degree-two cocycle `Z` of `Γ_L` in the whole-group homogeneous resolution (`Homogeneous.cocycles`)
*represents the cup product* of the potentials if its values on the vertex triples `(1, g, g h)`,
`g, h ∈ Γ_L`, are `(l (g h) - l g) (a g - a 1)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The stabilizer of the good line `⟨e₃⟩` in the arithmetic level group. -/
abbrev LineStab : Type :=
  ↥(flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))

/-- The binary forms of degree `n + 1`. -/
abbrev LineQ (n : ℕ) : Type := Binary.HomogeneousPoly (n + 1)

/-- The ternary coefficient module of degree `n`. -/
abbrev LineV (n : ℕ) : Type := HomogeneousPoly n

/-- The coefficient action of the stabilizer on `V`. -/
def lineVRep (n : ℕ) : Representation ℂ LineStab (LineV n) :=
  (rationalCoefficientComponent n trivialCharacter).comp
    (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)).subtype

/-- The action of the stabilizer on binary forms, through the Levi quotient, with determinant
twist `0`. -/
def lineQRep (n : ℕ) : Representation ℂ LineStab (LineQ n) :=
  ((Binary.homogeneousAction (n + 1) 0).comp
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ))).comp goodLineLeviProjection

/-- The values of a one-cocycle of `GL₂(ℤ)` in the binary forms, as a plain function with values in
`Q`. -/
def lineCocyclePhi (n : ℕ) (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) : LineQ n := φ m

/-- The two potentials whose cup product is the line source cocycle on the good line, with the two
laws used by the binary edge.  `lam` is the radical cocycle on the radical lattice. -/
structure LineCupData (n : ℕ) where
  /-- The Levi potential. -/
  a : RationalGL3 → LineQ n
  /-- The radical potential. -/
  l : RationalGL3 → (LineQ n →ₗ[ℂ] LineV n)
  /-- The radical cocycle on the radical lattice, the coboundary of `l`. -/
  lam : RadicalLattice → (LineQ n →ₗ[ℂ] LineV n)
  /-- The Levi potential does not see the radical lattice. -/
  a_radical : ∀ r : RadicalLattice, a (goodLineRadicalInclusion r).val = a 1
  /-- The cocycle law of the radical potential along the radical lattice. -/
  l_radical : ∀ (r : RadicalLattice) (g : LineStab),
    l ((goodLineRadicalInclusion r).val * g.val) =
      lam r + Representation.linHom (lineQRep n) (lineVRep n)
        (goodLineRadicalInclusion r) (l g.val)

/-- A degree-two cocycle of the stabilizer **represents the cup product** of the potentials: on the
vertex triples `(1, g, g h)` it takes the values `(l (g h) - l g) (a g - a 1)`. -/
def LineCupData.Represents {n : ℕ} (D : LineCupData n)
    (Z : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∀ g h : LineStab, Z.val.val ![1, g.val, g.val * h.val] =
    (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)

/-- The cup cochain of two potentials: `y ↦ (l y₂ - l y₁) (a y₁ - a y₀)`. -/
def lineCupChain {n : ℕ} (a : RationalGL3 → LineQ n)
    (l : RationalGL3 → (LineQ n →ₗ[ℂ] LineV n)) (y : Fin 3 → RationalGL3) : LineV n :=
  (l (y 2) - l (y 1)) (a (y 1) - a (y 0))

/-- The cocycle condition of the cup cochain, in the alternating form of `differentialTwo`. -/
theorem lineCupChain_cocycle {n : ℕ} (a : RationalGL3 → LineQ n)
    (l : RationalGL3 → (LineQ n →ₗ[ℂ] LineV n)) (x : Fin 4 → RationalGL3) :
    lineCupChain a l ![x 1, x 2, x 3] - lineCupChain a l ![x 0, x 2, x 3] +
      lineCupChain a l ![x 0, x 1, x 3] - lineCupChain a l ![x 0, x 1, x 2] = 0 := by
  show (l (x 3) - l (x 2)) (a (x 2) - a (x 1)) - (l (x 3) - l (x 2)) (a (x 2) - a (x 0)) +
      (l (x 3) - l (x 1)) (a (x 1) - a (x 0)) - (l (x 2) - l (x 1)) (a (x 1) - a (x 0)) = 0
  simp only [map_sub, LinearMap.sub_apply]
  abel

end TernaryPeriodPolynomials.SourceConstruction
