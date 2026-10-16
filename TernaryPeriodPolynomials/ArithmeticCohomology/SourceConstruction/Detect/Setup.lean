module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneAmbientEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula

@[expose] public section


/-!
# Cup products of two potentials on the identity-plane stabilizer

Let `Γ_F = flagArithmeticStabilizer .plane (mk 1)` be the stabilizer of the identity plane in the
arithmetic level group, `V = HomogeneousPoly n` the coefficient module (the group acts by
`rationalCoefficientComponent n trivialCharacter`) and `Q = Binary.HomogeneousPoly (n + 1)`.  The
group `Γ_F` acts on `Q` through its Levi quotient `π = identityPlaneLeviProjection : Γ_F → GL₂(ℤ)`
by `arithmeticBinaryRep (n + 1) (-1)`, and on `Hom(Q, V)` by conjugation.

`PlaneCupData n` is the data of two potentials on the vertex set `GL₃(ℚ)`:

* the Levi potential `a : GL₃(ℚ) → Q`, constant on the orbit of the base vertex `1` under the
  radical lattice `N = ℤ²` of `Γ_F` (`a (u 1) = a 1`);
* the radical potential `l : GL₃(ℚ) → Hom(Q, V)`, satisfying the cocycle law along the radical
  lattice: `l (u g) = lam u + u · l g` for `g ∈ Γ_F`.

A degree-two cocycle `Z` of `Γ_F` in the whole-group homogeneous resolution (`Homogeneous.cocycles`)
*represents the cup product* of the potentials if its values on the vertex triples `(1, g, g h)`,
`g, h ∈ Γ_F`, are `(l (g h) - l g) (a g - a 1)`; the class of such a cocycle in `H²(Γ_F, V)` is
determined by these values (`ambientCocycleToGroup`).  Only these two laws are needed for the binary
edge of the class; equivariance of `Z` is part of `Z ∈ cocycles`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The stabilizer of the identity plane in the arithmetic level group. -/
abbrev PlaneStab : Type :=
  ↥(flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))

/-- The binary forms of degree `n + 1`. -/
abbrev PlaneQ (n : ℕ) : Type := Binary.HomogeneousPoly (n + 1)

/-- The ternary coefficient module of degree `n`. -/
abbrev PlaneV (n : ℕ) : Type := HomogeneousPoly n

/-- The coefficient action of the stabilizer on `V`. -/
def planeVRep (n : ℕ) : Representation ℂ PlaneStab (PlaneV n) :=
  (rationalCoefficientComponent n trivialCharacter).comp
    (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))).subtype

/-- The action of the stabilizer on binary forms, through the Levi quotient, with the determinant
twist `-1`. -/
def planeQRep (n : ℕ) : Representation ℂ PlaneStab (PlaneQ n) :=
  ((Binary.homogeneousAction (n + 1) (-1)).comp
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ))).comp identityPlaneLeviProjection

/-- The values of a one-cocycle of `GL₂(ℤ)` in the binary forms, as a plain function with values in
`Q`. -/
def cocyclePhi (n : ℕ) (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) : PlaneQ n := φ m

/-- The two potentials whose cup product is the plane source cocycle on the identity plane, with
the two laws used by the binary edge.  `lam` is the radical cocycle on the radical lattice. -/
structure PlaneCupData (n : ℕ) where
  /-- The Levi potential. -/
  a : RationalGL3 → PlaneQ n
  /-- The radical potential. -/
  l : RationalGL3 → (PlaneQ n →ₗ[ℂ] PlaneV n)
  /-- The radical cocycle on the radical lattice, the coboundary of `l`. -/
  lam : RadicalLattice → (PlaneQ n →ₗ[ℂ] PlaneV n)
  /-- The Levi potential does not see the radical lattice. -/
  a_radical : ∀ r : RadicalLattice, a (identityPlaneRadicalInclusion r).val = a 1
  /-- The cocycle law of the radical potential along the radical lattice. -/
  l_radical : ∀ (r : RadicalLattice) (g : PlaneStab),
    l ((identityPlaneRadicalInclusion r).val * g.val) =
      lam r + Representation.linHom (planeQRep n) (planeVRep n)
        (identityPlaneRadicalInclusion r) (l g.val)

/-- A degree-two cocycle of the stabilizer **represents the cup product** of the potentials: on the
vertex triples `(1, g, g h)` it takes the values `(l (g h) - l g) (a g - a 1)`. -/
def PlaneCupData.Represents {n : ℕ} (D : PlaneCupData n)
    (Z : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∀ g h : PlaneStab, Z.val.val ![1, g.val, g.val * h.val] =
    (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)

/-- The cup cochain of two potentials: `y ↦ (l y₂ - l y₁) (a y₁ - a y₀)`, the specialization of the
generic cup product of two affine potentials to the evaluation pairing `Q × Hom(Q, V) → V`. -/
def planeCupChain {n : ℕ} (a : RationalGL3 → PlaneQ n)
    (l : RationalGL3 → (PlaneQ n →ₗ[ℂ] PlaneV n)) (y : Fin 3 → RationalGL3) : PlaneV n :=
  (l (y 2) - l (y 1)) (a (y 1) - a (y 0))

/-- The cocycle condition of the cup cochain, in the alternating form of `differentialTwo`. -/
theorem planeCupChain_cocycle {n : ℕ} (a : RationalGL3 → PlaneQ n)
    (l : RationalGL3 → (PlaneQ n →ₗ[ℂ] PlaneV n)) (x : Fin 4 → RationalGL3) :
    planeCupChain a l ![x 1, x 2, x 3] - planeCupChain a l ![x 0, x 2, x 3] +
      planeCupChain a l ![x 0, x 1, x 3] - planeCupChain a l ![x 0, x 1, x 2] = 0 := by
  show (l (x 3) - l (x 2)) (a (x 2) - a (x 1)) - (l (x 3) - l (x 2)) (a (x 2) - a (x 0)) +
      (l (x 3) - l (x 1)) (a (x 1) - a (x 0)) - (l (x 2) - l (x 1)) (a (x 1) - a (x 0)) = 0
  simp only [map_sub, LinearMap.sub_apply]
  abel

end TernaryPeriodPolynomials.SourceConstruction
