module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Edge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneCycle

@[expose] public section


/-!
# The binary edge of a cocycle representing a cup product, for the odd character

Port of `SourceConstruction.DetectSetup` and `DetectEdge` from the trivial character to a
rank-one character `χ` with `χ(-1_∞) = -1` (for instance the odd quadratic character of conductor
three).  The coefficient system is `rationalCoefficientComponent n χ`; the stabilizer `Γ_F` of the
identity plane acts on binary forms of degree `n + 1` through the Levi quotient with determinant
twist `0` (`planeQRepTw`), which is the Levi module `arithmeticBinaryRep (n + 1) 0` of the twisted
edge `identityPlaneBinaryEdgeT` of `AxiomCodeTwisted`.

`PlaneCupDataTw n χ` is the data of the two potentials `a`, `l` on the vertex set `GL₃(ℚ)` and the
radical cocycle `lam`; a degree-two cocycle `Z` of `Γ_F` represents their cup product
(`PlaneCupDataTw.Represents`) if its values on the vertex triples `(1, g, g h)` are
`(l (g h) - l g) (a g - a 1)`.  Then `Z` is a relative two-cocycle for the radical lattice
(`PlaneCupDataTw.cup_relative`), and under the Kostant law its twisted binary edge cocycle is
`m ↦ c • (a (s m) - a 1)` (`PlaneCupDataTw.edgeCycle_value`).  The Kostant law only involves the radical
lattice and is independent of the twist, so `KostantLawTw` is `KostantLaw`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
  (PlaneStab PlaneQ PlaneV KostantLaw plane_radical_commute)
open TernaryPeriodPolynomials.Twisted
  (identityPlaneCoefficientRepT identityPlaneBinaryEdgeCycleT identityPlaneBinaryEdgeCycleT_value
    binaryHomogeneousRestrict_radicalT)

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

/-- The coefficient action of the stabilizer on `V`, for the character `χ`. -/
def planeVRepTw (n : ℕ) (χ : RankOneCharacter) : Representation ℂ PlaneStab (PlaneV n) :=
  (rationalCoefficientComponent n χ).comp
    (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))).subtype

/-- The action of the stabilizer on binary forms, through the Levi quotient, with determinant
twist `0` (the Levi module of the twisted edge). -/
def planeQRepTw (n : ℕ) : Representation ℂ PlaneStab (PlaneQ n) :=
  ((Binary.homogeneousAction (n + 1) 0).comp
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ))).comp identityPlaneLeviProjection

/-- The two potentials whose cup product is the plane source cocycle on the identity plane, with
the two laws used by the binary edge, for the character `χ`.  `lam` is the radical cocycle on the
radical lattice. -/
structure PlaneCupDataTw (n : ℕ) (χ : RankOneCharacter) where
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
      lam r + Representation.linHom (planeQRepTw n) (planeVRepTw n χ)
        (identityPlaneRadicalInclusion r) (l g.val)

/-- A degree-two cocycle of the stabilizer **represents the cup product** of the potentials: on the
vertex triples `(1, g, g h)` it takes the values `(l (g h) - l g) (a g - a 1)`. -/
def PlaneCupDataTw.Represents {n : ℕ} {χ : RankOneCharacter} (D : PlaneCupDataTw n χ)
    (Z : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n χ)) : Prop :=
  ∀ g h : PlaneStab, Z.val.val ![1, g.val, g.val * h.val] =
    (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)

theorem planeQRepTw_apply {n : ℕ} (γ : PlaneStab) (q : PlaneQ n) :
    planeQRepTw n γ q =
      (arithmeticBinaryRep (n + 1) 0).ρ (identityPlaneLeviProjection γ) q := rfl

theorem planeQRepTw_eq_self {n : ℕ} {γ : PlaneStab} (h : identityPlaneLeviProjection γ = 1)
    (q : PlaneQ n) : planeQRepTw n γ q = q := by
  rw [planeQRepTw_apply, h, map_one]
  rfl

/-- The radical lattice acts on `Hom(Q, V)` through its action on `V` alone. -/
theorem linHom_radical_applyTw {n : ℕ} (χ : RankOneCharacter) (r : RadicalLattice)
    (k : PlaneQ n →ₗ[ℂ] PlaneV n) (q : PlaneQ n) :
    Representation.linHom (planeQRepTw n) (planeVRepTw n χ) (identityPlaneRadicalInclusion r) k q =
      planeVRepTw n χ (identityPlaneRadicalInclusion r) (k q) := by
  rw [Representation.linHom_apply]
  change planeVRepTw n χ (identityPlaneRadicalInclusion r)
    (k (planeQRepTw n (identityPlaneRadicalInclusion r)⁻¹ q)) = _
  rw [planeQRepTw_eq_self (γ := (identityPlaneRadicalInclusion r)⁻¹)
    (by rw [map_inv, identityPlaneLeviProjection_radical, inv_one])]

/-- The radical lattice does not change the restriction `x₂ = 0`. -/
theorem planeV_radical_restrictTw {n : ℕ} (χ : RankOneCharacter) (r : RadicalLattice)
    (w : PlaneV n) :
    binaryHomogeneousRestrict n (planeVRepTw n χ (identityPlaneRadicalInclusion r) w) =
      binaryHomogeneousRestrict n w :=
  binaryHomogeneousRestrict_radicalT n χ r w

/-- The Kostant law: the restriction of the radical cocycle to the two generators of the radical
lattice satisfies the Euler identity `(n+1)⁻¹ (X₀ · res λ(e₁) q + X₁ · res λ(e₂) q) = c q`.  It only
involves the radical lattice, hence does not depend on the twist: this is `KostantLaw`. -/
abbrev KostantLawTw (n : ℕ) (lam : RadicalLattice → (PlaneQ n →ₗ[ℂ] PlaneV n)) (c : ℂ) : Prop :=
  KostantLaw n lam c

namespace PlaneCupDataTw

variable {n : ℕ} {χ : RankOneCharacter} (D : PlaneCupDataTw n χ)
  {Z : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n χ)}

/-- The values of the group two-cocycle of a cocycle representing the cup product. -/
theorem group_apply (hZ : D.Represents Z) (g h : PlaneStab) :
    ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ) Z (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

theorem group_radical_left_zero (hZ : D.Represents Z) (r : RadicalLattice) (h : PlaneStab) :
    ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ) Z
        (identityPlaneRadicalInclusion r, h) = 0 := by
  rw [D.group_apply hZ, D.a_radical, sub_self]
  exact map_zero _

/-- The cup cocycle as a relative two-cocycle: it vanishes on pairs of radical elements. -/
theorem cup_relative (hZ : D.Represents Z) :
    ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ) Z ∈
      relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) := by
  intro first second
  exact D.group_radical_left_zero hZ first (identityPlaneRadicalInclusion second)

/-- The cocycle as a relative two-cocycle for the radical lattice. -/
def planeCupRelative (hZ : D.Represents Z) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) :=
  ⟨ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n χ) Z, D.cup_relative hZ⟩

theorem relative_apply (hZ : D.Represents Z) (g h : PlaneStab) :
    (D.planeCupRelative hZ).val (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

/-- The right-hand mixed term `c (u r, s m)` vanishes. -/
theorem edge_term_right (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    (D.planeCupRelative hZ).val (identityPlaneRadicalInclusion r, identityPlaneLeviSection m) = 0 :=
  D.group_radical_left_zero hZ r (identityPlaneLeviSection m)

/-- The restricted left-hand mixed term. -/
theorem edge_term_left (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    binaryHomogeneousRestrict n
        ((D.planeCupRelative hZ).val (identityPlaneLeviSection m,
          identityPlaneRadicalInclusion (upperLeviLatticeInput m r))) =
      binaryHomogeneousRestrict n
        (D.lam r (D.a (identityPlaneLeviSection m).val - D.a 1)) := by
  have hval : (identityPlaneLeviSection m).val *
      (identityPlaneRadicalInclusion (upperLeviLatticeInput m r)).val =
        (identityPlaneRadicalInclusion r).val * (identityPlaneLeviSection m).val :=
    (congrArg Subtype.val (plane_radical_commute m r)).symm
  rw [D.relative_apply hZ, hval, D.l_radical r (identityPlaneLeviSection m),
    LinearMap.sub_apply, LinearMap.add_apply, linHom_radical_applyTw, map_sub, map_add,
    planeV_radical_restrictTw]
  abel

/-- **The edge value.**  The restricted mixed term of the edge cocycle. -/
theorem edge_value (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    binaryHomogeneousRestrict n
        ((D.planeCupRelative hZ).val (identityPlaneLeviSection m,
            identityPlaneRadicalInclusion (upperLeviLatticeInput m r)) -
          (D.planeCupRelative hZ).val (identityPlaneRadicalInclusion r,
            identityPlaneLeviSection m)) =
      binaryHomogeneousRestrict n
        (D.lam r (D.a (identityPlaneLeviSection m).val - D.a 1)) := by
  rw [D.edge_term_right hZ, sub_zero]
  exact D.edge_term_left hZ m r

/-- The twisted binary edge cocycle, pointwise, under the Kostant law. -/
theorem edgeCycle_value (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hZ : D.Represents Z)
    {c : ℂ} (hK : KostantLawTw n D.lam c) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    (identityPlaneBinaryEdgeCycleT n χ hχ (D.planeCupRelative hZ) m).val =
      c • (D.a (identityPlaneLeviSection m).val - D.a 1).val := by
  rw [identityPlaneBinaryEdgeCycleT_value]
  refine (congrArg₂ (fun (u v : Binary.Poly) => ((n : ℂ) + 1)⁻¹ •
      (MvPolynomial.X 0 * u + MvPolynomial.X 1 * v))
    (congrArg Subtype.val (D.edge_value hZ m radicalLatticeFirst))
    (congrArg Subtype.val (D.edge_value hZ m radicalLatticeSecond))).trans ?_
  exact hK _

end PlaneCupDataTw

end TernaryPeriodPolynomials.TwistedSource
