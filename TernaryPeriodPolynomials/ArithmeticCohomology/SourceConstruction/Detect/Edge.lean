module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Setup

@[expose] public section


/-!
# The binary edge of a cocycle representing a cup product

Let `D : PlaneCupData n` and let `Z` be a degree-two cocycle of the identity-plane stabilizer that
represents the cup product of the potentials of `D` (`PlaneCupData.Represents`).  The group
two-cocycle `ambientCocycleToGroup Z` vanishes on pairs of radical elements
(`PlaneCupData.cup_relative`: `a` is constant on the radical orbit of `1`), so it is literally a
relative two-cocycle (`PlaneCupData.planeCupRelative`).  The mixed part of its edge cocycle is
computed in closed form (`PlaneCupData.edge_value`):

  `binaryRestrict (c (s m, u (m·r)) - c (u r, s m)) = binaryRestrict (lam r (a (s m) - a 1))`,

with `s m = identityPlaneLeviSection m`, `u r = identityPlaneRadicalInclusion r`.  Under the Kostant
law `KostantLaw n lam c` (the Euler identity for the restriction of `lam` to the two generators of
the radical lattice) the binary edge cocycle is `m ↦ c • (a (s m) - a 1)`
(`PlaneCupData.edgeCycle_value`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

theorem planeQRep_apply {n : ℕ} (γ : PlaneStab) (q : PlaneQ n) :
    planeQRep n γ q =
      (arithmeticBinaryRep (n + 1) (-1)).ρ (identityPlaneLeviProjection γ) q := rfl

theorem planeQRep_eq_self {n : ℕ} {γ : PlaneStab} (h : identityPlaneLeviProjection γ = 1)
    (q : PlaneQ n) : planeQRep n γ q = q := by
  rw [planeQRep_apply, h, map_one]
  rfl

/-- The group element `u r · s m` is `s m · u (m · r)`. -/
theorem plane_radical_commute (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    identityPlaneRadicalInclusion r * identityPlaneLeviSection m =
      identityPlaneLeviSection m *
        identityPlaneRadicalInclusion (upperLeviLatticeInput m r) := by
  have h := splitRadicalInput_commute identityPlaneSplitting m r
  rw [show splitRadicalInput identityPlaneSplitting m r = upperLeviLatticeInput m r from
    identityPlaneSplitting_inverse_action m r] at h
  exact h

/-- The radical lattice acts on `Hom(Q, V)` through its action on `V` alone. -/
theorem linHom_radical_apply {n : ℕ} (r : RadicalLattice) (k : PlaneQ n →ₗ[ℂ] PlaneV n)
    (q : PlaneQ n) :
    Representation.linHom (planeQRep n) (planeVRep n) (identityPlaneRadicalInclusion r) k q =
      planeVRep n (identityPlaneRadicalInclusion r) (k q) := by
  rw [Representation.linHom_apply]
  change planeVRep n (identityPlaneRadicalInclusion r)
    (k (planeQRep n (identityPlaneRadicalInclusion r)⁻¹ q)) = _
  rw [planeQRep_eq_self (γ := (identityPlaneRadicalInclusion r)⁻¹)
    (by rw [map_inv, identityPlaneLeviProjection_radical, inv_one])]

/-- The radical lattice does not change the restriction `x₂ = 0`. -/
theorem planeV_radical_restrict {n : ℕ} (r : RadicalLattice) (w : PlaneV n) :
    binaryHomogeneousRestrict n (planeVRep n (identityPlaneRadicalInclusion r) w) =
      binaryHomogeneousRestrict n w :=
  binaryHomogeneousRestrict_upperLattice n r w

/-- **The Kostant law**: the restriction of the radical cocycle to the two generators of the radical
lattice satisfies the Euler identity `(n+1)⁻¹ (X₀ · res λ(e₁) q + X₁ · res λ(e₂) q) = c q`.  For the
radical cocycle `λ(u(s,t)) q = ((ρ u)(ι q) - ι q) / x₂` of the real plane parabolic one has
`res λ(u(s,t)) q = -(s ∂₀ q + t ∂₁ q)`, so `c = -1` by Euler's identity. -/
def KostantLaw (n : ℕ) (lam : RadicalLattice → (PlaneQ n →ₗ[ℂ] PlaneV n)) (c : ℂ) : Prop :=
  ∀ q : PlaneQ n,
    ((n : ℂ) + 1)⁻¹ •
        (MvPolynomial.X 0 * (binaryHomogeneousRestrict n (lam radicalLatticeFirst q)).val +
          MvPolynomial.X 1 * (binaryHomogeneousRestrict n (lam radicalLatticeSecond q)).val) =
      c • q.val

namespace PlaneCupData

variable {n : ℕ} (D : PlaneCupData n)
  {Z : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n trivialCharacter)}

/-- The values of the group two-cocycle of a cocycle representing the cup product. -/
theorem group_apply (hZ : D.Represents Z) (g h : PlaneStab) :
    ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n trivialCharacter) Z (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

theorem group_radical_left_zero (hZ : D.Represents Z) (r : RadicalLattice) (h : PlaneStab) :
    ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n trivialCharacter) Z
        (identityPlaneRadicalInclusion r, h) = 0 := by
  rw [D.group_apply hZ, D.a_radical, sub_self]
  exact map_zero _

/-- The cup cocycle as a relative two-cocycle: it vanishes on pairs of radical elements. -/
theorem cup_relative (hZ : D.Represents Z) :
    ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n trivialCharacter) Z ∈
      relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) := by
  intro first second
  exact D.group_radical_left_zero hZ first (identityPlaneRadicalInclusion second)

/-- The cocycle as a relative two-cocycle for the radical lattice. -/
def planeCupRelative (hZ : D.Represents Z) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) :=
  ⟨ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n trivialCharacter) Z, D.cup_relative hZ⟩

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
    LinearMap.sub_apply, LinearMap.add_apply, linHom_radical_apply, map_sub, map_add,
    planeV_radical_restrict]
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

/-- The binary edge cocycle, pointwise, under the Kostant law. -/
theorem edgeCycle_value (hZ : D.Represents Z) {c : ℂ} (hK : KostantLaw n D.lam c)
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    (identityPlaneBinaryEdgeCycle n (D.planeCupRelative hZ) m).val =
      c • (D.a (identityPlaneLeviSection m).val - D.a 1).val := by
  rw [identityPlaneBinaryEdgeCycle_value]
  refine (congrArg₂ (fun (u v : Binary.Poly) => ((n : ℂ) + 1)⁻¹ •
      (MvPolynomial.X 0 * u + MvPolynomial.X 1 * v))
    (congrArg Subtype.val (D.edge_value hZ m radicalLatticeFirst))
    (congrArg Subtype.val (D.edge_value hZ m radicalLatticeSecond))).trans ?_
  exact hK _

end PlaneCupData

end TernaryPeriodPolynomials.SourceConstruction
