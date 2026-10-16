module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.FaceIdentification
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.FaceGeneric

@[expose] public section


/-!
# The identity-plane edge dictionary versus the Hochschild-Serre dictionary

At the identity plane `⟨e₁, e₂⟩` the literal dictionary of `Literal.OddGood` is `ξ ↦ edgeH2 (cuspRes false ξ)`, built from
the library's explicit edge `identityPlaneBinaryEdge` of relative two-cocycles of the arithmetic stabilizer
`Λ₀ = ℤ² ⋊ GL₂(ℤ)`; `Face/*` has the Hochschild-Serre isomorphism `badPlaneLocallyInnerEquiv` (mixed class
`ℓ ↦ [r ↦ c(ℓ, ℓ⁻¹·r) - c(r, ℓ)]`) onto the mixed cuspidal group. `bpPsi` is the Kostant coordinate of the radical `H¹`
(`upperRadicalH1Coordinate`) transported to `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`.

* `badPlaneParabolic_eq_hs`: for every inner plane class `ξ` (odd `n > 0`),
  `badPlaneParabolic ξ = h1EquivCrossed (bpPsi (badPlaneLocallyInnerEquiv (local class of ξ at the identity plane)))`:
  the library's edge map is the Hochschild-Serre composite, **sign `+1`**. This is a genuine comparison with the mixed class,
  not a definitional equality (`Face.badPlaneLocallyInnerEquivParabolic` is *defined* by the edge map; this theorem shows the
  edge map factors through the Hochschild-Serre isomorphism followed by the Kostant coordinate).
* `badPlaneLocallyInnerEquivParabolic_eq_hs`: equivalently the edge-defined `badPlaneLocallyInnerEquivParabolic` equals
  `h1EquivCrossed ∘ bpPsi ∘ badPlaneLocallyInnerEquiv` on the local class of every inner class.

Proof. As at the good line (`Literal.GoodLineIdentification`): a radical-zero representative `c₀` of the face class
(`FaceGeneric.exists_radicalZero_representative`) is pushed along `identityPlaneSemidirectEquiv` to a relative two-cocycle
of `Λ₀` (`pushCycle`); its class is that of the ambient cocycle (`H2π_pushCycle_eq_of_face`), the library edge of the pushed
cocycle is the Kostant coordinate of the mixed cocycle (`mixed_eq_binaryEdgeCycle`), and the mixed class is the image of the
local class under `badPlaneLocallyInnerEquiv` (`FaceGeneric.locallyInnerEquivCuspidal_coe_eq_mixed`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke (edgeH2)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (parabolicH1)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.BadPlaneId

variable (n : ℕ)

/-- The face representation of the identity plane. -/
abbrev bpRep :=
  faceRep identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag badPlaneSemidirectEquiv

theorem bpRep_symm (g : ↥(flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))) :
    bpRep n (identityPlaneSemidirectEquiv.symm g) = rationalCoefficientComponent n trivialCharacter g.val := by
  change rationalCoefficientComponent n trivialCharacter
    (identityPlaneSemidirectEquiv (identityPlaneSemidirectEquiv.symm g)).val = _
  rw [MulEquiv.apply_symm_apply]

/-- Push an inhomogeneous two-cocycle of the split extension to a two-cocycle of the arithmetic
stabilizer `Λ₀` of the identity plane. -/
def pushCycle (c : inhomogeneousTwoCycles (bpRep n)) :
    groupCohomology.cocycles₂ (identityPlaneCoefficientRep n) := by
  refine ⟨fun p => (c.val (identityPlaneSemidirectEquiv.symm p.1)
    (identityPlaneSemidirectEquiv.symm p.2) : (identityPlaneCoefficientRep n)), ?_⟩
  refine (groupCohomology.mem_cocycles₂_iff (A := identityPlaneCoefficientRep n) _).mpr ?_
  intro g h j
  have h1 := c.property (identityPlaneSemidirectEquiv.symm g) (identityPlaneSemidirectEquiv.symm h)
    (identityPlaneSemidirectEquiv.symm j)
  rw [bpRep_symm] at h1
  have h2 : c.val (identityPlaneSemidirectEquiv.symm g * identityPlaneSemidirectEquiv.symm h)
        (identityPlaneSemidirectEquiv.symm j) + c.val (identityPlaneSemidirectEquiv.symm g)
        (identityPlaneSemidirectEquiv.symm h) =
      rationalCoefficientComponent n trivialCharacter g.val
        (c.val (identityPlaneSemidirectEquiv.symm h) (identityPlaneSemidirectEquiv.symm j)) +
      c.val (identityPlaneSemidirectEquiv.symm g)
        (identityPlaneSemidirectEquiv.symm h * identityPlaneSemidirectEquiv.symm j) := by
    have h3 := sub_eq_zero.mp h1
    rw [← h3]
    abel
  simp only [map_mul]
  exact h2

theorem pushCycle_apply (c : inhomogeneousTwoCycles (bpRep n)) (g h : _) :
    pushCycle n c (g, h) = c.val (identityPlaneSemidirectEquiv.symm g)
      (identityPlaneSemidirectEquiv.symm h) := rfl

theorem iota_inl (r : RadicalLattice) :
    identityPlaneSemidirectEquiv (SemidirectProduct.inl r) = identityPlaneRadicalInclusion r := by
  change identityPlaneRadicalInclusion r * identityPlaneSplitting 1 = _
  rw [map_one, mul_one]

theorem iota_inr (l : GeneralLinearGroup (Fin 2) ℤ) :
    identityPlaneSemidirectEquiv (SemidirectProduct.inr l) = identityPlaneLeviSection l := by
  change identityPlaneRadicalInclusion 1 * identityPlaneSplitting l = _
  rw [map_one, one_mul]
  rfl

theorem iota_symm_inl (r : RadicalLattice) :
    identityPlaneSemidirectEquiv.symm (identityPlaneRadicalInclusion r) = SemidirectProduct.inl r := by
  rw [MulEquiv.symm_apply_eq]
  exact (iota_inl r).symm

theorem iota_symm_inr (l : GeneralLinearGroup (Fin 2) ℤ) :
    identityPlaneSemidirectEquiv.symm (identityPlaneLeviSection l) = SemidirectProduct.inr l := by
  rw [MulEquiv.symm_apply_eq]
  exact (iota_inr l).symm

theorem pushCycle_relative (c : radicalZeroTwoCycles identityPlaneSplitting.conjAct (bpRep n)) :
    pushCycle n c.val ∈ relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) := by
  intro r r'
  rw [pushCycle_apply, ← iota_inl, ← iota_inl, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact c.property r r'

theorem pushCycle_sub (a b : inhomogeneousTwoCycles (bpRep n)) :
    pushCycle n (a - b) = pushCycle n a - pushCycle n b := rfl

theorem pushCycle_boundary (u : _ → HomogeneousPoly n) :
    groupCohomology.H2π (identityPlaneCoefficientRep n)
      (pushCycle n (inhomogeneousBoundaryMap (bpRep n) u)) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun g => (u (identityPlaneSemidirectEquiv.symm g) : identityPlaneCoefficientRep n), ?_⟩
  funext p
  have hd := groupCohomology.d₁₂_hom_apply (identityPlaneCoefficientRep n)
    (fun g => u (identityPlaneSemidirectEquiv.symm g)) p
  rw [hd]
  change _ = (bpRep n (identityPlaneSemidirectEquiv.symm p.1) (u (identityPlaneSemidirectEquiv.symm p.2)) -
    u (identityPlaneSemidirectEquiv.symm p.1 * identityPlaneSemidirectEquiv.symm p.2) +
    u (identityPlaneSemidirectEquiv.symm p.1))
  rw [bpRep_symm, map_mul]
  rfl

theorem pushCycle_faceCycle
    (C : cocycles (fixedPointLevel rationalLevel badPlaneFlag)
      (rationalCoefficientComponent n trivialCharacter)) :
    pushCycle n (faceCycle identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
      badPlaneSemidirectEquiv C) =
      ambientCocycleToGroup (fixedPointLevel rationalLevel badPlaneFlag)
        (rationalCoefficientComponent n trivialCharacter) C := by
  apply Subtype.ext
  funext p
  change (faceCycle identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
      badPlaneSemidirectEquiv C).val (identityPlaneSemidirectEquiv.symm p.1)
      (identityPlaneSemidirectEquiv.symm p.2) = _
  rw [faceCycle_apply]
  change C.val.val ![1, (identityPlaneSemidirectEquiv (identityPlaneSemidirectEquiv.symm p.1)).val,
    (identityPlaneSemidirectEquiv (identityPlaneSemidirectEquiv.symm p.1)).val *
      (identityPlaneSemidirectEquiv (identityPlaneSemidirectEquiv.symm p.2)).val] = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl


/-! ### The Kostant coordinate on the face presentation (identity plane) -/

/-- The radical representation of the identity plane, on the face presentation. -/
abbrev bpRad (n : ℕ) :=
  (faceRep identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
    badPlaneSemidirectEquiv).comp SemidirectProduct.inl

/-- The Levi action on the identity-plane radical cohomology. -/
abbrev bpAction (n : ℕ) : Representation ℂ (GeneralLinearGroup (Fin 2) ℤ) (CrossedH1 (bpRad n)) :=
  leviCrossedH1Representation identityPlaneSplitting.conjAct
    (faceRep identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag badPlaneSemidirectEquiv)

theorem faceRep_badPlane_radical (n : ℕ) : bpRad n = (upperRadicalLatticeRep n).ρ := by
  apply MonoidHom.ext
  intro r
  change rationalCoefficientComponent n trivialCharacter
    (badPlaneSemidirectEquiv (SemidirectProduct.inl r)).val =
    rationalCoefficientComponent n trivialCharacter (upperRadicalLattice r)
  rw [badPlaneSemidirectEquiv_inl]
  rfl

theorem faceRep_badPlane_levi (n : ℕ) (l : GeneralLinearGroup (Fin 2) ℤ) :
    faceRep identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag badPlaneSemidirectEquiv
        (SemidirectProduct.inr l) =
      (identityPlaneCoefficientRep n).ρ (identityPlaneSplitting l) := by
  change rationalCoefficientComponent n trivialCharacter
    (badPlaneSemidirectEquiv (SemidirectProduct.inr l)).val = _
  have : (badPlaneSemidirectEquiv (SemidirectProduct.inr l)).val = arithmeticLevi l := by
    change (identityPlaneRadicalInclusion 1 * identityPlaneSplitting l).val = _
    rw [map_one, one_mul]
    rfl
  rw [this]
  rfl

/-- Crossed `H¹` of the radical versus Mathlib `H¹` of the lattice representation. -/
def bpToH1 (n : ℕ) : CrossedH1 (bpRad n) ≃ₗ[ℂ] groupCohomology.H1 (upperRadicalLatticeRep n) :=
  (crossedH1RepresentationEqEquiv _ _ (faceRep_badPlane_radical n)).trans
    (h1EquivCrossed (upperRadicalLatticeRep n))

theorem bpAction_cocycle (n : ℕ) (l : GeneralLinearGroup (Fin 2) ℤ)
    (φ : crossedCocycles (bpRad n)) :
    cocycleOfCrossed (upperRadicalLatticeRep n)
        (crossedRepresentationEqEquiv _ _ (faceRep_badPlane_radical n)
          (leviCrossedAction identityPlaneSplitting.conjAct
            (faceRep identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
              badPlaneSemidirectEquiv) l φ)) =
      splitRadicalCocycleAction identityPlaneSplitting (identityPlaneCoefficientRep n) l
        (cocycleOfCrossed (upperRadicalLatticeRep n)
          (crossedRepresentationEqEquiv _ _ (faceRep_badPlane_radical n) φ)) := by
  apply Subtype.ext
  funext r
  change (faceRep identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
      badPlaneSemidirectEquiv (SemidirectProduct.inr l)) (φ.val (identityPlaneSplitting.conjAct l⁻¹ r)) =
    (identityPlaneCoefficientRep n).ρ (identityPlaneSplitting l)
      (φ.val (identityPlaneSplitting.conjAct l⁻¹ r))
  rw [faceRep_badPlane_levi]
  rfl

theorem bpToH1_equivariant (n : ℕ) (l : GeneralLinearGroup (Fin 2) ℤ) (c : CrossedH1 (bpRad n)) :
    bpToH1 n (bpAction n l c) = upperRadicalH1Levi n l (bpToH1 n c) := by
  obtain ⟨φ, rfl⟩ := (crossedBoundaries (bpRad n)).mkQ_surjective c
  have h2 : bpAction n l ((crossedBoundaries (bpRad n)).mkQ φ) =
      (crossedBoundaries (bpRad n)).mkQ (leviCrossedAction identityPlaneSplitting.conjAct
        (faceRep identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
          badPlaneSemidirectEquiv) l φ) := leviCrossedH1Representation_mk _ _ l φ
  have h3 : ∀ ψ, bpToH1 n ((crossedBoundaries (bpRad n)).mkQ ψ) =
      groupCohomology.H1π (upperRadicalLatticeRep n)
        (cocycleOfCrossed (upperRadicalLatticeRep n)
          (crossedRepresentationEqEquiv _ _ (faceRep_badPlane_radical n) ψ)) := fun ψ => rfl
  refine ((congrArg (bpToH1 n) h2).trans (h3 _)).trans ?_
  refine (congrArg (groupCohomology.H1π (upperRadicalLatticeRep n)) (bpAction_cocycle n l φ)).trans ?_
  refine (splitRadicalH1Action_apply identityPlaneSplitting (identityPlaneCoefficientRep n) l _).symm.trans ?_
  rw [identityPlaneSplitH1Action]
  rfl

/-- Kostant isomorphism `H¹(N, Sym^n) ≅ Sym^{n+1}` for the identity plane. -/
def bpTheta (n : ℕ) : CrossedH1 (bpRad n) ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (bpToH1 n).trans (upperRadicalH1Coordinate n)

theorem bpTheta_equivariant (n : ℕ) (l : GeneralLinearGroup (Fin 2) ℤ) (c : CrossedH1 (bpRad n)) :
    bpTheta n (bpAction n l c) = (arithmeticBinaryRep (n + 1) (-1)).ρ l (bpTheta n c) := by
  change upperRadicalH1Coordinate n (bpToH1 n (bpAction n l c)) = _
  rw [bpToH1_equivariant, upperRadicalH1Coordinate_equivariant]
  rfl

theorem bpTransport_eq (n : ℕ) :
    coefficientTransportRepresentation (bpAction n) (bpTheta n) =
      (arithmeticBinaryRep (n + 1) (-1)).ρ := by
  apply MonoidHom.ext
  intro l
  apply LinearMap.ext
  intro v
  rw [coefficientTransportRepresentation_apply, bpTheta_equivariant, LinearEquiv.apply_symm_apply]
  rfl

/-- Change of coefficients `H¹(L, H¹(N, E)) ≅ H¹(L, Sym^{n+1} ⊗ det⁻¹)` for the identity plane. -/
def bpPsi (n : ℕ) : CrossedH1 (bpAction n) ≃ₗ[ℂ] CrossedH1 (arithmeticBinaryRep (n + 1) (-1)).ρ :=
  (crossedH1CoefficientEquiv (bpAction n) (bpTheta n)).trans
    (crossedH1RepresentationEqEquiv _ _ (bpTransport_eq n))

theorem bpPsi_mk (n : ℕ) (x : crossedCocycles (bpAction n)) :
    ∃ y : crossedCocycles (arithmeticBinaryRep (n + 1) (-1)).ρ,
      (∀ l, y.val l = bpTheta n (x.val l)) ∧
        bpPsi n ((crossedBoundaries (bpAction n)).mkQ x) =
          (crossedBoundaries (arithmeticBinaryRep (n + 1) (-1)).ρ).mkQ y :=
  ⟨crossedRepresentationEqEquiv _ _ (bpTransport_eq n)
    (crossedCoefficientEquiv (bpAction n) (bpTheta n) x), fun _ => rfl, rfl⟩

variable {n}

/-! ### The comparison -/

theorem mixed_eq_binaryEdgeCycle
    (c : radicalZeroTwoCycles identityPlaneSplitting.conjAct (bpRep n))
    (l : GeneralLinearGroup (Fin 2) ℤ) :
    bpTheta n ((mixedH1CocycleMap identityPlaneSplitting.conjAct (bpRep n) c).val l) =
      identityPlaneBinaryEdgeCycle n ⟨pushCycle n c.val, pushCycle_relative n c⟩ l := by
  rw [identityPlaneBinaryEdgeCycle_apply]
  have e1 : bpTheta n ((mixedH1CocycleMap identityPlaneSplitting.conjAct (bpRep n) c).val l) =
      upperRadicalH1Coordinate n (groupCohomology.H1π (upperRadicalLatticeRep n)
        (cocycleOfCrossed (upperRadicalLatticeRep n)
          (crossedRepresentationEqEquiv _ _ (faceRep_badPlane_radical n)
            (mixedCrossedMap identityPlaneSplitting.conjAct (bpRep n) l c)))) := rfl
  rw [e1, upperRadicalH1Coordinate_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro r
  change mixedCrossedCochain identityPlaneSplitting.conjAct (bpRep n) c l r =
    identityPlaneRadicalEdgeCycle n ⟨pushCycle n c.val, pushCycle_relative n c⟩ l r
  rw [identityPlaneSplitEdgeCycle_apply]
  dsimp only [mixedCrossedCochain]
  rw [pushCycle_apply, pushCycle_apply, iota_symm_inr, iota_symm_inl, iota_symm_inl,
    identityPlaneSplitting_inverse_action]
  rfl

theorem H2π_pushCycle_eq_of_face (z : H2 (fixedPointLevel rationalLevel badPlaneFlag) (ρn n))
    (c : radicalZeroTwoCycles identityPlaneSplitting.conjAct (bpRep n))
    (h : (inhomogeneousBoundaries (bpRep n)).mkQ c.val =
      faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
        badPlaneSemidirectEquiv z) :
    ∃ C : cocycles (fixedPointLevel rationalLevel badPlaneFlag) (ρn n),
      classOf (fixedPointLevel rationalLevel badPlaneFlag) (ρn n) C = z ∧
      groupCohomology.H2π (identityPlaneCoefficientRep n) (pushCycle n c.val) =
        groupCohomology.H2π (identityPlaneCoefficientRep n)
          (ambientCocycleToGroup (fixedPointLevel rationalLevel badPlaneFlag) (ρn n) C) := by
  induction z using Submodule.Quotient.induction_on with
  | _ C =>
  refine ⟨C, rfl, ?_⟩
  have h' := h.trans (faceH2Equiv_classOf identityPlaneSplitting.conjAct n trivialCharacter
    badPlaneFlag badPlaneSemidirectEquiv C)
  obtain ⟨u, hu⟩ := (Submodule.Quotient.eq (inhomogeneousBoundaries (bpRep n))).mp h'
  have e2 : c.val = faceCycle identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
      badPlaneSemidirectEquiv C + (c.val - faceCycle identityPlaneSplitting.conjAct n trivialCharacter
        badPlaneFlag badPlaneSemidirectEquiv C) := by abel
  have e3 : pushCycle n c.val = pushCycle n (faceCycle identityPlaneSplitting.conjAct n trivialCharacter
      badPlaneFlag badPlaneSemidirectEquiv C) + pushCycle n (c.val - faceCycle
        identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag badPlaneSemidirectEquiv C) := by
    conv_lhs => rw [e2]
    rfl
  rw [e3, map_add, ← hu, pushCycle_boundary, add_zero, pushCycle_faceCycle]

theorem hs_class_eq_mixed (x : H2 (fixedPointLevel rationalLevel badPlaneFlag)
      (rationalCoefficientComponent n trivialCharacter))
    (hxli : x ∈ locallyInnerClasses n trivialCharacter .plane badPlaneFlag)
    (c₀ : radicalZeroTwoCycles identityPlaneSplitting.conjAct (bpRep n))
    (hc₀ : (inhomogeneousBoundaries (bpRep n)).mkQ c₀.val =
      faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
        badPlaneSemidirectEquiv x) :
    ((badPlaneLocallyInnerEquiv n trivialCharacter ⟨x, hxli⟩ :
        FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
          badPlaneSemidirectEquiv) : CrossedH1 (bpAction n)) =
      (crossedBoundaries (bpAction n)).mkQ
        (mixedH1CocycleMap identityPlaneSplitting.conjAct (bpRep n) c₀) :=
  FaceGeneric.locallyInnerEquivCuspidal_coe_eq_mixed identityPlaneSplitting.conjAct n trivialCharacter
    badPlaneFlag badPlaneSemidirectEquiv
    (leviH2Vanishes_of_binary badPlaneLeviEmbedding badPlaneLeviEmbedding_injective)
    (fun radical e he => badPlane_radical_fixes radical e he) badPlaneLeviEmbedding
    badPlaneLeviEmbedding_injective x hxli c₀ hc₀

/-- The Kostant coordinate of the mixed class of a radical-zero cycle is the class of the library's edge cocycle
of the pushed relative cocycle. -/
theorem hs_coordinate_eq_edgeCycle (c₀ : radicalZeroTwoCycles identityPlaneSplitting.conjAct (bpRep n)) :
    h1EquivCrossed (arithmeticBinaryRep (n + 1) (-1))
        (bpPsi n ((crossedBoundaries (bpAction n)).mkQ
          (mixedH1CocycleMap identityPlaneSplitting.conjAct (bpRep n) c₀))) =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
        (identityPlaneBinaryEdgeCycle n ⟨pushCycle n c₀.val, pushCycle_relative n c₀⟩) := by
  obtain ⟨y, hy1, hy2⟩ := bpPsi_mk n (mixedH1CocycleMap identityPlaneSplitting.conjAct (bpRep n) c₀)
  rw [hy2, h1EquivCrossed_mk]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro l
  change y.val l = _
  rw [hy1 l]
  exact mixed_eq_binaryEdgeCycle c₀ l

/-- The library's edge map on a class represented by a radical-zero face cycle. -/
theorem edgeH2_eq_edgeCycle (hn : 0 < n) (hodd : Odd n)
    (z : H2 (fixedPointLevel rationalLevel badPlaneFlag) (ρn n))
    (c₀ : radicalZeroTwoCycles identityPlaneSplitting.conjAct (bpRep n))
    (hc₀ : (inhomogeneousBoundaries (bpRep n)).mkQ c₀.val =
      faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
        badPlaneSemidirectEquiv z) :
    edgeH2 n hn hodd z = groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
      (identityPlaneBinaryEdgeCycle n ⟨pushCycle n c₀.val, pushCycle_relative n c₀⟩) := by
  rw [← identityPlaneFullBinaryEdge_relative n hn hodd ⟨pushCycle n c₀.val, pushCycle_relative n c₀⟩]
  obtain ⟨C, hC, hH2⟩ := H2π_pushCycle_eq_of_face z c₀ hc₀
  change _ = identityPlaneFullBinaryEdge n hn hodd (groupCohomology.H2π (identityPlaneCoefficientRep n)
    (pushCycle n c₀.val))
  rw [hH2, ← hC]
  exact (TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke.edgeH2_classOf n hn hodd
    C).trans (identityPlaneAmbientBinaryEdge_apply n hn hodd C)

theorem repExists (x : H2 (fixedPointLevel rationalLevel badPlaneFlag)
      (rationalCoefficientComponent n trivialCharacter))
    (hxli : x ∈ locallyInnerClasses n trivialCharacter .plane badPlaneFlag) :
    ∃ c₀ : radicalZeroTwoCycles identityPlaneSplitting.conjAct (bpRep n),
      (inhomogeneousBoundaries (bpRep n)).mkQ c₀.val =
        faceH2Equiv identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
          badPlaneSemidirectEquiv x :=
  FaceGeneric.exists_radicalZero_representative identityPlaneSplitting.conjAct n
    trivialCharacter badPlaneFlag badPlaneSemidirectEquiv
    (fun radical e he => badPlane_radical_fixes radical e he) badPlaneLeviEmbedding
    badPlaneLeviEmbedding_injective x hxli

/-- **Identity plane: the library's explicit edge dictionary is the Hochschild-Serre dictionary.**
For an inner plane class `ξ` and odd `n > 0`, `badPlaneParabolic ξ = edgeH2 (cuspRes false ξ)` is (with sign `+1`)
the image of the local class of `ξ` at the identity plane under the Hochschild-Serre isomorphism
`Face.badPlaneLocallyInnerEquiv` followed by the Kostant coordinate `bpPsi`. -/
theorem badPlaneParabolic_eq_hs (hn : 0 < n) (hodd : Odd n) (ξ : innerClasses n .plane) :
    ((badPlaneParabolic hn hodd ξ : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) :
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) =
      h1EquivCrossed (arithmeticBinaryRep (n + 1) (-1))
        (bpPsi n ((badPlaneLocallyInnerEquiv n trivialCharacter
          ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
              badPlaneFlag ξ.val,
            innerBoundary_fixedPointH2_locallyInner ξ.property badPlaneFlag⟩ :
            FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
              badPlaneSemidirectEquiv) : CrossedH1 (bpAction n))) := by
  have hxli : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      badPlaneFlag ξ.val ∈ locallyInnerClasses n trivialCharacter .plane badPlaneFlag :=
    innerBoundary_fixedPointH2_locallyInner ξ.property badPlaneFlag
  have hrep := repExists _ hxli
  rcases hrep with ⟨c₀, hc₀⟩
  have e1 := hs_class_eq_mixed _ hxli c₀ hc₀
  have e2 := hs_coordinate_eq_edgeCycle c₀
  have e3 := edgeH2_eq_edgeCycle hn hodd _ c₀ hc₀
  exact e3.trans (e2.symm.trans (congrArg (fun m => h1EquivCrossed (arithmeticBinaryRep (n + 1) (-1))
    (bpPsi n m)) e1.symm))

/-- The Hochschild-Serre composite carries the edge-defined identification onto itself: the edge-defined
`badPlaneLocallyInnerEquivParabolic` and the Hochschild-Serre composite agree on the local class of every inner
class. -/
theorem badPlaneLocallyInnerEquivParabolic_eq_hs (hn : 0 < n) (hodd : Odd n) (ξ : innerClasses n .plane) :
    ((badPlaneLocallyInnerEquivParabolic n hn hodd
        ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) badPlaneFlag ξ.val,
          innerBoundary_fixedPointH2_locallyInner ξ.property badPlaneFlag⟩ :
        parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) =
      h1EquivCrossed (arithmeticBinaryRep (n + 1) (-1))
        (bpPsi n ((badPlaneLocallyInnerEquiv n trivialCharacter
          ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
              badPlaneFlag ξ.val,
            innerBoundary_fixedPointH2_locallyInner ξ.property badPlaneFlag⟩ :
            FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
              badPlaneSemidirectEquiv) : CrossedH1 (bpAction n))) :=
  badPlaneParabolic_eq_hs hn hodd ξ

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.BadPlaneId
