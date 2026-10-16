module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.MixedSubgroup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.SubgroupVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerMixed
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalReconstruction

@[expose] public section


/-!
# Locally inner classes at a face with a split stabilizer are the mixed cuspidal classes

Generic form of `StandardBadLineMixedCuspidal` for an arbitrary flag `F` whose stabilizer in the
arithmetic level is presented as a split extension `Radical ⋊ Levi` (`ι`). For a class
`c ∈ H²(Γ_F, E)` the paper's mixed cuspidal condition (end of Appendix C.4,
Hochschild-Serre) is: `c` has zero restriction to the radical, so that it has a mixed class
`m(c) ∈ H¹(Levi, H¹(Radical, E))`, and `m(c)` restricts to zero on the Levi part `B_e` of the
stabilizer of every complete flag `e` over `F` (the cusp subgroups). `face_locallyInner_iff`
proves that this is equivalent to `c` restricting to zero on the stabilizer of every complete
flag over `F` (`locallyInnerClasses`, the local form of `InnerBoundary`), provided each `B_e`
satisfies `H²(B_e, E^N) = 0` (`EdgeData`).

The forward direction generalizes `locallyInner_mixed_restriction_zero` of the library; the
converse is `MixedSubgroup.exists_primitive_of_pullback_mixed_zero` together with
`SubgroupVanishing.subgroupRestrictionH2_classOf_eq_zero`.

Formalized by Claude Sonnet 5.5 (Sol).
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- The coefficient representation restricted to the stabilizer and transported to the split
extension. -/
def faceRep : Representation ℂ (SemidirectProduct Radical Levi action) (HomogeneousPoly degree) :=
  ((rationalCoefficientComponent degree character).comp
    (fixedPointLevel rationalLevel F).subtype).comp ι.toMonoidHom

/-- The ambient matrix of an element of the split extension. -/
def faceAmbient : SemidirectProduct Radical Levi action →* RationalGL3 :=
  (fixedPointLevel rationalLevel F).subtype.comp ι.toMonoidHom

/-- The elements of the split extension stabilizing the complete flag `e`. -/
def faceEdgeSubgroup (e : Edges) : Subgroup (SemidirectProduct Radical Levi action) :=
  (fixedPointLevel rationalLevel e).comap (faceAmbient action F ι)

/-- Homogeneous to inhomogeneous cohomology of the stabilizer. -/
def faceH2Equiv :
    H2 (fixedPointLevel rationalLevel F) (rationalCoefficientComponent degree character) ≃ₗ[ℂ]
      InhomogeneousH2 (faceRep action degree character F ι) :=
  ((ambientResolutionH2Equiv (fixedPointLevel rationalLevel F)
    (rationalCoefficientComponent degree character)).trans
      (fullGroupEquivH2 ι ((rationalCoefficientComponent degree character).comp
        (fixedPointLevel rationalLevel F).subtype))).trans
    (fullInhomogeneousH2Equiv _)

/-- The inhomogeneous two-cycle of a homogeneous one. -/
def faceCycle
    (cycle : cocycles (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    inhomogeneousTwoCycles (faceRep action degree character F ι) :=
  fullInhomogeneousCycleEquiv _ (fullCycleEquiv ι _ (ambientRestrictionCycles _ _ cycle))

theorem faceH2Equiv_classOf
    (cycle : cocycles (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    faceH2Equiv action degree character F ι
        (classOf (fixedPointLevel rationalLevel F)
          (rationalCoefficientComponent degree character) cycle) =
      (inhomogeneousBoundaries (faceRep action degree character F ι)).mkQ
        (faceCycle action degree character F ι cycle) := rfl

theorem faceCycle_apply
    (cycle : cocycles (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character))
    (first second : SemidirectProduct Radical Levi action) :
    (faceCycle action degree character F ι cycle).val first second =
      cycle.val.val ![1, (ι first).val, (ι first).val * (ι second).val] := by
  change cycle.val.val (fun index => (ι (![1, first, first * second] index)).val) = _
  rw [ambientMapVectorThree (fun element : SemidirectProduct Radical Levi action =>
    (ι element).val), map_one, map_mul]
  rfl

def faceCochainPrimitive (edge : Edges)
    (primitive : cochains (fixedPointLevel rationalLevel edge)
      (rationalCoefficientComponent degree character) 1) :
    SemidirectProduct Radical Levi action → HomogeneousPoly degree :=
  fun element => primitive.val ![1, faceAmbient action F ι element]

theorem faceCochainPrimitive_boundary (edge : Edges)
    (primitive : cochains (fixedPointLevel rationalLevel edge)
      (rationalCoefficientComponent degree character) 1)
    (first second : SemidirectProduct Radical Levi action) (firstMem : first ∈ faceEdgeSubgroup action F ι edge) :
    (inhomogeneousBoundaryMap (faceRep action degree character F ι)
      (faceCochainPrimitive action degree character F ι edge primitive)).val first second =
      (boundaryMap (fixedPointLevel rationalLevel edge)
        (rationalCoefficientComponent degree character) primitive).val.val
        ![1, faceAmbient action F ι first,
          faceAmbient action F ι first * faceAmbient action F ι second] := by
  have equivariance := primitive.property ⟨faceAmbient action F ι first, firstMem⟩
    ![1, faceAmbient action F ι second]
  rw [ambientMapVectorTwo, mul_one] at equivariance
  change rationalCoefficientComponent degree character (faceAmbient action F ι first)
      (primitive.val ![1, faceAmbient action F ι second]) -
    primitive.val ![1, faceAmbient action F ι (first * second)] +
    primitive.val ![1, faceAmbient action F ι first] =
      primitive.val ![faceAmbient action F ι first,
        faceAmbient action F ι first * faceAmbient action F ι second] -
      primitive.val ![1, faceAmbient action F ι first * faceAmbient action F ι second] +
      primitive.val ![1, faceAmbient action F ι first]
  rw [equivariance, map_mul]


theorem face_cycle_boundary_on_edge (edge : Edges)
    (endpointEq : endpoint side edge = F)
    (coordinate : locallyInnerClasses degree character side F)
    (cycle : inhomogeneousTwoCycles (faceRep action degree character F ι))
    (represents : (inhomogeneousBoundaries (faceRep action degree character F ι)).mkQ cycle =
      faceH2Equiv action degree character F ι coordinate.val) :
    ∃ primitive : SemidirectProduct Radical Levi action → HomogeneousPoly degree,
      ∀ first ∈ faceEdgeSubgroup action F ι edge, ∀ second ∈ faceEdgeSubgroup action F ι edge,
        (inhomogeneousBoundaryMap (faceRep action degree character F ι) primitive).val first second =
          cycle.val first second := by
  obtain ⟨original, originalClass⟩ :=
    (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character))).mkQ_surjective coordinate.val
  have innerOriginal : classOf (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character) original ∈
      locallyInnerClasses degree character side F :=
    originalClass.symm ▸ coordinate.property
  have edgeZero := (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) _).mp innerOriginal ⟨edge, endpointEq⟩
  change classOf (fixedPointLevel rationalLevel edge)
    (rationalCoefficientComponent degree character)
    (subgroupRestrictionCycle
      (fixedPointLevel_edge_le_flag side edge F endpointEq)
      (rationalCoefficientComponent degree character) original) = 0 at edgeZero
  obtain ⟨edgePrimitive, edgeBoundary⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel edge)
      (rationalCoefficientComponent degree character)))).mp edgeZero
  have baseRepresents := faceH2Equiv_classOf action degree character F ι original
  change faceH2Equiv action degree character F ι
    ((LinearMap.range (boundaryMap (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character))).mkQ original) = _ at baseRepresents
  rw [originalClass] at baseRepresents
  have sameClass := represents.trans baseRepresents
  obtain ⟨correction, correctionBoundary⟩ := (Submodule.Quotient.eq
    (inhomogeneousBoundaries (faceRep action degree character F ι))).mp sameClass
  let base := faceCochainPrimitive action degree character F ι edge edgePrimitive
  have baseBoundary : ∀ first ∈ faceEdgeSubgroup action F ι edge, ∀ second,
      (inhomogeneousBoundaryMap (faceRep action degree character F ι) base).val first second =
        (faceCycle action degree character F ι original).val first second := by
    intro first firstMem second
    rw [faceCochainPrimitive_boundary action degree character F ι edge edgePrimitive first second firstMem,
      edgeBoundary, faceCycle_apply action degree character F ι]
    rfl
  refine ⟨base + correction, ?_⟩
  intro first firstMem second _secondMem
  rw [map_add]
  change (inhomogeneousBoundaryMap (faceRep action degree character F ι) base).val first second +
    (inhomogeneousBoundaryMap (faceRep action degree character F ι) correction).val first second = _
  rw [baseBoundary first firstMem second, correctionBoundary]
  change (faceCycle action degree character F ι original).val first second +
    (cycle.val first second - (faceCycle action degree character F ι original).val first second) = _
  rw [← add_sub_assoc, add_sub_cancel_left]


theorem face_radical_zero (e₀ : Edges) (he₀ : endpoint side e₀ = F)
    (hrad : ∀ radical : Radical,
      (ι (SemidirectProduct.inl radical)).val ∈ fixedPointLevel rationalLevel e₀)
    (coordinate : H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character side F →
      faceH2Equiv action degree character F ι coordinate ∈
        (radicalRestrictionH2 action (faceRep action degree character F ι)).ker := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle inner
  have edgeZero := (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) _).mp inner
        ⟨e₀, he₀⟩
  change classOf (fixedPointLevel rationalLevel e₀)
    (rationalCoefficientComponent degree character)
    (subgroupRestrictionCycle
      (fixedPointLevel_edge_le_flag side e₀ F he₀)
      (rationalCoefficientComponent degree character) cycle) = 0 at edgeZero
  obtain ⟨primitive, primitiveBoundary⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel e₀)
      (rationalCoefficientComponent degree character)))).mp edgeZero
  change radicalRestrictionH2 action
    (faceRep action degree character F ι)
    (faceH2Equiv action degree character F ι
      (classOf (fixedPointLevel rationalLevel F)
        (rationalCoefficientComponent degree character) cycle)) = 0
  rw [faceH2Equiv_classOf action degree character F ι]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨fun radical => primitive.val
    ![1, (ι (SemidirectProduct.inl radical)).val], ?_⟩
  apply Subtype.ext
  funext first second
  have boundary := congrArg
    (fun cycle : cocycles (fixedPointLevel rationalLevel e₀)
      (rationalCoefficientComponent degree character) =>
      cycle.val.val ![1, (ι (SemidirectProduct.inl first)).val,
        (ι (SemidirectProduct.inl first)).val *
          (ι (SemidirectProduct.inl second)).val]) primitiveBoundary
  have equivariance := primitive.property
    ⟨(ι (SemidirectProduct.inl first)).val,
      hrad first⟩
    ![1, (ι (SemidirectProduct.inl second)).val]
  rw [ambientMapVectorTwo, mul_one] at equivariance
  change primitive.val
      ![(ι (SemidirectProduct.inl first)).val,
        (ι (SemidirectProduct.inl first)).val *
          (ι (SemidirectProduct.inl second)).val] -
    primitive.val ![1, (ι (SemidirectProduct.inl first)).val *
      (ι (SemidirectProduct.inl second)).val] +
    primitive.val ![1, (ι (SemidirectProduct.inl first)).val] = _ at boundary
  rw [equivariance] at boundary
  change _ = (faceCycle action degree character F ι cycle).val
    (SemidirectProduct.inl first) (SemidirectProduct.inl second)
  rw [faceCycle_apply action degree character F ι]
  change rationalCoefficientComponent degree character
      (ι (SemidirectProduct.inl first)).val
        (primitive.val ![1, (ι (SemidirectProduct.inl second)).val]) -
    primitive.val ![1, (ι (SemidirectProduct.inl (first * second))).val] +
    primitive.val ![1, (ι (SemidirectProduct.inl first)).val] = _
  simpa only [map_mul, Subgroup.coe_mul, subgroupRestrictionCycle,
    subgroupRestrictionCochain, LinearMap.coe_mk, AddHom.coe_mk] using boundary


theorem mixedEq_of_class
    (coordinate : H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character))
    (radicalZero : faceH2Equiv action degree character F ι coordinate ∈
        (radicalRestrictionH2 action (faceRep action degree character F ι)).ker)
    (cycle : radicalZeroTwoCycles action (faceRep action degree character F ι))
    (cycleClass : (inhomogeneousBoundaries (faceRep action degree character F ι)).mkQ cycle.val =
      faceH2Equiv action degree character F ι coordinate) :
    radicalKernelMixedMap action (faceRep action degree character F ι)
        ⟨faceH2Equiv action degree character F ι coordinate, radicalZero⟩ =
      mixedClassMap action (faceRep action degree character F ι) cycle := by
  have same : (⟨faceH2Equiv action degree character F ι coordinate, radicalZero⟩ :
      (radicalRestrictionH2 action (faceRep action degree character F ι)).ker) =
      radicalZeroH2ToKernel action (faceRep action degree character F ι)
        ((radicalZeroBoundaries action (faceRep action degree character F ι)).mkQ cycle) :=
    Subtype.ext cycleClass.symm
  have step := radicalKernelMixedMap_representative action (faceRep action degree character F ι)
    cycle
  have unfoldRight : mixedClassMap action (faceRep action degree character F ι) cycle =
      (crossedBoundaries (leviCrossedH1Representation action
        (faceRep action degree character F ι))).mkQ
        (mixedH1CocycleMap action (faceRep action degree character F ι) cycle) :=
    LinearMap.comp_apply _ _ _
  exact (congrArg (radicalKernelMixedMap action (faceRep action degree character F ι)) same).trans
    (step.trans unfoldRight.symm)

theorem face_mixed_zero {Smaller : Type} [Group Smaller] (e : Edges) (he : endpoint side e = F)
    (φ : Smaller →* Levi)
    (radicalMem : ∀ radical, SemidirectProduct.inl radical ∈ faceEdgeSubgroup action F ι e)
    (leviMem : ∀ element, SemidirectProduct.inr (φ element) ∈ faceEdgeSubgroup action F ι e)
    (coordinate : H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character))
    (inner : coordinate ∈ locallyInnerClasses degree character side F) :
    ∃ radicalZero : faceH2Equiv action degree character F ι coordinate ∈
        (radicalRestrictionH2 action (faceRep action degree character F ι)).ker,
      crossedPullbackH1 φ (leviCrossedH1Representation action (faceRep action degree character F ι))
        (radicalKernelMixedMap action (faceRep action degree character F ι)
          ⟨faceH2Equiv action degree character F ι coordinate, radicalZero⟩) = 0 := by
  have radicalZero := face_radical_zero action degree character F ι e he radicalMem coordinate inner
  refine ⟨radicalZero, ?_⟩
  have representative := radicalRestrictionH2_ker_representative
    action (faceRep action degree character F ι)
    (faceH2Equiv action degree character F ι coordinate) radicalZero
  obtain ⟨cycle, cycleClass⟩ := representative
  have mixedEq := mixedEq_of_class action degree character F ι coordinate radicalZero cycle
    cycleClass
  refine (congrArg (crossedPullbackH1 φ (leviCrossedH1Representation action
    (faceRep action degree character F ι))) mixedEq).trans ?_
  have edgeBoundary := face_cycle_boundary_on_edge action degree character F ι e he
    ⟨coordinate, inner⟩ cycle.val cycleClass
  obtain ⟨primitive, boundary⟩ := edgeBoundary
  exact mixedRestriction_zero_of_subgroup_boundary action (faceRep action degree character F ι) φ
    cycle (faceEdgeSubgroup action F ι e) radicalMem leviMem primitive boundary


/-- The Levi data of the stabilizer of a complete flag over `F`: the Levi part `B` of its
stabilizer, for which `H²(B, E^N)` vanishes. -/
def EdgeData (e : Edges) : Prop :=
  ∃ B : Subgroup Levi, (∀ x, x ∈ faceEdgeSubgroup action F ι e ↔ x.right ∈ B) ∧
    ∀ x : InhomogeneousH2 (semidirectInvariantRepresentation (subAction action B)
      (subRepresentation action (faceRep action degree character F ι) B)), x = 0

/-- **Converse (mixed cuspidal implies locally inner).** -/
theorem face_locallyInner_of_mixed
    (hedge : ∀ e : Edges, endpoint side e = F → EdgeData action degree character F ι e)
    (coordinate : H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character))
    (radicalZero : faceH2Equiv action degree character F ι coordinate ∈
        (radicalRestrictionH2 action (faceRep action degree character F ι)).ker)
    (hmix : ∀ e : Edges, endpoint side e = F → ∀ B : Subgroup Levi,
      (∀ x, x ∈ faceEdgeSubgroup action F ι e ↔ x.right ∈ B) →
      crossedPullbackH1 B.subtype
        (leviCrossedH1Representation action (faceRep action degree character F ι))
        (radicalKernelMixedMap action (faceRep action degree character F ι)
          ⟨faceH2Equiv action degree character F ι coordinate, radicalZero⟩) = 0) :
    coordinate ∈ locallyInnerClasses degree character side F := by
  apply (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) _).mpr
  rintro ⟨edge, endpointEq⟩
  have edgeData := hedge edge endpointEq
  obtain ⟨B, hB, hvan⟩ := edgeData
  have originalExists := (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character))).mkQ_surjective coordinate
  obtain ⟨original, originalClass⟩ := originalExists
  have representative := radicalRestrictionH2_ker_representative
    action (faceRep action degree character F ι)
    (faceH2Equiv action degree character F ι coordinate) radicalZero
  obtain ⟨cycle, cycleClass⟩ := representative
  have mixedEq := mixedEq_of_class action degree character F ι coordinate radicalZero cycle
    cycleClass
  have zero : crossedPullbackH1 B.subtype
      (leviCrossedH1Representation action (faceRep action degree character F ι))
      (mixedClassMap action (faceRep action degree character F ι) cycle) = 0 := by
    exact (congrArg (crossedPullbackH1 B.subtype (leviCrossedH1Representation action
      (faceRep action degree character F ι))) mixedEq).symm.trans (hmix edge endpointEq B hB)
  have primitiveExists := exists_primitive_of_pullback_mixed_zero_of_vanishing action
      (faceRep action degree character F ι) B hvan cycle zero
  obtain ⟨primitive, primitiveBoundary⟩ := primitiveExists
  have sameClass : (inhomogeneousBoundaries (faceRep action degree character F ι)).mkQ cycle.val =
      (inhomogeneousBoundaries (faceRep action degree character F ι)).mkQ
        (faceCycle action degree character F ι original) := by
    rw [cycleClass, ← faceH2Equiv_classOf]
    exact congrArg _ originalClass.symm
  obtain ⟨correction, correctionBoundary⟩ :=
    (Submodule.Quotient.eq (inhomogeneousBoundaries (faceRep action degree character F ι))).mp
      sameClass
  rw [LinearMap.mem_ker]
  have hle := fixedPointLevel_edge_le_flag side edge F endpointEq
  rw [← originalClass]
  refine subgroupRestrictionH2_classOf_eq_zero hle _ original
    (fun a => (primitive - correction) (ι.symm ⟨a.val, hle a.property⟩)) ?_
  intro a b
  let X : SemidirectProduct Radical Levi action := ι.symm ⟨a.val, hle a.property⟩
  let Y : SemidirectProduct Radical Levi action := ι.symm ⟨b.val, hle b.property⟩
  have hX : (ι X).val = a.val := by
    simp only [X, MulEquiv.apply_symm_apply]
  have hY : (ι Y).val = b.val := by
    simp only [Y, MulEquiv.apply_symm_apply]
  have hXY : X * Y = ι.symm ⟨(a * b).val, hle (a * b).property⟩ := by
    simp only [X, Y]
    rw [← map_mul]
    rfl
  have memX : X ∈ faceEdgeSubgroup action F ι edge := by
    change (ι X).val ∈ fixedPointLevel rationalLevel edge
    rw [hX]
    exact a.property
  have memY : Y ∈ faceEdgeSubgroup action F ι edge := by
    change (ι Y).val ∈ fixedPointLevel rationalLevel edge
    rw [hY]
    exact b.property
  have rightX : X.right ∈ B := (hB X).mp memX
  have rightY : Y.right ∈ B := (hB Y).mp memY
  have hP := primitiveBoundary X Y rightX rightY
  have hC := congrArg (fun f => f.val X Y) correctionBoundary
  have key : (inhomogeneousBoundaryMap (faceRep action degree character F ι)
      (primitive - correction)).val X Y =
      (faceCycle action degree character F ι original).val X Y := by
    have hC' : (inhomogeneousBoundaryMap (faceRep action degree character F ι)
        correction).val X Y = cycle.val.val X Y -
          (faceCycle action degree character F ι original).val X Y := hC
    rw [map_sub]
    change (inhomogeneousBoundaryMap (faceRep action degree character F ι) primitive).val X Y -
      (inhomogeneousBoundaryMap (faceRep action degree character F ι) correction).val X Y = _
    rw [hP, hC']
    abel
  rw [faceCycle_apply, hX, hY] at key
  have hρ : faceRep action degree character F ι X =
      rationalCoefficientComponent degree character a.val := by
    change rationalCoefficientComponent degree character (ι X).val = _
    rw [hX]
  have key' : faceRep action degree character F ι X ((primitive - correction) Y) -
      (primitive - correction) (X * Y) + (primitive - correction) X =
      original.val.val ![1, a.val, a.val * b.val] := key
  rw [hρ, hXY] at key'
  exact key'

theorem exists_edge_over (F' : Flags side) : ∃ e : Edges, endpoint side e = F' := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective F'
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- **Locally inner iff mixed cuspidal, for a split stabilizer.** -/
theorem face_locallyInner_iff
    (hedge : ∀ e : Edges, endpoint side e = F → EdgeData action degree character F ι e)
    (coordinate : H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character side F ↔
      ∃ radicalZero : faceH2Equiv action degree character F ι coordinate ∈
          (radicalRestrictionH2 action (faceRep action degree character F ι)).ker,
        ∀ e : Edges, endpoint side e = F → ∀ B : Subgroup Levi,
          (∀ x, x ∈ faceEdgeSubgroup action F ι e ↔ x.right ∈ B) →
          crossedPullbackH1 B.subtype
            (leviCrossedH1Representation action (faceRep action degree character F ι))
            (radicalKernelMixedMap action (faceRep action degree character F ι)
              ⟨faceH2Equiv action degree character F ι coordinate, radicalZero⟩) = 0 := by
  constructor
  · intro inner
    have edgeOver := exists_edge_over F
    obtain ⟨e₀, he₀⟩ := edgeOver
    have edgeData₀ := hedge e₀ he₀
    obtain ⟨B₀, hB₀, -⟩ := edgeData₀
    have radicalZero := face_radical_zero action degree character F ι e₀ he₀
      (fun radical => (hB₀ _).mpr (by simp)) coordinate inner
    refine ⟨radicalZero, fun e he B hB => ?_⟩
    have mixedZero := face_mixed_zero action degree character F ι e he B.subtype
      (fun radical => (hB _).mpr (by simp)) (fun element => (hB _).mpr (by simp)) coordinate inner
    obtain ⟨radicalZero', h⟩ := mixedZero
    exact h
  · rintro ⟨radicalZero, hmix⟩
    exact face_locallyInner_of_mixed action degree character F ι hedge coordinate radicalZero hmix

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
