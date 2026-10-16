module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Helpers

def globalBoundaryLinear (degree : ℕ) (character : RankOneCharacter) :
    cocycles rationalLevel (rationalCoefficientComponent degree character) →ₗ[ℂ]
      fullBoundaryCycles degree character where
  toFun := globalBoundaryCocycle degree character
  map_add' first second := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl
    · change 0 = (0 : EdgeCochains degree character 1) + 0
      simp
  map_smul' scalar representative := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl
    · change 0 = scalar • (0 : EdgeCochains degree character 1)
      simp

def constantFlagCochain (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (representative : cochains rationalLevel (rationalCoefficientComponent degree character) 1) :
    MaximalCochains degree character side 1 :=
  ⟨fun vertices _ => representative.val vertices, by
    intro element vertices
    funext flag
    exact representative.property element vertices⟩

theorem globalBoundary_boundary (degree : ℕ) (character : RankOneCharacter)
    (representative : cochains rationalLevel (rationalCoefficientComponent degree character) 1) :
    globalBoundaryLinear degree character
        (boundaryMap rationalLevel (rationalCoefficientComponent degree character) representative) =
      fullBoundaryDifferential degree character
        (constantFlagCochain degree character .plane representative)
        (constantFlagCochain degree character .line representative) 0 := by
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl
  · apply Subtype.ext
    funext vertices edge
    change 0 = (representative.val vertices - representative.val vertices) - (0 - 0)
    simp

def canonicalRestriction (degree : ℕ) (character : RankOneCharacter) :
    WholeGlobalH2 degree character →ₗ[ℂ] FullBoundaryH2 degree character :=
  (LinearMap.range (boundaryMap rationalLevel (rationalCoefficientComponent degree character))).liftQ
    ((fullBoundaryClass degree character).comp (globalBoundaryLinear degree character)) (by
      rintro representative ⟨incoming, rfl⟩
      change fullBoundaryClass degree character
        (globalBoundaryLinear degree character
          (boundaryMap rationalLevel (rationalCoefficientComponent degree character) incoming)) = 0
      rw [globalBoundary_boundary]
      apply (Submodule.Quotient.mk_eq_zero (fullBoundaryRelations degree character)).mpr
      exact Submodule.subset_span
        (fullBoundaryDifferential_is_coboundary degree character _ _ _))

theorem canonicalRestriction_realizes (degree : ℕ) (character : RankOneCharacter) :
    RealizesFullRestriction degree character (canonicalRestriction degree character) := by
  intro representative
  exact Submodule.liftQ_apply _ _ _

def boundaryCoordinateLinear (degree : ℕ) (character : RankOneCharacter) :
    fullBoundaryCycles degree character →ₗ[ℂ] BoundaryCoordinates degree character where
  toFun representative :=
    (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree character) .plane)
        representative.val.1.1,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree character) .line)
        representative.val.1.2)
  map_add' first second := by
    apply Prod.ext <;> apply map_add
  map_smul' scalar representative := by
    apply Prod.ext <;> apply map_smul

def canonicalCoordinates (degree : ℕ) (character : RankOneCharacter) :
    FullBoundaryH2 degree character →ₗ[ℂ] BoundaryCoordinates degree character :=
  (fullBoundaryRelations degree character).liftQ
    (boundaryCoordinateLinear degree character) (by
      apply Submodule.span_le.mpr
      rintro representative ⟨planeIncoming, lineIncoming, edgeIncoming,
        planeEquality, lineEquality, edgeEquality⟩
      change boundaryCoordinateLinear degree character representative = 0
      apply Prod.ext
      · apply (Submodule.Quotient.mk_eq_zero _).mpr
        refine ⟨planeIncoming, ?_⟩
        exact Subtype.ext planeEquality.symm
      · apply (Submodule.Quotient.mk_eq_zero _).mpr
        refine ⟨lineIncoming, ?_⟩
        exact Subtype.ext lineEquality.symm)

theorem canonicalCoordinates_realizes (degree : ℕ) (character : RankOneCharacter) :
    RealizesBoundaryCoordinates degree character (canonicalCoordinates degree character) := by
  intro representative
  exact Submodule.liftQ_apply _ _ _

theorem canonicalRestriction_unique (degree : ℕ) (character : RankOneCharacter)
    (restriction : WholeGlobalH2 degree character →ₗ[ℂ] FullBoundaryH2 degree character)
    (realizes : RealizesFullRestriction degree character restriction) :
    restriction = canonicalRestriction degree character := by
  apply LinearMap.ext
  intro cohomologyClass
  obtain ⟨representative, rfl⟩ :=
    (LinearMap.range (boundaryMap rationalLevel
      (rationalCoefficientComponent degree character))).mkQ_surjective cohomologyClass
  exact (realizes representative).trans
    (canonicalRestriction_realizes degree character representative).symm

theorem canonicalCoordinates_unique (degree : ℕ) (character : RankOneCharacter)
    (coordinates : FullBoundaryH2 degree character →ₗ[ℂ] BoundaryCoordinates degree character)
    (realizes : RealizesBoundaryCoordinates degree character coordinates) :
    coordinates = canonicalCoordinates degree character := by
  apply LinearMap.ext
  intro cohomologyClass
  obtain ⟨representative, rfl⟩ :=
    (fullBoundaryRelations degree character).mkQ_surjective cohomologyClass
  exact (realizes representative).trans
    (canonicalCoordinates_realizes degree character representative).symm

theorem hecke_representative_exists (correspondence : HeckeCorrespondence)
    (element : rationalLevel) (representative : RationalGL3)
    (membership : representative ∈ correspondence.representatives) :
    ∃ translated ∈ correspondence.representatives,
      translated⁻¹ * (element.val * representative) ∈ rationalLevel := by
  obtain ⟨left, right, rfl⟩ := correspondence.inDoubleCoset representative membership
  simpa only [Subgroup.coe_mul, mul_assoc] using correspondence.complete (element * left) right

def translateRepresentative (correspondence : HeckeCorrespondence) (element : rationalLevel)
    (representative : {value // value ∈ correspondence.representatives}) :
    {value // value ∈ correspondence.representatives} :=
  ⟨(hecke_representative_exists correspondence element representative.val
      representative.property).choose,
    (hecke_representative_exists correspondence element representative.val
      representative.property).choose_spec.1⟩

theorem translateRepresentative_mem (correspondence : HeckeCorrespondence)
    (element : rationalLevel) (representative : {value // value ∈ correspondence.representatives}) :
    (translateRepresentative correspondence element representative).val⁻¹ *
      (element.val * representative.val) ∈ rationalLevel :=
  (hecke_representative_exists correspondence element representative.val
    representative.property).choose_spec.2

theorem translateRepresentative_injective (correspondence : HeckeCorrespondence)
    (element : rationalLevel) :
    Function.Injective (translateRepresentative correspondence element) := by
  intro first second equality
  have firstMembership := translateRepresentative_mem correspondence element first
  have secondMembership := translateRepresentative_mem correspondence element second
  rw [equality] at firstMembership
  have relativeMembership := rationalLevel.mul_mem
    (rationalLevel.inv_mem firstMembership) secondMembership
  have simplified : first.val⁻¹ * second.val ∈ rationalLevel := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left,
      inv_mul_cancel_left] using relativeMembership
  exact Subtype.ext
    (correspondence.disjoint first.val first.property second.val second.property simplified)

theorem translateRepresentative_surjective (correspondence : HeckeCorrespondence)
    (element : rationalLevel) :
    Function.Surjective (translateRepresentative correspondence element) := by
  classical
  exact Finite.surjective_of_injective
    (translateRepresentative_injective correspondence element)

theorem hecke_equivariant {Coefficient : Type} [AddCommGroup Coefficient] [Module ℂ Coefficient]
    (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence) (degree : ℕ)
    (cochain : cochains rationalLevel representation degree)
    (element : rationalLevel) (vertices : Fin (degree + 1) → RationalGL3) :
    (∑ representative ∈ correspondence.representatives,
      representation representative
        (cochain.val (fun index => representative⁻¹ * (element.val * vertices index)))) =
      representation element.val
        (∑ representative ∈ correspondence.representatives,
          representation representative
            (cochain.val (fun index => representative⁻¹ * vertices index))) := by
  classical
  rw [map_sum]
  apply (Finset.sum_bij
    (fun representative membership =>
      (translateRepresentative correspondence element⁻¹ ⟨representative, membership⟩).val))
  · intro representative membership
    exact (translateRepresentative correspondence element⁻¹ ⟨representative, membership⟩).property
  · intro first firstMembership second secondMembership equality
    exact congrArg Subtype.val
      (translateRepresentative_injective correspondence element⁻¹ (Subtype.ext equality))
  · intro representative membership
    obtain ⟨preimage, equality⟩ :=
      translateRepresentative_surjective correspondence element⁻¹ ⟨representative, membership⟩
    exact ⟨preimage.val, preimage.property, congrArg Subtype.val equality⟩
  · intro representative membership
    let translated := translateRepresentative correspondence element⁻¹ ⟨representative, membership⟩
    let relative : rationalLevel :=
      ⟨translated.val⁻¹ * (element⁻¹.val * representative),
        translateRepresentative_mem correspondence element⁻¹ ⟨representative, membership⟩⟩
    have verticesEquality :
        (fun index => representative⁻¹ * (element.val * vertices index)) =
          (fun index => relative⁻¹.val * (translated.val⁻¹ * vertices index)) := by
      funext index
      simp [relative, mul_assoc]
    change representation representative
      (cochain.val (fun index => representative⁻¹ * (element.val * vertices index))) =
      representation element.val
        (representation translated.val
          (cochain.val (fun index => translated.val⁻¹ * vertices index)))
    rw [verticesEquality, cochain.property relative⁻¹]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 1
    simp [relative, mul_assoc]

def heckeCochainLinear {Coefficient : Type} [AddCommGroup Coefficient] [Module ℂ Coefficient]
    (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence) (degree : ℕ) :
    cochains rationalLevel representation degree →ₗ[ℂ]
      cochains rationalLevel representation degree where
  toFun cochain :=
    ⟨fun vertices => ∑ representative ∈ correspondence.representatives,
      representation representative
        (cochain.val (fun index => representative⁻¹ * vertices index)),
      hecke_equivariant representation correspondence degree cochain⟩
  map_add' first second := by
    apply Subtype.ext
    funext vertices
    simp only [Submodule.coe_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext vertices
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Finset.smul_sum,
      RingHom.id_apply]

theorem hecke_differentialOne {Coefficient : Type} [AddCommGroup Coefficient]
    [Module ℂ Coefficient] (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence)
    (cochain : cochains rationalLevel representation 1) :
    heckeCochainLinear representation correspondence 2 (differentialOne _ _ cochain) =
      differentialOne _ _ (heckeCochainLinear representation correspondence 1 cochain) := by
  apply Subtype.ext
  funext vertices
  have pairEquality : ∀ representative first second,
      (fun index => representative⁻¹ * (![first, second] : Fin 2 → RationalGL3) index) =
        ![representative⁻¹ * first, representative⁻¹ * second] := by
    intro representative first second
    funext index
    fin_cases index <;> rfl
  simp only [heckeCochainLinear, differentialOne, LinearMap.coe_mk, AddHom.coe_mk,
    pairEquality]
  simp only [map_add, map_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem hecke_differentialTwo {Coefficient : Type} [AddCommGroup Coefficient]
    [Module ℂ Coefficient] (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence)
    (cochain : cochains rationalLevel representation 2) :
    differentialTwo rationalLevel representation
        (heckeCochainLinear representation correspondence 2 cochain) =
      fun vertices => ∑ representative ∈ correspondence.representatives,
        representation representative
          (differentialTwo rationalLevel representation cochain
            (fun index => representative⁻¹ * vertices index)) := by
  funext vertices
  have tripleEquality : ∀ representative first second third,
      (fun index => representative⁻¹ * (![first, second, third] : Fin 3 → RationalGL3) index) =
        ![representative⁻¹ * first, representative⁻¹ * second, representative⁻¹ * third] := by
    intro representative first second third
    funext index
    fin_cases index <;> rfl
  simp only [heckeCochainLinear, differentialTwo, LinearMap.coe_mk, AddHom.coe_mk,
    tripleEquality]
  simp only [map_sub, map_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

def heckeCocycleLinear {Coefficient : Type} [AddCommGroup Coefficient] [Module ℂ Coefficient]
    (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence) :
    cocycles rationalLevel representation →ₗ[ℂ] cocycles rationalLevel representation :=
  ((heckeCochainLinear representation correspondence 2).comp
      (cocycles rationalLevel representation).subtype).codRestrict _ (by
    intro cocycle
    change differentialTwo rationalLevel representation
      (heckeCochainLinear representation correspondence 2 cocycle.val) = 0
    rw [hecke_differentialTwo]
    funext vertices
    have vanishes : differentialTwo rationalLevel representation cocycle.val = 0 := cocycle.property
    simp only [vanishes, Pi.zero_apply, map_zero, Finset.sum_const_zero])

theorem hecke_boundaryMap {Coefficient : Type} [AddCommGroup Coefficient] [Module ℂ Coefficient]
    (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence)
    (cochain : cochains rationalLevel representation 1) :
    heckeCocycleLinear representation correspondence (boundaryMap _ _ cochain) =
      boundaryMap _ _ (heckeCochainLinear representation correspondence 1 cochain) := by
  apply Subtype.ext
  exact hecke_differentialOne representation correspondence cochain

def canonicalHecke {Coefficient : Type} [AddCommGroup Coefficient] [Module ℂ Coefficient]
    (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence) : Module.End ℂ (H2 rationalLevel representation) :=
  (LinearMap.range (boundaryMap rationalLevel representation)).liftQ
    ((classOf rationalLevel representation).comp
      (heckeCocycleLinear representation correspondence)) (by
    rintro cocycle ⟨incoming, rfl⟩
    change classOf rationalLevel representation
      (heckeCocycleLinear representation correspondence (boundaryMap _ _ incoming)) = 0
    rw [hecke_boundaryMap]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩)

theorem canonicalHecke_realizes {Coefficient : Type} [AddCommGroup Coefficient]
    [Module ℂ Coefficient] (representation : Representation ℂ RationalGL3 Coefficient) :
    RealizesHecke representation (canonicalHecke representation) := by
  intro correspondence cocycle
  refine ⟨heckeCocycleLinear representation correspondence cocycle, ?_, ?_⟩
  · intro vertices
    rfl
  · exact Submodule.liftQ_apply _ _ _

theorem canonicalHecke_unique {Coefficient : Type} [AddCommGroup Coefficient]
    [Module ℂ Coefficient] (representation : Representation ℂ RationalGL3 Coefficient)
    (action : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel representation))
    (realizes : RealizesHecke representation action) :
    action = canonicalHecke representation := by
  funext correspondence
  apply LinearMap.ext
  intro cohomologyClass
  obtain ⟨representative, rfl⟩ :=
    (LinearMap.range (boundaryMap rationalLevel representation)).mkQ_surjective cohomologyClass
  obtain ⟨image, imageFormula, actionFormula⟩ := realizes correspondence representative
  have imageEquality : image = heckeCocycleLinear representation correspondence representative := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    exact imageFormula vertices
  change action correspondence (classOf rationalLevel representation representative) = _
  rw [actionFormula, imageEquality]
  symm
  exact Submodule.liftQ_apply _ _ _

theorem canonicalCoordinates_restriction (degree : ℕ) (character : RankOneCharacter) :
    RealizesRestriction degree character
      ((canonicalCoordinates degree character).comp (canonicalRestriction degree character)) := by
  intro representative
  rw [LinearMap.comp_apply, canonicalRestriction_realizes,
    canonicalCoordinates_realizes]
  rfl

theorem restriction_heckeCocycle (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (correspondence : HeckeCorrespondence)
    (representative : cocycles rationalLevel (rationalCoefficientComponent degree character)) :
    restrictionCocycle degree character side
        (heckeCocycleLinear (rationalCoefficientComponent degree character)
          correspondence representative) =
      heckeCocycleLinear
        (flagRepresentation (rationalCoefficientComponent degree character) side)
        correspondence (restrictionCocycle degree character side representative) := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices flag
  change (∑ value ∈ correspondence.representatives,
      rationalCoefficientComponent degree character value
        (representative.val.val (fun index => value⁻¹ * vertices index))) =
    (∑ value ∈ correspondence.representatives,
      (flagRepresentation (rationalCoefficientComponent degree character) side value)
        (fun _ => representative.val.val (fun index => value⁻¹ * vertices index))) flag
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro value membership
  rfl

theorem canonicalHecke_apply {Coefficient : Type} [AddCommGroup Coefficient]
    [Module ℂ Coefficient] (representation : Representation ℂ RationalGL3 Coefficient)
    (correspondence : HeckeCorrespondence)
    (representative : cocycles rationalLevel representation) :
    canonicalHecke representation correspondence (classOf rationalLevel representation representative) =
      classOf rationalLevel representation
        (heckeCocycleLinear representation correspondence representative) :=
  Submodule.liftQ_apply _ _ _

theorem canonicalCoordinates_restriction_hecke (degree : ℕ) (character : RankOneCharacter)
    (correspondence : HeckeCorrespondence) :
    ((canonicalCoordinates degree character).comp (canonicalRestriction degree character)).comp
        (canonicalHecke (rationalCoefficientComponent degree character) correspondence) =
      ((canonicalHecke
          (flagRepresentation (rationalCoefficientComponent degree character) .plane)
          correspondence).prodMap
        (canonicalHecke
          (flagRepresentation (rationalCoefficientComponent degree character) .line)
          correspondence)).comp
        ((canonicalCoordinates degree character).comp (canonicalRestriction degree character)) := by
  apply LinearMap.ext
  intro cohomologyClass
  have surjective := (LinearMap.range (boundaryMap rationalLevel
      (rationalCoefficientComponent degree character))).mkQ_surjective cohomologyClass
  obtain ⟨representative, rfl⟩ := surjective
  have hecke_class := canonicalHecke_apply (rationalCoefficientComponent degree character)
    correspondence representative
  have hecke_plane := canonicalHecke_apply
    (flagRepresentation (rationalCoefficientComponent degree character) .plane)
    correspondence (restrictionCocycle degree character .plane representative)
  have hecke_line := canonicalHecke_apply
    (flagRepresentation (rationalCoefficientComponent degree character) .line)
    correspondence (restrictionCocycle degree character .line representative)
  have restrict_hecke := canonicalCoordinates_restriction degree character
    (heckeCocycleLinear (rationalCoefficientComponent degree character) correspondence
      representative)
  have restrict_class := canonicalCoordinates_restriction degree character representative
  have plane_eq := restriction_heckeCocycle degree character .plane correspondence representative
  have line_eq := restriction_heckeCocycle degree character .line correspondence representative
  refine (LinearMap.comp_apply _ _ _).trans ?_
  refine (congrArg _ hecke_class).trans ?_
  refine restrict_hecke.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg _ restrict_class).symm
  refine Eq.trans ?_ (LinearMap.prodMap_apply _ _ _).symm
  exact Prod.ext
    ((congrArg (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane))
      plane_eq).trans hecke_plane.symm)
    ((congrArg (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .line))
      line_eq).trans hecke_line.symm)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Helpers
