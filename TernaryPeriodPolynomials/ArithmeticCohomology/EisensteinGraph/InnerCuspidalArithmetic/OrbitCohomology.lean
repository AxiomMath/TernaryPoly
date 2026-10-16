module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.OrbitReconstruction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

abbrev OrbitIndex (level : Subgroup RationalGL3) (X : Type)
    [MulAction RationalGL3 X] := MulAction.orbitRel.Quotient level X

def orbitRestrictionCochain (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (degree : ℕ) :
    cochains level (functionRepresentation representation X) degree →ₗ[ℂ]
      ∀ orbit : OrbitIndex level X,
        cochains (fixedPointLevel level orbit.out) representation degree :=
  LinearMap.pi fun orbit => fixedPointCochain level representation orbit.out degree

def orbitReconstructionCochain (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (degree : ℕ) :
    (∀ orbit : OrbitIndex level X,
      cochains (fixedPointLevel level orbit.out) representation degree) →ₗ[ℂ]
      cochains level (functionRepresentation representation X) degree where
  toFun localCochains :=
    ⟨fun vertices point =>
      representation (orbitTransport level point).val
        ((localCochains (Quotient.mk'' point)).val
          (fun index => (orbitTransport level point).val⁻¹ * vertices index)), by
      intro element vertices
      funext point
      let previous := element.val⁻¹ • point
      let currentTransport := orbitTransport level point
      let previousTransport := orbitTransport level previous
      have sameOrbit : (Quotient.mk'' previous : OrbitIndex level X) =
          Quotient.mk'' point :=
        MulAction.orbitRel.Quotient.quotient_smul_eq (g := element⁻¹) (a := point)
      have sameRepresentative : orbitRepresentative level previous =
          orbitRepresentative level point := congrArg Quotient.out sameOrbit
      let correction := currentTransport⁻¹ * element * previousTransport
      have fixes : correction.val • orbitRepresentative level point =
          orbitRepresentative level point := by
        change (currentTransport.val⁻¹ * element.val * previousTransport.val) •
          orbitRepresentative level point = orbitRepresentative level point
        rw [mul_smul, mul_smul, ← sameRepresentative, orbitTransport_spec]
        change currentTransport.val⁻¹ • (element.val • (element.val⁻¹ • point)) = _
        rw [smul_inv_smul, sameRepresentative]
        have transported := congrArg (fun flag => currentTransport.val⁻¹ • flag)
          (orbitTransport_spec level point)
        change currentTransport.val⁻¹ • (currentTransport.val •
          orbitRepresentative level point) = currentTransport.val⁻¹ • point at transported
        simpa only [inv_smul_smul] using transported.symm
      have correctionLevel : correction.val ∈
          fixedPointLevel level (orbitRepresentative level point) :=
        ⟨correction.property, MulAction.mem_stabilizer_iff.mpr fixes⟩
      have equivariance := (localCochains (Quotient.mk'' point)).property
        ⟨correction.val, correctionLevel⟩
        (fun index => previousTransport.val⁻¹ * vertices index)
      have vertexEquality :
          (fun index => currentTransport.val⁻¹ * (element.val * vertices index)) =
          (fun index => correction.val * (previousTransport.val⁻¹ * vertices index)) := by
        funext index
        change currentTransport.val⁻¹ * (element.val * vertices index) =
          (currentTransport.val⁻¹ * element.val * previousTransport.val) *
            (previousTransport.val⁻¹ * vertices index)
        group
      change representation currentTransport.val
          ((localCochains (Quotient.mk'' point)).val
            (fun index => currentTransport.val⁻¹ * (element.val * vertices index))) =
        representation element.val
          (representation previousTransport.val
            ((localCochains (Quotient.mk'' previous)).val
              (fun index => previousTransport.val⁻¹ * vertices index)))
      rw [sameOrbit, vertexEquality, equivariance]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      have productEquality : currentTransport.val * correction.val =
          element.val * previousTransport.val := by
        change currentTransport.val *
          (currentTransport.val⁻¹ * element.val * previousTransport.val) =
          element.val * previousTransport.val
        group
      rw [productEquality]⟩
  map_add' first second := by
    apply Subtype.ext
    funext vertices point
    exact map_add _ _ _
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext vertices point
    exact map_smul _ _ _

theorem orbitRestriction_reconstructionCochain (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (degree : ℕ)
    (localCochains : ∀ orbit : OrbitIndex level X,
      cochains (fixedPointLevel level orbit.out) representation degree) :
    orbitRestrictionCochain level representation degree
        (orbitReconstructionCochain level representation degree localCochains) =
      localCochains := by
  funext orbit
  apply Subtype.ext
  funext vertices
  have sameOrbit : (Quotient.mk'' orbit.out : OrbitIndex level X) = orbit :=
    Quotient.out_eq orbit
  have sameRepresentative : orbitRepresentative level orbit.out = orbit.out :=
    congrArg Quotient.out sameOrbit
  have transportFixed : (orbitTransport level orbit.out).val • orbit.out = orbit.out := by
    simpa only [sameRepresentative] using orbitTransport_spec level orbit.out
  have transportLevel : (orbitTransport level orbit.out).val ∈
      fixedPointLevel level orbit.out :=
    ⟨(orbitTransport level orbit.out).property,
      MulAction.mem_stabilizer_iff.mpr transportFixed⟩
  have equivariance := (localCochains orbit).property
    ⟨(orbitTransport level orbit.out).val, transportLevel⟩
    (fun index => (orbitTransport level orbit.out).val⁻¹ * vertices index)
  change representation (orbitTransport level orbit.out).val
      ((localCochains (Quotient.mk'' orbit.out)).val
        (fun index => (orbitTransport level orbit.out).val⁻¹ * vertices index)) =
    (localCochains orbit).val vertices
  rw [sameOrbit]
  simpa only [mul_inv_cancel_left] using equivariance.symm

theorem orbitReconstruction_restrictionCochain (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (degree : ℕ)
    (cochain : cochains level (functionRepresentation representation X) degree) :
    orbitReconstructionCochain level representation degree
        (orbitRestrictionCochain level representation degree cochain) = cochain := by
  apply Subtype.ext
  funext vertices point
  exact (cochain_orbitTransport level representation degree cochain vertices point).symm

def orbitCochainEquiv (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (degree : ℕ) :
    cochains level (functionRepresentation representation X) degree ≃ₗ[ℂ]
      ∀ orbit : OrbitIndex level X,
        cochains (fixedPointLevel level orbit.out) representation degree where
  toLinearMap := orbitRestrictionCochain level representation degree
  invFun := orbitReconstructionCochain level representation degree
  left_inv := orbitReconstruction_restrictionCochain level representation degree
  right_inv := orbitRestriction_reconstructionCochain level representation degree

theorem orbitReconstructionCochain_differentialOne (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (localCochains : ∀ orbit : OrbitIndex level X,
      cochains (fixedPointLevel level orbit.out) representation 1) :
    orbitReconstructionCochain level representation 2
        (fun orbit => differentialOne (fixedPointLevel level orbit.out)
          representation (localCochains orbit)) =
      differentialOne level (functionRepresentation representation X)
        (orbitReconstructionCochain level representation 1 localCochains) := by
  apply (orbitCochainEquiv level representation 2).injective
  change orbitRestrictionCochain level representation 2 _ =
    orbitRestrictionCochain level representation 2 _
  rw [orbitRestriction_reconstructionCochain]
  funext orbit
  change differentialOne (fixedPointLevel level orbit.out) representation
      (localCochains orbit) =
    fixedPointCochain level representation orbit.out 2 _
  rw [fixedPointCochain_differentialOne]
  have restricted := congrFun
    (orbitRestriction_reconstructionCochain level representation 1 localCochains) orbit
  exact congrArg (differentialOne (fixedPointLevel level orbit.out) representation)
    restricted.symm

def orbitRestrictionCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) :
    cocycles level (functionRepresentation representation X) →ₗ[ℂ]
      ∀ orbit : OrbitIndex level X,
        cocycles (fixedPointLevel level orbit.out) representation :=
  LinearMap.pi fun orbit => fixedPointCycle level representation orbit.out

def orbitReconstructionCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) :
    (∀ orbit : OrbitIndex level X,
      cocycles (fixedPointLevel level orbit.out) representation) →ₗ[ℂ]
      cocycles level (functionRepresentation representation X) :=
  ((orbitReconstructionCochain level representation 2).comp
    (LinearMap.pi fun orbit =>
      (cocycles (fixedPointLevel level orbit.out) representation).subtype.comp
        (LinearMap.proj orbit))).codRestrict _ (by
      intro localCycles
      funext vertices point
      let transport := orbitTransport level point
      have translatedTriple (first second third : RationalGL3) :
          (fun index : Fin 3 => transport.val⁻¹ * ![first, second, third] index) =
            ![transport.val⁻¹ * first, transport.val⁻¹ * second,
              transport.val⁻¹ * third] := by
        funext index
        fin_cases index <;> rfl
      change representation transport.val
          ((localCycles (Quotient.mk'' point)).val.val
            (fun index => transport.val⁻¹ * ![vertices 1, vertices 2, vertices 3] index)) -
        representation transport.val
          ((localCycles (Quotient.mk'' point)).val.val
            (fun index => transport.val⁻¹ * ![vertices 0, vertices 2, vertices 3] index)) +
        representation transport.val
          ((localCycles (Quotient.mk'' point)).val.val
            (fun index => transport.val⁻¹ * ![vertices 0, vertices 1, vertices 3] index)) -
        representation transport.val
          ((localCycles (Quotient.mk'' point)).val.val
            (fun index => transport.val⁻¹ * ![vertices 0, vertices 1, vertices 2] index)) = 0
      simp only [translatedTriple]
      rw [← map_sub, ← map_add, ← map_sub]
      have vanishing := congrFun (localCycles (Quotient.mk'' point)).property
        (fun index => transport.val⁻¹ * vertices index)
      change (localCycles (Quotient.mk'' point)).val.val
          ![transport.val⁻¹ * vertices 1, transport.val⁻¹ * vertices 2,
            transport.val⁻¹ * vertices 3] -
        (localCycles (Quotient.mk'' point)).val.val
          ![transport.val⁻¹ * vertices 0, transport.val⁻¹ * vertices 2,
            transport.val⁻¹ * vertices 3] +
        (localCycles (Quotient.mk'' point)).val.val
          ![transport.val⁻¹ * vertices 0, transport.val⁻¹ * vertices 1,
            transport.val⁻¹ * vertices 3] -
        (localCycles (Quotient.mk'' point)).val.val
          ![transport.val⁻¹ * vertices 0, transport.val⁻¹ * vertices 1,
            transport.val⁻¹ * vertices 2] = 0 at vanishing
      rw [vanishing, map_zero])

theorem orbitRestriction_reconstructionCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (localCycles : ∀ orbit : OrbitIndex level X,
      cocycles (fixedPointLevel level orbit.out) representation) :
    orbitRestrictionCycle level representation
        (orbitReconstructionCycle level representation localCycles) = localCycles := by
  funext orbit
  apply Subtype.ext
  exact congrFun (orbitRestriction_reconstructionCochain level representation 2
    (fun orbit => (localCycles orbit).val)) orbit

theorem orbitReconstruction_restrictionCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (cycle : cocycles level (functionRepresentation representation X)) :
    orbitReconstructionCycle level representation
        (orbitRestrictionCycle level representation cycle) = cycle := by
  apply Subtype.ext
  exact orbitReconstruction_restrictionCochain level representation 2 cycle.val

def orbitCycleEquiv (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) :
    cocycles level (functionRepresentation representation X) ≃ₗ[ℂ]
      ∀ orbit : OrbitIndex level X,
        cocycles (fixedPointLevel level orbit.out) representation where
  toLinearMap := orbitRestrictionCycle level representation
  invFun := orbitReconstructionCycle level representation
  left_inv := orbitReconstruction_restrictionCycle level representation
  right_inv := orbitRestriction_reconstructionCycle level representation

theorem orbitReconstructionCycle_boundaryMap (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (localCochains : ∀ orbit : OrbitIndex level X,
      cochains (fixedPointLevel level orbit.out) representation 1) :
    orbitReconstructionCycle level representation
        (fun orbit => boundaryMap (fixedPointLevel level orbit.out)
          representation (localCochains orbit)) =
      boundaryMap level (functionRepresentation representation X)
        (orbitReconstructionCochain level representation 1 localCochains) := by
  apply Subtype.ext
  exact orbitReconstructionCochain_differentialOne level representation localCochains

def orbitRestrictionH2 (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) :
    H2 level (functionRepresentation representation X) →ₗ[ℂ]
      ∀ orbit : OrbitIndex level X,
        H2 (fixedPointLevel level orbit.out) representation :=
  LinearMap.pi fun orbit => fixedPointH2 level representation orbit.out

theorem orbitRestrictionH2_injective (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) :
    Function.Injective (orbitRestrictionH2 level representation (X := X)) := by
  intro first second sameRestrictions
  apply sub_eq_zero.mp
  have vanishing : orbitRestrictionH2 level representation (first - second) = 0 := by
    rw [map_sub, sameRestrictions, sub_self]
  generalize coordinate_eq : first - second = coordinate at vanishing ⊢
  revert vanishing
  refine Quotient.inductionOn' coordinate ?_
  intro cycle vanishing
  have localVanishing : ∀ orbit : OrbitIndex level X,
      classOf (fixedPointLevel level orbit.out) representation
        (fixedPointCycle level representation orbit.out cycle) = 0 := by
    intro orbit
    exact congrFun vanishing orbit
  have localBoundaries : ∀ orbit : OrbitIndex level X,
      ∃ primitive : cochains (fixedPointLevel level orbit.out) representation 1,
        boundaryMap (fixedPointLevel level orbit.out) representation primitive =
          fixedPointCycle level representation orbit.out cycle := by
    intro orbit
    exact (Submodule.Quotient.mk_eq_zero _).mp (localVanishing orbit)
  choose primitives boundaries using localBoundaries
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨orbitReconstructionCochain level representation 1 primitives, ?_⟩
  rw [← orbitReconstructionCycle_boundaryMap]
  exact (congrArg (orbitReconstructionCycle level representation)
    (funext fun orbit => (boundaries orbit).trans
      (LinearMap.pi_apply (fun orbit : OrbitIndex level X =>
        fixedPointCycle level representation orbit.out) cycle orbit).symm)).trans
    (orbitReconstruction_restrictionCycle level representation cycle)

theorem orbitRestrictionH2_surjective (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) :
    Function.Surjective (orbitRestrictionH2 level representation (X := X)) := by
  intro localClasses
  have representatives : ∀ orbit : OrbitIndex level X,
      ∃ cycle : cocycles (fixedPointLevel level orbit.out) representation,
        classOf (fixedPointLevel level orbit.out) representation cycle = localClasses orbit := by
    intro orbit
    exact Submodule.mkQ_surjective _ (localClasses orbit)
  choose cycles classes using representatives
  refine ⟨classOf level (functionRepresentation representation X)
    (orbitReconstructionCycle level representation cycles), ?_⟩
  funext orbit
  change classOf (fixedPointLevel level orbit.out) representation
    (orbitRestrictionCycle level representation
      (orbitReconstructionCycle level representation cycles) orbit) = localClasses orbit
  rw [orbitRestriction_reconstructionCycle]
  exact classes orbit

def orbitH2Equiv (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) :
    H2 level (functionRepresentation representation X) ≃ₗ[ℂ]
      ∀ orbit : OrbitIndex level X,
        H2 (fixedPointLevel level orbit.out) representation :=
  LinearEquiv.ofBijective (orbitRestrictionH2 level representation)
    ⟨orbitRestrictionH2_injective level representation,
      orbitRestrictionH2_surjective level representation⟩

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
