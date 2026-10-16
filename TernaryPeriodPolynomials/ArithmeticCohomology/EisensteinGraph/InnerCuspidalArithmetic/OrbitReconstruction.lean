module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerRestriction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

def orbitRepresentative (level : Subgroup RationalGL3) (point : X) : X :=
  (Quotient.mk'' point : MulAction.orbitRel.Quotient level X).out

theorem orbitRepresentative_smul (level : Subgroup RationalGL3)
    (element : level) (point : X) :
    orbitRepresentative level (element.val • point) = orbitRepresentative level point := by
  exact congrArg Quotient.out
    (MulAction.orbitRel.Quotient.quotient_smul_eq (g := element) (a := point))

theorem exists_orbitTransport (level : Subgroup RationalGL3) (point : X) :
    ∃ element : level, element.val • orbitRepresentative level point = point := by
  apply MulAction.mem_orbit_iff.mp
  apply MulAction.orbitRel_apply.mp
  exact Quotient.exact (Quotient.out_eq
    (Quotient.mk'' point : MulAction.orbitRel.Quotient level X)).symm

def orbitTransport (level : Subgroup RationalGL3) (point : X) : level :=
  Classical.choose (exists_orbitTransport level point)

theorem orbitTransport_spec (level : Subgroup RationalGL3) (point : X) :
    (orbitTransport level point).val • orbitRepresentative level point = point :=
  Classical.choose_spec (exists_orbitTransport level point)

def reconstructPrimitive (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (primitives : ∀ point : X,
      cochains (fixedPointLevel level point) representation 1) :
    cochains level (functionRepresentation representation X) 1 :=
  ⟨fun vertices point =>
    representation (orbitTransport level point).val
      ((primitives (orbitRepresentative level point)).val
        (fun index => (orbitTransport level point).val⁻¹ * vertices index)), by
    intro element vertices
    funext point
    let previous := element.val⁻¹ • point
    let currentTransport := orbitTransport level point
    let previousTransport := orbitTransport level previous
    have sameRepresentative : orbitRepresentative level previous =
        orbitRepresentative level point :=
      orbitRepresentative_smul level element⁻¹ point
    let correction := currentTransport⁻¹ * element * previousTransport
    have fixes : correction.val • orbitRepresentative level point =
        orbitRepresentative level point := by
      change (currentTransport.val⁻¹ * element.val * previousTransport.val) •
        orbitRepresentative level point = orbitRepresentative level point
      rw [mul_smul, mul_smul, ← sameRepresentative]
      rw [orbitTransport_spec]
      change currentTransport.val⁻¹ • (element.val • (element.val⁻¹ • point)) = _
      rw [smul_inv_smul]
      rw [sameRepresentative]
      have transported := congrArg (fun flag => currentTransport.val⁻¹ • flag)
        (orbitTransport_spec level point)
      change currentTransport.val⁻¹ • (currentTransport.val •
        orbitRepresentative level point) = currentTransport.val⁻¹ • point at transported
      simpa only [inv_smul_smul] using transported.symm
    have correctionLevel : correction.val ∈
        fixedPointLevel level (orbitRepresentative level point) :=
      ⟨correction.property, MulAction.mem_stabilizer_iff.mpr fixes⟩
    have equivariance := (primitives (orbitRepresentative level point)).property
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
        ((primitives (orbitRepresentative level point)).val
          (fun index => currentTransport.val⁻¹ * (element.val * vertices index))) =
      representation element.val
        (representation previousTransport.val
          ((primitives (orbitRepresentative level previous)).val
            (fun index => previousTransport.val⁻¹ * vertices index)))
    rw [sameRepresentative, vertexEquality, equivariance]
    rw [← Module.End.mul_apply, ← map_mul]
    rw [← Module.End.mul_apply, ← map_mul]
    have productEquality : currentTransport.val * correction.val =
        element.val * previousTransport.val := by
      change currentTransport.val *
        (currentTransport.val⁻¹ * element.val * previousTransport.val) =
        element.val * previousTransport.val
      group
    rw [productEquality]⟩

theorem cochain_orbitTransport (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (degree : ℕ)
    (cochain : cochains level (functionRepresentation representation X) degree)
    (vertices : Fin (degree + 1) → RationalGL3) (point : X) :
    cochain.val vertices point =
      representation (orbitTransport level point).val
        (cochain.val
          (fun index => (orbitTransport level point).val⁻¹ * vertices index)
          (orbitRepresentative level point)) := by
  have equivariance := congrFun
    (cochain.property (orbitTransport level point)
      (fun index => (orbitTransport level point).val⁻¹ * vertices index)) point
  have inversePoint : (orbitTransport level point).val⁻¹ • point =
      orbitRepresentative level point := by
    have transported := congrArg
      (fun flag => (orbitTransport level point).val⁻¹ • flag)
      (orbitTransport_spec level point)
    simpa only [inv_smul_smul] using transported.symm
  change cochain.val
      (fun index => (orbitTransport level point).val *
        ((orbitTransport level point).val⁻¹ * vertices index)) point =
    representation (orbitTransport level point).val
      (cochain.val (fun index => (orbitTransport level point).val⁻¹ * vertices index)
        ((orbitTransport level point).val⁻¹ • point)) at equivariance
  simpa only [mul_inv_cancel_left, inversePoint] using equivariance

theorem reconstructPrimitive_boundary (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (cycle : cocycles level (functionRepresentation representation X))
    (primitives : ∀ point : X,
      cochains (fixedPointLevel level point) representation 1)
    (localBoundaries : ∀ point,
      boundaryMap (fixedPointLevel level point) representation (primitives point) =
        fixedPointCycle level representation point cycle) :
    boundaryMap level (functionRepresentation representation X)
      (reconstructPrimitive level representation primitives) = cycle := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices point
  change representation (orbitTransport level point).val
      ((primitives (orbitRepresentative level point)).val
        (fun index => (orbitTransport level point).val⁻¹ *
          ![vertices 1, vertices 2] index)) -
    representation (orbitTransport level point).val
      ((primitives (orbitRepresentative level point)).val
        (fun index => (orbitTransport level point).val⁻¹ *
          ![vertices 0, vertices 2] index)) +
    representation (orbitTransport level point).val
      ((primitives (orbitRepresentative level point)).val
        (fun index => (orbitTransport level point).val⁻¹ *
          ![vertices 0, vertices 1] index)) = cycle.val.val vertices point
  have translatedPair (first second : RationalGL3) :
      (fun index : Fin 2 => (orbitTransport level point).val⁻¹ * ![first, second] index) =
        ![(orbitTransport level point).val⁻¹ * first,
          (orbitTransport level point).val⁻¹ * second] := by
    funext index
    fin_cases index <;> rfl
  simp only [translatedPair]
  rw [← map_sub, ← map_add]
  have boundary := congrArg
    (fun restricted => restricted.val.val
      (fun index => (orbitTransport level point).val⁻¹ * vertices index))
    (localBoundaries (orbitRepresentative level point))
  change (primitives (orbitRepresentative level point)).val
        ![(orbitTransport level point).val⁻¹ * vertices 1,
          (orbitTransport level point).val⁻¹ * vertices 2] -
      (primitives (orbitRepresentative level point)).val
        ![(orbitTransport level point).val⁻¹ * vertices 0,
          (orbitTransport level point).val⁻¹ * vertices 2] +
      (primitives (orbitRepresentative level point)).val
        ![(orbitTransport level point).val⁻¹ * vertices 0,
          (orbitTransport level point).val⁻¹ * vertices 1] =
    cycle.val.val (fun index => (orbitTransport level point).val⁻¹ * vertices index)
      (orbitRepresentative level point) at boundary
  rw [boundary]
  exact (cochain_orbitTransport level representation 2 cycle.val vertices point).symm

theorem eq_zero_iff_fixedPointH2 (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (coordinate : H2 level (functionRepresentation representation X)) :
    coordinate = 0 ↔ ∀ point : X,
      fixedPointH2 level representation point coordinate = 0 := by
  constructor
  · rintro rfl point
    exact map_zero _
  · refine Quotient.inductionOn' coordinate ?_
    intro cycle localVanishing
    have localBoundaries : ∀ point : X,
        ∃ primitive : cochains (fixedPointLevel level point) representation 1,
          boundaryMap (fixedPointLevel level point) representation primitive =
            fixedPointCycle level representation point cycle := by
      intro point
      have atPoint := localVanishing point
      change classOf (fixedPointLevel level point) representation
        (fixedPointCycle level representation point cycle) = 0 at atPoint
      exact (Submodule.Quotient.mk_eq_zero _).mp atPoint
    choose primitives boundaries using localBoundaries
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨reconstructPrimitive level representation primitives,
      reconstructPrimitive_boundary level representation cycle primitives boundaries⟩

theorem fixedPointH2_jointly_injective (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (first second : H2 level (functionRepresentation representation X))
    (sameRestrictions : ∀ point : X,
      fixedPointH2 level representation point first =
        fixedPointH2 level representation point second) : first = second := by
  apply sub_eq_zero.mp
  apply (eq_zero_iff_fixedPointH2 level representation (first - second)).mpr
  intro point
  rw [map_sub, sameRestrictions point, sub_self]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
