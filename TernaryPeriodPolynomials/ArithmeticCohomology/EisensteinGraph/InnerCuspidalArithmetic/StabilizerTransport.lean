module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

def stabilizerConjugateBack (level : Subgroup RationalGL3)
    (element : level) (source target : X) (transports : element.val • source = target)
    (fixed : fixedPointLevel level target) : fixedPointLevel level source :=
  ⟨element.val⁻¹ * fixed.val * element.val, by
    refine ⟨level.mul_mem (level.mul_mem (level.inv_mem element.property) fixed.property.1)
      element.property, MulAction.mem_stabilizer_iff.mpr ?_⟩
    rw [mul_smul, mul_smul, transports, MulAction.mem_stabilizer_iff.mp fixed.property.2]
    rw [← transports, inv_smul_smul]⟩

def stabilizerTransportCochain (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (source target : X) (transports : element.val • source = target)
    (degree : ℕ) :
    cochains (fixedPointLevel level source) representation degree →ₗ[ℂ]
      cochains (fixedPointLevel level target) representation degree where
  toFun cochain := ⟨fun vertices => representation element.val
    (cochain.val (fun index => element.val⁻¹ * vertices index)), by
      intro fixed vertices
      have equivariance := cochain.property
        (stabilizerConjugateBack level element source target transports fixed)
        (fun index => element.val⁻¹ * vertices index)
      change cochain.val (fun index => (element.val⁻¹ * fixed.val * element.val) *
          (element.val⁻¹ * vertices index)) =
        representation (element.val⁻¹ * fixed.val * element.val)
          (cochain.val (fun index => element.val⁻¹ * vertices index)) at equivariance
      have vertices_eq :
          (fun index => element.val⁻¹ * (fixed.val * vertices index)) =
            (fun index => (element.val⁻¹ * fixed.val * element.val) *
              (element.val⁻¹ * vertices index)) := by
        funext index
        group
      change representation element.val
          (cochain.val (fun index => element.val⁻¹ * (fixed.val * vertices index))) =
        representation fixed.val (representation element.val
          (cochain.val (fun index => element.val⁻¹ * vertices index)))
      rw [vertices_eq, equivariance]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 1
      group⟩
  map_add' first second := by
    apply Subtype.ext
    funext vertices
    exact map_add _ _ _
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext vertices
    exact map_smul _ _ _

theorem stabilizerTransportCochain_differentialOne (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (source target : X) (transports : element.val • source = target)
    (cochain : cochains (fixedPointLevel level source) representation 1) :
    stabilizerTransportCochain level representation element source target transports 2
        (differentialOne _ _ cochain) =
      differentialOne _ _
        (stabilizerTransportCochain level representation element source target transports 1
          cochain) := by
  apply Subtype.ext
  funext vertices
  have translatedPair (first second : RationalGL3) :
      (fun index : Fin 2 => element.val⁻¹ * ![first, second] index) =
        ![element.val⁻¹ * first, element.val⁻¹ * second] := by
    funext index
    fin_cases index <;> rfl
  change representation element.val
      (cochain.val ![element.val⁻¹ * vertices 1, element.val⁻¹ * vertices 2] -
        cochain.val ![element.val⁻¹ * vertices 0, element.val⁻¹ * vertices 2] +
        cochain.val ![element.val⁻¹ * vertices 0, element.val⁻¹ * vertices 1]) =
    representation element.val
        (cochain.val (fun index => element.val⁻¹ * ![vertices 1, vertices 2] index)) -
      representation element.val
        (cochain.val (fun index => element.val⁻¹ * ![vertices 0, vertices 2] index)) +
      representation element.val
        (cochain.val (fun index => element.val⁻¹ * ![vertices 0, vertices 1] index))
  simp only [translatedPair]
  rw [map_add, map_sub]

def stabilizerTransportCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (source target : X) (transports : element.val • source = target) :
    cocycles (fixedPointLevel level source) representation →ₗ[ℂ]
      cocycles (fixedPointLevel level target) representation where
  toFun cycle := ⟨stabilizerTransportCochain level representation element source target
    transports 2 cycle.val, by
      funext vertices
      have vanishing := congrFun cycle.property
        (fun index => element.val⁻¹ * vertices index)
      have translatedTriple (first second third : RationalGL3) :
          (fun index : Fin 3 => element.val⁻¹ * ![first, second, third] index) =
            ![element.val⁻¹ * first, element.val⁻¹ * second, element.val⁻¹ * third] := by
        funext index
        fin_cases index <;> rfl
      change representation element.val
          (cycle.val.val (fun index => element.val⁻¹ *
            ![vertices 1, vertices 2, vertices 3] index)) -
        representation element.val
          (cycle.val.val (fun index => element.val⁻¹ *
            ![vertices 0, vertices 2, vertices 3] index)) +
        representation element.val
          (cycle.val.val (fun index => element.val⁻¹ *
            ![vertices 0, vertices 1, vertices 3] index)) -
        representation element.val
          (cycle.val.val (fun index => element.val⁻¹ *
            ![vertices 0, vertices 1, vertices 2] index)) = 0
      simp only [translatedTriple]
      rw [← map_sub, ← map_add, ← map_sub]
      change cycle.val.val ![element.val⁻¹ * vertices 1, element.val⁻¹ * vertices 2,
          element.val⁻¹ * vertices 3] -
        cycle.val.val ![element.val⁻¹ * vertices 0, element.val⁻¹ * vertices 2,
          element.val⁻¹ * vertices 3] +
        cycle.val.val ![element.val⁻¹ * vertices 0, element.val⁻¹ * vertices 1,
          element.val⁻¹ * vertices 3] -
        cycle.val.val ![element.val⁻¹ * vertices 0, element.val⁻¹ * vertices 1,
          element.val⁻¹ * vertices 2] = 0 at vanishing
      rw [vanishing, map_zero]⟩
  map_add' first second := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' scalar cycle := by
    apply Subtype.ext
    exact map_smul _ _ _

theorem stabilizerTransportCycle_boundaryMap (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (source target : X) (transports : element.val • source = target)
    (cochain : cochains (fixedPointLevel level source) representation 1) :
    stabilizerTransportCycle level representation element source target transports
        (boundaryMap _ _ cochain) =
      boundaryMap _ _
        (stabilizerTransportCochain level representation element source target transports 1
          cochain) := by
  apply Subtype.ext
  exact stabilizerTransportCochain_differentialOne level representation element source target
    transports cochain

def stabilizerTransportH2 (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (source target : X) (transports : element.val • source = target) :
    H2 (fixedPointLevel level source) representation →ₗ[ℂ]
      H2 (fixedPointLevel level target) representation :=
  (LinearMap.range (boundaryMap (fixedPointLevel level source) representation)).mapQ
    (LinearMap.range (boundaryMap (fixedPointLevel level target) representation))
    (stabilizerTransportCycle level representation element source target transports) (by
      rintro cycle ⟨primitive, rfl⟩
      exact ⟨stabilizerTransportCochain level representation element source target transports 1
        primitive, (stabilizerTransportCycle_boundaryMap level representation element source
          target transports primitive).symm⟩)

theorem stabilizerTransportH2_fixedPointH2 (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (source target : X) (transports : element.val • source = target)
    (coordinate : H2 level (functionRepresentation representation X)) :
    stabilizerTransportH2 level representation element source target transports
        (fixedPointH2 level representation source coordinate) =
      fixedPointH2 level representation target coordinate := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle
  apply congrArg (classOf (fixedPointLevel level target) representation)
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  change representation element.val
      (cycle.val.val (fun index => element.val⁻¹ * vertices index) source) =
    cycle.val.val vertices target
  have equivariance := congrFun (cycle.val.property element
    (fun index => element.val⁻¹ * vertices index)) target
  change cycle.val.val (fun index => element.val * (element.val⁻¹ * vertices index))
      target = representation element.val
        (cycle.val.val (fun index => element.val⁻¹ * vertices index)
          (element.val⁻¹ • target)) at equivariance
  simpa only [mul_inv_cancel_left, ← transports, inv_smul_smul] using equivariance.symm

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
