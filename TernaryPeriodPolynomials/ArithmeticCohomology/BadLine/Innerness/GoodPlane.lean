module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.PathDefect

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section Transport

variable {GroupType Coefficient : Type} [Group GroupType]
  [AddCommGroup Coefficient] [Module ℂ Coefficient]

def transportCochain (source target : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (transport : GroupType)
    (conjugate_mem : ∀ element : target,
      transport⁻¹ * element.val * transport ∈ source)
    (primitive : cochains source representation 1) :
    cochains target representation 1 :=
  ⟨fun vertices => representation transport
      (primitive.val (fun index => transport⁻¹ * vertices index)), by
    intro element vertices
    let correction : source :=
      ⟨transport⁻¹ * element.val * transport, conjugate_mem element⟩
    have shifted_vertices :
        (fun index => transport⁻¹ * (element.val * vertices index)) =
          fun index => correction.val * (transport⁻¹ * vertices index) := by
      funext index
      simp only [correction, mul_assoc, mul_inv_cancel_left]
    change representation transport
      (primitive.val (fun index => transport⁻¹ * (element.val * vertices index))) =
        representation element.val (representation transport
          (primitive.val (fun index => transport⁻¹ * vertices index)))
    rw [shifted_vertices, primitive.property correction]
    rw [← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul]
    congr 2
    change transport * (transport⁻¹ * element.val * transport) =
      element.val * transport
    simp only [← mul_assoc, mul_inv_cancel, one_mul]⟩

theorem transportCochain_differential (source target : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (transport : GroupType)
    (conjugate_mem : ∀ element : target,
      transport⁻¹ * element.val * transport ∈ source)
    (primitive : cochains source representation 1)
    (vertices : Fin 3 → GroupType) :
    (differentialOne target representation
      (transportCochain source target representation transport conjugate_mem primitive)).val
      vertices = representation transport
        ((differentialOne source representation primitive).val
          (fun index => transport⁻¹ * vertices index)) := by
  change representation transport
      (primitive.val (fun index => transport⁻¹ * ![vertices 1, vertices 2] index)) -
    representation transport
      (primitive.val (fun index => transport⁻¹ * ![vertices 0, vertices 2] index)) +
    representation transport
      (primitive.val (fun index => transport⁻¹ * ![vertices 0, vertices 1] index)) = _
  have pair_eq (first second : GroupType) :
      (fun index => transport⁻¹ * ![first, second] index) =
        ![transport⁻¹ * first, transport⁻¹ * second] := by
    funext index
    fin_cases index <;> rfl
  rw [pair_eq, pair_eq, pair_eq, ← map_sub, ← map_add]
  rfl

theorem cocycle_primitive_transport (ambient source target : Subgroup GroupType)
    (representation : Representation ℂ GroupType Coefficient)
    (cocycle : cocycles ambient representation) (transport : ambient)
    (conjugate_mem : ∀ element : target,
      transport.val⁻¹ * element.val * transport.val ∈ source)
    (primitive : cochains source representation 1)
    (primitive_eq : ∀ vertices,
      (differentialOne source representation primitive).val vertices =
        cocycle.val.val vertices) :
    ∃ result : cochains target representation 1, ∀ vertices,
      (differentialOne target representation result).val vertices =
        cocycle.val.val vertices := by
  refine ⟨transportCochain source target representation transport.val conjugate_mem
    primitive, ?_⟩
  intro vertices
  rw [transportCochain_differential, primitive_eq]
  have equivariance := cocycle.val.property transport
    (fun index => transport.val⁻¹ * vertices index)
  have vertices_eq :
      (fun index => transport.val * (transport.val⁻¹ * vertices index)) = vertices := by
    funext index
    simp only [mul_inv_cancel_left]
  rw [vertices_eq] at equivariance
  exact equivariance.symm

end Transport

theorem edgeStabilizer_fixes_base (edge : Edges)
    (plane_eq : endpoint .plane edge = QuotientGroup.mk swapLastTwo)
    (element : edgeStabilizer edge) :
    translateVertex element.val pathBase = pathBase := by
  have fixes_edge : element.val • edge = edge := element.property.2
  have fixes_plane := congrArg (endpoint .plane) fixes_edge
  rw [endpoint_smul, plane_eq] at fixes_plane
  exact congrArg Sum.inl fixes_plane

theorem pathClass_primitive_at_base_plane {degree : ℕ}
    (polynomial : HomogeneousPoly degree)
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (functional_property : IsPolynomialFunctional polynomial functional)
    (paths : rationalLevel → EdgeChains)
    (cocycle : cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter))
    (path_property : IsPathFamily paths)
    (realization : RealizesPathClass functional paths cocycle)
    (edge : Edges)
    (plane_eq : endpoint .plane edge = QuotientGroup.mk swapLastTwo) :
    ∃ primitive : cochains (edgeStabilizer edge)
        (rationalCoefficientComponent degree trivialCharacter) 1,
      ∀ vertices, (differentialOne (edgeStabilizer edge)
        (rationalCoefficientComponent degree trivialCharacter) primitive).val vertices =
          cocycle.val.val vertices := by
  obtain ⟨primitive, primitive_eq⟩ := pathClass_coboundary_on_base_stabilizer polynomial
    functional functional_property paths cocycle path_property realization
    (edgeStabilizer edge) inf_le_left (edgeStabilizer_fixes_base edge plane_eq)
  refine ⟨primitive, ?_⟩
  intro vertices
  exact congrFun (congrArg Subtype.val primitive_eq) vertices

theorem pathClass_primitive_at_plane_orbit {degree : ℕ}
    (polynomial : HomogeneousPoly degree)
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (functional_property : IsPolynomialFunctional polynomial functional)
    (paths : rationalLevel → EdgeChains)
    (cocycle : cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter))
    (path_property : IsPathFamily paths)
    (realization : RealizesPathClass functional paths cocycle)
    (edge : Edges)
    (plane_orbit : ∃ transport : rationalLevel,
      endpoint .plane edge = transport.val • QuotientGroup.mk swapLastTwo) :
    ∃ primitive : cochains (edgeStabilizer edge)
        (rationalCoefficientComponent degree trivialCharacter) 1,
      ∀ vertices, (differentialOne (edgeStabilizer edge)
        (rationalCoefficientComponent degree trivialCharacter) primitive).val vertices =
          cocycle.val.val vertices := by
  obtain ⟨transport, plane_eq⟩ := plane_orbit
  let source_edge := transport.val⁻¹ • edge
  have source_plane : endpoint .plane source_edge = QuotientGroup.mk swapLastTwo := by
    simp only [source_edge, endpoint_smul, plane_eq, inv_smul_smul]
  obtain ⟨primitive, primitive_eq⟩ := pathClass_primitive_at_base_plane polynomial
    functional functional_property paths cocycle path_property realization
    source_edge source_plane
  apply cocycle_primitive_transport rationalLevel (edgeStabilizer source_edge)
    (edgeStabilizer edge) (rationalCoefficientComponent degree trivialCharacter)
    cocycle transport _ primitive primitive_eq
  intro element
  refine ⟨rationalLevel.mul_mem
    (rationalLevel.mul_mem (rationalLevel.inv_mem transport.property) element.property.1)
    transport.property, ?_⟩
  have fixes_edge : element.val • edge = edge := element.property.2
  change (transport.val⁻¹ * element.val * transport.val) •
    (transport.val⁻¹ • edge) = transport.val⁻¹ • edge
  rw [mul_smul, mul_smul, smul_inv_smul, fixes_edge]

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
