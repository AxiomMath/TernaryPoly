module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialPathIndependence.Helpers

variable {Ambient Coefficient : Type} [Group Ambient] [AddCommGroup Coefficient] [Module ℂ Coefficient]

def vertexMap (level : Subgroup Ambient) (vertex : Ambient) : level :=
  ⟨vertex * (Quotient.out (Quotient.mk (QuotientGroup.rightRel level) vertex))⁻¹,
    QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq _))⟩

theorem vertexMap_equivariant (level : Subgroup Ambient) (gamma : level) (vertex : Ambient) :
    vertexMap level (gamma.val * vertex) = gamma * vertexMap level vertex := by
  have quotient_eq : Quotient.mk (QuotientGroup.rightRel level) (gamma.val * vertex) =
      Quotient.mk (QuotientGroup.rightRel level) vertex := by
    apply Eq.symm
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using gamma.property
  apply Subtype.ext
  change (gamma.val * vertex) *
      (Quotient.out (Quotient.mk (QuotientGroup.rightRel level) (gamma.val * vertex)))⁻¹ =
    gamma.val * (vertex *
      (Quotient.out (Quotient.mk (QuotientGroup.rightRel level) vertex))⁻¹)
  rw [quotient_eq, mul_assoc]

theorem cocycle_equivariant (level : Subgroup Ambient) (action : Representation ℂ Ambient Coefficient)
    (cocycle : cocycles level action) (gamma : level) (first second third : Ambient) :
    cocycle.val.val ![gamma.val * first, gamma.val * second, gamma.val * third] =
      action gamma.val (cocycle.val.val ![first, second, third]) := by
  have vector_eq : (fun index => gamma.val * ![first, second, third] index) =
      ![gamma.val * first, gamma.val * second, gamma.val * third] := by
    funext index
    fin_cases index <;> rfl
  simpa only [vector_eq] using cocycle.val.property gamma ![first, second, third]

theorem cocycle_identity (level : Subgroup Ambient) (action : Representation ℂ Ambient Coefficient)
    (cocycle : cocycles level action) (first second third fourth : Ambient) :
    cocycle.val.val ![second, third, fourth] -
      cocycle.val.val ![first, third, fourth] +
      cocycle.val.val ![first, second, fourth] -
      cocycle.val.val ![first, second, third] = 0 := by
  exact congrFun cocycle.property ![first, second, third, fourth]

theorem cocycle_rearrange (level : Subgroup Ambient) (action : Representation ℂ Ambient Coefficient)
    (cocycle : cocycles level action) (first second third fourth : Ambient) :
    cocycle.val.val ![second, third, fourth] =
      cocycle.val.val ![first, third, fourth] -
      cocycle.val.val ![first, second, fourth] +
      cocycle.val.val ![first, second, third] := by
  calc
    _ = (cocycle.val.val ![second, third, fourth] -
        cocycle.val.val ![first, third, fourth] +
        cocycle.val.val ![first, second, fourth] -
        cocycle.val.val ![first, second, third]) +
      cocycle.val.val ![first, third, fourth] -
      cocycle.val.val ![first, second, fourth] +
      cocycle.val.val ![first, second, third] := by abel
    _ = _ := by rw [cocycle_identity]; abel

theorem boundary_of_subgroup_boundary (level : Subgroup Ambient) (action : Representation ℂ Ambient Coefficient)
    (cocycle : cocycles level action) (primitive : level → level → Coefficient)
    (primitive_equivariant : ∀ gamma first second,
      primitive (gamma * first) (gamma * second) = action gamma.val (primitive first second))
    (primitive_boundary : ∀ first second third : level,
      primitive second third - primitive first third + primitive first second =
        cocycle.val.val ![first.val, second.val, third.val]) :
    ∃ cochain : cochains level action 1, boundaryMap level action cochain = cocycle := by
  let retract := vertexMap level
  have retract_eq (gamma : level) (vertex : Ambient) :
      retract (gamma.val * vertex) = gamma * retract vertex :=
    vertexMap_equivariant level gamma vertex
  let cochain : cochains level action 1 := ⟨fun vertices =>
    primitive (retract (vertices 0)) (retract (vertices 1)) +
      cocycle.val.val ![(retract (vertices 0)).val, vertices 0, vertices 1] -
      cocycle.val.val ![(retract (vertices 0)).val, (retract (vertices 1)).val, vertices 1], by
    intro gamma vertices
    change primitive (retract (gamma.val * vertices 0)) (retract (gamma.val * vertices 1)) +
        cocycle.val.val ![(retract (gamma.val * vertices 0)).val,
          gamma.val * vertices 0, gamma.val * vertices 1] -
        cocycle.val.val ![(retract (gamma.val * vertices 0)).val,
          (retract (gamma.val * vertices 1)).val, gamma.val * vertices 1] = _
    rw [retract_eq, retract_eq, primitive_equivariant]
    change action gamma.val (primitive (retract (vertices 0)) (retract (vertices 1))) +
        cocycle.val.val ![gamma.val * (retract (vertices 0)).val,
          gamma.val * vertices 0, gamma.val * vertices 1] -
        cocycle.val.val ![gamma.val * (retract (vertices 0)).val,
          gamma.val * (retract (vertices 1)).val, gamma.val * vertices 1] = _
    rw [cocycle_equivariant, cocycle_equivariant, map_sub, map_add]⟩
  refine ⟨cochain, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  change (primitive (retract (vertices 1)) (retract (vertices 2)) +
      cocycle.val.val ![(retract (vertices 1)).val, vertices 1, vertices 2] -
      cocycle.val.val ![(retract (vertices 1)).val, (retract (vertices 2)).val, vertices 2]) -
    (primitive (retract (vertices 0)) (retract (vertices 2)) +
      cocycle.val.val ![(retract (vertices 0)).val, vertices 0, vertices 2] -
      cocycle.val.val ![(retract (vertices 0)).val, (retract (vertices 2)).val, vertices 2]) +
    (primitive (retract (vertices 0)) (retract (vertices 1)) +
      cocycle.val.val ![(retract (vertices 0)).val, vertices 0, vertices 1] -
      cocycle.val.val ![(retract (vertices 0)).val, (retract (vertices 1)).val, vertices 1]) =
    cocycle.val.val vertices
  have first_identity := cocycle_rearrange level action cocycle
    (retract (vertices 0)).val (vertices 0) (vertices 1) (vertices 2)
  have second_identity := cocycle_rearrange level action cocycle
    (retract (vertices 0)).val (retract (vertices 1)).val (vertices 1) (vertices 2)
  have third_identity := cocycle_rearrange level action cocycle
    (retract (vertices 0)).val (retract (vertices 1)).val
    (retract (vertices 2)).val (vertices 2)
  have boundary_identity := primitive_boundary
    (retract (vertices 0)) (retract (vertices 1)) (retract (vertices 2))
  have vector_eq : ![vertices 0, vertices 1, vertices 2] = vertices := by
    funext index
    fin_cases index <;> rfl
  conv_rhs => rw [← vector_eq]
  rw [second_identity, third_identity, first_identity, ← boundary_identity]
  abel

theorem path_difference_cycle (first second : rationalLevel → EdgeChains)
    (first_path : IsPathFamily first) (second_path : IsPathFamily second)
    (gamma : rationalLevel) : GoodCycle (first gamma - second gamma) := by
  constructor
  · rw [map_sub, (first_path gamma).2, (second_path gamma).2, sub_self]
  · classical
    intro edge edge_mem
    rcases Finset.mem_union.mp (Finsupp.support_sub edge_mem) with first_mem | second_mem
    · exact (first_path gamma).1 edge first_mem
    · exact (second_path gamma).1 edge second_mem

def pathPrimitive {degree : ℕ} (functionalMap : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (first second : rationalLevel → EdgeChains) (left right : rationalLevel) :
    HomogeneousPoly degree :=
  rationalCoefficientComponent degree trivialCharacter left.val
    (functionalMap (first (left⁻¹ * right) - second (left⁻¹ * right)))

theorem pathPrimitive_equivariant {degree : ℕ} (functionalMap : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (first second : rationalLevel → EdgeChains) (gamma left right : rationalLevel) :
    pathPrimitive functionalMap first second (gamma * left) (gamma * right) =
      rationalCoefficientComponent degree trivialCharacter gamma.val
        (pathPrimitive functionalMap first second left right) := by
  unfold pathPrimitive
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, Subgroup.coe_mul,
    map_mul, Module.End.mul_apply]

theorem pathPrimitive_boundary {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (functionalMap : EdgeChains →ₗ[ℂ] HomogeneousPoly degree) (functional : IsPolynomialFunctional polynomial functionalMap)
    (first second : rationalLevel → EdgeChains)
    (first_path : IsPathFamily first) (second_path : IsPathFamily second)
    (first_cocycle second_cocycle :
      cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (first_realizes : RealizesPathClass functionalMap first first_cocycle)
    (second_realizes : RealizesPathClass functionalMap second second_cocycle)
    (left middle right : rationalLevel) :
    pathPrimitive functionalMap first second middle right - pathPrimitive functionalMap first second left right +
      pathPrimitive functionalMap first second left middle =
      (first_cocycle - second_cocycle).val.val ![left.val, middle.val, right.val] := by
  let action := rationalCoefficientComponent degree trivialCharacter
  have translated_difference := functional.1 (left⁻¹ * middle)
    (first (middle⁻¹ * right) - second (middle⁻¹ * right))
    (path_difference_cycle first second first_path second_path (middle⁻¹ * right))
  have action_eq (value : HomogeneousPoly degree) :
      action left.val (action (left⁻¹ * middle).val value) = action middle.val value := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  change action middle.val (functionalMap (first (middle⁻¹ * right) - second (middle⁻¹ * right))) -
      action left.val (functionalMap (first (left⁻¹ * right) - second (left⁻¹ * right))) +
      action left.val (functionalMap (first (left⁻¹ * middle) - second (left⁻¹ * middle))) =
    first_cocycle.val.val ![left.val, middle.val, right.val] -
      second_cocycle.val.val ![left.val, middle.val, right.val]
  rw [first_realizes, second_realizes, ← action_eq,
    ← translated_difference]
  simp only [map_add, map_sub]
  abel

end TernaryPeriodPolynomials.PolynomialPathIndependence.Helpers
