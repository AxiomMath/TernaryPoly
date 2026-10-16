module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.PrimitiveExtension

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

variable {GroupType Vector FiniteGroup : Type}
  [Group GroupType] [AddCommGroup Vector] [Module ℂ Vector]
  [Group FiniteGroup] [Fintype FiniteGroup]

def finiteAveragePrimitive (representation : Representation ℂ GroupType Vector)
    (diagonal : FiniteGroup →* GroupType) (primitive : (Fin 2 → GroupType) → Vector)
    (vertices : Fin 2 → GroupType) :
    Vector := (Fintype.card FiniteGroup : ℂ)⁻¹ •
      ∑ index, representation (diagonal index)
        (primitive (fun position => (diagonal index)⁻¹ * vertices position))

theorem finiteAveragePrimitive_diagonal (representation : Representation ℂ GroupType Vector)
    (diagonal : FiniteGroup →* GroupType) (primitive : (Fin 2 → GroupType) → Vector)
    (matrix : FiniteGroup) (vertices : Fin 2 → GroupType) :
    finiteAveragePrimitive representation diagonal primitive
        (fun position => diagonal matrix * vertices position) =
      representation (diagonal matrix)
        (finiteAveragePrimitive representation diagonal primitive vertices) := by
  unfold finiteAveragePrimitive
  rw [map_smul, map_sum]
  congr 1
  have reindex := Equiv.sum_comp (Equiv.mulLeft matrix)
    (fun index => representation (diagonal index)
      (primitive (fun position => (diagonal index)⁻¹ *
        (diagonal matrix * vertices position))))
  rw [← reindex]
  apply Finset.sum_congr rfl
  intro index _
  change representation (diagonal (matrix * index))
    (primitive (fun position => (diagonal (matrix * index))⁻¹ *
      (diagonal matrix * vertices position))) = _
  simp only [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
    Module.End.mul_apply]

theorem finiteAveragePrimitive_normal (normal_subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Vector)
    (diagonal : FiniteGroup →* GroupType)
    (normalizes : ∀ index, ∀ matrix : normal_subgroup,
      (diagonal index)⁻¹ * matrix.val * diagonal index ∈ normal_subgroup)
    (primitive : cochains normal_subgroup representation 1)
    (matrix : normal_subgroup) (vertices : Fin 2 → GroupType) :
    finiteAveragePrimitive representation diagonal primitive.val
        (fun position => matrix.val * vertices position) =
      representation matrix.val
        (finiteAveragePrimitive representation diagonal primitive.val vertices) := by
  unfold finiteAveragePrimitive
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  let conjugate : normal_subgroup :=
    ⟨(diagonal index)⁻¹ * matrix.val * diagonal index, normalizes index matrix⟩
  have vertices_eq :
      (fun position => (diagonal index)⁻¹ * (matrix.val * vertices position)) =
        (fun position => conjugate.val * ((diagonal index)⁻¹ * vertices position)) := by
    funext position
    dsimp only [conjugate]
    group
  rw [vertices_eq, primitive.property]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  dsimp only [conjugate]
  group

/-- Averaging over a finite complement promotes a subgroup primitive to a primitive
on the whole extension. All equalities hold on the ambient homogeneous resolution. -/
theorem finiteExtension_exists_primitive (subgroup normal_subgroup : Subgroup GroupType)
    (representation : Representation ℂ GroupType Vector)
    (diagonal : FiniteGroup →* GroupType)
    (diagonal_mem : ∀ index, diagonal index ∈ subgroup)
    (normalizes : ∀ index, ∀ matrix : normal_subgroup,
      (diagonal index)⁻¹ * matrix.val * diagonal index ∈ normal_subgroup)
    (decomposes : ∀ matrix : subgroup, ∃ normal : normal_subgroup,
      ∃ index, normal.val * diagonal index = matrix.val)
    (cocycle : cocycles subgroup representation)
    (primitive : cochains normal_subgroup representation 1)
    (primitive_differential : ∀ vertices,
      (differentialOne normal_subgroup representation primitive).val vertices =
        cocycle.val.val vertices) :
    ∃ result : cochains subgroup representation 1,
      differentialOne subgroup representation result = cocycle.val := by
  let averaged : cochains subgroup representation 1 :=
    ⟨finiteAveragePrimitive representation diagonal primitive.val, by
      intro matrix vertices
      obtain ⟨normal, index, matrix_eq⟩ := decomposes matrix
      rw [← matrix_eq]
      have vertices_eq :
          (fun position => (normal.val * diagonal index) * vertices position) =
            (fun position => normal.val * (diagonal index * vertices position)) := by
        funext position
        exact mul_assoc _ _ _
      rw [vertices_eq, finiteAveragePrimitive_normal normal_subgroup representation diagonal
        normalizes primitive, finiteAveragePrimitive_diagonal, map_mul, Module.End.mul_apply]⟩
  refine ⟨averaged, ?_⟩
  apply Subtype.ext
  funext vertices
  have term (index : FiniteGroup) :
      representation (diagonal index)
        (primitive.val ![(diagonal index)⁻¹ * vertices 1, (diagonal index)⁻¹ * vertices 2]) -
      representation (diagonal index)
        (primitive.val ![(diagonal index)⁻¹ * vertices 0, (diagonal index)⁻¹ * vertices 2]) +
      representation (diagonal index)
        (primitive.val ![ (diagonal index)⁻¹ * vertices 0, (diagonal index)⁻¹ * vertices 1]) =
      cocycle.val.val vertices := by
    rw [← map_sub, ← map_add]
    have differential := primitive_differential
      (fun position => (diagonal index)⁻¹ * vertices position)
    change primitive.val ![(diagonal index)⁻¹ * vertices 1, (diagonal index)⁻¹ * vertices 2] -
      primitive.val ![(diagonal index)⁻¹ * vertices 0, (diagonal index)⁻¹ * vertices 2] +
      primitive.val ![(diagonal index)⁻¹ * vertices 0, (diagonal index)⁻¹ * vertices 1] = _
      at differential
    rw [differential]
    have equivariance := cocycle.val.property
      ⟨diagonal index, diagonal_mem index⟩
      (fun position => (diagonal index)⁻¹ * vertices position)
    simpa only [mul_inv_cancel_left] using equivariance.symm
  change finiteAveragePrimitive representation diagonal primitive.val ![vertices 1, vertices 2] -
    finiteAveragePrimitive representation diagonal primitive.val ![vertices 0, vertices 2] +
    finiteAveragePrimitive representation diagonal primitive.val ![vertices 0, vertices 1] = _
  have translated_pair (index : FiniteGroup) (first second : GroupType) :
      (fun position => (diagonal index)⁻¹ * (![first, second] : Fin 2 → GroupType) position) =
        ![(diagonal index)⁻¹ * first, (diagonal index)⁻¹ * second] := by
    funext position
    fin_cases position <;> rfl
  simp only [finiteAveragePrimitive, translated_pair, ← smul_sub, ← smul_add,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, term, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero (α := FiniteGroup)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
