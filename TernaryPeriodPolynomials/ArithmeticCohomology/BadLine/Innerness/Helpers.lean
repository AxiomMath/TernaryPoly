module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def endpointCochain (n : ℕ) (χ : RankOneCharacter) (side : Side) (degree : ℕ)
    (u : MaximalCochains n χ side degree) : EdgeCochains n χ degree :=
  ⟨fun vertices edge => u.val vertices (endpoint side edge), by
    intro γ vertices
    funext edge
    have witness := congrFun (u.property γ vertices) (endpoint side edge)
    change u.val (fun index => γ.val * vertices index) (endpoint side edge) =
      rationalCoefficientComponent n χ γ.val
        (u.val vertices (γ.val⁻¹ • endpoint side edge)) at witness
    change u.val (fun index => γ.val * vertices index) (endpoint side edge) =
      rationalCoefficientComponent n χ γ.val
        (u.val vertices (endpoint side (γ.val⁻¹ • edge)))
    simpa only [endpoint_smul] using witness⟩

theorem endpointCochain_differentialOne (n : ℕ) (χ : RankOneCharacter)
    (side : Side) (u : MaximalCochains n χ side 1) (vertices : Fin 3 → RationalGL3)
    (edge : Edges) :
    (differentialOne rationalLevel
      (functionRepresentation (rationalCoefficientComponent n χ) Edges)
      (endpointCochain n χ side 1 u)).val vertices edge =
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) side) u).val vertices
      (endpoint side edge) := rfl

theorem innerBoundary_globalCoordinates_iff (n : ℕ) (χ : RankOneCharacter)
    (side : Side) (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    InnerBoundary n χ side
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side)
        (restrictionCocycle n χ side c)) ↔
    ∃ u : EdgeCochains n χ 1, ∀ vertices edge,
      c.val.val vertices =
        (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n χ) Edges) u).val
          vertices edge := by
  constructor
  · rintro ⟨z, sameClass, u, hu⟩
    have differenceBoundary : z - restrictionCocycle n χ side c ∈
        LinearMap.range (boundaryMap rationalLevel
          (flagRepresentation (rationalCoefficientComponent n χ) side)) :=
      (Submodule.Quotient.eq _).mp sameClass
    obtain ⟨v, hv⟩ := differenceBoundary
    refine ⟨u - endpointCochain n χ side 1 v, ?_⟩
    intro vertices edge
    have hv' := congrFun (congrFun (congrArg (fun value => value.val.val) hv)
      vertices) (endpoint side edge)
    change (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) side) v).val
      vertices (endpoint side edge) =
      z.val.val vertices (endpoint side edge) - c.val.val vertices at hv'
    have subtract_eval :
        (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n χ) Edges)
          (u - endpointCochain n χ side 1 v)).val vertices edge =
        (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n χ) Edges) u).val
          vertices edge -
        (differentialOne rationalLevel
          (functionRepresentation (rationalCoefficientComponent n χ) Edges)
          (endpointCochain n χ side 1 v)).val vertices edge := by
      change (u.val ![vertices 1, vertices 2] edge -
          v.val ![vertices 1, vertices 2] (endpoint side edge)) -
        (u.val ![vertices 0, vertices 2] edge -
          v.val ![vertices 0, vertices 2] (endpoint side edge)) +
        (u.val ![vertices 0, vertices 1] edge -
          v.val ![vertices 0, vertices 1] (endpoint side edge)) =
        (u.val ![vertices 1, vertices 2] edge - u.val ![vertices 0, vertices 2] edge +
          u.val ![vertices 0, vertices 1] edge) -
        (v.val ![vertices 1, vertices 2] (endpoint side edge) -
          v.val ![vertices 0, vertices 2] (endpoint side edge) +
          v.val ![vertices 0, vertices 1] (endpoint side edge))
      abel
    rw [subtract_eval]
    rw [endpointCochain_differentialOne, hv', ← hu]
    abel
  · rintro ⟨u, hu⟩
    exact ⟨restrictionCocycle n χ side c, rfl, u, hu⟩

section AmbientHomotopy

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def cosetRepresentative (Γ : Subgroup G) (coset : G ⧸ Γ) : G := by
  classical
  exact if coset = QuotientGroup.mk (1 : G) then 1 else coset.out

theorem cosetRepresentative_mk (Γ : Subgroup G) (coset : G ⧸ Γ) :
    QuotientGroup.mk (cosetRepresentative Γ coset) = coset := by
  classical
  unfold cosetRepresentative
  split_ifs with isIdentity
  · exact isIdentity.symm
  · exact QuotientGroup.out_eq' coset

def ambientRetraction (Γ : Subgroup G) (vertex : G) : Γ :=
  ⟨vertex * cosetRepresentative Γ (QuotientGroup.mk vertex⁻¹), by
    have representative := (QuotientGroup.eq.mp
      (cosetRepresentative_mk Γ (QuotientGroup.mk vertex⁻¹)).symm)
    simpa only [inv_inv] using representative⟩

theorem ambientRetraction_equivariant (Γ : Subgroup G) (γ : Γ) (vertex : G) :
    ambientRetraction Γ (γ.val * vertex) = γ * ambientRetraction Γ vertex := by
  apply Subtype.ext
  have sameCoset : QuotientGroup.mk ((γ.val * vertex)⁻¹) =
      (QuotientGroup.mk vertex⁻¹ : G ⧸ Γ) := by
    apply QuotientGroup.eq.mpr
    simpa only [inv_inv, mul_assoc, mul_inv_cancel, mul_one] using γ.property
  change γ.val * vertex * cosetRepresentative Γ (QuotientGroup.mk ((γ.val * vertex)⁻¹)) =
    γ.val * (vertex * cosetRepresentative Γ (QuotientGroup.mk vertex⁻¹))
  rw [sameCoset, mul_assoc]

theorem ambientRetraction_subgroup (Γ : Subgroup G) (vertex : Γ) :
    ambientRetraction Γ vertex.val = vertex := by
  classical
  apply Subtype.ext
  have identityCoset : (QuotientGroup.mk vertex.val⁻¹ : G ⧸ Γ) =
      QuotientGroup.mk (1 : G) := by
    apply QuotientGroup.eq.mpr
    simpa only [inv_inv, mul_one] using vertex.property
  change vertex.val * cosetRepresentative Γ (QuotientGroup.mk vertex.val⁻¹) = vertex.val
  simp [identityCoset, cosetRepresentative]

theorem cocycle_four_vertices (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (c : cocycles Γ ρ) (first second third fourth : G) :
    c.val.val ![second, third, fourth] - c.val.val ![first, third, fourth] +
      c.val.val ![first, second, fourth] - c.val.val ![first, second, third] = 0 :=
  congrFun c.property ![first, second, third, fourth]

def vertexHomotopy (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (c : cocycles Γ ρ) (retract : G → G)
    (equivariant : ∀ (γ : Γ) vertex, retract (γ.val * vertex) = γ.val * retract vertex) :
    cochains Γ ρ 1 :=
  ⟨fun vertices => c.val.val ![vertices 0, vertices 1, retract (vertices 1)] -
    c.val.val ![vertices 0, retract (vertices 0), retract (vertices 1)], by
    intro γ vertices
    have equivariance (first second third : G) :
        c.val.val ![γ.val * first, γ.val * second, γ.val * third] =
          ρ γ.val (c.val.val ![first, second, third]) := by
      have vertices_eq : (fun index => γ.val * ![first, second, third] index) =
          ![γ.val * first, γ.val * second, γ.val * third] := by
        funext index
        fin_cases index <;> rfl
      simpa only [vertices_eq] using c.val.property γ ![first, second, third]
    change c.val.val ![γ.val * vertices 0, γ.val * vertices 1,
        retract (γ.val * vertices 1)] -
      c.val.val ![γ.val * vertices 0, retract (γ.val * vertices 0),
        retract (γ.val * vertices 1)] = _
    rw [equivariant, equivariant, equivariance, equivariance, map_sub]⟩

theorem vertexHomotopy_differential (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (c : cocycles Γ ρ) (retract : G → G)
    (equivariant : ∀ (γ : Γ) vertex, retract (γ.val * vertex) = γ.val * retract vertex)
    (vertices : Fin 3 → G) :
    (differentialOne Γ ρ (vertexHomotopy Γ ρ c retract equivariant)).val vertices =
      c.val.val vertices - c.val.val (fun index => retract (vertices index)) := by
  have first := cocycle_four_vertices Γ ρ c
    (vertices 0) (vertices 1) (vertices 2) (retract (vertices 2))
  have second := cocycle_four_vertices Γ ρ c
    (vertices 0) (vertices 1) (retract (vertices 1)) (retract (vertices 2))
  have third := cocycle_four_vertices Γ ρ c
    (vertices 0) (retract (vertices 0)) (retract (vertices 1)) (retract (vertices 2))
  have vertices_eq : ![vertices 0, vertices 1, vertices 2] = vertices := by
    funext index
    fin_cases index <;> rfl
  have retract_eq : ![retract (vertices 0), retract (vertices 1),
      retract (vertices 2)] = fun index => retract (vertices index) := by
    funext index
    fin_cases index <;> rfl
  change (c.val.val ![vertices 1, vertices 2, retract (vertices 2)] -
      c.val.val ![vertices 1, retract (vertices 1), retract (vertices 2)]) -
    (c.val.val ![vertices 0, vertices 2, retract (vertices 2)] -
      c.val.val ![vertices 0, retract (vertices 0), retract (vertices 2)]) +
    (c.val.val ![vertices 0, vertices 1, retract (vertices 1)] -
      c.val.val ![vertices 0, retract (vertices 0), retract (vertices 1)]) = _
  conv_rhs => rw [← retract_eq, ← vertices_eq]
  apply sub_eq_zero.mp
  calc
    _ = (c.val.val ![vertices 1, vertices 2, retract (vertices 2)] -
          c.val.val ![vertices 0, vertices 2, retract (vertices 2)] +
          c.val.val ![vertices 0, vertices 1, retract (vertices 2)] -
          c.val.val ![vertices 0, vertices 1, vertices 2]) -
        (c.val.val ![vertices 1, retract (vertices 1), retract (vertices 2)] -
          c.val.val ![vertices 0, retract (vertices 1), retract (vertices 2)] +
          c.val.val ![vertices 0, vertices 1, retract (vertices 2)] -
          c.val.val ![vertices 0, vertices 1, retract (vertices 1)]) +
        (c.val.val ![retract (vertices 0), retract (vertices 1), retract (vertices 2)] -
          c.val.val ![vertices 0, retract (vertices 1), retract (vertices 2)] +
          c.val.val ![vertices 0, retract (vertices 0), retract (vertices 2)] -
          c.val.val ![vertices 0, retract (vertices 0), retract (vertices 1)]) := by abel
    _ = 0 := by rw [first, second, third]; abel

theorem coboundary_of_zero_on_subgroup_vertices (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (c : cocycles Γ ρ)
    (vanishing : ∀ vertices : Fin 3 → Γ, c.val.val (fun index => (vertices index).val) = 0) :
    ∃ u : cochains Γ ρ 1, differentialOne Γ ρ u = c.val := by
  let retract : G → G := fun vertex => (ambientRetraction Γ vertex).val
  have equivariant : ∀ (γ : Γ) vertex,
      retract (γ.val * vertex) = γ.val * retract vertex := by
    intro γ vertex
    exact congrArg Subtype.val (ambientRetraction_equivariant Γ γ vertex)
  refine ⟨vertexHomotopy Γ ρ c retract equivariant, ?_⟩
  apply Subtype.ext
  funext vertices
  rw [vertexHomotopy_differential]
  have zero_value := vanishing (fun index => ambientRetraction Γ (vertices index))
  change c.val.val vertices - c.val.val (fun index =>
    (ambientRetraction Γ (vertices index)).val) = c.val.val vertices
  rw [zero_value, sub_zero]

theorem classOf_eq_of_eq_on_subgroup_vertices (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (first second : cocycles Γ ρ)
    (sameValues : ∀ vertices : Fin 3 → Γ,
      first.val.val (fun index => (vertices index).val) =
        second.val.val (fun index => (vertices index).val)) :
    classOf Γ ρ first = classOf Γ ρ second := by
  apply (Submodule.Quotient.eq _).mpr
  have vanishing : ∀ vertices : Fin 3 → Γ,
      (first - second).val.val (fun index => (vertices index).val) = 0 := by
    intro vertices
    change first.val.val (fun index => (vertices index).val) -
      second.val.val (fun index => (vertices index).val) = 0
    exact sub_eq_zero.mpr (sameValues vertices)
  obtain ⟨u, hu⟩ := coboundary_of_zero_on_subgroup_vertices Γ ρ (first - second) vanishing
  refine ⟨u, ?_⟩
  exact Subtype.ext hu

end AmbientHomotopy

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
