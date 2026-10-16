module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section Restriction

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def restrictCochain (Γ H : Subgroup G) (inclusion : H ≤ Γ)
    (ρ : Representation ℂ G V) (degree : ℕ) (u : cochains Γ ρ degree) :
    cochains H ρ degree :=
  ⟨u.val, fun γ vertices => u.property ⟨γ.val, inclusion γ.property⟩ vertices⟩

def restrictCocycle (Γ H : Subgroup G) (inclusion : H ≤ Γ)
    (ρ : Representation ℂ G V) (c : cocycles Γ ρ) : cocycles H ρ :=
  ⟨restrictCochain Γ H inclusion ρ 2 c.val, c.property⟩

theorem restrictCochain_differentialOne (Γ H : Subgroup G) (inclusion : H ≤ Γ)
    (ρ : Representation ℂ G V) (u : cochains Γ ρ 1) :
    differentialOne H ρ (restrictCochain Γ H inclusion ρ 1 u) =
      restrictCochain Γ H inclusion ρ 2 (differentialOne Γ ρ u) := rfl

end Restriction

def edgeStabilizer (edge : Edges) : Subgroup RationalGL3 :=
  rationalLevel ⊓ MulAction.stabilizer RationalGL3 edge

def edgeOrbitRepresentative (edge : Edges) : Edges :=
  (Quotient.mk'' edge : MulAction.orbitRel.Quotient rationalLevel Edges).out

theorem edgeOrbitRepresentative_smul (γ : rationalLevel) (edge : Edges) :
    edgeOrbitRepresentative (γ.val • edge) = edgeOrbitRepresentative edge := by
  unfold edgeOrbitRepresentative
  change (Quotient.mk'' (γ • edge) :
    MulAction.orbitRel.Quotient rationalLevel Edges).out = _
  exact congrArg Quotient.out
    (MulAction.orbitRel.Quotient.quotient_smul_eq (g := γ) (a := edge))

theorem edgeTransport_exists (edge : Edges) :
    ∃ γ : rationalLevel, γ.val • edgeOrbitRepresentative edge = edge := by
  have related := Quotient.exact' (Quotient.out_eq
    (Quotient.mk'' edge : MulAction.orbitRel.Quotient rationalLevel Edges)).symm
  exact MulAction.mem_orbit_iff.mp related

def edgeTransport (edge : Edges) : rationalLevel :=
  Classical.choose (edgeTransport_exists edge)

theorem edgeTransport_smul (edge : Edges) :
    (edgeTransport edge).val • edgeOrbitRepresentative edge = edge :=
  Classical.choose_spec (edgeTransport_exists edge)

def descendEdgeCochain (n : ℕ) (χ : RankOneCharacter)
    (primitives : ∀ edge : Edges,
      cochains (edgeStabilizer edge) (rationalCoefficientComponent n χ) 1)
    (vertices : Fin 2 → RationalGL3) (edge : Edges) : HomogeneousPoly n :=
  rationalCoefficientComponent n χ (edgeTransport edge).val
    ((primitives (edgeOrbitRepresentative edge)).val
      (fun index => (edgeTransport edge).val⁻¹ * vertices index))

theorem descendEdgeCochain_pair (n : ℕ) (χ : RankOneCharacter)
    (primitives : ∀ edge : Edges,
      cochains (edgeStabilizer edge) (rationalCoefficientComponent n χ) 1)
    (first second : RationalGL3) (edge : Edges) :
    descendEdgeCochain n χ primitives ![first, second] edge =
      rationalCoefficientComponent n χ (edgeTransport edge).val
        ((primitives (edgeOrbitRepresentative edge)).val
          ![(edgeTransport edge).val⁻¹ * first, (edgeTransport edge).val⁻¹ * second]) := by
  unfold descendEdgeCochain
  apply congrArg (rationalCoefficientComponent n χ (edgeTransport edge).val)
  apply congrArg (primitives (edgeOrbitRepresentative edge)).val
  funext index
  fin_cases index <;> rfl

theorem descendEdgeCochain_diagonal (n : ℕ) (χ : RankOneCharacter)
    (primitives : ∀ edge : Edges,
      cochains (edgeStabilizer edge) (rationalCoefficientComponent n χ) 1)
    (γ : rationalLevel) (vertices : Fin 2 → RationalGL3) (edge : Edges) :
    descendEdgeCochain n χ primitives (fun index => γ.val * vertices index)
        (γ.val • edge) =
      rationalCoefficientComponent n χ γ.val
        (descendEdgeCochain n χ primitives vertices edge) := by
  let source := edgeTransport edge
  let target := edgeTransport (γ.val • edge)
  have target_edge : target.val • edgeOrbitRepresentative edge = γ.val • edge := by
    simpa only [edgeOrbitRepresentative_smul] using edgeTransport_smul (γ.val • edge)
  have stabilizes : (target⁻¹ * γ * source).val ∈
      MulAction.stabilizer RationalGL3 (edgeOrbitRepresentative edge) := by
    apply MulAction.mem_stabilizer_iff.mpr
    change (target.val⁻¹ * γ.val * source.val) • edgeOrbitRepresentative edge = _
    rw [mul_smul, mul_smul, edgeTransport_smul]
    rw [← target_edge, inv_smul_smul]
  let correction : edgeStabilizer (edgeOrbitRepresentative edge) :=
    ⟨(target⁻¹ * γ * source).val, ⟨(target⁻¹ * γ * source).property, stabilizes⟩⟩
  have shifted_vertices : (fun index => correction.val *
      (source.val⁻¹ * vertices index)) =
      (fun index => target.val⁻¹ * (γ.val * vertices index)) := by
    funext index
    change (target.val⁻¹ * γ.val * source.val) *
      (source.val⁻¹ * vertices index) = _
    simp only [mul_assoc, mul_inv_cancel_left]
  have equivariance := (primitives (edgeOrbitRepresentative edge)).property
    correction (fun index => source.val⁻¹ * vertices index)
  rw [shifted_vertices] at equivariance
  unfold descendEdgeCochain
  rw [edgeOrbitRepresentative_smul]
  change rationalCoefficientComponent n χ target.val
      ((primitives (edgeOrbitRepresentative edge)).val
        (fun index => target.val⁻¹ * (γ.val * vertices index))) = _
  rw [equivariance]
  rw [← Module.End.mul_apply, ← map_mul]
  have product_eq : target.val * correction.val = γ.val * source.val := by
    change target.val * (target.val⁻¹ * γ.val * source.val) = _
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  rw [product_eq, map_mul, Module.End.mul_apply]

def edgeCochainFromStabilizers (n : ℕ) (χ : RankOneCharacter)
    (primitives : ∀ edge : Edges,
      cochains (edgeStabilizer edge) (rationalCoefficientComponent n χ) 1) :
    EdgeCochains n χ 1 :=
  ⟨descendEdgeCochain n χ primitives, by
    intro γ vertices
    funext edge
    have diagonal := descendEdgeCochain_diagonal n χ primitives γ vertices
      (γ.val⁻¹ • edge)
    change descendEdgeCochain n χ primitives (fun index => γ.val * vertices index)
      edge = rationalCoefficientComponent n χ γ.val
        (descendEdgeCochain n χ primitives vertices (γ.val⁻¹ • edge))
    simpa only [smul_inv_smul] using diagonal⟩

theorem edgeCochainFromStabilizers_differential (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (primitives : ∀ edge : Edges,
      cochains (edgeStabilizer edge) (rationalCoefficientComponent n χ) 1)
    (primitive_eq : ∀ edge vertices,
      (differentialOne (edgeStabilizer edge) (rationalCoefficientComponent n χ)
        (primitives edge)).val vertices = c.val.val vertices)
    (vertices : Fin 3 → RationalGL3) (edge : Edges) :
    (differentialOne rationalLevel
      (functionRepresentation (rationalCoefficientComponent n χ) Edges)
      (edgeCochainFromStabilizers n χ primitives)).val vertices edge =
        c.val.val vertices := by
  let transport := edgeTransport edge
  have primitive := primitive_eq (edgeOrbitRepresentative edge)
    (fun index => transport.val⁻¹ * vertices index)
  have equivariance := c.val.property transport
    (fun index => transport.val⁻¹ * vertices index)
  have vertices_eq : (fun index => transport.val *
      (transport.val⁻¹ * vertices index)) = vertices := by
    funext index
    simp only [mul_inv_cancel_left]
  rw [vertices_eq] at equivariance
  change descendEdgeCochain n χ primitives ![vertices 1, vertices 2] edge -
    descendEdgeCochain n χ primitives ![vertices 0, vertices 2] edge +
    descendEdgeCochain n χ primitives ![vertices 0, vertices 1] edge = _
  rw [descendEdgeCochain_pair, descendEdgeCochain_pair, descendEdgeCochain_pair]
  change rationalCoefficientComponent n χ transport.val
      ((primitives (edgeOrbitRepresentative edge)).val
        ![transport.val⁻¹ * vertices 1, transport.val⁻¹ * vertices 2]) -
    rationalCoefficientComponent n χ transport.val
      ((primitives (edgeOrbitRepresentative edge)).val
        ![transport.val⁻¹ * vertices 0, transport.val⁻¹ * vertices 2]) +
    rationalCoefficientComponent n χ transport.val
      ((primitives (edgeOrbitRepresentative edge)).val
        ![transport.val⁻¹ * vertices 0, transport.val⁻¹ * vertices 1]) = _
  rw [← map_sub, ← map_add]
  change rationalCoefficientComponent n χ transport.val
    ((differentialOne (edgeStabilizer (edgeOrbitRepresentative edge))
      (rationalCoefficientComponent n χ)
      (primitives (edgeOrbitRepresentative edge))).val
      (fun index => transport.val⁻¹ * vertices index)) = _
  rw [primitive]
  exact equivariance.symm

theorem innerBoundary_of_stabilizer_primitives (n : ℕ) (χ : RankOneCharacter)
    (side : Side) (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (primitive_exists : ∀ edge : Edges,
      ∃ primitive : cochains (edgeStabilizer edge) (rationalCoefficientComponent n χ) 1,
        ∀ vertices, (differentialOne (edgeStabilizer edge)
          (rationalCoefficientComponent n χ) primitive).val vertices = c.val.val vertices) :
    InnerBoundary n χ side
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side)
        (restrictionCocycle n χ side c)) := by
  classical
  let primitives := fun edge => Classical.choose (primitive_exists edge)
  apply (innerBoundary_globalCoordinates_iff n χ side c).mpr
  refine ⟨edgeCochainFromStabilizers n χ primitives, ?_⟩
  intro vertices edge
  exact (edgeCochainFromStabilizers_differential n χ c primitives
    (fun selected => Classical.choose_spec (primitive_exists selected)) vertices edge).symm

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
