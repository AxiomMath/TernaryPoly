module

public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperFinite
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Quotient
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Orbit.QuotientOpenEmbedding

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedQuotient
open Topology SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceRationalGluing
  SymmetricSpaceFlagCoordinates

variable (H : Subgroup IntegralGL)

/-- The actual interior arithmetic orbit space for the same subgroup. -/
abbrev InteriorOrbit := Quotient (MulAction.orbitRel H Space)

theorem embedding_equivariant (h : H) (S : Space) : embedding (h • S) = h • embedding S :=
  (integralAction_embedding h.val S).symm

/-- The actual inclusion of the interior arithmetic quotient into the bordified quotient. -/
def interiorEmbedding : InteriorOrbit H → QuotientSpace H :=
  OrbitQuotientOpenEmbedding.descend embedding (embedding_equivariant H)

@[simp] theorem interiorEmbedding_mk (S : Space) :
    interiorEmbedding H (Quotient.mk _ S) = interiorProjection H S := rfl

theorem interiorEmbedding_isOpenEmbedding : IsOpenEmbedding (interiorEmbedding H) :=
  OrbitQuotientOpenEmbedding.descend_isOpenEmbedding (embedding_equivariant H)
    embedding_isOpenEmbedding

theorem interiorEmbedding_dense : DenseRange (interiorEmbedding H) := by
  intro x
  apply closure_mono ?_ (interiorProjection_dense H x)
  rintro _ ⟨S,rfl⟩
  exact ⟨Quotient.mk _ S,rfl⟩

/-- The preimage of the actual arithmetic interior is exactly the positive-form locus. -/
theorem projection_preimage_interior :
    projection H ⁻¹' Set.range (interiorEmbedding H) = Set.range embedding := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨S,rfl⟩ := Quotient.mk_surjective y
    obtain ⟨h,hh⟩ := Quotient.exact hy
    refine ⟨h⁻¹ • S,?_⟩
    have hs := congrArg (fun z : Glued => h⁻¹ • z) hh
    rw [inv_smul_smul] at hs
    exact (embedding_equivariant H h⁻¹ S).trans hs.symm
  · rintro ⟨S,rfl⟩
    exact ⟨Quotient.mk _ S,rfl⟩

/-- The geometric boundary of the actual orbit bordification. -/
def boundary : Set (QuotientSpace H) := (Set.range (interiorEmbedding H))ᶜ

theorem boundary_closed : IsClosed (boundary H) :=
  (interiorEmbedding_isOpenEmbedding H).isOpen_range.isClosed_compl

theorem projection_preimage_boundary :
    projection H ⁻¹' boundary H = (Set.range embedding)ᶜ := by
  rw [boundary,Set.preimage_compl,projection_preimage_interior]

/-- On every rational chart, the actual quotient boundary consists of its two zero-root faces. -/
theorem chart_preimage_boundary (g : SymmetricSpaceRationalAction.RationalGL) :
    (projection H ∘ chart g) ⁻¹' boundary H =
      {p : Corner | p.2.1.val = 0 ∨ p.2.2.val = 0} := by
  rw [Set.preimage_comp,projection_preimage_boundary,Set.preimage_compl,chart_preimage_embedding]
  ext p
  simp only [Set.mem_compl_iff,cornerInterior,Set.mem_ofPred_eq,not_and_or,not_lt]
  constructor
  · intro h
    exact h.imp (fun h => le_antisymm h p.2.1.property) (fun h => le_antisymm h p.2.2.property)
  · intro h
    exact h.imp (fun h => h.le) (fun h => h.le)

end TernaryPoly.SymmetricSpaceBordifiedQuotient
