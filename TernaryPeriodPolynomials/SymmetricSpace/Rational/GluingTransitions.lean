module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingModels

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalGluing
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceLineBordification
open SymmetricSpaceBorelCorner TopologicalSpace

/-- Exactly the four actual extension cases selected by membership in the two real parabolics. -/
def extension (r : RealGL) : LocalExtension r := by
  classical
  exact if hp : r∈planeStabilizer then
    if hl : r∈lineStabilizer then borelModel ⟨r,⟨hp,hl⟩⟩ else planeModel ⟨r,hp⟩
  else if hl : r∈lineStabilizer then lineModel ⟨r,hl⟩ else interiorModel r

def domain (r : RealGL) : Opens Corner := (extension r).domain

def transition (r : RealGL) : domain r ≃ₜ domain r := (extension r).homeomorph

/-- The four cases have a single exact stratum criterion: a zero root requires its parabolic. -/
theorem mem_domain_iff (r : RealGL) (p : Corner) :
    p∈domain r ↔ (0<p.2.1.val ∨ r∈lineStabilizer) ∧ (0<p.2.2.val ∨ r∈planeStabilizer) := by
  classical
  unfold domain extension
  split_ifs with hp hl hl
  · simp [borelModel,hp,hl]
  · simp [planeModel,overlapDomain,hp,hl]
    rfl
  · simp [lineModel,lineOverlapDomain,hp,hl]
    rfl
  · simp [interiorModel,cornerInterior,hp,hl]
    rfl

theorem domain_inv (r : RealGL) : domain r⁻¹=domain r := by
  apply Opens.ext
  ext p
  change p∈domain r⁻¹ ↔ p∈domain r
  rw [mem_domain_iff,mem_domain_iff]
  simp only [Subgroup.inv_mem_iff]

theorem domain_one : domain 1=⊤ := by
  ext p
  simp [mem_domain_iff]

theorem interior_subset_domain (r : RealGL) : cornerInterior ⊆ domain r :=
  (extension r).interior_mem

def interiorPoint (r : RealGL) (S : Space) : domain r :=
  ⟨cornerEmbedding S,interior_subset_domain r (cornerHomeomorph S).property⟩

/-- Every chosen extension agrees exactly with the actual normalized congruence action. -/
theorem transition_interiorPoint (r : RealGL) (S : Space) :
    (transition r (interiorPoint r S)).val=cornerEmbedding (act r S) :=
  (extension r).embedding_apply S

theorem transition_pos1_iff (r : RealGL) (p : domain r) :
    0<(transition r p).val.2.1.val ↔ 0<p.val.2.1.val := (extension r).pos1_iff p

theorem transition_pos2_iff (r : RealGL) (p : domain r) :
    0<(transition r p).val.2.2.val ↔ 0<p.val.2.2.val := (extension r).pos2_iff p

theorem halfLine_zero_iff_not_pos (t : SymmetricSpaceFlagCoordinates.HalfLine) :
    t.val=0 ↔ ¬0<t.val := by
  constructor
  · intro h; simp [h]
  · intro h; exact le_antisymm (le_of_not_gt h) t.property

theorem transition_zero1_iff (r : RealGL) (p : domain r) :
    (transition r p).val.2.1.val=0 ↔ p.val.2.1.val=0 := by
  rw [halfLine_zero_iff_not_pos,halfLine_zero_iff_not_pos,transition_pos1_iff]

theorem transition_zero2_iff (r : RealGL) (p : domain r) :
    (transition r p).val.2.2.val=0 ↔ p.val.2.2.val=0 := by
  rw [halfLine_zero_iff_not_pos,halfLine_zero_iff_not_pos,transition_pos2_iff]

/-- Actual overlap intersections are carried to actual overlap intersections by subgroup cancellation. -/
theorem transition_inter (r s : RealGL) (p : domain r) (hp : p.val∈domain (s*r)) :
    (transition r p).val∈domain s := by
  rw [mem_domain_iff] at hp ⊢
  have h := (mem_domain_iff r p.val).mp p.property
  constructor
  · rcases hp.1 with hp|hs
    · exact Or.inl ((transition_pos1_iff r p).mpr hp)
    · rcases h.1 with h|hr
      · exact Or.inl ((transition_pos1_iff r p).mpr h)
      · exact Or.inr ((lineStabilizer.mul_mem_cancel_right hr).mp hs)
  · rcases hp.2 with hp|hs
    · exact Or.inl ((transition_pos2_iff r p).mpr hp)
    · rcases h.2 with h|hr
      · exact Or.inl ((transition_pos2_iff r p).mpr h)
      · exact Or.inr ((planeStabilizer.mul_mem_cancel_right hr).mp hs)

end TernaryPoly.SymmetricSpaceRationalGluing
