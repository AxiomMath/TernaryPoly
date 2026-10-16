module

public import TernaryPeriodPolynomials.SymmetricSpace.CoveringGeneral
public import TernaryPeriodPolynomials.SymmetricSpace.CoveringTopology
public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction

@[expose] public section


/-!
# General coercivity: admissible cover groups and their orbit spaces

Shared interface file of `GeneralCoercivity`.  `Admissible Γ` bundles
the three hypotheses on a subgroup `Γ` of `GL₃(ℝ)` that the coercivity estimate uses: determinant one,
a free action on the trace-one positive model `Space`, and finite compact transporters.  The orbit space
`OrbitSpace Γ` is the genuine quotient of `Space` by the action of `Γ`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open Topology Set

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceCharts

/-- The model `Space` is second countable, being homeomorphic to an open subset of `ℝ⁵`. -/
instance instSecondCountableTopologySpace : SecondCountableTopology Space :=
  chartHomeomorph.isEmbedding.secondCountableTopology

/-- The congruence action of `GL₃(ℝ)` on the model `Space` is continuous in the point. -/
instance instContinuousConstSMulRealGL : ContinuousConstSMul RealGL Space :=
  ⟨continuous_act⟩

/-- Hence so is the action of every subgroup. -/
instance instContinuousConstSMulSubgroup (Γ : Subgroup RealGL) : ContinuousConstSMul Γ Space :=
  ⟨fun γ => continuous_act (γ : RealGL)⟩

/-- Subgroups of `GL₃(ℝ)` of determinant one acting freely and properly discontinuously (finite
compact transporters) on the actual trace-one positive model `Space`. -/
structure Admissible (Γ : Subgroup RealGL) : Prop where
  det_one : ∀ g ∈ Γ, g.val.det = 1
  free : ∀ g ∈ Γ, ∀ S : Space, act g S = S → g = 1
  transporters : ∀ C D : Set Space, IsCompact C → IsCompact D →
    {g : Γ | ((g • ·) '' C ∩ D).Nonempty}.Finite

/-- The genuine orbit space of the action of `Γ` on `Space`. -/
abbrev OrbitSpace (Γ : Subgroup RealGL) := Quotient (MulAction.orbitRel Γ Space)

/-- The orbit projection. -/
def proj (Γ : Subgroup RealGL) : Space → OrbitSpace Γ := Quotient.mk _

variable {Γ : Subgroup RealGL}

theorem proj_smul (γ : Γ) (S : Space) : proj Γ (γ • S) = proj Γ S :=
  Quotient.sound ⟨γ, rfl⟩

theorem proj_eq_iff {S T : Space} : proj Γ S = proj Γ T ↔ ∃ γ : Γ, γ • S = T := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := (MulAction.orbitRel_apply).mp (Quotient.exact h)
    exact ⟨γ⁻¹, by rw [← hγ, inv_smul_smul]⟩
  · rintro ⟨γ, rfl⟩
    exact (proj_smul γ S).symm

theorem proj_surjective : Function.Surjective (proj Γ) := Quotient.mk_surjective

theorem continuous_proj : Continuous (proj Γ) := continuous_quotient_mk'

namespace Admissible

variable (h : Admissible Γ)
include h

theorem free' (g : Γ) (S : Space) (hS : g • S = S) : g = 1 :=
  Subtype.ext (h.free g.1 g.2 S hS)

theorem transporters' : ∀ C D : Set Space, IsCompact C → IsCompact D →
    {g : Γ | ((g • ·) '' C ∩ D).Nonempty}.Finite := h.transporters

/-- The orbit projection of an admissible group is a quotient covering map. -/
theorem quotientCovering : IsQuotientCoveringMap (proj Γ) Γ :=
  quotientCovering_of_finite_transporters h.transporters h.free'

theorem coveringMap : IsCoveringMap (proj Γ) := h.quotientCovering.isCoveringMap

theorem isOpenMap_proj : IsOpenMap (proj Γ) := h.coveringMap.isLocalHomeomorph.isOpenMap

theorem t2 : T2Space (OrbitSpace Γ) := quotient_t2_of_finite_transporters h.transporters

end Admissible

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
