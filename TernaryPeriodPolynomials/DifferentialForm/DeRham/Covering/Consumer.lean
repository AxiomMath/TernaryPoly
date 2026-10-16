module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.LocalSystem

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- Downstream local-coefficient exactness interface, with arbitrary actual quotient opens. -/
theorem covering_deRham_locally_exact {U : Set OrbitSpace} (hU : IsOpen U)
    {q : OrbitSpace} (hq : q ∈ U) :
    ∃ V : Set OrbitSpace, ∃ hV : IsOpen V, q ∈ V ∧ ∃ hVU : V ⊆ U,
      ∀ (n : ℕ) (w : EquivariantForm ρ U (n + 1)), differential ρ hU (n + 1) w = 0 →
        ∃ z : EquivariantForm ρ V n,
          differential ρ hV n z = restrictEquivariant ρ hVU (n + 1) w :=
  quotient_local_poincare ρ hU hq

/-- Downstream chart comparison is an isomorphism of the literal complexes. -/
def covering_deRham_chart_iso (S : Space) :
    coveringComplex ρ (quotientChart S).open_source ≅ complex (F := F) (quotientChart S).open_target :=
  chartComplexIso ρ S

/-- Compact support is measured on the actual quotient and preserved by the actual differential. -/
theorem covering_deRham_compact_support {U : Set OrbitSpace} (hU : IsOpen U)
    (n : ℕ) (w : EquivariantForm ρ U n) (hw : HasQuotientCompactSupport ρ w) :
    HasQuotientCompactSupport ρ (differential ρ hU n w) ∧
      quotientSupport (differential ρ hU n w) ⊆ quotientSupport w :=
  ⟨hasQuotientCompactSupport_differential ρ hU w hw, quotientSupport_differential hU w⟩

/-- The actual global compact-support-to-ordinary cochain map. -/
def globalCompactInclusion : globalCompactComplex ρ ⟶ globalComplex ρ :=
  compactInclusion ρ isOpen_univ

end TernaryPoly.SmoothCoveringDeRham
