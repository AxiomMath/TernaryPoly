module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set
open SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)
  (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

include hU hcover in
/-- For every form degree, actual global equivariant forms resolve the genuine horizontal
Čech row of every small-indexed quotient open cover by literal restriction. -/
theorem globalForms_resolve_cech : ∀ n : ℕ, QuasiIso (formCechAugmentation ρ U n) :=
  fun n => formCechAugmentation_quasiIso_of_cover ρ U n hU hcover

end TernaryPoly.SmoothSingularGlobal
