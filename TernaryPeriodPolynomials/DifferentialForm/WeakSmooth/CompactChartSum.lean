module

public import TernaryPeriodPolynomials.Analysis.Compact.ChartDetermination

@[expose] public section

/-! Finite sums of actual compact chart-supported quotient forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set SmoothCoveringDeRham SmoothLocalDeRham SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
variable {F ι : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (ρ : Representation ℝ DeckGroup F) (S : Space) (k : ℕ)

/-- The literal chart representative of a genuine compact global form is linear. -/
def compactChartRepresentative : CompactSupportForm ρ univ k →ₗ[ℝ]
    Form (F := F) (quotientChart S).target k :=
  (globalChartRepresentative ρ S k).comp (compactSupportSubmodule ρ univ k).subtype

/-- Finite sums preserve support in an actual prescribed quotient set. -/
theorem quotientSupport_compact_sum (s : Finset ι) (w : ι → CompactSupportForm ρ univ k)
    (V : Set OrbitSpace) (hw : ∀ i ∈ s, quotientSupport (w i).val ⊆ V) :
    quotientSupport (∑ i ∈ s, w i).val ⊆ V := by
  classical
  revert hw
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hw
    rw [Finset.sum_insert hi]
    exact (quotientSupport_add (w i).val (∑ j ∈ s, w j).val).trans
      (union_subset (hw i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hw j (Finset.mem_insert_of_mem hj))))

/-- Pointwise chart evaluation commutes with every finite sum of actual compact forms. -/
theorem compactChartRepresentative_sum_apply (s : Finset ι) (w : ι → CompactSupportForm ρ univ k)
    (x : Coordinates) :
    (compactChartRepresentative ρ S k (∑ i ∈ s, w i)).val x =
      ∑ i ∈ s, (compactChartRepresentative ρ S k (w i)).val x := by
  let ev : Form (F := F) (quotientChart S).target k →ₗ[ℝ] (Coordinates [⋀^Fin k]→L[ℝ] F) :=
    (LinearMap.proj x).comp (formSubmodule (F := F) (quotientChart S).target k).subtype
  exact map_sum (ev.comp (compactChartRepresentative ρ S k)) w s

end TernaryPoly.PolynomialFormWeakSmooth
