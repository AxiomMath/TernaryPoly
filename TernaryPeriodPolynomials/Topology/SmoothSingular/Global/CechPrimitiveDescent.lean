module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechDifferentialCommute

@[expose] public section

/-! An actual smooth Čech scalar correction descends local primitives to a global primitive. -/
noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))

theorem global_primitive_of_cech_correction (hcover : univ ⊆ ⋃ i, U i)
    (omega : EquivariantForm ρ univ 2) (v : FormCechTerms ρ U 1 1)
    (a : FormCechTerms ρ U 0 2)
    (ha : formCechD ρ U 0 2 a = 0)
    (hav : formCechColumnD ρ U hU 2 0 a = -formCechD ρ U 1 1 v)
    (hv : formCechColumnD ρ U hU 1 1 v =
      formCechD ρ U 2 0 (formCechEmptyEmbed ρ U 2 omega)) :
    ∃ w : EquivariantForm ρ univ 1, differential ρ isOpen_univ 1 w = omega := by
  obtain ⟨φ,hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    isClosed_univ U hU hcover
  let b := formCechH ρ U 0 hU φ hφ 1 a
  have hb : formCechD ρ U 0 1 b = a := formCech_primitive ρ U 0 hU φ hφ 0 a ha
  let z := v + formCechColumnD ρ U hU 1 0 b
  have hz : formCechD ρ U 1 1 z = 0 := by
    change formCechD ρ U 1 1 (v + formCechColumnD ρ U hU 1 0 b) = 0
    rw [map_add, formCechD_columnD, hb, hav, add_neg_cancel]
  have hdz : formCechColumnD ρ U hU 1 1 z =
      formCechD ρ U 2 0 (formCechEmptyEmbed ρ U 2 omega) := by
    change formCechColumnD ρ U hU 1 1 (v + formCechColumnD ρ U hU 1 0 b) = _
    rw [map_add, formCechColumnD_squared, add_zero, hv]
  let c := formCechH ρ U 1 hU φ hφ 0 z
  have hc : formCechD ρ U 1 0 c = z := by
    have H := formCech_contracting ρ U 1 hU φ hφ 0 z
    rw [hz, map_zero, add_zero] at H
    exact H
  have hdc : formCechColumnD ρ U hU 0 1 c = formCechEmptyEmbed ρ U 2 omega := by
    apply formCechD_zero_injective ρ U 2 hU φ hφ
    rw [formCechD_columnD, hc, hdz]
  refine ⟨formCechEmptyRecover ρ U 1 c,?_⟩
  rw [← formCechEmptyRecover_differential ρ U hU, hdc, formCechEmptyRecover_embed]

end TernaryPoly.SmoothSingularGlobal
