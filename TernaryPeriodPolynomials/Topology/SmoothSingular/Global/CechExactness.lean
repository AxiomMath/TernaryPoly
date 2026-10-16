module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechContraction

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory HomologicalComplex
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial Topology ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type*} (U : ι → Set OrbitSpace) (n : ℕ)
  (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ) (hφ : φ.IsSubordinate U)

include hU φ hφ in
/-- The true horizontal Čech complex of local-coefficient forms is exact in positive degrees,
proved by the explicit smooth partition homotopy on actual covering representatives. -/
theorem formCechComplex_exactAt (k : ℕ) : (formCechComplex ρ U n).ExactAt (k+1) := by
  rw [exactAt_iff' _ k (k+1) ((k+1)+1) (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro w hw
  change FormCechTerms ρ U n (k+2) at w
  have hd := formCechD_eq_complex ρ U n (k+1)
  have hw' : formCechD ρ U n (k+2) w = 0 := by
    exact (congrArg (fun f => f.hom w) hd).trans hw
  refine ⟨formCechH ρ U n hU φ hφ (k+1) w, ?_⟩
  exact (congrArg (fun f => f.hom (formCechH ρ U n hU φ hφ (k+1) w))
    (formCechD_eq_complex ρ U n k)).symm.trans
      (formCech_primitive ρ U n hU φ hφ k w hw')

include hU in
/-- Every actual quotient open cover admits the genuine smooth Čech contraction, so no
acyclicity or partition-existence hypothesis is left in this exactness theorem. -/
theorem formCechComplex_exactAt_of_cover (hcover : Set.univ ⊆ ⋃ i, U i) (k : ℕ) :
    (formCechComplex ρ U n).ExactAt (k+1) := by
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    isClosed_univ U hU hcover
  exact formCechComplex_exactAt ρ U n hU φ hφ k

end TernaryPoly.SmoothSingularGlobal
