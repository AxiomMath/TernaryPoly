module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechContractionAlgebra

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial Topology ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type*} (U : ι → Set OrbitSpace) (n : ℕ)
  (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ) (hφ : φ.IsSubordinate U)

/-- The actual partition-of-unity Čech homotopy satisfies δh+hδ=id on genuine covering forms.
Every summand is smoothly zero extended and every sum is locally finite on the quotient. -/
theorem formCech_contracting (k : ℕ) (w : FormCechTerms ρ U n (k+1)) :
    formCechD ρ U n k (formCechH ρ U n hU φ hφ k w) +
      formCechH ρ U n hU φ hφ (k+1) (formCechD ρ U n (k+1) w) = w := by
  funext t
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have h₁ : ((formCechD ρ U n k (formCechH ρ U n hU φ hφ k w) t).val :
      RawForm Coordinates F n) x =
      ∑ i : Fin (k+1), (-1 : ℤ)^i.val •
        ∑ j ∈ φ.finsupport (coordinateProjection x), φ j (coordinateProjection x) •
          ((w (Fin.cons j (t ∘ i.succAbove))).val : RawForm Coordinates F n) x := by
    rw [formCechD_value ρ U n k _ t x hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [formCechH_value_sum ρ U n hU φ hφ k w (t ∘ i.succAbove) x
      (liftedDomain_mono (cechDomain_select_subset U i.succAbove t) hx)]
  have h₂ : ((formCechH ρ U n hU φ hφ (k+1) (formCechD ρ U n (k+1) w) t).val :
      RawForm Coordinates F n) x =
      ∑ j ∈ φ.finsupport (coordinateProjection x), φ j (coordinateProjection x) •
        (((w t).val : RawForm Coordinates F n) x -
          ∑ i : Fin (k+1), (-1 : ℤ)^i.val •
            ((w (Fin.cons j (t ∘ i.succAbove))).val : RawForm Coordinates F n) x) := by
    rw [formCechH_value_sum ρ U n hU φ hφ (k+1) _ t x hx]
    apply Finset.sum_congr rfl
    intro j hj
    have hjU : coordinateProjection x ∈ U j := hφ j
      (subset_tsupport _ ((φ.mem_finsupport (coordinateProjection x)).mp hj))
    have hxj : x ∈ liftedDomain (cechDomain U (Fin.cons j t)) :=
      liftedDomain_mono (cechDomain_subset_cons U j t) ⟨hx.1, hjU, hx.2⟩
    rw [formCechD_cons_value ρ U n k w j t x hxj]
  change ((formCechD ρ U n k (formCechH ρ U n hU φ hφ k w) t).val : RawForm Coordinates F n) x +
    ((formCechH ρ U n hU φ hφ (k+1) (formCechD ρ U n (k+1) w) t).val : RawForm Coordinates F n) x = _
  rw [h₁, h₂]
  exact partition_contraction_algebra (φ.finsupport (coordinateProjection x))
    (fun j => φ j (coordinateProjection x)) (φ.sum_finsupport (coordinateProjection x) (Set.mem_univ _)) k _ _

/-- Every actual closed Čech cochain in positive horizontal degree has the explicit genuine
partition-of-unity primitive. -/
theorem formCech_primitive (k : ℕ) (w : FormCechTerms ρ U n (k+2))
    (hw : formCechD ρ U n (k+2) w = 0) :
    formCechD ρ U n (k+1) (formCechH ρ U n hU φ hφ (k+1) w) = w := by
  have h := formCech_contracting ρ U n hU φ hφ (k+1) w
  rw [hw, map_zero, add_zero] at h
  exact h

end TernaryPoly.SmoothSingularGlobal
