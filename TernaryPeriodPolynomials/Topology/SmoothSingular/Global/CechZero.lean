module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechEmpty

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Topology ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type*} (U : ι → Set OrbitSpace) (n : ℕ)

/-- The true augmented Čech differential evaluates to the actual global empty-tuple value. -/
theorem formCechD_zero_value (w : FormCechTerms ρ U n 0) (t : Fin 1 → ι)
    (x : Coordinates) (hx : x ∈ liftedDomain (cechDomain U t)) :
    ((formCechD ρ U n 0 w t).val : RawForm Coordinates F n) x =
      ((w Fin.elim0).val : RawForm Coordinates F n) x := by
  rw [formCechD_value ρ U n 0 w t x hx, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  exact congrArg (fun s => ((w s).val : RawForm Coordinates F n) x) (Subsingleton.elim _ _)

/-- The actual augmented global restriction has zero Čech coboundary. -/
theorem formCechD_one_zero (w : FormCechTerms ρ U n 0) :
    formCechD ρ U n 1 (formCechD ρ U n 0 w) = 0 := by
  funext t
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [formCechD_value ρ U n 1 _ t x hx]
  have h : ∀ i : Fin 2,
      (((formCechD ρ U n 0 w) (t ∘ i.succAbove)).val : RawForm Coordinates F n) x =
      ((w Fin.elim0).val : RawForm Coordinates F n) x := fun i =>
    formCechD_zero_value ρ U n w (t ∘ i.succAbove) x
      (liftedDomain_mono (cechDomain_select_subset U i.succAbove t) hx)
  simp only [h]
  change (∑ i : Fin 2, (-1 : ℤ)^i.val • ((w Fin.elim0).val : RawForm Coordinates F n) x) = 0
  simp [Fin.sum_univ_two]

variable (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ) (hφ : φ.IsSubordinate U)

/-- The genuine partition homotopy is a left inverse of the augmented actual global restriction. -/
theorem formCechH_D_zero (w : FormCechTerms ρ U n 0) :
    formCechH ρ U n hU φ hφ 0 (formCechD ρ U n 0 w) = w := by
  funext t
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [formCechH_value_sum ρ U n hU φ hφ 0 _ t x hx]
  have hv : ∀ j ∈ φ.finsupport (coordinateProjection x),
      (((formCechD ρ U n 0 w) (Fin.cons j t)).val : RawForm Coordinates F n) x =
      ((w t).val : RawForm Coordinates F n) x := by
    intro j hj
    have hjU : coordinateProjection x ∈ U j := hφ j
      (subset_tsupport _ ((φ.mem_finsupport (coordinateProjection x)).mp hj))
    have hxj : x ∈ liftedDomain (cechDomain U (Fin.cons j t)) :=
      liftedDomain_mono (cechDomain_subset_cons U j t) ⟨hx.1, hjU, hx.2⟩
    exact (formCechD_zero_value ρ U n w (Fin.cons j t) x hxj).trans
      (congrArg (fun s => ((w s).val : RawForm Coordinates F n) x) (Subsingleton.elim _ t))
  calc
    _ = ∑ j ∈ φ.finsupport (coordinateProjection x),
        φ j (coordinateProjection x) • ((w t).val : RawForm Coordinates F n) x :=
      Finset.sum_congr rfl (fun j hj => congrArg (_ • ·) (hv j hj))
    _ = _ := by rw [← Finset.sum_smul, φ.sum_finsupport _ (Set.mem_univ _), one_smul]

include hU φ hφ in
/-- The actual augmented Čech restriction is injective by its genuine partition left inverse. -/
theorem formCechD_zero_injective : Function.Injective (formCechD ρ U n 0) :=
  Function.LeftInverse.injective (formCechH_D_zero ρ U n hU φ hφ)

end TernaryPoly.SmoothSingularGlobal
