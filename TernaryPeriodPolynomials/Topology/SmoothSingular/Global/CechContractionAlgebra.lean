module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechOperators

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial Topology ContDiff Manifold

/-- The finite partition cancellation used by the genuine Čech contracting homotopy. -/
theorem partition_contraction_algebra {A : Type*} [AddCommGroup A] [Module ℝ A]
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∑ j ∈ s, c j = 1)
    (k : ℕ) (a : ι → Fin (k+1) → A) (b : A) :
    (∑ i : Fin (k+1), (-1 : ℤ)^i.val • ∑ j ∈ s, c j • a j i) +
      (∑ j ∈ s, c j • (b - ∑ i : Fin (k+1), (-1 : ℤ)^i.val • a j i)) = b := by
  have hcomm : (∑ j ∈ s, c j • ∑ i : Fin (k+1), (-1 : ℤ)^i.val • a j i) =
      ∑ i : Fin (k+1), (-1 : ℤ)^i.val • ∑ j ∈ s, c j • a j i := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, hcomm, ← Finset.sum_smul, hc, one_smul]
  abel

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type*} (U : ι → Set OrbitSpace) (n : ℕ)

/-- The true Čech differential on a prepended tuple separates the leading identity term from
the alternating remaining faces. -/
theorem formCechD_cons_value (k : ℕ) (w : FormCechTerms ρ U n (k+1))
    (j : ι) (t : Fin (k+1) → ι) (x : Coordinates)
    (hx : x ∈ liftedDomain (cechDomain U (Fin.cons j t))) :
    ((formCechD ρ U n (k+1) w (Fin.cons j t)).val : RawForm Coordinates F n) x =
      ((w t).val : RawForm Coordinates F n) x - ∑ i : Fin (k+1), (-1 : ℤ)^i.val •
        ((w (Fin.cons j (t ∘ i.succAbove))).val : RawForm Coordinates F n) x := by
  rw [formCechD_value ρ U n (k+1) w (Fin.cons j t) x hx, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  let v : (Fin (k+1) → ι) → (Coordinates [⋀^Fin n]→L[ℝ] F) :=
    fun s => ((w s).val : RawForm Coordinates F n) x
  change v (Fin.cons j t ∘ Fin.succ) +
    -(∑ i : Fin (k+1), (-1 : ℤ)^i.val • v (Fin.cons j t ∘ i.succ.succAbove)) =
    v t + -(∑ i : Fin (k+1), (-1 : ℤ)^i.val • v (Fin.cons j (t ∘ i.succAbove)))
  simp only [Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove]
  rfl


variable (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ) (hφ : φ.IsSubordinate U)

/-- The genuine Čech homotopy may be evaluated using the same finite scalar support at each
point, allowing finite face-sum cancellation without exchanging unsupported infinite sums. -/
theorem formCechH_value_sum (k : ℕ) (w : FormCechTerms ρ U n (k+1)) (t : Fin k → ι)
    (x : Coordinates) (hx : x ∈ liftedDomain (cechDomain U t)) :
    ((formCechH ρ U n hU φ hφ k w t).val : RawForm Coordinates F n) x =
      ∑ j ∈ φ.finsupport (coordinateProjection x), φ j (coordinateProjection x) •
        ((w (Fin.cons j t)).val : RawForm Coordinates F n) x := by
  rw [formCechH_value ρ U n hU φ hφ k w t x hx]
  exact (φ.sum_finsupport_smul_eq_finsum (coordinateProjection x)
    (fun j _ => ((w (Fin.cons j t)).val : RawForm Coordinates F n) x)).symm

end TernaryPoly.SmoothSingularGlobal
