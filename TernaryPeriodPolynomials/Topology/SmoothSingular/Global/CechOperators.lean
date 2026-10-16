module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechForms

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial Topology ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type*} (U : ι → Set OrbitSpace) (n : ℕ)

/-- Evaluation of the literal covering representative is a real linear map. -/
def formValueLinear {V : Set OrbitSpace} (x : Coordinates) :
    EquivariantForm ρ V n →ₗ[ℝ] (Coordinates [⋀^Fin n]→L[ℝ] F) where
  toFun w := (w.val : RawForm Coordinates F n) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual augmented Čech differential includes the empty tuple of global forms. -/
def formCechD (k : ℕ) : FormCechTerms ρ U n k →ₗ[ℝ] FormCechTerms ρ U n (k+1) :=
  ∑ i : Fin (k+1), (-1 : ℤ)^i.val • formCechSelect ρ U n i.succAbove

/-- The augmented differential is the true alternating restriction sum at every Čech tuple. -/
theorem formCechD_apply (k : ℕ) (w : FormCechTerms ρ U n k) (t : Fin (k+1) → ι) :
    formCechD ρ U n k w t = ∑ i : Fin (k+1), (-1 : ℤ)^i.val •
      restrictEquivariant ρ (cechDomain_select_subset U i.succAbove t) n (w (t ∘ i.succAbove)) := by
  simp only [formCechD, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  rfl

/-- In positive tuple lengths, the augmented Čech differential is exactly the differential of
the genuine cosimplicial Čech complex. -/
theorem formCechD_eq_complex (k : ℕ) : ModuleCat.ofHom (formCechD ρ U n (k+1)) =
    (formCechComplex ρ U n).d k (k+1) := by
  rw [formCechComplex_d]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom, formCechD]

/-- The actual Čech face sum evaluates without restriction masks inside its domain. -/
theorem formCechD_value (k : ℕ) (w : FormCechTerms ρ U n k) (t : Fin (k+1) → ι)
    (x : Coordinates) (hx : x ∈ liftedDomain (cechDomain U t)) :
    ((formCechD ρ U n k w t).val : RawForm Coordinates F n) x =
      ∑ i : Fin (k+1), (-1 : ℤ)^i.val •
        ((w (t ∘ i.succAbove)).val : RawForm Coordinates F n) x := by
  change formValueLinear ρ n x (formCechD ρ U n k w t) = _
  rw [formCechD_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  exact congrArg (((-1 : ℤ)^i.val) • ·)
    (restrictEquivariant_apply ρ (cechDomain_select_subset U i.succAbove t) (w (t ∘ i.succAbove)) hx)

/-- The prepended actual overlap family obtained from a Čech cochain by genuine restriction. -/
def formCechPrefix (k : ℕ) (t : Fin k → ι) : FormCechTerms ρ U n (k+1) →ₗ[ℝ]
    (∀ i, EquivariantForm ρ (U i ∩ cechDomain U t) n) where
  toFun w i := restrictEquivariant ρ (cechDomain_subset_cons U i t) n (w (Fin.cons i t))
  map_add' w z := by
    funext i
    exact map_add (restrictEquivariant ρ (cechDomain_subset_cons U i t) n) _ _
  map_smul' c w := by
    funext i
    exact map_smul (restrictEquivariant ρ (cechDomain_subset_cons U i t) n) c (w (Fin.cons i t))

variable (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ) (hφ : φ.IsSubordinate U)

/-- The genuine partition Čech homotopy, using actual scalar-weighted zero extension on
prepended overlaps and actual locally finite summation. -/
def formCechH (k : ℕ) : FormCechTerms ρ U n (k+1) →ₗ[ℝ] FormCechTerms ρ U n k :=
  LinearMap.pi (fun t =>
    (partitionSumLinear U hU φ hφ (cechDomain_isOpen U hU t) n).comp
      (formCechPrefix ρ U n k t))

/-- The actual Čech homotopy has the literal locally finite partition formula in every domain. -/
theorem formCechH_value (k : ℕ) (w : FormCechTerms ρ U n (k+1)) (t : Fin k → ι)
    (x : Coordinates) (hx : x ∈ liftedDomain (cechDomain U t)) :
    ((formCechH ρ U n hU φ hφ k w t).val : RawForm Coordinates F n) x =
      ∑ᶠ i, φ i (coordinateProjection x) •
        ((w (Fin.cons i t)).val : RawForm Coordinates F n) x := by
  change ((partitionSum U hU φ hφ (cechDomain_isOpen U hU t) n
    (fun i => restrictEquivariant ρ (cechDomain_subset_cons U i t) n (w (Fin.cons i t)))).val :
      RawForm Coordinates F n) x = _
  rw [partitionSum_apply]
  apply finsum_congr
  intro i
  by_cases hxi : coordinateProjection x ∈ U i
  · have hxt : x ∈ liftedDomain (U i ∩ cechDomain U t) := ⟨hx.1, hxi, hx.2⟩
    rw [restrictEquivariant_apply ρ _ _ hxt]
  · have hz : φ i (coordinateProjection x) = 0 := by
      by_contra hn
      exact hxi (hφ i (subset_tsupport _ hn))
    rw [hz, zero_smul, zero_smul]

end TernaryPoly.SmoothSingularGlobal
