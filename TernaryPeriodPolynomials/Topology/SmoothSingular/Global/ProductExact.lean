module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Resolution
public import Mathlib.Basic.Real.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits HomologicalComplex

/-- Exactness transfers through actual degreewise product identifications. This is the
explicit componentwise primitive construction for genuine real module short complexes. -/
theorem exact_of_product_equivs {ι : Type} (S : ShortComplex (ModuleCat.{0} ℝ))
    (T : ι → ShortComplex (ModuleCat.{0} ℝ))
    (e₁ : S.X₁ ≃ₗ[ℝ] ∀ i, (T i).X₁) (e₂ : S.X₂ ≃ₗ[ℝ] ∀ i, (T i).X₂)
    (e₃ : S.X₃ ≃ₗ[ℝ] ∀ i, (T i).X₃)
    (hf : ∀ x i, e₂ (S.f x) i = (T i).f (e₁ x i))
    (hg : ∀ x i, e₃ (S.g x) i = (T i).g (e₂ x i))
    (hex : ∀ i, (T i).Exact) : S.Exact := by
  apply (ShortComplex.moduleCat_exact_iff S).mpr
  intro x hx
  have hi (i : ι) : (T i).g (e₂ x i) = 0 := by
    rw [← hg x i, hx, map_zero]
    rfl
  choose z hz using fun i => (ShortComplex.moduleCat_exact_iff (T i)).mp (hex i) (e₂ x i) (hi i)
  refine ⟨e₁.symm z,?_⟩
  apply e₂.injective
  funext i
  exact (hf (e₁.symm z) i).trans
    ((congrArg (fun f => (T i).f (f i)) (e₁.apply_symm_apply z)).trans (hz i))

/-- A genuine augmentation quasi-isomorphism makes every positive target degree exact. -/
theorem augmentation_target_exactAt {K : CochainComplex (ModuleCat.{0} ℝ) ℕ}
    {A : ModuleCat.{0} ℝ} (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    [QuasiIso (SmoothSingularComparison.augmentation a ha)] (n : ℕ) : K.ExactAt (n+1) := by
  apply (exactAt_iff_of_quasiIsoAt (SmoothSingularComparison.augmentation a ha) (n+1)).mp
  apply (exactAt_iff_isZero_homology _ _).mpr
  exact isZero_single_obj_homology _ _ _ _ (Nat.succ_ne_zero n)

/-- A genuine augmentation quasi-isomorphism identifies its actual zero-degree kernel. -/
theorem augmentation_zero_exact {K : CochainComplex (ModuleCat.{0} ℝ) ℕ}
    {A : ModuleCat.{0} ℝ} (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    [QuasiIso (SmoothSingularComparison.augmentation a ha)] :
    (ShortComplex.mk a (K.d 0 1) ha).Exact := by
  have h : QuasiIsoAt (SmoothSingularComparison.augmentation a ha) 0 := inferInstance
  rw [CochainComplex.quasiIsoAt₀_iff] at h
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp; rfl) (by simp; rfl) (by simp; rfl)] at h
  simp only [shortComplexFunctor', SmoothSingularComparison.augmentation_f_zero,
    CochainComplex.single₀_obj_zero] at h
  exact h.1

/-- Actual degreewise product equivalences commute with the differential and transfer exactness. -/
theorem complex_exactAt_of_product_equivs {ι : Type}
    (C : CochainComplex (ModuleCat.{0} ℝ) ℕ) (D : ι → CochainComplex (ModuleCat.{0} ℝ) ℕ)
    (e : ∀ n, C.X n ≃ₗ[ℝ] ∀ i, (D i).X n)
    (hd : ∀ n x i, e (n+1) (C.d n (n+1) x) i = (D i).d n (n+1) (e n x i))
    (n : ℕ) (hex : ∀ i, (D i).ExactAt (n+1)) : C.ExactAt (n+1) := by
  rw [exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)]
  apply exact_of_product_equivs _ (fun i => (D i).sc' n (n+1) (n+2))
    (e n) (e (n+1)) (e (n+2)) (hd n) (hd (n+1))
  intro i
  exact (exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)).mp (hex i)

/-- A family of actual augmented resolutions descends through genuine coefficient and
cochain product equivalences. Every comparison identity concerns the literal maps. -/
theorem augmentation_quasiIso_of_product_equivs {ι : Type}
    {C : CochainComplex (ModuleCat.{0} ℝ) ℕ} (D : ι → CochainComplex (ModuleCat.{0} ℝ) ℕ)
    {A : ModuleCat.{0} ℝ} (B : ι → ModuleCat.{0} ℝ)
    (a : A ⟶ C.X 0) (ha : a ≫ C.d 0 1 = 0) [Mono a]
    (b : ∀ i, B i ⟶ (D i).X 0) (hb : ∀ i, b i ≫ (D i).d 0 1 = 0)
    (eA : A ≃ₗ[ℝ] ∀ i, B i) (e : ∀ n, C.X n ≃ₗ[ℝ] ∀ i, (D i).X n)
    (hd : ∀ n x i, e (n+1) (C.d n (n+1) x) i = (D i).d n (n+1) (e n x i))
    (haug : ∀ x i, e 0 (a x) i = b i (eA x i))
    (hq : ∀ i, QuasiIso (SmoothSingularComparison.augmentation (b i) (hb i))) :
    QuasiIso (SmoothSingularComparison.augmentation a ha) := by
  apply SmoothSingularComparison.augmentation_quasiIso
  · apply exact_of_product_equivs _ (fun i => ShortComplex.mk (b i) ((D i).d 0 1) (hb i))
      eA (e 0) (e 1) haug (hd 0)
    intro i
    have := hq i
    exact augmentation_zero_exact (b i) (hb i)
  · intro n
    apply complex_exactAt_of_product_equivs C D e hd n
    intro i
    have := hq i
    exact augmentation_target_exactAt (b i) (hb i) n

end TernaryPoly.SmoothSingularGlobal
