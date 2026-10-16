module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.L2Limit

@[expose] public section


/-!
# One step of elliptic regularity for Dirac-type systems

If `v, f ∈ L²` are supported in a compact set and `P₀ ∂₀ v + P₁ ∂₁ v = f` weakly, then `v` has weak
derivatives in `L²` supported in the same set (`exists_wd_of_weakEq`), and the regularity
propagates through the iterated spaces `Hk` (`Hk_succ_of_weakEq`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Supports

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem tsupport_mol_subset (n : ℕ) {K : Set ℂ} {v : ℂ → X} (hv : ∀ᵐ z, z ∉ K → v z = 0) :
    tsupport (mol n v) ⊆ cthickening 1 K := by
  refine closure_minimal (fun z hz => ?_) isClosed_cthickening
  by_contra hzK
  apply hz
  refine mol_eq_zero n hv fun hz' => hzK (cthickening_mono ?_ K hz')
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

omit [CompleteSpace X] in
theorem L2s_mol (n : ℕ) {K : Set ℂ} (hK : IsCompact K) {v : ℂ → X} (hv : L2s K v) :
    L2s (cthickening 1 K) (mol n v) := by
  have hvl : LocallyIntegrable v volume := (hv.integrable hK).locallyIntegrable
  have hz : ∀ z, z ∉ cthickening 1 K → mol n v z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_mol_subset n hv.2 h)
  refine ⟨?_, Eventually.of_forall hz⟩
  exact (mol_contDiff n hvl).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.intro hK.cthickening hz)

omit [CompleteSpace X] in
theorem L2s_mol_fderiv (n : ℕ) {K : Set ℂ} (hK : IsCompact K) {v : ℂ → X} (hv : L2s K v)
    (e : ℂ) : L2s (cthickening 1 K) fun z => fderiv ℝ (mol n v) z e := by
  have hvl : LocallyIntegrable v volume := (hv.integrable hK).locallyIntegrable
  have hz : ∀ z, z ∉ cthickening 1 K → fderiv ℝ (mol n v) z e = 0 := fun z hz => by
    rw [fderiv_of_notMem_tsupport ℝ fun h => hz (tsupport_mol_subset n hv.2 h)]
    rfl
  refine ⟨?_, Eventually.of_forall hz⟩
  exact (contDiff_fderiv_apply (mol_contDiff n hvl) e).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.intro hK.cthickening hz)

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
theorem L2s.mono {K K' : Set ℂ} (h : K ⊆ K') {v : ℂ → X} (hv : L2s K v) : L2s K' v :=
  ⟨hv.1, by
    filter_upwards [hv.2] with z hz hzK
    exact hz fun hz' => hzK (h hz')⟩

end Supports

section OneStep

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {P : Fin 2 → X →L[ℝ] X}

theorem eLpNorm_deriv_le (hP : DiracPair P) {K : Set ℂ} (hK : IsCompact K) {v f : ℂ → X}
    (hv : L2s K v) (hf : L2s K f) (h : WeakEq P v f) (n m : ℕ) (j : Fin 2) :
    eLpNorm (fun z => fderiv ℝ (mol n v) z (dir j) - fderiv ℝ (mol m v) z (dir j)) 2 volume ≤
      eLpNorm (fun z => mol n f z - mol m f z) 2 volume := by
  have A := (L2s_mol_fderiv n hK hv (dir j)).sub (L2s_mol_fderiv m hK hv (dir j))
  have B := (L2s_mol n hK hf).sub (L2s_mol m hK hf)
  rw [eLpNorm_two_eq A.1, eLpNorm_two_eq B.1]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (sq_integral_deriv_le hP hK hv h n m j))

theorem cauchy_mol {f : ℂ → X} (hf : MemLp f 2 volume) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ m, N ≤ m →
      eLpNorm (fun z => mol n f z - mol m f z) 2 volume ≤ ε := by
  intro ε hε
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  obtain ⟨N, hN⟩ := (eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp (tendsto_mol hf)) (ε / 2)
    (ENNReal.half_pos hε.ne')))
  refine ⟨N, fun n hn m hm => ?_⟩
  have e : (fun z => mol n f z - mol m f z) =
      (fun z => mol n f z - f z) - (fun z => mol m f z - f z) := by
    funext z
    simp
  have m1 : AEStronglyMeasurable (fun z => mol n f z - f z) volume :=
    ((mol_contDiff n hfl).continuous.aestronglyMeasurable).sub hf.aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun z => mol m f z - f z) volume :=
    ((mol_contDiff m hfl).continuous.aestronglyMeasurable).sub hf.aestronglyMeasurable
  rw [e]
  calc eLpNorm ((fun z => mol n f z - f z) - (fun z => mol m f z - f z)) 2 volume
      ≤ eLpNorm (fun z => mol n f z - f z) 2 volume + eLpNorm (fun z => mol m f z - f z) 2 volume :=
        eLpNorm_sub_le (by norm_num)
    _ ≤ ε / 2 + ε / 2 := add_le_add (hN n hn) (hN m hm)
    _ = ε := ENNReal.add_halves ε

theorem exists_wd_of_weakEq (hP : DiracPair P) {K : Set ℂ} (hK : IsCompact K) {v f : ℂ → X}
    (hv : L2s K v) (hf : L2s K f) (h : WeakEq P v f) :
    ∃ g : Fin 2 → ℂ → X, (∀ j, WD j v (g j)) ∧ ∀ j, L2s K (g j) := by
  have hK₁ : IsCompact (cthickening 1 K) := hK.cthickening
  have hKK : K ⊆ cthickening 1 K := self_subset_cthickening K
  have hlim : ∀ j : Fin 2, ∃ g : ℂ → X, L2s (cthickening 1 K) g ∧
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (mol n v) z (dir j) - g z) 2 volume) atTop (𝓝 0) := by
    intro j
    refine exists_L2_limit hK₁ (fun n => L2s_mol_fderiv n hK hv (dir j)) fun ε hε => ?_
    obtain ⟨N, hN⟩ := cauchy_mol hf.1 ε hε
    exact ⟨N, fun n hn m hm => (eLpNorm_deriv_le hP hK hv hf h n m j).trans (hN n hn m hm)⟩
  choose g hgL hgT using hlim
  have hW : ∀ j, WD j v (g j) := by
    intro j φ hφ
    obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2
    obtain ⟨C', hC'⟩ := (hφ.fderiv_apply (dir j)).bounded_above_of_compact_support
      (hφ.fderiv_compact (dir j))
    have hCa : ∀ z, |φ z| ≤ C := fun z => by simpa using hC z
    have hCa' : ∀ z, |fderiv ℝ φ z (dir j)| ≤ C' := fun z => by simpa using hC' z
    have t1 := tendsto_integral_smul hK₁ hφ.continuous hCa
      (fun n => L2s_mol_fderiv n hK hv (dir j)) (hgL j) (hgT j)
    have t2 := tendsto_integral_smul hK₁ (hφ.fderiv_apply (dir j)) hCa'
      (fun n => L2s_mol n hK hv) (hv.mono hKK) (tendsto_mol hv.1)
    have hvl : LocallyIntegrable v volume := (hv.integrable hK).locallyIntegrable
    have e : ∀ n, ∫ z, φ z • fderiv ℝ (mol n v) z (dir j) =
        - ∫ z, fderiv ℝ φ z (dir j) • mol n v z := by
      intro n
      have c1 := mol_contDiff n hvl
      have k1 := mol_hasCompactSupport n hK hv.2
      have i0 : Integrable (mol n v) := c1.continuous.integrable_of_hasCompactSupport k1
      have i1 : Integrable fun z => fderiv ℝ (mol n v) z (dir j) :=
        (contDiff_fderiv_apply c1 (dir j)).continuous.integrable_of_hasCompactSupport
          (hasCompactSupport_fderiv_apply k1 (dir j))
      exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (integrable_smul_cont (hφ.fderiv_apply (dir j)) (hφ.fderiv_compact (dir j)) i0)
        (integrable_smul_cont hφ.continuous hφ.2 i1) (integrable_smul_cont hφ.continuous hφ.2 i0)
        (fun x _ => hφ.1.differentiable (by simp) x) (fun x _ => c1.differentiable (by simp) x)
    have t3 : Tendsto (fun n => ∫ z, φ z • fderiv ℝ (mol n v) z (dir j)) atTop
        (𝓝 (- ∫ z, fderiv ℝ φ z (dir j) • v z)) := by
      simp only [e]
      exact t2.neg
    exact tendsto_nhds_unique t1 t3
  exact ⟨g, hW, fun j => ⟨(hgL j).1, WD.zero_off hK hv.2 (hW j)
    ((hgL j).integrable hK₁)⟩⟩

theorem IsTest.fderiv_test {φ : ℂ → ℝ} (hφ : IsTest φ) (e : ℂ) :
    IsTest fun z => fderiv ℝ φ z e :=
  ⟨contDiff_fderiv_apply hφ.1 e, hasCompactSupport_fderiv_apply hφ.2 e⟩

omit [CompleteSpace X] in
/-- Weak derivatives commute with the weak equation. -/
theorem WeakEq.deriv {j : Fin 2} {v f g f' : ℂ → X} (h : WeakEq P v f) (hg : WD j v g)
    (hf' : WD j f f') : WeakEq P g f' := by
  intro φ hφ
  have key : ∀ i, ∫ z, fderiv ℝ φ z (dir i) • g z =
      - ∫ z, fderiv ℝ (fun z => fderiv ℝ φ z (dir i)) z (dir j) • v z :=
    fun i => hg _ (hφ.fderiv_test (dir i))
  have sym : ∀ i, ∫ z, fderiv ℝ (fun z => fderiv ℝ φ z (dir i)) z (dir j) • v z =
      ∫ z, fderiv ℝ (fun z => fderiv ℝ φ z (dir j)) z (dir i) • v z := fun i => by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact congrArg (· • v z) (fderiv_symm hφ.1 z (dir j) (dir i))
  have h2 := h _ (hφ.fderiv_test (dir j))
  calc ∑ i, P i (∫ z, fderiv ℝ φ z (dir i) • g z)
      = ∑ i, P i (-∫ z, fderiv ℝ (fun z => fderiv ℝ φ z (dir j)) z (dir i) • v z) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [key i, sym i]
    _ = - ∑ i, P i (∫ z, fderiv ℝ (fun z => fderiv ℝ φ z (dir j)) z (dir i) • v z) := by
        simp only [map_neg, Finset.sum_neg_distrib]
    _ = ∫ z, fderiv ℝ φ z (dir j) • f z := by rw [h2, neg_neg]
    _ = - ∫ z, φ z • f' z := by rw [hf' φ hφ, neg_neg]

theorem Hk_succ_of_weakEq (hP : DiracPair P) {K : Set ℂ} (hK : IsCompact K) :
    ∀ (k : ℕ) {v f : ℂ → X}, Hk K k v → Hk K k f → WeakEq P v f → Hk K (k + 1) v := by
  intro k
  induction k with
  | zero =>
    intro v f hv hf h
    obtain ⟨g, hg, hgL⟩ := exists_wd_of_weakEq hP hK hv hf h
    exact ⟨hv, g, hg, hgL⟩
  | succ k ih =>
    intro v f hv hf h
    obtain ⟨hvl, g, hg, hgk⟩ := hv
    obtain ⟨hfl, f', hf', hf'k⟩ := hf
    refine ⟨hvl, g, hg, fun j => ?_⟩
    exact ih (hgk j) (hf'k j) (h.deriv (hg j) (hf' j))

end OneStep

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
