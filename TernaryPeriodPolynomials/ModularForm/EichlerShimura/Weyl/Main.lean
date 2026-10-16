module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Smooth

@[expose] public section


/-!
# Weyl's lemma for Dirac-type systems on the plane

A locally square integrable weak solution of `P₀ ∂₀ u + P₁ ∂₁ u + Q u = 0` on an open set `U ⊆ ℂ`,
where `Q = ∑ q_s T_s` has smooth coefficients, agrees almost everywhere with a function that is smooth
on `U` (`WeakSol.exists_smooth`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Main

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {P : Fin 2 → X →L[ℝ] X} {U : Set ℂ} {ι : Type} [Fintype ι] {T : ι → X →L[ℝ] X}
  {q : ι → ℂ → ℝ} {u : ℂ → X}

namespace WeakSol

variable (hs : WeakSol U P T q u)
include hs

theorem exists_smooth_rep {η : ℂ → ℝ} (hη : IsTest η) (hηU : tsupport η ⊆ U) :
    ∃ W : ℂ → X, ContDiff ℝ ∞ W ∧ (fun z => η z • u z) =ᵐ[volume] W := by
  have hK : IsCompact (tsupport η) := hη.2
  have hex : ∀ k : ℕ, ∃ w : ℂ → X, ContDiff ℝ k w ∧ (fun z => η z • u z) =ᵐ[volume] w ∧
      ∀ z, z ∉ cthickening 1 (tsupport η) → w z = 0 := fun k =>
    exists_contDiff_of_Hk hK k (hs.hk (k + 2) η hη hηU)
  choose w hwd hwe hwz using hex
  refine ⟨w 0, ?_, hwe 0⟩
  rw [contDiff_infty]
  intro k
  have : w k = w 0 := ((hwd k).continuous.ae_eq_iff_eq volume (hwd 0).continuous).mp
    ((hwe k).symm.trans (hwe 0))
  rw [← this]
  exact hwd k

theorem exists_smooth : ∃ w : ℂ → X, ContDiffOn ℝ ∞ w U ∧ u =ᵐ[volume.restrict U] w := by
  have hlocal : ∀ x ∈ U, ∃ (η : ℂ → ℝ) (W : ℂ → X), IsTest η ∧ tsupport η ⊆ U ∧
      η =ᶠ[𝓝 x] 1 ∧ ContDiff ℝ ∞ W ∧ (fun z => η z • u z) =ᵐ[volume] W := by
    intro x hx
    obtain ⟨η, hd, hc, hU, h1⟩ := TernaryPoly.CompactSmoothCutoff.exists_cutoff
      (isCompact_singleton (x := x)) hs.isOpen (singleton_subset_iff.mpr hx)
    obtain ⟨W, hW, hWe⟩ := hs.exists_smooth_rep ⟨hd, hc⟩ hU
    exact ⟨η, W, ⟨hd, hc⟩, hU, h1 x rfl, hW, hWe⟩
  choose! η W hη hηU hη1 hWd hWe using hlocal
  -- the glued function
  let w : ℂ → X := fun z => W z z
  have claimA : ∀ x ∈ U, ∃ N : Set ℂ, IsOpen N ∧ x ∈ N ∧ N ⊆ U ∧ EqOn w (W x) N ∧
      (∀ᵐ z ∂volume.restrict N, u z = W x z) := by
    intro x hx
    obtain ⟨N₀, hN₀, hN₀o, hxN₀⟩ := _root_.eventually_nhds_iff.mp (hη1 x hx)
    refine ⟨N₀ ∩ U, hN₀o.inter hs.isOpen, ⟨hxN₀, hx⟩, inter_subset_right, ?_, ?_⟩
    · intro z hz
      obtain ⟨N₁, hN₁, hN₁o, hzN₁⟩ := _root_.eventually_nhds_iff.mp (hη1 z hz.2)
      have hV : IsOpen (N₀ ∩ U ∩ N₁) := (hN₀o.inter hs.isOpen).inter hN₁o
      have hae : W z =ᵐ[volume.restrict (N₀ ∩ U ∩ N₁)] W x := by
        have h1 : ∀ᵐ y ∂volume, η z y • u y = W z y := hWe z hz.2
        have h2 : ∀ᵐ y ∂volume, η x y • u y = W x y := hWe x hx
        have h3 := ae_restrict_of_ae (μ := volume) (s := N₀ ∩ U ∩ N₁) (h1.and h2)
        filter_upwards [h3, ae_restrict_mem hV.measurableSet] with y ⟨hy1, hy2⟩ hyV
        rw [← hy1, ← hy2, hN₁ y hyV.2, hN₀ y hyV.1.1]
      have := Measure.eqOn_open_of_ae_eq hae hV (hWd z hz.2).continuous.continuousOn
        (hWd x hx).continuous.continuousOn
      exact this ⟨⟨hz.1, hz.2⟩, hzN₁⟩
    · have h2 : ∀ᵐ y ∂volume, η x y • u y = W x y := hWe x hx
      filter_upwards [ae_restrict_of_ae (μ := volume) (s := N₀ ∩ U) h2,
        ae_restrict_mem (hN₀o.inter hs.isOpen).measurableSet] with y hy hyN
      rw [← hy, hN₀ y hyN.1]
      simp
  choose! N hNo hNx hNU hNeq hNae using claimA
  refine ⟨w, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun x hx => ⟨N x, hNo x hx, hNx x hx, ?_⟩
    exact (hWd x hx).contDiffOn.congr fun z hz => hNeq x hx hz.2
  · obtain ⟨t, htU, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
      (f := N) (s := U) fun x hx => (hNo x hx).mem_nhds (hNx x hx) |> fun h => nhdsWithin_le_nhds h
    have hae : ∀ x ∈ t, ∀ᵐ z ∂volume.restrict (N x), u z = w z := by
      intro x hx
      have hxU := htU hx
      filter_upwards [hNae x hxU, ae_restrict_mem (hNo x hxU).measurableSet] with z hz hzN
      rw [hz, ← hNeq x hxU hzN]
    have := (ae_restrict_biUnion_iff N htc (fun z => u z = w z)).mpr hae
    exact ae_restrict_of_ae_restrict_of_subset hcov this

end WeakSol

end Main

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
