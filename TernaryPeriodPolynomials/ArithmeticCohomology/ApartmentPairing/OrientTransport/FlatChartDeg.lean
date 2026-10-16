module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatChartMap

@[expose] public section


/-!
# The planar degree of the flat over the chart box

`deg_G0_eq_G1`: on a chain of the part `VO F` of the glued flat over the chart box whose boundary lies where the plane coordinate
`δ⁻¹ ρ ψ s` of the chart point has norm `> 1`, the local degree of the image under that plane coordinate equals the local degree
of the image under the straight fan map `LamD` (the straight-line homotopy `(1 - λ) δ⁻¹ ρ + λ Λ` never vanishes there, by the
sign of the logarithms: `log s ≤ s - 1 ≤ 0` on `(0, 1]`).  `deg_Lam_eq`: the localization pieces of the glued flat have fan image of
degree `lam2`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalSupport
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.EquivariantSingularResolution TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceBordifiedCohomology
  TernaryPoly.SymmetricSpaceRationalAction TernaryPoly.SymmetricSpaceRationalCharts
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalRelativeSingular

theorem w_neg (c l s : ℝ) (hc : 0 < c) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hs : 0 < s) (hs1 : s < 1) :
    (1 - l) * c * Real.log s + l * (s - 1) < 0 := by
  have hL : Real.log s < 0 := Real.log_neg hs hs1
  have hS : s - 1 < 0 := sub_neg.mpr hs1
  have h1 : (1 - l) * c * Real.log s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sub_nonneg.2 hl1) hc.le) hL.le
  rcases hl0.eq_or_lt with h | h
  · subst h
    have : 0 < (1 - 0) * c := by simpa using hc
    have h2 : (1 - 0) * c * Real.log s < 0 := mul_neg_of_pos_of_neg this hL
    simpa using h2
  · have h2 : l * (s - 1) < 0 := mul_neg_of_pos_of_neg h hS
    linarith

theorem eq_one_of_w (c l s : ℝ) (hc : 0 < c) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (h : (1 - l) * c * Real.log s + l * (s - 1) = 0) : s = 1 := by
  by_contra hne
  have hlt : s < 1 := lt_of_le_of_ne hs1 hne
  have := w_neg c l s hc hl0 hl1 hs hlt
  linarith

theorem homotopy_ne_zero (k : Fin 6) (s t c l : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hv0 : c • mk2 (hexM k 0 0 * Real.log s + hexM k 0 1 * Real.log t)
      (hexM k 1 0 * Real.log s + hexM k 1 1 * Real.log t) ≠ 0) :
    (1 - l) • (c • mk2 (hexM k 0 0 * Real.log s + hexM k 0 1 * Real.log t)
      (hexM k 1 0 * Real.log s + hexM k 1 1 * Real.log t)) + l • hexLam k (s, t) ≠ 0 := by
  intro h
  apply hv0
  have h0 := congrArg (fun v : R2 => v 0) h
  have h1 := congrArg (fun v : R2 => v 1) h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mk2_zero, mk2_one, hexLam_apply0, hexLam_apply1,
    PiLp.zero_apply] at h0 h1
  set w1 := (1 - l) * c * Real.log s + l * (s - 1) with hw1
  set w2 := (1 - l) * c * Real.log t + l * (t - 1) with hw2
  have e0 : hexM k 0 0 * w1 + hexM k 0 1 * w2 = 0 := by rw [hw1, hw2]; linear_combination h0
  have e1 : hexM k 1 0 * w1 + hexM k 1 1 * w2 = 0 := by rw [hw1, hw2]; linear_combination h1
  have hdet : hexM k 0 0 * hexM k 1 1 - hexM k 0 1 * hexM k 1 0 ≠ 0 := by
    have := hexM_det k
    rw [Matrix.det_fin_two] at this
    rw [this]
    split_ifs <;> norm_num
  have hw1z : w1 = 0 := by
    have : (hexM k 0 0 * hexM k 1 1 - hexM k 0 1 * hexM k 1 0) * w1 = 0 := by
      linear_combination hexM k 1 1 * e0 - hexM k 0 1 * e1
    exact (mul_eq_zero.mp this).resolve_left hdet
  have hw2z : w2 = 0 := by
    have : (hexM k 0 0 * hexM k 1 1 - hexM k 0 1 * hexM k 1 0) * w2 = 0 := by
      linear_combination hexM k 0 0 * e1 - hexM k 1 0 * e0
    exact (mul_eq_zero.mp this).resolve_left hdet
  have hs' := eq_one_of_w c l s hc hl0 hl1 hs hs1 hw1z
  have ht' := eq_one_of_w c l t hc hl0 hl1 ht ht1 hw2z
  rw [hs', ht']
  have hz : mk2 0 0 = 0 := by ext i; fin_cases i <;> rfl
  simp [hz]

section Homotopy

variable (F : FrameOut)

/-- The scaled plane coordinate of the chart point. -/
def G0 : TopCat.of (VO F) ⟶ TopCat.of R2 :=
  kapHom F ≫ ((F.sec pS pS_isQuotientCovering ≫ psiHom) ≫ rhoEHom ≫ scale2 F.δ⁻¹)

/-- The straight fan map. -/
def G1 : TopCat.of (VO F) ⟶ TopCat.of R2 := sInclusion (X := FDT) (VO F) ≫ LamHom

theorem G0_apply (x : VO F) :
    (G0 F).hom x = F.δ⁻¹ • rhoE (psi ((F.sec pS pS_isQuotientCovering).hom (kap F x))) := rfl

theorem G1_apply (x : VO F) : (G1 F).hom x = LamD x.1 := rfl

/-- The straight-line homotopy from the scaled plane coordinate to the fan map. -/
def H01 : ContinuousMap.Homotopy (G0 F).hom (G1 F).hom where
  toFun p := (1 - (p.1 : ℝ)) • (G0 F).hom p.2 + (p.1 : ℝ) • (G1 F).hom p.2
  continuous_toFun := by
    have h0 := (G0 F).hom.continuous
    have h1 := (G1 F).hom.continuous
    fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

theorem deg_G0_eq_G1 (c : singularChainGroup ℚ (TopCat.of (VO F)) 2)
    (hc : (singularBoundary ℚ (TopCat.of (VO F)) 1).hom c ∈
      subChainSubmodule ℚ (TopCat.of (VO F)) {x : VO F | 1 < ‖(G0 F).hom x‖} 1) :
    ∃ (h0 : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ (G0 F) 2).hom c)) = 0)
      (h1 : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ (G1 F) 2).hom c)) = 0),
      degR2 ((singularChainMap ℚ (G0 F) 2).hom c) h0 = degR2 ((singularChainMap ℚ (G1 F) 2).hom c) h1 := by
  refine degR2_homotopy (G0 F) (G1 F) (H01 F) {x : VO F | 1 < ‖(G0 F).hom x‖} ?_ c hc
  intro l x hx
  obtain ⟨k, s, t, hs, hs1, ht, ht1, hLam, hrho⟩ := VO_coords F x
  have hG0 : (G0 F).hom x = F.δ⁻¹ • mk2 (hexM k 0 0 * Real.log s + hexM k 0 1 * Real.log t)
      (hexM k 1 0 * Real.log s + hexM k 1 1 * Real.log t) := by
    rw [G0_apply, hrho]
  have hG1 : (G1 F).hom x = hexLam k (s, t) := by rw [G1_apply, hLam]
  have hx' : 1 < ‖(G0 F).hom x‖ := hx
  have hne : (G0 F).hom x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx'
    linarith
  rw [hG0] at hne
  change (1 - (l : ℝ)) • (G0 F).hom x + (l : ℝ) • (G1 F).hom x ≠ 0
  rw [hG0, hG1]
  exact homotopy_ne_zero k s t _ _ hs hs1 ht ht1 (inv_pos.mpr F.hδ) l.2.1 l.2.2 hne

end Homotopy

section LamDegree

theorem locR2_boundary (w : singularChainGroup ℚ (TopCat.of R2) 3) :
    (locR2.f 2).hom ((singularBoundary ℚ (TopCat.of R2) 2).hom w) =
      ((localChains 2).d 3 2).hom ((locR2.f 3).hom w) := by
  have := congrArg (fun m => m.hom w) (locR2.comm 3 2)
  exact this.symm

theorem degR2_boundary (w : singularChainGroup ℚ (TopCat.of R2) 3)
    (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularBoundary ℚ (TopCat.of R2) 2).hom w)) = 0) :
    degR2 ((singularBoundary ℚ (TopCat.of R2) 2).hom w) h = 0 := by
  have h0 : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (0 : singularChainGroup ℚ (TopCat.of R2) 2)) = 0 := by simp
  rw [degR2_eq_of_sub _ 0 h h0 ((locR2.f 3).hom w) (by rw [locR2_boundary]; simp), degR2_zero]

/-- **The fan degree of the localization pieces.** -/
theorem deg_Lam_eq (P : Set FD) (hP0 : ∀ x : FD, x ∈ P → LamD x ≠ 0)
    (FT FA : singularChainGroup ℚ FDT 2) (u : singularChainGroup ℚ FDT 3)
    (hdec : flatD = FT + FA + (singularBoundary ℚ FDT 2).hom u)
    (hFA : FA ∈ subChainSubmodule ℚ FDT P 2)
    (hFT : (singularBoundary ℚ FDT 1).hom FT ∈ subChainSubmodule ℚ FDT P 1) :
    ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ LamHom 2).hom FT)) = 0,
      degR2 ((singularChainMap ℚ LamHom 2).hom FT) h = lam2 := by
  have hPm : P ⊆ LamHom.hom ⁻¹' ({0}ᶜ : Set R2) := fun x hx h0 => hP0 x hx h0
  have hFAm : (singularChainMap ℚ LamHom 2).hom FA ∈ subChainSubmodule ℚ (TopCat.of R2) ({0}ᶜ : Set R2) 2 :=
    singularChainMap_mem_sub LamHom _ 2 (subChainSubmodule_mono hPm 2 hFA)
  have hFTm : ((singularBoundary ℚ (TopCat.of R2) 1).hom ((singularChainMap ℚ LamHom 2).hom FT)) ∈
      subChainSubmodule ℚ (TopCat.of R2) ({0}ᶜ : Set R2) 1 := by
    have h1 := singularChainMap_boundary_apply ℚ LamHom 1 FT
    have h2 : (singularBoundary ℚ (TopCat.of R2) 1).hom ((singularChainMap ℚ LamHom 2).hom FT) =
        (singularChainMap ℚ LamHom 1).hom ((singularBoundary ℚ FDT 1).hom FT) := h1
    rw [h2]
    exact singularChainMap_mem_sub LamHom _ 1 (subChainSubmodule_mono hPm 1 hFT)
  have hcA : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ LamHom 2).hom FT)) = 0 :=
    locR2_cycle_of_boundary_mem (U := ({0}ᶜ : Set R2)) subset_rfl hFTm
  have hbz : (locR2.f 2).hom ((singularChainMap ℚ LamHom 2).hom FA) = 0 :=
    locR2_sub_zero (U := ({0}ᶜ : Set R2)) subset_rfl 2 hFAm
  have hcB : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ LamHom 2).hom FA)) = 0 := by
    rw [hbz, map_zero]
  have hbd : (singularChainMap ℚ LamHom 2).hom ((singularBoundary ℚ FDT 2).hom u) =
      (singularBoundary ℚ (TopCat.of R2) 2).hom ((singularChainMap ℚ LamHom 3).hom u) :=
    (singularChainMap_boundary_apply ℚ LamHom 2 u).symm
  have hcC : ((localChains 2).d 2 1).hom ((locR2.f 2).hom
      ((singularChainMap ℚ LamHom 2).hom ((singularBoundary ℚ FDT 2).hom u))) = 0 := by
    rw [hbd, locR2_boundary, ← ModuleCat.comp_apply, (localChains 2).d_comp_d]
    rfl
  have heq : fanChain = (singularChainMap ℚ LamHom 2).hom FT + (singularChainMap ℚ LamHom 2).hom FA +
      (singularChainMap ℚ LamHom 2).hom ((singularBoundary ℚ FDT 2).hom u) := by
    rw [← Lam_flatD, hdec, map_add, map_add]
  have hAB : ((localChains 2).d 2 1).hom ((locR2.f 2).hom
      ((singularChainMap ℚ LamHom 2).hom FT + (singularChainMap ℚ LamHom 2).hom FA)) = 0 := by
    rw [map_add, map_add, hcA, hcB, add_zero]
  have hABC : ((localChains 2).d 2 1).hom ((locR2.f 2).hom
      ((singularChainMap ℚ LamHom 2).hom FT + (singularChainMap ℚ LamHom 2).hom FA +
        (singularChainMap ℚ LamHom 2).hom ((singularBoundary ℚ FDT 2).hom u))) = 0 := by
    rw [← heq]; exact fan_cycle
  refine ⟨hcA, ?_⟩
  have e1 := degR2_congr _ _ heq fan_cycle hABC
  have e2 := degR2_add _ _ hAB hcC hABC
  have e3 := degR2_add _ _ hcA hcB hAB
  have e4 : degR2 ((singularChainMap ℚ LamHom 2).hom FA) hcB = 0 :=
    degR2_eq_zero_of_avoids _ hcB hbz
  have e5 : degR2 ((singularChainMap ℚ LamHom 2).hom ((singularBoundary ℚ FDT 2).hom u)) hcC = 0 := by
    have hh := degR2_boundary ((singularChainMap ℚ LamHom 3).hom u) (by
      rw [← hbd]; exact hcC)
    have := degR2_congr _ _ hbd hcC (by rw [← hbd]; exact hcC)
    rw [this]
    exact hh
  have e6 := fan_degree fan_cycle
  rw [← e6, e1, e2, e3, e4, e5]
  ring

end LamDegree

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
