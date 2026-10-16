module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatChartDeg
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ChartData

@[expose] public section


/-!
# The chart chain of the flat, with its oriented planar degree

`chart_chain_data_deg` is `Locality.chart_chain_data` with the chart chain `a` built from the localization of the glued flat `FD`
(`flat_localize_D`) rather than of the flat chain in the bordification, and with the extra output that the scaled plane image
`(δ⁻¹ ρ ψ s)_# a` of the chart chain has boundary off the unit disc and planar local degree `lam2`: the positively oriented count of the
six chambers around the centre of the flat.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly TernaryPoly.RationalManifoldCompact
  TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.RationalLocalOrientation
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceBordifiedCohomology
  TernaryPoly.SingularLocalCap.Descent TernaryPoly.SymmetricSpaceRelativeFundamental
  TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceRationalAction TernaryPoly.SymmetricSpaceRationalCharts
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalRelativeSingular
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33
  TernaryPeriodPolynomials.Argument.Lemma33.Locality

theorem hexM_det_ne (k : Fin 6) : hexM k 0 0 * hexM k 1 1 - hexM k 0 1 * hexM k 1 0 ≠ 0 := by
  have := hexM_det k
  rw [Matrix.det_fin_two] at this
  rw [this]
  split_ifs <;> norm_num

theorem hexLam_eq_zero (k : Fin 6) (q : ℝ × ℝ) (h : hexLam k q = 0) : q = (1, 1) := by
  have h0 := congrArg (fun v : R2 => v 0) h
  have h1 := congrArg (fun v : R2 => v 1) h
  simp only [hexLam_apply0, hexLam_apply1, PiLp.zero_apply] at h0 h1
  have hdet := hexM_det_ne k
  have e1 : (hexM k 0 0 * hexM k 1 1 - hexM k 0 1 * hexM k 1 0) * (q.1 - 1) = 0 := by
    linear_combination hexM k 1 1 * h0 - hexM k 0 1 * h1
  have e2 : (hexM k 0 0 * hexM k 1 1 - hexM k 0 1 * hexM k 1 0) * (q.2 - 1) = 0 := by
    linear_combination hexM k 0 0 * h1 - hexM k 1 0 * h0
  have a1 := (mul_eq_zero.mp e1).resolve_left hdet
  have a2 := (mul_eq_zero.mp e2).resolve_left hdet
  exact Prod.ext (by linarith) (by linarith)

/-- The fan map vanishes only at the chamber centres, which lie over the slab. -/
theorem LamD_zero_mem_Qs (F : FrameOut) (x : FD) (hx : LamD x = 0) :
    ∃ S : Space, PiD x = embedding S ∧ pS.hom S ∈ F.Qs pS := by
  induction x using Quot.ind with
  | mk d =>
  obtain ⟨k, ⟨q, hq⟩⟩ := d
  have hq1 : q = (1, 1) := hexLam_eq_zero k q hx
  subst hq1
  have h1 : (0 : ℝ) < ((1 : ℝ), (1 : ℝ)).1 := one_pos
  have h2 : PiD (Quot.mk _ (k, (⟨(1, 1), hq⟩ : SqT))) =
      embedding (act (realRational (hexW k.val)) (diagSpace 1 1 one_pos one_pos)) :=
    chamber_pos (hexW k.val) (1, 1) one_pos one_pos
  refine ⟨_, h2, ?_⟩
  set S := act (realRational (hexW k.val)) (diagSpace 1 1 one_pos one_pos) with hS
  have hflat : S ∈ flat := fk_interior_flat k.val (1, 1) S h2.symm
  have hpi : (coordHomeo S).1 = 0 := (mem_flat_iff S).mp hflat
  have hrho : (coordHomeo S).2 = 0 := by
    rw [← rhoE_psi, hS, rho_chamber k 1 1 one_pos one_pos]
    simp only [Real.log_one, mul_zero, add_zero]
    ext i; fin_cases i <;> rfl
  refine ⟨S, ?_, rfl⟩
  show coordHomeo S ∈ (Metric.closedBall (0 : R3) F.ε ×ˢ Metric.closedBall (0 : R2) F.δ)
  rw [Set.mem_prod, hpi, hrho]
  exact ⟨Metric.mem_closedBall_self F.hε.le, Metric.mem_closedBall_self F.hδ.le⟩

/-- Over the chart box, a point of the glued flat off the support set lies off the slab. -/
theorem slab_of_notP (F : FrameOut)
    (Kfull : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)
    (hQ : F.Qs pS ⊆ (Kfull : Set _)) (x : VO F)
    (hx : PiD x.1 ∉ wholeProjection ⁻¹' ((openCompactImage
      CompactInteriorRelativeBoundary.boundaryComplementOpen Kfull : Compacts BordifiedOrbit) :
        Set BordifiedOrbit)) :
    F.δ < ‖((F.eY pS pS_isQuotientCovering (kap F x) : boxSet F.ε F.R0) : R3 × R2).2‖ := by
  by_contra hle
  push Not at hle
  apply hx
  have hQu := (F.hQ pS pS_isQuotientCovering (kap F x)).mpr hle
  have hKQ := hQ hQu
  refine ⟨(kap F x).val, hKQ, ?_⟩
  have := congrArg Subtype.val (F.p_sec pS pS_isQuotientCovering (kap F x))
  show _ = wholeProjection (PiD x.1)
  rw [← embedding_sec_kap F x]
  exact this.symm

theorem norm_G0 (F : FrameOut) (x : VO F) :
    ‖(G0 F).hom x‖ = F.δ⁻¹ *
      ‖((F.eY pS pS_isQuotientCovering (kap F x) : boxSet F.ε F.R0) : R3 × R2).2‖ := by
  rw [G0_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr F.hδ.le), rhoE_psi]
  rfl

/-- The flat chain and the image of the localized chain have the same ambient value. -/
theorem flat_eval_D (Kh : Compacts BordifiedOrbit) (FT FA : singularChainGroup ℚ FDT 2)
    (u : singularChainGroup ℚ FDT 3)
    (hdec : flatD = FT + FA + (singularBoundary ℚ FDT 2).hom u)
    (hFA : FA ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ) 2)
    (W : Rep.{0} ℚ principalSix) (K'' : Compacts BordifiedOrbit) (hKle : K'' ≤ Kh)
    (φh : Cycles ((supportCochains wholeProjection W (K'' : Set BordifiedOrbit)).sc' (2 - 1) 2 (2 + 1))) :
    (ambientCochain W K'' φh).hom flatRep =
      (ambientCochain W K'' φh).hom ((singularChainMap ℚ PiHom 2).hom FT) := by
  have hPiFA : (singularChainMap ℚ PiHom 2).hom FA ∈ subChainSubmodule ℚ (TopCat.of Glued)
      (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ 2 := singularChainMap_mem_sub PiHom _ 2 hFA
  have hFA' : (singularChainMap ℚ PiHom 2).hom FA ∈ subChainSubmodule ℚ (TopCat.of Glued)
      (wholeProjection ⁻¹' (K'' : Set BordifiedOrbit))ᶜ 2 :=
    subChainSubmodule_mono (Set.compl_subset_compl.mpr (Set.preimage_mono hKle)) 2 hPiFA
  have hadd : ∀ x y : singularChainGroup ℚ (TopCat.of Glued) 2,
      (ambientCochain W K'' φh).hom (x + y) =
        (ambientCochain W K'' φh).hom x + (ambientCochain W K'' φh).hom y :=
    fun x y => map_add (ambientCochain W K'' φh).hom.toLinearMap x y
  have h2 : (ambientCochain W K'' φh).hom ((singularChainMap ℚ PiHom 2).hom FA) = 0 :=
    ambientCochain_vanish W K'' φh _ hFA'
  have h3 : (ambientCochain W K'' φh).hom
      ((singularBoundary ℚ (TopCat.of Glued) 2).hom ((singularChainMap ℚ PiHom 3).hom u)) = 0 :=
    ambientCochain_cocycle W K'' φh _
  have e : flatChain = (singularChainMap ℚ PiHom 2).hom FT + (singularChainMap ℚ PiHom 2).hom FA +
      (singularBoundary ℚ (TopCat.of Glued) 2).hom ((singularChainMap ℚ PiHom 3).hom u) := by
    rw [← Pi_flatD, hdec, map_add, map_add, singularChainMap_boundary_apply]
  unfold flatRep
  rw [e, hadd, hadd, h2, h3, add_zero, add_zero]

/-- **The chart chain of the flat, with its oriented planar degree.** -/
theorem chart_chain_data_deg (F : FrameOut)
    (Kfull : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)
    (hK : (Kfull : Set _) ⊆ F.D1 pS ∪ F.Qs pS) (hQ : F.Qs pS ⊆ (Kfull : Set _)) :
    ∃ a : singularChainGroup ℚ (TopCat.of ↥(F.UT pS)) 2,
      (singularBoundary ℚ (TopCat.of ↥(F.UT pS)) 1).hom a ∈
        subChainSubmodule ℚ (TopCat.of ↥(F.UT pS))
          {u : ↥(F.UT pS) | ‖((F.eY pS pS_isQuotientCovering u : boxSet F.ε F.R0) : R3 × R2).2‖ ≤ F.δ}ᶜ
          1 ∧
      (∀ (W : Rep.{0} ℚ principalSix)
        (K' : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ), K' ≤ Kfull →
        ∀ (φ : Cycles ((supportCochains pS W
          (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).sc' (2 - 1) 2 (2 + 1)))
          (φh : Cycles ((supportCochains wholeProjection W
            ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K' :
              Compacts BordifiedOrbit) : Set BordifiedOrbit)).sc' (2 - 1) 2 (2 + 1))),
          (∀ τ : SingularSimplex (TopCat.of Space) 2,
            vertexToFunction pS pS_isQuotientCovering
                ((supportInclusion pS W
                  (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val) τ =
              vertexToFunction wholeProjection wholeQuotientCovering
                ((supportInclusion wholeProjection W
                  ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K' :
                    Compacts BordifiedOrbit) : Set BordifiedOrbit)).f 2 φh.val)
                (projection upstairs 2 τ)) →
          (ambientCochain W
              (openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K') φh).hom
              flatRep =
            chainDesc (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
              vertexToFunction pS pS_isQuotientCovering
                ((supportInclusion pS W
                  (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val)
                (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ)) a) ∧
      (singularBoundary ℚ (TopCat.of R2) 1).hom
          ((singularChainMap ℚ ((F.sec pS pS_isQuotientCovering ≫ psiHom) ≫ rhoEHom ≫ scale2 F.δ⁻¹) 2).hom a) ∈
        subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 ∧
      ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom
          ((singularChainMap ℚ ((F.sec pS pS_isQuotientCovering ≫ psiHom) ≫ rhoEHom ≫ scale2 F.δ⁻¹) 2).hom a)) = 0,
        degR2 ((singularChainMap ℚ ((F.sec pS pS_isQuotientCovering ≫ psiHom) ≫ rhoEHom ≫ scale2 F.δ⁻¹) 2).hom a)
          h = lam2 := by
  have hp := pS_isQuotientCovering
  have hKA := openCompactImage_subset CompactInteriorRelativeBoundary.boundaryComplementOpen Kfull
  have hKT : ∀ S : Space, S ∈ flat →
      wholeProjection (embedding S) ∈
        ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen Kfull :
          Compacts BordifiedOrbit) : Set BordifiedOrbit) → S ∈ F.Tt := by
    intro S hS hmem
    obtain ⟨k, hk, hkS⟩ := hmem
    have hkp : k = pS S := Subtype.ext (hkS.trans (wholeProjection_embedding S))
    rw [hkp] at hk
    exact F.flat_over pS hp (Kfull : Set _) hK S hS hk
  set Kh : Compacts BordifiedOrbit := openCompactImage
    CompactInteriorRelativeBoundary.boundaryComplementOpen Kfull with hKh
  obtain ⟨FT, hFT, FA, hFA, u, hdec, hFTb⟩ := flat_localize_D F.Tt F.Tt_open Kh hKA hKT
  obtain ⟨c, hc⟩ := (subChainCorestrict_bijective (R := ℚ) (X := FDT) (VO F) 2).2 ⟨FT, hFT⟩
  have hc' : (singularChainMap ℚ (sInclusion (X := FDT) (VO F)) 2).hom c = FT := congrArg Subtype.val hc
  -- the boundary of `c`
  have hbc : (singularBoundary ℚ (TopCat.of (VO F)) 1).hom c ∈
      subChainSubmodule ℚ (TopCat.of (VO F)) (Subtype.val ⁻¹' (PiD ⁻¹' (embedding '' F.Tt ∩
        (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ))) 1 := by
    refine mem_sub_of_inclusion_mem (B := FDT) (VO F) _ 1 _ ?_
    rw [← singularChainMap_boundary_apply, hc']
    exact hFTb
  have hslab : ∀ x : VO F, PiD x.1 ∈ embedding '' F.Tt ∩ (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ →
      F.δ < ‖((F.eY pS hp (kap F x) : boxSet F.ε F.R0) : R3 × R2).2‖ := fun x hx =>
    slab_of_notP F Kfull hQ x hx.2
  refine ⟨(singularChainMap ℚ (kapHom F) 2).hom c, ?_, ?_, ?_⟩
  · -- the boundary of the chart chain is off the slab
    rw [singularChainMap_boundary_apply]
    refine singularChainMap_mem_sub (kapHom F) _ 1 ?_
    refine subChainSubmodule_mono ?_ 1 hbc
    intro x hx hle
    exact absurd hle (not_le.mpr (hslab x hx))
  · -- the evaluation clause
    intro W K' hK' φ φh hvt
    have hKle := openCompactImage_mono (K := Kfull) hK'
    have hflat := flat_eval_D Kh FT FA u hdec hFA W _ hKle φh
    have hchart : (singularChainMap ℚ (F.chartHom pS hp) 2).hom ((singularChainMap ℚ (kapHom F) 2).hom c) =
        (singularChainMap ℚ PiHom 2).hom FT := by
      have e1 : (singularChainMap ℚ (kapHom F ≫ F.chartHom pS hp) 2).hom c =
          (singularChainMap ℚ (F.chartHom pS hp) 2).hom ((singularChainMap ℚ (kapHom F) 2).hom c) := by
        rw [singularChainMap_comp]; rfl
      have e2 : (singularChainMap ℚ (sInclusion (X := FDT) (VO F) ≫ PiHom) 2).hom c =
          (singularChainMap ℚ PiHom 2).hom ((singularChainMap ℚ (sInclusion (X := FDT) (VO F)) 2).hom c) := by
        rw [singularChainMap_comp]; rfl
      rw [← e1, chartHom_kap, e2, hc']
    rw [hflat, ← hchart, ambientCochain_chart_chain W _ φh (F.chartHom pS hp) _]
    have hfun : (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
        vertexToFunction wholeProjection wholeQuotientCovering
          ((supportInclusion wholeProjection W ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K' : Compacts BordifiedOrbit) : Set BordifiedOrbit)).f 2 φh.val)
          (pushSimplex (F.chartHom pS hp) 2 σ)) =
        (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
          vertexToFunction pS pS_isQuotientCovering
            ((supportInclusion pS W
              (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val)
            (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ)) :=
      funext fun σ => (hvt (pushSimplex (F.sec pS hp) 2 σ)).symm
    rw [hfun]
  · -- the degree clause
    have hGsub : ∀ x : VO F, PiD x.1 ∈ embedding '' F.Tt ∩ (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ →
        1 < ‖(G0 F).hom x‖ := by
      intro x hx
      rw [norm_G0, inv_mul_eq_div, lt_div_iff₀ F.hδ, one_mul]
      exact hslab x hx
    have hbG : (singularBoundary ℚ (TopCat.of (VO F)) 1).hom c ∈
        subChainSubmodule ℚ (TopCat.of (VO F)) {x : VO F | 1 < ‖(G0 F).hom x‖} 1 :=
      subChainSubmodule_mono (fun x hx => hGsub x hx) 1 hbc
    have hCeq : (singularChainMap ℚ ((F.sec pS hp ≫ psiHom) ≫ rhoEHom ≫ scale2 F.δ⁻¹) 2).hom
        ((singularChainMap ℚ (kapHom F) 2).hom c) = (singularChainMap ℚ (G0 F) 2).hom c := by
      have e1 : (singularChainMap ℚ (G0 F) 2).hom c =
          (singularChainMap ℚ ((F.sec pS hp ≫ psiHom) ≫ rhoEHom ≫ scale2 F.δ⁻¹) 2).hom
            ((singularChainMap ℚ (kapHom F) 2).hom c) := by
        unfold G0
        rw [singularChainMap_comp]; rfl
      exact e1.symm
    rw [hCeq]
    refine ⟨?_, ?_⟩
    · rw [singularChainMap_boundary_apply]
      exact singularChainMap_mem_sub (G0 F) {v : R2 | 1 < ‖v‖} 1 hbG
    · obtain ⟨h0, h1, heq⟩ := deg_G0_eq_G1 F c hbG
      have hG1 : (singularChainMap ℚ (G1 F) 2).hom c = (singularChainMap ℚ LamHom 2).hom FT := by
        have e1 : (singularChainMap ℚ (G1 F) 2).hom c = (singularChainMap ℚ LamHom 2).hom
            ((singularChainMap ℚ (sInclusion (X := FDT) (VO F)) 2).hom c) := by
          unfold G1
          rw [singularChainMap_comp]; rfl
        rw [e1, hc']
      have hP0 : ∀ x : FD, x ∈ PiD ⁻¹' (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ → LamD x ≠ 0 := by
        intro x hx h0
        obtain ⟨S, hS, hQS⟩ := LamD_zero_mem_Qs F x h0
        apply hx
        refine ⟨(pS.hom S), hQ hQS, ?_⟩
        show _ = wholeProjection (PiD x)
        rw [hS]
        rfl
      have hFT' : (singularBoundary ℚ FDT 1).hom FT ∈
          subChainSubmodule ℚ FDT (PiD ⁻¹' (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ) 1 :=
        subChainSubmodule_mono (Set.preimage_mono Set.inter_subset_right) 1 hFTb
      obtain ⟨hL, hLd⟩ := deg_Lam_eq (PiD ⁻¹' (wholeProjection ⁻¹' (Kh : Set BordifiedOrbit))ᶜ) hP0
        FT FA u hdec hFA hFT'
      refine ⟨h0, ?_⟩
      rw [heq, degR2_congr _ _ hG1 h1 hL]
      exact hLd

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
