module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Transport of boundary summands along maps of cuspidal realizations

Let `Φ : σ.H →L[ℂ] σ'.H` be a continuous linear map that sends smooth vectors to smooth vectors and
intertwines the realizations, `realize' (Φ v) = realize v`. Then every source cocycle for `σ ⊗ χ`
is a source cocycle for `σ' ⊗ χ`. Hence the boundary summand of `σ ⊗ χ` lies in that of
`σ' ⊗ χ`, on either side, and isomorphic realizations have equal summands and equal associate
pairs. This is the last step of the strong-multiplicity-one part of constituent separation:
once two inducing data are shown to have isomorphic cuspidal realizations, their summands coincide.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SpectralSeparation

variable {n : ℕ}

/-- A realization-preserving map of cuspidal representations. -/
structure RealizationMap (σ σ' : CuspidalRepresentation) where
  Φ : σ.H →L[ℂ] σ'.H
  smooth : ∀ v ∈ σ.smooth, Φ v ∈ σ'.smooth
  realize : ∀ v : σ.smooth, σ'.realize ⟨Φ v.val, smooth v.val v.property⟩ = σ.realize v

theorem RealizationMap.cuspFunctions_le {σ σ' : CuspidalRepresentation}
    (M : RealizationMap σ σ') : cuspFunctions σ ≤ cuspFunctions σ' := by
  rintro f ⟨v, rfl⟩
  exact ⟨⟨M.Φ v.val, M.smooth v.val v.property⟩, M.realize v⟩

theorem RealizationMap.hasSmoothCuspLift {σ σ' : CuspidalRepresentation}
    (M : RealizationMap σ σ') (χ : RankOneCharacter) (coh : Cohomological σ n)
    (coh' : Cohomological σ' n) {k : ℕ} (side : Side) (s : ℂ)
    (f : (Fin k → RealGL3) → AdelicGL → ℂ)
    (hf : HasSmoothCuspLift (⟨σ, χ, coh⟩ : InducingData n) side s f) :
    HasSmoothCuspLift (⟨σ', χ, coh'⟩ : InducingData n) side s f := by
  intro a
  obtain ⟨v, hsmooth, hv⟩ := hf a
  refine ⟨fun x => ⟨M.Φ (v x).val, M.smooth _ (v x).property⟩, ?_, ?_⟩
  · exact (M.Φ.restrictScalars ℝ).contDiff.comp_contDiffOn hsmooth
  · intro x A
    change σ'.realize ⟨M.Φ (v x).val, M.smooth _ (v x).property⟩ A = _
    rw [M.realize (v x)]
    exact hv x A

theorem RealizationMap.isInduced {σ σ' : CuspidalRepresentation}
    (M : RealizationMap σ σ') (χ : RankOneCharacter) (coh : Cohomological σ n)
    (coh' : Cohomological σ' n) (side : Side) (s : ℂ) (f : AdelicGL → ℂ)
    (hf : IsInduced (⟨σ, χ, coh⟩ : InducingData n) side s f) :
    IsInduced (⟨σ', χ, coh'⟩ : InducingData n) side s f := by
  cases side
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
    exact ⟨h1, h2, M.hasSmoothCuspLift χ coh coh' _ s _ h3, h4, h5,
      fun g => M.cuspFunctions_le (h6 g)⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
    exact ⟨h1, h2, M.hasSmoothCuspLift χ coh coh' _ s _ h3, h4, h5,
      fun g => M.cuspFunctions_le (h6 g)⟩

theorem RealizationMap.isSourceCocycle {σ σ' : CuspidalRepresentation}
    (M : RealizationMap σ σ') (χ : RankOneCharacter) (coh : Cohomological σ n)
    (coh' : Cohomological σ' n) (side : Side)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n)
    (hc : IsSourceCocycle (⟨σ, χ, coh⟩ : InducingData n) side c) :
    IsSourceCocycle (⟨σ', χ, coh'⟩ : InducingData n) side c := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  exact ⟨fun x m => M.isInduced χ coh coh' side _ _ (h1 x m),
    fun m => M.hasSmoothCuspLift χ coh coh' side _ _ (h2 m), h3, h4⟩

/-- A map intertwining the realizations up to a nonzero scalar (as produced by Schur's lemma)
rescales to a realization map. -/
def RealizationMap.ofScalar {σ σ' : CuspidalRepresentation} (Φ : σ.H →L[ℂ] σ'.H)
    (hs : ∀ v ∈ σ.smooth, Φ v ∈ σ'.smooth) (c : ℂ) (hc : c ≠ 0)
    (hr : ∀ v : σ.smooth, σ'.realize ⟨Φ v.val, hs v.val v.property⟩ = c • σ.realize v) :
    RealizationMap σ σ' where
  Φ := c⁻¹ • Φ
  smooth v hv := σ'.smooth.smul_mem _ (hs v hv)
  realize v := by
    have : (⟨(c⁻¹ • Φ) v.val, σ'.smooth.smul_mem _ (hs v.val v.property)⟩ : σ'.smooth) =
        c⁻¹ • ⟨Φ v.val, hs v.val v.property⟩ := rfl
    rw [this, map_smul, hr, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Summand transport.** -/
theorem RealizationMap.boundarySummand_le {σ σ' : CuspidalRepresentation}
    (M : RealizationMap σ σ') (χ : RankOneCharacter) (coh : Cohomological σ n)
    (coh' : Cohomological σ' n) (side : Side) :
    boundarySummand (⟨σ, χ, coh⟩ : InducingData n) side ≤
      boundarySummand (⟨σ', χ, coh'⟩ : InducingData n) side := by
  apply Submodule.span_mono
  rintro a ⟨c, hc, z, hz, rfl⟩
  exact ⟨c, M.isSourceCocycle χ coh coh' side c hc, z, hz, rfl⟩

/-- Realization maps in both directions give equal associate pairs. -/
theorem associatePair_eq_of_realizationMaps {σ σ' : CuspidalRepresentation}
    (M : RealizationMap σ σ') (M' : RealizationMap σ' σ) (χ : RankOneCharacter)
    (coh : Cohomological σ n) (coh' : Cohomological σ' n) :
    associatePair (⟨σ, χ, coh⟩ : InducingData n) =
      associatePair (⟨σ', χ, coh'⟩ : InducingData n) := by
  unfold associatePair
  rw [le_antisymm (M.boundarySummand_le χ coh coh' .plane)
      (M'.boundarySummand_le χ coh' coh .plane),
    le_antisymm (M.boundarySummand_le χ coh coh' .line)
      (M'.boundarySummand_le χ coh' coh .line)]

end TernaryPeriodPolynomials.SpectralSeparation
