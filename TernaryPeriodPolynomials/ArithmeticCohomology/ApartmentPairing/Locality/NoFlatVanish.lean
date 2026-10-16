module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ChartData
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.PairRelation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.FrameFor

@[expose] public section


/-!
# Lemma 3.3, G3: a cellular cycle without a `T₀`-orbit term has zero apartment evaluation

If the coefficient at `T₀` of a cellular top cycle `z` vanishes, then `z` lies in the span of finitely many top
cells none of which is a translate of `T₀` (`exists_cellSpan_offT0`); the Γ(6)-saturation of those cells is a
closed set missing the flat, so there is a Γ(6)-invariant open neighbourhood of it missing the flat
(`tube_proper`), the dual of `z` can be taken supported in that neighbourhood (`dual_data_open`), and the flat
chain, being carried off the support, is killed (`flat_localize` with the empty chart).  This is the
non-vanishing input of the global bridge: `evaluation_eq_zero_of_coeff_zero`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

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
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.OrdinaryTopBoundaryComparison
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33

/-- The coinvariant class of a generator is invariant under translating cell and coefficient together. -/
theorem coinvMk_translate (W : Rep.{0} ℚ principalSix) (w : W) (g : principalSix) (C : Graded 3) :
    Rep.coinvariantsTensorMk W (cellRep 3) (W.ρ g w) (MonoidAlgebra.single (g • C) 1) =
      Rep.coinvariantsTensorMk W (cellRep 3) w (MonoidAlgebra.single C 1) := by
  have h1 : (cellRep 3).ρ g (MonoidAlgebra.single C (1 : ℚ)) = MonoidAlgebra.single (g • C) 1 :=
    Representation.ofMulAction_single (k := ℚ) g C 1
  rw [← h1]
  have := Representation.Coinvariants.mk_self_apply (W.ρ.tprod (cellRep 3).ρ) g
    (w ⊗ₜ[ℚ] (MonoidAlgebra.single C (1 : ℚ)))
  rw [Representation.tprod_apply, TensorProduct.map_tmul] at this
  exact this

/-- The elementary chain `[w ⊗ C]` as a linear function of `w`. -/
def genLin (W : Rep.{0} ℚ principalSix) (C : Graded 3) : W →ₗ[ℚ] (cellCoinv W).X 3 :=
  (Rep.coinvariantsTensorMk W (cellRep 3)).flip (MonoidAlgebra.single C 1)

theorem genLin_apply (W : Rep.{0} ℚ principalSix) (C : Graded 3) (w : W) :
    genLin W C w = Rep.coinvariantsTensorMk W (cellRep 3) w (MonoidAlgebra.single C 1) := rfl

/-- A cellular chain with vanishing coefficient at `T₀` is carried by finitely many cells, none of which is a
translate of `T₀`. -/
theorem exists_cellSpan_offT0 (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz0 : (coeffAtT0 W).hom z = 0) :
    ∃ 𝒞 : Finset (Graded 3), (∀ C ∈ 𝒞, ∀ g : principalSix, g • C ≠ T0g) ∧ z ∈ cellSpan W 𝒞 := by
  obtain ⟨𝒞, h𝒞⟩ := exists_cellSpan W z
  set 𝒞' : Finset (Graded 3) := 𝒞.filter (fun C => ∀ g : principalSix, g • C ≠ T0g) with h𝒞'
  refine ⟨𝒞', fun C hC => (Finset.mem_filter.mp hC).2, ?_⟩
  have hS : ∀ s ∈ cellSpan W 𝒞', (coeffAtT0 W).hom s = 0 := by
    intro s hs
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
    · rintro x ⟨C, hC, w, rfl⟩
      exact coeffAtT0_of_ne W w C (Finset.mem_filter.mp hC).2
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [map_smul, hx, smul_zero]
  have key : ∀ x ∈ cellSpan W 𝒞, ∃ s ∈ cellSpan W 𝒞', ∃ u : W,
      x = s + genLin W T0g u := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro x ⟨C, hC, w, rfl⟩
      by_cases h : ∀ g : principalSix, g • C ≠ T0g
      · exact ⟨_, Submodule.subset_span ⟨C, Finset.mem_filter.mpr ⟨hC, h⟩, w, rfl⟩, 0, by
          show genLin W C w = genLin W C w + genLin W T0g 0
          rw [map_zero, add_zero]⟩
      · push Not at h
        obtain ⟨g, hg⟩ := h
        refine ⟨0, Submodule.zero_mem _, W.ρ g w, ?_⟩
        rw [zero_add, genLin_apply, ← hg, coinvMk_translate]
    · exact ⟨0, Submodule.zero_mem _, 0, by rw [map_zero, add_zero]⟩
    · rintro x y _ _ ⟨s, hs, u, rfl⟩ ⟨s', hs', u', rfl⟩
      refine ⟨s + s', Submodule.add_mem _ hs hs', u + u', ?_⟩
      rw [map_add]
      abel
    · rintro a x _ ⟨s, hs, u, rfl⟩
      refine ⟨a • s, Submodule.smul_mem _ _ hs, a • u, ?_⟩
      rw [map_smul, smul_add]
  obtain ⟨s, hs, u, hx⟩ := key z h𝒞
  have hu : u = 0 := by
    have h := congrArg (fun x => (coeffAtT0 W).hom x) hx
    simp only at h
    rw [hz0, map_add, hS s hs, genLin_apply, coeffAtT0_mk, coeffVal_eq W u T0g 1 (one_smul _ _),
      zero_add] at h
    simpa using h.symm
  rw [hx, hu, map_zero, add_zero]
  exact hs

/-- A `Γ(6)`-invariant open neighbourhood of a closed invariant set missing the flat that itself misses the flat:
the complement of the saturation of a thin tube. -/
theorem exists_open_nbhd_missing_flat (N : Set Space) (hNc : IsClosed N)
    (hNinv : ∀ (g : principalSix) (S : Space), S ∈ N → g • S ∈ N) (hNF : ∀ S ∈ N, S ∉ flat) :
    ∃ D : Set Space, IsOpen D ∧ N ⊆ D ∧
      ∀ (S S' : Space) (g : principalSix), S ∈ flat → g • S = S' → S' ∉ D := by
  obtain ⟨ρ', hρc, hρpos, -, hρN, hρfin⟩ := tube_proper 1 one_pos N hNc hNF
  have hGt : IsClosed (⋃ g : principalSix, g • tube ρ') := by
    have := isClosed_biUnion_smul (tube ρ') (isClosed_tube hρc) (tube_finite_inv hρfin) Set.univ
    simpa using this
  refine ⟨(⋃ g : principalSix, g • tube ρ')ᶜ, hGt.isOpen_compl, ?_, ?_⟩
  · intro S hS hSG
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hSG
    have h1 : h⁻¹ • S ∈ tube ρ' := Set.mem_smul_set_iff_inv_smul_mem.mp hh
    have h2 : h⁻¹ • S ∈ N := hNinv h⁻¹ S hS
    exact absurd h1 (not_le.mpr (hρN _ h2))
  · intro S S' g hSf hgS hS'
    apply hS'
    subst hgS
    have hS0 : piR3 S = 0 := hSf
    have hSt : S ∈ tube ρ' := by
      change ‖piR3 S‖ ≤ ρ' S
      rw [hS0, norm_zero]
      exact (hρpos S).le
    exact (smul_mem_saturation_iff g (tube ρ') S).mpr (Set.mem_iUnion.mpr ⟨1, by rw [one_smul]; exact hSt⟩)

/-- **A cellular top cycle with vanishing coefficient at `T₀` has zero apartment evaluation.** -/
theorem evaluation_eq_zero_of_coeff_zero (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0) (hz0 : (coeffAtT0 W).hom z = 0) :
    (groupApartmentEvaluation W).hom ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) = 0 := by
  have hp := pS_isQuotientCovering
  obtain ⟨𝒞, hoff, hz𝒞⟩ := exists_cellSpan_offT0 W z hz0
  let N : Set Space := ⋃ C ∈ 𝒞, ⋃ g : principalSix, g • cellSet 3 C.1
  have hNc : IsClosed N :=
    isClosed_biUnion_finset fun C _ => isClosed_saturation _ (isCompact_cellSet 3 C.1)
  have hNmem : ∀ S : Space, S ∈ N ↔ ∃ C ∈ 𝒞, ∃ g : principalSix, S ∈ g • cellSet 3 C.1 := by
    intro S
    simp only [N, Set.mem_iUnion, exists_prop]
  have hNinv : ∀ (g : principalSix) (S : Space), S ∈ N → g • S ∈ N := by
    intro g S hS
    obtain ⟨C, hC, h, hSh⟩ := (hNmem S).mp hS
    refine (hNmem _).mpr ⟨C, hC, g * h, ?_⟩
    rw [mul_smul]
    exact Set.smul_mem_smul_set hSh
  have hNF : ∀ S ∈ N, S ∉ flat := by
    intro S hS
    obtain ⟨C, hC, g, hSg⟩ := (hNmem S).mp hS
    rw [cellSet_smul] at hSg
    have hne : g • C.1 ≠ T0g.1 := fun h => hoff C hC g (Subtype.ext h)
    exact cellSet_not_flat 3 (g • C.1) hne S hSg
  obtain ⟨D, hDo, hND, hDfl⟩ := exists_open_nbhd_missing_flat N hNc hNinv hNF
  have hFD : ∀ C ∈ 𝒞, ∀ g : principalSix, g • cellSet 3 C.1 ⊆ D :=
    fun C hC g S hS => hND ((hNmem S).mpr ⟨C, hC, g, hS⟩)
  have hzS : (coinvariantChains principalSix SpaceTop W).d 3 2 ((cellCoinvMapS W).f 3 z) = 0 := by
    have h := ConcreteCategory.congr_hom ((cellCoinvMapS W).comm 3 2) z
    refine h.trans ?_
    change (cellCoinvMapS W).f 2 (((cellCoinv W).d 3 2) z) = 0
    rw [hz, map_zero]
  obtain ⟨K, hK, y₁, φ, φh, hy₁, hφ, hvt, hcap⟩ := dual_data_open D hDo 𝒞 hFD W z hz hz𝒞 hzS
  have hKA := openCompactImage_subset CompactInteriorRelativeBoundary.boundaryComplementOpen K
  rw [ev_eq_ambient W _ hKA φh z hz hcap]
  have hKT : ∀ S : Space, S ∈ flat →
      wholeProjection (embedding S) ∈
        ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
          Compacts BordifiedOrbit) : Set BordifiedOrbit) → S ∈ (∅ : Set Space) := by
    intro S hSf hmem
    obtain ⟨k, hk, hkS⟩ := hmem
    have hkp : k = pS S := Subtype.ext (hkS.trans (wholeProjection_embedding S))
    rw [hkp] at hk
    obtain ⟨S', hS'D, hS'⟩ := hK hk
    obtain ⟨g, hg⟩ := (cover_eq_iff pS hp S' S).mp hS'
    exact hDfl S S' g hSf hg hS'D
  obtain ⟨FT, hFT, -, hFTev⟩ := flat_localize ∅ isOpen_empty _ hKA hKT
  rw [hFTev W _ le_rfl φh]
  rw [Set.image_empty, subChainSubmodule_empty] at hFT
  rw [(Submodule.mem_bot ℚ).mp hFT]
  exact LinearMap.map_zero (ambientCochain W _ φh).hom.toLinearMap

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
