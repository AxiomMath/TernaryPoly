module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize

@[expose] public section


/-!
# Triad decomposition of a chain

`triad_decomp`: if `U, V` are open, `w` is a chain carried by `U ∪ V` whose boundary is a sum of a chain over `U` and a
chain over `V`, then `w` is, up to a boundary, a sum of a chain over `U` and a chain over `V` (iterated barycentric
subdivision in the subspace `U ∪ V`).  This is the chain-level form of excision for the triad `(X; U, V)`.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory
open TernaryPeriodPolynomials.Argument.Lemma33.Locality

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

variable {X : TopCat.{0}}

/-- **Triad decomposition.**  If `U, V` are open, `w` is a chain carried by `U ∪ V` and `∂ w` is a sum of a chain
over `U` and a chain over `V`, then `w` is, up to a boundary, a sum of a chain over `U` and a chain over `V`. -/
theorem triad_decomp (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (w : singularChainGroup ℚ X (n + 1)) (hw : w ∈ subChainSubmodule ℚ X (U ∪ V) (n + 1))
    (hb : (singularBoundary ℚ X n).hom w ∈ subChainSubmodule ℚ X U n ⊔ subChainSubmodule ℚ X V n) :
    ∃ wU ∈ subChainSubmodule ℚ X U (n + 1), ∃ wV ∈ subChainSubmodule ℚ X V (n + 1),
      ∃ u : singularChainGroup ℚ X (n + 2), w = wU + wV + (singularBoundary ℚ X (n + 1)).hom u := by
  set W : Set X := U ∪ V with hWdef
  let ι := sInclusion W
  obtain ⟨w', hw'⟩ := (subChainCorestrict_bijective (R := ℚ) W (n + 1)).2 ⟨w, hw⟩
  have hw'' : (singularChainMap ℚ ι (n + 1)).hom w' = w := congrArg Subtype.val hw'
  have hbd : (singularChainMap ℚ ι n).hom ((singularBoundary ℚ (TopCat.of W) n).hom w') =
      (singularBoundary ℚ X n).hom w := by
    rw [← hw'']
    exact (singularChainMap_boundary_apply ℚ ι n w').symm
  obtain ⟨a, ha, b, hbmem, hab⟩ := Submodule.mem_sup.mp hb
  have hUW : U ⊆ W := Set.subset_union_left
  have hVW : V ⊆ W := Set.subset_union_right
  obtain ⟨a', ha'⟩ := (subChainCorestrict_bijective (R := ℚ) W n).2
    ⟨a, subChainSubmodule_mono hUW n ha⟩
  obtain ⟨b', hb'⟩ := (subChainCorestrict_bijective (R := ℚ) W n).2
    ⟨b, subChainSubmodule_mono hVW n hbmem⟩
  have ha'' : (singularChainMap ℚ ι n).hom a' = a := congrArg Subtype.val ha'
  have hb'' : (singularChainMap ℚ ι n).hom b' = b := congrArg Subtype.val hb'
  have hinj : Function.Injective (singularChainMap ℚ ι n).hom :=
    singularChainMap_injective_of_pushSimplex_injective _ _ (pushSimplex_sInclusion_injective W n)
  have hbd' : (singularBoundary ℚ (TopCat.of W) n).hom w' = a' + b' := by
    apply hinj
    rw [map_add, ha'', hb'', hbd, hab]
  have haU : a' ∈ subChainSubmodule ℚ (TopCat.of W) (Subtype.val ⁻¹' U) n :=
    mem_sub_of_inclusion_mem W U n a' (by rw [ha'']; exact ha)
  have hbV : b' ∈ subChainSubmodule ℚ (TopCat.of W) (Subtype.val ⁻¹' V) n :=
    mem_sub_of_inclusion_mem W V n b' (by rw [hb'']; exact hbmem)
  have hcov : (Subtype.val ⁻¹' U : Set (TopCat.of W)) ∪ (Subtype.val ⁻¹' V) ∪ (∅ : Set (TopCat.of W)) =
      Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_empty_iff_false, or_false, Set.mem_univ, iff_true]
    exact x.2
  have hUo : IsOpen (Subtype.val ⁻¹' U : Set (TopCat.of W)) := hU.preimage continuous_subtype_val
  have hVo : IsOpen (Subtype.val ⁻¹' V : Set (TopCat.of W)) := hV.preimage continuous_subtype_val
  set 𝒰 := threeCover _ _ _ hUo hVo isOpen_empty hcov with h𝒰
  have hsmall : (singularBoundary ℚ (TopCat.of W) n).hom w' ∈ smallChainSubmodule ℚ (TopCat.of W) 𝒰 n := by
    rw [hbd']
    refine Submodule.add_mem _ ?_ ?_
    · exact subChainSubmodule_le_smallChainSubmodule (𝒰 := 𝒰) (S := Subtype.val ⁻¹' U) (by simp [h𝒰, threeCover]) n haU
    · exact subChainSubmodule_le_smallChainSubmodule (𝒰 := 𝒰) (S := Subtype.val ⁻¹' V) (by simp [h𝒰, threeCover]) n hbV
  obtain ⟨N, hN1, hN2⟩ := exists_iteratedSubdivision_homotopy_boundary_mem_smallChains 𝒰 ℚ n w' hsmall
  have hform := barycentricSubdivisionIter_boundary_formula ℚ (TopCat.of W) N (n + 1) w'
  set s := barycentricSubdivisionIterLinearMap ℚ (TopCat.of W) N (n + 1) w' +
    barycentricSubdivisionIterHomotopyLinearMap ℚ (TopCat.of W) N n ((singularBoundary ℚ (TopCat.of W) n).hom w') with hs
  have hsmem : s ∈ smallChainSubmodule ℚ (TopCat.of W) 𝒰 (n + 1) := Submodule.add_mem _ hN1 hN2
  set u := barycentricSubdivisionIterHomotopyLinearMap ℚ (TopCat.of W) N (n + 1) w' with hu
  have hcs : w' = s + (singularBoundary ℚ (TopCat.of W) (n + 1)).hom u := by
    have := hform
    simp only [barycentricSubdivisionIterHomotopyBoundaryTerm] at this
    have h3 : w' = barycentricSubdivisionIterLinearMap ℚ (TopCat.of W) N (n + 1) w' +
        ((singularBoundary ℚ (TopCat.of W) (n + 1)).hom u +
          barycentricSubdivisionIterHomotopyLinearMap ℚ (TopCat.of W) N n
            ((singularBoundary ℚ (TopCat.of W) n).hom w')) := by
      rw [← this]; abel
    exact h3.trans (by rw [hs]; abel)
  obtain ⟨tU, htU, tV, htV, tE, htE, hsdec⟩ := small_threeCover_decomp _ _ _ hUo hVo isOpen_empty hcov
    (n + 1) hsmem
  have htE0 : tE = 0 := by
    have : tE ∈ (⊥ : Submodule ℚ (singularChainGroup ℚ (TopCat.of W) (n + 1))) := by
      rw [← subChainSubmodule_empty (X := TopCat.of W) (n + 1)]; exact htE
    simpa using this
  refine ⟨(singularChainMap ℚ ι (n + 1)).hom tU, singularChainMap_mem_sub ι U (n + 1) htU,
    (singularChainMap ℚ ι (n + 1)).hom tV, singularChainMap_mem_sub ι V (n + 1) htV,
    (singularChainMap ℚ ι (n + 2)).hom u, ?_⟩
  rw [← hw'', hcs, hsdec, htE0, map_add, map_add, map_add, map_zero, add_zero]
  have := singularChainMap_boundary_apply ℚ ι (n + 1) u
  rw [this]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
