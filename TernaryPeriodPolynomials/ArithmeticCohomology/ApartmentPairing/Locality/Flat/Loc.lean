module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Local
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatApartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.HomEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.PDRep

@[expose] public section


/-!
# Lemma 3.3, G3: localization of the compactified flat chain against a cochain supported in a compact

For the ambient equivariant cochain `ambientCochain` of a cocycle supported in a compact `K` of the interior
(`HomEvaluation`): it is a cocycle (`ambientCochain_cocycle`) and vanishes on chains carried off the
preimage of `K` (`ambientCochain_vanish`).  `flat_localize`: if the flat points over `K` lie in an open set
`T` of the symmetric space, the flat chain `flatRep` splits as `FT + FA + ∂u` with `FT` carried by the image
of `T` and with boundary carried off the preimage of `K`, `FA` carried off the preimage of `K`; consequently
every ambient cochain supported in a compact `K' ≤ K` has the same value on `flatRep` and on `FT`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalSupport
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceRelativeCapConnecting
  TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.EquivariantSingularCohomology
  SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision TernaryPoly.SymmetricSpacePositive
  TernaryPeriodPolynomials.Argument.Lemma33

variable (W : Rep.{0} ℚ principalSix) (K : Compacts BordifiedOrbit)

theorem ambientCochain_cocycle
    (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1)))
    (u : (equivariantChains principalSix (TopCat.of Glued)).X 3) :
    (ambientCochain W K φh).hom ((equivariantChains principalSix (TopCat.of Glued)).d 3 2 u) = 0 := by
  have hd : (supportCochains wholeProjection W (K : Set BordifiedOrbit)).d 2 3 φh.val = 0 :=
    φh.property
  have h1 : (localCochains wholeProjection wholeQuotientCovering W).d 2 3
      ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val) = 0 := by
    have := ConcreteCategory.congr_hom
      ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).comm 2 3) φh.val
    refine this.trans ?_
    change (supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 3
      ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).d 2 3 φh.val) = 0
    rw [hd, map_zero]
  have h2 : (cochains principalSix (TopCat.of Glued) W).d 2 3 (ambientCochain W K φh) = 0 := by
    have := ConcreteCategory.congr_hom
      ((cochainIso wholeProjection wholeQuotientCovering W).inv.comm 2 3)
      ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val)
    refine this.trans ?_
    change (cochainIso wholeProjection wholeQuotientCovering W).inv.f 3
      ((localCochains wholeProjection wholeQuotientCovering W).d 2 3
        ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val)) = 0
    rw [h1, map_zero]
  have h3 := congrArg (fun f => f.hom u) (show equivariantD principalSix (TopCat.of Glued) 3 2 ≫
      ambientCochain W K φh = 0 from h2)
  exact h3

theorem ambientCochain_vanish
    (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1)))
    (c : (equivariantChains principalSix (TopCat.of Glued)).X 2)
    (hc : c ∈ subChainSubmodule ℚ (TopCat.of Glued) (wholeProjection ⁻¹' (K : Set BordifiedOrbit))ᶜ 2) :
    (ambientCochain W K φh).hom c = 0 := by
  refine subChainSubmodule_induction (S := (wholeProjection ⁻¹' (K : Set BordifiedOrbit))ᶜ)
    (p := fun x => (ambientCochain W K φh).hom x = 0) ?_ ?_ ?_ ?_ hc
  · intro τ hτ
    change (ambientCochain W K φh).hom (chainElement principalSix (TopCat.of Glued) 2 τ) = 0
    rw [ambientCochain_eval_generator]
    have h1 : IsSubordinate (wholeProjection ⁻¹' (K : Set BordifiedOrbit)ᶜ) τ := by
      rw [Set.preimage_compl]; exact hτ
    have h2 : IsSubordinate (K : Set BordifiedOrbit)ᶜ (projection wholeProjection 2 τ) :=
      (isSubordinate_projection_iff wholeProjection _ τ).mpr h1
    have h3 : ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val)
        (projection wholeProjection 2 τ) = 0 :=
      supportInclusion_vanish wholeProjection W (K : Set BordifiedOrbit) φh.val _ h2
    change (((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val)
      (projection wholeProjection 2 τ)).val ⟨atVertex τ, rfl⟩ = 0
    rw [h3]
    rfl
  · exact map_zero _
  · intro x y hx hy
    have e : (ambientCochain W K φh).hom (x + y) =
        (ambientCochain W K φh).hom.toLinearMap x + (ambientCochain W K φh).hom.toLinearMap y :=
      map_add (ambientCochain W K φh).hom.toLinearMap x y
    rw [e]
    change (ambientCochain W K φh).hom x + (ambientCochain W K φh).hom y = 0
    rw [hx, hy, add_zero]
  · intro r x hx
    have e : (ambientCochain W K φh).hom (r • x) =
        r • (ambientCochain W K φh).hom.toLinearMap x :=
      map_smul (ambientCochain W K φh).hom.toLinearMap r x
    rw [e]
    change r • (ambientCochain W K φh).hom x = 0
    rw [hx, smul_zero]

/-- **Localization of the compactified flat chain.**  If the flat points over the compact `K` lie in the
open set `T` of the symmetric space, the flat chain splits as a chain carried by the image of `T`, a chain
carried off the preimage of `K`, and a boundary; hence every ambient cochain supported in a compact
`K' ≤ K` takes the same value on `flatRep` as on the chain `FT`, which is carried by `T` and has boundary
off the preimage of `K`. -/
theorem flat_localize (T : Set Space) (hT : IsOpen T) (K : Compacts BordifiedOrbit)
    (hKA : (K : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)
    (hKT : ∀ S : Space, S ∈ flat → wholeProjection (embedding S) ∈ (K : Set BordifiedOrbit) →
      S ∈ T) :
    ∃ FT : singularChainGroup ℚ (TopCat.of Glued) 2,
      FT ∈ subChainSubmodule ℚ (TopCat.of Glued) (embedding '' T) 2 ∧
      (singularBoundary ℚ (TopCat.of Glued) 1).hom FT ∈ subChainSubmodule ℚ (TopCat.of Glued)
        (embedding '' T ∩ (wholeProjection ⁻¹' (K : Set BordifiedOrbit))ᶜ) 1 ∧
      ∀ (W : Rep.{0} ℚ principalSix) (K' : Compacts BordifiedOrbit), K' ≤ K →
        ∀ φh : Cycles ((supportCochains wholeProjection W (K' : Set BordifiedOrbit)).sc'
          (2 - 1) 2 (2 + 1)),
        (ambientCochain W K' φh).hom flatRep = (ambientCochain W K' φh).hom FT := by
  set P : Set (TopCat.of Glued) := wholeProjection ⁻¹' (K : Set BordifiedOrbit) with hPdef
  have hPclosed : IsClosed P := K.isCompact.isClosed.preimage wholeProjection.hom.continuous
  have hPint : P ⊆ Set.range embedding := by
    intro x hx
    by_contra hnot
    have : x ∈ projection principalSix ⁻¹' boundary principalSix := by
      rw [projection_preimage_boundary]; exact hnot
    exact hKA hx this
  have hT' : IsOpen (embedding '' T) := embedding_isOpenEmbedding.isOpenMap T hT
  have hflat : flatChain ∈ subChainSubmodule ℚ (TopCat.of Glued) (embedding '' T ∪ Pᶜ) 2 :=
    flatChain_mem_sub _ (fun k q => fk_mem_cover T P hPint hKT k q)
  have hbd : (singularBoundary ℚ (TopCat.of Glued) 1).hom flatChain ∈
      subChainSubmodule ℚ (TopCat.of Glued) Pᶜ 1 := by
    have h1 : (singularBoundary ℚ (TopCat.of Glued) 1).hom flatChain = hexBoundary := d_flatChain
    rw [h1]
    exact hexBoundary_mem_sub Pᶜ (fun x hx hxP => hx (hPint hxP))
  obtain ⟨FT, hFT, FA, hFA, u, hu, hFTb⟩ :=
    localize_relative_chain (embedding '' T) Pᶜ hT' hPclosed.isOpen_compl flatChain hflat hbd
  refine ⟨FT, hFT, hFTb, ?_⟩
  intro W K' hK' φh
  have hFA' : FA ∈ subChainSubmodule ℚ (TopCat.of Glued)
      (wholeProjection ⁻¹' (K' : Set BordifiedOrbit))ᶜ 2 := by
    refine subChainSubmodule_mono ?_ 2 hFA
    exact Set.compl_subset_compl.mpr (Set.preimage_mono hK')
  have hadd : ∀ x y : singularChainGroup ℚ (TopCat.of Glued) 2,
      (ambientCochain W K' φh).hom (x + y) =
        (ambientCochain W K' φh).hom x + (ambientCochain W K' φh).hom y :=
    fun x y => map_add (ambientCochain W K' φh).hom.toLinearMap x y
  have h2 : (ambientCochain W K' φh).hom FA = 0 := ambientCochain_vanish W K' φh FA hFA'
  have h3 : (ambientCochain W K' φh).hom ((singularBoundary ℚ (TopCat.of Glued) 2).hom u) = 0 :=
    ambientCochain_cocycle W K' φh u
  unfold flatRep
  rw [hu, hadd, hadd, h2, h3, add_zero, add_zero]

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
