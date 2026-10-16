module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatQuot

@[expose] public section


/-!
# Localization of the glued flat

`flat_localize_D`: the localization of the flat chain, carried out in the glued model `FD` (so that the pieces lift through the six chamber
squares).  Pushing the pieces to the bordification gives the conclusion of `Locality.flat_localize`.

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
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceRelativeCapConnecting
  TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.EquivariantSingularCohomology
  SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision TernaryPoly.SymmetricSpacePositive

theorem PiD_fkD_any (k : ℕ) (hk : k < 6) (q : ℝ × ℝ) : PiD (fkD k q) = fk k (clampSq q).1 := by
  change chamber (hexW (Fin.ofNat 6 k).val) (clampSq q).1 = chamber (hexW k) (clampSq q).1
  simp [Nat.mod_eq_of_lt hk]

theorem fkD_mem (U : Set (TopCat.of Glued)) (k : ℕ) (hk : k < 6) (q : ℝ × ℝ)
    (h : ∀ (k : ℕ) (q : ℝ × ℝ), fk k q ∈ U) : fkD k q ∈ PiD ⁻¹' U := by
  change PiD (fkD k q) ∈ U
  rw [PiD_fkD_any k hk q]
  exact h k _

theorem sqG_mem (U : Set (TopCat.of Glued)) (h : ∀ (k : ℕ) (q : ℝ × ℝ), fk k q ∈ U) (k : ℕ) (hk : k < 6) :
    sqG (fkD k) ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' U) 2 := by
  unfold sqG tri
  refine Submodule.add_mem _ ?_ ?_
  · exact chainGenerator_mem_subChainSubmodule
      (isSubordinate_affSimplex (fkD k) (PiD ⁻¹' U) _ Set.univ convex_univ (fun _ => trivial)
        (fun q _ => fkD_mem U k hk q h))
  · exact chainGenerator_mem_subChainSubmodule
      (isSubordinate_affSimplex (fkD k) (PiD ⁻¹' U) _ Set.univ convex_univ (fun _ => trivial)
        (fun q _ => fkD_mem U k hk q h))

theorem flatD_mem (U : Set (TopCat.of Glued)) (h : ∀ (k : ℕ) (q : ℝ × ℝ), fk k q ∈ U) :
    flatD ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' U) 2 := by
  unfold flatD
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ (sqG_mem U h 0 (by norm_num)) (sqG_mem U h 1 (by norm_num)))
    (sqG_mem U h 2 (by norm_num))) (sqG_mem U h 3 (by norm_num))) (sqG_mem U h 4 (by norm_num)))
    (sqG_mem U h 5 (by norm_num))

theorem hexBoundaryD_mem (U : Set (TopCat.of Glued)) (hU : (Set.range embedding)ᶜ ⊆ U) :
    hexBoundaryD ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' U) 1 := by
  have hs1 : ∀ k : ℕ, k < 6 → sg (fkD k) pv pa ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' U) 1 := by
    intro k hk
    unfold sg seg
    refine chainGenerator_mem_subChainSubmodule
      (isSubordinate_affSimplex (fkD k) (PiD ⁻¹' U) _ {q : ℝ × ℝ | q.2 = 0} convex_second_zero ?_ ?_)
    · intro i
      fin_cases i <;> simp [pv, pa]
    · intro q hq
      change PiD (fkD k q) ∈ U
      rw [PiD_fkD_any k hk q]
      refine hU (fk_edge_not_interior k _ (Or.inr ?_))
      have : q.2 = 0 := hq
      simp [clampSq, this]
  have hs2 : ∀ k : ℕ, k < 6 → sg (fkD k) pv pb ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' U) 1 := by
    intro k hk
    unfold sg seg
    refine chainGenerator_mem_subChainSubmodule
      (isSubordinate_affSimplex (fkD k) (PiD ⁻¹' U) _ {q : ℝ × ℝ | q.1 = 0} convex_first_zero ?_ ?_)
    · intro i
      fin_cases i <;> simp [pv, pb]
    · intro q hq
      change PiD (fkD k q) ∈ U
      rw [PiD_fkD_any k hk q]
      refine hU (fk_edge_not_interior k _ (Or.inl ?_))
      have : q.1 = 0 := hq
      simp [clampSq, this]
  have hk : ∀ k : ℕ, k < 6 → sg (fkD k) pv pa - sg (fkD k) pv pb ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' U) 1 :=
    fun k hk => Submodule.sub_mem _ (hs1 k hk) (hs2 k hk)
  unfold hexBoundaryD
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ (hk 0 (by norm_num)) (hk 1 (by norm_num))) (hk 2 (by norm_num)))
    (hk 3 (by norm_num))) (hk 4 (by norm_num))) (hk 5 (by norm_num))

/-- **Localization of the glued flat chain.** -/
theorem flat_localize_D (T : Set Space) (hT : IsOpen T) (K : Compacts BordifiedOrbit)
    (hKA : (K : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)
    (hKT : ∀ S : Space, S ∈ flat → wholeProjection (embedding S) ∈ (K : Set BordifiedOrbit) → S ∈ T) :
    ∃ FT ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' (embedding '' T)) 2,
      ∃ FA ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' (wholeProjection ⁻¹' (K : Set BordifiedOrbit))ᶜ) 2,
      ∃ u : singularChainGroup ℚ FDT 3,
        flatD = FT + FA + (singularBoundary ℚ FDT 2).hom u ∧
        (singularBoundary ℚ FDT 1).hom FT ∈ subChainSubmodule ℚ FDT
          (PiD ⁻¹' (embedding '' T ∩ (wholeProjection ⁻¹' (K : Set BordifiedOrbit))ᶜ)) 1 := by
  set P : Set (TopCat.of Glued) := wholeProjection ⁻¹' (K : Set BordifiedOrbit) with hPdef
  have hPclosed : IsClosed P := K.isCompact.isClosed.preimage wholeProjection.hom.continuous
  have hPint : P ⊆ Set.range embedding := by
    intro x hx
    by_contra hnot
    have : x ∈ projection principalSix ⁻¹' boundary principalSix := by
      rw [projection_preimage_boundary]; exact hnot
    exact hKA hx this
  have hT' : IsOpen (embedding '' T) := embedding_isOpenEmbedding.isOpenMap T hT
  have hTD : IsOpen (PiD ⁻¹' (embedding '' T) : Set FDT) := hT'.preimage continuous_PiD
  have hAD : IsOpen (PiD ⁻¹' Pᶜ : Set FDT) := hPclosed.isOpen_compl.preimage continuous_PiD
  have hF : flatD ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' (embedding '' T) ∪ PiD ⁻¹' Pᶜ) 2 :=
    flatD_mem (embedding '' T ∪ Pᶜ) (fun k q => fk_mem_cover T P hPint (fun S hS hSP => hKT S hS hSP) k q)
  have hFA : (singularBoundary ℚ FDT 1).hom flatD ∈ subChainSubmodule ℚ FDT (PiD ⁻¹' Pᶜ) 1 := by
    rw [d_flatD]
    exact hexBoundaryD_mem Pᶜ (fun x hx hxP => hx (hPint hxP))
  obtain ⟨FT, hFT, FA, hFA', u, hu, hFTb⟩ := localize_relative_chain (X := FDT)
    (PiD ⁻¹' (embedding '' T)) (PiD ⁻¹' Pᶜ) hTD hAD flatD hF hFA
  exact ⟨FT, hFT, FA, hFA', u, hu, hFTb⟩

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
