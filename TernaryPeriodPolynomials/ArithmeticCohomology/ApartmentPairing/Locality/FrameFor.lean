module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BridgeFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Support
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.MapS

@[expose] public section


/-!
# Lemma 3.3, G3: the frame for a finite set of top cells

`Rset 𝒞` is the `Γ(6)`-saturation of the carriers of the top cells in `𝒞` (closed, invariant, meeting the flat
at most in the identity form) and `R2set 𝒞` collects the carriers of the translates of those cells other than
`T₀` and of the faces of `T₀` (closed, missing the flat).  `frame_for` applies the frame theorem to them: a
`FrameOut` whose neighbourhood `D` contains every translate of each carrier and whose tube radius is below
`‖π‖` on the carriers of the other translates and of the faces of `T₀`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.IntegralGL3Congruence
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

/-- The `Γ(6)`-saturation of the carriers of a finite set of top cells. -/
def Rset (𝒞 : Finset (Graded 3)) : Set Space :=
  ⋃ C ∈ 𝒞, ⋃ g : principalSix, g • cellSet 3 C.1

/-- The carriers of the lower cells in the boundary of `T₀` and of the translates of the cells other
than `T₀`. -/
def R2set (𝒞 : Finset (Graded 3)) : Set Space :=
  (⋃ C ∈ 𝒞, ⋃ g ∈ {g : principalSix | g • C.1 ≠ T0}, g • cellSet 3 C.1) ∪
    ⋃ D ∈ (incQ T0).support, cellSet 2 D

theorem Rset_closed (𝒞 : Finset (Graded 3)) : IsClosed (Rset 𝒞) :=
  𝒞.finite_toSet.isClosed_biUnion fun C _ => isClosed_saturation _ (isCompact_cellSet 3 C.1)

theorem Rset_invariant (𝒞 : Finset (Graded 3)) (g : principalSix) (S : Space) (hS : S ∈ Rset 𝒞) :
    g • S ∈ Rset 𝒞 := by
  obtain ⟨C, hC, hSC⟩ := Set.mem_iUnion₂.mp hS
  exact Set.mem_iUnion₂.mpr ⟨C, hC, (smul_mem_saturation_iff g _ S).mpr hSC⟩

theorem Rset_flat (𝒞 : Finset (Graded 3)) (S : Space) (hS : S ∈ Rset 𝒞) (hf : S ∈ flat) :
    S = p0 := by
  obtain ⟨C, hC, hSC⟩ := Set.mem_iUnion₂.mp hS
  obtain ⟨g, hgS⟩ := Set.mem_iUnion.mp hSC
  rw [cellSet_smul] at hgS
  by_cases hg : g • C.1 = T0
  · rw [hg] at hgS
    exact cellSet_flat_T0 3 S hgS hf
  · exact absurd hf (cellSet_not_flat 3 _ hg S hgS)

theorem R2set_closed (𝒞 : Finset (Graded 3)) : IsClosed (R2set 𝒞) := by
  refine IsClosed.union ?_ ?_
  · exact 𝒞.finite_toSet.isClosed_biUnion fun C _ =>
      isClosed_biUnion_smul_compact _ (isCompact_cellSet 3 C.1) _
  · exact (Finset.finite_toSet _).isClosed_biUnion fun D _ => (isCompact_cellSet 2 D).isClosed

theorem R2set_flat (𝒞 : Finset (Graded 3)) (S : Space) (hS : S ∈ R2set 𝒞) : S ∉ flat := by
  rcases hS with hS | hS
  · obtain ⟨C, hC, hSC⟩ := Set.mem_iUnion₂.mp hS
    obtain ⟨g, hg, hgS⟩ := Set.mem_iUnion₂.mp hSC
    rw [cellSet_smul] at hgS
    exact cellSet_not_flat 3 _ hg S hgS
  · obtain ⟨D, hD, hDS⟩ := Set.mem_iUnion₂.mp hS
    have hne : D ≠ T0 := by
      intro hDT
      have := incQ_grade T0 D (Finsupp.mem_support_iff.mp hD)
      rw [hDT] at this
      omega
    exact cellSet_not_flat 2 D hne S hDS

/-- **The frame for a finite set of top cells.** -/
theorem frame_for (𝒞 : Finset (Graded 3)) :
    ∃ F : FrameOut,
      (∀ C ∈ 𝒞, ∀ g : principalSix, g • cellSet 3 C.1 ⊆ F.D) ∧
      (∀ C ∈ 𝒞, ∀ g : principalSix, g • C.1 ≠ T0 →
        cellSet 3 (g • C.1) ⊆ {S : Space | F.ρ' S < ‖piR3 S‖}) ∧
      (∀ D ∈ (incQ T0).support, cellSet 2 D ⊆ {S : Space | F.ρ' S < ‖piR3 S‖}) := by
  obtain ⟨ε, R0, δ, ρ', D, hε, hδ, hδR, hρc, hρpos, hρε, hinj, hone, hfin, hDo, hDg, hRD, hDt,
    hDz, hR2⟩ := frame (Rset 𝒞) (R2set 𝒞) (Rset_closed 𝒞) (Rset_invariant 𝒞)
    (fun S hS hf => Rset_flat 𝒞 S hS hf) (R2set_closed 𝒞) (R2set_flat 𝒞)
  refine ⟨⟨ε, R0, δ, ρ', D, hε, hδ, hδR, hρc, hρpos, hρε, hinj, hone, hfin, hDo, hDg, hDt, hDz⟩,
    ?_, ?_, ?_⟩
  · intro C hC g S hS
    apply hRD
    exact Set.mem_iUnion₂.mpr ⟨C, hC, Set.mem_iUnion.mpr ⟨g, hS⟩⟩
  · intro C hC g hg S hS
    rw [← cellSet_smul] at hS
    apply hR2
    exact Or.inl (Set.mem_iUnion₂.mpr ⟨C, hC, Set.mem_iUnion₂.mpr ⟨g, hg, hS⟩⟩)
  · intro D hD S hS
    apply hR2
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨D, hD, hS⟩)

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
