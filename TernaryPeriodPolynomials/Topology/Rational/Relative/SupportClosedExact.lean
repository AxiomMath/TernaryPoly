module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportClosed

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

/-- Exactness of actual rational linear maps transports through specified object isomorphisms. -/
theorem range_eq_ker_transport (S : ShortComplex (ModuleCat.{0} ℚ)) (hS : S.Exact)
    {A B D : ModuleCat.{0} ℚ} (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (a : A ⟶ B) (b : B ⟶ D)
    (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ a) (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ b) :
    LinearMap.range a.hom = LinearMap.ker b.hom := by
  have hab : a ≫ b = 0 := by
    apply (cancel_epi e₁.hom).mp
    rw [← Category.assoc, ← h₁, Category.assoc, ← h₂, ← Category.assoc, S.zero, zero_comp, comp_zero]
  exact (exact_transport S hS e₁ e₂ e₃ a b hab h₁ h₂).moduleCat_range_eq_ker

variable {X : Type} [TopologicalSpace X]

/-- The literal closed-support Mayer–Vietoris sequence is exact at the direct sum. -/
theorem closed_exact_pair (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ) :
    LinearMap.range (closedPair A B k).hom = LinearMap.ker (closedDifference A B k).hom := by
  apply range_eq_ker_transport _ (homology_exact_pair (complementOpen A hA) (complementOpen B hB) k)
    (closedUnionIso A B k).symm (Iso.refl _) (closedIntersectionIso A B k).symm
  · change homologyRestrictionPair Aᶜ Bᶜ k ≫ 𝟙 _ = (closedUnionIso A B k).inv ≫ closedPair A B k
    erw [Category.comp_id, ← closedPair_comm, Iso.inv_hom_id_assoc]
  · change homologyRestrictionDifference Aᶜ Bᶜ k ≫ (closedIntersectionIso A B k).inv = 𝟙 _ ≫ closedDifference A B k
    erw [Category.id_comp, ← closedDifference_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The literal closed-support sequence is exact at union-supported homology. -/
theorem closed_exact_union (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ) :
    LinearMap.range (closedConnecting A B hA hB k).hom = LinearMap.ker (closedPair A B k).hom := by
  apply range_eq_ker_transport _ (homology_exact_union (complementOpen A hA) (complementOpen B hB) k)
    (closedIntersectionIso A B (k+1)).symm (closedUnionIso A B k).symm (Iso.refl _)
  · simp [closedConnecting]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · change homologyRestrictionPair Aᶜ Bᶜ k ≫ 𝟙 _ = (closedUnionIso A B k).inv ≫ closedPair A B k
    erw [Category.comp_id, ← closedPair_comm, Iso.inv_hom_id_assoc]

/-- The literal closed-support sequence is exact at positive-degree intersection-supported homology. -/
theorem closed_exact_intersection (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (k : ℕ) :
    LinearMap.range (closedDifference A B (k+1)).hom = LinearMap.ker (closedConnecting A B hA hB k).hom := by
  apply range_eq_ker_transport _ (homology_exact_intersection (complementOpen A hA) (complementOpen B hB) k)
    (Iso.refl _) (closedIntersectionIso A B (k+1)).symm (closedUnionIso A B k).symm
  · change homologyRestrictionDifference Aᶜ Bᶜ (k+1) ≫ (closedIntersectionIso A B (k+1)).inv =
      𝟙 _ ≫ closedDifference A B (k+1)
    erw [Category.id_comp, ← closedDifference_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simp [closedConnecting]
    exact (Iso.inv_hom_id_assoc _ _).symm

/-- The degree-zero intersection term is the surjective endpoint of the actual support sequence. -/
theorem closed_zero_surjective (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) :
    Function.Surjective (closedDifference A B 0) := by
  have hd := restrictionDifference_zero_surjective (complementOpen A hA) (complementOpen B hB)
  intro z
  obtain ⟨x, hx⟩ := hd ((closedIntersectionIso A B 0).hom z)
  refine ⟨x, (ModuleCat.mono_iff_injective (closedIntersectionIso A B 0).hom).mp inferInstance ?_⟩
  change (closedDifference A B 0 ≫ (closedIntersectionIso A B 0).hom) x = _
  rw [closedDifference_comm]
  exact hx

end TernaryPoly.RationalRelativeSupport
