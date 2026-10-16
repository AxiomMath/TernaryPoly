module

public import TernaryPeriodPolynomials.Topology.SingularLocal.NestedRestriction
public import TernaryPeriodPolynomials.Topology.SingularLocal.CochainExcisionTheorem

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalCoefficient
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalCochainExcision

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Actual neighborhood cochains agree with the genuine relative cochains of the restricted covering. -/
def nestedKernelIso (A D : Set B) : neighborhoodCochains p V A D ≅
    kernel (localRestriction (restrictedProjection p D) (Subtype.val ⁻¹' A) V) :=
  kernel.mapIso _ _ (Iso.refl _) (nestedCochainIso p A D V) (by
    rw [Iso.refl_hom,Category.id_comp]
    exact nestedCochainIso_restriction p A D V)

/-- Restriction to a subspace carries genuine support-K local cochains to support-preimage(K) cochains. -/
def supportToOpen (D K : Set B) : supportCochains p V K ⟶
    supportCochains (restrictedProjection p D) V (Subtype.val ⁻¹' K) :=
  cochainExcisionMap p V Kᶜ D ≫ (nestedKernelIso p V Kᶜ D).hom

/-- The relative support restriction retains literal restriction of its ambient cochain. -/
theorem supportToOpen_inclusion (D K : Set B) :
    supportToOpen p V D K ≫ supportInclusion (restrictedProjection p D) V (Subtype.val ⁻¹' K) =
      supportInclusion p V K ≫ localRestriction p D V := by
  unfold supportToOpen nestedKernelIso
  erw [Category.assoc,kernel.lift_ι,Category.comp_id,cochainExcisionMap_inclusion]

/-- Actual restriction to a subspace is natural for enlargement of the support. -/
theorem supportToOpen_natural (D K L : Set B) (hKL : K ⊆ L) :
    supportMap p V K L hKL ≫ supportToOpen p V D L = supportToOpen p V D K ≫
      supportMap (restrictedProjection p D) V (Subtype.val ⁻¹' K) (Subtype.val ⁻¹' L)
        (Set.preimage_mono hKL) := by
  apply (cancel_mono (supportInclusion (restrictedProjection p D) V (Subtype.val ⁻¹' L))).mp
  rw [Category.assoc,supportToOpen_inclusion,← Category.assoc,supportMap_inclusion,
    Category.assoc,supportMap_inclusion,supportToOpen_inclusion]

/-- A closed support contained in an open neighborhood and its complement cover the base. -/
theorem supportComplement_cover (D : Opens B) (K : Set B) (hK : IsClosed K) (hKD : K ⊆ D) :
    (⟨Kᶜ,hK.isOpen_compl⟩ : Opens B) ⊔ D = ⊤ := by
  ext x
  change (x ∈ Kᶜ ∨ x ∈ D) ↔ True
  simp only [iff_true]
  by_cases hx : x ∈ K
  · exact Or.inr (hKD hx)
  · exact Or.inl hx

/-- Actual fixed-support local-cochain restriction to an open containing the closed support is a
quasi-isomorphism in every degree, for arbitrary rational coefficients. -/
theorem supportToOpen_quasiIso (D : Opens B) (K : Set B) (hK : IsClosed K) (hKD : K ⊆ D) :
    QuasiIso (supportToOpen p V D K) := by
  have := cochainExcisionMap_quasiIso p V (⟨Kᶜ,hK.isOpen_compl⟩ : Opens B) D
    (supportComplement_cover D K hK hKD)
  unfold supportToOpen
  infer_instance

/-- Genuine fixed-support excision, with the actual restriction map as its forward map. -/
def supportExcisionIso (D : Opens B) (K : Set B) (hK : IsClosed K) (hKD : K ⊆ D) (k : ℕ) :
    (supportCochains p V K).homology k ≅
      (supportCochains (restrictedProjection p D) V (Subtype.val ⁻¹' K)).homology k := by
  have := supportToOpen_quasiIso p V D K hK hKD
  exact asIso (homologyMap (supportToOpen p V D K) k)

end TernaryPoly.SingularLocalSupport
