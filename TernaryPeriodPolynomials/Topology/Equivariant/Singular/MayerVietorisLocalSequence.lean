module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallRestrictedNaturality
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisSeparated
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisSequence

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall TopologicalSpace
open SingularLocalCoefficient

/-- Transfer of a genuine short complex through three specified object isomorphisms. -/
def transportShortComplex {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
    {X Y Z : C} (e₁ : S.X₁ ≅ X) (e₂ : S.X₂ ≅ Y) (e₃ : S.X₃ ≅ Z) : ShortComplex C :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    simp only [Category.assoc, e₂.hom_inv_id_assoc, ← Category.assoc S.f S.g, S.zero,
      zero_comp, comp_zero])

/-- The actual comparison with the short complex transported by specified isomorphisms. -/
def transportShortComplexIso {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
    {X Y Z : C} (e₁ : S.X₁ ≅ X) (e₂ : S.X₂ ≅ Y) (e₃ : S.X₃ ≅ Z) :
    S ≅ transportShortComplex S e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃ (by simp [transportShortComplex]) (by simp [transportShortComplex])

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (A D : Opens B) (hAD : A ⊔ D = ⊤)

/-- The actual open preimage of a base open set under the quotient covering. -/
abbrev preimageOpen (A : Opens B) : Opens E := ⟨p ⁻¹' (A : Set B),A.isOpen.preimage p.hom.continuous⟩

include hAD in
/-- The literal preimages of a base open cover cover the actual covering space. -/
theorem preimageOpen_cover : preimageOpen p A ⊔ preimageOpen p D = ⊤ := by
  ext x
  change (p x ∈ A ∨ p x ∈ D) ↔ True
  change p x ∈ A ⊔ D ↔ True
  rw [hAD]
  simp

/-- The genuine equivariant small-chain complex for a pulled-back base open cover. -/
abbrev localCoverChains := coverChains G E (preimageOpen p A) (preimageOpen p D)
  (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD)

/-- The actual geometric local-system MV cochain sequence, retaining small cochains at its first term. -/
def localSmallSequence (W : Rep.{0} ℚ G) : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  transportShortComplex (separatedShortComplex G E (preimageOpen p A) (preimageOpen p D)
    (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W)
    (Iso.refl _) (biprod.mapIso (subordinateLocalIso p A W) (subordinateLocalIso p D W))
    (subordinateLocalIso p ((A : Set B) ∩ (D : Set B)) W)

/-- The genuine geometric local-system MV sequence is short exact before cohomology. -/
theorem localSmallSequence_shortExact (W : Rep.{0} ℚ G) : (localSmallSequence p A D hAD W).ShortExact :=
  ShortComplex.shortExact_of_iso (transportShortComplexIso _ _ _ _)
    (separatedShortExact G E (preimageOpen p A) (preimageOpen p D)
      (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W)

/-- The connecting map of actual geometric local-system Mayer–Vietoris, into small cohomology. -/
def localSmallConnecting (W : Rep.{0} ℚ G) (n : ℕ) :
    (localCochains (restrictedProjection p ((A : Set B) ∩ (D : Set B)))
      (restrictedQuotientCovering p ((A : Set B) ∩ (D : Set B))) W).homology n ⟶
        (homCochains (localCoverChains p A D hAD) W).homology (n+1) :=
  (localSmallSequence_shortExact p A D hAD W).δ n (n+1) rfl

end TernaryPoly.EquivariantSingularMayerVietoris
