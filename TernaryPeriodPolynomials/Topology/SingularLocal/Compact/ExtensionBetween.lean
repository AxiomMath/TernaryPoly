module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionSupport
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Representatives

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalCoefficient EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]

/-- Actual extension of one support class between nested opens of a common ambient space. -/
def openBetweenClass (D U : Opens B) (hDU : D ≤ U) (K : Compacts D) (k : ℕ) :
    (supportCochains (restrictedProjection p D) V (K : Set D)).homology k ⟶
      compactCohomology (restrictedProjection p U) V k :=
  (openSupportIso p V D K k).inv ≫
    classInOpen p V U (openCompactImage D K) ((openCompactImage_subset D K).trans hDU) k

/-- Extension between nested opens is natural in actual compact supports. -/
theorem openBetweenClass_natural (D U : Opens B) (hDU : D ≤ U) (K L : Compacts D)
    (hKL : (K : Set D) ⊆ L) (k : ℕ) :
    homologyMap (supportMap (restrictedProjection p D) V (K : Set D) (L : Set D) hKL) k ≫
      openBetweenClass p V D U hDU L k = openBetweenClass p V D U hDU K k := by
  unfold openBetweenClass
  rw [← Category.assoc,← openSupportIso_inv_natural p V D K L hKL k,Category.assoc]
  erw [classInOpen_natural p V U (openCompactImage D K) (openCompactImage D L)
    (Set.image_mono hKL) ((openCompactImage_subset D L).trans hDU) k]

/-- Genuine compact-support extension between two nested opens in the same ambient space. -/
def openExtensionBetween (D U : Opens B) (hDU : D ≤ U) (k : ℕ) :
    compactCohomology (restrictedProjection p D) V k ⟶
      compactCohomology (restrictedProjection p U) V k :=
  compactCohomologyDesc (restrictedProjection p D) V k (compactCohomology (restrictedProjection p U) V k)
    (fun K => openBetweenClass p V D U hDU K k)
    (fun K L hKL => openBetweenClass_natural p V D U hDU K L hKL k)

/-- The actual class formula for extension between nested open sets. -/
theorem openExtensionBetween_classMap (D U : Opens B) (hDU : D ≤ U) (K : Compacts D) (k : ℕ) :
    compactClassMap (restrictedProjection p D) V K k ≫ openExtensionBetween p V D U hDU k =
      (openSupportIso p V D K k).inv ≫
        classInOpen p V U (openCompactImage D K) ((openCompactImage_subset D K).trans hDU) k :=
  compactCohomologyDesc_ι _ _ _ _ _ _ _

/-- The actual support class in an open set, using the image of a compact in that open set. -/
theorem classInOpen_image (D : Opens B) (K : Compacts D) (k : ℕ) :
    classInOpen p V D (openCompactImage D K) (openCompactImage_subset D K) k =
      (openSupportIso p V D K k).hom ≫ compactClassMap (restrictedProjection p D) V K k :=
  classInOpen_congr p V D (openCompactImage D K) (openCompactImage_subset D K) K
    (openCompactImage_preimage D K) k

/-- Extension from an open set to itself is the identity on actual compact-support cohomology. -/
theorem openExtensionBetween_self (D : Opens B) (k : ℕ) :
    openExtensionBetween p V D D le_rfl k = 𝟙 _ := by
  apply compactCohomology_hom_ext
  intro K
  rw [openExtensionBetween_classMap,classInOpen_image,Iso.inv_hom_id_assoc,Category.comp_id]

/-- Restricting any ambient representative to a smaller open and then extending to a larger open
retains the same representative in that larger open. -/
theorem classInOpen_between (D U : Opens B) (hDU : D ≤ U) (K : Compacts B)
    (hKD : (K : Set B) ⊆ D) (k : ℕ) :
    classInOpen p V D K hKD k ≫ openExtensionBetween p V D U hDU k =
      classInOpen p V U K (hKD.trans hDU) k := by
  have aux : ∀ (K : Compacts B) (L : Compacts D) (himage : openCompactImage D L = K)
      (hpre : (Subtype.val ⁻¹' (K : Set B) : Set D) = (L : Set D))
      (hKU : (K : Set B) ⊆ U),
      homologyMap (supportToOpen p V D (K : Set B) ≫
        supportCongrMap (restrictedProjection p D) V _ _ hpre) k ≫
        compactClassMap (restrictedProjection p D) V L k ≫ openExtensionBetween p V D U hDU k =
          classInOpen p V U K hKU k := by
    intro K L himage hpre hKU
    subst K
    rw [openExtensionBetween_classMap]
    change (openSupportIso p V D L k).hom ≫ (openSupportIso p V D L k).inv ≫ _ = _
    rw [Iso.hom_inv_id_assoc]
  rw [classInOpen_congr p V D K hKD (compactWithinOpen D K hKD) rfl k,Category.assoc]
  exact aux K (compactWithinOpen D K hKD) (openCompactImage_compactWithin D K hKD) rfl _

/-- Actual extension between nested opens composes with extension to the common ambient space. -/
theorem openExtensionBetween_ambient (D U : Opens B) (hDU : D ≤ U) (k : ℕ) :
    openExtensionBetween p V D U hDU k ≫ openExtension p V U k = openExtension p V D k := by
  apply compactCohomology_hom_ext
  intro K
  rw [← Category.assoc,openExtensionBetween_classMap,Category.assoc,classInOpen_extension,
    openExtension_classMap]

/-- Genuine compact-support extensions compose for nested open subsets of one ambient space. -/
theorem openExtensionBetween_comp (D U W : Opens B) (hDU : D ≤ U) (hUW : U ≤ W) (k : ℕ) :
    openExtensionBetween p V D U hDU k ≫ openExtensionBetween p V U W hUW k =
      openExtensionBetween p V D W (hDU.trans hUW) k := by
  apply compactCohomology_hom_ext
  intro K
  rw [← Category.assoc,openExtensionBetween_classMap,Category.assoc,classInOpen_between,
    openExtensionBetween_classMap]

end TernaryPoly.SingularLocalSupport
