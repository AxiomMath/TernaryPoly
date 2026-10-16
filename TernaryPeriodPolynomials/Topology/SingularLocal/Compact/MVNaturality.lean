module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MV

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalSupport EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B] [LocallyCompactSpace B]
  (U D : Opens B) (hUD : U ⊔ D = ⊤)

/-- The genuine connecting formula holds for every pair of ambient compact supports subordinate to the cover. -/
theorem compactConnecting_ambient_pair (K L : Compacts B)
    (hKU : (K : Set B) ⊆ U) (hLD : (L : Set B) ⊆ D) (n : ℕ) :
    compactClassMap p V (K ⊔ L) n ≫ compactConnecting p V U D hUD n =
      fixedConnecting p V K L K.isCompact.isClosed L.isCompact.isClosed n ≫
        classInOpen p V (U ⊓ D) (K ⊓ L) (fun _ hx => ⟨hKU hx.1,hLD hx.2⟩) (n+1) := by
  have aux (P : Compacts U × Compacts D) (K L : Compacts B)
      (hK : compactOpenImage U P.1 = K) (hL : compactOpenImage D P.2 = L)
      (hKU : (K : Set B) ⊆ U) (hLD : (L : Set B) ⊆ D) :
      compactClassMap p V (K ⊔ L) n ≫ compactConnecting p V U D hUD n =
      fixedConnecting p V K L K.isCompact.isClosed L.isCompact.isClosed n ≫
        classInOpen p V (U ⊓ D) (K ⊓ L) (fun _ hx => ⟨hKU hx.1,hLD hx.2⟩) (n+1) := by
    subst K
    subst L
    exact compactConnecting_classMap p V U D hUD n P
  exact aux (compactWithinOpen U K hKU,compactWithinOpen D L hLD) K L
    (openCompactImage_compactWithin U K hKU) (openCompactImage_compactWithin D L hLD) hKU hLD

/-- The cover-enlargement connecting square holds on any actual pair of subordinate compact supports. -/
theorem compactConnecting_open_natural_pair (U' D' : Opens B) (hU'D' : U' ⊔ D' = ⊤)
    (hUU' : U ≤ U') (hDD' : D ≤ D') (K L : Compacts B)
    (hKU : (K : Set B) ⊆ U) (hLD : (L : Set B) ⊆ D) (n : ℕ) :
    compactClassMap p V (K ⊔ L) n ≫ (compactConnecting p V U D hUD n ≫
      openExtensionBetween p V (U ⊓ D) (U' ⊓ D') (inf_le_inf hUU' hDD') (n+1)) =
        compactClassMap p V (K ⊔ L) n ≫ compactConnecting p V U' D' hU'D' n := by
  erw [← Category.assoc,compactConnecting_ambient_pair p V U D hUD K L hKU hLD n,
    Category.assoc,classInOpen_between p V (U ⊓ D) (U' ⊓ D') (inf_le_inf hUU' hDD') (K ⊓ L)
      (fun _ hx => ⟨hKU hx.1,hLD hx.2⟩) (n+1),
    compactConnecting_ambient_pair p V U' D' hU'D' K L (hKU.trans hUU') (hLD.trans hDD') n]

/-- The genuine compact-support connecting map is natural under enlargement of the two opens. -/
theorem compactConnecting_open_natural (U' D' : Opens B) (hU'D' : U' ⊔ D' = ⊤)
    (hUU' : U ≤ U') (hDD' : D ≤ D') (n : ℕ) :
    compactConnecting p V U D hUD n ≫
      openExtensionBetween p V (U ⊓ D) (U' ⊓ D') (inf_le_inf hUU' hDD') (n+1) =
        compactConnecting p V U' D' hU'D' n := by
  apply compactCohomology_hom_ext
  intro S
  obtain ⟨K,L,hK,hL,_,_,hKU,hLD,hKL⟩ := compact_binary_refinement U D hUD S S.isCompact
  let K' : Compacts B := ⟨K,hK⟩
  let L' : Compacts B := ⟨L,hL⟩
  have hS : K' ⊔ L' = S := SetLike.coe_injective hKL
  rw [← hS]
  exact compactConnecting_open_natural_pair p V U D hUD U' D' hU'D' hUU' hDD' K' L' hKU hLD n

omit [LocallyCompactSpace B] in
/-- The signed open-extension diagonal is natural under enlargement of the two opens. -/
theorem compactDiagonal_open_natural (U' D' : Opens B) (hUU' : U ≤ U') (hDD' : D ≤ D') (n : ℕ) :
    openExtensionBetween p V (U ⊓ D) (U' ⊓ D') (inf_le_inf hUU' hDD') n ≫ compactDiagonal p V U' D' n =
      compactDiagonal p V U D n ≫
        biprod.map (openExtensionBetween p V U U' hUU' n) (openExtensionBetween p V D D' hDD' n) := by
  apply biprod.hom_ext
  · simp only [compactDiagonal,Category.assoc,biprod.lift_fst,biprod.map_fst,biprod.lift_fst_assoc]
    rw [openExtensionBetween_comp,openExtensionBetween_comp]
  · simp only [compactDiagonal,Category.assoc,biprod.lift_snd,biprod.map_snd,biprod.lift_snd_assoc,
      Preadditive.comp_neg,Preadditive.neg_comp]
    rw [openExtensionBetween_comp,openExtensionBetween_comp]

omit [LocallyCompactSpace B] in
/-- The sum of actual open extensions is natural under enlargement of the two opens. -/
theorem compactSum_open_natural (U' D' : Opens B) (hUU' : U ≤ U') (hDD' : D ≤ D') (n : ℕ) :
    biprod.map (openExtensionBetween p V U U' hUU' n) (openExtensionBetween p V D D' hDD' n) ≫
      compactSum p V U' D' n = compactSum p V U D n := by
  apply biprod.hom_ext'
  · simp only [compactSum,biprod.inl_map_assoc,biprod.inl_desc ]
    rw [openExtensionBetween_ambient]
  · simp only [compactSum,biprod.inr_map_assoc,biprod.inr_desc ]
    rw [openExtensionBetween_ambient]

end TernaryPoly.SingularLocalCompactMV
