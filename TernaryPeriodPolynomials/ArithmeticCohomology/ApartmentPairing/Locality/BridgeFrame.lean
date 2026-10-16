module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Frame
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Eval
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BridgeCore

@[expose] public section


/-!
# Lemma 3.3, G3: from the frame to the hypotheses of the bridge core

For a quotient covering `p : Space ⟶ B` with deck group `Γ(6)`, a `FrameOut` (the output of the frame
theorem: coordinate box `T̃ = {‖π‖ < ε, ‖t‖ < R0}`, slab level `δ`, tube radius `ρ'`, neighbourhood `D` of the
retract) provides every geometric hypothesis of `bridge_core`:

* the chart `UT = p(T̃)` (`FrameOut.UT_open`), its section `sec` with `sec ≫ p = ι` (`sec_comp`) and the
  coordinate homeomorphism `eY` onto the model box;
* the complement `UB` of the image of the tube (`UB_open`, `UB_pre`), the compact slab `Qs`
  (`Qs_compact`, `image_slab_cov`) and the image `D1` of `D` (`D1_cov`);
* `hQ`, `hD1`: the slab description of the support inside the chart;
* for a scalar cochain `y` vanishing off the tube: `hfin_y` (finitely many translates) and `hone_y`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

section Cover

variable {B : TopCat.{0}} (p : SpaceTop ⟶ B) (hp : IsQuotientCoveringMap p principalSix)

include hp

theorem cover_eq_iff (x x' : Space) : p x = p x' ↔ ∃ g : principalSix, g • x' = x := by
  rw [hp.apply_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩; exact ⟨g, hg⟩

theorem cover_injOn (A : Set Space) (hA : ∀ g : principalSix, g ≠ 1 → Disjoint (g • A) A) :
    Set.InjOn p A := by
  intro x hx x' hx' h
  obtain ⟨g, rfl⟩ := (cover_eq_iff p hp x x').mp h
  by_cases hg : g = 1
  · subst hg; simp
  · exact (Set.disjoint_left.mp (hA g hg) (Set.smul_mem_smul_set hx') hx).elim

theorem cover_preimage_image (Z : Set Space) : p ⁻¹' (p '' Z) = ⋃ g : principalSix, g • Z := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨g, rfl⟩ := (cover_eq_iff p hp z x).mp hzx
    exact ⟨g⁻¹, Set.mem_smul_set_iff_inv_smul_mem.mpr (by simpa using hz)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hg
    exact ⟨z, hz, ((cover_eq_iff p hp (g • z) z).mpr ⟨g, rfl⟩).symm⟩

/-- The restriction of the covering to an open set on which it is injective is an open embedding. -/
theorem cover_restrict_isOpenEmbedding (A : Set Space) (hAo : IsOpen A) (hinj : Set.InjOn p A) :
    Topology.IsOpenEmbedding (A.domRestrict p) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact p.hom.continuous.comp continuous_subtype_val
  · exact hinj.injective
  · exact hp.isOpenQuotientMap.isOpenMap.domRestrict hAo

/-- The chart: the covering restricted to an open set of injectivity is a homeomorphism onto its image. -/
def coverChart (A : Set Space) (hAo : IsOpen A) (hinj : Set.InjOn p A) : A ≃ₜ ↥(p '' A) :=
  (cover_restrict_isOpenEmbedding p hp A hAo hinj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [Set.range_domRestrict]))

theorem coverChart_apply (A : Set Space) (hAo : IsOpen A) (hinj : Set.InjOn p A) (x : A) :
    ((coverChart p hp A hAo hinj x : ↥(p '' A)) : B) = p x := rfl

end Cover

/-- The output of the frame theorem. -/
structure FrameOut where
  ε : ℝ
  R0 : ℝ
  δ : ℝ
  ρ' : Space → ℝ
  D : Set Space
  hε : 0 < ε
  hδ : 0 < δ
  hδR : δ < R0
  hρc : Continuous ρ'
  hρpos : ∀ S, 0 < ρ' S
  hρε : ∀ S, ρ' S < ε
  hinj : ∀ g : principalSix, g ≠ 1 → Disjoint (g • boxC ε R0) (boxC ε R0)
  hone : ∀ g : principalSix, g ≠ 1 → Disjoint (g • boxC ε R0) (tube ρ')
  hfin : ∀ K : Set Space, IsCompact K → {g : principalSix | ((g • K) ∩ tube ρ').Nonempty}.Finite
  hDo : IsOpen D
  hDg : ∀ (g : principalSix) (S : Space), S ∈ D → g • S ∈ D
  hDt : ∀ S ∈ D, S ∈ boxO ε R0 → ‖(coordHomeo S).2‖ < δ
  hDz : ∀ S ∈ D, S ∈ tube ρ' → S ∈ boxO ε R0

namespace FrameOut

variable (F : FrameOut)

/-- The chart box. -/
def Tt : Set Space := boxO F.ε F.R0

theorem Tt_open : IsOpen F.Tt := isOpen_boxO _ _

theorem Tt_sub : F.Tt ⊆ boxC F.ε F.R0 := boxO_subset_boxC _ _

theorem Tt_disj (g : principalSix) (hg : g ≠ 1) : Disjoint (g • F.Tt) F.Tt :=
  (F.hinj g hg).mono (Set.smul_set_mono F.Tt_sub) F.Tt_sub

theorem boxC_slab_sub : boxC F.ε F.δ ⊆ boxC F.ε F.R0 := fun _ hS =>
  ⟨hS.1, Metric.closedBall_subset_closedBall F.hδR.le hS.2⟩

end FrameOut

section Charts

variable {B : TopCat.{0}} (p : SpaceTop ⟶ B) (hp : IsQuotientCoveringMap p principalSix)
  (F : FrameOut)

include hp

theorem FrameOut.Tt_injOn : Set.InjOn p F.Tt := cover_injOn p hp _ F.Tt_disj

/-- The chart of the base. -/
def FrameOut.UT : Set B := p '' F.Tt

theorem FrameOut.UT_open : IsOpen (F.UT p) :=
  hp.isOpenQuotientMap.isOpenMap _ F.Tt_open

/-- The chart homeomorphism from the box to its image. -/
def FrameOut.eT : F.Tt ≃ₜ ↥(F.UT p) := coverChart p hp F.Tt F.Tt_open (F.Tt_injOn p hp)

/-- The section over the chart. -/
def FrameOut.sec : TopCat.of ↥(F.UT p) ⟶ SpaceTop :=
  TopCat.ofHom ⟨fun u => ((F.eT p hp).symm u).val,
    continuous_subtype_val.comp (F.eT p hp).symm.continuous⟩

theorem FrameOut.sec_val (u : ↥(F.UT p)) : (F.sec p hp).hom u = ((F.eT p hp).symm u).val := rfl

theorem FrameOut.sec_mem (u : ↥(F.UT p)) : (F.sec p hp).hom u ∈ F.Tt := ((F.eT p hp).symm u).2

theorem FrameOut.p_sec (u : ↥(F.UT p)) : p ((F.sec p hp).hom u) = u.val := by
  have := congrArg Subtype.val ((F.eT p hp).apply_symm_apply u)
  exact this

theorem FrameOut.sec_comp : F.sec p hp ≫ p = sInclusion (F.UT p) := by
  ext u
  exact F.p_sec p hp u

/-- The chart homeomorphism onto the model box. -/
def FrameOut.eY : TopCat.of ↥(F.UT p) ≃ₜ boxSet F.ε F.R0 :=
  (F.eT p hp).symm.trans (coordHomeo.subtype (fun x => by
    change x ∈ boxO F.ε F.R0 ↔ coordHomeo x ∈ boxSet F.ε F.R0
    simp [boxO, boxSet, Set.mem_prod, Metric.mem_ball, dist_zero_right]))

theorem FrameOut.eY_apply (u : ↥(F.UT p)) :
    ((F.eY p hp u : boxSet F.ε F.R0) : R3 × R2) = coordHomeo ((F.sec p hp).hom u) := rfl

/-- The complement of the image of the tube. -/
def FrameOut.UB : Set B := (p '' tube F.ρ')ᶜ

theorem FrameOut.UB_open : IsOpen (F.UB p) := by
  have hcl : IsClosed (p '' tube F.ρ') := by
    rw [← hp.toIsQuotientMap.isClosed_preimage, cover_preimage_image p hp]
    have := isClosed_biUnion_smul (tube F.ρ') (isClosed_tube F.hρc)
      (tube_finite_inv F.hfin) Set.univ
    simpa using this
  exact hcl.isOpen_compl

omit hp in
theorem FrameOut.UB_pre : p ⁻¹' F.UB p ⊆ (tube F.ρ')ᶜ := by
  intro x hx hxz
  exact hx ⟨x, hxz, rfl⟩

/-- The compact slab. -/
def FrameOut.Qs : Set B := p '' boxC F.ε F.δ

omit hp in
theorem FrameOut.Qs_compact : IsCompact (F.Qs p) :=
  (isCompact_boxC F.ε F.δ).image p.hom.continuous

/-- The image of the neighbourhood of the retract. -/
def FrameOut.D1 : Set B := p '' F.D


/-- A point of the box not in the open box lies off the tube, as do its nontrivial translates. -/
theorem FrameOut.image_slab_cov : F.Qs p ⊆ F.UT p ∪ F.UB p := by
  rintro b ⟨x, hx, rfl⟩
  by_cases hxT : x ∈ F.Tt
  · exact Or.inl ⟨x, hxT, rfl⟩
  · refine Or.inr ?_
    rintro ⟨z, hz, hzx⟩
    obtain ⟨g, rfl⟩ := (cover_eq_iff p hp z x).mp hzx
    by_cases hg : g = 1
    · subst hg
      rw [one_smul] at hz
      have hπ : ‖(coordHomeo x).1‖ < F.ε := by
        have := hz
        change ‖piR3 x‖ ≤ F.ρ' x at this
        exact lt_of_le_of_lt this (F.hρε x)
      apply hxT
      refine ⟨?_, ?_⟩
      · simpa [dist_zero_right] using hπ
      · have : ‖(coordHomeo x).2‖ ≤ F.δ := by simpa [dist_zero_right] using hx.2
        simpa [dist_zero_right] using lt_of_le_of_lt this F.hδR
    · exact Set.disjoint_left.mp (F.hone g hg)
        (Set.smul_mem_smul_set (F.boxC_slab_sub hx)) hz

theorem FrameOut.D1_cov : F.D1 p ⊆ F.UT p ∪ F.UB p := by
  rintro b ⟨d, hd, rfl⟩
  by_cases hb : p d ∈ p '' tube F.ρ'
  · obtain ⟨z, hz, hzd⟩ := hb
    obtain ⟨g, rfl⟩ := (cover_eq_iff p hp z d).mp hzd
    have hzD : g • d ∈ F.D := F.hDg g d hd
    exact Or.inl ⟨g • d, F.hDz _ hzD hz, hzd⟩
  · exact Or.inr hb

end Charts


section YFacts

variable {B : TopCat.{0}} (p : SpaceTop ⟶ B) (hp : IsQuotientCoveringMap p principalSix)
  (F : FrameOut)

theorem FrameOut.compl_tube_eq :
    (tube F.ρ')ᶜ = {s : SpaceTop | 1 < ‖(thomMap F.ρ' F.hρc F.hρpos).hom s‖} := by
  ext S
  simp only [tube, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  exact (one_lt_thomMap_iff F.ρ' F.hρc F.hρpos S).symm

variable (y : singularChainGroup ℚ SpaceTop 3 →ₗ[ℚ] ℚ)
  (hyZ : ∀ τ : SingularSimplex SpaceTop 3, IsSubordinate (tube F.ρ')ᶜ τ →
    y (chainGenerator ℚ SpaceTop 3 τ) = 0)

include hyZ in
theorem FrameOut.hfin_y : ∀ τ : SingularSimplex SpaceTop 3,
    {g : principalSix | y (chainGenerator ℚ SpaceTop 3 (g • τ)) ≠ 0}.Finite := by
  intro τ
  let K : Set Space := Set.range (singularSimplexAsContinuousMap SpaceTop 3 τ)
  have hK : IsCompact K := isCompact_range (singularSimplexAsContinuousMap SpaceTop 3 τ).continuous
  refine (F.hfin K hK).subset ?_
  intro g hg
  by_contra hnon
  apply hg
  apply hyZ
  rw [singular_smul_eq_map, show (TopCat.toSSet.map (scalarMap principalSix SpaceTop g)).app
      (Opposite.op (SimplexCategory.mk 3)) τ = pushSimplex (scalarMap principalSix SpaceTop g) 3 τ
      from rfl, isSubordinate_pushSimplex_iff]
  intro x hx
  by_contra hxn
  apply hnon
  refine ⟨_, Set.smul_mem_smul_set hx, ?_⟩
  by_contra hnt
  exact hxn hnt

include hp hyZ in
theorem FrameOut.hone_y (ρ : SingularSimplex (TopCat.of ↥(F.UT p)) 3) (g : principalSix) (hg : g ≠ 1) :
    y (chainGenerator ℚ SpaceTop 3 (g • pushSimplex (F.sec p hp) 3 ρ)) = 0 := by
  apply hyZ
  rw [singular_smul_eq_map, show (TopCat.toSSet.map (scalarMap principalSix SpaceTop g)).app
      (Opposite.op (SimplexCategory.mk 3)) (pushSimplex (F.sec p hp) 3 ρ) =
      pushSimplex (scalarMap principalSix SpaceTop g) 3 (pushSimplex (F.sec p hp) 3 ρ) from rfl,
    isSubordinate_pushSimplex_iff, isSubordinate_pushSimplex_iff]
  intro x _ hmem
  exact Set.disjoint_left.mp (F.hone g hg)
    (Set.smul_mem_smul_set (F.Tt_sub (F.sec_mem p hp x))) hmem

end YFacts


section HQ

variable {B : TopCat.{0}} (p : SpaceTop ⟶ B) (hp : IsQuotientCoveringMap p principalSix)
  (F : FrameOut)

include hp

theorem FrameOut.hQ (u : ↥(F.UT p)) :
    (u : B) ∈ F.Qs p ↔ ‖((F.eY p hp u : boxSet F.ε F.R0) : R3 × R2).2‖ ≤ F.δ := by
  have hxT := F.sec_mem p hp u
  have hpx := F.p_sec p hp u
  rw [FrameOut.eY_apply]
  constructor
  · rintro ⟨q, hq, hqu⟩
    obtain ⟨g, hg⟩ := (cover_eq_iff p hp q _).mp (hqu.trans hpx.symm)
    by_cases hg1 : g = 1
    · subst hg1
      rw [one_smul] at hg
      subst hg
      simpa [dist_zero_right] using hq.2
    · exfalso
      exact Set.disjoint_left.mp (F.hinj g hg1) (Set.smul_mem_smul_set (F.Tt_sub hxT))
        (hg ▸ F.boxC_slab_sub hq)
  · intro h
    refine ⟨_, ⟨?_, ?_⟩, hpx⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (by simpa [dist_zero_right] using hxT.1 : ‖(coordHomeo _).1‖ < F.ε).le
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact h

theorem FrameOut.hD1 : ∀ b ∈ F.D1 p, ∀ u : ↥(F.UT p), (u : B) = b →
    ‖((F.eY p hp u : boxSet F.ε F.R0) : R3 × R2).2‖ ≤ F.δ := by
  rintro b ⟨d, hd, rfl⟩ u hu
  have hxT := F.sec_mem p hp u
  have hpx := F.p_sec p hp u
  rw [FrameOut.eY_apply]
  obtain ⟨g, hg⟩ := (cover_eq_iff p hp _ d).mp (hpx.trans hu)
  rw [← hg] at hxT ⊢
  exact (F.hDt _ (F.hDg g d hd) hxT).le

end HQ

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
