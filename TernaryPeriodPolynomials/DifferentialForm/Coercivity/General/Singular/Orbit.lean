module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Singular.Cover
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Basic

@[expose] public section


/-!
# Orbit covers of admissible subgroups and the transfer to an overgroup

For admissible subgroups `Γ' ≤ Γ` of `GL₃(ℝ)` with `Γ'` of finite index in `Γ`, the identity of
`Space` descends to a finite covering `orbitMap : OrbitSpace Γ' → OrbitSpace Γ` whose preimages of
compact sets are compact (`isCompact_preimage_orbitMap`).  With `Singular/Cover` this gives
`singularVanish_of_subgroup`: the actual compact-to-ordinary map of the cover by an admissible
group vanishes in degree two (with rational coefficients `A`) as soon as it does for a finite-index
admissible subgroup (with the restricted coefficients).

Formalized by Claude Sonnet 5.5.
-/


open TopologicalSpace

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering

/-- Finite right transversal of a finite-index subgroup. -/
theorem exists_right_transversal {G : Type} [Group G] (K : Subgroup G) [Finite (G ⧸ K)] :
    ∃ R : Finset G, ∀ g : G, ∃ r ∈ R, ∃ k ∈ K, g = k * r := by
  classical
  have := Fintype.ofFinite (G ⧸ K)
  refine ⟨(Finset.univ : Finset (G ⧸ K)).image (fun q => (Quotient.out q)⁻¹), fun g => ?_⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g⁻¹
  refine ⟨(Quotient.out (QuotientGroup.mk g⁻¹ : G ⧸ K))⁻¹,
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (k : G), k.2, ?_⟩
  rw [hk]
  group

/-- Compact subsets of the target of an open surjection from a locally compact space are covered
by the image of a compact set. -/
theorem exists_compact_lift {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p) (hs : Function.Surjective p) {K : Set Y}
    (hK : IsCompact K) : ∃ C : Set X, IsCompact C ∧ K ⊆ p '' C := by
  classical
  have hloc : ∀ y ∈ K, ∃ N : Set X, IsCompact N ∧ p '' N ∈ nhds y := by
    intro y _
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨N, hN, -, hNc⟩ := local_compact_nhds (x := x) (n := Set.univ) Filter.univ_mem
    refine ⟨N, hNc, ?_⟩
    exact (hp.image_mem_nhds hN)
  choose! N hNc hNn using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun y => p '' N y) (fun y hy => hNn y hy)
  refine ⟨⋃ y ∈ t, N y, ?_, ?_⟩
  · exact t.isCompact_biUnion fun y hy => hNc y (htK y hy)
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hcov hy)
    obtain ⟨x, hx, rfl⟩ := hyz
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨z, hz, hx⟩, rfl⟩


section OrbitMap

variable {Γ' Γ : Subgroup RealGL} (hle : Γ' ≤ Γ)

/-- The covering map from the orbit space of a subgroup to that of the larger group. -/
def orbitMap : OrbitSpace Γ' → OrbitSpace Γ :=
  Quotient.map' id (fun S T h => by
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
    exact MulAction.orbitRel_apply.mpr ⟨Subgroup.inclusion hle g, hg⟩)

theorem orbitMap_proj (S : Space) : orbitMap hle (proj Γ' S) = proj Γ S := rfl

theorem continuous_orbitMap : Continuous (orbitMap hle) := by
  apply Continuous.quotient_lift
  exact continuous_proj

/-- **Properness of the finite cover of orbit spaces.** -/
theorem isCompact_preimage_orbitMap (hΓ : Admissible Γ) [Finite (Γ ⧸ Γ'.subgroupOf Γ)]
    {K : Set (OrbitSpace Γ)} (hK : IsCompact K) : IsCompact (orbitMap hle ⁻¹' K) := by
  classical
  have := hΓ.t2
  obtain ⟨C, hC, hKC⟩ := exists_compact_lift (proj Γ) hΓ.isOpenMap_proj proj_surjective hK
  obtain ⟨R, hR⟩ := exists_right_transversal (Γ'.subgroupOf Γ)
  let D : Set Space := ⋃ r ∈ R, (fun S => (r : RealGL) • S) '' C
  have hD : IsCompact D := R.isCompact_biUnion fun r _ =>
    hC.image (continuous_const_smul (r : RealGL))
  have hDK : IsCompact (D ∩ proj Γ ⁻¹' K) := hD.inter_right (hK.isClosed.preimage continuous_proj)
  have himg : orbitMap hle ⁻¹' K = proj Γ' '' (D ∩ proj Γ ⁻¹' K) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := proj_surjective (Γ := Γ') y
      have hx : proj Γ x ∈ K := hy
      obtain ⟨c, hc, hcx⟩ := hKC hx
      obtain ⟨γ, hγ⟩ := proj_eq_iff.mp hcx
      obtain ⟨r, hrR, k, hk, hγk⟩ := hR γ
      have hxe : x = ((k : Γ) : RealGL) • ((r : RealGL) • c) := by
        rw [← hγ, hγk]
        simp [mul_smul]
        rfl
      refine ⟨(r : RealGL) • c, ⟨Set.mem_iUnion₂.mpr ⟨r, hrR, c, hc, rfl⟩, ?_⟩, ?_⟩
      · change proj Γ ((r : RealGL) • c) ∈ K
        have : proj Γ ((r : RealGL) • c) = proj Γ c := proj_smul r c
        rw [this, hcx]; exact hx
      · rw [hxe]
        exact (proj_smul (⟨(k : Γ).1, hk⟩ : Γ') ((r : RealGL) • c)).symm
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
  rw [himg]
  exact hDK.image continuous_proj

end OrbitMap


section Concrete

open CategoryTheory TernaryPoly.CompactInteriorRelativeBoundary

/-- The orbit covering of `Space` by a subgroup, as a morphism of topological spaces. -/
def coverHom (Γ : Subgroup RealGL) : TopCat.of Space ⟶ TopCat.of (OrbitSpace Γ) :=
  TopCat.ofHom ⟨proj Γ, continuous_proj⟩

/-- The actual compact-to-ordinary map of the cover by an admissible group with coefficients `A`
vanishes in degree two. -/
def SingularVanish (Γ : Subgroup RealGL) (hΓ : Admissible Γ) (A : Rep.{0} ℚ Γ) : Prop :=
  letI : Fact (IsQuotientCoveringMap (coverHom Γ) Γ) := ⟨hΓ.quotientCovering⟩
  compactForget (coverHom Γ) A 2 = 0

variable {Γ' Γ : Subgroup RealGL}

/-- **Transfer to an overgroup**: vanishing for a finite-index admissible subgroup (with the
restricted coefficients) gives vanishing for the admissible overgroup. -/
theorem singularVanish_of_subgroup (hΓ' : Admissible Γ') (hΓ : Admissible Γ) (hle : Γ' ≤ Γ)
    [Finite (Γ ⧸ Γ'.subgroupOf Γ)] (A : Rep.{0} ℚ Γ)
    (h : SingularVanish Γ' hΓ' (Rep.res (Subgroup.inclusion hle) A)) : SingularVanish Γ hΓ A := by
  let _ : Fact (IsQuotientCoveringMap (coverHom Γ) Γ) := ⟨hΓ.quotientCovering⟩
  let _ : Fact (IsQuotientCoveringMap (coverHom Γ') Γ') := ⟨hΓ'.quotientCovering⟩
  have hfin : Finite (Γ ⧸ (Subgroup.inclusion hle).range) := by
    have e : (Subgroup.inclusion hle).range = Γ'.subgroupOf Γ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x.1, hx⟩, rfl⟩
    rw [e]; exact inferInstance
  change compactForget (coverHom Γ) A 2 = 0
  have h' : compactForget (coverHom Γ') (Rep.res (Subgroup.inclusion hle) A) 2 = 0 := h
  exact compactForget_zero_of_res (Subgroup.inclusion hle) (fun _ _ => rfl) (coverHom Γ)
    (coverHom Γ') (TopCat.ofHom ⟨orbitMap hle, continuous_orbitMap hle⟩) rfl
    (fun K => isCompact_preimage_orbitMap hle hΓ K.isCompact) A h'

end Concrete

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
