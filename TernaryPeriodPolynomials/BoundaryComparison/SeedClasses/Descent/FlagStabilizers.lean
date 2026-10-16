module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturality

@[expose] public section


/-!
# Classes vanishing on the flag stabilizers: the Hochschild--Serre characterization

Paper: Lemma C.3 (`ar:lem:seed`),: the mixed cuspidal group `𝒞_R(E)` consists of the classes of `H¹(L_R, H¹(N_R, E))`
"whose restrictions at all rational cusps of the binary Levi vanish", and injects into degree-two face
cohomology by Hochschild--Serre.

For a split extension `N → E → L`, a family of subgroups `B i ≤ L` (the stabilizers in the Levi of
the rational cusps, i.e. of the complete flags over the plane) with `H²(B i, ·) = 0`, the preimage
`E_i` of `B i` in `E` is the stabilizer of the complete flag. `extRestrict`/`splitRestrict` realize
`E_i` as a split extension of `B i`, and by the naturality of the edge (`EdgeNaturality`):

* `edge_mem_cuspidalFamily_iff`: a class `y ∈ H²(E, ρ)` with zero radical restriction has
  Hochschild--Serre edge in the cuspidal subspace for the family `B` iff its restriction to
  every flag stabilizer `E_i` vanishes. This is the frame-free description of `𝒞_R(E)` as the
  *locally inner* classes (vanishing on the stabilizer of every complete flag over the face).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace LocallyInner

variable {N E L : Type} [Group N] [Group E] [Group L]

/-- The extension restricted to a subgroup `B` of the Levi: the preimage `E_B` of `B` in `E`. -/
def extRestrict (ext : GroupExtension N E L) (B : Subgroup L) :
    GroupExtension N (B.comap ext.rightHom) B where
  inl := ext.inl.codRestrict _ (fun n => by
    have : ext.inl n ∈ ext.rightHom.ker := by
      rw [← ext.range_inl_eq_ker_rightHom]; exact ⟨n, rfl⟩
    exact (by simp))
  rightHom := (ext.rightHom.comp (B.comap ext.rightHom).subtype).codRestrict B (fun e => e.2)
  inl_injective := fun a b h => ext.inl_injective (congrArg Subtype.val h)
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      have : ext.inl n ∈ ext.rightHom.ker := by
        rw [← ext.range_inl_eq_ker_rightHom]; exact ⟨n, rfl⟩
      exact Subtype.ext this
    · intro hx
      have hx' : (x : E) ∈ ext.inl.range := by
        rw [ext.range_inl_eq_ker_rightHom]; exact congrArg Subtype.val hx
      obtain ⟨n, hn⟩ := hx'
      exact ⟨n, Subtype.ext hn⟩
  rightHom_surjective := fun b => by
    obtain ⟨e, he⟩ := ext.rightHom_surjective (b : L)
    exact ⟨⟨e, by simp [Subgroup.mem_comap, he]⟩, Subtype.ext he⟩

/-- The Levi splitting restricted to `B`. -/
def splitRestrict {ext : GroupExtension N E L} (s : ext.Splitting) (B : Subgroup L) :
    (extRestrict ext B).Splitting where
  toFun b := ⟨s.toMonoidHom (b : L), by
    show ext.rightHom (s.toMonoidHom (b : L)) ∈ B
    have h : ext.rightHom (s.toMonoidHom (b : L)) = (b : L) := s.rightInverse_rightHom (b : L)
    rw [h]; exact b.2⟩
  map_one' := Subtype.ext (map_one s.toMonoidHom)
  map_mul' a b := Subtype.ext (map_mul s.toMonoidHom (a : L) (b : L))
  rightInverse_rightHom b := Subtype.ext (s.rightInverse_rightHom (b : L))

variable {ext : GroupExtension N E L} (s : ext.Splitting) (ρ : Rep ℂ E) (B : Subgroup L)

theorem res_inl_eq : Rep.res (extRestrict ext B).inl (Rep.res (B.comap ext.rightHom).subtype ρ) =
    Rep.res ext.inl ρ := rfl


/-- The inclusion of the preimage of `B` in `E`. -/
abbrev incl (ext : GroupExtension N E L) (B : Subgroup L) : (B.comap ext.rightHom) →* E :=
  (B.comap ext.rightHom).subtype

/-- The restricted coefficient module. -/
abbrev resRep (ext : GroupExtension N E L) (ρ : Rep ℂ E) (B : Subgroup L) :
    Rep ℂ (B.comap ext.rightHom) :=
  Rep.res (incl ext B) ρ

theorem hinl (ext : GroupExtension N E L) (B : Subgroup L) (r : N) :
    incl ext B ((extRestrict ext B).inl r) = ext.inl ((MonoidHom.id N) r) := rfl

theorem hsplit (s : ext.Splitting) (B : Subgroup L) (m : B) :
    incl ext B (splitRestrict s B m) = s.toMonoidHom (B.subtype m) := rfl

theorem hT (ρ : Rep ℂ E) (B : Subgroup L) (g : B.comap ext.rightHom) (v : ρ) :
    (LinearMap.id : ρ →ₗ[ℂ] resRep ext ρ B) (ρ.ρ (incl ext B g) v) =
      (resRep ext ρ B).ρ g ((LinearMap.id : ρ →ₗ[ℂ] resRep ext ρ B) v) := rfl

/-- The restriction of a radical-kernel class to the preimage of `B`. -/
def kerRes (ρ : Rep ℂ E) (B : Subgroup L) :
    (twoCohomologyRestriction ext.inl ρ).ker →ₗ[ℂ]
      (twoCohomologyRestriction (extRestrict ext B).inl (resRep ext ρ B)).ker :=
  EdgeNat.kerMap (incl ext B) (MonoidHom.id N) (hinl ext B) ρ (resRep ext ρ B) LinearMap.id
    (hT ρ B)

theorem kerRes_val (ρ : Rep ℂ E) (B : Subgroup L) (x : (twoCohomologyRestriction ext.inl ρ).ker) :
    (kerRes ρ B x).val = twoCohomologyRestriction (incl ext B) ρ x.val := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective ρ y
  rw [twoCohomologyRestriction_apply]
  change EdgeNat.h2Map (incl ext B) ρ (resRep ext ρ B) LinearMap.id (hT ρ B)
    (groupCohomology.H2π ρ z) = _
  rw [EdgeNat.h2Map_π]
  rfl


theorem edge_kerRes (ρ : Rep ℂ E) (B : Subgroup L) (x : (twoCohomologyRestriction ext.inl ρ).ker) :
    splitCohomologyEdge (splitRestrict s B) (resRep ext ρ B) (kerRes ρ B x) =
      (groupCohomology.map B.subtype (EdgeNat.modMor s (splitRestrict s B) (incl ext B)
        B.subtype (MonoidHom.id N) (hinl ext B) (hsplit s B) ρ (resRep ext ρ B) LinearMap.id
        (hT ρ B)) 1).hom (splitCohomologyEdge s ρ x) :=
  EdgeNat.edge_kerMap s (splitRestrict s B) (incl ext B) B.subtype (MonoidHom.id N) (hinl ext B)
    (hsplit s B) ρ (resRep ext ρ B) LinearMap.id (hT ρ B) x


theorem radH1Map_restrict (ρ : Rep ℂ E) (B : Subgroup L)
    (x : groupCohomology.H1 (Rep.res ext.inl ρ)) :
    EdgeNat.radH1Map (incl ext B) (MonoidHom.id N) (hinl ext B) ρ (resRep ext ρ B) LinearMap.id
      (hT ρ B) x = x := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res ext.inl ρ) x
  rw [EdgeNat.radH1Map_π]
  congr 1

theorem action_restrict (ρ : Rep ℂ E) (B : Subgroup L) (γ : B)
    (u : groupCohomology.H1 (Rep.res ext.inl ρ)) :
    splitRadicalH1Action (splitRestrict s B) (resRep ext ρ B) γ u =
      splitRadicalH1Action s ρ (γ : L) u := by
  have h := EdgeNat.radH1Map_equivariant s (splitRestrict s B) (incl ext B) B.subtype
    (MonoidHom.id N) (hinl ext B) (hsplit s B) ρ (resRep ext ρ B) LinearMap.id (hT ρ B) γ u
  rw [radH1Map_restrict, radH1Map_restrict] at h
  exact h.symm

theorem map_modMor_eq_zero_iff (ρ : Rep ℂ E) (B : Subgroup L)
    (x : groupCohomology.H1 (splitRadicalH1Representation s ρ)) :
    (groupCohomology.map B.subtype (EdgeNat.modMor s (splitRestrict s B) (incl ext B)
        B.subtype (MonoidHom.id N) (hinl ext B) (hsplit s B) ρ (resRep ext ρ B) LinearMap.id
        (hT ρ B)) 1).hom x = 0 ↔ oneRestriction B (splitRadicalH1Representation s ρ) x = 0 := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (splitRadicalH1Representation s ρ) x
  rw [EdgeNat.map_H1_π_gen, groupCohomology.H1π_eq_zero_iff, oneRestriction_π_eq_zero_iff]
  have h2 : ∀ γ : B, ((ConcreteCategory.hom (groupCohomology.mapCocycles₁ B.subtype
      (EdgeNat.modMor s (splitRestrict s B) (incl ext B) B.subtype (MonoidHom.id N) (hinl ext B)
        (hsplit s B) ρ (resRep ext ρ B) LinearMap.id (hT ρ B)))) c) γ = c.1 (γ : L) :=
    fun γ => radH1Map_restrict ρ B _
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun γ => ?_⟩
    have h := congrFun hu γ
    simp only [groupCohomology.d₀₁_hom_apply] at h
    rw [← h2 γ, ← h]
    exact congrArg (· - u) (action_restrict s ρ B γ u)
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    funext γ
    let u' : splitRadicalH1Representation (splitRestrict s B) (resRep ext ρ B) := u
    change (splitRadicalH1Representation (splitRestrict s B) (resRep ext ρ B)).ρ γ u' - u' = _
    rw [h2 γ, hu γ]
    exact congrArg (· - u) (action_restrict s ρ B γ u)


/-- Shapiro: if `H²(G, ·)` vanishes for all representations then so does `H²(S, ·)` for a
subgroup `S`. -/
theorem h2_zero_subgroup {G : Type} [Group G]
    (hG : ∀ (A : Rep ℂ G) (x : groupCohomology.H2 A), x = 0) (S : Subgroup G) (A : Rep ℂ S)
    (x : groupCohomology.H2 A) : x = 0 := by
  let e := groupCohomology.coindIso A 2
  have h := hG (Rep.coind S.subtype A) (e.inv x)
  have back : e.hom (e.inv x) = x := by
    change (e.inv ≫ e.hom) x = x
    rw [e.inv_hom_id]
    rfl
  rw [← back, h, map_zero]

/-- **Hochschild--Serre characterization of the classes vanishing on the flag stabilizers.** Let
`B i ≤ L` be a family of subgroups of the Levi (the cusp stabilizers) such that `H²(B i, ·)` vanishes.
A class `y` of `H²(E, ρ)` with zero radical restriction has Hochschild--Serre edge in the cuspidal
subspace of `H¹(L, H¹(N, ρ))` for the family `B` iff its restriction to the preimage in `E` of each
`B i` (the stabilizer of the corresponding complete flag) vanishes. -/
theorem edge_mem_cuspidalFamily_iff {ι : Type} (B : ι → Subgroup L)
    (hB : ∀ i (V : Rep ℂ (B i)) (x : groupCohomology.H2 V), x = 0)
    (y : groupCohomology.H2 ρ) (hy : twoCohomologyRestriction ext.inl ρ y = 0) :
    splitCohomologyEdge s ρ ⟨y, hy⟩ ∈ cuspidalFamily B (splitRadicalH1Representation s ρ) ↔
      ∀ i, twoCohomologyRestriction (incl ext (B i)) ρ y = 0 := by
  unfold cuspidalFamily
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun i => ?_
  rw [← map_modMor_eq_zero_iff s ρ (B i), ← edge_kerRes s ρ (B i) ⟨y, hy⟩]
  have hinj := splitCohomologyEdge_injective_of_invariant_H2_zero (splitRestrict s (B i))
    (resRep ext ρ (B i)) (fun x => hB i _ x)
  rw [← map_zero (splitCohomologyEdge (splitRestrict s (B i)) (resRep ext ρ (B i))),
    hinj.eq_iff, Subtype.ext_iff, kerRes_val]
  rfl

end LocallyInner

end TernaryPeriodPolynomials.Argument.SeedC3S4c
