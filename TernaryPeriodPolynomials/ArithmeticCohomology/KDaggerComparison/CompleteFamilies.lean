module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Injective
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteShapiro

@[expose] public section


/-!
# `K†` comparison, completeness: the `K†`-equivariant families of face classes

For `side ∈ {plane, line}` let `FaceFamily N n side = ∏_{F ∈ Flags side} H²(Γ_F ∩ (Γ ∩ Γ(N)), E_n)` (homogeneous model, `Γ_F` the
stabilizer of `F` in `K†`).  The group `K† = rationalLevel` acts on it by `(k • w)(F) = k_* w(k⁻¹ F)` (`famAct`, conjugation `actH2Conj` of
the stabilizer classes).  `stratumFamily` sends a `K†`-stratum class `ξ` (the coinduced `H²(K†, Map(Flags, E_n))`) to the family of its
restrictions `F ↦ res_{Γ_F ∩ Γ(N)} (ξ at F)`.

* `stratumFamily_injective`: no information is lost (Shapiro + level descent);
* `range_stratumFamily`: **the image is exactly the `K†`-invariant families** (`qFamilies`): Shapiro surjectivity for `K†`
  (`exists_fixedPointH2_eq`) together with the finite-group descent `mem_range_resH2_iff` for each stabilizer;
* `stratumFamilyEquiv`: the resulting linear isomorphism `StratumH2 ≃ₗ[ℂ] qFamilies`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

section Families

variable (N : ℕ) [NeZero N] (n : ℕ) {side : Side}

omit [NeZero N] in
theorem isConj_stab_principal_side {q : RationalGL3} (hq : q ∈ rationalLevel) {F F' : Flags side}
    (hF : F' = q⁻¹ • F) :
    IsConj (fixedPointLevel (levelPrincipal N) F') (fixedPointLevel (levelPrincipal N) F) q := by
  intro x
  subst hF
  constructor
  · rintro ⟨hxM, hxF⟩
    refine ⟨levelPrincipal_norm N q hq x hxM, ?_⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have := MulAction.mem_stabilizer_iff.mp hxF
    rw [mul_smul, mul_smul, smul_inv_smul, this]
  · rintro ⟨hxM, hxF⟩
    have hxM' : x ∈ levelPrincipal N := by
      have := levelPrincipal_norm N q⁻¹ ((rationalLevel).inv_mem hq) _ hxM
      simpa [mul_assoc] using this
    refine ⟨hxM', ?_⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have h2 := MulAction.mem_stabilizer_iff.mp hxF
    rw [mul_smul, mul_smul, smul_inv_smul] at h2
    exact smul_left_cancel q⁻¹ h2

omit [NeZero N] in
/-- Restriction to `Γ_F ∩ Γ(N)` commutes with the transport of stabilizer classes along `q ∈ K†` (conjugation of `Γ ∩ Γ(N)`-classes). -/
theorem resPrincipal_transport_side (q : rationalLevel) {F' F : Flags side} (hF : q.val • F' = F)
    (hg : IsConj (fixedPointLevel (levelPrincipal N) F') (fixedPointLevel (levelPrincipal N) F) q.val)
    (z : H2 (fixedPointLevel rationalLevel F') (rationalCoefficientComponent n trivialCharacter)) :
    resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) q F' F hF z) =
      actH2Conj (rationalCoefficientComponent n trivialCharacter) q.val hg
        (resPrincipal N F' (rationalCoefficientComponent n trivialCharacter) z) := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

/-- The restrictions of a stratum class to the groups `Γ_F ∩ Γ(N)`, for all flags `F`. -/
abbrev FaceFamily (side : Side) : Type :=
  ∀ F : Flags side, H2 (fixedPointLevel (levelPrincipal N) F) (rationalCoefficientComponent n trivialCharacter)

/-- The action of `k ∈ K†` on families: `(k • w)(F) = k_* w(k⁻¹ F)`. -/
def famAct (k : rationalLevel) : FaceFamily N n side →ₗ[ℂ] FaceFamily N n side :=
  LinearMap.pi fun F => (actH2Conj (rationalCoefficientComponent n trivialCharacter) k.val
    (isConj_stab_principal_side N k.2 (F := F) (F' := k.val⁻¹ • F) rfl)).comp
    (LinearMap.proj (k.val⁻¹ • F))

/-- The `K†`-invariant families. -/
def qFamilies (side : Side) : Submodule ℂ (FaceFamily N n side) where
  carrier := {w | ∀ k : rationalLevel, famAct N n k w = w}
  zero_mem' := fun k => map_zero _
  add_mem' := fun {x y} hx hy k => by rw [map_add, hx k, hy k]
  smul_mem' := fun a x hx k => by rw [map_smul, hx k]

/-- The family of restrictions of a stratum class to the groups `Γ_F ∩ Γ(N)`. -/
def stratumFamily (side : Side) : StratumH2 n trivialCharacter side →ₗ[ℂ] FaceFamily N n side :=
  LinearMap.pi fun F => resPrincipal N F (rationalCoefficientComponent n trivialCharacter) ∘ₗ
    fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F

omit [NeZero N] in
theorem stratumFamily_apply (ξ : StratumH2 n trivialCharacter side) (F : Flags side) :
    stratumFamily N n side ξ F = resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ) := rfl

omit [NeZero N] in
theorem famAct_apply (k : rationalLevel) (w : FaceFamily N n side) (F : Flags side) :
    famAct N n k w F = actH2Conj (rationalCoefficientComponent n trivialCharacter) k.val
      (isConj_stab_principal_side N k.2 (F := F) (F' := k.val⁻¹ • F) rfl) (w (k.val⁻¹ • F)) := rfl

omit [NeZero N] in
/-- The restriction families of stratum classes are `K†`-invariant. -/
theorem stratumFamily_mem (ξ : StratumH2 n trivialCharacter side) :
    stratumFamily N n side ξ ∈ qFamilies N n side := by
  intro k
  funext F
  rw [famAct_apply, stratumFamily_apply, stratumFamily_apply]
  have hF' : k.val • (k.val⁻¹ • F) = F := smul_inv_smul k.val F
  have h2 := resPrincipal_transport_side N n k hF' (isConj_stab_principal_side N k.2 rfl)
    (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (k.val⁻¹ • F) ξ)
  have e := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    k (k.val⁻¹ • F) F hF' ξ
  rw [e] at h2
  exact h2.symm

/-- **No information is lost** (Shapiro + level descent). -/
theorem stratumFamily_injective (side : Side) : Function.Injective (stratumFamily N n side) := by
  rw [injective_iff_map_eq_zero]
  intro ξ h
  refine (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) ξ).mpr fun F => ?_
  exact fixedPointH2_eq_zero_of_res N n ξ F (congrFun h F)

omit [NeZero N] in
theorem orbitRepresentative_orbitRepresentative (F : Flags side) :
    orbitRepresentative rationalLevel (orbitRepresentative rationalLevel F) = orbitRepresentative rationalLevel F := by
  have h := orbitRepresentative_smul rationalLevel (orbitTransport rationalLevel F)⁻¹ F
  have e : ((orbitTransport rationalLevel F)⁻¹).val • F = orbitRepresentative rationalLevel F := by
    have := congrArg (fun f => ((orbitTransport rationalLevel F).val)⁻¹ • f) (orbitTransport_spec rationalLevel F)
    simpa only [Subgroup.coe_inv, inv_smul_smul] using this.symm
  rw [e] at h
  exact h

theorem actH2Conj_self_eq_actH2 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {Δ : Subgroup G} {g : G} (hg : IsConj Δ Δ g) (hn : ∀ m ∈ Δ, g⁻¹ * m * g ∈ Δ) (x : H2 Δ ρ) :
    actH2Conj ρ g hg x = actH2 ρ g hn x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

omit [NeZero N] in
theorem famAct_apply' (k : rationalLevel) (w : FaceFamily N n side) {F F' : Flags side} (hF : F' = k.val⁻¹ • F) :
    famAct N n k w F = actH2Conj (rationalCoefficientComponent n trivialCharacter) k.val
      (isConj_stab_principal_side N k.2 hF) (w F') := by
  subst hF
  rfl

/-- **Every `K†`-invariant family is the restriction family of a stratum class** (Shapiro surjectivity for `K†`). -/
theorem exists_stratum_of_mem (w : FaceFamily N n side) (hw : w ∈ qFamilies N n side) :
    ∃ ξ : StratumH2 n trivialCharacter side, stratumFamily N n side ξ = w := by
  have hrange : ∀ F : Flags side, ∃ z : H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent n trivialCharacter),
      resPrincipal N F (rationalCoefficientComponent n trivialCharacter) z = w F := by
    intro F
    have hfin : ((levelPrincipal N).subgroupOf (fixedPointLevel rationalLevel F)).FiniteIndex := by
      have : (levelPrincipal N).IsFiniteRelIndex (fixedPointLevel rationalLevel F) :=
        Subgroup.isFiniteRelIndex_of_le_right (H := levelPrincipal N) (K := fixedPointLevel rationalLevel F)
          (L := rationalLevel) inf_le_left
      infer_instance
    have heq : (fixedPointLevel (levelPrincipal N) F).subgroupOf (fixedPointLevel rationalLevel F) =
        (levelPrincipal N).subgroupOf (fixedPointLevel rationalLevel F) := by
      ext g
      exact ⟨fun h => h.1, fun h => ⟨h, g.2.2⟩⟩
    have hfin' : ((fixedPointLevel (levelPrincipal N) F).subgroupOf (fixedPointLevel rationalLevel F)).FiniteIndex := by
      rw [heq]; exact hfin
    let _ : Fintype (↥(fixedPointLevel rationalLevel F) ⧸
        (fixedPointLevel (levelPrincipal N) F).subgroupOf (fixedPointLevel rationalLevel F)) :=
      Subgroup.fintypeQuotientOfFiniteIndex
    refine (mem_range_resH2_iff (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) F)
      (fixedPointLevel_hnorm (levelPrincipal N) (levelPrincipal_norm N) F) (w F)).mpr ?_
    intro s hs
    have hstab : F = s⁻¹ • F := by
      have := MulAction.mem_stabilizer_iff.mp hs.2
      rw [eq_inv_smul_iff]; exact this
    have h1 := congrFun (hw ⟨s, hs.1⟩) F
    rw [famAct_apply' N n ⟨s, hs.1⟩ w hstab] at h1
    rw [← actH2Conj_self_eq_actH2 _ (isConj_stab_principal_side N hs.1 hstab)]
    exact h1
  choose z hz using hrange
  obtain ⟨y, hy⟩ := exists_fixedPointH2_eq rationalLevel (rationalCoefficientComponent n trivialCharacter)
    (X := Flags side) z
  refine ⟨y, ?_⟩
  funext F
  change resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
    (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F y) = w F
  have ht := orbitTransport_spec rationalLevel F
  have hF₀ := orbitRepresentative_orbitRepresentative (side := side) F
  have e := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    (orbitTransport rationalLevel F) (orbitRepresentative rationalLevel F) F ht y
  rw [← e, hy _ hF₀]
  have hinv : orbitRepresentative rationalLevel F = (orbitTransport rationalLevel F).val⁻¹ • F := by
    rw [eq_inv_smul_iff]; exact ht
  rw [resPrincipal_transport_side N n (orbitTransport rationalLevel F) ht
    (isConj_stab_principal_side N (orbitTransport rationalLevel F).2 hinv), hz]
  have h1 := congrFun (hw (orbitTransport rationalLevel F)) F
  rw [famAct_apply' N n _ w hinv] at h1
  exact h1

/-- **The image of the restriction families is exactly the `K†`-invariant families.** -/
theorem range_stratumFamily (side : Side) :
    LinearMap.range (stratumFamily N n side) = qFamilies N n side := by
  apply le_antisymm
  · rintro _ ⟨ξ, rfl⟩
    exact stratumFamily_mem N n ξ
  · intro w hw
    obtain ⟨ξ, hξ⟩ := exists_stratum_of_mem N n w hw
    exact ⟨ξ, hξ⟩

/-- **Completeness of the restriction families.**  The stratum cohomology of `K†` is isomorphic to the `K†`-invariant families
of classes of the groups `Γ_F ∩ Γ(N)`. -/
def stratumFamilyEquiv (side : Side) : StratumH2 n trivialCharacter side ≃ₗ[ℂ] qFamilies N n side :=
  (LinearEquiv.ofInjective (stratumFamily N n side) (stratumFamily_injective N n side)).trans
    (LinearEquiv.ofEq _ _ (range_stratumFamily N n side))

end Families
end TernaryPeriodPolynomials.Argument.KDaggerComparison
