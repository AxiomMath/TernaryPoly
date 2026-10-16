module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.DescentHom

@[expose] public section


/-!
# Transfer back: the level group's locally inner classes are the transfers of those of `Γ ∩ Γ(N)`

Paper: Lemma C.3 (`ar:lem:seed`),
 ("the seeds span `𝒞_P(E)` after including all plane cusps and finite
reflections").

In the homogeneous-cochain model, for a normal finite-index subgroup `M` of the level group:

* `trH2`: the transfer (corestriction) `H²(N, ρ) → H²(S, ρ)` for `N ≤ S` normal of finite index,
  given by averaging cocycles; `trH2_resH2`: `tr ∘ res = id`; `resH2_trH2`: `res ∘ tr` is the averaging
  projection `|S/N|⁻¹ ∑ q•` onto the invariants;
* `res_act_zero`, `actH2_mem_locallyInnerAt`: the locally inner classes for the level `M` are stable
  under the conjugation action of the stabilizer `Γ_F` of the flag (conjugation permutes the flags over
  `F`);
* `trH2_mem_locallyInnerAt`: the transfer of a locally inner class of `Γ_F ∩ M` is a locally inner class
  of `Γ_F`;
* **`map_trH2_locallyInnerAt`: `𝒞(Γ_F) = tr(𝒞(Γ_F ∩ M))`**, as submodules of `H²(Γ_F, ρ)`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.LevelTransfer

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section Stability

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

theorem isEq_act' {N N' : Subgroup G} {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ N f) {s : G}
    (hs : ∀ n ∈ N', s⁻¹ * n * s ∈ N) : IsEq ρ N' (actFun ρ s f) := by
  intro γ hγ x
  simp only [actFun_apply]
  have h1 : (fun i => s⁻¹ * (γ * x i)) = fun i => (s⁻¹ * γ * s) * (s⁻¹ * x i) := by
    funext i; group
  rw [h1, hf _ (hs γ hγ), ← Module.End.mul_apply, ← map_mul]
  have : s * (s⁻¹ * γ * s) = γ * s := by group
  rw [this, map_mul, Module.End.mul_apply]

/-- If `y ∈ H²(B)` vanishes on `A' ≤ B` and `s` carries `A` into `A'` by conjugation (and normalizes
`B`), then `s • y` vanishes on `A ≤ B`. -/
theorem res_act_zero {A A' B : Subgroup G} (hAB : A ≤ B) (hA'B : A' ≤ B) {s : G}
    (hsB : ∀ n ∈ B, s⁻¹ * n * s ∈ B) (hsA : ∀ n ∈ A, s⁻¹ * n * s ∈ A') (y : H2 B ρ)
    (hy : resH2 ρ hA'B y = 0) : resH2 ρ hAB (actH2 ρ s hsB y) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have h1 : Submodule.Quotient.mk (cocyclesRes ρ hA'B z) = (0 : H2 A' ρ) := hy
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : rd1 c.val = z.val.val := congrArg (fun t => t.val.val) hc
  have hcEq : IsEq ρ A' c.val := (mem_cochains_iff ρ A' 1 _).mp c.2
  change Submodule.Quotient.mk (cocyclesRes ρ hAB (actCocycle ρ s hsB z)) = (0 : H2 A ρ)
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨⟨actFun ρ s c.val, (mem_cochains_iff ρ A 1 _).mpr (isEq_act' ρ hcEq hsA)⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change rd1 (actFun ρ s c.val) = actFun ρ s z.val.val
  rw [← actFun_rd1, h2]

section FlagStability

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
  (M : Subgroup RationalGL3) (hM : M ≤ rationalLevel)
  (hMnorm : ∀ g ∈ rationalLevel, ∀ m ∈ M, g⁻¹ * m * g ∈ M)

omit hM in
/-- The locally inner classes for the level `M` are stable under the conjugation action of the
stabilizer `Γ_F` of the flag in the level group. -/
theorem actH2_mem_locallyInnerAt {side : Side} (flag : Flags side) {s : RationalGL3}
    (hs : s ∈ fixedPointLevel rationalLevel flag) (y : H2 (fixedPointLevel M flag) ρ)
    (hy : y ∈ locallyInnerAt ρ M flag) :
    actH2 ρ s (fixedPointLevel_hnorm M hMnorm flag s hs) y ∈ locallyInnerAt ρ M flag := by
  simp only [locallyInnerAt, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall] at hy ⊢
  intro e he
  have hsF : s⁻¹ • flag = flag := by
    have := MulAction.mem_stabilizer_iff.mp ((fixedPointLevel rationalLevel flag).inv_mem hs).2
    exact this
  have he' : endpoint side (s⁻¹ • e) = flag := by
    rw [endpoint_smul, he, hsF]
  refine res_act_zero ρ (fixedPointLevel_edge_le_flag' M side e flag he)
    (fixedPointLevel_edge_le_flag' M side (s⁻¹ • e) flag he')
    (fixedPointLevel_hnorm M hMnorm flag s hs) ?_ y (hy _ he')
  intro n hn
  refine ⟨hMnorm s hs.1 n hn.1, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  have h2 : n • e = e := MulAction.mem_stabilizer_iff.mp hn.2
  rw [mul_smul, mul_smul, smul_inv_smul, h2]

end FlagStability

section Transfer

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  {N S : Subgroup G} [Fintype (S ⧸ N.subgroupOf S)]

/-- The averaging of cocycles as a linear map. -/
def avgCocycleL (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) :
    cocycles N ρ →ₗ[ℂ] cocycles S ρ where
  toFun := avgCocycle ρ hNS hnorm
  map_add' a b := by
    apply Subtype.ext; apply Subtype.ext
    exact map_add (avg ρ N S) _ _
  map_smul' c a := by
    apply Subtype.ext; apply Subtype.ext
    exact map_smul (avg ρ N S) _ _

/-- **The transfer (corestriction) `H²(N, ρ) → H²(S, ρ)`** for a normal finite-index `N ≤ S`:
the averaging of cocycles. -/
def trH2 (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) : H2 N ρ →ₗ[ℂ] H2 S ρ :=
  Submodule.mapQ _ _ (avgCocycleL ρ hNS hnorm) (by
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨avg ρ N S c.val, avg_mem_cochains ρ hNS hnorm c⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (avg_rd1 ρ N S c.val).symm)

/-- `tr ∘ res = id`. -/
theorem trH2_resH2 (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) (x : H2 S ρ) :
    trH2 ρ hNS hnorm (resH2 ρ hNS x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (avgCocycle ρ hNS hnorm (cocyclesRes ρ hNS z)) = _
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact avg_of_isEq_S ρ ((mem_cochains_iff ρ S 2 _).mp z.val.2)

/-- `res ∘ tr` is the averaging projection onto the invariants. -/
theorem resH2_trH2 (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) (y : H2 N ρ) :
    resH2 ρ hNS (trH2 ρ hNS hnorm y) =
      ((Fintype.card (S ⧸ N.subgroupOf S) : ℂ)⁻¹) •
        ∑ q : S ⧸ N.subgroupOf S, actH2 ρ ((Quotient.out q : S) : G) (hnorm _ (Quotient.out q).2) y := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (cocyclesRes ρ hNS (avgCocycle ρ hNS hnorm w)) = _
  rw [cocyclesRes_avg]
  rw [← Submodule.mkQ_apply, map_smul, map_sum]
  rfl

end Transfer

section TransferBack

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
  (M : Subgroup RationalGL3) (hM : M ≤ rationalLevel)
  (hMnorm : ∀ g ∈ rationalLevel, ∀ m ∈ M, g⁻¹ * m * g ∈ M)
  [M.IsFiniteRelIndex rationalLevel]

/-- The finite quotient `Γ_F / (Γ_F ∩ M)`. -/
abbrev quotFintype {side : Side} (flag : Flags side) :
    Fintype (↥(fixedPointLevel rationalLevel flag) ⧸
      (fixedPointLevel M flag).subgroupOf (fixedPointLevel rationalLevel flag)) := by
  have hfin : (M.subgroupOf (fixedPointLevel rationalLevel flag)).FiniteIndex := by
    have : M.IsFiniteRelIndex (fixedPointLevel rationalLevel flag) :=
      Subgroup.isFiniteRelIndex_of_le_right (H := M) (K := fixedPointLevel rationalLevel flag)
        (L := rationalLevel) inf_le_left
    infer_instance
  have heq : (fixedPointLevel M flag).subgroupOf (fixedPointLevel rationalLevel flag) =
      M.subgroupOf (fixedPointLevel rationalLevel flag) := by
    ext g
    exact ⟨fun h => h.1, fun h => ⟨h, g.2.2⟩⟩
  have hfin' : ((fixedPointLevel M flag).subgroupOf
      (fixedPointLevel rationalLevel flag)).FiniteIndex := by
    rw [heq]; exact hfin
  exact Subgroup.fintypeQuotientOfFiniteIndex

include hM hMnorm in
/-- The transfer `H²(Γ_F ∩ M, ρ) → H²(Γ_F, ρ)` (averaging over `Γ_F / (Γ_F ∩ M)`). -/
def trLevel {side : Side} (flag : Flags side) :
    H2 (fixedPointLevel M flag) ρ →ₗ[ℂ] H2 (fixedPointLevel rationalLevel flag) ρ :=
  @trH2 _ _ _ _ _ ρ _ _ (quotFintype M flag) (fixedPointLevel_mono_level M hM flag)
    (fixedPointLevel_hnorm M hMnorm flag)

include hM hMnorm in
/-- **The transfer of a locally inner class of `Γ_F ∩ M` is a locally inner class of `Γ_F`.** -/
theorem trH2_mem_locallyInnerAt {side : Side} (flag : Flags side)
    (y : H2 (fixedPointLevel M flag) ρ) (hy : y ∈ locallyInnerAt ρ M flag) :
    trLevel ρ M hM hMnorm flag y ∈ locallyInnerAt ρ rationalLevel flag := by
  let _ := quotFintype M flag
  rw [mem_locallyInnerAt_iff_res ρ M hM hMnorm flag]
  change resH2 ρ _ (trH2 ρ _ _ y) ∈ _
  rw [resH2_trH2]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
  exact actH2_mem_locallyInnerAt ρ M hMnorm flag (Quotient.out q).2 y hy

include hM hMnorm in
/-- **The locally inner classes of the level group are the transfers of the locally inner classes of
`Γ_F ∩ M`.** -/
theorem map_trH2_locallyInnerAt {side : Side} (flag : Flags side) :
    Submodule.map (trLevel ρ M hM hMnorm flag) (locallyInnerAt ρ M flag) =
      locallyInnerAt ρ rationalLevel flag := by
  let _ := quotFintype M flag
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact trH2_mem_locallyInnerAt ρ M hM hMnorm flag y hy
  · intro x hx
    refine ⟨resH2 ρ (fixedPointLevel_mono_level M hM flag) x,
      (mem_locallyInnerAt_iff_res ρ M hM hMnorm flag x).mp hx, ?_⟩
    exact trH2_resH2 ρ _ _ x

/-- `tr ∘ res = id` on the level group's classes. -/
theorem trLevel_resH2 {side : Side} (flag : Flags side) (x : H2 (fixedPointLevel rationalLevel flag) ρ) :
    trLevel ρ M hM hMnorm flag (resH2 ρ (fixedPointLevel_mono_level M hM flag) x) = x := by
  let _ := quotFintype M flag
  exact trH2_resH2 ρ _ _ x

end TransferBack



end Stability

end TernaryPeriodPolynomials.Argument.SeedC3S4c
