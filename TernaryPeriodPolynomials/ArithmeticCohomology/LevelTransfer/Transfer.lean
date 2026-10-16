module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Cochains

@[expose] public section


/-!
# Level transfer (L2), step 2: restriction `H²(S, ρ) → H²(N, ρ)` and its image

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelTransfer

open GeneralEisenstein.Homogeneous

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  {N S : Subgroup G}

theorem cochains_mono (hNS : N ≤ S) (k : ℕ) : cochains S ρ k ≤ cochains N ρ k := by
  intro f hf
  exact (mem_cochains_iff ρ N k f).mpr (fun γ hγ x => ((mem_cochains_iff ρ S k f).mp hf) γ (hNS hγ) x)

/-- Restriction of equivariant cochains from `S` to `N ≤ S`. -/
def cochainsRes (hNS : N ≤ S) (k : ℕ) : cochains S ρ k →ₗ[ℂ] cochains N ρ k :=
  Submodule.inclusion (cochains_mono ρ hNS k)

theorem differentialTwo_eq (Γ : Subgroup G) (f : cochains Γ ρ 2) :
    differentialTwo Γ ρ f = rd2 f.val := rfl

theorem differentialOne_val (Γ : Subgroup G) (f : cochains Γ ρ 1) :
    (differentialOne Γ ρ f).val = rd1 f.val := rfl

/-- Restriction of cocycles. -/
def cocyclesRes (hNS : N ≤ S) : cocycles S ρ →ₗ[ℂ] cocycles N ρ where
  toFun z := ⟨cochainsRes ρ hNS 2 z.val, by
    have h := z.property
    change differentialTwo S ρ z.val = 0 at h
    change differentialTwo N ρ (cochainsRes ρ hNS 2 z.val) = 0
    rw [differentialTwo_eq] at h ⊢
    exact h⟩
  map_add' z w := rfl
  map_smul' a z := rfl

/-- Restriction `H²(S, ρ) → H²(N, ρ)`. -/
def resH2 (hNS : N ≤ S) : H2 S ρ →ₗ[ℂ] H2 N ρ :=
  Submodule.mapQ _ _ (cocyclesRes ρ hNS) (by
    rintro _ ⟨c, rfl⟩
    refine ⟨cochainsRes ρ hNS 1 c, ?_⟩
    rfl)

/-- The action of `s ∈ S` on the `N`-cocycles (`N` normal in `S`). -/
def actCocycle (s : G) (hs : ∀ n ∈ N, s⁻¹ * n * s ∈ N) : cocycles N ρ →ₗ[ℂ] cocycles N ρ where
  toFun z := ⟨⟨actFun ρ s z.val.val,
      (mem_cochains_iff ρ N 2 _).mpr (IsEq.act ρ ((mem_cochains_iff ρ N 2 _).mp z.val.2) hs)⟩, by
    have h := z.property
    change differentialTwo N ρ z.val = 0 at h
    rw [differentialTwo_eq] at h
    change differentialTwo N ρ _ = 0
    rw [differentialTwo_eq]
    change rd2 (actFun ρ s z.val.val) = 0
    rw [← actFun_rd2, h, map_zero]⟩
  map_add' z w := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' a z := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

/-- The action of `s ∈ S` on `H²(N, ρ)`. -/
def actH2 (s : G) (hs : ∀ n ∈ N, s⁻¹ * n * s ∈ N) : H2 N ρ →ₗ[ℂ] H2 N ρ :=
  Submodule.mapQ _ _ (actCocycle ρ s hs) (by
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨actFun ρ s c.val,
      (mem_cochains_iff ρ N 1 _).mpr (IsEq.act ρ ((mem_cochains_iff ρ N 1 _).mp c.2) hs)⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    exact (actFun_rd1 ρ s c.val).symm)

section Main

variable [Fintype (S ⧸ N.subgroupOf S)]

theorem avg_mem_cochains (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) {k : ℕ}
    (f : cochains N ρ k) : avg ρ N S f.val ∈ cochains S ρ k := by
  have hf := (mem_cochains_iff ρ N k _).mp f.2
  exact (mem_cochains_iff ρ S k _).mpr
    ((isEq_iff_fixed ρ hNS _).mpr ⟨isEq_avg ρ N S hf hnorm, fun s hs => actFun_avg ρ N S hf hs⟩)

/-- Averaging a cocycle of `N` gives a cocycle of `S`. -/
def avgCocycle (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) (w : cocycles N ρ) :
    cocycles S ρ :=
  ⟨⟨avg ρ N S w.val.val, avg_mem_cochains ρ hNS hnorm w.val⟩, by
    have h := w.property
    change differentialTwo N ρ w.val = 0 at h
    rw [differentialTwo_eq] at h
    change differentialTwo S ρ _ = 0
    rw [differentialTwo_eq]
    change rd2 (avg ρ N S w.val.val) = 0
    rw [← avg_rd2, h, map_zero]⟩

theorem resH2_injective (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) :
    Function.Injective (resH2 ρ hNS) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : Submodule.Quotient.mk (cocyclesRes ρ hNS z) = (0 : H2 N ρ) := hx
  rw [Submodule.Quotient.mk_eq_zero] at hx'
  obtain ⟨c, hc⟩ := hx'
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨⟨avg ρ N S c.val, avg_mem_cochains ρ hNS hnorm c⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h1 : rd1 c.val = z.val.val := congrArg (fun t => t.val.val) hc
  change rd1 (avg ρ N S c.val) = z.val.val
  rw [← avg_rd1, h1]
  exact avg_of_isEq_S ρ ((mem_cochains_iff ρ S 2 _).mp z.val.2)

theorem cocyclesRes_avg (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
    (w : cocycles N ρ) :
    cocyclesRes ρ hNS (avgCocycle ρ hNS hnorm w) =
      ((Fintype.card (S ⧸ N.subgroupOf S) : ℂ)⁻¹) •
        ∑ q : S ⧸ N.subgroupOf S,
          actCocycle ρ ((Quotient.out q : S) : G) (hnorm _ (Quotient.out q).2) w := by
  apply Subtype.ext
  apply Subtype.ext
  change avg ρ N S w.val.val = _
  rw [avg_apply]
  simp only [Submodule.coe_smul, Submodule.coe_sum]
  rfl

theorem mem_range_resH2_iff (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
    (x : H2 N ρ) :
    x ∈ LinearMap.range (resH2 ρ hNS) ↔ ∀ (s : G) (hs : s ∈ S), actH2 ρ s (hnorm s hs) x = x := by
  constructor
  · rintro ⟨y, rfl⟩ s hs
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (actCocycle ρ s (hnorm s hs) (cocyclesRes ρ hNS z)) =
      Submodule.Quotient.mk (cocyclesRes ρ hNS z)
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact IsEq.act_mem ρ ((mem_cochains_iff ρ S 2 _).mp z.val.2) hs
  · intro h
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨Submodule.Quotient.mk (avgCocycle ρ hNS hnorm w), ?_⟩
    change Submodule.Quotient.mk (cocyclesRes ρ hNS (avgCocycle ρ hNS hnorm w)) = _
    rw [Submodule.Quotient.eq, cocyclesRes_avg]
    have hm : (Fintype.card (S ⧸ N.subgroupOf S) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hw : w = ((Fintype.card (S ⧸ N.subgroupOf S) : ℂ)⁻¹) •
        ∑ q : S ⧸ N.subgroupOf S, w := by
      simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      rw [inv_mul_cancel₀ hm, one_smul]
    have key : ((Fintype.card (S ⧸ N.subgroupOf S) : ℂ)⁻¹) •
          ∑ q : S ⧸ N.subgroupOf S, actCocycle ρ ((Quotient.out q : S) : G)
            (hnorm _ (Quotient.out q).2) w - w =
        ((Fintype.card (S ⧸ N.subgroupOf S) : ℂ)⁻¹) •
          ∑ q : S ⧸ N.subgroupOf S, (actCocycle ρ ((Quotient.out q : S) : G)
            (hnorm _ (Quotient.out q).2) w - w) := by
      rw [Finset.sum_sub_distrib, smul_sub, ← hw]
    rw [key]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro q _
    have hq := h _ (Quotient.out q).2
    change Submodule.Quotient.mk (actCocycle ρ _ _ w) = Submodule.Quotient.mk w at hq
    rw [Submodule.Quotient.eq] at hq
    exact hq

/-- The `S`-invariant classes in `H²(N, ρ)`. -/
def invariantsH2 (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) :
    Submodule ℂ (H2 N ρ) where
  carrier := {x | ∀ (s : G) (hs : s ∈ S), actH2 ρ s (hnorm s hs) x = x}
  zero_mem' := fun s hs => map_zero _
  add_mem' := fun {x y} hx hy s hs => by rw [map_add, hx s hs, hy s hs]
  smul_mem' := fun a x hx s hs => by rw [map_smul, hx s hs]

/-- **Level transfer in degree two** (link L2 of the model comparison): for `N ⊲ S` of finite index,
restriction identifies the homogeneous-cochain cohomology `H²(S, ρ)` with the `S/N`-invariants of
`H²(N, ρ)`. -/
def resH2Equiv (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) :
    H2 S ρ ≃ₗ[ℂ] invariantsH2 ρ hnorm :=
  LinearEquiv.ofBijective
    ((resH2 ρ hNS).codRestrict (invariantsH2 ρ hnorm) (fun y => by
      exact (mem_range_resH2_iff ρ hNS hnorm _).mp ⟨y, rfl⟩))
    ⟨fun x y h => resH2_injective ρ hNS hnorm (congrArg Subtype.val h),
     fun ⟨x, hx⟩ => by
       obtain ⟨y, hy⟩ := (mem_range_resH2_iff ρ hNS hnorm x).mpr hx
       exact ⟨y, Subtype.ext hy⟩⟩

theorem resH2Equiv_apply (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) (x : H2 S ρ) :
    ((resH2Equiv ρ hNS hnorm x : invariantsH2 ρ hnorm) : H2 N ρ) = resH2 ρ hNS x := rfl

end Main

/-- Restriction is transitive. -/
theorem resH2_comp {M : Subgroup G} (hMN : M ≤ N) (hNS : N ≤ S) (x : H2 S ρ) :
    resH2 ρ hMN (resH2 ρ hNS x) = resH2 ρ (hMN.trans hNS) x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- If `M` is normal in the ambient group, `S ⊓ M` is normalized by `S`. -/
theorem normalizes_inf (M : Subgroup G) [M.Normal] (S : Subgroup G) :
    ∀ s ∈ S, ∀ n ∈ S ⊓ M, s⁻¹ * n * s ∈ S ⊓ M := by
  rintro s hs n ⟨hnS, hnM⟩
  refine ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hnS) hs, ?_⟩
  have := ‹M.Normal›.conj_mem n hnM s⁻¹
  simpa using this

end TernaryPeriodPolynomials.Argument.LevelTransfer
