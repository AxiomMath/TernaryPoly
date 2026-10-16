module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Gamma2Generation

@[expose] public section


/-!
# `Γ₂ = ⟨A₀, B₀⟩ * ⟨R₀⟩ ≅ 𝔖₃ * C₂` (`eq:Gamma-presentation`)

The natural map from the free product of `⟨A₀, B₀⟩ ≅ 𝔖₃` and `⟨R₀⟩ ≅ C₂` to `Γ₂` is bijective.
Surjectivity is the Euclidean descent of `Gamma2Generation`; injectivity is the ping-pong lemma
(`Monoid.CoprodI.lift_injective_of_ping_pong`) for the action on `ℤ²` with the ping-pong sets
`{xy > 0}` (for `⟨A₀, B₀⟩ ∖ 1` to land in) and `{xy < 0}` (for `R₀` to land in).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open scoped Pointwise

/-- The group `Γ₂`, as a type. -/
abbrev Gamma2G : Type := ↥Gamma2

/-- `A₀ ∈ Γ₂`. -/
def a0 : Gamma2G := ⟨A0, A0_mem⟩
/-- `B₀ ∈ Γ₂`. -/
def b0 : Gamma2G := ⟨B0, B0_mem⟩
/-- `R₀ ∈ Γ₂`. -/
def r0 : Gamma2G := ⟨R0, R0_mem⟩

/-- The two factors of the presentation: `⟨A₀, B₀⟩` and `⟨R₀⟩`. -/
def Gamma2Factor : Fin 2 → Subgroup Gamma2G :=
  ![Subgroup.closure {a0, b0}, Subgroup.closure {r0}]

/-- The action of `Γ₂` on integral vectors. -/
local instance : MulAction Gamma2G (Fin 2 → ℤ) where
  smul g v := g.1.val.mulVec v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v g.1.val h.1.val).symm

theorem smul_def (g : Gamma2G) (v : Fin 2 → ℤ) : g • v = g.1.val.mulVec v := rfl

/-- The six elements of `⟨A₀, B₀⟩`. -/
def sixElts : List Gamma2G := [1, a0, a0⁻¹, b0, a0 * b0, a0⁻¹ * b0]

theorem sixElts_mul : ∀ x ∈ sixElts, ∀ y ∈ sixElts, x * y ∈ sixElts := by
  unfold sixElts a0 b0 A0 B0 Gamma2G
  decide +kernel

theorem sixElts_inv : ∀ x ∈ sixElts, x⁻¹ ∈ sixElts := by
  unfold sixElts a0 b0 A0 B0 Gamma2G
  decide +kernel

theorem closure_ab_mem_sixElts : ∀ h ∈ Subgroup.closure ({a0, b0} : Set Gamma2G), h ∈ sixElts := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · simp [sixElts]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simp [sixElts]
  | one => simp [sixElts]
  | mul x y _ _ hx hy => exact sixElts_mul x hx y hy
  | inv x _ hx => exact sixElts_inv x hx

/-- The two elements of `⟨R₀⟩`. -/
def twoElts : List Gamma2G := [1, r0]

theorem twoElts_mul : ∀ x ∈ twoElts, ∀ y ∈ twoElts, x * y ∈ twoElts := by
  unfold twoElts r0 R0 Gamma2G
  decide +kernel

theorem twoElts_inv : ∀ x ∈ twoElts, x⁻¹ ∈ twoElts := by
  unfold twoElts r0 R0 Gamma2G
  decide +kernel

theorem closure_r_mem_twoElts : ∀ h ∈ Subgroup.closure ({r0} : Set Gamma2G), h ∈ twoElts := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp [twoElts]
  | one => simp [twoElts]
  | mul x y _ _ hx hy => exact twoElts_mul x hx y hy
  | inv x _ hx => exact twoElts_inv x hx

/-- The ping-pong sets: `{xy > 0}` for the factor `⟨A₀, B₀⟩` and `{xy < 0}` for `⟨R₀⟩`. -/
def pingSet : Fin 2 → Set (Fin 2 → ℤ) := ![{v | 0 < v 0 * v 1}, {v | v 0 * v 1 < 0}]

theorem pp_lemma (a b c d x y : ℤ) (hac : 0 ≤ a * c) (hbd : 0 ≤ b * d) (hmid : a * d + b * c < 0)
    (hxy : x * y < 0) : 0 < (a * x + b * y) * (c * x + d * y) := by
  nlinarith [mul_nonneg hac (sq_nonneg x), mul_nonneg hbd (sq_nonneg y),
    mul_pos_of_neg_of_neg hmid hxy]

theorem pp_of_entries (h : Gamma2G) (hac : 0 ≤ h.1.val 0 0 * h.1.val 1 0)
    (hbd : 0 ≤ h.1.val 0 1 * h.1.val 1 1)
    (hmid : h.1.val 0 0 * h.1.val 1 1 + h.1.val 0 1 * h.1.val 1 0 < 0) (v : Fin 2 → ℤ)
    (hv : v 0 * v 1 < 0) : 0 < (h • v) 0 * (h • v) 1 := by
  rw [smul_def]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact pp_lemma _ _ _ _ _ _ hac hbd hmid hv

theorem pingpong_pairs : Pairwise fun i j : Fin 2 =>
    ∀ h : ↥(Gamma2Factor i), h ≠ 1 → (Gamma2Factor i).subtype h • pingSet j ⊆ pingSet i := by
  intro i j hij h hne v hv
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · obtain ⟨h, hh⟩ := h
    change h ∈ Subgroup.closure ({a0, b0} : Set Gamma2G) at hh
    have hne' : h ≠ 1 := fun e => hne (Subtype.ext e)
    obtain ⟨w, hw, rfl⟩ := hv
    have hw' : w 0 * w 1 < 0 := hw
    have hm := closure_ab_mem_sixElts h hh
    simp only [sixElts, List.mem_cons, List.not_mem_nil, or_false] at hm
    show 0 < (h • w) 0 * (h • w) 1
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hne'
    all_goals
      exact pp_of_entries _ (by decide +kernel)
        (by decide +kernel) (by decide +kernel) w hw'
  · obtain ⟨h, hh⟩ := h
    change h ∈ Subgroup.closure ({r0} : Set Gamma2G) at hh
    have hne' : h ≠ 1 := fun e => hne (Subtype.ext e)
    obtain ⟨w, hw, rfl⟩ := hv
    have hw' : 0 < w 0 * w 1 := hw
    have hm := closure_r_mem_twoElts h hh
    simp only [twoElts, List.mem_cons, List.not_mem_nil, or_false] at hm
    show (h • w) 0 * (h • w) 1 < 0
    rcases hm with rfl | rfl
    · exact absurd rfl hne'
    · rw [smul_def]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have e : (r0 : Gamma2G).1.val = !![-1, 0; 0, 1] := rfl
      rw [e]
      simp
      linarith
  · exact absurd rfl hij


theorem three_le_card_factor0 : 3 ≤ Cardinal.mk ↥(Gamma2Factor 0) := by
  have hmem : ∀ x ∈ ({1, a0, a0⁻¹} : Set Gamma2G), x ∈ Gamma2Factor 0 := by
    intro x hx
    change x ∈ Subgroup.closure ({a0, b0} : Set Gamma2G)
    rcases hx with rfl | hx
    · exact Subgroup.one_mem _
    rcases hx with rfl | hx
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  let f : Fin 3 → ↥(Gamma2Factor 0) := fun i =>
    ⟨![1, a0, a0⁻¹] i, hmem _ (by fin_cases i <;> simp)⟩
  have hf : Function.Injective f := by
    have h3 : ∀ i j : Fin 3, (![1, a0, a0⁻¹] : Fin 3 → Gamma2G) i = ![1, a0, a0⁻¹] j → i = j := by
      unfold a0 A0 Gamma2G
      decide +kernel
    intro i j hij
    exact h3 i j (congrArg Subtype.val hij)
  have := Cardinal.mk_le_of_injective hf
  simpa using this

/-- Injectivity of the free product map, by the ping-pong lemma. -/
theorem lift_injective :
    Function.Injective (Monoid.CoprodI.lift (fun i : Fin 2 => (Gamma2Factor i).subtype)) := by
  apply Monoid.CoprodI.lift_injective_of_ping_pong (fun i : Fin 2 => (Gamma2Factor i).subtype)
    (Or.inr ⟨0, three_le_card_factor0⟩) pingSet
  · intro i
    fin_cases i
    · exact ⟨![1, 1], by simp [pingSet]⟩
    · exact ⟨![-1, 1], by simp [pingSet]⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Function.onFun, Set.disjoint_left]
      intro v h0 h1
      simp only [pingSet] at h0 h1
      change 0 < v 0 * v 1 at h0
      change v 0 * v 1 < 0 at h1
      linarith
    · rw [Function.onFun, Set.disjoint_left]
      intro v h0 h1
      simp only [pingSet] at h0 h1
      change v 0 * v 1 < 0 at h0
      change 0 < v 0 * v 1 at h1
      linarith
    · exact absurd rfl hij
  · exact pingpong_pairs


theorem a0_mem_factor : a0 ∈ Gamma2Factor 0 :=
  Subgroup.subset_closure (by simp)

theorem b0_mem_factor : b0 ∈ Gamma2Factor 0 :=
  Subgroup.subset_closure (by simp)

theorem r0_mem_factor : r0 ∈ Gamma2Factor 1 :=
  Subgroup.subset_closure (by simp)

/-- Surjectivity of the free product map, from the Euclidean descent. -/
theorem lift_surjective :
    Function.Surjective (Monoid.CoprodI.lift (fun i : Fin 2 => (Gamma2Factor i).subtype)) := by
  set L := Monoid.CoprodI.lift (fun i : Fin 2 => (Gamma2Factor i).subtype) with hL
  have ha : a0 ∈ L.range :=
    ⟨Monoid.CoprodI.of (i := 0) ⟨a0, a0_mem_factor⟩, by simp [hL, Monoid.CoprodI.lift_of]⟩
  have hb : b0 ∈ L.range :=
    ⟨Monoid.CoprodI.of (i := 0) ⟨b0, b0_mem_factor⟩, by simp [hL, Monoid.CoprodI.lift_of]⟩
  have hr : r0 ∈ L.range :=
    ⟨Monoid.CoprodI.of (i := 1) ⟨r0, r0_mem_factor⟩, by simp [hL, Monoid.CoprodI.lift_of]⟩
  have key : ∀ x ∈ genSub, ∃ hx : x ∈ Gamma2, (⟨x, hx⟩ : Gamma2G) ∈ L.range := by
    intro x hx
    change x ∈ Subgroup.closure ({A0, B0, R0} : Set GL2Z) at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact ⟨A0_mem, ha⟩
      rcases hy with rfl | hy
      · exact ⟨B0_mem, hb⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨R0_mem, hr⟩
    | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨Subgroup.mul_mem _ hx1 hy1, L.range.mul_mem hx2 hy2⟩
    | inv x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      exact ⟨Subgroup.inv_mem _ hx1, L.range.inv_mem hx2⟩
  intro g
  obtain ⟨hx, hr⟩ := key g.1 (Gamma2_le_genSub g.2)
  exact hr

/-- The free product map is bijective. -/
theorem lift_bijective :
    Function.Bijective (Monoid.CoprodI.lift (fun i : Fin 2 => (Gamma2Factor i).subtype)) :=
  ⟨lift_injective, lift_surjective⟩

/-- A three-cycle of `Fin 3`. -/
def c3 : Equiv.Perm (Fin 3) := finRotate 3
/-- The transposition `(0 1)` of `Fin 3`. -/
def t3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The map `𝔖₃ → Γ₂` with `c ↦ A₀`, `t ↦ B₀`. -/
def toS3Fun (σ : Equiv.Perm (Fin 3)) : Gamma2G :=
  if σ = 1 then 1 else if σ = c3 then a0 else if σ = c3⁻¹ then a0⁻¹ else
    if σ = t3 then b0 else if σ = c3 * t3 then a0 * b0 else a0⁻¹ * b0

/-- The homomorphism `𝔖₃ → Γ₂` sending a three-cycle to `A₀` and a transposition to `B₀`. -/
def toS3 : Equiv.Perm (Fin 3) →* Gamma2G where
  toFun := toS3Fun
  map_one' := by simp [toS3Fun]
  map_mul' := by
    unfold toS3Fun c3 t3 a0 b0 A0 B0 Gamma2G
    decide +kernel

theorem toS3_injective : Function.Injective toS3 := by
  intro x y h
  revert x y
  unfold toS3 toS3Fun c3 t3 a0 b0 A0 B0 Gamma2G
  decide +kernel

theorem toS3_range : toS3.range = Gamma2Factor 0 := by
  have hval : ∀ σ, toS3Fun σ ∈ sixElts := by
    unfold toS3Fun c3 t3 sixElts a0 b0 A0 B0 Gamma2G
    decide +kernel
  have hsix : ∀ x ∈ sixElts, x ∈ Gamma2Factor 0 := by
    intro x hx
    change x ∈ Subgroup.closure ({a0, b0} : Set Gamma2G)
    simp only [sixElts, List.mem_cons, List.not_mem_nil, or_false] at hx
    have ha : a0 ∈ Subgroup.closure ({a0, b0} : Set Gamma2G) := Subgroup.subset_closure (by simp)
    have hb : b0 ∈ Subgroup.closure ({a0, b0} : Set Gamma2G) := Subgroup.subset_closure (by simp)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ha
    · exact Subgroup.inv_mem _ ha
    · exact hb
    · exact Subgroup.mul_mem _ ha hb
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    exact hsix _ (hval σ)
  · change Subgroup.closure ({a0, b0} : Set Gamma2G) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨c3, by unfold toS3 toS3Fun c3 a0 b0 A0 B0 Gamma2G; decide +kernel⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨t3, by unfold toS3 toS3Fun c3 t3 a0 b0 A0 B0 Gamma2G; decide +kernel⟩

/-- `⟨A₀, B₀⟩ ≅ 𝔖₃`. -/
def factor0Equiv : Equiv.Perm (Fin 3) ≃* ↥(Gamma2Factor 0) :=
  (MonoidHom.ofInjective toS3_injective).trans (MulEquiv.subgroupCongr toS3_range)

/-- The homomorphism `C₂ → Γ₂` sending the generator to `R₀`. -/
def toC2 : Multiplicative (ZMod 2) →* Gamma2G where
  toFun x := if x = 1 then 1 else r0
  map_one' := by simp
  map_mul' := by
    unfold r0 R0 Gamma2G
    decide +kernel

theorem toC2_injective : Function.Injective toC2 := by
  intro x y h
  revert x y
  unfold toC2 r0 R0 Gamma2G
  decide +kernel

theorem toC2_range : toC2.range = Gamma2Factor 1 := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change toC2 x ∈ Subgroup.closure ({r0} : Set Gamma2G)
    by_cases hx : x = 1
    · change (if x = 1 then 1 else r0) ∈ _
      rw [ite_eq_left hx]
      exact Subgroup.one_mem _
    · change (if x = 1 then 1 else r0) ∈ _
      rw [ite_eq_right hx]
      exact Subgroup.subset_closure (by simp)
  · change Subgroup.closure ({r0} : Set Gamma2G) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨Multiplicative.ofAdd 1, by unfold toC2 r0 R0 Gamma2G; decide +kernel⟩

/-- `⟨R₀⟩ ≅ C₂`. -/
def factor1Equiv : Multiplicative (ZMod 2) ≃* ↥(Gamma2Factor 1) :=
  (MonoidHom.ofInjective toC2_injective).trans (MulEquiv.subgroupCongr toC2_range)


/-- The two factors `𝔖₃` and `C₂`. -/
def Fac : Fin 2 → Type := ![Equiv.Perm (Fin 3), Multiplicative (ZMod 2)]

instance instGroupFac : ∀ i, Group (Fac i)
  | 0 => inferInstanceAs (Group (Equiv.Perm (Fin 3)))
  | 1 => inferInstanceAs (Group (Multiplicative (ZMod 2)))

/-- The identification of the factors with the subgroups `⟨A₀, B₀⟩` and `⟨R₀⟩` of `Γ₂`. -/
def facEquiv : ∀ i, Fac i ≃* ↥(Gamma2Factor i)
  | 0 => factor0Equiv
  | 1 => factor1Equiv

/-- The free product of the subgroups. -/
abbrev SubFreeProduct : Type := Monoid.CoprodI (fun i : Fin 2 => ↥(Gamma2Factor i))

/-- The free product `𝔖₃ * C₂`. -/
abbrev S3C2 : Type := Monoid.CoprodI Fac

/-- `𝔖₃ * C₂ ≅ ⟨A₀, B₀⟩ * ⟨R₀⟩`. -/
def freeProductCongr : S3C2 ≃* SubFreeProduct :=
  MonoidHom.toMulEquiv
    (Monoid.CoprodI.lift fun i => (Monoid.CoprodI.of (M := fun i : Fin 2 => ↥(Gamma2Factor i))
      (i := i)).comp (facEquiv i).toMonoidHom)
    (Monoid.CoprodI.lift fun i => (Monoid.CoprodI.of (M := Fac) (i := i)).comp
      (facEquiv i).symm.toMonoidHom)
    (by
      apply Monoid.CoprodI.ext_hom
      intro i
      ext x
      simp)
    (by
      apply Monoid.CoprodI.ext_hom
      intro i
      ext x
      simp)

/-- The free product map `⟨A₀, B₀⟩ * ⟨R₀⟩ → Γ₂`, as an isomorphism. -/
def freeProductToGamma2 : SubFreeProduct ≃* Gamma2G :=
  MulEquiv.ofBijective _ lift_bijective

end TernaryPeriodPolynomials.Argument.FiberModel
