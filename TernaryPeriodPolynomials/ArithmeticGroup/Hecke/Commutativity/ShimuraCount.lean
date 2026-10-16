module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Gelfand's trick for Hecke coset counts

Let `H ≤ G` and let `ι : G → G` be an involutive anti-automorphism with `ι H = H` and
`ι x ∈ H x H` for all `x`. Then the Hecke structure constants
`m(a,b;c) = #{xH : x ∈ HaH, x⁻¹c ∈ HbH}` are symmetric in `a, b`. Only bijections
of coset sets are used. No finiteness or measure theory is needed (`Nat.card`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

namespace TernaryPeriodPolynomials.HeckeCommutativity

variable {G : Type*} [Group G] (H : Subgroup G)

/-- The double coset `H a H` as a set. -/
def dcoset (a : G) : Set G := {y | ∃ h₁ ∈ H, ∃ h₂ ∈ H, y = h₁ * a * h₂}

theorem mem_dcoset_mul_right {a y : G} (hy : y ∈ dcoset H a) {h : G} (hh : h ∈ H) :
    y * h ∈ dcoset H a := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hy
  exact ⟨h₁, hh₁, h₂ * h, H.mul_mem hh₂ hh, by group⟩

theorem mem_dcoset_mul_left {a y : G} (hy : y ∈ dcoset H a) {h : G} (hh : h ∈ H) :
    h * y ∈ dcoset H a := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hy
  exact ⟨h * h₁, H.mul_mem hh hh₁, h₂, hh₂, by group⟩

theorem self_mem_dcoset (a : G) : a ∈ dcoset H a := ⟨1, H.one_mem, 1, H.one_mem, by group⟩

/-- The set of left cosets `xH` with `x ∈ HaH` and `x⁻¹ c ∈ HbH`. -/
def cosetSet (a b c : G) : Set (G ⧸ H) :=
  {q | ∃ x : G, (x : G ⧸ H) = q ∧ x ∈ dcoset H a ∧ x⁻¹ * c ∈ dcoset H b}

/-- The Hecke structure constant `m(a, b; c)`. -/
noncomputable def heckeCount (a b c : G) : ℕ := Nat.card (cosetSet H a b c)

theorem mem_cosetSet_iff {a b c x : G} :
    (x : G ⧸ H) ∈ cosetSet H a b c ↔ x ∈ dcoset H a ∧ x⁻¹ * c ∈ dcoset H b := by
  constructor
  · rintro ⟨y, hyx, hya, hyb⟩
    have hxy : y⁻¹ * x ∈ H := QuotientGroup.eq.mp hyx
    have hx : x = y * (y⁻¹ * x) := by group
    rw [hx]
    refine ⟨mem_dcoset_mul_right H hya hxy, ?_⟩
    have : (y * (y⁻¹ * x))⁻¹ * c = (y⁻¹ * x)⁻¹ * (y⁻¹ * c) := by group
    rw [this]
    exact mem_dcoset_mul_left H hyb (H.inv_mem hxy)
  · rintro ⟨hxa, hxb⟩
    exact ⟨x, rfl, hxa, hxb⟩

section Involution

variable (ι : G → G) (hmul : ∀ x y, ι (x * y) = ι y * ι x) (hinvol : ∀ x, ι (ι x) = x)
  (hH : ∀ h ∈ H, ι h ∈ H)

include hmul in
theorem ι_one : ι 1 = 1 := by
  have h2 : ι (1 * 1) = ι 1 * ι 1 := hmul 1 1
  rw [one_mul] at h2
  exact mul_left_cancel (h2.symm.trans (mul_one _).symm)

include hmul in
theorem ι_inv (x : G) : ι x⁻¹ = (ι x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hmul, mul_inv_cancel, ι_one ι hmul]

include hmul hH in
theorem ι_dcoset {a y : G} (hy : y ∈ dcoset H a) : ι y ∈ dcoset H (ι a) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hy
  exact ⟨ι h₂, hH _ hh₂, ι h₁, hH _ hh₁, by rw [hmul, hmul, mul_assoc]⟩

include hmul hH in
theorem ι_mem_dcoset_of {a y : G} (hda : ι a ∈ dcoset H a) (hy : y ∈ dcoset H a) :
    ι y ∈ dcoset H a := by
  have h1 := ι_dcoset H ι hmul hH hy
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := hda
  obtain ⟨h₁, hh₁, h₂, hh₂, hh⟩ := h1
  exact ⟨h₁ * k₁, H.mul_mem hh₁ hk₁, k₂ * h₂, H.mul_mem hk₂ hh₂, by rw [hh, hk]; group⟩

include hmul hinvol hH in
/-- The coset map `xH ↦ ι(x⁻¹ c) H`. -/
theorem heckeCount_swap (a b c : G) (hda : ι a ∈ dcoset H a) (hdb : ι b ∈ dcoset H b) :
    heckeCount H a b c = heckeCount H b a (ι c) := by
  let f : G → G := fun x => ι (x⁻¹ * c)
  have hf : ∀ x y : G, x⁻¹ * y ∈ H → (f x)⁻¹ * f y ∈ H := by
    intro x y hxy
    have : (f x)⁻¹ * f y = ι (y⁻¹ * x) := by
      simp only [f]
      rw [← ι_inv ι hmul, ← hmul]
      congr 1
      group
    rw [this]
    have : y⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
    rw [this]
    exact hH _ (H.inv_mem hxy)
  let g : G → G := fun z => ι (z⁻¹ * ι c)
  have hg : ∀ x y : G, x⁻¹ * y ∈ H → (g x)⁻¹ * g y ∈ H := by
    intro x y hxy
    have : (g x)⁻¹ * g y = ι (y⁻¹ * x) := by
      simp only [g]
      rw [← ι_inv ι hmul, ← hmul]
      congr 1
      group
    rw [this]
    have : y⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
    rw [this]
    exact hH _ (H.inv_mem hxy)
  have hgf : ∀ x, g (f x) = x := by
    intro x
    have e : (f x)⁻¹ * ι c = ι x := by
      simp only [f]
      rw [← ι_inv ι hmul, ← hmul]
      congr 1
      group
    simp only [g]
    rw [e, hinvol]
  have hfg : ∀ z, f (g z) = z := by
    intro z
    have e : (g z)⁻¹ * c = ι z := by
      simp only [g]
      calc (ι (z⁻¹ * ι c))⁻¹ * c = ι ((z⁻¹ * ι c)⁻¹) * ι (ι c) := by
            rw [ι_inv ι hmul, hinvol]
        _ = ι (ι c * (z⁻¹ * ι c)⁻¹) := by rw [hmul]
        _ = ι z := by congr 1; group
    simp only [f]
    rw [e, hinvol]
  let F : G ⧸ H → G ⧸ H := Quotient.map' f (fun x y hxy => by
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hf x y hxy)
  let Gm : G ⧸ H → G ⧸ H := Quotient.map' g (fun x y hxy => by
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hg x y hxy)
  have hF : ∀ x : G, F (x : G ⧸ H) = (f x : G ⧸ H) := fun x => rfl
  have hG : ∀ z : G, Gm (z : G ⧸ H) = (g z : G ⧸ H) := fun z => rfl
  have hmapsF : ∀ q ∈ cosetSet H a b c, F q ∈ cosetSet H b a (ι c) := by
    rintro q ⟨x, rfl, hxa, hxb⟩
    rw [hF, mem_cosetSet_iff]
    refine ⟨ι_mem_dcoset_of H ι hmul hH hdb hxb, ?_⟩
    have : (f x)⁻¹ * ι c = ι x := by
      simp only [f]
      rw [← ι_inv ι hmul, ← hmul]
      congr 1
      group
    rw [this]
    exact ι_mem_dcoset_of H ι hmul hH hda hxa
  have hmapsG : ∀ q ∈ cosetSet H b a (ι c), Gm q ∈ cosetSet H a b c := by
    rintro q ⟨z, rfl, hzb, hza⟩
    rw [hG, mem_cosetSet_iff]
    refine ⟨ι_mem_dcoset_of H ι hmul hH hda hza, ?_⟩
    have : (g z)⁻¹ * c = ι z := by
      simp only [g]
      calc (ι (z⁻¹ * ι c))⁻¹ * c = ι ((z⁻¹ * ι c)⁻¹) * ι (ι c) := by
            rw [ι_inv ι hmul, hinvol]
        _ = ι (ι c * (z⁻¹ * ι c)⁻¹) := by rw [hmul]
        _ = ι z := by congr 1; group
    rw [this]
    exact ι_mem_dcoset_of H ι hmul hH hdb hzb
  have hGF : ∀ q, Gm (F q) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => rw [hF, hG, hgf]
  have hFG : ∀ q, F (Gm q) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H z => rw [hG, hF, hfg]
  unfold heckeCount
  apply Nat.card_congr
  exact {
    toFun := fun q => ⟨F q.1, hmapsF q.1 q.2⟩
    invFun := fun q => ⟨Gm q.1, hmapsG q.1 q.2⟩
    left_inv := fun q => Subtype.ext (hGF q.1)
    right_inv := fun q => Subtype.ext (hFG q.1) }

end Involution

/-- `m(a, b; ·)` is invariant under left multiplication by `H`. -/
theorem heckeCount_left (a b c : G) {h : G} (hh : h ∈ H) :
    heckeCount H a b (h * c) = heckeCount H a b c := by
  unfold heckeCount
  apply Nat.card_congr
  refine {
    toFun := fun q => ⟨h⁻¹ • q.1, ?_⟩
    invFun := fun q => ⟨h • q.1, ?_⟩
    left_inv := fun q => Subtype.ext (by simp)
    right_inv := fun q => Subtype.ext (by simp) }
  · obtain ⟨x, hx, hxa, hxb⟩ := q.2
    refine ⟨h⁻¹ * x, ?_, mem_dcoset_mul_left H hxa (H.inv_mem hh), ?_⟩
    · rw [← hx]; rfl
    · have : (h⁻¹ * x)⁻¹ * c = x⁻¹ * (h * c) := by group
      rw [this]; exact hxb
  · obtain ⟨x, hx, hxa, hxb⟩ := q.2
    refine ⟨h * x, ?_, mem_dcoset_mul_left H hxa hh, ?_⟩
    · rw [← hx]; rfl
    · have : (h * x)⁻¹ * (h * c) = x⁻¹ * c := by group
      rw [this]; exact hxb

/-- `m(a, b; ·)` is invariant under right multiplication by `H`. -/
theorem heckeCount_right (a b c : G) {h : G} (hh : h ∈ H) :
    heckeCount H a b (c * h) = heckeCount H a b c := by
  unfold heckeCount
  have hset : cosetSet H a b (c * h) = cosetSet H a b c := by
    ext q
    constructor
    · rintro ⟨x, hx, hxa, hxb⟩
      refine ⟨x, hx, hxa, ?_⟩
      have := mem_dcoset_mul_right H hxb (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rintro ⟨x, hx, hxa, hxb⟩
      refine ⟨x, hx, hxa, ?_⟩
      have := mem_dcoset_mul_right H hxb hh
      simpa [mul_assoc] using this
  rw [hset]

/-- **Gelfand's trick.** The Hecke structure constants are symmetric. -/
theorem heckeCount_comm (ι : G → G) (hmul : ∀ x y, ι (x * y) = ι y * ι x)
    (hinvol : ∀ x, ι (ι x) = x) (hH : ∀ h ∈ H, ι h ∈ H) (a b c : G)
    (hda : ι a ∈ dcoset H a) (hdb : ι b ∈ dcoset H b) (hdc : ι c ∈ dcoset H c) :
    heckeCount H a b c = heckeCount H b a c := by
  rw [heckeCount_swap H ι hmul hinvol hH a b c hda hdb]
  obtain ⟨h₁, hh₁, h₂, hh₂, hc⟩ := hdc
  rw [hc, heckeCount_right H _ _ _ hh₂, heckeCount_left H _ _ _ hh₁]

end TernaryPeriodPolynomials.HeckeCommutativity
