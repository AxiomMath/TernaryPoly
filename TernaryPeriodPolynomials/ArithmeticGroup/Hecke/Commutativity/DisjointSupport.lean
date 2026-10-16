module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.LocalGlobal
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.Commutation

@[expose] public section


/-!
# Hecke operators with disjoint local supports commute

If at every finite place at least one of `a, b` lies in the local level, then
`Γ a Γ · Γ b Γ = Γ a b Γ = Γ b a Γ` with every coset of `Γ a b Γ` represented
exactly once.  Consequently the Hecke structure constants are
`m(a, b; c) = m(b, a; c) = [c ∈ Γ a b Γ]`, and any realized Hecke action
satisfies `T s ∘ T t = T t ∘ T s` for such `s, t`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.HeckeCommutativity

/-- At every place one of the two matrices is in the local level. -/
def DisjointSupport (a b : RationalGL3) : Prop := ∀ v, LocK a v ∨ LocK b v

theorem DisjointSupport.symm {a b : RationalGL3} (h : DisjointSupport a b) :
    DisjointSupport b a := fun v => (h v).symm

theorem mul_mem_dcoset_mul (a b γ : RationalGL3) (hab : DisjointSupport a b)
    (hγ : γ ∈ rationalLevel) : a * γ * b ∈ dcoset rationalLevel (a * b) := by
  classical
  refine mem_dcoset_of_local (fun v => if LocK a v then a * γ * a⁻¹ else 1)
    (fun v => if LocK a v then 1 else b⁻¹ * γ * b) (fun v => ?_) (fun v => ?_) (fun v => ?_)
  · by_cases ha : LocK a v
    · simp only [ha, ite_true]
      exact locK_mul (locK_mul ha (locK_of_mem hγ v)) (locK_inv ha)
    · simp only [ha, ite_false]
      exact locK_one v
  · by_cases ha : LocK a v
    · simp only [ha, ite_true]
      exact locK_one v
    · simp only [ha, ite_false]
      have hb := (hab v).resolve_left ha
      exact locK_mul (locK_mul (locK_inv hb) (locK_of_mem hγ v)) hb
  · by_cases ha : LocK a v
    · simp only [ha, ite_true]
      group
    · simp only [ha, ite_false]
      group

theorem mem_dcoset_trans {x y z : RationalGL3} (hxy : x ∈ dcoset rationalLevel y)
    (hyz : y ∈ dcoset rationalLevel z) : x ∈ dcoset rationalLevel z := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hxy
  exact mem_dcoset_mul_right _ (mem_dcoset_mul_left _ hyz hh₁) hh₂

theorem mul_mem_dcoset_of_disjoint {a b x y : RationalGL3} (hab : DisjointSupport a b)
    (hx : x ∈ dcoset rationalLevel a) (hy : y ∈ dcoset rationalLevel b) :
    x * y ∈ dcoset rationalLevel (a * b) := by
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := hx
  obtain ⟨γ₃, hγ₃, γ₄, hγ₄, rfl⟩ := hy
  have h := mul_mem_dcoset_mul a b (γ₂ * γ₃) hab (mul_mem hγ₂ hγ₃)
  have e : γ₁ * a * γ₂ * (γ₃ * b * γ₄) = γ₁ * (a * (γ₂ * γ₃) * b) * γ₄ := by group
  rw [e]
  exact mem_dcoset_mul_right _ (mem_dcoset_mul_left _ h hγ₁) hγ₄

theorem swap_mem_dcoset (a b : RationalGL3) (hab : DisjointSupport a b) :
    a * b ∈ dcoset rationalLevel (b * a) := by
  classical
  refine mem_dcoset_of_local (fun v => if LocK b v then b⁻¹ else a)
    (fun v => if LocK b v then b else a⁻¹) (fun v => ?_) (fun v => ?_) (fun v => ?_)
  · by_cases hb : LocK b v
    · simp only [hb, ite_true]
      exact locK_inv hb
    · simp only [hb, ite_false]
      exact (hab v).resolve_right hb
  · by_cases hb : LocK b v
    · simp only [hb, ite_true]
    · simp only [hb, ite_false]
      exact locK_inv ((hab v).resolve_right hb)
  · by_cases hb : LocK b v
    · simp only [hb, ite_true]
      group
    · simp only [hb, ite_false]
      group

theorem inv_mul_mem_of_disjoint {a b x₁ x₂ y₁ y₂ : RationalGL3} (hab : DisjointSupport a b)
    (hx₁ : x₁ ∈ dcoset rationalLevel a) (hx₂ : x₂ ∈ dcoset rationalLevel a)
    (hy₁ : y₁ ∈ dcoset rationalLevel b) (hy₂ : y₂ ∈ dcoset rationalLevel b)
    (h : x₁ * y₁ = x₂ * y₂) : x₁⁻¹ * x₂ ∈ rationalLevel := by
  apply mem_rationalLevel_of_locK
  intro v
  rcases hab v with ha | hb
  · exact locK_mul (locK_inv (locK_of_dcoset hx₁ ha)) (locK_of_dcoset hx₂ ha)
  · have e : x₁⁻¹ * x₂ = y₁ * y₂⁻¹ := by
      have : x₂ = x₁ * y₁ * y₂⁻¹ := by rw [h]; group
      rw [this]; group
    rw [e]
    exact locK_mul (locK_of_dcoset hy₁ hb) (locK_inv (locK_of_dcoset hy₂ hb))

/-- The structure constant for disjoint supports. -/
theorem heckeCount_eq_of_disjoint {a b : RationalGL3} (hab : DisjointSupport a b)
    (c : RationalGL3) [Decidable (c ∈ dcoset rationalLevel (a * b))] :
    heckeCount rationalLevel a b c = if c ∈ dcoset rationalLevel (a * b) then 1 else 0 := by
  unfold heckeCount
  split_ifs with hc
  · rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨?_⟩, ?_⟩
    · rintro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
      induction q₁ using QuotientGroup.induction_on with
      | H x₁ =>
      induction q₂ using QuotientGroup.induction_on with
      | H x₂ =>
      rw [mem_cosetSet_iff] at hq₁ hq₂
      apply Subtype.ext
      apply QuotientGroup.eq.mpr
      exact inv_mul_mem_of_disjoint hab hq₁.1 hq₂.1 hq₁.2 hq₂.2 (by group)
    · obtain ⟨γ, hγ, γ', hγ', rfl⟩ := hc
      refine ⟨⟨((γ * a : RationalGL3) : RationalGL3 ⧸ rationalLevel), ?_⟩⟩
      rw [mem_cosetSet_iff]
      refine ⟨⟨γ, hγ, 1, one_mem _, by group⟩, ⟨1, one_mem _, γ', hγ', by group⟩⟩
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H x =>
    rw [mem_cosetSet_iff] at hq
    apply hc
    have e : c = x * (x⁻¹ * c) := by group
    rw [e]
    exact mul_mem_dcoset_of_disjoint hab hq.1 hq.2

theorem heckeCount_comm_of_disjoint {a b : RationalGL3} (hab : DisjointSupport a b)
    (c : RationalGL3) : heckeCount rationalLevel a b c = heckeCount rationalLevel b a c := by
  classical
  rw [heckeCount_eq_of_disjoint hab, heckeCount_eq_of_disjoint hab.symm]
  have hiff : c ∈ dcoset rationalLevel (a * b) ↔ c ∈ dcoset rationalLevel (b * a) :=
    ⟨fun h => mem_dcoset_trans h (swap_mem_dcoset a b hab),
     fun h => mem_dcoset_trans h (swap_mem_dcoset b a hab.symm)⟩
  by_cases h : c ∈ dcoset rationalLevel (a * b)
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

/-- **Realized Hecke operators with disjoint local supports commute.** -/
theorem realizesHecke_comm_of_disjoint {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V)
    (T : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel ρ)) (hT : RealizesHecke ρ T)
    {s t : HeckeCorrespondence} (hst : DisjointSupport s.g t.g) :
    T s * T t = T t * T s :=
  realizesHecke_comm_of_count ρ T hT (heckeCount_comm_of_disjoint hst)

end TernaryPeriodPolynomials.HeckeCommutativity
