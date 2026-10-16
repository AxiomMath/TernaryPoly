module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.TwoGenerator
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Restriction

@[expose] public section


/-!
# Splitting the cohomology of an index-two subgroup by the two twists

Let `H ≤ G` have index two, `G = H ⊔ H ε` with an involution `ε ∉ H` normalizing `H`, and let
`ρ₁, ρ₂` be representations of `G` that agree on `H` and satisfy `ρ₂ ε = -ρ₁ ε` (e.g. `Sym^m ⊗ det^e`
and `Sym^m ⊗ det^{e+1}` on `Γ₁'(3) ⊇ Γ₁(3)`). Conjugation by `ε` is an involution `ι` of the
cocycles of `H`; `ι`-invariant cocycles extend to `ρ₁`-cocycles of `G` and `ι`-anti-invariant ones to
`ρ₂`-cocycles (`extendCocycle`). Hence

* `finrank_H1_le_add`: `dim H¹(H) ≤ dim H¹(G, ρ₁) + dim H¹(G, ρ₂)`;
* `finrank_parabolicH1_le_add`: the same for the classes trivial on `⟨T⟩`, `⟨L⟩` (`T, L ∈ H`
  inverted by `ε`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.TwistSplitting

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TwoGenerator Module

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable {H : Subgroup G} {ε : G}

section Conjugation

/-- Conjugation by `ε` on `H`. -/
def conjH (normal : ∀ k ∈ H, ε * k * ε ∈ H) (k : H) : H := ⟨ε * k * ε, normal k k.property⟩

theorem conjH_mul (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H) (k₁ k₂ : H) :
    conjH normal (k₁ * k₂) = conjH normal k₁ * conjH normal k₂ := by
  apply Subtype.ext
  change ε * (k₁.val * k₂.val) * ε = ε * k₁.val * ε * (ε * k₂.val * ε)
  calc ε * (k₁.val * k₂.val) * ε = ε * k₁.val * 1 * k₂.val * ε := by group
    _ = ε * k₁.val * ε * (ε * k₂.val * ε) := by rw [← hεε]; group

/-- `ε ∘ (εkε) = k ∘ ε` on `V`. -/
theorem rho_conj (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (ρ : Representation ℂ G V) (k : H) (w : V) :
    ρ ε (ρ (conjH normal k).val w) = ρ k.val (ρ ε w) := by
  change ρ ε (ρ (ε * k.val * ε) w) = _
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  calc ε * (ε * k.val * ε) = (ε * ε) * k.val * ε := by group
    _ = k.val * ε := by rw [hεε, one_mul]

/-- The involution `ι z (k) = ε · z(ε k ε)` on cocycles of `H`. -/
def conjCocycle (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (ρ : Representation ℂ G V) :
    crossedCocycles (ρ.comp H.subtype) →ₗ[ℂ] crossedCocycles (ρ.comp H.subtype) where
  toFun z := ⟨fun k => ρ ε (z.val (conjH normal k)), by
    intro k₁ k₂
    change ρ ε (z.val (conjH normal (k₁ * k₂))) =
      ρ ε (z.val (conjH normal k₁)) + ρ k₁.val (ρ ε (z.val (conjH normal k₂)))
    rw [conjH_mul hεε normal, cocycle_mul, map_add]
    congr 1
    exact rho_conj hεε normal ρ k₁ _⟩
  map_add' z w := by
    apply Subtype.ext
    funext k
    exact map_add _ _ _
  map_smul' c z := by
    apply Subtype.ext
    funext k
    exact map_smul _ _ _

theorem conjCocycle_apply (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (ρ : Representation ℂ G V) (z : crossedCocycles (ρ.comp H.subtype)) (k : H) :
    (conjCocycle hεε normal ρ z).val k = ρ ε (z.val (conjH normal k)) := rfl

theorem conjH_conjH (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H) (k : H) :
    conjH normal (conjH normal k) = k := by
  apply Subtype.ext
  change ε * (ε * k.val * ε) * ε = k.val
  calc ε * (ε * k.val * ε) * ε = (ε * ε) * k.val * (ε * ε) := by group
    _ = k.val := by rw [hεε, one_mul, mul_one]

end Conjugation

section Extension

variable (cover : ∀ g : G, g ∈ H ∨ g * ε ∈ H)

variable (ρ ρ' : Representation ℂ G V)

open Classical in
/-- The function extending a cocycle of `H` to `G`: `g ↦ z(g)` on `H`, `g ↦ z(gε)` off `H`. -/
def extendFun (z : crossedCocycles (ρ.comp H.subtype)) (g : G) : V :=
  if h : g ∈ H then z.val ⟨g, h⟩ else z.val ⟨g * ε, (cover g).resolve_left h⟩

theorem extendFun_mem (z : crossedCocycles (ρ.comp H.subtype)) {g : G} (h : g ∈ H) :
    extendFun cover ρ z g = z.val ⟨g, h⟩ := by
  classical
  unfold extendFun
  rw [dite_eq_left h]

theorem extendFun_not_mem (z : crossedCocycles (ρ.comp H.subtype)) {g : G} (h : g ∉ H) :
    extendFun cover ρ z g = z.val ⟨g * ε, (cover g).resolve_left h⟩ := by
  classical
  unfold extendFun
  rw [dite_eq_right h]

/-- **Extension**: a cocycle of `H` with `z(εkε) = ρ'(ε) z(k)` extends to a `ρ'`-cocycle of `G`. -/
def extendCocycle (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (agree : ∀ k : H, ρ' k.val = ρ k.val) (z : crossedCocycles (ρ.comp H.subtype))
    (hz : ∀ k : H, z.val (conjH normal k) = ρ' ε (z.val k)) : crossedCocycles ρ' :=
  ⟨extendFun cover ρ z, by
    -- cocycle relation in `ρ` on `H`, rewritten through `agree`
    have zmul : ∀ (k₁ k₂ : H), z.val (k₁ * k₂) = z.val k₁ + ρ' k₁.val (z.val k₂) := by
      intro k₁ k₂
      rw [agree]
      exact z.property k₁ k₂
    have hεε' : ∀ v : V, ρ' ε (ρ' ε v) = v := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, hεε, map_one, Module.End.one_apply]
    intro g₁ g₂
    by_cases h₁ : g₁ ∈ H <;> by_cases h₂ : g₂ ∈ H
    · rw [extendFun_mem cover ρ z (H.mul_mem h₁ h₂), extendFun_mem cover ρ z h₁,
        extendFun_mem cover ρ z h₂]
      exact zmul ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    · have h₁₂ : g₁ * g₂ ∉ H := by
        intro h
        apply h₂
        have := H.mul_mem (H.inv_mem h₁) h
        rwa [inv_mul_cancel_left] at this
      rw [extendFun_not_mem cover ρ z h₁₂, extendFun_mem cover ρ z h₁,
        extendFun_not_mem cover ρ z h₂]
      have key := zmul ⟨g₁, h₁⟩ ⟨g₂ * ε, (cover g₂).resolve_left h₂⟩
      have e : (⟨g₁ * g₂ * ε, (cover _).resolve_left h₁₂⟩ : H) =
          ⟨g₁, h₁⟩ * ⟨g₂ * ε, (cover g₂).resolve_left h₂⟩ := by
        apply Subtype.ext
        change g₁ * g₂ * ε = g₁ * (g₂ * ε)
        group
      rw [e]
      exact key
    · have h₁₂ : g₁ * g₂ ∉ H := by
        intro h
        apply h₁
        have := H.mul_mem h (H.inv_mem h₂)
        rwa [mul_inv_cancel_right] at this
      rw [extendFun_not_mem cover ρ z h₁₂, extendFun_not_mem cover ρ z h₁,
        extendFun_mem cover ρ z h₂]
      have hk : g₁ * ε ∈ H := (cover g₁).resolve_left h₁
      have key := zmul ⟨g₁ * ε, hk⟩ (conjH normal ⟨g₂, h₂⟩)
      have e : (⟨g₁ * g₂ * ε, (cover _).resolve_left h₁₂⟩ : H) =
          ⟨g₁ * ε, hk⟩ * conjH normal ⟨g₂, h₂⟩ := by
        apply Subtype.ext
        change g₁ * g₂ * ε = g₁ * ε * (ε * g₂ * ε)
        calc g₁ * g₂ * ε = g₁ * 1 * g₂ * ε := by rw [mul_one]
          _ = g₁ * ε * (ε * g₂ * ε) := by rw [← hεε]; group
      rw [e, key, hz]
      congr 1
      change ρ' (g₁ * ε) (ρ' ε (z.val ⟨g₂, h₂⟩)) = _
      rw [map_mul, Module.End.mul_apply, hεε']
    · have h₁₂ : g₁ * g₂ ∈ H := by
        have hk₁ : g₁ * ε ∈ H := (cover g₁).resolve_left h₁
        have hk₂ : g₂ * ε ∈ H := (cover g₂).resolve_left h₂
        have := H.mul_mem hk₁ (normal _ hk₂)
        have e : g₁ * ε * (ε * (g₂ * ε) * ε) = g₁ * g₂ := by
          calc g₁ * ε * (ε * (g₂ * ε) * ε) = g₁ * (ε * ε) * g₂ * (ε * ε) := by group
            _ = g₁ * g₂ := by rw [hεε, mul_one, mul_one]
        rwa [e] at this
      rw [extendFun_mem cover ρ z h₁₂, extendFun_not_mem cover ρ z h₁,
        extendFun_not_mem cover ρ z h₂]
      have hk₁ : g₁ * ε ∈ H := (cover g₁).resolve_left h₁
      have hk₂ : g₂ * ε ∈ H := (cover g₂).resolve_left h₂
      have key := zmul ⟨g₁ * ε, hk₁⟩ (conjH normal ⟨g₂ * ε, hk₂⟩)
      have e : (⟨g₁ * g₂, h₁₂⟩ : H) = ⟨g₁ * ε, hk₁⟩ * conjH normal ⟨g₂ * ε, hk₂⟩ := by
        apply Subtype.ext
        change g₁ * g₂ = g₁ * ε * (ε * (g₂ * ε) * ε)
        calc g₁ * g₂ = g₁ * (ε * ε) * g₂ * (ε * ε) := by rw [hεε, mul_one, mul_one]
          _ = g₁ * ε * (ε * (g₂ * ε) * ε) := by group
      rw [e, key, hz]
      congr 1
      change ρ' (g₁ * ε) (ρ' ε (z.val ⟨g₂ * ε, hk₂⟩)) = _
      rw [map_mul, Module.End.mul_apply, hεε']⟩

theorem extendCocycle_mem (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (agree : ∀ k : H, ρ' k.val = ρ k.val) (z : crossedCocycles (ρ.comp H.subtype))
    (hz : ∀ k : H, z.val (conjH normal k) = ρ' ε (z.val k)) (k : H) :
    (extendCocycle cover ρ ρ' hεε normal agree z hz).val k.val = z.val k :=
  extendFun_mem cover ρ z k.property

end Extension

section Dimension

variable (ρ₁ ρ₂ : Representation ℂ G V)

/-- Restriction of `ρ₂`-cocycles to `H`, read as `ρ₁|H`-cocycles. -/
def twistedRestriction (agree : ∀ k : H, ρ₂ k.val = ρ₁ k.val) :
    crossedCocycles ρ₂ →ₗ[ℂ] crossedCocycles (ρ₁.comp H.subtype) where
  toFun z := ⟨fun k => z.val k.val, by
    intro k₁ k₂
    change z.val (k₁.val * k₂.val) = z.val k₁.val + ρ₁ k₁.val (z.val k₂.val)
    rw [cocycle_mul, agree]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The induced map on `H¹`. -/
def twistedRestrictionH1 (agree : ∀ k : H, ρ₂ k.val = ρ₁ k.val) :
    CrossedH1 ρ₂ →ₗ[ℂ] CrossedH1 (ρ₁.comp H.subtype) :=
  (crossedBoundaries ρ₂).mapQ (crossedBoundaries (ρ₁.comp H.subtype))
    (twistedRestriction ρ₁ ρ₂ agree) (by
      rintro _ ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      apply Subtype.ext
      funext k
      change ρ₁ k.val v - v = ρ₂ k.val v - v
      rw [agree])

/-- Restriction on both twists, summed. -/
def splitMap (agree : ∀ k : H, ρ₂ k.val = ρ₁ k.val) :
    CrossedH1 ρ₁ × CrossedH1 ρ₂ →ₗ[ℂ] CrossedH1 (ρ₁.comp H.subtype) :=
  (crossedPullbackH1 H.subtype ρ₁).coprod (twistedRestrictionH1 ρ₁ ρ₂ agree)

/-- The `ι`-symmetric part `(z + ι z)/2`. -/
def plusPart (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (z : crossedCocycles (ρ₁.comp H.subtype)) : crossedCocycles (ρ₁.comp H.subtype) :=
  (2 : ℂ)⁻¹ • (z + conjCocycle hεε normal ρ₁ z)

/-- The `ι`-antisymmetric part `(z - ι z)/2`. -/
def minusPart (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (z : crossedCocycles (ρ₁.comp H.subtype)) : crossedCocycles (ρ₁.comp H.subtype) :=
  (2 : ℂ)⁻¹ • (z - conjCocycle hεε normal ρ₁ z)

theorem rho_eps_eps (hεε : ε * ε = 1) (w : V) : ρ₁ ε (ρ₁ ε w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, hεε, map_one, Module.End.one_apply]

theorem plusPart_conj (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (z : crossedCocycles (ρ₁.comp H.subtype)) (k : H) :
    (plusPart ρ₁ hεε normal z).val (conjH normal k) =
      ρ₁ ε ((plusPart ρ₁ hεε normal z).val k) := by
  change (2 : ℂ)⁻¹ • (z.val (conjH normal k) + ρ₁ ε (z.val (conjH normal (conjH normal k)))) =
    ρ₁ ε ((2 : ℂ)⁻¹ • (z.val k + ρ₁ ε (z.val (conjH normal k))))
  rw [conjH_conjH hεε normal, map_smul, map_add, rho_eps_eps ρ₁ hεε, add_comm (z.val _)]

theorem minusPart_conj (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (anti : ρ₂ ε = -(ρ₁ ε)) (z : crossedCocycles (ρ₁.comp H.subtype)) (k : H) :
    (minusPart ρ₁ hεε normal z).val (conjH normal k) =
      ρ₂ ε ((minusPart ρ₁ hεε normal z).val k) := by
  change (2 : ℂ)⁻¹ • (z.val (conjH normal k) - ρ₁ ε (z.val (conjH normal (conjH normal k)))) =
    ρ₂ ε ((2 : ℂ)⁻¹ • (z.val k - ρ₁ ε (z.val (conjH normal k))))
  rw [conjH_conjH hεε normal, anti, LinearMap.neg_apply, map_smul, map_sub,
    rho_eps_eps ρ₁ hεε, smul_sub, smul_sub, neg_sub]

theorem plus_add_minus (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (z : crossedCocycles (ρ₁.comp H.subtype)) :
    plusPart ρ₁ hεε normal z + minusPart ρ₁ hεε normal z = z := by
  unfold plusPart minusPart
  rw [← smul_add]
  rw [show z + conjCocycle hεε normal ρ₁ z + (z - conjCocycle hεε normal ρ₁ z) = (2 : ℂ) • z by
    rw [two_smul]; abel]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

theorem splitMap_surjective (cover : ∀ g : G, g ∈ H ∨ g * ε ∈ H) (hεε : ε * ε = 1)
    (normal : ∀ k ∈ H, ε * k * ε ∈ H) (agree : ∀ k : H, ρ₂ k.val = ρ₁ k.val)
    (anti : ρ₂ ε = -(ρ₁ ε)) : Function.Surjective (splitMap ρ₁ ρ₂ agree) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let plus := extendCocycle cover ρ₁ ρ₁ hεε normal (fun _ => rfl) (plusPart ρ₁ hεε normal z)
    (plusPart_conj ρ₁ hεε normal z)
  let minus := extendCocycle cover ρ₁ ρ₂ hεε normal agree (minusPart ρ₁ hεε normal z)
    (minusPart_conj ρ₁ ρ₂ hεε normal anti z)
  refine ⟨((crossedBoundaries ρ₁).mkQ plus, (crossedBoundaries ρ₂).mkQ minus), ?_⟩
  change crossedPullbackH1 H.subtype ρ₁ ((crossedBoundaries ρ₁).mkQ plus) +
    twistedRestrictionH1 ρ₁ ρ₂ agree ((crossedBoundaries ρ₂).mkQ minus) = _
  rw [crossedPullbackH1_mk]
  change (crossedBoundaries (ρ₁.comp H.subtype)).mkQ (crossedPullbackCocycles H.subtype ρ₁ plus) +
    (crossedBoundaries (ρ₁.comp H.subtype)).mkQ (twistedRestriction ρ₁ ρ₂ agree minus) =
      (crossedBoundaries (ρ₁.comp H.subtype)).mkQ z
  rw [← map_add]
  congr 1
  conv_rhs => rw [← plus_add_minus ρ₁ hεε normal z]
  congr 1
  · apply Subtype.ext
    funext k
    exact extendCocycle_mem cover ρ₁ ρ₁ hεε normal (fun _ => rfl) _
      (plusPart_conj ρ₁ hεε normal z) k
  · apply Subtype.ext
    funext k
    exact extendCocycle_mem cover ρ₁ ρ₂ hεε normal agree _
      (minusPart_conj ρ₁ ρ₂ hεε normal anti z) k

/-- **`dim H¹(H) ≤ dim H¹(G, ρ₁) + dim H¹(G, ρ₂)`**. -/
theorem finrank_H1_le_add [FiniteDimensional ℂ (CrossedH1 ρ₁)] [FiniteDimensional ℂ (CrossedH1 ρ₂)]
    (cover : ∀ g : G, g ∈ H ∨ g * ε ∈ H) (hεε : ε * ε = 1)
    (normal : ∀ k ∈ H, ε * k * ε ∈ H) (agree : ∀ k : H, ρ₂ k.val = ρ₁ k.val)
    (anti : ρ₂ ε = -(ρ₁ ε)) :
    finrank ℂ (CrossedH1 (ρ₁.comp H.subtype)) ≤
      finrank ℂ (CrossedH1 ρ₁) + finrank ℂ (CrossedH1 ρ₂) := by
  have h := LinearMap.finrank_range_le (splitMap ρ₁ ρ₂ agree)
  rw [LinearMap.range_eq_top.mpr (splitMap_surjective ρ₁ ρ₂ cover hεε normal agree anti),
    finrank_top, Module.finrank_prod] at h
  exact h

end Dimension

section ParabolicSplitting

variable (ρ₁ ρ₂ : Representation ℂ G V)

theorem conj_moved (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H) (k : G) (hk : k ∈ H)
    (hεk : ε * k * ε = k⁻¹) (z : crossedCocycles (ρ₁.comp H.subtype))
    (hz : z.val ⟨k, hk⟩ ∈ moved ρ₁ k) :
    (conjCocycle hεε normal ρ₁ z).val ⟨k, hk⟩ ∈ moved ρ₁ k := by
  obtain ⟨a, ha⟩ := hz
  rw [conjCocycle_apply]
  have hconj : conjH normal ⟨k, hk⟩ = ⟨k, hk⟩⁻¹ := by
    apply Subtype.ext
    exact hεk
  rw [hconj, cocycle_inv, ← ha]
  have e : ε * k⁻¹ = k * ε := by
    calc ε * k⁻¹ = ε * (ε * k * ε) := by rw [hεk]
      _ = (ε * ε) * k * ε := by group
      _ = k * ε := by rw [hεε, one_mul]
  refine ⟨ρ₁ ε a, ?_⟩
  change ρ₁ k (ρ₁ ε a) - ρ₁ ε a = ρ₁ ε (-(ρ₁ k⁻¹ ((ρ₁ k - 1) a)))
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_neg, map_sub, neg_sub,
    ← Module.End.mul_apply (ρ₁ ε) (ρ₁ k⁻¹), ← map_mul, e, map_mul, Module.End.mul_apply,
    ← Module.End.mul_apply (ρ₁ k⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem plusPart_parabolic (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (T L : G) (hT : T ∈ H) (hL : L ∈ H) (hεT : ε * T * ε = T⁻¹) (hεL : ε * L * ε = L⁻¹)
    (z : crossedCocycles (ρ₁.comp H.subtype)) (hz : z ∈ parabolicCocycles (ρ₁.comp H.subtype) ⟨T, hT⟩ ⟨L, hL⟩) :
    (plusPart ρ₁ hεε normal z).val ⟨T, hT⟩ ∈ moved ρ₁ T ∧
      (plusPart ρ₁ hεε normal z).val ⟨L, hL⟩ ∈ moved ρ₁ L :=
  ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hz.1 (conj_moved ρ₁ hεε normal T hT hεT z hz.1)),
    Submodule.smul_mem _ _ (Submodule.add_mem _ hz.2 (conj_moved ρ₁ hεε normal L hL hεL z hz.2))⟩

theorem minusPart_parabolic (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (T L : G) (hT : T ∈ H) (hL : L ∈ H) (hεT : ε * T * ε = T⁻¹) (hεL : ε * L * ε = L⁻¹)
    (z : crossedCocycles (ρ₁.comp H.subtype)) (hz : z ∈ parabolicCocycles (ρ₁.comp H.subtype) ⟨T, hT⟩ ⟨L, hL⟩) :
    (minusPart ρ₁ hεε normal z).val ⟨T, hT⟩ ∈ moved ρ₁ T ∧
      (minusPart ρ₁ hεε normal z).val ⟨L, hL⟩ ∈ moved ρ₁ L :=
  ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hz.1 (conj_moved ρ₁ hεε normal T hT hεT z hz.1)),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hz.2 (conj_moved ρ₁ hεε normal L hL hεL z hz.2))⟩

theorem moved_agree (agree : ∀ k : H, ρ₂ k.val = ρ₁ k.val) (k : G) (hk : k ∈ H) :
    moved ρ₂ k = moved ρ₁ k := by
  unfold moved
  rw [agree ⟨k, hk⟩]

/-- **Parabolic splitting**: `dim H¹_par(H) ≤ dim H¹_par(G, ρ₁) + dim H¹_par(G, ρ₂)`. -/
theorem finrank_parabolicH1_le_add [FiniteDimensional ℂ (CrossedH1 ρ₁)]
    [FiniteDimensional ℂ (CrossedH1 ρ₂)]
    (cover : ∀ g : G, g ∈ H ∨ g * ε ∈ H) (hεε : ε * ε = 1)
    (normal : ∀ k ∈ H, ε * k * ε ∈ H) (agree : ∀ k : H, ρ₂ k.val = ρ₁ k.val)
    (anti : ρ₂ ε = -(ρ₁ ε)) (T L : G) (hT : T ∈ H) (hL : L ∈ H)
    (hεT : ε * T * ε = T⁻¹) (hεL : ε * L * ε = L⁻¹) :
    finrank ℂ (parabolicH1 (ρ₁.comp H.subtype) ⟨T, hT⟩ ⟨L, hL⟩) ≤
      finrank ℂ (parabolicH1 ρ₁ T L) + finrank ℂ (parabolicH1 ρ₂ T L) := by
  let P₁ := parabolicH1 ρ₁ T L
  let P₂ := parabolicH1 ρ₂ T L
  let Φ : P₁ × P₂ →ₗ[ℂ] CrossedH1 (ρ₁.comp H.subtype) :=
    (splitMap ρ₁ ρ₂ agree).comp (P₁.subtype.prodMap P₂.subtype)
  have cover_le : parabolicH1 (ρ₁.comp H.subtype) ⟨T, hT⟩ ⟨L, hL⟩ ≤ LinearMap.range Φ := by
    rintro _ ⟨z, hz, rfl⟩
    let plus := extendCocycle cover ρ₁ ρ₁ hεε normal (fun _ => rfl) (plusPart ρ₁ hεε normal z)
      (plusPart_conj ρ₁ hεε normal z)
    let minus := extendCocycle cover ρ₁ ρ₂ hεε normal agree (minusPart ρ₁ hεε normal z)
      (minusPart_conj ρ₁ ρ₂ hεε normal anti z)
    have plusT := extendCocycle_mem cover ρ₁ ρ₁ hεε normal (fun _ => rfl) _
      (plusPart_conj ρ₁ hεε normal z) ⟨T, hT⟩
    have plusL := extendCocycle_mem cover ρ₁ ρ₁ hεε normal (fun _ => rfl) _
      (plusPart_conj ρ₁ hεε normal z) ⟨L, hL⟩
    have minusT := extendCocycle_mem cover ρ₁ ρ₂ hεε normal agree _
      (minusPart_conj ρ₁ ρ₂ hεε normal anti z) ⟨T, hT⟩
    have minusL := extendCocycle_mem cover ρ₁ ρ₂ hεε normal agree _
      (minusPart_conj ρ₁ ρ₂ hεε normal anti z) ⟨L, hL⟩
    have pp := plusPart_parabolic ρ₁ hεε normal T L hT hL hεT hεL z hz
    have mp := minusPart_parabolic ρ₁ hεε normal T L hT hL hεT hεL z hz
    have plus_mem : (crossedBoundaries ρ₁).mkQ plus ∈ P₁ :=
      ⟨plus, ⟨by rw [plusT]; exact pp.1, by rw [plusL]; exact pp.2⟩, rfl⟩
    have minus_mem : (crossedBoundaries ρ₂).mkQ minus ∈ P₂ :=
      ⟨minus, ⟨by
        rw [minusT, moved_agree ρ₁ ρ₂ agree T hT]
        exact mp.1, by
        rw [minusL, moved_agree ρ₁ ρ₂ agree L hL]
        exact mp.2⟩, rfl⟩
    refine ⟨(⟨_, plus_mem⟩, ⟨_, minus_mem⟩), ?_⟩
    change crossedPullbackH1 H.subtype ρ₁ ((crossedBoundaries ρ₁).mkQ plus) +
      twistedRestrictionH1 ρ₁ ρ₂ agree ((crossedBoundaries ρ₂).mkQ minus) = _
    rw [crossedPullbackH1_mk]
    change (crossedBoundaries (ρ₁.comp H.subtype)).mkQ (crossedPullbackCocycles H.subtype ρ₁ plus) +
      (crossedBoundaries (ρ₁.comp H.subtype)).mkQ (twistedRestriction ρ₁ ρ₂ agree minus) =
        (crossedBoundaries (ρ₁.comp H.subtype)).mkQ z
    rw [← map_add]
    congr 1
    conv_rhs => rw [← plus_add_minus ρ₁ hεε normal z]
    congr 1
    · apply Subtype.ext
      funext k
      exact extendCocycle_mem cover ρ₁ ρ₁ hεε normal (fun _ => rfl) _
        (plusPart_conj ρ₁ hεε normal z) k
    · apply Subtype.ext
      funext k
      exact extendCocycle_mem cover ρ₁ ρ₂ hεε normal agree _
        (minusPart_conj ρ₁ ρ₂ hεε normal anti z) k
  have mono := Submodule.finrank_mono cover_le
  have range := LinearMap.finrank_range_le Φ
  rw [Module.finrank_prod] at range
  have e₁ : finrank ℂ P₁ = finrank ℂ (parabolicH1 ρ₁ T L) := rfl
  have e₂ : finrank ℂ P₂ = finrank ℂ (parabolicH1 ρ₂ T L) := rfl
  omega

end ParabolicSplitting

end TernaryPeriodPolynomials.LevelThree.TwistSplitting
