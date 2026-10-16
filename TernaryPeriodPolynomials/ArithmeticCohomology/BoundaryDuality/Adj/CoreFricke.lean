module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreStab

@[expose] public section


/-!
# A Fricke-type involution of the stabilizer of a Hecke coset

Let `Γ' = G ∩ α⁻¹ G α` be the stabilizer of the coset `j₀` of a Hecke correspondence
(`α = α_{j₀}`), and let `g' ∈ 𝔾` with `α g' = s ∈ G` (so `g'` maps `Γ'` into the conjugate
`α⁻¹ Γ α`), such that conjugation by `g'` is an involution `c` of `Γ'` and `g'²` is central.  For
a crossed homomorphism `x` of `G` the cocycle `α^* x : h ↦ α⁻¹ x(α h α⁻¹)` of `Γ'` and the
restriction of `x` are exchanged by `c` up to the twist by `g'` and an explicit coboundary:

  `x h = g'⁻¹ (α^* x)(c h) + (h - 1) s⁻¹ x(s)`,
  `(α^* y) h = g' y(c h) + (h - 1) b₀`,  `b₀ = -g' s⁻¹ y(s)`.

Consequently a primitive `θ'` of the scalar cup product of `(α^* x, y)` on `Γ'` yields, through the
twisted pullback by `c` (scaled by the factor `κ` with `B(g'⁻¹ v, g' w) = κ B(v, w)`) and the two
coboundary corrections, an explicit primitive of the cup product of `(x, α^* y)`
(`isCupPrimitive_fricke`).  This is the symmetry which makes the Hecke operator of a double coset
adjoint to the Hecke operator of the transposed double coset.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.Spectral.HeckeH1

section Fricke

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾} {S : RightCosets embed}
  {j₀ : S.index} {K : Subgroup G} {s : G} {g' : 𝔾} {c : K →* K}

/-- The transition at `j₀` of `c h` is `s h s⁻¹`. -/
theorem delta_fricke (hK : K ≤ stab S j₀) (embedded : Function.Injective embed)
    (hs : S.rep j₀ * g' = embed s) (hc : ∀ h, embed (c h : G) = g' * embed h * g'⁻¹) (h : K) :
    S.delta (c h : G) j₀ = s * h * s⁻¹ := by
  apply embedded
  rw [embed_delta_stab (hK (c h).2), hc, map_mul, map_mul, map_inv, ← hs]
  group

/-- The transition at `j₀` of `h` is `s (c h) s⁻¹`, when `c` is an involution. -/
theorem delta_fricke' (hK : K ≤ stab S j₀) (embedded : Function.Injective embed)
    (hs : S.rep j₀ * g' = embed s) (hc : ∀ h, embed (c h : G) = g' * embed h * g'⁻¹)
    (hcc : ∀ h, c (c h) = h) (h : K) : S.delta (h : G) j₀ = s * (c h : G) * s⁻¹ := by
  have e := delta_fricke hK embedded hs hc (c h)
  rwa [hcc] at e

/-- `g'` intertwines `c h` and `h`: `g' (c h) = h g'`, since `g'²` is central. -/
theorem fricke_comm (hc : ∀ h, embed (c h : G) = g' * embed h * g'⁻¹)
    (hcent : ∀ k : 𝔾, g' * g' * k = k * (g' * g')) (h : K) :
    g' * embed (c h : G) = embed (h : G) * g' := by
  have e := hcent (embed (h : G))
  calc g' * embed (c h : G) = g' * (g' * embed (h : G) * g'⁻¹) := by rw [hc]
    _ = g' * g' * embed (h : G) * g'⁻¹ := by group
    _ = embed (h : G) * (g' * g') * g'⁻¹ := by rw [e]
    _ = embed (h : G) * g' := by group

variable {A A' : Rep.{0, 0, 0} ℂ G} {ρ𝔾 : Representation ℂ 𝔾 A} {ρ𝔾' : Representation ℂ 𝔾 A'}

/-- The cocycle `α^* x : h ↦ α⁻¹ x(α h α⁻¹)` of the stabilizer. -/
theorem isCocycle_pullbackBase (hK : K ≤ stab S j₀) (compat : ∀ g, A.ρ g = ρ𝔾 (embed g))
    (embedded : Function.Injective embed) {x : G → A} (hx : IsCocycle A.ρ x) :
    IsCocycle (A.ρ.comp K.subtype)
      (fun h => ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (h : G) j₀))) := by
  intro h k
  have key : ∀ v : A, ρ𝔾 (S.rep j₀)⁻¹ (A.ρ (S.delta (h : G) j₀) v) =
      A.ρ (h : G) (ρ𝔾 (S.rep j₀)⁻¹ v) := by
    intro v
    rw [compat, compat, ← rep_mul_apply ρ𝔾, ← rep_mul_apply ρ𝔾, embed_delta_stab (hK h.2),
      show (S.rep j₀)⁻¹ * (S.rep j₀ * embed (h : G) * (S.rep j₀)⁻¹) =
        embed (h : G) * (S.rep j₀)⁻¹ by group]
  change ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta ((h : G) * k) j₀)) =
    ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (h : G) j₀)) +
      A.ρ (h : G) (ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (k : G) j₀)))
  rw [delta_stab_mul embedded (hK h.2), hx, map_add, key]

/-- The restriction of a crossed homomorphism to the stabilizer. -/
theorem isCocycle_restrictStab {y : G → A'} (hy : IsCocycle A'.ρ y) :
    IsCocycle (A'.ρ.comp K.subtype) (fun h => y h) :=
  fun a b => hy a b

/-- **The Fricke symmetry of cup primitives.**  If `θ'` is a cup primitive of `(α^* x, y)` on the
stabilizer, then an explicit twist of `θ' ∘ c` is a cup primitive of `(x, α^* y)`. -/
theorem isCupPrimitive_fricke (hK : K ≤ stab S j₀) (compat : ∀ g, A.ρ g = ρ𝔾 (embed g))
    (compat' : ∀ g, A'.ρ g = ρ𝔾' (embed g)) (embedded : Function.Injective embed)
    (hs : S.rep j₀ * g' = embed s) (hc : ∀ h, embed (c h : G) = g' * embed h * g'⁻¹)
    (hcc : ∀ h, c (c h) = h) (hcent : ∀ k : 𝔾, g' * g' * k = k * (g' * g'))
    {B : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}
    (hinv : ∀ (g : K) v w, B (A.ρ (g : G) v) (A'.ρ (g : G) w) = B v w) (κ : ℂ)
    (hW : ∀ v w, B (ρ𝔾 g'⁻¹ v) (ρ𝔾' g' w) = κ * B v w)
    {x : G → A} (hx : IsCocycle A.ρ x) {y : G → A'} (hy : IsCocycle A'.ρ y)
    {θ' : K → ℂ}
    (hθ' : IsCupPrimitive B (A'.ρ.comp K.subtype)
      (fun h => ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (h : G) j₀))) (fun h => y h) θ') :
    IsCupPrimitive B (A'.ρ.comp K.subtype) (fun h => x h)
      (fun h => ρ𝔾' (S.rep j₀)⁻¹ (y (S.delta (h : G) j₀)))
      (fun h => κ * θ' (c h) + B (A.ρ s⁻¹ (x s)) (ρ𝔾' g' (y (c h))) -
        B (x h) ((A'.ρ.comp K.subtype) h (-(ρ𝔾' g' (A'.ρ s⁻¹ (y s)))))) := by
  set a₀ : A := A.ρ s⁻¹ (x s) with ha₀
  set b₀ : A' := -(ρ𝔾' g' (A'.ρ s⁻¹ (y s))) with hb₀
  have hinvH : ∀ (g : K) v w, B ((A.ρ.comp K.subtype) g v)
      ((A'.ρ.comp K.subtype) g w) = B v w := fun g => hinv g
  -- the twisted pullbacks
  have hf : ∀ (a : K) (v : A), ρ𝔾 g'⁻¹ ((A.ρ.comp K.subtype) (c a) v) =
      (A.ρ.comp K.subtype) a (ρ𝔾 g'⁻¹ v) := by
    intro a v
    change ρ𝔾 g'⁻¹ (A.ρ (c a : G) v) = A.ρ (a : G) (ρ𝔾 g'⁻¹ v)
    rw [compat, compat, ← rep_mul_apply ρ𝔾, ← rep_mul_apply ρ𝔾, hc,
      show g'⁻¹ * (g' * embed (a : G) * g'⁻¹) = embed (a : G) * g'⁻¹ by group]
  have hf' : ∀ (a : K) (w : A'), ρ𝔾' g' ((A'.ρ.comp K.subtype) (c a) w) =
      (A'.ρ.comp K.subtype) a (ρ𝔾' g' w) := by
    intro a w
    change ρ𝔾' g' (A'.ρ (c a : G) w) = A'.ρ (a : G) (ρ𝔾' g' w)
    rw [compat', compat', ← rep_mul_apply ρ𝔾', ← rep_mul_apply ρ𝔾', fricke_comm hc hcent a]
  have hX₁ := isCocycle_pullbackBase (S := S) (j₀ := j₀) hK compat embedded hx
  have hXhat := isCocycle_pullback c (ρ𝔾 g'⁻¹) hf hX₁
  have hYhat := isCocycle_pullback c (ρ𝔾' g') hf' (isCocycle_restrictStab (K := K) hy)
  have hcomp : ∀ (a : K) (v : A) (w : A'),
      B (ρ𝔾 g'⁻¹ v) ((A'.ρ.comp K.subtype) a (ρ𝔾' g' w)) =
        κ * B v ((A'.ρ.comp K.subtype) (c a) w) := by
    intro a v w
    rw [← hf', hW]
  have hpull := isCupPrimitive_pullback c (ρ𝔾 g'⁻¹) (ρ𝔾' g') κ hcomp hθ'
  have hL := isCupPrimitive_add_boundary_left hinvH hYhat hpull a₀
  have hR := isCupPrimitive_add_boundary_right hinvH
    (isCocycle_add hXhat (isCocycle_boundary _ a₀)) hL b₀
  -- the two coboundary identities
  have hρ : ∀ v : A, ρ𝔾 g'⁻¹ (ρ𝔾 (S.rep j₀)⁻¹ v) = A.ρ s⁻¹ v := by
    intro v
    rw [← rep_mul_apply ρ𝔾, compat, map_inv, ← hs, mul_inv_rev]
  have keyX : ∀ h : K, ρ𝔾 g'⁻¹ (ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (c h : G) j₀))) +
      ((A.ρ.comp K.subtype) h a₀ - a₀) = x h := by
    intro h
    change ρ𝔾 g'⁻¹ (ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (c h : G) j₀))) + (A.ρ (h : G) a₀ - a₀) = x h
    rw [delta_fricke hK embedded hs hc h, hρ, hx (s * h) s⁻¹, hx s h, isCocycle_map_inv hx s, ha₀]
    simp only [map_add, map_neg, rep_mul_apply A.ρ, rep_inv_apply A.ρ]
    abel
  have hρ' : ∀ w : A', ρ𝔾' (S.rep j₀)⁻¹ (A'.ρ s w) = ρ𝔾' g' w := by
    intro w
    rw [compat', ← rep_mul_apply ρ𝔾', ← hs,
      show (S.rep j₀)⁻¹ * (S.rep j₀ * g') = g' by group]
  have hys : ρ𝔾' (S.rep j₀)⁻¹ (y s) = ρ𝔾' g' (A'.ρ s⁻¹ (y s)) := by
    conv_lhs => rw [← rep_apply_inv A'.ρ s (y s)]
    exact hρ' _
  have keyY : ∀ h : K, ρ𝔾' g' (y (c h : G)) +
      ((A'.ρ.comp K.subtype) h b₀ - b₀) =
        ρ𝔾' (S.rep j₀)⁻¹ (y (S.delta (h : G) j₀)) := by
    intro h
    have hcomm := hf' h (A'.ρ s⁻¹ (y s))
    change ρ𝔾' g' (A'.ρ (c h : G) (A'.ρ s⁻¹ (y s))) =
      A'.ρ (h : G) (ρ𝔾' g' (A'.ρ s⁻¹ (y s))) at hcomm
    change ρ𝔾' g' (y (c h : G)) + (A'.ρ (h : G) b₀ - b₀) = _
    rw [delta_fricke' hK embedded hs hc hcc h, hy (s * (c h : G)) s⁻¹, hy s (c h : G),
      isCocycle_map_inv hy s]
    simp only [map_add, map_neg, rep_mul_apply A'.ρ, hρ', hys, hcomm, hb₀]
    abel
  intro g h
  have e := hR g h
  dsimp only at e ⊢
  rw [keyX g, keyX h, keyX (g * h), keyY h] at e
  exact e

end Fricke

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
