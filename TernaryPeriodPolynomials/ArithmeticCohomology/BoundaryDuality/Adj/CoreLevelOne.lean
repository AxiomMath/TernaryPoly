module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreCores
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreModular
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreFricke

@[expose] public section


/-!
# Hecke adjointness of the cup pairing of `SL₂(ℤ)`

Let `T_p` be the Hecke operator of `SL₂(ℤ) diag(p, 1) SL₂(ℤ)` on crossed homomorphisms with values
in restrictions of representations of `GL₂(ℚ)`, and let `B` be an `SL₂(ℤ)`-invariant pairing with
`B(g_W⁻¹ v, g_W w) = κ B(v, w)` for the Fricke-type element `g_W = α₀⁻¹ S`
(`α₀ = diag(1, p)`).  For crossed homomorphisms `x`, `y` vanishing at `T`, the cup formula of the
triple model satisfies

  `⟨x, T_p y⟩ = κ ⟨T_p x, y⟩`  (`cupFormula_hecke_adjoint_core`).

The proof:
* the cup formula is `-θ(T)` for any primitive `θ` of the scalar cup product
  (`cupFormula_eq_neg_theta`);
* the Hecke cocycle is the corestriction from `Γ⁰(p) = Stab(Γ α₀)` of `α₀^* x` along the
  transversal `T^b`, `S`, up to a coboundary, so the projection formulas turn a primitive `θ'` on
  `Γ⁰(p)` into one on `SL₂(ℤ)`, and its value at `T` is the sum of the values of `θ'` at the two
  cusp generators `T^p` and `S T S⁻¹` of `Γ⁰(p)` plus an explicit correction
  (`cupFormula_hecke_left`, `cupFormula_hecke_right`);
* the Fricke involution `h ↦ g_W h g_W⁻¹` of `Γ⁰(p)` exchanges the two cusp generators and carries
  a primitive for `(α₀^* x, y)` to one for `(x, α₀^* y)` (`isCupPrimitive_fricke`); the remaining
  corrections cancel.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open scoped MatrixGroups
open Matrix TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Generic

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾}

/-- The Hecke formula maps crossed homomorphisms to crossed homomorphisms. -/
theorem isCocycle_heckeFun (S : RightCosets embed) (A : Rep.{0, 0, 0} ℂ G)
    (ρ𝔾 : Representation ℂ 𝔾 A) (compat : ∀ g, A.ρ g = ρ𝔾 (embed g))
    (embedded : Function.Injective embed) {x : G → A} (hx : IsCocycle A.ρ x) :
    IsCocycle A.ρ (heckeFun S A ρ𝔾 x) := by
  have hmem : x ∈ groupCohomology.cocycles₁ A :=
    (groupCohomology.mem_cocycles₁_iff x).2 fun g h => (hx g h).trans (add_comm _ _)
  have h := heckeFun_mem S A ρ𝔾 compat embedded ⟨x, hmem⟩
  intro g k
  exact ((groupCohomology.mem_cocycles₁_iff _).1 h g k).trans (add_comm _ _)

end Generic

variable (p : Nat.Primes)

/-- The transition of `T` at a coset `α_b`, `b + 1 < p`, is trivial (as a stabilizer element). -/
theorem transit_T_some' (b : Fin p.val) (hb : b.val + 1 < p.val) :
    transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
      (levelOneTransversal_spec p) ModularGroup.T (some b) = 1 :=
  Subtype.ext (transit_T_some p b hb)

/-- The transition of `T` at the last coset is `T^p` (as a stabilizer element). -/
theorem transit_T_last' :
    transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
      (levelOneTransversal_spec p) ModularGroup.T
      (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) =
        ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ :=
  Subtype.ext (transit_T_last p)

/-- The transition of `T` at the cusp coset is `S T S⁻¹` (as a stabilizer element). -/
theorem transit_T_none' :
    transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
      (levelOneTransversal_spec p) ModularGroup.T none =
        ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ :=
  Subtype.ext (transit_T_none p)

/-- The Fricke involution maps `T^p` to `S T S⁻¹`. -/
theorem conjWHom_T_pow :
    conjWHom p ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ =
      ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ :=
  Subtype.ext (conjW_T_pow p)

/-- The Fricke involution maps `S T S⁻¹` to `T^p`. -/
theorem conjWHom_STS :
    conjWHom p ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ =
      ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ :=
  Subtype.ext (conjW_STS p)

/-- `g_W² = -1/p` is central. -/
theorem gW_mul_gW_central (k : GL (Fin 2) ℚ) : gW p * gW p * k = k * (gW p * gW p) := by
  rw [gW_mul_gW p]
  exact GeneralLinearGroup.scalar_commute _ k

/-- A sum over the Hecke cosets of a function vanishing at the cosets `α_b` with `b + 1 < p` is
its value at the last coset plus its value at the cusp coset. -/
theorem sum_cosets_last {M : Type*} [AddCommMonoid M] (F : (modularCosets p).index → M)
    (hF : ∀ b : Fin p.val, b.val + 1 < p.val → F (some b) = 0) :
    ∑ j, F j = F (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩) + F none :=
  sum_option_last p F hF

section Core

variable {A A' : Rep.{0, 0, 0} ℂ SL(2, ℤ)} {ρ𝔾 : Representation ℂ (GL (Fin 2) ℚ) A}
  {ρ𝔾' : Representation ℂ (GL (Fin 2) ℚ) A'}
  {B : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}

/-- **The Hecke cocycle of a crossed homomorphism vanishing on `T` vanishes at `T`**: the
transitions of `T` are `1`, `T` and `T^p`. -/
theorem heckeFun_T_eq_zero {x : SL(2, ℤ) → A} (hx : IsCocycle A.ρ x)
    (hxT : x ModularGroup.T = 0) :
    heckeFun (modularCosets p) A ρ𝔾 x ModularGroup.T = 0 := by
  rw [heckeFun_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hval : x ((modularCosets p).delta ModularGroup.T j) = 0 := by
    cases j with
    | none =>
      rw [delta_T_none p]
      exact isCocycle_zpow_eq_zero hx hxT _
    | some b =>
      by_cases hb : b.val + 1 < p.val
      · rw [delta_T_some p b hb]
        exact hx.map_one
      · have hbl : b = ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩ := by
          apply Fin.ext
          have := b.isLt
          show b.val = p.val - 1
          omega
        rw [hbl, delta_T_last p]
        exact hxT
  rw [hval, map_zero]

/-- **The cup formula of a Hecke cocycle against a cocycle vanishing at `T`** is read off from a
cup primitive `θ'` of `(α₀^* x, y)` on `Γ⁰(p)` at the two cusp generators `T^p`, `S T S⁻¹`. -/
theorem cupFormula_hecke_left (compat : ∀ n, A.ρ n = ρ𝔾 (modularEmbed n))
    (hinv : ∀ n v w, B (A.ρ n v) (A'.ρ n w) = B v w)
    {x : SL(2, ℤ) → A} (hx : IsCocycle A.ρ x) {y : SL(2, ℤ) → A'} (hy : IsCocycle A'.ρ y)
    (hyT : y ModularGroup.T = 0) {θ' : stab (modularCosets p) (levelOneBase p) → ℂ}
    (hθ' : IsCupPrimitive B (A'.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      (baseCocycle ρ𝔾 x) (fun h => y h) θ')
    {v : A × A × A}
    (hv : IsPrimitive A.ρ ModularGroup.S ModularGroup.T⁻¹ (heckeFun (modularCosets p) A ρ𝔾 x) v) :
    cupFormula B A'.ρ ModularGroup.S ModularGroup.T⁻¹ (heckeFun (modularCosets p) A ρ𝔾 x) y v =
      -(θ' ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ +
        θ' ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ -
        B (baseCocycle ρ𝔾 x ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩)
          (A'.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) (y ModularGroup.S))) := by
  have hX' : IsCocycle (A.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      (baseCocycle ρ𝔾 x) := isCocycle_baseCocycle ρ𝔾 compat modularEmbed_injective hx
  have hθtil := isCupPrimitive_transverseSum_left (levelOneTransversal p)
    (levelOneTransversal_spec p) hinv hX' hy hθ'
  have hL := isCupPrimitive_add_boundary_left hinv hy hθtil
    (heckeCorrection (S := modularCosets p) (levelOneBase p) (levelOneTransversal p) ρ𝔾 x)
  have hθ₁ : IsCupPrimitive B A'.ρ (heckeFun (modularCosets p) A ρ𝔾 x) y
      (fun g => (∑ j, θ' (transit (S := modularCosets p) (j₀ := levelOneBase p)
          (levelOneTransversal p) (levelOneTransversal_spec p) g j) -
        ∑ j, B (baseCocycle ρ𝔾 x
            (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
                (levelOneTransversal_spec p) g j))
          (A'.ρ (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
              (levelOneTransversal_spec p) g j : SL(2, ℤ))
            (y (levelOneTransversal p ((modularCosets p).next g j))))) +
        B (heckeCorrection (S := modularCosets p) (levelOneBase p) (levelOneTransversal p) ρ𝔾 x)
            (y g)) := by
    intro g h
    rw [heckeFun_eq_transverseSum (levelOneTransversal p) (levelOneTransversal_spec p) ρ𝔾 compat
      modularEmbed_injective hx g]
    exact hL g h
  rw [cupFormula_eq_neg_theta hinv
    (isCocycle_heckeFun (modularCosets p) A ρ𝔾 compat modularEmbed_injective hx) hy hθ₁ hv hyT]
  congr 1
  rw [hyT, map_zero, add_zero]
  have h0 := hθ'.map_one hX'
  have hX0 := hX'.map_one
  have hr1 : levelOneTransversal p ((modularCosets p).next ModularGroup.T
      (some ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩)) = 1 :=
    (congrArg (levelOneTransversal p) (next_T_last p)).trans (levelOneTransversal_base p)
  have hrN : levelOneTransversal p ((modularCosets p).next ModularGroup.T none) =
      ModularGroup.S := congrArg (levelOneTransversal p) (next_T_none p)
  have e1 : (∑ j, θ' (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
        (levelOneTransversal_spec p) ModularGroup.T j)) =
      θ' ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ +
        θ' ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ := by
    refine (sum_cosets_last p _ fun b hb => ?_).trans ?_
    · simp only [transit_T_some' p b hb, h0]
    · exact congrArg₂ (· + ·) (congrArg θ' (transit_T_last' p)) (congrArg θ' (transit_T_none' p))
  have e2 : (∑ j, B (baseCocycle ρ𝔾 x (transit (S := modularCosets p) (j₀ := levelOneBase p)
      (levelOneTransversal p)
        (levelOneTransversal_spec p) ModularGroup.T j))
      (A'.ρ (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
        (levelOneTransversal_spec p) ModularGroup.T j : SL(2, ℤ))
        (y (levelOneTransversal p ((modularCosets p).next ModularGroup.T j))))) =
      B (baseCocycle ρ𝔾 x ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩)
        (A'.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) (y ModularGroup.S)) := by
    refine (sum_cosets_last p _ fun b hb => ?_).trans ?_
    · simp only [transit_T_some' p b hb, hX0, map_zero, LinearMap.zero_apply]
    · rw [hr1, hy.map_one, map_zero, map_zero, zero_add, hrN]
      exact congrArg (fun k : stab (modularCosets p) (levelOneBase p) =>
        B (baseCocycle ρ𝔾 x k) (A'.ρ (k : SL(2, ℤ)) (y ModularGroup.S))) (transit_T_none' p)
  linear_combination e1 - e2

/-- **The cup formula of a cocycle vanishing at `T` against a Hecke cocycle** is read off from a
cup primitive `θ''` of `(x, α₀^* y)` on `Γ⁰(p)` at the two cusp generators. -/
theorem cupFormula_hecke_right (compat' : ∀ n, A'.ρ n = ρ𝔾' (modularEmbed n))
    (hinv : ∀ n v w, B (A.ρ n v) (A'.ρ n w) = B v w)
    {x : SL(2, ℤ) → A} (hx : IsCocycle A.ρ x) (hxT : x ModularGroup.T = 0)
    {y : SL(2, ℤ) → A'} (hy : IsCocycle A'.ρ y) (hyT : y ModularGroup.T = 0)
    {θ'' : stab (modularCosets p) (levelOneBase p) → ℂ}
    (hθ'' : IsCupPrimitive B (A'.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      (fun h => x h) (baseCocycle ρ𝔾' y) θ'')
    {v₀ : A × A × A} (hv₀ : IsPrimitive A.ρ ModularGroup.S ModularGroup.T⁻¹ x v₀) :
    cupFormula B A'.ρ ModularGroup.S ModularGroup.T⁻¹ x (heckeFun (modularCosets p) A' ρ𝔾' y) v₀ =
      -(θ'' ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ +
        θ'' ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ +
        B (x ModularGroup.S)
          (baseCocycle ρ𝔾' y
            ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩)) := by
  have hY' : IsCocycle (A'.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      (baseCocycle ρ𝔾' y) := isCocycle_baseCocycle ρ𝔾' compat' modularEmbed_injective hy
  have hθhat := isCupPrimitive_transverseSum_right (levelOneTransversal p)
    (levelOneTransversal_spec p) hinv hx hY' hθ''
  have hR := isCupPrimitive_add_boundary_right hinv hx hθhat
    (heckeCorrection (S := modularCosets p) (levelOneBase p) (levelOneTransversal p) ρ𝔾' y)
  have hθ₂ : IsCupPrimitive B A'.ρ x (heckeFun (modularCosets p) A' ρ𝔾' y)
      (fun g => (∑ j, θ'' (transit (S := modularCosets p) (j₀ := levelOneBase p)
          (levelOneTransversal p) (levelOneTransversal_spec p) g j) +
        ∑ j, B (x (levelOneTransversal p j)) (baseCocycle ρ𝔾' y
            (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
                (levelOneTransversal_spec p) g j))) -
        B (x g) (A'.ρ g (heckeCorrection (S := modularCosets p) (levelOneBase p)
            (levelOneTransversal p) ρ𝔾' y))) := by
    intro g h
    rw [heckeFun_eq_transverseSum (levelOneTransversal p) (levelOneTransversal_spec p) ρ𝔾' compat'
      modularEmbed_injective hy h]
    exact hR g h
  rw [cupFormula_eq_neg_theta hinv hx
    (isCocycle_heckeFun (modularCosets p) A' ρ𝔾' compat' modularEmbed_injective hy) hθ₂ hv₀
    (heckeFun_T_eq_zero p hy hyT)]
  congr 1
  rw [hxT, map_zero, LinearMap.zero_apply, sub_zero]
  have h0 := hθ''.map_one (isCocycle_restrictStab (K := stab (modularCosets p) (levelOneBase p)) hx)
  have e1 : (∑ j, θ'' (transit (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
        (levelOneTransversal_spec p) ModularGroup.T j)) =
      θ'' ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ +
        θ'' ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ := by
    refine (sum_cosets_last p _ fun b hb => ?_).trans ?_
    · simp only [transit_T_some' p b hb, h0]
    · exact congrArg₂ (· + ·) (congrArg θ'' (transit_T_last' p))
        (congrArg θ'' (transit_T_none' p))
  have e2 : (∑ j, B (x (levelOneTransversal p j)) (baseCocycle ρ𝔾' y (transit
      (S := modularCosets p) (j₀ := levelOneBase p) (levelOneTransversal p)
        (levelOneTransversal_spec p) ModularGroup.T j))) =
      B (x ModularGroup.S)
        (baseCocycle ρ𝔾' y
            ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩) := by
    refine (sum_cosets_last p _ fun b _ => ?_).trans ?_
    · simp only [levelOneTransversal_some, isCocycle_zpow_eq_zero hx hxT, map_zero,
        LinearMap.zero_apply]
    · rw [levelOneTransversal_some, isCocycle_zpow_eq_zero hx hxT, map_zero, LinearMap.zero_apply,
        zero_add, levelOneTransversal_none]
      exact congrArg (fun k : stab (modularCosets p) (levelOneBase p) =>
        B (x ModularGroup.S) (baseCocycle ρ𝔾' y k)) (transit_T_none' p)
  linear_combination e1 + e2

/-- **Hecke adjointness of the cup formula of `SL₂(ℤ)`**, for crossed homomorphisms vanishing at
`T`: `⟨x, T_p y⟩ = κ ⟨T_p x, y⟩`, where `B(g_W⁻¹ v, g_W w) = κ B(v, w)`. -/
theorem cupFormula_hecke_adjoint_core (compat : ∀ n, A.ρ n = ρ𝔾 (modularEmbed n))
    (compat' : ∀ n, A'.ρ n = ρ𝔾' (modularEmbed n))
    (hinv : ∀ n v w, B (A.ρ n v) (A'.ρ n w) = B v w) (κ : ℂ)
    (hW : ∀ v w, B (ρ𝔾 (gW p)⁻¹ v) (ρ𝔾' (gW p) w) = κ * B v w)
    {x : SL(2, ℤ) → A} (hx : IsCocycle A.ρ x) (hxT : x ModularGroup.T = 0)
    {y : SL(2, ℤ) → A'} (hy : IsCocycle A'.ρ y) (hyT : y ModularGroup.T = 0)
    {v : A × A × A}
    (hv : IsPrimitive A.ρ ModularGroup.S ModularGroup.T⁻¹ (heckeFun (modularCosets p) A ρ𝔾 x) v)
    {v₀ : A × A × A} (hv₀ : IsPrimitive A.ρ ModularGroup.S ModularGroup.T⁻¹ x v₀) :
    cupFormula B A'.ρ ModularGroup.S ModularGroup.T⁻¹ x (heckeFun (modularCosets p) A' ρ𝔾' y) v₀ =
      κ * cupFormula B A'.ρ ModularGroup.S ModularGroup.T⁻¹
        (heckeFun (modularCosets p) A ρ𝔾 x) y v := by
  have hX' : IsCocycle (A.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      (baseCocycle ρ𝔾 x) := isCocycle_baseCocycle ρ𝔾 compat modularEmbed_injective hx
  have hyH : IsCocycle (A'.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      (fun h => y h) := fun a b => hy a b
  obtain ⟨θ', hθ'⟩ := exists_isCupPrimitive_subgroup (stab (modularCosets p) (levelOneBase p))
    (ρ := A.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
    (ρ' := A'.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype) (fun g => hinv g) hX' hyH
  have hθ'' := isCupPrimitive_fricke (S := modularCosets p) (j₀ := levelOneBase p)
    (s := ModularGroup.S) (g' := gW p) (c := conjWHom p) le_rfl compat compat'
    modularEmbed_injective
    (rep_base_mul_gW p) (fun h => modularEmbed_conjW p h) (fun h => conjW_conjW p h)
    (gW_mul_gW_central p) (fun g => hinv g) κ hW hx hy hθ'
  rw [cupFormula_hecke_right p compat' hinv hx hxT hy hyT hθ'' hv₀,
    cupFormula_hecke_left p compat hinv hx hy hyT hθ' hv]
  dsimp only
  rw [conjWHom_T_pow p, conjWHom_STS p]
  -- values of the cocycles at the cusp generators
  have hxTp : x (ModularGroup.T ^ (p.val : ℤ)) = 0 := isCocycle_zpow_eq_zero hx hxT _
  have hyTp : y (ModularGroup.T ^ (p.val : ℤ)) = 0 := isCocycle_zpow_eq_zero hy hyT _
  have hxs : x (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) = x ModularGroup.S -
      A.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) (x ModularGroup.S) := by
    rw [hx (ModularGroup.S * ModularGroup.T) ModularGroup.S⁻¹, hx ModularGroup.S ModularGroup.T,
      hxT, map_zero, add_zero, isCocycle_map_inv hx ModularGroup.S, map_neg,
      ← rep_mul_apply A.ρ, ← sub_eq_add_neg]
  have hys : y (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) = y ModularGroup.S -
      A'.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) (y ModularGroup.S) := by
    rw [hy (ModularGroup.S * ModularGroup.T) ModularGroup.S⁻¹, hy ModularGroup.S ModularGroup.T,
      hyT, map_zero, add_zero, isCocycle_map_inv hy ModularGroup.S, map_neg,
      ← rep_mul_apply A'.ρ, ← sub_eq_add_neg]
  have hxt : x (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹) =
      x ModularGroup.S - A.ρ (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹)
        (x ModularGroup.S) := by
    rw [hx (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ)) ModularGroup.S⁻¹,
      hx ModularGroup.S (ModularGroup.T ^ (p.val : ℤ)), hxTp, map_zero, add_zero,
      isCocycle_map_inv hx ModularGroup.S, map_neg, ← rep_mul_apply A.ρ, ← sub_eq_add_neg]
  have hyt : y (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹) =
      y ModularGroup.S - A'.ρ (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹)
        (y ModularGroup.S) := by
    rw [hy (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ)) ModularGroup.S⁻¹,
      hy ModularGroup.S (ModularGroup.T ^ (p.val : ℤ)), hyTp, map_zero, add_zero,
      isCocycle_map_inv hy ModularGroup.S, map_neg, ← rep_mul_apply A'.ρ, ← sub_eq_add_neg]
  -- `α₀⁻¹ (S T^p S⁻¹) = (S T S⁻¹) α₀⁻¹`
  have hembed : (binaryHeckeRepresentative p (levelOneBase p))⁻¹ *
      modularEmbed (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹) =
      modularEmbed (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) *
        (binaryHeckeRepresentative p (levelOneBase p))⁻¹ := by
    have e := embed_delta_stab (S := modularCosets p) (j₀ := levelOneBase p) (mem_stab_STS p)
    rw [delta_STS_base p] at e
    change modularEmbed (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹) =
      binaryHeckeRepresentative p (levelOneBase p) *
        modularEmbed (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) *
          (binaryHeckeRepresentative p (levelOneBase p))⁻¹ at e
    rw [e]
    group
  have hcomm : ∀ v : A, ρ𝔾 (binaryHeckeRepresentative p (levelOneBase p))⁻¹
      (A.ρ (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹) v) =
      A.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹)
        (ρ𝔾 (binaryHeckeRepresentative p (levelOneBase p))⁻¹ v) := by
    intro v
    rw [compat, compat, ← rep_mul_apply ρ𝔾, ← rep_mul_apply ρ𝔾, hembed]
  have hcomm' : ∀ w : A', ρ𝔾' (binaryHeckeRepresentative p (levelOneBase p))⁻¹
      (A'.ρ (ModularGroup.S * ModularGroup.T ^ (p.val : ℤ) * ModularGroup.S⁻¹) w) =
      A'.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹)
        (ρ𝔾' (binaryHeckeRepresentative p (levelOneBase p))⁻¹ w) := by
    intro w
    rw [compat', compat', ← rep_mul_apply ρ𝔾', ← rep_mul_apply ρ𝔾', hembed]
  -- the base cocycles at `S T S⁻¹`
  have hX's : baseCocycle ρ𝔾 x ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹,
      mem_stab_STS p⟩ = ρ𝔾 (binaryHeckeRepresentative p (levelOneBase p))⁻¹ (x ModularGroup.S) -
        A.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹)
          (ρ𝔾 (binaryHeckeRepresentative p (levelOneBase p))⁻¹ (x ModularGroup.S)) := by
    change ρ𝔾 (binaryHeckeRepresentative p (levelOneBase p))⁻¹
      (x ((modularCosets p).delta (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹)
        (levelOneBase p))) = _
    rw [delta_STS_base p, hxt, map_sub, hcomm]
  have hY's : baseCocycle ρ𝔾' y ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹,
      mem_stab_STS p⟩ = ρ𝔾' (binaryHeckeRepresentative p (levelOneBase p))⁻¹ (y ModularGroup.S) -
        A'.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹)
          (ρ𝔾' (binaryHeckeRepresentative p (levelOneBase p))⁻¹ (y ModularGroup.S)) := by
    change ρ𝔾' (binaryHeckeRepresentative p (levelOneBase p))⁻¹
      (y ((modularCosets p).delta (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹)
        (levelOneBase p))) = _
    rw [delta_STS_base p, hyt, map_sub, hcomm']
  -- the Fricke twists
  have hgS : (gW p)⁻¹ * (binaryHeckeRepresentative p (levelOneBase p))⁻¹ =
      modularEmbed ModularGroup.S⁻¹ := by
    rw [map_inv, ← rep_base_mul_gW p, _root_.mul_inv_rev]
  have ha₀ : A.ρ ModularGroup.S⁻¹ (x ModularGroup.S) =
      ρ𝔾 (gW p)⁻¹ (ρ𝔾 (binaryHeckeRepresentative p (levelOneBase p))⁻¹ (x ModularGroup.S)) := by
    rw [← rep_mul_apply ρ𝔾, hgS, compat]
  have hgS' : gW p * modularEmbed ModularGroup.S⁻¹ =
      (binaryHeckeRepresentative p (levelOneBase p))⁻¹ := by
    rw [map_inv, ← rep_base_mul_gW p]
    group
  have hb₀ : ρ𝔾' (gW p) (A'.ρ ModularGroup.S⁻¹ (y ModularGroup.S)) =
      ρ𝔾' (binaryHeckeRepresentative p (levelOneBase p))⁻¹ (y ModularGroup.S) := by
    rw [compat', ← rep_mul_apply ρ𝔾', hgS']
  have hcoe : ((⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ :
      stab (modularCosets p) (levelOneBase p)) : SL(2, ℤ)) =
        ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ := rfl
  have hcoeT : ((⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ :
      stab (modularCosets p) (levelOneBase p)) : SL(2, ℤ)) = ModularGroup.T ^ (p.val : ℤ) := rfl
  have hρs : ∀ w : A', (A'.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹, mem_stab_STS p⟩ w =
        A'.ρ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) w := fun _ => rfl
  have hρT : ∀ w : A', (A'.ρ.comp (stab (modularCosets p) (levelOneBase p)).subtype)
      ⟨ModularGroup.T ^ (p.val : ℤ), mem_stab_T_pow p⟩ w =
        A'.ρ (ModularGroup.T ^ (p.val : ℤ)) w := fun _ => rfl
  simp only [hρs, hρT, hX's, hY's, hxTp, hyTp, hxs, hys, ha₀, hb₀, map_zero,
    LinearMap.zero_apply, map_sub, map_neg, LinearMap.sub_apply, hW, hinv]
  ring

end Core

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
