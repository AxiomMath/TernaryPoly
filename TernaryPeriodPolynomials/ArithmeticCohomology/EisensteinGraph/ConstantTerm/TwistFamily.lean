module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.SemidirectTwist

@[expose] public section


/-!
# Constancy of the class of a rational translation family on a semidirect lattice

Let `G = L ⋊ M` be embedded by `ι` in a group `H`, and let `h ∈ H` normalize `ι(G)` through an
endomorphism `φ` of `G` that fixes `L` and induces the identity on `M`. Let `C k` (`k ∈ ℤ`) be
homogeneous 2-cocycles on `H`-tuples, all `ι(G)`-equivariant, related by `C k (h x) = ρ h (C (k+1) x)`
and periodic, `C K = C 0`, where `h ^ K` lies in `ι(L)`. If `ρ h` is unipotent and `h` commutes with
`ι(L)`, then `C 1 - C 0` is the inhomogeneous coboundary of a `G`-cochain.

This is the parabolic (Levi times radical) analogue of `FlagExactness.translation_family_inhomogeneous`;
the unipotence input is the semidirect twist of `SemidirectTwist`.

Written by AxiomCode.
-/

open TernaryPeriodPolynomials.FlagExactness.FilteredUnipotence

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

section Factor

open Polynomial

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem commute_aeval {f S : Module.End ℂ M} (h : Commute S f) (p : ℂ[X]) :
    Commute S (aeval f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c S).mul_right (h.pow_right n)

/-- A unipotent invertible endomorphism: `T⁻¹ - 1` factors through `T ^ K - 1`, through a factor
commuting with everything that commutes with `T`. -/
theorem exists_inv_factor (T Tinv : Module.End ℂ M) (h1 : Tinv * T = 1) (h2 : T * Tinv = 1)
    (m K : ℕ) (hK : 0 < K) (hnil : (T - 1) ^ m = 0) :
    ∃ Q : Module.End ℂ M, Tinv - 1 = Q * (T ^ K - 1) ∧
      ∀ S : Module.End ℂ M, S * T = T * S → S * Q = Q * S := by
  obtain ⟨u, v, huv⟩ := (isCoprime_sub_one_geom K hK).pow_left (m := m)
  have hgeom : (∑ i ∈ Finset.range K, (X : ℂ[X]) ^ i) * (X - 1) = X ^ K - 1 := geom_sum_mul X K
  have hpoly : (X - 1 : ℂ[X]) = u * (X - 1) ^ (m + 1) + v * (X ^ K - 1) := by
    rw [← hgeom, pow_succ]
    linear_combination (1 - X : ℂ[X]) * huv
  have key := congrArg (aeval T) hpoly
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_one] at key
  have hz : (T - 1) ^ (m + 1) = 0 := by rw [pow_succ, hnil, zero_mul]
  rw [hz, mul_zero, zero_add] at key
  refine ⟨-(Tinv * aeval T v), ?_, ?_⟩
  · have e : Tinv - 1 = -(Tinv * (T - 1)) := by
      rw [mul_sub, h1, mul_one]
      abel
    rw [e, key, neg_mul, mul_assoc]
  · intro S hS
    have hSinv : S * Tinv = Tinv * S := by
      calc S * Tinv = (Tinv * T) * S * Tinv := by rw [h1, one_mul]
        _ = Tinv * (T * S) * Tinv := by simp only [mul_assoc]
        _ = Tinv * (S * T) * Tinv := by rw [hS]
        _ = Tinv * S * (T * Tinv) := by simp only [mul_assoc]
        _ = Tinv * S := by rw [h2, mul_one]
    have c1 : Commute S Tinv := hSinv
    have c2 : Commute S (aeval T v) := commute_aeval (f := T) hS v
    exact (c1.mul_right c2).neg_right

end Factor

variable {L M V H : Type} [CommGroup L] [Group M] [AddCommGroup V] [Module ℂ V] [Group H]

/-- **Class constancy of a rational translation family on `L ⋊ M`.** -/
theorem translation_class_eq (action : M →* MulAut L) (ρ : Representation ℂ H V)
    (ι : SemidirectProduct L M action →* H) (h : H)
    (φ : SemidirectProduct L M action →* SemidirectProduct L M action)
    (hφι : ∀ g, ι (φ g) = h * ι g * h⁻¹)
    (φ_inl : ∀ ℓ, φ (SemidirectProduct.inl ℓ) = SemidirectProduct.inl ℓ)
    (φ_right : ∀ g, (φ g).right = g.right)
    (ℓ₀ : L) (K : ℕ) (hK : 0 < K) (hℓ₀ : ι (SemidirectProduct.inl ℓ₀) = h ^ K)
    (hcomm : ∀ ℓ, ι (SemidirectProduct.inl ℓ) * h = h * ι (SemidirectProduct.inl ℓ))
    (nil : ∃ m : ℕ, (ρ h - 1) ^ m = 0)
    (C : ℤ → (Fin 3 → H) → V)
    (cocycle : ∀ k (x : Fin 4 → H), C k ![x 1, x 2, x 3] - C k ![x 0, x 2, x 3] +
      C k ![x 0, x 1, x 3] - C k ![x 0, x 1, x 2] = 0)
    (shift : ∀ k x, C k (fun i => h * x i) = ρ h (C (k + 1) x))
    (equiv : ∀ k (g : SemidirectProduct L M action) x,
      C k (fun i => ι g * x i) = ρ (ι g) (C k x))
    (period : ∀ x, C K x = C 0 x) :
    ∃ τ : SemidirectProduct L M action → V, ∀ a b : SemidirectProduct L M action,
      C 1 ![1, ι a, ι a * ι b] - C 0 ![1, ι a, ι a * ι b] =
        ρ (ι a) (τ b) - τ (a * b) + τ a := by
  obtain ⟨m, hm⟩ := nil
  set ρG : Representation ℂ (SemidirectProduct L M action) V := ρ.comp ι
  have hρGapp : ∀ g v, ρG g v = ρ (ι g) v := fun g v => rfl
  have hinv1 : ρ h⁻¹ * ρ h = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv2 : ρ h * ρ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨Q, hQ, hQcomm⟩ := exists_inv_factor (ρ h) (ρ h⁻¹) hinv1 hinv2 m K hK hm
  let T : TwistData action ρG :=
    { φ := φ
      A := ρ h⁻¹
      ℓ₀ := ℓ₀
      Q := Q
      φ_inl := φ_inl
      φ_right := φ_right
      compat := by
        intro g v
        rw [hρGapp, hρGapp, hφι, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply,
          ← map_mul]
        congr 2
        group
      factor := by
        intro v
        have e := congrArg (fun F : Module.End ℂ V => F v) hQ
        simp only [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply] at e
        rw [hρGapp, hℓ₀, map_pow]
        exact e
      Q_comm := by
        intro ℓ v
        have hS : ρ (ι (SemidirectProduct.inl ℓ)) * ρ h = ρ h * ρ (ι (SemidirectProduct.inl ℓ)) := by
          rw [← map_mul, ← map_mul, hcomm]
        have e := congrArg (fun F : Module.End ℂ V => F v)
          (hQcomm (ρ (ι (SemidirectProduct.inl ℓ))) hS)
        have e' : ρ (ι (SemidirectProduct.inl ℓ)) (Q v) = Q (ρ (ι (SemidirectProduct.inl ℓ)) v) := by
          simpa only [Module.End.mul_apply] using e
        exact e'.symm }
  have hA : ∀ g v, T.A (ρG (T.φ g) v) = ρG g (T.A v) := T.compat
  have coc4 : ∀ k (a b c d : H), C k ![b, c, d] - C k ![a, c, d] + C k ![a, b, d] -
      C k ![a, b, c] = 0 := fun k a b c d => cocycle k ![a, b, c, d]
  have shift' : ∀ k x, C (k + 1) x = ρ h⁻¹ (C k (fun i => h * x i)) := by
    intro k x
    rw [shift, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hCeq : ∀ k (g : SemidirectProduct L M action) (a b c : H),
      C k ![ι g * a, ι g * b, ι g * c] = ρ (ι g) (C k ![a, b, c]) := by
    intro k g a b c
    have e := equiv k g ![a, b, c]
    have ht : (fun i => ι g * (![a, b, c] : Fin 3 → H) i) = ![ι g * a, ι g * b, ι g * c] := by
      funext i; fin_cases i <;> rfl
    rwa [ht] at e
  let ω : ℤ → SemidirectProduct L M action → SemidirectProduct L M action → V :=
    fun k a b => C k ![1, ι a, ι a * ι b]
  have hωc : ∀ k, IsCocycle2 ρG (ω k) := by
    intro k a b c
    have e := coc4 k 1 (ι a) (ι a * ι b) (ι a * ι b * ι c)
    have e1 : ρG a (ω k b c) = C k ![ι a, ι a * ι b, ι a * ι b * ι c] := by
      change ρ (ι a) (C k ![1, ι b, ι b * ι c]) = _
      rw [← hCeq]
      simp only [mul_one, mul_assoc]
    have e2 : ω k (a * b) c = C k ![1, ι a * ι b, ι a * ι b * ι c] := by
      simp only [ω, map_mul]
    have e3 : ω k a (b * c) = C k ![1, ι a, ι a * ι b * ι c] := by
      simp only [ω, map_mul, mul_assoc]
    rw [e1, e2, e3]
    exact e
  let σ : ℤ → SemidirectProduct L M action → V := fun k a =>
    C k ![1, h, ι a * h] - C k ![1, ι a, ι a * h]
  have prism : ∀ k (a b : SemidirectProduct L M action),
      ρG a (σ k b) - σ k (a * b) + σ k a = C k ![h, ι a * h, ι a * ι b * h] - ω k a b := by
    intro k a b
    have i1 := coc4 k 1 h (ι a * h) (ι a * ι b * h)
    have i2 := coc4 k 1 (ι a) (ι a * h) (ι a * ι b * h)
    have i3 := coc4 k 1 (ι a) (ι a * ι b) (ι a * ι b * h)
    have e1 : ρG a (σ k b) = C k ![ι a, ι a * h, ι a * ι b * h] -
        C k ![ι a, ι a * ι b, ι a * ι b * h] := by
      change ρ (ι a) (C k ![1, h, ι b * h] - C k ![1, ι b, ι b * h]) = _
      rw [map_sub, ← hCeq, ← hCeq]
      simp only [mul_one, mul_assoc]
    have e2 : σ k (a * b) = C k ![1, h, ι a * ι b * h] - C k ![1, ι a * ι b, ι a * ι b * h] := by
      simp only [σ, map_mul]
    rw [e1, e2]
    simp only [σ, ω]
    linear_combination (norm := abel) i2 - i3 - i1
  set f := pull2 T.φ T.A
  set B := LinearMap.range (dρ ρG)
  have hBf : ∀ x ∈ B, f x ∈ B := by
    rintro _ ⟨τ, rfl⟩
    exact ⟨pull1 T.φ T.A τ, (pull2_dρ hA τ).symm⟩
  have hstep : ∀ k, ω (k + 1) - f (ω k) = dρ ρG (pull1 T.φ T.A (σ k)) := by
    intro k
    funext a b
    have hp := prism k (T.φ a) (T.φ b)
    rw [Pi.sub_apply, Pi.sub_apply, dρ_apply, pull1_apply, pull1_apply, pull1_apply, ← hA,
      map_mul, ← map_sub, ← map_add, hp]
    change C (k + 1) ![1, ι a, ι a * ι b] -
        ρ h⁻¹ (C k ![1, ι (φ a), ι (φ a) * ι (φ b)]) =
      ρ h⁻¹ (C k ![h, ι (φ a) * h, ι (φ a) * ι (φ b) * h] -
        C k ![1, ι (φ a), ι (φ a) * ι (φ b)])
    rw [shift', map_sub, hφι, hφι]
    have ht : (fun i => h * (![1, ι a, ι a * ι b] : Fin 3 → H) i) =
        ![h, h * ι a * h⁻¹ * h, h * ι a * h⁻¹ * (h * ι b * h⁻¹) * h] := by
      funext i
      fin_cases i <;> simp [mul_assoc]
    rw [ht]
  have hiter : ∀ j : ℕ, (f ^ j) (ω 0) - ω j ∈ B := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (f ^ (j + 1)) (ω 0) - ω ((j + 1 : ℕ) : ℤ) =
          f ((f ^ j) (ω 0) - ω j) - (ω ((j : ℤ) + 1) - f (ω j)) := by
        rw [pow_succ', Module.End.mul_apply, map_sub]
        push_cast
        abel
      rw [e, hstep]
      exact B.sub_mem (hBf _ ih) ⟨_, rfl⟩
  have hper : (f ^ K) (ω 0) - ω 0 ∈ B := by
    have hK' : ω K = ω 0 := by
      funext a b
      exact period _
    have := hiter K
    rwa [hK'] at this
  have hfix0 : f (ω 0) - ω 0 ∈ B := T.sub_mem_range_of_periodic (hωc 0) K hK hper
  have hmem : ω 1 - ω 0 ∈ B := by
    have e : ω 1 - ω 0 = (ω (0 + 1) - f (ω 0)) + (f (ω 0) - ω 0) := by
      simp only [zero_add]
      abel
    rw [e, hstep]
    exact B.add_mem ⟨_, rfl⟩ hfix0
  obtain ⟨τ, hτ⟩ := hmem
  refine ⟨τ, fun a b => ?_⟩
  have e := congrFun (congrFun hτ a) b
  rw [dρ_apply] at e
  exact e.symm

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
