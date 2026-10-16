module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.FilteredUnipotence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Kernel

@[expose] public section


/-!
# Twisted pullbacks on semidirect products act trivially on second cohomology

Let `G = L ⋊ M` with `L` abelian and let `V` be a `G`-module. Let `φ` be an endomorphism of `G`
fixing `L` pointwise and inducing the identity on `M = G / L`, and let `A` be a compatible
coefficient map, `A ∘ ρ(φ g) = ρ(g) ∘ A`, commuting with `ρ(L)`. Suppose `A - 1` factors as
`Q ∘ (ρ(ℓ₀) - 1)` for some `ℓ₀ ∈ L` and some `Q` commuting with `ρ(L)`; this is the situation of
conjugation by a rational point `v` of the radical with `ℓ₀ = N v`.

Then the twisted pullback `α ω (a, b) = A (ω (φ a) (φ b))` satisfies `(α - 1)³ ω ∈ B²` for every
2-cocycle `ω`: `α - 1` maps cocycles into those vanishing on `L × L`, these into the kernel of
the mixed class (by a direct computation of the mixed crossed cochain of `α η`), hence into the
classes inflated from `H²(M, V^L)` (Sol's exactness `radicalKernelMixedMap_zero_iff_mem_inflation`),
on which `α` is the identity. If moreover `α^K ω - ω ∈ B²` for some `K > 0`, then
`α ω - ω ∈ B²`.

Written by AxiomCode.
-/

open TernaryPeriodPolynomials.FlagExactness.FilteredUnipotence
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

section Central

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- A central element acts trivially on second cohomology, with explicit primitive. -/
theorem central_twist_boundary {ω : G → G → V} (hω : IsCocycle2 ρ ω) (z a b : G)
    (ha : a * z = z * a) (hb : b * z = z * b) :
    ρ z (ω a b) - ω a b =
      ρ a (ω z b - ω b z) - (ω z (a * b) - ω (a * b) z) + (ω z a - ω a z) := by
  have h1 := hω z a b
  have h2 := hω a z b
  have h3 := hω a b z
  rw [ha] at h2
  rw [hb] at h3
  rw [map_sub]
  linear_combination (norm := abel) h1 - h2 + h3

/-- A central element acts trivially on first cohomology: for a crossed homomorphism `κ`,
`ρ(z) κ(a) - κ(a) = ρ(a) κ(z) - κ(z)`. -/
theorem central_crossed (κ : G → V)
    (hκ : ∀ a b, κ (a * b) = κ a + ρ a (κ b)) (z a : G) (ha : a * z = z * a) :
    ρ z (κ a) - κ a = ρ a (κ z) - κ z := by
  have h1 := hκ z a
  have h2 := hκ a z
  rw [ha] at h2
  rw [h1] at h2
  linear_combination (norm := abel) h2

end Central

variable {L M V : Type} [CommGroup L] [Group M] [AddCommGroup V] [Module ℂ V]
  (action : M →* MulAut L) (ρ : Representation ℂ (SemidirectProduct L M action) V)

local notation "G" => SemidirectProduct L M action

theorem inl_comm (ℓ ℓ' : L) :
    (SemidirectProduct.inl ℓ : G) * SemidirectProduct.inl ℓ' =
      SemidirectProduct.inl ℓ' * SemidirectProduct.inl ℓ := by
  rw [← map_mul, ← map_mul, mul_comm]

/-- The data of a twisted pullback: an endomorphism `φ` of `L ⋊ M` fixing `L` and inducing the
identity on `M`, and a compatible coefficient map `A` with `A - 1 = Q ∘ (ρ(ℓ₀) - 1)`. -/
structure TwistData where
  /-- The endomorphism of the group. -/
  φ : G →* G
  /-- The coefficient map. -/
  A : V →ₗ[ℂ] V
  /-- The element of `L` through which `A - 1` factors. -/
  ℓ₀ : L
  /-- The factor commuting with `ρ(L)`. -/
  Q : V →ₗ[ℂ] V
  φ_inl : ∀ ℓ, φ (SemidirectProduct.inl ℓ) = SemidirectProduct.inl ℓ
  φ_right : ∀ g, (φ g).right = g.right
  compat : ∀ g v, A (ρ (φ g) v) = ρ g (A v)
  factor : ∀ v, A v - v = Q (ρ (SemidirectProduct.inl ℓ₀) v - v)
  Q_comm : ∀ ℓ v, Q (ρ (SemidirectProduct.inl ℓ) v) = ρ (SemidirectProduct.inl ℓ) (Q v)

namespace TwistData

variable {action ρ} (T : TwistData action ρ)

theorem A_comm (ℓ : L) (v : V) :
    T.A (ρ (SemidirectProduct.inl ℓ) v) = ρ (SemidirectProduct.inl ℓ) (T.A v) := by
  have h := T.compat (SemidirectProduct.inl ℓ) v
  rwa [T.φ_inl] at h

theorem A_fix (v : V) (hv : ∀ ℓ : L, ρ (SemidirectProduct.inl ℓ) v = v) : T.A v = v := by
  have h := T.factor v
  rw [hv, sub_self, map_zero] at h
  exact sub_eq_zero.mp h

theorem ρ_inl_comm (ℓ ℓ' : L) (v : V) :
    ρ (SemidirectProduct.inl ℓ) (ρ (SemidirectProduct.inl ℓ') v) =
      ρ (SemidirectProduct.inl ℓ') (ρ (SemidirectProduct.inl ℓ) v) := by
  rw [← Module.End.mul_apply, ← map_mul, inl_comm, map_mul, Module.End.mul_apply]

/-- Step A: after subtracting a coboundary, `(α - 1) ω` vanishes on `L × L`. -/
theorem exists_radical_correction {ω : G → G → V} (hω : IsCocycle2 ρ ω) :
    ∃ τ : G → V, ∀ a b : L,
      (((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ω) - dρ ρ τ)
        (SemidirectProduct.inl a) (SemidirectProduct.inl b) = 0 := by
  classical
  let τL : L → V := fun ℓ =>
    T.Q (ω (SemidirectProduct.inl T.ℓ₀) (SemidirectProduct.inl ℓ) -
      ω (SemidirectProduct.inl ℓ) (SemidirectProduct.inl T.ℓ₀))
  refine ⟨fun g => if g.right = 1 then τL g.left else 0, fun a b => ?_⟩
  have key := central_twist_boundary ρ hω (SemidirectProduct.inl T.ℓ₀) (SemidirectProduct.inl a)
    (SemidirectProduct.inl b) (inl_comm action a T.ℓ₀) (inl_comm action b T.ℓ₀)
  have e : (SemidirectProduct.inl a : G) * SemidirectProduct.inl b =
      SemidirectProduct.inl (a * b) :=
    (map_mul (SemidirectProduct.inl : L →* G) a b).symm
  rw [e] at key
  have hA : T.A (ω (SemidirectProduct.inl a) (SemidirectProduct.inl b)) -
      ω (SemidirectProduct.inl a) (SemidirectProduct.inl b) =
        ρ (SemidirectProduct.inl a) (τL b) - τL (a * b) + τL a := by
    rw [T.factor, key]
    simp only [τL, map_sub, map_add, T.Q_comm]
  have hτ : ∀ ℓ : L, (if (SemidirectProduct.inl ℓ : G).right = 1 then
      τL (SemidirectProduct.inl ℓ : G).left else 0) = τL ℓ := by
    intro ℓ
    simp
  simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull2_apply, T.φ_inl,
    dρ_apply, e, hτ]
  linear_combination (norm := abel) hA

/-- The crossed coboundary datum of the mixed cochain of `(α - 1) η`. -/
def mixedKappa (η : G → G → V) (m : M) (ℓ : L) : V :=
  η (SemidirectProduct.inr m) (SemidirectProduct.inl (action m⁻¹ ℓ)) -
    η (SemidirectProduct.inl ℓ) (SemidirectProduct.inr m)

/-- The translation part `λ_m` of `φ (m)`. -/
def lam (m : M) : L := (T.φ (SemidirectProduct.inr m)).left

theorem φ_inr (m : M) : T.φ (SemidirectProduct.inr m) =
    SemidirectProduct.inl (T.lam m) * SemidirectProduct.inr m := by
  have h := semidirect_factorization action (T.φ (SemidirectProduct.inr m))
  rw [T.φ_right, SemidirectProduct.right_inr] at h
  exact h

/-- The primitive of the mixed cochain of `(α - 1) η`. -/
def mixedW (η : G → G → V) (m : M) : V :=
  mixedKappa (action := action) η m (T.lam m) +
    T.Q (ρ (SemidirectProduct.inl (T.lam m)) (mixedKappa (action := action) η m T.ℓ₀)) +
    T.A (η (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inr m))

theorem sub_one_isCocycle {ω : G → G → V} (hω : IsCocycle2 ρ ω) :
    IsCocycle2 ρ ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ω) := by
  simpa using sub_one_pow_isCocycle T.compat 1 hω

/-- The mixed formula: the mixed cochain of `(α - 1) η` is a crossed coboundary on `L`. -/
theorem mixed_formula {η : G → G → V} (hη : IsCocycle2 ρ η)
    (hη0 : ∀ a b : L, η (SemidirectProduct.inl a) (SemidirectProduct.inl b) = 0) (m : M) (ℓ : L) :
    ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) η) (SemidirectProduct.inr m)
        (SemidirectProduct.inl (action m⁻¹ ℓ)) -
      ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) η) (SemidirectProduct.inl ℓ)
        (SemidirectProduct.inr m) =
      ρ (SemidirectProduct.inl ℓ) (T.mixedW η m) - T.mixedW η m := by
  have hxe := semidirect_conjugation_intertwines action m ℓ
  have hφx := T.φ_inr m
  have c1 := hη (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inr m)
    (SemidirectProduct.inl (action m⁻¹ ℓ))
  have c2 := hη (SemidirectProduct.inl ℓ) (SemidirectProduct.inl (T.lam m))
    (SemidirectProduct.inr m)
  have c3 := hη (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inl ℓ)
    (SemidirectProduct.inr m)
  rw [hxe] at c1
  rw [inl_comm action (T.lam m) ℓ, hη0 (T.lam m) ℓ] at c3
  rw [hη0 ℓ (T.lam m)] at c2
  -- crossed cocycle property of the mixed cochain
  let η' : radicalZeroTwoCycles action ρ := ⟨⟨η, hη⟩, hη0⟩
  have hκ : ∀ a b : L, mixedKappa (action := action) η m (a * b) =
      mixedKappa (action := action) η m a +
        ρ (SemidirectProduct.inl a) (mixedKappa (action := action) η m b) :=
    fun a b => mixedCrossedCochain_cocycle action ρ η' m a b
  have s1 : ρ (SemidirectProduct.inl (T.lam m))
        (η (SemidirectProduct.inr m) (SemidirectProduct.inl (action m⁻¹ ℓ)) -
          η (SemidirectProduct.inl ℓ) (SemidirectProduct.inr m)) -
      (η (SemidirectProduct.inr m) (SemidirectProduct.inl (action m⁻¹ ℓ)) -
        η (SemidirectProduct.inl ℓ) (SemidirectProduct.inr m)) =
      ρ (SemidirectProduct.inl ℓ) (mixedKappa (action := action) η m (T.lam m)) -
        mixedKappa (action := action) η m (T.lam m) :=
    central_crossed (ρ.comp SemidirectProduct.inl) (mixedKappa (action := action) η m) hκ
      (T.lam m) ℓ (mul_comm _ _)
  have s0 : ρ (SemidirectProduct.inl T.ℓ₀) (mixedKappa (action := action) η m ℓ) -
      mixedKappa (action := action) η m ℓ =
      ρ (SemidirectProduct.inl ℓ) (mixedKappa (action := action) η m T.ℓ₀) -
        mixedKappa (action := action) η m T.ℓ₀ :=
    central_crossed (ρ.comp SemidirectProduct.inl) (mixedKappa (action := action) η m) hκ
      T.ℓ₀ ℓ (mul_comm _ _)
  have s2 : T.A (ρ (SemidirectProduct.inl (T.lam m)) (mixedKappa (action := action) η m ℓ)) -
      ρ (SemidirectProduct.inl (T.lam m)) (mixedKappa (action := action) η m ℓ) =
      ρ (SemidirectProduct.inl ℓ)
          (T.Q (ρ (SemidirectProduct.inl (T.lam m)) (mixedKappa (action := action) η m T.ℓ₀))) -
        T.Q (ρ (SemidirectProduct.inl (T.lam m)) (mixedKappa (action := action) η m T.ℓ₀)) := by
    have hq := T.Q_comm ℓ (ρ (SemidirectProduct.inl (T.lam m))
      (mixedKappa (action := action) η m T.ℓ₀))
    rw [T.factor, ρ_inl_comm T.ℓ₀ (T.lam m), ← map_sub, s0, map_sub, map_sub,
      ρ_inl_comm (T.lam m) ℓ, hq]
  have hAcomm := T.A_comm ℓ (η (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inr m))
  have e1 : η (SemidirectProduct.inl (T.lam m) * SemidirectProduct.inr m)
        (SemidirectProduct.inl (action m⁻¹ ℓ)) =
      ρ (SemidirectProduct.inl (T.lam m))
          (η (SemidirectProduct.inr m) (SemidirectProduct.inl (action m⁻¹ ℓ))) +
        η (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inl ℓ * SemidirectProduct.inr m) -
        η (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inr m) := by
    linear_combination (norm := abel) -c1
  have e2 : η (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inl ℓ * SemidirectProduct.inr m) =
      η (SemidirectProduct.inl ℓ * SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inr m) -
        ρ (SemidirectProduct.inl (T.lam m))
          (η (SemidirectProduct.inl ℓ) (SemidirectProduct.inr m)) := by
    linear_combination (norm := abel) c3
  have e3 : η (SemidirectProduct.inl ℓ) (SemidirectProduct.inl (T.lam m) * SemidirectProduct.inr m) =
      η (SemidirectProduct.inl ℓ * SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inr m) -
        ρ (SemidirectProduct.inl ℓ)
          (η (SemidirectProduct.inl (T.lam m)) (SemidirectProduct.inr m)) := by
    linear_combination (norm := abel) c2
  simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull2_apply, T.φ_inl,
    hφx]
  rw [e1, e2, e3]
  unfold TwistData.mixedW
  have hk : mixedKappa (action := action) η m ℓ =
      η (SemidirectProduct.inr m) (SemidirectProduct.inl (action m⁻¹ ℓ)) -
        η (SemidirectProduct.inl ℓ) (SemidirectProduct.inr m) := rfl
  rw [hk] at s2
  simp only [map_sub, map_add] at s2 s1 ⊢
  linear_combination (norm := abel) s2 + s1 + hAcomm

/-- The radical-zero cycle `(α - 1) η`. -/
def twistCycle {η : G → G → V} (hη : IsCocycle2 ρ η)
    (hη0 : ∀ a b : L, η (SemidirectProduct.inl a) (SemidirectProduct.inl b) = 0) :
    radicalZeroTwoCycles action ρ :=
  ⟨⟨(pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) η, T.sub_one_isCocycle hη⟩, by
    intro a b
    change ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) η) (SemidirectProduct.inl a)
      (SemidirectProduct.inl b) = 0
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull2_apply, T.φ_inl,
      hη0, map_zero, sub_self]⟩

theorem twistCycle_mixedClass_zero {η : G → G → V} (hη : IsCocycle2 ρ η)
    (hη0 : ∀ a b : L, η (SemidirectProduct.inl a) (SemidirectProduct.inl b) = 0) :
    mixedClassMap action ρ (T.twistCycle hη hη0) = 0 := by
  have mixedZero : mixedH1CocycleMap action ρ (T.twistCycle hη hη0) = 0 := by
    apply Subtype.ext
    funext m
    change (crossedBoundaries (ρ.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action ρ m (T.twistCycle hη hη0)) = 0
    refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨T.mixedW η m, ?_⟩
    apply Subtype.ext
    funext ℓ
    exact (T.mixed_formula hη hη0 m ℓ).symm
  change (crossedBoundaries (leviCrossedH1Representation action ρ)).mkQ
    (mixedH1CocycleMap action ρ (T.twistCycle hη hη0)) = 0
  rw [mixedZero, map_zero]

/-- Step C: for a cocycle vanishing on `L × L`, `(α - 1)² η` is a coboundary. -/
theorem sub_one_sq_mem_range {η : G → G → V} (hη : IsCocycle2 ρ η)
    (hη0 : ∀ a b : L, η (SemidirectProduct.inl a) (SemidirectProduct.inl b) = 0) :
    ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ^ 2) η ∈ LinearMap.range (dρ ρ) := by
  obtain ⟨c, hc⟩ := mixedClass_zero_mem_inflation action ρ (T.twistCycle hη hη0)
    (T.twistCycle_mixedClass_zero hη hη0)
  obtain ⟨θ, rfl⟩ := (inhomogeneousBoundaries
    (semidirectInvariantRepresentation action ρ)).mkQ_surjective c
  change (inhomogeneousBoundaries ρ).mkQ (semidirectInflationCycles action ρ θ) =
    (inhomogeneousBoundaries ρ).mkQ (T.twistCycle hη hη0).val at hc
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hc
  obtain ⟨τ, hτ⟩ := (Submodule.Quotient.eq _).mp hc
  have hζ : (pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) η =
      (fun a b : G => ((θ.val a.right b.right : semidirectRadicalInvariants action ρ) : V))
        - dρ ρ τ := by
    funext a b
    have h := congrFun (congrFun (congrArg Subtype.val hτ) a) b
    change ρ a (τ b) - τ (a * b) + τ a =
      (θ.val a.right b.right).val - ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) η) a b at h
    change _ = (θ.val a.right b.right).val - (ρ a (τ b) - τ (a * b) + τ a)
    rw [h]
    abel
  have hι : (pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V))
      (fun a b : G => ((θ.val a.right b.right : semidirectRadicalInvariants action ρ) : V))
        = 0 := by
    funext a b
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, pull2_apply, T.φ_right,
      Pi.zero_apply]
    rw [T.A_fix (θ.val a.right b.right).val (θ.val a.right b.right).property, sub_self]
  refine ⟨-(((pull1 T.φ T.A - 1 : Module.End ℂ (G → V)) τ)), ?_⟩
  rw [pow_two, Module.End.mul_apply, hζ, map_sub, hι, zero_sub]
  have h := sub_one_pow_dρ T.compat 1 τ
  simp only [pow_one] at h
  rw [h, map_neg]

/-- **The twisted pullback is cubically unipotent on second cohomology.** -/
theorem cube_mem_range {ω : G → G → V} (hω : IsCocycle2 ρ ω) :
    ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ^ 3) ω ∈ LinearMap.range (dρ ρ) := by
  obtain ⟨τ, hτ⟩ := T.exists_radical_correction hω
  have hηc : IsCocycle2 ρ
      (((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ω) - dρ ρ τ) := by
    intro a b c
    have h1 := T.sub_one_isCocycle hω a b c
    have h2 := dρ_isCocycle ρ τ a b c
    simp only [Pi.sub_apply, map_sub] at h1 h2 ⊢
    linear_combination (norm := abel) h1 - h2
  have hmem := T.sub_one_sq_mem_range hηc hτ
  have hd := sub_one_pow_dρ T.compat 2 τ
  have hsplit : ((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ω) =
      (((pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ω) - dρ ρ τ) + dρ ρ τ := by abel
  have h3 : (pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ^ 3 =
      (pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) ^ 2 *
        (pull2 T.φ T.A - 1 : Module.End ℂ (G → G → V)) := pow_succ _ 2
  rw [h3, Module.End.mul_apply, hsplit, map_add]
  exact Submodule.add_mem _ hmem ⟨_, hd.symm⟩

/-- If `α^K ω - ω` is a coboundary for some `K > 0`, so is `α ω - ω`. -/
theorem sub_mem_range_of_periodic {ω : G → G → V} (hω : IsCocycle2 ρ ω) (K : ℕ) (hK : 0 < K)
    (hper : ((pull2 T.φ T.A) ^ K) ω - ω ∈ LinearMap.range (dρ ρ)) :
    pull2 T.φ T.A ω - ω ∈ LinearMap.range (dρ ρ) := by
  have hB : ∀ x ∈ LinearMap.range (dρ ρ), pull2 T.φ T.A x ∈ LinearMap.range (dρ ρ) := by
    rintro _ ⟨τ, rfl⟩
    exact ⟨pull1 T.φ T.A τ, (pull2_dρ T.compat τ).symm⟩
  exact sub_mem_of_unipotent_periodic (pull2 T.φ T.A) _ hB ω 3 K hK
    (T.cube_mem_range hω) hper

end TwistData

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
