module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.Compression

@[expose] public section


/-!
# Gelfand's trick for finite double cosets

Let `ι` be an involutive anti-automorphism of a group `G` preserving a subgroup `K`. For
bi-`K`-invariant `φ` and double cosets `K g K = ⊔ rᵢ K`, `K h K = ⊔ sⱼ K` with `ι g ∈ K g K` and
`ι h ∈ K h K`, double counting `Σᵢⱼ φ(ι(sⱼ) rᵢ)` gives

`#(KhK/K) · Σᵢ φ(h rᵢ) = #(KgK/K) · Σⱼ φ(g sⱼ)`.

Applied to matrix coefficients `φ(x) = ⟪π(x) v, w⟫` of `K`-fixed vectors, this makes the
compressions `C_g` and `C_h` commute. No Haar measure is used.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.RepresentationTheory

section Abstract

variable {G : Type*} [Group G] {K : Subgroup G}

/-- Left multiplication by `k ∈ K` permutes the left cosets of a double coset. -/
theorem DoubleCoset.sum_left_mul (T : DoubleCoset K) {M : Type*} [AddCommMonoid M] (φ : G → M)
    (hφ : ∀ x (k : K), φ (x * k.val) = φ x) (x : G) (k : K) :
    ∑ r ∈ T.reps, φ (x * (k.val * r)) = ∑ r ∈ T.reps, φ (x * r) := by
  classical
  choose! ψ hψ hψK using fun r (hr : r ∈ T.reps) => T.exists_rep k r hr
  have hterm : ∀ r ∈ T.reps, φ (x * (k.val * r)) = φ (x * ψ r) := by
    intro r hr
    have := hφ (x * ψ r) ⟨_, hψK r hr⟩
    simpa [mul_assoc] using this
  rw [Finset.sum_congr rfl hterm]
  have hinj : Set.InjOn ψ T.reps := by
    intro r₁ h₁ r₂ h₂ heq
    apply T.disjoint r₁ h₁ r₂ h₂
    have m₁ := hψK r₁ h₁
    have m₂ := hψK r₂ h₂
    rw [heq] at m₁
    have := K.mul_mem (K.inv_mem m₁) m₂
    simpa [mul_assoc] using this
  have hsurj : Set.SurjOn ψ T.reps T.reps := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le (fun r _ => ψ r)
      (fun r hr => hψ r hr) (fun a b ha hb h => hinj ha hb h) le_rfl b hb
    exact ⟨a, ha, hab.symm⟩
  exact Finset.sum_nbij ψ hψ hinj hsurj (fun _ _ => rfl)

/-- The data of Gelfand's trick: an involutive anti-automorphism preserving `K`. -/
structure GelfandInvolution (K : Subgroup G) where
  ι : G → G
  map_mul : ∀ x y, ι (x * y) = ι y * ι x
  invol : ∀ x, ι (ι x) = x
  mem : ∀ k ∈ K, ι k ∈ K
  /-- the subgroup on which the Cartan property holds -/
  F : Subgroup G
  le : K ≤ F
  memF : ∀ x ∈ F, ι x ∈ F
  cartan : ∀ x ∈ F, ∃ a b : K, ι x = a.val * x * b.val

variable (J : GelfandInvolution K)

theorem GelfandInvolution.sum_right_mul (T : DoubleCoset K) {M : Type*} [AddCommMonoid M]
    (φ : G → M) (hφ : ∀ x (k : K), φ (k.val * x) = φ x) (x : G) (k : K) :
    ∑ s ∈ T.reps, φ (J.ι s * (k.val * x)) = ∑ s ∈ T.reps, φ (J.ι s * x) := by
  have hφι : ∀ y (k : K), (φ ∘ J.ι) (y * k.val) = (φ ∘ J.ι) y := by
    intro y k
    simp only [Function.comp, J.map_mul]
    exact hφ _ ⟨_, J.mem k.val k.property⟩
  have key := T.sum_left_mul (φ ∘ J.ι) hφι (J.ι x) ⟨_, J.mem k.val k.property⟩
  have e1 : ∀ s, (φ ∘ J.ι) (J.ι x * (J.ι k.val * s)) = φ (J.ι s * (k.val * x)) := by
    intro s
    simp only [Function.comp, J.map_mul, J.invol, mul_assoc]
  have e2 : ∀ s, (φ ∘ J.ι) (J.ι x * s) = φ (J.ι s * x) := by
    intro s
    simp only [Function.comp, J.map_mul, J.invol]
  simp only [e1, e2] at key
  exact key

/-- **Gelfand's identity.** -/
theorem GelfandInvolution.identity (Tg Th : DoubleCoset K) {M : Type*} [AddCommMonoid M]
    (φ : G → M) (hl : ∀ x (k : K), φ (k.val * x) = φ x) (hr : ∀ x (k : K), φ (x * k.val) = φ x)
    (hgF : Tg.g ∈ J.F) (hhF : Th.g ∈ J.F) :
    Th.reps.card • ∑ r ∈ Tg.reps, φ (Th.g * r) = Tg.reps.card • ∑ s ∈ Th.reps, φ (Tg.g * s) := by
  have hφι : ∀ y ∈ J.F, φ (J.ι y) = φ y := by
    intro y hy
    obtain ⟨a, b, hab⟩ := J.cartan y hy
    rw [hab, hr, hl]
  have hg := J.cartan _ hgF
  have hh := J.cartan _ hhF
  -- the double sum `Σ_{s, r} φ(ι s * r)` computed in two ways
  have rows : ∀ s ∈ Th.reps, ∑ r ∈ Tg.reps, φ (J.ι s * r) = ∑ r ∈ Tg.reps, φ (Th.g * r) := by
    intro s hs
    obtain ⟨a, b, rfl⟩ := Th.inDouble s hs
    obtain ⟨c, d, hcd⟩ := hh
    have hι : J.ι (a.val * Th.g * b.val) =
        (J.ι b.val * c.val) * Th.g * (d.val * J.ι a.val) := by
      rw [J.map_mul, J.map_mul, hcd]; group
    have hb : J.ι b.val * c.val ∈ K := K.mul_mem (J.mem _ b.property) c.property
    have hd : d.val * J.ι a.val ∈ K := K.mul_mem d.property (J.mem _ a.property)
    have step1 : ∀ r, φ (J.ι (a.val * Th.g * b.val) * r) = φ (Th.g * ((d.val * J.ι a.val) * r)) := by
      intro r
      rw [hι]
      have := hl (Th.g * ((d.val * J.ι a.val) * r)) ⟨_, hb⟩
      rw [← this]
      congr 1
      group
    rw [Finset.sum_congr rfl (fun r _ => step1 r)]
    exact Tg.sum_left_mul φ hr Th.g ⟨_, hd⟩
  have cols : ∀ r ∈ Tg.reps, ∑ s ∈ Th.reps, φ (J.ι s * r) = ∑ s ∈ Th.reps, φ (Tg.g * s) := by
    intro r hr'
    obtain ⟨a, b, rfl⟩ := Tg.inDouble r hr'
    have s1 : ∀ s, φ (J.ι s * (a.val * Tg.g * b.val)) = φ (J.ι s * (a.val * Tg.g)) := by
      intro s
      have := hr (J.ι s * (a.val * Tg.g)) b
      rw [← this]
      congr 1
      group
    rw [Finset.sum_congr rfl (fun s _ => s1 s), J.sum_right_mul Th φ hl Tg.g a]
    obtain ⟨c, d, hcd⟩ := hg
    have s2 : ∀ s ∈ Th.reps, φ (J.ι s * Tg.g) = φ (Tg.g * (d.val * s)) := by
      intro s hs
      have hsF : s ∈ J.F := by
        obtain ⟨a', b', rfl⟩ := Th.inDouble s hs
        exact J.F.mul_mem (J.F.mul_mem (J.le a'.property) hhF) (J.le b'.property)
      have hyF : J.ι s * Tg.g ∈ J.F := J.F.mul_mem (J.memF s hsF) hgF
      rw [← hφι _ hyF, J.map_mul, J.invol, hcd]
      have := hl (Tg.g * (d.val * s)) c
      rw [← this]
      congr 1
      group
    rw [Finset.sum_congr rfl s2]
    exact Th.sum_left_mul φ hr Tg.g d
  calc Th.reps.card • ∑ r ∈ Tg.reps, φ (Th.g * r)
      = ∑ s ∈ Th.reps, ∑ r ∈ Tg.reps, φ (J.ι s * r) := by
        rw [Finset.sum_congr rfl rows, Finset.sum_const]
    _ = ∑ r ∈ Tg.reps, ∑ s ∈ Th.reps, φ (J.ι s * r) := Finset.sum_comm
    _ = Tg.reps.card • ∑ s ∈ Th.reps, φ (Tg.g * s) := by
        rw [Finset.sum_congr rfl cols, Finset.sum_const]

end Abstract

section Compressions

variable {σ : CuspidalRepresentation} {K : Subgroup BinaryAdelicGL}

/-- The compression of a double coset, in terms of its coset representatives. -/
theorem compression_coe_eq (T : DoubleCoset K) (v : fixedVectors σ K) :
    ((compression σ K T.g v : fixedVectors σ K) : σ.H) =
      ((T.reps.card : ℂ)⁻¹) • ∑ r ∈ T.reps, σ.π r (v : σ.H) := by
  have hcard : (T.reps.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr T.reps_nonempty).ne'
  have h := heckeOperator_eq_compression (σ := σ) T v
  rw [heckeOperator_apply] at h
  rw [h, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem inner_compression_compression (Tg Th : DoubleCoset K) (v w : fixedVectors σ K) :
    inner ℂ (compression σ K Tg.g (compression σ K Th.g v)) w =
      ((Th.reps.card : ℂ)⁻¹) * ∑ s ∈ Th.reps, inner ℂ (σ.π (Tg.g * s) (v : σ.H)) (w : σ.H) := by
  rw [inner_compression, compression_coe_eq, map_smul, inner_smul_left, map_sum, sum_inner]
  simp only [Complex.conj_inv, Complex.conj_natCast, map_mul, Module.End.mul_apply]

/-- **Commutativity of compressions** from a Gelfand involution. -/
theorem compression_commute (J : GelfandInvolution K) (Tg Th : DoubleCoset K)
    (hgF : Tg.g ∈ J.F) (hhF : Th.g ∈ J.F) :
    Commute (compression σ K Tg.g) (compression σ K Th.g) := by
  ext1 v
  apply ext_inner_right ℂ
  intro w
  change inner ℂ (compression σ K Tg.g (compression σ K Th.g v)) w =
    inner ℂ (compression σ K Th.g (compression σ K Tg.g v)) w
  rw [inner_compression_compression, inner_compression_compression]
  let φ : BinaryAdelicGL → ℂ := fun x => inner ℂ (σ.π x (v : σ.H)) (w : σ.H)
  have hl : ∀ x (k : K), φ (k.val * x) = φ x := by
    intro x k
    simp only [φ, map_mul, Module.End.mul_apply]
    exact inner_pi_fixed σ k _ w.property
  have hr : ∀ x (k : K), φ (x * k.val) = φ x := by
    intro x k
    simp only [φ, map_mul, Module.End.mul_apply, v.property k]
  have key := J.identity Tg Th φ hl hr hgF hhF
  rw [nsmul_eq_mul, nsmul_eq_mul] at key
  have hg0 : (Tg.reps.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr Tg.reps_nonempty).ne'
  have hh0 : (Th.reps.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr Th.reps_nonempty).ne'
  change (Th.reps.card : ℂ)⁻¹ * ∑ s ∈ Th.reps, φ (Tg.g * s) =
    (Tg.reps.card : ℂ)⁻¹ * ∑ r ∈ Tg.reps, φ (Th.g * r)
  field_simp
  linear_combination key.symm

end Compressions

section Central

variable {σ : CuspidalRepresentation} {K : Subgroup BinaryAdelicGL}

theorem pi_mem_fixed_of_commute (u : BinaryAdelicGL) (hu : ∀ k : K, u * k.val = k.val * u)
    {y : σ.H} (hy : y ∈ fixedVectors σ K) : σ.π u y ∈ fixedVectors σ K := by
  intro k
  rw [← Module.End.mul_apply, ← map_mul, ← hu k, map_mul, Module.End.mul_apply, hy k]

theorem inner_pi_left (u : BinaryAdelicGL) (a b : σ.H) :
    inner ℂ (σ.π u a) b = inner ℂ a (σ.π u⁻¹ b) := by
  have hb : σ.π u (σ.π u⁻¹ b) = b := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  conv_lhs => rw [← hb]
  exact cuspOperator_inner σ u a _

/-- Elements commuting with `K` commute with the orthogonal projection onto `σ.H^K`. -/
theorem projection_pi_comm (u : BinaryAdelicGL) (hu : ∀ k : K, u * k.val = k.val * u) (y : σ.H) :
    (fixedVectors σ K).starProjection (σ.π u y) = σ.π u ((fixedVectors σ K).starProjection y) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact pi_mem_fixed_of_commute u hu (Submodule.starProjection_apply_mem _ y)
  · intro w hw
    have hu' : ∀ k : K, u⁻¹ * k.val = k.val * u⁻¹ := by
      intro k
      have := hu k
      calc u⁻¹ * k.val = u⁻¹ * (k.val * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * k.val) * u⁻¹ := by rw [this]
        _ = k.val * u⁻¹ := by group
    rw [← map_sub, inner_pi_left]
    exact Submodule.starProjection_inner_eq_zero y _ (pi_mem_fixed_of_commute u⁻¹ hu' hw)

theorem compression_coe (g : BinaryAdelicGL) (v : fixedVectors σ K) :
    ((compression σ K g v : fixedVectors σ K) : σ.H) =
      (fixedVectors σ K).starProjection (σ.π g (v : σ.H)) := rfl

theorem compression_mul_left (u x : BinaryAdelicGL) (hu : ∀ k : K, u * k.val = k.val * u) :
    compression σ K (u * x) = compression σ K u * compression σ K x := by
  ext1 v
  apply Subtype.ext
  change _ = ((compression σ K u (compression σ K x v) : fixedVectors σ K) : σ.H)
  rw [compression_coe, compression_coe, compression_coe,
    map_mul, Module.End.mul_apply, projection_pi_comm u hu, projection_pi_comm u hu,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

theorem compression_mul_right (x u : BinaryAdelicGL) (hu : ∀ k : K, u * k.val = k.val * u) :
    compression σ K (x * u) = compression σ K x * compression σ K u := by
  ext1 v
  apply Subtype.ext
  change _ = ((compression σ K x (compression σ K u v) : fixedVectors σ K) : σ.H)
  rw [compression_coe, compression_coe, compression_coe,
    map_mul, Module.End.mul_apply, projection_pi_comm u hu,
    Submodule.starProjection_eq_self_iff.mpr v.property]

/-- **Hecke operators are scalars on `σ.H^K`**, given a Gelfand involution whose Cartan subgroup
`F` covers every element up to factors commuting with `K` and with the double coset. -/
theorem heckeOperator_scalar_of_gelfand (J : GelfandInvolution K) (Tg : DoubleCoset K)
    (hgF : Tg.g ∈ J.F)
    (decomp : ∀ h : BinaryAdelicGL, ∃ (u : BinaryAdelicGL) (Th : DoubleCoset K),
      h = u * Th.g ∧ Th.g ∈ J.F ∧ (∀ k : K, u * k.val = k.val * u) ∧ u * Tg.g = Tg.g * u) :
    ∃ z : ℂ, ∀ v ∈ fixedVectors σ K, heckeOperator σ Tg v = z • v := by
  apply heckeOperator_scalar Tg
  intro h
  obtain ⟨u, Th, rfl, hThF, hu, hug⟩ := decomp h
  rw [compression_mul_left u Th.g hu]
  refine Commute.mul_right ?_ (compression_commute J Tg Th hgF hThF)
  change compression σ K Tg.g * compression σ K u = compression σ K u * compression σ K Tg.g
  rw [← compression_mul_right Tg.g u hu, ← compression_mul_left u Tg.g hu, hug]

end Central

end TernaryPeriodPolynomials.RepresentationTheory
