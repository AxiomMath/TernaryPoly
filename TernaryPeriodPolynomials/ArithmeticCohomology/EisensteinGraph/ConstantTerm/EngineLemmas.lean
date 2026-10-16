module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Frame
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.GridCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.OrbitPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.HomogeneousCorestriction

@[expose] public section


/-!
# Elementary lemmas for the constant-term engine

Primitives over an injective image of a group, averaging of primitives over the torus grid,
integrality of `x - A x` on the `K`-torsion grid for `A ≡ 1 mod K`, and finiteness of the
orbit space of a finite relative index.

Written by AxiomCode.
-/

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

/-! ## Primitives over the image of an injective homomorphism -/

/-- A homogeneous 2-cocycle whose restriction to the image of an injective `ι : G →* H` is the
inhomogeneous coboundary of `τ` is the differential of a homogeneous 1-cochain. -/
theorem exists_primitive_range {G V H : Type} [Group G] [Group H] [AddCommGroup V]
    [Module ℂ V] (ι : G →* H) (hι : Function.Injective ι) (ρ : Representation ℂ H V)
    (Kc : GeneralEisenstein.Homogeneous.cochains ι.range ρ 2)
    (cocycle : ∀ x : Fin 4 → H, Kc.val ![x 1, x 2, x 3] - Kc.val ![x 0, x 2, x 3] +
      Kc.val ![x 0, x 1, x 3] - Kc.val ![x 0, x 1, x 2] = 0)
    (τ : G → V)
    (hτ : ∀ a b : G, Kc.val ![1, ι a, ι a * ι b] = ρ (ι a) (τ b) - τ (a * b) + τ a) :
    ∃ P : GeneralEisenstein.Homogeneous.cochains ι.range ρ 1,
      ∀ x, (GeneralEisenstein.Homogeneous.differentialOne ι.range ρ P).val x = Kc.val x := by
  let e : G ≃* ι.range := MonoidHom.ofInjective hι
  refine TernaryPeriodPolynomials.FlagExactness.exists_primitive_of_inhomogeneous
    ι.range ρ Kc cocycle (fun γ => τ (e.symm γ)) ?_
  intro a b
  obtain ⟨a0, rfl⟩ := e.surjective a
  obtain ⟨b0, rfl⟩ := e.surjective b
  have ha : ((e a0 : ι.range) : H) = ι a0 := rfl
  have hb : ((e b0 : ι.range) : H) = ι b0 := rfl
  have hab : e a0 * e b0 = e (a0 * b0) := (map_mul e a0 b0).symm
  simp only [ha, hb, hab, MulEquiv.symm_apply_apply]
  exact hτ a0 b0

/-! ## Averaging of primitives over the grid -/

section GridPrimitive

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The grid average of a doubly indexed family of 1-cochains. -/
def gridPrimitive (P : ℕ → ℕ → (Fin 2 → RationalGL3) → V) (K : ℕ) :
    (Fin 2 → RationalGL3) → V :=
  fun x => (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, P a b x

theorem gridAverage_sub_eq_codiff (Θ : ℝ × ℝ → (Fin 3 → RationalGL3) → V)
    (P : ℕ → ℕ → (Fin 2 → RationalGL3) → V) {K : ℕ} (hK : K ≠ 0)
    (hP : ∀ a ∈ Finset.range K, ∀ b ∈ Finset.range K,
      (fun x => Θ ((a : ℝ) / K, (b : ℝ) / K) x - Θ 0 x) = codiff (P a b)) :
    gridAverage Θ K - Θ 0 = codiff (gridPrimitive P K) := by
  have e1 : gridAverage (fun r y => Θ r y - Θ 0 y) K =
      gridAverage Θ K - gridAverage (fun _ => Θ 0) K :=
    gridAverage_sub Θ (fun _ => Θ 0) K
  have e2 : gridAverage Θ K - Θ 0 = gridAverage (fun r y => Θ r y - Θ 0 y) K := by
    rw [e1, gridAverage_const (Θ 0) hK]
  rw [e2]
  funext x
  have h1 : ∀ a ∈ Finset.range K, ∀ b ∈ Finset.range K,
      Θ ((a : ℝ) / K, (b : ℝ) / K) x - Θ 0 x =
        P a b ![x 1, x 2] - P a b ![x 0, x 2] + P a b ![x 0, x 1] :=
    fun a ha b hb => congrFun (hP a ha b hb) x
  have h2 : ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
      (Θ ((a : ℝ) / K, (b : ℝ) / K) x - Θ 0 x) =
      ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        (P a b ![x 1, x 2] - P a b ![x 0, x 2] + P a b ![x 0, x 1]) :=
    Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => h1 a ha b hb
  show (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
      (Θ ((a : ℝ) / K, (b : ℝ) / K) x - Θ 0 x) =
    (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, P a b ![x 1, x 2] -
      (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, P a b ![x 0, x 2] +
      (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, P a b ![x 0, x 1]
  rw [h2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_add, smul_sub]

theorem gridPrimitive_equivariant (Γ : Subgroup RationalGL3)
    (ρ : Representation ℂ RationalGL3 V) (P : ℕ → ℕ → (Fin 2 → RationalGL3) → V) (K : ℕ)
    (h : ∀ a b, Equivariant Γ ρ (P a b)) : Equivariant Γ ρ (gridPrimitive P K) := by
  intro γ hγ x
  have h' : ∀ a b, P a b (fun i => γ * x i) = ρ γ (P a b x) := fun a b => h a b γ hγ x
  simp only [gridPrimitive, map_smul, map_sum, h']

end GridPrimitive

/-! ## Congruence modulo `K` on the grid -/

/-- If `A ≡ 1 mod K`, then every entry of `A - 1` is `K` times an integer. -/
private theorem entries_of_reduction_eq_one (A : GLTwo ℤ) (K : ℕ)
    (h : reduction K A = 1) :
    ∃ c₀₀ c₀₁ c₁₀ c₁₁ : ℤ,
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 + (K : ℤ) * c₀₀ ∧
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (K : ℤ) * c₀₁ ∧
      (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (K : ℤ) * c₁₀ ∧
      (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 + (K : ℤ) * c₁₁ := by
  have e : ∀ i j, (((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) =
      ((1 : GLTwo (ZMod K)) : Matrix (Fin 2) (Fin 2) (ZMod K)) i j := by
    intro i j
    have h1 : ((reduction K A : GLTwo (ZMod K)) : Matrix (Fin 2) (Fin 2) (ZMod K)) i j =
        ((1 : GLTwo (ZMod K)) : Matrix (Fin 2) (Fin 2) (ZMod K)) i j :=
      congrArg (fun g : GLTwo (ZMod K) => ((g : Matrix (Fin 2) (Fin 2) (ZMod K)) i j)) h
    have h2 : ((reduction K A : GLTwo (ZMod K)) : Matrix (Fin 2) (Fin 2) (ZMod K)) i j =
        (((A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := rfl
    exact h2.symm.trans h1
  have h00 : (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod K) = 1 := by
    rw [e 0 0]; simp
  have h01 : (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod K) = 0 := by
    rw [e 0 1]; simp
  have h10 : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod K) = 0 := by
    rw [e 1 0]; simp
  have h11 : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod K) = 1 := by
    rw [e 1 1]; simp
  have d00 : (((((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 : ℤ)) : ZMod K)) = 0 := by
    rw [Int.cast_sub, h00, Int.cast_one, sub_self]
  have d11 : (((((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 : ℤ)) : ZMod K)) = 0 := by
    rw [Int.cast_sub, h11, Int.cast_one, sub_self]
  obtain ⟨c₀₀, hc₀₀⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ K).1 d00
  obtain ⟨c₀₁, hc₀₁⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ K).1 h01
  obtain ⟨c₁₀, hc₁₀⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ K).1 h10
  obtain ⟨c₁₁, hc₁₁⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ K).1 d11
  refine ⟨c₀₀, c₀₁, c₁₀, c₁₁, ?_, hc₀₁, hc₁₀, ?_⟩
  · linarith
  · linarith

theorem exists_int_sub_leviAct (A : GLTwo ℤ) (K : ℕ) (hK : 0 < K)
    (h : reduction K A = 1) (a b : ℤ) :
    ∃ δ : ℤ × ℤ, ((δ.1 : ℚ), (δ.2 : ℚ)) =
      (((a : ℚ) / K, (b : ℚ) / K) - leviAct A ((a : ℚ) / K, (b : ℚ) / K)) := by
  obtain ⟨c₀₀, c₀₁, c₁₀, c₁₁, h₀₀, h₀₁, h₁₀, h₁₁⟩ := entries_of_reduction_eq_one A K h
  have hK' : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
  have hX : (K : ℚ) * ((a : ℚ) / K) = a := by field_simp
  have hY : (K : ℚ) * ((b : ℚ) / K) = b := by field_simp
  refine ⟨(-(c₀₀ * a + c₀₁ * b), -(c₁₀ * a + c₁₁ * b)), ?_⟩
  simp only [leviAct, h₀₀, h₀₁, h₁₀, h₁₁, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor
  · push_cast
    linear_combination (c₀₀ : ℚ) * hX + (c₀₁ : ℚ) * hY
  · push_cast
    linear_combination (c₁₀ : ℚ) * hX + (c₁₁ : ℚ) * hY

theorem exists_int_sub_leviAct_inv (A : GLTwo ℤ) (K : ℕ) (hK : 0 < K)
    (h : reduction K A = 1) (a b : ℤ) :
    ∃ δ : ℤ × ℤ, ((δ.1 : ℚ), (δ.2 : ℚ)) =
      (leviAct A ((a : ℚ) / K, (b : ℚ) / K) - ((a : ℚ) / K, (b : ℚ) / K)) := by
  obtain ⟨δ, hδ⟩ := exists_int_sub_leviAct A K hK h a b
  refine ⟨(-δ.1, -δ.2), ?_⟩
  rw [← neg_sub, ← hδ]
  simp

/-- The real action of `A ≡ 1 mod K` moves a point of the grid `(1/K) ℤ²` by an integer vector. -/
theorem realAct_div_sub (A : GLTwo ℤ) (K : ℕ) (hK : 0 < K) (h : reduction K A = 1)
    (a b : ℤ) :
    ∃ δ : ℤ × ℤ, realAct A ((a : ℝ) / K, (b : ℝ) / K) =
      ((a : ℝ) / K + (δ.1 : ℝ), (b : ℝ) / K + (δ.2 : ℝ)) := by
  obtain ⟨c₀₀, c₀₁, c₁₀, c₁₁, h₀₀, h₀₁, h₁₀, h₁₁⟩ := entries_of_reduction_eq_one A K h
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hX : (K : ℝ) * ((a : ℝ) / K) = a := by field_simp
  have hY : (K : ℝ) * ((b : ℝ) / K) = b := by field_simp
  refine ⟨(c₀₀ * a + c₀₁ * b, c₁₀ * a + c₁₁ * b), ?_⟩
  simp only [realAct, h₀₀, h₀₁, h₁₀, h₁₁, Prod.mk.injEq]
  constructor
  · push_cast
    linear_combination (c₀₀ : ℝ) * hX + (c₀₁ : ℝ) * hY
  · push_cast
    linear_combination (c₁₀ : ℝ) * hX + (c₁₁ : ℝ) * hY

/-! ## Finiteness of orbit spaces -/

theorem finite_rightRel_of_relIndex_ne_zero {G : Type} [Group G] (H K : Subgroup G)
    (h : H.relIndex K ≠ 0) :
    Finite (Quotient (QuotientGroup.rightRel (H.subgroupOf K))) := by
  have hidx : (H.subgroupOf K).index ≠ 0 := h
  have : Finite (↥K ⧸ H.subgroupOf K) := Subgroup.index_ne_zero_iff_finite.1 hidx
  exact Finite.of_equiv _
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel (s := H.subgroupOf K)).symm

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
