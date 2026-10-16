module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Interface
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Frame

@[expose] public section


/-!
# Covariance of grid averages

The `K × K` grid average of a `ℤ²`-periodic family is invariant under reindexing the family by
the real action of an integral invertible matrix. The proof reduces the grid to `(ℤ/K)²`, where
the matrix acts by a bijection.

Written by AxiomCode.
-/

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

/-- The column action of an integral `2 × 2` matrix on `ℝ²`. -/
def realAct (A : GLTwo ℤ) (r : ℝ × ℝ) : ℝ × ℝ :=
  (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * r.1 + ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) * r.2,
    ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * r.1 + ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) * r.2)

/-- The column action of an integral matrix on `(ℤ/K)²`. -/
def zAct (K : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) (z : ZMod K × ZMod K) : ZMod K × ZMod K :=
  (((B 0 0 : ℤ) : ZMod K) * z.1 + ((B 0 1 : ℤ) : ZMod K) * z.2,
    ((B 1 0 : ℤ) : ZMod K) * z.1 + ((B 1 1 : ℤ) : ZMod K) * z.2)

/-- A function on the real plane restricted to the grid `(ℤ/K)²`, through the representatives
of the residues. -/
def gridFun {W : Type} (f : ℝ × ℝ → W) (K : ℕ) (z : ZMod K × ZMod K) : W :=
  f (((z.1.val : ℕ) : ℝ) / K, ((z.2.val : ℕ) : ℝ) / K)

theorem realAct_intCast (A : GLTwo ℤ) (K : ℕ) (a b : ℤ) :
    realAct A ((a : ℝ) / K, (b : ℝ) / K) =
      (((intAct A (a, b)).1 : ℝ) / K, ((intAct A (a, b)).2 : ℝ) / K) := by
  refine Prod.ext ?_ ?_ <;> simp only [realAct, intAct] <;> push_cast <;> ring

theorem zAct_intCast (K : ℕ) (A : GLTwo ℤ) (a b : ℤ) :
    zAct K (A : Matrix (Fin 2) (Fin 2) ℤ) ((a : ZMod K), (b : ZMod K)) =
      (((intAct A (a, b)).1 : ZMod K), ((intAct A (a, b)).2 : ZMod K)) := by
  simp only [zAct, intAct, Int.cast_add, Int.cast_mul]

theorem zAct_zAct (K : ℕ) (B C : Matrix (Fin 2) (Fin 2) ℤ) (z : ZMod K × ZMod K) :
    zAct K B (zAct K C z) = zAct K (B * C) z := by
  refine Prod.ext ?_ ?_ <;>
    simp only [zAct, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] <;> ring

theorem zAct_one (K : ℕ) (z : ZMod K × ZMod K) :
    zAct K (1 : Matrix (Fin 2) (Fin 2) ℤ) z = z := by
  have h01 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have h10 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  have h00 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := Matrix.one_apply_eq 0
  have h11 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := Matrix.one_apply_eq 1
  refine Prod.ext ?_ ?_
  · simp only [zAct, h00, h01, Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero]
  · simp only [zAct, h10, h11, Int.cast_one, Int.cast_zero, one_mul, zero_mul, zero_add]

/-- The bijection of `(ℤ/K)²` induced by an integral invertible matrix. -/
def zEquiv (K : ℕ) (A : GLTwo ℤ) : ZMod K × ZMod K ≃ ZMod K × ZMod K where
  toFun := zAct K (A : Matrix (Fin 2) (Fin 2) ℤ)
  invFun := zAct K ((A⁻¹ : GLTwo ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  left_inv := fun z => by
    have h := zAct_zAct K ((A⁻¹ : GLTwo ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      (A : Matrix (Fin 2) (Fin 2) ℤ) z
    rw [Units.inv_mul, zAct_one] at h
    exact h
  right_inv := fun z => by
    have h := zAct_zAct K (A : Matrix (Fin 2) (Fin 2) ℤ)
      ((A⁻¹ : GLTwo ℤ) : Matrix (Fin 2) (Fin 2) ℤ) z
    rw [Units.mul_inv, zAct_one] at h
    exact h

theorem div_decomp (K : ℕ) [NeZero K] (r q : ℤ) :
    (((r + (K : ℤ) * q : ℤ) : ℝ)) / K = (r : ℝ) / K + (q : ℝ) := by
  have hKr : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  push_cast
  field_simp

theorem gridFun_int {W : Type} (f : ℝ × ℝ → W)
    (periodic : ∀ (r : ℝ × ℝ) (ℓ : ℤ × ℤ), f (r.1 + ℓ.1, r.2 + ℓ.2) = f r)
    (K : ℕ) [NeZero K] (a b : ℤ) :
    gridFun f K ((a : ZMod K), (b : ZMod K)) = f ((a : ℝ) / K, (b : ℝ) / K) := by
  show f ((((a : ZMod K).val : ℕ) : ℝ) / K, (((b : ZMod K).val : ℕ) : ℝ) / K) = _
  have ha := ZMod.val_intCast (n := K) a
  have hb := ZMod.val_intCast (n := K) b
  have hra : (((a : ZMod K).val : ℕ) : ℝ) = ((a % (K : ℤ) : ℤ) : ℝ) := by
    rw [← ha]
    exact (Int.cast_natCast _).symm
  have hrb : (((b : ZMod K).val : ℕ) : ℝ) = ((b % (K : ℤ) : ℤ) : ℝ) := by
    rw [← hb]
    exact (Int.cast_natCast _).symm
  have hdecomp : ∀ x : ℤ, (x : ℝ) / K = ((x % (K : ℤ) : ℤ) : ℝ) / K + ((x / (K : ℤ) : ℤ) : ℝ) :=
    fun x => by
      have h : x % (K : ℤ) + (K : ℤ) * (x / (K : ℤ)) = x := by
        have := Int.emod_def x (K : ℤ)
        linarith
      have h2 := div_decomp K (x % (K : ℤ)) (x / (K : ℤ))
      rw [h] at h2
      exact h2
  calc f ((((a : ZMod K).val : ℕ) : ℝ) / K, (((b : ZMod K).val : ℕ) : ℝ) / K)
      = f (((a % (K : ℤ) : ℤ) : ℝ) / K, ((b % (K : ℤ) : ℤ) : ℝ) / K) := by rw [hra, hrb]
    _ = f (((a % (K : ℤ) : ℤ) : ℝ) / K + ((a / (K : ℤ) : ℤ) : ℝ),
          ((b % (K : ℤ) : ℤ) : ℝ) / K + ((b / (K : ℤ) : ℤ) : ℝ)) :=
        (periodic (((a % (K : ℤ) : ℤ) : ℝ) / K, ((b % (K : ℤ) : ℤ) : ℝ) / K)
          (a / (K : ℤ), b / (K : ℤ))).symm
    _ = f ((a : ℝ) / K, (b : ℝ) / K) := by rw [← hdecomp a, ← hdecomp b]

theorem sum_range_natCast {W : Type} [AddCommMonoid W] (K : ℕ) [NeZero K] (g : ZMod K → W) :
    ∑ a ∈ Finset.range K, g (a : ZMod K) = ∑ x, g x := by
  refine Finset.sum_bij (fun a _ => (a : ZMod K)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro a ha b hb h
    rw [Finset.mem_range] at ha hb
    have h2 := (ZMod.natCast_eq_natCast_iff' a b K).1 h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  · intro x _
    exact ⟨x.val, Finset.mem_range.2 (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

theorem sum_range_range_natCast {W : Type} [AddCommMonoid W] (K : ℕ) [NeZero K]
    (g : ZMod K × ZMod K → W) :
    ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, g ((a : ZMod K), (b : ZMod K)) = ∑ z, g z := by
  calc ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, g ((a : ZMod K), (b : ZMod K))
      = ∑ a ∈ Finset.range K, ∑ y : ZMod K, g ((a : ZMod K), y) :=
        Finset.sum_congr rfl fun a _ => sum_range_natCast K (fun y => g ((a : ZMod K), y))
    _ = ∑ x : ZMod K, ∑ y : ZMod K, g (x, y) :=
        sum_range_natCast K (fun x => ∑ y : ZMod K, g (x, y))
    _ = ∑ z, g z := (Fintype.sum_prod_type g).symm

theorem f_realAct_eq {W : Type} (f : ℝ × ℝ → W)
    (periodic : ∀ (r : ℝ × ℝ) (ℓ : ℤ × ℤ), f (r.1 + ℓ.1, r.2 + ℓ.2) = f r)
    (A : GLTwo ℤ) (K : ℕ) [NeZero K] (a b : ℤ) :
    f (realAct A ((a : ℝ) / K, (b : ℝ) / K)) =
      gridFun f K (zAct K (A : Matrix (Fin 2) (Fin 2) ℤ) ((a : ZMod K), (b : ZMod K))) := by
  calc f (realAct A ((a : ℝ) / K, (b : ℝ) / K))
      = f (((intAct A (a, b)).1 : ℝ) / K, ((intAct A (a, b)).2 : ℝ) / K) := by
        rw [realAct_intCast]
    _ = gridFun f K (((intAct A (a, b)).1 : ZMod K), ((intAct A (a, b)).2 : ZMod K)) :=
        (gridFun_int f periodic K (intAct A (a, b)).1 (intAct A (a, b)).2).symm
    _ = gridFun f K (zAct K (A : Matrix (Fin 2) (Fin 2) ℤ) ((a : ZMod K), (b : ZMod K))) := by
        rw [zAct_intCast]

/-- The `K × K` grid sum of a `ℤ²`-periodic family is invariant under reindexing by an integral
invertible matrix. -/
theorem gridSum_comp_realAct {W : Type} [AddCommGroup W] (f : ℝ × ℝ → W)
    (periodic : ∀ (r : ℝ × ℝ) (ℓ : ℤ × ℤ), f (r.1 + ℓ.1, r.2 + ℓ.2) = f r)
    (A : GLTwo ℤ) {K : ℕ} (hK : 0 < K) :
    ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, f (realAct A ((a : ℝ) / K, (b : ℝ) / K)) =
      ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, f ((a : ℝ) / K, (b : ℝ) / K) := by
  have : NeZero K := ⟨hK.ne'⟩
  have key_nat : ∀ a b : ℕ, f (realAct A ((a : ℝ) / K, (b : ℝ) / K)) =
      gridFun f K (zAct K (A : Matrix (Fin 2) (Fin 2) ℤ) ((a : ZMod K), (b : ZMod K))) := by
    intro a b
    have h := f_realAct_eq f periodic A K (a : ℤ) (b : ℤ)
    simpa only [Int.cast_natCast] using h
  have rhs_nat : ∀ a b : ℕ,
      f ((a : ℝ) / K, (b : ℝ) / K) = gridFun f K ((a : ZMod K), (b : ZMod K)) := by
    intro a b
    have h := gridFun_int f periodic K (a : ℤ) (b : ℤ)
    simpa only [Int.cast_natCast] using h.symm
  calc ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, f (realAct A ((a : ℝ) / K, (b : ℝ) / K))
      = ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
          gridFun f K (zAct K (A : Matrix (Fin 2) (Fin 2) ℤ) ((a : ZMod K), (b : ZMod K))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key_nat a b
    _ = ∑ z, gridFun f K (zAct K (A : Matrix (Fin 2) (Fin 2) ℤ) z) :=
        sum_range_range_natCast K (fun z => gridFun f K (zAct K (A : Matrix (Fin 2) (Fin 2) ℤ) z))
    _ = ∑ z, gridFun f K z := Equiv.sum_comp (zEquiv K A) (gridFun f K)
    _ = ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, gridFun f K ((a : ZMod K), (b : ZMod K)) :=
        (sum_range_range_natCast K (gridFun f K)).symm
    _ = ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, f ((a : ℝ) / K, (b : ℝ) / K) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (rhs_nat a b).symm

/-- The grid average of a periodic family whose members are covariant under `Γ` up to integral
reindexing of the real parameter is `Γ`-equivariant. -/
theorem gridAverage_equivariant_of_covariant {V : Type} [AddCommGroup V] [Module ℂ V]
    (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (Θ : ℝ × ℝ → (Fin 3 → RationalGL3) → V)
    (periodic : ∀ (r : ℝ × ℝ) (ℓ : ℤ × ℤ) (y : Fin 3 → RationalGL3),
      Θ (r.1 + ℓ.1, r.2 + ℓ.2) y = Θ r y)
    (cov : ∀ γ ∈ Γ, ∃ A : GLTwo ℤ, ∀ (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      Θ r (fun i => γ * y i) = ρ γ (Θ (realAct A r) y))
    (K : ℕ) (hK : 0 < K) : Equivariant Γ ρ (gridAverage Θ K) := by
  unfold Equivariant
  intro γ hγ x
  obtain ⟨A, hA⟩ := cov γ hγ
  have hsum : ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
      Θ (realAct A ((a : ℝ) / K, (b : ℝ) / K)) x =
      ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, Θ ((a : ℝ) / K, (b : ℝ) / K) x :=
    gridSum_comp_realAct (fun r => Θ r x) (fun r ℓ => periodic r ℓ x) A hK
  have h1 : ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
      Θ ((a : ℝ) / K, (b : ℝ) / K) (fun i => γ * x i) =
      ρ γ (∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        Θ (realAct A ((a : ℝ) / K, (b : ℝ) / K)) x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => hA _ x
  simp only [gridAverage]
  rw [h1, hsum]
  exact (map_smul (ρ γ) _ _).symm

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
