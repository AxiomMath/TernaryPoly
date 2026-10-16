module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FarePeriod
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


/-!
# A Schur-type lemma for the plain binary forms

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial TernaryPoly.BinaryModularSymbolCoefficients TernaryPoly.RankTwoAugmentedFrames

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FareyTree


theorem eval_smul_homog {q : Poly} {d : ℕ} (hq : q.IsHomogeneous d) (c : ℚ) (x : Fin 2 → ℚ) :
    eval (c • x) q = c ^ d * eval x q := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m 0 + m 1 = d := by
    have h := hq (MvPolynomial.mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa [Fin.sum_univ_two] using h
  simp only [Fin.prod_univ_two, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← hdeg, pow_add]
  ring

theorem poly_eval_aeval (r : Poly) (t : ℚ) :
    Polynomial.eval t (aeval (fun i : Fin 2 => (![Polynomial.X, 1] : Fin 2 → Polynomial ℚ) i) r) =
      eval ![t, 1] r := by
  have h := congrArg (fun φ => φ r)
    (MvPolynomial.comp_aeval (R := ℚ) (fun i : Fin 2 => (![Polynomial.X, 1] : Fin 2 → Polynomial ℚ) i)
      (Polynomial.aeval t))
  simp only [AlgHom.comp_apply] at h
  have e : (fun i : Fin 2 => Polynomial.aeval t ((![Polynomial.X, 1] : Fin 2 → Polynomial ℚ) i)) =
      (![t, 1] : Fin 2 → ℚ) := by
    funext i; fin_cases i <;> simp
  rw [e] at h
  have h2 : (Polynomial.aeval t) ((aeval fun i : Fin 2 => (![Polynomial.X, 1] : Fin 2 → Polynomial ℚ) i) r) =
      Polynomial.eval t ((aeval fun i : Fin 2 => (![Polynomial.X, 1] : Fin 2 → Polynomial ℚ) i) r) :=
    by simp
  have h3 : (aeval (![t, 1] : Fin 2 → ℚ)) r = eval ![t, 1] r := by simp
  exact h2.symm.trans (h.trans h3)

theorem eval_zero_of_dehomog {r : Poly} {d : ℕ} (hr : r.IsHomogeneous d) (h1 : ∀ t : ℚ, eval ![t, 1] r = 0) :
    r = 0 := by
  have h2 : ∀ x y : ℚ, eval ![x, y] (X 1 * r) = 0 := by
    intro x y
    by_cases hy : y = 0
    · simp [hy]
    · have e : (![x, y] : Fin 2 → ℚ) = y • ![x / y, 1] := by
        funext i; fin_cases i
        · simp
          field_simp
        · simp
      rw [map_mul, e, eval_smul_homog hr, h1]
      simp
  have h3 : X 1 * r = 0 := MvPolynomial.funext fun x => by
    have := h2 (x 0) (x 1)
    have e : (![x 0, x 1] : Fin 2 → ℚ) = x := by funext i; fin_cases i <;> rfl
    rw [e] at this
    simpa using this
  exact (mul_eq_zero.mp h3).resolve_left (X_ne_zero 1)

theorem fixedU_eq_zero {r : Poly} {d : ℕ} (hr : r.IsHomogeneous d)
    (hfix : ∀ x y : ℚ, eval ![x - y, y] r = eval ![x, y] r) (h0 : eval ![0, 1] r = 0) : r = 0 := by
  apply eval_zero_of_dehomog hr
  set P := aeval (fun i : Fin 2 => (![Polynomial.X, 1] : Fin 2 → Polynomial ℚ) i) r with hP
  have hPe : ∀ t, P.eval t = eval ![t, 1] r := fun t => poly_eval_aeval r t
  have hstep : ∀ t, P.eval (t - 1) = P.eval t := fun t => by
    rw [hPe, hPe]; exact hfix t 1
  have hk : ∀ k : ℕ, P.eval (-(k : ℚ)) = P.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep (-(k : ℚ))
      rw [show -((k + 1 : ℕ) : ℚ) = -(k : ℚ) - 1 by push_cast; ring, this, ih]
  have hPC : P = Polynomial.C (P.eval 0) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range fun k : ℕ => -(k : ℚ))
    · rintro _ ⟨k, rfl⟩
      simpa using hk k
    · exact Set.infinite_range_of_injective (fun a b h => by simpa using h)
  intro t
  rw [← hPe t, hPC]
  simp [hPe, h0]



/-- `[[1,k],[0,1]]`. -/
def elemU (k : ℤ) : IntegralGL :=
  Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- `[[1,0],[k,1]]`. -/
def elemL (k : ℤ) : IntegralGL :=
  Matrix.SpecialLinearGroup.toGL ⟨!![1, 0; k, 1], by simp [Matrix.det_fin_two]⟩

theorem elemU_val (k : ℤ) : (elemU k).val = !![1, k; 0, 1] := rfl
theorem elemL_val (k : ℤ) : (elemL k).val = !![1, 0; k, 1] := rfl

theorem elemU_mul (k l : ℤ) : elemU k * elemU l = elemU (k + l) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elemU_val, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem elemU_zero : elemU 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elemU_val]

theorem elemL_mul (k l : ℤ) : elemL k * elemL l = elemL (k + l) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elemL_val, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem elemL_zero : elemL 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elemL_val]

theorem rho_elemU (d : ℕ) (k : ℤ) (q : (Dplain d).V) :
    (((Dplain d).ρ (elemU k) q : HomogeneousPoly d) : Poly) =
      bind₁ (![X 0 - C (k : ℚ) * X 1, X 1] : Fin 2 → Poly) (q : Poly) := by
  have hgh : elemU k * elemU (-k) = 1 := by rw [elemU_mul]; simp [elemU_zero]
  rw [show (Dplain d).ρ (elemU k) q = integralAction d 0 (elemU k) q from rfl,
    integralAction_zero_coe d (elemU k) (elemU (-k)) hgh]
  rw [subsZ_eq_bind _ ![X 0 - C (k : ℚ) * X 1, X 1]]
  · simp [elemU_val]
    ring
  · simp [elemU_val]



theorem mem_span_monomials {q : Poly} {d : ℕ} (hq : q.IsHomogeneous d) :
    q ∈ Submodule.span ℚ (Set.range fun i : Fin (d + 1) => (X 0 ^ i.val * X 1 ^ (d - i.val) : Poly)) := by
  have hsum := q.as_sum
  rw [hsum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hdeg : m 0 + m 1 = d := by
    have h := hq (MvPolynomial.mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa [Fin.sum_univ_two] using h
  have hm0 : m 0 < d + 1 := by omega
  have e : monomial m (q.coeff m) = q.coeff m • (X 0 ^ (m 0) * X 1 ^ (d - m 0) : Poly) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two,
      show d - m 0 = m 1 by omega, smul_eq_C_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨m 0, hm0⟩, rfl⟩)

theorem wk_expand (d : ℕ) (k : ℕ) :
    ((X 1 - C (k : ℚ) * X 0) ^ d : Poly) =
      ∑ i ∈ Finset.range (d + 1), ((d.choose i : ℚ) * (-(k : ℚ)) ^ i) • (X 0 ^ i * X 1 ^ (d - i) : Poly) := by
  rw [show (X 1 - C (k : ℚ) * X 0 : Poly) = (-(C (k : ℚ)) * X 0) + X 1 by ring, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, smul_eq_C_mul, map_mul, map_pow, map_neg, map_natCast]
  rw [map_natCast]
  ring

theorem monomial_mem_span_w (d : ℕ) (i : Fin (d + 1)) :
    (X 0 ^ i.val * X 1 ^ (d - i.val) : Poly) ∈
      Submodule.span ℚ (Set.range fun k : Fin (d + 1) => ((X 1 - C ((k : ℕ) : ℚ) * X 0) ^ d : Poly)) := by
  set B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ := Matrix.vandermonde (fun k : Fin (d + 1) => -((k : ℕ) : ℚ)) with hB
  have hdet : B.det ≠ 0 := by
    rw [hB, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    have : ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ) := neg_injective hab
    exact Fin.ext (by exact_mod_cast this)
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hdet)
  have key : ∑ k : Fin (d + 1), (B⁻¹ i k) • ((X 1 - C ((k : ℕ) : ℚ) * X 0) ^ d : Poly) =
      (d.choose i : ℚ) • (X 0 ^ i.val * X 1 ^ (d - i.val) : Poly) := by
    simp_rw [wk_expand]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    rw [Finset.sum_range (fun j => ∑ k : Fin (d + 1), (B⁻¹ i k * ((d.choose j : ℚ) * (-((k : ℕ) : ℚ)) ^ j)) •
      (X 0 ^ j * X 1 ^ (d - j) : Poly))]
    have h1 : ∀ j : Fin (d + 1), ∑ k : Fin (d + 1), (B⁻¹ i k * ((d.choose j : ℚ) * (-((k : ℕ) : ℚ)) ^ (j : ℕ))) =
        (d.choose j : ℚ) * (B⁻¹ * B) i j := by
      intro j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hB, Matrix.vandermonde_apply]
      ring
    simp_rw [← Finset.sum_smul, h1, hBinv, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  have hc : (d.choose i : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
  have e : (X 0 ^ i.val * X 1 ^ (d - i.val) : Poly) =
      ((d.choose i : ℚ)⁻¹) • ∑ k : Fin (d + 1), (B⁻¹ i k) • ((X 1 - C ((k : ℕ) : ℚ) * X 0) ^ d : Poly) := by
    rw [key, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))


theorem rho_elemL (d : ℕ) (k : ℤ) (q : (Dplain d).V) :
    (((Dplain d).ρ (elemL k) q : HomogeneousPoly d) : Poly) =
      bind₁ (![X 0, X 1 - C (k : ℚ) * X 0] : Fin 2 → Poly) (q : Poly) := by
  have hgh : elemL k * elemL (-k) = 1 := by rw [elemL_mul]; simp [elemL_zero]
  rw [show (Dplain d).ρ (elemL k) q = integralAction d 0 (elemL k) q from rfl,
    integralAction_zero_coe d (elemL k) (elemL (-k)) hgh]
  rw [subsZ_eq_bind _ ![X 0, X 1 - C (k : ℚ) * X 0]]
  · simp [elemL_val]
  · simp [elemL_val]
    ring

theorem mem_span_w {q : Poly} {d : ℕ} (hq : q.IsHomogeneous d) :
    q ∈ Submodule.span ℚ (Set.range fun k : Fin (d + 1) => ((X 1 - C ((k : ℕ) : ℚ) * X 0) ^ d : Poly)) := by
  refine (Submodule.span_le.mpr ?_) (mem_span_monomials hq)
  rintro _ ⟨i, rfl⟩
  exact monomial_mem_span_w d i

/-- `X₁^d` as an element of the plain binary forms of degree `d`. -/
def zpoly (d : ℕ) : HomogeneousPoly d :=
  ⟨X 1 ^ d, by
    rw [mem_homogeneousSubmodule]
    simpa using (isHomogeneous_X ℚ (1 : Fin 2)).pow d⟩

theorem eval_bind₁_two (f : Fin 2 → Poly) (p : Poly) (x : Fin 2 → ℚ) :
    eval x (bind₁ f p) = eval (fun i => eval x (f i)) p := by
  have := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℚ) x f p
  simpa [MvPolynomial.coe_eval₂Hom] using this

theorem phi_zpoly (d : ℕ) (φ : (Dplain d).V →ₗ[ℚ] (Dplain d).V)
    (hφ : ∀ (g : IntegralGL) (q : (Dplain d).V), φ ((Dplain d).ρ g q) = (Dplain d).ρ g (φ q)) :
    ∃ c : ℚ, φ (zpoly d) = c • zpoly d := by
  have hz : (Dplain d).ρ (elemU 1) (zpoly d) = zpoly d := by
    apply Subtype.ext
    rw [rho_elemU]
    simp [zpoly]
  have hu : (Dplain d).ρ (elemU 1) (φ (zpoly d)) = φ (zpoly d) := by
    rw [← hφ, hz]
  set u := φ (zpoly d) with hudef
  have hbu : bind₁ (![X 0 - C ((1 : ℤ) : ℚ) * X 1, X 1] : Fin 2 → Poly) (u : Poly) = (u : Poly) := by
    rw [← rho_elemU]; exact congrArg Subtype.val hu
  refine ⟨eval ![0, 1] (u : Poly), ?_⟩
  set c := eval ![0, 1] (u : Poly) with hc
  set r : Poly := (u : Poly) - C c * X 1 ^ d with hr
  have hrh : r.IsHomogeneous d := by
    refine ((mem_homogeneousSubmodule d _).1 u.2).sub ?_
    simpa using (isHomogeneous_X ℚ (1 : Fin 2)).pow d |>.C_mul c
  have hbr : bind₁ (![X 0 - C ((1 : ℤ) : ℚ) * X 1, X 1] : Fin 2 → Poly) r = r := by
    rw [hr, map_sub, hbu, map_mul, map_pow]
    simp
  have hfix : ∀ x y : ℚ, eval ![x - y, y] r = eval ![x, y] r := by
    intro x y
    have := congrArg (eval ![x, y]) hbr
    rw [eval_bind₁_two] at this
    have e : (fun i => eval ![x, y] ((![X 0 - C ((1 : ℤ) : ℚ) * X 1, X 1] : Fin 2 → Poly) i)) =
        (![x - y, y] : Fin 2 → ℚ) := by
      funext i; fin_cases i <;> simp
    rw [e] at this
    exact this
  have h0 : eval ![0, 1] r = 0 := by
    simp [hr, hc]
  have := fixedU_eq_zero hrh hfix h0
  apply Subtype.ext
  change (u : Poly) = c • (X 1 ^ d : Poly)
  rw [hr] at this
  rw [smul_eq_C_mul]
  exact sub_eq_zero.1 this

/-- **Schur-type lemma**: an endomorphism of the `GL₂(ℤ)`-module of binary forms of degree `d` is a scalar. -/
theorem dplain_endo_scalar (d : ℕ) (φ : (Dplain d).V →ₗ[ℚ] (Dplain d).V)
    (hφ : ∀ (g : IntegralGL) (q : (Dplain d).V), φ ((Dplain d).ρ g q) = (Dplain d).ρ g (φ q)) :
    ∃ c : ℚ, ∀ q, φ q = c • q := by
  obtain ⟨c, hc⟩ := phi_zpoly d φ hφ
  refine ⟨c, fun q => ?_⟩
  let S : Submodule ℚ (Dplain d).V := Submodule.span ℚ
    (Set.range fun k : Fin (d + 1) => (Dplain d).ρ (elemL ((k : ℕ) : ℤ)) (zpoly d))
  have hw : ∀ k : Fin (d + 1), (((Dplain d).ρ (elemL ((k : ℕ) : ℤ)) (zpoly d) : HomogeneousPoly d) : Poly) =
      (X 1 - C ((k : ℕ) : ℚ) * X 0) ^ d := by
    intro k
    rw [rho_elemL]
    simp [zpoly]
  have hS : q ∈ S := by
    have h1 : (q : Poly) ∈ Submodule.map (Submodule.subtype (homogeneousSubmodule (Fin 2) ℚ d)) S := by
      have hset : (Submodule.subtype (homogeneousSubmodule (Fin 2) ℚ d)) ''
          (Set.range fun k : Fin (d + 1) => (Dplain d).ρ (elemL ((k : ℕ) : ℤ)) (zpoly d)) =
          Set.range fun k : Fin (d + 1) => ((X 1 - C ((k : ℕ) : ℚ) * X 0) ^ d : Poly) := by
        ext p
        simp only [Set.mem_image, Set.mem_range, Submodule.subtype_apply]
        constructor
        · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, (hw k).symm⟩
        · rintro ⟨k, rfl⟩
          exact ⟨_, ⟨k, rfl⟩, hw k⟩
      rw [Submodule.map_span, hset]
      exact mem_span_w ((mem_homogeneousSubmodule d _).1 q.2)
    obtain ⟨s, hs, hsq⟩ := Submodule.mem_map.1 h1
    have : s = q := Subtype.ext hsq
    rwa [this] at hs
  have hker : S ≤ LinearMap.ker (φ - c • LinearMap.id) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      hφ, hc, map_smul, sub_self]
  have := hker hS
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at this
  exact this

end TernaryPeriodPolynomials.Argument.FareyTree
