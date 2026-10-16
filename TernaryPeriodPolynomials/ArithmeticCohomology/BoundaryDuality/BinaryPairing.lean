module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.BinaryCoefficients

@[expose] public section


/-!
# The classical invariant pairing on binary forms

On the space `HomogeneousPoly n` of binary forms of degree `n` we construct the bilinear form
`binaryPairing n` with `⟨x^i y^(n-i), x^j y^(n-j)⟩ = δ_{i+j,n} (-1)^i / C(n,i)`, prove that it is
perfect (nondegenerate in each variable), and prove its `GL₂(ℂ)`-semi-invariance

  `⟨g·v, g'·w⟩ = (det g)^(e + e' - n) ⟨v, w⟩`

for the actions `homogeneousAction n e` and `homogeneousAction n e'`
(`g · p = det(g)^e · p(g⁻¹ x)`).  In particular for `e + e' = n` the pairing is exactly invariant.

The proof of semi-invariance uses the identity `⟨(a x + b y)^n, (c x + d y)^n⟩ = (b c - a d)^n`
and the fact that the powers of linear forms span the forms of degree `n`
(a one-variable Vandermonde argument through `Polynomial.funext`).
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.BinaryPairing

open GeneralEisenstein.Binary

/-! ### Exponent vectors -/

/-- The exponent vector of `x^a y^b`. -/
def mon (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem mon_zero (a b : ℕ) : mon a b 0 = a := by
  simp [mon]

@[simp] theorem mon_one (a b : ℕ) : mon a b 1 = b := by
  simp [mon]

theorem mon_inj {a b c d : ℕ} (h : mon a b = mon c d) : a = c ∧ b = d := by
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp only [mon_zero, mon_one] at h0 h1
  exact ⟨h0, h1⟩

theorem degree_fin_two (d : Fin 2 →₀ ℕ) : Finsupp.degree d = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem degree_mon (a b : ℕ) : Finsupp.degree (mon a b) = a + b := by
  rw [degree_fin_two, mon_zero, mon_one]

theorem leOfMemRange {n j : ℕ} (hj : j ∈ Finset.range (n + 1)) : j ≤ n := by
  have := Finset.mem_range.mp hj
  omega

/-- The monomial `x^j y^(n-j)`. -/
abbrev xyPow (n j : ℕ) : Poly := monomial (mon j (n - j)) (1 : ℂ)

/-- The monomial `x^(n-j) y^j`. -/
abbrev xyPowD (n j : ℕ) : Poly := monomial (mon (n - j) j) (1 : ℂ)

theorem xyPow_isHomogeneous {n j : ℕ} (hj : j ≤ n) : (xyPow n j).IsHomogeneous n :=
  isHomogeneous_monomial (d := mon j (n - j)) (1 : ℂ) (by rw [degree_mon]; omega)

theorem xyPowD_isHomogeneous {n j : ℕ} (hj : j ≤ n) : (xyPowD n j).IsHomogeneous n :=
  isHomogeneous_monomial (d := mon (n - j) j) (1 : ℂ) (by rw [degree_mon]; omega)

theorem xyPow_mem {n j : ℕ} (hj : j ≤ n) : xyPow n j ∈ HomogeneousPoly n :=
  (mem_homogeneousSubmodule n _).mpr (xyPow_isHomogeneous hj)

theorem xyPowD_mem {n j : ℕ} (hj : j ≤ n) : xyPowD n j ∈ HomogeneousPoly n :=
  (mem_homogeneousSubmodule n _).mpr (xyPowD_isHomogeneous hj)

theorem isHomogeneous_of_mem' {n : ℕ} (v : HomogeneousPoly n) : (v : Poly).IsHomogeneous n :=
  (mem_homogeneousSubmodule n _).mp v.2

/-- A homogeneous binary form is the sum of its monomials. -/
theorem hom_expand {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    p = ∑ j ∈ Finset.range (n + 1), p.coeff (mon j (n - j)) • xyPow n j := by
  ext d
  rw [coeff_sum]
  simp only [xyPow, coeff_smul, coeff_monomial, smul_eq_mul]
  by_cases hd : d 0 + d 1 = n
  · have hdm : mon (d 0) (n - d 0) = d := by
      refine Finsupp.ext fun k => ?_
      fin_cases k
      · simp
      · simp
        omega
    rw [Finset.sum_eq_single (d 0)]
    · rw [hdm]
      simp
    · intro j _ hj
      have hne : ¬ (mon j (n - j) = d) := by
        intro h
        apply hj
        have h0 := DFunLike.congr_fun h 0
        simp only [mon_zero] at h0
        exact h0
      rw [ite_eq_right hne, mul_zero]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · rw [hp.coeff_eq_zero (d := d) (by rw [degree_fin_two]; exact hd)]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hne : ¬ (mon j (n - j) = d) := by
      intro h
      have h0 := DFunLike.congr_fun h 0
      have h1 := DFunLike.congr_fun h 1
      simp only [mon_zero, mon_one] at h0 h1
      omega
    rw [ite_eq_right hne, mul_zero]

theorem eq_zero_of_coeff {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n)
    (h : ∀ j ≤ n, p.coeff (mon j (n - j)) = 0) : p = 0 := by
  rw [hom_expand hp]
  exact Finset.sum_eq_zero fun j hj => by
    rw [h j (leOfMemRange hj), zero_smul]

theorem eq_zero_of_coeff_dual {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n)
    (h : ∀ j ≤ n, p.coeff (mon (n - j) j) = 0) : p = 0 := by
  refine eq_zero_of_coeff hp fun j hj => ?_
  have := h (n - j) (Nat.sub_le n j)
  rwa [Nat.sub_sub_self hj] at this

/-! ### The pairing on all polynomials -/

/-- Normalisation `(-1)^i / C(n,i)` of the pairing. -/
def pairCoef (n i : ℕ) : ℂ := (-1) ^ i * ((n.choose i : ℕ) : ℂ)⁻¹

theorem pairCoef_ne_zero {n i : ℕ} (hi : i ≤ n) : pairCoef n i ≠ 0 := by
  unfold pairCoef
  have h : ((n.choose i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hi).ne'
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero h)

/-- The bilinear form on `MvPolynomial (Fin 2) ℂ` reading only the degree-`n` coefficients. -/
def binForm (n : ℕ) : Poly →ₗ[ℂ] Poly →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun p q => ∑ i ∈ Finset.range (n + 1),
      pairCoef n i * (p.coeff (mon i (n - i)) * q.coeff (mon (n - i) i)))
    (by
      intro p₁ p₂ q
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul, mul_add, Finset.sum_add_distrib])
    (by
      intro c p q
      simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (by
      intro p q₁ q₂
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro c p q
      simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

theorem binForm_apply (n : ℕ) (p q : Poly) :
    binForm n p q = ∑ i ∈ Finset.range (n + 1),
      pairCoef n i * (p.coeff (mon i (n - i)) * q.coeff (mon (n - i) i)) := rfl

theorem binForm_right_mono {n j : ℕ} (hj : j ≤ n) (p : Poly) :
    binForm n p (xyPowD n j) = pairCoef n j * p.coeff (mon j (n - j)) := by
  rw [binForm_apply]
  simp only [xyPowD, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    have hne : ¬ (mon (n - j) j = mon (n - i) i) := fun h => hi (mon_inj h).2.symm
    simp [hne]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem binForm_left_mono {n j : ℕ} (hj : j ≤ n) (q : Poly) :
    binForm n (xyPow n j) q = pairCoef n j * q.coeff (mon (n - j) j) := by
  rw [binForm_apply]
  simp only [xyPow, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    have hne : ¬ (mon j (n - j) = mon i (n - i)) := fun h => hi (mon_inj h).1.symm
    simp [hne]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ### Powers of linear forms -/

theorem monomial_mon (m k : ℕ) : monomial (mon m k) (1 : ℂ) = (X 0 ^ m * X 1 ^ k : Poly) := by
  rw [mon, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one]

theorem linPow_expand (a b : ℂ) (n : ℕ) :
    (C a * X 0 + C b * X 1 : Poly) ^ n =
      ∑ m ∈ Finset.range (n + 1), (a ^ m * b ^ (n - m) * (n.choose m : ℂ)) • xyPow n m := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [xyPow, monomial_mon, smul_eq_C_mul, mul_pow, mul_pow, ← C_pow, ← C_pow, map_mul, map_mul,
    map_natCast]
  ring

theorem coeff_linPow (a b : ℂ) (n i : ℕ) (hi : i ≤ n) :
    ((C a * X 0 + C b * X 1 : Poly) ^ n).coeff (mon i (n - i)) =
      a ^ i * b ^ (n - i) * (n.choose i : ℂ) := by
  rw [linPow_expand, coeff_sum]
  simp only [xyPow, coeff_smul, coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hne : ¬ (mon j (n - j) = mon i (n - i)) := fun h => hj (mon_inj h).1
    simp [hne]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_linPow_dual (a b : ℂ) (n i : ℕ) (hi : i ≤ n) :
    ((C a * X 0 + C b * X 1 : Poly) ^ n).coeff (mon (n - i) i) =
      a ^ (n - i) * b ^ i * (n.choose i : ℂ) := by
  have h := coeff_linPow a b n (n - i) (Nat.sub_le n i)
  rwa [Nat.sub_sub_self hi, Nat.choose_symm hi] at h

/-- `⟨(a x + b y)^n, (c x + d y)^n⟩ = (b c - a d)^n`. -/
theorem binForm_linPow (n : ℕ) (a b c d : ℂ) :
    binForm n ((C a * X 0 + C b * X 1 : Poly) ^ n) ((C c * X 0 + C d * X 1 : Poly) ^ n) =
      (b * c - a * d) ^ n := by
  have key : (b * c - a * d) ^ n = ∑ i ∈ Finset.range (n + 1),
      (-(a * d)) ^ i * (b * c) ^ (n - i) * (n.choose i : ℂ) := by
    rw [show b * c - a * d = -(a * d) + b * c by ring, add_pow]
  rw [binForm_apply, key]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := leOfMemRange hi
  rw [coeff_linPow a b n i hi', coeff_linPow_dual c d n i hi']
  have hne : ((n.choose i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hi').ne'
  have hcancel : ((n.choose i : ℕ) : ℂ)⁻¹ * ((n.choose i : ℕ) : ℂ) = 1 := inv_mul_cancel₀ hne
  have h1 : (-(a * d)) ^ i = (-1) ^ i * (a ^ i * d ^ i) := by
    rw [neg_pow (a * d) i, mul_pow a d i]
  rw [h1]
  unfold pairCoef
  linear_combination
    ((-1 : ℂ) ^ i * a ^ i * b ^ (n - i) * c ^ (n - i) * d ^ i * ((n.choose i : ℕ) : ℂ)) * hcancel

/-! ### Transformation of powers of linear forms -/

theorem substitute_C (M : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : substitute M (C a) = C a := by
  simp [substitute]

theorem substitute_linPow (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) (n : ℕ) :
    substitute M ((C a * X 0 + C b * X 1 : Poly) ^ n) =
      (C (a * M 0 0 + b * M 1 0) * X 0 + C (a * M 0 1 + b * M 1 1) * X 1 : Poly) ^ n := by
  rw [map_pow]
  congr 1
  simp only [map_add, map_mul, substitute_X, substitute_C, linearForm, Fin.sum_univ_two]
  ring

theorem binForm_substitute_linPow (M : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (a b c d : ℂ) :
    binForm n (substitute M ((C a * X 0 + C b * X 1 : Poly) ^ n))
        (substitute M ((C c * X 0 + C d * X 1 : Poly) ^ n)) =
      M.det ^ n * binForm n ((C a * X 0 + C b * X 1 : Poly) ^ n)
        ((C c * X 0 + C d * X 1 : Poly) ^ n) := by
  rw [substitute_linPow, substitute_linPow, binForm_linPow, binForm_linPow, ← mul_pow,
    Matrix.det_fin_two]
  congr 1
  ring

/-! ### Powers of linear forms span -/

/-- Two linear functionals agreeing on all `(a x + y)^n` agree on every monomial `x^j y^(n-j)`. -/
theorem eq_of_linPow (n : ℕ) (f g : Poly →ₗ[ℂ] ℂ)
    (h : ∀ a : ℂ, f ((C a * X 0 + C 1 * X 1 : Poly) ^ n) = g ((C a * X 0 + C 1 * X 1 : Poly) ^ n)) :
    ∀ j ≤ n, f (xyPow n j) = g (xyPow n j) := by
  intro j hj
  have hP : (∑ i ∈ Finset.range (n + 1),
      Polynomial.C ((n.choose i : ℂ) * (f (xyPow n i) - g (xyPow n i))) * Polynomial.X ^ i) = 0 := by
    apply Polynomial.funext
    intro a
    have h2 := sub_eq_zero.mpr (h a)
    rw [linPow_expand, map_sum, map_sum, ← Finset.sum_sub_distrib] at h2
    rw [Polynomial.eval_zero]
    refine Eq.trans ?_ h2
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_smul, smul_eq_mul]
    ring
  have hcoef : ((n.choose j : ℕ) : ℂ) * (f (xyPow n j) - g (xyPow n j)) = 0 := by
    have h3 := congrArg (fun P => Polynomial.coeff P j) hP
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at h3
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (by omega))] at h3
    exact h3
  have hne : ((n.choose j : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcoef).resolve_left hne)

theorem binForm_substitute_mono_linPow (M : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (c : ℂ) :
    ∀ j ≤ n, binForm n (substitute M (xyPow n j))
        (substitute M ((C c * X 0 + C 1 * X 1 : Poly) ^ n)) =
      M.det ^ n * binForm n (xyPow n j) ((C c * X 0 + C 1 * X 1 : Poly) ^ n) := by
  have key := eq_of_linPow n
    (((binForm n).flip (substitute M ((C c * X 0 + C 1 * X 1 : Poly) ^ n))).comp
      (substitute M).toLinearMap)
    (M.det ^ n • (binForm n).flip ((C c * X 0 + C 1 * X 1 : Poly) ^ n))
    (fun a => by exact binForm_substitute_linPow M n a 1 c 1)
  intro j hj
  exact key j hj

theorem binForm_substitute_mono (M : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    ∀ i ≤ n, ∀ j ≤ n, binForm n (substitute M (xyPow n i)) (substitute M (xyPow n j)) =
      M.det ^ n * binForm n (xyPow n i) (xyPow n j) := by
  intro i hi
  have key := eq_of_linPow n
    ((binForm n (substitute M (xyPow n i))).comp (substitute M).toLinearMap)
    (M.det ^ n • binForm n (xyPow n i))
    (fun c => by exact binForm_substitute_mono_linPow M n c i hi)
  intro j hj
  exact key j hj

theorem eq_of_basis (n : ℕ) (F G : Poly →ₗ[ℂ] Poly →ₗ[ℂ] ℂ)
    (h : ∀ i ≤ n, ∀ j ≤ n, F (xyPow n i) (xyPow n j) = G (xyPow n i) (xyPow n j))
    {p q : Poly} (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous n) : F p q = G p q := by
  rw [hom_expand hp, hom_expand hq]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [h j (leOfMemRange hj) i (leOfMemRange hi)]

/-- Substitution by `M` scales the pairing on degree-`n` forms by `det M ^ n`. -/
theorem binForm_substitute (M : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ} {p q : Poly}
    (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous n) :
    binForm n (substitute M p) (substitute M q) = M.det ^ n * binForm n p q := by
  have key := eq_of_basis n
    ((binForm n).compl₁₂ (substitute M).toLinearMap (substitute M).toLinearMap)
    (M.det ^ n • binForm n)
    (fun i hi j hj => by exact binForm_substitute_mono M n i hi j hj) hp hq
  exact key

/-! ### The pairing on `HomogeneousPoly n` -/

/-- The classical invariant pairing on binary forms of degree `n`:
`⟨x^i y^(n-i), x^j y^(n-j)⟩ = δ_{i+j,n} (-1)^i / C(n,i)`. -/
def binaryPairing (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ :=
  (binForm n).compl₁₂ (HomogeneousPoly n).subtype (HomogeneousPoly n).subtype

@[simp] theorem binaryPairing_apply (n : ℕ) (v w : HomogeneousPoly n) :
    binaryPairing n v w = binForm n (v : Poly) (w : Poly) := rfl

theorem binaryPairing_left_eq_zero (n : ℕ) {v : HomogeneousPoly n}
    (h : ∀ w : HomogeneousPoly n, binaryPairing n v w = 0) : v = 0 := by
  have hv : (v : Poly) = 0 := by
    refine eq_zero_of_coeff (isHomogeneous_of_mem' v) fun j hj => ?_
    have h' : binForm n (v : Poly) (xyPowD n j) = 0 := h ⟨xyPowD n j, xyPowD_mem hj⟩
    rw [binForm_right_mono hj] at h'
    exact (mul_eq_zero.mp h').resolve_left (pairCoef_ne_zero hj)
  exact Subtype.ext hv

theorem binaryPairing_right_eq_zero (n : ℕ) {w : HomogeneousPoly n}
    (h : ∀ v : HomogeneousPoly n, binaryPairing n v w = 0) : w = 0 := by
  have hw : (w : Poly) = 0 := by
    refine eq_zero_of_coeff_dual (isHomogeneous_of_mem' w) fun j hj => ?_
    have h' : binForm n (xyPow n j) (w : Poly) = 0 := h ⟨xyPow n j, xyPow_mem hj⟩
    rw [binForm_left_mono hj] at h'
    exact (mul_eq_zero.mp h').resolve_left (pairCoef_ne_zero hj)
  exact Subtype.ext hw

theorem binaryPairing_injective_left (n : ℕ) : Function.Injective (binaryPairing n) :=
  (injective_iff_map_eq_zero _).mpr fun _ hv =>
    binaryPairing_left_eq_zero n fun w => LinearMap.congr_fun hv w

theorem binaryPairing_injective_right (n : ℕ) : Function.Injective (binaryPairing n).flip :=
  (injective_iff_map_eq_zero _).mpr fun _ hw =>
    binaryPairing_right_eq_zero n fun v => LinearMap.congr_fun hw v

/-- The coefficients of `x^j y^(n-j)`, `j = 0, …, n`. -/
def coeffMap (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun p j := (p : Poly).coeff (mon j (n - j))
  map_add' p q := by
    ext j
    simp
  map_smul' c p := by
    ext j
    simp

theorem coeffMap_apply (n : ℕ) (p : HomogeneousPoly n) (j : Fin (n + 1)) :
    coeffMap n p j = (p : Poly).coeff (mon j (n - j)) := rfl

/-- Binary forms of degree `n` form a finite-dimensional space. -/
instance instModuleFiniteHomogeneousPoly (n : ℕ) : Module.Finite ℂ (HomogeneousPoly n) := by
  refine Module.Finite.of_injective (coeffMap n)
    ((injective_iff_map_eq_zero (coeffMap n)).mpr fun p hp => ?_)
  have h : ∀ j ≤ n, (p : Poly).coeff (mon j (n - j)) = 0 := fun j hj => by
    have h0 := congrFun hp ⟨j, by omega⟩
    exact (coeffMap_apply n p ⟨j, by omega⟩).symm.trans h0
  exact Subtype.ext (eq_zero_of_coeff (isHomogeneous_of_mem' p) h)

/-! ### Semi-invariance under `GL₂(ℂ)` -/

theorem determinantCharacter_apply (e : ℤ) (g : GL2) :
    determinantCharacter e g = ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ e := rfl

theorem det_inv_coe (g : GL2) :
    (((g⁻¹ : GL2) : Matrix (Fin 2) (Fin 2) ℂ)).det =
      (((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ))⁻¹ := by
  have h1 : (g : Matrix (Fin 2) (Fin 2) ℂ) * ((g⁻¹ : GL2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Units.mul_inv g
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, ← Matrix.GeneralLinearGroup.val_det_apply g] at h2
  exact (inv_eq_of_mul_eq_one_right h2).symm

theorem zpow_aux (d : ℂ) (hd : d ≠ 0) (e e' : ℤ) (n : ℕ) (X : ℂ) :
    d ^ e * (d ^ e' * ((d⁻¹) ^ n * X)) = d ^ (e + e' - (n : ℤ)) * X := by
  rw [zpow_sub₀ hd, zpow_add₀ hd, zpow_natCast, div_eq_mul_inv, inv_pow]
  ring

/-- Semi-invariance of the pairing: `⟨g·v, g'·w⟩ = (det g)^(e + e' - n) ⟨v, w⟩`,
where `g · p = det(g)^e p(g⁻¹ x)` and `g' · p = det(g)^e' p(g⁻¹ x)`. -/
theorem binaryPairing_homogeneousAction (n : ℕ) (e e' : ℤ) (g : GL2)
    (v w : HomogeneousPoly n) :
    binaryPairing n (homogeneousAction n e g v) (homogeneousAction n e' g w) =
      ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ (e + e' - (n : ℤ)) * binaryPairing n v w := by
  have hv := isHomogeneous_of_mem' v
  have hw := isHomogeneous_of_mem' w
  simp only [binaryPairing_apply, homogeneousAction_coe, action_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  rw [binForm_substitute _ hv hw, det_inv_coe g]
  simp only [determinantCharacter_apply]
  rw [mul_left_comm]
  exact zpow_aux _ (Units.ne_zero _) e e' n _

/-- Exact invariance when the two determinant twists add up to `n`. -/
theorem binaryPairing_homogeneousAction_invariant (n : ℕ) (e e' : ℤ) (he : e + e' = (n : ℤ))
    (g : GL2) (v w : HomogeneousPoly n) :
    binaryPairing n (homogeneousAction n e g v) (homogeneousAction n e' g w) =
      binaryPairing n v w := by
  rw [binaryPairing_homogeneousAction, he, sub_self, zpow_zero, one_mul]

/-- Elements of `SL₂` (determinant one) preserve the pairing for every twist. -/
theorem binaryPairing_homogeneousAction_of_det_eq_one (n : ℕ) (e e' : ℤ) (g : GL2)
    (hg : Matrix.GeneralLinearGroup.det g = 1) (v w : HomogeneousPoly n) :
    binaryPairing n (homogeneousAction n e g v) (homogeneousAction n e' g w) =
      binaryPairing n v w := by
  rw [binaryPairing_homogeneousAction, hg]
  simp

end TernaryPeriodPolynomials.BoundaryDuality.BinaryPairing

end
