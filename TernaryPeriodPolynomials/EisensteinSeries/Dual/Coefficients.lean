module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Coefficients
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Funext
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.CoefSpace
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


open MvPolynomial Matrix

/-!
# The coefficient system `E^∨ = E∘ȷ` is the contragredient `E*` (after the coordinate change by `J`)

Formalized by Claude Sonnet 5.5.

Paper: "`ȷ(g) = J (g⁻¹)ᵗ J` exchanges `P`, `Q` and pulls `E` back to its dual, after the fixed linear change of coefficient
coordinates by `J`"; `E*` is the literal linear dual with the contragredient action.

`E = E_{n,e}` is `GeneralEisenstein.homogeneousAction n e` on `HomogeneousPoly n = Sym^n((ℂ³)*)` (`ρ(g) f (X) = det(g)^e f(g⁻¹ X)`), `E*` is
`Representation.dual` of it on `Module.Dual ℂ (HomogeneousPoly n)`.  **Theorem `dualIso_equivariant`**: there is a linear isomorphism
`dualIso n : HomogeneousPoly n ≃ₗ[ℂ] (HomogeneousPoly n)*` with
`dualIso n (ρ(ȷ g) f) = ρ(g)^∨ (dualIso n f)` for every `g ∈ GL₃(ℂ)` and every `e`.

**The identification and its scaling (explicit).**  `Sym^n(V)* ≅ Sym^n(V*)` in characteristic 0 needs the divided-power (multinomial)
scaling.  The symbol map `symbol n : (Sym^n V*)* → Sym^n V*`, `Λφ = Σ_{|s|=n} (n!/s!) φ(X^s) X^s` (equivalently `Λφ(a) = φ(ℓ_a^n)`,
`ℓ_a = Σ a_i X_i`, `eval_symbol`) is a linear isomorphism (`symbolEquiv`) with `Λ(g·φ) = ρ((gᵗ)⁻¹) Λφ` (`symbol_equivariant`); `permJ`
is the coordinate change `f ↦ f(J X)` and `dualIso = Λ⁻¹ ∘ permJ`.  Explicitly (`dualIso_monomial_factorial`): for `|t| = n`,
`n! · (dualIso f)(X^t) = (t₀! t₁! t₂!) · f_{J t}`, i.e. `(dualIso f)(h) = Σ_{|t|=n} (t!/n!) f_{Jt} h_t` (the apolar pairing with
weights `t!/n!`, defined over `ℚ`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein

/-- The antidiagonal permutation matrix `J` (`J i j = 1` iff `j = 2 - i`). -/
def Jm : Matrix (Fin 3) (Fin 3) ℂ := fun i j => if j = i.rev then 1 else 0

theorem Jm_mul_self : Jm * Jm = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

theorem Jm_transpose : Jmᵀ = Jm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, Fin.rev]

/-- The element `ȷ(g) = J (g⁻¹)ᵗ J` of `GL₃(ℂ)`. -/
def jGL (g : GL3) : GL3 where
  val := Jm * ((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm
  inv := Jm * (g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm
  val_inv := by
    calc Jm * ((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm * (Jm * (g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm)
        = Jm * (((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * ((g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ)) * Jm := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Jm Jm, Jm_mul_self, Matrix.one_mul]
      _ = 1 := by
          rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]
          simp [Jm_mul_self]
  inv_val := by
    calc Jm * (g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm * (Jm * ((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm)
        = Jm * (((g : Matrix (Fin 3) (Fin 3) ℂ))ᵀ * (((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ)) * Jm := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Jm Jm, Jm_mul_self, Matrix.one_mul]
      _ = 1 := by
          rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
          simp [Jm_mul_self]

/-- The element `(gᵗ)⁻¹ = (g⁻¹)ᵗ` of `GL₃(ℂ)`. -/
def gtinv (g : GL3) : GL3 where
  val := ((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ
  inv := (g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]
    simp
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
    simp

/-- The linear form `ℓ_a = Σ_i a_i X_i`. -/
def ell (a : Fin 3 → ℂ) : Poly := ∑ i, C (a i) * X i

theorem ell_eq_smul (a : Fin 3 → ℂ) : ell a = ∑ i, a i • (X i : Poly) := by
  simp [ell, smul_eq_C_mul]

theorem ell_homogeneous (a : Fin 3 → ℂ) : (ell a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

/-- The exponents of degree `n`. -/
def Sn (n : ℕ) : Finset (Fin 3 →₀ ℕ) := Finset.finsuppAntidiag Finset.univ n

theorem mem_Sn {n : ℕ} {s : Fin 3 →₀ ℕ} : s ∈ Sn n ↔ s.sum (fun _ m => m) = n := by
  unfold Sn
  rw [Finset.mem_finsuppAntidiag']
  simp

theorem mem_Sn_degree {n : ℕ} {s : Fin 3 →₀ ℕ} : s ∈ Sn n ↔ s.degree = n := by
  rw [mem_Sn]
  rfl

/-- **Multinomial expansion**: `ℓ_a ^ n = Σ_{|s| = n} (n!/s!) a^s X^s`. -/
theorem ell_pow_eq (a : Fin 3 → ℂ) (n : ℕ) :
    ell a ^ n = ∑ s ∈ Sn n, C ((s.multinomial : ℂ) * s.prod (fun r m => a r ^ m)) * monomial s (1 : ℂ) := by
  ext t
  rw [ell_eq_smul, coeff_linearCombination_X_pow_of_fintype]
  simp only [coeff_sum, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases h : t ∈ Sn n
  · rw [ite_eq_left h, ite_eq_left (mem_Sn.1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (mem_Sn.2 h'))]

/-- A homogeneous polynomial of degree `n` is the sum of its monomials of degree `n`. -/
theorem homogeneous_eq_sum {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    p = ∑ s ∈ Sn n, C (p.coeff s) * monomial s (1 : ℂ) := by
  ext t
  simp only [coeff_sum, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases h : t ∈ Sn n
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    by_contra hne
    apply h
    have := hp hne
    rw [mem_Sn_degree, Finsupp.degree_eq_weight_one]
    exact this

/-- The extension to all polynomials of a functional on degree-`n` forms (through the degree-`n` component). -/
def extFun (n : ℕ) (φ : Module.Dual ℂ (HomogeneousPoly n)) : Poly →ₗ[ℂ] ℂ :=
  φ ∘ₗ (homogeneousComponent n).codRestrict (homogeneousSubmodule (Fin 3) ℂ n)
    (fun p => homogeneousComponent_mem n p)

theorem extFun_of_homogeneous {n : ℕ} (φ : Module.Dual ℂ (HomogeneousPoly n)) {p : Poly} (hp : p.IsHomogeneous n) :
    extFun n φ p = φ ⟨p, hp⟩ := by
  unfold extFun
  simp only [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  exact homogeneousComponent_eq_self hp

/-- **The symbol map** `Λ : (Sym^n V*)* → Sym^n V*`: the functional `φ` goes to `Σ_{|s|=n} (n!/s!) φ(X^s) X^s`.  The weights
`n!/s!` (multinomial coefficients) are the divided-power scaling identifying `(Sym^n V*)*` with `Sym^n V*`
(`φ ↦ (a ↦ φ(ℓ_a^n))`). -/
def symbolPoly {n : ℕ} (φ : Module.Dual ℂ (HomogeneousPoly n)) : Poly :=
  ∑ s ∈ Sn n, C ((s.multinomial : ℂ) * extFun n φ (monomial s (1 : ℂ))) * monomial s (1 : ℂ)

theorem symbolPoly_homogeneous {n : ℕ} (φ : Module.Dual ℂ (HomogeneousPoly n)) :
    (symbolPoly φ).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro s hs
  exact (isHomogeneous_monomial (1 : ℂ) (mem_Sn_degree.1 hs)).C_mul _

/-- The pure power `ℓ_a^n` as an element of `Sym^n V*`. -/
def ellH (n : ℕ) (a : Fin 3 → ℂ) : HomogeneousPoly n :=
  ⟨ell a ^ n, by simpa using (ell_homogeneous a).pow n⟩

/-- The symbol map as a linear map. -/
def symbol (n : ℕ) : Module.Dual ℂ (HomogeneousPoly n) →ₗ[ℂ] HomogeneousPoly n where
  toFun φ := ⟨symbolPoly φ, symbolPoly_homogeneous φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    simp only [symbolPoly, extFun, LinearMap.comp_apply, LinearMap.add_apply, map_add, mul_add, add_mul,
      Finset.sum_add_distrib]
    rfl
  map_smul' c φ := by
    apply Subtype.ext
    simp only [symbolPoly, extFun, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    change _ = c • (∑ s ∈ Sn n, _)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [smul_eq_C_mul, ← mul_assoc, ← C_mul]
    congr 3
    ring

theorem symbol_val (n : ℕ) (φ : Module.Dual ℂ (HomogeneousPoly n)) :
    ((symbol n φ : HomogeneousPoly n) : Poly) = symbolPoly φ := rfl

/-- **Evaluation formula**: `Λφ (a) = φ(ℓ_a^n)`. -/
theorem eval_symbol (n : ℕ) (φ : Module.Dual ℂ (HomogeneousPoly n)) (a : Fin 3 → ℂ) :
    eval a (symbol n φ : Poly) = φ (ellH n a) := by
  have h1 : φ (ellH n a) = extFun n φ (ell a ^ n) :=
    (extFun_of_homogeneous φ (ellH n a).2).symm
  rw [h1, ell_pow_eq, map_sum, symbol_val]
  unfold symbolPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e1 : ∀ c : ℂ, extFun n φ (C c * monomial s 1) = c * extFun n φ (monomial s 1) := fun c => by
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  rw [e1, map_mul, eval_C, eval_monomial]
  simp only [one_mul]
  ring

theorem substitute_ell (M : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3 → ℂ) :
    substitute M (ell a) = ell (a ᵥ* M) := by
  simp only [ell, substitute, map_sum, map_mul, bind₁_C_right, bind₁_X_right, linearForm, Matrix.vecMul, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_congr rfl fun x _ => by ring

theorem eval_substitute (M : Matrix (Fin 3) (Fin 3) ℂ) (u : Poly) (a : Fin 3 → ℂ) :
    eval a (substitute M u) = eval (M *ᵥ a) u := by
  unfold substitute
  change aeval a (bind₁ (linearForm M) u) = aeval (M *ᵥ a) u
  rw [aeval_bind₁]
  have : (fun i => aeval a (linearForm M i)) = M *ᵥ a := by
    funext i
    simp [linearForm, Matrix.mulVec, dotProduct]
  rw [this]

theorem det_gtinv (g : GL3) : (GeneralLinearGroup.det (gtinv g) : ℂ) = (GeneralLinearGroup.det g : ℂ)⁻¹ := by
  rw [GeneralLinearGroup.val_det_apply]
  change ((((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ))ᵀ).det = _
  rw [Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val]

theorem homogeneousAction_ellH (n : ℕ) (e : ℤ) (h : GL3) (a : Fin 3 → ℂ) :
    homogeneousAction n e h (ellH n a) =
      (determinantCharacter e h) • ellH n (a ᵥ* ((h⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)) := by
  apply Subtype.ext
  change action e h (ell a ^ n) = determinantCharacter e h • (ell (a ᵥ* ((h⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)) ^ n)
  rw [action_apply, map_pow, substitute_ell]

/-- **Equivariance of the symbol map**: `Λ(g·φ) = ρ((gᵗ)⁻¹) Λφ`. -/
theorem symbol_equivariant (n : ℕ) (e : ℤ) (g : GL3) (φ : Module.Dual ℂ (HomogeneousPoly n)) :
    symbol n ((homogeneousAction n e).dual g φ) = homogeneousAction n e (gtinv g) (symbol n φ) := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro a
  change eval a (symbol n ((homogeneousAction n e).dual g φ) : Poly) =
    eval a (action e (gtinv g) (symbol n φ : Poly))
  rw [eval_symbol]
  have hL : ((homogeneousAction n e).dual g φ) (ellH n a) = determinantCharacter e g⁻¹ * eval (a ᵥ* (g : Matrix (Fin 3) (Fin 3) ℂ)) (symbol n φ : Poly) := by
    change φ (homogeneousAction n e g⁻¹ (ellH n a)) = _
    rw [homogeneousAction_ellH, map_smul, smul_eq_mul, inv_inv, eval_symbol]
  have hR : eval a (action e (gtinv g) (symbol n φ : Poly)) = determinantCharacter e (gtinv g) * eval (a ᵥ* (g : Matrix (Fin 3) (Fin 3) ℂ)) (symbol n φ : Poly) := by
    rw [action_apply, smul_eval, eval_substitute]
    have : (((gtinv g)⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ a = a ᵥ* (g : Matrix (Fin 3) (Fin 3) ℂ) := by
      change (g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ *ᵥ a = _
      rw [Matrix.mulVec_transpose]
    rw [this]
  rw [hL, hR]
  congr 1
  unfold determinantCharacter
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [det_gtinv, map_inv, Units.val_inv_eq_inv_val]

theorem coeff_symbolPoly {n : ℕ} (φ : Module.Dual ℂ (HomogeneousPoly n)) {s : Fin 3 →₀ ℕ} (hs : s ∈ Sn n) :
    (symbolPoly φ).coeff s = (s.multinomial : ℂ) * extFun n φ (monomial s (1 : ℂ)) := by
  unfold symbolPoly
  simp only [coeff_sum, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  rw [ite_eq_left hs]

theorem multinomial_ne_zero (s : Fin 3 →₀ ℕ) : (s.multinomial : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero, Finsupp.multinomial_eq]
  exact (Nat.multinomial_pos _ _).ne'

instance finiteHomogeneousPoly (n : ℕ) : FiniteDimensional ℂ (HomogeneousPoly n) :=
  Module.Finite.of_injective (SeedC3.coefVec n) (SeedC3.coefVec_injective n)

theorem symbol_injective (n : ℕ) : Function.Injective (symbol n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have h0 : symbolPoly φ = 0 := congrArg Subtype.val hφ
  have hs : ∀ s ∈ Sn n, extFun n φ (monomial s (1 : ℂ)) = 0 := by
    intro s hs
    have := coeff_symbolPoly φ hs
    rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (multinomial_ne_zero s)
    · exact h
  apply LinearMap.ext
  intro p
  have h1 : φ p = extFun n φ p.1 := (extFun_of_homogeneous φ p.2).symm
  rw [h1, homogeneous_eq_sum (n := n) p.2, map_sum]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun s hs' => ?_
  rw [← smul_eq_C_mul, map_smul, hs s hs', smul_zero]

/-- **The symbol isomorphism** `Λ : (Sym^n V*)* ≃ Sym^n V*`, `Λφ = Σ_{|s|=n} (n!/s!) φ(X^s) X^s` (equivalently
`Λφ(a) = φ(ℓ_a^n)`). -/
def symbolEquiv (n : ℕ) : Module.Dual ℂ (HomogeneousPoly n) ≃ₗ[ℂ] HomogeneousPoly n :=
  LinearEquiv.ofBijective (symbol n) ⟨symbol_injective n,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := ℂ) (V := HomogeneousPoly n))).1
      (symbol_injective n)⟩

/-- The coordinate change by `J`: `f ↦ f(J X)` (a permutation of the variables `X ↔ Z`). -/
def permJ (n : ℕ) : HomogeneousPoly n ≃ₗ[ℂ] HomogeneousPoly n :=
  LinearEquiv.ofLinearMap
    ((substitute Jm).toLinearMap.restrict (p := homogeneousSubmodule (Fin 3) ℂ n) (q := homogeneousSubmodule (Fin 3) ℂ n)
      (fun f hf => substitute_homogeneous Jm hf))
    ((substitute Jm).toLinearMap.restrict (p := homogeneousSubmodule (Fin 3) ℂ n) (q := homogeneousSubmodule (Fin 3) ℂ n)
      (fun f hf => substitute_homogeneous Jm hf))
    (by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      change substitute Jm (substitute Jm f.1) = f.1
      have := congrArg (fun q : Poly →ₐ[ℂ] Poly => q f.1) (substitute_comp Jm Jm)
      simp only [AlgHom.comp_apply, Jm_mul_self, substitute_one, AlgHom.id_apply] at this
      exact this)
    (by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      change substitute Jm (substitute Jm f.1) = f.1
      have := congrArg (fun q : Poly →ₐ[ℂ] Poly => q f.1) (substitute_comp Jm Jm)
      simp only [AlgHom.comp_apply, Jm_mul_self, substitute_one, AlgHom.id_apply] at this
      exact this)

theorem permJ_val (n : ℕ) (f : HomogeneousPoly n) : ((permJ n f : HomogeneousPoly n) : Poly) = substitute Jm f.1 := rfl

theorem det_Jm_sq : Jm.det * Jm.det = 1 := by
  rw [← Matrix.det_mul, Jm_mul_self, Matrix.det_one]

theorem det_jGL (g : GL3) : (GeneralLinearGroup.det (jGL g) : ℂ) = (GeneralLinearGroup.det g : ℂ)⁻¹ := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
  change (Jm * (((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ))ᵀ * Jm).det = _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have h := det_Jm_sq
  have e : (((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ)).det = ((g : Matrix (Fin 3) (Fin 3) ℂ).det)⁻¹ := by
    rw [← GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]
  rw [e]
  linear_combination (((g : Matrix (Fin 3) (Fin 3) ℂ).det)⁻¹) * h

theorem permJ_equivariant (n : ℕ) (e : ℤ) (g : GL3) (f : HomogeneousPoly n) :
    permJ n (homogeneousAction n e (jGL g) f) = homogeneousAction n e (gtinv g) (permJ n f) := by
  apply Subtype.ext
  change substitute Jm (action e (jGL g) f.1) = action e (gtinv g) (substitute Jm f.1)
  rw [action_apply, action_apply, map_smul]
  have h1 := congrArg (fun q : Poly →ₐ[ℂ] Poly => q f.1) (substitute_comp Jm ((jGL g)⁻¹ : GL3))
  have h2 := congrArg (fun q : Poly →ₐ[ℂ] Poly => q f.1) (substitute_comp ((gtinv g)⁻¹ : GL3) Jm)
  simp only [AlgHom.comp_apply] at h1 h2
  rw [h1, h2]
  have hm : (((jGL g)⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) * Jm = Jm * (((gtinv g)⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) := by
    change Jm * (g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * Jm * Jm = Jm * (g : Matrix (Fin 3) (Fin 3) ℂ)ᵀ
    rw [Matrix.mul_assoc _ Jm Jm, Jm_mul_self, Matrix.mul_one]
  rw [hm]
  congr 1
  unfold determinantCharacter
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [det_jGL, det_gtinv]

/-- **The equivariant isomorphism `E ≅ E*` (before twisting by `ȷ`)**: `f ↦ Λ⁻¹(f(J X))`. -/
def dualIso (n : ℕ) : HomogeneousPoly n ≃ₗ[ℂ] Module.Dual ℂ (HomogeneousPoly n) :=
  (permJ n).trans (symbolEquiv n).symm

/-- **`E_{n,e}∘ȷ ≅ (E_{n,e})*`**: for every `g ∈ GL₃(ℂ)` (and every determinant exponent `e`),
`dualIso (ρ(ȷ(g)) f) = ρ(g)^∨ (dualIso f)`, with `ȷ(g) = J (g⁻¹)ᵗ J` and `ρ^∨` the contragredient `φ ↦ φ ∘ ρ(g⁻¹)`. -/
theorem dualIso_equivariant (n : ℕ) (e : ℤ) (g : GL3) (f : HomogeneousPoly n) :
    dualIso n (homogeneousAction n e (jGL g) f) = (homogeneousAction n e).dual g (dualIso n f) := by
  apply (symbolEquiv n).injective
  change symbol n _ = symbol n _
  have h1 : symbol n (dualIso n (homogeneousAction n e (jGL g) f)) = permJ n (homogeneousAction n e (jGL g) f) :=
    (symbolEquiv n).apply_symm_apply _
  have h2 : symbol n (dualIso n f) = permJ n f := (symbolEquiv n).apply_symm_apply _
  have h3 := symbol_equivariant n e g (dualIso n f)
  change symbol n _ = _ at h1
  rw [h1, h3]
  change _ = homogeneousAction n e (gtinv g) (symbol n (dualIso n f))
  rw [h2]
  exact permJ_equivariant n e g f

/-- Reversal of an exponent vector, `(s₀, s₁, s₂) ↦ (s₂, s₁, s₀)`. -/
def revExp (s : Fin 3 →₀ ℕ) : Fin 3 →₀ ℕ := Finsupp.mapDomain Fin.rev s

theorem revExp_revExp (s : Fin 3 →₀ ℕ) : revExp (revExp s) = s := by
  unfold revExp
  rw [← Finsupp.mapDomain_comp]
  have : (Fin.rev ∘ Fin.rev : Fin 3 → Fin 3) = id := funext Fin.rev_rev
  rw [this, Finsupp.mapDomain_id]

theorem linearForm_Jm : linearForm Jm = fun i => (X i.rev : Poly) := by
  funext i
  fin_cases i <;> simp [linearForm, Jm, Fin.rev]

theorem substitute_Jm_eq_rename : substitute Jm = (rename Fin.rev : Poly →ₐ[ℂ] Poly) := by
  rw [rename_eq_aeval]
  unfold substitute
  rw [linearForm_Jm]
  rfl

theorem coeff_permJ (n : ℕ) (f : HomogeneousPoly n) (t : Fin 3 →₀ ℕ) :
    (permJ n f : Poly).coeff t = f.1.coeff (revExp t) := by
  rw [permJ_val, substitute_Jm_eq_rename]
  have := coeff_rename_mapDomain Fin.rev Fin.rev_injective f.1 (revExp t)
  have h' : Finsupp.mapDomain Fin.rev (revExp t) = t := revExp_revExp t
  rw [h'] at this
  exact this

/-- **The pairing `E × E → ℂ` explicitly** (the scaling of the identification `E* ≅ E ∘ ȷ` is the multinomial coefficient):
`n!/t! · φ(X^t) = f_{J t}` for `φ = dualIso f` and `|t| = n`, i.e. `φ(h) = Σ_{|t|=n} (t!/n!) f_{J t} h_t`. -/
theorem dualIso_monomial (n : ℕ) (f : HomogeneousPoly n) {t : Fin 3 →₀ ℕ} (ht : t ∈ Sn n) :
    (t.multinomial : ℂ) * extFun n (dualIso n f) (monomial t (1 : ℂ)) = f.1.coeff (revExp t) := by
  have h := coeff_symbolPoly (dualIso n f) ht
  have h2 : symbolPoly (dualIso n f) = ((permJ n f : HomogeneousPoly n) : Poly) := by
    have := (symbolEquiv n).apply_symm_apply (permJ n f)
    exact congrArg Subtype.val this
  rw [h2, coeff_permJ] at h
  exact h.symm

/-- The same with factorials: `n! · φ(X^t) = (t₀! t₁! t₂!) · f_{J t}`. -/
theorem dualIso_monomial_factorial (n : ℕ) (f : HomogeneousPoly n) {t : Fin 3 →₀ ℕ} (ht : t ∈ Sn n) :
    ((n.factorial : ℕ) : ℂ) * extFun n (dualIso n f) (monomial t (1 : ℂ)) =
      (((∏ i, (t i).factorial : ℕ)) : ℂ) * f.1.coeff (revExp t) := by
  rw [← dualIso_monomial n f ht, ← mul_assoc]
  congr 1
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin 3)) (⇑t)
  have hs : (t.sum fun _ x => x) = n := mem_Sn.1 ht
  rw [Finsupp.sum_of_support_subset t (Finset.subset_univ _) _ (fun _ _ => rfl)] at hs
  rw [hs, ← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ t.support)] at h
  exact_mod_cast h.symm

end TernaryPeriodPolynomials.Argument.EisensteinDual
