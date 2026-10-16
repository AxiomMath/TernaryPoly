module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.RepUnfolding

@[expose] public section


/-!
# Corollary 1.4, Step 1a: the `T`-fixed subspace of `HomogeneousPoly n`

For `v : HomogeneousPoly n`, if `(modularBinaryRep n twist).ρ ModularGroup.T v = v` then `v` is a
scalar multiple of `binaryStandardBasis n 0` (the pure `X 1 ^ n` monomial).

**Proof idea.** Unfolding `ρ(T)` (`modularBinaryRep_apply`) turns the hypothesis into the shear
equation `bind₁ ![X 0 - X 1, X 1] (v : Poly) = (v : Poly)`. Composing with the dehomogenizing
evaluation `aeval ![a, 1]` (`MvPolynomial.aeval_bind₁`) yields a functional equation
`φ(a) = φ(a - 1)` for `φ(a) := aeval ![a,1] (v:Poly)`, hence by induction `φ` agrees with the
constant `φ 0` at every natural number cast into `ℂ`; `Polynomial.eq_of_infinite_eval_eq` upgrades
this (an infinite set of agreements) to literal equality of the univariate dehomogenization
`F := aeval ![Polynomial.X,1] (v:Poly)` with `Polynomial.C (φ 0)`. Finally, comparing basis
coordinates (`Module.Basis.sum_repr`, `Polynomial.coeff_X_pow`, `Module.Basis.ext_elem`) shows this
forces `v = φ(0) • binaryStandardBasis n 0`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein.Binary (substitute linearForm HomogeneousPoly Poly)

variable {n : ℕ} (twist : ℤ)

/-- The complex cast of an integer `SpecialLinearGroup` element, entrywise (local re-derivation;
`RepUnfolding.lean`'s private `castSL_apply` is not visible from this file). -/
private theorem castSL_entry (g : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℂ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

/-- `T⁻¹` is `!![1,-1;0,1]` as an integer matrix (mirrors `EvenInjectivity.lean`'s private
`coe_modularT_inv`, not visible from this file). -/
private theorem coe_modularT_inv :
    ((ModularGroup.T⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, -1; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `T⁻¹` casts to `!![1,-1;0,1]` as a complex matrix. -/
private theorem castT_inv_matrix :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.T⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![1, -1; 0, 1] := by
  ext i j
  rw [castSL_entry]
  fin_cases i <;> fin_cases j <;> norm_num [coe_modularT_inv]

/-- The substitution linear form of `cast T⁻¹` is `![X 0 - X 1, X 1]`. -/
private theorem linearForm_castT_inv :
    linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.T⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) =
      ![X 0 - X 1, X 1] := by
  rw [castT_inv_matrix]
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]; ring

private theorem substitute_castT_inv (p : Poly) :
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL ModularGroup.T⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) p =
      bind₁ ![X 0 - X 1, X 1] p := by
  show bind₁ (linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.T⁻¹) : Matrix (Fin 2) (Fin 2) ℂ)) p =
    bind₁ ![X 0 - X 1, X 1] p
  rw [linearForm_castT_inv]

/-- The dehomogenizing evaluation `v ↦ v(X,1)`, bundled as a `ℂ`-linear map
`HomogeneousPoly n →ₗ[ℂ] Polynomial ℂ`, so that `map_sum`/`map_smul` apply directly. -/
private def dehom (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] Polynomial ℂ :=
  (aeval (![Polynomial.X, 1] : Fin 2 → Polynomial ℂ)).toLinearMap.comp
    (HomogeneousPoly n).subtype

private theorem dehom_apply (x : HomogeneousPoly n) :
    dehom n x = aeval (![Polynomial.X, 1] : Fin 2 → Polynomial ℂ) (x : Poly) := rfl

private theorem dehom_basis (k : Fin (n + 1)) :
    dehom n (binaryStandardBasis n k) = Polynomial.X ^ (k : ℕ) := by
  rw [dehom_apply, binaryStandardBasis_coe]
  simp

/-- **Step 1a.** If `v : HomogeneousPoly n` is fixed by `ρ(T)`, it is a scalar multiple of the
pure `X 1 ^ n` monomial `binaryStandardBasis n 0`. -/
theorem eq_smul_binaryStandardBasis_zero_of_T_fixed (v : HomogeneousPoly n)
    (hv : (modularBinaryRep n twist).ρ ModularGroup.T v = v) :
    ∃ c : ℂ, v = c • binaryStandardBasis n 0 := by
  have hshear : bind₁ (![X 0 - X 1, X 1] : Fin 2 → Poly) (v : Poly) = (v : Poly) := by
    have hT := modularBinaryRep_apply n twist ModularGroup.T v
    rw [hv] at hT
    rw [← substitute_castT_inv]
    exact hT.symm
  set φ : ℂ → ℂ := fun a => aeval (![a, 1] : Fin 2 → ℂ) (v : Poly) with hφ_def
  have hfunc : ∀ a : ℂ, φ a = φ (a - 1) := by
    intro a
    have key := aeval_bind₁ (f := (![a, 1] : Fin 2 → ℂ))
      (g := (![X 0 - X 1, X 1] : Fin 2 → Poly)) (φ := (v : Poly))
    rw [hshear] at key
    have hrw : (fun i : Fin 2 => aeval (![a, 1] : Fin 2 → ℂ) ((![X 0 - X 1, X 1] : Fin 2 → Poly) i))
        = (![a - 1, 1] : Fin 2 → ℂ) := by
      funext i
      fin_cases i <;> simp
    rw [hrw] at key
    exact key
  have hnat : ∀ k : ℕ, φ (k : ℂ) = φ 0 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hstep := hfunc ((k : ℂ) + 1)
      rw [add_sub_cancel_right] at hstep
      have hcast : ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
      rw [hcast, hstep, ih]
  set F : Polynomial ℂ := dehom n v with hF_def
  have hbridge : ∀ a : ℂ, Polynomial.aeval a F = φ a := by
    intro a
    have hhoms : (Polynomial.aeval a).comp
        (aeval (![Polynomial.X, 1] : Fin 2 → Polynomial ℂ) : Poly →ₐ[ℂ] Polynomial ℂ) =
        (aeval (![a, 1] : Fin 2 → ℂ) : Poly →ₐ[ℂ] ℂ) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [AlgHom.comp_apply, MvPolynomial.aeval_X, Polynomial.aeval_X]
    rw [hF_def, dehom_apply]
    exact DFunLike.congr_fun hhoms (v : Poly)
  have hFnat : ∀ k : ℕ, F.eval (k : ℂ) = φ 0 := by
    intro k
    rw [← Polynomial.coe_aeval_eq_eval, hbridge]
    exact hnat k
  have hFeq : F = Polynomial.C (φ 0) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : Set.range ((↑) : ℕ → ℂ) ⊆ {x : ℂ | F.eval x = (Polynomial.C (φ 0)).eval x} := by
      rintro x ⟨k, rfl⟩
      show F.eval (k : ℂ) = (Polynomial.C (φ 0)).eval (k : ℂ)
      rw [Polynomial.eval_C]
      exact hFnat k
    exact Set.Infinite.mono hsub (Set.infinite_range_of_injective Nat.cast_injective)
  refine ⟨φ 0, ?_⟩
  have hDzero : dehom n (φ 0 • binaryStandardBasis n 0) = Polynomial.C (φ 0) := by
    rw [map_smul, dehom_basis 0]
    simp [pow_zero, Algebra.smul_def, Polynomial.algebraMap_eq, mul_one]
  have hDw : dehom n (v - φ 0 • binaryStandardBasis n 0) = 0 := by
    rw [map_sub, ← hF_def, hDzero, hFeq, sub_self]
  have hw0 : v - φ 0 • binaryStandardBasis n 0 = 0 := by
    apply (binaryStandardBasis n).ext_elem
    intro j
    simp only [map_zero, Finsupp.zero_apply]
    set u : HomogeneousPoly n := v - φ 0 • binaryStandardBasis n 0 with hu_def
    have hsum := Module.Basis.sum_repr (binaryStandardBasis n) u
    have hDsum : dehom n u =
        ∑ k : Fin (n + 1), (binaryStandardBasis n).repr u k • Polynomial.X ^ (k : ℕ) := by
      conv_lhs => rw [← hsum]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, dehom_basis]
    rw [hDw] at hDsum
    have hterm0 : ∀ k : Fin (n + 1), k ≠ j →
        ((binaryStandardBasis n).repr u k • (Polynomial.X : Polynomial ℂ) ^ (k : ℕ)).coeff
          (j : ℕ) = 0 := by
      intro k hk
      rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow,
        ite_eq_right (fun he : (j : ℕ) = (k : ℕ) => hk (Fin.ext he.symm))]
      simp
    have htermj : ((binaryStandardBasis n).repr u j • (Polynomial.X : Polynomial ℂ) ^ (j : ℕ)).coeff
        (j : ℕ) = (binaryStandardBasis n).repr u j := by
      rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, ite_eq_left rfl]
      simp
    have hcollapse : (∑ k : Fin (n + 1),
        (binaryStandardBasis n).repr u k • (Polynomial.X : Polynomial ℂ) ^ (k : ℕ)).coeff
        (j : ℕ) = (binaryStandardBasis n).repr u j := by
      rw [Polynomial.finsetSum_coeff]
      exact (Finset.sum_eq_single j (fun k _ hk => hterm0 k hk)
        (fun h => absurd (Finset.mem_univ j) h)).trans htermj
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff (j : ℕ)) hDsum
    rw [Polynomial.coeff_zero, hcollapse] at hc
    exact hc.symm
  rw [sub_eq_zero] at hw0
  exact hw0

end TernaryPeriodPolynomials.Argument.Corollary14
