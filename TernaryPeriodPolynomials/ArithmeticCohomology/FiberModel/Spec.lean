module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Defs

@[expose] public section


/-!
# The literal fiber functions are the abstract fiber systems for `E_{n,t}`

The literal equations `eq:fiber-signed` and `eq:fiber-norm` (with the characters `χ_t`, the direct
substitution `∣` and the covector multiplication modulo three) are equivalent to the abstract
system of `FiberModel.Abstract` for the left action `coeff n t` of `GL₃(ℤ)` on `E_{n,t}`: indeed
`ρ_t(h⁻¹) f = det(h)^t (f ∣ h)`, and `χ_t(h) = sgn(π) det(h)^t` for every signed permutation
matrix `h = D π`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryApartmentFrames

theorem bar_eq_substitute (g : IntegralGL) :
    bar g.val = PolynomialGLAction.substitute (ReferenceCoefficientMatrices.rational g).val := by
  unfold bar PolynomialGLAction.substitute PolynomialGLAction.linearForm
  congr 1

theorem rational_det (g : IntegralGL) :
    ((Matrix.GeneralLinearGroup.det (ReferenceCoefficientMatrices.rational g) : ℚˣ) : ℚ) =
      ((g.val.det : ℤ) : ℚ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((g.val.map (Int.castRingHom ℚ)).det : ℚ) = _
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- `ρ_t(g⁻¹) f = det(g)^t (f ∣ g)`. -/
theorem coeff_inv_apply (n : ℕ) (t : Fin 2) (g : IntegralGL) (f : V n) :
    ((coeff n t g⁻¹ f : V n) : MvPolynomial (Fin 3) ℚ) =
      ((g.val.det : ℤ) : ℚ) ^ (t : ℕ) • bar g.val f := by
  show PolynomialGLAction.action _ (ReferenceCoefficientMatrices.rational g⁻¹) f.1 = _
  rw [PolynomialGLAction.action_apply, map_inv, inv_inv, ← bar_eq_substitute]
  show ((Matrix.GeneralLinearGroup.det ((ReferenceCoefficientMatrices.rational g)⁻¹) : ℚˣ) : ℚ) ^
    (-((t : ℕ) : ℤ)) • _ = _
  rw [map_inv, Units.val_inv_eq_inv_val, rational_det]
  simp [zpow_neg]


/-- The sign set of a diagonal sign vector. -/
def Dof (s : Finset (Fin 3)) : Fin 3 → ℤˣ := fun i => if i ∈ s then -1 else 1

/-- The set of coordinates where a sign vector is `-1`. -/
def sOf (D : Fin 3 → ℤˣ) : Finset (Fin 3) := Finset.univ.filter fun i => D i = -1

theorem Dof_val (s : Finset (Fin 3)) (i : Fin 3) : ((Dof s i : ℤˣ) : ℤ) = signEntry s i := by
  unfold Dof signEntry
  split_ifs <;> simp

theorem Dof_sOf (D : Fin 3 → ℤˣ) : Dof (sOf D) = D := by
  funext i
  unfold Dof sOf
  rcases Int.units_eq_one_or (D i) with h | h <;> simp [h]

theorem sOf_Dof (s : Finset (Fin 3)) : sOf (Dof s) = s := by
  ext i
  unfold sOf Dof
  by_cases h : i ∈ s <;> simp [h]

theorem signedPerm_val (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) :
    (signedPerm s π).val = signedPermMatrix (Dof s) π⁻¹ := by
  unfold signedPerm signedPermMatrix
  rw [Units.val_mul, permFrame_val]
  congr 1
  change Matrix.diagonal (signEntry s) = _
  congr 1
  funext i
  exact (Dof_val s i).symm

theorem det_signedPermMatrix (D : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3)) :
    (signedPermMatrix D π).det = (∏ i, ((D i : ℤˣ) : ℤ)) * ((Equiv.Perm.sign π : ℤˣ) : ℤ) := by
  unfold signedPermMatrix
  rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]
  simp

theorem chi_eq (t : Fin 2) (D : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3)) :
    chi t D π = ((Equiv.Perm.sign π⁻¹ : ℤˣ) : ℤ) * (signedPermMatrix D π).det ^ (t : ℕ) := by
  rw [det_signedPermMatrix, Equiv.Perm.sign_inv]
  unfold chi
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> fin_cases t <;> simp [h]

theorem signed_rhs (n : ℕ) (t : Fin 2) (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (x : V n) :
    ((((Equiv.Perm.sign π : ℤˣ) : ℤ) • coeff n t (signedPerm s π)⁻¹ x : V n) :
        MvPolynomial (Fin 3) ℚ) =
      (chi t (Dof s) π⁻¹ : ℚ) • bar (signedPermMatrix (Dof s) π⁻¹) x := by
  rw [Submodule.coe_smul_of_tower, coeff_inv_apply, signedPerm_val, ← Int.cast_smul_eq_zsmul ℚ,
    smul_smul, chi_eq, inv_inv]
  push_cast
  rfl

theorem bar_Amat : bar Amat = TernaryPoly.A := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [bar, Amat, TernaryPoly.A, Fin.sum_univ_three, sub_eq_add_neg]

theorem Amat_sq : Amat * Amat = !![-1, 1, 0; -1, 0, 0; 0, 0, 1] := by
  decide +kernel

theorem bar_Amat_sq : bar (Amat * Amat) = TernaryPoly.A2 := by
  rw [Amat_sq]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [bar, TernaryPoly.A2, Fin.sum_univ_three, neg_add_eq_sub]

theorem a_val : ReferenceCoefficientMatrices.a.val = Amat := rfl

theorem a_sq_val : (ReferenceCoefficientMatrices.a ^ 2).val = Amat * Amat := by
  rw [Units.val_pow_eq_pow_val, pow_two]
  rfl

theorem coeff_a_apply (n : ℕ) (t : Fin 2) (f : V n) :
    ((coeff n t ReferenceCoefficientMatrices.a f : V n) : MvPolynomial (Fin 3) ℚ) =
      bar (Amat * Amat) f := by
  rw [bar_Amat_sq]
  exact ReferenceCoefficientMatrices.coefficientAction_a _ f.1

theorem coeff_a_sq_apply (n : ℕ) (t : Fin 2) (f : V n) :
    ((coeff n t (ReferenceCoefficientMatrices.a ^ 2) f : V n) : MvPolynomial (Fin 3) ℚ) =
      bar Amat f := by
  rw [bar_Amat]
  exact ReferenceCoefficientMatrices.coefficientAction_a_sq _ f.1

theorem norm_coe (n : ℕ) (t : Fin 2) (F : Covectors → V n) (r : Covectors) :
    ((normExpr (coeff n t) F r : V n) : MvPolynomial (Fin 3) ℚ) =
      (F r : MvPolynomial (Fin 3) ℚ) + bar (Amat * Amat) (F (act r ReferenceCoefficientMatrices.a)) +
        bar Amat (F (act r (ReferenceCoefficientMatrices.a ^ 2))) := by
  unfold normExpr
  rw [Submodule.coe_add, Submodule.coe_add, coeff_a_apply, coeff_a_sq_apply]

/-- The literal equations of Lemma 3.2 are the abstract fiber system for `E_{n,t}`. -/
theorem isFiberFunction_iff (t : Fin 2) (n : ℕ) (F : Covectors → V n) :
    IsFiberFunction t n F ↔ IsFiberSystem (coeff n t) F := by
  constructor
  · intro h
    refine ⟨fun s π r => ?_, fun r => ?_⟩
    · apply Subtype.ext
      rw [signed_rhs]
      exact h.signed (Dof s) π⁻¹ r (act r (signedPerm s π)) (by rw [act_val, signedPerm_val])
    · apply Subtype.ext
      have h1 := h.norm r (act r (ReferenceCoefficientMatrices.a ^ 2))
        (act r ReferenceCoefficientMatrices.a) (by rw [act_val, a_sq_val]) (by rw [act_val, a_val])
      rw [norm_coe, add_right_comm]
      exact h1
  · intro h
    refine ⟨fun D π r r' hr' => ?_, fun r r₁ r₂ h₁ h₂ => ?_⟩
    · have h1 := h.signed (sOf D) π⁻¹ r
      have h2 : r' = act r (signedPerm (sOf D) π⁻¹) := by
        apply Subtype.ext
        rw [hr', act_val, signedPerm_val, Dof_sOf, inv_inv]
      have h3 := congrArg Subtype.val h1
      rw [signed_rhs, Dof_sOf, inv_inv] at h3
      rw [h2]
      exact h3
    · have e₁ : r₁ = act r (ReferenceCoefficientMatrices.a ^ 2) :=
        Subtype.ext (by rw [h₁, act_val, a_sq_val])
      have e₂ : r₂ = act r ReferenceCoefficientMatrices.a :=
        Subtype.ext (by rw [h₂, act_val, a_val])
      subst e₁ e₂
      have h3 := congrArg Subtype.val (h.norm r)
      rw [norm_coe, add_right_comm] at h3
      exact h3

/-- The fiber functions of Lemma 3.2, as a `ℚ`-subspace of all functions `𝒮 → V_n`. -/
def fiberFunctions (t : Fin 2) (n : ℕ) : Submodule ℚ (Covectors → V n) :=
  fiberSpace (coeff n t)

theorem mem_fiberFunctions {t : Fin 2} {n : ℕ} {F : Covectors → V n} :
    F ∈ fiberFunctions t n ↔ IsFiberFunction t n F :=
  (isFiberFunction_iff t n F).symm

end TernaryPeriodPolynomials.Argument.FiberModel
