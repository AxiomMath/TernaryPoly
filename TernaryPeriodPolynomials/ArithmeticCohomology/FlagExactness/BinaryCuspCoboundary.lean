module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.BinaryCuspRestriction

@[expose] public section


/-!
# The cusp restriction of a cuspidal binary cocycle is a coboundary

This sharpens `binary_cusp_restriction` to an honest `H¹` statement. There are `M > 0`
and a coefficient vector `w` such that `c(n(kM))(1) = n(kM)·w − w` for all `k : ℕ`.
So the evaluated cocycle is a coboundary on the cusp subgroup `n(Mℕ)`.

Ingredients:
* `binaryUnipotent_coeff_polynomial`: along the real unipotent, the coefficient action
  is polynomial in the parameter.
* `functional_unipotent_invariant`: invariance under `n(M)` propagates to all `n(u)`,
  because a periodic polynomial is constant.
* `mem_range_sub_one_of_functionals`: duality in finite dimension.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- Generic linear forms of the inverse unipotent `!![1, -T; 0, 1]` over `ℂ[T]`. -/
def genericUnipotentForm : Fin 2 → MvPolynomial (Fin 2) (Polynomial ℂ) :=
  ![MvPolynomial.X 0 - MvPolynomial.C Polynomial.X * MvPolynomial.X 1, MvPolynomial.X 1]

/-- Evaluation of the parameter. -/
def parameterEvaluation (u : ℂ) : MvPolynomial (Fin 2) (Polynomial ℂ) →ₐ[ℂ] Binary.Poly :=
  MvPolynomial.mapAlgHom (Polynomial.aeval u)

theorem substitute_unipotent_eq (u : ℂ) (f : Binary.Poly) :
    Binary.substitute (binaryUnipotent (-u)).val f =
      parameterEvaluation u (MvPolynomial.aeval genericUnipotentForm f) := by
  rw [MvPolynomial.comp_aeval_apply]
  change MvPolynomial.bind₁ _ f = _
  rw [← MvPolynomial.aeval_eq_bind₁]
  have hforms : Binary.linearForm (binaryUnipotent (-u)).val =
      fun i => parameterEvaluation u (genericUnipotentForm i) := by
    funext i
    fin_cases i
    · simp [genericUnipotentForm, parameterEvaluation, Binary.linearForm, binaryUnipotent,
        Fin.sum_univ_two, MvPolynomial.mapAlgHom_apply]
      ring
    · simp [genericUnipotentForm, parameterEvaluation, Binary.linearForm, binaryUnipotent,
        Fin.sum_univ_two, MvPolynomial.mapAlgHom_apply]
  rw [hforms]

theorem binaryCoefficient_unipotent_val (n : ℕ) (u : ℝ) (p : Binary.HomogeneousPoly (n + 1)) :
    (binaryCoefficient n (binaryUnipotent u) p).val =
      Binary.substitute (binaryUnipotent (-(u : ℂ))).val p.val := by
  change Binary.action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (binaryUnipotent u)) p.val = _
  rw [Binary.action_apply]
  have hdet : Binary.determinantCharacter (-1)
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) (binaryUnipotent u)) = 1 := by
    change (((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) (binaryUnipotent u)) :
      ℂˣ) : ℂ)) ^ (-1 : ℤ) = 1
    rw [GeneralLinearGroup.val_det_apply]
    simp [binaryUnipotent, Matrix.det_fin_two, GeneralLinearGroup.map]
  rw [hdet, one_smul, ← map_inv, ← binaryUnipotent_neg', map_binaryUnipotent]
  congr 3
  simp

/-- Along the real unipotent the coefficient action is polynomial in the parameter. -/
theorem binaryUnipotent_coeff_polynomial (n : ℕ) (p : Binary.HomogeneousPoly (n + 1))
    (monomial : Fin 2 →₀ ℕ) :
    ∃ P : Polynomial ℂ, ∀ u : ℝ,
      (binaryCoefficient n (binaryUnipotent u) p).val.coeff monomial = P.eval (u : ℂ) := by
  refine ⟨(MvPolynomial.aeval genericUnipotentForm p.val).coeff monomial, fun u => ?_⟩
  rw [binaryCoefficient_unipotent_val, substitute_unipotent_eq]
  change (MvPolynomial.map (Polynomial.aeval (u : ℂ)).toRingHom _).coeff monomial = _
  rw [MvPolynomial.coeff_map]
  simp

theorem binaryCoefficient_pow (n : ℕ) (g : BinaryRealGL) (k : ℕ) :
    binaryCoefficient n (g ^ k) = binaryCoefficient n g ^ k := by
  unfold binaryCoefficient
  rw [map_pow, map_pow]

theorem binaryUnipotent_nat_mul (k : ℕ) (M : ℝ) :
    binaryUnipotent ((k : ℝ) * M) = (binaryUnipotent M) ^ k := by
  induction k with
  | zero => simp [binaryUnipotent_zero']
  | succ k ih =>
    rw [pow_succ, ← ih, ← binaryUnipotent_add]
    congr 1
    push_cast
    ring

/-- Invariance of a functional under `n(M)` propagates to every `n(u)`. -/
theorem functional_unipotent_invariant (n : ℕ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) (M : ℝ) (hM : M ≠ 0)
    (invariant : functional ∘ₗ binaryCoefficient n (binaryUnipotent M) = functional) (u : ℝ) :
    functional ∘ₗ binaryCoefficient n (binaryUnipotent u) = functional := by
  apply LinearMap.ext
  intro p
  obtain ⟨weight, hweight⟩ := functional_eq_sum_coeff functional
  choose P hP using fun s : degreeMonomials (n + 1) => binaryUnipotent_coeff_polynomial n p s.val
  set R : Polynomial ℂ := (∑ s, P s * Polynomial.C (weight s)) - Polynomial.C (functional p)
  have hR : ∀ v : ℝ, functional (binaryCoefficient n (binaryUnipotent v) p) - functional p =
      R.eval (v : ℂ) := by
    intro v
    rw [hweight (binaryCoefficient n (binaryUnipotent v) p)]
    simp only [R, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, hP]
  have hpow : ∀ k : ℕ, functional ∘ₗ binaryCoefficient n (binaryUnipotent M) ^ k = functional := by
    intro k
    induction k with
    | zero => exact LinearMap.comp_id functional
    | succ k ih =>
      rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, invariant]
  have hroots : ∀ k : ℕ, R.IsRoot (((k : ℝ) * M : ℝ) : ℂ) := by
    intro k
    rw [Polynomial.IsRoot, ← hR, binaryUnipotent_nat_mul, binaryCoefficient_pow]
    have := LinearMap.congr_fun (hpow k) p
    simp only [LinearMap.comp_apply] at this
    rw [this, sub_self]
  have hzero : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective (fun k : ℕ => ((((k : ℝ) * M : ℝ)) : ℂ)) := by
      intro a b hab
      have h1 : (a : ℝ) * M = (b : ℝ) * M := Complex.ofReal_injective hab
      exact_mod_cast mul_right_cancel₀ hM h1
    exact Set.infinite_of_injective_forall_mem hinj hroots
  have := hR u
  rw [hzero, Polynomial.eval_zero, sub_eq_zero] at this
  exact this

/-- Finite-dimensional duality for `range (T - 1)`. -/
theorem mem_range_sub_one_of_functionals {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (v : V) (h : ∀ functional : V →ₗ[ℂ] ℂ, functional ∘ₗ T = functional → functional v = 0) :
    v ∈ LinearMap.range (T - LinearMap.id) := by
  by_contra hv
  obtain ⟨functional, hne, hle⟩ := Submodule.exists_le_ker_of_notMem hv
  apply hne
  apply h
  apply LinearMap.ext
  intro x
  have hx : (T - LinearMap.id : V →ₗ[ℂ] V) x ∈ LinearMap.ker functional :=
    hle (LinearMap.mem_range_self _ x)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, sub_eq_zero] at hx
  exact hx

theorem binaryCoefficient_mul (n : ℕ) (g h : BinaryRealGL) :
    binaryCoefficient n (g * h) = binaryCoefficient n g * binaryCoefficient n h := by
  unfold binaryCoefficient
  rw [map_mul, map_mul]

theorem binaryCocycle_one {n : ℕ} {c : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (cocycle : ∀ g h x, c (g * h) x = c g x + binaryCohomologicalAction n g (c h) x)
    (x : BinaryAdelicGL) : c 1 x = 0 := by
  have h := cocycle 1 1 x
  rw [mul_one] at h
  have hact : binaryCohomologicalAction n 1 (c 1) x = c 1 x := by
    have hdet := det_atInfinity_binaryUnipotent 0
    rw [binaryUnipotent_zero'] at hdet
    unfold binaryCohomologicalAction
    rw [hdet, normPower_one, one_smul]
    have hone : binaryCoefficient n 1 = 1 := by
      unfold binaryCoefficient
      rw [map_one, map_one]
    have hinf : atInfinity (1 : BinaryRealGL) = 1 := by
      have := atInfinity_binaryUnipotent 0
      rw [binaryUnipotent_zero'] at this
      rw [this]
      have hz : ((0 : ℝ), (0 : FiniteAdeles)) = (0 : Adeles) := rfl
      rw [hz, binaryUnipotent_zero']
    rw [hone, hinf, mul_one]
    rfl
  rw [hact] at h
  have : c 1 x + c 1 x - c 1 x = c 1 x - c 1 x := by rw [← h]
  simpa using this

/-- **The cusp restriction of a cuspidal binary cocycle is a coboundary.** With the
hypotheses of `Cohomological` except non-triviality, there are `M > 0` and `w` such
that the evaluated cocycle on the cusp elements `n(kM)` is the coboundary of `w`. -/
theorem binary_cusp_coboundary (D : CuspidalRepresentation) (n : ℕ)
    (c : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (values : ∀ g, BinaryValues D n (c g))
    (U : Subgroup BinaryFiniteGL) (hU : IsOpen (U : Set BinaryFiniteGL))
    (level : ∀ u : U, ∀ g x, c g (x * atFinite u.val) = c g x)
    (cocycle : ∀ g h x, c (g * h) x = c g x + binaryCohomologicalAction n g (c h) x) :
    ∃ M : ℕ, 0 < M ∧ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ k : ℕ,
      c (binaryUnipotent ((k : ℝ) * M)) 1 =
        binaryCoefficient n (binaryUnipotent ((k : ℝ) * M)) w - w := by
  obtain ⟨M, hM, hlev⟩ := exists_unipotent_level U hU
  have hvanish := binary_cusp_restriction_of_level D n c values U level cocycle M hM hlev
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hmem := mem_range_sub_one_of_functionals (binaryCoefficient n (binaryUnipotent (M : ℝ)))
    (c (binaryUnipotent (M : ℝ)) 1)
    (fun functional hf => hvanish functional (functional_unipotent_invariant n functional M hMne hf))
  obtain ⟨w, hw⟩ := hmem
  refine ⟨M, hM, w, fun k => ?_⟩
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, binaryUnipotent_zero']
    rw [binaryCocycle_one cocycle]
    have hone : binaryCoefficient n 1 = 1 := by
      unfold binaryCoefficient
      rw [map_one, map_one]
    rw [hone, Module.End.one_apply, sub_self]
  | succ k ih =>
    have hsplit : binaryUnipotent (((k + 1 : ℕ) : ℝ) * M) =
        binaryUnipotent ((k : ℝ) * M) * binaryUnipotent (M : ℝ) := by
      rw [← binaryUnipotent_add]
      congr 1
      push_cast
      ring
    rw [hsplit, cocycle]
    unfold binaryCohomologicalAction
    rw [det_atInfinity_binaryUnipotent, normPower_one, one_smul, one_mul,
      cusp_shift_invariant values U level M hlev k, ih, binaryCoefficient_mul, Module.End.mul_apply]
    rw [← hw]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    abel

end TernaryPeriodPolynomials.FlagExactness
