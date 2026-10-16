module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisGauge
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisPolyNilp
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Trans

@[expose] public section


open MvPolynomial
open scoped ContDiff
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

open TernaryPeriodPolynomials.Argument.SeedC3

/-- **The Heisenberg group as an abstract group** (Malcev chart). -/
def HGrp : Type := Pt

/-- The point of the chart as an element of the group. -/
def toH (p : Pt) : HGrp := p

/-- The coordinates of an element of the group. -/
def ofH (p : HGrp) : Pt := p

instance : Group HGrp where
  mul p q := mulH p q
  one := (0 : Pt)
  inv p := invH p
  mul_assoc := mulH_assoc
  one_mul := mulH_zero_left
  mul_one := mulH_zero_right
  inv_mul_cancel := invH_mulH

/-- The Levi block `[[1, x], [0, 1]]`. -/
def hLamMat (x : ℝ) : GL (Fin 2) ℝ :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem hLamMat_add (x y : ℝ) : hLamMat (x + y) = hLamMat x * hLamMat y := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hLamMat, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem hLamMat_zero : hLamMat 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hLamMat]

/-- The Heisenberg group as a plane parabolic group: Levi block `[[1, x], [0, 1]]`, radical `(z, y)`. -/
def hPD : PlaneData HGrp where
  lam :=
    { toFun := fun p => hLamMat (ofH p).1
      map_one' := hLamMat_zero
      map_mul' := fun p q => hLamMat_add _ _ }
  w p := ![(ofH p).2.2, (ofH p).2.1]
  det_one p := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.det, hLamMat]
  w_mul p q := by
    ext i
    fin_cases i
    · show (mulH (ofH p) (ofH q)).2.2 = _
      simp [mulH, hLamMat]
      ring
    · show (mulH (ofH p) (ofH q)).2.1 = _
      simp [mulH, hLamMat]

/-- The matrix `[[1, x, z], [0, 1, y], [0, 0, 1]]` of a point of the Malcev chart. -/
def nMat (p : Pt) : Matrix (Fin 3) (Fin 3) ℝ := !![1, p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1]

theorem hPD_plm (p : HGrp) : hPD.plm p = nMat (ofH p) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PlaneData.plm, hPD, hLamMat, parabolicMatrix, nMat]

theorem nMat_inv (p : Pt) : (nMat p)⁻¹ = nMat (invH p) := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nMat, invH, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_nMat (p : Pt) : (nMat p).det = 1 := by
  simp [nMat, Matrix.det_fin_three]

/-- **The polynomial coefficient representation restricted to the Heisenberg radical**, `p ↦ ρ(n(p))` on `Coef n`. -/
def polyRep (n : ℕ) (p : Pt) : Coef n →L[ℝ] Coef n := ZigZag.repCLM (hPD.rhoR n) (toH p)

theorem toPoly_polyRep (n : ℕ) (p : Pt) (q : Coef n) :
    Coef.toPoly (polyRep n p q) = rho (nMat p) (Coef.toPoly q) := by
  change Coef.toPoly (hPD.rhoCoef n (toH p) q) = _
  rw [hPD.toPoly_rhoCoef, hPD_plm]
  rfl

theorem rho_nMat (p : Pt) (q : MvPolynomial (Fin 3) ℂ) :
    rho (nMat p) q = bind₁ (![X 0 + C (((-p.1 : ℝ)) : ℂ) * X 1 + C ((p.1 * p.2.1 - p.2.2 : ℝ) : ℂ) * X 2,
      X 1 + C ((-p.2.1 : ℝ) : ℂ) * X 2, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) q := by
  unfold rho
  rw [nMat_inv, det_nMat]
  simp only [inv_one, Complex.ofReal_one, map_one, one_mul]
  congr 2
  funext i
  fin_cases i
  · simp [nMat, invH, Fin.sum_univ_three, sub_eq_add_neg, add_assoc]
    ring
  · simp [nMat, invH, Fin.sum_univ_three, sub_eq_add_neg, add_assoc]
  · simp [nMat, invH, Fin.sum_univ_three, sub_eq_add_neg, add_assoc]

theorem polyRep_mul (n : ℕ) (p q : Pt) : polyRep n (mulH p q) = polyRep n p * polyRep n q :=
  ZigZag.repCLM_mul (hPD.rhoR n) (toH p) (toH q)

theorem polyRep_one (n : ℕ) : polyRep n 0 = 1 := by
  ext q
  change hPD.rhoR n (toH 0) q = q
  change hPD.rhoR n 1 q = q
  rw [map_one]
  rfl

/-! ### Smoothness -/

theorem contDiff_coeff_rho_nMat (q : MvPolynomial (Fin 3) ℂ) (e : Fin 3 →₀ ℕ) :
    ContDiff ℝ ∞ (fun p : Pt => (rho (nMat p) q).coeff e) := by
  let f : Fin 3 → MvPolynomial (Fin 3 ⊕ Fin 3) ℂ :=
    ![X (Sum.inl 0) + (-X (Sum.inr 0)) * X (Sum.inl 1) +
        (X (Sum.inr 0) * X (Sum.inr 1) - X (Sum.inr 2)) * X (Sum.inl 2),
      X (Sum.inl 1) + (-X (Sum.inr 1)) * X (Sum.inl 2), X (Sum.inl 2)]
  let Q : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ := bind₁ f q
  let s : Fin 3 → Pt → ℂ := fun a p => ((![p.1, p.2.1, p.2.2] a : ℝ) : ℂ)
  have hs : ∀ a, ContDiffOn ℝ ∞ (s a) Set.univ := by
    intro a
    fin_cases a
    · exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).contDiffOn
    · exact (Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)).contDiffOn
    · exact (Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
  have key := Calc.contDiffOn_coeff_spec Set.univ s hs Q e
  have key' : ContDiff ℝ ∞ (fun p : Pt => (Calc.spec (fun a => s a p) Q).coeff e) :=
    contDiffOn_univ.mp key
  have hfun : (fun p : Pt => (rho (nMat p) q).coeff e) =
      (fun p : Pt => (Calc.spec (fun a => s a p) Q).coeff e) := by
    funext p
    rw [rho_nMat]
    congr 2
    simp only [Q, Calc.spec]
    rw [MvPolynomial.aeval_bind₁]
    show aeval _ q = aeval _ q
    congr 2
    funext i
    fin_cases i <;> simp [f, s]
  rw [hfun]
  exact key'

theorem contDiff_polyRep (n : ℕ) : ContDiff ℝ ∞ (polyRep n) := by
  rw [contDiff_clm_apply_iff]
  intro q
  refine Calc.contDiffOn_of_vec n ?_ |> contDiffOn_univ.mp
  rw [contDiffOn_univ, contDiff_pi]
  intro e
  have := contDiff_coeff_rho_nMat (Coef.toPoly q) (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ)))
  change ContDiff ℝ ∞ (fun x : Pt =>
    (Coef.toPoly (polyRep n x q)).coeff (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ))))
  simp only [toPoly_polyRep]
  exact this

/-! ### Unipotence -/

theorem toPoly_polyRep_sub_one (n : ℕ) (p : Pt) (r : Coef n) :
    Coef.toPoly ((polyRep n p - 1) r) =
      shearAlg ((-p.1 : ℝ) : ℂ) ((p.1 * p.2.1 - p.2.2 : ℝ) : ℂ) ((-p.2.1 : ℝ) : ℂ) (Coef.toPoly r) -
        Coef.toPoly r := by
  rw [sub_apply, Coef.toPoly_sub, toPoly_polyRep, rho_nMat]
  rfl

theorem toPoly_polyRep_pow_mem (n : ℕ) (p : Pt) (k : ℕ) (r : Coef n) :
    Coef.toPoly (((polyRep n p - 1) ^ k) r) ∈ WJ k := by
  induction k with
  | zero => intro m _; exact Nat.zero_le _
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, toPoly_polyRep_sub_one]
    exact (Tp.of_mem ih).2

theorem homogeneous_WJ_zero {n : ℕ} {p : MvPolynomial (Fin 3) ℂ} (hp : p.IsHomogeneous n)
    (hW : p ∈ WJ (3 * n + 1)) : p = 0 := by
  by_contra hne
  obtain ⟨m, hm⟩ := (MvPolynomial.support_nonempty).mpr hne
  have hcoeff : p.coeff m ≠ 0 := mem_support_iff.mp hm
  have hdeg : m.degree = n := by
    have := hp hcoeff
    rw [Finsupp.degree_eq_weight_one]
    exact this
  have h1 : m 1 ≤ n := hdeg ▸ Finsupp.le_degree 1 m
  have h2 : m 2 ≤ n := hdeg ▸ Finsupp.le_degree 2 m
  have := hW m hm
  simp only [wt] at this
  omega

theorem polyRep_unip (n : ℕ) (p : Pt) : (polyRep n p - 1) ^ (3 * n + 1) = 0 := by
  ext r
  apply Coef.toPoly_injective
  change _ = Coef.toPoly (0 : Coef n)
  exact homogeneous_WJ_zero (Coef.toPoly_isHomogeneous _) (toPoly_polyRep_pow_mem n p _ r)

/-- **The polynomial coefficient representation `Sym^n ⊗ det⁻¹`, restricted to the Heisenberg radical, is a smooth unipotent representation.** -/
theorem polyRep_heisRep (n : ℕ) : HeisRep (polyRep n) where
  smooth := contDiff_polyRep n
  one := polyRep_one n
  mul := polyRep_mul n
  unip := ⟨3 * n + 1, polyRep_unip n⟩

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
