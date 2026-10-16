module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RealIwasawa

@[expose] public section


/-!
# Real analyticity of the radical along the Iwasawa factor

* `planeRadical n χ p` depends only on `s = p₀₂ / p₂₂` and `t = p₁₂ / p₂₂`
  (`planeRadical_eq_unipotent`), and each coefficient of `planeRadical n χ p Q` is the coefficient
  of `ρ(planeUnipotent s t) (ι Q) - ι Q` at the shifted monomial `m + e₂`
  (`coeff_planeRadical_eq`), hence a polynomial, in particular real analytic, function of `(s, t)`
  (`contDiff_radicalCoeff`).
* For every `Q` and monomial `m`, `A ↦ coeff m (planeRadical n χ ⟨iwasawaB A, _⟩ Q)` is real analytic
  on the invertible matrices (`planeRadical_iwasawaB_contDiffOn`).
* For a character trivial on the real ideles, the matrix coefficients of the coefficient
  representation are real analytic (`realCoefficientComponent_inv_contDiffOn`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial Matrix GeneralEisenstein
open GeneralEisenstein.Adelic
  (InPlaneParabolic planeParabolic planeUnipotent planeLevi realAdeleUnit invertibleMatrix)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (invertibleMatrix_val)
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-! ## Coefficients of an exact quotient by `x₂` -/

theorem coeff_X2_mul (R : Poly) (m : Fin 3 →₀ ℕ) :
    ((X 2 : Poly) * R).coeff (m + Finsupp.single 2 1) = R.coeff m := by
  classical
  rw [coeff_X_mul']
  have hmem : (2 : Fin 3) ∈ (m + Finsupp.single 2 1).support := by
    rw [Finsupp.mem_support_iff]
    simp
  rw [ite_eq_left hmem, add_tsub_cancel_right]

theorem coeff_planeRadical (n : ℕ) (χ : RankOneCharacter) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ) :
    (planeRadical n χ p Q : Poly).coeff m =
      (fullCoefficientComponent χ (planeUnipotentPart p) (binaryEmbed (n + 1) Q) -
        binaryEmbed (n + 1) Q).coeff (m + Finsupp.single 2 1) := by
  rw [← X2_mul_planeRadical n χ p Q, coeff_X2_mul]

/-! ## The radical depends only on the unipotent coordinates -/

/-- The radical of `p` is the radical of the unipotent `planeUnipotent (p₀₂/p₂₂) (p₁₂/p₂₂)`. -/
theorem planeRadical_eq_unipotent (n : ℕ) (χ : RankOneCharacter) (p : planeParabolic ℝ) :
    planeRadical n χ p =
      planeRadical n χ
        ⟨planeUnipotent (p.1.val 0 2 / p.1.val 2 2) (p.1.val 1 2 / p.1.val 2 2),
          planeUnipotent_mem _ _⟩ := by
  apply LinearMap.ext
  intro Q
  apply Subtype.ext
  apply mul_left_cancel₀ X2_ne_zero
  rw [X2_mul_planeRadical n χ p Q, X2_mul_planeRadical n χ _ Q, planeUnipotentPart_unipotent]
  rfl

/-! ## Smoothness of coefficients of parametrized linear substitutions -/

theorem contDiff_algebraMap_real : ContDiff ℝ ⊤ (fun x : ℝ => algebraMap ℝ ℂ x) :=
  Complex.ofRealCLM.contDiff

theorem contDiff_coeff_mul_X {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Poly}
    (hf : ∀ m, ContDiff ℝ ⊤ (fun x => (f x).coeff m)) (i : Fin 3) (m : Fin 3 →₀ ℕ) :
    ContDiff ℝ ⊤ (fun x => (f x * X i).coeff m) := by
  classical
  by_cases h : i ∈ m.support
  · have e : (fun x => (f x * X i).coeff m) = fun x => (f x).coeff (m - Finsupp.single i 1) := by
      funext x
      rw [coeff_mul_X', ite_eq_left h]
    rw [e]
    exact hf _
  · have e : (fun x => (f x * X i).coeff m) = fun _ => (0 : ℂ) := by
      funext x
      rw [coeff_mul_X', ite_eq_right h]
    rw [e]
    exact contDiff_const

/-- If the entries of a family of matrices depend smoothly on a parameter, so does every coefficient
of the image of a fixed polynomial under the linear substitution. -/
theorem contDiff_coeff_substitute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E → Matrix (Fin 3) (Fin 3) ℂ) (hM : ∀ i j, ContDiff ℝ ⊤ (fun x => M x i j))
    (F : Poly) : ∀ m : Fin 3 →₀ ℕ, ContDiff ℝ ⊤ (fun x => (substitute (M x) F).coeff m) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    intro m
    have h : ∀ x, substitute (M x) (C a) = C a := fun x => by simp [substitute]
    simp only [h]
    exact contDiff_const
  | add p q hp hq =>
    intro m
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (hp m).add (hq m)
  | mul_X p i hp =>
    intro m
    have h : ∀ x, (substitute (M x) (p * X i)).coeff m =
        M x i 0 * (substitute (M x) p * X 0).coeff m +
          M x i 1 * (substitute (M x) p * X 1).coeff m +
            M x i 2 * (substitute (M x) p * X 2).coeff m := by
      intro x
      have e : substitute (M x) (p * X i) =
          C (M x i 0) * (substitute (M x) p * X 0) + C (M x i 1) * (substitute (M x) p * X 1) +
            C (M x i 2) * (substitute (M x) p * X 2) := by
        rw [map_mul, substitute_X, linearForm, Fin.sum_univ_three]
        ring
      rw [e, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_C_mul, coeff_C_mul]
    simp only [h]
    exact (((hM i 0).mul (contDiff_coeff_mul_X hp 0 m)).add
      ((hM i 1).mul (contDiff_coeff_mul_X hp 1 m))).add
      ((hM i 2).mul (contDiff_coeff_mul_X hp 2 m))

/-! ## The unipotent parameter -/

/-- The substitution `x ↦ u(s,t)⁻¹ x = (x₀ - s x₂, x₁ - t x₂, x₂)` for `(s, t) ∈ ℝ²`. -/
def unipSubst (st : ℝ × ℝ) : Poly →ₐ[ℂ] Poly :=
  substitute ((planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3)

theorem contDiff_unipInv_entry (i j : Fin 3) :
    ContDiff ℝ ⊤ (fun st : ℝ × ℝ =>
      (((planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ) i j) := by
  have hs : ContDiff ℝ ⊤ (fun st : ℝ × ℝ => algebraMap ℝ ℂ st.1) :=
    contDiff_algebraMap_real.comp contDiff_fst
  have ht : ContDiff ℝ ⊤ (fun st : ℝ × ℝ => algebraMap ℝ ℂ st.2) :=
    contDiff_algebraMap_real.comp contDiff_snd
  fin_cases i <;> fin_cases j
  · exact (show ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (1 : ℂ)) from contDiff_const)
  · exact (show ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℂ)) from contDiff_const)
  · exact (show ContDiff ℝ ⊤ (fun st : ℝ × ℝ => -(algebraMap ℝ ℂ st.1)) from hs.neg)
  · exact (show ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℂ)) from contDiff_const)
  · exact (show ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (1 : ℂ)) from contDiff_const)
  · exact (show ContDiff ℝ ⊤ (fun st : ℝ × ℝ => -(algebraMap ℝ ℂ st.2)) from ht.neg)
  · exact (show ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℂ)) from contDiff_const)
  · exact (show ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℂ)) from contDiff_const)
  · exact (show ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (1 : ℂ)) from contDiff_const)

theorem contDiff_unipSubst_coeff (F : Poly) (m : Fin 3 →₀ ℕ) :
    ContDiff ℝ ⊤ (fun st : ℝ × ℝ => (unipSubst st F).coeff m) :=
  contDiff_coeff_substitute
    (fun st : ℝ × ℝ =>
      (((planeUnipotent (algebraMap ℝ ℂ st.1) (algebraMap ℝ ℂ st.2))⁻¹ : GL3) :
        Matrix (Fin 3) (Fin 3) ℂ))
    contDiff_unipInv_entry F m

/-- The coefficient of `x^m` in `(ρ(u(s,t)) (ι Q) - ι Q) / x₂`, as a function of `(s, t)`. -/
def radicalCoeff (n : ℕ) (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ)
    (st : ℝ × ℝ) : ℂ :=
  (unipSubst st (binaryEmbed (n + 1) Q) - binaryEmbed (n + 1) Q).coeff (m + Finsupp.single 2 1)

/-- The coefficients of the radical are real analytic (indeed polynomial) functions of the unipotent
coordinates `(s, t)`. -/
theorem contDiff_radicalCoeff (n : ℕ) (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ) :
    ContDiff ℝ ⊤ (radicalCoeff n Q m) := by
  have e : radicalCoeff n Q m = fun st : ℝ × ℝ =>
      (unipSubst st (binaryEmbed (n + 1) Q)).coeff (m + Finsupp.single 2 1) -
        (binaryEmbed (n + 1) Q).coeff (m + Finsupp.single 2 1) := by
    funext st
    simp only [radicalCoeff, coeff_sub]
  rw [e]
  exact (contDiff_unipSubst_coeff _ _).sub contDiff_const

theorem coeff_planeRadical_eq (n : ℕ) (χ : RankOneCharacter) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ) :
    (planeRadical n χ p Q : Poly).coeff m =
      radicalCoeff n Q m (p.1.val 0 2 / p.1.val 2 2, p.1.val 1 2 / p.1.val 2 2) := by
  rw [coeff_planeRadical, rho_planeUnipotentPart]
  rfl

/-! ## Analyticity along the Iwasawa factor -/

theorem iwasawaB_mem_planeParabolic (g : RealGL3) : iwasawaB g ∈ planeParabolic ℝ :=
  ⟨(iwasawaB_upper g).2.1, (iwasawaB_upper g).2.2.1⟩

/-- **Analyticity of the radical along the analytic Iwasawa factor.** -/
theorem planeRadical_iwasawaB_contDiffOn (n : ℕ) (χ : RankOneCharacter)
    (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ⊤ (fun A : Mat3 =>
      (planeRadical n χ ⟨iwasawaB (invertibleMatrix A), iwasawaB_mem_planeParabolic _⟩ Q).val.coeff
        m) {A | A.det ≠ 0} := by
  have hB := iwasawaB_contDiffOn
  have hentry : ∀ i j, ContDiffOn ℝ ⊤
      (fun A : Mat3 => (iwasawaB (invertibleMatrix A)).val i j) {A | A.det ≠ 0} :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hB i) j
  have hpos : ∀ A ∈ {A : Mat3 | A.det ≠ 0}, (iwasawaB (invertibleMatrix A)).val 2 2 ≠ 0 :=
    fun A _ => (iwasawaB_upper (invertibleMatrix A)).2.2.2.2.2.ne'
  have hs : ContDiffOn ℝ ⊤ (fun A : Mat3 =>
      (iwasawaB (invertibleMatrix A)).val 0 2 / (iwasawaB (invertibleMatrix A)).val 2 2)
      {A | A.det ≠ 0} := (hentry 0 2).div (hentry 2 2) hpos
  have ht : ContDiffOn ℝ ⊤ (fun A : Mat3 =>
      (iwasawaB (invertibleMatrix A)).val 1 2 / (iwasawaB (invertibleMatrix A)).val 2 2)
      {A | A.det ≠ 0} := (hentry 1 2).div (hentry 2 2) hpos
  have hst := hs.prodMk ht
  refine ((contDiff_radicalCoeff n Q m).fun_comp_contDiffOn hst).congr fun A _ => ?_
  exact coeff_planeRadical_eq n χ ⟨iwasawaB (invertibleMatrix A), iwasawaB_mem_planeParabolic _⟩
    Q m

/-! ## Matrix coefficients of the coefficient representation -/

theorem contDiff_mapEntry (i j : Fin 3) :
    ContDiff ℝ ⊤ (fun A : Mat3 => (A.map (algebraMap ℝ ℂ)) i j) :=
  contDiff_algebraMap_real.comp (iwEntry_contDiff i j)

theorem contDiff_det_cast :
    ContDiff ℝ ⊤ (fun A : Mat3 => algebraMap ℝ ℂ A.det) := by
  have hdet : ContDiff ℝ ⊤ (fun A : Mat3 => A.det) := by
    simp only [Matrix.det_fin_three]
    fun_prop
  exact contDiff_algebraMap_real.comp hdet

theorem componentCharacter_eq_one {χ : RankOneCharacter}
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (g : RealGL3) :
    componentCharacter χ g = 1 :=
  hχ (GeneralLinearGroup.det g)

theorem fullCoefficientComponent_inv_apply (χ : RankOneCharacter) (g : RealGL3) (F : Poly) :
    fullCoefficientComponent χ g⁻¹ F =
      (componentCharacter χ g⁻¹ * algebraMap ℝ ℂ g.val.det) •
        substitute (g.val.map (algebraMap ℝ ℂ)) F := by
  have e1 : GeneralLinearGroup.map (algebraMap ℝ ℂ) g⁻¹ =
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) g)⁻¹ :=
    map_inv (GeneralLinearGroup.map (algebraMap ℝ ℂ)) g
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) g) : ℂˣ) : ℂ) =
      algebraMap ℝ ℂ g.val.det := by
    rw [GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (algebraMap ℝ ℂ) g.val).symm
  have hs : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) g⁻¹) : ℂˣ) :
      ℂ)⁻¹ = algebraMap ℝ ℂ g.val.det := by
    rw [e1, map_inv GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) g),
      Units.val_inv_eq_inv_val, inv_inv, h1]
  have hm : ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g⁻¹)⁻¹ : GL3) =
      GeneralLinearGroup.map (algebraMap ℝ ℂ) g := by
    rw [e1, inv_inv]
  rw [fullCoefficientComponent_apply, hs, hm]
  rfl

theorem realCoefficientComponent_inv_val (n : ℕ) (χ : RankOneCharacter)
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (g : RealGL3)
    (P : HomogeneousPoly n) :
    ((realCoefficientComponent n χ g⁻¹ P : HomogeneousPoly n) : Poly) =
      algebraMap ℝ ℂ g.val.det • substitute (g.val.map (algebraMap ℝ ℂ)) (P : Poly) := by
  rw [coe_realCoefficientComponent, fullCoefficientComponent_inv_apply,
    componentCharacter_eq_one hχ, one_mul]

/-- **Analyticity of the matrix coefficients of the coefficient representation**, for a character
that is trivial on the real ideles. -/
theorem realCoefficientComponent_inv_contDiffOn (n : ℕ) (χ : RankOneCharacter)
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (P : HomogeneousPoly n)
    (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ⊤ (fun A : Mat3 =>
      (realCoefficientComponent n χ (invertibleMatrix A)⁻¹ P).val.coeff m) {A | A.det ≠ 0} := by
  have hS : ContDiff ℝ ⊤ (fun A : Mat3 =>
      algebraMap ℝ ℂ A.det * (substitute (A.map (algebraMap ℝ ℂ)) (P : Poly)).coeff m) :=
    contDiff_det_cast.mul
      (contDiff_coeff_substitute (fun A : Mat3 => A.map (algebraMap ℝ ℂ)) contDiff_mapEntry
        (P : Poly) m)
  refine hS.contDiffOn.congr fun A hA => ?_
  have hA' : A.det ≠ 0 := hA
  rw [realCoefficientComponent_inv_val n χ hχ, invertibleMatrix_val A hA', coeff_smul, smul_eq_mul]

end TernaryPeriodPolynomials.SourceConstruction

end
