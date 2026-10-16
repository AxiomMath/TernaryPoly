module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.GammaNPlane
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.Group
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Edge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerActions

@[expose] public section


/-!
# The paper's plane group `Γ_P = Γ(N) ∩ P(ℤ)` as a split extension with radical `Nℤ²`

Paper: Lemma C.3
(`ar:lem:seed`): `Γ_P = Γ ∩ P(ℚ)`, `Λ_P` its projection to the determinant-one Levi.

Scope of `gammaNP N`: it is `Γ(N) ∩ planeStab`, the elements of `Γ(N)` with bottom row `(0, 0, 1)`
(`Γ(N) ∩ P(ℤ)`). It is the full stabilizer `Γ(N) ∩ P(ℚ)` of the rational plane only for `N ≥ 3`
(`ConvergenceC4.gammaN_inf_rationalPlane`, `mem_planeStab_of_gammaN`); for `N = 1, 2` it can be
strictly smaller (for example `diag(-1, 1, -1) ∈ Γ(2)` stabilizes the plane but has bottom-right
entry `-1`). The statements of this file are about `Γ(N) ∩ P(ℤ)`.

For `Γ = Γ(N)` the group `Γ_P = gammaNP N` is the split extension of `Λ_P = Γ₂(N)` by the radical
lattice `Nℤ² = {[[1, 0, Na], [0, 1, Nb], [0, 0, 1]]}` (`gammaNExt`, `gammaNSplitting`), and the
complex coefficient representation of its plane data is `gammaNRep n`. The conjugation by
`dmat N = diag(1, 1, N) ∈ GL₃(ℝ)` carries `Γ_P` onto the plane group `ℤ² ⋊ Γ₂(N) ⊆ Λ₀⁺` of
`LevelGroup`: it maps the radical `Nℤ²` onto `ℤ²` and commutes with the Levi block
(`dmat_mul_radical`, `dmat_mul_section`); hence `T = ρ(dmat N)` intertwines the two coefficient
representations on the radical and Levi parts (`tOp_rad`, `tOp_sect`), and the Levi action on the
radical lattice is the integral action `r ↦ A⁻¹ r` (`gammaN_radicalInput`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open Matrix GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ)

/-- The radical element `[[1, 0, N a], [0, 1, N b], [0, 0, 1]]` of `Γ(N) ∩ P(ℤ)`. -/
def radElt (r : RadicalLattice) : SL(3, ℤ) :=
  ⟨!![1, 0, (N : ℤ) * r.toAdd.1; 0, 1, (N : ℤ) * r.toAdd.2; 0, 0, 1], by
    rw [Matrix.det_fin_three]; simp⟩

theorem radElt_mul (r s : RadicalLattice) : radElt N (r * s) = radElt N r * radElt N s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radElt, Matrix.mul_apply, Fin.sum_univ_three, mul_add, toAdd_mul, add_comm]

theorem radElt_one : radElt N 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radElt]

theorem radElt_mem_gammaN (r : RadicalLattice) : radElt N r ∈ gammaN N := by
  rw [mem_gammaN]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [radElt]

theorem radElt_mem_planeStab (r : RadicalLattice) : radElt N r ∈ planeStab :=
  ⟨by simp [radElt], by simp [radElt], by simp [radElt]⟩


theorem leviBlock_mul (γ δ : SL(3, ℤ)) (hγ : γ ∈ planeStab) (hδ : δ ∈ planeStab) :
    leviBlock (γ * δ) (planeStab.mul_mem hγ hδ) = leviBlock γ hγ * leviBlock δ hδ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  obtain ⟨h0, h1, h2⟩ := hδ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h1]

theorem leviBlock_one : leviBlock 1 planeStab.one_mem = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviBlock]

/-- The Levi projection `Γ(N) ∩ P(ℤ) → Γ₂(N)`. -/
def gammaNProj : ↥(gammaNP N) →* ↥(CongruenceSubgroup.Gamma N) where
  toFun g := ⟨leviBlock g.1 g.2.2, leviBlock_mem_Gamma g.2.1 g.2.2⟩
  map_one' := Subtype.ext leviBlock_one
  map_mul' g h := Subtype.ext (leviBlock_mul g.1 h.1 g.2.2 h.2.2)

theorem blockDiag_mul (A B : SL(2, ℤ)) :
    ConvergenceC4.blockDiag (A * B) = ConvergenceC4.blockDiag A * ConvergenceC4.blockDiag B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ConvergenceC4.blockDiag, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockDiag_one : ConvergenceC4.blockDiag 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ConvergenceC4.blockDiag]

/-- The Levi section `Γ₂(N) → Γ(N) ∩ P(ℤ)`. -/
def gammaNSect : ↥(CongruenceSubgroup.Gamma N) →* ↥(gammaNP N) where
  toFun A := ⟨ConvergenceC4.blockDiag A.1, ConvergenceC4.blockDiag_mem_gammaN A.2,
    ConvergenceC4.blockDiag_mem_planeStab A.1⟩
  map_one' := Subtype.ext blockDiag_one
  map_mul' A B := Subtype.ext (blockDiag_mul A.1 B.1)

theorem gammaNProj_sect (A : ↥(CongruenceSubgroup.Gamma N)) :
    gammaNProj N (gammaNSect N A) = A := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaNProj, gammaNSect, leviBlock, ConvergenceC4.blockDiag]

/-- The radical lattice `Nℤ²` inside `Γ(N) ∩ P(ℤ)`. -/
def gammaNInl : RadicalLattice →* ↥(gammaNP N) where
  toFun r := ⟨radElt N r, radElt_mem_gammaN N r, radElt_mem_planeStab N r⟩
  map_one' := Subtype.ext (radElt_one N)
  map_mul' r s := Subtype.ext (radElt_mul N r s)

theorem gammaNInl_injective [NeZero N] : Function.Injective (gammaNInl N) := by
  intro r s h
  have h' := congrArg (fun g : ↥(gammaNP N) => ((g : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ)) h
  have e1 := congrFun (congrFun h' 0) 2
  have e2 := congrFun (congrFun h' 1) 2
  simp only [gammaNInl, MonoidHom.coe_mk, OneHom.coe_mk, radElt, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e1 e2
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply Multiplicative.toAdd.injective
  exact Prod.ext (mul_left_cancel₀ hN e1) (mul_left_cancel₀ hN e2)

theorem gammaNProj_ker [NeZero N] (g : ↥(gammaNP N)) (hg : gammaNProj N g = 1) :
    ∃ r, gammaNInl N r = g := by
  have h' := congrArg (fun A : ↥(CongruenceSubgroup.Gamma N) =>
    ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) hg
  have a00 := congrFun (congrFun h' 0) 0
  have a01 := congrFun (congrFun h' 0) 1
  have a10 := congrFun (congrFun h' 1) 0
  have a11 := congrFun (congrFun h' 1) 1
  simp only [gammaNProj, MonoidHom.coe_mk, OneHom.coe_mk, leviBlock, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Subgroup.coe_one,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at a00 a01 a10 a11
  have d02 := mem_gammaN.1 g.2.1 0 2
  have d12 := mem_gammaN.1 g.2.1 1 2
  simp at d02 d12
  obtain ⟨e, he⟩ := d02
  obtain ⟨f, hf⟩ := d12
  refine ⟨Multiplicative.ofAdd (e, f), ?_⟩
  obtain ⟨⟨γ, h1⟩, h2⟩ := g
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨p0, p1, p2⟩ := h2
  have q0 : γ 2 0 = 0 := p1
  have q1 : γ 2 1 = 0 := p2.1
  have q2 : γ 2 2 = 1 := p2.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [gammaNInl, radElt]


/-- **The split extension `Nℤ² → Γ(N) ∩ P(ℤ) → Γ₂(N)`** of the paper's plane group. -/
def gammaNExt [NeZero N] :
    GroupExtension RadicalLattice ↥(gammaNP N) ↥(CongruenceSubgroup.Gamma N) where
  inl := gammaNInl N
  rightHom := gammaNProj N
  inl_injective := gammaNInl_injective N
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gammaNProj, gammaNInl, leviBlock, radElt]
    · intro hg
      exact gammaNProj_ker N g (MonoidHom.mem_ker.mp hg)
  rightHom_surjective A := ⟨gammaNSect N A, gammaNProj_sect N A⟩

/-- The Levi splitting of `Γ(N) ∩ P(ℤ)`. -/
def gammaNSplitting [NeZero N] : (gammaNExt N).Splitting :=
  ⟨gammaNSect N, gammaNProj_sect N⟩

/-- The complex coefficient representation `E_n` of `Γ(N) ∩ P(ℤ)`. -/
def gammaNRep (n : ℕ) : Rep ℂ ↥(gammaNP N) := Rep.of ((gammaNPlaneData N).rhoC n)

/-- The polynomial underlying a value of `gammaNRep`. -/
def gval (n : ℕ) (x : gammaNRep N n) : MvPolynomial (Fin 3) ℂ := (x : HomogeneousPoly n).val

theorem gammaNRep_coe (n : ℕ) (g : ↥(gammaNP N)) (q : gammaNRep N n) :
    gval N n ((gammaNRep N n).ρ g q) = rho (realMat g.1) (gval N n q) := by
  have h := (gammaNPlaneData N).rhoC_coe n g q
  rw [gammaNPlaneData_plm] at h
  exact h


section Conj

/-- The diagonal matrix `diag(1, 1, N) ∈ GL₃(ℝ)`. -/
def dmat [NeZero N] : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, 1, (N : ℝ)]) (by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_three]
    exact_mod_cast NeZero.ne N)

theorem dmat_val [NeZero N] :
    (dmat N : Matrix (Fin 3) (Fin 3) ℝ) = Matrix.diagonal ![1, 1, (N : ℝ)] := rfl

theorem realMat_radElt (r : RadicalLattice) :
    realMat (radElt N r) = parabolicMatrix 1
      ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realMat, radElt, parabolicMatrix]

theorem plm_plusInl (r : RadicalLattice) :
    plusPlaneData.plm (plusInl r) = parabolicMatrix 1 ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)] := by
  have hl : plusPlaneData.lamM (plusInl r) = 1 := by
    show ((plusLam (plusInl r) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1
    rw [plusLam_inl]
    rfl
  rw [PlaneData.plm_eq, hl]
  show parabolicMatrix 1 (plusW (plusInl r)) = _
  rw [plusW_inl]

theorem dmat_mul_radical [NeZero N] (r : RadicalLattice) :
    dmat N * (gammaNPlaneData N).sigma (gammaNInl N r) =
      plusPlaneData.sigma (plusInl r) * dmat N := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dmat_val, PlaneData.sigma_val, PlaneData.sigma_val,
    gammaNPlaneData_plm, plm_plusInl]
  change _ * realMat (radElt N r) = _
  rw [realMat_radElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]

theorem plm_plusSection (A : SL(2, ℤ)) :
    plusPlaneData.plm (plusSectionS A) =
      parabolicMatrix ((SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 := by
  rw [PlaneData.plm_eq]
  have hl : plusPlaneData.lamM (plusSectionS A) =
      ((SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    show ((plusLam (plusSectionS A) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [plusLam_section]
  rw [hl]
  show parabolicMatrix _ (plusW (plusSectionS A)) = _
  rw [plusW_section]

theorem realMat_blockDiag (A : SL(2, ℤ)) :
    realMat (ConvergenceC4.blockDiag A) =
      parabolicMatrix ((SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMat, ConvergenceC4.blockDiag, parabolicMatrix,
      Matrix.SpecialLinearGroup.map_apply_coe]

theorem dmat_mul_section [NeZero N] (A : ↥(CongruenceSubgroup.Gamma N)) :
    dmat N * (gammaNPlaneData N).sigma (gammaNSect N A) =
      plusPlaneData.sigma (plusSectionS A.1) * dmat N := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dmat_val, PlaneData.sigma_val, PlaneData.sigma_val,
    gammaNPlaneData_plm, plm_plusSection]
  change _ * realMat (ConvergenceC4.blockDiag A.1) = _
  rw [realMat_blockDiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, Matrix.mul_apply, Matrix.diagonal_apply]


end Conj



theorem gammaN_radicalInput [NeZero N] (A : ↥(CongruenceSubgroup.Gamma N)) (r : RadicalLattice) :
    splitRadicalInput (gammaNSplitting N) A r =
      upperLeviLatticeInput (SpecialLinearGroup.toGL A.1) r := by
  set u := upperLeviLatticeInput (SpecialLinearGroup.toGL A.1) r with hu
  have h1 := splitRadicalInput_commute (gammaNSplitting N) A r
  have h2 : gammaNInl N r * gammaNSect N A = gammaNSect N A * gammaNInl N u := by
    apply Subtype.ext
    apply Subtype.ext
    have hdet : (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := A.1.det_coe
      rwa [Matrix.det_fin_two] at this
    have hinv : ∀ i j, ((SpecialLinearGroup.toGL A.1)⁻¹ : GL (Fin 2) ℤ).val i j =
        (A.1 : Matrix (Fin 2) (Fin 2) ℤ).adjugate i j := fun i j => rfl
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gammaNInl, gammaNSect, radElt, ConvergenceC4.blockDiag, hu, upperLeviLatticeInput,
        hinv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_two]
    · linear_combination (-((N : ℤ) * r.toAdd.1)) * hdet
    · linear_combination (-((N : ℤ) * r.toAdd.2)) * hdet
  have h3 : gammaNSect N A * gammaNInl N (splitRadicalInput (gammaNSplitting N) A r) =
      gammaNSect N A * gammaNInl N u := by
    rw [← h2]
    exact h1.symm
  exact gammaNInl_injective N (mul_left_cancel h3)



section Transport

variable [NeZero N]

/-- The conjugating operator `T = ρ(diag(1, 1, N))` on `E_n`. -/
def tOp (n : ℕ) : Module.End ℂ (HomogeneousPoly n) := GeneralEisenstein.realCoefficient n (dmat N)

/-- `T` as a linear automorphism. -/
def tEquiv (n : ℕ) : HomogeneousPoly n ≃ₗ[ℂ] HomogeneousPoly n where
  toLinearMap := tOp N n
  invFun := GeneralEisenstein.realCoefficient n (dmat N)⁻¹
  left_inv v := by
    change (GeneralEisenstein.realCoefficient n (dmat N)⁻¹)
      ((GeneralEisenstein.realCoefficient n (dmat N)) v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change (GeneralEisenstein.realCoefficient n (dmat N))
      ((GeneralEisenstein.realCoefficient n (dmat N)⁻¹) v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem tOp_rad (n : ℕ) (r : RadicalLattice) (v : HomogeneousPoly n) :
    tOp N n ((gammaNRep N n).ρ (gammaNInl N r) v) =
      (plusRep n).ρ (plusInl r) (tOp N n v) := by
  have h := dmat_mul_radical N r
  have e : (plusRep n).ρ (plusInl r) =
      GeneralEisenstein.realCoefficient n (plusPlaneData.sigma (plusInl r)) :=
    (plusPlaneData_rhoC n (plusInl r)).symm
  rw [e]
  change (GeneralEisenstein.realCoefficient n (dmat N) *
    GeneralEisenstein.realCoefficient n ((gammaNPlaneData N).sigma (gammaNInl N r))) v =
      (GeneralEisenstein.realCoefficient n (plusPlaneData.sigma (plusInl r)) *
        GeneralEisenstein.realCoefficient n (dmat N)) v
  rw [← map_mul, ← map_mul, h]

theorem tOp_sect (n : ℕ) (A : ↥(CongruenceSubgroup.Gamma N)) (v : HomogeneousPoly n) :
    tOp N n ((gammaNRep N n).ρ (gammaNSect N A) v) =
      arithmeticLeviCoefficient n (SpecialLinearGroup.toGL A.1) (tOp N n v) := by
  have h := dmat_mul_section N A
  have e : arithmeticLeviCoefficient n (SpecialLinearGroup.toGL A.1) =
      GeneralEisenstein.realCoefficient n (plusPlaneData.sigma (plusSectionS A.1)) :=
    (plusPlaneData_rhoC n (plusSectionS A.1)).symm
  rw [e]
  change (GeneralEisenstein.realCoefficient n (dmat N) *
    GeneralEisenstein.realCoefficient n ((gammaNPlaneData N).sigma (gammaNSect N A))) v =
      (GeneralEisenstein.realCoefficient n (plusPlaneData.sigma (plusSectionS A.1)) *
        GeneralEisenstein.realCoefficient n (dmat N)) v
  rw [← map_mul, ← map_mul, h]

end Transport


end TernaryPeriodPolynomials.Argument.SeedC3S4c
