module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps

@[expose] public section


/-!
# The paper's line group `Γ_Q = Γ(N) ∩ Q(ℤ)` as a split extension with radical `Nℤ²`

Formalized by Claude Sonnet 5.5.
Paper: Appendix C (`ar:sec:stokes`),:
"`Q` the upper rational parabolic subgroup of block type `(1,2)`, it stabilizes the line `ℚ e₁`", "`N_R` its arithmetic unipotent
radical and `L_R` its arithmetic Levi quotient. The radical is a lattice in `ℝ²`, and the Levi has a finite-index subgroup acting
on a modular curve."

`Γ_Q = Γ(N) ∩ Q(ℤ)` consists of the elements of `Γ(N)` with first column `(1, 0, 0)ᵗ`.  For `N ≥ 3` it is the full stabilizer
`Γ(N) ∩ Q(ℚ)` of the rational line `ℚ e₁` (`mem_lineStab_of_gammaN`).  It is the split extension of the Levi
`Γ₂(N)` (the lower right `2 × 2` block) by the radical lattice `Nℤ² = {[[1, Na, Nb], [0, 1, 0], [0, 0, 1]]}`
(`lineExt`, `lineSplitting`), the line analogue of `SeedC3S4c.gammaNExt`.
-/

open scoped MatrixGroups
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaces

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The stabilizer of the line `ℚ e₁`: the elements of `SL₃(ℤ)` with first column `(1, 0, 0)ᵗ`. -/
def lineStab : Subgroup SL(3, ℤ) where
  carrier := {γ | (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧ (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0}
  mul_mem' := by
    rintro γ δ ⟨h0, h1, h2⟩ ⟨k0, k1, k2⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, k0, k1, k2]
  one_mem' := by simp
  inv_mem' := by
    rintro γ ⟨h0, h1, h2⟩
    have hm : ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
        (γ : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    have key : ∀ i, ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) i 0 =
        (1 : Matrix (Fin 3) (Fin 3) ℤ) i 0 := by
      intro i
      have := congrFun (congrFun hm i) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, mul_zero, mul_one,
        add_zero] at this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · simpa using key 0
    · simpa using key 1
    · simpa using key 2

/-- The line group `Γ_Q = Γ(N) ∩ Q(ℤ)`. -/
def gammaNQ (N : ℕ) : Subgroup SL(3, ℤ) := gammaN N ⊓ lineStab

/-- For `N ≥ 3`, an element of `Γ(N)` lying in a rational parabolic of type `(1,2)` (first column `(c, 0, 0)ᵗ`) has `c = 1`: it
lies in the line stabilizer. -/
theorem mem_lineStab_of_gammaN {N : ℕ} (hN : 3 ≤ N) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N)
    (h1 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0) (h2 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0) :
    γ ∈ lineStab := by
  refine ⟨?_, h1, h2⟩
  have hdet : (γ : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_three, h1, h2] at hdet
  have hu : (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0 *
      ((γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
        (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1) = 1 := by
    linear_combination hdet
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hu) with h | h
  · exact h
  · exfalso
    have hd := mem_gammaN.1 hγ 0 0
    rw [h] at hd
    have h2 : (N : ℤ) ∣ 2 := by
      have := dvd_neg.mpr hd
      simpa using this
    have := Int.le_of_dvd (by norm_num) h2
    omega

/-- The Levi block (lower right `2 × 2` block) of an element of the line stabilizer. -/
def leviBlockQ (γ : SL(3, ℤ)) (hγ : γ ∈ lineStab) : SL(2, ℤ) :=
  ⟨!![(γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1, (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2;
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1, (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2], by
    obtain ⟨h0, h1, h2⟩ := hγ
    have hdet : (γ : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := γ.2
    rw [Matrix.det_fin_three, h0, h1, h2] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩

theorem leviBlockQ_mem_Gamma {N : ℕ} {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) (hs : γ ∈ lineStab) :
    leviBlockQ γ hs ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [leviBlockQ] using entry_eq_of_mem_gammaN hγ 1 1
  · simpa [leviBlockQ] using entry_eq_of_mem_gammaN hγ 1 2
  · simpa [leviBlockQ] using entry_eq_of_mem_gammaN hγ 2 1
  · simpa [leviBlockQ] using entry_eq_of_mem_gammaN hγ 2 2

theorem leviBlockQ_mul (γ δ : SL(3, ℤ)) (hγ : γ ∈ lineStab) (hδ : δ ∈ lineStab) :
    leviBlockQ (γ * δ) (lineStab.mul_mem hγ hδ) = leviBlockQ γ hγ * leviBlockQ δ hδ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  obtain ⟨h0, h1, h2⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviBlockQ, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h1, h2]

theorem leviBlockQ_one : leviBlockQ 1 lineStab.one_mem = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviBlockQ]

/-- The block-diagonal element `diag(1, A) ∈ SL₃(ℤ)`. -/
def blockDiagQ (A : SL(2, ℤ)) : SL(3, ℤ) :=
  ⟨!![1, 0, 0; 0, (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      0, (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    have hA : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := A.2
    rw [Matrix.det_fin_two] at hA
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination hA⟩

theorem blockDiagQ_mem_lineStab (A : SL(2, ℤ)) : blockDiagQ A ∈ lineStab :=
  ⟨by simp [blockDiagQ], by simp [blockDiagQ], by simp [blockDiagQ]⟩

theorem blockDiagQ_mem_gammaN {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma N) :
    blockDiagQ A ∈ gammaN N := by
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [mem_gammaN]
  have d : ∀ x y : ℤ, (x : ZMod N) = (y : ZMod N) → (N : ℤ) ∣ x - y := fun x y h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by rw [Int.cast_sub, h, sub_self])
  intro i j
  fin_cases i <;> fin_cases j <;> simp [blockDiagQ]
  · exact d _ 1 (by simpa using hA.1)
  · simpa using d _ 0 (by simpa using hA.2.1)
  · simpa using d _ 0 (by simpa using hA.2.2.1)
  · exact d _ 1 (by simpa using hA.2.2.2)

theorem blockDiagQ_mul (A B : SL(2, ℤ)) : blockDiagQ (A * B) = blockDiagQ A * blockDiagQ B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiagQ, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockDiagQ_one : blockDiagQ 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiagQ]

/-- The radical element `[[1, N a, N b], [0, 1, 0], [0, 0, 1]]` of `Γ(N) ∩ Q(ℤ)`. -/
def radEltQ (N : ℕ) (r : RadicalLattice) : SL(3, ℤ) :=
  ⟨!![1, (N : ℤ) * r.toAdd.1, (N : ℤ) * r.toAdd.2; 0, 1, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]; simp⟩

theorem radEltQ_mul (N : ℕ) (r s : RadicalLattice) :
    radEltQ N (r * s) = radEltQ N r * radEltQ N s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radEltQ, Matrix.mul_apply, Fin.sum_univ_three, mul_add, toAdd_mul, add_comm]

theorem radEltQ_one (N : ℕ) : radEltQ N 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radEltQ]

theorem radEltQ_mem_gammaN (N : ℕ) (r : RadicalLattice) : radEltQ N r ∈ gammaN N := by
  rw [mem_gammaN]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [radEltQ]

theorem radEltQ_mem_lineStab (N : ℕ) (r : RadicalLattice) : radEltQ N r ∈ lineStab :=
  ⟨by simp [radEltQ], by simp [radEltQ], by simp [radEltQ]⟩

/-- The Levi projection `Γ(N) ∩ Q(ℤ) → Γ₂(N)`. -/
def gammaNQProj (N : ℕ) : ↥(gammaNQ N) →* ↥(CongruenceSubgroup.Gamma N) where
  toFun g := ⟨leviBlockQ g.1 g.2.2, leviBlockQ_mem_Gamma g.2.1 g.2.2⟩
  map_one' := Subtype.ext leviBlockQ_one
  map_mul' g h := Subtype.ext (leviBlockQ_mul g.1 h.1 g.2.2 h.2.2)

/-- The Levi section `Γ₂(N) → Γ(N) ∩ Q(ℤ)`. -/
def gammaNQSect (N : ℕ) : ↥(CongruenceSubgroup.Gamma N) →* ↥(gammaNQ N) where
  toFun A := ⟨blockDiagQ A.1, blockDiagQ_mem_gammaN A.2, blockDiagQ_mem_lineStab A.1⟩
  map_one' := Subtype.ext blockDiagQ_one
  map_mul' A B := Subtype.ext (blockDiagQ_mul A.1 B.1)

theorem gammaNQProj_sect (N : ℕ) (A : ↥(CongruenceSubgroup.Gamma N)) :
    gammaNQProj N (gammaNQSect N A) = A := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaNQProj, gammaNQSect, leviBlockQ, blockDiagQ]

/-- The radical lattice `Nℤ²` inside `Γ(N) ∩ Q(ℤ)`. -/
def gammaNQInl (N : ℕ) : RadicalLattice →* ↥(gammaNQ N) where
  toFun r := ⟨radEltQ N r, radEltQ_mem_gammaN N r, radEltQ_mem_lineStab N r⟩
  map_one' := Subtype.ext (radEltQ_one N)
  map_mul' r s := Subtype.ext (radEltQ_mul N r s)

theorem gammaNQInl_injective (N : ℕ) [NeZero N] : Function.Injective (gammaNQInl N) := by
  intro r s h
  have h' := congrArg (fun g : ↥(gammaNQ N) => ((g : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ)) h
  have e1 := congrFun (congrFun h' 0) 1
  have e2 := congrFun (congrFun h' 0) 2
  simp only [gammaNQInl, MonoidHom.coe_mk, OneHom.coe_mk, radEltQ, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e1 e2
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply Multiplicative.toAdd.injective
  exact Prod.ext (mul_left_cancel₀ hN e1) (mul_left_cancel₀ hN e2)

theorem gammaNQProj_ker (N : ℕ) [NeZero N] (g : ↥(gammaNQ N)) (hg : gammaNQProj N g = 1) :
    ∃ r, gammaNQInl N r = g := by
  have h' := congrArg (fun A : ↥(CongruenceSubgroup.Gamma N) =>
    ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) hg
  have a00 := congrFun (congrFun h' 0) 0
  have a01 := congrFun (congrFun h' 0) 1
  have a10 := congrFun (congrFun h' 1) 0
  have a11 := congrFun (congrFun h' 1) 1
  simp only [gammaNQProj, MonoidHom.coe_mk, OneHom.coe_mk, leviBlockQ, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Subgroup.coe_one,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at a00 a01 a10 a11
  have d01 := mem_gammaN.1 g.2.1 0 1
  have d02 := mem_gammaN.1 g.2.1 0 2
  simp at d01 d02
  obtain ⟨e, he⟩ := d01
  obtain ⟨f, hf⟩ := d02
  refine ⟨Multiplicative.ofAdd (e, f), ?_⟩
  obtain ⟨⟨γ, h1⟩, h2⟩ := g
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨p0, p1, p2⟩ := h2
  have q0 : γ 0 0 = 1 := p1
  have q1 : γ 1 0 = 0 := p2.1
  have q2 : γ 2 0 = 0 := p2.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [gammaNQInl, radEltQ]

/-- **The split extension `Nℤ² → Γ(N) ∩ Q(ℤ) → Γ₂(N)`** of the paper's line group. -/
def lineExt (N : ℕ) [NeZero N] :
    GroupExtension RadicalLattice ↥(gammaNQ N) ↥(CongruenceSubgroup.Gamma N) where
  inl := gammaNQInl N
  rightHom := gammaNQProj N
  inl_injective := gammaNQInl_injective N
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gammaNQProj, gammaNQInl, leviBlockQ, radEltQ]
    · intro hg
      exact gammaNQProj_ker N g (MonoidHom.mem_ker.mp hg)
  rightHom_surjective A := ⟨gammaNQSect N A, gammaNQProj_sect N A⟩

/-- The Levi splitting of `Γ(N) ∩ Q(ℤ)`. -/
def lineSplitting (N : ℕ) [NeZero N] : (lineExt N).Splitting :=
  ⟨gammaNQSect N, gammaNQProj_sect N⟩

end TernaryPeriodPolynomials.Argument.GammaNFaces
