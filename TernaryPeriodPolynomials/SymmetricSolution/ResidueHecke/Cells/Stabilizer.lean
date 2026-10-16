module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Geometry

@[expose] public section


/-!
# Lemma B.1: the stabilizer of the ternary top cell has order 48, and 16 preserve `H`

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3
(`app:Hecke-coordinate`): "The ternary cell stabilizer has order 48 and the
stabilizer also preserving `H` has order 16. Their three cosets give the three coordinate residues."

`GL₃(ℤ)` acts on forms by `A ↦ gᵗ A g`.  The stabilizer of `Tcell` (the unit-diagonal top cell)
is exactly the group of signed permutation matrices (order 48): the identity form lies in the
cell, so a stabilizing `g` has columns of Euclidean norm one.  Those with first row `(±1,0,0)`,
i.e. preserving the hyperplane `H = {a = 0}`, form a subgroup of order 16, and the 48 elements
fall into three cosets according to the position of the nonzero entry of the first row.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry

open Matrix

abbrev IMat3 := Matrix (Fin 3) (Fin 3) ℤ

/-- The real matrix underlying an integral ternary matrix. -/
def castMat3 (g : IMat3) : Mat3 := g.map (Int.cast : ℤ → ℝ)

theorem castMat3_mulVec (g : IMat3) (v : Fin 3 → ℤ) :
    castMat3 g *ᵥ castVec3 v = castVec3 (g *ᵥ v) := by
  funext i
  simp [castMat3, castVec3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem castMat3_mul (g h : IMat3) : castMat3 (g * h) = castMat3 g * castMat3 h := by
  exact (Int.castRingHom ℝ).mapMatrix.map_mul g h

theorem castMat3_det (g : IMat3) : (castMat3 g).det = (g.det : ℝ) :=
  (RingHom.map_det (Int.castRingHom ℝ) g).symm

theorem castMat3_transpose (g : IMat3) : (castMat3 g)ᵀ = castMat3 gᵀ := by
  ext i j; simp [castMat3]

/-- The six signed unit vectors. -/
def colVec : Fin 6 → (Fin 3 → ℤ) :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]]

/-- The integral matrix with the prescribed signed-unit columns. -/
def matOfCols (c : Fin 3 → Fin 6) : IMat3 := fun i j => colVec (c j) i

/-- The `48` signed permutation matrices. -/
def SignedPerms : Finset IMat3 :=
  (Finset.univ.filter
    (fun c : Fin 3 → Fin 6 => (matOfCols c).det = 1 ∨ (matOfCols c).det = -1)).image matOfCols

theorem colVec_injective : Function.Injective colVec := by decide +kernel

theorem matOfCols_injective : Function.Injective matOfCols := by
  intro c c' h
  funext j
  apply colVec_injective
  funext i
  exact congrFun (congrFun h i) j

/-- There are exactly `48` signed permutation matrices. -/
theorem signedPerms_card : SignedPerms.card = 48 := by
  unfold SignedPerms
  rw [Finset.card_image_of_injective _ matOfCols_injective]
  decide +kernel

/-- Those with first row `(±1, 0, 0)`, i.e. preserving the hyperplane `H = {a = 0}`: order 16. -/
theorem signedPerms_H_card :
    (SignedPerms.filter (fun g => g 0 1 = 0 ∧ g 0 2 = 0)).card = 16 := by
  unfold SignedPerms
  rw [Finset.filter_image, Finset.card_image_of_injective _ matOfCols_injective]
  decide +kernel

/-- The first row of each element has exactly one nonzero entry, at position `i`; the three
cosets of the stabilizer of `H` have the same order `16`. -/
theorem signedPerms_cosets (i : Fin 3) :
    (SignedPerms.filter (fun g => ∀ j, j ≠ i → g 0 j = 0)).card = 16 := by
  unfold SignedPerms
  rw [Finset.filter_image, Finset.card_image_of_injective _ matOfCols_injective]
  fin_cases i <;> decide +kernel

theorem signedPerms_first_row : ∀ g ∈ SignedPerms, ∃ i : Fin 3, ∀ j, j ≠ i → g 0 j = 0 := by
  unfold SignedPerms
  decide +kernel

theorem signedPerms_transpose : ∀ g ∈ SignedPerms, gᵀ ∈ SignedPerms ∧ g * gᵀ = 1 := by
  unfold SignedPerms
  decide +kernel

theorem signedPerms_det : ∀ g ∈ SignedPerms, g.det = 1 ∨ g.det = -1 := by
  intro g hg
  unfold SignedPerms at hg
  rw [Finset.mem_image] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  simpa using hc

theorem signedPerms_cols : ∀ g ∈ SignedPerms, ∀ j : Fin 3, ∃ k : Fin 6, (fun i => g i j) = colVec k := by
  intro g hg j
  unfold SignedPerms at hg
  rw [Finset.mem_image] at hg
  obtain ⟨c, _, rfl⟩ := hg
  exact ⟨c j, rfl⟩

/-- The identity form lies in the cell. -/
theorem one_mem_Tcell : (1 : Mat3) ∈ Tcell := by
  refine ⟨⟨by simp, ?_⟩, by simp, by simp, by simp, ?_⟩
  · intro v hv
    simp only [Matrix.one_mulVec, dotProduct, Fin.sum_univ_three]
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  · intro v hv
    simp only [Matrix.one_mulVec, dotProduct, Fin.sum_univ_three, castVec3]
    have : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hv
      funext i
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    have key : ∀ a : ℤ, a ≠ 0 → (1 : ℝ) ≤ (a : ℝ) * (a : ℝ) := by
      intro a ha
      have : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
      nlinarith [abs_mul_abs_self (a : ℝ)]
    rcases this with h | h | h
    · nlinarith [key _ h, mul_self_nonneg (v 1 : ℝ), mul_self_nonneg (v 2 : ℝ)]
    · nlinarith [key _ h, mul_self_nonneg (v 0 : ℝ), mul_self_nonneg (v 2 : ℝ)]
    · nlinarith [key _ h, mul_self_nonneg (v 0 : ℝ), mul_self_nonneg (v 1 : ℝ)]

/-- `g ∈ GL₃(ℤ)` stabilizes the cell `Tcell` under `A ↦ gᵗ A g`. -/
def StabCell (g : IMat3) : Prop :=
  (g.det = 1 ∨ g.det = -1) ∧
    ∀ A : Mat3, A ∈ Tcell ↔ (castMat3 g)ᵀ * A * castMat3 g ∈ Tcell

theorem exists_colVec3 (a b c : ℤ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    ∃ k : Fin 6, ![a, b, c] = colVec k := by
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b, sq_nonneg c]
  have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a, sq_nonneg c]
  have hc : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    first | (exfalso; norm_num at h; done) | decide

theorem diag_formula (P A : Mat3) (j : Fin 3) :
    (Pᵀ * A * P) j j = (fun i => P i j) ⬝ᵥ (A *ᵥ (fun i => P i j)) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.transpose_apply]
  ring

theorem stabCell_imp {g : IMat3} (hg : StabCell g) : g ∈ SignedPerms := by
  obtain ⟨hdet, hiff⟩ := hg
  obtain ⟨_, d0, d1, d2, _⟩ := (hiff 1).mp one_mem_Tcell
  have hcol : ∀ j : Fin 3, g 0 j ^ 2 + g 1 j ^ 2 + g 2 j ^ 2 = 1 := by
    intro j
    have h1 : ((castMat3 g)ᵀ * (1 : Mat3) * castMat3 g) j j = 1 := by
      fin_cases j
      · exact d0
      · exact d1
      · exact d2
    rw [diag_formula] at h1
    simp only [dotProduct, Matrix.one_mulVec, Fin.sum_univ_three, castMat3, Matrix.map_apply] at h1
    have : (((g 0 j) ^ 2 + (g 1 j) ^ 2 + (g 2 j) ^ 2 : ℤ) : ℝ) = 1 := by
      push_cast; nlinarith [h1]
    exact_mod_cast this
  choose k hk using fun j => exists_colVec3 (g 0 j) (g 1 j) (g 2 j) (hcol j)
  have hgk : g = matOfCols k := by
    ext i j
    have := congrFun (hk j) i
    fin_cases i <;> simpa [matOfCols] using this
  unfold SignedPerms
  rw [Finset.mem_image]
  refine ⟨k, ?_, hgk.symm⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← hgk]
  exact hdet

theorem preserves {g : IMat3} (hg : g ∈ SignedPerms) {A : Mat3} (hA : A ∈ Tcell) :
    (castMat3 g)ᵀ * A * castMat3 g ∈ Tcell := by
  obtain ⟨⟨hsym, hpos⟩, h00, h11, h22, hmin⟩ := hA
  have hdet := signedPerms_det g hg
  have hdetR : (castMat3 g).det ≠ 0 := by
    rw [castMat3_det]; rcases hdet with h | h <;> simp [h]
  have hdetZ : g.det ≠ 0 := by rcases hdet with h | h <;> simp [h]
  have hinj : ∀ v, castMat3 g *ᵥ v = 0 → v = 0 := fun v h =>
    Matrix.eq_zero_of_mulVec_eq_zero hdetR h
  have hinjZ : ∀ v : Fin 3 → ℤ, g *ᵥ v = 0 → v = 0 := fun v h =>
    Matrix.eq_zero_of_mulVec_eq_zero hdetZ h
  have hdiag : ∀ j : Fin 3, ((castMat3 g)ᵀ * A * castMat3 g) j j = 1 := by
    intro j
    rw [diag_formula]
    obtain ⟨k, hk⟩ := signedPerms_cols g hg j
    have hcolj : (fun i => (castMat3 g) i j) = castVec3 (colVec k) := by
      funext i
      have := congrFun hk i
      simp [castMat3, castVec3, this]
    rw [hcolj]
    fin_cases k <;> simp [colVec, castVec3, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      h00, h11, h22]
  refine ⟨⟨?_, ?_⟩, hdiag 0, hdiag 1, hdiag 2, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, hsym, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  · intro v hv
    rw [quad_conj3]
    apply hpos
    intro h
    exact hv (hinj v h)
  · intro v hv
    rw [quad_conj3, castMat3_mulVec]
    apply hmin
    intro h
    exact hv (hinjZ v h)

theorem mem_signedPerms_imp {g : IMat3} (hg : g ∈ SignedPerms) : StabCell g := by
  refine ⟨signedPerms_det g hg, fun A => ⟨preserves hg, fun h => ?_⟩⟩
  obtain ⟨hgt, hgg⟩ := signedPerms_transpose g hg
  have := preserves hgt h
  have e : (castMat3 gᵀ)ᵀ * ((castMat3 g)ᵀ * A * castMat3 g) * castMat3 gᵀ = A := by
    have h1 : castMat3 g * (castMat3 g)ᵀ = 1 := by
      rw [castMat3_transpose, ← castMat3_mul, hgg]
      simp [castMat3]
    rw [← castMat3_transpose, Matrix.transpose_transpose]
    calc castMat3 g * ((castMat3 g)ᵀ * A * castMat3 g) * (castMat3 g)ᵀ
        = (castMat3 g * (castMat3 g)ᵀ) * A * (castMat3 g * (castMat3 g)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1]; simp
  rw [e] at this
  exact this

theorem stabCell_iff (g : IMat3) : StabCell g ↔ g ∈ SignedPerms :=
  ⟨stabCell_imp, mem_signedPerms_imp⟩

/-- **The stabilizer of the ternary top cell in `GL₃(ℤ)` has order 48** (the signed permutation
matrices). -/
theorem stabilizer_card : Set.ncard {g : IMat3 | StabCell g} = 48 := by
  have : {g : IMat3 | StabCell g} = (SignedPerms : Set IMat3) := by
    ext g; simp [stabCell_iff]
  rw [this, Set.ncard_coe_finset, signedPerms_card]

/-- **The stabilizer of the cell which also preserves `H = {a = 0}` has order 16** (first row
`(±1, 0, 0)`). -/
theorem stabilizer_H_card :
    Set.ncard {g : IMat3 | StabCell g ∧ g 0 1 = 0 ∧ g 0 2 = 0} = 16 := by
  have : {g : IMat3 | StabCell g ∧ g 0 1 = 0 ∧ g 0 2 = 0} =
      ((SignedPerms.filter (fun g => g 0 1 = 0 ∧ g 0 2 = 0) : Finset IMat3) : Set IMat3) := by
    ext g; simp [stabCell_iff]
  rw [this, Set.ncard_coe_finset, signedPerms_H_card]

/-- Three cosets: the stabilizer of the cell is the disjoint union of the three sets of matrices
whose first row is supported at the `i`-th coordinate, `i = 0, 1, 2`, each of order `16 = 48/3`
(these are the three coordinate residues of the cell). -/
theorem stabilizer_cosets (i : Fin 3) :
    Set.ncard {g : IMat3 | StabCell g ∧ ∀ j, j ≠ i → g 0 j = 0} = 16 := by
  have : {g : IMat3 | StabCell g ∧ ∀ j, j ≠ i → g 0 j = 0} =
      ((SignedPerms.filter (fun g => ∀ j, j ≠ i → g 0 j = 0) : Finset IMat3) : Set IMat3) := by
    ext g; simp [stabCell_iff]
  rw [this, Set.ncard_coe_finset, signedPerms_cosets]

theorem stabilizer_first_row (g : IMat3) (hg : StabCell g) :
    ∃ i : Fin 3, ∀ j, j ≠ i → g 0 j = 0 :=
  signedPerms_first_row g ((stabCell_iff g).mp hg)

end TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry
