module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Geometry

@[expose] public section


/-!
# Lemma B.1: the image of `i` is the union of integral-parabolic translates of the top cell

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3: "The map is injective, and its image is the union of integral-parabolic
translates of the standard ternary top cell: reduce the binary block and translate `w` to its
Voronoi polygon."

A binary form is *minimum-one well-rounded* (`BinWR`) if it is positive definite, takes values
`≥ 1` on nonzero integral vectors and has two independent integral vectors of value one.  Such a
form is `GL₂(ℤ)`-equivalent to `C(t) = [[1,t],[t,1]]` with `|t| ≤ 1/2` (`BinWR_reduce`: the two
minimal vectors are a `ℤ`-basis, since a nonzero lattice point in the half-open parallelogram would
have squared length at most `3/4`).  Then `{G(w,C) : C ∈ BinWR, w ∈ ℝ²}` is exactly the set of
`pᵗ A p` with `A ∈ Tcell` and `p = [[η,0],[u,D]]` integral parabolic (`image_eq_translates`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry

open Matrix

/-- Minimum-one well-rounded binary forms. -/
def BinWR (C : Mat2) : Prop :=
  Cᵀ = C ∧ (∀ v : Vec2, v ≠ 0 → 0 < quad C v) ∧
    (∀ z : Fin 2 → ℤ, z ≠ 0 → 1 ≤ quad C (intVec z)) ∧
    ∃ v1 v2 : Fin 2 → ℤ, quad C (intVec v1) = 1 ∧ quad C (intVec v2) = 1 ∧
      v1 0 * v2 1 - v1 1 * v2 0 ≠ 0

theorem Ct_binWR {t : ℝ} (ht : |t| ≤ 1/2) : BinWR (Ct t) :=
  ⟨Ct_symm t, Ct_pos ht, Ct_min_one ht, ![1, 0], ![0, 1],
    by simp [quad_Ct, intVec], by simp [quad_Ct, intVec], by simp⟩

theorem intVec_sub (z z' : Fin 2 → ℤ) : intVec (z - z') = intVec z - intVec z' := by
  funext i; simp [intVec]

theorem intVec_mulVec (D : IMat2) (z : Fin 2 → ℤ) :
    castMat D *ᵥ intVec z = intVec (D *ᵥ z) := castMat_mulVec_intVec D z

theorem castMat_mul (D E : IMat2) : castMat (D * E) = castMat D * castMat E :=
  (Int.castRingHom ℝ).mapMatrix.map_mul D E

theorem castMat_one : castMat (1 : IMat2) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [castMat]

theorem castMat_transpose' (D : IMat2) : (castMat D)ᵀ = castMat Dᵀ := by
  ext i j; simp [castMat]

theorem castMat_det (D : IMat2) : (castMat D).det = (D.det : ℝ) :=
  (RingHom.map_det (Int.castRingHom ℝ) D).symm

/-- A binary minimum-one well-rounded form is `DᵗC(t)D` for a unimodular `D` and `|t| ≤ 1/2`. -/
theorem BinWR_reduce {C : Mat2} (hC : BinWR C) :
    ∃ t : ℝ, |t| ≤ 1/2 ∧ ∃ D D' : IMat2, D * D' = 1 ∧ D' * D = 1 ∧
      C = (castMat D)ᵀ * Ct t * castMat D := by
  obtain ⟨hsym, hpos, hmin, v1, v2, h1, h2, hdet⟩ := hC
  let P : IMat2 := !![v1 0, v2 0; v1 1, v2 1]
  have hPdet : P.det = v1 0 * v2 1 - v1 1 * v2 0 := by
    simp [P, Matrix.det_fin_two]; ring
  have hPdetR : (castMat P).det ≠ 0 := by
    rw [castMat_det, hPdet]; exact_mod_cast hdet
  have hPdetZ : P.det ≠ 0 := by rw [hPdet]; exact hdet
  have hC10 : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hsym 0) 1
  -- the Gram matrix of the two minimal vectors
  obtain ⟨s, hs⟩ : ∃ s : ℝ, (castMat P)ᵀ * C * castMat P = Ct s := by
    refine ⟨((castMat P)ᵀ * C * castMat P) 0 1, ?_⟩
    have e00 : ((castMat P)ᵀ * C * castMat P) 0 0 = 1 := by
      have := h1
      simp only [quad, intVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [castMat, P, Matrix.mul_apply, Fin.sum_univ_two]
      nlinarith [this, hC10]
    have e11 : ((castMat P)ᵀ * C * castMat P) 1 1 = 1 := by
      have := h2
      simp only [quad, intVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [castMat, P, Matrix.mul_apply, Fin.sum_univ_two]
      nlinarith [this, hC10]
    have e10 : ((castMat P)ᵀ * C * castMat P) 1 0 = ((castMat P)ᵀ * C * castMat P) 0 1 := by
      simp [castMat, P, Matrix.mul_apply, Fin.sum_univ_two, hC10]
      ring
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Ct] using e00
    · simp [Ct]
    · simpa [Ct] using e10
    · simpa [Ct] using e11
  have hquad : ∀ u : Fin 2 → ℤ, quad C (intVec (P *ᵥ u)) = quad (Ct s) (intVec u) := by
    intro u
    rw [← hs, quad_conj, castMat_mulVec_intVec]
  -- |s| ≤ 1/2
  have hinj : ∀ u : Fin 2 → ℤ, P *ᵥ u = 0 → u = 0 := fun u h =>
    Matrix.eq_zero_of_mulVec_eq_zero hPdetZ h
  have hs12 : |s| ≤ 1/2 := by
    have a1 := hmin (P *ᵥ ![1, 1]) (fun h => by
      have := hinj _ h; have := congrFun this 0; simp at this)
    have a2 := hmin (P *ᵥ ![1, -1]) (fun h => by
      have := hinj _ h; have := congrFun this 0; simp at this)
    rw [hquad, quad_Ct] at a1 a2
    simp [intVec] at a1 a2
    rw [abs_le]
    constructor <;> nlinarith [a1, a2]
  -- surjectivity of `P` on `ℤ²`
  have hsurj : ∀ z : Fin 2 → ℤ, ∃ a : Fin 2 → ℤ, P *ᵥ a = z := by
    intro z
    set Pr := castMat P with hPr
    have hunit : IsUnit Pr.det := isUnit_iff_ne_zero.mpr hPdetR
    let c : Vec2 := Pr⁻¹ *ᵥ intVec z
    have hc : Pr *ᵥ c = intVec z := by
      simp only [c, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    let a : Fin 2 → ℤ := fun i => round (c i)
    refine ⟨a, ?_⟩
    set z' : Fin 2 → ℤ := z - P *ᵥ a with hz'
    have hz'r : intVec z' = Pr *ᵥ (c - intVec a) := by
      rw [Matrix.mulVec_sub, hc, hPr, castMat_mulVec_intVec]
      show intVec (z - P *ᵥ a) = _
      rw [intVec_sub]
    have hu : ∀ i, |(c - intVec a) i| ≤ 1/2 := by
      intro i
      simp only [Pi.sub_apply, intVec, a]
      exact abs_sub_round (c i)
    by_contra hne
    have hz0 : z' ≠ 0 := by
      intro h
      apply hne
      exact (sub_eq_zero.mp h).symm
    have hlow := hmin z' hz0
    have hq : quad C (intVec z') = quad (Ct s) (c - intVec a) := by
      rw [hz'r, ← hs, quad_conj, hPr]
    rw [hq, quad_Ct] at hlow
    have u0 := abs_le.mp (hu 0)
    have u1 := abs_le.mp (hu 1)
    have s1 := abs_le.mp hs12
    set x0 := (c - intVec a) 0 with hx0
    set x1 := (c - intVec a) 1 with hx1
    have hx0s : x0 ^ 2 ≤ 1/4 := by nlinarith
    have hx1s : x1 ^ 2 ≤ 1/4 := by nlinarith
    have hprod : |x0 * x1| ≤ 1/4 := by
      rw [abs_mul]
      nlinarith [abs_nonneg x0, abs_nonneg x1, hu 0, hu 1]
    have hsp : |s * (x0 * x1)| ≤ 1/8 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg (x0 * x1)]
    have hsp' := abs_le.mp hsp
    nlinarith [hsp'.1, hsp'.2]
  -- the inverse matrix
  choose a ha using hsurj
  let E : IMat2 := !![a ![1, 0] 0, a ![0, 1] 0; a ![1, 0] 1, a ![0, 1] 1]
  have hPE : P * E = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · have := congrFun (ha ![1, 0]) 0
      simpa [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] using this
    · have := congrFun (ha ![0, 1]) 0
      simpa [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] using this
    · have := congrFun (ha ![1, 0]) 1
      simpa [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] using this
    · have := congrFun (ha ![0, 1]) 1
      simpa [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] using this
  have hEP : E * P = 1 := by
    exact mul_eq_one_comm.mp hPE
  refine ⟨s, hs12, E, P, ?_, ?_, ?_⟩
  · exact hEP
  · exact hPE
  · have h1' : castMat P * castMat E = 1 := by rw [← castMat_mul, hPE, castMat_one]
    have h2' : castMat E * castMat P = 1 := by rw [← castMat_mul, hEP, castMat_one]
    rw [← hs]
    have e : (castMat E)ᵀ * ((castMat P)ᵀ * C * castMat P) * castMat E =
        (castMat P * castMat E)ᵀ * C * (castMat P * castMat E) := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    rw [e, h1']; simp

/-! ### The image of `i` -/

theorem BinWR_conj {t : ℝ} (ht : |t| ≤ 1/2) (D D' : IMat2) (h1 : D * D' = 1) (h2 : D' * D = 1) :
    BinWR ((castMat D)ᵀ * Ct t * castMat D) := by
  have hmul : castMat D * castMat D' = 1 := by rw [← castMat_mul, h1, castMat_one]
  have hmul' : castMat D' * castMat D = 1 := by rw [← castMat_mul, h2, castMat_one]
  have hinjR : ∀ v : Vec2, castMat D *ᵥ v = 0 → v = 0 := by
    intro v h
    have h' : castMat D' *ᵥ (castMat D *ᵥ v) = castMat D' *ᵥ 0 := by rw [h]
    rwa [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec, Matrix.mulVec_zero] at h'
  have hinjZ : ∀ z : Fin 2 → ℤ, D *ᵥ z = 0 → z = 0 := by
    intro z h
    have h' : D' *ᵥ (D *ᵥ z) = D' *ᵥ 0 := by rw [h]
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h'
  refine ⟨castMat_symm (Ct_symm t) D, ?_, ?_, ![D' 0 0, D' 1 0], ![D' 0 1, D' 1 1], ?_, ?_, ?_⟩
  · intro v hv
    rw [quad_conj]
    exact Ct_pos ht _ (fun h => hv (hinjR v h))
  · intro z hz
    rw [quad_conj, castMat_mulVec_intVec]
    exact Ct_min_one ht _ (fun h => hz (hinjZ z h))
  · rw [quad_conj, castMat_mulVec_intVec]
    have e00 : D 0 0 * D' 0 0 + D 0 1 * D' 1 0 = 1 := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have e10 : D 1 0 * D' 0 0 + D 1 1 * D' 1 0 = 0 := by
      have := congrFun (congrFun h1 1) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have : D *ᵥ ![D' 0 0, D' 1 0] = ![1, 0] := by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> linarith
    rw [this]
    simp [quad_Ct, intVec]
  · rw [quad_conj, castMat_mulVec_intVec]
    have e01 : D 0 0 * D' 0 1 + D 0 1 * D' 1 1 = 0 := by
      have := congrFun (congrFun h1 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have e11 : D 1 0 * D' 0 1 + D 1 1 * D' 1 1 = 1 := by
      have := congrFun (congrFun h1 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have : D *ᵥ ![D' 0 1, D' 1 1] = ![0, 1] := by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> linarith
    rw [this]
    simp [quad_Ct, intVec]
  · have hd : D.det * D'.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
    have : D'.det ≠ 0 := by intro h; rw [h] at hd; simp at hd
    simpa [Matrix.det_fin_two, mul_comm] using this

/-- The top cell translated by the integral parabolic. -/
def Translates : Set Mat3 :=
  {B | ∃ A ∈ Tcell, ∃ (η : ℤ) (u : Fin 2 → ℤ) (D D' : IMat2), (η = 1 ∨ η = -1) ∧
    D * D' = 1 ∧ D' * D = 1 ∧ B = (parab η u D)ᵀ * A * parab η u D}

/-- The image of `i(w, C) = G(w, C)` over all minimum-one well-rounded binary `C` and `w ∈ ℝ²`. -/
def GImage : Set Mat3 := {B | ∃ (C : Mat2) (w : Vec2), BinWR C ∧ B = Gmat w C}

/-- **The image of `i` is the union of integral-parabolic translates of the standard ternary top
cell.** -/
theorem image_eq_translates : GImage = Translates := by
  ext B
  constructor
  · rintro ⟨C, w, hC, rfl⟩
    obtain ⟨t, ht, D, D', h1, h2, hCD⟩ := BinWR_reduce hC
    obtain ⟨z0, hz0⟩ := exists_nearest ht (castMat D *ᵥ w)
    set w0 : Vec2 := castMat D *ᵥ w - intVec z0 with hw0
    have hvor : w0 ∈ Voronoi (Ct t) := by
      rw [mem_Voronoi_iff ht]
      intro z
      have := hz0 (z0 + z)
      have e : castMat D *ᵥ w - intVec (z0 + z) = w0 - intVec z := by
        rw [intVec_add, hw0]; abel
      rwa [e] at this
    refine ⟨Gmat w0 (Ct t), Gmat_mem_Tcell ht hvor, 1, z0, D, D', Or.inl rfl, h1, h2, ?_⟩
    rw [Gmat_equivariant (Ct_symm t) D D' h1 h2 z0 1 (Or.inl rfl) w0 w, ← hCD]
    rw [hw0]; push_cast; module
  · rintro ⟨A, hA, η, u, D, D', hη, h1, h2, rfl⟩
    obtain ⟨t, ht, w0, hw0, rfl⟩ := Tcell_eq_Gmat hA
    have hmul : castMat D * castMat D' = 1 := by rw [← castMat_mul, h1, castMat_one]
    refine ⟨(castMat D)ᵀ * Ct t * castMat D, castMat D' *ᵥ (intVec u + (η : ℝ) • w0),
      BinWR_conj ht D D' h1 h2, ?_⟩
    rw [Gmat_equivariant (Ct_symm t) D D' h1 h2 u η hη w0 _]
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

end TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry
