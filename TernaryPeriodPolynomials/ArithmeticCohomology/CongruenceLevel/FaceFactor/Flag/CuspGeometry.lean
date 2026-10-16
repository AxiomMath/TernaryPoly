module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine4
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BaseSumZeroBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Vanish

@[expose] public section


/-!
# Geometry of the flags over one line: the flags `flagAt h w`, and the letters of the line group

Formalized by Claude Sonnet 5.5.

For a frame `h` of a line and a primitive vector `w` (a cusp vector), `qMat w` is an element of the Borel of the line with first row `(1,0,0)` and `Q⁻¹ e₁ = w`, and `flagAt h w = flagOf (qMat w · h)` is the complete flag over `lineOf h` attached to
the cusp `w` (`flagLineOf_flagAt`).  `lineEmb_inl_mem_stab` and `lineEmb_split_mem_stab` are (G-a): the radical letters `ext.inl r` and the Levi letters `s A` with `A w = w` of the conjugate line group
`gammaNQAt 6 h` lie in the stabilizer of `flagAt h w`.  `gammaEquiv_symm_cuspSigma`: the generator `σ_c` of the stabilizer of the cusp `c` is `posPar (cuspPrim c)`, `cuspPrim c` the first column of `cuspElt c`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (RadicalLattice)

/-- The primitive vector `first column of cuspElt c` of a cusp `c`. -/
def cuspPrim (c : RationalLine2) : Prim2 :=
  ⟨fun i => (cuspElt c).val i 0, coprime_of_prim (isGen_cuspElt c).1⟩

/-- An element of the Borel of the line with first row `(1, 0, 0)`, lower block `Q` and `Q⁻¹ e₁ = w`. -/
def qMat (w : Prim2) : SL(3, ℤ) :=
  ⟨!![1, 0, 0; 0, w.2.choose, w.2.choose_spec.choose; 0, -(w.1 1), w.1 0], by
    rw [Matrix.det_fin_three]
    simp
    linear_combination w.2.choose_spec.choose_spec⟩

theorem qMat_mem (w : Prim2) : qMat w ∈ lineBorel := ⟨by simp [qMat], by simp [qMat]⟩

theorem qMat_00 (w : Prim2) : ((qMat w : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 := by simp [qMat]

theorem qMat_vec (w : Prim2) : qVec (qMat w) = w.1 := by
  rw [qVec_apply]
  ext i
  fin_cases i <;> simp [qMat]

theorem blockQinv_eq (q : SL(3, ℤ)) (hq : q ∈ lineBorel) : blockQinv q = blockQ q⁻¹ := by
  obtain ⟨a1, a2⟩ := blockQ_mul_inv q hq
  refine left_inv_eq_right_inv a2 ?_
  have := blockQ_mul q q⁻¹ hq
  rw [mul_inv_cancel] at this
  have h1 : blockQ (1 : SL(3, ℤ)) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [blockQ]
  rw [h1] at this
  exact this.symm

theorem conj_mem_borelStab (q m : SL(3, ℤ)) (hq : q ∈ lineBorel) (hm : m ∈ lineBorel)
    (h10 : (blockQ q * blockQ m * blockQinv q) 1 0 = 0) : q * m * q⁻¹ ∈ borelStab := by
  have hx : q * m * q⁻¹ ∈ lineBorel := lineBorel.mul_mem (lineBorel.mul_mem hq hm) (lineBorel.inv_mem hq)
  refine ⟨hx.1, hx.2, ?_⟩
  have hb : blockQ (q * m * q⁻¹) = blockQ q * blockQ m * blockQinv q := by
    rw [blockQ_mul _ _ (lineBorel.mul_mem hq hm), blockQ_mul _ _ hq, blockQinv_eq q hq]
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hb
  simp only [blockQ] at this
  rw [← h10]
  simpa [blockQ] using this

/-- Conjugating a radical element by an element of the Borel of the line gives an upper triangular matrix. -/
theorem conj_rad_borelStab (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (r : RadicalLattice) :
    q * radEltQ 6 r * q⁻¹ ∈ borelStab := by
  have hr : radEltQ 6 r ∈ lineBorel := lineStab_le_lineBorel (radEltQ_mem_lineStab 6 r)
  refine conj_mem_borelStab q _ hq hr ?_
  have h1 : blockQ (radEltQ 6 r) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [blockQ, radEltQ]
  rw [h1, Matrix.mul_one, (blockQ_mul_inv q hq).1]
  simp

/-- Conjugating the Levi lift of an element fixing the cusp vector of `q` gives an upper triangular matrix. -/
theorem conj_levi_borelStab (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (A : SL(2, ℤ))
    (hA : (A : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ qVec q = qVec q) :
    q * blockDiagQ A * q⁻¹ ∈ borelStab := by
  have hr : blockDiagQ A ∈ lineBorel := lineStab_le_lineBorel (blockDiagQ_mem_lineStab A)
  refine conj_mem_borelStab q _ hq hr ?_
  have h1 : blockQ (blockDiagQ A) = (A : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [blockQ, blockDiagQ]
  rw [h1]
  have hv : blockQinv q *ᵥ ![1, 0] = qVec q := rfl
  have key : (blockQ q * (A : Matrix (Fin 2) (Fin 2) ℤ) * blockQinv q) *ᵥ ![1, 0] = ![1, 0] := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, hA, qVec, Matrix.mulVec_mulVec, (blockQ_mul_inv q hq).1,
      Matrix.one_mulVec]
  have h10 := congrFun key 1
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h10

section Letters

variable (h : SL(3, ℤ))

/-- The radical letters of the conjugate line group, as matrices of `SL₃(ℤ)`. -/
theorem inl_val (r : RadicalLattice) : (((lineFaceExt 6 h).inl r : ↥(gammaNQAt 6 h)) : SL(3, ℤ)) = h⁻¹ * radEltQ 6 r * h := rfl

/-- The Levi letters. -/
theorem split_val (A : Gamma 6) : (((lineFaceSplitting 6 h) A : ↥(gammaNQAt 6 h)) : SL(3, ℤ)) = h⁻¹ * blockDiagQ A.1 * h := rfl

theorem mem_gammaNBAt_of_conj (h q m : SL(3, ℤ)) (hm : m ∈ gammaN 6) (hb : q * m * q⁻¹ ∈ borelStab) :
    h⁻¹ * m * h ∈ gammaNBAt 6 (q * h) := by
  rw [mem_gammaNBAt]
  have e : q * h * (h⁻¹ * m * h) * (q * h)⁻¹ = q * m * q⁻¹ := by group
  rw [e]
  exact ⟨by simpa [mul_assoc] using (gammaN_normal 6).conj_mem m hm q, hb⟩

/-- The flag over the line of `h` attached to a primitive vector `w`: the frame is `q_w h`. -/
def flagAt (h : SL(3, ℤ)) (w : Prim2) : Flag := flagOf (qMat w * h)

theorem flagLineOf_flagAt (w : Prim2) : flagLineOf (flagAt h w) = lineOf h := by
  have := (lineOf_eq_iff h (qMat w * h)).2 (by simpa using qMat_mem w)
  exact this.symm

theorem lineEmb_val (e : ↥(gammaNQAt 6 h)) :
    gammaSixEquiv.symm (lineEmb h e) = Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 h hp) e := by
  simp [lineEmb]

/-- **(G-a), radical.** -/
theorem lineEmb_inl_mem_stab (w : Prim2) (r : RadicalLattice) :
    lineEmb h ((lineFaceExt 6 h).inl r) ∈ MulAction.stabilizer Γ6 (flagAt h w) := by
  have hmem : ((Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 h hp) ((lineFaceExt 6 h).inl r) : gammaN 6) :
      SL(3, ℤ)) ∈ gammaNBAt 6 (qMat w * h) := by
    rw [show ((Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 h hp) ((lineFaceExt 6 h).inl r) : gammaN 6) : SL(3, ℤ)) =
      h⁻¹ * radEltQ 6 r * h from inl_val h r]
    exact mem_gammaNBAt_of_conj h _ _ (radEltQ_mem_gammaN 6 r) (conj_rad_borelStab _ (qMat_mem w) r)
  exact (mem_stabilizer_flagOf_iff _ (qMat w * h)).2 hmem

/-- **(G-a), Levi.** -/
theorem lineEmb_split_mem_stab (w : Prim2) (A : Gamma 6)
    (hA : ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ w.1 = w.1) :
    lineEmb h ((lineFaceSplitting 6 h) A) ∈ MulAction.stabilizer Γ6 (flagAt h w) := by
  have hmem : ((Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 h hp) ((lineFaceSplitting 6 h) A) : gammaN 6) :
      SL(3, ℤ)) ∈ gammaNBAt 6 (qMat w * h) := by
    rw [show ((Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 h hp) ((lineFaceSplitting 6 h) A) : gammaN 6) : SL(3, ℤ)) =
      h⁻¹ * blockDiagQ A.1 * h from split_val h A]
    exact mem_gammaNBAt_of_conj h _ _ (blockDiagQ_mem_gammaN A.2)
      (conj_levi_borelStab _ (qMat_mem w) A.1 (by rw [qMat_vec]; exact hA))
  exact (mem_stabilizer_flagOf_iff _ (qMat w * h)).2 hmem

end Letters

section Sigma

theorem posPar_fix (v : Fin 2 → ℤ) : (posPar v : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v = v := by
  ext i
  fin_cases i <;> simp [posPar, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem gammaEquiv_symm_cuspSigma (c : RationalLine2) :
    (gammaEquiv (by norm_num : 3 ≤ 6)).symm (cuspSigma (N := 6) c) = posParSL (cuspPrim c).1 := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  exact cuspSigma_eq_posParGL c

theorem sigma_fix (c : RationalLine2) :
    (((gammaEquiv (by norm_num : 3 ≤ 6)).symm (cuspSigma (N := 6) c) : Gamma 6) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ (cuspPrim c).1 =
      (cuspPrim c).1 := by
  rw [gammaEquiv_symm_cuspSigma]
  exact posPar_fix _

end Sigma

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
