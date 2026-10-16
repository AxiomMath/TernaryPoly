module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SeedK0
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.BasisChange
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitGL
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlaneG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinGlobal
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinBlockMulti

@[expose] public section


/-!
# Local plane data at one place (step B2-i)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a local pair `z = (s,t)` with `max ‖s‖ ‖t‖ = p^r`, `exists_k0` gives an integral `k` with
`det k = 1` and a `2 × 2` block `A` with `det A = p^r`. The local plane datum is
`P = L(z) · k` and `κ = k⁻¹` (the adjugate), so that `L(z) = P κ`, `P` has bottom row
`(0, 0, *)`, `blk2 P = ψ(A)`, and `κ` is `GL₃`-integral at the place. For integral `(s,t)` the
`ℤ²`-term is `P = 1`, `κ = L(z)`. These are the local hypotheses of `pointwise_multi`.
-/

open Matrix PadicInt GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlane

section Generic

variable {p : ℕ} [Fact p.Prime] {K : Type*} [CommRing K]

lemma lpToQMap (f : ℚ_[p] →+* K) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) :
    (toQ k).map f = k.map (f.comp cq) := by
  rw [toQ, Matrix.map_map]; rfl

lemma lpPlaneMap (f : ℚ_[p] →+* K) (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) :
    (Lst s t * toQ k).map f = (Lst s t).map f * k.map (f.comp cq) := by
  rw [Matrix.map_mul, lpToQMap]

lemma lpKMulAdj (f : ℚ_[p] →+* K) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    k.map (f.comp cq) * k.adjugate.map (f.comp cq) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_adjugate, hk, one_smul,
    Matrix.map_one (f.comp cq) (map_zero (f.comp cq)) (map_one (f.comp cq))]

lemma lpAdjMulK (f : ℚ_[p] →+* K) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    k.adjugate.map (f.comp cq) * k.map (f.comp cq) = 1 := by
  rw [← Matrix.map_mul, Matrix.adjugate_mul, hk, one_smul,
    Matrix.map_one (f.comp cq) (map_zero (f.comp cq)) (map_one (f.comp cq))]

lemma lpLstMapInv (f : ℚ_[p] →+* K) (s t : ℚ_[p]) :
    (Lst s t).map f * (LstInv s t).map f = 1 := by
  rw [← Matrix.map_mul, Lst_mul_LstInv, Matrix.map_one f (map_zero f) (map_one f)]

lemma lpInvMapLst (f : ℚ_[p] →+* K) (s t : ℚ_[p]) :
    (LstInv s t).map f * (Lst s t).map f = 1 := by
  rw [← Matrix.map_mul, LstInv_mul_Lst, Matrix.map_one f (map_zero f) (map_one f)]

lemma lpLstR_map (f : ℚ_[p] →+* K) (s t : ℚ_[p]) :
    LstR (f s) (f t) = (Lst s t).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LstR, Lst, Matrix.map_apply]

/-- The `GL₃(K)`-element `L(z) · k` for an integral unimodular `k`. -/
def lpPlane (f : ℚ_[p] →+* K) (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    GeneralLinearGroup (Fin 3) K :=
  ⟨(Lst s t).map f * k.map (f.comp cq), k.adjugate.map (f.comp cq) * (LstInv s t).map f,
    by
      calc (Lst s t).map f * k.map (f.comp cq) * (k.adjugate.map (f.comp cq) * (LstInv s t).map f)
          = (Lst s t).map f * (k.map (f.comp cq) * k.adjugate.map (f.comp cq)) *
              (LstInv s t).map f := by simp only [mul_assoc]
        _ = (Lst s t).map f * (LstInv s t).map f := by rw [lpKMulAdj f k hk, mul_one]
        _ = 1 := lpLstMapInv f s t,
    by
      calc k.adjugate.map (f.comp cq) * (LstInv s t).map f * ((Lst s t).map f * k.map (f.comp cq))
          = k.adjugate.map (f.comp cq) * ((LstInv s t).map f * (Lst s t).map f) *
              k.map (f.comp cq) := by simp only [mul_assoc]
        _ = k.adjugate.map (f.comp cq) * k.map (f.comp cq) := by
              rw [lpInvMapLst f s t, mul_one]
        _ = 1 := lpAdjMulK f k hk⟩

/-- The `GL₃(K)`-element `k⁻¹ = adj k` for an integral unimodular `k`. -/
def lpKappa (f : ℚ_[p] →+* K) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    GeneralLinearGroup (Fin 3) K :=
  ⟨k.adjugate.map (f.comp cq), k.map (f.comp cq), lpAdjMulK f k hk, lpKMulAdj f k hk⟩

lemma lpPlane_val (f : ℚ_[p] →+* K) (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (hk : k.det = 1) :
    (lpPlane f s t k hk).val = (Lst s t).map f * k.map (f.comp cq) := rfl

lemma lpKappa_val (f : ℚ_[p] →+* K) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (hk : k.det = 1) :
    (lpKappa f k hk).val = k.adjugate.map (f.comp cq) := rfl

lemma lpPlane_mul_kappa (f : ℚ_[p] →+* K) (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (hk : k.det = 1) :
    (lpPlane f s t k hk).val * (lpKappa f k hk).val = LstR (f s) (f t) := by
  rw [lpPlane_val, lpKappa_val, lpLstR_map, mul_assoc, lpKMulAdj f k hk, mul_one]

lemma lpPlane_bottom (f : ℚ_[p] →+* K) (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (hk : k.det = 1) (h20 : (Lst s t * toQ k) 2 0 = 0) (h21 : (Lst s t * toQ k) 2 1 = 0) :
    (lpPlane f s t k hk).val 2 0 = 0 ∧ (lpPlane f s t k hk).val 2 1 = 0 := by
  constructor
  · rw [lpPlane_val, ← lpPlaneMap, Matrix.map_apply, h20, map_zero]
  · rw [lpPlane_val, ← lpPlaneMap, Matrix.map_apply, h21, map_zero]

lemma lpBlk2_apply {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 2) :
    blk2 M i j = M i.castSucc j.castSucc := by
  fin_cases i <;> fin_cases j <;> rfl

lemma lpPlane_blk2 (f : ℚ_[p] →+* K) (s t : ℚ_[p]) (k : Matrix (Fin 3) (Fin 3) ℤ_[p])
    (hk : k.det = 1) (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ i j : Fin 2, (Lst s t * toQ k) i.castSucc j.castSucc = (A i j : ℚ_[p])) :
    blk2 (lpPlane f s t k hk).val = A.map (fun x => f (x : ℚ_[p])) := by
  ext i j
  have h := congrArg f (hA i j)
  rw [lpBlk2_apply, lpPlane_val, ← lpPlaneMap, Matrix.map_apply, Matrix.map_apply]
  exact h

end Generic

section Place

/-- Local plane data for a shell pair at the place `v`. -/
theorem local_plane_shell (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (r : ℕ) {s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hmax : max ‖s‖ ‖t‖ = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r) :
    ∃ P κ : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ),
      P.val 2 0 = 0 ∧ P.val 2 1 = 0 ∧
      LstR (psiV v s) (psiV v t) = P.val * κ.val ∧ IntGL3 v κ.val ∧
      ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val],
        A.det = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ^ r ∧
        blk2 P.val = A.map (fun x => psiV v (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) := by
  obtain ⟨k, A, hK⟩ := exists_k0 r hmax
  obtain ⟨hk, hAdet, -, hent, h20, h21, -⟩ := hK
  obtain ⟨b20, b21⟩ := lpPlane_bottom (psiV v) s t k hk h20 h21
  refine ⟨lpPlane (psiV v) s t k hk, lpKappa (psiV v) k hk, b20, b21,
    (lpPlane_mul_kappa (psiV v) s t k hk).symm, ?_, A, hAdet,
    lpPlane_blk2 (psiV v) s t k hk A hent⟩
  rw [lpKappa_val]
  refine ⟨Matrix.isUnit_det_of_right_inverse (lpAdjMulK (psiV v) k hk), fun i j => ?_,
    fun i j => ?_⟩
  · rw [Matrix.map_apply]
    exact psiV_mem_OS v (k.adjugate i j)
  · rw [Matrix.inv_eq_right_inv (lpAdjMulK (psiV v) k hk), Matrix.map_apply]
    exact psiV_mem_OS v (k i j)

/-- The `GL₃(K)`-element `L(z)` for an arbitrary pair in `K`. -/
def lstUnit {K : Type*} [CommRing K] (s t : K) : GeneralLinearGroup (Fin 3) K :=
  ⟨LstR s t, LstRInv s t, LstR_mul_LstRInv s t, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LstR, LstRInv, Matrix.mul_apply, Fin.sum_univ_three]⟩

lemma lstUnit_val {K : Type*} [CommRing K] (s t : K) : (lstUnit s t).val = LstR s t := rfl

/-- The `ℤ²`-term: for integral `(s,t)`, `P = 1` and `κ = L(z)`. -/
theorem local_plane_zero (v : FinitePlace) {s t : v.adicCompletion ℚ} (hs : s ∈ OS v)
    (ht : t ∈ OS v) :
    ∃ P κ : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ),
      P.val 2 0 = 0 ∧ P.val 2 1 = 0 ∧ LstR s t = P.val * κ.val ∧ IntGL3 v κ.val ∧
      blk2 P.val = 1 := by
  refine ⟨1, lstUnit s t, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · rw [Units.val_one, one_mul, lstUnit_val]
  · rw [lstUnit_val]
    exact intGL3_LstR v hs ht
  · rw [Units.val_one]
    exact blk2_one

end Place

end TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlane
