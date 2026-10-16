module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Plane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinGlobal
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBasis
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp

@[expose] public section


/-!
# Hermite-class adjustment of the local plane data (step B2-i, class form)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a shell pair `z` with `max ‖z.1‖ ‖z.2‖ = p^r` and a Hermite class `tc ∈ cyclicHNF p r` with
`pairLat z = hermLat tc`, `exists_k0` gives `A` with `A = Mz tc * D`, `det D = 1` (`exists_mul_Mz`).
Multiplying `P` on the right by `diag(adj D, 1)` and `κ` on the left by `diag(D, 1)` keeps
`P κ = L(z)` and the bottom row zero, and makes `blk2 P = Mz tc` exactly, so the local datum depends
only on the Hermite class. `κ' = diag(D,1) κ` stays integral.
-/

open Matrix PadicInt GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBasis
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlaneClass

/-- The block embedding `diag(M, 1)` of a `2 × 2` matrix into `3 × 3`. -/
def emb2 {R : Type*} [Zero R] [One R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

section Algebra

variable {R : Type*} [CommRing R]

lemma emb2_mul (M N : Matrix (Fin 2) (Fin 2) R) : emb2 (M * N) = emb2 M * emb2 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

lemma emb2_one : emb2 (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb2]

lemma blk2_mul_emb2 (M : Matrix (Fin 3) (Fin 3) R) (N : Matrix (Fin 2) (Fin 2) R) :
    blk2 (M * emb2 N) = blk2 M * N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, emb2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

lemma bottom_mul_emb2 (M : Matrix (Fin 3) (Fin 3) R) (N : Matrix (Fin 2) (Fin 2) R)
    (h20 : M 2 0 = 0) (h21 : M 2 1 = 0) :
    (M * emb2 N) 2 0 = 0 ∧ (M * emb2 N) 2 1 = 0 := by
  constructor <;> simp [emb2, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]

end Algebra

section Units

variable {p : ℕ} [Fact p.Prime] {K : Type*} [CommRing K] (f : ℚ_[p] →+* K)

lemma lpEmb_v1 (M N : Matrix (Fin 2) (Fin 2) ℤ_[p]) (h1 : M * N = 1) :
    emb2 (M.map (f.comp cq)) * emb2 (N.map (f.comp cq)) = 1 := by
  rw [← emb2_mul, ← Matrix.map_mul, h1, Matrix.map_one (f.comp cq) (map_zero _) (map_one _),
    emb2_one]

lemma lpEmb_v2 (M N : Matrix (Fin 2) (Fin 2) ℤ_[p]) (h2 : N * M = 1) :
    emb2 (N.map (f.comp cq)) * emb2 (M.map (f.comp cq)) = 1 := by
  rw [← emb2_mul, ← Matrix.map_mul, h2, Matrix.map_one (f.comp cq) (map_zero _) (map_one _),
    emb2_one]

/-- `diag(M, 1)` in `GL₃(K)` for integral `M` with integral inverse `N`. -/
def lpEmb (M N : Matrix (Fin 2) (Fin 2) ℤ_[p]) (h1 : M * N = 1) (h2 : N * M = 1) :
    GeneralLinearGroup (Fin 3) K :=
  ⟨emb2 (M.map (f.comp cq)), emb2 (N.map (f.comp cq)), lpEmb_v1 f M N h1, lpEmb_v2 f M N h2⟩

lemma lpEmb_val (M N : Matrix (Fin 2) (Fin 2) ℤ_[p]) (h1 : M * N = 1) (h2 : N * M = 1) :
    (lpEmb f M N h1 h2).val = emb2 (M.map (f.comp cq)) := rfl

/-- The Hermite-class adjustment, algebraic form. -/
theorem lp_class_alg (P κ : GeneralLinearGroup (Fin 3) K) (A M D : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : A = M * D) (hD : D.det = 1) (hP20 : P.val 2 0 = 0) (hP21 : P.val 2 1 = 0)
    (hblk : blk2 P.val = A.map (f.comp cq)) :
    ∃ P' κ' : GeneralLinearGroup (Fin 3) K, P'.val 2 0 = 0 ∧ P'.val 2 1 = 0 ∧
      P'.val * κ'.val = P.val * κ.val ∧ blk2 P'.val = M.map (f.comp cq) ∧
      κ'.val = emb2 (D.map (f.comp cq)) * κ.val := by
  have hDadj : D * D.adjugate = 1 := by rw [Matrix.mul_adjugate, hD, one_smul]
  have hadjD : D.adjugate * D = 1 := by rw [Matrix.adjugate_mul, hD, one_smul]
  refine ⟨P * lpEmb f D.adjugate D hadjD hDadj, lpEmb f D D.adjugate hDadj hadjD * κ,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul, lpEmb_val]
    exact (bottom_mul_emb2 _ _ hP20 hP21).1
  · rw [Units.val_mul, lpEmb_val]
    exact (bottom_mul_emb2 _ _ hP20 hP21).2
  · calc (P * lpEmb f D.adjugate D hadjD hDadj).val *
          (lpEmb f D D.adjugate hDadj hadjD * κ).val
        = P.val * (emb2 (D.adjugate.map (f.comp cq)) * emb2 (D.map (f.comp cq))) * κ.val := by
          simp only [Units.val_mul, lpEmb_val, mul_assoc]
      _ = P.val * κ.val := by rw [lpEmb_v1 f D.adjugate D hadjD, mul_one]
  · rw [Units.val_mul, lpEmb_val, blk2_mul_emb2, hblk, ← Matrix.map_mul, hA, mul_assoc, hDadj,
      mul_one]
  · rw [Units.val_mul, lpEmb_val]

end Units

section Place

/-- The class adjustment of a Hermite-class shell datum is integral at `v`. -/
theorem intGL3_emb (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (M N : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (h1 : M * N = 1) (h2 : N * M = 1) :
    IntGL3 v (lpEmb (psiV v) M N h1 h2).val := by
  have hM : ∀ i j, (M.map ((psiV v).comp cq)) i j ∈ OS v := fun i j => by
    rw [Matrix.map_apply]; exact psiV_mem_OS v (M i j)
  have hN : ∀ i j, (N.map ((psiV v).comp cq)) i j ∈ OS v := fun i j => by
    rw [Matrix.map_apply]; exact psiV_mem_OS v (N i j)
  have hemb : ∀ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, X i j ∈ OS v) →
      ∀ i j, emb2 X i j ∈ OS v := by
    intro X hX i j
    fin_cases i <;> fin_cases j <;> simp [emb2, hX, (OS v).zero_mem, (OS v).one_mem]
  rw [lpEmb_val]
  refine ⟨Matrix.isUnit_det_of_right_inverse (lpEmb_v1 (psiV v) M N h1),
    fun i j => hemb _ hM i j, ?_⟩
  intro i j
  rw [Matrix.inv_eq_right_inv (lpEmb_v1 (psiV v) M N h1)]
  exact hemb _ hN i j

theorem intGL3_mul (v : FinitePlace) {X Y : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)}
    (hX : IntGL3 v X) (hY : IntGL3 v Y) : IntGL3 v (X * Y) := by
  refine ⟨?_, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.det_mul]
    exact hX.1.mul hY.1
  · rw [Matrix.mul_apply]
    exact (OS v).sum_mem (fun k _ => (OS v).mul_mem (hX.2.1 i k) (hY.2.1 k j))
  · rw [Matrix.mul_inv_rev, Matrix.mul_apply]
    exact (OS v).sum_mem (fun k _ => (OS v).mul_mem (hY.2.2 i k) (hX.2.2 k j))

theorem lp_kappa_int (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) (hk : k.det = 1) :
    IntGL3 v (lpKappa (psiV v) k hk).val := by
  rw [lpKappa_val]
  refine ⟨Matrix.isUnit_det_of_right_inverse (lpAdjMulK (psiV v) k hk), fun i j => ?_,
    fun i j => ?_⟩
  · rw [Matrix.map_apply]
    exact psiV_mem_OS v (k.adjugate i j)
  · rw [Matrix.inv_eq_right_inv (lpAdjMulK (psiV v) k hk), Matrix.map_apply]
    exact psiV_mem_OS v (k i j)

/-- Local shell datum with the Hermite-class representative `blk2 P = Mz tc` exactly. -/
theorem local_plane_class (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (r : ℕ) (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (hmax : max ‖z.1‖ ‖z.2‖ = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)
    (tc : ℕ × ℕ × ℕ) (htc : tc ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val r)
    (hz : pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z = hermLat (Rat.HeightOneSpectrum.primesEquiv v).val tc) :
    ∃ P κ : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ),
      P.val 2 0 = 0 ∧ P.val 2 1 = 0 ∧
      LstR (psiV v z.1) (psiV v z.2) = P.val * κ.val ∧ IntGL3 v κ.val ∧
      blk2 P.val = (Mz (q := (Rat.HeightOneSpectrum.primesEquiv v).val) tc).map
        (fun x => psiV v (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) := by
  obtain ⟨k, A, hK⟩ := exists_k0 r hmax
  obtain ⟨hk, hAdet, hbd, hent, h20, h21, -⟩ := hK
  obtain ⟨D, hA, hD⟩ := exists_mul_Mz htc hz hAdet hbd
  obtain ⟨b20, b21⟩ := lpPlane_bottom (psiV v) z.1 z.2 k hk h20 h21
  obtain ⟨P', κ', c20, c21, ceq, cblk, ckval⟩ :=
    lp_class_alg (psiV v) (lpPlane (psiV v) z.1 z.2 k hk) (lpKappa (psiV v) k hk) A
      (Mz (q := (Rat.HeightOneSpectrum.primesEquiv v).val) tc) D hA hD b20 b21
      (lpPlane_blk2 (psiV v) z.1 z.2 k hk A hent)
  have hDadj : D * D.adjugate = 1 := by rw [Matrix.mul_adjugate, hD, one_smul]
  have hadjD : D.adjugate * D = 1 := by rw [Matrix.adjugate_mul, hD, one_smul]
  refine ⟨P', κ', c20, c21, ?_, ?_, cblk⟩
  · rw [ceq]
    exact (lpPlane_mul_kappa (psiV v) z.1 z.2 k hk).symm
  · rw [ckval]
    exact intGL3_mul v (intGL3_emb v D D.adjugate hDadj hadjD) (lp_kappa_int v k hk)

end Place

end TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlaneClass
