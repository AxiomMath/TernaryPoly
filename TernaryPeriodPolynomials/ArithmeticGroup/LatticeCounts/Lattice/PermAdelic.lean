module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.IotaValue
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof

@[expose] public section


/-!
# Lattice permutation at every finite place: `hPerm` discharged

Formalized by Claude Haiku 5.5.

For `u ∈ binaryIntegralFinite` and the Hermite lifts `ι_v(B t)` of `A_t` at the prime `p_v`:

* `hPerm_core`: there is a permutation `σ` of `hnfData (p^r)` and `w_t ∈ binaryIntegralFinite`
  with `u · ι(B_t) = ι(B_{σ t}) · w_t`. The `ℤ_p`-level permutation is `LatticePermZp.exists_perm_zp`
  applied to the `ℤ_p`-lift of `u_v`; the other places are untouched because `u` is integral there.
* `hecke_right_everywhere_unconditional`: `hecke_right_everywhere_hnf` with `hPerm` discharged,
  so the lattice-sum identity holds at every `g_f` with no lattice-permutation hypothesis.
-/

open Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalIwasawa (PInt)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeTransform (latSum vhRight)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (HasPrimeHeckeRelations)
open TernaryPeriodPolynomials.Argument.LatticeCounts (hnfData mem_hnfData)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermAdelic

/-- `GL₂(ℤ̂)` elements are integral at every finite place. -/
theorem intGL_of_mem_bIF (u : BinaryFiniteGL) (hu : u ∈ binaryIntegralFinite) (w : FinitePlace) :
    IntGL w (evM w u.val) := by
  rw [binaryIntegralFinite, MonoidHom.mem_range] at hu
  obtain ⟨g, rfl⟩ := hu
  show IntGL w (evM w (g.val.map integralEmbedding))
  refine intGL_evM_of_good (g.val.map integralEmbedding)
    ((g⁻¹ : GeneralLinearGroup (Fin 2) IntegralAdeles).val.map integralEmbedding) ?_ w ?_
  · rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · intro i j
    exact ⟨(g.val i j w).2, ((g⁻¹ : GeneralLinearGroup (Fin 2) IntegralAdeles).val i j w).2⟩

theorem evM_ιGL_self (v : FinitePlace) (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    evM v (ιGL v A).val = A.val := by
  rw [ιGL_val, evM_ιMat_self]

theorem evM_ιGL_ne (v w : FinitePlace) (hw : w ≠ v)
    (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    evM w (ιGL v A).val = 1 := by
  rw [ιGL_val, evM_ιMat_ne v w hw]

/-- The `ℚ_p`-reduction of the Hermite matrix `Mz t` is the image of `A_t` in `ℚ_p`. -/
theorem Mz_map_cq {q : ℕ} [Fact q.Prime] (t : ℕ × ℕ × ℕ) :
    (Mz (q := q) t).map cq = (intMat t).map (Int.cast : ℤ → ℚ_[q]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mz, intMat, cq]

/-- The `p_v`-adic side of a Hermite lift is `Mz t`. -/
theorem pe_B_eq (v : FinitePlace) (B : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (t : ℕ × ℕ × ℕ) (hB : B.val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ)) :
    B.val.map (pe v) = (Mz (q := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) t).map cq := by
  rw [Mz_map_cq, hB, Matrix.map_map]
  congr 1
  funext n
  exact map_intCast (pe v) n

/-- The `ℚ_p`-image of a unit of `GL₂(ℤ_p)` is `PInt`. -/
theorem pInt_of_units {q : ℕ} [Fact q.Prime] (C : (Matrix (Fin 2) (Fin 2) ℤ_[q])ˣ) :
    PInt (C.val.map cq) := by
  have hCdet : IsUnit C.val.det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit C)
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.map_apply]
    exact (C.val i j).2
  · rw [show (C.val.map cq).det = cq C.val.det from (RingHom.map_det cq _).symm]
    have h1 := PadicInt.isUnit_iff.1 hCdet
    rw [PadicInt.norm_def] at h1
    exact h1

/-- If `Bs · X` and `Bs · C` agree `p`-adically with `Bs` a unit and `C` in `GL₂(ℤ_p)`, then `X`
is integral at `v`. -/
theorem intGL_of_pe_eq (v : FinitePlace)
    (Bs X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hBs : IsUnit Bs.det)
    (Cq : Matrix (Fin 2) (Fin 2) ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])
    (hC : PInt Cq)
    (h : Bs.map (pe v) * X.map (pe v) = Bs.map (pe v) * Cq) : IntGL v X := by
  rw [intGL_iff_pInt]
  have hdetσ : IsUnit (Bs.map (pe v)).det := by
    rw [map_det_pe]
    exact hBs.map (pe v)
  have hunit : IsUnit (Bs.map (pe v)) := (Matrix.isUnit_iff_isUnit_det _).2 hdetσ
  have hX : X.map (pe v) = Cq := hunit.mul_left_cancel h
  rw [hX]
  exact hC

/-- **Lattice permutation at the place `v`.** For `u ∈ binaryIntegralFinite` there is a
permutation `σ` of the Hermite triples with `u · ι(B_t) = ι(B_{σ t}) · w_t`, `w_t ∈ GL₂(ℤ̂)`. -/
theorem hPerm_core (v : FinitePlace) (r : ℕ)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ r),
      (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (u : BinaryFiniteGL) (hu : u ∈ binaryIntegralFinite) :
    ∃ σ : {t // t ∈ hnfData ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ r)} ≃
        {t // t ∈ hnfData ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ r)},
      IsLatticePerm u (hnfLift v B ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ r)) σ := by
  have hn : 0 < (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ r :=
    pow_pos (Rat.HeightOneSpectrum.primesEquiv v).2.pos r
  have hPU : PInt ((evM v u.val).map (pe v)) :=
    (intGL_iff_pInt v _).1 (intGL_of_mem_bIF u hu v)
  obtain ⟨Y, hYq⟩ : ∃ Y : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)],
      Y.map cq = (evM v u.val).map (pe v) :=
    ⟨fun i j => ⟨(evM v u.val).map (pe v) i j, hPU.1 i j⟩, by ext i j; rfl⟩
  have hYdet : IsUnit Y.det := by
    have h1 : cq Y.det = ((evM v u.val).map (pe v)).det := by
      rw [← hYq]
      exact RingHom.map_det cq Y
    rw [PadicInt.isUnit_iff, PadicInt.norm_def]
    show ‖cq Y.det‖ = 1
    rw [h1]
    exact hPU.2
  obtain ⟨σ, hσ⟩ := exists_perm_zp (q := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) r hn Y hYdet
  choose C hC using hσ
  have hkey : ∀ t : {t // t ∈ hnfData ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ r)},
      (evM v u.val).map (pe v) * (B t.1).val.map (pe v) =
        (B (σ t).1).val.map (pe v) * (C t).val.map cq := by
    intro t
    have h1 := congrArg (fun M => M.map cq) (hC t)
    simp only [Matrix.map_mul] at h1
    rw [hYq] at h1
    rw [pe_B_eq v (B t.1) t.1 (hB t.1 t.2),
      pe_B_eq v (B (σ t).1) (σ t).1 (hB (σ t).1 (σ t).2)]
    exact h1
  refine ⟨σ, fun t => ?_⟩
  obtain ⟨W, hWdef⟩ : ∃ W : BinaryFiniteGL,
      W = (ιGL v (B (σ t).1))⁻¹ * (u * ιGL v (B t.1)) := ⟨_, rfl⟩
  refine ⟨W, ?_, ?_⟩
  · apply mem_binaryIntegralFinite_of_intGL
    intro w'
    have hmat : (ιGL v (B (σ t).1)).val * W.val = u.val * (ιGL v (B t.1)).val := by
      rw [hWdef, ← Units.val_mul, mul_inv_cancel_left, Units.val_mul]
    have hE : evM w' (ιGL v (B (σ t).1)).val * evM w' W.val =
        evM w' u.val * evM w' (ιGL v (B t.1)).val := by
      unfold evM
      rw [← Matrix.map_mul, ← Matrix.map_mul, hmat]
    by_cases hw : w' = v
    · rw [hw] at hE ⊢
      rw [evM_ιGL_self, evM_ιGL_self] at hE
      have hp := congrArg (fun M => M.map (pe v)) hE
      simp only [Matrix.map_mul] at hp
      have hpp := hp.trans (hkey t)
      have hCq : PInt ((C t).val.map cq) := pInt_of_units (C t)
      exact intGL_of_pe_eq v _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (B (σ t).1)))
        ((C t).val.map cq) hCq hpp
    · rw [evM_ιGL_ne v w' hw, evM_ιGL_ne v w' hw, one_mul, mul_one] at hE
      rw [hE]
      exact intGL_of_mem_bIF u hu w'
  · rw [hWdef]
    exact (mul_inv_cancel_left _ _).symm

/-- `hPerm_core` with the Hermite index set identified by an equation `m = p_v^r`. -/
theorem hPerm_of_eq (v : FinitePlace) (m r : ℕ)
    (hm : m = (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ r)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData m, (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ)) :
    ∀ u ∈ binaryIntegralFinite, ∃ σ : {t // t ∈ hnfData m} ≃ {t // t ∈ hnfData m},
      IsLatticePerm u (hnfLift v B m) σ := by
  subst hm
  exact fun u hu => hPerm_core v r B hB u hu

/-- **The identity at every `g_f`, with `hPerm` discharged.** -/
theorem hecke_right_everywhere_unconditional (k : ℤ) (h : CuspForm levelOne k)
    (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (v : FinitePlace) (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (p.val ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ)) :
    ∀ gInf : BinaryRealGL, 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ gf : BinaryFiniteGL,
        latSum k h (hnfLift v B (p.val ^ r)) gInf gf =
          vhRight k h (((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
            (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r)) gInf gf :=
  hecke_right_everywhere_hnf k h eigenvalues relations normalized p r v hv B hB
    (hPerm_of_eq v (p.val ^ r) r (by rw [hv]) B hB)

end TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermAdelic

end
