module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermAdelic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicZp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.RecursionLattice

@[expose] public section


/-!
# `eq:cyclic-hecke` at every finite `g_f`

Formalized by Claude Haiku 5.5.

* `hPerm_core_cyc`: the lattice permutation of `LatticePermAdelic.hPerm_core`, together with the
  fact that it preserves cyclicity (`LatticeCyclicZp.cyclic_preserved_of_perm`).
* `cyc_isLatticePerm`: restriction of that permutation to the cyclic subtype.
* `H1_cyc`: the finite coordinate-one identity over the cyclic triples, from S5's
  `HeckeRecursion.eq_cyclic_hecke_finite_one`, by the per-term identity `vhValue_iotaGL_eq`.
* `eq_cyclic_hecke`: the identity at every `g_f`, with no hypothesis
  beyond the normalized eigenform data and the Hermite lifts `hB`.
-/

open Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalIwasawa (PInt)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicZp
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh lowMat Gl Gl_eq lowMat_det_ne_zero)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeTransform
  (latSum vhRight latSum_diag latSum_mul_integral_of_perm vhRight_mul_integral vhRight_diag)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion (eq_cyclic_hecke_finite_one)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (HasPrimeHeckeRelations)
open TernaryPeriodPolynomials.Argument.LatticeCounts (hnfData mem_hnfData cyclicHNF)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicAdelic

/-- The cyclic Hermite lifts `t ↦ ι_v(B t)`, indexed by the subtype of `cyclicHNF q r`. -/
def cycLift (v : FinitePlace) (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (q r : ℕ) : {t // t ∈ cyclicHNF q r} → BinaryFiniteGL :=
  fun t => ιGL v (B t.1)

/-- The lattice permutation at `v`, with the cyclic-invariance of the permutation. This is
`LatticePermAdelic.hPerm_core` with the extra conjunct; the proof is the same. -/
theorem hPerm_core_cyc (v : FinitePlace) (q r : ℕ) [Fact q.Prime]
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = q)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (q ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (u : BinaryFiniteGL) (hu : u ∈ binaryIntegralFinite) :
    ∃ σ : {t // t ∈ hnfData (q ^ r)} ≃ {t // t ∈ hnfData (q ^ r)},
      IsLatticePerm u (hnfLift v B (q ^ r)) σ ∧
        ∀ t : {t // t ∈ hnfData (q ^ r)}, t.1 ∈ cyclicHNF q r ↔ (σ t).1 ∈ cyclicHNF q r := by
  subst hv
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
  have hcyc := cyclic_preserved_of_perm (q := (Rat.HeightOneSpectrum.primesEquiv v : ℕ))
    (Rat.HeightOneSpectrum.primesEquiv v).2 Y hYdet σ hσ
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
  refine ⟨σ, fun t => ?_, hcyc⟩
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

/-- The cyclic subfamily is permuted, up to `GL₂(ℤ̂)`, by the restriction of the lattice
permutation. -/
theorem cyc_isLatticePerm (v : FinitePlace) (q r : ℕ) [Fact q.Prime]
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = q)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (q ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (u : BinaryFiniteGL) (hu : u ∈ binaryIntegralFinite) :
    ∃ σ : {t // t ∈ cyclicHNF q r} ≃ {t // t ∈ cyclicHNF q r},
      IsLatticePerm u (cycLift v B q r) σ := by
  obtain ⟨σ, hP, hcyc⟩ := hPerm_core_cyc v q r hv B hB u hu
  let e0 : {x : {t // t ∈ hnfData (q ^ r)} // x.1 ∈ cyclicHNF q r} ≃ {t // t ∈ cyclicHNF q r} :=
    Equiv.subtypeSubtypeEquivSubtype fun {x} hx => (Finset.mem_filter.1 hx).1
  let e2 : {x : {t // t ∈ hnfData (q ^ r)} // x.1 ∈ cyclicHNF q r} ≃
      {x : {t // t ∈ hnfData (q ^ r)} // x.1 ∈ cyclicHNF q r} :=
    Equiv.subtypeEquiv σ (fun x => hcyc x)
  refine ⟨e0.symm.trans (e2.trans e0), fun c => ?_⟩
  obtain ⟨w, hw, hEq⟩ := hP ⟨c.1, (Finset.mem_filter.1 c.2).1⟩
  exact ⟨w, hw, hEq⟩

/-- Finite coordinate one over the cyclic triples, in `v_h` form: the sum over the
cyclic Hermite triples of `v_h(g_∞, ι_p(A_t))` is `p^{r(1-k/2)} {a_h(p^r) - p^{k-2} a_h(p^{r-2})} v_h(g_∞, 1)`.
Derived from `eq_cyclic_hecke_finite_one` by the per-term identity `vhValue_iotaGL_eq`. -/
theorem H1_cyc (k : ℤ) (h : CuspForm levelOne k) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (v : FinitePlace) (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (p.val ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val) :
    ∑ t ∈ cyclicHNF p.val r, vhValue k h gInf (ιGL v (B t)) =
      ((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
        ((UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r) -
          (p.val : ℂ) ^ (k - 2) *
            (if 2 ≤ r then (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ (r - 2)) else 0)) *
        vhValue k h gInf 1 := by
  have hpos : 0 < p.val ^ r := pow_pos p.property.pos r
  have HV : ∀ t ∈ cyclicHNF p.val r, vhValue k h gInf (ιGL v (B t)) = Fh k ⇑h (Gl t gInf) := by
    intro t ht
    have hmem : t ∈ hnfData (p.val ^ r) := (Finset.mem_filter.1 ht).1
    have ht' := (mem_hnfData hpos t).1 hmem
    obtain ⟨h1, h2, _⟩ := ht'
    have hd : 0 < t.2.2 := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at h2
      exact hpos.ne' h2.symm
    have hdet : (intMat t).det = ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ^ r := by
      rw [intMat_det, hv]
      exact_mod_cast h2
    have hlow : lowMat t = (intMat t).map (Int.cast : ℤ → ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lowMat, intMat]
    rw [Gl_eq ⟨h1, hd⟩ gInf]
    refine vhValue_iotaGL_eq k h v r (intMat t) hdet (B t) (hB t hmem)
      ((GeneralLinearGroup.mkOfDetNeZero (lowMat t) (lowMat_det_ne_zero ⟨h1, hd⟩))⁻¹) ?_ gInf hgInf
    rw [Matrix.coe_units_inv]
    show (lowMat t)⁻¹ = _
    rw [hlow]
  rw [Finset.sum_congr rfl HV,
    eq_cyclic_hecke_finite_one k h eigenvalues relations normalized p r gInf hgInf,
    vhValue_one k h gInf hgInf]

/-- **`eq:cyclic-hecke` at every `g_f`.** For a normalized level-one eigenform `h`, the sum over the
cyclic Hermite lifts of `v_h(g_∞, g_f · x_Λ)` equals `p^{r(1-k/2)} {a_h(p^r) - p^{k-2} a_h(p^{r-2})} v_h(g_∞, g_f)`.
No lattice-permutation hypothesis remains. -/
theorem eq_cyclic_hecke (k : ℤ) (h : CuspForm levelOne k)
    (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (v : FinitePlace) (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (p.val ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ)) :
    ∀ gInf : BinaryRealGL, 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ gf : BinaryFiniteGL,
        latSum k h (cycLift v B p.val r) gInf gf =
          vhRight k h (((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
            ((UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r) -
              (p.val : ℂ) ^ (k - 2) *
                (if 2 ≤ r then (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ (r - 2)) else 0)))
            gInf gf := by
  have : Fact p.val.Prime := ⟨p.property⟩
  intro gInf hgInf
  refine hecke_right_everywhere
    (fun g f => latSum k h (cycLift v B p.val r) g f)
    (fun g f => vhRight k h (((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
      ((UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r) -
        (p.val : ℂ) ^ (k - 2) *
          (if 2 ≤ r then (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ (r - 2)) else 0))) g f)
    ?_ ?_ ?_ ?_ ?_ gInf hgInf
  · intro g hg f u hu
    obtain ⟨σ, hP⟩ := cyc_isLatticePerm v p.val r hv B hB u hu
    exact latSum_mul_integral_of_perm k h (cycLift v B p.val r) g hg f u σ hP
  · intro g hg f u hu
    exact vhRight_mul_integral k h _ g hg f u hu
  · intro g hg δ f hδ
    exact latSum_diag k h (cycLift v B p.val r) g hg δ hδ f
  · intro g hg δ f hδ
    exact vhRight_diag k h _ g hg δ hδ f
  · intro g hg
    simp only [latSum, vhRight, cycLift, one_mul]
    exact (Finset.sum_coe_sort (cyclicHNF p.val r) (fun t => vhValue k h g (ιGL v (B t)))).trans
      (H1_cyc k h eigenvalues relations normalized p r v hv B hB g hg)

end TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicAdelic

end
