module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.RightTranslation
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Adelic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.RecursionLattice
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.Transform

@[expose] public section


/-!
# Finite coordinate one in `v_h` form, and the identity everywhere

Formalized by Claude Haiku 5.5.

Proved here:
* `vhValue_iotaGL_eq`: the per-term identity `v_h(g_∞, ι_v(A)) = F_h(A⁻¹ g_∞)` for an integer matrix
  `A` with `det A = p^r`, `p` the prime of the place `v`. The reduction is `γ = A⁻¹ ∈ GL₂⁺(ℚ)`.
* `H1_vh`: the sum over `hnfData (p^r)` of `v_h(g_∞, ι_p(A_t))` equals `p^{r(1-k/2)} a_h(p^r) v_h(g_∞, 1)`,
  from S5's `eq_lattice_hecke_finite_one` and `vhValue_one`.
* `hecke_right_everywhere_hnf`: the identity at every `g_f`, with `L = latSum` over `hnfData` and
  `R = c · v_h`, from `RightTranslation.hecke_right_everywhere`.

Hypothesis:
* `hPerm` of `hecke_right_everywhere_hnf`: for every `u ∈ binaryIntegralFinite` there is a permutation
  `σ` of `hnfData (p^r)` with `ι(A_t) u = ι(A_{σ t}) w` for integral `w`. This is the lattice-permutation
  property of the index-`p^r` sublattices; its proof (rank-2 bases via `Submodule.basisOfPid`) is the
  remaining item (1) of the H4 directive.
-/

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof (evM qv evM_qFA)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh lowMat Gl Gl_eq lowMat_det_ne_zero)
open TernaryPeriodPolynomials.Argument.LatticeCounts (hnfData mem_hnfData)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (HasPrimeHeckeRelations)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion (eq_lattice_hecke_finite_one)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeTransform (latSum vhRight latSum_diag latSum_mul_integral_of_perm vhRight_mul_integral vhRight_diag)

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue

/-- `det` of an integer matrix mapped into a field, as the cast of the integer determinant. -/
theorem det_map_intCast (K : Type*) [Field K] (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (A.map (Int.cast : ℤ → K)).det = ((A.det : ℤ) : K) :=
  (RingHom.map_det (Int.castRingHom K) A).symm

/-- Inverse commutes with a ring hom on matrices with nonzero determinant. -/
theorem inv_map_eq {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) :
    (M.map f)⁻¹ = M⁻¹.map f := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hM),
    Matrix.map_one _ (map_zero _) (map_one _)]

/-- Entries of the rational inverse of an integer matrix of determinant `P^r` have denominators
dividing a power of `P`. -/
theorem inv_entry_denom (A : Matrix (Fin 2) (Fin 2) ℤ) (P r : ℕ) (hP : (P : ℚ) ≠ 0)
    (hA : A.det = (P : ℤ) ^ r) :
    ∀ i j, ∃ (n : ℤ) (k : ℕ), ((A.map (Int.cast : ℤ → ℚ))⁻¹) i j * (P : ℚ) ^ k = n := by
  have hdet : (A.map (Int.cast : ℤ → ℚ)).det = (P : ℚ) ^ r := by
    rw [det_map_intCast, hA]
    norm_cast
  have hPr : (P : ℚ) ^ r ≠ 0 := pow_ne_zero _ hP
  intro i j
  rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet, Matrix.smul_apply, Matrix.adjugate_fin_two,
    smul_eq_mul]
  fin_cases i <;> fin_cases j
  · exact ⟨A 1 1, r, by simp [Matrix.map_apply]; field_simp⟩
  · exact ⟨-A 0 1, r, by simp [Matrix.map_apply]; field_simp⟩
  · exact ⟨-A 1 0, r, by simp [Matrix.map_apply]; field_simp⟩
  · exact ⟨A 0 0, r, by simp [Matrix.map_apply]; field_simp⟩

/-- Membership in `GL₂(ℤ̂)` from local integrality at every finite place. -/
theorem mem_binaryIntegralFinite_of_intGL (g : BinaryFiniteGL)
    (hX : ∀ v : FinitePlace, IntGL v (evM v g.val)) : g ∈ binaryIntegralFinite := by
  let N : Matrix (Fin 2) (Fin 2) IntegralAdeles :=
    fun i j v => ⟨(evM v g.val) i j, (hX v).2.1 i j⟩
  let Ni : Matrix (Fin 2) (Fin 2) IntegralAdeles :=
    fun i j v => ⟨(evM v g.val)⁻¹ i j, (hX v).2.2 i j⟩
  have hevP : ∀ v, evM v (N.map integralEmbedding) = evM v g.val :=
    fun v => Matrix.ext fun _ _ => rfl
  have hevQ : ∀ v, evM v (Ni.map integralEmbedding) = (evM v g.val)⁻¹ :=
    fun v => Matrix.ext fun _ _ => rfl
  have hPQv : ∀ v, evM v ((N.map integralEmbedding) * (Ni.map integralEmbedding)) = evM v 1 := by
    intro v
    have hmul : evM v ((N.map integralEmbedding) * (Ni.map integralEmbedding)) =
        evM v (N.map integralEmbedding) * evM v (Ni.map integralEmbedding) := by
      unfold evM
      exact Matrix.map_mul
    rw [hmul, hevP v, hevQ v, Matrix.mul_nonsing_inv _ (hX v).1]
    unfold evM
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hQPv : ∀ v, evM v ((Ni.map integralEmbedding) * (N.map integralEmbedding)) = evM v 1 := by
    intro v
    have hmul : evM v ((Ni.map integralEmbedding) * (N.map integralEmbedding)) =
        evM v (Ni.map integralEmbedding) * evM v (N.map integralEmbedding) := by
      unfold evM
      exact Matrix.map_mul
    rw [hmul, hevP v, hevQ v, Matrix.nonsing_inv_mul _ (hX v).1]
    unfold evM
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hPQ : (N.map integralEmbedding) * (Ni.map integralEmbedding) = 1 :=
    Matrix.ext fun i j => RestrictedProduct.ext _ _ fun v => congrFun (congrFun (hPQv v) i) j
  have hQP : (Ni.map integralEmbedding) * (N.map integralEmbedding) = 1 :=
    Matrix.ext fun i j => RestrictedProduct.ext _ _ fun v => congrFun (congrFun (hQPv v) i) j
  have hNNi : N * Ni = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (N * Ni).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hNiN : Ni * N = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (Ni * N).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  let gI : GeneralLinearGroup (Fin 2) IntegralAdeles := ⟨N, Ni, hNNi, hNiN⟩
  rw [binaryIntegralFinite, MonoidHom.mem_range]
  exact ⟨gI, Units.ext (Matrix.ext fun i j => RestrictedProduct.ext _ _ fun v => rfl)⟩

/-- Per-term identity: for an integer matrix `A` with `det A = p^r` at the place
`v`, right translation of `v_h` by `ι_v(A)` at finite coordinate `ι_v(A)` is `F_h(A⁻¹ g_∞)`.
The reduction is `γ = A⁻¹ ∈ GL₂⁺(ℚ)`: at `v`, `γ A = 1`; at `w ≠ v`, `A⁻¹ ∈ GL₂(O_w)`.
`B` is any lift of `A` to `GL₂(K_v)` and `Ginv` any lift of `A⁻¹` to `GL₂(ℝ)`. -/
theorem vhValue_iotaGL_eq (k : ℤ) (h : CuspForm levelOne k) (v : FinitePlace) (r : ℕ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ^ r)
    (B : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : B.val = A.map (Int.cast : ℤ → v.adicCompletion ℚ))
    (Ginv : BinaryRealGL) (hG : Ginv.val = (A.map (Int.cast : ℤ → ℝ))⁻¹)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val) :
    vhValue k h gInf (ιGL v B) = Fh k ⇑h (Ginv * gInf) := by
  have hP : ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).2.ne_zero
  have hPpos : (0 : ℚ) < ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) := by
    exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).2.pos
  have hdetQ : (A.map (Int.cast : ℤ → ℚ)).det =
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ r := by
    rw [det_map_intCast, hA]
    norm_cast
  have hQne : (A.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [hdetQ]; exact pow_ne_zero _ hP
  have hQinvne : ((A.map (Int.cast : ℤ → ℚ))⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hQne
  let γ : BinaryRationalGL := GeneralLinearGroup.mkOfDetNeZero (A.map (Int.cast : ℤ → ℚ))⁻¹ hQinvne
  have hγval : γ.val = (A.map (Int.cast : ℤ → ℚ))⁻¹ := rfl
  have hγdet : 0 < (Matrix.GeneralLinearGroup.det γ).val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hγval, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
      hdetQ]
    exact inv_pos.2 (pow_pos hPpos _)
  have hint : binaryRationalFinite γ * ιGL v B ∈ binaryIntegralFinite := by
    apply mem_binaryIntegralFinite_of_intGL
    intro w
    show IntGL w (((γ.val.map (algebraMap ℚ FiniteAdeles)) * (ιGL v B).val).map (finiteEvaluation w))
    rw [evM_qFA]
    rcases eq_or_ne w v with rfl | hwv
    · have hAK : A.map (Int.cast : ℤ → w.adicCompletion ℚ) = qv w (A.map (Int.cast : ℤ → ℚ)) := by
        ext i j
        simp [qv, Matrix.map_apply]
      have hkey : qv w ((A.map (Int.cast : ℤ → ℚ))⁻¹) * qv w (A.map (Int.cast : ℤ → ℚ)) = 1 := by
        unfold qv
        rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQne),
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [ιGL_val, evM_ιMat_self, hB, hγval, hAK, hkey]
      exact intGL_one w
    · rw [ιGL_val, evM_ιMat_ne v w hwv, mul_one, hγval]
      have hdetinv : ∃ E : ℤ, ((A.map (Int.cast : ℤ → ℚ))⁻¹).det =
          ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ E :=
        ⟨-(r : ℤ), by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdetQ, _root_.zpow_neg, zpow_natCast]⟩
      exact intGL_of_denom v w hwv _ (inv_entry_denom A _ r hP hA) hdetinv
  have hGeq : binaryRationalReal γ = Ginv := by
    apply Units.ext
    rw [hG]
    show (γ.val).map (Rat.castHom ℝ) = _
    have hAR : A.map (Int.cast : ℤ → ℝ) = (A.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℝ) := by
      ext i j
      simp [Matrix.map_apply]
    rw [hγval, hAR]
    exact (inv_map_eq (Rat.castHom ℝ) _ hQne).symm
  rw [vhValue_eq_of_reduction k h gInf hgInf (ιGL v B) ⟨γ, hγdet, hint⟩, hGeq]

/-- The lower-triangular Hermite matrix `A_t` as an integer matrix. -/
def intMat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(t.1 : ℤ), 0; (t.2.1 : ℤ), (t.2.2 : ℤ)]

theorem intMat_det (t : ℕ × ℕ × ℕ) : (intMat t).det = (t.1 : ℤ) * (t.2.2 : ℤ) := by
  simp [intMat, Matrix.det_fin_two]

/-- Finite coordinate one, in `v_h` form: the sum over the Hermite triples of
`v_h(g_∞, ι_p(A_t))` equals `p^{r(1-k/2)} a_h(p^r) v_h(g_∞, 1)`. The lifts `B t` of `A_t` to
`GL₂(K_v)` are arbitrary subject to `hB`. Derived from S5's `eq_lattice_hecke_finite_one` via the
per-term identity `vhValue_iotaGL_eq` and `vhValue_one`. -/
theorem H1_vh (k : ℤ) (h : CuspForm levelOne k) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (v : FinitePlace) (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (p.val ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val) :
    ∑ t ∈ hnfData (p.val ^ r), vhValue k h gInf (ιGL v (B t)) =
      ((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
        (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r) * vhValue k h gInf 1 := by
  have hpos : 0 < p.val ^ r := pow_pos p.property.pos r
  have HV : ∀ t ∈ hnfData (p.val ^ r),
      vhValue k h gInf (ιGL v (B t)) = Fh k ⇑h (Gl t gInf) := by
    intro t ht
    have ht' := (mem_hnfData hpos t).1 ht
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
    refine vhValue_iotaGL_eq k h v r (intMat t) hdet (B t) (hB t ht)
      ((GeneralLinearGroup.mkOfDetNeZero (lowMat t) (lowMat_det_ne_zero ⟨h1, hd⟩))⁻¹) ?_ gInf hgInf
    rw [Matrix.coe_units_inv]
    show (lowMat t)⁻¹ = _
    rw [hlow]
  rw [Finset.sum_congr rfl HV, eq_lattice_hecke_finite_one k h eigenvalues relations normalized p r gInf hgInf,
    vhValue_one k h gInf hgInf]

/-- The Hermite-lift family indexed by the finite set `hnfData m` (a `Fintype` subtype). -/
def hnfLift (v : FinitePlace) (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (m : ℕ) : {t // t ∈ hnfData m} → BinaryFiniteGL :=
  fun t => ιGL v (B t.1)

/-- The identity of the paper in lattice-sum form at every `g_f`: `L = latSum` over `hnfData`,
`R = c · v_h` with `c = p^{r(1-k/2)} a_h(p^r)`. The finite coordinate-one identity is `H1_vh`;
the integral-invariance of the sum is supplied by the lattice-permutation input `hPerm`. -/
theorem hecke_right_everywhere_hnf (k : ℤ) (h : CuspForm levelOne k) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (v : FinitePlace) (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ t ∈ hnfData (p.val ^ r), (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (hPerm : ∀ u ∈ binaryIntegralFinite, ∃ σ : {t // t ∈ hnfData (p.val ^ r)} ≃ {t // t ∈ hnfData (p.val ^ r)},
      IsLatticePerm u (hnfLift v B (p.val ^ r)) σ) :
    ∀ gInf : BinaryRealGL, 0 < (Matrix.GeneralLinearGroup.det gInf).val →
      ∀ gf : BinaryFiniteGL,
        latSum k h (hnfLift v B (p.val ^ r)) gInf gf =
          vhRight k h (((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
            (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r)) gInf gf := by
  intro gInf hgInf
  refine hecke_right_everywhere
    (fun g f => latSum k h (hnfLift v B (p.val ^ r)) g f)
    (fun g f => vhRight k h (((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
      (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r)) g f)
    ?_ ?_ ?_ ?_ ?_ gInf hgInf
  · intro g hg f u hu
    obtain ⟨σ, hP⟩ := hPerm u hu
    exact latSum_mul_integral_of_perm k h (hnfLift v B (p.val ^ r)) g hg f u σ hP
  · intro g hg f u hu
    exact vhRight_mul_integral k h _ g hg f u hu
  · intro g hg δ f hδ
    exact latSum_diag k h (hnfLift v B (p.val ^ r)) g hg δ hδ f
  · intro g hg δ f hδ
    exact vhRight_diag k h _ g hg δ hδ f
  · intro g hg
    simp only [latSum, vhRight, hnfLift, one_mul]
    exact (Finset.sum_coe_sort (hnfData (p.val ^ r))
      (fun t => vhValue k h g (ιGL v (B t)))).trans
      (H1_vh k h eigenvalues relations normalized p r v hv B hB g hg)

end TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue
