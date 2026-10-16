module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Basic
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ArithmeticModularity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralRationals
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.RowLevel
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.IntegralModularLevel

@[expose] public section


/-!
# Adelic decompositions `GL₂(𝔸) = GL₂(ℚ) · GL₂(ℝ)⁺ · K'`

Strong approximation in the form `exists_isDecomp`, the uniqueness statement `isDecomp_eq` (two
decompositions differ by an element of `Γ₁(3)`), and the Iwasawa decomposition
`GL₂(ℚ) = B(ℚ) · SL₂(ℤ)` with the commutation of the unipotent with the Borel part.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

/-! ### Entries and projections -/

theorem mapGL_entry (R : Type*) [CommRing R] (δ : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (SpecialLinearGroup.mapGL R δ).val i j = ((δ.val i j : ℤ) : R) :=
  binaryIntegral_mapGL_entry R δ i j

theorem redGL_val (m : IntegralBinaryGL) (i j : Fin 2) :
    (redGL m).val i j = integralReduction (m.val i j) := rfl

theorem intGL_val (m : IntegralBinaryGL) (i j : Fin 2) :
    (intGL m).val i j = integralEmbedding (m.val i j) := rfl

theorem redGL_mapGL (τ : SpecialLinearGroup (Fin 2) ℤ) :
    redGL (SpecialLinearGroup.mapGL IntegralAdeles τ) = SpecialLinearGroup.mapGL (ZMod 3) τ :=
  binaryIntegral_mapGL_map integralReduction τ

theorem fst_ratGL (δ : BinaryRationalGL) :
    GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (ratGL δ) = realOfRat δ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem snd_ratGL (δ : BinaryRationalGL) :
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (ratGL δ) = finOfRat δ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem fst_infGL (r : BinaryRealGL) :
    GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (infGL r) = r :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem snd_infGL (r : BinaryRealGL) :
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (infGL r) = 1 :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem fst_finGL (k : BinaryFiniteGL) :
    GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (finGL k) = 1 :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem snd_finGL (k : BinaryFiniteGL) :
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (finGL k) = k :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem vecMul_row {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (![0, 1] : Fin 2 → R) ᵥ* M = M 1 := by
  funext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem det_mapGL_real (σ : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ σ) = 1 := by
  apply Units.ext
  have h := σ.det_coe
  rw [Matrix.det_fin_two] at h
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, mapGL_entry, mapGL_entry,
    mapGL_entry, mapGL_entry, Units.val_one]
  exact_mod_cast h

/-! ### Strong approximation -/

theorem exists_row_lift (B : GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ τ : SpecialLinearGroup (Fin 2) ℤ,
      ![0, 1] ᵥ* (SpecialLinearGroup.mapGL (ZMod 3) τ).val = ![0, 1] ᵥ* (B⁻¹).val := by
  have hw : (![0, 1] ᵥ* (B⁻¹).val) ≠ 0 := by
    intro h
    have h2 : (![0, 1] ᵥ* (B⁻¹).val) ᵥ* B.val = ![0, 1] := by
      rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
    rw [h, Matrix.zero_vecMul] at h2
    have h3 := congrFun h2 1
    simp at h3
  obtain ⟨i, hi⟩ := binaryIntegralRowRepresentatives_cover _ hw
  exact ⟨binaryIntegralRowRepresentatives i, (vecMul_row _).trans hi⟩

theorem exists_isDecomp (g : BinaryAdelicGL) : ∃ γ r k, IsDecomp g γ r k := by
  obtain ⟨γ0, m, r, hr, hg⟩ :=
    BinaryAdelicReduction.exists_rational_integral_positive g
  obtain ⟨τ, hτ⟩ := exists_row_lift (redGL m)
  obtain ⟨σ, hσ⟩ : ∃ σ : SpecialLinearGroup (Fin 2) ℤ, σ = τ⁻¹ := ⟨_, rfl⟩
  obtain ⟨kI, hkI⟩ : ∃ kI : IntegralBinaryGL,
      kI = SpecialLinearGroup.mapGL IntegralAdeles τ * m := ⟨_, rfl⟩
  have hm : m = SpecialLinearGroup.mapGL IntegralAdeles σ * kI := by
    rw [hkI, hσ, map_inv, inv_mul_cancel_left]
  have hrow : ![0, 1] ᵥ* (redGL kI).val = ![0, 1] := by
    rw [hkI, map_mul, redGL_mapGL, Units.val_mul, ← Matrix.vecMul_vecMul, hτ,
      Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  have hlevel : intGL kI ∈ levelGroup := (mem_levelGroup_iff _).mpr ⟨kI, rfl, hrow⟩
  have hP : ratGL (SpecialLinearGroup.mapGL ℚ σ) =
      infGL (SpecialLinearGroup.mapGL ℝ σ) *
        finGL (intGL (SpecialLinearGroup.mapGL IntegralAdeles σ)) :=
    ArithmeticModularity.rational_decomposition σ
  have hcomm := infGL_finGL_comm (SpecialLinearGroup.mapGL ℝ σ)
    (intGL (SpecialLinearGroup.mapGL IntegralAdeles σ))
  have hIK := infGL_finGL_comm r (intGL kI)
  have key : finGL (intGL (SpecialLinearGroup.mapGL IntegralAdeles σ)) =
      ratGL (SpecialLinearGroup.mapGL ℚ σ) * (infGL (SpecialLinearGroup.mapGL ℝ σ))⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [hP, hcomm]
  refine ⟨γ0 * SpecialLinearGroup.mapGL ℚ σ, (SpecialLinearGroup.mapGL ℝ σ)⁻¹ * r,
    intGL kI, ?_⟩
  unfold IsDecomp
  refine ⟨?_, hlevel, ?_⟩
  · rw [map_mul, map_inv, det_mapGL_real, inv_one, one_mul]
    exact hr
  · calc g = ratGL γ0 * (finGL (intGL m) * infGL r) := hg
      _ = ratGL γ0 * (finGL (intGL (SpecialLinearGroup.mapGL IntegralAdeles σ * kI)) *
          infGL r) := by rw [← hm]
      _ = ratGL γ0 * (ratGL (SpecialLinearGroup.mapGL ℚ σ) *
          ((infGL (SpecialLinearGroup.mapGL ℝ σ))⁻¹ * (finGL (intGL kI) * infGL r))) := by
        rw [map_mul, map_mul, key]
        simp only [mul_assoc]
      _ = ratGL γ0 * (ratGL (SpecialLinearGroup.mapGL ℚ σ) *
          ((infGL (SpecialLinearGroup.mapGL ℝ σ))⁻¹ * (infGL r * finGL (intGL kI)))) := by
        rw [hIK]
      _ = _ := by
        rw [map_mul, map_mul, map_inv]
        simp only [mul_assoc]

/-! ### Uniqueness -/

theorem exists_int_matrix (δ : BinaryRationalGL) (h : finOfRat δ ∈ levelGroup) :
    ∃ (N : Fin 2 → Fin 2 → ℤ) (m : IntegralBinaryGL),
      (∀ i j, δ.val i j = (N i j : ℚ)) ∧ (∀ i j, m.val i j = (N i j : IntegralAdeles)) ∧
        ![0, 1] ᵥ* (redGL m).val = ![0, 1] := by
  obtain ⟨m, hm, hrow⟩ := (mem_levelGroup_iff _).mp h
  have hent : ∀ i j, integralEmbedding (m.val i j) = algebraMap ℚ FiniteAdeles (δ.val i j) :=
    fun i j => congrArg (fun B : BinaryFiniteGL => B.val i j) hm
  have hint : ∀ i j, ∃ n : ℤ, δ.val i j = n := by
    intro i j
    exact (IntegralRationals.integral_iff_integer (δ.val i j)).mp ⟨m.val i j, hent i j⟩
  choose N hN using hint
  refine ⟨N, m, hN, ?_, hrow⟩
  intro i j
  apply integralEmbedding_injective
  rw [hent i j, hN i j]
  simp

theorem exists_sl_of_rational {δ : BinaryRationalGL} {r r' : BinaryRealGL}
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val)
    (hr' : 0 < (GeneralLinearGroup.det r' : ℝˣ).val)
    (hreal : realOfRat δ * r = r') (hmem : finOfRat δ ∈ levelGroup) :
    ∃ ε : SpecialLinearGroup (Fin 2) ℤ, ε ∈ CongruenceSubgroup.Gamma1 3 ∧
      δ = SpecialLinearGroup.mapGL ℚ ε := by
  obtain ⟨N, m, hN, hm, hrow⟩ := exists_int_matrix δ hmem
  obtain ⟨N', -, hN', -, -⟩ := exists_int_matrix δ⁻¹ (by
    rw [map_inv]
    exact Subgroup.inv_mem _ hmem)
  have hdetR : (GeneralLinearGroup.det (realOfRat δ) : ℝˣ).val =
      algebraMap ℚ ℝ δ.val.det := by
    rw [GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (algebraMap ℚ ℝ) δ.val).symm
  have hmulR : (GeneralLinearGroup.det (realOfRat δ) : ℝˣ).val *
      (GeneralLinearGroup.det r : ℝˣ).val = (GeneralLinearGroup.det r' : ℝˣ).val := by
    have h := congrArg (fun x : BinaryRealGL => (GeneralLinearGroup.det x : ℝˣ).val) hreal
    simpa only [map_mul, Units.val_mul] using h
  have hposR : 0 < (GeneralLinearGroup.det (realOfRat δ) : ℝˣ).val := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    nlinarith [mul_nonneg (neg_nonneg.mpr hneg) hr.le, hmulR, hr']
  have hposQ : 0 < δ.val.det := by
    rw [hdetR] at hposR
    simpa using hposR
  obtain ⟨D1, hD1⟩ : ∃ D1 : ℤ, D1 = N 0 0 * N 1 1 - N 0 1 * N 1 0 := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ D2 : ℤ, D2 = N' 0 0 * N' 1 1 - N' 0 1 * N' 1 0 := ⟨_, rfl⟩
  have hD1q : (D1 : ℚ) = δ.val.det := by
    rw [hD1, Matrix.det_fin_two, hN 0 0, hN 0 1, hN 1 0, hN 1 1]
    push_cast
    ring
  have hD2q : (D2 : ℚ) = (δ⁻¹).val.det := by
    rw [hD2, Matrix.det_fin_two, hN' 0 0, hN' 0 1, hN' 1 0, hN' 1 1]
    push_cast
    ring
  have hprod : δ.val.det * (δ⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hZ : D1 * D2 = 1 := by
    have : ((D1 * D2 : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, hD1q, hD2q]
      exact hprod
    exact_mod_cast this
  have hD1pos : 0 ≤ D1 := by
    have : (0 : ℚ) < D1 := by rw [hD1q]; exact hposQ
    exact_mod_cast this.le
  have hD1one : D1 = 1 := Int.eq_one_of_mul_eq_one_right hD1pos hZ
  have hdet1 : (Matrix.of N).det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    rw [← hD1]
    exact hD1one
  have hrow' : (redGL m).val 1 = ![0, 1] := (vecMul_row _).symm.trans hrow
  have hred : ∀ i j, (redGL m).val i j = ((N i j : ℤ) : ZMod 3) := by
    intro i j
    rw [redGL_val, hm i j, integralReduction_int]
  have h10 : ((N 1 0 : ℤ) : ZMod 3) = 0 := by
    rw [← hred]
    exact (congrFun hrow' 0).trans (by simp)
  have h11 : ((N 1 1 : ℤ) : ZMod 3) = 1 := by
    rw [← hred]
    exact (congrFun hrow' 1).trans (by simp)
  have h00 : ((N 0 0 : ℤ) : ZMod 3) = 1 := by
    have h3 : ((N 0 0 * N 1 1 - N 0 1 * N 1 0 : ℤ) : ZMod 3) = 1 := by
      rw [hD1.symm.trans hD1one]
      exact Int.cast_one
    push_cast at h3
    rw [h11, h10] at h3
    erw [mul_one, mul_zero, sub_zero] at h3
    exact h3
  obtain ⟨ε, hε⟩ : ∃ ε : SpecialLinearGroup (Fin 2) ℤ, (ε : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.of N :=
    ⟨⟨Matrix.of N, hdet1⟩, rfl⟩
  have e : ∀ i j, ε.val i j = N i j := fun i j => by rw [hε]; rfl
  refine ⟨ε, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem, e, e, e]
    exact ⟨h00, h11, h10⟩
  · apply Units.ext
    ext i j
    rw [mapGL_entry, e]
    exact hN i j

theorem isDecomp_eq {g : BinaryAdelicGL} {γ γ' : BinaryRationalGL} {r r' : BinaryRealGL}
    {k k' : BinaryFiniteGL} (h : IsDecomp g γ r k) (h' : IsDecomp g γ' r' k') :
    ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ CongruenceSubgroup.Gamma1 3 ∧
      γ = γ' * SpecialLinearGroup.mapGL ℚ δ ∧ r' = SpecialLinearGroup.mapGL ℝ δ * r := by
  obtain ⟨hr, hk, hg⟩ := h
  obtain ⟨hr', hk', hg'⟩ := h'
  have E := hg.symm.trans hg'
  have EF := congrArg (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)) E
  have ES := congrArg (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)) E
  simp only [map_mul, fst_ratGL, fst_infGL, fst_finGL, mul_one] at EF
  simp only [map_mul, snd_ratGL, snd_infGL, snd_finGL, one_mul] at ES
  have hreal : realOfRat (γ'⁻¹ * γ) * r = r' := by
    rw [map_mul, map_inv, mul_assoc, EF, inv_mul_cancel_left]
  have hfin : finOfRat (γ'⁻¹ * γ) * k = k' := by
    rw [map_mul, map_inv, mul_assoc, ES, inv_mul_cancel_left]
  have hmem : finOfRat (γ'⁻¹ * γ) ∈ levelGroup := by
    have : finOfRat (γ'⁻¹ * γ) = k' * k⁻¹ := eq_mul_inv_of_mul_eq hfin
    rw [this]
    exact Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk)
  obtain ⟨ε, hε, hδ⟩ := exists_sl_of_rational hr hr' hreal hmem
  refine ⟨ε, hε, ?_, ?_⟩
  · rw [← hδ, mul_inv_cancel_left]
  · rw [← hreal, hδ]
    congr 1
    apply Units.ext
    ext i j
    change algebraMap ℚ ℝ ((SpecialLinearGroup.mapGL ℚ ε).val i j) =
      (SpecialLinearGroup.mapGL ℝ ε).val i j
    rw [mapGL_entry, mapGL_entry]
    exact map_intCast _ _

/-! ### Iwasawa decomposition over `ℚ` -/

theorem exists_coprime_proportional (x y : ℚ) (h : ¬(x = 0 ∧ y = 0)) :
    ∃ (c d : ℤ) (e : ℚ), IsCoprime c d ∧ x = e * c ∧ y = e * d := by
  obtain ⟨D, hD, C, hC, E, hE⟩ : ∃ D : ℚ, D ≠ 0 ∧ ∃ C : ℤ, (C : ℚ) = x * D ∧
      ∃ E : ℤ, (E : ℚ) = y * D := by
    refine ⟨(x.den : ℚ) * y.den,
      mul_ne_zero (by exact_mod_cast x.den_nz) (by exact_mod_cast y.den_nz),
      x.num * y.den, ?_, y.num * x.den, ?_⟩
    · have h1 := Rat.mul_den_eq_num x
      push_cast
      linear_combination (-(y.den : ℚ)) * h1
    · have h1 := Rat.mul_den_eq_num y
      push_cast
      linear_combination (-(x.den : ℚ)) * h1
  have hne : ¬(C = 0 ∧ E = 0) := by
    rintro ⟨rfl, rfl⟩
    apply h
    constructor
    · have h1 : x * D = 0 := by rw [← hC]; simp
      exact (mul_eq_zero.mp h1).resolve_right hD
    · have h1 : y * D = 0 := by rw [← hE]; simp
      exact (mul_eq_zero.mp h1).resolve_right hD
  have hpos : 0 < Int.gcd C E :=
    Nat.pos_of_ne_zero (fun h0 => hne (Int.gcd_eq_zero_iff.mp h0))
  obtain ⟨g, c, d, -, hcd, hcg, hdg⟩ := Int.exists_gcd_one' hpos
  refine ⟨c, d, (g : ℚ) / D, Int.isCoprime_iff_gcd_eq_one.mpr hcd, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff hD, ← hC, hcg]
    push_cast
    ring
  · rw [div_mul_eq_mul_div, eq_div_iff hD, ← hE, hdg]
    push_cast
    ring

theorem exists_upper_triangular_mul (γ : BinaryRationalGL) :
    ∃ (b : BinaryRationalGL) (c : ℚˣ) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      γ = b * SpecialLinearGroup.mapGL ℚ σ ∧
      ∀ u : Adeles, binaryUnipotent u * ratGL b =
        ratGL b * binaryUnipotent (rationalAdele c.val * u) := by
  obtain ⟨c0, d0, e, hcop, hx, hy⟩ := exists_coprime_proportional (γ.val 1 0) (γ.val 1 1) (by
    rintro ⟨h0, h1⟩
    apply (GeneralLinearGroup.det γ).ne_zero
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h0, h1]
    ring)
  obtain ⟨σ, -, hσ⟩ := ModularGroup.bottom_row_surj (R := ℤ)
    (show (![c0, d0] : Fin 2 → ℤ) ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from hcop)
  have hσ10 : σ.val 1 0 = c0 := congrFun hσ 0
  have hσ11 : σ.val 1 1 = d0 := congrFun hσ 1
  obtain ⟨b, hbγ⟩ : ∃ b : BinaryRationalGL, γ = b * SpecialLinearGroup.mapGL ℚ σ :=
    ⟨γ * (SpecialLinearGroup.mapGL ℚ σ)⁻¹, (inv_mul_cancel_right _ _).symm⟩
  have e10 := congrArg (fun A : BinaryRationalGL => A.val 1 0) hbγ
  have e11 := congrArg (fun A : BinaryRationalGL => A.val 1 1) hbγ
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_entry, hσ10, hσ11] at e10 e11
  have hdetσ : ((σ.val 0 0 : ℤ) : ℚ) * (σ.val 1 1 : ℤ) -
      (σ.val 0 1 : ℤ) * (σ.val 1 0 : ℤ) = 1 := by
    have h := σ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hb10 : b.val 1 0 = 0 := by
    rw [hσ10, hσ11] at hdetσ
    rw [hx] at e10
    rw [hy] at e11
    linear_combination (-(d0 : ℚ)) * e10 + (c0 : ℚ) * e11 - b.val 1 0 * hdetσ
  have hbdet : b.val 0 0 * b.val 1 1 ≠ 0 := by
    have hd := (GeneralLinearGroup.det b).ne_zero
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hb10, mul_zero, sub_zero] at hd
    exact hd
  have ha : b.val 0 0 ≠ 0 := left_ne_zero_of_mul hbdet
  have hd : b.val 1 1 ≠ 0 := right_ne_zero_of_mul hbdet
  refine ⟨b, Units.mk0 (b.val 1 1 / b.val 0 0) (div_ne_zero hd ha), σ, hbγ, ?_⟩
  intro u
  have hc : rationalAdele (b.val 0 0) * rationalAdele (b.val 1 1 / b.val 0 0) =
      rationalAdele (b.val 1 1) := by
    rw [← map_mul]
    congr 1
    field_simp
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [ratGL, binaryUnipotent, Matrix.mul_apply,
      Fin.sum_univ_two, hb10]
  linear_combination (-u) * hc

end TernaryPeriodPolynomials.CuspIntegral
