module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCosets
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.Involution
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LineStabilizer
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneConj

@[expose] public section


/-!
# Block coordinates for the stabilizer of the good plane

The reference good-plane cusp is `cuspFlag .plane true = F · P`, `F` the permutation `e₂ ↔ e₃`, so
its stabilizer in `Γ = {γ ∈ GL₃(ℤ) : last row ≡ e₃ mod 3}` consists of the integral matrices
`[[a, β, b], [0, d, 0], [c, ζ, e]]` with `d = ±1`, `(c, ζ, e) ≡ (0, 0, 1) mod 3`.
Conjugating by the *rational* frame `g = F · diag(1, 3, 1)` (`gF`) puts this group into the rational
plane parabolic, with standard radical lattice:
`g⁻¹ Γ_F g = Λ = {P(b, κ(m), d) : b ∈ ℤ², m ∈ Γ₁'(3), d ∈ ℤˣ}` (`mem_ΛG_iff`),
where `Γ₁'(3) = binaryArithmeticLevel` (second row `≡ (0, 1) mod 3`) and `κ(m) = δ⁻¹ m δ`,
`δ = diag(1, 3)` (`kap`, `integralEmbed_kap`), i.e. `κ([[a, b], [c, e]]) = [[a, 3b], [c/3, e]]`.
So `Λ ≅ ℤ² ⋊ (Γ₁'(3) × ℤˣ)`, and `Pg b m d · Pg b' m' d' = Pg (b + d κ(m) b') (m m') (d d')`
(`Pg_mul`).

The conjugation transport of `GoodPlaneConj` gives
`psiG : CuspH2 n χ .plane true ≃ₗ H²(Λ, V)` for every character `χ`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates LevelOneCosets IdentityPlaneCosets CuspOrbits CuspReduction
open TernaryPeriodPolynomials.HeckeCommutativity (mem_rationalLevel_of_int)

/-! ### The conjugation `κ(m) = δ⁻¹ m δ` -/

/-- `δ = diag(1, 3)`. -/
def del : GL (Fin 2) ℚ :=
  ⟨!![1, 0; 0, 3], !![1, 0; 0, 1/3], by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem del_val : (del : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, 3] := rfl

theorem del_inv_val : ((del⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, 1/3] := rfl

/-- The integral matrix `[[a, 3b], [c/3, e]]`. -/
def kapMat (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 0 0, 3 * A 0 1; A 1 0 / 3, A 1 1]

theorem kapMat_map {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : (3 : ℤ) ∣ A 1 0) :
    (kapMat A).map (Int.castRingHom ℚ) =
      ((del⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * A.map (Int.castRingHom ℚ) *
        (del : Matrix (Fin 2) (Fin 2) ℚ) := by
  obtain ⟨c, hc⟩ := hA
  have h3 : A 1 0 / 3 = c := by omega
  have h4 : ((A 1 0 : ℤ) : ℚ) = 3 * c := by exact_mod_cast hc
  rw [del_val, del_inv_val, Matrix.eta_fin_two (A.map _)]
  simp only [Matrix.mul_fin_two, Matrix.map_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kapMat, h3, h4] <;> ring

theorem three_dvd_of_cast_zero {a : ℤ} (h : ((a : ℤ) : ZMod 3) = 0) : (3 : ℤ) ∣ a := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp h
  exact_mod_cast this

theorem level_row (m : binaryArithmeticLevel) :
    ((m.val.val 1 0 : ℤ) : ZMod 3) = 0 ∧ ((m.val.val 1 1 : ℤ) : ZMod 3) = 1 := by
  have h := (mem_binaryArithmeticLevel_iff m.val).mp m.property
  exact ⟨by simpa using h 0, by simpa using h 1⟩

theorem level_dvd (m : binaryArithmeticLevel) : (3 : ℤ) ∣ m.val.val 1 0 :=
  three_dvd_of_cast_zero (level_row m).1

theorem kapMat_mul (m m' : binaryArithmeticLevel) :
    kapMat m.val.val * kapMat m'.val.val = kapMat (m * m').val.val := by
  have h : (del : Matrix (Fin 2) (Fin 2) ℚ) * ((del⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : (kapMat m.val.val * kapMat m'.val.val).map (Int.castRingHom ℚ) =
      (kapMat (m * m').val.val).map (Int.castRingHom ℚ) := by
    rw [Matrix.map_mul, kapMat_map (A := m.val.val) (level_dvd m),
      kapMat_map (A := m'.val.val) (level_dvd m'),
      kapMat_map (A := (m * m').val.val) (level_dvd (m * m'))]
    change _ = _ * (m.val.val * m'.val.val).map (Int.castRingHom ℚ) * _
    rw [Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (del : Matrix (Fin 2) (Fin 2) ℚ), h, Matrix.one_mul]
  exact Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective key

theorem kapMat_one : kapMat (1 : binaryArithmeticLevel).val.val = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kapMat]

/-- **`κ : Γ₁'(3) → GL₂(ℤ)`**, `κ(m) = δ⁻¹ m δ`. -/
def kap : binaryArithmeticLevel →* GL (Fin 2) ℤ where
  toFun m := ⟨kapMat m.val.val, kapMat m⁻¹.val.val, by
      rw [kapMat_mul, mul_inv_cancel, kapMat_one], by
      rw [kapMat_mul, inv_mul_cancel, kapMat_one]⟩
  map_one' := Units.ext kapMat_one
  map_mul' m m' := Units.ext (kapMat_mul m m').symm

theorem kap_val (m : binaryArithmeticLevel) :
    ((kap m : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = kapMat m.val.val := rfl

/-- **`κ(m) = δ⁻¹ m δ` in `GL₂(ℚ)`.** -/
theorem integralEmbed_kap (m : binaryArithmeticLevel) :
    integralEmbed (kap m) = del⁻¹ * integralEmbed m.val * del := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, integralEmbed_val, integralEmbed_val, kap_val]
  exact kapMat_map (level_dvd m)

theorem integralEmbed_kap_val (m : binaryArithmeticLevel) :
    ((integralEmbed (kap m) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (kapMat m.val.val).map (Int.castRingHom ℚ) := rfl

theorem kap_injective : Function.Injective kap := by
  intro m m' h
  have h' := congrArg integralEmbed h
  rw [integralEmbed_kap, integralEmbed_kap] at h'
  apply Subtype.ext
  apply integralEmbed_injective
  have := congrArg (fun x => del * x * del⁻¹) h'
  simpa [mul_assoc] using this

/-! ### The frame `g = F · diag(1, 3, 1)` -/

/-- The rational frame `g = F · diag(1, 3, 1)` of the good plane. -/
def gF : RationalGL3 :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 3, 0], !![1, 0, 0; 0, 0, 1/3; 0, 1, 0], by
    rw [Matrix.mul_fin_three, Matrix.one_fin_three]
    norm_num, by
    rw [Matrix.mul_fin_three, Matrix.one_fin_three]
    norm_num⟩

theorem gF_val : (gF : Matrix (Fin 3) (Fin 3) ℚ) = !![1, 0, 0; 0, 0, 1; 0, 3, 0] := rfl

theorem gF_inv_val :
    ((gF⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) = !![1, 0, 0; 0, 0, 1/3; 0, 1, 0] := rfl

theorem rational_goodPlaneFrame_val :
    ((rational goodPlaneFrame : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rational, goodPlaneFrame, GeneralLinearGroup.map_apply]

theorem rational_goodPlaneFrame_inv :
    ((rational goodPlaneFrame)⁻¹ : RationalGL3) = rational goodPlaneFrame := by
  rw [← map_inv, show goodPlaneFrame⁻¹ = goodPlaneFrame from Units.ext rfl]

/-- The reference good-plane flag is `g P`. -/
theorem cuspFlag_eq : cuspFlag .plane true = (QuotientGroup.mk gF : Flags .plane) := by
  change (QuotientGroup.mk (rational goodPlaneFrame) : Flags .plane) = QuotientGroup.mk gF
  rw [QuotientGroup.eq]
  change InPlaneParabolic ((rational goodPlaneFrame)⁻¹ * gF)
  have hmul : (((rational goodPlaneFrame)⁻¹ * gF : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] * !![1, 0, 0; 0, 0, 1; 0, 3, 0] := by
    rw [Units.val_mul, rational_goodPlaneFrame_inv, rational_goodPlaneFrame_val, gF_val]
  constructor
  · rw [hmul]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hmul]
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ### The conjugated stabilizer -/

/-- **The good-plane stabilizer in block coordinates**: `Λ = g⁻¹ Γ_F g`. -/
def ΛG : Subgroup RationalGL3 := (cuspLevel .plane true).comap (MulAut.conj gF).toMonoidHom

theorem mem_ΛG (h : RationalGL3) : h ∈ ΛG ↔ gF * h * gF⁻¹ ∈ cuspLevel .plane true :=
  Iff.rfl

/-- The rational unit of `d ∈ ℤˣ`. -/
abbrev uq (d : ℤˣ) : ℚˣ := Units.map (Int.castRingHom ℚ : ℤ →* ℚ) d

theorem uq_val (d : ℤˣ) : ((uq d : ℚˣ) : ℚ) = ((d : ℤ) : ℚ) := rfl

theorem int_unit_sq (d : ℤˣ) : (d : ℤ) * (d : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem uq_sq (d : ℤˣ) : ((d : ℤ) : ℚ) * ((d : ℤ) : ℚ) = 1 := by
  exact_mod_cast int_unit_sq d

theorem uq_inv (d : ℤˣ) : (((uq d)⁻¹ : ℚˣ) : ℚ) = ((d : ℤ) : ℚ) := by
  rw [Units.val_inv_eq_inv_val, uq_val]
  exact inv_eq_of_mul_eq_one_right (uq_sq d)

/-- The block element `P(b, κ(m), d)`. -/
def Pg (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) : RationalGL3 :=
  P (icast b) (integralEmbed (kap m)) (uq d)

/-- The integral matrix `g P(b, κ(m), d) g⁻¹ = [[a, b₁d, β], [0, d, 0], [c, 3b₂d, e]]`. -/
def Kmat (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![m.val.val 0 0, b.1 * (d : ℤ), m.val.val 0 1; 0, (d : ℤ), 0;
    m.val.val 1 0, 3 * b.2 * (d : ℤ), m.val.val 1 1]

theorem conj_Pg_val (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) :
    ((gF * Pg b m d * gF⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      (Kmat b m d).map (Int.cast : ℤ → ℚ) := by
  obtain ⟨c, hc⟩ := level_dvd m
  have h3 : m.val.val 1 0 / 3 = c := by omega
  have h4 : ((m.val.val 1 0 : ℤ) : ℚ) = 3 * c := by exact_mod_cast hc
  rw [Units.val_mul, Units.val_mul, Pg, P_val, uq_val, gF_val, gF_inv_val, integralEmbed_kap_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kmat, kapMat, icast, Matrix.mul_apply, Fin.sum_univ_three, h3, h4] <;> ring

theorem Kmat_det (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) :
    (Kmat b m d).det = (d : ℤ) * (m.val.val).det := by
  rw [Kmat, Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

theorem det_isUnit (m : GL (Fin 2) ℤ) : IsUnit (m : Matrix (Fin 2) (Fin 2) ℤ).det := by
  rcases det_units m with h | h <;> rw [h]
  · exact isUnit_one
  · exact isUnit_one.neg

theorem Pg_parabolic (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) :
    Pg b m d ∈ planeParabolic ℚ := by
  change InPlaneParabolic (Pg b m d)
  constructor <;> simp [Pg, P_val]

theorem Pg_mem (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) : Pg b m d ∈ ΛG := by
  rw [mem_ΛG]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · apply mem_rationalLevel_of_int _ (Kmat b m d) (conj_Pg_val b m d)
    · rw [Kmat_det]
      exact (Units.isUnit d).mul (det_isUnit m.val)
    · obtain ⟨r0, r1⟩ := level_row m
      intro j
      fin_cases j
      · simpa [Kmat] using r0
      · have h3 : (3 : ZMod 3) = 0 := by decide
        simp [Kmat, h3]
      · simpa [Kmat] using r1
  · rw [MulAction.mem_stabilizer_iff, cuspFlag_eq]
    change (QuotientGroup.mk (gF * Pg b m d * gF⁻¹ * gF) : Flags .plane) = QuotientGroup.mk gF
    rw [inv_mul_cancel_right, QuotientGroup.eq]
    have h := (parabolic .plane).inv_mem (Pg_parabolic b m d)
    simpa [mul_assoc] using h

/-! ### Every element of `Λ` is a block element -/

theorem level_entries (k : arithmeticLevel) (j : Fin 3) :
    ((k.val.val 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
  have h := k.property
  change lastRow ᵥ* (reductionThree k.val).val = lastRow at h
  have e := congrFun h j
  rw [CuspOrbits.lastRow_vecMul] at e
  change ((k.val.val 2 j : ℤ) : ZMod 3) = lastRow j at e
  rw [e]
  fin_cases j <;> simp [lastRow]

/-- An integer whose product with another integer is `±1` is a unit. -/
def unitOf (u : ℤ) (h : u * u = 1) : ℤˣ := ⟨u, u, h, h⟩

theorem mem_ΛG_exists (h : RationalGL3) (hh : h ∈ ΛG) :
    ∃ b m d, h = Pg b m d := by
  rw [mem_ΛG] at hh
  obtain ⟨⟨k, hk⟩, hstab⟩ := Subgroup.mem_inf.mp hh
  have hpar : h ∈ planeParabolic ℚ := by
    rw [MulAction.mem_stabilizer_iff, cuspFlag_eq] at hstab
    change (QuotientGroup.mk (gF * h * gF⁻¹ * gF) : Flags .plane) = QuotientGroup.mk gF at hstab
    rw [inv_mul_cancel_right, QuotientGroup.eq] at hstab
    have h1 : h⁻¹ ∈ parabolic .plane := by simpa [mul_assoc] using hstab
    have h2 := (parabolic .plane).inv_mem h1
    rw [inv_inv] at h2
    exact h2
  set K : Matrix (Fin 3) (Fin 3) ℤ := k.val.val
  have hval : (h : Matrix (Fin 3) (Fin 3) ℚ) =
      ((gF⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) * K.map (Int.cast : ℤ → ℚ) *
        (gF : Matrix (Fin 3) (Fin 3) ℚ) := by
    have e : h = gF⁻¹ * rationalInclusion k * gF := by rw [hk]; group
    rw [e, Units.val_mul, Units.val_mul]
    rfl
  have entry : ∀ i j, (h : Matrix (Fin 3) (Fin 3) ℚ) i j =
      (!![(K 0 0 : ℚ), 3 * K 0 2, K 0 1; K 2 0 / 3, K 2 2, K 2 1 / 3; K 1 0, 3 * K 1 2, K 1 1] :
        Matrix (Fin 3) (Fin 3) ℚ) i j := by
    intro i j
    rw [hval, gF_val, gF_inv_val, Matrix.eta_fin_three (K.map _)]
    simp only [Matrix.mul_fin_three, Matrix.map_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have h10 : K 1 0 = 0 := by
    have e := entry 2 0
    rw [hpar.1] at e
    simpa using e.symm
  have h12 : K 1 2 = 0 := by
    have e := entry 2 1
    rw [hpar.2] at e
    simpa using e.symm
  have hrow := level_entries k
  have r0 : ((K 2 0 : ℤ) : ZMod 3) = 0 := by simpa using hrow 0
  have r1 : ((K 2 1 : ℤ) : ZMod 3) = 0 := by simpa using hrow 1
  have r2 : ((K 2 2 : ℤ) : ZMod 3) = 1 := by simpa using hrow 2
  obtain ⟨c0, hc0⟩ := three_dvd_of_cast_zero r0
  obtain ⟨c1, hc1⟩ := three_dvd_of_cast_zero r1
  have hc0' : K 2 0 / 3 = c0 := by omega
  have hc0q : ((K 2 0 : ℤ) : ℚ) = 3 * c0 := by exact_mod_cast hc0
  have hc1q : ((K 2 1 : ℤ) : ℚ) = 3 * c1 := by exact_mod_cast hc1
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![K 0 0, K 0 2; K 2 0, K 2 2]
  have hMdet : M.det = K 0 0 * K 2 2 - K 0 2 * K 2 0 := Matrix.det_fin_two_of _ _ _ _
  have hdetK : K.det = K 1 1 * M.det := by
    rw [Matrix.det_fin_three, hMdet, h10, h12]
    ring
  have hKdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det _).mp k.val.isUnit
  have hunit : IsUnit (K 1 1 * M.det) := by
    rw [← hdetK]
    exact hKdet
  have hd : IsUnit (K 1 1) := isUnit_of_mul_isUnit_left hunit
  have hM : IsUnit M.det := isUnit_of_mul_isUnit_right hunit
  have hsq : K 1 1 * K 1 1 = 1 := by
    rcases Int.isUnit_iff.mp hd with e | e <;> simp [e]
  let mGL : GL (Fin 2) ℤ := ⟨M, M⁻¹, Matrix.mul_nonsing_inv M hM, Matrix.nonsing_inv_mul M hM⟩
  have hmem : mGL ∈ binaryArithmeticLevel := by
    apply (mem_binaryArithmeticLevel_iff mGL).mpr
    intro column
    fin_cases column
    · simpa [mGL, M] using r0
    · simpa [mGL, M] using r2
  refine ⟨(K 0 1 * K 1 1, c1 * K 1 1), ⟨mGL, hmem⟩, unitOf (K 1 1) hsq, ?_⟩
  have hsqQ : ((K 1 1 : ℤ) : ℚ) * ((K 1 1 : ℤ) : ℚ) = 1 := by exact_mod_cast hsq
  apply Units.ext
  rw [Pg, P_val, uq_val]
  ext i j
  rw [entry, integralEmbed_kap_val]
  fin_cases i <;> fin_cases j <;>
    simp [kapMat, mGL, M, icast, unitOf, h10, h12, hc0q, hc1q, hc0'] <;>
    first
    | linear_combination (-((K 0 1 : ℤ) : ℚ)) * hsqQ
    | linear_combination (-(c1 : ℚ)) * hsqQ

/-- **Membership in `Λ` in block coordinates.** -/
theorem mem_ΛG_iff (h : RationalGL3) : h ∈ ΛG ↔ ∃ b m d, h = Pg b m d := by
  constructor
  · exact mem_ΛG_exists h
  · rintro ⟨b, m, d, rfl⟩
    exact Pg_mem b m d

end TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
