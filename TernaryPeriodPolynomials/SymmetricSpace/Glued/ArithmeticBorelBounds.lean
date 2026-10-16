module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticRational
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.SymmetricSpaceArithmeticProper

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceBorelCorner
open SymmetricSpaceRationalGluing SymmetricSpaceRationalAction

/-- The real relative arithmetic matrix has a fixed absolute determinant for two fixed frames. -/
theorem relative_det_abs (a b : RationalGL) (g : IntegralGL) :
    |(realRational (relative a b g)).val.det|=
      |(realRational b⁻¹).val.det| *|(realRational a).val.det| := by
  have hg : |(SymmetricSpaceArithmeticProper.realIntegral g).val.det|=1 := by
    have h := SymmetricSpaceArithmeticProper.realIntegral_det_sq g
    have h' : |(SymmetricSpaceArithmeticProper.realIntegral g).val.det|^2=1 := by
      simpa only [sq_abs] using h
    nlinarith [abs_nonneg (SymmetricSpaceArithmeticProper.realIntegral g).val.det]
  simp only [relative,map_mul]
  rw [show realRational (integralRational g)=SymmetricSpaceArithmeticProper.realIntegral g from
    realRational_integral g]
  change |((realRational b⁻¹).val*(SymmetricSpaceArithmeticProper.realIntegral g).val*
    (realRational a).val).det|=_
  rw [det_mul,det_mul,abs_mul,abs_mul,hg,mul_one]

/-- Each factor of a fixed positive triple product is bounded when the other factors are bounded below. -/
theorem triple_factor_bound (ε x y z D : ℝ) (hε : 0<ε) (hx : 0≤x)
    (hy : ε≤y) (hz : ε≤z) (hprod : x*y*z=D) : x≤D/ε^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  calc
    x*ε^2 ≤ x*(y*z) := mul_le_mul_of_nonneg_left
      (by simpa only [pow_two] using mul_le_mul hy hz hε.le (hε.le.trans hy)) hx
    _ = D := by simpa only [mul_assoc] using hprod

/-- Fixed rational denominators and determinant bound every diagonal of an actual Borel relative matrix. -/
theorem borel_diagonal_bound (a b : RationalGL) :
    ∃ A : ℝ,0<A ∧ ∀ (g : IntegralGL) (_h : realRational (relative a b g)∈borelStabilizer),
      ∀ i, |(realRational (relative a b g)).val i i|≤A := by
  obtain ⟨d,hd,hden⟩ := relative_denominator a b
  let ε : ℝ := 1/(d : ℝ)
  have hε : 0<ε := one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd)
  let D : ℝ := |(realRational b⁻¹).val.det| *|(realRational a).val.det|
  have hD : 0<D := mul_pos (abs_pos.mpr (realRational b⁻¹).det_ne_zero)
    (abs_pos.mpr (realRational a).det_ne_zero)
  refine ⟨D/ε^2,div_pos hD (sq_pos_of_pos hε),?_⟩
  intro g h
  let r : BorelGroup := ⟨realRational (relative a b g),h⟩
  have hdiag := diagonal_nonzero r
  have hlo (i : Fin 3) (hi : r.val.val i i≠0) : ε≤|r.val.val i i| :=
    denominator_lower_bound d hd ((relative a b g).val i i)
      (by change ((relative a b g).val i i : ℝ)≠0 at hi; exact_mod_cast hi) (hden g i i)
  have h0 := hlo 0 hdiag.1
  have h1 := hlo 1 hdiag.2.1
  have h2 := hlo 2 hdiag.2.2
  have hprod : |r.val.val 0 0| *|r.val.val 1 1| *|r.val.val 2 2|=D := by
    have hdet := relative_det_abs a b g
    change |r.val.val.det|=D at hdet
    rw [matrix_eq_upper,upperMatrix_det,abs_mul,abs_mul] at hdet
    exact hdet
  change ∀ i,|r.val.val i i|≤D/ε^2
  intro i
  fin_cases i
  · exact triple_factor_bound ε _ _ _ D hε (abs_nonneg _) h1 h2 hprod
  · change |r.val.val 1 1|≤D/ε^2
    exact triple_factor_bound ε _ _ _ D hε (abs_nonneg _) h0 h2 (by nlinarith only [hprod])
  · change |r.val.val 2 2|≤D/ε^2
    exact triple_factor_bound ε _ _ _ D hε (abs_nonneg _) h0 h1 (by nlinarith only [hprod])

/-- Compact corners have uniformly bounded actual unipotent coordinates, even on the zero-root faces. -/
theorem compact_unipotent_bound (K L : Set Corner) (hK : IsCompact K) (hL : IsCompact L) :
    ∃ M : ℝ,1≤M ∧ ∀ p∈K∪L,∀ i,|p.1 i|≤M := by
  obtain ⟨M,hM⟩ := (hK.union hL).bddAbove_image continuous_fst.norm.continuousOn
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro p hp i
  exact (norm_le_pi_norm p.1 i).trans ((hM ⟨p,hp,rfl⟩).trans (le_max_right _ _))

end TernaryPoly.SymmetricSpaceGluedArithmetic
