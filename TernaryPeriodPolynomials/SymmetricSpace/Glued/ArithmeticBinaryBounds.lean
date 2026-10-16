module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticRational
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic

/-- Squared real bounds give a convenient bound without introducing square roots. -/
theorem abs_le_max_one_of_sq_le (x R : ℝ) (h : x^2≤R) : |x|≤max 1 R := by
  by_cases hx : |x|≤1
  · exact hx.trans (le_max_left _ _)
  · have hp := le_self_pow₀ (le_of_not_ge hx) (by decide : (2 : ℕ)≠0)
    have hs : |x|^2≤R := by simpa only [sq_abs] using h
    exact hp.trans (hs.trans (le_max_right _ _))

/-- The rank-two Siegel estimate, with literal congruence equations and no lower root bound.
The nonzero lower-left entry has one fixed arithmetic lower bound. -/
theorem binary_siegel_entry_bound (δ D M : ℝ) (hδ : 0<δ) (hD : 0≤D) (hM : 1≤M) :
    ∃ R : ℝ,∀ a b c d x y t s k : ℝ,
      0<t → 0<s → 0<k → δ≤|c| → |a*d-b*c|≤D →
      |x|≤M → |y|≤M → t≤M → s≤M →
      a^2+t^2*(a*x+b)^2=k*(1+y^2*s^2) →
      a*c+t^2*(a*x+b)*(c*x+d)=k*y*s^2 →
      c^2+t^2*(c*x+d)^2=k*s^2 →
      |a|≤R ∧ |b|≤R ∧ |c|≤R ∧ |d|≤R := by
  let C := max 1 (D^2*M^4)
  let E := max 1 (D^2*M^2/δ^2)
  let B := E+C*M
  let F := (B^2+D)/δ
  let R := max B (max F C)
  have hM0 : 0≤M := zero_le_one.trans hM
  have hC : 0≤C := zero_le_one.trans (le_max_left _ _)
  have hE : 0≤E := zero_le_one.trans (le_max_left _ _)
  have hB : 0≤B := add_nonneg hE (mul_nonneg hC hM0)
  refine ⟨R,?_⟩
  intro a b c d x y t s k ht hs hk hc hdet hx hy htM hsM h00 h01 h11
  let Δ := a*d-b*c
  let u := c*x+d
  let v := a-c*y
  let w := a*x+b-y*(c*x+d)
  have hd2 : Δ^2≤D^2 := by
    simpa only [←pow_two,sq_abs] using mul_le_mul hdet hdet (abs_nonneg _) hD
  have ht2 := pow_le_pow_left₀ ht.le htM 2
  have hs2 := pow_le_pow_left₀ hs.le hsM 2
  have hc2 : δ^2≤c^2 := by
    simpa only [←pow_two,sq_abs] using mul_le_mul hc hc hδ.le (abs_nonneg _)
  have hk2 : k^2*s^2=Δ^2*t^2 := by
    have hmul := congrArg₂ (fun A B : ℝ => A*B) h00 h11
    have hsq := congrArg (fun A : ℝ => A^2) h01
    dsimp [Δ]
    nlinarith only [hmul,hsq]
  have hv : v^2+t^2*w^2=k := by
    dsimp [v,w]
    linear_combination h00-2*y*h01+y^2*h11
  have hv2 : v^2≤k := by nlinarith only [hv,mul_nonneg (sq_nonneg t) (sq_nonneg w)]
  have hcRow : c^2≤k*s^2 := by
    nlinarith only [h11,mul_nonneg (sq_nonneg t) (sq_nonneg (c*x+d))]
  have huRow : t^2*u^2≤k*s^2 := by dsimp [u]; nlinarith only [h11,sq_nonneg c]
  have hΔt : Δ^2*t^2≤D^2*M^2 :=
    mul_le_mul hd2 ht2 (sq_nonneg t) (sq_nonneg D)
  have hΔs : Δ^2*s^2≤D^2*M^2 :=
    mul_le_mul hd2 hs2 (sq_nonneg s) (sq_nonneg D)
  have hc4 : c^4≤D^2*M^4 := calc
    c^4=(c^2)^2 := by ring
    _ ≤ (k*s^2)^2 := pow_le_pow_left₀ (sq_nonneg c) hcRow 2
    _ = (k^2*s^2)*s^2 := by ring
    _ = (Δ^2*t^2)*s^2 := by rw [hk2]
    _ ≤ (D^2*M^2)*M^2 := mul_le_mul hΔt hs2 (sq_nonneg s)
      (mul_nonneg (sq_nonneg D) (sq_nonneg M))
    _ = D^2*M^4 := by ring
  have habsc : |c|≤C := by
    by_cases hc1 : |c|≤1
    · exact hc1.trans (le_max_left _ _)
    · have hh := le_self_pow₀ (le_of_not_ge hc1) (by decide : (4 : ℕ)≠0)
      have he4 : |c|^4=c^4 := calc
        _ = (|c|^2)^2 := by ring
        _ = (c^2)^2 := by rw [sq_abs]
        _ = c^4 := by ring
      have h4 : |c|^4≤D^2*M^4 := he4.symm ▸ hc4
      exact hh.trans (h4.trans (le_max_right _ _))
  have hcv : c^2*v^2≤D^2*M^2 := calc
    _ ≤ (k*s^2)*k := mul_le_mul hcRow hv2 (sq_nonneg v) (mul_nonneg hk.le (sq_nonneg s))
    _ = Δ^2*t^2 := by nlinarith only [hk2]
    _ ≤ _ := hΔt
  have hcu : c^2*u^2≤D^2*M^2 := by
    have he : t^2*(c^2*u^2)≤t^2*(Δ^2*s^2) := calc
      _ = c^2*(t^2*u^2) := by ring
      _ ≤ (k*s^2)*(k*s^2) := mul_le_mul hcRow huRow
        (mul_nonneg (sq_nonneg t) (sq_nonneg u)) (mul_nonneg hk.le (sq_nonneg s))
      _ = (k^2*s^2)*s^2 := by ring
      _ = t^2*(Δ^2*s^2) := by rw [hk2]; ring
    exact (le_of_mul_le_mul_left he (sq_pos_of_pos ht)).trans hΔs
  have hbound (z : ℝ) (hz : c^2*z^2≤D^2*M^2) : |z|≤E := by
    apply abs_le_max_one_of_sq_le
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
    have hh : z^2*δ^2≤c^2*z^2 := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc2 (sq_nonneg z)
    exact hh.trans hz
  have hvE := hbound v hcv
  have huE := hbound u hcu
  have haB : |a|≤B := calc
    _ = |v+c*y| := by congr 1; dsimp [v]; ring
    _ ≤ |v|+|c*y| := abs_add_le _ _
    _ ≤ E+C*M := add_le_add hvE (by rw [abs_mul]; exact mul_le_mul habsc hy (abs_nonneg y) hC)
  have hdB : |d|≤B := calc
    _ = |u-c*x| := by congr 1; dsimp [u]; ring
    _ ≤ |u|+|c*x| := abs_sub _ _
    _ ≤ E+C*M := add_le_add huE (by rw [abs_mul]; exact mul_le_mul habsc hx (abs_nonneg x) hC)
  have hbc : |b| *|c|≤B^2+D := calc
    _ = |a*d-Δ| := by rw [←abs_mul]; congr 1; dsimp [Δ]; ring
    _ ≤ |a*d|+|Δ| := abs_sub _ _
    _ ≤ B^2+D := add_le_add (by rw [abs_mul,pow_two]; exact mul_le_mul haB hdB (abs_nonneg d) hB) hdet
  have hbF : |b|≤F := (le_div_iff₀ hδ).mpr
    ((mul_le_mul_of_nonneg_left hc (abs_nonneg b)).trans hbc)
  exact ⟨haB.trans (le_max_left _ _),hbF.trans ((le_max_left _ _).trans (le_max_right _ _)),
    habsc.trans ((le_max_right _ _).trans (le_max_right _ _)),hdB.trans (le_max_left _ _)⟩

end TernaryPoly.SymmetricSpaceGluedArithmetic
