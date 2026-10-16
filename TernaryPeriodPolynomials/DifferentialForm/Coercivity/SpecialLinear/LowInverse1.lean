module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowHodge1

@[expose] public section


/-! Exact inverse-row certificates for the actual low-degree Hodge coordinates. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

theorem lowHodgeAction1_kernel_0 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h0 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h0
  have h8 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h8
  have h10 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h10
  have h17 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h17
  have h19 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h19
  have h22 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h22
  have h26 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h26
  have hz : (143 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (399 : ℝ) * h0 + (351 : ℝ) * h8 + (351 : ℝ) * h10 + (-171 : ℝ) * h17 + (171 : ℝ) * h19 + (-162 : ℝ) * h22 + (162 : ℝ) * h26
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_1 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h1 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h1
  have h5 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h5
  have h9 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h9
  have h14 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h14
  have h18 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h18
  have h21 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h21
  have h29 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h29
  have hz : (143 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (399 : ℝ) * h1 + (81 : ℝ) * h5 + (-432 : ℝ) * h9 + (-261 : ℝ) * h14 + (-90 : ℝ) * h18 + (-162 : ℝ) * h21 + (-162 : ℝ) * h29
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_2 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h2 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h2
  have h4 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h4
  have h6 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h6
  have h13 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h13
  have h15 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h15
  have h24 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h24
  have h28 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h28
  have hz : (143 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (399 : ℝ) * h2 + (81 : ℝ) * h4 + (-432 : ℝ) * h6 + (261 : ℝ) * h13 + (90 : ℝ) * h15 + (162 : ℝ) * h24 + (-162 : ℝ) * h28
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_3 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (308 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (390 : ℝ) * h3 + (171 : ℝ) * h7 + (171 : ℝ) * h11 + (-81 : ℝ) * h16 + (81 : ℝ) * h20 + (-171 : ℝ) * h23 + (171 : ℝ) * h25 + (-351 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_4 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h2 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h2
  have h4 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h4
  have h6 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h6
  have h13 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h13
  have h15 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h15
  have h24 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h24
  have h28 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h28
  have hz : (1001 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (189 : ℝ) * h2 + (1011 : ℝ) * h4 + (-684 : ℝ) * h6 + (-189 : ℝ) * h13 + (324 : ℝ) * h15 + (-684 : ℝ) * h24 + (-702 : ℝ) * h28
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_5 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h1 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h1
  have h5 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h5
  have h9 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h9
  have h14 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h14
  have h18 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h18
  have h21 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h21
  have h29 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h29
  have hz : (1001 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (189 : ℝ) * h1 + (1011 : ℝ) * h5 + (-684 : ℝ) * h9 + (189 : ℝ) * h14 + (-324 : ℝ) * h18 + (684 : ℝ) * h21 + (-702 : ℝ) * h29
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_6 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h2 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h2
  have h4 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h4
  have h6 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h6
  have h13 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h13
  have h15 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h15
  have h24 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h24
  have h28 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h28
  have hz : (1001 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-1008 : ℝ) * h2 + (-684 : ℝ) * h4 + (2064 : ℝ) * h6 + (-378 : ℝ) * h13 + (-540 : ℝ) * h15 + (216 : ℝ) * h24 + (1170 : ℝ) * h28
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_7 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h12 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h12
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (8008 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (4446 : ℝ) * h3 + (19293 : ℝ) * h7 + (12141 : ℝ) * h11 + (-3024 : ℝ) * h12 + (-3051 : ℝ) * h16 + (459 : ℝ) * h20 + (12051 : ℝ) * h23 + (-4563 : ℝ) * h25 + (-7605 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_8 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h0 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h0
  have h8 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h8
  have h10 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h10
  have h17 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h17
  have h19 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h19
  have h22 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h22
  have h26 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h26
  have hz : (1001 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (819 : ℝ) * h0 + (2631 : ℝ) * h8 + (-603 : ℝ) * h10 + (-351 : ℝ) * h17 + (351 : ℝ) * h19 + (-1854 : ℝ) * h22 + (-918 : ℝ) * h26
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_9 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h1 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h1
  have h5 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h5
  have h9 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h9
  have h14 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h14
  have h18 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h18
  have h21 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h21
  have h29 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h29
  have hz : (1001 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-1008 : ℝ) * h1 + (-684 : ℝ) * h5 + (2064 : ℝ) * h9 + (378 : ℝ) * h14 + (540 : ℝ) * h18 + (-216 : ℝ) * h21 + (1170 : ℝ) * h29
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_10 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h0 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h0
  have h8 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h8
  have h10 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h10
  have h17 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h17
  have h19 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h19
  have h22 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h22
  have h26 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h26
  have hz : (1001 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (819 : ℝ) * h0 + (-603 : ℝ) * h8 + (2631 : ℝ) * h10 + (-351 : ℝ) * h17 + (351 : ℝ) * h19 + (918 : ℝ) * h22 + (1854 : ℝ) * h26
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_11 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h12 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h12
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (8008 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (4446 : ℝ) * h3 + (12141 : ℝ) * h7 + (19293 : ℝ) * h11 + (3024 : ℝ) * h12 + (-459 : ℝ) * h16 + (3051 : ℝ) * h20 + (4563 : ℝ) * h23 + (-12051 : ℝ) * h25 + (-7605 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_12 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h12 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h12
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have hz : (143 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-162 : ℝ) * h7 + (162 : ℝ) * h11 + (399 : ℝ) * h12 + (171 : ℝ) * h16 + (171 : ℝ) * h20 + (-351 : ℝ) * h23 + (-351 : ℝ) * h25
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_13 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h2 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h2
  have h4 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h4
  have h6 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h6
  have h13 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h13
  have h15 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h15
  have h24 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h24
  have h28 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h28
  have hz : (143 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (261 : ℝ) * h2 + (-81 : ℝ) * h4 + (-162 : ℝ) * h6 + (399 : ℝ) * h13 + (-90 : ℝ) * h15 + (432 : ℝ) * h24 + (162 : ℝ) * h28
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_14 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h1 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h1
  have h5 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h5
  have h9 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h9
  have h14 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h14
  have h18 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h18
  have h21 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h21
  have h29 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h29
  have hz : (143 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-261 : ℝ) * h1 + (81 : ℝ) * h5 + (162 : ℝ) * h9 + (399 : ℝ) * h14 + (-90 : ℝ) * h18 + (432 : ℝ) * h21 + (-162 : ℝ) * h29
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_15 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h2 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h2
  have h4 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h4
  have h6 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h6
  have h13 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h13
  have h15 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h15
  have h24 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h24
  have h28 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h28
  have hz : (1001 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (630 : ℝ) * h2 + (972 : ℝ) * h4 + (-1620 : ℝ) * h6 + (-630 : ℝ) * h13 + (1740 : ℝ) * h15 + (-1620 : ℝ) * h24 + (-2538 : ℝ) * h28
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_16 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h12 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h12
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (8008 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-6318 : ℝ) * h3 + (-9153 : ℝ) * h7 + (-1377 : ℝ) * h11 + (9576 : ℝ) * h12 + (13191 : ℝ) * h16 + (1881 : ℝ) * h20 + (-3159 : ℝ) * h23 + (-13689 : ℝ) * h25 + (16497 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_17 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h0 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h0
  have h8 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h8
  have h10 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h10
  have h17 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h17
  have h19 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h19
  have h22 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h22
  have h26 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h26
  have hz : (1001 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-1197 : ℝ) * h0 + (-1053 : ℝ) * h8 + (-1053 : ℝ) * h10 + (1173 : ℝ) * h17 + (-711 : ℝ) * h19 + (486 : ℝ) * h22 + (-486 : ℝ) * h26
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_18 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h1 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h1
  have h5 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h5
  have h9 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h9
  have h14 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h14
  have h18 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h18
  have h21 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h21
  have h29 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h29
  have hz : (1001 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-630 : ℝ) * h1 + (-972 : ℝ) * h5 + (1620 : ℝ) * h9 + (-630 : ℝ) * h14 + (1740 : ℝ) * h18 + (-1620 : ℝ) * h21 + (2538 : ℝ) * h29
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_19 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h0 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h0
  have h8 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h8
  have h10 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h10
  have h17 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h17
  have h19 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h19
  have h22 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h22
  have h26 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h26
  have hz : (1001 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (1197 : ℝ) * h0 + (1053 : ℝ) * h8 + (1053 : ℝ) * h10 + (-711 : ℝ) * h17 + (1173 : ℝ) * h19 + (-486 : ℝ) * h22 + (486 : ℝ) * h26
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_20 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h12 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h12
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (8008 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (6318 : ℝ) * h3 + (1377 : ℝ) * h7 + (9153 : ℝ) * h11 + (9576 : ℝ) * h12 + (1881 : ℝ) * h16 + (13191 : ℝ) * h20 + (-13689 : ℝ) * h23 + (-3159 : ℝ) * h25 + (-16497 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_21 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h1 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h1
  have h5 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h5
  have h9 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h9
  have h14 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h14
  have h18 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h18
  have h21 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h21
  have h29 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h29
  have hz : (1001 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-378 : ℝ) * h1 + (684 : ℝ) * h5 + (-216 : ℝ) * h9 + (1008 : ℝ) * h14 + (-540 : ℝ) * h18 + (2064 : ℝ) * h21 + (-1170 : ℝ) * h29
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_22 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h0 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h0
  have h8 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h8
  have h10 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h10
  have h17 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h17
  have h19 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h19
  have h22 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h22
  have h26 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h26
  have hz : (1001 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-378 : ℝ) * h0 + (-1854 : ℝ) * h8 + (918 : ℝ) * h10 + (162 : ℝ) * h17 + (-162 : ℝ) * h19 + (2064 : ℝ) * h22 + (1170 : ℝ) * h26
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_23 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h12 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h12
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (616 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-342 : ℝ) * h3 + (927 : ℝ) * h7 + (351 : ℝ) * h11 + (-504 : ℝ) * h12 + (-81 : ℝ) * h16 + (-351 : ℝ) * h20 + (1833 : ℝ) * h23 + (-585 : ℝ) * h25 + (585 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_24 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h2 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h2
  have h4 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h4
  have h6 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h6
  have h13 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h13
  have h15 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h15
  have h24 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h24
  have h28 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h28
  have hz : (1001 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (378 : ℝ) * h2 + (-684 : ℝ) * h4 + (216 : ℝ) * h6 + (1008 : ℝ) * h13 + (-540 : ℝ) * h15 + (2064 : ℝ) * h24 + (1170 : ℝ) * h28
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_25 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h12 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h12
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (616 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (342 : ℝ) * h3 + (-351 : ℝ) * h7 + (-927 : ℝ) * h11 + (-504 : ℝ) * h12 + (-351 : ℝ) * h16 + (-81 : ℝ) * h20 + (-585 : ℝ) * h23 + (1833 : ℝ) * h25 + (-585 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_26 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h0 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h0
  have h8 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h8
  have h10 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h10
  have h17 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h17
  have h19 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h19
  have h22 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h22
  have h26 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h26
  have hz : (1001 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (378 : ℝ) * h0 + (-918 : ℝ) * h8 + (1854 : ℝ) * h10 + (-162 : ℝ) * h17 + (162 : ℝ) * h19 + (1170 : ℝ) * h22 + (2064 : ℝ) * h26
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_27 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
  have h3 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h3
  have h7 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h7
  have h11 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h11
  have h16 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h16
  have h20 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h20
  have h23 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h23
  have h25 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h25
  have h27 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h27
  have hz : (616 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-702 : ℝ) * h3 + (-585 : ℝ) * h7 + (-585 : ℝ) * h11 + (423 : ℝ) * h16 + (-423 : ℝ) * h20 + (585 : ℝ) * h23 + (-585 : ℝ) * h25 + (1833 : ℝ) * h27
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_28 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
  have h2 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h2
  have h4 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h4
  have h6 := congrFun (congrFun hx (⟨2, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h6
  have h13 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h13
  have h15 := congrFun (congrFun hx (⟨5, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h15
  have h24 := congrFun (congrFun hx (⟨8, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h24
  have h28 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3)) = 0 at h28
  have hz : (1001 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-378 : ℝ) * h2 + (-702 : ℝ) * h4 + (1170 : ℝ) * h6 + (378 : ℝ) * h13 + (-846 : ℝ) * h15 + (1170 : ℝ) * h24 + (2064 : ℝ) * h28
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel_29 (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
  have h1 := congrFun (congrFun hx (⟨0, by decide⟩ : Fin 10)) (⟨1, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h1
  have h5 := congrFun (congrFun hx (⟨1, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((5/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h5
  have h9 := congrFun (congrFun hx (⟨3, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h9
  have h14 := congrFun (congrFun hx (⟨4, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3)) = 0 at h14
  have h18 := congrFun (congrFun hx (⟨6, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h18
  have h21 := congrFun (congrFun hx (⟨7, by decide⟩ : Fin 10)) (⟨0, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h21
  have h29 := congrFun (congrFun hx (⟨9, by decide⟩ : Fin 10)) (⟨2, by decide⟩ : Fin 3)
  change ((-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 3) + (5/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3)) = 0 at h29
  have hz : (1001 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 3) = 0 := by
    linear_combination (-378 : ℝ) * h1 + (-702 : ℝ) * h5 + (1170 : ℝ) * h9 + (-378 : ℝ) * h14 + (846 : ℝ) * h18 + (-1170 : ℝ) * h21 + (2064 : ℝ) * h29
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem lowHodgeAction1_kernel (x : Fin 10 → Fin 3 → ℝ)
    (hx : lowHodgeAction1 x = 0) : x = 0 := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact lowHodgeAction1_kernel_0 x hx
  · exact lowHodgeAction1_kernel_1 x hx
  · exact lowHodgeAction1_kernel_2 x hx
  · exact lowHodgeAction1_kernel_3 x hx
  · exact lowHodgeAction1_kernel_4 x hx
  · exact lowHodgeAction1_kernel_5 x hx
  · exact lowHodgeAction1_kernel_6 x hx
  · exact lowHodgeAction1_kernel_7 x hx
  · exact lowHodgeAction1_kernel_8 x hx
  · exact lowHodgeAction1_kernel_9 x hx
  · exact lowHodgeAction1_kernel_10 x hx
  · exact lowHodgeAction1_kernel_11 x hx
  · exact lowHodgeAction1_kernel_12 x hx
  · exact lowHodgeAction1_kernel_13 x hx
  · exact lowHodgeAction1_kernel_14 x hx
  · exact lowHodgeAction1_kernel_15 x hx
  · exact lowHodgeAction1_kernel_16 x hx
  · exact lowHodgeAction1_kernel_17 x hx
  · exact lowHodgeAction1_kernel_18 x hx
  · exact lowHodgeAction1_kernel_19 x hx
  · exact lowHodgeAction1_kernel_20 x hx
  · exact lowHodgeAction1_kernel_21 x hx
  · exact lowHodgeAction1_kernel_22 x hx
  · exact lowHodgeAction1_kernel_23 x hx
  · exact lowHodgeAction1_kernel_24 x hx
  · exact lowHodgeAction1_kernel_25 x hx
  · exact lowHodgeAction1_kernel_26 x hx
  · exact lowHodgeAction1_kernel_27 x hx
  · exact lowHodgeAction1_kernel_28 x hx
  · exact lowHodgeAction1_kernel_29 x hx

end TernaryPoly.SL3PolynomialCoercivity
