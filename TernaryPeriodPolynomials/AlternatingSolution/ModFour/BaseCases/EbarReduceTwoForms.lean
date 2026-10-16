module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.Operators
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section



/-!
The hand-reduced mod-two forms of `Ebar1_D4`, `Ebar2_D4`,
`Ebar1_D6`, `Ebar2_D6` (small, no `bind₁` nesting, same recipe as
`reduceTwo_g40`/`reduceTwo_g70`).
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem Ebar1_D4_eq_probe :
    Ebar1_D4 = X 0 ^ 2 * X 1 ^ 2 + X 0 ^ 2 * X 1 * X 2 + X 0 * X 1 ^ 3 + X 0 * X 1 ^ 2 * X 2 +
      X 1 ^ 3 * X 2 + X 1 ^ 2 * X 2 ^ 2 := by
  show reduceTwo E1_D4 = _
  simp [E1_D4, reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

theorem Ebar2_D4_eq_probe :
    Ebar2_D4 = X 0 ^ 3 * X 1 + X 0 ^ 3 * X 2 + X 0 ^ 2 * X 1 ^ 2 + X 0 ^ 2 * X 1 * X 2 +
      X 0 ^ 2 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 := by
  show reduceTwo E2_D4 = _
  simp [E2_D4, reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

theorem Ebar1_D6_eq_probe :
    Ebar1_D6 = X 0 ^ 4 * X 1 * X 2 + X 0 ^ 2 * X 1 ^ 3 * X 2 + X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 +
      X 0 ^ 2 * X 1 * X 2 ^ 3 + X 0 * X 1 ^ 3 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 ^ 3 +
      X 1 ^ 5 * X 2 + X 1 ^ 4 * X 2 ^ 2 + X 1 ^ 3 * X 2 ^ 3 := by
  show reduceTwo E1_D6 = _
  simp [E1_D6, reduceTwo, CharTwo.sub_eq_add]; ring_nf;
    simp [ofNat_mod_poly2, CharTwo.sub_eq_add]

theorem Ebar2_D6_eq_probe :
    Ebar2_D6 = X 0 ^ 5 * X 2 + X 0 ^ 4 * X 2 ^ 2 + X 0 ^ 3 * X 1 ^ 2 * X 2 + X 0 ^ 3 * X 1 * X 2 ^ 2 +
      X 0 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 1 * X 2 ^ 3 + X 0 * X 1 ^ 4 * X 2 +
      X 0 * X 1 ^ 2 * X 2 ^ 3 := by
  show reduceTwo E2_D6 = _
  simp [E2_D6, reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

section Reflection

open PolynomialReflection

def Ebar1_D4L : List Mon :=
  [(0, 2, 2), (0, 3, 1), (1, 2, 1), (1, 3, 0), (2, 1, 1), (2, 2, 0)]

theorem Ebar1_D4_eq_ev : Ebar1_D4 = ev Ebar1_D4L := by
  rw [Ebar1_D4_eq_probe]
  simp only [ev, mono, Ebar1_D4L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

def Ebar2_D4L : List Mon :=
  [(1, 2, 1), (2, 0, 2), (2, 1, 1), (2, 2, 0), (3, 0, 1), (3, 1, 0)]

theorem Ebar2_D4_eq_ev : Ebar2_D4 = ev Ebar2_D4L := by
  rw [Ebar2_D4_eq_probe]
  simp only [ev, mono, Ebar2_D4L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

def Ebar1_D6L : List Mon :=
  [(0, 3, 3), (0, 4, 2), (0, 5, 1), (1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 2, 2), (2, 3, 1),
   (4, 1, 1)]

theorem Ebar1_D6_eq_ev : Ebar1_D6 = ev Ebar1_D6L := by
  rw [Ebar1_D6_eq_probe]
  simp only [ev, mono, Ebar1_D6L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

def Ebar2_D6L : List Mon :=
  [(1, 2, 3), (1, 4, 1), (2, 1, 3), (2, 2, 2), (3, 0, 3), (3, 1, 2), (3, 2, 1), (4, 0, 2),
   (5, 0, 1)]

theorem Ebar2_D6_eq_ev : Ebar2_D6 = ev Ebar2_D6L := by
  rw [Ebar2_D6_eq_probe]
  simp only [ev, mono, Ebar2_D6L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- `δ_p w`, computed on exponent lists: `w` and the target `Q` are given as exponent lists. -/
theorem delta_p_eq_of_reflect {w Q : Poly2} {lw lQ : List Mon} (hw : w = ev lw)
    (hQ : Q = ev lQ)
    (h : piL (addL (mulL Ebar1_D4L (sub1L lw)) (mulL Ebar2_D4L (sub2L lw))) = lQ) :
    delta_p w = Q := by
  show piOperator (Ebar1_D4 * sub₁ w + Ebar2_D4 * sub₂ w) = Q
  rw [Ebar1_D4_eq_ev, Ebar2_D4_eq_ev, hw, hQ, ev_sub₁, ev_sub₂, ← ev_mulL, ← ev_mulL, ← ev_addL,
    piOperator_ev, h]

/-- `δ_q w`, computed on exponent lists: `w` and the target `Q` are given as exponent lists. -/
theorem delta_q_eq_of_reflect {w Q : Poly2} {lw lQ : List Mon} (hw : w = ev lw)
    (hQ : Q = ev lQ)
    (h : piL (addL (mulL Ebar1_D6L (sub1L lw)) (mulL Ebar2_D6L (sub2L lw))) = lQ) :
    delta_q w = Q := by
  show piOperator (Ebar1_D6 * sub₁ w + Ebar2_D6 * sub₂ w) = Q
  rw [Ebar1_D6_eq_ev, Ebar2_D6_eq_ev, hw, hQ, ev_sub₁, ev_sub₂, ← ev_mulL, ← ev_mulL, ← ev_addL,
    piOperator_ev, h]

end Reflection

end TernaryPeriodPolynomials.Argument.ModFourBeta
