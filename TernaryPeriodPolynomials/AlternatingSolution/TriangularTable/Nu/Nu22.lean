module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section


/-!
Lemma 5.6 table (`mf:eq:table`, the paper) — one column per file. Column `nu`
is `beta_+(V_nu)`, where `V_{4j+m} = mult_m * L_j`, `mult = (1, d6, d4, d4 d6)`, and the
half-norm `g` satisfies `threeTermNorm (baseSym j m) = C 2 * g` (symmetric lift).
Each column has: a literal integral half-norm `lit*G`, its reduction `lit*P` mod two, and
`piOperator lit*P = value` (the printed table entry, with `rho = d7^2` where printed).
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 d4 d6 basis generator)
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.ModFourBeta

namespace TernaryPeriodPolynomials.Argument.Identities.Lemma56Table

noncomputable section

def lit22G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (544 * X 0 ^ 18 * X 2- 4896 * X 0 ^ 17 * X 1 * X 2- 6928 * X 0 ^ 17 * X 2 ^ 2+ 20248 * X 0 ^ 16 * X 1 ^ 2 * X 2+ 58888 * X 0 ^ 16 * X 1 * X 2 ^ 2
    + 37768 * X 0 ^ 16 * X 2 ^ 3- 51008 * X 0 ^ 15 * X 1 ^ 3 * X 2- 229224 * X 0 ^ 15 * X 1 ^ 2 * X 2 ^ 2- 302144 * X 0 ^ 15 * X 1 * X 2 ^ 3- 116508 * X 0 ^ 15 * X 2 ^ 4
    + 87463 * X 0 ^ 14 * X 1 ^ 4 * X 2+ 541420 * X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 2+ 1102407 * X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 3+ 873810 * X 0 ^ 14 * X 1 * X 2 ^ 4
    + 227476 * X 0 ^ 14 * X 2 ^ 5- 108017 * X 0 ^ 13 * X 1 ^ 5 * X 2- 866562 * X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 2- 2429329 * X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 3
    - 2973992 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 4- 1592332 * X 0 ^ 13 * X 1 * X 2 ^ 5- 298628 * X 0 ^ 13 * X 2 ^ 6+ 99259 * X 0 ^ 12 * X 1 ^ 6 * X 2
    + 993655 * X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 2+ 3609743 * X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 3)

def lit22G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (6078163 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 4+ 5027822 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 5+ 1941082 * X 0 ^ 12 * X 1 * X 2 ^ 6+ 273072 * X 0 ^ 12 * X 2 ^ 7
    - 69509 * X 0 ^ 11 * X 1 ^ 7 * X 2- 837282 * X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 2- 3824733 * X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 3- 8308418 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 4
    - 9466616 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 5- 5647470 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 6- 1638432 * X 0 ^ 11 * X 1 * X 2 ^ 7- 177380 * X 0 ^ 11 * X 2 ^ 8
    + 40482 * X 0 ^ 10 * X 1 ^ 8 * X 2+ 512248 * X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 2+ 3020449 * X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 3+ 7992633 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 4
    + 11874588 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 5+ 9709183 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 6+ 4364675 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 7+ 975590 * X 0 ^ 10 * X 1 * X 2 ^ 8
    + 82468 * X 0 ^ 10 * X 2 ^ 9- 28588 * X 0 ^ 9 * X 1 ^ 9 * X 2- 162751 * X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 2- 1935707 * X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 3)

def lit22G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-5327154 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 4- 10546206 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 5- 10867775 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 6- 6804415 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 7
    - 2350092 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 8- 412340 * X 0 ^ 9 * X 1 * X 2 ^ 9- 27324 * X 0 ^ 9 * X 2 ^ 10+ 40482 * X 0 ^ 8 * X 1 ^ 10 * X 2
    - 162751 * X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 2+ 1480860 * X 0 ^ 8 * X 1 ^ 8 * X 2 ^ 3+ 1839720 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 4+ 7512292 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 5
    + 8113968 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 6+ 7043714 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 7+ 3258489 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 8+ 896868 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 9
    + 122958 * X 0 ^ 8 * X 1 * X 2 ^ 10+ 6328 * X 0 ^ 8 * X 2 ^ 11- 69509 * X 0 ^ 7 * X 1 ^ 11 * X 2+ 512248 * X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 2
    - 1935707 * X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 3+ 1839720 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 4- 5846572 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 5- 2801046 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 6)

def lit22G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-5371118 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 7- 2703694 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 8- 1113432 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 9- 232162 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 10
    - 25312 * X 0 ^ 7 * X 1 * X 2 ^ 11- 980 * X 0 ^ 7 * X 2 ^ 12+ 99259 * X 0 ^ 6 * X 1 ^ 12 * X 2- 837282 * X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 2
    + 3020449 * X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 3- 5327154 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 4+ 7512292 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 5- 2801046 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 6
    + 4538080 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 7+ 1085777 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 8+ 989844 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 9+ 238763 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 10
    + 43536 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 11+ 3430 * X 0 ^ 6 * X 1 * X 2 ^ 12+ 92 * X 0 ^ 6 * X 2 ^ 13- 108017 * X 0 ^ 5 * X 1 ^ 13 * X 2+ 993655 * X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 2
    - 3824733 * X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 3+ 7992633 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 4- 10546206 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 5)

def lit22G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (8113968 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 6- 5371118 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 7+ 1085777 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 8- 804348 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 9
    - 88573 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 10- 42016 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 11- 4410 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 12- 276 * X 0 ^ 5 * X 1 * X 2 ^ 13- 4 * X 0 ^ 5 * X 2 ^ 14
    + 87463 * X 0 ^ 4 * X 1 ^ 14 * X 2- 866562 * X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 2+ 3609743 * X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 3- 8308418 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 4
    + 11874588 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 5- 10867775 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 6+ 7043714 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 7- 2703694 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 8
    + 989844 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 9- 88573 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 10+ 41256 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 11+ 2450 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 12
    + 390 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 13+ 10 * X 0 ^ 4 * X 1 * X 2 ^ 14- 51008 * X 0 ^ 3 * X 1 ^ 15 * X 2)

def lit22G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (541420 * X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 2- 2429329 * X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 3+ 6078163 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 4- 9466616 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 5
    + 9709183 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 6- 6804415 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 7+ 3258489 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 8- 1113432 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 9
    + 238763 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 10- 42016 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 11+ 2450 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 12- 320 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 13
    - 4 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 14+ 20248 * X 0 ^ 2 * X 1 ^ 16 * X 2- 229224 * X 0 ^ 2 * X 1 ^ 15 * X 2 ^ 2+ 1102407 * X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 3
    - 2973992 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 4+ 5027822 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 5- 5647470 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 6+ 4364675 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 7
    - 2350092 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 8+ 896868 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 9- 232162 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 10+ 43536 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 11)

def lit22G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-4410 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 12+ 390 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 13- 4 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 14- 4896 * X 0 * X 1 ^ 17 * X 2+ 58888 * X 0 * X 1 ^ 16 * X 2 ^ 2
    - 302144 * X 0 * X 1 ^ 15 * X 2 ^ 3+ 873810 * X 0 * X 1 ^ 14 * X 2 ^ 4- 1592332 * X 0 * X 1 ^ 13 * X 2 ^ 5+ 1941082 * X 0 * X 1 ^ 12 * X 2 ^ 6
    - 1638432 * X 0 * X 1 ^ 11 * X 2 ^ 7+ 975590 * X 0 * X 1 ^ 10 * X 2 ^ 8- 412340 * X 0 * X 1 ^ 9 * X 2 ^ 9+ 122958 * X 0 * X 1 ^ 8 * X 2 ^ 10
    - 25312 * X 0 * X 1 ^ 7 * X 2 ^ 11+ 3430 * X 0 * X 1 ^ 6 * X 2 ^ 12- 276 * X 0 * X 1 ^ 5 * X 2 ^ 13+ 10 * X 0 * X 1 ^ 4 * X 2 ^ 14+ 544 * X 1 ^ 18 * X 2
    - 6928 * X 1 ^ 17 * X 2 ^ 2+ 37768 * X 1 ^ 16 * X 2 ^ 3- 116508 * X 1 ^ 15 * X 2 ^ 4+ 227476 * X 1 ^ 14 * X 2 ^ 5- 298628 * X 1 ^ 13 * X 2 ^ 6
    + 273072 * X 1 ^ 12 * X 2 ^ 7)

def lit22G_7 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-177380 * X 1 ^ 11 * X 2 ^ 8+ 82468 * X 1 ^ 10 * X 2 ^ 9- 27324 * X 1 ^ 9 * X 2 ^ 10+ 6328 * X 1 ^ 8 * X 2 ^ 11- 980 * X 1 ^ 7 * X 2 ^ 12+ 92 * X 1 ^ 6 * X 2 ^ 13
    - 4 * X 1 ^ 5 * X 2 ^ 14)

/-- The full lit22G, a sum of 8 chunks. -/
def lit22G : MvPolynomial (Fin 3) ℤ :=
    lit22G_0 + lit22G_1 + lit22G_2 + lit22G_3 + lit22G_4 + lit22G_5 + lit22G_6 + lit22G_7

def lit22P_0 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 14 * X 1 ^ 4 * X 2+ X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 3+ X 0 ^ 13 * X 1 ^ 5 * X 2+ X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 3+ X 0 ^ 12 * X 1 ^ 6 * X 2+ X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 2
    + X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 3+ X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 4+ X 0 ^ 11 * X 1 ^ 7 * X 2+ X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 3+ X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 3
    + X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 4+ X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 6+ X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 7+ X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 2+ X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 3
    + X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 6+ X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 7+ X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 2+ X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 8+ X 0 ^ 7 * X 1 ^ 11 * X 2
    + X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 12 * X 2+ X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 3)

def lit22P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 8+ X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 10+ X 0 ^ 5 * X 1 ^ 13 * X 2+ X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 2+ X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 3
    + X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 4+ X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 8+ X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 10+ X 0 ^ 4 * X 1 ^ 14 * X 2+ X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 3
    + X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 6+ X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 10+ X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 3+ X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 4+ X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 6
    + X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 7+ X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 8+ X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 10+ X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 3+ X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 7)

/-- The full lit22P, a sum of 2 chunks. -/
def lit22P : Poly2 :=
    lit22P_0 + lit22P_1

set_option maxRecDepth 20000 in
theorem lemma56_nu22_half :
    threeTermNorm (baseSym 5 2) = C 2 * lit22G := by
  unfold lit22G lit22G_0 lit22G_1 lit22G_2 lit22G_3 lit22G_4 lit22G_5 lit22G_6 lit22G_7
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, threeTermNorm]
  ring

set_option maxRecDepth 20000 in
theorem lemma56_nu22_reduce : reduceTwo lit22G = lit22P := by
  unfold lit22G lit22G_0 lit22G_1 lit22G_2 lit22G_3 lit22G_4 lit22G_5 lit22G_6 lit22G_7 lit22P lit22P_0 lit22P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp only [ofNat_mod_poly2]
  ring

open PolynomialReflection in
theorem lemma56_nu22_pi : piOperator lit22P = d7 ^ 2 * (oddGenerator 1) := by
  refine piOperator_eq_of_reflect (lP :=
      [(2, 10, 7), (2, 14, 3), (3, 6, 10), (3, 8, 8), (3, 9, 7), (3, 10, 6), (3, 12, 4),
       (3, 13, 3), (4, 5, 10), (4, 9, 6), (4, 12, 3), (4, 14, 1), (5, 4, 10), (5, 6, 8),
       (5, 10, 4), (5, 11, 3), (5, 12, 2), (5, 13, 1), (6, 3, 10), (6, 5, 8), (6, 10, 3),
       (6, 12, 1), (7, 9, 3), (7, 11, 1), (8, 3, 8), (8, 9, 2), (9, 3, 7), (9, 4, 6), (9, 7, 3),
       (9, 8, 2), (10, 2, 7), (10, 3, 6), (10, 5, 4), (10, 6, 3), (11, 5, 3), (11, 7, 1),
       (12, 3, 4), (12, 4, 3), (12, 5, 2), (12, 6, 1), (13, 3, 3), (13, 5, 1), (14, 2, 3),
       (14, 4, 1)])
    (lQ := mulL (powL d7L 2) (oddGeneratorL 1)) ?_ ?_ ?_
  · unfold lit22P lit22P_0 lit22P_1
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_mulL, ev_powL, ev_d7, ev_oddGenerator]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
