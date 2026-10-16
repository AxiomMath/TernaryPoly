module

public import TernaryPeriodPolynomials.Polynomial.IntegralTaylor.Certificate

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.IntegralTaylorCertificate

private theorem pderiv_numeral (n : ℕ) [n.AtLeastTwo] :
    pderiv 0 (ofNat(n) : Poly) = 0 := by
  simpa only [map_ofNat] using (pderiv_C (i := (0 : Fin 3)) (a := (ofNat(n) : ℤ)))

private def expandedF0Chunk0 (t : Poly) : Poly :=
  (8 : Poly)*t^7*y^2 + (-8 : Poly)*t^7*y*z + (-28 : Poly)*t^6*y^3 + (28 : Poly)*t^6*y^2*z + (-34 : Poly)*t^5*y^4 + (106 : Poly)*t^5*y^3*z + (-90 : Poly)*t^5*y^2*z^2 + (18 : Poly)*t^5*y*z^3

private def expandedF0Chunk1 (t : Poly) : Poly :=
  (155 : Poly)*t^4*y^5 + (-335 : Poly)*t^4*y^4*z + (225 : Poly)*t^4*y^3*z^2 + (-45 : Poly)*t^4*y^2*z^3 + (8 : Poly)*t^3*y^6 + (-200 : Poly)*t^3*y^5*z + (432 : Poly)*t^3*y^4*z^2 + (-336 : Poly)*t^3*y^3*z^3

private def expandedF0Chunk2 (t : Poly) : Poly :=
  (108 : Poly)*t^3*y^2*z^4 + (-12 : Poly)*t^3*y*z^5 + (-181 : Poly)*t^2*y^7 + (649 : Poly)*t^2*y^6*z + (-873 : Poly)*t^2*y^5*z^2 + (549 : Poly)*t^2*y^4*z^3 + (-162 : Poly)*t^2*y^3*z^4 + (18 : Poly)*t^2*y^2*z^5

private def expandedF0Chunk3 (t : Poly) : Poly :=
  (96 : Poly)*t*y^7*z + (-344 : Poly)*t*y^6*z^2 + (488 : Poly)*t*y^5*z^3 + (-350 : Poly)*t*y^4*z^4 + (134 : Poly)*t*y^3*z^5 + (-26 : Poly)*t*y^2*z^6 + (2 : Poly)*t*y*z^7 + (36 : Poly)*y^9

private def expandedF0Chunk4 (_t : Poly) : Poly :=
  (-168 : Poly)*y^8*z + (325 : Poly)*y^7*z^2 + (-337 : Poly)*y^6*z^3 + (202 : Poly)*y^5*z^4 + (-70 : Poly)*y^4*z^5 + (13 : Poly)*y^3*z^6 + (-1 : Poly)*y^2*z^7

private def expandedF0 (t : Poly) : Poly :=
  expandedF0Chunk0 t + expandedF0Chunk1 t + expandedF0Chunk2 t + expandedF0Chunk3 t + expandedF0Chunk4 t

private def expandedF1_0Chunk0 : Poly :=
  (56 : Poly)*x^6*y^2 + (-56 : Poly)*x^6*y*z + (-168 : Poly)*x^5*y^3 + (168 : Poly)*x^5*y^2*z + (-170 : Poly)*x^4*y^4 + (530 : Poly)*x^4*y^3*z + (-450 : Poly)*x^4*y^2*z^2 + (90 : Poly)*x^4*y*z^3

private def expandedF1_0Chunk1 : Poly :=
  (620 : Poly)*x^3*y^5 + (-1340 : Poly)*x^3*y^4*z + (900 : Poly)*x^3*y^3*z^2 + (-180 : Poly)*x^3*y^2*z^3 + (24 : Poly)*x^2*y^6 + (-600 : Poly)*x^2*y^5*z + (1296 : Poly)*x^2*y^4*z^2 + (-1008 : Poly)*x^2*y^3*z^3

private def expandedF1_0Chunk2 : Poly :=
  (324 : Poly)*x^2*y^2*z^4 + (-36 : Poly)*x^2*y*z^5 + (-362 : Poly)*x*y^7 + (1298 : Poly)*x*y^6*z + (-1746 : Poly)*x*y^5*z^2 + (1098 : Poly)*x*y^4*z^3 + (-324 : Poly)*x*y^3*z^4 + (36 : Poly)*x*y^2*z^5

private def expandedF1_0Chunk3 : Poly :=
  (96 : Poly)*y^7*z + (-344 : Poly)*y^6*z^2 + (488 : Poly)*y^5*z^3 + (-350 : Poly)*y^4*z^4 + (134 : Poly)*y^3*z^5 + (-26 : Poly)*y^2*z^6 + (2 : Poly)*y*z^7

private def expandedF1_0 : Poly :=
  expandedF1_0Chunk0 + expandedF1_0Chunk1 + expandedF1_0Chunk2 + expandedF1_0Chunk3

private def expandedF2_0Chunk0 : Poly :=
  (336 : Poly)*x^5*y^2 + (-336 : Poly)*x^5*y*z + (-840 : Poly)*x^4*y^3 + (840 : Poly)*x^4*y^2*z + (-680 : Poly)*x^3*y^4 + (2120 : Poly)*x^3*y^3*z + (-1800 : Poly)*x^3*y^2*z^2 + (360 : Poly)*x^3*y*z^3

private def expandedF2_0Chunk1 : Poly :=
  (1860 : Poly)*x^2*y^5 + (-4020 : Poly)*x^2*y^4*z + (2700 : Poly)*x^2*y^3*z^2 + (-540 : Poly)*x^2*y^2*z^3 + (48 : Poly)*x*y^6 + (-1200 : Poly)*x*y^5*z + (2592 : Poly)*x*y^4*z^2 + (-2016 : Poly)*x*y^3*z^3

private def expandedF2_0Chunk2 : Poly :=
  (648 : Poly)*x*y^2*z^4 + (-72 : Poly)*x*y*z^5 + (-362 : Poly)*y^7 + (1298 : Poly)*y^6*z + (-1746 : Poly)*y^5*z^2 + (1098 : Poly)*y^4*z^3 + (-324 : Poly)*y^3*z^4 + (36 : Poly)*y^2*z^5

private def expandedF2_0 : Poly :=
  expandedF2_0Chunk0 + expandedF2_0Chunk1 + expandedF2_0Chunk2

private def expandedF1Chunk0 (t : Poly) : Poly :=
  (-16 : Poly)*t^7*y^2 + (24 : Poly)*t^7*y*z + (-8 : Poly)*t^7*z^2 + (112 : Poly)*t^6*y^3 + (-112 : Poly)*t^6*y^2*z + (-28 : Poly)*t^6*y*z^2 + (28 : Poly)*t^6*z^3 + (-268 : Poly)*t^5*y^4

private def expandedF1Chunk1 (t : Poly) : Poly :=
  (34 : Poly)*t^5*y^3*z + (342 : Poly)*t^5*y^2*z^2 + (-70 : Poly)*t^5*y*z^3 + (-38 : Poly)*t^5*z^4 + (220 : Poly)*t^4*y^5 + (500 : Poly)*t^4*y^4*z + (-675 : Poly)*t^4*y^3*z^2 + (-225 : Poly)*t^4*y^2*z^3

private def expandedF1Chunk2 (t : Poly) : Poly :=
  (155 : Poly)*t^4*y*z^4 + (25 : Poly)*t^4*z^5 + (104 : Poly)*t^3*y^6 + (-908 : Poly)*t^3*y^5*z + (252 : Poly)*t^3*y^4*z^2 + (744 : Poly)*t^3*y^3*z^3 + (-72 : Poly)*t^3*y^2*z^4 + (-112 : Poly)*t^3*y*z^5

private def expandedF1Chunk3 (t : Poly) : Poly :=
  (-8 : Poly)*t^3*z^6 + (-296 : Poly)*t^2*y^7 + (584 : Poly)*t^2*y^6*z + (414 : Poly)*t^2*y^5*z^2 + (-630 : Poly)*t^2*y^4*z^3 + (-225 : Poly)*t^2*y^3*z^4 + (117 : Poly)*t^2*y^2*z^5 + (35 : Poly)*t^2*y*z^6

private def expandedF1Chunk4 (t : Poly) : Poly :=
  t^2*z^7 + (180 : Poly)*t*y^8 + (-110 : Poly)*t*y^7*z + (-378 : Poly)*t*y^6*z^2 + (126 : Poly)*t*y^5*z^3 + (234 : Poly)*t*y^4*z^4 + (-12 : Poly)*t*y^3*z^5 + (-36 : Poly)*t*y^2*z^6

private def expandedF1Chunk5 (t : Poly) : Poly :=
  (-4 : Poly)*t*y*z^7 + (-36 : Poly)*y^9 + (-12 : Poly)*y^8*z + (81 : Poly)*y^7*z^2 + (27 : Poly)*y^6*z^3 + (-54 : Poly)*y^5*z^4 + (-18 : Poly)*y^4*z^5 + (9 : Poly)*y^3*z^6

private def expandedF1Chunk6 (_t : Poly) : Poly :=
  (3 : Poly)*y^2*z^7

private def expandedF1 (t : Poly) : Poly :=
  expandedF1Chunk0 t + expandedF1Chunk1 t + expandedF1Chunk2 t + expandedF1Chunk3 t + expandedF1Chunk4 t + expandedF1Chunk5 t + expandedF1Chunk6 t

private def expandedF1_1Chunk0 : Poly :=
  (-112 : Poly)*x^6*y^2 + (168 : Poly)*x^6*y*z + (-56 : Poly)*x^6*z^2 + (672 : Poly)*x^5*y^3 + (-672 : Poly)*x^5*y^2*z + (-168 : Poly)*x^5*y*z^2 + (168 : Poly)*x^5*z^3 + (-1340 : Poly)*x^4*y^4

private def expandedF1_1Chunk1 : Poly :=
  (170 : Poly)*x^4*y^3*z + (1710 : Poly)*x^4*y^2*z^2 + (-350 : Poly)*x^4*y*z^3 + (-190 : Poly)*x^4*z^4 + (880 : Poly)*x^3*y^5 + (2000 : Poly)*x^3*y^4*z + (-2700 : Poly)*x^3*y^3*z^2 + (-900 : Poly)*x^3*y^2*z^3

private def expandedF1_1Chunk2 : Poly :=
  (620 : Poly)*x^3*y*z^4 + (100 : Poly)*x^3*z^5 + (312 : Poly)*x^2*y^6 + (-2724 : Poly)*x^2*y^5*z + (756 : Poly)*x^2*y^4*z^2 + (2232 : Poly)*x^2*y^3*z^3 + (-216 : Poly)*x^2*y^2*z^4 + (-336 : Poly)*x^2*y*z^5

private def expandedF1_1Chunk3 : Poly :=
  (-24 : Poly)*x^2*z^6 + (-592 : Poly)*x*y^7 + (1168 : Poly)*x*y^6*z + (828 : Poly)*x*y^5*z^2 + (-1260 : Poly)*x*y^4*z^3 + (-450 : Poly)*x*y^3*z^4 + (234 : Poly)*x*y^2*z^5 + (70 : Poly)*x*y*z^6

private def expandedF1_1Chunk4 : Poly :=
  (2 : Poly)*x*z^7 + (180 : Poly)*y^8 + (-110 : Poly)*y^7*z + (-378 : Poly)*y^6*z^2 + (126 : Poly)*y^5*z^3 + (234 : Poly)*y^4*z^4 + (-12 : Poly)*y^3*z^5 + (-36 : Poly)*y^2*z^6

private def expandedF1_1Chunk5 : Poly :=
  (-4 : Poly)*y*z^7

private def expandedF1_1 : Poly :=
  expandedF1_1Chunk0 + expandedF1_1Chunk1 + expandedF1_1Chunk2 + expandedF1_1Chunk3 + expandedF1_1Chunk4 + expandedF1_1Chunk5

private def expandedF2_1Chunk0 : Poly :=
  (-672 : Poly)*x^5*y^2 + (1008 : Poly)*x^5*y*z + (-336 : Poly)*x^5*z^2 + (3360 : Poly)*x^4*y^3 + (-3360 : Poly)*x^4*y^2*z + (-840 : Poly)*x^4*y*z^2 + (840 : Poly)*x^4*z^3 + (-5360 : Poly)*x^3*y^4

private def expandedF2_1Chunk1 : Poly :=
  (680 : Poly)*x^3*y^3*z + (6840 : Poly)*x^3*y^2*z^2 + (-1400 : Poly)*x^3*y*z^3 + (-760 : Poly)*x^3*z^4 + (2640 : Poly)*x^2*y^5 + (6000 : Poly)*x^2*y^4*z + (-8100 : Poly)*x^2*y^3*z^2 + (-2700 : Poly)*x^2*y^2*z^3

private def expandedF2_1Chunk2 : Poly :=
  (1860 : Poly)*x^2*y*z^4 + (300 : Poly)*x^2*z^5 + (624 : Poly)*x*y^6 + (-5448 : Poly)*x*y^5*z + (1512 : Poly)*x*y^4*z^2 + (4464 : Poly)*x*y^3*z^3 + (-432 : Poly)*x*y^2*z^4 + (-672 : Poly)*x*y*z^5

private def expandedF2_1Chunk3 : Poly :=
  (-48 : Poly)*x*z^6 + (-592 : Poly)*y^7 + (1168 : Poly)*y^6*z + (828 : Poly)*y^5*z^2 + (-1260 : Poly)*y^4*z^3 + (-450 : Poly)*y^3*z^4 + (234 : Poly)*y^2*z^5 + (70 : Poly)*y*z^6

private def expandedF2_1Chunk4 : Poly :=
  (2 : Poly)*z^7

private def expandedF2_1 : Poly :=
  expandedF2_1Chunk0 + expandedF2_1Chunk1 + expandedF2_1Chunk2 + expandedF2_1Chunk3 + expandedF2_1Chunk4

private def expandedF2Chunk0 (t : Poly) : Poly :=
  (8 : Poly)*t^7*y^2 + (-8 : Poly)*t^7*y*z + (-84 : Poly)*t^6*y^3 + (84 : Poly)*t^6*y^2*z + (302 : Poly)*t^5*y^4 + (-230 : Poly)*t^5*y^3*z + (-90 : Poly)*t^5*y^2*z^2 + (18 : Poly)*t^5*y*z^3

private def expandedF2Chunk1 (t : Poly) : Poly :=
  (-375 : Poly)*t^4*y^5 + (-165 : Poly)*t^4*y^4*z + (675 : Poly)*t^4*y^3*z^2 + (-135 : Poly)*t^4*y^2*z^3 + (-112 : Poly)*t^3*y^6 + (1360 : Poly)*t^3*y^5*z + (-1368 : Poly)*t^3*y^4*z^2 + (24 : Poly)*t^3*y^3*z^3

private def expandedF2Chunk2 (t : Poly) : Poly :=
  (108 : Poly)*t^3*y^2*z^4 + (-12 : Poly)*t^3*y*z^5 + (477 : Poly)*t^2*y^7 + (-1233 : Poly)*t^2*y^6*z + (81 : Poly)*t^2*y^5*z^2 + (1107 : Poly)*t^2*y^4*z^3 + (-486 : Poly)*t^2*y^3*z^4 + (54 : Poly)*t^2*y^2*z^5

private def expandedF2Chunk3 (t : Poly) : Poly :=
  (-180 : Poly)*t*y^8 + (-156 : Poly)*t*y^7*z + (1348 : Poly)*t*y^6*z^2 + (-1348 : Poly)*t*y^5*z^3 + (298 : Poly)*t*y^4*z^4 + (62 : Poly)*t*y^3*z^5 + (-26 : Poly)*t*y^2*z^6 + (2 : Poly)*t*y*z^7

private def expandedF2Chunk4 (_t : Poly) : Poly :=
  (180 : Poly)*y^8*z + (-321 : Poly)*y^7*z^2 + (-3 : Poly)*y^6*z^3 + (282 : Poly)*y^5*z^4 + (-174 : Poly)*y^4*z^5 + (39 : Poly)*y^3*z^6 + (-3 : Poly)*y^2*z^7

private def expandedF2 (t : Poly) : Poly :=
  expandedF2Chunk0 t + expandedF2Chunk1 t + expandedF2Chunk2 t + expandedF2Chunk3 t + expandedF2Chunk4 t

private def expandedF1_2Chunk0 : Poly :=
  (56 : Poly)*x^6*y^2 + (-56 : Poly)*x^6*y*z + (-504 : Poly)*x^5*y^3 + (504 : Poly)*x^5*y^2*z + (1510 : Poly)*x^4*y^4 + (-1150 : Poly)*x^4*y^3*z + (-450 : Poly)*x^4*y^2*z^2 + (90 : Poly)*x^4*y*z^3

private def expandedF1_2Chunk1 : Poly :=
  (-1500 : Poly)*x^3*y^5 + (-660 : Poly)*x^3*y^4*z + (2700 : Poly)*x^3*y^3*z^2 + (-540 : Poly)*x^3*y^2*z^3 + (-336 : Poly)*x^2*y^6 + (4080 : Poly)*x^2*y^5*z + (-4104 : Poly)*x^2*y^4*z^2 + (72 : Poly)*x^2*y^3*z^3

private def expandedF1_2Chunk2 : Poly :=
  (324 : Poly)*x^2*y^2*z^4 + (-36 : Poly)*x^2*y*z^5 + (954 : Poly)*x*y^7 + (-2466 : Poly)*x*y^6*z + (162 : Poly)*x*y^5*z^2 + (2214 : Poly)*x*y^4*z^3 + (-972 : Poly)*x*y^3*z^4 + (108 : Poly)*x*y^2*z^5

private def expandedF1_2Chunk3 : Poly :=
  (-180 : Poly)*y^8 + (-156 : Poly)*y^7*z + (1348 : Poly)*y^6*z^2 + (-1348 : Poly)*y^5*z^3 + (298 : Poly)*y^4*z^4 + (62 : Poly)*y^3*z^5 + (-26 : Poly)*y^2*z^6 + (2 : Poly)*y*z^7

private def expandedF1_2 : Poly :=
  expandedF1_2Chunk0 + expandedF1_2Chunk1 + expandedF1_2Chunk2 + expandedF1_2Chunk3

private def expandedF2_2Chunk0 : Poly :=
  (336 : Poly)*x^5*y^2 + (-336 : Poly)*x^5*y*z + (-2520 : Poly)*x^4*y^3 + (2520 : Poly)*x^4*y^2*z + (6040 : Poly)*x^3*y^4 + (-4600 : Poly)*x^3*y^3*z + (-1800 : Poly)*x^3*y^2*z^2 + (360 : Poly)*x^3*y*z^3

private def expandedF2_2Chunk1 : Poly :=
  (-4500 : Poly)*x^2*y^5 + (-1980 : Poly)*x^2*y^4*z + (8100 : Poly)*x^2*y^3*z^2 + (-1620 : Poly)*x^2*y^2*z^3 + (-672 : Poly)*x*y^6 + (8160 : Poly)*x*y^5*z + (-8208 : Poly)*x*y^4*z^2 + (144 : Poly)*x*y^3*z^3

private def expandedF2_2Chunk2 : Poly :=
  (648 : Poly)*x*y^2*z^4 + (-72 : Poly)*x*y*z^5 + (954 : Poly)*y^7 + (-2466 : Poly)*y^6*z + (162 : Poly)*y^5*z^2 + (2214 : Poly)*y^4*z^3 + (-972 : Poly)*y^3*z^4 + (108 : Poly)*y^2*z^5

private def expandedF2_2 : Poly :=
  expandedF2_2Chunk0 + expandedF2_2Chunk1 + expandedF2_2Chunk2

private theorem frameF_expansion0 (t : Poly) : frameF 0 t = expandedF0 t := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, frameF, nineFactor, frame, expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0]
  ring

private theorem frameF_derivative0 : pderiv 0 (frameF 0 x) = expandedF1_0 := by
  rw [frameF_expansion0]
  simp [expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF1_0Chunk0, expandedF1_0Chunk1, expandedF1_0Chunk2, expandedF1_0Chunk3, expandedF1_0, x, y, z, pderiv_numeral]
  ring

private theorem frameF_second_derivative0 : pderiv 0 (expandedF1_0) = expandedF2_0 := by
  simp [expandedF1_0Chunk0, expandedF1_0Chunk1, expandedF1_0Chunk2, expandedF1_0Chunk3, expandedF1_0, expandedF2_0Chunk0, expandedF2_0Chunk1, expandedF2_0Chunk2, expandedF2_0, x, y, z, pderiv_numeral]
  ring

private theorem frameF_expansion1 (t : Poly) : frameF 1 t = expandedF1 t := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, frameF, nineFactor, frame, expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1]
  ring

private theorem frameF_derivative1 : pderiv 0 (frameF 1 x) = expandedF1_1 := by
  rw [frameF_expansion1]
  simp [expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1, expandedF1_1Chunk0, expandedF1_1Chunk1, expandedF1_1Chunk2, expandedF1_1Chunk3, expandedF1_1Chunk4, expandedF1_1Chunk5, expandedF1_1, x, y, z, pderiv_numeral]
  ring

private theorem frameF_second_derivative1 : pderiv 0 (expandedF1_1) = expandedF2_1 := by
  simp [expandedF1_1Chunk0, expandedF1_1Chunk1, expandedF1_1Chunk2, expandedF1_1Chunk3, expandedF1_1Chunk4, expandedF1_1Chunk5, expandedF1_1, expandedF2_1Chunk0, expandedF2_1Chunk1, expandedF2_1Chunk2, expandedF2_1Chunk3, expandedF2_1Chunk4, expandedF2_1, x, y, z, pderiv_numeral]
  ring

private theorem frameF_expansion2 (t : Poly) : frameF 2 t = expandedF2 t := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, frameF, nineFactor, frame, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2]
  ring

private theorem frameF_derivative2 : pderiv 0 (frameF 2 x) = expandedF1_2 := by
  rw [frameF_expansion2]
  simp [expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, x, y, z, pderiv_numeral]
  ring

private theorem frameF_second_derivative2 : pderiv 0 (expandedF1_2) = expandedF2_2 := by
  simp [expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, expandedF2_2Chunk0, expandedF2_2Chunk1, expandedF2_2Chunk2, expandedF2_2, x, y, z, pderiv_numeral]
  ring

def quotient0_0Chunk0 : Poly :=
  (-4 : Poly)*x^7*y^3 + (8 : Poly)*x^7*y^2*z + (-4 : Poly)*x^7*y*z^2 + (28 : Poly)*x^6*y^4 + (-56 : Poly)*x^6*y^3*z + (28 : Poly)*x^6*y^2*z^2 + (-67 : Poly)*x^5*y^5 + (98 : Poly)*x^5*y^4*z

def quotient0_0Chunk1 : Poly :=
  (182 : Poly)*x^5*y^3*z^2 + (-222 : Poly)*x^5*y^2*z^3 + (9 : Poly)*x^5*y*z^4 + (55 : Poly)*x^4*y^6 + (-70 : Poly)*x^4*y^5*z + (-1050 : Poly)*x^4*y^4*z^2 + (1110 : Poly)*x^4*y^3*z^3 + (-45 : Poly)*x^4*y^2*z^4

def quotient0_0Chunk2 : Poly :=
  (26 : Poly)*x^3*y^7 + (244 : Poly)*x^3*y^6*z + (1304 : Poly)*x^3*y^5*z^2 + (-776 : Poly)*x^3*y^4*z^3 + (-1032 : Poly)*x^3*y^3*z^4 + (240 : Poly)*x^3*y^2*z^5 + (-6 : Poly)*x^3*y*z^6 + (-74 : Poly)*x^2*y^8

def quotient0_0Chunk3 : Poly :=
  (-198 : Poly)*x^2*y^7*z + (-550 : Poly)*x^2*y^6*z^2 + (-1662 : Poly)*x^2*y^5*z^3 + (3186 : Poly)*x^2*y^4*z^4 + (-720 : Poly)*x^2*y^3*z^5 + (18 : Poly)*x^2*y^2*z^6 + (45 : Poly)*x*y^9 + (-258 : Poly)*x*y^8*z

def quotient0_0Chunk4 : Poly :=
  (526 : Poly)*x*y^7*z^2 + (1306 : Poly)*x*y^6*z^3 + (-1426 : Poly)*x*y^5*z^4 + (-530 : Poly)*x*y^4*z^5 + (386 : Poly)*x*y^3*z^6 + (-50 : Poly)*x*y^2*z^7 + x*y*z^8 + (-9 : Poly)*y^10

def quotient0_0Chunk5 : Poly :=
  (137 : Poly)*y^9*z + (-137 : Poly)*y^8*z^2 + (-107 : Poly)*y^7*z^3 + (-497 : Poly)*y^6*z^4 + (956 : Poly)*y^5*z^5 + (-392 : Poly)*y^4*z^6 + (50 : Poly)*y^3*z^7 + (-1 : Poly)*y^2*z^8

def quotient0_0 : Poly :=
  quotient0_0Chunk0 + quotient0_0Chunk1 + quotient0_0Chunk2 + quotient0_0Chunk3 + quotient0_0Chunk4 + quotient0_0Chunk5

def quotient0_1Chunk0 : Poly :=
  (-4 : Poly)*x^8*y^4 + (8 : Poly)*x^8*y^3*z + (-4 : Poly)*x^8*y^2*z^2 + (46 : Poly)*x^7*y^5 + (-92 : Poly)*x^7*y^4*z + (-74 : Poly)*x^7*y^3*z^2 + (120 : Poly)*x^7*y^2*z^3 + (-193 : Poly)*x^6*y^6

def quotient0_1Chunk1 : Poly :=
  (546 : Poly)*x^6*y^5*z + (700 : Poly)*x^6*y^4*z^2 + (-1062 : Poly)*x^6*y^3*z^3 + (9 : Poly)*x^6*y^2*z^4 + (338 : Poly)*x^5*y^7 + (-1689 : Poly)*x^5*y^6*z + (-2779 : Poly)*x^5*y^5*z^2 + (3407 : Poly)*x^5*y^4*z^3

def quotient0_1Chunk2 : Poly :=
  (913 : Poly)*x^5*y^3*z^4 + (-198 : Poly)*x^5*y^2*z^5 + (-133 : Poly)*x^4*y^8 + (1806 : Poly)*x^4*y^7*z + (7672 : Poly)*x^4*y^6*z^2 + (-5014 : Poly)*x^4*y^5*z^3 + (-5609 : Poly)*x^4*y^4*z^4 + (1228 : Poly)*x^4*y^3*z^5

def quotient0_1Chunk3 : Poly :=
  (-6 : Poly)*x^4*y^2*z^6 + (-296 : Poly)*x^3*y^9 + (846 : Poly)*x^3*y^8*z + (-12125 : Poly)*x^3*y^7*z^2 + (675 : Poly)*x^3*y^6*z^3 + (12535 : Poly)*x^3*y^5*z^4 + (-1145 : Poly)*x^3*y^4*z^5 + (-726 : Poly)*x^3*y^3*z^6

def quotient0_1Chunk4 : Poly :=
  (84 : Poly)*x^3*y^2*z^7 + (328 : Poly)*x^2*y^10 + (-2266 : Poly)*x^2*y^9*z + (6311 : Poly)*x^2*y^8*z^2 + (9578 : Poly)*x^2*y^7*z^3 + (-13569 : Poly)*x^2*y^6*z^4 + (-2820 : Poly)*x^2*y^5*z^5 + (2541 : Poly)*x^2*y^4*z^6

def quotient0_1Chunk5 : Poly :=
  (-304 : Poly)*x^2*y^3*z^7 + x^2*y^2*z^8 + (-90 : Poly)*x*y^11 + (768 : Poly)*x*y^10*z + (1749 : Poly)*x*y^9*z^2 + (-10712 : Poly)*x*y^8*z^3 + (5245 : Poly)*x*y^7*z^4 + (5244 : Poly)*x*y^6*z^5

def quotient0_1Chunk6 : Poly :=
  (-2407 : Poly)*x*y^5*z^6 + (6 : Poly)*x*y^4*z^7 + (75 : Poly)*x*y^3*z^8 + (-6 : Poly)*x*y^2*z^9 + (18 : Poly)*y^11*z + (-1316 : Poly)*y^10*z^2 + (2366 : Poly)*y^9*z^3 + (817 : Poly)*y^8*z^4

def quotient0_1Chunk7 : Poly :=
  (-2669 : Poly)*y^7*z^5 + (631 : Poly)*y^6*z^6 + (191 : Poly)*y^5*z^7 + (-76 : Poly)*y^4*z^8 + (6 : Poly)*y^3*z^9

def quotient0_1 : Poly :=
  quotient0_1Chunk0 + quotient0_1Chunk1 + quotient0_1Chunk2 + quotient0_1Chunk3 + quotient0_1Chunk4 + quotient0_1Chunk5 + quotient0_1Chunk6 + quotient0_1Chunk7

def quotient0_2Chunk0 : Poly :=
  (8 : Poly)*x^8*y^5 + (-20 : Poly)*x^8*y^4*z + (16 : Poly)*x^8*y^3*z^2 + (-4 : Poly)*x^8*y^2*z^3 + (-92 : Poly)*x^7*y^6 + (230 : Poly)*x^7*y^5*z + (56 : Poly)*x^7*y^4*z^2 + (-314 : Poly)*x^7*y^3*z^3

def quotient0_2Chunk1 : Poly :=
  (120 : Poly)*x^7*y^2*z^4 + (386 : Poly)*x^6*y^7 + (-1285 : Poly)*x^6*y^6*z + (-854 : Poly)*x^6*y^5*z^2 + (2824 : Poly)*x^6*y^4*z^3 + (-1080 : Poly)*x^6*y^3*z^4 + (9 : Poly)*x^6*y^2*z^5 + (-677 : Poly)*x^5*y^8

def quotient0_2Chunk2 : Poly :=
  (3712 : Poly)*x^5*y^7*z + (3863 : Poly)*x^5*y^6*z^2 + (-9597 : Poly)*x^5*y^5*z^3 + (1580 : Poly)*x^5*y^4*z^4 + (1309 : Poly)*x^5*y^3*z^5 + (-198 : Poly)*x^5*y^2*z^6 + (263 : Poly)*x^4*y^9 + (-3761 : Poly)*x^4*y^8*z

def quotient0_2Chunk3 : Poly :=
  (-13572 : Poly)*x^4*y^7*z^2 + (17664 : Poly)*x^4*y^6*z^3 + (6185 : Poly)*x^4*y^5*z^4 + (-8069 : Poly)*x^4*y^4*z^5 + (1240 : Poly)*x^4*y^3*z^6 + (-6 : Poly)*x^4*y^2*z^7 + (589 : Poly)*x^3*y^10 + (-2010 : Poly)*x^3*y^9*z

def quotient0_2Chunk4 : Poly :=
  (25032 : Poly)*x^3*y^8*z^2 + (-13571 : Poly)*x^3*y^7*z^3 + (-24474 : Poly)*x^3*y^6*z^4 + (14791 : Poly)*x^3*y^5*z^5 + (301 : Poly)*x^3*y^4*z^6 + (-894 : Poly)*x^3*y^3*z^7 + (84 : Poly)*x^3*y^2*z^8 + (-657 : Poly)*x^2*y^11

def quotient0_2Chunk5 : Poly :=
  (4848 : Poly)*x^2*y^10*z + (-14938 : Poly)*x^2*y^9*z^2 + (-12949 : Poly)*x^2*y^8*z^3 + (36595 : Poly)*x^2*y^7*z^4 + (-8009 : Poly)*x^2*y^6*z^5 + (-7930 : Poly)*x^2*y^5*z^6 + (3145 : Poly)*x^2*y^4*z^7 + (-306 : Poly)*x^2*y^3*z^8

def quotient0_2Chunk6 : Poly :=
  x^2*y^2*z^9 + (180 : Poly)*x*y^12 + (-1628 : Poly)*x*y^11*z + (-2745 : Poly)*x*y^10*z^2 + (23127 : Poly)*x*y^9*z^3 + (-21277 : Poly)*x*y^8*z^4 + (-5313 : Poly)*x*y^7*z^5 + (10021 : Poly)*x*y^6*z^6

def quotient0_2Chunk7 : Poly :=
  (-2429 : Poly)*x*y^5*z^7 + (-145 : Poly)*x*y^4*z^8 + (87 : Poly)*x*y^3*z^9 + (-6 : Poly)*x*y^2*z^10 + (-36 : Poly)*y^12*z + (2649 : Poly)*y^11*z^2 + (-6054 : Poly)*y^10*z^3 + (717 : Poly)*y^9*z^4

def quotient0_2Chunk8 : Poly :=
  (6135 : Poly)*y^8*z^5 + (-3946 : Poly)*y^7*z^6 + (243 : Poly)*y^6*z^7 + (342 : Poly)*y^5*z^8 + (-88 : Poly)*y^4*z^9 + (6 : Poly)*y^3*z^10

def quotient0_2 : Poly :=
  quotient0_2Chunk0 + quotient0_2Chunk1 + quotient0_2Chunk2 + quotient0_2Chunk3 + quotient0_2Chunk4 + quotient0_2Chunk5 + quotient0_2Chunk6 + quotient0_2Chunk7 + quotient0_2Chunk8

def quotient0_3Chunk0 : Poly :=
  (-8 : Poly)*x^9*y^5 + (16 : Poly)*x^9*y^4*z + (24 : Poly)*x^9*y^3*z^2 + (-32 : Poly)*x^9*y^2*z^3 + (100 : Poly)*x^8*y^6 + (-328 : Poly)*x^8*y^5*z + (-300 : Poly)*x^8*y^4*z^2 + (528 : Poly)*x^8*y^3*z^3

def quotient0_3Chunk1 : Poly :=
  (-478 : Poly)*x^7*y^7 + (2300 : Poly)*x^7*y^6*z + (2500 : Poly)*x^7*y^5*z^2 + (-4052 : Poly)*x^7*y^4*z^3 + (-342 : Poly)*x^7*y^3*z^4 + (72 : Poly)*x^7*y^2*z^5 + (1063 : Poly)*x^6*y^8 + (-6438 : Poly)*x^6*y^7*z

def quotient0_3Chunk2 : Poly :=
  (-14300 : Poly)*x^6*y^6*z^2 + (16462 : Poly)*x^6*y^5*z^3 + (4113 : Poly)*x^6*y^4*z^4 + (-900 : Poly)*x^6*y^3*z^5 + (-940 : Poly)*x^5*y^9 + (6906 : Poly)*x^5*y^8*z + (43794 : Poly)*x^5*y^7*z^2 + (-30842 : Poly)*x^5*y^6*z^3

def quotient0_3Chunk3 : Poly :=
  (-23502 : Poly)*x^5*y^5*z^4 + (4212 : Poly)*x^5*y^4*z^5 + (420 : Poly)*x^5*y^3*z^6 + (-48 : Poly)*x^5*y^2*z^7 + (-326 : Poly)*x^4*y^10 + (887 : Poly)*x^4*y^9*z + (-64121 : Poly)*x^4*y^8*z^2 + (3569 : Poly)*x^4*y^7*z^3

def quotient0_3Chunk4 : Poly :=
  (70401 : Poly)*x^4*y^6*z^4 + (-7320 : Poly)*x^4*y^5*z^5 + (-3498 : Poly)*x^4*y^4*z^6 + (408 : Poly)*x^4*y^3*z^7 + (1246 : Poly)*x^3*y^11 + (-7866 : Poly)*x^3*y^10*z + (36144 : Poly)*x^3*y^9*z^2 + (68448 : Poly)*x^3*y^8*z^3

def quotient0_3Chunk5 : Poly :=
  (-101968 : Poly)*x^3*y^7*z^4 + (-6974 : Poly)*x^3*y^6*z^5 + (12116 : Poly)*x^3*y^5*z^6 + (-1052 : Poly)*x^3*y^4*z^7 + (-102 : Poly)*x^3*y^3*z^8 + (8 : Poly)*x^3*y^2*z^9 + (-837 : Poly)*x^2*y^12 + (5915 : Poly)*x^2*y^11*z

def quotient0_3Chunk6 : Poly :=
  (6034 : Poly)*x^2*y^10*z^2 + (-86283 : Poly)*x^2*y^9*z^3 + (55535 : Poly)*x^2*y^8*z^4 + (37774 : Poly)*x^2*y^7*z^5 + (-19165 : Poly)*x^2*y^6*z^6 + (610 : Poly)*x^2*y^5*z^7 + (453 : Poly)*x^2*y^4*z^8 + (-36 : Poly)*x^2*y^3*z^9

def quotient0_3Chunk7 : Poly :=
  (180 : Poly)*x*y^13 + (-1356 : Poly)*x*y^12*z + (-13192 : Poly)*x*y^11*z^2 + (35600 : Poly)*x*y^10*z^3 + (4222 : Poly)*x*y^9*z^4 + (-37780 : Poly)*x*y^8*z^5 + (11680 : Poly)*x*y^7*z^6 + (1340 : Poly)*x*y^6*z^7

def quotient0_3Chunk8 : Poly :=
  (-754 : Poly)*x*y^5*z^8 + (60 : Poly)*x*y^4*z^9 + (-18 : Poly)*y^13*z + (3243 : Poly)*y^12*z^2 + (-3075 : Poly)*y^11*z^3 + (-8626 : Poly)*y^10*z^4 + (10876 : Poly)*y^9*z^5 + (-1501 : Poly)*y^8*z^6

def quotient0_3Chunk9 : Poly :=
  (-1271 : Poly)*y^7*z^7 + (404 : Poly)*y^6*z^8 + (-32 : Poly)*y^5*z^9

def quotient0_3 : Poly :=
  quotient0_3Chunk0 + quotient0_3Chunk1 + quotient0_3Chunk2 + quotient0_3Chunk3 + quotient0_3Chunk4 + quotient0_3Chunk5 + quotient0_3Chunk6 + quotient0_3Chunk7 + quotient0_3Chunk8 + quotient0_3Chunk9

def quotient0_4Chunk0 : Poly :=
  (16 : Poly)*x^9*y^6 + (-40 : Poly)*x^9*y^5*z + (-32 : Poly)*x^9*y^4*z^2 + (88 : Poly)*x^9*y^3*z^3 + (-32 : Poly)*x^9*y^2*z^4 + (-200 : Poly)*x^8*y^7 + (756 : Poly)*x^8*y^6*z + (272 : Poly)*x^8*y^5*z^2

def quotient0_4Chunk1 : Poly :=
  (-1356 : Poly)*x^8*y^4*z^3 + (528 : Poly)*x^8*y^3*z^4 + (956 : Poly)*x^7*y^8 + (-5078 : Poly)*x^7*y^7*z + (-2700 : Poly)*x^7*y^6*z^2 + (10604 : Poly)*x^7*y^5*z^3 + (-3368 : Poly)*x^7*y^4*z^4 + (-486 : Poly)*x^7*y^3*z^5

def quotient0_4Chunk2 : Poly :=
  (72 : Poly)*x^7*y^2*z^6 + (-2126 : Poly)*x^6*y^9 + (13939 : Poly)*x^6*y^8*z + (22162 : Poly)*x^6*y^7*z^2 + (-47224 : Poly)*x^6*y^6*z^3 + (8236 : Poly)*x^6*y^5*z^4 + (5913 : Poly)*x^6*y^4*z^5 + (-900 : Poly)*x^6*y^3*z^6

def quotient0_4Chunk3 : Poly :=
  (1880 : Poly)*x^5*y^10 + (-14752 : Poly)*x^5*y^9*z + (-80682 : Poly)*x^5*y^8*z^2 + (105478 : Poly)*x^5*y^7*z^3 + (16162 : Poly)*x^5*y^6*z^4 + (-31926 : Poly)*x^5*y^5*z^5 + (3372 : Poly)*x^5*y^4*z^6 + (516 : Poly)*x^5*y^3*z^7

def quotient0_4Chunk4 : Poly :=
  (-48 : Poly)*x^5*y^2*z^8 + (652 : Poly)*x^4*y^11 + (-2100 : Poly)*x^4*y^10*z + (129129 : Poly)*x^4*y^9*z^2 + (-71259 : Poly)*x^4*y^8*z^3 + (-137233 : Poly)*x^4*y^7*z^4 + (85041 : Poly)*x^4*y^6*z^5 + (-324 : Poly)*x^4*y^5*z^6

def quotient0_4Chunk5 : Poly :=
  (-4314 : Poly)*x^4*y^4*z^7 + (408 : Poly)*x^4*y^3*z^8 + (-2492 : Poly)*x^3*y^12 + (16978 : Poly)*x^3*y^11*z + (-80154 : Poly)*x^3*y^10*z^2 + (-100752 : Poly)*x^3*y^9*z^3 + (272384 : Poly)*x^3*y^8*z^4 + (-88020 : Poly)*x^3*y^7*z^5

def quotient0_4Chunk6 : Poly :=
  (-31206 : Poly)*x^3*y^6*z^6 + (14220 : Poly)*x^3*y^5*z^7 + (-848 : Poly)*x^3*y^4*z^8 + (-118 : Poly)*x^3*y^3*z^9 + (8 : Poly)*x^3*y^2*z^10 + (1674 : Poly)*x^2*y^13 + (-12667 : Poly)*x^2*y^12*z + (-6153 : Poly)*x^2*y^11*z^2

def quotient0_4Chunk7 : Poly :=
  (178600 : Poly)*x^2*y^10*z^3 + (-197353 : Poly)*x^2*y^9*z^4 + (-20013 : Poly)*x^2*y^8*z^5 + (76104 : Poly)*x^2*y^7*z^6 + (-20385 : Poly)*x^2*y^6*z^7 + (-296 : Poly)*x^2*y^5*z^8 + (525 : Poly)*x^2*y^4*z^9 + (-36 : Poly)*x^2*y^3*z^10

def quotient0_4Chunk8 : Poly :=
  (-360 : Poly)*x*y^14 + (2892 : Poly)*x*y^13*z + (25028 : Poly)*x*y^12*z^2 + (-84392 : Poly)*x*y^11*z^3 + (27156 : Poly)*x*y^10*z^4 + (79782 : Poly)*x*y^9*z^5 + (-61140 : Poly)*x*y^8*z^6 + (9000 : Poly)*x*y^7*z^7

def quotient0_4Chunk9 : Poly :=
  (2848 : Poly)*x*y^6*z^8 + (-874 : Poly)*x*y^5*z^9 + (60 : Poly)*x*y^4*z^10 + (36 : Poly)*y^14*z + (-6504 : Poly)*y^13*z^2 + (9393 : Poly)*y^12*z^3 + (14177 : Poly)*y^11*z^4 + (-30378 : Poly)*y^10*z^5

def quotient0_4Chunk10 : Poly :=
  (13878 : Poly)*y^9*z^6 + (1041 : Poly)*y^8*z^7 + (-2079 : Poly)*y^7*z^8 + (468 : Poly)*y^6*z^9 + (-32 : Poly)*y^5*z^10

def quotient0_4 : Poly :=
  quotient0_4Chunk0 + quotient0_4Chunk1 + quotient0_4Chunk2 + quotient0_4Chunk3 + quotient0_4Chunk4 + quotient0_4Chunk5 + quotient0_4Chunk6 + quotient0_4Chunk7 + quotient0_4Chunk8 + quotient0_4Chunk9 + quotient0_4Chunk10

def quotient0_5Chunk0 : Poly :=
  (-32 : Poly)*x^9*y^7 + (96 : Poly)*x^9*y^6*z + (24 : Poly)*x^9*y^5*z^2 + (-208 : Poly)*x^9*y^4*z^3 + (152 : Poly)*x^9*y^3*z^4 + (-32 : Poly)*x^9*y^2*z^5 + (400 : Poly)*x^8*y^8 + (-1712 : Poly)*x^8*y^7*z

def quotient0_5Chunk1 : Poly :=
  (212 : Poly)*x^8*y^6*z^2 + (2984 : Poly)*x^8*y^5*z^3 + (-2412 : Poly)*x^8*y^4*z^4 + (528 : Poly)*x^8*y^3*z^5 + (-1912 : Poly)*x^7*y^9 + (11112 : Poly)*x^7*y^8*z + (322 : Poly)*x^7*y^7*z^2 + (-23908 : Poly)*x^7*y^6*z^3

def quotient0_5Chunk2 : Poly :=
  (17340 : Poly)*x^7*y^5*z^4 + (-2396 : Poly)*x^7*y^4*z^5 + (-630 : Poly)*x^7*y^3*z^6 + (72 : Poly)*x^7*y^2*z^7 + (4252 : Poly)*x^6*y^10 + (-30004 : Poly)*x^6*y^9*z + (-30385 : Poly)*x^6*y^8*z^2 + (116610 : Poly)*x^6*y^7*z^3

def quotient0_5Chunk3 : Poly :=
  (-63696 : Poly)*x^6*y^6*z^4 + (-3590 : Poly)*x^6*y^5*z^5 + (7713 : Poly)*x^6*y^4*z^6 + (-900 : Poly)*x^6*y^3*z^7 + (-3760 : Poly)*x^5*y^11 + (31384 : Poly)*x^5*y^10*z + (146612 : Poly)*x^5*y^9*z^2 + (-291638 : Poly)*x^5*y^8*z^3

def quotient0_5Chunk4 : Poly :=
  (73154 : Poly)*x^5*y^7*z^4 + (80014 : Poly)*x^5*y^6*z^5 + (-38670 : Poly)*x^5*y^5*z^6 + (2340 : Poly)*x^5*y^4*z^7 + (612 : Poly)*x^5*y^3*z^8 + (-48 : Poly)*x^5*y^2*z^9 + (-1304 : Poly)*x^4*y^12 + (4852 : Poly)*x^4*y^11*z

def quotient0_5Chunk5 : Poly :=
  (-260358 : Poly)*x^4*y^10*z^2 + (271647 : Poly)*x^4*y^9*z^3 + (203207 : Poly)*x^4*y^8*z^4 + (-307315 : Poly)*x^4*y^7*z^5 + (85689 : Poly)*x^4*y^6*z^6 + (8304 : Poly)*x^4*y^5*z^7 + (-5130 : Poly)*x^4*y^4*z^8 + (408 : Poly)*x^4*y^3*z^9

def quotient0_5Chunk6 : Poly :=
  (4984 : Poly)*x^3*y^13 + (-36448 : Poly)*x^3*y^12*z + (177286 : Poly)*x^3*y^11*z^2 + (121350 : Poly)*x^3*y^10*z^3 + (-645520 : Poly)*x^3*y^9*z^4 + (448424 : Poly)*x^3*y^8*z^5 + (-25608 : Poly)*x^3*y^7*z^6 + (-59646 : Poly)*x^3*y^6*z^7

def quotient0_5Chunk7 : Poly :=
  (15916 : Poly)*x^3*y^5*z^8 + (-612 : Poly)*x^3*y^4*z^9 + (-134 : Poly)*x^3*y^3*z^10 + (8 : Poly)*x^3*y^2*z^11 + (-3348 : Poly)*x^2*y^14 + (27008 : Poly)*x^2*y^13*z + (-361 : Poly)*x^2*y^12*z^2 + (-363353 : Poly)*x^2*y^11*z^3

def quotient0_5Chunk8 : Poly :=
  (573306 : Poly)*x^2*y^10*z^4 + (-157327 : Poly)*x^2*y^9*z^5 + (-172221 : Poly)*x^2*y^8*z^6 + (116874 : Poly)*x^2*y^7*z^7 + (-19793 : Poly)*x^2*y^6*z^8 + (-1346 : Poly)*x^2*y^5*z^9 + (597 : Poly)*x^2*y^4*z^10 + (-36 : Poly)*x^2*y^3*z^11

def quotient0_5Chunk9 : Poly :=
  (720 : Poly)*x*y^15 + (-6144 : Poly)*x*y^14*z + (-47164 : Poly)*x*y^13*z^2 + (193812 : Poly)*x*y^12*z^3 + (-138704 : Poly)*x*y^11*z^4 + (-132408 : Poly)*x*y^10*z^5 + (202062 : Poly)*x*y^9*z^6 + (-79140 : Poly)*x*y^8*z^7

def quotient0_5Chunk10 : Poly :=
  (3304 : Poly)*x*y^7*z^8 + (4596 : Poly)*x*y^6*z^9 + (-994 : Poly)*x*y^5*z^10 + (60 : Poly)*x*y^4*z^11 + (-72 : Poly)*y^15*z + (13044 : Poly)*y^14*z^2 + (-25290 : Poly)*y^13*z^3 + (-18961 : Poly)*y^12*z^4

def quotient0_5Chunk11 : Poly :=
  (74933 : Poly)*y^11*z^5 + (-58134 : Poly)*y^10*z^6 + (11796 : Poly)*y^9*z^7 + (5199 : Poly)*y^8*z^8 + (-3015 : Poly)*y^7*z^9 + (532 : Poly)*y^6*z^10 + (-32 : Poly)*y^5*z^11

def quotient0_5 : Poly :=
  quotient0_5Chunk0 + quotient0_5Chunk1 + quotient0_5Chunk2 + quotient0_5Chunk3 + quotient0_5Chunk4 + quotient0_5Chunk5 + quotient0_5Chunk6 + quotient0_5Chunk7 + quotient0_5Chunk8 + quotient0_5Chunk9 + quotient0_5Chunk10 + quotient0_5Chunk11

def quotient1_0Chunk0 : Poly :=
  (8 : Poly)*x^7*y^3 + (-12 : Poly)*x^7*y^2*z + (4 : Poly)*x^7*y*z^2 + (-56 : Poly)*x^6*y^4 + (84 : Poly)*x^6*y^3*z + (-28 : Poly)*x^6*y^2*z^2 + (134 : Poly)*x^5*y^5 + (-185 : Poly)*x^5*y^4*z

def quotient1_0Chunk1 : Poly :=
  (-87 : Poly)*x^5*y^3*z^2 + (203 : Poly)*x^5*y^2*z^3 + (-65 : Poly)*x^5*y*z^4 + (-110 : Poly)*x^4*y^6 + (85 : Poly)*x^4*y^5*z + (715 : Poly)*x^4*y^4*z^2 + (-735 : Poly)*x^4*y^3*z^3 + (-95 : Poly)*x^4*y^2*z^4

def quotient1_0Chunk2 : Poly :=
  (140 : Poly)*x^4*y*z^5 + (-52 : Poly)*x^3*y^7 + (234 : Poly)*x^3*y^6*z + (-1296 : Poly)*x^3*y^5*z^2 + (388 : Poly)*x^3*y^4*z^3 + (1256 : Poly)*x^3*y^3*z^4 + (-484 : Poly)*x^3*y^2*z^5 + (-46 : Poly)*x^3*y*z^6

def quotient1_0Chunk3 : Poly :=
  (148 : Poly)*x^2*y^8 + (-370 : Poly)*x^2*y^7*z + (804 : Poly)*x^2*y^6*z^2 + (876 : Poly)*x^2*y^5*z^3 + (-1878 : Poly)*x^2*y^4*z^4 + (78 : Poly)*x^2*y^3*z^5 + (404 : Poly)*x^2*y^2*z^6 + (-62 : Poly)*x^2*y*z^7

def quotient1_0Chunk4 : Poly :=
  (-90 : Poly)*x*y^9 + (203 : Poly)*x*y^8*z + (-25 : Poly)*x*y^7*z^2 + (-951 : Poly)*x*y^6*z^3 + (722 : Poly)*x*y^5*z^4 + (634 : Poly)*x*y^4*z^5 + (-494 : Poly)*x*y^3*z^6 + (-54 : Poly)*x*y^2*z^7

def quotient1_0Chunk5 : Poly :=
  (55 : Poly)*x*y*z^8 + (18 : Poly)*y^10 + (-39 : Poly)*y^9*z + (-87 : Poly)*y^8*z^2 + (227 : Poly)*y^7*z^3 + (44 : Poly)*y^6*z^4 + (-332 : Poly)*y^5*z^5 + (83 : Poly)*y^4*z^6

def quotient1_0Chunk6 : Poly :=
  (121 : Poly)*y^3*z^7 + (-22 : Poly)*y^2*z^8 + (-13 : Poly)*y*z^9

def quotient1_0 : Poly :=
  quotient1_0Chunk0 + quotient1_0Chunk1 + quotient1_0Chunk2 + quotient1_0Chunk3 + quotient1_0Chunk4 + quotient1_0Chunk5 + quotient1_0Chunk6

def quotient1_1Chunk0 : Poly :=
  (-8 : Poly)*x^8*y^3*z + (12 : Poly)*x^8*y^2*z^2 + (-4 : Poly)*x^8*y*z^3 + (64 : Poly)*x^7*y^4*z + (-4 : Poly)*x^7*y^3*z^2 + (-106 : Poly)*x^7*y^2*z^3 + (46 : Poly)*x^7*y*z^4 + (-190 : Poly)*x^6*y^5*z

def quotient1_1Chunk1 : Poly :=
  (-375 : Poly)*x^6*y^4*z^2 + (633 : Poly)*x^6*y^3*z^3 + (63 : Poly)*x^6*y^2*z^4 + (-131 : Poly)*x^6*y*z^5 + (244 : Poly)*x^5*y^6*z + (1373 : Poly)*x^5*y^5*z^2 + (-779 : Poly)*x^5*y^4*z^3 + (-1721 : Poly)*x^5*y^3*z^4

def quotient1_1Chunk2 : Poly :=
  (893 : Poly)*x^5*y^2*z^5 + (-14 : Poly)*x^5*y*z^6 + (-58 : Poly)*x^4*y^7*z + (-1924 : Poly)*x^4*y^6*z^2 + (-1039 : Poly)*x^4*y^5*z^3 + (4881 : Poly)*x^4*y^4*z^4 + (-1129 : Poly)*x^4*y^3*z^5 + (-1099 : Poly)*x^4*y^2*z^6

def quotient1_1Chunk3 : Poly :=
  (340 : Poly)*x^4*y*z^7 + (-200 : Poly)*x^3*y^8*z + (978 : Poly)*x^3*y^7*z^2 + (3112 : Poly)*x^3*y^6*z^3 + (-5190 : Poly)*x^3*y^5*z^4 + (-1902 : Poly)*x^3*y^4*z^5 + (3422 : Poly)*x^3*y^3*z^6 + (242 : Poly)*x^3*y^2*z^7

def quotient1_1Chunk4 : Poly :=
  (-538 : Poly)*x^3*y*z^8 + (238 : Poly)*x^2*y^9*z + (253 : Poly)*x^2*y^8*z^2 + (-2561 : Poly)*x^2*y^7*z^3 + (1543 : Poly)*x^2*y^6*z^4 + (4695 : Poly)*x^2*y^5*z^5 + (-2538 : Poly)*x^2*y^4*z^6 + (-2660 : Poly)*x^2*y^3*z^7

def quotient1_1Chunk5 : Poly :=
  (524 : Poly)*x^2*y^2*z^8 + (406 : Poly)*x^2*y*z^9 + (-108 : Poly)*x*y^10*z + (-427 : Poly)*x*y^9*z^2 + (773 : Poly)*x*y^8*z^3 + (713 : Poly)*x*y^7*z^4 + (-3069 : Poly)*x*y^6*z^5 + (-436 : Poly)*x*y^5*z^6

def quotient1_1Chunk6 : Poly :=
  (2313 : Poly)*x*y^4*z^7 + (771 : Poly)*x*y^3*z^8 + (-433 : Poly)*x*y^2*z^9 + (-161 : Poly)*x*y*z^10 + (18 : Poly)*y^11*z + (114 : Poly)*y^10*z^2 + (-45 : Poly)*y^9*z^3 + (-399 : Poly)*y^8*z^4

def quotient1_1Chunk7 : Poly :=
  (551 : Poly)*y^7*z^5 + (573 : Poly)*y^6*z^6 + (-363 : Poly)*y^5*z^7 + (-546 : Poly)*y^4*z^8 + (-52 : Poly)*y^3*z^9 + (106 : Poly)*y^2*z^10 + (27 : Poly)*y*z^11

def quotient1_1 : Poly :=
  quotient1_1Chunk0 + quotient1_1Chunk1 + quotient1_1Chunk2 + quotient1_1Chunk3 + quotient1_1Chunk4 + quotient1_1Chunk5 + quotient1_1Chunk6 + quotient1_1Chunk7

def quotient1_2Chunk0 : Poly :=
  (8 : Poly)*x^8*y^4*z + (-12 : Poly)*x^8*y^3*z^2 + (4 : Poly)*x^8*y^2*z^3 + (-64 : Poly)*x^7*y^5*z + (4 : Poly)*x^7*y^4*z^2 + (106 : Poly)*x^7*y^3*z^3 + (-46 : Poly)*x^7*y^2*z^4 + (190 : Poly)*x^6*y^6*z

def quotient1_2Chunk1 : Poly :=
  (375 : Poly)*x^6*y^5*z^2 + (-633 : Poly)*x^6*y^4*z^3 + (-63 : Poly)*x^6*y^3*z^4 + (131 : Poly)*x^6*y^2*z^5 + (-244 : Poly)*x^5*y^7*z + (-1373 : Poly)*x^5*y^6*z^2 + (778 : Poly)*x^5*y^5*z^3 + (1718 : Poly)*x^5*y^4*z^4

def quotient1_2Chunk2 : Poly :=
  (-896 : Poly)*x^5*y^3*z^5 + (13 : Poly)*x^5*y^2*z^6 + (58 : Poly)*x^4*y^8*z + (1924 : Poly)*x^4*y^7*z^2 + (1034 : Poly)*x^4*y^6*z^3 + (-4898 : Poly)*x^4*y^5*z^4 + (1108 : Poly)*x^4*y^4*z^5 + (1088 : Poly)*x^4*y^3*z^6

def quotient1_2Chunk3 : Poly :=
  (-342 : Poly)*x^4*y^2*z^7 + (200 : Poly)*x^3*y^9*z + (-978 : Poly)*x^3*y^8*z^2 + (-3122 : Poly)*x^3*y^7*z^3 + (5152 : Poly)*x^3*y^6*z^4 + (1847 : Poly)*x^3*y^5*z^5 + (-3459 : Poly)*x^3*y^4*z^6 + (-253 : Poly)*x^3*y^3*z^7

def quotient1_2Chunk4 : Poly :=
  (537 : Poly)*x^3*y^2*z^8 + (-238 : Poly)*x^2*y^10*z + (-253 : Poly)*x^2*y^9*z^2 + (2551 : Poly)*x^2*y^8*z^3 + (-1585 : Poly)*x^2*y^7*z^4 + (-4764 : Poly)*x^2*y^6*z^5 + (2483 : Poly)*x^2*y^5*z^6 + (2639 : Poly)*x^2*y^4*z^7

def quotient1_2Chunk5 : Poly :=
  (-527 : Poly)*x^2*y^3*z^8 + (-406 : Poly)*x^2*y^2*z^9 + (108 : Poly)*x*y^11*z + (427 : Poly)*x*y^10*z^2 + (-778 : Poly)*x*y^9*z^3 + (-736 : Poly)*x*y^8*z^4 + (3027 : Poly)*x*y^7*z^5 + (398 : Poly)*x*y^6*z^6

def quotient1_2Chunk6 : Poly :=
  (-2330 : Poly)*x*y^5*z^7 + (-774 : Poly)*x*y^4*z^8 + (433 : Poly)*x*y^3*z^9 + (161 : Poly)*x*y^2*z^10 + (-18 : Poly)*y^12*z + (-114 : Poly)*y^11*z^2 + (44 : Poly)*y^10*z^3 + (394 : Poly)*y^9*z^4

def quotient1_2Chunk7 : Poly :=
  (-561 : Poly)*y^8*z^5 + (-583 : Poly)*y^7*z^6 + (358 : Poly)*y^6*z^7 + (545 : Poly)*y^5*z^8 + (52 : Poly)*y^4*z^9 + (-106 : Poly)*y^3*z^10 + (-27 : Poly)*y^2*z^11

def quotient1_2 : Poly :=
  quotient1_2Chunk0 + quotient1_2Chunk1 + quotient1_2Chunk2 + quotient1_2Chunk3 + quotient1_2Chunk4 + quotient1_2Chunk5 + quotient1_2Chunk6 + quotient1_2Chunk7

def quotient1_3Chunk0 : Poly :=
  (-16 : Poly)*x^9*y^3*z^2 + (24 : Poly)*x^9*y^2*z^3 + (-8 : Poly)*x^9*y*z^4 + (144 : Poly)*x^8*y^4*z^2 + (-144 : Poly)*x^8*y^3*z^3 + (-36 : Poly)*x^8*y^2*z^4 + (36 : Poly)*x^8*y*z^5 + (-508 : Poly)*x^7*y^5*z^2

def quotient1_3Chunk1 : Poly :=
  (154 : Poly)*x^7*y^4*z^3 + (974 : Poly)*x^7*y^3*z^4 + (-778 : Poly)*x^7*y^2*z^5 + (158 : Poly)*x^7*y*z^6 + (868 : Poly)*x^6*y^6*z^2 + (700 : Poly)*x^6*y^5*z^3 + (-4669 : Poly)*x^6*y^4*z^4 + (2709 : Poly)*x^6*y^3*z^5

def quotient1_3Chunk2 : Poly :=
  (1113 : Poly)*x^6*y^2*z^6 + (-721 : Poly)*x^6*y*z^7 + (-604 : Poly)*x^5*y^7*z^2 + (-2362 : Poly)*x^5*y^6*z^3 + (9866 : Poly)*x^5*y^5*z^4 + (-553 : Poly)*x^5*y^4*z^5 + (-7467 : Poly)*x^5*y^3*z^6 + (-565 : Poly)*x^5*y^2*z^7

def quotient1_3Chunk3 : Poly :=
  (1685 : Poly)*x^5*y*z^8 + (-284 : Poly)*x^4*y^8*z^2 + (3016 : Poly)*x^4*y^7*z^3 + (-9937 : Poly)*x^4*y^6*z^4 + (-10770 : Poly)*x^4*y^5*z^5 + (10490 : Poly)*x^4*y^4*z^6 + (11808 : Poly)*x^4*y^3*z^7 + (-1997 : Poly)*x^4*y^2*z^8

def quotient1_3Chunk4 : Poly :=
  (-2326 : Poly)*x^4*y*z^9 + (876 : Poly)*x^3*y^9*z^2 + (-1786 : Poly)*x^3*y^8*z^3 + (3130 : Poly)*x^3*y^7*z^4 + (19516 : Poly)*x^3*y^6*z^5 + (1434 : Poly)*x^3*y^5*z^6 + (-20149 : Poly)*x^3*y^4*z^7 + (-9023 : Poly)*x^3*y^3*z^8

def quotient1_3Chunk5 : Poly :=
  (3931 : Poly)*x^3*y^2*z^9 + (2071 : Poly)*x^3*y*z^10 + (-692 : Poly)*x^2*y^10*z^2 + (316 : Poly)*x^2*y^9*z^3 + (2449 : Poly)*x^2*y^8*z^4 + (-13839 : Poly)*x^2*y^7*z^5 + (-12313 : Poly)*x^2*y^6*z^6 + (8784 : Poly)*x^2*y^5*z^7

def quotient1_3Chunk6 : Poly :=
  (16536 : Poly)*x^2*y^4*z^8 + (3324 : Poly)*x^2*y^3*z^9 + (-3400 : Poly)*x^2*y^2*z^10 + (-1165 : Poly)*x^2*y*z^11 + (252 : Poly)*x*y^11*z^2 + (130 : Poly)*x*y^10*z^3 + (-2314 : Poly)*x*y^9*z^4 + (3879 : Poly)*x*y^8*z^5

def quotient1_3Chunk7 : Poly :=
  (8011 : Poly)*x*y^7*z^6 + (2606 : Poly)*x*y^6*z^7 + (-7572 : Poly)*x*y^5*z^8 + (-6691 : Poly)*x*y^4*z^9 + (-171 : Poly)*x*y^3*z^10 + (1492 : Poly)*x*y^2*z^11 + (378 : Poly)*x*y*z^12 + (-36 : Poly)*y^12*z^2

def quotient1_3Chunk8 : Poly :=
  (-48 : Poly)*y^11*z^3 + (545 : Poly)*y^10*z^4 + (-200 : Poly)*y^9*z^5 + (-1426 : Poly)*y^8*z^6 + (-1787 : Poly)*y^7*z^7 + (419 : Poly)*y^6*z^8 + (1960 : Poly)*y^5*z^9 + (1056 : Poly)*y^4*z^10

def quotient1_3Chunk9 : Poly :=
  (-159 : Poly)*y^3*z^11 + (-270 : Poly)*y^2*z^12 + (-54 : Poly)*y*z^13

def quotient1_3 : Poly :=
  quotient1_3Chunk0 + quotient1_3Chunk1 + quotient1_3Chunk2 + quotient1_3Chunk3 + quotient1_3Chunk4 + quotient1_3Chunk5 + quotient1_3Chunk6 + quotient1_3Chunk7 + quotient1_3Chunk8 + quotient1_3Chunk9

def quotient1_4Chunk0 : Poly :=
  (16 : Poly)*x^9*y^4*z^2 + (-24 : Poly)*x^9*y^3*z^3 + (8 : Poly)*x^9*y^2*z^4 + (-144 : Poly)*x^8*y^5*z^2 + (144 : Poly)*x^8*y^4*z^3 + (36 : Poly)*x^8*y^3*z^4 + (-36 : Poly)*x^8*y^2*z^5 + (508 : Poly)*x^7*y^6*z^2

def quotient1_4Chunk1 : Poly :=
  (-154 : Poly)*x^7*y^5*z^3 + (-974 : Poly)*x^7*y^4*z^4 + (778 : Poly)*x^7*y^3*z^5 + (-158 : Poly)*x^7*y^2*z^6 + (-868 : Poly)*x^6*y^7*z^2 + (-700 : Poly)*x^6*y^6*z^3 + (4669 : Poly)*x^6*y^5*z^4 + (-2709 : Poly)*x^6*y^4*z^5

def quotient1_4Chunk2 : Poly :=
  (-1113 : Poly)*x^6*y^3*z^6 + (721 : Poly)*x^6*y^2*z^7 + (604 : Poly)*x^5*y^8*z^2 + (2362 : Poly)*x^5*y^7*z^3 + (-9866 : Poly)*x^5*y^6*z^4 + (553 : Poly)*x^5*y^5*z^5 + (7467 : Poly)*x^5*y^4*z^6 + (565 : Poly)*x^5*y^3*z^7

def quotient1_4Chunk3 : Poly :=
  (-1685 : Poly)*x^5*y^2*z^8 + (284 : Poly)*x^4*y^9*z^2 + (-3016 : Poly)*x^4*y^8*z^3 + (9937 : Poly)*x^4*y^7*z^4 + (10770 : Poly)*x^4*y^6*z^5 + (-10490 : Poly)*x^4*y^5*z^6 + (-11808 : Poly)*x^4*y^4*z^7 + (1997 : Poly)*x^4*y^3*z^8

def quotient1_4Chunk4 : Poly :=
  (2326 : Poly)*x^4*y^2*z^9 + (-876 : Poly)*x^3*y^10*z^2 + (1786 : Poly)*x^3*y^9*z^3 + (-3130 : Poly)*x^3*y^8*z^4 + (-19516 : Poly)*x^3*y^7*z^5 + (-1434 : Poly)*x^3*y^6*z^6 + (20149 : Poly)*x^3*y^5*z^7 + (9023 : Poly)*x^3*y^4*z^8

def quotient1_4Chunk5 : Poly :=
  (-3931 : Poly)*x^3*y^3*z^9 + (-2071 : Poly)*x^3*y^2*z^10 + (692 : Poly)*x^2*y^11*z^2 + (-316 : Poly)*x^2*y^10*z^3 + (-2449 : Poly)*x^2*y^9*z^4 + (13839 : Poly)*x^2*y^8*z^5 + (12313 : Poly)*x^2*y^7*z^6 + (-8784 : Poly)*x^2*y^6*z^7

def quotient1_4Chunk6 : Poly :=
  (-16536 : Poly)*x^2*y^5*z^8 + (-3324 : Poly)*x^2*y^4*z^9 + (3400 : Poly)*x^2*y^3*z^10 + (1165 : Poly)*x^2*y^2*z^11 + (-252 : Poly)*x*y^12*z^2 + (-130 : Poly)*x*y^11*z^3 + (2314 : Poly)*x*y^10*z^4 + (-3879 : Poly)*x*y^9*z^5

def quotient1_4Chunk7 : Poly :=
  (-8011 : Poly)*x*y^8*z^6 + (-2606 : Poly)*x*y^7*z^7 + (7572 : Poly)*x*y^6*z^8 + (6691 : Poly)*x*y^5*z^9 + (171 : Poly)*x*y^4*z^10 + (-1492 : Poly)*x*y^3*z^11 + (-378 : Poly)*x*y^2*z^12 + (36 : Poly)*y^13*z^2

def quotient1_4Chunk8 : Poly :=
  (48 : Poly)*y^12*z^3 + (-545 : Poly)*y^11*z^4 + (200 : Poly)*y^10*z^5 + (1426 : Poly)*y^9*z^6 + (1787 : Poly)*y^8*z^7 + (-419 : Poly)*y^7*z^8 + (-1960 : Poly)*y^6*z^9 + (-1056 : Poly)*y^5*z^10

def quotient1_4Chunk9 : Poly :=
  (159 : Poly)*y^4*z^11 + (270 : Poly)*y^3*z^12 + (54 : Poly)*y^2*z^13

def quotient1_4 : Poly :=
  quotient1_4Chunk0 + quotient1_4Chunk1 + quotient1_4Chunk2 + quotient1_4Chunk3 + quotient1_4Chunk4 + quotient1_4Chunk5 + quotient1_4Chunk6 + quotient1_4Chunk7 + quotient1_4Chunk8 + quotient1_4Chunk9

def quotient1_5Chunk0 : Poly :=
  (-16 : Poly)*x^9*y^5*z^2 + (24 : Poly)*x^9*y^4*z^3 + (-8 : Poly)*x^9*y^3*z^4 + (144 : Poly)*x^8*y^6*z^2 + (-144 : Poly)*x^8*y^5*z^3 + (-36 : Poly)*x^8*y^4*z^4 + (36 : Poly)*x^8*y^3*z^5 + (-508 : Poly)*x^7*y^7*z^2

def quotient1_5Chunk1 : Poly :=
  (154 : Poly)*x^7*y^6*z^3 + (974 : Poly)*x^7*y^5*z^4 + (-778 : Poly)*x^7*y^4*z^5 + (158 : Poly)*x^7*y^3*z^6 + (868 : Poly)*x^6*y^8*z^2 + (700 : Poly)*x^6*y^7*z^3 + (-4669 : Poly)*x^6*y^6*z^4 + (2709 : Poly)*x^6*y^5*z^5

def quotient1_5Chunk2 : Poly :=
  (1113 : Poly)*x^6*y^4*z^6 + (-721 : Poly)*x^6*y^3*z^7 + (-604 : Poly)*x^5*y^9*z^2 + (-2362 : Poly)*x^5*y^8*z^3 + (9866 : Poly)*x^5*y^7*z^4 + (-553 : Poly)*x^5*y^6*z^5 + (-7467 : Poly)*x^5*y^5*z^6 + (-565 : Poly)*x^5*y^4*z^7

def quotient1_5Chunk3 : Poly :=
  (1685 : Poly)*x^5*y^3*z^8 + (-284 : Poly)*x^4*y^10*z^2 + (3016 : Poly)*x^4*y^9*z^3 + (-9937 : Poly)*x^4*y^8*z^4 + (-10770 : Poly)*x^4*y^7*z^5 + (10490 : Poly)*x^4*y^6*z^6 + (11808 : Poly)*x^4*y^5*z^7 + (-1997 : Poly)*x^4*y^4*z^8

def quotient1_5Chunk4 : Poly :=
  (-2326 : Poly)*x^4*y^3*z^9 + (876 : Poly)*x^3*y^11*z^2 + (-1786 : Poly)*x^3*y^10*z^3 + (3130 : Poly)*x^3*y^9*z^4 + (19516 : Poly)*x^3*y^8*z^5 + (1434 : Poly)*x^3*y^7*z^6 + (-20149 : Poly)*x^3*y^6*z^7 + (-9023 : Poly)*x^3*y^5*z^8

def quotient1_5Chunk5 : Poly :=
  (3931 : Poly)*x^3*y^4*z^9 + (2071 : Poly)*x^3*y^3*z^10 + (-692 : Poly)*x^2*y^12*z^2 + (316 : Poly)*x^2*y^11*z^3 + (2449 : Poly)*x^2*y^10*z^4 + (-13839 : Poly)*x^2*y^9*z^5 + (-12313 : Poly)*x^2*y^8*z^6 + (8784 : Poly)*x^2*y^7*z^7

def quotient1_5Chunk6 : Poly :=
  (16536 : Poly)*x^2*y^6*z^8 + (3324 : Poly)*x^2*y^5*z^9 + (-3400 : Poly)*x^2*y^4*z^10 + (-1165 : Poly)*x^2*y^3*z^11 + (252 : Poly)*x*y^13*z^2 + (130 : Poly)*x*y^12*z^3 + (-2314 : Poly)*x*y^11*z^4 + (3879 : Poly)*x*y^10*z^5

def quotient1_5Chunk7 : Poly :=
  (8011 : Poly)*x*y^9*z^6 + (2606 : Poly)*x*y^8*z^7 + (-7572 : Poly)*x*y^7*z^8 + (-6691 : Poly)*x*y^6*z^9 + (-171 : Poly)*x*y^5*z^10 + (1492 : Poly)*x*y^4*z^11 + (378 : Poly)*x*y^3*z^12 + (-36 : Poly)*y^14*z^2

def quotient1_5Chunk8 : Poly :=
  (-48 : Poly)*y^13*z^3 + (545 : Poly)*y^12*z^4 + (-200 : Poly)*y^11*z^5 + (-1426 : Poly)*y^10*z^6 + (-1787 : Poly)*y^9*z^7 + (419 : Poly)*y^8*z^8 + (1960 : Poly)*y^7*z^9 + (1056 : Poly)*y^6*z^10

def quotient1_5Chunk9 : Poly :=
  (-159 : Poly)*y^5*z^11 + (-270 : Poly)*y^4*z^12 + (-54 : Poly)*y^3*z^13

def quotient1_5 : Poly :=
  quotient1_5Chunk0 + quotient1_5Chunk1 + quotient1_5Chunk2 + quotient1_5Chunk3 + quotient1_5Chunk4 + quotient1_5Chunk5 + quotient1_5Chunk6 + quotient1_5Chunk7 + quotient1_5Chunk8 + quotient1_5Chunk9

def quotient2_0Chunk0 : Poly :=
  (-4 : Poly)*x^7*y^3 + (4 : Poly)*x^7*y^2*z + (28 : Poly)*x^6*y^4 + (-28 : Poly)*x^6*y^3*z + (-67 : Poly)*x^5*y^5 + (31 : Poly)*x^5*y^4*z + (-39 : Poly)*x^5*y^3*z^2 + (75 : Poly)*x^5*y^2*z^3

def quotient2_0Chunk1 : Poly :=
  (55 : Poly)*x^4*y^6 + (125 : Poly)*x^4*y^5*z + (195 : Poly)*x^4*y^4*z^2 + (-375 : Poly)*x^4*y^3*z^3 + (26 : Poly)*x^3*y^7 + (-290 : Poly)*x^3*y^6*z + (-436 : Poly)*x^3*y^5*z^2 + (388 : Poly)*x^3*y^4*z^3

def quotient2_0Chunk2 : Poly :=
  (256 : Poly)*x^3*y^3*z^4 + (56 : Poly)*x^3*y^2*z^5 + (-74 : Poly)*x^2*y^8 + (146 : Poly)*x^2*y^7*z + (528 : Poly)*x^2*y^6*z^2 + (336 : Poly)*x^2*y^5*z^3 + (-768 : Poly)*x^2*y^4*z^4 + (-168 : Poly)*x^2*y^3*z^5

def quotient2_0Chunk3 : Poly :=
  (45 : Poly)*x*y^9 + (15 : Poly)*x*y^8*z + (-173 : Poly)*x*y^7*z^2 + (-655 : Poly)*x*y^6*z^3 + (380 : Poly)*x*y^5*z^4 + (340 : Poly)*x*y^4*z^5 + (48 : Poly)*x*y^3*z^6 + (-9 : Poly)*y^10

def quotient2_0Chunk4 : Poly :=
  (-3 : Poly)*y^9*z + (-75 : Poly)*y^8*z^2 + (231 : Poly)*y^7*z^3 + (132 : Poly)*y^6*z^4 + (-228 : Poly)*y^5*z^5 + (-48 : Poly)*y^4*z^6

def quotient2_0 : Poly :=
  quotient2_0Chunk0 + quotient2_0Chunk1 + quotient2_0Chunk2 + quotient2_0Chunk3 + quotient2_0Chunk4

def quotient2_1Chunk0 : Poly :=
  (-4 : Poly)*x^8*y^4 + (-4 : Poly)*x^8*y^3*z + (8 : Poly)*x^8*y^2*z^2 + (46 : Poly)*x^7*y^5 + (14 : Poly)*x^7*y^4*z + (-4 : Poly)*x^7*y^3*z^2 + (-56 : Poly)*x^7*y^2*z^3 + (-193 : Poly)*x^6*y^6

def quotient2_1Chunk1 : Poly :=
  (-5 : Poly)*x^6*y^5*z + (-341 : Poly)*x^6*y^4*z^2 + (389 : Poly)*x^6*y^3*z^3 + (150 : Poly)*x^6*y^2*z^4 + (338 : Poly)*x^5*y^7 + (143 : Poly)*x^5*y^6*z + (1639 : Poly)*x^5*y^5*z^2 + (-939 : Poly)*x^5*y^4*z^3

def quotient2_1Chunk2 : Poly :=
  (-995 : Poly)*x^5*y^3*z^4 + (-190 : Poly)*x^5*y^2*z^5 + (-133 : Poly)*x^4*y^8 + (-770 : Poly)*x^4*y^7*z + (-3358 : Poly)*x^4*y^6*z^2 + (362 : Poly)*x^4*y^5*z^3 + (2257 : Poly)*x^4*y^4*z^4 + (1518 : Poly)*x^4*y^3*z^5

def quotient2_1Chunk3 : Poly :=
  (112 : Poly)*x^4*y^2*z^6 + (-296 : Poly)*x^3*y^9 + (1118 : Poly)*x^3*y^8*z + (3302 : Poly)*x^3*y^7*z^2 + (2864 : Poly)*x^3*y^6*z^3 + (-2038 : Poly)*x^3*y^5*z^4 + (-4138 : Poly)*x^3*y^4*z^5 + (-800 : Poly)*x^3*y^3*z^6

def quotient2_1Chunk4 : Poly :=
  (-24 : Poly)*x^3*y^2*z^7 + (328 : Poly)*x^2*y^10 + (-376 : Poly)*x^2*y^9*z + (-1166 : Poly)*x^2*y^8*z^2 + (-5676 : Poly)*x^2*y^7*z^3 + (-4 : Poly)*x^2*y^6*z^4 + (4602 : Poly)*x^2*y^5*z^5 + (2120 : Poly)*x^2*y^4*z^6

def quotient2_1Chunk5 : Poly :=
  (168 : Poly)*x^2*y^3*z^7 + (-90 : Poly)*x*y^11 + (-231 : Poly)*x*y^10*z + (-308 : Poly)*x*y^9*z^2 + (3502 : Poly)*x*y^8*z^3 + (1710 : Poly)*x*y^7*z^4 + (-1963 : Poly)*x*y^6*z^5 + (-2296 : Poly)*x*y^5*z^6

def quotient2_1Chunk6 : Poly :=
  (-324 : Poly)*x*y^4*z^7 + (99 : Poly)*y^11*z + (216 : Poly)*y^10*z^2 + (-450 : Poly)*y^9*z^3 + (-1080 : Poly)*y^8*z^4 + (171 : Poly)*y^7*z^5 + (864 : Poly)*y^6*z^6 + (180 : Poly)*y^5*z^7

def quotient2_1 : Poly :=
  quotient2_1Chunk0 + quotient2_1Chunk1 + quotient2_1Chunk2 + quotient2_1Chunk3 + quotient2_1Chunk4 + quotient2_1Chunk5 + quotient2_1Chunk6

def quotient2_2Chunk0 : Poly :=
  (8 : Poly)*x^8*y^5 + (4 : Poly)*x^8*y^4*z + (-20 : Poly)*x^8*y^3*z^2 + (8 : Poly)*x^8*y^2*z^3 + (-92 : Poly)*x^7*y^6 + (18 : Poly)*x^7*y^5*z + (22 : Poly)*x^7*y^4*z^2 + (108 : Poly)*x^7*y^3*z^3

def quotient2_2Chunk1 : Poly :=
  (-56 : Poly)*x^7*y^2*z^4 + (386 : Poly)*x^6*y^7 + (-183 : Poly)*x^6*y^6*z + (677 : Poly)*x^6*y^5*z^2 + (-1119 : Poly)*x^6*y^4*z^3 + (89 : Poly)*x^6*y^3*z^4 + (150 : Poly)*x^6*y^2*z^5 + (-677 : Poly)*x^5*y^8

def quotient2_2Chunk2 : Poly :=
  (49 : Poly)*x^5*y^7*z + (-3138 : Poly)*x^5*y^6*z^2 + (3516 : Poly)*x^5*y^5*z^3 + (1051 : Poly)*x^5*y^4*z^4 + (-615 : Poly)*x^5*y^3*z^5 + (-190 : Poly)*x^5*y^2*z^6 + (263 : Poly)*x^4*y^9 + (1398 : Poly)*x^4*y^8*z

def quotient2_2Chunk3 : Poly :=
  (5937 : Poly)*x^4*y^7*z^2 + (-4085 : Poly)*x^4*y^6*z^3 + (-4152 : Poly)*x^4*y^5*z^4 + (-779 : Poly)*x^4*y^4*z^5 + (1294 : Poly)*x^4*y^3*z^6 + (112 : Poly)*x^4*y^2*z^7 + (589 : Poly)*x^3*y^10 + (-2541 : Poly)*x^3*y^9*z

def quotient2_2Chunk4 : Poly :=
  (-5495 : Poly)*x^3*y^8*z^2 + (-2429 : Poly)*x^3*y^7*z^3 + (6940 : Poly)*x^3*y^6*z^4 + (6238 : Poly)*x^3*y^5*z^5 + (-2538 : Poly)*x^3*y^4*z^6 + (-752 : Poly)*x^3*y^3*z^7 + (-24 : Poly)*x^3*y^2*z^8 + (-657 : Poly)*x^2*y^11

def quotient2_2Chunk5 : Poly :=
  (1077 : Poly)*x^2*y^10*z + (1953 : Poly)*x^2*y^9*z^2 + (10185 : Poly)*x^2*y^8*z^3 + (-5668 : Poly)*x^2*y^7*z^4 + (-9208 : Poly)*x^2*y^6*z^5 + (362 : Poly)*x^2*y^5*z^6 + (1784 : Poly)*x^2*y^4*z^7 + (168 : Poly)*x^2*y^3*z^8

def quotient2_2Chunk6 : Poly :=
  (180 : Poly)*x*y^12 + (372 : Poly)*x*y^11*z + (385 : Poly)*x*y^10*z^2 + (-7312 : Poly)*x*y^9*z^3 + (82 : Poly)*x*y^8*z^4 + (5636 : Poly)*x*y^7*z^5 + (2629 : Poly)*x*y^6*z^6 + (-1648 : Poly)*x*y^5*z^7

def quotient2_2Chunk7 : Poly :=
  (-324 : Poly)*x*y^4*z^8 + (-198 : Poly)*y^12*z + (-333 : Poly)*y^11*z^2 + (1116 : Poly)*y^10*z^3 + (1710 : Poly)*y^9*z^4 + (-1422 : Poly)*y^8*z^5 + (-1557 : Poly)*y^7*z^6 + (504 : Poly)*y^6*z^7

def quotient2_2Chunk8 : Poly :=
  (180 : Poly)*y^5*z^8

def quotient2_2 : Poly :=
  quotient2_2Chunk0 + quotient2_2Chunk1 + quotient2_2Chunk2 + quotient2_2Chunk3 + quotient2_2Chunk4 + quotient2_2Chunk5 + quotient2_2Chunk6 + quotient2_2Chunk7 + quotient2_2Chunk8

def quotient2_3Chunk0 : Poly :=
  (-8 : Poly)*x^9*y^5 + (-8 : Poly)*x^9*y^4*z + (-16 : Poly)*x^9*y^3*z^2 + (32 : Poly)*x^9*y^2*z^3 + (100 : Poly)*x^8*y^6 + (92 : Poly)*x^8*y^5*z + (192 : Poly)*x^8*y^4*z^2 + (-160 : Poly)*x^8*y^3*z^3

def quotient2_3Chunk1 : Poly :=
  (-224 : Poly)*x^8*y^2*z^4 + (-478 : Poly)*x^7*y^7 + (-458 : Poly)*x^7*y^6*z + (-1598 : Poly)*x^7*y^5*z^2 + (266 : Poly)*x^7*y^4*z^3 + (1668 : Poly)*x^7*y^3*z^4 + (600 : Poly)*x^7*y^2*z^5 + (1063 : Poly)*x^6*y^8

def quotient2_3Chunk2 : Poly :=
  (1361 : Poly)*x^6*y^7*z + (7809 : Poly)*x^6*y^6*z^2 + (203 : Poly)*x^6*y^5*z^3 + (-4716 : Poly)*x^6*y^4*z^4 + (-4960 : Poly)*x^6*y^3*z^5 + (-760 : Poly)*x^6*y^2*z^6 + (-940 : Poly)*x^5*y^9 + (-2663 : Poly)*x^5*y^8*z

def quotient2_3Chunk3 : Poly :=
  (-19667 : Poly)*x^5*y^7*z^2 + (-5947 : Poly)*x^5*y^6*z^3 + (5407 : Poly)*x^5*y^5*z^4 + (16910 : Poly)*x^5*y^4*z^5 + (6452 : Poly)*x^5*y^3*z^6 + (448 : Poly)*x^5*y^2*z^7 + (-326 : Poly)*x^4*y^10 + (3203 : Poly)*x^4*y^9*z

def quotient2_3Chunk4 : Poly :=
  (23963 : Poly)*x^4*y^8*z^2 + (25199 : Poly)*x^4*y^7*z^3 + (4103 : Poly)*x^4*y^6*z^4 + (-30922 : Poly)*x^4*y^5*z^5 + (-21428 : Poly)*x^4*y^4*z^6 + (-3696 : Poly)*x^4*y^3*z^7 + (-96 : Poly)*x^4*y^2*z^8 + (1246 : Poly)*x^3*y^11

def quotient2_3Chunk5 : Poly :=
  (-1767 : Poly)*x^3*y^10*z + (-10479 : Poly)*x^3*y^9*z^2 + (-43991 : Poly)*x^3*y^8*z^3 + (-22855 : Poly)*x^3*y^7*z^4 + (28650 : Poly)*x^3*y^6*z^5 + (36900 : Poly)*x^3*y^5*z^6 + (11576 : Poly)*x^3*y^4*z^7 + (720 : Poly)*x^3*y^3*z^8

def quotient2_3Chunk6 : Poly :=
  (-837 : Poly)*x^2*y^12 + (-276 : Poly)*x^2*y^11*z + (-3590 : Poly)*x^2*y^10*z^2 + (34092 : Poly)*x^2*y^9*z^3 + (30747 : Poly)*x^2*y^8*z^4 + (-5656 : Poly)*x^2*y^7*z^5 + (-35472 : Poly)*x^2*y^6*z^6 + (-17184 : Poly)*x^2*y^5*z^7

def quotient2_3Chunk7 : Poly :=
  (-1824 : Poly)*x^2*y^4*z^8 + (180 : Poly)*x*y^13 + (696 : Poly)*x*y^12*z + (4280 : Poly)*x*y^11*z^2 + (-9670 : Poly)*x*y^10*z^3 + (-18438 : Poly)*x*y^9*z^4 + (-8522 : Poly)*x*y^8*z^5 + (17074 : Poly)*x*y^7*z^6

def quotient2_3Chunk8 : Poly :=
  (12552 : Poly)*x*y^6*z^7 + (1848 : Poly)*x*y^5*z^8 + (-180 : Poly)*y^13*z + (-894 : Poly)*y^12*z^2 + (-24 : Poly)*y^11*z^3 + (4308 : Poly)*y^10*z^4 + (3900 : Poly)*y^9*z^5 + (-2766 : Poly)*y^8*z^6

def quotient2_3Chunk9 : Poly :=
  (-3696 : Poly)*y^7*z^7 + (-648 : Poly)*y^6*z^8

def quotient2_3 : Poly :=
  quotient2_3Chunk0 + quotient2_3Chunk1 + quotient2_3Chunk2 + quotient2_3Chunk3 + quotient2_3Chunk4 + quotient2_3Chunk5 + quotient2_3Chunk6 + quotient2_3Chunk7 + quotient2_3Chunk8 + quotient2_3Chunk9

def quotient2_4Chunk0 : Poly :=
  (16 : Poly)*x^9*y^6 + (8 : Poly)*x^9*y^5*z + (24 : Poly)*x^9*y^4*z^2 + (-80 : Poly)*x^9*y^3*z^3 + (32 : Poly)*x^9*y^2*z^4 + (-200 : Poly)*x^8*y^7 + (-84 : Poly)*x^8*y^6*z + (-292 : Poly)*x^8*y^5*z^2

def quotient2_4Chunk1 : Poly :=
  (512 : Poly)*x^8*y^4*z^3 + (288 : Poly)*x^8*y^3*z^4 + (-224 : Poly)*x^8*y^2*z^5 + (956 : Poly)*x^7*y^8 + (438 : Poly)*x^7*y^7*z + (2738 : Poly)*x^7*y^6*z^2 + (-2130 : Poly)*x^7*y^5*z^3 + (-3070 : Poly)*x^7*y^4*z^4

def quotient2_4Chunk2 : Poly :=
  (468 : Poly)*x^7*y^3*z^5 + (600 : Poly)*x^7*y^2*z^6 + (-2126 : Poly)*x^6*y^9 + (-1659 : Poly)*x^6*y^8*z + (-14257 : Poly)*x^6*y^7*z^2 + (7403 : Poly)*x^6*y^6*z^3 + (9635 : Poly)*x^6*y^5*z^4 + (5204 : Poly)*x^6*y^4*z^5

def quotient2_4Chunk3 : Poly :=
  (-3440 : Poly)*x^6*y^3*z^6 + (-760 : Poly)*x^6*y^2*z^7 + (1880 : Poly)*x^5*y^10 + (4386 : Poly)*x^5*y^9*z + (36671 : Poly)*x^5*y^8*z^2 + (-7773 : Poly)*x^5*y^7*z^3 + (-16761 : Poly)*x^5*y^6*z^4 + (-28413 : Poly)*x^5*y^5*z^5

def quotient2_4Chunk4 : Poly :=
  (4006 : Poly)*x^5*y^4*z^6 + (5556 : Poly)*x^5*y^3*z^7 + (448 : Poly)*x^5*y^2*z^8 + (652 : Poly)*x^4*y^11 + (-6732 : Poly)*x^4*y^10*z + (-44723 : Poly)*x^4*y^9*z^2 + (-26435 : Poly)*x^4*y^8*z^3 + (16993 : Poly)*x^4*y^7*z^4

def quotient2_4Chunk5 : Poly :=
  (65947 : Poly)*x^4*y^6*z^5 + (11934 : Poly)*x^4*y^5*z^6 + (-14036 : Poly)*x^4*y^4*z^7 + (-3504 : Poly)*x^4*y^3*z^8 + (-96 : Poly)*x^4*y^2*z^9 + (-2492 : Poly)*x^3*y^12 + (4780 : Poly)*x^3*y^11*z + (19191 : Poly)*x^3*y^10*z^2

def quotient2_4Chunk6 : Poly :=
  (77503 : Poly)*x^3*y^9*z^3 + (1719 : Poly)*x^3*y^8*z^4 + (-80155 : Poly)*x^3*y^7*z^5 + (-45150 : Poly)*x^3*y^6*z^6 + (13748 : Poly)*x^3*y^5*z^7 + (10136 : Poly)*x^3*y^4*z^8 + (720 : Poly)*x^3*y^3*z^9 + (1674 : Poly)*x^2*y^13

def quotient2_4Chunk7 : Poly :=
  (-285 : Poly)*x^2*y^12*z + (6904 : Poly)*x^2*y^11*z^2 + (-71774 : Poly)*x^2*y^10*z^3 + (-27402 : Poly)*x^2*y^9*z^4 + (42059 : Poly)*x^2*y^8*z^5 + (65288 : Poly)*x^2*y^7*z^6 + (-1104 : Poly)*x^2*y^6*z^7 + (-13536 : Poly)*x^2*y^5*z^8

def quotient2_4Chunk8 : Poly :=
  (-1824 : Poly)*x^2*y^4*z^9 + (-360 : Poly)*x*y^14 + (-1212 : Poly)*x*y^13*z + (-7864 : Poly)*x*y^12*z^2 + (23620 : Poly)*x*y^11*z^3 + (27206 : Poly)*x*y^10*z^4 + (-1394 : Poly)*x*y^9*z^5 + (-42670 : Poly)*x*y^8*z^6

def quotient2_4Chunk9 : Poly :=
  (-8030 : Poly)*x*y^7*z^7 + (8856 : Poly)*x*y^6*z^8 + (1848 : Poly)*x*y^5*z^9 + (360 : Poly)*y^14*z + (1608 : Poly)*y^13*z^2 + (-846 : Poly)*y^12*z^3 + (-8640 : Poly)*y^11*z^4 + (-3492 : Poly)*y^10*z^5

def quotient2_4Chunk10 : Poly :=
  (9432 : Poly)*y^9*z^6 + (4626 : Poly)*y^8*z^7 + (-2400 : Poly)*y^7*z^8 + (-648 : Poly)*y^6*z^9

def quotient2_4 : Poly :=
  quotient2_4Chunk0 + quotient2_4Chunk1 + quotient2_4Chunk2 + quotient2_4Chunk3 + quotient2_4Chunk4 + quotient2_4Chunk5 + quotient2_4Chunk6 + quotient2_4Chunk7 + quotient2_4Chunk8 + quotient2_4Chunk9 + quotient2_4Chunk10

def quotient2_5Chunk0 : Poly :=
  (-32 : Poly)*x^9*y^7 + (-40 : Poly)*x^9*y^5*z^2 + (184 : Poly)*x^9*y^4*z^3 + (-144 : Poly)*x^9*y^3*z^4 + (32 : Poly)*x^9*y^2*z^5 + (400 : Poly)*x^8*y^8 + (-32 : Poly)*x^8*y^7*z + (500 : Poly)*x^8*y^6*z^2

def quotient2_5Chunk1 : Poly :=
  (-1316 : Poly)*x^8*y^5*z^3 + (-64 : Poly)*x^8*y^4*z^4 + (736 : Poly)*x^8*y^3*z^5 + (-224 : Poly)*x^8*y^2*z^6 + (-1912 : Poly)*x^7*y^9 + (80 : Poly)*x^7*y^8*z + (-5038 : Poly)*x^7*y^7*z^2 + (6998 : Poly)*x^7*y^6*z^3

def quotient2_5Chunk2 : Poly :=
  (4010 : Poly)*x^7*y^5*z^4 + (-4006 : Poly)*x^7*y^4*z^5 + (-732 : Poly)*x^7*y^3*z^6 + (600 : Poly)*x^7*y^2*z^7 + (4252 : Poly)*x^6*y^10 + (1192 : Poly)*x^6*y^9*z + (26855 : Poly)*x^6*y^8*z^2 + (-29063 : Poly)*x^6*y^7*z^3

def quotient2_5Chunk3 : Poly :=
  (-11867 : Poly)*x^6*y^6*z^4 + (-773 : Poly)*x^6*y^5*z^5 + (12084 : Poly)*x^6*y^4*z^6 + (-1920 : Poly)*x^6*y^3*z^7 + (-760 : Poly)*x^6*y^2*z^8 + (-3760 : Poly)*x^5*y^11 + (-6892 : Poly)*x^5*y^10*z + (-68956 : Poly)*x^5*y^9*z^2

def quotient2_5Chunk4 : Poly :=
  (52217 : Poly)*x^5*y^8*z^3 + (25749 : Poly)*x^5*y^7*z^4 + (40065 : Poly)*x^5*y^6*z^5 + (-36425 : Poly)*x^5*y^5*z^6 + (-7106 : Poly)*x^5*y^4*z^7 + (4660 : Poly)*x^5*y^3*z^8 + (448 : Poly)*x^5*y^2*z^9 + (-1304 : Poly)*x^4*y^12

def quotient2_5Chunk5 : Poly :=
  (14116 : Poly)*x^4*y^11*z + (82714 : Poly)*x^4*y^10*z^2 + (8147 : Poly)*x^4*y^9*z^3 + (-60421 : Poly)*x^4*y^8*z^4 + (-114901 : Poly)*x^4*y^7*z^5 + (42079 : Poly)*x^4*y^6*z^6 + (40006 : Poly)*x^4*y^5*z^7 + (-7028 : Poly)*x^4*y^4*z^8

def quotient2_5Chunk6 : Poly :=
  (-3312 : Poly)*x^4*y^3*z^9 + (-96 : Poly)*x^4*y^2*z^10 + (4984 : Poly)*x^3*y^13 + (-12052 : Poly)*x^3*y^12*z + (-33602 : Poly)*x^3*y^11*z^2 + (-135815 : Poly)*x^3*y^10*z^3 + (74065 : Poly)*x^3*y^9*z^4 + (162029 : Poly)*x^3*y^8*z^5

def quotient2_5Chunk7 : Poly :=
  (10145 : Poly)*x^3*y^7*z^6 + (-72646 : Poly)*x^3*y^6*z^7 + (-6524 : Poly)*x^3*y^5*z^8 + (8696 : Poly)*x^3*y^4*z^9 + (720 : Poly)*x^3*y^3*z^10 + (-3348 : Poly)*x^2*y^14 + (2244 : Poly)*x^2*y^13*z + (-14093 : Poly)*x^2*y^12*z^2

def quotient2_5Chunk8 : Poly :=
  (150452 : Poly)*x^2*y^11*z^3 + (-16970 : Poly)*x^2*y^10*z^4 + (-111520 : Poly)*x^2*y^9*z^5 + (-88517 : Poly)*x^2*y^8*z^6 + (67496 : Poly)*x^2*y^7*z^7 + (25968 : Poly)*x^2*y^6*z^8 + (-9888 : Poly)*x^2*y^5*z^9 + (-1824 : Poly)*x^2*y^4*z^10

def quotient2_5Chunk9 : Poly :=
  (720 : Poly)*x*y^15 + (2064 : Poly)*x*y^14*z + (14516 : Poly)*x*y^13*z^2 + (-55104 : Poly)*x*y^12*z^3 + (-30792 : Poly)*x*y^11*z^4 + (29994 : Poly)*x*y^10*z^5 + (83946 : Poly)*x*y^9*z^6 + (-26610 : Poly)*x*y^8*z^7

def quotient2_5Chunk10 : Poly :=
  (-25742 : Poly)*x*y^7*z^8 + (5160 : Poly)*x*y^6*z^9 + (1848 : Poly)*x*y^5*z^10 + (-720 : Poly)*y^15*z + (-2856 : Poly)*y^14*z^2 + (3300 : Poly)*y^13*z^3 + (16434 : Poly)*y^12*z^4 + (-1656 : Poly)*y^11*z^5

def quotient2_5Chunk11 : Poly :=
  (-22356 : Poly)*y^10*z^6 + (180 : Poly)*y^9*z^7 + (9426 : Poly)*y^8*z^8 + (-1104 : Poly)*y^7*z^9 + (-648 : Poly)*y^6*z^10

def quotient2_5 : Poly :=
  quotient2_5Chunk0 + quotient2_5Chunk1 + quotient2_5Chunk2 + quotient2_5Chunk3 + quotient2_5Chunk4 + quotient2_5Chunk5 + quotient2_5Chunk6 + quotient2_5Chunk7 + quotient2_5Chunk8 + quotient2_5Chunk9 + quotient2_5Chunk10 + quotient2_5Chunk11

/-- Explicit integer quotients in the finite eighteen-entry certificate. -/
def certificateQuotient : Fin 3 → Fin 6 → Poly :=
  ![![quotient0_0, quotient0_1, quotient0_2, quotient0_3, quotient0_4, quotient0_5],
    ![quotient1_0, quotient1_1, quotient1_2, quotient1_3, quotient1_4, quotient1_5],
    ![quotient2_0, quotient2_1, quotient2_2, quotient2_3, quotient2_4, quotient2_5]]

theorem certificate_0_0 : localCoeff 0 (jetI 0) (jetJ 0) =
    4*expected 0 0+8*certificateQuotient 0 0 := by
  change localCoeff 0 0 0 = 4*((0 : Poly))+8*quotient0_0
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative0, frameF_derivative2,
    frameF_second_derivative0, frameF_second_derivative2,
    IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF1_0Chunk0, expandedF1_0Chunk1, expandedF1_0Chunk2, expandedF1_0Chunk3, expandedF1_0, expandedF2_0Chunk0, expandedF2_0Chunk1, expandedF2_0Chunk2, expandedF2_0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, expandedF2_2Chunk0, expandedF2_2Chunk1, expandedF2_2Chunk2, expandedF2_2, quotient0_0Chunk0, quotient0_0Chunk1, quotient0_0Chunk2, quotient0_0Chunk3, quotient0_0Chunk4, quotient0_0Chunk5, quotient0_0]
  ring

theorem certificate_0_1 : localCoeff 0 (jetI 1) (jetJ 1) =
    4*expected 0 1+8*certificateQuotient 0 1 := by
  change localCoeff 0 1 0 = 4*(expectedBase 0)+8*quotient0_1
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative0, frameF_derivative2,
    frameF_second_derivative0, frameF_second_derivative2,
    IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    expectedBase, U, V, W, alpha, pderiv_numeral, x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF1_0Chunk0, expandedF1_0Chunk1, expandedF1_0Chunk2, expandedF1_0Chunk3, expandedF1_0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, expandedF2_2Chunk0, expandedF2_2Chunk1, expandedF2_2Chunk2, expandedF2_2, quotient0_1Chunk0, quotient0_1Chunk1, quotient0_1Chunk2, quotient0_1Chunk3, quotient0_1Chunk4, quotient0_1Chunk5, quotient0_1Chunk6, quotient0_1Chunk7, quotient0_1]
  ring

theorem certificate_0_2 : localCoeff 0 (jetI 2) (jetJ 2) =
    4*expected 0 2+8*certificateQuotient 0 2 := by
  change localCoeff 0 0 1 = 4*(z*expectedBase 0)+8*quotient0_2
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative0, frameF_derivative2,
    frameF_second_derivative0, frameF_second_derivative2,
    IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    expectedBase, U, V, W, alpha, pderiv_numeral, x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF1_0Chunk0, expandedF1_0Chunk1, expandedF1_0Chunk2, expandedF1_0Chunk3, expandedF1_0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, expandedF2_2Chunk0, expandedF2_2Chunk1, expandedF2_2Chunk2, expandedF2_2, quotient0_2Chunk0, quotient0_2Chunk1, quotient0_2Chunk2, quotient0_2Chunk3, quotient0_2Chunk4, quotient0_2Chunk5, quotient0_2Chunk6, quotient0_2Chunk7, quotient0_2Chunk8, quotient0_2]
  ring

theorem certificate_0_3 : localCoeff 0 (jetI 3) (jetJ 3) =
    4*expected 0 3+8*certificateQuotient 0 3 := by
  change localCoeff 0 2 0 = 4*((0 : Poly))+8*quotient0_3
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative0, frameF_derivative2,
    frameF_second_derivative0, frameF_second_derivative2,
    IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    pderiv_numeral, x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, expandedF2_2Chunk0, expandedF2_2Chunk1, expandedF2_2Chunk2, expandedF2_2, quotient0_3Chunk0, quotient0_3Chunk1, quotient0_3Chunk2, quotient0_3Chunk3, quotient0_3Chunk4, quotient0_3Chunk5, quotient0_3Chunk6, quotient0_3Chunk7, quotient0_3Chunk8, quotient0_3Chunk9, quotient0_3]
  ring

theorem certificate_0_4 : localCoeff 0 (jetI 4) (jetJ 4) =
    4*expected 0 4+8*certificateQuotient 0 4 := by
  change localCoeff 0 1 1 = 4*((0 : Poly))+8*quotient0_4
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative0, frameF_derivative2,
    frameF_second_derivative0, frameF_second_derivative2,
    IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    pderiv_numeral, x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, expandedF2_2Chunk0, expandedF2_2Chunk1, expandedF2_2Chunk2, expandedF2_2, quotient0_4Chunk0, quotient0_4Chunk1, quotient0_4Chunk2, quotient0_4Chunk3, quotient0_4Chunk4, quotient0_4Chunk5, quotient0_4Chunk6, quotient0_4Chunk7, quotient0_4Chunk8, quotient0_4Chunk9, quotient0_4Chunk10, quotient0_4]
  ring

theorem certificate_0_5 : localCoeff 0 (jetI 5) (jetJ 5) =
    4*expected 0 5+8*certificateQuotient 0 5 := by
  change localCoeff 0 0 2 = 4*((0 : Poly))+8*quotient0_5
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative0, frameF_derivative2,
    frameF_second_derivative0, frameF_second_derivative2,
    IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    pderiv_numeral, x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, expandedF1_2Chunk0, expandedF1_2Chunk1, expandedF1_2Chunk2, expandedF1_2Chunk3, expandedF1_2, expandedF2_2Chunk0, expandedF2_2Chunk1, expandedF2_2Chunk2, expandedF2_2, quotient0_5Chunk0, quotient0_5Chunk1, quotient0_5Chunk2, quotient0_5Chunk3, quotient0_5Chunk4, quotient0_5Chunk5, quotient0_5Chunk6, quotient0_5Chunk7, quotient0_5Chunk8, quotient0_5Chunk9, quotient0_5Chunk10, quotient0_5Chunk11, quotient0_5]
  ring

theorem certificate_1_0 : localCoeff 1 (jetI 0) (jetJ 0) =
    4*expected 1 0+8*certificateQuotient 1 0 := by
  change localCoeff 1 0 0 = 4*((0 : Poly))+8*quotient1_0
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative1,     frameF_second_derivative1,     IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    x, y, z]
  simp only [frameF_expansion1,         expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1, expandedF1_1Chunk0, expandedF1_1Chunk1, expandedF1_1Chunk2, expandedF1_1Chunk3, expandedF1_1Chunk4, expandedF1_1Chunk5, expandedF1_1, expandedF2_1Chunk0, expandedF2_1Chunk1, expandedF2_1Chunk2, expandedF2_1Chunk3, expandedF2_1Chunk4, expandedF2_1, quotient1_0Chunk0, quotient1_0Chunk1, quotient1_0Chunk2, quotient1_0Chunk3, quotient1_0Chunk4, quotient1_0Chunk5, quotient1_0Chunk6, quotient1_0]
  ring

theorem certificate_1_1 : localCoeff 1 (jetI 1) (jetJ 1) =
    4*expected 1 1+8*certificateQuotient 1 1 := by
  change localCoeff 1 1 0 = 4*(expectedBase 1)+8*quotient1_1
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative1,     frameF_second_derivative1,     IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    expectedBase, U, V, W, alpha, pderiv_numeral, x, y, z]
  simp only [frameF_expansion1,         expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1, expandedF1_1Chunk0, expandedF1_1Chunk1, expandedF1_1Chunk2, expandedF1_1Chunk3, expandedF1_1Chunk4, expandedF1_1Chunk5, expandedF1_1, quotient1_1Chunk0, quotient1_1Chunk1, quotient1_1Chunk2, quotient1_1Chunk3, quotient1_1Chunk4, quotient1_1Chunk5, quotient1_1Chunk6, quotient1_1Chunk7, quotient1_1]
  ring

theorem certificate_1_2 : localCoeff 1 (jetI 2) (jetJ 2) =
    4*expected 1 2+8*certificateQuotient 1 2 := by
  change localCoeff 1 0 1 = 4*(y*expectedBase 1)+8*quotient1_2
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative1,     frameF_second_derivative1,     IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    expectedBase, U, V, W, alpha, pderiv_numeral, x, y, z]
  simp only [frameF_expansion1,         expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1, expandedF1_1Chunk0, expandedF1_1Chunk1, expandedF1_1Chunk2, expandedF1_1Chunk3, expandedF1_1Chunk4, expandedF1_1Chunk5, expandedF1_1, quotient1_2Chunk0, quotient1_2Chunk1, quotient1_2Chunk2, quotient1_2Chunk3, quotient1_2Chunk4, quotient1_2Chunk5, quotient1_2Chunk6, quotient1_2Chunk7, quotient1_2]
  ring

theorem certificate_1_3 : localCoeff 1 (jetI 3) (jetJ 3) =
    4*expected 1 3+8*certificateQuotient 1 3 := by
  change localCoeff 1 2 0 = 4*((0 : Poly))+8*quotient1_3
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative1,     frameF_second_derivative1,     IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    pderiv_numeral, x, y, z]
  simp only [frameF_expansion1,         expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1, quotient1_3Chunk0, quotient1_3Chunk1, quotient1_3Chunk2, quotient1_3Chunk3, quotient1_3Chunk4, quotient1_3Chunk5, quotient1_3Chunk6, quotient1_3Chunk7, quotient1_3Chunk8, quotient1_3Chunk9, quotient1_3]
  ring

theorem certificate_1_4 : localCoeff 1 (jetI 4) (jetJ 4) =
    4*expected 1 4+8*certificateQuotient 1 4 := by
  change localCoeff 1 1 1 = 4*((0 : Poly))+8*quotient1_4
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative1,     frameF_second_derivative1,     IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    pderiv_numeral, x, y, z]
  simp only [frameF_expansion1,         expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1, quotient1_4Chunk0, quotient1_4Chunk1, quotient1_4Chunk2, quotient1_4Chunk3, quotient1_4Chunk4, quotient1_4Chunk5, quotient1_4Chunk6, quotient1_4Chunk7, quotient1_4Chunk8, quotient1_4Chunk9, quotient1_4]
  ring

theorem certificate_1_5 : localCoeff 1 (jetI 5) (jetJ 5) =
    4*expected 1 5+8*certificateQuotient 1 5 := by
  change localCoeff 1 0 2 = 4*((0 : Poly))+8*quotient1_5
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
    frameF_derivative1,     frameF_second_derivative1,     IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    pderiv_numeral, x, y, z]
  simp only [frameF_expansion1,         expandedF1Chunk0, expandedF1Chunk1, expandedF1Chunk2, expandedF1Chunk3, expandedF1Chunk4, expandedF1Chunk5, expandedF1Chunk6, expandedF1, quotient1_5Chunk0, quotient1_5Chunk1, quotient1_5Chunk2, quotient1_5Chunk3, quotient1_5Chunk4, quotient1_5Chunk5, quotient1_5Chunk6, quotient1_5Chunk7, quotient1_5Chunk8, quotient1_5Chunk9, quotient1_5]
  ring

theorem certificate_2_0 : localCoeff 2 (jetI 0) (jetJ 0) =
    4*expected 2 0+8*certificateQuotient 2 0 := by
  change localCoeff 2 0 0 = 4*((0 : Poly))+8*quotient2_0
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
            IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, quotient2_0Chunk0, quotient2_0Chunk1, quotient2_0Chunk2, quotient2_0Chunk3, quotient2_0Chunk4, quotient2_0]
  ring

theorem certificate_2_1 : localCoeff 2 (jetI 1) (jetJ 1) =
    4*expected 2 1+8*certificateQuotient 2 1 := by
  change localCoeff 2 1 0 = 4*(expectedBase 2)+8*quotient2_1
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
            IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    expectedBase, U, V, W, alpha, x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, quotient2_1Chunk0, quotient2_1Chunk1, quotient2_1Chunk2, quotient2_1Chunk3, quotient2_1Chunk4, quotient2_1Chunk5, quotient2_1Chunk6, quotient2_1]
  ring

theorem certificate_2_2 : localCoeff 2 (jetI 2) (jetJ 2) =
    4*expected 2 2+8*certificateQuotient 2 2 := by
  change localCoeff 2 0 1 = 4*(z*expectedBase 2)+8*quotient2_2
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
            IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    expectedBase, U, V, W, alpha, x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, quotient2_2Chunk0, quotient2_2Chunk1, quotient2_2Chunk2, quotient2_2Chunk3, quotient2_2Chunk4, quotient2_2Chunk5, quotient2_2Chunk6, quotient2_2Chunk7, quotient2_2Chunk8, quotient2_2]
  ring

theorem certificate_2_3 : localCoeff 2 (jetI 3) (jetJ 3) =
    4*expected 2 3+8*certificateQuotient 2 3 := by
  change localCoeff 2 2 0 = 4*((0 : Poly))+8*quotient2_3
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
            IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, quotient2_3Chunk0, quotient2_3Chunk1, quotient2_3Chunk2, quotient2_3Chunk3, quotient2_3Chunk4, quotient2_3Chunk5, quotient2_3Chunk6, quotient2_3Chunk7, quotient2_3Chunk8, quotient2_3Chunk9, quotient2_3]
  ring

theorem certificate_2_4 : localCoeff 2 (jetI 4) (jetJ 4) =
    4*expected 2 4+8*certificateQuotient 2 4 := by
  change localCoeff 2 1 1 = 4*((0 : Poly))+8*quotient2_4
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
            IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, quotient2_4Chunk0, quotient2_4Chunk1, quotient2_4Chunk2, quotient2_4Chunk3, quotient2_4Chunk4, quotient2_4Chunk5, quotient2_4Chunk6, quotient2_4Chunk7, quotient2_4Chunk8, quotient2_4Chunk9, quotient2_4Chunk10, quotient2_4]
  ring

theorem certificate_2_5 : localCoeff 2 (jetI 5) (jetJ 5) =
    4*expected 2 5+8*certificateQuotient 2 5 := by
  change localCoeff 2 0 2 = 4*((0 : Poly))+8*quotient2_5
  simp [-Matrix.cons_val,     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, localCoeff, Fin.sum_univ_succ, recordTaylorValue, recordWeight, recordClass,
    recordOrder, recordMultiplier, recordStep, recordShift, recordFrame, recordF,
    recordB, recordC, deltaB, deltaC, referenceB, referenceC, frameB, frameC, frame,
            IntegralTaylorTail.powerTerm, IntegralTaylorTail.firstTerm, IntegralTaylorTail.secondTerm,
    x, y, z]
  simp only [frameF_expansion0, frameF_expansion2,
        expandedF0Chunk0, expandedF0Chunk1, expandedF0Chunk2, expandedF0Chunk3, expandedF0Chunk4, expandedF0, expandedF2Chunk0, expandedF2Chunk1, expandedF2Chunk2, expandedF2Chunk3, expandedF2Chunk4, expandedF2, quotient2_5Chunk0, quotient2_5Chunk1, quotient2_5Chunk2, quotient2_5Chunk3, quotient2_5Chunk4, quotient2_5Chunk5, quotient2_5Chunk6, quotient2_5Chunk7, quotient2_5Chunk8, quotient2_5Chunk9, quotient2_5Chunk10, quotient2_5Chunk11, quotient2_5]
  ring

/-- The eighteen exact integer identities for the six jets in each residue class. -/
theorem coefficient_certificate (p : Fin 3) (l : Fin 6) :
    localCoeff p (jetI l) (jetJ l) = 4*expected p l+8*certificateQuotient p l := by
  fin_cases p <;> fin_cases l
  · exact certificate_0_0
  · exact certificate_0_1
  · exact certificate_0_2
  · exact certificate_0_3
  · exact certificate_0_4
  · exact certificate_0_5
  · exact certificate_1_0
  · exact certificate_1_1
  · exact certificate_1_2
  · exact certificate_1_3
  · exact certificate_1_4
  · exact certificate_1_5
  · exact certificate_2_0
  · exact certificate_2_1
  · exact certificate_2_2
  · exact certificate_2_3
  · exact certificate_2_4
  · exact certificate_2_5

end TernaryPoly.IntegralTaylorCertificate
