module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SymmetricCoordinates
public import Mathlib.Algebra.CharP.Two

@[expose] public section


/-!
# Proof of Lemma 5.4 (`mf:lem:cancellation`)

For symmetric `g : Poly2`, `piOperator (TernaryPoly.CharTwoNorm.norm g) = 0`.

The eighteen substitutions of `piOperator`, applied to the three-term norm
`g + sub₁ g + sub₂ g`, expand into fifty-four `sub g A B C` atoms (three per
substitution). Since `g` is symmetric, these fifty-four atoms pair up into
twenty-seven equal pairs under the permutation action (`sub_permutations`),
so the whole sum cancels in characteristic two.
-/

open MvPolynomial
open TernaryPeriodPolynomials.Argument
open TernaryPoly.CharTwoProjector (sub Symmetric sub_permutations symmetric_of_isSymmetric)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem my_sub_comp (f a b c x y z : Poly2) :
    sub (sub f a b c) x y z = sub f (sub a x y z) (sub b x y z) (sub c x y z) := by
  simp only [sub, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem my_sub_add (f h a b c : Poly2) :
    sub (f + h) a b c = sub f a b c + sub h a b c :=
  map_add (bind₁ ![a, b, c]) f h

private theorem sub_X0 (p q r : Poly2) : sub (X 0) p q r = p := by simp [sub]
private theorem sub_X1 (p q r : Poly2) : sub (X 1) p q r = q := by simp [sub]
private theorem sub_X2 (p q r : Poly2) : sub (X 2) p q r = r := by simp [sub]

private theorem sub_X0X1 (p q r : Poly2) : sub (X 0 + X 1) p q r = p + q := by
  rw [my_sub_add, sub_X0, sub_X1]

private theorem sub_sub1 (g p q r : Poly2) :
    sub (TernaryPoly.CharTwoNorm.sub₁ g) p q r = sub g q (p + q) r := by
  have e : TernaryPoly.CharTwoNorm.sub₁ g = sub g (X 1) (X 0 + X 1) (X 2) := rfl
  rw [e, my_sub_comp, sub_X1, sub_X0X1, sub_X2]

private theorem sub_sub2 (g p q r : Poly2) :
    sub (TernaryPoly.CharTwoNorm.sub₂ g) p q r = sub g (p + q) p r := by
  have e : TernaryPoly.CharTwoNorm.sub₂ g = sub g (X 0 + X 1) (X 0) (X 2) := rfl
  rw [e, my_sub_comp, sub_X0X1, sub_X0, sub_X2]

private theorem sub_norm (g p q r : Poly2) :
    sub (TernaryPoly.CharTwoNorm.norm g) p q r =
      sub g p q r + sub g q (p + q) r + sub g (p + q) p r := by
  show sub (g + TernaryPoly.CharTwoNorm.sub₁ g + TernaryPoly.CharTwoNorm.sub₂ g) p q r = _
  rw [my_sub_add, my_sub_add, sub_sub1, sub_sub2]

private theorem cancel1 : (X 1 : Poly2) + (X 2) = X 1 + X 2 := by
  ring_nf

private theorem h1 (g : Poly2) :
    bind₁ (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 1) (X 2) (X 0 + X 1) + sub g (X 2) (X 1 + X 2) (X 0 + X 1) +
        sub g (X 1 + X 2) (X 1) (X 0 + X 1) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 1) (X 2) (X 0 + X 1) = _
  rw [sub_norm, cancel1]

private theorem cancel2 : (X 2 : Poly2) + (X 1) = X 1 + X 2 := by
  ring_nf

private theorem h2 (g : Poly2) :
    bind₁ (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 2) (X 1) (X 0 + X 2) + sub g (X 1) (X 1 + X 2) (X 0 + X 2) +
        sub g (X 1 + X 2) (X 2) (X 0 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 2) (X 1) (X 0 + X 2) = _
  rw [sub_norm, cancel2]

private theorem cancel3 : (X 0 : Poly2) + (X 2) = X 0 + X 2 := by
  ring_nf

private theorem h3 (g : Poly2) :
    bind₁ (![X 0, X 2, X 0 + X 1] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 2) (X 0 + X 1) + sub g (X 2) (X 0 + X 2) (X 0 + X 1) +
        sub g (X 0 + X 2) (X 0) (X 0 + X 1) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 2) (X 0 + X 1) = _
  rw [sub_norm, cancel3]

private theorem cancel4 : (X 0 : Poly2) + (X 2) = X 0 + X 2 := by
  ring_nf

private theorem h4 (g : Poly2) :
    bind₁ (![X 0, X 2, X 1 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 2) (X 1 + X 2) + sub g (X 2) (X 0 + X 2) (X 1 + X 2) +
        sub g (X 0 + X 2) (X 0) (X 1 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 2) (X 1 + X 2) = _
  rw [sub_norm, cancel4]

private theorem cancel5 : (X 0 + X 1 : Poly2) + (X 2) = X 0 + X 1 + X 2 := by
  ring_nf

private theorem h5 (g : Poly2) :
    bind₁ (![X 0 + X 1, X 2, X 0] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0 + X 1) (X 2) (X 0) + sub g (X 2) (X 0 + X 1 + X 2) (X 0) +
        sub g (X 0 + X 1 + X 2) (X 0 + X 1) (X 0) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0 + X 1) (X 2) (X 0) = _
  rw [sub_norm, cancel5]

private theorem cancel6 : (X 0 + X 1 : Poly2) + (X 2) = X 0 + X 1 + X 2 := by
  ring_nf

private theorem h6 (g : Poly2) :
    bind₁ (![X 0 + X 1, X 2, X 1] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0 + X 1) (X 2) (X 1) + sub g (X 2) (X 0 + X 1 + X 2) (X 1) +
        sub g (X 0 + X 1 + X 2) (X 0 + X 1) (X 1) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0 + X 1) (X 2) (X 1) = _
  rw [sub_norm, cancel6]

private theorem cancel7 : (X 2 : Poly2) + (X 0 + X 1 + X 2) = X 0 + X 1 := by
  ring_nf; simp [CharTwo.two_eq_zero]

private theorem h7 (g : Poly2) :
    bind₁ (![X 2, X 0 + X 1 + X 2, X 0 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 2) (X 0 + X 1 + X 2) (X 0 + X 2) + sub g (X 0 + X 1 + X 2) (X 0 + X 1) (X 0 + X 2) +
        sub g (X 0 + X 1) (X 2) (X 0 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 2) (X 0 + X 1 + X 2) (X 0 + X 2) = _
  rw [sub_norm, cancel7]

private theorem cancel8 : (X 0 + X 1 + X 2 : Poly2) + (X 2) = X 0 + X 1 := by
  ring_nf; simp [CharTwo.two_eq_zero]

private theorem h8 (g : Poly2) :
    bind₁ (![X 0 + X 1 + X 2, X 2, X 1 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0 + X 1 + X 2) (X 2) (X 1 + X 2) + sub g (X 2) (X 0 + X 1) (X 1 + X 2) +
        sub g (X 0 + X 1) (X 0 + X 1 + X 2) (X 1 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0 + X 1 + X 2) (X 2) (X 1 + X 2) = _
  rw [sub_norm, cancel8]

private theorem cancel9 : (X 0 : Poly2) + (X 1) = X 0 + X 1 := by
  ring_nf

private theorem h9 (g : Poly2) :
    bind₁ (![X 0, X 1, X 0 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 1) (X 0 + X 2) + sub g (X 1) (X 0 + X 1) (X 0 + X 2) +
        sub g (X 0 + X 1) (X 0) (X 0 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 1) (X 0 + X 2) = _
  rw [sub_norm, cancel9]

private theorem cancel10 : (X 0 : Poly2) + (X 1) = X 0 + X 1 := by
  ring_nf

private theorem h10 (g : Poly2) :
    bind₁ (![X 0, X 1, X 1 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 1) (X 1 + X 2) + sub g (X 1) (X 0 + X 1) (X 1 + X 2) +
        sub g (X 0 + X 1) (X 0) (X 1 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 1) (X 1 + X 2) = _
  rw [sub_norm, cancel10]

private theorem cancel11 : (X 1 : Poly2) + (X 0 + X 2) = X 0 + X 1 + X 2 := by
  ring_nf

private theorem h11 (g : Poly2) :
    bind₁ (![X 1, X 0 + X 2, X 0] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 1) (X 0 + X 2) (X 0) + sub g (X 0 + X 2) (X 0 + X 1 + X 2) (X 0) +
        sub g (X 0 + X 1 + X 2) (X 1) (X 0) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 1) (X 0 + X 2) (X 0) = _
  rw [sub_norm, cancel11]

private theorem cancel12 : (X 1 : Poly2) + (X 0 + X 1 + X 2) = X 0 + X 2 := by
  ring_nf; simp [CharTwo.two_eq_zero]

private theorem h12 (g : Poly2) :
    bind₁ (![X 1, X 0 + X 1 + X 2, X 0 + X 1] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 1) (X 0 + X 1 + X 2) (X 0 + X 1) + sub g (X 0 + X 1 + X 2) (X 0 + X 2) (X 0 + X 1) +
        sub g (X 0 + X 2) (X 1) (X 0 + X 1) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 1) (X 0 + X 1 + X 2) (X 0 + X 1) = _
  rw [sub_norm, cancel12]

private theorem cancel13 : (X 0 + X 2 : Poly2) + (X 1) = X 0 + X 1 + X 2 := by
  ring_nf

private theorem h13 (g : Poly2) :
    bind₁ (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0 + X 2) (X 1) (X 2) + sub g (X 1) (X 0 + X 1 + X 2) (X 2) +
        sub g (X 0 + X 1 + X 2) (X 0 + X 2) (X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0 + X 2) (X 1) (X 2) = _
  rw [sub_norm, cancel13]

private theorem cancel14 : (X 0 + X 1 + X 2 : Poly2) + (X 1) = X 0 + X 2 := by
  ring_nf; simp [CharTwo.two_eq_zero]

private theorem h14 (g : Poly2) :
    bind₁ (![X 0 + X 1 + X 2, X 1, X 1 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0 + X 1 + X 2) (X 1) (X 1 + X 2) + sub g (X 1) (X 0 + X 2) (X 1 + X 2) +
        sub g (X 0 + X 2) (X 0 + X 1 + X 2) (X 1 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0 + X 1 + X 2) (X 1) (X 1 + X 2) = _
  rw [sub_norm, cancel14]

private theorem cancel15 : (X 0 : Poly2) + (X 1 + X 2) = X 0 + X 1 + X 2 := by
  ring_nf

private theorem h15 (g : Poly2) :
    bind₁ (![X 0, X 1 + X 2, X 1] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 1 + X 2) (X 1) + sub g (X 1 + X 2) (X 0 + X 1 + X 2) (X 1) +
        sub g (X 0 + X 1 + X 2) (X 0) (X 1) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 1 + X 2) (X 1) = _
  rw [sub_norm, cancel15]

private theorem cancel16 : (X 0 : Poly2) + (X 0 + X 1 + X 2) = X 1 + X 2 := by
  ring_nf; simp [CharTwo.two_eq_zero]

private theorem h16 (g : Poly2) :
    bind₁ (![X 0, X 0 + X 1 + X 2, X 0 + X 1] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 0 + X 1 + X 2) (X 0 + X 1) + sub g (X 0 + X 1 + X 2) (X 1 + X 2) (X 0 + X 1) +
        sub g (X 1 + X 2) (X 0) (X 0 + X 1) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 0 + X 1 + X 2) (X 0 + X 1) = _
  rw [sub_norm, cancel16]

private theorem cancel17 : (X 0 : Poly2) + (X 1 + X 2) = X 0 + X 1 + X 2 := by
  ring_nf

private theorem h17 (g : Poly2) :
    bind₁ (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 1 + X 2) (X 2) + sub g (X 1 + X 2) (X 0 + X 1 + X 2) (X 2) +
        sub g (X 0 + X 1 + X 2) (X 0) (X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 1 + X 2) (X 2) = _
  rw [sub_norm, cancel17]

private theorem cancel18 : (X 0 : Poly2) + (X 0 + X 1 + X 2) = X 1 + X 2 := by
  ring_nf; simp [CharTwo.two_eq_zero]

private theorem h18 (g : Poly2) :
    bind₁ (![X 0, X 0 + X 1 + X 2, X 0 + X 2] : Fin 3 → Poly2) (TernaryPoly.CharTwoNorm.norm g) =
      sub g (X 0) (X 0 + X 1 + X 2) (X 0 + X 2) + sub g (X 0 + X 1 + X 2) (X 1 + X 2) (X 0 + X 2) +
        sub g (X 1 + X 2) (X 0) (X 0 + X 2) := by
  show sub (TernaryPoly.CharTwoNorm.norm g) (X 0) (X 0 + X 1 + X 2) (X 0 + X 2) = _
  rw [sub_norm, cancel18]

-- pair 1A = 6A
private theorem p1 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1) (X 2) (X 1) = sub g (X 1) (X 2) (X 0 + X 1) :=
  (sub_permutations hs (X 1) (X 2) (X 0 + X 1)).2.2.2.2

-- pair 1B = 8B
private theorem p2 (g : Poly2) (hs : Symmetric g) :
    sub g (X 2) (X 0 + X 1) (X 1 + X 2) = sub g (X 2) (X 1 + X 2) (X 0 + X 1) :=
  (sub_permutations hs (X 2) (X 1 + X 2) (X 0 + X 1)).2.2.2.1

-- pair 1C = 10B
private theorem p3 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1) (X 0 + X 1) (X 1 + X 2) = sub g (X 1 + X 2) (X 1) (X 0 + X 1) :=
  (sub_permutations hs (X 1 + X 2) (X 1) (X 0 + X 1)).2.1

-- pair 2A = 13A
private theorem p4 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 2) (X 1) (X 2) = sub g (X 2) (X 1) (X 0 + X 2) :=
  (sub_permutations hs (X 2) (X 1) (X 0 + X 2)).2.2.2.2

-- pair 2B = 14B
private theorem p5 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1) (X 0 + X 2) (X 1 + X 2) = sub g (X 1) (X 1 + X 2) (X 0 + X 2) :=
  (sub_permutations hs (X 1) (X 1 + X 2) (X 0 + X 2)).2.2.2.1

-- pair 2C = 4B
private theorem p6 (g : Poly2) (hs : Symmetric g) :
    sub g (X 2) (X 0 + X 2) (X 1 + X 2) = sub g (X 1 + X 2) (X 2) (X 0 + X 2) :=
  (sub_permutations hs (X 1 + X 2) (X 2) (X 0 + X 2)).2.1

-- pair 3A = 5A
private theorem p7 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1) (X 2) (X 0) = sub g (X 0) (X 2) (X 0 + X 1) :=
  (sub_permutations hs (X 0) (X 2) (X 0 + X 1)).2.2.2.2

-- pair 3B = 7C
private theorem p8 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1) (X 2) (X 0 + X 2) = sub g (X 2) (X 0 + X 2) (X 0 + X 1) :=
  (sub_permutations hs (X 2) (X 0 + X 2) (X 0 + X 1)).2.2.1

-- pair 3C = 9C
private theorem p9 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1) (X 0) (X 0 + X 2) = sub g (X 0 + X 2) (X 0) (X 0 + X 1) :=
  (sub_permutations hs (X 0 + X 2) (X 0) (X 0 + X 1)).2.2.2.2

-- pair 4A = 17A
private theorem p10 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0) (X 1 + X 2) (X 2) = sub g (X 0) (X 2) (X 1 + X 2) :=
  (sub_permutations hs (X 0) (X 2) (X 1 + X 2)).2.2.2.1

-- pair 4C = 18C
private theorem p11 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1 + X 2) (X 0) (X 0 + X 2) = sub g (X 0 + X 2) (X 0) (X 1 + X 2) :=
  (sub_permutations hs (X 0 + X 2) (X 0) (X 1 + X 2)).2.2.2.2

-- pair 5B = 17C
private theorem p12 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1 + X 2) (X 0) (X 2) = sub g (X 2) (X 0 + X 1 + X 2) (X 0) :=
  (sub_permutations hs (X 2) (X 0 + X 1 + X 2) (X 0)).2.1

-- pair 5C = 16A
private theorem p13 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0) (X 0 + X 1 + X 2) (X 0 + X 1) = sub g (X 0 + X 1 + X 2) (X 0 + X 1) (X 0) :=
  (sub_permutations hs (X 0 + X 1 + X 2) (X 0 + X 1) (X 0)).2.2.1

-- pair 6B = 13B
private theorem p14 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1) (X 0 + X 1 + X 2) (X 2) = sub g (X 2) (X 0 + X 1 + X 2) (X 1) :=
  (sub_permutations hs (X 2) (X 0 + X 1 + X 2) (X 1)).2.2.2.2

-- pair 6C = 12A
private theorem p15 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1) (X 0 + X 1 + X 2) (X 0 + X 1) = sub g (X 0 + X 1 + X 2) (X 0 + X 1) (X 1) :=
  (sub_permutations hs (X 0 + X 1 + X 2) (X 0 + X 1) (X 1)).2.2.1

-- pair 7A = 13C
private theorem p16 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1 + X 2) (X 0 + X 2) (X 2) = sub g (X 2) (X 0 + X 1 + X 2) (X 0 + X 2) :=
  (sub_permutations hs (X 2) (X 0 + X 1 + X 2) (X 0 + X 2)).2.1

-- pair 7B = 12B
private theorem p17 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1 + X 2) (X 0 + X 2) (X 0 + X 1) = sub g (X 0 + X 1 + X 2) (X 0 + X 1) (X 0 + X 2) :=
  (sub_permutations hs (X 0 + X 1 + X 2) (X 0 + X 1) (X 0 + X 2)).2.2.2.1

-- pair 8A = 17B
private theorem p18 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1 + X 2) (X 0 + X 1 + X 2) (X 2) = sub g (X 0 + X 1 + X 2) (X 2) (X 1 + X 2) :=
  (sub_permutations hs (X 0 + X 1 + X 2) (X 2) (X 1 + X 2)).2.2.1

-- pair 8C = 16B
private theorem p19 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1 + X 2) (X 1 + X 2) (X 0 + X 1) = sub g (X 0 + X 1) (X 0 + X 1 + X 2) (X 1 + X 2) :=
  (sub_permutations hs (X 0 + X 1) (X 0 + X 1 + X 2) (X 1 + X 2)).2.1

-- pair 9A = 11A
private theorem p20 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1) (X 0 + X 2) (X 0) = sub g (X 0) (X 1) (X 0 + X 2) :=
  (sub_permutations hs (X 0) (X 1) (X 0 + X 2)).2.1

-- pair 9B = 12C
private theorem p21 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 2) (X 1) (X 0 + X 1) = sub g (X 1) (X 0 + X 1) (X 0 + X 2) :=
  (sub_permutations hs (X 1) (X 0 + X 1) (X 0 + X 2)).2.2.1

-- pair 10A = 15A
private theorem p22 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0) (X 1 + X 2) (X 1) = sub g (X 0) (X 1) (X 1 + X 2) :=
  (sub_permutations hs (X 0) (X 1) (X 1 + X 2)).2.2.2.1

-- pair 10C = 16C
private theorem p23 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1 + X 2) (X 0) (X 0 + X 1) = sub g (X 0 + X 1) (X 0) (X 1 + X 2) :=
  (sub_permutations hs (X 0 + X 1) (X 0) (X 1 + X 2)).2.2.2.2

-- pair 11B = 18A
private theorem p24 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0) (X 0 + X 1 + X 2) (X 0 + X 2) = sub g (X 0 + X 2) (X 0 + X 1 + X 2) (X 0) :=
  (sub_permutations hs (X 0 + X 2) (X 0 + X 1 + X 2) (X 0)).2.2.2.2

-- pair 11C = 15C
private theorem p25 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1 + X 2) (X 0) (X 1) = sub g (X 0 + X 1 + X 2) (X 1) (X 0) :=
  (sub_permutations hs (X 0 + X 1 + X 2) (X 1) (X 0)).2.2.2.1

-- pair 14A = 15B
private theorem p26 (g : Poly2) (hs : Symmetric g) :
    sub g (X 1 + X 2) (X 0 + X 1 + X 2) (X 1) = sub g (X 0 + X 1 + X 2) (X 1) (X 1 + X 2) :=
  (sub_permutations hs (X 0 + X 1 + X 2) (X 1) (X 1 + X 2)).2.2.1

-- pair 14C = 18B
private theorem p27 (g : Poly2) (hs : Symmetric g) :
    sub g (X 0 + X 1 + X 2) (X 1 + X 2) (X 0 + X 2) = sub g (X 0 + X 2) (X 0 + X 1 + X 2) (X 1 + X 2) :=
  (sub_permutations hs (X 0 + X 2) (X 0 + X 1 + X 2) (X 1 + X 2)).2.1

theorem lemma_5_4_proof (g : Poly2) (hg : g.IsSymmetric) :
    piOperator (TernaryPoly.CharTwoNorm.norm g) = 0 := by
  have hs : Symmetric g := symmetric_of_isSymmetric hg
  show (piSubstitutions.map fun t => bind₁ t (TernaryPoly.CharTwoNorm.norm g)).sum = 0
  simp only [piSubstitutions, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    h1 g, h2 g, h3 g, h4 g, h5 g, h6 g, h7 g, h8 g, h9 g, h10 g, h11 g, h12 g, h13 g, h14 g, h15 g, h16 g, h17 g, h18 g]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    p1 g hs + p2 g hs + p3 g hs + p4 g hs + p5 g hs + p6 g hs + p7 g hs + p8 g hs + p9 g hs + p10 g hs + p11 g hs + p12 g hs + p13 g hs + p14 g hs + p15 g hs + p16 g hs + p17 g hs + p18 g hs + p19 g hs + p20 g hs + p21 g hs + p22 g hs + p23 g hs + p24 g hs + p25 g hs + p26 g hs + p27 g hs

end TernaryPeriodPolynomials.Argument.ModFourBeta
