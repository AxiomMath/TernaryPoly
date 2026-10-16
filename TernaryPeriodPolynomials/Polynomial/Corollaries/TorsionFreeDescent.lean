module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Corollaries.Lemma21Parts
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.Polynomial.Classification.Pairwise
public import TernaryPeriodPolynomials.Polynomial.Classification.Restriction
public import TernaryPeriodPolynomials.Polynomial.Restriction
public import TernaryPeriodPolynomials.Polynomial.PeriodNormalization
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section


/-! Proof pieces for the torsion-free descent target. Feeds
`TernaryPeriodPolynomials.torsion_free_descent`.

Strategy: embed `R` (any `[CommRing R] [IsAddTorsionFree R]`) into `TFHull R :=
Localization (nonZeroDivisors R)`, which carries a genuine `[Algebra ℚ (TFHull R)]` instance
because every nonzero integer becomes a non-zero-divisor, hence a unit after localization. The
embedding `algebraMap R (TFHull R)` is injective (`IsLocalization.injective`), so the three
"coefficient ring" facts the paper proves under `[Algebra ℚ R]` (`solution_pairwise`,
`restriction_periodRelations`, `cyclicLift_restriction`) can be proved over `TFHull R` and pulled
straight back down along the embedding, using naturality of `restriction`/`cyclicLift` under
coefficient maps and injectivity of `MvPolynomial.map`. The one remaining ingredient the
paper gates by `[Field F][CharZero F]` (`period_odd_eq_zero`) is regeneralized here to
`[IsAddTorsionFree R]` directly (its only field/characteristic-zero-specific step is
`x = -x → x = 0`, which holds for any additively torsion-free commutative group, including
`MvPolynomial σ R` whenever `R` is additively torsion-free), so it can be applied to the
restriction of a homogeneous component of `f` *before* crossing the embedding. The divisibility
clause (`universalDivisor R ∣ f`) is handled separately, since divisibility need not descend
through a general injective ring hom. -/


open MvPolynomial TernaryPoly TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification

namespace TernaryPeriodPolynomials.Argument

section Embedding

variable (R : Type*) [CommRing R] [IsAddTorsionFree R]

/-- The localization of `R` at its non-zero-divisors. Every nonzero integer becomes a unit here
(see `TFHull.int_isUnit`), which is what lets us put a `ℚ`-algebra structure on it below. -/
abbrev TFHull : Type _ := Localization (nonZeroDivisors R)

variable {R}

omit [IsAddTorsionFree R] in
/-- `R` embeds into `TFHull R`, for any commutative ring `R` (no torsion-freeness needed for
injectivity itself; it is only needed below to equip `TFHull R` with a `ℚ`-algebra structure). -/
theorem TFHull.algebraMap_injective : Function.Injective (algebraMap R (TFHull R)) :=
  IsLocalization.injective (TFHull R) (le_refl (nonZeroDivisors R))

/-- Every nonzero integer, viewed in an additively torsion-free `R`, is a non-zero-divisor. -/
theorem TFHull.intCast_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :
    (n : R) ∈ nonZeroDivisors R := by
  have key : ∀ y : R, y * (n : R) = 0 → y = 0 := by
    intro y hy
    have h2 : n • y = 0 := by rw [zsmul_eq_mul, mul_comm]; exact hy
    exact (zsmul_right_inj hn).mp (by simpa using h2)
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

/-- Every nonzero integer is a unit in `TFHull R`. -/
theorem TFHull.int_isUnit {n : ℤ} (hn : n ≠ 0) : IsUnit ((n : TFHull R)) := by
  have hmem : (n : R) ∈ nonZeroDivisors R := TFHull.intCast_mem_nonZeroDivisors hn
  have := IsLocalization.map_units (TFHull R) (⟨(n : R), hmem⟩ : nonZeroDivisors R)
  simpa using this

/-- The structure map `ℚ →+* TFHull R`, built from the fraction-field universal property of `ℚ`
over `ℤ`. -/
noncomputable def TFHull.ratMap : ℚ →+* TFHull R :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
    (g := Int.castRingHom (TFHull R))
    (by
      intro n
      have hn : (n : ℤ) ≠ 0 := by
        have hmem := n.2
        rwa [mem_nonZeroDivisors_iff_ne_zero] at hmem
      simpa using TFHull.int_isUnit (R := R) hn)

/-- `TFHull R` is a `ℚ`-algebra. -/
noncomputable instance TFHull.instAlgebraRat : Algebra ℚ (TFHull R) :=
  (TFHull.ratMap (R := R)).toAlgebra

end Embedding

section MvPolynomialTorsionFree

/-- Additive torsion-freeness transfers from coefficients to the whole polynomial ring: this is
not already in Mathlib, but follows directly from `MvPolynomial.coeff` being additive (so
`n`-torsion of a polynomial is detected coefficientwise) plus `MvPolynomial.ext`. -/
private theorem mvpoly_nsmul_right_injective {σ R : Type*} [CommRing R] [IsAddTorsionFree R]
    {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun p : MvPolynomial σ R => n • p) := by
  intro p q hpq
  simp only at hpq
  apply MvPolynomial.ext
  intro d
  have h := congrArg (·.coeff d) hpq
  simp only [MvPolynomial.coeff_smul] at h
  exact IsAddTorsionFree.nsmul_right_injective hn (by simpa using h)

instance mvpoly_isAddTorsionFree {σ R : Type*} [CommRing R] [IsAddTorsionFree R] :
    IsAddTorsionFree (MvPolynomial σ R) :=
  ⟨fun _ hn _ _ h => mvpoly_nsmul_right_injective hn h⟩

end MvPolynomialTorsionFree

section OddVanishing

/-- The torsion-free analogue of `x = -x → x = 0` (the only field/characteristic-zero-specific
step in the paper's `period_odd_eq_zero`), for any additively torsion-free commutative
group. -/
theorem eq_neg_self_of_torsionFree {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    (x : M) (h : x = -x) : x = 0 := by
  have h2 : (2 : ℤ) • x = (2 : ℤ) • (0 : M) := by
    simp only [smul_zero]
    rw [two_zsmul]
    nth_rewrite 2 [h]
    abel
  exact (zsmul_right_inj (by norm_num : (2 : ℤ) ≠ 0)).mp h2

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

/-- Odd-degree-homogeneous normalized full periods vanish over any additively torsion-free
commutative ring, regeneralizing `period_odd_eq_zero` away from `[Field F][CharZero F]`: every
other step of that proof (`homogeneous_bind_smul`, `PeriodIdentities.neg_neg`, `Odd.neg_one_pow`)
already holds over an arbitrary commutative (semi)ring, and `Binary R` inherits torsion-freeness
from `R` via `mvpoly_isAddTorsionFree`. -/
theorem period_odd_eq_zero_torsionFree {q : Binary R} {n : ℕ}
    (hh : q.IsHomogeneous n) (hq : PeriodIdentities q) (hn : Odd n) : q = 0 := by
  have h := TernaryPoly.homogeneous_bind_smul hh (-1 : R)
  have hv : (fun i : Fin 2 => (-1 : R) • (X i : Binary R)) = ![-X 0, -X 1] := by
    funext i; fin_cases i <;> simp
  rw [hv, PeriodIdentities.neg_neg hq, hn.neg_one_pow, neg_one_smul] at h
  exact eq_neg_self_of_torsionFree q h

end OddVanishing

section Naturality

variable {R : Type*} [CommRing R]

/-- The image under `MvPolynomial.map` of a length-2 or length-3 `Matrix.cons` vector of
polynomials, pulled inside the `map`. Covers every coordinate substitution vector appearing in
`restriction`, `cyclicLift`, and `PeriodRelations`. -/
private theorem map_vec2_apply {A σ : Type*} [CommRing A] (φ : R →+* A)
    (a b : MvPolynomial σ R) :
    (fun i : Fin 2 => MvPolynomial.map φ (![a, b] i)) =
      (![MvPolynomial.map φ a, MvPolynomial.map φ b] : Fin 2 → MvPolynomial σ A) := by
  funext i; fin_cases i <;> simp

private theorem map_vec3_apply {A σ : Type*} [CommRing A] (φ : R →+* A)
    (a b c : MvPolynomial σ R) :
    (fun i : Fin 3 => MvPolynomial.map φ (![a, b, c] i)) =
      (![MvPolynomial.map φ a, MvPolynomial.map φ b, MvPolynomial.map φ c] :
        Fin 3 → MvPolynomial σ A) := by
  funext i; fin_cases i <;> simp

/-- Naturality of `restriction` under a coefficient ring hom. -/
private theorem map_restriction {A : Type*} [CommRing A] (φ : R →+* A) (f : Ternary R) :
    map φ (restriction f) = restriction (map φ f) := by
  simp only [restriction, map_bind₁, map_vec3_apply, map_X, map_zero]

/-- Naturality of `cyclicLift` under a coefficient ring hom. -/
private theorem map_cyclicLift {A : Type*} [CommRing A] (φ : R →+* A) (q : Binary R) :
    map φ (cyclicLift q) = cyclicLift (map φ q) := by
  simp only [cyclicLift, binaryEval, map_add, map_bind₁, map_vec2_apply, map_X]

/-- `PeriodRelations` descends through an injective coefficient ring hom. -/
private theorem periodRelations_descend {A : Type*} [CommRing A] (φ : R →+* A)
    (hφ : Function.Injective φ) {q : Binary R} (hq : PeriodRelations (map φ q)) :
    PeriodRelations q := by
  have hinj : Function.Injective (MvPolynomial.map φ : Binary R →+* Binary A) :=
    MvPolynomial.map_injective φ hφ
  obtain ⟨h1, h2, h3, h4⟩ := hq
  refine ⟨hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩
  · simpa only [map_bind₁, map_vec2_apply, map_X, map_zero] using h1
  · simpa only [map_bind₁, map_vec2_apply, map_X, map_zero] using h2
  · simpa only [map_add, map_bind₁, map_vec2_apply, map_X, map_neg, map_zero] using h3
  · simpa only [map_add, map_bind₁, map_vec2_apply, map_X, map_neg, map_sub, map_zero] using h4

end Naturality

section Descent

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

/-- The three "coefficient-ring" facts the paper proves only under `[Algebra ℚ R]`
(`solution_pairwise`, `restriction_periodRelations`, `cyclicLift_restriction`), descended to any
`[IsAddTorsionFree R]` via the embedding into `TFHull R`. -/
theorem solution_descend {f : Ternary R} (hf : Solution f) :
    Pairwise f ∧ PeriodRelations (restriction f) ∧ f = cyclicLift (restriction f) := by
  set φ : R →+* TFHull R := algebraMap R (TFHull R) with hφdef
  have hφ : Function.Injective φ := TFHull.algebraMap_injective
  have hF : Solution (map φ f) := Solution.map hf φ
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    have hP : (map φ f).coeff d = 0 := TernaryPeriodPolynomials.Argument.Classification.solution_pairwise (map φ f) hF d hd
    rw [coeff_map] at hP
    exact hφ (by rw [hP, map_zero])
  · have hq2 : PeriodRelations (map φ (restriction f)) := by
      have hpr := TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hF
      rwa [← map_restriction] at hpr
    exact periodRelations_descend φ hφ hq2
  · have hC : map φ f = cyclicLift (restriction (map φ f)) :=
      (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hF).symm
    rw [← map_restriction] at hC
    rw [← map_cyclicLift] at hC
    exact MvPolynomial.map_injective φ hφ hC

/-- Odd-degree homogeneous components of any torsion-free-ring solution vanish. -/
theorem solution_odd_eq_zero_torsionFree {f : Ternary R} (hf : Solution f) {n : ℕ}
    (hn : Odd n) : MvPolynomial.homogeneousComponent n f = 0 := by
  set g := MvPolynomial.homogeneousComponent n f with hgdef
  have hg : Solution g := Solution.homogeneousComponent hf n
  have hgh : g.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous n f
  obtain ⟨-, hgP, hgC⟩ := solution_descend hg
  have hgRh : (restriction g).IsHomogeneous n := restriction_homogeneous hgh
  have hzero : restriction g = 0 :=
    period_odd_eq_zero_torsionFree hgRh (PeriodRelations.identities hgP) hn
  rw [hgC, hzero]
  simp [cyclicLift, binaryEval]

/-- The four non-divisibility conjuncts of `torsion_free_descent`, assembled. -/
theorem torsionFree_assembled_main {f : Ternary R} (hf : Solution f) :
    Pairwise f ∧ (∀ n : ℕ, Odd n → MvPolynomial.homogeneousComponent n f = 0) ∧
      PeriodRelations (restriction f) ∧ f = cyclicLift (restriction f) := by
  obtain ⟨hP, hPR, hCL⟩ := solution_descend hf
  exact ⟨hP, fun n hn => solution_odd_eq_zero_torsionFree hf hn, hPR, hCL⟩

end Descent

end TernaryPeriodPolynomials.Argument
