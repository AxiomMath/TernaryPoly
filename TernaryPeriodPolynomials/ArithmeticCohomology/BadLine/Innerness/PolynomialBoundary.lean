module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem polynomial_constant_of_period {K : Type*} [Field K] [CharZero K]
    (p : Polynomial K) (step : K) (step_ne : step ≠ 0)
    (periodic : ∀ x, p.eval (x + step) = p.eval x) :
    p = Polynomial.C (p.eval 0) := by
  have values (k : ℕ) : p.eval ((k : K) * step) = p.eval 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, periodic, ih]
  apply Polynomial.eq_of_infinite_eval_eq
  have injective : Function.Injective (fun k : ℕ => (k : K) * step) := by
    intro first second equal
    exact Nat.cast_injective (mul_right_cancel₀ step_ne equal)
  apply (Set.infinite_range_of_injective injective).mono
  rintro _ ⟨k, rfl⟩
  change p.eval ((k : K) * step) = (Polynomial.C (p.eval 0)).eval _
  simpa only [Polynomial.eval_C] using values k

theorem homogeneous_aeval_scale {n : ℕ} (f : HomogeneousPoly n)
    {R : Type*} [CommRing R] [Algebra ℂ R] (v : Fin 3 → R) (t : R) :
    aeval (fun i => t * v i) f.val = t ^ n * aeval v f.val := by
  classical
  change eval₂ (algebraMap ℂ R) (fun i => t * v i) f.val =
    t ^ n * eval₂ (algebraMap ℂ R) v f.val
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent supported
  have degree_eq := f.property (mem_support_iff.mp supported)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
    Finsupp.sum] at degree_eq
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [degree_eq]
  ring

theorem symmetricSolution_aeval_swap {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) {R : Type*} [CommRing R] [Algebra ℂ R]
    (v : Fin 3 → R) (first second : Fin 3) :
    aeval (fun i => v (Equiv.swap first second i)) f.val = aeval v f.val := by
  have symmetry := congrArg (aeval v) (solution.1 (Equiv.swap first second))
  simpa only [aeval_bind₁, aeval_X] using symmetry

theorem symmetricSolution_aeval_relation {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) {R : Type*} [CommRing R] [Algebra ℂ R]
    (x y z : R) :
    aeval ![x,y,z] f.val + aeval ![-y,x-y,z] f.val +
      aeval ![y-x,-x,z] f.val = 0 := by
  have relation := congrArg (aeval ![x,y,z]) solution.2
  have first_eq : (fun i => aeval ![x,y,z] (![-X 1,X 0-X 1,X 2] i : Poly)) =
      ![-y,x-y,z] := by
    funext i
    fin_cases i <;> simp
  have second_eq : (fun i => aeval ![x,y,z] (![X 1-X 0,-X 0,X 2] i : Poly)) =
      ![y-x,-x,z] := by
    funext i
    fin_cases i <;> simp
  simpa only [map_add, map_zero, aeval_bind₁, first_eq, second_eq] using relation

def evalTriple {n : ℕ} (f : HomogeneousPoly n)
    {R : Type*} [CommRing R] [Algebra ℂ R] (x y z : R) : R :=
  aeval ![x,y,z] f.val

theorem evalTriple_swap12 {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) {R : Type*} [CommRing R] [Algebra ℂ R]
    (x y z : R) : evalTriple f x y z = evalTriple f y x z := by
  have perm_eq : (fun i => ![x,y,z] (Equiv.swap (0 : Fin 3) 1 i)) = ![y,x,z] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  exact (perm_eq ▸ symmetricSolution_aeval_swap f solution ![x,y,z] 0 1).symm

theorem evalTriple_swap23 {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) {R : Type*} [CommRing R] [Algebra ℂ R]
    (x y z : R) : evalTriple f x y z = evalTriple f x z y := by
  have perm_eq : (fun i => ![x,y,z] (Equiv.swap (1 : Fin 3) 2 i)) = ![x,z,y] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  exact (perm_eq ▸ symmetricSolution_aeval_swap f solution ![x,y,z] 1 2).symm

theorem evalTriple_swap13 {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) {R : Type*} [CommRing R] [Algebra ℂ R]
    (x y z : R) : evalTriple f x y z = evalTriple f z y x := by
  have perm_eq : (fun i => ![x,y,z] (Equiv.swap (0 : Fin 3) 2 i)) = ![z,y,x] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  exact (perm_eq ▸ symmetricSolution_aeval_swap f solution ![x,y,z] 0 2).symm

theorem evalTriple_neg_even {n : ℕ} (f : HomogeneousPoly n) (even : Even n)
    {R : Type*} [CommRing R] [Algebra ℂ R] (x y z : R) :
    evalTriple f (-x) (-y) (-z) = evalTriple f x y z := by
  have negate_eq : (fun i => (-1 : R) * ![x,y,z] i) = ![-x,-y,-z] := by
    funext i
    fin_cases i <;> simp
  have scale := homogeneous_aeval_scale f ![x,y,z] (-1)
  simpa only [evalTriple, negate_eq, even.neg_one_pow, one_mul] using scale

theorem evalTriple_relation23 {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) {R : Type*} [CommRing R] [Algebra ℂ R]
    (x y z : R) :
    evalTriple f x y z + evalTriple f x (-z) (y-z) +
      evalTriple f x (z-y) (-y) = 0 := by
  have relation := symmetricSolution_aeval_relation f solution y z x
  change evalTriple f y z x + evalTriple f (-z) (y-z) x +
    evalTriple f (z-y) (-y) x = 0 at relation
  have cycle (a b c : R) : evalTriple f a b c = evalTriple f c a b := by
    rw [evalTriple_swap13 f solution a b c, evalTriple_swap23 f solution c b a]
  simpa only [cycle] using relation

theorem symmetricSolution_sum_plane_shear {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) (even : Even n)
    {R : Type*} [CommRing R] [Algebra ℂ R] (s t : R) :
    evalTriple f (s+t) t (-(s+t)-t) = evalTriple f s t (-s-t) := by
  have first := symmetricSolution_aeval_relation f solution (-s-t) t s
  change evalTriple f (-s-t) t s + evalTriple f (-t) (-s-t-t) s +
    evalTriple f (t-(-s-t)) (-(-s-t)) s = 0 at first
  have second := evalTriple_relation23 f solution (-s-2*t) (-t) s
  have first_value : evalTriple f (-s-t) t s = evalTriple f s t (-s-t) :=
    evalTriple_swap13 f solution _ _ _
  have middle_value : evalTriple f (-t) (-s-t-t) s =
      evalTriple f (-s-2*t) (-t) s := by
    rw [evalTriple_swap12 f solution]
    congr 1
    ring
  have last_value : evalTriple f (t-(-s-t)) (-(-s-t)) s =
      evalTriple f (-s-2*t) (-s) (-t-s) := by
    rw [evalTriple_swap23 f solution]
    rw [← evalTriple_neg_even f even (t-(-s-t)) s (-(-s-t))]
    congr 1 <;> ring
  have remaining_value : evalTriple f (-s-2*t) (s-(-t)) (-(-t)) =
      evalTriple f (s+t) t (-(s+t)-t) := by
    rw [evalTriple_swap13 f solution, evalTriple_swap12 f solution]
    congr 1 <;> ring
  rw [first_value, middle_value, last_value] at first
  rw [remaining_value] at second
  linear_combination second - first

theorem map_evalTriple {n : ℕ} (f : HomogeneousPoly n)
    {R S : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (map : R →ₐ[ℂ] S) (x y z : R) :
    map (evalTriple f x y z) = evalTriple f (map x) (map y) (map z) := by
  have hom_eq : map.comp (aeval ![x,y,z]) = aeval ![map x,map y,map z] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact congrArg (fun hom : Poly →ₐ[ℂ] S => hom f.val) hom_eq

theorem evalTriple_scale {n : ℕ} (f : HomogeneousPoly n)
    {R : Type*} [CommRing R] [Algebra ℂ R] (x y z t : R) :
    evalTriple f (t*x) (t*y) (t*z) = t^n * evalTriple f x y z := by
  have vector_eq : (fun i => t * ![x,y,z] i) = ![t*x,t*y,t*z] := by
    funext i
    fin_cases i <;> rfl
  simpa only [evalTriple, vector_eq] using homogeneous_aeval_scale f ![x,y,z] t

theorem symmetricSolution_sum_plane_unit {n : ℕ} (f : HomogeneousPoly n)
    (solution : SymmetricSolution f) (even : Even n) (s : ℂ) :
    evalTriple f s 1 (-s-1) = evalTriple f 0 1 (-1 : ℂ) := by
  let p : Polynomial ℂ := evalTriple f Polynomial.X 1 (-Polynomial.X-1)
  have evaluation (x : ℂ) : p.eval x = evalTriple f x 1 (-x-1) := by
    have mapped := map_evalTriple f (Polynomial.aeval x)
      Polynomial.X 1 (-Polynomial.X-1)
    simpa only [map_one, map_neg, map_sub, Polynomial.aeval_X,
      Polynomial.coe_aeval_eq_eval, Polynomial.eval_X, p] using mapped
  have constant := polynomial_constant_of_period p 1 one_ne_zero (by
    intro x
    rw [evaluation, evaluation]
    exact symmetricSolution_sum_plane_shear f solution even x 1)
  have value := congrArg (Polynomial.eval s) constant
  simpa only [evaluation, Polynomial.eval_C, neg_zero, zero_sub] using value

theorem symmetricSolution_sum_plane_zero {n : ℕ} (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f) (even : Even n)
    (s t : ℂ) : evalTriple f s t (-s-t) = 0 := by
  have unit_value := symmetricSolution_sum_plane_unit f solution even
  have scaling (s t : ℂ) (nonzero : t ≠ 0) :
      evalTriple f s t (-s-t) = t^n * evalTriple f 0 1 (-1 : ℂ) := by
    have scaled := evalTriple_scale f (s/t) 1 (-(s/t)-1) t
    rw [unit_value] at scaled
    have first_eq : t * (s/t) = s := by field_simp
    have last_eq : t * (-(s/t)-1) = -s-t := by
      rw [mul_sub, mul_neg, first_eq, mul_one]
    simpa only [first_eq, last_eq, mul_one] using scaled
  have fixed_zero : evalTriple f 0 1 (-1 : ℂ) = 0 := by
    have scaled := scaling 1 2 (by norm_num)
    have swapped := evalTriple_swap12 f solution (1 : ℂ) 2 (-1-2)
    have arguments : (-1-2 : ℂ) = -2-1 := by ring
    rw [arguments, unit_value] at swapped
    rw [arguments, swapped] at scaled
    have scalar_ne : (2 : ℂ)^n ≠ 1 := by
      have greater : 1 < (2 : ℕ)^n := one_lt_pow₀ (by decide) (Nat.ne_of_gt positive)
      exact_mod_cast (ne_of_gt greater)
    exact (mul_eq_zero.mp (show ((2 : ℂ)^n-1) * evalTriple f 0 1 (-1 : ℂ) = 0 by
      linear_combination -scaled)).resolve_left (sub_ne_zero.mpr scalar_ne)
  by_cases nonzero : t ≠ 0
  · rw [scaling s t nonzero, fixed_zero, mul_zero]
  · have t_zero := not_ne_iff.mp nonzero
    subst t
    by_cases s_nonzero : s ≠ 0
    · rw [evalTriple_swap12 f solution]
      have arguments : (-s-0 : ℂ) = -0-s := by ring
      rw [arguments, scaling 0 s s_nonzero, fixed_zero, mul_zero]
    · have s_zero := not_ne_iff.mp s_nonzero
      subst s
      have scaled := evalTriple_scale f (0 : ℂ) 0 0 0
      simpa only [zero_mul, zero_pow (Nat.ne_of_gt positive), neg_zero, sub_zero]
        using scaled

theorem symmetricSolution_sum_plane_substitution {n : ℕ} (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f) (even : Even n)
    (p q : Poly) : evalTriple f p q (-p-q) = 0 := by
  apply MvPolynomial.funext
  intro values
  change aeval values (evalTriple f p q (-p-q)) = aeval values 0
  rw [map_evalTriple, map_zero, map_sub, map_neg]
  exact symmetricSolution_sum_plane_zero positive f solution even _ _

/-- Restriction to the upper-cusp vanishing plane in the Bernoulli coordinate. -/
def cuspSubstitution : Poly →ₐ[ℂ] Poly := bind₁ ![X 0,X 1,3*X 1]

theorem cuspSubstitution_pderiv (p : Poly) :
    cuspSubstitution (pderiv 0 p) = pderiv 0 (cuspSubstitution p) := by
  have derivative_three : pderiv 0 (3 : Poly) = 0 := by
    change pderiv 0 (C (3 : ℂ)) = 0
    exact pderiv_C
  induction p using MvPolynomial.induction_on with
  | C a => simp [cuspSubstitution]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [pderiv_mul, map_add, map_mul, hp]
    congr 1
    fin_cases i <;> simp [cuspSubstitution, derivative_three]

theorem cuspSubstitution_iterate_pderiv (p : Poly) (k : ℕ) :
    cuspSubstitution (((fun q : Poly => pderiv 0 q)^[k]) p) =
      ((fun q : Poly => pderiv 0 q)^[k]) (cuspSubstitution p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', cuspSubstitution_pderiv, ih,
      Function.iterate_succ_apply']

theorem cuspSubstitution_bernoulli_zero (n : ℕ) (t p : Poly)
    (vanishing : cuspSubstitution p = 0) :
    cuspSubstitution (bernoulliOperator n t p) = 0 := by
  have zero_iterate (k : ℕ) : ((fun q : Poly => pderiv 0 q)^[k]) 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  unfold bernoulliOperator
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [map_mul, cuspSubstitution_iterate_pderiv, vanishing]
  rw [zero_iterate k, mul_zero]

theorem cuspSubstitution_frame_zero {n : ℕ} (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f) (even : Even n)
    (x y z : Poly)
    (sum_zero : cuspSubstitution x + cuspSubstitution y + cuspSubstitution z = 0) :
    cuspSubstitution (evalTriple f x y z) = 0 := by
  rw [map_evalTriple]
  have third_eq : cuspSubstitution z = -cuspSubstitution x - cuspSubstitution y := by
    linear_combination sum_zero
  rw [third_eq]
  exact symmetricSolution_sum_plane_substitution positive f solution even _ _

theorem bernoulliObstruction_cusp_zero {n : ℕ} (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f) (even : Even n) :
    cuspSubstitution (bernoulliObstruction f) = 0 := by
  have first := cuspSubstitution_frame_zero positive f solution even
    (X 2 - 2*X 1) (-X 0) (X 0-X 1) (by simp [cuspSubstitution, map_ofNat]; ring)
  have second := cuspSubstitution_frame_zero positive f solution even
    (X 2-X 0) (X 0-2*X 1) (-X 1) (by simp [cuspSubstitution, map_ofNat]; ring)
  have third := cuspSubstitution_frame_zero positive f solution even
    (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1) (by simp [cuspSubstitution, map_ofNat]; ring)
  change cuspSubstitution
    (X 2 * bernoulliOperator n (X 1)
      (evalTriple f (X 2-2*X 1) (-X 0) (X 0-X 1)) -
      X 1 * bernoulliOperator n (X 2)
        (evalTriple f (X 2-2*X 1) (-X 0) (X 0-X 1) -
          evalTriple f (X 2-X 0) (X 0-2*X 1) (-X 1) +
          evalTriple f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1))) = 0
  rw [map_sub, map_mul, map_mul, cuspSubstitution_bernoulli_zero n _ _ first,
    cuspSubstitution_bernoulli_zero n _ _ (by
      rw [map_add, map_sub, first, second, third, sub_self, add_zero]),
    mul_zero, mul_zero, sub_self]

theorem normalizedBadLine_cusp_zero {n : ℕ} (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f) (even : Even n)
    (c : Homogeneous.cocycles rationalLevel
      (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    cuspSubstitution (mixedBernoulliCoordinate c binaryA) = 0 := by
  rw [normalized.2.1, map_neg,
    bernoulliObstruction_cusp_zero positive f solution even, neg_zero]

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
