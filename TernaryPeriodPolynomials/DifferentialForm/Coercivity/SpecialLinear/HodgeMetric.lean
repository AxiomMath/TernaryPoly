module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Hodge

@[expose] public section

/-! Finite-dimensional algebraic energy identity for the concrete exterior operator. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

/-- Inner products in exterior coordinates; the factorials remove repeated tuples. -/
def onePairing (a b : OneCoordinates) : ℝ :=
  ∑ i : Fin 5, tangentWeight i * factorialPairing (a i) (b i)

def twoPairing (a b : TwoCoordinates) : ℝ :=
  (1/2 : ℝ) * ∑ i : Fin 5, ∑ j : Fin 5,
    tangentWeight i * tangentWeight j * factorialPairing (a i j) (b i j)

def threePairing (a b : ThreeCoordinates) : ℝ :=
  (1/6 : ℝ) * ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
    tangentWeight i * tangentWeight j * tangentWeight k * factorialPairing (a i j k) (b i j k)

theorem onePairing_self_nonneg (a : OneCoordinates) : 0 ≤ onePairing a a := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (tangentWeight_pos i).le
    (factorialPairing_self_nonneg (a i)))

theorem twoPairing_self_nonneg (a : TwoCoordinates) : 0 ≤ twoPairing a a := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (tangentWeight_pos i).le (tangentWeight_pos j).le)
      (factorialPairing_self_nonneg (a i j))))

theorem twoPairing_self_eq_zero (a : TwoCoordinates) : twoPairing a a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have hnonneg (i j : Fin 5) : 0 ≤ tangentWeight i * tangentWeight j *
        factorialPairing (a i j) (a i j) :=
      mul_nonneg (mul_nonneg (tangentWeight_pos i).le (tangentWeight_pos j).le)
        (factorialPairing_self_nonneg _)
    have hsum : (∑ i : Fin 5, ∑ j : Fin 5, tangentWeight i * tangentWeight j *
        factorialPairing (a i j) (a i j)) = 0 := by
      unfold twoPairing at ha
      linarith
    have hrows := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => hnonneg i j))).mp hsum
    funext i j
    have hrow := hrows i (Finset.mem_univ i)
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg i k)).mp hrow
    have hz := hterms j (Finset.mem_univ j)
    exact (factorialPairing_self_eq_zero _).mp ((mul_eq_zero.mp hz).resolve_left
      (ne_of_gt (mul_pos (tangentWeight_pos i) (tangentWeight_pos j))))
  · rintro rfl
    simp [twoPairing]

theorem threePairing_self_nonneg (a : ThreeCoordinates) : 0 ≤ threePairing a a := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/6)
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (tangentWeight_pos i).le (tangentWeight_pos j).le)
        (tangentWeight_pos k).le) (factorialPairing_self_nonneg (a i j k)))))

theorem twoPairing_symmetric (a b : TwoCoordinates) : twoPairing a b = twoPairing b a := by
  simp only [twoPairing, factorialPairing_symmetric]

theorem twoPairing_add_left (a b c : TwoCoordinates) :
    twoPairing (a + b) c = twoPairing a c + twoPairing b c := by
  simp [twoPairing, mul_add, Finset.sum_add_distrib]

theorem exteriorOne_contractionTwo_adjoint (a : OneCoordinates) (b : TwoCoordinates)
    (hb : IsAlternatingTwo b) :
    twoPairing (exteriorOne a) b = onePairing a (contractionTwo b) := by
  let F := fun i j : Fin 5 => tangentWeight i * tangentWeight j *
    factorialPairing (a i) (infinitesimal (tangentFrame j) (b j i))
  have hpoint (i j : Fin 5) : tangentWeight i * tangentWeight j *
      factorialPairing (exteriorOne a i j) (b i j) = F j i + F i j := by
    have hij : factorialPairing (infinitesimal (tangentFrame j) (a i)) (b i j) =
        -factorialPairing (a i) (infinitesimal (tangentFrame j) (b j i)) := by
      rw [infinitesimal_symmetric_adjoint _ (tangentFrame_mem j).1, hb i j]
      simp
    simp only [exteriorOne, map_sub, LinearMap.sub_apply, hij,
      infinitesimal_symmetric_adjoint _ (tangentFrame_mem i).1]
    dsimp [F]
    ring
  have hswap : (∑ i : Fin 5, ∑ j : Fin 5, F j i) = ∑ i : Fin 5, ∑ j : Fin 5, F i j :=
    Finset.sum_comm
  rw [twoPairing]
  simp_rw [hpoint]
  simp_rw [Finset.sum_add_distrib]
  rw [hswap]
  have hone : onePairing a (contractionTwo b) = ∑ i : Fin 5, ∑ j : Fin 5, F i j := by
    simp only [onePairing, contractionTwo, map_sum, map_smul, Finset.mul_sum, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F]
    ring
  rw [hone]
  ring

def IsAlternatingThree (a : ThreeCoordinates) : Prop :=
  (∀ i j k, a i j k = -a j i k) ∧ (∀ i j k, a i j k = a k i j)

theorem exteriorTwo_alternating (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    IsAlternatingThree (exteriorTwo a) := by
  constructor
  · intro i j k
    simp only [exteriorTwo, ha j i, map_neg]
    abel
  · intro i j k
    simp only [exteriorTwo]
    rw [ha j k, ha k i, map_neg, map_neg]
    abel

theorem exteriorTwo_contractionThree_adjoint (a : TwoCoordinates) (b : ThreeCoordinates)
    (hb : IsAlternatingThree b) :
    threePairing (exteriorTwo a) b = twoPairing a (contractionThree b) := by
  let F := fun i j k : Fin 5 => tangentWeight i * tangentWeight j * tangentWeight k *
    factorialPairing (a i j) (infinitesimal (tangentFrame k) (b k i j))
  have hpoint (i j k : Fin 5) : tangentWeight i * tangentWeight j * tangentWeight k *
      factorialPairing (exteriorTwo a i j k) (b i j k) = F j k i + F i k j + F i j k := by
    have hj : factorialPairing (infinitesimal (tangentFrame j) (a i k)) (b i j k) =
        -factorialPairing (a i k) (infinitesimal (tangentFrame j) (b j i k)) := by
      rw [infinitesimal_symmetric_adjoint _ (tangentFrame_mem j).1, hb.1 i j k]
      simp
    have hk : factorialPairing (infinitesimal (tangentFrame k) (a i j)) (b i j k) =
        factorialPairing (a i j) (infinitesimal (tangentFrame k) (b k i j)) := by
      rw [infinitesimal_symmetric_adjoint _ (tangentFrame_mem k).1, hb.2 i j k]
    simp only [exteriorTwo, map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply,
      hj, hk, infinitesimal_symmetric_adjoint _ (tangentFrame_mem i).1]
    dsimp [F]
    ring
  have hrotate : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, F j k i) =
      ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, F i j k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  have hswap : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, F i k j) =
      ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, F i j k := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  rw [threePairing]
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [hrotate, hswap]
  have htwo : twoPairing a (contractionThree b) =
      (1/2 : ℝ) * ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, F i j k := by
    simp only [twoPairing, contractionThree, map_sum, map_smul, Finset.mul_sum, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    ring
  rw [htwo]
  ring

/-- The algebraic Hodge energy includes both adjacent exterior degrees. -/
theorem algebraicHodgeTwo_energy (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    twoPairing (algebraicHodgeTwo a) a =
      onePairing (contractionTwo a) (contractionTwo a) +
        threePairing (exteriorTwo a) (exteriorTwo a) := by
  rw [algebraicHodgeTwo, twoPairing_add_left,
    exteriorOne_contractionTwo_adjoint _ _ ha, twoPairing_symmetric]
  rw [← exteriorTwo_contractionThree_adjoint _ _ (exteriorTwo_alternating a ha)]

theorem algebraicHodgeTwo_nonneg (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    0 ≤ twoPairing (algebraicHodgeTwo a) a := by
  rw [algebraicHodgeTwo_energy a ha]
  exact add_nonneg (onePairing_self_nonneg _) (threePairing_self_nonneg _)

/-- The actual positive metric on homogeneous exterior-degree-two coordinates. -/
@[instance_reducible] def homogeneousTwoInnerCore (n : ℕ) :
    InnerProductSpace.Core ℝ (homogeneousTwoForms n) where
  inner := fun a b => twoPairing a.val b.val
  conj_inner_symm := fun a b => by simpa using twoPairing_symmetric b.val a.val
  re_inner_nonneg := fun a => twoPairing_self_nonneg a.val
  add_left := by intros; apply twoPairing_add_left
  smul_left := by intros; simp [twoPairing, Finset.mul_sum, mul_assoc, mul_left_comm]
  definite := fun a h => Subtype.ext ((twoPairing_self_eq_zero a.val).mp h)

end TernaryPoly.SL3PolynomialCoercivity
