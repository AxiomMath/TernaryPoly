module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.ToddSurjective
public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import TernaryPeriodPolynomials.SymmetricSolution.Scalar

@[expose] public section

open MvPolynomial

noncomputable section
namespace TernaryPoly

/-- The Hasse derivative in the first ternary coordinate. -/
def ternaryHasse (k : ℕ) (f : TernaryPolynomial) : TernaryPolynomial :=
  (finSuccEquiv ℚ 2).symm (Polynomial.hasseDeriv k (finSuccEquiv ℚ 2 f))

/-- The exact coefficient formula for the transported Hasse derivative. -/
theorem coeff_ternaryHasse (k : ℕ) (f : TernaryPolynomial) (d : Fin 3 →₀ ℕ) :
    (ternaryHasse k f).coeff d = ((d 0 + k).choose k : ℚ) *
      f.coeff (Finsupp.cons (d 0 + k) d.tail) := by
  calc
    _ = ((finSuccEquiv ℚ 2 (ternaryHasse k f)).coeff (d 0)).coeff d.tail := by
      rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail]
    _ = _ := by
      rw [ternaryHasse, AlgEquiv.apply_symm_apply, Polynomial.hasseDeriv_coeff,
        ← nsmul_eq_mul, coeff_smul, nsmul_eq_mul, finSuccEquiv_coeff_coeff]

private theorem finsupp_degree_cons (i : ℕ) (d : Fin 2 →₀ ℕ) :
    (Finsupp.cons i d).degree = i + d.degree := by
  simp only [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ]

/-- Hasse differentiation lowers homogeneous degree by its order. -/
theorem ternaryHasse_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (k : ℕ) :
    (ternaryHasse k f).IsHomogeneous (n - k) := by
  intro d hd
  rw [coeff_ternaryHasse] at hd
  have hs : f.coeff (Finsupp.cons (d 0 + k) d.tail) ≠ 0 := (mul_ne_zero_iff.mp hd).2
  have hn : (Finsupp.cons (d 0 + k) d.tail).degree = n := by
    by_contra hn
    exact hs (hf.coeff_eq_zero hn)
  have hb : d.degree = d 0 + d.tail.degree := by
    calc
      d.degree = (Finsupp.cons (d 0) d.tail).degree := by rw [Finsupp.cons_tail]
      _ = _ := finsupp_degree_cons _ _
  change Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = n - k
  rw [← Finsupp.degree_eq_weight_one]
  rw [finsupp_degree_cons] at hn
  omega

/-- The first-coordinate degree is bounded by the total homogeneous degree. -/
theorem natDegree_finSuccEquiv_le_of_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (finSuccEquiv ℚ 2 f).natDegree ≤ n := by
  rw [natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree f 0).trans hf.totalDegree_le

private theorem finSuccEquiv_C (r : ℚ) :
    finSuccEquiv ℚ 2 (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  simp only [finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply]

/-- The finite ternary Todd formula separates its coefficient and Hasse factors. -/
theorem ternaryTodd_eq_hasse_sum {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (u : MvPolynomial (Fin 2) ℚ) :
    ternaryTodd u f = ∑ k ∈ Finset.range (n + 1),
      MvPolynomial.C (_root_.bernoulli k) * rename Fin.succ ((-u)^k) * ternaryHasse k f := by
  apply (finSuccEquiv ℚ 2).injective
  rw [ternaryTodd, AlgEquiv.apply_symm_apply,
    todd_eq_sum u _ (n + 1) (Nat.lt_succ_of_le (natDegree_finSuccEquiv_le_of_homogeneous hf)), map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_mul, finSuccEquiv_rename_succ, ternaryHasse, AlgEquiv.apply_symm_apply,
    Polynomial.smul_eq_C_mul, finSuccEquiv_C]
  rfl

/-- A degree-one parameter makes the Todd operator preserve total homogeneous degree. -/
theorem ternaryTodd_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) {u : MvPolynomial (Fin 2) ℚ} (hu : u.IsHomogeneous 1) :
    (ternaryTodd u f).IsHomogeneous n := by
  rw [ternaryTodd_eq_hasse_sum hf u]
  apply IsHomogeneous.sum
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hu' : (MvPolynomial.C (_root_.bernoulli k) * rename Fin.succ ((-u)^k)).IsHomogeneous k := by
    simpa only [one_mul] using (hu.neg.pow k).rename_isHomogeneous.C_mul (_root_.bernoulli k)
  convert hu'.mul (ternaryHasse_homogeneous hf k) using 1
  exact (Nat.add_sub_of_le hk').symm

/-- Substitution by three homogeneous linear forms preserves degree. -/
theorem substitute3_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) {a b c : TernaryPolynomial}
    (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    (substitute3 f a b c).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hf
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

private theorem twice_X_homogeneous (i : Fin 3) :
    (2 * X i : TernaryPolynomial).IsHomogeneous 1 := by
  simpa only [map_ofNat] using (isHomogeneous_X ℚ i).C_mul 2

/-- The first alternating frame preserves homogeneous degree. -/
theorem alternatingFrame1_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (alternatingFrame1 f).IsHomogeneous n :=
  substitute3_homogeneous hf ((isHomogeneous_X ℚ 2).sub (twice_X_homogeneous 1))
    (isHomogeneous_X ℚ 0).neg ((isHomogeneous_X ℚ 0).sub (isHomogeneous_X ℚ 1))

private theorem middleFrame_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    (substitute3 f (X 2 - X 0) (X 0 - 2 * X 1) (-X 1)).IsHomogeneous n :=
  substitute3_homogeneous hf ((isHomogeneous_X ℚ 2).sub (isHomogeneous_X ℚ 0))
    ((isHomogeneous_X ℚ 0).sub (twice_X_homogeneous 1)) (isHomogeneous_X ℚ 1).neg

private theorem lastFrame_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    (substitute3 f (X 2 - 2 * X 1) (X 1 - X 0) (X 0 - 2 * X 1)).IsHomogeneous n :=
  substitute3_homogeneous hf ((isHomogeneous_X ℚ 2).sub (twice_X_homogeneous 1))
    ((isHomogeneous_X ℚ 1).sub (isHomogeneous_X ℚ 0))
    ((isHomogeneous_X ℚ 0).sub (twice_X_homogeneous 1))

/-- The second alternating frame preserves homogeneous degree. -/
theorem alternatingFrame2_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (alternatingFrame2 f).IsHomogeneous n :=
  ((alternatingFrame1_homogeneous hf).add (middleFrame_homogeneous hf)).add
    (lastFrame_homogeneous hf)

/-- The first symmetric frame preserves homogeneous degree. -/
theorem symmetricFrame1_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (symmetricFrame1 f).IsHomogeneous n :=
  alternatingFrame1_homogeneous hf

/-- The second symmetric frame preserves homogeneous degree. -/
theorem symmetricFrame2_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (symmetricFrame2 f).IsHomogeneous n :=
  ((symmetricFrame1_homogeneous hf).sub (middleFrame_homogeneous hf)).add
    (lastFrame_homogeneous hf)

/-- The alternating Todd expression increases homogeneous degree by one. -/
theorem alternatingTodd_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (alternatingTodd f).IsHomogeneous (n + 1) := by
  simpa only [alternatingTodd, Nat.add_comm 1 n] using
    ((isHomogeneous_X ℚ 2).mul
      (ternaryTodd_homogeneous (alternatingFrame1_homogeneous hf) (isHomogeneous_X ℚ 0))).sub
    ((isHomogeneous_X ℚ 1).mul
      (ternaryTodd_homogeneous (alternatingFrame2_homogeneous hf) (isHomogeneous_X ℚ 1)))

/-- The symmetric Todd expression increases homogeneous degree by one. -/
theorem symmetricTodd_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (symmetricTodd f).IsHomogeneous (n + 1) := by
  simpa only [symmetricTodd, Nat.add_comm 1 n] using
    ((isHomogeneous_X ℚ 2).mul
      (ternaryTodd_homogeneous (symmetricFrame1_homogeneous hf) (isHomogeneous_X ℚ 0))).sub
    ((isHomogeneous_X ℚ 1).mul
      (ternaryTodd_homogeneous (symmetricFrame2_homogeneous hf) (isHomogeneous_X ℚ 1)))

/-- The genuine binary symmetric scalar has the same degree as the Todd expression. -/
theorem symmetricScalar_homogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (symmetricScalar f).IsHomogeneous (n + 1) :=
  (symmetricTodd_homogeneous hf).finSuccEquiv_coeff_isHomogeneous 0 (n + 1) (Nat.zero_add _)

end TernaryPoly
