module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineLocalOp

@[expose] public section


/-!
# The radical restriction at the good line

The radical `U = ℤ²` of the good-line stabilizer acts on `V = Sym^n ⊗ det⁻¹` by lower unipotents,
whose coinvariants are spanned by `X₂ⁿ`: the coefficient `κ` of `X₂ⁿ` is `U`-invariant
(`kappa_rhoU`), kills the infinitesimal generators, and its kernel is `N₀ V + N₁ V`
(`mem_span_of_kappa`). A two-cocycle on `U` is a coboundary as soon as `κ` kills its alternation
(`H2_zero_of_kappa`). On the alternation, the local Hecke operator acts by the scalar
`λ_p = p + 1 + εp^{-(n+1)}` (`kappaAlt_hecke`), so `T x - λ_p x` has vanishing radical restriction
for every class `x` (`hecke_sub_mem_KL`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.GoodLineRestriction

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets LineCoordinates GoodLineCosets GoodLineEdge
open IdentityPlaneCoordinate GoodLineCoordinate GoodLineHecke LocalHecke AmbientHecke

attribute [local instance] complexEndRationalAlgebra

variable (n : ℕ)

/-! ### The coefficient of `X₂ⁿ` -/

/-- The coefficient of `X₂ⁿ`. -/
def kappa : HomogeneousPoly n →ₗ[ℂ] ℂ where
  toFun v := v.val.coeff (Finsupp.single 2 n)
  map_add' v w := by simp
  map_smul' a v := by simp

theorem coeff_X_mul_zero (i : Fin 3) (hi : i ≠ 2) (m : ℕ) (g : Poly) :
    (X i * g).coeff (Finsupp.single 2 m) = 0 := by
  rw [mul_comm, MvPolynomial.coeff_mul_X']
  rw [ite_eq_right]
  simp [Finsupp.mem_support_iff, hi.symm]

theorem kappa_N (i : Fin 2) (v : HomogeneousPoly n) : kappa n (lowerRadicalGenerator n i v) = 0 := by
  change (lowerRadicalGenerator n i v).val.coeff (Finsupp.single 2 n) = 0
  rw [lowerGen_val, MvPolynomial.coeff_smul, coeff_X_mul_zero _ (by fin_cases i <;> decide), smul_zero]

theorem kappa_exp (i : Fin 2) (v : HomogeneousPoly n) :
    kappa n (IsNilpotent.exp (lowerRadicalGenerator n i) v) = kappa n v := by
  have e := nilpotent_difference_apply (lowerRadicalGenerator n i) n
    (lowerRadicalGenerator_power_zero n i) v
  rw [LinearMap.sub_apply, Module.End.one_apply] at e
  have hc := (nilpotentExponentialAverage_commute (lowerRadicalGenerator n i) (n + 1)).eq
  have e' : IsNilpotent.exp (lowerRadicalGenerator n i) v =
      v + lowerRadicalGenerator n i (nilpotentExponentialAverage (lowerRadicalGenerator n i) (n + 1) v) := by
    rw [← sub_eq_iff_eq_add', exp_inst_irrel _ Algebra.toModule]
    exact e.trans (LinearMap.congr_fun hc v).symm
  rw [e', map_add, kappa_N, add_zero]

theorem kappa_rhoU (u : RadicalLattice) (v : HomogeneousPoly n) :
    kappa n (ρn n (lowerRadicalLattice u) v) = kappa n v := by
  let H : Subgroup RadicalLattice :=
    { carrier := {u | ∀ v, kappa n (ρn n (lowerRadicalLattice u) v) = kappa n v}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro a b ha hb v
        rw [map_mul, map_mul, Module.End.mul_apply, ha, hb]
      inv_mem' := by
        intro a ha v
        have := ha (ρn n (lowerRadicalLattice a⁻¹) v)
        rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
          Module.End.one_apply] at this
        exact this.symm }
  have h1 : radicalLatticeFirst ∈ H := by
    intro v
    have := kappa_exp n 0 v
    rwa [← lowerRadicalLatticeRep_first n] at this
  have h2 : radicalLatticeSecond ∈ H := by
    intro v
    have := kappa_exp n 1 v
    rwa [← lowerRadicalLatticeRep_second n] at this
  obtain ⟨a, b, rfl⟩ := radicalLattice_generated u
  exact H.mul_mem (H.zpow_mem h1 a) (H.zpow_mem h2 b) v

theorem coeff_mul_X2 (m : ℕ) (g : Poly) :
    (g * X 2).coeff (Finsupp.single 2 (m + 1)) = g.coeff (Finsupp.single 2 m) := by
  rw [MvPolynomial.coeff_mul_X']
  rw [ite_eq_left (by simp)]
  congr 1
  ext k
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem coeff_zero_mul_X2 (g : Poly) :
    (g * X 2).coeff (Finsupp.single 2 0) = 0 := by
  rw [MvPolynomial.coeff_mul_X', ite_eq_right (by simp)]

theorem coeff_mul_X_zero (i : Fin 3) (hi : i ≠ 2) (m : ℕ) (g : Poly) :
    (g * X i).coeff (Finsupp.single 2 m) = 0 := by
  rw [mul_comm]
  exact coeff_X_mul_zero i hi m g

/-- **Substitution by a plane block scales the coefficient of `X₂ᵐ` by `sᵐ`.** -/
theorem coeff_subst (M : Matrix (Fin 2) (Fin 2) ℂ) (sc : ℂ) (f : Poly) :
    ∀ m : ℕ, (substitute (planeBlock M sc) f).coeff (Finsupp.single 2 m) =
      sc ^ m * f.coeff (Finsupp.single 2 m) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro m
    rw [show substitute (planeBlock M sc) (C a) = C a from MvPolynomial.bind₁_C_right _ _,
      MvPolynomial.coeff_C]
    split_ifs with h
    · have : m = 0 := by
        have := congrArg (fun x : Fin 3 →₀ ℕ => x 2) h
        simpa using this.symm
      subst this
      simp
    · simp
  | add f g hf hg =>
    intro m
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, mul_add]
  | mul_X f i hf =>
    intro m
    rw [map_mul, substitute_X]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [coeff_mul_X_zero 0 (by decide)]
      have hl : linearForm (planeBlock M sc) 0 = C (M 0 0) * X 0 + C (M 0 1) * X 1 := by
        simp [linearForm, planeBlock, Fin.sum_univ_three]
      rw [hl, mul_add, ← mul_assoc, ← mul_assoc, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_X_zero 0 (by decide),
        coeff_mul_X_zero 1 (by decide)]
      simp
    · simp only [Fin.mk_one, Fin.isValue]
      rw [coeff_mul_X_zero 1 (by decide)]
      have hl : linearForm (planeBlock M sc) 1 = C (M 1 0) * X 0 + C (M 1 1) * X 1 := by
        simp [linearForm, planeBlock, Fin.sum_univ_three]
      rw [hl, mul_add, ← mul_assoc, ← mul_assoc, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_X_zero 0 (by decide),
        coeff_mul_X_zero 1 (by decide)]
      simp
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [planeBlock_linearForm_third, mul_comm (C sc) (X 2), ← mul_assoc, mul_comm _ (C sc),
        MvPolynomial.coeff_C_mul]
      cases m with
      | zero => rw [coeff_zero_mul_X2, coeff_zero_mul_X2]; simp
      | succ m => rw [coeff_mul_X2, coeff_mul_X2, hf m]; ring

/-- **The Levi action on the coefficient of `X₂ⁿ`.** -/
theorem kappa_levi (B : Binary.GL2) (d : ℂˣ) (v : HomogeneousPoly n) :
    kappa n (homogeneousAction n (-1) (planeLevi B d) v) =
      ((B.val.det)⁻¹ * ((d : ℂ)⁻¹) ^ (n + 1)) * kappa n v := by
  change (action (-1) (planeLevi B d) v.val).coeff (Finsupp.single 2 n) = _
  rw [action_apply, planeLevi_determinantCharacter, planeLevi_inverse, planeLevi_value,
    MvPolynomial.coeff_smul, coeff_subst]
  change _ = _ * v.val.coeff (Finsupp.single 2 n)
  simp only [Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, _root_.zpow_neg_one,
    Units.val_inv_eq_inv_val, smul_eq_mul, GeneralLinearGroup.val_det_apply]
  ring

/-! ### The kernel of `κ` -/

theorem monomial_eq3 (m : Fin 3 →₀ ℕ) (a : ℂ) :
    monomial m a = C a * (X 0 ^ m 0 * X 1 ^ m 1 * X 2 ^ m 2) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_three]

theorem deg3 (v : HomogeneousPoly n) {m : Fin 3 →₀ ℕ} (h : v.val.coeff m ≠ 0) :
    m 0 + m 1 + m 2 = n := by
  have h1 := v.property h
  have h2 : m.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact h1
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at h2
  exact h2

/-- A homogeneous monomial term. -/
def termHP (k l e : ℕ) (c : ℂ) (h : k + l + e = n) : HomogeneousPoly n :=
  ⟨C c * (X 0 ^ k * X 1 ^ l * X 2 ^ e), by
    have := (((isHomogeneous_X_pow (R := ℂ) (0 : Fin 3) k).mul (isHomogeneous_X_pow 1 l)).mul
      (isHomogeneous_X_pow 2 e)).C_mul c
    rw [h] at this
    exact this⟩

theorem N0_term (k l e : ℕ) (a : ℂ) (h : k + l + (e + 1) = n) :
    (lowerRadicalGenerator n 0 (termHP n k l (e + 1) (-a / (3 * ((e : ℂ) + 1))) h)).val =
      C a * (X 0 ^ (k + 1) * X 1 ^ l * X 2 ^ e) := by
  rw [lowerGen_val]
  change (-3 : ℂ) • (X 0 * pderiv 2 (C (-a / (3 * ((e : ℂ) + 1))) * (X 0 ^ k * X 1 ^ l * X 2 ^ (e + 1)))) = _
  simp only [Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X,
    Pi.single_apply, smul_eq_mul, Fin.isValue]
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ite_false, ite_true,
    smul_zero, mul_zero, add_zero, Nat.add_sub_cancel]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  have he : (3 * ((e : ℂ) + 1)) ≠ 0 := by
    have : ((e : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
    exact mul_ne_zero (by norm_num) this
  have hC : (C a : Poly) = C (-3 : ℂ) * C (-a / (3 * ((e : ℂ) + 1))) * C ((e : ℂ) + 1) := by
    rw [← C_mul, ← C_mul]
    congr 1
    field_simp
  rw [hC, nsmul_eq_mul, map_add, map_one, map_natCast]
  push_cast
  ring

theorem N1_term (l e : ℕ) (a : ℂ) (h : 0 + l + (e + 1) = n) :
    (lowerRadicalGenerator n 1 (termHP n 0 l (e + 1) (-a / (3 * ((e : ℂ) + 1))) h)).val =
      C a * (X 0 ^ 0 * X 1 ^ (l + 1) * X 2 ^ e) := by
  rw [lowerGen_val]
  change (-3 : ℂ) • (X 1 * pderiv 2 (C (-a / (3 * ((e : ℂ) + 1))) * (X 0 ^ 0 * X 1 ^ l * X 2 ^ (e + 1)))) = _
  simp only [Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X,
    Pi.single_apply, smul_eq_mul, Fin.isValue]
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ite_false, ite_true,
    smul_zero, mul_zero, add_zero, Nat.add_sub_cancel]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  have he : (3 * ((e : ℂ) + 1)) ≠ 0 := by
    have : ((e : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
    exact mul_ne_zero (by norm_num) this
  have hC : (C a : Poly) = C (-3 : ℂ) * C (-a / (3 * ((e : ℂ) + 1))) * C ((e : ℂ) + 1) := by
    rw [← C_mul, ← C_mul]
    congr 1
    field_simp
  rw [hC, nsmul_eq_mul, map_add, map_one, map_natCast]
  push_cast
  ring

/-- `N₀ V + N₁ V`. -/
def Wsp : Submodule ℂ (HomogeneousPoly n) :=
  LinearMap.range (lowerRadicalGenerator n 0) ⊔ LinearMap.range (lowerRadicalGenerator n 1)

/-- **The kernel of `κ` is `N₀ V + N₁ V`.** -/
theorem mem_Wsp_of_kappa (v : HomogeneousPoly n) (hv : kappa n v = 0) : v ∈ Wsp n := by
  let Wp : Submodule ℂ Poly := (Wsp n).map (HomogeneousPoly n).subtype
  suffices h : v.val ∈ Wp by
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp h
    rwa [show w = v from Subtype.ext hwv] at hw
  rw [v.val.as_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hc : v.val.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hdeg := deg3 n v hc
  have hne : ¬ (m 0 = 0 ∧ m 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hc
    have : m = Finsupp.single 2 n := by
      ext i
      fin_cases i
      · simp [h0]
      · simp [h1]
      · simp only [Fin.reduceFinMk, Finsupp.single_eq_same]
        omega
    rw [this]
    exact hv
  rw [monomial_eq3]
  by_cases h0 : m 0 = 0
  · have h1 : m 1 ≠ 0 := fun h1 => hne ⟨h0, h1⟩
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero h1
    have hsum : 0 + l + (m 2 + 1) = n := by omega
    rw [h0, hl, ← N1_term n l (m 2) _ hsum]
    exact Submodule.mem_map_of_mem (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hsum : k + m 1 + (m 2 + 1) = n := by omega
    rw [hk, ← N0_term n k (m 1) (m 2) _ hsum]
    exact Submodule.mem_map_of_mem (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))

theorem N_eq_exp_sub (i : Fin 2) (g : HomogeneousPoly n) :
    lowerRadicalGenerator n i g =
      (IsNilpotent.exp (lowerRadicalGenerator n i) - 1) ((lowerRadicalAverageEquiv n i).symm g) := by
  rw [exp_inst_irrel _ Algebra.toModule]
  have e := nilpotent_difference_apply (lowerRadicalGenerator n i) n
    (lowerRadicalGenerator_power_zero n i) ((lowerRadicalAverageEquiv n i).symm g)
  have hc := (nilpotentExponentialAverage_commute (lowerRadicalGenerator n i) (n + 1)).eq
  have hg : nilpotentExponentialAverage (lowerRadicalGenerator n i) (n + 1)
      ((lowerRadicalAverageEquiv n i).symm g) = g := (lowerRadicalAverageEquiv n i).apply_symm_apply g
  refine (?_ : _ = _).trans e.symm
  calc lowerRadicalGenerator n i g
      = lowerRadicalGenerator n i (nilpotentExponentialAverage (lowerRadicalGenerator n i) (n + 1)
          ((lowerRadicalAverageEquiv n i).symm g)) := (congrArg _ hg).symm
    _ = nilpotentExponentialAverage (lowerRadicalGenerator n i) (n + 1)
          (lowerRadicalGenerator n i ((lowerRadicalAverageEquiv n i).symm g)) := by
      have := LinearMap.congr_fun hc ((lowerRadicalAverageEquiv n i).symm g)
      simpa only [Module.End.mul_apply] using this

/-- **A two-cocycle on the lower radical is a coboundary when `κ` kills its alternation.** -/
theorem H2_zero_of_kappa (z : groupCohomology.cocycles₂ (lowerRadicalLatticeRep n))
    (hz : kappa n (latticeTwoCocycleAlternation (lowerRadicalLatticeRep n) z) = 0) :
    groupCohomology.H2π (lowerRadicalLatticeRep n) z = 0 := by
  obtain ⟨y, ⟨g0, rfl⟩, w, ⟨g1, rfl⟩, hyw⟩ := Submodule.mem_sup.mp (mem_Wsp_of_kappa n _ hz)
  apply (latticeTwoCocycle_H2_zero_iff (lowerRadicalLatticeRep n) z).mpr
  refine ⟨(lowerRadicalAverageEquiv n 1).symm (-g1), (lowerRadicalAverageEquiv n 0).symm g0, ?_⟩
  have h0 : ((lowerRadicalLatticeRep n).ρ radicalLatticeFirst - 1) ((lowerRadicalAverageEquiv n 0).symm g0) =
      lowerRadicalGenerator n 0 g0 := by
    rw [lowerRadicalLatticeRep_first]; exact (N_eq_exp_sub n 0 g0).symm
  have h1 : ((lowerRadicalLatticeRep n).ρ radicalLatticeSecond - 1) ((lowerRadicalAverageEquiv n 1).symm (-g1)) =
      lowerRadicalGenerator n 1 (-g1) := by
    rw [lowerRadicalLatticeRep_second]; exact (N_eq_exp_sub n 1 (-g1)).symm
  have key : lowerRadicalGenerator n 0 g0 + lowerRadicalGenerator n 1 g1 =
      lowerRadicalGenerator n 0 g0 - lowerRadicalGenerator n 1 (-g1) := by
    rw [map_neg, sub_neg_eq_add]
  exact hyw.symm.trans (key.trans (congrArg₂ (· - ·) h0.symm h1.symm))

/-! ### Alternation of scalar two-cocycles on `ℤ²` -/

section Alt

variable (f : ℤ × ℤ → ℤ × ℤ → ℂ) (hf : ∀ x y z, f (x + y) z + f x y = f y z + f x (y + z))

/-- The alternation `A(x, y) = f(x, y) - f(y, x)`. -/
def altF (x y : ℤ × ℤ) : ℂ := f x y - f y x

include hf in
theorem f_zero_left (y : ℤ × ℤ) : f 0 y = f 0 0 := by
  have h := hf 0 0 y
  simp only [zero_add] at h
  linear_combination -h

include hf in
theorem f_zero_right (x : ℤ × ℤ) : f x 0 = f 0 0 := by
  have h := hf x 0 0
  simp only [add_zero] at h
  linear_combination h

include hf in
theorem altF_add_left (x y z : ℤ × ℤ) : altF f (x + y) z = altF f x z + altF f y z := by
  have h1 := hf x y z
  have h2 := hf x z y
  have h3 := hf z x y
  rw [add_comm z x] at h3
  rw [add_comm z y] at h2
  unfold altF
  linear_combination h1 + h3 - h2

include hf in
theorem altF_add_right (x y z : ℤ × ℤ) : altF f x (y + z) = altF f x y + altF f x z := by
  have h := altF_add_left f hf y z x
  unfold altF at h ⊢
  linear_combination -h

include hf in
theorem altF_zero_left (y : ℤ × ℤ) : altF f 0 y = 0 := by
  unfold altF
  rw [f_zero_left f hf y, f_zero_right f hf y, sub_self]

include hf in
theorem altF_smul_left (k : ℤ) (x y : ℤ × ℤ) : altF f (k • x) y = k * altF f x y := by
  let φ : ℤ × ℤ →+ ℂ := AddMonoidHom.mk' (fun x => altF f x y) (fun a b => altF_add_left f hf a b y)
  have := map_zsmul φ k x
  simpa [φ] using this

include hf in
theorem altF_smul_right (k : ℤ) (x y : ℤ × ℤ) : altF f x (k • y) = k * altF f x y := by
  have h := altF_smul_left f hf k y x
  unfold altF at h ⊢
  linear_combination -h

include hf in
/-- **The alternation is the determinant form.** -/
theorem altF_eq (x y : ℤ × ℤ) :
    altF f x y = ((x.1 * y.2 - x.2 * y.1 : ℤ) : ℂ) * altF f (1, 0) (0, 1) := by
  have hx : x = x.1 • ((1, 0) : ℤ × ℤ) + x.2 • ((0, 1) : ℤ × ℤ) := by ext <;> simp
  have hy : y = y.1 • ((1, 0) : ℤ × ℤ) + y.2 • ((0, 1) : ℤ × ℤ) := by ext <;> simp
  have h11 : altF f (1, 0) (1, 0) = 0 := by unfold altF; ring
  have h22 : altF f (0, 1) (0, 1) = 0 := by unfold altF; ring
  have h21 : altF f (0, 1) (1, 0) = -altF f (1, 0) (0, 1) := by unfold altF; ring
  conv_lhs => rw [hx, hy]
  rw [altF_add_left f hf, altF_smul_left f hf, altF_smul_left f hf, altF_add_right f hf,
    altF_add_right f hf, altF_smul_right f hf, altF_smul_right f hf, altF_smul_right f hf,
    altF_smul_right f hf, h11, h22, h21]
  push_cast
  ring

end Alt

/-! ### The radical residues of the unit vectors -/

section Residues

variable (p : Nat.Primes)

theorem ediv_pred (a : Fin p.val) : ((a.val : ℤ) - 1) / (p.val : ℤ) = if a.val = 0 then -1 else 0 := by
  have hp := p_pos p
  have hp1 : (1 : ℤ) < p.val := by exact_mod_cast p.property.one_lt
  have ha := a.isLt
  split_ifs with h
  · rw [h]
    simp only [Nat.cast_zero, zero_sub]
    exact ((Int.ediv_emod_unique (a := -1) (b := (p.val : ℤ)) (q := -1) (r := p.val - 1) hp).mpr
      ⟨by ring, by omega, by omega⟩).1
  · exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

theorem ediv_fin (a : Fin p.val) : (a.val : ℤ) / (p.val : ℤ) = 0 :=
  Int.ediv_eq_zero_of_lt (by omega) (by have := a.isLt; omega)

theorem res1_fin (a : Fin p.val) : res1 p (a.val : ℤ) = a := by
  apply Fin.ext
  have := res1_val p (a.val : ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by have := a.isLt; omega)] at this
  exact_mod_cast this

/-- `w_c(e₁) = (s·[c₁ = 0], 0)`. -/
theorem w_e1 (c : Fin p.val × Fin p.val) :
    -cq p (cvec p c - (1, 0)) = (if c.1.val = 0 then sgnL p else 0, 0) := by
  simp only [cq, cvec, Prod.fst_sub, Prod.snd_sub, sub_zero, ediv_pred, ediv_fin, Prod.neg_mk]
  refine Prod.ext ?_ ?_
  · dsimp only
    split_ifs <;> simp
  · simp

/-- `w_c(e₂) = (0, s·[c₂ = 0])`. -/
theorem w_e2 (c : Fin p.val × Fin p.val) :
    -cq p (cvec p c - (0, 1)) = (0, if c.2.val = 0 then sgnL p else 0) := by
  simp only [cq, cvec, Prod.fst_sub, Prod.snd_sub, sub_zero, ediv_pred, ediv_fin, Prod.neg_mk]
  refine Prod.ext ?_ ?_
  · simp
  · dsimp only
    split_ifs <;> simp

theorem crep_e1_snd (c : Fin p.val × Fin p.val) : (crep p (cvec p c - (1, 0))).2 = c.2 := by
  simp only [crep, cvec, Prod.snd_sub, sub_zero, res1_fin]

theorem crep_e2_fst (c : Fin p.val × Fin p.val) : (crep p (cvec p c - (0, 1))).1 = c.1 := by
  simp only [crep, cvec, Prod.fst_sub, sub_zero, res1_fin]

variable (f : ℤ × ℤ → ℤ × ℤ → ℂ) (hf : ∀ x y z, f (x + y) z + f x y = f y z + f x (y + z))

include hf in
/-- **The radical corestriction preserves the alternation.** -/
theorem radical_alt_sum :
    ∑ c : Fin p.val × Fin p.val,
      (f (-cq p (cvec p c - (1, 0))) (-cq p (cvec p (crep p (cvec p c - (1, 0))) - (0, 1))) -
        f (-cq p (cvec p c - (0, 1))) (-cq p (cvec p (crep p (cvec p c - (0, 1))) - (1, 0)))) =
      altF f (1, 0) (0, 1) := by
  simp only [w_e1, w_e2, crep_e1_snd, crep_e2_fst]
  have hz : ((0 : Fin p.val), (0 : Fin p.val)) = ((⟨0, p.property.pos⟩ : Fin p.val), (⟨0, p.property.pos⟩ : Fin p.val)) := rfl
  rw [Finset.sum_eq_single ((⟨0, p.property.pos⟩ : Fin p.val), (⟨0, p.property.pos⟩ : Fin p.val))]
  · simp only [ite_true]
    have h := altF_eq f hf (sgnL p, 0) (0, sgnL p)
    have hs := sgnL_sq p
    unfold altF at h ⊢
    rw [h]
    simp only [mul_zero, sub_zero]
    push_cast
    rw [show ((sgnL p : ℂ)) * (sgnL p : ℂ) = 1 by exact_mod_cast hs, one_mul]
  · rintro ⟨c1, c2⟩ - hne
    by_cases h1 : c1.val = 0
    · have h2 : c2.val ≠ 0 := by
        intro h2
        apply hne
        ext <;> simp [h1, h2]
      simp only [h1, h2, ite_true, ite_false, Prod.mk_zero_zero]
      rw [f_zero_right f hf (sgnL p, 0), f_zero_left f hf (sgnL p, 0), sub_self]
    · simp only [h1, ite_false, Prod.mk_zero_zero]
      generalize ((0 : ℤ), (if c2.val = 0 then sgnL p else 0 : ℤ)) = y
      rw [f_zero_left f hf y, f_zero_right f hf y, sub_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Residues

/-! ### The local Hecke operator on the alternation -/

section HeckeAlt

variable (p : Nat.Primes)

/-- `κ` on the coefficients of `Λ₁`. -/
abbrev kappaA : Aρ1 (ρn n) →ₗ[ℂ] ℂ := kappa n

theorem kappa_ell (j : Option (Fin p.val)) (w : HomogeneousPoly n) :
    kappa n (ρn n (rExpl p (.inl j)) w) = (p.val : ℂ)⁻¹ * kappa n w := by
  change kappa n (ρn n (Q 0 (BGL p j) 1) w) = _
  rw [rho_leviQ, kappa_levi]
  have hdet : (cx2 (BGL p j)).val.det = (p.val : ℂ) := by
    have h1 : ((BGL p j).val.map (algebraMap ℚ ℂ)).det = algebraMap ℚ ℂ ((BGL p j).val.det) :=
      (RingHom.map_det _ _).symm
    change ((BGL p j).val.map (algebraMap ℚ ℂ)).det = _
    rw [h1]
    simp [BGL_val, Bmat_det]
  rw [hdet]
  simp

theorem kappa_tau (c : Fin p.val × Fin p.val) (w : HomogeneousPoly n) :
    kappa n (ρn n (rExpl p (.inr c)) w) = ((epsP p : ℂ)⁻¹) ^ (n + 1) * kappa n w := by
  rw [rho_tau, kappa_rhoU, kappa_levi, epsC_val]
  simp

theorem det_Bint (j : Option (Fin p.val)) :
    (ivmul (1, 0) (Bint p j)).1 * (ivmul (0, 1) (Bint p j)).2 -
      (ivmul (1, 0) (Bint p j)).2 * (ivmul (0, 1) (Bint p j)).1 = p.val := by
  cases j <;> simp [ivmul, Bint]

/-- The scalar `κ`-alternation of a two-cocycle restricted to the radical. -/
def kappaAlt (z : groupCohomology.cocycles₂ (Aρ1 (ρn n))) : ℂ :=
  kappaA n (z (U1 (1, 0), U1 (0, 1))) - kappaA n (z (U1 (0, 1), U1 (1, 0)))

theorem kappaAlt_eq (z : groupCohomology.cocycles₂ (goodLineCoefficientRep n)) :
    kappaAlt n z = kappa n (latticeTwoCocycleAlternation (lowerRadicalLatticeRep n)
      (twoCocycleRestriction goodLineRadicalInclusion (goodLineCoefficientRep n) z)) := by
  have h1 := inl1_eq radicalLatticeFirst
  have h2 := inl1_eq radicalLatticeSecond
  change _ = kappa n (z (goodLineRadicalInclusion radicalLatticeFirst,
    goodLineRadicalInclusion radicalLatticeSecond) - z (goodLineRadicalInclusion radicalLatticeSecond,
      goodLineRadicalInclusion radicalLatticeFirst))
  rw [h1, h2]
  exact (map_sub (kappa n) _ _).symm

theorem cocycle_kappa (z : groupCohomology.cocycles₂ (Aρ1 (ρn n))) (x y w : ℤ × ℤ) :
    kappaA n (z (U1 (x + y), U1 w)) + kappaA n (z (U1 x, U1 y)) =
      kappaA n (z (U1 y, U1 w)) + kappaA n (z (U1 x, U1 (y + w))) := by
  have h := twoCocycle_relation (Aρ1 (ρn n)) z (U1 x) (U1 y) (U1 w)
  rw [U1_mul, U1_mul] at h
  have h2 := congrArg (kappaA n) h
  rw [map_add, map_add] at h2
  refine h2.trans ?_
  congr 1
  exact (congrArg (kappa n) (rho_U n x _)).trans (kappa_rhoU n _ _)

/-- **The local Hecke operator multiplies the `κ`-alternation by `p + 1 + εp^{-(n+1)}`.** -/
theorem kappaAlt_hecke (z : groupCohomology.cocycles₂ (Aρ1 (ρn n))) :
    kappaAlt n (heckeTwoL p (ρn n) z) =
      ((p.val : ℂ) + 1 + ((epsP p : ℂ)⁻¹) ^ (n + 1)) * kappaAlt n z := by
  set f : ℤ × ℤ → ℤ × ℤ → ℂ := fun x y => kappaA n (z (U1 x, U1 y))
  have hf : ∀ x y w, f (x + y) w + f x y = f y w + f x (y + w) := cocycle_kappa n z
  have hval : ∀ a b : ℤ × ℤ, kappaA n (heckeTwoL p (ρn n) z (U1 a, U1 b)) =
      (∑ j : Option (Fin p.val), (p.val : ℂ)⁻¹ * f (ivmul a (Bint p j)) (ivmul b (Bint p j))) +
        ∑ c : Fin p.val × Fin p.val, ((epsP p : ℂ)⁻¹) ^ (n + 1) *
          f (-cq p (cvec p c - a)) (-cq p (cvec p (crep p (cvec p c - a)) - b)) := by
    intro a b
    rw [heckeTwoL_apply, Fintype.sum_sum_type]
    simp only [delta_U_inl, next_U_inl, delta_U_inr, next_U_inr, map_add, map_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl (fun j _ => kappa_ell n p j _))
      (Finset.sum_congr rfl (fun c _ => kappa_tau n p c _))
  have hA : kappaAlt n z = altF f (1, 0) (0, 1) := rfl
  have hlevi : ∀ j : Option (Fin p.val),
      f (ivmul (1, 0) (Bint p j)) (ivmul (0, 1) (Bint p j)) -
        f (ivmul (0, 1) (Bint p j)) (ivmul (1, 0) (Bint p j)) = (p.val : ℂ) * altF f (1, 0) (0, 1) := by
    intro j
    have h := altF_eq f hf (ivmul (1, 0) (Bint p j)) (ivmul (0, 1) (Bint p j))
    unfold altF at h
    rw [h, det_Bint]
    push_cast
    rfl
  have hrad := radical_alt_sum p f hf
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  unfold kappaAlt
  rw [hval, hval]
  change _ = _ * altF f (1, 0) (0, 1)
  calc _ = (p.val : ℂ)⁻¹ * ∑ j : Option (Fin p.val),
        (f (ivmul (1, 0) (Bint p j)) (ivmul (0, 1) (Bint p j)) -
          f (ivmul (0, 1) (Bint p j)) (ivmul (1, 0) (Bint p j))) +
      ((epsP p : ℂ)⁻¹) ^ (n + 1) * ∑ c : Fin p.val × Fin p.val,
        (f (-cq p (cvec p c - (1, 0))) (-cq p (cvec p (crep p (cvec p c - (1, 0))) - (0, 1))) -
          f (-cq p (cvec p c - (0, 1))) (-cq p (cvec p (crep p (cvec p c - (0, 1))) - (1, 0)))) := by
        simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
        ring
    _ = _ := by
        rw [Finset.sum_congr rfl (fun j _ => hlevi j), hrad, Finset.sum_const, Finset.card_univ,
          Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        push_cast
        ring

end HeckeAlt

/-! ### The local Hecke operator modulo `KL` -/

/-- The scalar `λ_p = p + 1 + εp^{-(n+1)}` on the radical part. -/
def lamL (p : Nat.Primes) : ℂ := (p.val : ℂ) + 1 + ((epsP p : ℂ)⁻¹) ^ (n + 1)

theorem kappaAlt_sub_smul (z w : groupCohomology.cocycles₂ (Aρ1 (ρn n))) (a : ℂ) :
    kappaAlt n (z - a • w) = kappaAlt n z - a * kappaAlt n w := by
  unfold kappaAlt
  change kappaA n (z _ - a • w _) - kappaA n (z _ - a • w _) = _
  rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Modulo the kernel of the radical restriction, the local `T_p` is the scalar `λ_p`.** -/
theorem hecke_sub_mem_KL (p : Nat.Primes) (x : H2 Λ₁ (ρn n)) :
    cohomologyAction (ρn n) (goodLineCosets p) x - lamL n p • x ∈ KL n := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  let z : groupCohomology.cocycles₂ (goodLineCoefficientRep n) := ambientCocycleToGroup Λ₁ (ρn n) C
  let w : groupCohomology.cocycles₂ (goodLineCoefficientRep n) :=
    heckeTwoL p (ρn n) (ambientCocycleToGroup Λ₁ (ρn n) C)
  have hT : toH2L n (cohomologyAction (ρn n) (goodLineCosets p) (classOf Λ₁ (ρn n) C)) =
      groupCohomology.H2π (goodLineCoefficientRep n) w := by
    rw [cohomologyAction_classOf, toH2L_classOf]
    exact ambientHecke_class (goodLineCosets p) (ρn n) C
  have hz : toH2L n (classOf Λ₁ (ρn n) C) = groupCohomology.H2π (goodLineCoefficientRep n) z := rfl
  change toH2L n (cohomologyAction (ρn n) (goodLineCosets p) (classOf Λ₁ (ρn n) C) -
    lamL n p • classOf Λ₁ (ρn n) C) ∈
      LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))
  rw [map_sub, map_smul, hT, hz, LinearMap.mem_ker, map_sub, map_smul,
    twoCohomologyRestriction_apply, twoCohomologyRestriction_apply, ← map_smul, ← map_sub, ← map_smul,
    ← map_sub]
  apply H2_zero_of_kappa
  rw [← kappaAlt_eq]
  change kappaAlt n (heckeTwoL p (ρn n) (ambientCocycleToGroup Λ₁ (ρn n) C) -
    lamL n p • ambientCocycleToGroup Λ₁ (ρn n) C) = 0
  rw [kappaAlt_sub_smul, kappaAlt_hecke, lamL, sub_self]

open GoodLineLocalOp CuspOrbits CuspReduction TernaryPeriodPolynomials.HeckeEigen.Satake in
/-- **The local `T_p` at the good-line cusp modulo `KL`.** For every away-from-three correspondence
`t` of `Γ diag(p,1,1) Γ` (`p ≠ 3`), `ψ(localOp t y) - λ_p ψ(y)` has vanishing radical restriction,
where `λ_p = p + 1 + εp^{-(n+1)}`. -/
theorem localOp_sub_mem_KL (p : Nat.Primes) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP p.property) (hp3 : p.val ≠ 3) (y : CuspH2 n trivialCharacter .line true) :
    psiL n (localOp n trivialCharacter t ht .line true y) - lamL n p • psiL n y ∈ KL n := by
  rw [transport_localOp n p t ht hg hp3 y]
  exact hecke_sub_mem_KL n p (psiL n y)

end TernaryPeriodPolynomials.Spectral.GoodLineRestriction
