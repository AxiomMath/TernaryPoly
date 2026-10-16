module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.VanishCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.VanishPoly
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitBinaryAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators

@[expose] public section


/-!
# `H²(Γ_F, V_χ) = 0` at the bad line for an odd character

The stabilizer of the standard bad line is the split extension `ℤ² ⋊ (ℤˣ × Γ₁'(3))` of Sol's
`integralBadLineExtension`. For a character `χ` with `χ(-1_∞) = -1` the coefficient representation is
the trivial-character one twisted by the sign of the determinant. Then

* the central element `h = diag(-1, 1, 1)` of the Levi group inverts the radical and acts by `-1`
  on `H¹(ℤ², V)`: by Sol's Kostant computation every class is a homomorphism into the invariants
  `Sym^n(X₁, X₂)`, on which `h` acts by `-1` for the trivial character, i.e. by `+1` for `χ` odd
  (`bl_hneg`);
* the restriction `H²(Γ_F, V) → H²(ℤ², V)` vanishes: `H²(ℤ², V)` is detected by the coefficient
  `κ` of `X₀ⁿ`, which is invariant under the Levi reflection `diag(1, -1, 1)`, whereas the reflection
  changes the sign of the alternation of the radical (`bl_restriction_zero_pos`,
  `bl_restriction_zero_zero`);
* `H²` of the Levi group vanishes (`ModularH2`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (reflection)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (RadicalLattice radicalLatticeFirst radicalLatticeSecond splitRadicalInput
    splitRadicalInput_commute splitRadicalCocycleAction splitRadicalCocycleAction_apply
    splitRadicalH1Action splitRadicalH1Action_apply twoCocycle_H2_surjective
    twoCohomologyRestriction twoCohomologyRestriction_apply twoCocycleRestriction
    oneCocycle_H1_surjective latticeTwoCocycleAlternation subgroupCoefficientRep)
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.SourceConstruction

namespace BadLineVanish

variable (n : ℕ) (χ : RankOneCharacter)

/-! ### The representation of the bad-line stabilizer -/

/-- The coefficient representation of the integral bad-line stabilizer, for the character `χ`. -/
abbrev blRep : Rep ℂ integralBadLineStabilizer :=
  Rep.res integralBadLineStabilizerEquiv.toMonoidHom
    (subgroupCoefficientRep (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent n χ))

theorem blRep_apply (g : integralBadLineStabilizer) (v : HomogeneousPoly n) :
    (blRep n χ).ρ g v = rationalCoefficientComponent n χ (integralRational g.val) v := rfl

theorem det_integralRational (g : IntegralGL3) :
    (integralRational g).val.det = ((g.val.det : ℤ) : ℚ) := by
  change (g.val.map (Int.castRingHom ℚ)).det = _
  exact (RingHom.map_det (Int.castRingHom ℚ) g.val).symm

theorem det_lineUnipotent (a b : ℤ) : (lineUnipotent a b).val.det = 1 := by
  simp [lineUnipotent, upperUnipotent, Matrix.det_fin_three]

/-- On the radical lattice the twisted and the trivial-character systems agree. -/
theorem blRep_radical (r : RadicalLattice) :
    (blRep n χ).ρ (integralBadLineExtension.inl r) = radicalRepresentation n r := by
  apply LinearMap.ext
  intro v
  change rationalCoefficientComponent n χ
      (integralRational (lineUnipotent r.toAdd.1 r.toAdd.2)) v =
    rationalCoefficientComponent n trivialCharacter (integralRadicalRationalHom r) v
  have hpos : 0 < (integralRational (lineUnipotent r.toAdd.1 r.toAdd.2)).val.det := by
    rw [det_integralRational, det_lineUnipotent]
    norm_num
  rw [Twisted.rho_eq_of_pos n χ hpos]
  rfl

/-! ### The coefficient of `X₀ⁿ` -/

/-- The coefficient of `X₀ⁿ`. -/
def kappaLin : HomogeneousPoly n →ₗ[ℂ] ℂ where
  toFun v := v.val.coeff (Finsupp.single 0 n)
  map_add' v w := by simp
  map_smul' a v := by simp

/-- For a homogeneous polynomial of degree `n`, the coefficient of `X₀ⁿ` is the value at
`(1, 0, 0)`. -/
theorem kappaLin_eq_eval (v : HomogeneousPoly n) :
    kappaLin n v = MvPolynomial.eval (![1, 0, 0] : Fin 3 → ℂ) v.val := by
  change v.val.coeff (Finsupp.single 0 n) = _
  rw [MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 n)]
  · simp [Finsupp.single_apply]
  · intro d hd hne
    have h3 := GoodLineRestriction.deg3 n v (MvPolynomial.mem_support_iff.mp hd)
    have hprod : ∏ i, (![1, 0, 0] : Fin 3 → ℂ) i ^ d i = 0 := by
      rw [Fin.prod_univ_three]
      by_cases h1 : d 1 = 0
      · by_cases h2 : d 2 = 0
        · exfalso
          apply hne
          ext i
          fin_cases i <;> simp <;> omega
        · simp [h2]
      · simp [h1]
    rw [hprod, mul_zero]
  · intro hnot
    rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]

/-- A matrix whose first column is `e₁` has the same inverse first column. -/
theorem inv_col_zero (G : GL3) (h0 : G.val 0 0 = 1) (h1 : G.val 1 0 = 0) (h2 : G.val 2 0 = 0) :
    (fun i => ∑ j, (G⁻¹ : GL3).val i j * (![1, 0, 0] : Fin 3 → ℂ) j) = ![1, 0, 0] := by
  have hG : G.val.mulVec (![1, 0, 0] : Fin 3 → ℂ) = ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2]
  have h := congrArg (fun w => (G⁻¹ : GL3).val.mulVec w) hG
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
  funext i
  have hi := congrFun h.symm i
  exact hi

/-- **The coefficient `κ` along an integral element fixing `e₁`.** -/
theorem kappa_rho_integral (g : IntegralGL3) (h0 : g.val 0 0 = 1) (h1 : g.val 1 0 = 0)
    (h2 : g.val 2 0 = 0) (v : HomogeneousPoly n) :
    kappaLin n (rationalCoefficientComponent n trivialCharacter (integralRational g) v) =
      ((g.val.det : ℤ) : ℂ)⁻¹ * kappaLin n v := by
  have hG0 : (GeneralLinearGroup.map (Int.castRingHom ℂ) g).val 0 0 = 1 := by
    simp [GeneralLinearGroup.map_apply, h0]
  have hG1 : (GeneralLinearGroup.map (Int.castRingHom ℂ) g).val 1 0 = 0 := by
    simp [GeneralLinearGroup.map_apply, h1]
  have hG2 : (GeneralLinearGroup.map (Int.castRingHom ℂ) g).val 2 0 = 0 := by
    simp [GeneralLinearGroup.map_apply, h2]
  have hdetG : determinantCharacter (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) g) =
      ((g.val.det : ℤ) : ℂ)⁻¹ := by
    change (((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) g) : ℂˣ) : ℂ)) ^
      (-1 : ℤ) = _
    rw [_root_.zpow_neg_one, GeneralLinearGroup.val_det_apply]
    congr 1
    exact (RingHom.map_det (Int.castRingHom ℂ) g.val).symm
  rw [kappaLin_eq_eval, kappaLin_eq_eval, rationalCoefficientComponent_integral_val, action_apply,
    MvPolynomial.smul_eval, eval_substitute3, inv_col_zero _ hG0 hG1 hG2, hdetG]

/-! ### The kernel of `κ` is generated by the radical differences -/

/-- The monomial `c X^m` as an element of `Sym^n`, for `|m| = n`. -/
def monoHP (m : Fin 3 →₀ ℕ) (c : ℂ) (h : m 0 + m 1 + m 2 = n) : HomogeneousPoly n :=
  ⟨MvPolynomial.monomial m c, MvPolynomial.isHomogeneous_monomial c (by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
    exact h)⟩

theorem X_mul_pderiv0_monomial (j : Fin 3) (s : Fin 3 →₀ ℕ) (c : ℂ) :
    (X j : Poly) * pderiv 0 (monomial s c) =
      monomial (Finsupp.single j 1 + (s - Finsupp.single 0 1)) (c * (s 0 : ℂ)) := by
  rw [MvPolynomial.pderiv_monomial]
  change monomial (Finsupp.single j 1) (1 : ℂ) * _ = _
  rw [MvPolynomial.monomial_mul_monomial, one_mul]

theorem radInf0_monoHP (hn : 0 < n) (s : Fin 3 →₀ ℕ) (c : ℂ) (h : s 0 + s 1 + s 2 = n) :
    (radicalInfinitesimal n hn 0 (monoHP n s c h)).val =
      monomial (Finsupp.single 1 1 + (s - Finsupp.single 0 1)) (c * (s 0 : ℂ)) :=
  X_mul_pderiv0_monomial 1 s c

theorem radInf1_monoHP (hn : 0 < n) (s : Fin 3 →₀ ℕ) (c : ℂ) (h : s 0 + s 1 + s 2 = n) :
    (radicalInfinitesimal n hn 1 (monoHP n s c h)).val =
      monomial (Finsupp.single 2 1 + (s - Finsupp.single 0 1)) (c * (s 0 : ℂ)) :=
  X_mul_pderiv0_monomial 2 s c

theorem aux_exps (m : Fin 3 →₀ ℕ) (j : Fin 3) (hj : j = 1 ∨ j = 2) (hm : 1 ≤ m j) :
    Finsupp.single j 1 + (m + Finsupp.single 0 1 - Finsupp.single j 1 - Finsupp.single 0 1) =
      m := by
  ext k
  rcases hj with rfl | rfl <;> fin_cases k <;>
    simp [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

/-- The image of `N₀V + N₁V` in the full polynomial ring. -/
def blWp (hn : 0 < n) : Submodule ℂ Poly :=
  (LinearMap.range (radicalInfinitesimal n hn 0) ⊔
    LinearMap.range (radicalInfinitesimal n hn 1)).map (HomogeneousPoly n).subtype

/-- **The kernel of `κ` is `N₀V + N₁V`.** -/
theorem bl_mem_Wsp (hn : 0 < n) (v : HomogeneousPoly n) (hv : kappaLin n v = 0) :
    v ∈ LinearMap.range (radicalInfinitesimal n hn 0) ⊔
      LinearMap.range (radicalInfinitesimal n hn 1) := by
  suffices h : v.val ∈ blWp n hn by
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp h
    rwa [show w = v from Subtype.ext hwv] at hw
  rw [v.val.as_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hc : v.val.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hdeg := GoodLineRestriction.deg3 n v hc
  have hne : ¬ (m 1 = 0 ∧ m 2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hc
    have : m = Finsupp.single 0 n := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [this]
    exact hv
  by_cases h1 : m 1 = 0
  · have h2 : m 2 ≠ 0 := fun h2 => hne ⟨h1, h2⟩
    have hs := aux_exps m 2 (Or.inr rfl) (Nat.one_le_iff_ne_zero.mpr h2)
    obtain ⟨m', hm'⟩ : ∃ m' : Fin 3 →₀ ℕ, m' = m + Finsupp.single 0 1 - Finsupp.single 2 1 :=
      ⟨_, rfl⟩
    rw [← hm'] at hs
    have e0 : m' 0 = m 0 + 1 := by
      subst hm'
      simp
    have e1 : m' 1 = m 1 := by
      subst hm'
      simp
    have e2 : m' 2 = m 2 - 1 := by
      subst hm'
      simp
    have hsum : m' 0 + m' 1 + m' 2 = n := by
      rw [e0, e1, e2]
      omega
    have key : (radicalInfinitesimal n hn 1 (monoHP n m'
        (v.val.coeff m / ((m 0 : ℂ) + 1)) hsum)).val =
        monomial m (v.val.coeff m) := by
      rw [radInf1_monoHP, hs, e0]
      congr 1
      have : ((m 0 : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m 0)
      push_cast
      field_simp
    exact Submodule.mem_map.mpr ⟨_, Submodule.mem_sup_right (LinearMap.mem_range_self _ _), key⟩
  · have hs := aux_exps m 1 (Or.inl rfl) (Nat.one_le_iff_ne_zero.mpr h1)
    obtain ⟨m', hm'⟩ : ∃ m' : Fin 3 →₀ ℕ, m' = m + Finsupp.single 0 1 - Finsupp.single 1 1 :=
      ⟨_, rfl⟩
    rw [← hm'] at hs
    have e0 : m' 0 = m 0 + 1 := by
      subst hm'
      simp
    have e1 : m' 1 = m 1 - 1 := by
      subst hm'
      simp
    have e2 : m' 2 = m 2 := by
      subst hm'
      simp
    have hsum : m' 0 + m' 1 + m' 2 = n := by
      rw [e0, e1, e2]
      omega
    have key : (radicalInfinitesimal n hn 0 (monoHP n m'
        (v.val.coeff m / ((m 0 : ℂ) + 1)) hsum)).val =
        monomial m (v.val.coeff m) := by
      rw [radInf0_monoHP, hs, e0]
      congr 1
      have : ((m 0 : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m 0)
      push_cast
      field_simp
    exact Submodule.mem_map.mpr ⟨_, Submodule.mem_sup_left (LinearMap.mem_range_self _ _), key⟩

theorem bl_radicalDifference_range (hn : 0 < n) (i : Fin 2) (γ : HomogeneousPoly n) :
    ∃ δ, radicalDifference n i δ = radicalInfinitesimal n hn i γ := by
  let E : HomogeneousPoly n ≃ₗ[ℂ] HomogeneousPoly n :=
    finiteExponentialRatioEquiv n (-(radicalInfinitesimal n hn i))
      (radicalInfinitesimal_nilpotent n hn i).neg
  have hNrm : radicalDifferenceNormalization n hn i = E.symm := rfl
  have hEapp : ∀ y, E y = finiteExponentialRatio n (-(radicalInfinitesimal n hn i)) y :=
    fun y => rfl
  have hc : ∀ y, finiteExponentialRatio n (-(radicalInfinitesimal n hn i))
      (radicalInfinitesimal n hn i y) =
      radicalInfinitesimal n hn i (finiteExponentialRatio n (-(radicalInfinitesimal n hn i)) y) := by
    intro y
    have h := (finiteExponentialRatio_commute n (-(radicalInfinitesimal n hn i))
      (radicalInfinitesimal n hn i) (Commute.refl (radicalInfinitesimal n hn i)).neg_left).eq
    exact LinearMap.congr_fun h y
  have hEc : ∀ y, E (radicalInfinitesimal n hn i y) = radicalInfinitesimal n hn i (E y) := by
    intro y
    rw [hEapp, hEapp]
    exact hc y
  have hcomm : ∀ x, E.symm (radicalInfinitesimal n hn i x) =
      radicalInfinitesimal n hn i (E.symm x) := by
    intro x
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hEc, LinearEquiv.apply_symm_apply]
  refine ⟨-(E.symm γ), ?_⟩
  apply E.symm.injective
  rw [← hNrm, radicalDifferenceNormalization_difference, hNrm, hcomm, map_neg, neg_neg]

theorem integralRadicalGenerator_zero : integralRadicalGenerator 0 = radicalLatticeFirst := by
  simp [integralRadicalGenerator, radicalLatticeFirst]

theorem integralRadicalGenerator_one : integralRadicalGenerator 1 = radicalLatticeSecond := by
  simp [integralRadicalGenerator, radicalLatticeSecond]

theorem bl_rho_first : (Rep.res integralBadLineExtension.inl (blRep n χ)).ρ radicalLatticeFirst - 1 =
    radicalDifference n 0 := by
  have h : (Rep.res integralBadLineExtension.inl (blRep n χ)).ρ radicalLatticeFirst =
      rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) := by
    rw [← radicalRepresentation_generator n 0, integralRadicalGenerator_zero]
    exact blRep_radical n χ radicalLatticeFirst
  rw [h]
  rfl

theorem bl_rho_second : (Rep.res integralBadLineExtension.inl (blRep n χ)).ρ radicalLatticeSecond - 1 =
    radicalDifference n 1 := by
  have h : (Rep.res integralBadLineExtension.inl (blRep n χ)).ρ radicalLatticeSecond =
      rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) := by
    rw [← radicalRepresentation_generator n 1, integralRadicalGenerator_one]
    exact blRep_radical n χ radicalLatticeSecond
  rw [h]
  rfl

/-- In positive degree the kernel of `κ` consists of sums of radical differences. -/
theorem bl_ker_le (hn : 0 < n) :
    LinearMap.ker (kappaLin n) ≤
      LinearMap.range ((Rep.res integralBadLineExtension.inl (blRep n χ)).ρ radicalLatticeFirst - 1) ⊔
        LinearMap.range ((Rep.res integralBadLineExtension.inl (blRep n χ)).ρ radicalLatticeSecond - 1) := by
  intro v hv
  have hmem := bl_mem_Wsp n hn v (LinearMap.mem_ker.mp hv)
  obtain ⟨y, ⟨γ₀, rfl⟩, w, ⟨γ₁, rfl⟩, hyw⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨δ₀, hδ₀⟩ := bl_radicalDifference_range n hn 0 γ₀
  obtain ⟨δ₁, hδ₁⟩ := bl_radicalDifference_range n hn 1 γ₁
  refine Submodule.mem_sup.mpr ⟨_, ⟨δ₀, rfl⟩, _, ⟨δ₁, rfl⟩, ?_⟩
  have e0 := LinearMap.congr_fun (bl_rho_first n χ) δ₀
  have e1 := LinearMap.congr_fun (bl_rho_second n χ) δ₁
  exact (congrArg₂ (· + ·) e0 e1).trans ((congrArg₂ (· + ·) hδ₀ hδ₁).trans hyw)

/-! ### The Levi reflection `diag(1, -1, 1)` and the restriction to the radical -/

theorem kappa_blRep_radical (r : RadicalLattice) (v : HomogeneousPoly n) :
    kappaLin n ((blRep n χ).ρ (integralBadLineExtension.inl r) v) = kappaLin n v := by
  rw [blRep_radical]
  change kappaLin n (rationalCoefficientComponent n trivialCharacter
    (integralRational (lineUnipotent r.toAdd.1 r.toAdd.2)) v) = _
  rw [kappa_rho_integral n (lineUnipotent r.toAdd.1 r.toAdd.2) (by simp [lineUnipotent, upperUnipotent])
    (by simp [lineUnipotent, upperUnipotent]) (by simp [lineUnipotent, upperUnipotent]) v,
    det_lineUnipotent]
  simp

theorem det_lineLevi_reflection : (lineLevi (1 : ℤˣ) reflection.val).val.det = -1 := by
  rw [lineLevi_val]
  simp [reflection, Matrix.det_fin_three]

theorem kappa_blRep_reflection (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (v : HomogeneousPoly n) :
    kappaLin n ((blRep n χ).ρ (integralBadLineSplitting ((1 : ℤˣ), reflection)) v) =
      kappaLin n v := by
  have h0 : (lineLevi (1 : ℤˣ) reflection.val).val 0 0 = 1 := by
    rw [lineLevi_val]; simp
  have h1 : (lineLevi (1 : ℤˣ) reflection.val).val 1 0 = 0 := by
    rw [lineLevi_val]; simp
  have h2 : (lineLevi (1 : ℤˣ) reflection.val).val 2 0 = 0 := by
    rw [lineLevi_val]; simp
  have hdet : ¬ (0 : ℚ) < (integralRational (lineLevi (1 : ℤˣ) reflection.val)).val.det := by
    rw [det_integralRational, det_lineLevi_reflection]
    norm_num
  have e : (blRep n χ).ρ (integralBadLineSplitting ((1 : ℤˣ), reflection)) v =
      -(rationalCoefficientComponent n trivialCharacter
        (integralRational (lineLevi (1 : ℤˣ) reflection.val)) v) := by
    refine (blRep_apply n χ _ v).trans ?_
    change rationalCoefficientComponent n χ (integralRational (lineLevi (1 : ℤˣ) reflection.val)) v =
      -(rationalCoefficientComponent n trivialCharacter
        (integralRational (lineLevi (1 : ℤˣ) reflection.val)) v)
    rw [Twisted.rho_apply_eq_detSign_smul n χ, Twisted.detSign_odd hodd,
      ite_eq_right hdet]
    exact neg_one_smul ℂ _
  rw [e, map_neg, kappa_rho_integral n (lineLevi (1 : ℤˣ) reflection.val) h0 h1 h2 v,
    det_lineLevi_reflection]
  norm_num

theorem bl_phi_reflection (r : RadicalLattice) :
    (splitRadicalInput integralBadLineSplitting ((1 : ℤˣ), reflection) r).toAdd =
      (-r.toAdd.1, r.toAdd.2) := by
  change (integralBadLineSplitting.conjAct ((1 : ℤˣ), reflection)⁻¹ r).toAdd = _
  rw [integralBadLine_inverse_conjAct_coordinates]
  apply Prod.ext
  · simp [reflection]
  · simp [reflection]

/-- **Degree zero.** The representation is trivial and the Levi reflection kills the alternation. -/
theorem bl_restriction_zero_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : groupCohomology.cocycles₂ (blRep 0 χ)) :
    groupCohomology.H2π (Rep.res integralBadLineExtension.inl (blRep 0 χ))
      (twoCocycleRestriction integralBadLineExtension.inl (blRep 0 χ) cycle) = 0 := by
  have hφ1 : splitRadicalInput integralBadLineSplitting ((1 : ℤˣ), reflection) radicalLatticeFirst =
      radicalLatticeFirst⁻¹ := by
    apply Multiplicative.toAdd.injective
    rw [bl_phi_reflection]
    simp [radicalLatticeFirst]
  have hφ2 : splitRadicalInput integralBadLineSplitting ((1 : ℤˣ), reflection) radicalLatticeSecond =
      radicalLatticeSecond := by
    apply Multiplicative.toAdd.injective
    rw [bl_phi_reflection]
    simp [radicalLatticeSecond]
  have htrivial : ∀ (r : RadicalLattice) (v : HomogeneousPoly 0),
      (blRep 0 χ).ρ (integralBadLineExtension.inl r) v = v := by
    intro r v
    change rationalCoefficientComponent 0 χ
      (integralRational (lineUnipotent r.toAdd.1 r.toAdd.2)) v = v
    refine rho_chi_zero hodd _ (Or.inl ?_) v
    rw [det_integralRational, det_lineUnipotent]
    norm_num
  have hfixed : ∀ v : HomogeneousPoly 0,
      (blRep 0 χ).ρ (integralBadLineSplitting ((1 : ℤˣ), reflection)) v = v := by
    intro v
    change rationalCoefficientComponent 0 χ
      (integralRational (lineLevi (1 : ℤˣ) reflection.val)) v = v
    refine rho_chi_zero hodd _ (Or.inr ?_) v
    rw [det_integralRational, det_lineLevi_reflection]
    norm_num
  refine latticeH2_eq_zero_of_projected (Rep.res integralBadLineExtension.inl (blRep 0 χ))
    LinearMap.id ?_ _ ?_
  · rw [LinearMap.ker_id]
    exact bot_le
  · exact projected_alternation_zero_of_reflection integralBadLineExtension.inl (blRep 0 χ)
      LinearMap.id (fun r v => by simp only [LinearMap.id_apply]; exact htrivial r v)
      (integralBadLineSplitting ((1 : ℤˣ), reflection))
      (by rw [splitting_conj_inl, hφ1]) (by rw [splitting_conj_inl, hφ2])
      (fun v => by simp only [LinearMap.id_apply]; exact hfixed v) cycle

/-- **Positive degree.** -/
theorem bl_restriction_zero_pos (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (cycle : groupCohomology.cocycles₂ (blRep n χ)) :
    groupCohomology.H2π (Rep.res integralBadLineExtension.inl (blRep n χ))
      (twoCocycleRestriction integralBadLineExtension.inl (blRep n χ) cycle) = 0 := by
  have hφ1 : splitRadicalInput integralBadLineSplitting ((1 : ℤˣ), reflection) radicalLatticeFirst =
      radicalLatticeFirst⁻¹ := by
    apply Multiplicative.toAdd.injective
    rw [bl_phi_reflection]
    simp [radicalLatticeFirst]
  have hφ2 : splitRadicalInput integralBadLineSplitting ((1 : ℤˣ), reflection) radicalLatticeSecond =
      radicalLatticeSecond := by
    apply Multiplicative.toAdd.injective
    rw [bl_phi_reflection]
    simp [radicalLatticeSecond]
  refine latticeH2_eq_zero_of_projected (Rep.res integralBadLineExtension.inl (blRep n χ))
    (kappaLin n) (bl_ker_le n χ hn) _ ?_
  exact projected_alternation_zero_of_reflection integralBadLineExtension.inl (blRep n χ)
    (kappaLin n) (fun r v => kappa_blRep_radical n χ r v)
    (integralBadLineSplitting ((1 : ℤˣ), reflection))
    (by rw [splitting_conj_inl, hφ1]) (by rw [splitting_conj_inl, hφ2])
    (fun v => kappa_blRep_reflection n χ hodd v) cycle

/-- **The restriction of every class to the radical vanishes.** -/
theorem bl_hres (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (x : groupCohomology.H2 (blRep n χ)) :
    twoCohomologyRestriction integralBadLineExtension.inl (blRep n χ) x = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (blRep n χ) x
  rw [twoCohomologyRestriction_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact bl_restriction_zero_zero χ hodd cycle
  · exact bl_restriction_zero_pos n χ hodd hn cycle

/-! ### The central element acts by `-1` on `H¹` of the radical -/

/-- The central Levi element `diag(-1, 1, 1)`. -/
abbrev blZ : ℤˣ × binaryArithmeticLevel := (-1, 1)

theorem blZ_central (g : ℤˣ × binaryArithmeticLevel) : blZ * g = g * blZ :=
  Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul]; exact mul_comm _ _)
    (by rw [Prod.snd_mul, Prod.snd_mul]; simp)

theorem blZ_phi (r : RadicalLattice) :
    splitRadicalInput integralBadLineSplitting blZ r = r⁻¹ := by
  apply Multiplicative.toAdd.injective
  change (integralBadLineSplitting.conjAct blZ⁻¹ r).toAdd = _
  rw [integralBadLine_inverse_conjAct_coordinates]
  apply Prod.ext
  · simp
  · simp

theorem det_lineLevi_blZ : (lineLevi (-1 : ℤˣ) (1 : GeneralLinearGroup (Fin 2) ℤ)).val.det = -1 := by
  rw [lineLevi_val]
  simp [Matrix.det_fin_three]

/-- The twisted action of the central element, in degree zero, is trivial. -/
theorem bl_rho_blZ_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (v : HomogeneousPoly 0) :
    (blRep 0 χ).ρ (integralBadLineSplitting blZ) v = v := by
  change rationalCoefficientComponent 0 χ (integralRational
    (lineLevi (-1 : ℤˣ) (1 : GeneralLinearGroup (Fin 2) ℤ))) v = v
  refine rho_chi_zero hodd _ (Or.inr ?_) v
  rw [det_integralRational, det_lineLevi_blZ]
  norm_num

/-- **Degree zero.** -/
theorem bl_hneg_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (w : groupCohomology.H1 (Rep.res integralBadLineExtension.inl (blRep 0 χ))) :
    splitRadicalH1Action integralBadLineSplitting (blRep 0 χ) blZ w = -w := by
  obtain ⟨ξ, rfl⟩ := oneCocycle_H1_surjective _ w
  rw [splitRadicalH1Action_apply]
  have htrivial : ∀ (r : RadicalLattice) (v : HomogeneousPoly 0),
      (blRep 0 χ).ρ (integralBadLineExtension.inl r) v = v := by
    intro r v
    change rationalCoefficientComponent 0 χ
      (integralRational (lineUnipotent r.toAdd.1 r.toAdd.2)) v = v
    refine rho_chi_zero hodd _ (Or.inl ?_) v
    rw [det_integralRational, det_lineUnipotent]
    norm_num
  have hadd : ∀ a b : RadicalLattice, ξ (a * b) = ξ a + ξ b := by
    intro a b
    have key := (groupCohomology.mem_cocycles₁_iff _).mp ξ.property a b
    have hv : (Rep.res integralBadLineExtension.inl (blRep 0 χ)).ρ a (ξ b) = ξ b := htrivial a (ξ b)
    exact eq_swap_add_aux key hv.symm
  have hone : ξ 1 = 0 := by
    have h11 := hadd 1 1
    rw [one_mul] at h11
    exact add_eq_left.mp h11.symm
  have hinv : ∀ r : RadicalLattice, ξ r⁻¹ = -ξ r := by
    intro r
    have h := hadd r r⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hξ : splitRadicalCocycleAction integralBadLineSplitting (blRep 0 χ) blZ ξ = -ξ := by
    apply Subtype.ext
    funext r
    change (blRep 0 χ).ρ (integralBadLineSplitting blZ)
      (ξ (splitRadicalInput integralBadLineSplitting blZ r)) = -ξ r
    exact (bl_rho_blZ_zero χ hodd _).trans ((congrArg ξ.val (blZ_phi r)).trans (hinv r))
  rw [hξ, map_neg]

/-! #### Positive degree: Sol's Kostant computation -/

/-- Sol's crossed cocycle attached to a radical cocycle of the twisted system. -/
def blSol (ξ : groupCohomology.cocycles₁ (Rep.res integralBadLineExtension.inl (blRep n χ))) :
    crossedCocycles ((standardBadLineRepresentation n).comp SemidirectProduct.inl) :=
  ⟨fun r => ξ r, by
    intro a b
    have key := (groupCohomology.mem_cocycles₁_iff _).mp ξ.property a b
    have rep : ((standardBadLineRepresentation n).comp SemidirectProduct.inl) a (ξ b) =
        (Rep.res integralBadLineExtension.inl (blRep n χ)).ρ a (ξ b) := by
      rw [standardBadLineRepresentation_radical]
      exact (congrArg (fun f => f (ξ b)) (blRep_radical n χ a)).symm
    exact eq_swap_add_aux key rep⟩

/-- The twisted action of the central element is minus the untwisted one. -/
theorem bl_rho_blZ (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (v : HomogeneousPoly n) :
    (blRep n χ).ρ (integralBadLineSplitting blZ) v =
      -(standardBadLineRepresentation n (SemidirectProduct.inr blZ) v) := by
  change rationalCoefficientComponent n χ (integralRational
      (lineLevi (-1 : ℤˣ) (1 : GeneralLinearGroup (Fin 2) ℤ))) v =
    -(rationalCoefficientComponent n trivialCharacter
      (standardBadLineSemidirectEquiv (SemidirectProduct.inr blZ)).val v)
  rw [standardBadLineSemidirectEquiv_inr]
  change _ = -(rationalCoefficientComponent n trivialCharacter (integralRational
    (lineLevi (-1 : ℤˣ) (1 : GeneralLinearGroup (Fin 2) ℤ))) v)
  have hneg : ¬ (0 : ℚ) < ((-1 : ℤ) : ℚ) := by norm_num
  rw [Twisted.rho_apply_eq_detSign_smul n χ, Twisted.detSign_odd hodd,
    det_integralRational, det_lineLevi_blZ, ite_eq_right hneg, neg_one_smul]

/-- **Positive degree.** -/
theorem bl_hneg_pos (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (w : groupCohomology.H1 (Rep.res integralBadLineExtension.inl (blRep n χ))) :
    splitRadicalH1Action integralBadLineSplitting (blRep n χ) blZ w = -w := by
  obtain ⟨ξ, rfl⟩ := oneCocycle_H1_surjective _ w
  rw [splitRadicalH1Action_apply]
  have key : groupCohomology.H1π (Rep.res integralBadLineExtension.inl (blRep n χ))
      (splitRadicalCocycleAction integralBadLineSplitting (blRep n χ) blZ ξ + ξ) = 0 := by
    rw [groupCohomology.H1π_eq_zero_iff]
    have hequiv := explicitRadicalBinaryEquiv_equivariant n hn blZ
      ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
        (blSol n χ ξ))
    rw [leviCrossedH1Representation_mk] at hequiv
    have hbin : ∀ y : Binary.HomogeneousPoly (n + 1), binaryLeviRepresentation n blZ y = y := by
      intro y
      simp [binaryLeviRepresentation, blZ]
    rw [hbin] at hequiv
    have heq := (explicitRadicalBinaryEquiv n hn).injective hequiv
    have hmem := (Submodule.Quotient.eq _).mp heq
    obtain ⟨x, hx⟩ := hmem
    let x' : Rep.res integralBadLineExtension.inl (blRep n χ) := x
    refine ⟨-x', ?_⟩
    funext r
    have hxr : ((standardBadLineRepresentation n).comp SemidirectProduct.inl) r x - x =
        (leviCrossedAction integralBadLineSplitting.conjAct (standardBadLineRepresentation n) blZ
          (blSol n χ ξ)).val r - (blSol n χ ξ).val r := congrFun (congrArg Subtype.val hx) r
    have hL : (splitRadicalCocycleAction integralBadLineSplitting (blRep n χ) blZ ξ) r =
        -((leviCrossedAction integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
          blZ (blSol n χ ξ)).val r) := by
      change (blRep n χ).ρ (integralBadLineSplitting blZ)
        (ξ (splitRadicalInput integralBadLineSplitting blZ r)) =
          -(standardBadLineRepresentation n (SemidirectProduct.inr blZ)
            (ξ (integralBadLineSplitting.conjAct blZ⁻¹ r)))
      exact bl_rho_blZ n χ hodd _
    have hrep : (Rep.res integralBadLineExtension.inl (blRep n χ)).ρ r x =
        ((standardBadLineRepresentation n).comp SemidirectProduct.inl) r x :=
      (congrArg (fun f => f x) (blRep_radical n χ r)).trans
        (congrArg (fun f : Representation ℂ RadicalLattice (HomogeneousPoly n) => f r x)
          (standardBadLineRepresentation_radical n)).symm
    rw [groupCohomology.d₀₁_hom_apply]
    exact neg_cocycle_aux (R := fun y => (Rep.res integralBadLineExtension.inl (blRep n χ)).ρ r y)
      (map_neg ((Rep.res integralBadLineExtension.inl (blRep n χ)).ρ r) x') hrep hxr hL
  rw [map_add] at key
  exact eq_neg_of_add_eq_zero_left key

/-- **The central element acts by `-1` on `H¹(ℤ², V_χ)`.** -/
theorem bl_hneg (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (w : groupCohomology.H1 (Rep.res integralBadLineExtension.inl (blRep n χ))) :
    splitRadicalH1Action integralBadLineSplitting (blRep n χ) blZ w = -w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact bl_hneg_zero χ hodd w
  · exact bl_hneg_pos n χ hodd hn w

/-! ### Assembly -/

/-- The embedding of the Levi group in `GL₂(ℤ) × ℤˣ`. -/
def blPsi : ℤˣ × binaryArithmeticLevel →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ :=
  (binaryArithmeticLevel.subtype.comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)

theorem blPsi_injective : Function.Injective blPsi := by
  intro x y h
  have h1 : (blPsi x).1 = (blPsi y).1 := congrArg Prod.fst h
  have h2 : (blPsi x).2 = (blPsi y).2 := congrArg Prod.snd h
  exact Prod.ext h2 (Subtype.ext h1)

/-- **`H²(Γ_F, V_χ) = 0`** for `χ(-1_∞) = -1`, in the integral model of the stabilizer. -/
theorem bl_groupH2_eq_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (x : groupCohomology.H2 (blRep n χ)) : x = 0 :=
  groupH2_eq_zero_of_split integralBadLineSplitting (blRep n χ) blPsi blPsi_injective
    (bl_hres n χ hodd) blZ blZ_central (bl_hneg n χ hodd) x

/-- **The local cohomology at the bad-line cusp vanishes for an odd character.** -/
theorem cuspH2_line_false_eq_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (x : CuspReduction.CuspH2 n χ .line false) : x = 0 :=
  homogeneousH2_eq_zero_of_group (CuspReduction.cuspLevel .line false)
    (rationalCoefficientComponent n χ)
    (groupH2_eq_zero_of_mulEquiv integralBadLineStabilizerEquiv
      (subgroupCoefficientRep (CuspReduction.cuspLevel .line false)
        (rationalCoefficientComponent n χ))
      (fun y => bl_groupH2_eq_zero n χ hodd y)) x

end BadLineVanish

end TernaryPeriodPolynomials.SourceConstruction
