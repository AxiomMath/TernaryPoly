module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.CentralExtension
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.CharacterTriviality
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity

@[expose] public section



/-!
# The reflection sign of the normal inducing character

The paper extends the global class to the group `⟨K†, -I₃⟩`: `-I₃` fixes every rational flag and acts on the
coefficients by a scalar.  Formalization:

* `reflLevel = ⟨K†, -I₃⟩` (`CentralExtension.centralExtension`), with `resCocycle`/`resH2` the restriction to `K† =
  rationalLevel` and `IsReflExtended a` the statement that a stratum class lies in the image (a cocycle of `reflLevel`
  with values in the flag representation restricts to a representative).
* `rationalCoefficientComponent_reflZ`: `-I₃` acts on the `χ`-component coefficients by
  `reflScalar n χ = χ_∞(-1)·(-1)^{n+1}` (computed from the definition of the coefficient representation).
* `reflScalar_sub_one_smul_extended`: an extended class is killed by `reflScalar - 1` (prism homotopy of the
  translation by the central `-I₃`, `CentralExtension.smul_sub_one_eq_zero`).
* `exists_extension_global`, `globalCoordinates_extended`: when `reflScalar n χ = 1` (for `χ = trivialCharacter`: `n` odd,
  `reflScalar_trivial_odd`) EVERY class of the global `χ`-component extends, and its boundary coordinates lie in the image;
  so the global class of Proposition C.5 needs no visible `-I₃`-invariance (the cocycle is only a `K†`-cocycle; its class
  extends by averaging `½(c(x) + c(-x))`).
* `chi_eq_trivial_of_extended_bad_plane`: for an arbitrary inducing datum `D`, a class `a` of its plane summand that
  extends and has a nonzero bad-plane coordinate forces `reflScalar n D.chi = 1`; sphericity (nonzero bad-plane
  coordinate) and the parity of `n` (`cohomological_spherical_odd`) then give `χ_∞(-1) = 1`, and
  `CharacterTriviality.chi_eq_trivial_of_pair_even` gives `D.chi = trivialCharacter`.  For odd `n` the odd character
  of conductor three is excluded (`extended_class_eq_zero_of_odd`: its extended classes vanish identically).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

/-- `c • x = 0` over `ℂ` (proved for an arbitrary module so that the instance problem is not
re-solved on the concrete cohomology space). -/
private theorem complex_smul_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {c : ℂ} {x : V}
    (h : c • x = 0) : c = 0 ∨ x = 0 :=
  smul_eq_zero.mp h


/-- The central involution `-I₃` of `GL₃(ℚ)`. -/
def reflZ : RationalGL3 := -1

theorem reflZ_comm : ∀ g : RationalGL3, reflZ * g = g * reflZ := by
  intro g; simp [reflZ]

theorem reflZ_sq : reflZ * reflZ = 1 := by simp [reflZ]

/-- `-I₃` fixes every rational flag. -/
theorem reflZ_mem_parabolic (s : Side) : reflZ ∈ parabolic s := by
  cases s
  · show InPlaneParabolic reflZ
    constructor <;> simp [reflZ]
  · show InLineParabolic reflZ
    constructor <;> simp [reflZ]

theorem map_reflZ : GeneralLinearGroup.map (algebraMap ℚ ℝ) reflZ = (-1 : RealGL3) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflZ, GeneralLinearGroup.map_apply]

theorem substitute_neg_one_homogeneous (n : ℕ) (v : HomogeneousPoly n) :
    substitute (-1 : Matrix (Fin 3) (Fin 3) ℂ) v.val = (-1 : ℂ) ^ n • v.val := by
  have forms : linearForm (-1 : Matrix (Fin 3) (Fin 3) ℂ) = fun i => C (-1) * X i := by
    funext i
    simp [linearForm, Matrix.neg_apply, Matrix.one_apply]
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff v.val, map_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff v.val, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro exponent supported
  have hom := (MvPolynomial.mem_homogeneousSubmodule n v.val).mp v.property
  simp only [substitute, forms, MvPolynomial.bind₁_monomial, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    MvPolynomial.prod_X_pow_eq_monomial, MvPolynomial.smul_eq_C_mul]
  have hd : (∑ i ∈ exponent.support, exponent i) = n := (hom.degree_eq_sum_deg_support supported).symm
  rw [hd]
  simp only [MvPolynomial.C_mul_monomial]
  congr 1
  ring

theorem det_neg_one_real : GeneralLinearGroup.det (-1 : RealGL3) = -1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, Matrix.det_neg]
  norm_num

theorem realCoefficient_neg_one (n : ℕ) (v : HomogeneousPoly n) :
    realCoefficient n (-1) v = (-1 : ℂ) ^ (n + 1) • v := by
  apply Subtype.ext
  have hmap : GeneralLinearGroup.map (algebraMap ℝ ℂ) (-1 : RealGL3) = (-1 : GL3) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply]
  change ((homogeneousAction n (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (-1 : RealGL3)) v :
    HomogeneousPoly n) : Poly) = _
  rw [hmap, homogeneousAction_coe, action_apply]
  have hdet : ((GeneralLinearGroup.det (-1 : GL3) : ℂˣ) : ℂ) = -1 := by
    simp [GeneralLinearGroup.val_det_apply, Matrix.det_neg]
    norm_num
  have hinv : ((-1 : GL3)⁻¹ : GL3) = (-1 : GL3) := by
    rw [inv_neg, inv_one]
  have hcoe : (((-1 : GL3)⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
    rw [hinv]; simp
  rw [hcoe]
  simp only [determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, hdet]
  rw [substitute_neg_one_homogeneous]
  simp only [Submodule.coe_smul, smul_smul]
  congr 1
  rw [pow_succ]
  norm_num

theorem rationalCoefficientComponent_reflZ (n : ℕ) (χ : RankOneCharacter) (v : HomogeneousPoly n) :
    rationalCoefficientComponent n χ reflZ v =
      (χ.toMonoidHom (realAdeleUnit (-1)) * (-1 : ℂ) ^ (n + 1)) • v := by
  change realCoefficientComponent n χ (GeneralLinearGroup.map (algebraMap ℚ ℝ) reflZ) v = _
  rw [map_reflZ]
  change componentCharacter χ (-1) • realCoefficient n (-1) v = _
  rw [realCoefficient_neg_one, smul_smul]
  congr 1
  unfold componentCharacter
  simp only [MonoidHom.comp_apply, det_neg_one_real]
  congr 2

/-- The extended level `⟨K†, -I₃⟩`: the rational arithmetic level together with `-I₃`. -/
def reflLevel : Subgroup RationalGL3 := centralExtension rationalLevel reflZ reflZ_comm reflZ_sq

theorem rationalLevel_le_reflLevel : rationalLevel ≤ reflLevel :=
  le_centralExtension rationalLevel reflZ reflZ_comm reflZ_sq

theorem reflZ_mem_reflLevel : reflZ ∈ reflLevel :=
  z_mem_centralExtension rationalLevel reflZ reflZ_comm reflZ_sq

/-- `-I₃` fixes every rational flag. -/
theorem reflZ_inv_smul_flag (s : Side) (x : Flags s) : reflZ⁻¹ • x = x := by
  induction x using QuotientGroup.induction_on with
  | H q =>
    change (QuotientGroup.mk (reflZ⁻¹ * q) : Flags s) = QuotientGroup.mk q
    rw [QuotientGroup.eq]
    have h : (reflZ⁻¹ * q)⁻¹ * q = reflZ := by
      have hinv : reflZ⁻¹ = reflZ := inv_eq_of_mul_eq_one_right reflZ_sq
      rw [hinv, _root_.mul_inv_rev, hinv, mul_assoc, reflZ_comm q, inv_mul_cancel_left]
    rw [h]
    exact reflZ_mem_parabolic s

/-- The scalar by which `-I₃` acts on the coefficients of the `χ`-component: `χ_∞(-1)·(-1)^{n+1}`. -/
def reflScalar (n : ℕ) (χ : RankOneCharacter) : ℂ := χ.toMonoidHom (realAdeleUnit (-1)) * (-1 : ℂ) ^ (n + 1)

theorem flagRepresentation_reflZ (n : ℕ) (χ : RankOneCharacter) (s : Side)
    (f : Flags s → HomogeneousPoly n) :
    flagRepresentation (rationalCoefficientComponent n χ) s reflZ f = reflScalar n χ • f := by
  funext x
  change rationalCoefficientComponent n χ reflZ (f (reflZ⁻¹ • x)) = _
  rw [reflZ_inv_smul_flag, rationalCoefficientComponent_reflZ]
  rfl

/-- **A class of the stratum that extends over `⟨K†, -I₃⟩` is killed by `χ_∞(-1)(-1)^{n+1} - 1`.** -/
theorem reflScalar_sub_one_smul_extended (n : ℕ) (χ : RankOneCharacter) (s : Side)
    (c' : cocycles reflLevel (flagRepresentation (rationalCoefficientComponent n χ) s)) :
    (reflScalar n χ - 1) • classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
      (resCocycle _ rationalLevel_le_reflLevel c') = 0 :=
  smul_sub_one_eq_zero rationalLevel reflZ reflZ_comm reflZ_sq _ (reflScalar n χ)
    (fun v => by rw [flagRepresentation_reflZ]) c'

/-- Every `K†`-class of the global `χ`-component extends over `⟨K†, -I₃⟩` once `reflScalar n χ = 1`
(for the trivial character and odd `n`: always). -/
theorem exists_extension_global (n : ℕ) (χ : RankOneCharacter) (h : reflScalar n χ = 1)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    ∃ c' : cocycles reflLevel (rationalCoefficientComponent n χ),
      classOf rationalLevel (rationalCoefficientComponent n χ) (resCocycle _ rationalLevel_le_reflLevel c') =
        classOf rationalLevel (rationalCoefficientComponent n χ) c :=
  exists_extension_of_one rationalLevel reflZ reflZ_comm reflZ_sq _
    (fun v => by
      rw [rationalCoefficientComponent_reflZ]
      have h1 : χ.toMonoidHom (realAdeleUnit (-1)) * (-1 : ℂ) ^ (n + 1) = 1 := h
      rw [h1, one_smul]) c

/-- Pulling a global cocycle of any level back to a stratum is constant on flags. -/
def restrictionCocycleG (n : ℕ) (χ : RankOneCharacter) (s : Side) (Γ : Subgroup RationalGL3)
    (c : cocycles Γ (rationalCoefficientComponent n χ)) :
    cocycles Γ (flagRepresentation (rationalCoefficientComponent n χ) s) :=
  ⟨⟨fun x _ => c.val.val x, by
    intro γ x
    funext f
    exact c.val.property γ x⟩, by
    funext x f
    exact congrFun c.property x⟩

/-- The constant-on-flags lift of a global one-cochain. -/
def flatCochain (n : ℕ) (χ : RankOneCharacter) (s : Side)
    (b : cochains rationalLevel (rationalCoefficientComponent n χ) 1) :
    cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) 1 :=
  ⟨fun x _ => b.val x, by
    intro γ x
    funext f
    exact b.property γ x⟩

theorem restrictionCocycle_add_boundary (n : ℕ) (χ : RankOneCharacter) (s : Side)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (b : cochains rationalLevel (rationalCoefficientComponent n χ) 1) :
    restrictionCocycle n χ s (c + boundaryMap rationalLevel _ b) =
      restrictionCocycle n χ s c + boundaryMap rationalLevel _ (flatCochain n χ s b) := rfl

/-- A stratum class lies in the image of the restriction from the extended level `⟨K†, -I₃⟩`. -/
def IsReflExtended {n : ℕ} {χ : RankOneCharacter} {s : Side} (a : StratumH2 n χ s) : Prop :=
  ∃ c' : cocycles reflLevel (flagRepresentation (rationalCoefficientComponent n χ) s),
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
      (resCocycle _ rationalLevel_le_reflLevel c') = a

/-- **The boundary coordinates of a global class lie in the image of the extended level**, as soon as the
reflection scalar is `1`. -/
theorem globalCoordinates_extended (n : ℕ) (χ : RankOneCharacter) (h : reflScalar n χ = 1)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) (s : Side) :
    IsReflExtended (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
      (restrictionCocycle n χ s c)) := by
  have hobtain1 := exists_extension_global n χ h c
  obtain ⟨c', hc'⟩ := hobtain1
  refine ⟨restrictionCocycleG n χ s reflLevel c', ?_⟩
  have hq := (Submodule.Quotient.eq _).mp hc'
  obtain ⟨b, hb⟩ := hq
  have e : resCocycle _ rationalLevel_le_reflLevel c' = c + boundaryMap rationalLevel _ b := by
    have : boundaryMap rationalLevel _ b = resCocycle _ rationalLevel_le_reflLevel c' - c := hb
    rw [this]; abel
  have e2 : resCocycle _ rationalLevel_le_reflLevel (restrictionCocycleG n χ s reflLevel c') =
      restrictionCocycle n χ s (resCocycle _ rationalLevel_le_reflLevel c') := rfl
  rw [e2, e, restrictionCocycle_add_boundary]
  have : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
      (boundaryMap rationalLevel _ (flatCochain n χ s b)) = 0 := classOf_boundaryMap _ _ _
  rw [map_add, this, add_zero]

/-- The reflection scalar of the trivial character is `1` for odd `n`. -/
theorem reflScalar_trivial_odd {n : ℕ} (hn : Odd n) : reflScalar n trivialCharacter = 1 := by
  unfold reflScalar
  have : trivialCharacter.toMonoidHom (realAdeleUnit (-1)) = 1 := rfl
  rw [this, one_mul]
  exact (hn.add_one).neg_one_pow

/-- An extended class of an odd-degree odd-character stratum vanishes. -/
theorem extended_class_eq_zero_of_odd {n : ℕ} (hn : Odd n) {χ : RankOneCharacter}
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) {s : Side} {a : StratumH2 n χ s}
    (hext : IsReflExtended a) : a = 0 := by
  obtain ⟨c', hc'⟩ := hext
  have h := reflScalar_sub_one_smul_extended n χ s c'
  rw [hc'] at h
  have hs : reflScalar n χ = -1 := by
    unfold reflScalar
    rw [hχ, (hn.add_one).neg_one_pow]
    norm_num
  rw [hs] at h
  have h2 : ((-1 : ℂ) - 1) ≠ 0 := by norm_num
  exact (complex_smul_eq_zero h).resolve_left h2

open TernaryPeriodPolynomials.Spectral.CuspReduction in
/-- **The reflection sign of an extended bad-plane class**: if a class `a` of the plane summand of an
arbitrary inducing datum extends over `⟨K†, -I₃⟩` and has a nonzero bad-plane coordinate, then `χ_∞(-1) = 1`. -/
theorem even_of_extended_bad_plane {n : ℕ} (D : InducingData n) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) (hext : IsReflExtended a)
    (hbad : cuspRes n D.chi .plane false a ≠ 0) : D.chi.toMonoidHom (realAdeleUnit (-1)) = 1 := by
  have hsph : SphericalCusp D.cusp := by
    by_contra hns
    exact hbad (TernaryPeriodPolynomials.Separation.cuspRes_plane_false_eq_zero_of_not_spherical
      D hns ha)
  have hodd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd n D.cusp
      D.cohomological hsph
  obtain ⟨c', hc'⟩ := hext
  have h := reflScalar_sub_one_smul_extended n D.chi .plane c'
  rw [hc'] at h
  have hane : a ≠ 0 := fun h0 => hbad (by rw [h0, map_zero])
  have hs : reflScalar n D.chi = 1 := by
    have := (complex_smul_eq_zero h).resolve_right hane
    exact sub_eq_zero.mp this
  unfold reflScalar at hs
  rw [(hodd.add_one).neg_one_pow, mul_one] at hs
  exact hs

open TernaryPeriodPolynomials.Spectral.CuspReduction in
/-- **The inducing character of an extended bad-plane class is trivial.** -/
theorem chi_eq_trivial_of_extended_bad_plane {n : ℕ} (D : InducingData n) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) (hext : IsReflExtended a)
    (hbad : cuspRes n D.chi .plane false a ≠ 0) : D.chi = trivialCharacter := by
  have heven := even_of_extended_bad_plane D ha hext hbad
  have hane : a ≠ 0 := fun h0 => hbad (by rw [h0, map_zero])
  have hne : associatePair D ≠ ⊥ := by
    intro hbot
    have hmem : ((a, 0) : BoundaryCoordinates n D.chi) ∈ associatePair D := ⟨ha, Submodule.zero_mem _⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hane (congrArg Prod.fst hmem)
  exact chi_eq_trivial_of_pair_even D hne heven

open TernaryPeriodPolynomials.Spectral.CuspReduction in
/-- The entry package for the datum of an extended bad-plane class, with no character hypothesis. -/
theorem exists_sphericalEntryPackage_of_extended {n : ℕ} (D : InducingData n) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) (hext : IsReflExtended a)
    (hbad : cuspRes n D.chi .plane false a ≠ 0) : Nonempty (Entry.SphericalEntryPackage D) := by
  have hsph : SphericalCusp D.cusp := by
    by_contra hns
    exact hbad (TernaryPeriodPolynomials.Separation.cuspRes_plane_false_eq_zero_of_not_spherical
      D hns ha)
  have hodd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd n D.cusp
      D.cohomological hsph
  exact Entry.exists_sphericalEntryPackage D hodd (chi_eq_trivial_of_extended_bad_plane D ha hext hbad) hsph

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
