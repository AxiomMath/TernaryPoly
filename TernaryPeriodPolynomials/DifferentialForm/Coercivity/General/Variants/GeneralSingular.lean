module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.SmoothInduction

@[expose] public section


/-!
# The actual `H²_c → H²` vanishing for every permitted arithmetic group

For a subgroup `Γ ≤ GL₃(ℝ)` that is admissible, carries a rational structure `κ : Γ →* GL₃(ℚ)`
(`IsRationalStructure`) and is commensurable with the cover `gamma0 = Γ(6)`, the actual
singular compact-to-ordinary map in degree two (`SingularVanish Γ hΓ A`) vanishes for the five
coefficient systems on `Γ` built from `κ`: the real polynomial system `realSystem κ n e`, its dual
`dualSystem κ n`, their doubled rational models `complexSystem`, `complexDualSystem` (with real and
imaginary coordinates; the base change to singular cohomology with `ℂ` coefficients is not proved),
and, with the literal `StrongDual ℂ (Sym^n ℂ³)` identification of the real scalar extension, the same
doubled dual system (`singularVanish_lit`).

The proof is the finite-cover and coefficient descent: with `H = Γ ⊓ gamma0`, the smooth Shapiro
lemma `singularVanish_of_primitive` (`Variants/SmoothInduction`, from the Tier B primitives over `H`)
gives the vanishing for `H` with the restricted deck coefficients, and the transfer
`singularVanish_of_subgroup` (`Singular/Orbit`, characteristic zero, `cor ∘ res = index`) passes it up
to `Γ`.  The arithmetic input is concrete: principal congruence subgroups `Γ(N)` (`3 ∣ N`, `N > 0`)
and their conjugates `g Γ(N) g⁻¹` by `g ∈ GL₃(ℚ)` are commensurable with `Γ(6)`
(`commensurable_principalReal`, `commensurable_conjQ_PQ`, from `exists_conj_le`: conjugation by a
rational matrix maps a deep principal congruence subgroup into a shallow one).

Formalized by Claude Sonnet 5.5.
-/

open TopologicalSpace CategoryTheory Matrix
open scoped TensorProduct

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.SmoothSingularGlobal
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceArithmeticProper

section RationalSystems

open TernaryPoly.PolynomialGLAction (GL3)

/-- The dual rational action of `GL₃(ℚ)` on `Sym^n ℚ³`, substitution by the transpose. -/
def dualAction (n : ℕ) : Representation ℚ GL3 (RationalCoefficients n) where
  toFun g := dualSubst n ((g : Matrix (Fin 3) (Fin 3) ℚ).transpose)
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp [dualSubst_val, TernaryPoly.PolynomialGLAction.substitute_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul, dualSubst_val,
      Module.End.mul_apply]
    exact (congrArg (fun q => q p.val)
      (TernaryPoly.PolynomialGLAction.substitute_comp
        ((g : Matrix (Fin 3) (Fin 3) ℚ).transpose) ((h : Matrix (Fin 3) (Fin 3) ℚ).transpose))).symm

theorem integralDualAction_eq (n : ℕ) :
    integralDualAction n = (dualAction n).comp (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)) := rfl

theorem dualDeckCoefficientRep_eq (n : ℕ) :
    dualDeckCoefficientRep n = Rep.of ((dualAction n).comp rationalDeckMatrix) := rfl

theorem rationalDeckCoefficientRep_eq (n : ℕ) (e : ℤ) :
    rationalDeckCoefficientRep n e =
      Rep.of ((TernaryPoly.PolynomialGLAction.homogeneousAction n e).comp rationalDeckMatrix) := rfl

end RationalSystems

section Systems

open TernaryPoly.PolynomialGLAction (GL3 homogeneousAction)

theorem glMap_injective : Function.Injective
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) : GL3 →* RealGL) := by
  intro a b hab
  apply Units.ext
  have := congrArg (fun g : RealGL => (g : Matrix (Fin 3) (Fin 3) ℝ)) hab
  exact Matrix.map_injective (algebraMap ℚ ℝ).injective this

variable {Γ H : Subgroup RealGL} (κ : Γ →* GL3)

/-- The real polynomial system `Sym^n` (with determinant twist `e`) on `Γ` through the rational
structure `κ`. -/
def realSystem (n : ℕ) (e : ℤ) : Rep.{0} ℚ Γ := Rep.of ((homogeneousAction n e).comp κ)

/-- The dual polynomial system on `Γ` through `κ`. -/
def dualSystem (n : ℕ) : Rep.{0} ℚ Γ := Rep.of ((dualAction n).comp κ)

instance realSystem_finiteDimensional (n : ℕ) (e : ℤ) : FiniteDimensional ℚ (realSystem κ n e) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℚ n)

instance dualSystem_finiteDimensional (n : ℕ) : FiniteDimensional ℚ (dualSystem κ n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℚ n)

/-- A rational structure on `Γ`: `κ` lifts the inclusion `Γ ⊆ GL₃(ℝ)` to `GL₃(ℚ)`. -/
def IsRationalStructure (Γ : Subgroup RealGL) (κ : Γ →* GL3) : Prop :=
  ∀ γ : Γ, Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (κ γ) = (γ : RealGL)

theorem compat_deck {κ : Γ →* GL3} (hκ : IsRationalStructure Γ κ) (hle : H ≤ gamma0) (hHΓ : H ≤ Γ)
    (h : H) : κ (Subgroup.inclusion hHΓ h) = rationalDeckMatrix (toDeck hle h) := by
  apply glMap_injective
  rw [hκ, rationalDeckMatrix_real]
  exact (deckMat_toDeck hle h).symm

theorem res_realSystem {κ : Γ →* GL3} (hκ : IsRationalStructure Γ κ) (hle : H ≤ gamma0)
    (hHΓ : H ≤ Γ) (n : ℕ) (e : ℤ) :
    Rep.res (Subgroup.inclusion hHΓ) (realSystem κ n e) =
      Rep.res (toDeck hle) (rationalDeckCoefficientRep n e) := by
  have : κ.comp (Subgroup.inclusion hHΓ) = rationalDeckMatrix.comp (toDeck hle) :=
    MonoidHom.ext fun h => compat_deck hκ hle hHΓ h
  change Rep.of ((homogeneousAction n e).comp (κ.comp (Subgroup.inclusion hHΓ))) =
    Rep.of ((homogeneousAction n e).comp (rationalDeckMatrix.comp (toDeck hle)))
  rw [this]

theorem res_dualSystem {κ : Γ →* GL3} (hκ : IsRationalStructure Γ κ) (hle : H ≤ gamma0)
    (hHΓ : H ≤ Γ) (n : ℕ) :
    Rep.res (Subgroup.inclusion hHΓ) (dualSystem κ n) =
      Rep.res (toDeck hle) (dualDeckCoefficientRep n) := by
  have : κ.comp (Subgroup.inclusion hHΓ) = rationalDeckMatrix.comp (toDeck hle) :=
    MonoidHom.ext fun h => compat_deck hκ hle hHΓ h
  change Rep.of ((dualAction n).comp (κ.comp (Subgroup.inclusion hHΓ))) =
    Rep.of ((dualAction n).comp (rationalDeckMatrix.comp (toDeck hle)))
  rw [this]

end Systems


section Vanishing

open TernaryPoly.PolynomialGLAction (GL3 homogeneousAction)

/-- The complexification (`V ⊕ V`) of the real polynomial system on `Γ`. -/
abbrev complexSystem {Γ : Subgroup RealGL} (κ : Γ →* GL3) (n : ℕ) (e : ℤ) : Rep.{0} ℚ Γ := doubleRep (realSystem κ n e)

/-- The complexified dual system on `Γ`. -/
abbrev complexDualSystem {Γ : Subgroup RealGL} (κ : Γ →* GL3) (n : ℕ) : Rep.{0} ℚ Γ := doubleRep (dualSystem κ n)

variable {Γ H : Subgroup RealGL} {κ : Γ →* GL3} (hκ : IsRationalStructure Γ κ)
  (hΓ : Admissible Γ) (hH : Admissible H) (hle : H ≤ gamma0) (hHΓ : H ≤ Γ)
  [Finite (gamma0 ⧸ H.subgroupOf gamma0)] [Finite (Γ ⧸ H.subgroupOf Γ)] {n : ℕ} (hn : 0 < n)

include hκ hH hle hHΓ hn in
/-- **Real coefficients, general `Γ`.** -/
theorem singularVanish_real (e : ℤ) : SingularVanish Γ hΓ (realSystem κ n e) := by
  refine singularVanish_of_subgroup hH hΓ hHΓ _ ?_
  rw [res_realSystem hκ hle hHΓ]
  exact singularVanish_of_primitive (Treal n) hle hH _ (coefficientScalarExtension n)
    (fun g z => coefficientScalarExtension_equivariant n e g z) (primitive_real hH hn)

include hκ hH hle hHΓ hn in
/-- **Dual coefficients, general `Γ`.** -/
theorem singularVanish_dual : SingularVanish Γ hΓ (dualSystem κ n) := by
  refine singularVanish_of_subgroup hH hΓ hHΓ _ ?_
  rw [res_dualSystem hκ hle hHΓ]
  exact singularVanish_of_primitive (Tdual n) hle hH _ (coefficientScalarExtension n)
    (fun g z => dual_scalarExtension_equivariant n g z) (primitive_dual hH hn)

include hκ hH hle hHΓ hn in
/-- **Complex coefficients (doubled rational model), general `Γ`.** -/
theorem singularVanish_complex (e : ℤ) : SingularVanish Γ hΓ (complexSystem κ n e) := by
  refine singularVanish_of_subgroup hH hΓ hHΓ _ ?_
  have h := res_realSystem hκ hle hHΓ n e
  change SingularVanish H hH (doubleRep (Rep.res (Subgroup.inclusion hHΓ) (realSystem κ n e)))
  rw [h]
  exact singularVanish_of_primitive (Tcx n) hle hH (doubleRep (rationalDeckCoefficientRep n e))
    (doubleCxEquiv (rationalDeckCoefficientRep n e) (coefficientScalarExtension n))
    (doubleCxEquiv_equivariant (rationalDeckCoefficientRep n e) (Treal n) (Tcx n)
      (fun g p => reImEquiv_complexRepresentation n g p) (coefficientScalarExtension n)
      (fun g z => coefficientScalarExtension_equivariant n e g z))
    (primitive_complex hH hn)

include hκ hH hle hHΓ hn in
/-- **Complexified dual coefficients (doubled rational model), general `Γ`.** -/
theorem singularVanish_complex_dual : SingularVanish Γ hΓ (complexDualSystem κ n) := by
  refine singularVanish_of_subgroup hH hΓ hHΓ _ ?_
  have h := res_dualSystem hκ hle hHΓ n
  change SingularVanish H hH (doubleRep (Rep.res (Subgroup.inclusion hHΓ) (dualSystem κ n)))
  rw [h]
  exact singularVanish_of_primitive (Tcxd n) hle hH (doubleRep (dualDeckCoefficientRep n))
    (doubleCxEquiv (dualDeckCoefficientRep n) (coefficientScalarExtension n))
    (doubleCxEquiv_equivariant (dualDeckCoefficientRep n) (Tdual n) (Tcxd n)
      (fun g p => reImEquiv_complexRepresentation n (thetaHom g) p) (coefficientScalarExtension n)
      (fun g z => dual_scalarExtension_equivariant n g z))
    (primitive_complex_dual hH hn)

include hκ hH hle hHΓ hn in
/-- **Literal complex dual coefficients, general `Γ`:** the real scalar extension of the doubled dual
system is the literal `StrongDual ℂ (Sym^n ℂ³)` with the contragredient action. -/
theorem singularVanish_lit : SingularVanish Γ hΓ (complexDualSystem κ n) := by
  refine singularVanish_of_subgroup hH hΓ hHΓ _ ?_
  have h := res_dualSystem hκ hle hHΓ n
  change SingularVanish H hH (doubleRep (Rep.res (Subgroup.inclusion hHΓ) (dualSystem κ n)))
  rw [h]
  exact singularVanish_of_primitive (Tlit n) hle hH (doubleRep (dualDeckCoefficientRep n))
    (litRealEquiv n) (fun g z => litRealEquiv_equivariant n g z) (primitive_lit hH hn)

end Vanishing


section Commensurable

open TernaryPoly.PolynomialGLAction (GL3 homogeneousAction)

theorem finite_quotient_of_relIndex {A B : Subgroup RealGL} (h : A.relIndex B ≠ 0) :
    Finite (B ⧸ A.subgroupOf B) := by
  have hfi : (A.subgroupOf B).FiniteIndex := ⟨h⟩
  exact Subgroup.finite_quotient_of_finiteIndex

variable {Γ : Subgroup RealGL} {κ : Γ →* GL3} (hκ : IsRationalStructure Γ κ)
  (hΓ : Admissible Γ) (hc : Γ.Commensurable gamma0) {n : ℕ} (hn : 0 < n)

include hc in
theorem finite_gamma0_inf : Finite (gamma0 ⧸ (Γ ⊓ gamma0).subgroupOf gamma0) :=
  finite_quotient_of_relIndex (by rw [Subgroup.inf_relIndex_right]; exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hc.1)

include hc in
theorem finite_Γ_inf : Finite (Γ ⧸ (Γ ⊓ gamma0).subgroupOf Γ) :=
  finite_quotient_of_relIndex (by rw [Subgroup.inf_relIndex_left]; exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hc.2)

include hκ hΓ hc hn in
/-- **Real coefficients for every arithmetic group commensurable with the cover.** -/
theorem singularVanish_real_of_comm (e : ℤ) : SingularVanish Γ hΓ (realSystem κ n e) := by
  have := finite_gamma0_inf hc
  have := finite_Γ_inf hc
  exact singularVanish_real hκ hΓ (hΓ.mono inf_le_left) inf_le_right inf_le_left hn e

include hκ hΓ hc hn in
/-- **Dual coefficients for every arithmetic group commensurable with the cover.** -/
theorem singularVanish_dual_of_comm : SingularVanish Γ hΓ (dualSystem κ n) := by
  have := finite_gamma0_inf hc
  have := finite_Γ_inf hc
  exact singularVanish_dual hκ hΓ (hΓ.mono inf_le_left) inf_le_right inf_le_left hn

include hκ hΓ hc hn in
/-- **Complex coefficients (doubled rational model).** -/
theorem singularVanish_complex_of_comm (e : ℤ) : SingularVanish Γ hΓ (complexSystem κ n e) := by
  have := finite_gamma0_inf hc
  have := finite_Γ_inf hc
  exact singularVanish_complex hκ hΓ (hΓ.mono inf_le_left) inf_le_right inf_le_left hn e

include hκ hΓ hc hn in
/-- **Complexified dual coefficients (doubled rational model).** -/
theorem singularVanish_complex_dual_of_comm : SingularVanish Γ hΓ (complexDualSystem κ n) := by
  have := finite_gamma0_inf hc
  have := finite_Γ_inf hc
  exact singularVanish_complex_dual hκ hΓ (hΓ.mono inf_le_left) inf_le_right inf_le_left hn

include hκ hΓ hc hn in
/-- **Literal complex dual coefficients.** -/
theorem singularVanish_lit_of_comm : SingularVanish Γ hΓ (complexDualSystem κ n) := by
  have := finite_gamma0_inf hc
  have := finite_Γ_inf hc
  exact singularVanish_lit hκ hΓ (hΓ.mono inf_le_left) inf_le_right inf_le_left hn

end Commensurable


section Arithmetic

open TernaryPoly.PolynomialGLAction (GL3)

/-- Rational matrices as real ones. -/
abbrev embQ : GL3 →* RealGL := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- Integral matrices as rational ones. -/
abbrev embZ : IntegralGL →* GL3 := Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)

theorem realIntegral_eq_comp : realIntegral = embQ.comp embZ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  ext i j
  simp [realIntegral]

/-- A common integral denominator for a finite set of rationals. -/
theorem exists_int_mul (S : Finset ℚ) : ∃ b : ℤ, b ≠ 0 ∧ ∀ q ∈ S, ∃ z : ℤ, (z : ℚ) = b * q := by
  refine ⟨∏ q ∈ S, (q.den : ℤ), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro q _
    exact_mod_cast q.den_nz
  · intro q hq
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℚ => (q.den : ℤ)) hq
    refine ⟨k * q.num, ?_⟩
    rw [hk]
    push_cast
    have := Rat.mul_den_eq_num q
    calc ((k : ℚ) * q.num) = k * (q * q.den) := by rw [this]
      _ = _ := by ring

theorem alg (Gq G'q Yq : Matrix (Fin 3) (Fin 3) ℚ) (hGG : Gq * G'q = 1) (b N : ℤ) :
    (1 : Matrix (Fin 3) (Fin 3) ℚ) + N • ((b • Gq) * Yq * (b • G'q)) =
      Gq * (1 + (N * b ^ 2) • Yq) * G'q := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, hGG]
  congr 2
  · ring

/-- **Conjugation by a rational matrix maps deep principal congruence subgroups into shallow ones.** -/
theorem exists_conj_le (g0 : GL3) {N' : ℕ} (hN' : 0 < N') :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ (principal M).map embZ, g0 * x * g0⁻¹ ∈ (principal N').map embZ := by
  classical
  obtain ⟨b, hb, hS⟩ := exists_int_mul
    (Finset.univ.image (fun p : Fin 3 × Fin 3 => (g0 : Matrix (Fin 3) (Fin 3) ℚ) p.1 p.2) ∪
      Finset.univ.image (fun p : Fin 3 × Fin 3 => ((g0⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℚ) p.1 p.2))
  have hG : ∀ i j, ∃ z : ℤ, (z : ℚ) = b * (g0 : Matrix (Fin 3) (Fin 3) ℚ) i j := fun i j =>
    hS _ (by simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
             exact Or.inl ⟨(i, j), rfl⟩)
  have hG' : ∀ i j, ∃ z : ℤ, (z : ℚ) = b * ((g0⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℚ) i j := fun i j =>
    hS _ (by simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
             exact Or.inr ⟨(i, j), rfl⟩)
  choose G₁ hG₁ using hG
  choose G₁' hG₁' using hG'
  refine ⟨N' * b.natAbs ^ 2, by positivity, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hM : ((N' * b.natAbs ^ 2 : ℕ) : ℤ) = N' * b ^ 2 := by
    push_cast
    rw [sq_abs]
  choose Y hY using fun i j => (mem_principal_iff (N' * b.natAbs ^ 2) a).mp ha i j
  set Gq : Matrix (Fin 3) (Fin 3) ℚ := (g0 : Matrix (Fin 3) (Fin 3) ℚ) with hGq
  set G'q : Matrix (Fin 3) (Fin 3) ℚ := ((g0⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℚ) with hG'q
  have hGG : Gq * G'q = 1 := Units.mul_inv g0
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  let Ym : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of Y
  let G1 : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of G₁
  let G1' : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of G₁'
  have ha_eq : a.val = 1 + ((N' : ℤ) * b ^ 2) • Ym := by
    ext i j
    have := hY i j
    rw [hM] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Ym, Matrix.of_apply]
    linarith
  have hG1 : G1.map f = b • Gq := by
    ext i j
    simp only [G1, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Gq]
    exact_mod_cast hG₁ i j
  have hG1' : G1'.map f = b • G'q := by
    ext i j
    simp only [G1', Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, G'q]
    exact_mod_cast hG₁' i j
  let B : Matrix (Fin 3) (Fin 3) ℤ := 1 + (N' : ℤ) • (G1 * Ym * G1')
  have hB : B.map f = Gq * a.val.map f * G'q := by
    have e1 : f.mapMatrix B = 1 + (N' : ℤ) • ((b • Gq) * f.mapMatrix Ym * (b • G'q)) := by
      simp only [B, map_add, map_one, map_zsmul, map_mul]
      have h1 : f.mapMatrix G1 = b • Gq := hG1
      have h1' : f.mapMatrix G1' = b • G'q := hG1'
      rw [h1, h1']
    have e2 : f.mapMatrix a.val = 1 + ((N' : ℤ) * b ^ 2) • f.mapMatrix Ym := by
      rw [ha_eq]
      simp only [map_add, map_one, map_zsmul]
    change f.mapMatrix B = Gq * f.mapMatrix a.val * G'q
    rw [e1, e2]
    exact alg Gq G'q (f.mapMatrix Ym) hGG b N'
  have hdet : IsUnit B.det := by
    have h1 : f B.det = f a.val.det := by
      rw [RingHom.map_det, RingHom.map_det]
      change (B.map f).det = (a.val.map f).det
      rw [hB, Matrix.det_mul, Matrix.det_mul]
      have : Gq.det * G'q.det = 1 := by
        rw [← Matrix.det_mul, hGG, Matrix.det_one]
      calc Gq.det * (a.val.map f).det * G'q.det = (a.val.map f).det * (Gq.det * G'q.det) := by ring
        _ = _ := by rw [this, mul_one]
    have h2 : B.det = a.val.det := Int.cast_injective h1
    rw [h2]
    exact (Matrix.GeneralLinearGroup.det a).isUnit
  let b' : IntegralGL := ⟨B, B⁻¹, Matrix.mul_nonsing_inv B hdet, Matrix.nonsing_inv_mul B hdet⟩
  refine ⟨b', ?_, ?_⟩
  · refine (mem_principal_iff N' b').mpr ?_
    intro i j
    refine ⟨(G1 * Ym * G1') i j, ?_⟩
    change B i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j = _
    simp only [B, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · apply Units.ext
    exact hB

theorem principalReal_eq (N : ℕ) : principalReal N = ((principal N).map embZ).map embQ := by
  rw [Subgroup.map_map, ← realIntegral_eq_comp]
  rfl

theorem gamma0_eq : gamma0 = principalReal 6 := by
  have h : principalSixInK.map TernaryPoly.ModThreeGoodAction.K.subtype = principalSix := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (mem_principalSixInK k).mp hk
    · intro hg
      exact ⟨⟨g, principalSix_le_K hg⟩, hg, rfl⟩
  change (principalSixInK.map TernaryPoly.ModThreeGoodAction.K.subtype).map realIntegral = _
  rw [h]
  rfl

theorem commensurable_principal (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (principal N).Commensurable (principal M) := by
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero M := ⟨hM.ne'⟩
  have h1 : (principal N).IsFiniteRelIndex (principal M) := Subgroup.isFiniteRelIndex_of_finiteIndex
  have h2 : (principal M).IsFiniteRelIndex (principal N) := Subgroup.isFiniteRelIndex_of_finiteIndex
  exact ⟨h1, h2⟩

theorem commensurable_map {G G' : Type*} [Group G] [Group G'] {f : G →* G'} (hf : Function.Injective f)
    {A B : Subgroup G} (h : A.Commensurable B) : (A.map f).Commensurable (B.map f) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Subgroup.relIndex_map_map_of_injective A B hf]; exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp h.1
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Subgroup.relIndex_map_map_of_injective B A hf]; exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp h.2

theorem commensurable_principalReal (N : ℕ) (hN : 0 < N) :
    (principalReal N).Commensurable gamma0 := by
  rw [gamma0_eq]
  exact commensurable_map realIntegral_injective (commensurable_principal N 6 hN (by norm_num))


theorem embZ_injective : Function.Injective embZ := by
  intro a b h
  apply Units.ext
  have := congrArg (fun g : GL3 => (g : Matrix (Fin 3) (Fin 3) ℚ)) h
  exact Matrix.map_injective Int.cast_injective this

/-- The principal congruence subgroup of level `M` inside `GL₃(ℚ)`. -/
def PQ (M : ℕ) : Subgroup GL3 := (principal M).map embZ

/-- The conjugate `g Δ g⁻¹` of a subgroup of `GL₃(ℚ)`. -/
def conjQ (Δ : Subgroup GL3) (g0 : GL3) : Subgroup GL3 := Δ.map (MulAut.conj g0).toMonoidHom

theorem principal_le_of_dvd {M M' : ℕ} (h : M' ∣ M) : principal M ≤ principal M' := by
  intro g hg
  apply (mem_principal_iff M' g).mpr
  intro i j
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) ((mem_principal_iff M g).mp hg i j)

theorem PQ_le_of_dvd {M M' : ℕ} (h : M' ∣ M) : PQ M ≤ PQ M' :=
  Subgroup.map_mono (principal_le_of_dvd h)

theorem commensurable_PQ (M N : ℕ) (hM : 0 < M) (hN : 0 < N) : (PQ M).Commensurable (PQ N) :=
  commensurable_map embZ_injective (commensurable_principal M N hM hN)

theorem conjQ_mono {Δ Δ' : Subgroup GL3} (h : Δ ≤ Δ') (g0 : GL3) : conjQ Δ g0 ≤ conjQ Δ' g0 :=
  Subgroup.map_mono h

theorem conj_mem_conjQ {Δ : Subgroup GL3} {x : GL3} (hx : x ∈ Δ) (g0 : GL3) :
    g0 * x * g0⁻¹ ∈ conjQ Δ g0 := ⟨x, hx, rfl⟩

theorem exists_conjQ_le (g0 : GL3) {N' : ℕ} (hN' : 0 < N') :
    ∃ M : ℕ, 0 < M ∧ conjQ (PQ M) g0 ≤ PQ N' := by
  obtain ⟨M, hM, h⟩ := exists_conj_le g0 hN'
  refine ⟨M, hM, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

/-- **Rational conjugates of principal congruence subgroups are commensurable with `Γ(6)`.** -/
theorem commensurable_conjQ_PQ (g0 : GL3) (N : ℕ) (hN : 0 < N) :
    (conjQ (PQ N) g0).Commensurable (PQ 6) := by
  obtain ⟨M1, hM1, h1⟩ := exists_conjQ_le g0 (N' := 6) (by norm_num)
  have hM : 0 < M1 * N := Nat.mul_pos hM1 hN
  obtain ⟨M2', hM2', h2⟩ := exists_conjQ_le g0⁻¹ (N' := M1 * N) hM
  have hM2 : 0 < M2' * 6 := Nat.mul_pos hM2' (by norm_num)
  -- C = g0 Γ(M1 N) g0⁻¹ lies between Γ(6 M2') and both Γ(N)-conjugate and Γ(6)
  have hCB : conjQ (PQ (M1 * N)) g0 ≤ PQ 6 :=
    (conjQ_mono (PQ_le_of_dvd (Dvd.intro N rfl)) g0).trans h1
  have hCA : conjQ (PQ (M1 * N)) g0 ≤ conjQ (PQ N) g0 :=
    conjQ_mono (PQ_le_of_dvd (Dvd.intro_left M1 rfl)) g0
  have hDC : PQ (M2' * 6) ≤ conjQ (PQ (M1 * N)) g0 := by
    intro x hx
    have hx' : x ∈ PQ M2' := PQ_le_of_dvd (Dvd.intro 6 rfl) hx
    have hm : g0⁻¹ * x * g0⁻¹⁻¹ ∈ PQ (M1 * N) := h2 (conj_mem_conjQ hx' g0⁻¹)
    refine ⟨g0⁻¹ * x * g0⁻¹⁻¹, hm, ?_⟩
    change g0 * (g0⁻¹ * x * g0⁻¹⁻¹) * g0⁻¹ = x
    group
  constructor
  · -- `[Γ(6) : (g0 Γ(N) g0⁻¹) ⊓ Γ(6)]` is finite
    by_contra hzero
    have h0 : (conjQ (PQ N) g0).relIndex (PQ 6) = 0 := by
      by_contra h; exact hzero (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr h)
    have : (PQ (M2' * 6)).relIndex (PQ 6) = 0 :=
      Subgroup.relIndex_eq_zero_of_le_left (hDC.trans hCA) h0
    exact (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp (commensurable_PQ (M2' * 6) 6 hM2 (by norm_num)).1) this
  · by_contra hzero
    have h0 : (PQ 6).relIndex (conjQ (PQ N) g0) = 0 := by
      by_contra h; exact hzero (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr h)
    have : (conjQ (PQ (M1 * N)) g0).relIndex (conjQ (PQ N) g0) = 0 :=
      Subgroup.relIndex_eq_zero_of_le_left hCB h0
    have hinj : Function.Injective (MulAut.conj g0).toMonoidHom := (MulAut.conj g0).injective
    rw [conjQ, conjQ, Subgroup.relIndex_map_map_of_injective _ _ hinj] at this
    exact (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp (commensurable_PQ (M1 * N) N hM hN).1) this

end Arithmetic

section Concrete

open TernaryPoly.PolynomialGLAction (GL3)

/-- The rational structure of the image of a subgroup of `GL₃(ℤ)` in `GL₃(ℝ)`. -/
def intStructure (A : Subgroup IntegralGL) : A.map realIntegral →* GL3 :=
  embZ.comp (A.subtype.comp
    (Subgroup.equivMapOfInjective A realIntegral realIntegral_injective).symm.toMonoidHom)

theorem intStructure_isRational (A : Subgroup IntegralGL) :
    IsRationalStructure (A.map realIntegral) (intStructure A) := by
  intro γ
  have h := (Subgroup.equivMapOfInjective A realIntegral realIntegral_injective).apply_symm_apply γ
  have h2 := congrArg Subtype.val h
  rw [Subgroup.coe_equivMapOfInjective_apply] at h2
  change embQ (embZ _) = _
  rw [← MonoidHom.comp_apply embQ embZ, ← realIntegral_eq_comp]
  exact h2

/-- The rational structure of the principal congruence subgroup `Γ(N)`. -/
def principalStructure (N : ℕ) : principalReal N →* GL3 := intStructure (principal N)

theorem principalStructure_isRational (N : ℕ) :
    IsRationalStructure (principalReal N) (principalStructure N) :=
  intStructure_isRational (principal N)

/-- Conjugation identifies `Γ` with `g Γ g⁻¹`. -/
def conjEquiv (Γ : Subgroup RealGL) (g : RealGL) : Γ ≃* conjSubgroup Γ g :=
  Subgroup.equivMapOfInjective Γ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem coe_conjEquiv (Γ : Subgroup RealGL) (g : RealGL) (y : Γ) :
    ((conjEquiv Γ g y : conjSubgroup Γ g) : RealGL) = g * y * g⁻¹ := rfl

/-- The rational structure of a conjugate `g Γ g⁻¹` by a rational matrix `g`. -/
def conjStructure {Γ : Subgroup RealGL} (κ : Γ →* GL3) (g0 : GL3) :
    conjSubgroup Γ (embQ g0) →* GL3 :=
  (MulAut.conj g0).toMonoidHom.comp (κ.comp (conjEquiv Γ (embQ g0)).symm.toMonoidHom)

theorem conjStructure_isRational {Γ : Subgroup RealGL} {κ : Γ →* GL3} (hκ : IsRationalStructure Γ κ)
    (g0 : GL3) : IsRationalStructure (conjSubgroup Γ (embQ g0)) (conjStructure κ g0) := by
  intro x
  have h2 := congrArg Subtype.val ((conjEquiv Γ (embQ g0)).apply_symm_apply x)
  rw [coe_conjEquiv] at h2
  change embQ (g0 * κ ((conjEquiv Γ (embQ g0)).symm x) * g0⁻¹) = _
  rw [map_mul, map_mul, map_inv, hκ]
  exact h2

theorem conjQ_map_embQ (Δ : Subgroup GL3) (g0 : GL3) :
    (conjQ Δ g0).map embQ = conjSubgroup (Δ.map embQ) (embQ g0) := by
  unfold conjQ conjSubgroup
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp

theorem commensurable_principalReal_conj (g0 : GL3) (N : ℕ) (hN : 0 < N) :
    (conjSubgroup (principalReal N) (embQ g0)).Commensurable gamma0 := by
  have h := commensurable_map glMap_injective (commensurable_conjQ_PQ g0 N hN)
  rw [conjQ_map_embQ] at h
  have e1 : (PQ N).map embQ = principalReal N := (principalReal_eq N).symm
  have e2 : (PQ 6).map embQ = gamma0 := by
    rw [gamma0_eq, principalReal_eq]
    rfl
  rw [e1, e2] at h
  exact h

end Concrete

section Final

open TernaryPoly.PolynomialGLAction (GL3)

variable {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) {n : ℕ} (hn : 0 < n)

/-! ### Principal congruence subgroups `Γ(N)`, `3 ∣ N` -/

include h3 hN hn in
/-- **`H²_c → H²` vanishes for `Γ(N)` with real coefficients `Sym^n`.** -/
theorem singularVanish_principal_real (e : ℤ) :
    SingularVanish (principalReal N) (admissible_principalReal h3)
      (realSystem (principalStructure N) n e) :=
  singularVanish_real_of_comm (principalStructure_isRational N) (admissible_principalReal h3)
    (commensurable_principalReal N hN) hn e

include h3 hN hn in
/-- **Dual coefficients.** -/
theorem singularVanish_principal_dual :
    SingularVanish (principalReal N) (admissible_principalReal h3)
      (dualSystem (principalStructure N) n) :=
  singularVanish_dual_of_comm (principalStructure_isRational N) (admissible_principalReal h3)
    (commensurable_principalReal N hN) hn

include h3 hN hn in
/-- **Complex coefficients (doubled rational model).** -/
theorem singularVanish_principal_complex (e : ℤ) :
    SingularVanish (principalReal N) (admissible_principalReal h3)
      (complexSystem (principalStructure N) n e) :=
  singularVanish_complex_of_comm (principalStructure_isRational N) (admissible_principalReal h3)
    (commensurable_principalReal N hN) hn e

include h3 hN hn in
/-- **Complexified dual coefficients (doubled rational model).** -/
theorem singularVanish_principal_complex_dual :
    SingularVanish (principalReal N) (admissible_principalReal h3)
      (complexDualSystem (principalStructure N) n) :=
  singularVanish_complex_dual_of_comm (principalStructure_isRational N)
    (admissible_principalReal h3) (commensurable_principalReal N hN) hn

include h3 hN hn in
/-- **Literal complex dual coefficients.** -/
theorem singularVanish_principal_lit :
    SingularVanish (principalReal N) (admissible_principalReal h3)
      (complexDualSystem (principalStructure N) n) :=
  singularVanish_lit_of_comm (principalStructure_isRational N) (admissible_principalReal h3)
    (commensurable_principalReal N hN) hn

/-! ### Rational conjugates `g Γ(N) g⁻¹`, `g ∈ GL₃(ℚ)` -/

include h3 hN hn in
/-- **Real coefficients, rational conjugate.** -/
theorem singularVanish_conj_real (g0 : GL3) (e : ℤ) :
    SingularVanish (conjSubgroup (principalReal N) (embQ g0))
      ((admissible_principalReal h3).conj _)
      (realSystem (conjStructure (principalStructure N) g0) n e) :=
  singularVanish_real_of_comm
    (conjStructure_isRational (principalStructure_isRational N) g0)
    ((admissible_principalReal h3).conj _) (commensurable_principalReal_conj g0 N hN) hn e

include h3 hN hn in
/-- **Dual coefficients, rational conjugate.** -/
theorem singularVanish_conj_dual (g0 : GL3) :
    SingularVanish (conjSubgroup (principalReal N) (embQ g0))
      ((admissible_principalReal h3).conj _)
      (dualSystem (conjStructure (principalStructure N) g0) n) :=
  singularVanish_dual_of_comm
    (conjStructure_isRational (principalStructure_isRational N) g0)
    ((admissible_principalReal h3).conj _) (commensurable_principalReal_conj g0 N hN) hn

include h3 hN hn in
/-- **Complex coefficients (doubled rational model), rational conjugate.** -/
theorem singularVanish_conj_complex (g0 : GL3) (e : ℤ) :
    SingularVanish (conjSubgroup (principalReal N) (embQ g0))
      ((admissible_principalReal h3).conj _)
      (complexSystem (conjStructure (principalStructure N) g0) n e) :=
  singularVanish_complex_of_comm
    (conjStructure_isRational (principalStructure_isRational N) g0)
    ((admissible_principalReal h3).conj _) (commensurable_principalReal_conj g0 N hN) hn e

include h3 hN hn in
/-- **Complexified dual coefficients (doubled rational model), rational conjugate.** -/
theorem singularVanish_conj_complex_dual (g0 : GL3) :
    SingularVanish (conjSubgroup (principalReal N) (embQ g0))
      ((admissible_principalReal h3).conj _)
      (complexDualSystem (conjStructure (principalStructure N) g0) n) :=
  singularVanish_complex_dual_of_comm
    (conjStructure_isRational (principalStructure_isRational N) g0)
    ((admissible_principalReal h3).conj _) (commensurable_principalReal_conj g0 N hN) hn

include h3 hN hn in
/-- **Literal complex dual coefficients, rational conjugate.** -/
theorem singularVanish_conj_lit (g0 : GL3) :
    SingularVanish (conjSubgroup (principalReal N) (embQ g0))
      ((admissible_principalReal h3).conj _)
      (complexDualSystem (conjStructure (principalStructure N) g0) n) :=
  singularVanish_lit_of_comm
    (conjStructure_isRational (principalStructure_isRational N) g0)
    ((admissible_principalReal h3).conj _) (commensurable_principalReal_conj g0 N hN) hn

end Final

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
