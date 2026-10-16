module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.Descent
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneFaceBridge
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNExt

@[expose] public section


/-!
# The Γ(N) plane group versus the level group's identity plane

Paper: Lemma C.3 (`ar:lem:seed`).

The identity plane of the paper's level group `Γ = {g ∈ GL₃(ℤ) | e₃* g ≡ e₃* mod 3}` has stabilizer
`Λ₀ = ℤ² ⋊ GL₂(ℤ)` (`LamStab`); the plane group of `Γ(N)` is `Γ(N) ∩ P(ℤ) = Nℤ² ⋊ Γ₂(N)`
(`gammaNExt`).  Every element of the latter has bottom row `(0, 0, 1)` and lies in `Γ`, so there is a
direct inclusion `gammaNToStab : Γ(N) ∩ P(ℤ) → Λ₀`, a morphism of split extensions (radical
multiplied by `N`, Levi `Γ₂(N) ⊆ SL₂(ℤ) ⊆ GL₂(ℤ)`, identical coefficients).  Its image is the kernel of
`(reduction mod N, det)` (`range_eq_ker`), hence normal of finite index.

* `badPlane_level_descent`: for a class `z ∈ H²(Λ₀, E_n)` with zero radical restriction (automatic for
  odd `n`), the Hochschild--Serre edge of `z` lies in the literal mixed cuspidal group
  `badPlaneCuspidal n` of `H¹(GL₂(ℤ), H¹(ℤ², E_n))` iff the restriction of `z` to the plane group of
  `Γ(N)` lies in `gammaNCuspidalInH2 N n`.  This is the finite-index descent of
  `LevelDescent.edge_mem_cuspidalFamily_descent`; the cusp subgroups `cuspGL F` pull back to the cusp
  stabilizers `leviCuspStab Γ(N) F` of `Γ₂(N)`.
* `badPlane_locallyInner_level_descent`: the same for the face library's `locallyInnerClasses`.

Hence, with the unconditional `Γ(N)` spanning theorem, the seeds of the plane group of `Γ(N)` span the
image of the level group's locally inner classes in `H²(Γ(N) ∩ P(ℤ), E_n)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section BadPlaneLevel

variable (N : ℕ)

/-- The stabilizer of the identity plane in the paper's level group. -/
abbrev LamStab : Subgroup RationalGL3 :=
  flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))

theorem gammaNP_mem_arithmeticLevel (p : ↥(gammaNP N)) :
    Matrix.SpecialLinearGroup.toGL p.1 ∈ arithmeticLevel := by
  have h0 : (p.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := p.2.2.1
  have h1 : (p.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := p.2.2.2.1
  have h2 : (p.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := p.2.2.2.2
  change lastRow ᵥ* (reductionThree (Matrix.SpecialLinearGroup.toGL p.1)).val = lastRow
  funext j
  fin_cases j <;>
    simp [vecMul, dotProduct, lastRow, Pi.single_apply, reductionThree,
      GeneralLinearGroup.map_apply, h0, h1, h2]

/-- The homomorphism `gammaNP N → arithmeticLevel`. -/
def gammaNToLevel : ↥(gammaNP N) →* arithmeticLevel :=
  ((Matrix.SpecialLinearGroup.toGL).comp (gammaNP N).subtype).codRestrict arithmeticLevel
    (gammaNP_mem_arithmeticLevel N)

theorem gammaNToLevel_val (p : ↥(gammaNP N)) :
    (rationalInclusion (gammaNToLevel N p)).val =
      (Matrix.SpecialLinearGroup.mapGL ℚ p.1).val := by
  ext i j
  simp only [rationalInclusion, MonoidHom.comp_apply, GeneralLinearGroup.map_apply,
    Matrix.SpecialLinearGroup.mapGL]
  rfl

theorem gammaNToLevel_apply (p : ↥(gammaNP N)) (i j : Fin 3) :
    ((rationalInclusion (gammaNToLevel N p)).val : Matrix (Fin 3) (Fin 3) ℚ) i j =
      (((p.1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ℚ) := rfl

theorem gammaNToLevel_mem_stab (p : ↥(gammaNP N)) :
    rationalInclusion (gammaNToLevel N p) ∈ MulAction.stabilizer RationalGL3
      (QuotientGroup.mk (1 : RationalGL3) : Flags .plane) := by
  have h0 : (p.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := p.2.2.1
  have h1 : (p.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := p.2.2.2.1
  have hx : rationalInclusion (gammaNToLevel N p) ∈ planeParabolic ℚ := by
    refine ⟨?_, ?_⟩ <;>
      simp [gammaNToLevel_val, Matrix.SpecialLinearGroup.mapGL, h0, h1]
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (rationalInclusion (gammaNToLevel N p) * 1) : Flags .plane) =
    QuotientGroup.mk 1
  rw [mul_one]
  apply QuotientGroup.eq.mpr
  rw [mul_one]
  exact (parabolic .plane).inv_mem hx

/-- **The plane group `Γ(N) ∩ P(ℤ)` as a subgroup of the stabilizer of the identity plane in the
level group.** -/
def gammaNToStab : ↥(gammaNP N) →* ↥(LamStab) :=
  (rationalInclusion.comp (gammaNToLevel N)).codRestrict LamStab
    (fun p => ⟨⟨gammaNToLevel N p, rfl⟩, gammaNToLevel_mem_stab N p⟩)

theorem gammaNToStab_val (p : ↥(gammaNP N)) :
    (gammaNToStab N p).val = rationalInclusion (gammaNToLevel N p) := rfl

theorem gammaNToStab_injective : Function.Injective (gammaNToStab N) := by
  intro a b h
  have h1 := congrArg Subtype.val h
  rw [gammaNToStab_val, gammaNToStab_val] at h1
  have h2 := congrArg Units.val h1
  rw [gammaNToLevel_val, gammaNToLevel_val] at h2
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h2 i) j
  simpa [Matrix.SpecialLinearGroup.mapGL] using this

variable [NeZero N]

/-- The comparison of radicals: multiplication by `N` on `ℤ²`. -/
def radScale : RadicalLattice →* RadicalLattice := powMonoidHom N

theorem gammaNToStab_inl (r : RadicalLattice) :
    gammaNToStab N ((gammaNExt N).inl r) = identityPlaneExtension.inl (radScale N r) := by
  apply Subtype.ext
  apply Units.ext
  rw [gammaNToStab_val]
  ext i j
  rw [gammaNToLevel_apply]
  fin_cases i <;> fin_cases j <;>
    simp [gammaNExt, gammaNInl, radElt, radScale, identityPlaneExtension,
      identityPlaneRadicalInclusion, upperRadicalLattice, planeUnipotent, toAdd_pow]

/-- The comparison of Levi factors: `Γ(N) ⊆ SL₂(ℤ) ⊆ GL₂(ℤ)`. -/
def leviIncl : ↥(CongruenceSubgroup.Gamma N) →* GL (Fin 2) ℤ :=
  (Matrix.SpecialLinearGroup.toGL).comp (CongruenceSubgroup.Gamma N).subtype

omit [NeZero N] in
theorem leviIncl_injective : Function.Injective (leviIncl N) := by
  intro a b h
  have h1 := congrArg Units.val h
  apply Subtype.ext
  apply Subtype.ext
  simpa [leviIncl] using h1

theorem gammaNToStab_split (γ : ↥(CongruenceSubgroup.Gamma N)) :
    gammaNToStab N ((gammaNSplitting N) γ) = identityPlaneSplitting (leviIncl N γ) := by
  apply Subtype.ext
  apply Units.ext
  rw [gammaNToStab_val]
  ext i j
  rw [gammaNToLevel_apply]
  fin_cases i <;> fin_cases j <;>
    simp [gammaNSplitting, gammaNSect, ConvergenceC4.blockDiag, identityPlaneSplitting,
      identityPlaneLeviSection, arithmeticLeviHom, arithmeticLevi, planeLevi, planeBlock, leviIncl,
      GeneralLinearGroup.map_apply]

omit [NeZero N] in
theorem coeff_compat (n : ℕ) (p : ↥(gammaNP N)) :
    (identityPlaneCoefficientRep n).ρ (gammaNToStab N p) = (gammaNRep N n).ρ p := by
  rw [gammaNRep_ambient]
  have hmat : GeneralLinearGroup.map (algebraMap ℚ ℝ) (rationalInclusion (gammaNToLevel N p)) =
      Matrix.SpecialLinearGroup.mapGL ℝ p.1 := by
    apply Units.ext
    ext i j
    simp [GeneralLinearGroup.map_apply, gammaNToLevel_apply, Matrix.SpecialLinearGroup.mapGL]
  apply LinearMap.ext
  intro v
  change (rationalCoefficientComponent n trivialCharacter) (rationalInclusion (gammaNToLevel N p)) v =
    (realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ p.1) v
  unfold rationalCoefficientComponent
  rw [MonoidHom.comp_apply, hmat]
  simp [realCoefficientComponent, componentCharacter, trivialCharacter]

omit [NeZero N] in
theorem rationalInclusion_injective : Function.Injective rationalInclusion := by
  intro a b h
  have h1 := congrArg (fun x : RationalGL3 => (x.val : Matrix (Fin 3) (Fin 3) ℚ)) h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (congrFun h1 i) j
  simpa [rationalInclusion, GeneralLinearGroup.map_apply] using this

omit [NeZero N] in
theorem exists_lift (x : ↥LamStab) : ∃ g : arithmeticLevel, rationalInclusion g = x.val :=
  x.2.1

/-- The integral matrix of an element of the stabilizer of the identity plane. -/
def stabToLevel : ↥LamStab →* arithmeticLevel :=
  TernaryPeriodPolynomials.SphericalDetection.Helpers.monoidHomLiftThroughInjective
    LamStab.subtype rationalInclusion rationalInclusion_injective exists_lift

theorem rationalInclusion_stabToLevel (x : ↥LamStab) :
    rationalInclusion (stabToLevel x) = x.val :=
  TernaryPeriodPolynomials.SphericalDetection.Helpers.monoidHomLiftThroughInjective_spec _
    _ rationalInclusion_injective exists_lift x

omit [NeZero N] in
/-- Reduction modulo `N` and determinant of the integral matrix of an element of the stabilizer. -/
def stabReduce : ↥LamStab →* GL (Fin 3) (ZMod N) × ℤˣ :=
  ((GeneralLinearGroup.map (Int.castRingHom (ZMod N))).comp
      (arithmeticLevel.subtype.comp stabToLevel)).prod
    (Matrix.GeneralLinearGroup.det.comp (arithmeticLevel.subtype.comp stabToLevel))

omit [NeZero N] in
theorem stabToLevel_gammaNToStab (p : ↥(gammaNP N)) :
    stabToLevel (gammaNToStab N p) = gammaNToLevel N p := by
  apply rationalInclusion_injective
  rw [rationalInclusion_stabToLevel]
  rfl

omit [NeZero N] in
theorem gammaNToLevel_det (p : ↥(gammaNP N)) :
    Matrix.GeneralLinearGroup.det ((gammaNToLevel N p).1) = 1 := by
  apply Units.ext
  change (p.1 : Matrix (Fin 3) (Fin 3) ℤ).det = 1
  exact p.1.2

omit [NeZero N] in
theorem range_le_ker : (gammaNToStab N).range ≤ (stabReduce N).ker := by
  rintro _ ⟨p, rfl⟩
  rw [MonoidHom.mem_ker]
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext i j
    have h := mem_gammaN.mp p.2.1 i j
    have h2 : (((p.1 : Matrix (Fin 3) (Fin 3) ℤ) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) :
        ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr h
    rw [Int.cast_sub, sub_eq_zero] at h2
    simp only [stabReduce, MonoidHom.prod_apply, MonoidHom.comp_apply, stabToLevel_gammaNToStab]
    change (((p.1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j
    rw [h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · simp only [stabReduce, MonoidHom.prod_apply, MonoidHom.comp_apply, stabToLevel_gammaNToStab]
    exact gammaNToLevel_det N p

omit [NeZero N] in
/-- The last row of the integral matrix of an element of the stabilizer of the identity plane is
`(0, 0, 1)`. -/
theorem stab_bottom_row (x : ↥LamStab) :
    ((stabToLevel x).1.val : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    ((stabToLevel x).1.val : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
    ((stabToLevel x).1.val : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := by
  set X := (stabToLevel x).1 with hX
  have hval : ∀ i j, ((X.val i j : ℤ) : ℚ) = x.val.val i j := by
    intro i j
    have := congrArg (fun y : RationalGL3 => (y.val : Matrix (Fin 3) (Fin 3) ℚ) i j)
      (rationalInclusion_stabToLevel x)
    exact this
  have hplane : x.val ∈ planeParabolic ℚ := by
    have hst : x.val ∈ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (1 : RationalGL3) : Flags .plane) := x.2.2
    rw [MulAction.mem_stabilizer_iff] at hst
    change (QuotientGroup.mk (x.val * 1) : Flags .plane) = QuotientGroup.mk 1 at hst
    rw [mul_one] at hst
    have := QuotientGroup.eq.mp hst
    rw [mul_one] at this
    have h2 : x.val ∈ parabolic .plane := by simpa using (parabolic .plane).inv_mem this
    exact h2
  have h20 : X.val 2 0 = 0 := by
    have : ((X.val 2 0 : ℤ) : ℚ) = 0 := by rw [hval]; exact hplane.1
    exact_mod_cast this
  have h21 : X.val 2 1 = 0 := by
    have : ((X.val 2 1 : ℤ) : ℚ) = 0 := by rw [hval]; exact hplane.2
    exact_mod_cast this
  have hlev : ((X.val 2 2 : ℤ) : ZMod 3) = 1 := by
    have hm : X ∈ arithmeticLevel := (stabToLevel x).2
    have h : lastRow ᵥ* (reductionThree X).val = lastRow := hm
    have := congrFun h 2
    simpa [vecMul, dotProduct, lastRow, Fin.sum_univ_three, Pi.single_apply, reductionThree,
      GeneralLinearGroup.map_apply] using this
  have hdet : X.val.det * 1 = ((X.det : ℤˣ) : ℤ) := by
    simp
  have hu : IsUnit (X.val 2 2) := by
    have h := (Matrix.isUnit_iff_isUnit_det X.val).mp X.isUnit
    rw [Matrix.det_fin_three] at h
    simp only [h20, h21] at h
    have : X.val 0 0 * X.val 1 1 * X.val 2 2 - X.val 0 0 * X.val 1 2 * 0 - X.val 0 1 * X.val 1 0 * X.val 2 2 +
        X.val 0 1 * X.val 1 2 * 0 + X.val 0 2 * X.val 1 0 * 0 - X.val 0 2 * X.val 1 1 * 0 =
        X.val 2 2 * (X.val 0 0 * X.val 1 1 - X.val 0 1 * X.val 1 0) := by ring
    rw [this] at h
    exact isUnit_of_mul_isUnit_left h
  have h22 : X.val 2 2 = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · rw [h] at hlev
      exact absurd hlev (by decide)
  exact ⟨h20, h21, h22⟩

omit [NeZero N] in
theorem ker_le_range : (stabReduce N).ker ≤ (gammaNToStab N).range := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨h20, h21, h22⟩ := stab_bottom_row x
  set X := (stabToLevel x).1 with hX
  have hdet : X.val.det = 1 := by
    have := congrArg Prod.snd hx
    have h' : Matrix.GeneralLinearGroup.det X = 1 := this
    exact congrArg Units.val h'
  have hred : ∀ i j, (((X.val i j : ℤ)) : ZMod N) = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
    intro i j
    have := congrArg (fun y : GL (Fin 3) (ZMod N) × ℤˣ => (y.1.val : Matrix (Fin 3) (Fin 3) (ZMod N)) i j) hx
    exact this
  let q : SL(3, ℤ) := ⟨X.val, hdet⟩
  have hqN : q ∈ gammaN N := by
    rw [mem_gammaN]
    intro i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    rw [Int.cast_sub, sub_eq_zero]
    have h1 : (((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [h1]
    exact hred i j
  have hqP : q ∈ planeStab := ⟨h20, h21, h22⟩
  refine ⟨⟨q, hqN, hqP⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [gammaNToStab_val]
  ext i j
  rw [gammaNToLevel_apply]
  have := congrArg (fun y : RationalGL3 => (y.val : Matrix (Fin 3) (Fin 3) ℚ) i j)
    (rationalInclusion_stabToLevel x)
  exact this

omit [NeZero N] in
theorem range_eq_ker : (gammaNToStab N).range = (stabReduce N).ker :=
  le_antisymm (range_le_ker N) (ker_le_range N)

omit [NeZero N] in
instance range_normal : (gammaNToStab N).range.Normal := by
  rw [range_eq_ker]; infer_instance

instance range_finiteIndex : (gammaNToStab N).range.FiniteIndex := by
  rw [range_eq_ker]
  exact Subgroup.finiteIndex_ker _

omit [NeZero N] in
theorem hB_GL (F : GL (Fin 2) ℚ) (V : Rep ℂ (cuspGL F)) (x : groupCohomology.H2 V) : x = 0 :=
  TernaryPeriodPolynomials.Spectral.ModularH2.H2_zero_of_injective_binary
    ((cuspGL F).subtype.prod 1) (fun _ _ h => Subtype.ext (congrArg Prod.fst h)) V x

omit [NeZero N] in
theorem hB_Gamma (F : GL (Fin 2) ℚ)
    (V : Rep ℂ ((cuspGL F).comap (leviIncl N))) (x : groupCohomology.H2 V) : x = 0 :=
  TernaryPeriodPolynomials.Spectral.ModularH2.H2_zero_of_injective_binary
    (((leviIncl N).comp ((cuspGL F).comap (leviIncl N)).subtype).prod 1)
    (fun _ _ h => Subtype.ext (leviIncl_injective N (congrArg Prod.fst h))) V x

omit [NeZero N] in
theorem comap_cuspGL (F : GL (Fin 2) ℚ) :
    (cuspGL F).comap (leviIncl N) = leviCuspStab (CongruenceSubgroup.Gamma N) F := rfl

omit [NeZero N] in
theorem coeff_hT (n : ℕ) (g : ↥(gammaNP N)) (v : identityPlaneCoefficientRep n) :
    (LinearMap.id : identityPlaneCoefficientRep n →ₗ[ℂ] gammaNRep N n)
      ((identityPlaneCoefficientRep n).ρ (gammaNToStab N g) v) =
    (gammaNRep N n).ρ g ((LinearMap.id : identityPlaneCoefficientRep n →ₗ[ℂ] gammaNRep N n) v) := by
  have := congrArg (fun f => f v) (coeff_compat N n g)
  exact this

/-- **Level descent for the bad plane.** For `N ≠ 0` and a class `z ∈ H²(Λ₀, E_n)` of the stabilizer
of the identity plane in the paper's level group with zero radical restriction (automatic for
odd `n`), the Hochschild--Serre edge of `z` lies in the literal mixed cuspidal group of
`H¹(GL₂(ℤ), H¹(ℤ², E_n))` (restrictions to zero at every rational cusp, finite reflections included)
iff the restriction of `z` to the plane group `Γ(N) ∩ P(ℤ)` has edge in the literal mixed cuspidal
group of `H¹(Γ₂(N), H¹(Nℤ², E_n))`, that is, lies in `gammaNCuspidalInH2 N n`. -/
theorem badPlane_level_descent (n : ℕ)
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n))
    (hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0) :
    splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n) ⟨z, hz⟩ ∈
        badPlaneCuspidal n ↔
      EdgeNat.h2Map (gammaNToStab N) (identityPlaneCoefficientRep n) (gammaNRep N n)
        LinearMap.id (coeff_hT N n) z ∈ gammaNCuspidalInH2 N n := by
  rw [mem_gammaNCuspidalInH2_iff]
  have hy := EdgeNat.h2Map_ker (gammaNToStab N) (radScale N) (gammaNToStab_inl N)
    (identityPlaneCoefficientRep n) (gammaNRep N n) LinearMap.id (coeff_hT N n) z hz
  have desc := edge_mem_cuspidalFamily_descent identityPlaneSplitting (gammaNSplitting N)
    (gammaNToStab N) (leviIncl N) (radScale N) (gammaNToStab_inl N) (gammaNToStab_split N)
    (gammaNToStab_injective N) (identityPlaneCoefficientRep n) (gammaNRep N n) LinearMap.id
    (coeff_hT N n) Function.bijective_id cuspGL (fun F V x => hB_GL F V x)
    (fun F V x => hB_Gamma N F V x) z hz
  exact ⟨fun h => ⟨hy, desc.mp h⟩, fun ⟨_, h⟩ => desc.mpr h⟩

/-- **Locally inner classes at the identity plane, and the plane group of `Γ(N)`.** For a class
`z ∈ H²(Λ₀, E_n)` with zero radical restriction, its image in the face library's `H²` of the
stabilizer of the identity plane is locally inner (vanishes on the stabilizer of every complete
flag over the plane) iff the restriction of `z` to `Γ(N) ∩ P(ℤ)` lies in the literal mixed
cuspidal group `gammaNCuspidalInH2 N n` of the plane group of `Γ(N)`. -/
theorem badPlane_locallyInner_level_descent (n : ℕ)
    (z : groupCohomology.H2 (identityPlaneCoefficientRep n))
    (hz : twoCohomologyRestriction identityPlaneExtension.inl (identityPlaneCoefficientRep n) z = 0) :
    badPlaneH2Equiv n z ∈ locallyInnerClasses n trivialCharacter .plane
        FacePairingFull.Face.badPlaneFlag ↔
      EdgeNat.h2Map (gammaNToStab N) (identityPlaneCoefficientRep n) (gammaNRep N n)
        LinearMap.id (coeff_hT N n) z ∈ gammaNCuspidalInH2 N n :=
  (badPlaneH2Equiv_mem_locallyInner_iff_general n z).trans
    ⟨fun ⟨hz', h⟩ => (badPlane_level_descent N n z hz').mp h,
      fun h => ⟨hz, (badPlane_level_descent N n z hz).mpr h⟩⟩

end BadPlaneLevel

end TernaryPeriodPolynomials.Argument.SeedC3S4c
