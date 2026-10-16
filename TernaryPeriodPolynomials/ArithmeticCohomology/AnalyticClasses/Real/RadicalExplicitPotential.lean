module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinaryRelativeClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperRadicalExponential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticeInvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.NilpotentRadicalComparison

@[expose] public section


/-!
# Explicit potentials for exact real-radical one-cocycles

For a one-cocycle `C` of the real plane radical `ℝ²` with values in the cuspidal tensor values
(the radical acting through the coefficients only) whose class vanishes, an explicit potential is
obtained by applying, pointwise, one fixed linear map `g : F × F → F` (`F` the coefficient space)
to the two lattice values `C(e₁), C(e₂)`: `g` is a generalized inverse of
`q ↦ ((e₁ - 1) q, (e₂ - 1) q)`, whose kernel (the lattice invariants) is fixed by the whole real
radical. No choice depending on `C` is made, so the potential depends linearly and continuously
on finitely many values of `C`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Every linear map between finite-dimensional spaces has a generalized inverse. -/
theorem exists_generalizedInverse {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (f : V →ₗ[ℂ] W) :
    ∃ g : W →ₗ[ℂ] V, ∀ v, v - g (f v) ∈ LinearMap.ker f := by
  obtain ⟨p, complement⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have injective : LinearMap.ker (f.domRestrict p) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hker : (x : V) ∈ LinearMap.ker f := hx
    have hboth : (x : V) ∈ LinearMap.ker f ⊓ p := ⟨hker, x.property⟩
    rw [complement.inf_eq_bot, Submodule.mem_bot] at hboth
    exact Subtype.ext hboth
  obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective (f.domRestrict p) injective
  refine ⟨p.subtype.comp g', fun v => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    ((complement.sup_eq_top).symm ▸ Submodule.mem_top : v ∈ LinearMap.ker f ⊔ p)
  have fa : f a = 0 := ha
  have value : g' (f (a + b)) = ⟨b, hb⟩ := by
    rw [map_add, fa, zero_add]
    exact LinearMap.congr_fun hg' ⟨b, hb⟩
  simp only [LinearMap.comp_apply, value, Submodule.subtype_apply]
  simpa using ha

variable (degree : ℕ)

/-- The two lattice differences on the coefficient space. -/
def latticeDifferences :
    HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly degree × HomogeneousPoly degree :=
  LinearMap.prod
    ((show Module.End ℂ (HomogeneousPoly degree) from
      (upperRadicalLatticeRep degree).ρ radicalLatticeFirst) - 1)
    ((show Module.End ℂ (HomogeneousPoly degree) from
      (upperRadicalLatticeRep degree).ρ radicalLatticeSecond) - 1)

/-- A fixed generalized inverse of the lattice differences. -/
def latticeInverse :
    HomogeneousPoly degree × HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly degree :=
  Classical.choose (exists_generalizedInverse (latticeDifferences degree))

theorem latticeInverse_spec (q : HomogeneousPoly degree) :
    q - latticeInverse degree (latticeDifferences degree q) ∈
      LinearMap.ker (latticeDifferences degree) :=
  Classical.choose_spec (exists_generalizedInverse (latticeDifferences degree)) q

theorem latticeDifferences_kernel_invariant (q : HomogeneousPoly degree)
    (kernel : q ∈ LinearMap.ker (latticeDifferences degree)) :
    q ∈ (upperRadicalLatticeRep degree).ρ.invariants := by
  have value : latticeDifferences degree q = 0 := kernel
  exact (radicalLattice_invariants_iff (upperRadicalLatticeRep degree) q).mpr
    ⟨congrArg Prod.fst value, congrArg Prod.snd value⟩

theorem realRadical_decomposition (radical : RealPlaneRadical) :
    radical = realRadicalAxis 0 (radical.toAdd 0) * realRadicalAxis 1 (radical.toAdd 1) := by
  apply Multiplicative.toAdd.injective
  funext index
  fin_cases index <;> simp [realRadicalAxis]

/-- **Lattice invariants are fixed by the whole real radical.** -/
theorem realUpperRadicalRep_fixed_of_lattice (q : HomogeneousPoly degree)
    (invariant : q ∈ (upperRadicalLatticeRep degree).ρ.invariants) (radical : RealPlaneRadical) :
    (realUpperRadicalRep degree).ρ radical q = q := by
  obtain ⟨first, second⟩ := (upperRadicalInvariant_generators degree q).mp invariant
  have axis (coordinate : Fin 2) (zero : upperRadicalGenerator degree coordinate q = 0) (t : ℝ) :
      (realUpperRadicalRep degree).ρ (realRadicalAxis coordinate t) q = q := by
    rw [realUpperRadicalRep_axis]
    have nilpotent : ((t : ℂ) • upperRadicalGenerator degree coordinate) ^ (degree + 1) = 0 := by
      rw [smul_pow, upperRadicalGenerator_power_zero, smul_zero]
    have kernel := (nilpotent_difference_kernel _ degree nilpotent q).mpr (by
      rw [LinearMap.smul_apply, zero, smul_zero])
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at kernel
    refine Eq.trans ?_ kernel
    exact congrFun (congrArg DFunLike.coe (exp_inst_irrel _ _ _)) q
  rw [realRadical_decomposition radical, map_mul, Module.End.mul_apply, axis 1 second,
    axis 0 first]

variable (cusp : CuspidalRepresentation)

/-- The explicit potential of a real-radical one-cochain: the generalized inverse applied pointwise
to its two lattice values. -/
def latticePotential (first second : cuspidalTensorValues cusp (HomogeneousPoly degree)) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  cuspidalTensorMap cusp ((latticeInverse degree).comp (LinearMap.inl ℂ _ _)) first +
    cuspidalTensorMap cusp ((latticeInverse degree).comp (LinearMap.inr ℂ _ _)) second

theorem latticePotential_apply (first second : cuspidalTensorValues cusp (HomogeneousPoly degree))
    (argument : BinaryAdelicGL) :
    (latticePotential degree cusp first second).val argument =
      latticeInverse degree (first.val argument, second.val argument) := by
  change latticeInverse degree (first.val argument, 0) +
    latticeInverse degree (0, second.val argument) = _
  rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]

theorem latticePotential_zero : latticePotential degree cusp 0 0 = 0 := by
  unfold latticePotential
  rw [map_zero, map_zero, add_zero]

/-- The real radical acting on the cuspidal tensor values. -/
abbrev RealRadicalCocycles :=
  groupCohomology.cocycles₁ (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
    (realPlaneCuspidalRep degree cusp trivialCharacter))

/-- The value of a real-radical one-cocycle as cuspidal tensor values. -/
def radicalCocycleValue (cycle : RealRadicalCocycles degree cusp) (radical : RealPlaneRadical) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) := cycle radical

/-- The explicit potential of a real-radical one-cocycle. -/
def radicalCocyclePotential (cycle : RealRadicalCocycles degree cusp) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  latticePotential degree cusp (radicalCocycleValue degree cusp cycle (realRadicalAxis 0 1))
    (radicalCocycleValue degree cusp cycle (realRadicalAxis 1 1))

theorem realPlaneCuspidalRep_inl_apply (radical : RealPlaneRadical)
    (values : cuspidalTensorValues cusp (HomogeneousPoly degree)) (argument : BinaryAdelicGL) :
    (show cuspidalTensorValues cusp (HomogeneousPoly degree) from
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl radical)
        values).val argument =
      (realUpperRadicalRep degree).ρ radical (values.val argument) :=
  congrArg (fun vector : cuspidalTensorValues cusp (HomogeneousPoly degree) => vector.val argument)
    (realPlaneCuspidalRep_radical degree cusp radical values)

/-- **An exact real-radical one-cocycle is the coboundary of its explicit potential.** -/
theorem radicalCocyclePotential_boundary (cycle : RealRadicalCocycles degree cusp)
    (zero : groupCohomology.H1π _ cycle = 0) :
    oneBoundaryCycle _ (radicalCocyclePotential degree cusp cycle) = cycle := by
  obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp zero
  let p : cuspidalTensorValues cusp (HomogeneousPoly degree) := potential
  have value (radical : RealPlaneRadical) :
      radicalCocycleValue degree cusp cycle radical =
        (show cuspidalTensorValues cusp (HomogeneousPoly degree) from
          (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl radical) p) -
          p := (congrFun boundary radical).symm
  have pointwise (radical : RealPlaneRadical) (argument : BinaryAdelicGL) :
      (radicalCocycleValue degree cusp cycle radical).val argument =
        (realUpperRadicalRep degree).ρ radical (p.val argument) - p.val argument := by
    rw [value, Submodule.coe_sub, Pi.sub_apply, realPlaneCuspidalRep_inl_apply]
  have lattice (coordinate : Fin 2) (argument : BinaryAdelicGL) :
      (radicalCocycleValue degree cusp cycle (realRadicalAxis coordinate 1)).val argument =
        (show Module.End ℂ (HomogeneousPoly degree) from
          (upperRadicalLatticeRep degree).ρ (radicalLatticeGenerator coordinate)) (p.val argument) -
          p.val argument := by
    rw [value, Submodule.coe_sub, Pi.sub_apply, realRadicalAxis_one]
    congr 1
    exact realPlaneCuspidalRep_latticeRadical degree cusp (radicalLatticeGenerator coordinate) p
      argument
  apply groupCohomology.cocycles₁_ext
  intro radical
  apply Subtype.ext
  funext argument
  change (show cuspidalTensorValues cusp (HomogeneousPoly degree) from
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl radical)
        (radicalCocyclePotential degree cusp cycle)).val argument -
      (radicalCocyclePotential degree cusp cycle).val argument =
    (radicalCocycleValue degree cusp cycle radical).val argument
  rw [realPlaneCuspidalRep_inl_apply]
  have differences : ((radicalCocycleValue degree cusp cycle (realRadicalAxis 0 1)).val argument,
      (radicalCocycleValue degree cusp cycle (realRadicalAxis 1 1)).val argument) =
      latticeDifferences degree (p.val argument) := by
    rw [lattice 0, lattice 1]
    rfl
  have kernel := latticeInverse_spec degree (p.val argument)
  have fixed := realUpperRadicalRep_fixed_of_lattice degree _
    (latticeDifferences_kernel_invariant degree _ kernel) radical
  unfold radicalCocyclePotential
  rw [latticePotential_apply, differences, pointwise]
  rw [map_sub] at fixed
  linear_combination (norm := abel) -fixed

end TernaryPeriodPolynomials.AnalyticClasses
