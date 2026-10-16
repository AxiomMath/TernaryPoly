module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorExactness
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OneCocyclePullback

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspidalTensorPointwiseRep {G : Type} [Group G] (cusp : CuspidalRepresentation) (representation : Rep ℂ G) : Rep ℂ G :=
  Rep.of (X := cuspidalTensorValues cusp representation)
    { toFun := fun element => cuspidalTensorMap cusp (representation.ρ element)
      map_one' := by
        apply LinearMap.ext
        intro values
        apply Subtype.ext
        funext argument
        change representation.ρ 1 (values.val argument) = values.val argument
        rw [map_one, Module.End.one_apply]
      map_mul' := by
        intro first second
        apply LinearMap.ext
        intro values
        apply Subtype.ext
        funext argument
        change representation.ρ (first * second) (values.val argument) =
          representation.ρ first (representation.ρ second (values.val argument))
        rw [map_mul, Module.End.mul_apply] }

def cuspidalTensorEvaluation {G : Type} [Group G] (cusp : CuspidalRepresentation) (representation : Rep ℂ G)
    (argument : BinaryAdelicGL) : cuspidalTensorPointwiseRep cusp representation →ₗ[ℂ] representation where
  toFun values := values.val argument
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cuspidalTensorCocycleEvaluation {G : Type} [Group G] (cusp : CuspidalRepresentation) (representation : Rep ℂ G)
    (argument : BinaryAdelicGL) :
    groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation) →ₗ[ℂ] groupCohomology.cocycles₁ representation :=
  oneCocyclePullback _ _ (MonoidHom.id G) (cuspidalTensorEvaluation cusp representation argument) (fun _ => rfl)

theorem cuspidalTensorCocycleEvaluation_apply {G : Type} [Group G] (cusp : CuspidalRepresentation) (representation : Rep ℂ G)
    (argument : BinaryAdelicGL) (cycle : groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation)) (element : G) :
    cuspidalTensorCocycleEvaluation cusp representation argument cycle element = (cycle element).val argument := rfl

def latticeCocycleGeneratorValues (representation : Rep ℂ RadicalLattice) :
    groupCohomology.cocycles₁ representation →ₗ[ℂ] (representation × representation) where
  toFun cycle := (cycle radicalLatticeFirst, cycle radicalLatticeSecond)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem latticeCocycleGeneratorValues_injective (representation : Rep ℂ RadicalLattice) :
    Function.Injective (latticeCocycleGeneratorValues representation) := by
  intro first second equality
  exact oneCocycle_eq_of_two_generators representation first second
    radicalLatticeFirst radicalLatticeSecond radicalLattice_generated
    (congrArg Prod.fst equality) (congrArg Prod.snd equality)

def latticeCocycleGeneratorRetraction (representation : Rep ℂ RadicalLattice) :
    (representation × representation) →ₗ[ℂ] groupCohomology.cocycles₁ representation :=
  ((latticeCocycleGeneratorValues representation).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (latticeCocycleGeneratorValues_injective representation))).choose

theorem latticeCocycleGeneratorRetraction_apply (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₁ representation) :
    latticeCocycleGeneratorRetraction representation (cycle radicalLatticeFirst, cycle radicalLatticeSecond) = cycle :=
  LinearMap.congr_fun ((latticeCocycleGeneratorValues representation).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (latticeCocycleGeneratorValues_injective representation))).choose_spec cycle

def cuspidalLatticeCocycleFamily (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice) :
    groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation) →ₗ[ℂ]
      cuspidalTensorValues cusp (groupCohomology.cocycles₁ representation) where
  toFun cycle := cuspidalTensorMap cusp (latticeCocycleGeneratorRetraction representation)
    (cuspidalTensorPair cusp (cycle radicalLatticeFirst) (cycle radicalLatticeSecond))
  map_add' first second := by
    apply Subtype.ext
    funext argument
    exact map_add (latticeCocycleGeneratorRetraction representation)
      ((first radicalLatticeFirst).val argument, (first radicalLatticeSecond).val argument)
      ((second radicalLatticeFirst).val argument, (second radicalLatticeSecond).val argument)
  map_smul' scalar cycle := by
    apply Subtype.ext
    funext argument
    exact map_smul (latticeCocycleGeneratorRetraction representation) scalar
      ((cycle radicalLatticeFirst).val argument, (cycle radicalLatticeSecond).val argument)

theorem cuspidalLatticeCocycleFamily_apply (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation)) (argument : BinaryAdelicGL) :
    (cuspidalLatticeCocycleFamily cusp representation cycle).val argument =
      cuspidalTensorCocycleEvaluation cusp representation argument cycle :=
  latticeCocycleGeneratorRetraction_apply representation (cuspidalTensorCocycleEvaluation cusp representation argument cycle)

def oneCocycleEvaluation {G : Type} [Group G] (representation : Rep ℂ G) (element : G) :
    groupCohomology.cocycles₁ representation →ₗ[ℂ] representation where
  toFun cycle := cycle element
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cuspidalLatticeCocycleFromFamily (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice) :
    cuspidalTensorValues cusp (groupCohomology.cocycles₁ representation) →ₗ[ℂ]
      groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation) where
  toFun values := ⟨fun element => cuspidalTensorMap cusp (oneCocycleEvaluation representation element) values, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    apply Subtype.ext
    funext argument
    exact oneCocycle_mul representation (values.val argument) first second⟩
  map_add' first second := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_add (cuspidalTensorMap cusp (oneCocycleEvaluation representation element)) first second
  map_smul' scalar values := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_smul (cuspidalTensorMap cusp (oneCocycleEvaluation representation element)) scalar values

theorem cuspidalLatticeCocycleFromFamily_apply (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice)
    (values : cuspidalTensorValues cusp (groupCohomology.cocycles₁ representation)) (element : RadicalLattice)
    (argument : BinaryAdelicGL) :
    (cuspidalLatticeCocycleFromFamily cusp representation values element).val argument = values.val argument element := rfl

def cuspidalLatticeCocycleEquiv (cusp : CuspidalRepresentation) (representation : Rep ℂ RadicalLattice) :
    groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp representation) ≃ₗ[ℂ]
      cuspidalTensorValues cusp (groupCohomology.cocycles₁ representation) :=
  { cuspidalLatticeCocycleFamily cusp representation with
    invFun := cuspidalLatticeCocycleFromFamily cusp representation
    left_inv := by
      intro cycle
      apply groupCohomology.cocycles₁_ext
      intro element
      apply Subtype.ext
      funext argument
      exact congrArg (fun scalarCycle : groupCohomology.cocycles₁ representation => scalarCycle element)
        (cuspidalLatticeCocycleFamily_apply cusp representation cycle argument)
    right_inv := by
      intro values
      apply Subtype.ext
      funext argument
      calc
        _ = cuspidalTensorCocycleEvaluation cusp representation argument
            (cuspidalLatticeCocycleFromFamily cusp representation values) :=
          cuspidalLatticeCocycleFamily_apply cusp representation _ argument
        _ = values.val argument := by
          apply groupCohomology.cocycles₁_ext
          intro element
          rfl }

end TernaryPeriodPolynomials.SphericalDetection.Helpers
