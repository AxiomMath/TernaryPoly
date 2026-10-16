module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Plane.EdgeBlocks
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Period

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryResidueSymbol
open OrdinaryPlaneEdge SinglePole SinglePoleCoordinate OrdinaryResidueParabolic

/-- The exterior line is the first line of the actual ordinary reference apartment. -/
theorem exterior_reference : exterior = OrdinaryApartmentSpanComparison.line
    (AugmentedFrameComplex.augmentedLine 1 0) := by
  apply Subtype.ext
  change Submodule.span ℚ {![1,0,0]} = Submodule.span ℚ
    {ModThreeGoodAction.rationalRepresentation 1 (AugmentedFrameComplex.template 0)}
  simp [AugmentedFrameComplex.template]
  apply congrArg (fun v : Fin 3 → ℚ => Submodule.span ℚ {v})
  ext i
  fin_cases i <;> simp

/-- The first binary coordinate line embeds as the second ternary coordinate line. -/
theorem embedLine_reference_zero : (embedLine (RankTwoAugmentedFrames.augmentedLine 1 0)).val =
    OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 1) := by
  apply Subtype.ext
  change (Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation 1
      (RankTwoAugmentedFrames.template 0))}).map embed =
    Submodule.span ℚ {ModThreeGoodAction.rationalRepresentation 1 (AugmentedFrameComplex.template 1)}
  simp [Submodule.map_span,Set.image_singleton,OrdinaryPlaneEdge.embed,RankTwoAugmentedFrames.template,
    AugmentedFrameComplex.template]
  apply congrArg (fun v : Fin 3 → ℚ => Submodule.span ℚ {v})
  ext i
  fin_cases i <;> simp

/-- The second binary coordinate line embeds as the third ternary coordinate line. -/
theorem embedLine_reference_one : (embedLine (RankTwoAugmentedFrames.augmentedLine 1 1)).val =
    OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine 1 2) := by
  apply Subtype.ext
  change (Submodule.span ℚ {(RankTwoAugmentedFrames.rationalRepresentation 1
      (RankTwoAugmentedFrames.template 1))}).map embed =
    Submodule.span ℚ {ModThreeGoodAction.rationalRepresentation 1 (AugmentedFrameComplex.template 2)}
  simp [Submodule.map_span,Set.image_singleton,OrdinaryPlaneEdge.embed,RankTwoAugmentedFrames.template,
    AugmentedFrameComplex.template]
  apply congrArg (fun v : Fin 3 → ℚ => Submodule.span ℚ {v})
  ext i
  fin_cases i <;> simp

/-- The reference symbol cones to the actual reference apartment with positive sign. -/
theorem binaryCone_reference : binaryCone BinaryModularSymbol.reference =
    OrdinaryApartmentPresentation.frameCycle 1 := by
  rw [BinaryModularSymbol.reference,binaryCone_symbol,OrdinaryApartmentPresentation.frameCycle_apartment,
    exterior_reference,embedLine_reference_zero,embedLine_reference_one]

/-- The parabolic coefficient law is literally the binary modular-symbol coefficient representation. -/
theorem coefficient_action (d : ℕ) (g : BinaryModularSymbol.GL2) (q : BinaryV d) :
    g.val.det⁻¹ • homogeneousBinarySubstitute d (g⁻¹).val q =
      BinaryModularSymbolCoefficients.homogeneousAction d (-1) g q := by
  apply Subtype.ext
  change g.val.det⁻¹ • binarySubstitute (g⁻¹).val q.val =
    g.val.det ^ (-1 : ℤ) • BinaryModularSymbolCoefficients.substitute (g⁻¹).val q.val
  rw [zpow_neg_one]
  rfl

/-- Restrict an actual ternary residue functional along the literal binary cone and coordinate residue. -/
def restriction (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    BinaryModularSymbol.St →ₗ[ℚ] BinaryV (n+1) :=
  (zeroCoordinate n).comp (F.val.comp binaryCone)

/-- Full integral equivariance follows from actual coning and the proved block-parabolic residue law. -/
theorem restriction_equivariant (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (g : RankTwoAugmentedFrames.IntegralGL) (c : BinaryModularSymbol.St) :
    restriction n F (BinaryModularSymbol.action (BinaryModularSymbol.integral g) c) =
      BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1) (BinaryModularSymbol.integral g)
        (restriction n F c) := by
  change zeroCoordinate n (F.val (binaryCone (BinaryModularSymbol.action (BinaryModularSymbol.integral g) c))) = _
  rw [binaryCone_equivariant,←blockEmbed_integral,F.property (blockEmbed g)]
  change coordinateTuple n (residueAction n (-1) (OrdinaryFullAction.integral (blockEmbed g))
    (F.val (binaryCone c))) 0 = _
  rw [blockEmbed_integral,coordinateTuple_action n (blockEmbed (BinaryModularSymbol.integral g))
    1 0 (BinaryModularSymbol.integral g) (blockEmbed_val _),coefficient_action]
  rfl

/-- A literal linear map between actual full ternary residue Hom and actual binary modular-symbol Hom. -/
def toBinaryHom (n : ℕ) : OrdinaryFullCoefficient.ResidueHom n (-1) →ₗ[ℚ]
    BinaryModularSymbol.PeriodHom (n+1) where
  toFun F := ⟨restriction n F,restriction_equivariant n F⟩
  map_add' F G := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    change zeroCoordinate n ((F.val+G.val) (binaryCone c)) = _
    simp only [LinearMap.add_apply,map_add]
    rfl
  map_smul' a F := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    change zeroCoordinate n ((a • F.val) (binaryCone c)) = _
    simp only [LinearMap.smul_apply,map_smul]
    rfl

/-- Reference evaluation of the actual restricted Hom is exactly the original literal binary period coordinate. -/
theorem evaluation_toBinaryHom (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    BinaryModularSymbol.evaluation (BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1))
      (toBinaryHom n F) = OrdinaryFullCoefficient.coordinatePeriod n 0 F := by
  change zeroCoordinate n (F.val (binaryCone BinaryModularSymbol.reference)) = _
  rw [binaryCone_reference]
  rfl

/-- The actual restriction is faithful because the literal period coordinate already determines the full residue functional. -/
theorem toBinaryHom_injective (n : ℕ) : Function.Injective (toBinaryHom n) := by
  intro F G h
  apply (OrdinaryResiduePeriod.periodEquiv n).injective
  apply Subtype.ext
  have he := congrArg (BinaryModularSymbol.evaluation
    (BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1))) h
  simpa only [evaluation_toBinaryHom,OrdinaryResiduePeriod.periodEquiv_val] using he

end TernaryPoly.OrdinaryResidueSymbol
