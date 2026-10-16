module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Plane.EdgeCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Parabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.ActionFrames

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryPlaneEdge

/-- Adjoin a fixed exterior coordinate to a binary matrix. -/
def diagonalBlock {R : Type*} [Zero R] [One R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  ![![1,0,0],![0,M 0 0,M 0 1],![0,M 1 0,M 1 1]]

theorem diagonalBlock_mul {R : Type*} [CommRing R] (M N : Matrix (Fin 2) (Fin 2) R) :
    diagonalBlock (M*N) = diagonalBlock M * diagonalBlock N := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [diagonalBlock,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two]

theorem diagonalBlock_one {R : Type*} [CommRing R] :
    diagonalBlock (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalBlock]

/-- The actual block embedding of invertible binary matrices, over either integers or rationals. -/
def blockEmbed {R : Type*} [CommRing R] (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    Matrix.GeneralLinearGroup (Fin 3) R where
  val := diagonalBlock g.val
  inv := diagonalBlock g.inv
  val_inv := by rw [←diagonalBlock_mul,g.val_inv,diagonalBlock_one]
  inv_val := by rw [←diagonalBlock_mul,g.inv_val,diagonalBlock_one]

theorem blockEmbed_integral (g : RankTwoAugmentedFrames.IntegralGL) :
    OrdinaryFullAction.integral (blockEmbed g) = blockEmbed (BinaryModularSymbol.integral g) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OrdinaryFullAction.integral,BinaryModularSymbol.integral,blockEmbed,diagonalBlock]

theorem blockEmbed_val (g : BinaryModularSymbol.GL2) :
    (blockEmbed g).val = OrdinaryResidueParabolic.blockMatrix 1 0 g := rfl

/-- Literal action of the block embedding on the embedded binary vector. -/
theorem vectorAction_embed (g : BinaryModularSymbol.GL2) (x : Fin 2 → ℚ) :
    OrdinaryFullAction.vectorAction (blockEmbed g) (embed x) = embed (BinaryModularSymbol.vectorAction g x) := by
  change (diagonalBlock g.val).mulVec (embed x) = embed (g.val.mulVec x)
  ext i
  fin_cases i <;> simp [diagonalBlock,embed,Matrix.mulVec, dotProduct,Fin.sum_univ_three,Fin.sum_univ_two]

theorem vectorAction_exterior (g : BinaryModularSymbol.GL2) :
    OrdinaryFullAction.vectorAction (blockEmbed g) (![1,0,0] : Fin 3 → ℚ) = ![1,0,0] := by
  change (diagonalBlock g.val).mulVec ![1,0,0] = _
  ext i
  fin_cases i <;> simp [diagonalBlock,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

/-- The actual action on embedded rational lines is the binary projective action. -/
theorem lineAction_embedLine (g : BinaryModularSymbol.GL2) (L : BinaryModularSymbol.Line) :
    OrdinaryFullAction.lineAction (blockEmbed g) (embedLine L).val =
      (embedLine (BinaryModularSymbol.lineAction g L)).val := by
  apply Subtype.ext
  change (L.val.map embed).map (OrdinaryFullAction.vectorAction (blockEmbed g)).toLinearMap =
    (L.val.map (BinaryModularSymbol.vectorAction g).toLinearMap).map embed
  rw [←Submodule.map_comp,←Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact vectorAction_embed g x

/-- Block diagonals fix the actual exterior projective line. -/
theorem lineAction_exterior (g : BinaryModularSymbol.GL2) :
    OrdinaryFullAction.lineAction (blockEmbed g) exterior = exterior := by
  apply Subtype.ext
  change (Submodule.span ℚ {![1,0,0]}).map (OrdinaryFullAction.vectorAction (blockEmbed g)).toLinearMap = _
  rw [Submodule.map_span,Set.image_singleton]
  change Submodule.span ℚ {OrdinaryFullAction.vectorAction (blockEmbed g) ![1,0,0]} =
    Submodule.span ℚ {![1,0,0]}
  rw [vectorAction_exterior]

/-- Rational matrix transport sends every literal apartment to the apartment of its transported lines. -/
theorem cycleAction_apartment (g : OrdinaryFullAction.GL3) (L M N : OrdinaryIncidence.Line) :
    OrdinaryFullAction.cycleAction g (GoodApartmentCycles.apartmentCycle (fun _ => True) L M N) =
      GoodApartmentCycles.apartmentCycle (fun _ => True) (OrdinaryFullAction.lineAction g L)
        (OrdinaryFullAction.lineAction g M) (OrdinaryFullAction.lineAction g N) := by
  apply Subtype.ext
  exact GoodApartmentCycles.apartmentChainEquiv_apartment (fun _ => True)
    (OrdinaryFullAction.subspaceAction g) (OrdinaryFullAction.subspaceAction_finrank g)
    (fun _ => Iff.rfl) L M N

/-- The actual linear cone is equivariant for all rational block diagonals. -/
theorem binaryCone_equivariant (g : BinaryModularSymbol.GL2) (c : BinaryModularSymbol.St) :
    binaryCone (BinaryModularSymbol.action g c) = OrdinaryFullAction.cycleAction (blockEmbed g) (binaryCone c) := by
  have hc : c ∈ Submodule.span ℚ (Set.range (BinaryModularSymbol.symbol
      (RankTwoAugmentedFrames.augmentedLine 1 0))) := by
    rw [BinaryModularSymbol.span_symbols]
    trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨L,rfl⟩ := hc
    rw [BinaryModularSymbol.action_symbol,binaryCone_symbol,binaryCone_symbol,cycleAction_apartment,
      lineAction_exterior,lineAction_embedLine,lineAction_embedLine]
  | zero => simp only [map_zero]
  | add c d _ _ hc hd => simp only [map_add,hc,hd]
  | smul q c _ hc => simp only [map_smul,hc]

end TernaryPoly.OrdinaryPlaneEdge
