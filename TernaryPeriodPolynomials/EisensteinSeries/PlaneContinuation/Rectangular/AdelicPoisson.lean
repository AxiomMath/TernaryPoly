module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.LinearLattices

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularAdelicPoisson

def coordinates {Ring : Type*} [CommRing Ring] : Rectangular Ring ≃ₗ[Ring] (Coordinate → Ring) where
  toFun matrix := fun coordinate => matrix coordinate.1 coordinate.2
  invFun vector := fun row column => vector (row, column)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteTransform (point : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (binary : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    FiniteRectangularFourier.Space ≃ₗ[FiniteAdeles] FiniteRectangularFourier.Space :=
  (coordinates.symm.trans (RectangularTransport.matrixEquiv point binary)).trans coordinates

def finiteTest (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) : Rectangular FiniteAdeles → ℂ :=
  fun matrix => FiniteRectangularFourier.boxTest (fun _ => scale) offset (coordinates matrix)

def pullback (realTest : SchwartzMap RealSpace ℂ) (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (binary : BinaryAdelicGL) : AdelicRectangularFourier.Space → ℂ :=
  AdelicRectangularFourier.tensor (AdelicSchwartzTheta.realPullback realTest point binary)
    (fun value => FiniteRectangularFourier.boxTest (fun _ => scale) offset
      (finiteTransform (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) point)
        (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) binary) value))

theorem pullback_rational (realTest : SchwartzMap RealSpace ℂ) (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) :
    pullback realTest scale offset point binary (UnitBoxPoisson.rationalPoint (coordinates matrix)) =
      RectangularTheta.matrixTerm (AdelicSchwartzTheta.tensorTest realTest (finiteTest scale offset)) point binary matrix := by
  rw [AdelicSchwartzTheta.matrixTerm_factorization]
  rfl

theorem pullback_poisson_hasSum (realTest : SchwartzMap RealSpace ℂ) (scale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (binary : BinaryAdelicGL) :
    HasSum (fun rational : Coordinate → ℚ =>
      AdelicRectangularFourier.transform (pullback realTest scale offset point binary) (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ, pullback realTest scale offset point binary (UnitBoxPoisson.rationalPoint rational)) :=
  FiniteLinearLattices.pullback_poisson_hasSum (AdelicSchwartzTheta.realPullback realTest point binary)
    (finiteTransform (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) point)
      (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) binary)) scale offset

theorem fullTheta_eq_coordinate_sum (realTest : SchwartzMap RealSpace ℂ) (scale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (binary : BinaryAdelicGL) :
    RectangularTheta.fullTheta (AdelicSchwartzTheta.tensorTest realTest (finiteTest scale offset)) point binary =
      ∑' rational : Coordinate → ℚ, pullback realTest scale offset point binary (UnitBoxPoisson.rationalPoint rational) := by
  have equality := (coordinates (Ring := ℚ)).toEquiv.tsum_eq
    (fun rational => pullback realTest scale offset point binary (UnitBoxPoisson.rationalPoint rational))
  change (∑' matrix : Rectangular ℚ,
    pullback realTest scale offset point binary (UnitBoxPoisson.rationalPoint (coordinates matrix))) = _ at equality
  simpa only [pullback_rational, RectangularTheta.fullTheta] using equality

theorem poisson_hasSum (realTest : SchwartzMap RealSpace ℂ) (scale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (binary : BinaryAdelicGL) :
    HasSum (fun matrix : Rectangular ℚ =>
      AdelicRectangularFourier.transform (pullback realTest scale offset point binary)
        (UnitBoxPoisson.rationalPoint (coordinates matrix)))
      (RectangularTheta.fullTheta (AdelicSchwartzTheta.tensorTest realTest (finiteTest scale offset)) point binary) := by
  rw [fullTheta_eq_coordinate_sum]
  have reindexed := (coordinates (Ring := ℚ)).toEquiv.hasSum_iff.mpr
    (pullback_poisson_hasSum realTest scale offset point binary)
  exact reindexed

theorem poisson (realTest : SchwartzMap RealSpace ℂ) (scale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (binary : BinaryAdelicGL) :
    RectangularTheta.fullTheta (AdelicSchwartzTheta.tensorTest realTest (finiteTest scale offset)) point binary =
      ∑' matrix : Rectangular ℚ,
        AdelicRectangularFourier.transform (pullback realTest scale offset point binary)
          (UnitBoxPoisson.rationalPoint (coordinates matrix)) :=
  (poisson_hasSum realTest scale offset point binary).tsum_eq.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularAdelicPoisson
