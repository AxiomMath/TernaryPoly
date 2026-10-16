module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

noncomputable section
namespace TernaryPoly.OrbitMinorCertificate

abbrev Code := Fin 16

/-- Hexadecimal encoding of coefficients in ascending powers of the root. -/
def decode {R : Type*} [CommRing R] (t : R) : Code → R :=
  ![0, 1, t, 1 + t, t^2, 1 + t^2, t + t^2, 1 + t + t^2, t^3, 1 + t^3, t + t^3, 1 + t + t^3, t^2 + t^3, 1 + t^2 + t^3, t + t^2 + t^3, 1 + t + t^2 + t^3]

/-- Addition on four binary coefficients. -/
def addCode (i j : Code) : Code := i ^^^ j

def mulRow0 : Code → Code := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def mulRow1 : Code → Code := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def mulRow2 : Code → Code := ![0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]
def mulRow3 : Code → Code := ![0, 3, 6, 5, 12, 15, 10, 9, 11, 8, 13, 14, 7, 4, 1, 2]
def mulRow4 : Code → Code := ![0, 4, 8, 12, 3, 7, 11, 15, 6, 2, 14, 10, 5, 1, 13, 9]
def mulRow5 : Code → Code := ![0, 5, 10, 15, 7, 2, 13, 8, 14, 11, 4, 1, 9, 12, 3, 6]
def mulRow6 : Code → Code := ![0, 6, 12, 10, 11, 13, 7, 1, 5, 3, 9, 15, 14, 8, 2, 4]
def mulRow7 : Code → Code := ![0, 7, 14, 9, 15, 8, 1, 6, 13, 10, 3, 4, 2, 5, 12, 11]
def mulRow8 : Code → Code := ![0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1]
def mulRow9 : Code → Code := ![0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14]
def mulRow10 : Code → Code := ![0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12]
def mulRow11 : Code → Code := ![0, 11, 5, 14, 10, 1, 15, 4, 7, 12, 2, 9, 13, 6, 8, 3]
def mulRow12 : Code → Code := ![0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8]
def mulRow13 : Code → Code := ![0, 13, 9, 4, 1, 12, 8, 5, 2, 15, 11, 6, 3, 14, 10, 7]
def mulRow14 : Code → Code := ![0, 14, 15, 1, 13, 3, 2, 12, 9, 7, 6, 8, 4, 10, 11, 5]
def mulRow15 : Code → Code := ![0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10]

/-- Literal multiplication table modulo T^4+T+1. -/
def mulCode : Code → Code → Code :=
  ![mulRow0, mulRow1, mulRow2, mulRow3, mulRow4, mulRow5, mulRow6, mulRow7, mulRow8, mulRow9, mulRow10, mulRow11, mulRow12, mulRow13, mulRow14, mulRow15]

def matrixRow0 : Fin 32 → Code := ![5, 2, 6, 5, 13, 12, 7, 13, 11, 9, 2, 9, 5, 8, 8, 0, 10, 1, 10, 12, 9, 15, 11, 10, 14, 1, 4, 8, 10, 11, 14, 8]
def matrixRow1 : Fin 32 → Code := ![4, 7, 9, 0, 11, 1, 3, 0, 12, 2, 2, 0, 5, 1, 4, 1, 11, 14, 10, 9, 15, 8, 5, 6, 2, 14, 12, 14, 3, 0, 6, 1]
def matrixRow2 : Fin 32 → Code := ![10, 13, 1, 12, 3, 5, 7, 2, 8, 4, 12, 4, 3, 0, 9, 3, 14, 10, 5, 4, 12, 11, 4, 2, 14, 3, 5, 7, 5, 3, 11, 12]
def matrixRow3 : Fin 32 → Code := ![11, 14, 13, 5, 4, 12, 5, 8, 14, 0, 12, 14, 3, 8, 11, 8, 15, 5, 5, 0, 11, 13, 10, 15, 12, 2, 14, 2, 13, 8, 6, 0]
def matrixRow4 : Fin 32 → Code := ![7, 8, 11, 12, 15, 6, 10, 5, 11, 12, 7, 12, 5, 10, 8, 13, 15, 7, 9, 10, 9, 9, 15, 6, 14, 1, 4, 13, 8, 1, 3, 4]
def matrixRow5 : Fin 32 → Code := ![9, 11, 14, 14, 2, 10, 13, 13, 8, 3, 13, 5, 5, 11, 14, 11, 3, 14, 7, 12, 12, 15, 9, 5, 8, 8, 0, 8, 9, 4, 8, 15]
def matrixRow6 : Fin 32 → Code := ![15, 2, 8, 7, 6, 10, 14, 8, 8, 7, 15, 7, 3, 5, 9, 10, 13, 13, 1, 3, 12, 12, 6, 10, 14, 3, 5, 4, 0, 12, 2, 4]
def matrixRow7 : Fin 32 → Code := ![6, 10, 14, 1, 13, 4, 3, 5, 10, 13, 3, 9, 3, 14, 13, 14, 7, 9, 8, 5, 8, 10, 10, 2, 10, 10, 0, 10, 11, 2, 10, 12]
def matrixRow8 : Fin 32 → Code := ![12, 11, 1, 10, 2, 4, 7, 3, 15, 5, 10, 5, 2, 0, 14, 2, 9, 12, 4, 5, 10, 13, 5, 3, 9, 2, 4, 7, 4, 2, 13, 10]
def matrixRow9 : Fin 32 → Code := ![13, 9, 11, 4, 5, 10, 4, 15, 9, 0, 10, 9, 2, 15, 13, 15, 8, 4, 4, 0, 13, 11, 12, 8, 10, 3, 9, 3, 11, 15, 6, 0]
def matrixRow10 : Fin 32 → Code := ![4, 3, 6, 4, 11, 10, 7, 11, 13, 14, 3, 14, 4, 15, 15, 0, 12, 1, 12, 10, 14, 8, 13, 12, 9, 1, 5, 15, 12, 13, 9, 15]
def matrixRow11 : Fin 32 → Code := ![5, 7, 14, 0, 13, 1, 2, 0, 10, 3, 3, 0, 4, 1, 5, 1, 13, 9, 12, 14, 8, 15, 4, 6, 3, 9, 10, 9, 2, 0, 6, 1]
def matrixRow12 : Fin 32 → Code := ![7, 15, 13, 10, 8, 6, 12, 4, 13, 10, 7, 10, 4, 12, 15, 11, 8, 7, 14, 12, 14, 14, 8, 6, 9, 1, 5, 11, 15, 1, 2, 5]
def matrixRow13 : Fin 32 → Code := ![14, 13, 9, 9, 3, 12, 11, 11, 15, 2, 11, 4, 4, 13, 9, 13, 2, 9, 7, 10, 10, 8, 14, 4, 15, 15, 0, 15, 14, 5, 15, 8]
def matrixRow14 : Fin 32 → Code := ![8, 3, 15, 7, 6, 12, 9, 15, 15, 7, 8, 7, 2, 4, 14, 12, 11, 11, 1, 2, 10, 10, 6, 12, 9, 2, 4, 5, 0, 10, 3, 5]
def matrixRow15 : Fin 32 → Code := ![6, 12, 9, 1, 11, 5, 2, 4, 12, 11, 2, 14, 2, 9, 11, 9, 7, 14, 15, 4, 15, 12, 12, 3, 12, 12, 0, 12, 13, 3, 12, 10]
def matrixRow16 : Fin 32 → Code := ![8, 14, 1, 15, 5, 2, 6, 4, 12, 3, 15, 3, 5, 0, 13, 5, 11, 8, 2, 3, 15, 9, 3, 4, 11, 5, 2, 6, 2, 5, 9, 15]
def matrixRow17 : Fin 32 → Code := ![9, 11, 14, 2, 3, 15, 2, 12, 11, 0, 15, 11, 5, 12, 9, 12, 10, 2, 2, 0, 9, 14, 8, 10, 15, 4, 11, 4, 14, 12, 7, 0]
def matrixRow18 : Fin 32 → Code := ![2, 4, 7, 2, 14, 15, 6, 14, 9, 13, 4, 13, 2, 12, 12, 0, 8, 1, 8, 15, 13, 10, 9, 8, 11, 1, 3, 12, 8, 9, 11, 12]
def matrixRow19 : Fin 32 → Code := ![3, 6, 13, 0, 9, 1, 5, 0, 15, 4, 4, 0, 2, 1, 3, 1, 9, 11, 8, 13, 10, 12, 2, 7, 4, 11, 15, 11, 5, 0, 7, 1]
def matrixRow20 : Fin 32 → Code := ![3, 5, 7, 3, 9, 8, 6, 9, 14, 11, 5, 11, 3, 10, 10, 0, 15, 1, 15, 8, 11, 12, 14, 15, 13, 1, 2, 10, 15, 14, 13, 10]
def matrixRow21 : Fin 32 → Code := ![2, 6, 11, 0, 14, 1, 4, 0, 8, 5, 5, 0, 3, 1, 2, 1, 14, 13, 15, 11, 12, 10, 3, 7, 5, 13, 8, 13, 4, 0, 7, 1]
def matrixRow22 : Fin 32 → Code := ![15, 9, 1, 8, 4, 3, 6, 5, 10, 2, 8, 2, 4, 0, 11, 4, 13, 15, 3, 2, 8, 14, 2, 5, 13, 4, 3, 6, 3, 4, 14, 8]
def matrixRow23 : Fin 32 → Code := ![14, 13, 9, 3, 2, 8, 3, 10, 13, 0, 8, 13, 4, 10, 14, 10, 12, 3, 3, 0, 14, 9, 15, 12, 8, 5, 13, 5, 9, 10, 7, 0]
def matrixRow24 : Fin 32 → Code := ![1, 5, 15, 10, 4, 7, 9, 14, 8, 2, 10, 2, 5, 4, 0, 2, 3, 10, 8, 3, 12, 5, 13, 14, 6, 11, 5, 9, 6, 2, 2, 10]
def matrixRow25 : Fin 32 → Code := ![15, 6, 10, 7, 9, 11, 14, 15, 11, 2, 0, 1, 5, 12, 9, 12, 15, 10, 6, 11, 9, 3, 2, 6, 15, 4, 11, 4, 14, 12, 7, 0]
def matrixRow26 : Fin 32 → Code := ![1, 4, 8, 12, 5, 7, 14, 9, 15, 3, 12, 3, 4, 5, 0, 3, 2, 12, 15, 2, 10, 4, 11, 9, 6, 13, 4, 14, 6, 3, 3, 12]
def matrixRow27 : Fin 32 → Code := ![8, 6, 12, 7, 14, 13, 9, 8, 13, 3, 0, 1, 4, 10, 14, 10, 8, 12, 6, 13, 14, 2, 3, 6, 8, 5, 13, 5, 9, 10, 7, 0]
def matrixRow28 : Fin 32 → Code := ![4, 12, 5, 4, 7, 9, 2, 7, 10, 6, 12, 6, 3, 7, 0, 12, 7, 8, 14, 3, 8, 4, 11, 5, 7, 14, 3, 8, 2, 10, 12, 7]
def matrixRow29 : Fin 32 → Code := ![13, 4, 3, 4, 12, 7, 15, 7, 8, 10, 0, 6, 3, 1, 2, 1, 13, 1, 7, 6, 12, 2, 10, 9, 5, 13, 8, 13, 4, 0, 7, 1]
def matrixRow30 : Fin 32 → Code := ![5, 10, 4, 5, 7, 14, 3, 7, 12, 6, 10, 6, 2, 7, 0, 10, 7, 15, 9, 2, 15, 5, 13, 4, 7, 9, 2, 15, 3, 12, 10, 7]
def matrixRow31 : Fin 32 → Code := ![11, 5, 2, 5, 10, 7, 8, 7, 15, 12, 0, 6, 2, 1, 3, 1, 11, 1, 7, 6, 10, 3, 12, 14, 4, 11, 15, 11, 5, 0, 7, 1]

/-- The paper matrix, in its exact selected-row and source-column order. -/
def matrixCode : Matrix (Fin 32) (Fin 32) Code :=
  ![matrixRow0, matrixRow1, matrixRow2, matrixRow3, matrixRow4, matrixRow5, matrixRow6, matrixRow7, matrixRow8, matrixRow9, matrixRow10, matrixRow11, matrixRow12, matrixRow13, matrixRow14, matrixRow15, matrixRow16, matrixRow17, matrixRow18, matrixRow19, matrixRow20, matrixRow21, matrixRow22, matrixRow23, matrixRow24, matrixRow25, matrixRow26, matrixRow27, matrixRow28, matrixRow29, matrixRow30, matrixRow31]

def inverseColumn0 : Fin 32 → Code := ![10, 15, 2, 13, 15, 7, 6, 1, 11, 10, 15, 13, 13, 4, 3, 1, 9, 4, 1, 14, 10, 11, 2, 7, 14, 10, 0, 15, 7, 10, 14, 3]
def inverseColumn1 : Fin 32 → Code := ![7, 13, 6, 8, 12, 14, 6, 2, 0, 12, 1, 10, 12, 10, 14, 5, 0, 8, 7, 6, 4, 0, 8, 10, 0, 14, 7, 15, 12, 7, 2, 3]
def inverseColumn2 : Fin 32 → Code := ![2, 13, 15, 2, 11, 6, 1, 7, 13, 10, 6, 15, 8, 2, 15, 1, 7, 8, 9, 12, 15, 14, 3, 6, 9, 14, 2, 14, 8, 9, 5, 10]
def inverseColumn3 : Fin 32 → Code := ![5, 6, 11, 7, 11, 15, 8, 4, 4, 11, 4, 6, 13, 3, 3, 14, 5, 7, 10, 4, 12, 0, 7, 3, 1, 1, 11, 14, 1, 12, 2, 10]
def inverseColumn4 : Fin 32 → Code := ![10, 12, 6, 10, 1, 13, 5, 8, 7, 7, 4, 2, 15, 0, 0, 1, 4, 6, 8, 9, 2, 7, 11, 13, 5, 9, 9, 6, 14, 0, 10, 7]
def inverseColumn5 : Fin 32 → Code := ![8, 11, 2, 15, 11, 4, 0, 11, 10, 10, 0, 3, 11, 5, 14, 7, 10, 9, 11, 1, 15, 4, 0, 15, 3, 15, 8, 6, 12, 2, 4, 7]
def inverseColumn6 : Fin 32 → Code := ![12, 10, 13, 7, 10, 11, 4, 15, 1, 1, 15, 9, 12, 14, 6, 1, 15, 6, 2, 5, 2, 13, 3, 11, 4, 5, 10, 8, 7, 0, 6, 13]
def inverseColumn7 : Fin 32 → Code := ![13, 14, 9, 2, 0, 2, 2, 12, 9, 9, 9, 10, 10, 11, 2, 8, 0, 10, 4, 13, 0, 14, 14, 12, 13, 12, 9, 8, 0, 7, 7, 13]
def inverseColumn8 : Fin 32 → Code := ![3, 11, 8, 3, 13, 6, 1, 7, 11, 12, 6, 8, 15, 3, 8, 1, 7, 15, 14, 10, 8, 9, 2, 6, 14, 9, 3, 9, 15, 14, 4, 12]
def inverseColumn9 : Fin 32 → Code := ![4, 6, 13, 7, 13, 8, 15, 5, 5, 13, 5, 6, 11, 2, 2, 9, 4, 7, 12, 5, 10, 0, 7, 2, 1, 1, 13, 9, 1, 10, 3, 12]
def inverseColumn10 : Fin 32 → Code := ![12, 8, 3, 11, 8, 7, 6, 1, 13, 12, 8, 11, 11, 5, 2, 1, 14, 5, 1, 9, 12, 13, 3, 7, 9, 12, 0, 8, 7, 12, 9, 2]
def inverseColumn11 : Fin 32 → Code := ![7, 11, 6, 15, 10, 9, 6, 3, 0, 10, 1, 12, 10, 12, 9, 4, 0, 15, 7, 6, 5, 0, 15, 12, 0, 9, 7, 8, 10, 7, 3, 2]
def inverseColumn12 : Fin 32 → Code := ![12, 10, 6, 12, 1, 11, 4, 15, 7, 7, 5, 3, 8, 0, 0, 1, 5, 6, 15, 14, 3, 7, 13, 11, 4, 14, 14, 6, 9, 0, 12, 7]
def inverseColumn13 : Fin 32 → Code := ![15, 13, 3, 8, 13, 5, 0, 13, 12, 12, 0, 2, 13, 4, 9, 7, 12, 14, 13, 1, 8, 5, 0, 8, 2, 8, 15, 6, 10, 3, 5, 7]
def inverseColumn14 : Fin 32 → Code := ![10, 12, 11, 7, 12, 13, 5, 8, 1, 1, 8, 14, 10, 9, 6, 1, 8, 6, 3, 4, 3, 11, 2, 13, 5, 4, 12, 15, 7, 0, 6, 11]
def inverseColumn15 : Fin 32 → Code := ![11, 9, 14, 3, 0, 3, 3, 10, 14, 14, 14, 12, 12, 13, 3, 15, 0, 12, 5, 11, 0, 9, 9, 10, 11, 10, 14, 15, 0, 7, 7, 11]
def inverseColumn16 : Fin 32 → Code := ![14, 5, 3, 11, 1, 7, 11, 6, 8, 14, 10, 6, 2, 1, 4, 8, 12, 10, 11, 8, 14, 6, 3, 4, 11, 3, 11, 15, 10, 9, 1, 3]
def inverseColumn17 : Fin 32 → Code := ![9, 15, 3, 11, 9, 7, 1, 6, 9, 3, 9, 14, 7, 2, 8, 15, 2, 15, 9, 8, 15, 8, 14, 0, 10, 4, 3, 15, 1, 13, 6, 3]
def inverseColumn18 : Fin 32 → Code := ![13, 9, 9, 4, 7, 6, 5, 1, 8, 9, 9, 11, 8, 6, 12, 15, 9, 2, 1, 13, 14, 1, 13, 10, 8, 7, 0, 9, 14, 2, 13, 12]
def inverseColumn19 : Fin 32 → Code := ![7, 11, 9, 4, 10, 6, 7, 1, 15, 0, 1, 12, 10, 15, 9, 11, 15, 7, 3, 13, 11, 13, 12, 0, 4, 3, 7, 9, 3, 8, 9, 12]
def inverseColumn20 : Fin 32 → Code := ![11, 14, 14, 5, 7, 6, 4, 1, 15, 14, 14, 13, 15, 6, 10, 8, 14, 3, 1, 11, 9, 1, 11, 12, 15, 7, 0, 14, 9, 3, 11, 10]
def inverseColumn21 : Fin 32 → Code := ![7, 13, 14, 5, 12, 6, 7, 1, 8, 0, 1, 10, 12, 8, 14, 13, 8, 7, 2, 11, 13, 11, 10, 0, 5, 2, 7, 14, 2, 15, 14, 10]
def inverseColumn22 : Fin 32 → Code := ![9, 4, 2, 13, 1, 7, 13, 6, 15, 9, 12, 6, 3, 1, 5, 15, 10, 12, 13, 15, 9, 6, 2, 5, 13, 2, 13, 8, 12, 14, 1, 2]
def inverseColumn23 : Fin 32 → Code := ![14, 8, 2, 13, 14, 7, 1, 6, 14, 2, 14, 9, 7, 3, 15, 8, 3, 8, 14, 15, 8, 15, 9, 0, 12, 5, 2, 8, 1, 11, 6, 2]
def inverseColumn24 : Fin 32 → Code := ![11, 15, 5, 8, 9, 0, 2, 13, 11, 11, 3, 7, 8, 2, 3, 12, 14, 9, 15, 5, 6, 2, 5, 11, 8, 4, 12, 6, 8, 6, 11, 7]
def inverseColumn25 : Fin 32 → Code := ![2, 0, 5, 8, 8, 0, 13, 13, 12, 12, 10, 8, 1, 4, 6, 8, 6, 14, 9, 5, 5, 5, 8, 0, 10, 0, 3, 6, 4, 13, 15, 7]
def inverseColumn26 : Fin 32 → Code := ![13, 8, 4, 15, 14, 0, 3, 11, 13, 13, 2, 7, 15, 3, 2, 10, 9, 14, 8, 4, 6, 3, 4, 13, 15, 5, 10, 6, 15, 6, 13, 7]
def inverseColumn27 : Fin 32 → Code := ![3, 0, 4, 15, 15, 0, 11, 11, 10, 10, 12, 15, 1, 5, 6, 15, 6, 9, 14, 4, 4, 4, 15, 0, 12, 0, 2, 6, 5, 11, 8, 7]
def inverseColumn28 : Fin 32 → Code := ![9, 12, 15, 4, 5, 0, 7, 11, 8, 8, 13, 8, 14, 13, 11, 6, 2, 10, 6, 15, 11, 9, 13, 14, 3, 2, 11, 8, 2, 5, 11, 13]
def inverseColumn29 : Fin 32 → Code := ![2, 0, 15, 4, 4, 0, 11, 11, 14, 14, 6, 4, 5, 10, 8, 4, 8, 12, 1, 15, 15, 15, 4, 0, 6, 0, 7, 8, 10, 11, 9, 13]
def inverseColumn30 : Fin 32 → Code := ![14, 10, 8, 5, 4, 0, 7, 13, 15, 15, 11, 15, 9, 11, 13, 6, 3, 12, 6, 8, 13, 14, 11, 9, 2, 3, 13, 15, 3, 4, 13, 11]
def inverseColumn31 : Fin 32 → Code := ![3, 0, 8, 5, 5, 0, 13, 13, 9, 9, 6, 5, 4, 12, 15, 5, 15, 10, 1, 8, 8, 8, 5, 0, 6, 0, 7, 15, 12, 13, 14, 11]

/-- Explicit inverse discovered by the supplied GF16 arithmetic and replayed below. -/
def inverseCode (i j : Fin 32) : Code :=
  (![inverseColumn0, inverseColumn1, inverseColumn2, inverseColumn3, inverseColumn4, inverseColumn5, inverseColumn6, inverseColumn7, inverseColumn8, inverseColumn9, inverseColumn10, inverseColumn11, inverseColumn12, inverseColumn13, inverseColumn14, inverseColumn15, inverseColumn16, inverseColumn17, inverseColumn18, inverseColumn19, inverseColumn20, inverseColumn21, inverseColumn22, inverseColumn23, inverseColumn24, inverseColumn25, inverseColumn26, inverseColumn27, inverseColumn28, inverseColumn29, inverseColumn30, inverseColumn31]) j i

def codeSum : List Code → Code
  | [] => 0
  | x :: xs => addCode x (codeSum xs)

def codeDot (i j : Fin 32) : Code :=
  codeSum (List.ofFn fun k : Fin 32 => mulCode (matrixCode i k) (inverseCode k j))

def matrix {R : Type*} [CommRing R] (t : R) : Matrix (Fin 32) (Fin 32) R :=
  fun i j => decode t (matrixCode i j)

def inverseMatrix {R : Type*} [CommRing R] (t : R) : Matrix (Fin 32) (Fin 32) R :=
  fun i j => decode t (inverseCode i j)

section Algebra
variable {R : Type*} [CommRing R] [CharP R 2] (t : R)

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : R) = ((n % 2 : ℕ) : R) :=
  CharP.cast_eq_mod R 2 n

omit [CharP R 2] in
private theorem decode_add_0_0 : decode t (addCode 0 0) = decode t 0+decode t 0 := by
  change (0) = (0)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_0_1 : decode t (addCode 0 1) = decode t 0+decode t 1 := by
  change (1) = (0)+(1)
  ring
omit [CharP R 2] in
private theorem decode_add_0_2 : decode t (addCode 0 2) = decode t 0+decode t 2 := by
  change (t) = (0)+(t)
  ring
omit [CharP R 2] in
private theorem decode_add_0_3 : decode t (addCode 0 3) = decode t 0+decode t 3 := by
  change (1 + t) = (0)+(1 + t)
  ring
omit [CharP R 2] in
private theorem decode_add_0_4 : decode t (addCode 0 4) = decode t 0+decode t 4 := by
  change (t^2) = (0)+(t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_0_5 : decode t (addCode 0 5) = decode t 0+decode t 5 := by
  change (1 + t^2) = (0)+(1 + t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_0_6 : decode t (addCode 0 6) = decode t 0+decode t 6 := by
  change (t + t^2) = (0)+(t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_0_7 : decode t (addCode 0 7) = decode t 0+decode t 7 := by
  change (1 + t + t^2) = (0)+(1 + t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_0_8 : decode t (addCode 0 8) = decode t 0+decode t 8 := by
  change (t^3) = (0)+(t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_0_9 : decode t (addCode 0 9) = decode t 0+decode t 9 := by
  change (1 + t^3) = (0)+(1 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_0_10 : decode t (addCode 0 10) = decode t 0+decode t 10 := by
  change (t + t^3) = (0)+(t + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_0_11 : decode t (addCode 0 11) = decode t 0+decode t 11 := by
  change (1 + t + t^3) = (0)+(1 + t + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_0_12 : decode t (addCode 0 12) = decode t 0+decode t 12 := by
  change (t^2 + t^3) = (0)+(t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_0_13 : decode t (addCode 0 13) = decode t 0+decode t 13 := by
  change (1 + t^2 + t^3) = (0)+(1 + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_0_14 : decode t (addCode 0 14) = decode t 0+decode t 14 := by
  change (t + t^2 + t^3) = (0)+(t + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_0_15 : decode t (addCode 0 15) = decode t 0+decode t 15 := by
  change (1 + t + t^2 + t^3) = (0)+(1 + t + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_1_0 : decode t (addCode 1 0) = decode t 1+decode t 0 := by
  change (1) = (1)+(0)
  ring
private theorem decode_add_1_1 : decode t (addCode 1 1) = decode t 1+decode t 1 := by
  change (0) = (1)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_1_2 : decode t (addCode 1 2) = decode t 1+decode t 2 := by
  change (1 + t) = (1)+(t)
  ring
private theorem decode_add_1_3 : decode t (addCode 1 3) = decode t 1+decode t 3 := by
  change (t) = (1)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_1_4 : decode t (addCode 1 4) = decode t 1+decode t 4 := by
  change (1 + t^2) = (1)+(t^2)
  ring
private theorem decode_add_1_5 : decode t (addCode 1 5) = decode t 1+decode t 5 := by
  change (t^2) = (1)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_1_6 : decode t (addCode 1 6) = decode t 1+decode t 6 := by
  change (1 + t + t^2) = (1)+(t + t^2)
  ring
private theorem decode_add_1_7 : decode t (addCode 1 7) = decode t 1+decode t 7 := by
  change (t + t^2) = (1)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_1_8 : decode t (addCode 1 8) = decode t 1+decode t 8 := by
  change (1 + t^3) = (1)+(t^3)
  ring
private theorem decode_add_1_9 : decode t (addCode 1 9) = decode t 1+decode t 9 := by
  change (t^3) = (1)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_1_10 : decode t (addCode 1 10) = decode t 1+decode t 10 := by
  change (1 + t + t^3) = (1)+(t + t^3)
  ring
private theorem decode_add_1_11 : decode t (addCode 1 11) = decode t 1+decode t 11 := by
  change (t + t^3) = (1)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_1_12 : decode t (addCode 1 12) = decode t 1+decode t 12 := by
  change (1 + t^2 + t^3) = (1)+(t^2 + t^3)
  ring
private theorem decode_add_1_13 : decode t (addCode 1 13) = decode t 1+decode t 13 := by
  change (t^2 + t^3) = (1)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_1_14 : decode t (addCode 1 14) = decode t 1+decode t 14 := by
  change (1 + t + t^2 + t^3) = (1)+(t + t^2 + t^3)
  ring
private theorem decode_add_1_15 : decode t (addCode 1 15) = decode t 1+decode t 15 := by
  change (t + t^2 + t^3) = (1)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_2_0 : decode t (addCode 2 0) = decode t 2+decode t 0 := by
  change (t) = (t)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_2_1 : decode t (addCode 2 1) = decode t 2+decode t 1 := by
  change (1 + t) = (t)+(1)
  ring
private theorem decode_add_2_2 : decode t (addCode 2 2) = decode t 2+decode t 2 := by
  change (0) = (t)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_2_3 : decode t (addCode 2 3) = decode t 2+decode t 3 := by
  change (1) = (t)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_2_4 : decode t (addCode 2 4) = decode t 2+decode t 4 := by
  change (t + t^2) = (t)+(t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_2_5 : decode t (addCode 2 5) = decode t 2+decode t 5 := by
  change (1 + t + t^2) = (t)+(1 + t^2)
  ring
private theorem decode_add_2_6 : decode t (addCode 2 6) = decode t 2+decode t 6 := by
  change (t^2) = (t)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_2_7 : decode t (addCode 2 7) = decode t 2+decode t 7 := by
  change (1 + t^2) = (t)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_2_8 : decode t (addCode 2 8) = decode t 2+decode t 8 := by
  change (t + t^3) = (t)+(t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_2_9 : decode t (addCode 2 9) = decode t 2+decode t 9 := by
  change (1 + t + t^3) = (t)+(1 + t^3)
  ring
private theorem decode_add_2_10 : decode t (addCode 2 10) = decode t 2+decode t 10 := by
  change (t^3) = (t)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_2_11 : decode t (addCode 2 11) = decode t 2+decode t 11 := by
  change (1 + t^3) = (t)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_2_12 : decode t (addCode 2 12) = decode t 2+decode t 12 := by
  change (t + t^2 + t^3) = (t)+(t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_2_13 : decode t (addCode 2 13) = decode t 2+decode t 13 := by
  change (1 + t + t^2 + t^3) = (t)+(1 + t^2 + t^3)
  ring
private theorem decode_add_2_14 : decode t (addCode 2 14) = decode t 2+decode t 14 := by
  change (t^2 + t^3) = (t)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_2_15 : decode t (addCode 2 15) = decode t 2+decode t 15 := by
  change (1 + t^2 + t^3) = (t)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_3_0 : decode t (addCode 3 0) = decode t 3+decode t 0 := by
  change (1 + t) = (1 + t)+(0)
  ring
private theorem decode_add_3_1 : decode t (addCode 3 1) = decode t 3+decode t 1 := by
  change (t) = (1 + t)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_2 : decode t (addCode 3 2) = decode t 3+decode t 2 := by
  change (1) = (1 + t)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_3 : decode t (addCode 3 3) = decode t 3+decode t 3 := by
  change (0) = (1 + t)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_3_4 : decode t (addCode 3 4) = decode t 3+decode t 4 := by
  change (1 + t + t^2) = (1 + t)+(t^2)
  ring
private theorem decode_add_3_5 : decode t (addCode 3 5) = decode t 3+decode t 5 := by
  change (t + t^2) = (1 + t)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_6 : decode t (addCode 3 6) = decode t 3+decode t 6 := by
  change (1 + t^2) = (1 + t)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_7 : decode t (addCode 3 7) = decode t 3+decode t 7 := by
  change (t^2) = (1 + t)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_3_8 : decode t (addCode 3 8) = decode t 3+decode t 8 := by
  change (1 + t + t^3) = (1 + t)+(t^3)
  ring
private theorem decode_add_3_9 : decode t (addCode 3 9) = decode t 3+decode t 9 := by
  change (t + t^3) = (1 + t)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_10 : decode t (addCode 3 10) = decode t 3+decode t 10 := by
  change (1 + t^3) = (1 + t)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_11 : decode t (addCode 3 11) = decode t 3+decode t 11 := by
  change (t^3) = (1 + t)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_3_12 : decode t (addCode 3 12) = decode t 3+decode t 12 := by
  change (1 + t + t^2 + t^3) = (1 + t)+(t^2 + t^3)
  ring
private theorem decode_add_3_13 : decode t (addCode 3 13) = decode t 3+decode t 13 := by
  change (t + t^2 + t^3) = (1 + t)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_14 : decode t (addCode 3 14) = decode t 3+decode t 14 := by
  change (1 + t^2 + t^3) = (1 + t)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_3_15 : decode t (addCode 3 15) = decode t 3+decode t 15 := by
  change (t^2 + t^3) = (1 + t)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_4_0 : decode t (addCode 4 0) = decode t 4+decode t 0 := by
  change (t^2) = (t^2)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_4_1 : decode t (addCode 4 1) = decode t 4+decode t 1 := by
  change (1 + t^2) = (t^2)+(1)
  ring
omit [CharP R 2] in
private theorem decode_add_4_2 : decode t (addCode 4 2) = decode t 4+decode t 2 := by
  change (t + t^2) = (t^2)+(t)
  ring
omit [CharP R 2] in
private theorem decode_add_4_3 : decode t (addCode 4 3) = decode t 4+decode t 3 := by
  change (1 + t + t^2) = (t^2)+(1 + t)
  ring
private theorem decode_add_4_4 : decode t (addCode 4 4) = decode t 4+decode t 4 := by
  change (0) = (t^2)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_4_5 : decode t (addCode 4 5) = decode t 4+decode t 5 := by
  change (1) = (t^2)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_4_6 : decode t (addCode 4 6) = decode t 4+decode t 6 := by
  change (t) = (t^2)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_4_7 : decode t (addCode 4 7) = decode t 4+decode t 7 := by
  change (1 + t) = (t^2)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_4_8 : decode t (addCode 4 8) = decode t 4+decode t 8 := by
  change (t^2 + t^3) = (t^2)+(t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_4_9 : decode t (addCode 4 9) = decode t 4+decode t 9 := by
  change (1 + t^2 + t^3) = (t^2)+(1 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_4_10 : decode t (addCode 4 10) = decode t 4+decode t 10 := by
  change (t + t^2 + t^3) = (t^2)+(t + t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_4_11 : decode t (addCode 4 11) = decode t 4+decode t 11 := by
  change (1 + t + t^2 + t^3) = (t^2)+(1 + t + t^3)
  ring
private theorem decode_add_4_12 : decode t (addCode 4 12) = decode t 4+decode t 12 := by
  change (t^3) = (t^2)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_4_13 : decode t (addCode 4 13) = decode t 4+decode t 13 := by
  change (1 + t^3) = (t^2)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_4_14 : decode t (addCode 4 14) = decode t 4+decode t 14 := by
  change (t + t^3) = (t^2)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_4_15 : decode t (addCode 4 15) = decode t 4+decode t 15 := by
  change (1 + t + t^3) = (t^2)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_5_0 : decode t (addCode 5 0) = decode t 5+decode t 0 := by
  change (1 + t^2) = (1 + t^2)+(0)
  ring
private theorem decode_add_5_1 : decode t (addCode 5 1) = decode t 5+decode t 1 := by
  change (t^2) = (1 + t^2)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_5_2 : decode t (addCode 5 2) = decode t 5+decode t 2 := by
  change (1 + t + t^2) = (1 + t^2)+(t)
  ring
private theorem decode_add_5_3 : decode t (addCode 5 3) = decode t 5+decode t 3 := by
  change (t + t^2) = (1 + t^2)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_4 : decode t (addCode 5 4) = decode t 5+decode t 4 := by
  change (1) = (1 + t^2)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_5 : decode t (addCode 5 5) = decode t 5+decode t 5 := by
  change (0) = (1 + t^2)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_6 : decode t (addCode 5 6) = decode t 5+decode t 6 := by
  change (1 + t) = (1 + t^2)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_7 : decode t (addCode 5 7) = decode t 5+decode t 7 := by
  change (t) = (1 + t^2)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_5_8 : decode t (addCode 5 8) = decode t 5+decode t 8 := by
  change (1 + t^2 + t^3) = (1 + t^2)+(t^3)
  ring
private theorem decode_add_5_9 : decode t (addCode 5 9) = decode t 5+decode t 9 := by
  change (t^2 + t^3) = (1 + t^2)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_5_10 : decode t (addCode 5 10) = decode t 5+decode t 10 := by
  change (1 + t + t^2 + t^3) = (1 + t^2)+(t + t^3)
  ring
private theorem decode_add_5_11 : decode t (addCode 5 11) = decode t 5+decode t 11 := by
  change (t + t^2 + t^3) = (1 + t^2)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_12 : decode t (addCode 5 12) = decode t 5+decode t 12 := by
  change (1 + t^3) = (1 + t^2)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_13 : decode t (addCode 5 13) = decode t 5+decode t 13 := by
  change (t^3) = (1 + t^2)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_14 : decode t (addCode 5 14) = decode t 5+decode t 14 := by
  change (1 + t + t^3) = (1 + t^2)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_5_15 : decode t (addCode 5 15) = decode t 5+decode t 15 := by
  change (t + t^3) = (1 + t^2)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_6_0 : decode t (addCode 6 0) = decode t 6+decode t 0 := by
  change (t + t^2) = (t + t^2)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_6_1 : decode t (addCode 6 1) = decode t 6+decode t 1 := by
  change (1 + t + t^2) = (t + t^2)+(1)
  ring
private theorem decode_add_6_2 : decode t (addCode 6 2) = decode t 6+decode t 2 := by
  change (t^2) = (t + t^2)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_3 : decode t (addCode 6 3) = decode t 6+decode t 3 := by
  change (1 + t^2) = (t + t^2)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_4 : decode t (addCode 6 4) = decode t 6+decode t 4 := by
  change (t) = (t + t^2)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_5 : decode t (addCode 6 5) = decode t 6+decode t 5 := by
  change (1 + t) = (t + t^2)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_6 : decode t (addCode 6 6) = decode t 6+decode t 6 := by
  change (0) = (t + t^2)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_7 : decode t (addCode 6 7) = decode t 6+decode t 7 := by
  change (1) = (t + t^2)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_6_8 : decode t (addCode 6 8) = decode t 6+decode t 8 := by
  change (t + t^2 + t^3) = (t + t^2)+(t^3)
  ring
omit [CharP R 2] in
private theorem decode_add_6_9 : decode t (addCode 6 9) = decode t 6+decode t 9 := by
  change (1 + t + t^2 + t^3) = (t + t^2)+(1 + t^3)
  ring
private theorem decode_add_6_10 : decode t (addCode 6 10) = decode t 6+decode t 10 := by
  change (t^2 + t^3) = (t + t^2)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_11 : decode t (addCode 6 11) = decode t 6+decode t 11 := by
  change (1 + t^2 + t^3) = (t + t^2)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_12 : decode t (addCode 6 12) = decode t 6+decode t 12 := by
  change (t + t^3) = (t + t^2)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_13 : decode t (addCode 6 13) = decode t 6+decode t 13 := by
  change (1 + t + t^3) = (t + t^2)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_14 : decode t (addCode 6 14) = decode t 6+decode t 14 := by
  change (t^3) = (t + t^2)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_6_15 : decode t (addCode 6 15) = decode t 6+decode t 15 := by
  change (1 + t^3) = (t + t^2)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_7_0 : decode t (addCode 7 0) = decode t 7+decode t 0 := by
  change (1 + t + t^2) = (1 + t + t^2)+(0)
  ring
private theorem decode_add_7_1 : decode t (addCode 7 1) = decode t 7+decode t 1 := by
  change (t + t^2) = (1 + t + t^2)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_2 : decode t (addCode 7 2) = decode t 7+decode t 2 := by
  change (1 + t^2) = (1 + t + t^2)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_3 : decode t (addCode 7 3) = decode t 7+decode t 3 := by
  change (t^2) = (1 + t + t^2)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_4 : decode t (addCode 7 4) = decode t 7+decode t 4 := by
  change (1 + t) = (1 + t + t^2)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_5 : decode t (addCode 7 5) = decode t 7+decode t 5 := by
  change (t) = (1 + t + t^2)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_6 : decode t (addCode 7 6) = decode t 7+decode t 6 := by
  change (1) = (1 + t + t^2)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_7 : decode t (addCode 7 7) = decode t 7+decode t 7 := by
  change (0) = (1 + t + t^2)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_7_8 : decode t (addCode 7 8) = decode t 7+decode t 8 := by
  change (1 + t + t^2 + t^3) = (1 + t + t^2)+(t^3)
  ring
private theorem decode_add_7_9 : decode t (addCode 7 9) = decode t 7+decode t 9 := by
  change (t + t^2 + t^3) = (1 + t + t^2)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_10 : decode t (addCode 7 10) = decode t 7+decode t 10 := by
  change (1 + t^2 + t^3) = (1 + t + t^2)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_11 : decode t (addCode 7 11) = decode t 7+decode t 11 := by
  change (t^2 + t^3) = (1 + t + t^2)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_12 : decode t (addCode 7 12) = decode t 7+decode t 12 := by
  change (1 + t + t^3) = (1 + t + t^2)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_13 : decode t (addCode 7 13) = decode t 7+decode t 13 := by
  change (t + t^3) = (1 + t + t^2)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_14 : decode t (addCode 7 14) = decode t 7+decode t 14 := by
  change (1 + t^3) = (1 + t + t^2)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_7_15 : decode t (addCode 7 15) = decode t 7+decode t 15 := by
  change (t^3) = (1 + t + t^2)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_8_0 : decode t (addCode 8 0) = decode t 8+decode t 0 := by
  change (t^3) = (t^3)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_8_1 : decode t (addCode 8 1) = decode t 8+decode t 1 := by
  change (1 + t^3) = (t^3)+(1)
  ring
omit [CharP R 2] in
private theorem decode_add_8_2 : decode t (addCode 8 2) = decode t 8+decode t 2 := by
  change (t + t^3) = (t^3)+(t)
  ring
omit [CharP R 2] in
private theorem decode_add_8_3 : decode t (addCode 8 3) = decode t 8+decode t 3 := by
  change (1 + t + t^3) = (t^3)+(1 + t)
  ring
omit [CharP R 2] in
private theorem decode_add_8_4 : decode t (addCode 8 4) = decode t 8+decode t 4 := by
  change (t^2 + t^3) = (t^3)+(t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_8_5 : decode t (addCode 8 5) = decode t 8+decode t 5 := by
  change (1 + t^2 + t^3) = (t^3)+(1 + t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_8_6 : decode t (addCode 8 6) = decode t 8+decode t 6 := by
  change (t + t^2 + t^3) = (t^3)+(t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_8_7 : decode t (addCode 8 7) = decode t 8+decode t 7 := by
  change (1 + t + t^2 + t^3) = (t^3)+(1 + t + t^2)
  ring
private theorem decode_add_8_8 : decode t (addCode 8 8) = decode t 8+decode t 8 := by
  change (0) = (t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_8_9 : decode t (addCode 8 9) = decode t 8+decode t 9 := by
  change (1) = (t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_8_10 : decode t (addCode 8 10) = decode t 8+decode t 10 := by
  change (t) = (t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_8_11 : decode t (addCode 8 11) = decode t 8+decode t 11 := by
  change (1 + t) = (t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_8_12 : decode t (addCode 8 12) = decode t 8+decode t 12 := by
  change (t^2) = (t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_8_13 : decode t (addCode 8 13) = decode t 8+decode t 13 := by
  change (1 + t^2) = (t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_8_14 : decode t (addCode 8 14) = decode t 8+decode t 14 := by
  change (t + t^2) = (t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_8_15 : decode t (addCode 8 15) = decode t 8+decode t 15 := by
  change (1 + t + t^2) = (t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_9_0 : decode t (addCode 9 0) = decode t 9+decode t 0 := by
  change (1 + t^3) = (1 + t^3)+(0)
  ring
private theorem decode_add_9_1 : decode t (addCode 9 1) = decode t 9+decode t 1 := by
  change (t^3) = (1 + t^3)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_9_2 : decode t (addCode 9 2) = decode t 9+decode t 2 := by
  change (1 + t + t^3) = (1 + t^3)+(t)
  ring
private theorem decode_add_9_3 : decode t (addCode 9 3) = decode t 9+decode t 3 := by
  change (t + t^3) = (1 + t^3)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_9_4 : decode t (addCode 9 4) = decode t 9+decode t 4 := by
  change (1 + t^2 + t^3) = (1 + t^3)+(t^2)
  ring
private theorem decode_add_9_5 : decode t (addCode 9 5) = decode t 9+decode t 5 := by
  change (t^2 + t^3) = (1 + t^3)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_9_6 : decode t (addCode 9 6) = decode t 9+decode t 6 := by
  change (1 + t + t^2 + t^3) = (1 + t^3)+(t + t^2)
  ring
private theorem decode_add_9_7 : decode t (addCode 9 7) = decode t 9+decode t 7 := by
  change (t + t^2 + t^3) = (1 + t^3)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_8 : decode t (addCode 9 8) = decode t 9+decode t 8 := by
  change (1) = (1 + t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_9 : decode t (addCode 9 9) = decode t 9+decode t 9 := by
  change (0) = (1 + t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_10 : decode t (addCode 9 10) = decode t 9+decode t 10 := by
  change (1 + t) = (1 + t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_11 : decode t (addCode 9 11) = decode t 9+decode t 11 := by
  change (t) = (1 + t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_12 : decode t (addCode 9 12) = decode t 9+decode t 12 := by
  change (1 + t^2) = (1 + t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_13 : decode t (addCode 9 13) = decode t 9+decode t 13 := by
  change (t^2) = (1 + t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_14 : decode t (addCode 9 14) = decode t 9+decode t 14 := by
  change (1 + t + t^2) = (1 + t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_9_15 : decode t (addCode 9 15) = decode t 9+decode t 15 := by
  change (t + t^2) = (1 + t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_10_0 : decode t (addCode 10 0) = decode t 10+decode t 0 := by
  change (t + t^3) = (t + t^3)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_10_1 : decode t (addCode 10 1) = decode t 10+decode t 1 := by
  change (1 + t + t^3) = (t + t^3)+(1)
  ring
private theorem decode_add_10_2 : decode t (addCode 10 2) = decode t 10+decode t 2 := by
  change (t^3) = (t + t^3)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_3 : decode t (addCode 10 3) = decode t 10+decode t 3 := by
  change (1 + t^3) = (t + t^3)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_10_4 : decode t (addCode 10 4) = decode t 10+decode t 4 := by
  change (t + t^2 + t^3) = (t + t^3)+(t^2)
  ring
omit [CharP R 2] in
private theorem decode_add_10_5 : decode t (addCode 10 5) = decode t 10+decode t 5 := by
  change (1 + t + t^2 + t^3) = (t + t^3)+(1 + t^2)
  ring
private theorem decode_add_10_6 : decode t (addCode 10 6) = decode t 10+decode t 6 := by
  change (t^2 + t^3) = (t + t^3)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_7 : decode t (addCode 10 7) = decode t 10+decode t 7 := by
  change (1 + t^2 + t^3) = (t + t^3)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_8 : decode t (addCode 10 8) = decode t 10+decode t 8 := by
  change (t) = (t + t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_9 : decode t (addCode 10 9) = decode t 10+decode t 9 := by
  change (1 + t) = (t + t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_10 : decode t (addCode 10 10) = decode t 10+decode t 10 := by
  change (0) = (t + t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_11 : decode t (addCode 10 11) = decode t 10+decode t 11 := by
  change (1) = (t + t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_12 : decode t (addCode 10 12) = decode t 10+decode t 12 := by
  change (t + t^2) = (t + t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_13 : decode t (addCode 10 13) = decode t 10+decode t 13 := by
  change (1 + t + t^2) = (t + t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_14 : decode t (addCode 10 14) = decode t 10+decode t 14 := by
  change (t^2) = (t + t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_10_15 : decode t (addCode 10 15) = decode t 10+decode t 15 := by
  change (1 + t^2) = (t + t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_11_0 : decode t (addCode 11 0) = decode t 11+decode t 0 := by
  change (1 + t + t^3) = (1 + t + t^3)+(0)
  ring
private theorem decode_add_11_1 : decode t (addCode 11 1) = decode t 11+decode t 1 := by
  change (t + t^3) = (1 + t + t^3)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_2 : decode t (addCode 11 2) = decode t 11+decode t 2 := by
  change (1 + t^3) = (1 + t + t^3)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_3 : decode t (addCode 11 3) = decode t 11+decode t 3 := by
  change (t^3) = (1 + t + t^3)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_11_4 : decode t (addCode 11 4) = decode t 11+decode t 4 := by
  change (1 + t + t^2 + t^3) = (1 + t + t^3)+(t^2)
  ring
private theorem decode_add_11_5 : decode t (addCode 11 5) = decode t 11+decode t 5 := by
  change (t + t^2 + t^3) = (1 + t + t^3)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_6 : decode t (addCode 11 6) = decode t 11+decode t 6 := by
  change (1 + t^2 + t^3) = (1 + t + t^3)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_7 : decode t (addCode 11 7) = decode t 11+decode t 7 := by
  change (t^2 + t^3) = (1 + t + t^3)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_8 : decode t (addCode 11 8) = decode t 11+decode t 8 := by
  change (1 + t) = (1 + t + t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_9 : decode t (addCode 11 9) = decode t 11+decode t 9 := by
  change (t) = (1 + t + t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_10 : decode t (addCode 11 10) = decode t 11+decode t 10 := by
  change (1) = (1 + t + t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_11 : decode t (addCode 11 11) = decode t 11+decode t 11 := by
  change (0) = (1 + t + t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_12 : decode t (addCode 11 12) = decode t 11+decode t 12 := by
  change (1 + t + t^2) = (1 + t + t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_13 : decode t (addCode 11 13) = decode t 11+decode t 13 := by
  change (t + t^2) = (1 + t + t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_14 : decode t (addCode 11 14) = decode t 11+decode t 14 := by
  change (1 + t^2) = (1 + t + t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_11_15 : decode t (addCode 11 15) = decode t 11+decode t 15 := by
  change (t^2) = (1 + t + t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_12_0 : decode t (addCode 12 0) = decode t 12+decode t 0 := by
  change (t^2 + t^3) = (t^2 + t^3)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_12_1 : decode t (addCode 12 1) = decode t 12+decode t 1 := by
  change (1 + t^2 + t^3) = (t^2 + t^3)+(1)
  ring
omit [CharP R 2] in
private theorem decode_add_12_2 : decode t (addCode 12 2) = decode t 12+decode t 2 := by
  change (t + t^2 + t^3) = (t^2 + t^3)+(t)
  ring
omit [CharP R 2] in
private theorem decode_add_12_3 : decode t (addCode 12 3) = decode t 12+decode t 3 := by
  change (1 + t + t^2 + t^3) = (t^2 + t^3)+(1 + t)
  ring
private theorem decode_add_12_4 : decode t (addCode 12 4) = decode t 12+decode t 4 := by
  change (t^3) = (t^2 + t^3)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_5 : decode t (addCode 12 5) = decode t 12+decode t 5 := by
  change (1 + t^3) = (t^2 + t^3)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_6 : decode t (addCode 12 6) = decode t 12+decode t 6 := by
  change (t + t^3) = (t^2 + t^3)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_7 : decode t (addCode 12 7) = decode t 12+decode t 7 := by
  change (1 + t + t^3) = (t^2 + t^3)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_8 : decode t (addCode 12 8) = decode t 12+decode t 8 := by
  change (t^2) = (t^2 + t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_9 : decode t (addCode 12 9) = decode t 12+decode t 9 := by
  change (1 + t^2) = (t^2 + t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_10 : decode t (addCode 12 10) = decode t 12+decode t 10 := by
  change (t + t^2) = (t^2 + t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_11 : decode t (addCode 12 11) = decode t 12+decode t 11 := by
  change (1 + t + t^2) = (t^2 + t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_12 : decode t (addCode 12 12) = decode t 12+decode t 12 := by
  change (0) = (t^2 + t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_13 : decode t (addCode 12 13) = decode t 12+decode t 13 := by
  change (1) = (t^2 + t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_14 : decode t (addCode 12 14) = decode t 12+decode t 14 := by
  change (t) = (t^2 + t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_12_15 : decode t (addCode 12 15) = decode t 12+decode t 15 := by
  change (1 + t) = (t^2 + t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_13_0 : decode t (addCode 13 0) = decode t 13+decode t 0 := by
  change (1 + t^2 + t^3) = (1 + t^2 + t^3)+(0)
  ring
private theorem decode_add_13_1 : decode t (addCode 13 1) = decode t 13+decode t 1 := by
  change (t^2 + t^3) = (1 + t^2 + t^3)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_13_2 : decode t (addCode 13 2) = decode t 13+decode t 2 := by
  change (1 + t + t^2 + t^3) = (1 + t^2 + t^3)+(t)
  ring
private theorem decode_add_13_3 : decode t (addCode 13 3) = decode t 13+decode t 3 := by
  change (t + t^2 + t^3) = (1 + t^2 + t^3)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_4 : decode t (addCode 13 4) = decode t 13+decode t 4 := by
  change (1 + t^3) = (1 + t^2 + t^3)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_5 : decode t (addCode 13 5) = decode t 13+decode t 5 := by
  change (t^3) = (1 + t^2 + t^3)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_6 : decode t (addCode 13 6) = decode t 13+decode t 6 := by
  change (1 + t + t^3) = (1 + t^2 + t^3)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_7 : decode t (addCode 13 7) = decode t 13+decode t 7 := by
  change (t + t^3) = (1 + t^2 + t^3)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_8 : decode t (addCode 13 8) = decode t 13+decode t 8 := by
  change (1 + t^2) = (1 + t^2 + t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_9 : decode t (addCode 13 9) = decode t 13+decode t 9 := by
  change (t^2) = (1 + t^2 + t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_10 : decode t (addCode 13 10) = decode t 13+decode t 10 := by
  change (1 + t + t^2) = (1 + t^2 + t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_11 : decode t (addCode 13 11) = decode t 13+decode t 11 := by
  change (t + t^2) = (1 + t^2 + t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_12 : decode t (addCode 13 12) = decode t 13+decode t 12 := by
  change (1) = (1 + t^2 + t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_13 : decode t (addCode 13 13) = decode t 13+decode t 13 := by
  change (0) = (1 + t^2 + t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_14 : decode t (addCode 13 14) = decode t 13+decode t 14 := by
  change (1 + t) = (1 + t^2 + t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_13_15 : decode t (addCode 13 15) = decode t 13+decode t 15 := by
  change (t) = (1 + t^2 + t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_14_0 : decode t (addCode 14 0) = decode t 14+decode t 0 := by
  change (t + t^2 + t^3) = (t + t^2 + t^3)+(0)
  ring
omit [CharP R 2] in
private theorem decode_add_14_1 : decode t (addCode 14 1) = decode t 14+decode t 1 := by
  change (1 + t + t^2 + t^3) = (t + t^2 + t^3)+(1)
  ring
private theorem decode_add_14_2 : decode t (addCode 14 2) = decode t 14+decode t 2 := by
  change (t^2 + t^3) = (t + t^2 + t^3)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_3 : decode t (addCode 14 3) = decode t 14+decode t 3 := by
  change (1 + t^2 + t^3) = (t + t^2 + t^3)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_4 : decode t (addCode 14 4) = decode t 14+decode t 4 := by
  change (t + t^3) = (t + t^2 + t^3)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_5 : decode t (addCode 14 5) = decode t 14+decode t 5 := by
  change (1 + t + t^3) = (t + t^2 + t^3)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_6 : decode t (addCode 14 6) = decode t 14+decode t 6 := by
  change (t^3) = (t + t^2 + t^3)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_7 : decode t (addCode 14 7) = decode t 14+decode t 7 := by
  change (1 + t^3) = (t + t^2 + t^3)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_8 : decode t (addCode 14 8) = decode t 14+decode t 8 := by
  change (t + t^2) = (t + t^2 + t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_9 : decode t (addCode 14 9) = decode t 14+decode t 9 := by
  change (1 + t + t^2) = (t + t^2 + t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_10 : decode t (addCode 14 10) = decode t 14+decode t 10 := by
  change (t^2) = (t + t^2 + t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_11 : decode t (addCode 14 11) = decode t 14+decode t 11 := by
  change (1 + t^2) = (t + t^2 + t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_12 : decode t (addCode 14 12) = decode t 14+decode t 12 := by
  change (t) = (t + t^2 + t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_13 : decode t (addCode 14 13) = decode t 14+decode t 13 := by
  change (1 + t) = (t + t^2 + t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_14 : decode t (addCode 14 14) = decode t 14+decode t 14 := by
  change (0) = (t + t^2 + t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_14_15 : decode t (addCode 14 15) = decode t 14+decode t 15 := by
  change (1) = (t + t^2 + t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_15_0 : decode t (addCode 15 0) = decode t 15+decode t 0 := by
  change (1 + t + t^2 + t^3) = (1 + t + t^2 + t^3)+(0)
  ring
private theorem decode_add_15_1 : decode t (addCode 15 1) = decode t 15+decode t 1 := by
  change (t + t^2 + t^3) = (1 + t + t^2 + t^3)+(1)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_2 : decode t (addCode 15 2) = decode t 15+decode t 2 := by
  change (1 + t^2 + t^3) = (1 + t + t^2 + t^3)+(t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_3 : decode t (addCode 15 3) = decode t 15+decode t 3 := by
  change (t^2 + t^3) = (1 + t + t^2 + t^3)+(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_4 : decode t (addCode 15 4) = decode t 15+decode t 4 := by
  change (1 + t + t^3) = (1 + t + t^2 + t^3)+(t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_5 : decode t (addCode 15 5) = decode t 15+decode t 5 := by
  change (t + t^3) = (1 + t + t^2 + t^3)+(1 + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_6 : decode t (addCode 15 6) = decode t 15+decode t 6 := by
  change (1 + t^3) = (1 + t + t^2 + t^3)+(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_7 : decode t (addCode 15 7) = decode t 15+decode t 7 := by
  change (t^3) = (1 + t + t^2 + t^3)+(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_8 : decode t (addCode 15 8) = decode t 15+decode t 8 := by
  change (1 + t + t^2) = (1 + t + t^2 + t^3)+(t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_9 : decode t (addCode 15 9) = decode t 15+decode t 9 := by
  change (t + t^2) = (1 + t + t^2 + t^3)+(1 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_10 : decode t (addCode 15 10) = decode t 15+decode t 10 := by
  change (1 + t^2) = (1 + t + t^2 + t^3)+(t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_11 : decode t (addCode 15 11) = decode t 15+decode t 11 := by
  change (t^2) = (1 + t + t^2 + t^3)+(1 + t + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_12 : decode t (addCode 15 12) = decode t 15+decode t 12 := by
  change (1 + t) = (1 + t + t^2 + t^3)+(t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_13 : decode t (addCode 15 13) = decode t 15+decode t 13 := by
  change (t) = (1 + t + t^2 + t^3)+(1 + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_14 : decode t (addCode 15 14) = decode t 15+decode t 14 := by
  change (1) = (1 + t + t^2 + t^3)+(t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_add_15_15 : decode t (addCode 15 15) = decode t 15+decode t 15 := by
  change (0) = (1 + t + t^2 + t^3)+(1 + t + t^2 + t^3)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_add_row_0 (j : Code) : decode t (addCode 0 j) = decode t 0+decode t j := by
  fin_cases j
  · exact decode_add_0_0 t
  · exact decode_add_0_1 t
  · exact decode_add_0_2 t
  · exact decode_add_0_3 t
  · exact decode_add_0_4 t
  · exact decode_add_0_5 t
  · exact decode_add_0_6 t
  · exact decode_add_0_7 t
  · exact decode_add_0_8 t
  · exact decode_add_0_9 t
  · exact decode_add_0_10 t
  · exact decode_add_0_11 t
  · exact decode_add_0_12 t
  · exact decode_add_0_13 t
  · exact decode_add_0_14 t
  · exact decode_add_0_15 t
private theorem decode_add_row_1 (j : Code) : decode t (addCode 1 j) = decode t 1+decode t j := by
  fin_cases j
  · exact decode_add_1_0 t
  · exact decode_add_1_1 t
  · exact decode_add_1_2 t
  · exact decode_add_1_3 t
  · exact decode_add_1_4 t
  · exact decode_add_1_5 t
  · exact decode_add_1_6 t
  · exact decode_add_1_7 t
  · exact decode_add_1_8 t
  · exact decode_add_1_9 t
  · exact decode_add_1_10 t
  · exact decode_add_1_11 t
  · exact decode_add_1_12 t
  · exact decode_add_1_13 t
  · exact decode_add_1_14 t
  · exact decode_add_1_15 t
private theorem decode_add_row_2 (j : Code) : decode t (addCode 2 j) = decode t 2+decode t j := by
  fin_cases j
  · exact decode_add_2_0 t
  · exact decode_add_2_1 t
  · exact decode_add_2_2 t
  · exact decode_add_2_3 t
  · exact decode_add_2_4 t
  · exact decode_add_2_5 t
  · exact decode_add_2_6 t
  · exact decode_add_2_7 t
  · exact decode_add_2_8 t
  · exact decode_add_2_9 t
  · exact decode_add_2_10 t
  · exact decode_add_2_11 t
  · exact decode_add_2_12 t
  · exact decode_add_2_13 t
  · exact decode_add_2_14 t
  · exact decode_add_2_15 t
private theorem decode_add_row_3 (j : Code) : decode t (addCode 3 j) = decode t 3+decode t j := by
  fin_cases j
  · exact decode_add_3_0 t
  · exact decode_add_3_1 t
  · exact decode_add_3_2 t
  · exact decode_add_3_3 t
  · exact decode_add_3_4 t
  · exact decode_add_3_5 t
  · exact decode_add_3_6 t
  · exact decode_add_3_7 t
  · exact decode_add_3_8 t
  · exact decode_add_3_9 t
  · exact decode_add_3_10 t
  · exact decode_add_3_11 t
  · exact decode_add_3_12 t
  · exact decode_add_3_13 t
  · exact decode_add_3_14 t
  · exact decode_add_3_15 t
private theorem decode_add_row_4 (j : Code) : decode t (addCode 4 j) = decode t 4+decode t j := by
  fin_cases j
  · exact decode_add_4_0 t
  · exact decode_add_4_1 t
  · exact decode_add_4_2 t
  · exact decode_add_4_3 t
  · exact decode_add_4_4 t
  · exact decode_add_4_5 t
  · exact decode_add_4_6 t
  · exact decode_add_4_7 t
  · exact decode_add_4_8 t
  · exact decode_add_4_9 t
  · exact decode_add_4_10 t
  · exact decode_add_4_11 t
  · exact decode_add_4_12 t
  · exact decode_add_4_13 t
  · exact decode_add_4_14 t
  · exact decode_add_4_15 t
private theorem decode_add_row_5 (j : Code) : decode t (addCode 5 j) = decode t 5+decode t j := by
  fin_cases j
  · exact decode_add_5_0 t
  · exact decode_add_5_1 t
  · exact decode_add_5_2 t
  · exact decode_add_5_3 t
  · exact decode_add_5_4 t
  · exact decode_add_5_5 t
  · exact decode_add_5_6 t
  · exact decode_add_5_7 t
  · exact decode_add_5_8 t
  · exact decode_add_5_9 t
  · exact decode_add_5_10 t
  · exact decode_add_5_11 t
  · exact decode_add_5_12 t
  · exact decode_add_5_13 t
  · exact decode_add_5_14 t
  · exact decode_add_5_15 t
private theorem decode_add_row_6 (j : Code) : decode t (addCode 6 j) = decode t 6+decode t j := by
  fin_cases j
  · exact decode_add_6_0 t
  · exact decode_add_6_1 t
  · exact decode_add_6_2 t
  · exact decode_add_6_3 t
  · exact decode_add_6_4 t
  · exact decode_add_6_5 t
  · exact decode_add_6_6 t
  · exact decode_add_6_7 t
  · exact decode_add_6_8 t
  · exact decode_add_6_9 t
  · exact decode_add_6_10 t
  · exact decode_add_6_11 t
  · exact decode_add_6_12 t
  · exact decode_add_6_13 t
  · exact decode_add_6_14 t
  · exact decode_add_6_15 t
private theorem decode_add_row_7 (j : Code) : decode t (addCode 7 j) = decode t 7+decode t j := by
  fin_cases j
  · exact decode_add_7_0 t
  · exact decode_add_7_1 t
  · exact decode_add_7_2 t
  · exact decode_add_7_3 t
  · exact decode_add_7_4 t
  · exact decode_add_7_5 t
  · exact decode_add_7_6 t
  · exact decode_add_7_7 t
  · exact decode_add_7_8 t
  · exact decode_add_7_9 t
  · exact decode_add_7_10 t
  · exact decode_add_7_11 t
  · exact decode_add_7_12 t
  · exact decode_add_7_13 t
  · exact decode_add_7_14 t
  · exact decode_add_7_15 t
private theorem decode_add_row_8 (j : Code) : decode t (addCode 8 j) = decode t 8+decode t j := by
  fin_cases j
  · exact decode_add_8_0 t
  · exact decode_add_8_1 t
  · exact decode_add_8_2 t
  · exact decode_add_8_3 t
  · exact decode_add_8_4 t
  · exact decode_add_8_5 t
  · exact decode_add_8_6 t
  · exact decode_add_8_7 t
  · exact decode_add_8_8 t
  · exact decode_add_8_9 t
  · exact decode_add_8_10 t
  · exact decode_add_8_11 t
  · exact decode_add_8_12 t
  · exact decode_add_8_13 t
  · exact decode_add_8_14 t
  · exact decode_add_8_15 t
private theorem decode_add_row_9 (j : Code) : decode t (addCode 9 j) = decode t 9+decode t j := by
  fin_cases j
  · exact decode_add_9_0 t
  · exact decode_add_9_1 t
  · exact decode_add_9_2 t
  · exact decode_add_9_3 t
  · exact decode_add_9_4 t
  · exact decode_add_9_5 t
  · exact decode_add_9_6 t
  · exact decode_add_9_7 t
  · exact decode_add_9_8 t
  · exact decode_add_9_9 t
  · exact decode_add_9_10 t
  · exact decode_add_9_11 t
  · exact decode_add_9_12 t
  · exact decode_add_9_13 t
  · exact decode_add_9_14 t
  · exact decode_add_9_15 t
private theorem decode_add_row_10 (j : Code) : decode t (addCode 10 j) = decode t 10+decode t j := by
  fin_cases j
  · exact decode_add_10_0 t
  · exact decode_add_10_1 t
  · exact decode_add_10_2 t
  · exact decode_add_10_3 t
  · exact decode_add_10_4 t
  · exact decode_add_10_5 t
  · exact decode_add_10_6 t
  · exact decode_add_10_7 t
  · exact decode_add_10_8 t
  · exact decode_add_10_9 t
  · exact decode_add_10_10 t
  · exact decode_add_10_11 t
  · exact decode_add_10_12 t
  · exact decode_add_10_13 t
  · exact decode_add_10_14 t
  · exact decode_add_10_15 t
private theorem decode_add_row_11 (j : Code) : decode t (addCode 11 j) = decode t 11+decode t j := by
  fin_cases j
  · exact decode_add_11_0 t
  · exact decode_add_11_1 t
  · exact decode_add_11_2 t
  · exact decode_add_11_3 t
  · exact decode_add_11_4 t
  · exact decode_add_11_5 t
  · exact decode_add_11_6 t
  · exact decode_add_11_7 t
  · exact decode_add_11_8 t
  · exact decode_add_11_9 t
  · exact decode_add_11_10 t
  · exact decode_add_11_11 t
  · exact decode_add_11_12 t
  · exact decode_add_11_13 t
  · exact decode_add_11_14 t
  · exact decode_add_11_15 t
private theorem decode_add_row_12 (j : Code) : decode t (addCode 12 j) = decode t 12+decode t j := by
  fin_cases j
  · exact decode_add_12_0 t
  · exact decode_add_12_1 t
  · exact decode_add_12_2 t
  · exact decode_add_12_3 t
  · exact decode_add_12_4 t
  · exact decode_add_12_5 t
  · exact decode_add_12_6 t
  · exact decode_add_12_7 t
  · exact decode_add_12_8 t
  · exact decode_add_12_9 t
  · exact decode_add_12_10 t
  · exact decode_add_12_11 t
  · exact decode_add_12_12 t
  · exact decode_add_12_13 t
  · exact decode_add_12_14 t
  · exact decode_add_12_15 t
private theorem decode_add_row_13 (j : Code) : decode t (addCode 13 j) = decode t 13+decode t j := by
  fin_cases j
  · exact decode_add_13_0 t
  · exact decode_add_13_1 t
  · exact decode_add_13_2 t
  · exact decode_add_13_3 t
  · exact decode_add_13_4 t
  · exact decode_add_13_5 t
  · exact decode_add_13_6 t
  · exact decode_add_13_7 t
  · exact decode_add_13_8 t
  · exact decode_add_13_9 t
  · exact decode_add_13_10 t
  · exact decode_add_13_11 t
  · exact decode_add_13_12 t
  · exact decode_add_13_13 t
  · exact decode_add_13_14 t
  · exact decode_add_13_15 t
private theorem decode_add_row_14 (j : Code) : decode t (addCode 14 j) = decode t 14+decode t j := by
  fin_cases j
  · exact decode_add_14_0 t
  · exact decode_add_14_1 t
  · exact decode_add_14_2 t
  · exact decode_add_14_3 t
  · exact decode_add_14_4 t
  · exact decode_add_14_5 t
  · exact decode_add_14_6 t
  · exact decode_add_14_7 t
  · exact decode_add_14_8 t
  · exact decode_add_14_9 t
  · exact decode_add_14_10 t
  · exact decode_add_14_11 t
  · exact decode_add_14_12 t
  · exact decode_add_14_13 t
  · exact decode_add_14_14 t
  · exact decode_add_14_15 t
private theorem decode_add_row_15 (j : Code) : decode t (addCode 15 j) = decode t 15+decode t j := by
  fin_cases j
  · exact decode_add_15_0 t
  · exact decode_add_15_1 t
  · exact decode_add_15_2 t
  · exact decode_add_15_3 t
  · exact decode_add_15_4 t
  · exact decode_add_15_5 t
  · exact decode_add_15_6 t
  · exact decode_add_15_7 t
  · exact decode_add_15_8 t
  · exact decode_add_15_9 t
  · exact decode_add_15_10 t
  · exact decode_add_15_11 t
  · exact decode_add_15_12 t
  · exact decode_add_15_13 t
  · exact decode_add_15_14 t
  · exact decode_add_15_15 t
theorem decode_add (i j : Code) : decode t (addCode i j) = decode t i+decode t j := by
  fin_cases i
  · exact decode_add_row_0 t j
  · exact decode_add_row_1 t j
  · exact decode_add_row_2 t j
  · exact decode_add_row_3 t j
  · exact decode_add_row_4 t j
  · exact decode_add_row_5 t j
  · exact decode_add_row_6 t j
  · exact decode_add_row_7 t j
  · exact decode_add_row_8 t j
  · exact decode_add_row_9 t j
  · exact decode_add_row_10 t j
  · exact decode_add_row_11 t j
  · exact decode_add_row_12 t j
  · exact decode_add_row_13 t j
  · exact decode_add_row_14 t j
  · exact decode_add_row_15 t j
omit [CharP R 2] in
private theorem decode_mul_0_0 (_ht : t^4+t+1=0) : decode t (mulCode 0 0) = decode t 0*decode t 0 := by
  change (0) = (0)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_1 (_ht : t^4+t+1=0) : decode t (mulCode 0 1) = decode t 0*decode t 1 := by
  change (0) = (0)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_2 (_ht : t^4+t+1=0) : decode t (mulCode 0 2) = decode t 0*decode t 2 := by
  change (0) = (0)*(t)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_3 (_ht : t^4+t+1=0) : decode t (mulCode 0 3) = decode t 0*decode t 3 := by
  change (0) = (0)*(1 + t)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_4 (_ht : t^4+t+1=0) : decode t (mulCode 0 4) = decode t 0*decode t 4 := by
  change (0) = (0)*(t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_5 (_ht : t^4+t+1=0) : decode t (mulCode 0 5) = decode t 0*decode t 5 := by
  change (0) = (0)*(1 + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_6 (_ht : t^4+t+1=0) : decode t (mulCode 0 6) = decode t 0*decode t 6 := by
  change (0) = (0)*(t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_7 (_ht : t^4+t+1=0) : decode t (mulCode 0 7) = decode t 0*decode t 7 := by
  change (0) = (0)*(1 + t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_8 (_ht : t^4+t+1=0) : decode t (mulCode 0 8) = decode t 0*decode t 8 := by
  change (0) = (0)*(t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_9 (_ht : t^4+t+1=0) : decode t (mulCode 0 9) = decode t 0*decode t 9 := by
  change (0) = (0)*(1 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_10 (_ht : t^4+t+1=0) : decode t (mulCode 0 10) = decode t 0*decode t 10 := by
  change (0) = (0)*(t + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_11 (_ht : t^4+t+1=0) : decode t (mulCode 0 11) = decode t 0*decode t 11 := by
  change (0) = (0)*(1 + t + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_12 (_ht : t^4+t+1=0) : decode t (mulCode 0 12) = decode t 0*decode t 12 := by
  change (0) = (0)*(t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_13 (_ht : t^4+t+1=0) : decode t (mulCode 0 13) = decode t 0*decode t 13 := by
  change (0) = (0)*(1 + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_14 (_ht : t^4+t+1=0) : decode t (mulCode 0 14) = decode t 0*decode t 14 := by
  change (0) = (0)*(t + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_0_15 (_ht : t^4+t+1=0) : decode t (mulCode 0 15) = decode t 0*decode t 15 := by
  change (0) = (0)*(1 + t + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_0 (_ht : t^4+t+1=0) : decode t (mulCode 1 0) = decode t 1*decode t 0 := by
  change (0) = (1)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_1 (_ht : t^4+t+1=0) : decode t (mulCode 1 1) = decode t 1*decode t 1 := by
  change (1) = (1)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_2 (_ht : t^4+t+1=0) : decode t (mulCode 1 2) = decode t 1*decode t 2 := by
  change (t) = (1)*(t)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_3 (_ht : t^4+t+1=0) : decode t (mulCode 1 3) = decode t 1*decode t 3 := by
  change (1 + t) = (1)*(1 + t)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_4 (_ht : t^4+t+1=0) : decode t (mulCode 1 4) = decode t 1*decode t 4 := by
  change (t^2) = (1)*(t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_5 (_ht : t^4+t+1=0) : decode t (mulCode 1 5) = decode t 1*decode t 5 := by
  change (1 + t^2) = (1)*(1 + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_6 (_ht : t^4+t+1=0) : decode t (mulCode 1 6) = decode t 1*decode t 6 := by
  change (t + t^2) = (1)*(t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_7 (_ht : t^4+t+1=0) : decode t (mulCode 1 7) = decode t 1*decode t 7 := by
  change (1 + t + t^2) = (1)*(1 + t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_8 (_ht : t^4+t+1=0) : decode t (mulCode 1 8) = decode t 1*decode t 8 := by
  change (t^3) = (1)*(t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_9 (_ht : t^4+t+1=0) : decode t (mulCode 1 9) = decode t 1*decode t 9 := by
  change (1 + t^3) = (1)*(1 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_10 (_ht : t^4+t+1=0) : decode t (mulCode 1 10) = decode t 1*decode t 10 := by
  change (t + t^3) = (1)*(t + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_11 (_ht : t^4+t+1=0) : decode t (mulCode 1 11) = decode t 1*decode t 11 := by
  change (1 + t + t^3) = (1)*(1 + t + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_12 (_ht : t^4+t+1=0) : decode t (mulCode 1 12) = decode t 1*decode t 12 := by
  change (t^2 + t^3) = (1)*(t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_13 (_ht : t^4+t+1=0) : decode t (mulCode 1 13) = decode t 1*decode t 13 := by
  change (1 + t^2 + t^3) = (1)*(1 + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_14 (_ht : t^4+t+1=0) : decode t (mulCode 1 14) = decode t 1*decode t 14 := by
  change (t + t^2 + t^3) = (1)*(t + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_1_15 (_ht : t^4+t+1=0) : decode t (mulCode 1 15) = decode t 1*decode t 15 := by
  change (1 + t + t^2 + t^3) = (1)*(1 + t + t^2 + t^3)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_0 (_ht : t^4+t+1=0) : decode t (mulCode 2 0) = decode t 2*decode t 0 := by
  change (0) = (t)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_1 (_ht : t^4+t+1=0) : decode t (mulCode 2 1) = decode t 2*decode t 1 := by
  change (t) = (t)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_2 (_ht : t^4+t+1=0) : decode t (mulCode 2 2) = decode t 2*decode t 2 := by
  change (t^2) = (t)*(t)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_3 (_ht : t^4+t+1=0) : decode t (mulCode 2 3) = decode t 2*decode t 3 := by
  change (t + t^2) = (t)*(1 + t)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_4 (_ht : t^4+t+1=0) : decode t (mulCode 2 4) = decode t 2*decode t 4 := by
  change (t^3) = (t)*(t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_5 (_ht : t^4+t+1=0) : decode t (mulCode 2 5) = decode t 2*decode t 5 := by
  change (t + t^3) = (t)*(1 + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_6 (_ht : t^4+t+1=0) : decode t (mulCode 2 6) = decode t 2*decode t 6 := by
  change (t^2 + t^3) = (t)*(t + t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_2_7 (_ht : t^4+t+1=0) : decode t (mulCode 2 7) = decode t 2*decode t 7 := by
  change (t + t^2 + t^3) = (t)*(1 + t + t^2)
  ring
private theorem decode_mul_2_8 (_ht : t^4+t+1=0) : decode t (mulCode 2 8) = decode t 2*decode t 8 := by
  change (1 + t) = (t)*(t^3)
  have h : (t)*(t^3) = (1 + t)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_2_9 (_ht : t^4+t+1=0) : decode t (mulCode 2 9) = decode t 2*decode t 9 := by
  change (1) = (t)*(1 + t^3)
  have h : (t)*(1 + t^3) = (1)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_2_10 (_ht : t^4+t+1=0) : decode t (mulCode 2 10) = decode t 2*decode t 10 := by
  change (1 + t + t^2) = (t)*(t + t^3)
  have h : (t)*(t + t^3) = (1 + t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_2_11 (_ht : t^4+t+1=0) : decode t (mulCode 2 11) = decode t 2*decode t 11 := by
  change (1 + t^2) = (t)*(1 + t + t^3)
  have h : (t)*(1 + t + t^3) = (1 + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_2_12 (_ht : t^4+t+1=0) : decode t (mulCode 2 12) = decode t 2*decode t 12 := by
  change (1 + t + t^3) = (t)*(t^2 + t^3)
  have h : (t)*(t^2 + t^3) = (1 + t + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_2_13 (_ht : t^4+t+1=0) : decode t (mulCode 2 13) = decode t 2*decode t 13 := by
  change (1 + t^3) = (t)*(1 + t^2 + t^3)
  have h : (t)*(1 + t^2 + t^3) = (1 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_2_14 (_ht : t^4+t+1=0) : decode t (mulCode 2 14) = decode t 2*decode t 14 := by
  change (1 + t + t^2 + t^3) = (t)*(t + t^2 + t^3)
  have h : (t)*(t + t^2 + t^3) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_2_15 (_ht : t^4+t+1=0) : decode t (mulCode 2 15) = decode t 2*decode t 15 := by
  change (1 + t^2 + t^3) = (t)*(1 + t + t^2 + t^3)
  have h : (t)*(1 + t + t^2 + t^3) = (1 + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_3_0 (_ht : t^4+t+1=0) : decode t (mulCode 3 0) = decode t 3*decode t 0 := by
  change (0) = (1 + t)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_3_1 (_ht : t^4+t+1=0) : decode t (mulCode 3 1) = decode t 3*decode t 1 := by
  change (1 + t) = (1 + t)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_3_2 (_ht : t^4+t+1=0) : decode t (mulCode 3 2) = decode t 3*decode t 2 := by
  change (t + t^2) = (1 + t)*(t)
  ring
private theorem decode_mul_3_3 (_ht : t^4+t+1=0) : decode t (mulCode 3 3) = decode t 3*decode t 3 := by
  change (1 + t^2) = (1 + t)*(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
omit [CharP R 2] in
private theorem decode_mul_3_4 (_ht : t^4+t+1=0) : decode t (mulCode 3 4) = decode t 3*decode t 4 := by
  change (t^2 + t^3) = (1 + t)*(t^2)
  ring
omit [CharP R 2] in
private theorem decode_mul_3_5 (_ht : t^4+t+1=0) : decode t (mulCode 3 5) = decode t 3*decode t 5 := by
  change (1 + t + t^2 + t^3) = (1 + t)*(1 + t^2)
  ring
private theorem decode_mul_3_6 (_ht : t^4+t+1=0) : decode t (mulCode 3 6) = decode t 3*decode t 6 := by
  change (t + t^3) = (1 + t)*(t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_mul_3_7 (_ht : t^4+t+1=0) : decode t (mulCode 3 7) = decode t 3*decode t 7 := by
  change (1 + t^3) = (1 + t)*(1 + t + t^2)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_mul_3_8 (_ht : t^4+t+1=0) : decode t (mulCode 3 8) = decode t 3*decode t 8 := by
  change (1 + t + t^3) = (1 + t)*(t^3)
  have h : (1 + t)*(t^3) = (1 + t + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_3_9 (_ht : t^4+t+1=0) : decode t (mulCode 3 9) = decode t 3*decode t 9 := by
  change (t^3) = (1 + t)*(1 + t^3)
  have h : (1 + t)*(1 + t^3) = (t^3)+(t^4+t+1)*(1) := by
    ring
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_3_10 (_ht : t^4+t+1=0) : decode t (mulCode 3 10) = decode t 3*decode t 10 := by
  change (1 + t^2 + t^3) = (1 + t)*(t + t^3)
  have h : (1 + t)*(t + t^3) = (1 + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_3_11 (_ht : t^4+t+1=0) : decode t (mulCode 3 11) = decode t 3*decode t 11 := by
  change (t + t^2 + t^3) = (1 + t)*(1 + t + t^3)
  have h : (1 + t)*(1 + t + t^3) = (t + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_3_12 (_ht : t^4+t+1=0) : decode t (mulCode 3 12) = decode t 3*decode t 12 := by
  change (1 + t + t^2) = (1 + t)*(t^2 + t^3)
  have h : (1 + t)*(t^2 + t^3) = (1 + t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_3_13 (_ht : t^4+t+1=0) : decode t (mulCode 3 13) = decode t 3*decode t 13 := by
  change (t^2) = (1 + t)*(1 + t^2 + t^3)
  have h : (1 + t)*(1 + t^2 + t^3) = (t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_3_14 (_ht : t^4+t+1=0) : decode t (mulCode 3 14) = decode t 3*decode t 14 := by
  change (1) = (1 + t)*(t + t^2 + t^3)
  have h : (1 + t)*(t + t^2 + t^3) = (1)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_3_15 (_ht : t^4+t+1=0) : decode t (mulCode 3 15) = decode t 3*decode t 15 := by
  change (t) = (1 + t)*(1 + t + t^2 + t^3)
  have h : (1 + t)*(1 + t + t^2 + t^3) = (t)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_4_0 (_ht : t^4+t+1=0) : decode t (mulCode 4 0) = decode t 4*decode t 0 := by
  change (0) = (t^2)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_4_1 (_ht : t^4+t+1=0) : decode t (mulCode 4 1) = decode t 4*decode t 1 := by
  change (t^2) = (t^2)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_4_2 (_ht : t^4+t+1=0) : decode t (mulCode 4 2) = decode t 4*decode t 2 := by
  change (t^3) = (t^2)*(t)
  ring
omit [CharP R 2] in
private theorem decode_mul_4_3 (_ht : t^4+t+1=0) : decode t (mulCode 4 3) = decode t 4*decode t 3 := by
  change (t^2 + t^3) = (t^2)*(1 + t)
  ring
private theorem decode_mul_4_4 (_ht : t^4+t+1=0) : decode t (mulCode 4 4) = decode t 4*decode t 4 := by
  change (1 + t) = (t^2)*(t^2)
  have h : (t^2)*(t^2) = (1 + t)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_5 (_ht : t^4+t+1=0) : decode t (mulCode 4 5) = decode t 4*decode t 5 := by
  change (1 + t + t^2) = (t^2)*(1 + t^2)
  have h : (t^2)*(1 + t^2) = (1 + t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_6 (_ht : t^4+t+1=0) : decode t (mulCode 4 6) = decode t 4*decode t 6 := by
  change (1 + t + t^3) = (t^2)*(t + t^2)
  have h : (t^2)*(t + t^2) = (1 + t + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_7 (_ht : t^4+t+1=0) : decode t (mulCode 4 7) = decode t 4*decode t 7 := by
  change (1 + t + t^2 + t^3) = (t^2)*(1 + t + t^2)
  have h : (t^2)*(1 + t + t^2) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_8 (_ht : t^4+t+1=0) : decode t (mulCode 4 8) = decode t 4*decode t 8 := by
  change (t + t^2) = (t^2)*(t^3)
  have h : (t^2)*(t^3) = (t + t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_9 (_ht : t^4+t+1=0) : decode t (mulCode 4 9) = decode t 4*decode t 9 := by
  change (t) = (t^2)*(1 + t^3)
  have h : (t^2)*(1 + t^3) = (t)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_10 (_ht : t^4+t+1=0) : decode t (mulCode 4 10) = decode t 4*decode t 10 := by
  change (t + t^2 + t^3) = (t^2)*(t + t^3)
  have h : (t^2)*(t + t^3) = (t + t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_11 (_ht : t^4+t+1=0) : decode t (mulCode 4 11) = decode t 4*decode t 11 := by
  change (t + t^3) = (t^2)*(1 + t + t^3)
  have h : (t^2)*(1 + t + t^3) = (t + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_12 (_ht : t^4+t+1=0) : decode t (mulCode 4 12) = decode t 4*decode t 12 := by
  change (1 + t^2) = (t^2)*(t^2 + t^3)
  have h : (t^2)*(t^2 + t^3) = (1 + t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_13 (_ht : t^4+t+1=0) : decode t (mulCode 4 13) = decode t 4*decode t 13 := by
  change (1) = (t^2)*(1 + t^2 + t^3)
  have h : (t^2)*(1 + t^2 + t^3) = (1)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_14 (_ht : t^4+t+1=0) : decode t (mulCode 4 14) = decode t 4*decode t 14 := by
  change (1 + t^2 + t^3) = (t^2)*(t + t^2 + t^3)
  have h : (t^2)*(t + t^2 + t^3) = (1 + t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_4_15 (_ht : t^4+t+1=0) : decode t (mulCode 4 15) = decode t 4*decode t 15 := by
  change (1 + t^3) = (t^2)*(1 + t + t^2 + t^3)
  have h : (t^2)*(1 + t + t^2 + t^3) = (1 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_5_0 (_ht : t^4+t+1=0) : decode t (mulCode 5 0) = decode t 5*decode t 0 := by
  change (0) = (1 + t^2)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_5_1 (_ht : t^4+t+1=0) : decode t (mulCode 5 1) = decode t 5*decode t 1 := by
  change (1 + t^2) = (1 + t^2)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_5_2 (_ht : t^4+t+1=0) : decode t (mulCode 5 2) = decode t 5*decode t 2 := by
  change (t + t^3) = (1 + t^2)*(t)
  ring
omit [CharP R 2] in
private theorem decode_mul_5_3 (_ht : t^4+t+1=0) : decode t (mulCode 5 3) = decode t 5*decode t 3 := by
  change (1 + t + t^2 + t^3) = (1 + t^2)*(1 + t)
  ring
private theorem decode_mul_5_4 (_ht : t^4+t+1=0) : decode t (mulCode 5 4) = decode t 5*decode t 4 := by
  change (1 + t + t^2) = (1 + t^2)*(t^2)
  have h : (1 + t^2)*(t^2) = (1 + t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_5 (_ht : t^4+t+1=0) : decode t (mulCode 5 5) = decode t 5*decode t 5 := by
  change (t) = (1 + t^2)*(1 + t^2)
  have h : (1 + t^2)*(1 + t^2) = (t)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_6 (_ht : t^4+t+1=0) : decode t (mulCode 5 6) = decode t 5*decode t 6 := by
  change (1 + t^2 + t^3) = (1 + t^2)*(t + t^2)
  have h : (1 + t^2)*(t + t^2) = (1 + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_7 (_ht : t^4+t+1=0) : decode t (mulCode 5 7) = decode t 5*decode t 7 := by
  change (t^3) = (1 + t^2)*(1 + t + t^2)
  have h : (1 + t^2)*(1 + t + t^2) = (t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_8 (_ht : t^4+t+1=0) : decode t (mulCode 5 8) = decode t 5*decode t 8 := by
  change (t + t^2 + t^3) = (1 + t^2)*(t^3)
  have h : (1 + t^2)*(t^3) = (t + t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_9 (_ht : t^4+t+1=0) : decode t (mulCode 5 9) = decode t 5*decode t 9 := by
  change (1 + t + t^3) = (1 + t^2)*(1 + t^3)
  have h : (1 + t^2)*(1 + t^3) = (1 + t + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_10 (_ht : t^4+t+1=0) : decode t (mulCode 5 10) = decode t 5*decode t 10 := by
  change (t^2) = (1 + t^2)*(t + t^3)
  have h : (1 + t^2)*(t + t^3) = (t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_11 (_ht : t^4+t+1=0) : decode t (mulCode 5 11) = decode t 5*decode t 11 := by
  change (1) = (1 + t^2)*(1 + t + t^3)
  have h : (1 + t^2)*(1 + t + t^3) = (1)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_12 (_ht : t^4+t+1=0) : decode t (mulCode 5 12) = decode t 5*decode t 12 := by
  change (1 + t^3) = (1 + t^2)*(t^2 + t^3)
  have h : (1 + t^2)*(t^2 + t^3) = (1 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_13 (_ht : t^4+t+1=0) : decode t (mulCode 5 13) = decode t 5*decode t 13 := by
  change (t^2 + t^3) = (1 + t^2)*(1 + t^2 + t^3)
  have h : (1 + t^2)*(1 + t^2 + t^3) = (t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_14 (_ht : t^4+t+1=0) : decode t (mulCode 5 14) = decode t 5*decode t 14 := by
  change (1 + t) = (1 + t^2)*(t + t^2 + t^3)
  have h : (1 + t^2)*(t + t^2 + t^3) = (1 + t)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_5_15 (_ht : t^4+t+1=0) : decode t (mulCode 5 15) = decode t 5*decode t 15 := by
  change (t + t^2) = (1 + t^2)*(1 + t + t^2 + t^3)
  have h : (1 + t^2)*(1 + t + t^2 + t^3) = (t + t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_6_0 (_ht : t^4+t+1=0) : decode t (mulCode 6 0) = decode t 6*decode t 0 := by
  change (0) = (t + t^2)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_6_1 (_ht : t^4+t+1=0) : decode t (mulCode 6 1) = decode t 6*decode t 1 := by
  change (t + t^2) = (t + t^2)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_6_2 (_ht : t^4+t+1=0) : decode t (mulCode 6 2) = decode t 6*decode t 2 := by
  change (t^2 + t^3) = (t + t^2)*(t)
  ring
private theorem decode_mul_6_3 (_ht : t^4+t+1=0) : decode t (mulCode 6 3) = decode t 6*decode t 3 := by
  change (t + t^3) = (t + t^2)*(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_mul_6_4 (_ht : t^4+t+1=0) : decode t (mulCode 6 4) = decode t 6*decode t 4 := by
  change (1 + t + t^3) = (t + t^2)*(t^2)
  have h : (t + t^2)*(t^2) = (1 + t + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_5 (_ht : t^4+t+1=0) : decode t (mulCode 6 5) = decode t 6*decode t 5 := by
  change (1 + t^2 + t^3) = (t + t^2)*(1 + t^2)
  have h : (t + t^2)*(1 + t^2) = (1 + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_6 (_ht : t^4+t+1=0) : decode t (mulCode 6 6) = decode t 6*decode t 6 := by
  change (1 + t + t^2) = (t + t^2)*(t + t^2)
  have h : (t + t^2)*(t + t^2) = (1 + t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_7 (_ht : t^4+t+1=0) : decode t (mulCode 6 7) = decode t 6*decode t 7 := by
  change (1) = (t + t^2)*(1 + t + t^2)
  have h : (t + t^2)*(1 + t + t^2) = (1)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_8 (_ht : t^4+t+1=0) : decode t (mulCode 6 8) = decode t 6*decode t 8 := by
  change (1 + t^2) = (t + t^2)*(t^3)
  have h : (t + t^2)*(t^3) = (1 + t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_9 (_ht : t^4+t+1=0) : decode t (mulCode 6 9) = decode t 6*decode t 9 := by
  change (1 + t) = (t + t^2)*(1 + t^3)
  have h : (t + t^2)*(1 + t^3) = (1 + t)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_10 (_ht : t^4+t+1=0) : decode t (mulCode 6 10) = decode t 6*decode t 10 := by
  change (1 + t^3) = (t + t^2)*(t + t^3)
  have h : (t + t^2)*(t + t^3) = (1 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_11 (_ht : t^4+t+1=0) : decode t (mulCode 6 11) = decode t 6*decode t 11 := by
  change (1 + t + t^2 + t^3) = (t + t^2)*(1 + t + t^3)
  have h : (t + t^2)*(1 + t + t^3) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_12 (_ht : t^4+t+1=0) : decode t (mulCode 6 12) = decode t 6*decode t 12 := by
  change (t + t^2 + t^3) = (t + t^2)*(t^2 + t^3)
  have h : (t + t^2)*(t^2 + t^3) = (t + t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_13 (_ht : t^4+t+1=0) : decode t (mulCode 6 13) = decode t 6*decode t 13 := by
  change (t^3) = (t + t^2)*(1 + t^2 + t^3)
  have h : (t + t^2)*(1 + t^2 + t^3) = (t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_14 (_ht : t^4+t+1=0) : decode t (mulCode 6 14) = decode t 6*decode t 14 := by
  change (t) = (t + t^2)*(t + t^2 + t^3)
  have h : (t + t^2)*(t + t^2 + t^3) = (t)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_6_15 (_ht : t^4+t+1=0) : decode t (mulCode 6 15) = decode t 6*decode t 15 := by
  change (t^2) = (t + t^2)*(1 + t + t^2 + t^3)
  have h : (t + t^2)*(1 + t + t^2 + t^3) = (t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_7_0 (_ht : t^4+t+1=0) : decode t (mulCode 7 0) = decode t 7*decode t 0 := by
  change (0) = (1 + t + t^2)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_7_1 (_ht : t^4+t+1=0) : decode t (mulCode 7 1) = decode t 7*decode t 1 := by
  change (1 + t + t^2) = (1 + t + t^2)*(1)
  ring
omit [CharP R 2] in
private theorem decode_mul_7_2 (_ht : t^4+t+1=0) : decode t (mulCode 7 2) = decode t 7*decode t 2 := by
  change (t + t^2 + t^3) = (1 + t + t^2)*(t)
  ring
private theorem decode_mul_7_3 (_ht : t^4+t+1=0) : decode t (mulCode 7 3) = decode t 7*decode t 3 := by
  change (1 + t^3) = (1 + t + t^2)*(1 + t)
  ring_nf
  simp only [ofNat_mod]
  norm_num
private theorem decode_mul_7_4 (_ht : t^4+t+1=0) : decode t (mulCode 7 4) = decode t 7*decode t 4 := by
  change (1 + t + t^2 + t^3) = (1 + t + t^2)*(t^2)
  have h : (1 + t + t^2)*(t^2) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_5 (_ht : t^4+t+1=0) : decode t (mulCode 7 5) = decode t 7*decode t 5 := by
  change (t^3) = (1 + t + t^2)*(1 + t^2)
  have h : (1 + t + t^2)*(1 + t^2) = (t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_6 (_ht : t^4+t+1=0) : decode t (mulCode 7 6) = decode t 7*decode t 6 := by
  change (1) = (1 + t + t^2)*(t + t^2)
  have h : (1 + t + t^2)*(t + t^2) = (1)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_7 (_ht : t^4+t+1=0) : decode t (mulCode 7 7) = decode t 7*decode t 7 := by
  change (t + t^2) = (1 + t + t^2)*(1 + t + t^2)
  have h : (1 + t + t^2)*(1 + t + t^2) = (t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_8 (_ht : t^4+t+1=0) : decode t (mulCode 7 8) = decode t 7*decode t 8 := by
  change (1 + t^2 + t^3) = (1 + t + t^2)*(t^3)
  have h : (1 + t + t^2)*(t^3) = (1 + t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_9 (_ht : t^4+t+1=0) : decode t (mulCode 7 9) = decode t 7*decode t 9 := by
  change (t + t^3) = (1 + t + t^2)*(1 + t^3)
  have h : (1 + t + t^2)*(1 + t^3) = (t + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_10 (_ht : t^4+t+1=0) : decode t (mulCode 7 10) = decode t 7*decode t 10 := by
  change (1 + t) = (1 + t + t^2)*(t + t^3)
  have h : (1 + t + t^2)*(t + t^3) = (1 + t)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_11 (_ht : t^4+t+1=0) : decode t (mulCode 7 11) = decode t 7*decode t 11 := by
  change (t^2) = (1 + t + t^2)*(1 + t + t^3)
  have h : (1 + t + t^2)*(1 + t + t^3) = (t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_12 (_ht : t^4+t+1=0) : decode t (mulCode 7 12) = decode t 7*decode t 12 := by
  change (t) = (1 + t + t^2)*(t^2 + t^3)
  have h : (1 + t + t^2)*(t^2 + t^3) = (t)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_13 (_ht : t^4+t+1=0) : decode t (mulCode 7 13) = decode t 7*decode t 13 := by
  change (1 + t^2) = (1 + t + t^2)*(1 + t^2 + t^3)
  have h : (1 + t + t^2)*(1 + t^2 + t^3) = (1 + t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_14 (_ht : t^4+t+1=0) : decode t (mulCode 7 14) = decode t 7*decode t 14 := by
  change (t^2 + t^3) = (1 + t + t^2)*(t + t^2 + t^3)
  have h : (1 + t + t^2)*(t + t^2 + t^3) = (t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_7_15 (_ht : t^4+t+1=0) : decode t (mulCode 7 15) = decode t 7*decode t 15 := by
  change (1 + t + t^3) = (1 + t + t^2)*(1 + t + t^2 + t^3)
  have h : (1 + t + t^2)*(1 + t + t^2 + t^3) = (1 + t + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_8_0 (_ht : t^4+t+1=0) : decode t (mulCode 8 0) = decode t 8*decode t 0 := by
  change (0) = (t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_8_1 (_ht : t^4+t+1=0) : decode t (mulCode 8 1) = decode t 8*decode t 1 := by
  change (t^3) = (t^3)*(1)
  ring
private theorem decode_mul_8_2 (_ht : t^4+t+1=0) : decode t (mulCode 8 2) = decode t 8*decode t 2 := by
  change (1 + t) = (t^3)*(t)
  have h : (t^3)*(t) = (1 + t)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_3 (_ht : t^4+t+1=0) : decode t (mulCode 8 3) = decode t 8*decode t 3 := by
  change (1 + t + t^3) = (t^3)*(1 + t)
  have h : (t^3)*(1 + t) = (1 + t + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_4 (_ht : t^4+t+1=0) : decode t (mulCode 8 4) = decode t 8*decode t 4 := by
  change (t + t^2) = (t^3)*(t^2)
  have h : (t^3)*(t^2) = (t + t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_5 (_ht : t^4+t+1=0) : decode t (mulCode 8 5) = decode t 8*decode t 5 := by
  change (t + t^2 + t^3) = (t^3)*(1 + t^2)
  have h : (t^3)*(1 + t^2) = (t + t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_6 (_ht : t^4+t+1=0) : decode t (mulCode 8 6) = decode t 8*decode t 6 := by
  change (1 + t^2) = (t^3)*(t + t^2)
  have h : (t^3)*(t + t^2) = (1 + t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_7 (_ht : t^4+t+1=0) : decode t (mulCode 8 7) = decode t 8*decode t 7 := by
  change (1 + t^2 + t^3) = (t^3)*(1 + t + t^2)
  have h : (t^3)*(1 + t + t^2) = (1 + t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_8 (_ht : t^4+t+1=0) : decode t (mulCode 8 8) = decode t 8*decode t 8 := by
  change (t^2 + t^3) = (t^3)*(t^3)
  have h : (t^3)*(t^3) = (t^2 + t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_9 (_ht : t^4+t+1=0) : decode t (mulCode 8 9) = decode t 8*decode t 9 := by
  change (t^2) = (t^3)*(1 + t^3)
  have h : (t^3)*(1 + t^3) = (t^2)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_10 (_ht : t^4+t+1=0) : decode t (mulCode 8 10) = decode t 8*decode t 10 := by
  change (1 + t + t^2 + t^3) = (t^3)*(t + t^3)
  have h : (t^3)*(t + t^3) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_11 (_ht : t^4+t+1=0) : decode t (mulCode 8 11) = decode t 8*decode t 11 := by
  change (1 + t + t^2) = (t^3)*(1 + t + t^3)
  have h : (t^3)*(1 + t + t^3) = (1 + t + t^2)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_12 (_ht : t^4+t+1=0) : decode t (mulCode 8 12) = decode t 8*decode t 12 := by
  change (t + t^3) = (t^3)*(t^2 + t^3)
  have h : (t^3)*(t^2 + t^3) = (t + t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_13 (_ht : t^4+t+1=0) : decode t (mulCode 8 13) = decode t 8*decode t 13 := by
  change (t) = (t^3)*(1 + t^2 + t^3)
  have h : (t^3)*(1 + t^2 + t^3) = (t)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_14 (_ht : t^4+t+1=0) : decode t (mulCode 8 14) = decode t 8*decode t 14 := by
  change (1 + t^3) = (t^3)*(t + t^2 + t^3)
  have h : (t^3)*(t + t^2 + t^3) = (1 + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_8_15 (_ht : t^4+t+1=0) : decode t (mulCode 8 15) = decode t 8*decode t 15 := by
  change (1) = (t^3)*(1 + t + t^2 + t^3)
  have h : (t^3)*(1 + t + t^2 + t^3) = (1)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_9_0 (_ht : t^4+t+1=0) : decode t (mulCode 9 0) = decode t 9*decode t 0 := by
  change (0) = (1 + t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_9_1 (_ht : t^4+t+1=0) : decode t (mulCode 9 1) = decode t 9*decode t 1 := by
  change (1 + t^3) = (1 + t^3)*(1)
  ring
private theorem decode_mul_9_2 (_ht : t^4+t+1=0) : decode t (mulCode 9 2) = decode t 9*decode t 2 := by
  change (1) = (1 + t^3)*(t)
  have h : (1 + t^3)*(t) = (1)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_9_3 (_ht : t^4+t+1=0) : decode t (mulCode 9 3) = decode t 9*decode t 3 := by
  change (t^3) = (1 + t^3)*(1 + t)
  have h : (1 + t^3)*(1 + t) = (t^3)+(t^4+t+1)*(1) := by
    ring
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_4 (_ht : t^4+t+1=0) : decode t (mulCode 9 4) = decode t 9*decode t 4 := by
  change (t) = (1 + t^3)*(t^2)
  have h : (1 + t^3)*(t^2) = (t)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_5 (_ht : t^4+t+1=0) : decode t (mulCode 9 5) = decode t 9*decode t 5 := by
  change (1 + t + t^3) = (1 + t^3)*(1 + t^2)
  have h : (1 + t^3)*(1 + t^2) = (1 + t + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_6 (_ht : t^4+t+1=0) : decode t (mulCode 9 6) = decode t 9*decode t 6 := by
  change (1 + t) = (1 + t^3)*(t + t^2)
  have h : (1 + t^3)*(t + t^2) = (1 + t)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_7 (_ht : t^4+t+1=0) : decode t (mulCode 9 7) = decode t 9*decode t 7 := by
  change (t + t^3) = (1 + t^3)*(1 + t + t^2)
  have h : (1 + t^3)*(1 + t + t^2) = (t + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_8 (_ht : t^4+t+1=0) : decode t (mulCode 9 8) = decode t 9*decode t 8 := by
  change (t^2) = (1 + t^3)*(t^3)
  have h : (1 + t^3)*(t^3) = (t^2)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_9 (_ht : t^4+t+1=0) : decode t (mulCode 9 9) = decode t 9*decode t 9 := by
  change (1 + t^2 + t^3) = (1 + t^3)*(1 + t^3)
  have h : (1 + t^3)*(1 + t^3) = (1 + t^2 + t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_10 (_ht : t^4+t+1=0) : decode t (mulCode 9 10) = decode t 9*decode t 10 := by
  change (1 + t^2) = (1 + t^3)*(t + t^3)
  have h : (1 + t^3)*(t + t^3) = (1 + t^2)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_11 (_ht : t^4+t+1=0) : decode t (mulCode 9 11) = decode t 9*decode t 11 := by
  change (t^2 + t^3) = (1 + t^3)*(1 + t + t^3)
  have h : (1 + t^3)*(1 + t + t^3) = (t^2 + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_12 (_ht : t^4+t+1=0) : decode t (mulCode 9 12) = decode t 9*decode t 12 := by
  change (t + t^2) = (1 + t^3)*(t^2 + t^3)
  have h : (1 + t^3)*(t^2 + t^3) = (t + t^2)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_13 (_ht : t^4+t+1=0) : decode t (mulCode 9 13) = decode t 9*decode t 13 := by
  change (1 + t + t^2 + t^3) = (1 + t^3)*(1 + t^2 + t^3)
  have h : (1 + t^3)*(1 + t^2 + t^3) = (1 + t + t^2 + t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_14 (_ht : t^4+t+1=0) : decode t (mulCode 9 14) = decode t 9*decode t 14 := by
  change (1 + t + t^2) = (1 + t^3)*(t + t^2 + t^3)
  have h : (1 + t^3)*(t + t^2 + t^3) = (1 + t + t^2)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_9_15 (_ht : t^4+t+1=0) : decode t (mulCode 9 15) = decode t 9*decode t 15 := by
  change (t + t^2 + t^3) = (1 + t^3)*(1 + t + t^2 + t^3)
  have h : (1 + t^3)*(1 + t + t^2 + t^3) = (t + t^2 + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_10_0 (_ht : t^4+t+1=0) : decode t (mulCode 10 0) = decode t 10*decode t 0 := by
  change (0) = (t + t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_10_1 (_ht : t^4+t+1=0) : decode t (mulCode 10 1) = decode t 10*decode t 1 := by
  change (t + t^3) = (t + t^3)*(1)
  ring
private theorem decode_mul_10_2 (_ht : t^4+t+1=0) : decode t (mulCode 10 2) = decode t 10*decode t 2 := by
  change (1 + t + t^2) = (t + t^3)*(t)
  have h : (t + t^3)*(t) = (1 + t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_3 (_ht : t^4+t+1=0) : decode t (mulCode 10 3) = decode t 10*decode t 3 := by
  change (1 + t^2 + t^3) = (t + t^3)*(1 + t)
  have h : (t + t^3)*(1 + t) = (1 + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_4 (_ht : t^4+t+1=0) : decode t (mulCode 10 4) = decode t 10*decode t 4 := by
  change (t + t^2 + t^3) = (t + t^3)*(t^2)
  have h : (t + t^3)*(t^2) = (t + t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_5 (_ht : t^4+t+1=0) : decode t (mulCode 10 5) = decode t 10*decode t 5 := by
  change (t^2) = (t + t^3)*(1 + t^2)
  have h : (t + t^3)*(1 + t^2) = (t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_6 (_ht : t^4+t+1=0) : decode t (mulCode 10 6) = decode t 10*decode t 6 := by
  change (1 + t^3) = (t + t^3)*(t + t^2)
  have h : (t + t^3)*(t + t^2) = (1 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_7 (_ht : t^4+t+1=0) : decode t (mulCode 10 7) = decode t 10*decode t 7 := by
  change (1 + t) = (t + t^3)*(1 + t + t^2)
  have h : (t + t^3)*(1 + t + t^2) = (1 + t)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_8 (_ht : t^4+t+1=0) : decode t (mulCode 10 8) = decode t 10*decode t 8 := by
  change (1 + t + t^2 + t^3) = (t + t^3)*(t^3)
  have h : (t + t^3)*(t^3) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_9 (_ht : t^4+t+1=0) : decode t (mulCode 10 9) = decode t 10*decode t 9 := by
  change (1 + t^2) = (t + t^3)*(1 + t^3)
  have h : (t + t^3)*(1 + t^3) = (1 + t^2)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_10 (_ht : t^4+t+1=0) : decode t (mulCode 10 10) = decode t 10*decode t 10 := by
  change (t^3) = (t + t^3)*(t + t^3)
  have h : (t + t^3)*(t + t^3) = (t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_11 (_ht : t^4+t+1=0) : decode t (mulCode 10 11) = decode t 10*decode t 11 := by
  change (t) = (t + t^3)*(1 + t + t^3)
  have h : (t + t^3)*(1 + t + t^3) = (t)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_12 (_ht : t^4+t+1=0) : decode t (mulCode 10 12) = decode t 10*decode t 12 := by
  change (1) = (t + t^3)*(t^2 + t^3)
  have h : (t + t^3)*(t^2 + t^3) = (1)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_13 (_ht : t^4+t+1=0) : decode t (mulCode 10 13) = decode t 10*decode t 13 := by
  change (1 + t + t^3) = (t + t^3)*(1 + t^2 + t^3)
  have h : (t + t^3)*(1 + t^2 + t^3) = (1 + t + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_14 (_ht : t^4+t+1=0) : decode t (mulCode 10 14) = decode t 10*decode t 14 := by
  change (t + t^2) = (t + t^3)*(t + t^2 + t^3)
  have h : (t + t^3)*(t + t^2 + t^3) = (t + t^2)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_10_15 (_ht : t^4+t+1=0) : decode t (mulCode 10 15) = decode t 10*decode t 15 := by
  change (t^2 + t^3) = (t + t^3)*(1 + t + t^2 + t^3)
  have h : (t + t^3)*(1 + t + t^2 + t^3) = (t^2 + t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_11_0 (_ht : t^4+t+1=0) : decode t (mulCode 11 0) = decode t 11*decode t 0 := by
  change (0) = (1 + t + t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_11_1 (_ht : t^4+t+1=0) : decode t (mulCode 11 1) = decode t 11*decode t 1 := by
  change (1 + t + t^3) = (1 + t + t^3)*(1)
  ring
private theorem decode_mul_11_2 (_ht : t^4+t+1=0) : decode t (mulCode 11 2) = decode t 11*decode t 2 := by
  change (1 + t^2) = (1 + t + t^3)*(t)
  have h : (1 + t + t^3)*(t) = (1 + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_11_3 (_ht : t^4+t+1=0) : decode t (mulCode 11 3) = decode t 11*decode t 3 := by
  change (t + t^2 + t^3) = (1 + t + t^3)*(1 + t)
  have h : (1 + t + t^3)*(1 + t) = (t + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_4 (_ht : t^4+t+1=0) : decode t (mulCode 11 4) = decode t 11*decode t 4 := by
  change (t + t^3) = (1 + t + t^3)*(t^2)
  have h : (1 + t + t^3)*(t^2) = (t + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_5 (_ht : t^4+t+1=0) : decode t (mulCode 11 5) = decode t 11*decode t 5 := by
  change (1) = (1 + t + t^3)*(1 + t^2)
  have h : (1 + t + t^3)*(1 + t^2) = (1)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_6 (_ht : t^4+t+1=0) : decode t (mulCode 11 6) = decode t 11*decode t 6 := by
  change (1 + t + t^2 + t^3) = (1 + t + t^3)*(t + t^2)
  have h : (1 + t + t^3)*(t + t^2) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_7 (_ht : t^4+t+1=0) : decode t (mulCode 11 7) = decode t 11*decode t 7 := by
  change (t^2) = (1 + t + t^3)*(1 + t + t^2)
  have h : (1 + t + t^3)*(1 + t + t^2) = (t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_8 (_ht : t^4+t+1=0) : decode t (mulCode 11 8) = decode t 11*decode t 8 := by
  change (1 + t + t^2) = (1 + t + t^3)*(t^3)
  have h : (1 + t + t^3)*(t^3) = (1 + t + t^2)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_9 (_ht : t^4+t+1=0) : decode t (mulCode 11 9) = decode t 11*decode t 9 := by
  change (t^2 + t^3) = (1 + t + t^3)*(1 + t^3)
  have h : (1 + t + t^3)*(1 + t^3) = (t^2 + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_10 (_ht : t^4+t+1=0) : decode t (mulCode 11 10) = decode t 11*decode t 10 := by
  change (t) = (1 + t + t^3)*(t + t^3)
  have h : (1 + t + t^3)*(t + t^3) = (t)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_11 (_ht : t^4+t+1=0) : decode t (mulCode 11 11) = decode t 11*decode t 11 := by
  change (1 + t^3) = (1 + t + t^3)*(1 + t + t^3)
  have h : (1 + t + t^3)*(1 + t + t^3) = (1 + t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_12 (_ht : t^4+t+1=0) : decode t (mulCode 11 12) = decode t 11*decode t 12 := by
  change (1 + t^2 + t^3) = (1 + t + t^3)*(t^2 + t^3)
  have h : (1 + t + t^3)*(t^2 + t^3) = (1 + t^2 + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_13 (_ht : t^4+t+1=0) : decode t (mulCode 11 13) = decode t 11*decode t 13 := by
  change (t + t^2) = (1 + t + t^3)*(1 + t^2 + t^3)
  have h : (1 + t + t^3)*(1 + t^2 + t^3) = (t + t^2)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_14 (_ht : t^4+t+1=0) : decode t (mulCode 11 14) = decode t 11*decode t 14 := by
  change (t^3) = (1 + t + t^3)*(t + t^2 + t^3)
  have h : (1 + t + t^3)*(t + t^2 + t^3) = (t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_11_15 (_ht : t^4+t+1=0) : decode t (mulCode 11 15) = decode t 11*decode t 15 := by
  change (1 + t) = (1 + t + t^3)*(1 + t + t^2 + t^3)
  have h : (1 + t + t^3)*(1 + t + t^2 + t^3) = (1 + t)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_12_0 (_ht : t^4+t+1=0) : decode t (mulCode 12 0) = decode t 12*decode t 0 := by
  change (0) = (t^2 + t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_12_1 (_ht : t^4+t+1=0) : decode t (mulCode 12 1) = decode t 12*decode t 1 := by
  change (t^2 + t^3) = (t^2 + t^3)*(1)
  ring
private theorem decode_mul_12_2 (_ht : t^4+t+1=0) : decode t (mulCode 12 2) = decode t 12*decode t 2 := by
  change (1 + t + t^3) = (t^2 + t^3)*(t)
  have h : (t^2 + t^3)*(t) = (1 + t + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_3 (_ht : t^4+t+1=0) : decode t (mulCode 12 3) = decode t 12*decode t 3 := by
  change (1 + t + t^2) = (t^2 + t^3)*(1 + t)
  have h : (t^2 + t^3)*(1 + t) = (1 + t + t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_4 (_ht : t^4+t+1=0) : decode t (mulCode 12 4) = decode t 12*decode t 4 := by
  change (1 + t^2) = (t^2 + t^3)*(t^2)
  have h : (t^2 + t^3)*(t^2) = (1 + t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_5 (_ht : t^4+t+1=0) : decode t (mulCode 12 5) = decode t 12*decode t 5 := by
  change (1 + t^3) = (t^2 + t^3)*(1 + t^2)
  have h : (t^2 + t^3)*(1 + t^2) = (1 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_6 (_ht : t^4+t+1=0) : decode t (mulCode 12 6) = decode t 12*decode t 6 := by
  change (t + t^2 + t^3) = (t^2 + t^3)*(t + t^2)
  have h : (t^2 + t^3)*(t + t^2) = (t + t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_7 (_ht : t^4+t+1=0) : decode t (mulCode 12 7) = decode t 12*decode t 7 := by
  change (t) = (t^2 + t^3)*(1 + t + t^2)
  have h : (t^2 + t^3)*(1 + t + t^2) = (t)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_8 (_ht : t^4+t+1=0) : decode t (mulCode 12 8) = decode t 12*decode t 8 := by
  change (t + t^3) = (t^2 + t^3)*(t^3)
  have h : (t^2 + t^3)*(t^3) = (t + t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_9 (_ht : t^4+t+1=0) : decode t (mulCode 12 9) = decode t 12*decode t 9 := by
  change (t + t^2) = (t^2 + t^3)*(1 + t^3)
  have h : (t^2 + t^3)*(1 + t^3) = (t + t^2)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_10 (_ht : t^4+t+1=0) : decode t (mulCode 12 10) = decode t 12*decode t 10 := by
  change (1) = (t^2 + t^3)*(t + t^3)
  have h : (t^2 + t^3)*(t + t^3) = (1)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_11 (_ht : t^4+t+1=0) : decode t (mulCode 12 11) = decode t 12*decode t 11 := by
  change (1 + t^2 + t^3) = (t^2 + t^3)*(1 + t + t^3)
  have h : (t^2 + t^3)*(1 + t + t^3) = (1 + t^2 + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_12 (_ht : t^4+t+1=0) : decode t (mulCode 12 12) = decode t 12*decode t 12 := by
  change (1 + t + t^2 + t^3) = (t^2 + t^3)*(t^2 + t^3)
  have h : (t^2 + t^3)*(t^2 + t^3) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_13 (_ht : t^4+t+1=0) : decode t (mulCode 12 13) = decode t 12*decode t 13 := by
  change (1 + t) = (t^2 + t^3)*(1 + t^2 + t^3)
  have h : (t^2 + t^3)*(1 + t^2 + t^3) = (1 + t)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_14 (_ht : t^4+t+1=0) : decode t (mulCode 12 14) = decode t 12*decode t 14 := by
  change (t^2) = (t^2 + t^3)*(t + t^2 + t^3)
  have h : (t^2 + t^3)*(t + t^2 + t^3) = (t^2)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_12_15 (_ht : t^4+t+1=0) : decode t (mulCode 12 15) = decode t 12*decode t 15 := by
  change (t^3) = (t^2 + t^3)*(1 + t + t^2 + t^3)
  have h : (t^2 + t^3)*(1 + t + t^2 + t^3) = (t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_13_0 (_ht : t^4+t+1=0) : decode t (mulCode 13 0) = decode t 13*decode t 0 := by
  change (0) = (1 + t^2 + t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_13_1 (_ht : t^4+t+1=0) : decode t (mulCode 13 1) = decode t 13*decode t 1 := by
  change (1 + t^2 + t^3) = (1 + t^2 + t^3)*(1)
  ring
private theorem decode_mul_13_2 (_ht : t^4+t+1=0) : decode t (mulCode 13 2) = decode t 13*decode t 2 := by
  change (1 + t^3) = (1 + t^2 + t^3)*(t)
  have h : (1 + t^2 + t^3)*(t) = (1 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_3 (_ht : t^4+t+1=0) : decode t (mulCode 13 3) = decode t 13*decode t 3 := by
  change (t^2) = (1 + t^2 + t^3)*(1 + t)
  have h : (1 + t^2 + t^3)*(1 + t) = (t^2)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_4 (_ht : t^4+t+1=0) : decode t (mulCode 13 4) = decode t 13*decode t 4 := by
  change (1) = (1 + t^2 + t^3)*(t^2)
  have h : (1 + t^2 + t^3)*(t^2) = (1)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_5 (_ht : t^4+t+1=0) : decode t (mulCode 13 5) = decode t 13*decode t 5 := by
  change (t^2 + t^3) = (1 + t^2 + t^3)*(1 + t^2)
  have h : (1 + t^2 + t^3)*(1 + t^2) = (t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_6 (_ht : t^4+t+1=0) : decode t (mulCode 13 6) = decode t 13*decode t 6 := by
  change (t^3) = (1 + t^2 + t^3)*(t + t^2)
  have h : (1 + t^2 + t^3)*(t + t^2) = (t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_7 (_ht : t^4+t+1=0) : decode t (mulCode 13 7) = decode t 13*decode t 7 := by
  change (1 + t^2) = (1 + t^2 + t^3)*(1 + t + t^2)
  have h : (1 + t^2 + t^3)*(1 + t + t^2) = (1 + t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_8 (_ht : t^4+t+1=0) : decode t (mulCode 13 8) = decode t 13*decode t 8 := by
  change (t) = (1 + t^2 + t^3)*(t^3)
  have h : (1 + t^2 + t^3)*(t^3) = (t)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_9 (_ht : t^4+t+1=0) : decode t (mulCode 13 9) = decode t 13*decode t 9 := by
  change (1 + t + t^2 + t^3) = (1 + t^2 + t^3)*(1 + t^3)
  have h : (1 + t^2 + t^3)*(1 + t^3) = (1 + t + t^2 + t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_10 (_ht : t^4+t+1=0) : decode t (mulCode 13 10) = decode t 13*decode t 10 := by
  change (1 + t + t^3) = (1 + t^2 + t^3)*(t + t^3)
  have h : (1 + t^2 + t^3)*(t + t^3) = (1 + t + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_11 (_ht : t^4+t+1=0) : decode t (mulCode 13 11) = decode t 13*decode t 11 := by
  change (t + t^2) = (1 + t^2 + t^3)*(1 + t + t^3)
  have h : (1 + t^2 + t^3)*(1 + t + t^3) = (t + t^2)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_12 (_ht : t^4+t+1=0) : decode t (mulCode 13 12) = decode t 13*decode t 12 := by
  change (1 + t) = (1 + t^2 + t^3)*(t^2 + t^3)
  have h : (1 + t^2 + t^3)*(t^2 + t^3) = (1 + t)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_13 (_ht : t^4+t+1=0) : decode t (mulCode 13 13) = decode t 13*decode t 13 := by
  change (t + t^2 + t^3) = (1 + t^2 + t^3)*(1 + t^2 + t^3)
  have h : (1 + t^2 + t^3)*(1 + t^2 + t^3) = (t + t^2 + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_14 (_ht : t^4+t+1=0) : decode t (mulCode 13 14) = decode t 13*decode t 14 := by
  change (t + t^3) = (1 + t^2 + t^3)*(t + t^2 + t^3)
  have h : (1 + t^2 + t^3)*(t + t^2 + t^3) = (t + t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_13_15 (_ht : t^4+t+1=0) : decode t (mulCode 13 15) = decode t 13*decode t 15 := by
  change (1 + t + t^2) = (1 + t^2 + t^3)*(1 + t + t^2 + t^3)
  have h : (1 + t^2 + t^3)*(1 + t + t^2 + t^3) = (1 + t + t^2)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_14_0 (_ht : t^4+t+1=0) : decode t (mulCode 14 0) = decode t 14*decode t 0 := by
  change (0) = (t + t^2 + t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_14_1 (_ht : t^4+t+1=0) : decode t (mulCode 14 1) = decode t 14*decode t 1 := by
  change (t + t^2 + t^3) = (t + t^2 + t^3)*(1)
  ring
private theorem decode_mul_14_2 (_ht : t^4+t+1=0) : decode t (mulCode 14 2) = decode t 14*decode t 2 := by
  change (1 + t + t^2 + t^3) = (t + t^2 + t^3)*(t)
  have h : (t + t^2 + t^3)*(t) = (1 + t + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_3 (_ht : t^4+t+1=0) : decode t (mulCode 14 3) = decode t 14*decode t 3 := by
  change (1) = (t + t^2 + t^3)*(1 + t)
  have h : (t + t^2 + t^3)*(1 + t) = (1)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_4 (_ht : t^4+t+1=0) : decode t (mulCode 14 4) = decode t 14*decode t 4 := by
  change (1 + t^2 + t^3) = (t + t^2 + t^3)*(t^2)
  have h : (t + t^2 + t^3)*(t^2) = (1 + t^2 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_5 (_ht : t^4+t+1=0) : decode t (mulCode 14 5) = decode t 14*decode t 5 := by
  change (1 + t) = (t + t^2 + t^3)*(1 + t^2)
  have h : (t + t^2 + t^3)*(1 + t^2) = (1 + t)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_6 (_ht : t^4+t+1=0) : decode t (mulCode 14 6) = decode t 14*decode t 6 := by
  change (t) = (t + t^2 + t^3)*(t + t^2)
  have h : (t + t^2 + t^3)*(t + t^2) = (t)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_7 (_ht : t^4+t+1=0) : decode t (mulCode 14 7) = decode t 14*decode t 7 := by
  change (t^2 + t^3) = (t + t^2 + t^3)*(1 + t + t^2)
  have h : (t + t^2 + t^3)*(1 + t + t^2) = (t^2 + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_8 (_ht : t^4+t+1=0) : decode t (mulCode 14 8) = decode t 14*decode t 8 := by
  change (1 + t^3) = (t + t^2 + t^3)*(t^3)
  have h : (t + t^2 + t^3)*(t^3) = (1 + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_9 (_ht : t^4+t+1=0) : decode t (mulCode 14 9) = decode t 14*decode t 9 := by
  change (1 + t + t^2) = (t + t^2 + t^3)*(1 + t^3)
  have h : (t + t^2 + t^3)*(1 + t^3) = (1 + t + t^2)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_10 (_ht : t^4+t+1=0) : decode t (mulCode 14 10) = decode t 14*decode t 10 := by
  change (t + t^2) = (t + t^2 + t^3)*(t + t^3)
  have h : (t + t^2 + t^3)*(t + t^3) = (t + t^2)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_11 (_ht : t^4+t+1=0) : decode t (mulCode 14 11) = decode t 14*decode t 11 := by
  change (t^3) = (t + t^2 + t^3)*(1 + t + t^3)
  have h : (t + t^2 + t^3)*(1 + t + t^3) = (t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_12 (_ht : t^4+t+1=0) : decode t (mulCode 14 12) = decode t 14*decode t 12 := by
  change (t^2) = (t + t^2 + t^3)*(t^2 + t^3)
  have h : (t + t^2 + t^3)*(t^2 + t^3) = (t^2)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_13 (_ht : t^4+t+1=0) : decode t (mulCode 14 13) = decode t 14*decode t 13 := by
  change (t + t^3) = (t + t^2 + t^3)*(1 + t^2 + t^3)
  have h : (t + t^2 + t^3)*(1 + t^2 + t^3) = (t + t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_14 (_ht : t^4+t+1=0) : decode t (mulCode 14 14) = decode t 14*decode t 14 := by
  change (1 + t + t^3) = (t + t^2 + t^3)*(t + t^2 + t^3)
  have h : (t + t^2 + t^3)*(t + t^2 + t^3) = (1 + t + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_14_15 (_ht : t^4+t+1=0) : decode t (mulCode 14 15) = decode t 14*decode t 15 := by
  change (1 + t^2) = (t + t^2 + t^3)*(1 + t + t^2 + t^3)
  have h : (t + t^2 + t^3)*(1 + t + t^2 + t^3) = (1 + t^2)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_15_0 (_ht : t^4+t+1=0) : decode t (mulCode 15 0) = decode t 15*decode t 0 := by
  change (0) = (1 + t + t^2 + t^3)*(0)
  ring
omit [CharP R 2] in
private theorem decode_mul_15_1 (_ht : t^4+t+1=0) : decode t (mulCode 15 1) = decode t 15*decode t 1 := by
  change (1 + t + t^2 + t^3) = (1 + t + t^2 + t^3)*(1)
  ring
private theorem decode_mul_15_2 (_ht : t^4+t+1=0) : decode t (mulCode 15 2) = decode t 15*decode t 2 := by
  change (1 + t^2 + t^3) = (1 + t + t^2 + t^3)*(t)
  have h : (1 + t + t^2 + t^3)*(t) = (1 + t^2 + t^3)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_3 (_ht : t^4+t+1=0) : decode t (mulCode 15 3) = decode t 15*decode t 3 := by
  change (t) = (1 + t + t^2 + t^3)*(1 + t)
  have h : (1 + t + t^2 + t^3)*(1 + t) = (t)+(t^4+t+1)*(1) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_4 (_ht : t^4+t+1=0) : decode t (mulCode 15 4) = decode t 15*decode t 4 := by
  change (1 + t^3) = (1 + t + t^2 + t^3)*(t^2)
  have h : (1 + t + t^2 + t^3)*(t^2) = (1 + t^3)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_5 (_ht : t^4+t+1=0) : decode t (mulCode 15 5) = decode t 15*decode t 5 := by
  change (t + t^2) = (1 + t + t^2 + t^3)*(1 + t^2)
  have h : (1 + t + t^2 + t^3)*(1 + t^2) = (t + t^2)+(t^4+t+1)*(1 + t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_6 (_ht : t^4+t+1=0) : decode t (mulCode 15 6) = decode t 15*decode t 6 := by
  change (t^2) = (1 + t + t^2 + t^3)*(t + t^2)
  have h : (1 + t + t^2 + t^3)*(t + t^2) = (t^2)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_7 (_ht : t^4+t+1=0) : decode t (mulCode 15 7) = decode t 15*decode t 7 := by
  change (1 + t + t^3) = (1 + t + t^2 + t^3)*(1 + t + t^2)
  have h : (1 + t + t^2 + t^3)*(1 + t + t^2) = (1 + t + t^3)+(t^4+t+1)*(t) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_8 (_ht : t^4+t+1=0) : decode t (mulCode 15 8) = decode t 15*decode t 8 := by
  change (1) = (1 + t + t^2 + t^3)*(t^3)
  have h : (1 + t + t^2 + t^3)*(t^3) = (1)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_9 (_ht : t^4+t+1=0) : decode t (mulCode 15 9) = decode t 15*decode t 9 := by
  change (t + t^2 + t^3) = (1 + t + t^2 + t^3)*(1 + t^3)
  have h : (1 + t + t^2 + t^3)*(1 + t^3) = (t + t^2 + t^3)+(t^4+t+1)*(1 + t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_10 (_ht : t^4+t+1=0) : decode t (mulCode 15 10) = decode t 15*decode t 10 := by
  change (t^2 + t^3) = (1 + t + t^2 + t^3)*(t + t^3)
  have h : (1 + t + t^2 + t^3)*(t + t^3) = (t^2 + t^3)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_11 (_ht : t^4+t+1=0) : decode t (mulCode 15 11) = decode t 15*decode t 11 := by
  change (1 + t) = (1 + t + t^2 + t^3)*(1 + t + t^3)
  have h : (1 + t + t^2 + t^3)*(1 + t + t^3) = (1 + t)+(t^4+t+1)*(t + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_12 (_ht : t^4+t+1=0) : decode t (mulCode 15 12) = decode t 15*decode t 12 := by
  change (t^3) = (1 + t + t^2 + t^3)*(t^2 + t^3)
  have h : (1 + t + t^2 + t^3)*(t^2 + t^3) = (t^3)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_13 (_ht : t^4+t+1=0) : decode t (mulCode 15 13) = decode t 15*decode t 13 := by
  change (1 + t + t^2) = (1 + t + t^2 + t^3)*(1 + t^2 + t^3)
  have h : (1 + t + t^2 + t^3)*(1 + t^2 + t^3) = (1 + t + t^2)+(t^4+t+1)*(t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_14 (_ht : t^4+t+1=0) : decode t (mulCode 15 14) = decode t 15*decode t 14 := by
  change (1 + t^2) = (1 + t + t^2 + t^3)*(t + t^2 + t^3)
  have h : (1 + t + t^2 + t^3)*(t + t^2 + t^3) = (1 + t^2)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
private theorem decode_mul_15_15 (_ht : t^4+t+1=0) : decode t (mulCode 15 15) = decode t 15*decode t 15 := by
  change (t + t^3) = (1 + t + t^2 + t^3)*(1 + t + t^2 + t^3)
  have h : (1 + t + t^2 + t^3)*(1 + t + t^2 + t^3) = (t + t^3)+(t^4+t+1)*(1 + t^2) := by
    ring_nf
    simp only [ofNat_mod]
    norm_num
  rw [h, _ht, zero_mul, add_zero]
omit [CharP R 2] in
private theorem decode_mul_row_0 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 0 j) = decode t 0*decode t j := by
  fin_cases j
  · exact decode_mul_0_0 t ht
  · exact decode_mul_0_1 t ht
  · exact decode_mul_0_2 t ht
  · exact decode_mul_0_3 t ht
  · exact decode_mul_0_4 t ht
  · exact decode_mul_0_5 t ht
  · exact decode_mul_0_6 t ht
  · exact decode_mul_0_7 t ht
  · exact decode_mul_0_8 t ht
  · exact decode_mul_0_9 t ht
  · exact decode_mul_0_10 t ht
  · exact decode_mul_0_11 t ht
  · exact decode_mul_0_12 t ht
  · exact decode_mul_0_13 t ht
  · exact decode_mul_0_14 t ht
  · exact decode_mul_0_15 t ht
omit [CharP R 2] in
private theorem decode_mul_row_1 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 1 j) = decode t 1*decode t j := by
  fin_cases j
  · exact decode_mul_1_0 t ht
  · exact decode_mul_1_1 t ht
  · exact decode_mul_1_2 t ht
  · exact decode_mul_1_3 t ht
  · exact decode_mul_1_4 t ht
  · exact decode_mul_1_5 t ht
  · exact decode_mul_1_6 t ht
  · exact decode_mul_1_7 t ht
  · exact decode_mul_1_8 t ht
  · exact decode_mul_1_9 t ht
  · exact decode_mul_1_10 t ht
  · exact decode_mul_1_11 t ht
  · exact decode_mul_1_12 t ht
  · exact decode_mul_1_13 t ht
  · exact decode_mul_1_14 t ht
  · exact decode_mul_1_15 t ht
private theorem decode_mul_row_2 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 2 j) = decode t 2*decode t j := by
  fin_cases j
  · exact decode_mul_2_0 t ht
  · exact decode_mul_2_1 t ht
  · exact decode_mul_2_2 t ht
  · exact decode_mul_2_3 t ht
  · exact decode_mul_2_4 t ht
  · exact decode_mul_2_5 t ht
  · exact decode_mul_2_6 t ht
  · exact decode_mul_2_7 t ht
  · exact decode_mul_2_8 t ht
  · exact decode_mul_2_9 t ht
  · exact decode_mul_2_10 t ht
  · exact decode_mul_2_11 t ht
  · exact decode_mul_2_12 t ht
  · exact decode_mul_2_13 t ht
  · exact decode_mul_2_14 t ht
  · exact decode_mul_2_15 t ht
private theorem decode_mul_row_3 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 3 j) = decode t 3*decode t j := by
  fin_cases j
  · exact decode_mul_3_0 t ht
  · exact decode_mul_3_1 t ht
  · exact decode_mul_3_2 t ht
  · exact decode_mul_3_3 t ht
  · exact decode_mul_3_4 t ht
  · exact decode_mul_3_5 t ht
  · exact decode_mul_3_6 t ht
  · exact decode_mul_3_7 t ht
  · exact decode_mul_3_8 t ht
  · exact decode_mul_3_9 t ht
  · exact decode_mul_3_10 t ht
  · exact decode_mul_3_11 t ht
  · exact decode_mul_3_12 t ht
  · exact decode_mul_3_13 t ht
  · exact decode_mul_3_14 t ht
  · exact decode_mul_3_15 t ht
private theorem decode_mul_row_4 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 4 j) = decode t 4*decode t j := by
  fin_cases j
  · exact decode_mul_4_0 t ht
  · exact decode_mul_4_1 t ht
  · exact decode_mul_4_2 t ht
  · exact decode_mul_4_3 t ht
  · exact decode_mul_4_4 t ht
  · exact decode_mul_4_5 t ht
  · exact decode_mul_4_6 t ht
  · exact decode_mul_4_7 t ht
  · exact decode_mul_4_8 t ht
  · exact decode_mul_4_9 t ht
  · exact decode_mul_4_10 t ht
  · exact decode_mul_4_11 t ht
  · exact decode_mul_4_12 t ht
  · exact decode_mul_4_13 t ht
  · exact decode_mul_4_14 t ht
  · exact decode_mul_4_15 t ht
private theorem decode_mul_row_5 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 5 j) = decode t 5*decode t j := by
  fin_cases j
  · exact decode_mul_5_0 t ht
  · exact decode_mul_5_1 t ht
  · exact decode_mul_5_2 t ht
  · exact decode_mul_5_3 t ht
  · exact decode_mul_5_4 t ht
  · exact decode_mul_5_5 t ht
  · exact decode_mul_5_6 t ht
  · exact decode_mul_5_7 t ht
  · exact decode_mul_5_8 t ht
  · exact decode_mul_5_9 t ht
  · exact decode_mul_5_10 t ht
  · exact decode_mul_5_11 t ht
  · exact decode_mul_5_12 t ht
  · exact decode_mul_5_13 t ht
  · exact decode_mul_5_14 t ht
  · exact decode_mul_5_15 t ht
private theorem decode_mul_row_6 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 6 j) = decode t 6*decode t j := by
  fin_cases j
  · exact decode_mul_6_0 t ht
  · exact decode_mul_6_1 t ht
  · exact decode_mul_6_2 t ht
  · exact decode_mul_6_3 t ht
  · exact decode_mul_6_4 t ht
  · exact decode_mul_6_5 t ht
  · exact decode_mul_6_6 t ht
  · exact decode_mul_6_7 t ht
  · exact decode_mul_6_8 t ht
  · exact decode_mul_6_9 t ht
  · exact decode_mul_6_10 t ht
  · exact decode_mul_6_11 t ht
  · exact decode_mul_6_12 t ht
  · exact decode_mul_6_13 t ht
  · exact decode_mul_6_14 t ht
  · exact decode_mul_6_15 t ht
private theorem decode_mul_row_7 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 7 j) = decode t 7*decode t j := by
  fin_cases j
  · exact decode_mul_7_0 t ht
  · exact decode_mul_7_1 t ht
  · exact decode_mul_7_2 t ht
  · exact decode_mul_7_3 t ht
  · exact decode_mul_7_4 t ht
  · exact decode_mul_7_5 t ht
  · exact decode_mul_7_6 t ht
  · exact decode_mul_7_7 t ht
  · exact decode_mul_7_8 t ht
  · exact decode_mul_7_9 t ht
  · exact decode_mul_7_10 t ht
  · exact decode_mul_7_11 t ht
  · exact decode_mul_7_12 t ht
  · exact decode_mul_7_13 t ht
  · exact decode_mul_7_14 t ht
  · exact decode_mul_7_15 t ht
private theorem decode_mul_row_8 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 8 j) = decode t 8*decode t j := by
  fin_cases j
  · exact decode_mul_8_0 t ht
  · exact decode_mul_8_1 t ht
  · exact decode_mul_8_2 t ht
  · exact decode_mul_8_3 t ht
  · exact decode_mul_8_4 t ht
  · exact decode_mul_8_5 t ht
  · exact decode_mul_8_6 t ht
  · exact decode_mul_8_7 t ht
  · exact decode_mul_8_8 t ht
  · exact decode_mul_8_9 t ht
  · exact decode_mul_8_10 t ht
  · exact decode_mul_8_11 t ht
  · exact decode_mul_8_12 t ht
  · exact decode_mul_8_13 t ht
  · exact decode_mul_8_14 t ht
  · exact decode_mul_8_15 t ht
private theorem decode_mul_row_9 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 9 j) = decode t 9*decode t j := by
  fin_cases j
  · exact decode_mul_9_0 t ht
  · exact decode_mul_9_1 t ht
  · exact decode_mul_9_2 t ht
  · exact decode_mul_9_3 t ht
  · exact decode_mul_9_4 t ht
  · exact decode_mul_9_5 t ht
  · exact decode_mul_9_6 t ht
  · exact decode_mul_9_7 t ht
  · exact decode_mul_9_8 t ht
  · exact decode_mul_9_9 t ht
  · exact decode_mul_9_10 t ht
  · exact decode_mul_9_11 t ht
  · exact decode_mul_9_12 t ht
  · exact decode_mul_9_13 t ht
  · exact decode_mul_9_14 t ht
  · exact decode_mul_9_15 t ht
private theorem decode_mul_row_10 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 10 j) = decode t 10*decode t j := by
  fin_cases j
  · exact decode_mul_10_0 t ht
  · exact decode_mul_10_1 t ht
  · exact decode_mul_10_2 t ht
  · exact decode_mul_10_3 t ht
  · exact decode_mul_10_4 t ht
  · exact decode_mul_10_5 t ht
  · exact decode_mul_10_6 t ht
  · exact decode_mul_10_7 t ht
  · exact decode_mul_10_8 t ht
  · exact decode_mul_10_9 t ht
  · exact decode_mul_10_10 t ht
  · exact decode_mul_10_11 t ht
  · exact decode_mul_10_12 t ht
  · exact decode_mul_10_13 t ht
  · exact decode_mul_10_14 t ht
  · exact decode_mul_10_15 t ht
private theorem decode_mul_row_11 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 11 j) = decode t 11*decode t j := by
  fin_cases j
  · exact decode_mul_11_0 t ht
  · exact decode_mul_11_1 t ht
  · exact decode_mul_11_2 t ht
  · exact decode_mul_11_3 t ht
  · exact decode_mul_11_4 t ht
  · exact decode_mul_11_5 t ht
  · exact decode_mul_11_6 t ht
  · exact decode_mul_11_7 t ht
  · exact decode_mul_11_8 t ht
  · exact decode_mul_11_9 t ht
  · exact decode_mul_11_10 t ht
  · exact decode_mul_11_11 t ht
  · exact decode_mul_11_12 t ht
  · exact decode_mul_11_13 t ht
  · exact decode_mul_11_14 t ht
  · exact decode_mul_11_15 t ht
private theorem decode_mul_row_12 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 12 j) = decode t 12*decode t j := by
  fin_cases j
  · exact decode_mul_12_0 t ht
  · exact decode_mul_12_1 t ht
  · exact decode_mul_12_2 t ht
  · exact decode_mul_12_3 t ht
  · exact decode_mul_12_4 t ht
  · exact decode_mul_12_5 t ht
  · exact decode_mul_12_6 t ht
  · exact decode_mul_12_7 t ht
  · exact decode_mul_12_8 t ht
  · exact decode_mul_12_9 t ht
  · exact decode_mul_12_10 t ht
  · exact decode_mul_12_11 t ht
  · exact decode_mul_12_12 t ht
  · exact decode_mul_12_13 t ht
  · exact decode_mul_12_14 t ht
  · exact decode_mul_12_15 t ht
private theorem decode_mul_row_13 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 13 j) = decode t 13*decode t j := by
  fin_cases j
  · exact decode_mul_13_0 t ht
  · exact decode_mul_13_1 t ht
  · exact decode_mul_13_2 t ht
  · exact decode_mul_13_3 t ht
  · exact decode_mul_13_4 t ht
  · exact decode_mul_13_5 t ht
  · exact decode_mul_13_6 t ht
  · exact decode_mul_13_7 t ht
  · exact decode_mul_13_8 t ht
  · exact decode_mul_13_9 t ht
  · exact decode_mul_13_10 t ht
  · exact decode_mul_13_11 t ht
  · exact decode_mul_13_12 t ht
  · exact decode_mul_13_13 t ht
  · exact decode_mul_13_14 t ht
  · exact decode_mul_13_15 t ht
private theorem decode_mul_row_14 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 14 j) = decode t 14*decode t j := by
  fin_cases j
  · exact decode_mul_14_0 t ht
  · exact decode_mul_14_1 t ht
  · exact decode_mul_14_2 t ht
  · exact decode_mul_14_3 t ht
  · exact decode_mul_14_4 t ht
  · exact decode_mul_14_5 t ht
  · exact decode_mul_14_6 t ht
  · exact decode_mul_14_7 t ht
  · exact decode_mul_14_8 t ht
  · exact decode_mul_14_9 t ht
  · exact decode_mul_14_10 t ht
  · exact decode_mul_14_11 t ht
  · exact decode_mul_14_12 t ht
  · exact decode_mul_14_13 t ht
  · exact decode_mul_14_14 t ht
  · exact decode_mul_14_15 t ht
private theorem decode_mul_row_15 (ht : t^4+t+1=0) (j : Code) : decode t (mulCode 15 j) = decode t 15*decode t j := by
  fin_cases j
  · exact decode_mul_15_0 t ht
  · exact decode_mul_15_1 t ht
  · exact decode_mul_15_2 t ht
  · exact decode_mul_15_3 t ht
  · exact decode_mul_15_4 t ht
  · exact decode_mul_15_5 t ht
  · exact decode_mul_15_6 t ht
  · exact decode_mul_15_7 t ht
  · exact decode_mul_15_8 t ht
  · exact decode_mul_15_9 t ht
  · exact decode_mul_15_10 t ht
  · exact decode_mul_15_11 t ht
  · exact decode_mul_15_12 t ht
  · exact decode_mul_15_13 t ht
  · exact decode_mul_15_14 t ht
  · exact decode_mul_15_15 t ht
theorem decode_mul (ht : t^4+t+1=0) (i j : Code) : decode t (mulCode i j) = decode t i*decode t j := by
  fin_cases i
  · exact decode_mul_row_0 t ht j
  · exact decode_mul_row_1 t ht j
  · exact decode_mul_row_2 t ht j
  · exact decode_mul_row_3 t ht j
  · exact decode_mul_row_4 t ht j
  · exact decode_mul_row_5 t ht j
  · exact decode_mul_row_6 t ht j
  · exact decode_mul_row_7 t ht j
  · exact decode_mul_row_8 t ht j
  · exact decode_mul_row_9 t ht j
  · exact decode_mul_row_10 t ht j
  · exact decode_mul_row_11 t ht j
  · exact decode_mul_row_12 t ht j
  · exact decode_mul_row_13 t ht j
  · exact decode_mul_row_14 t ht j
  · exact decode_mul_row_15 t ht j
end Algebra

private theorem codeDot_row_0 : ∀ j : Fin 32, codeDot 0 (j : Fin 32) = if (0 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_1 : ∀ j : Fin 32, codeDot 1 (j : Fin 32) = if (1 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_2 : ∀ j : Fin 32, codeDot 2 (j : Fin 32) = if (2 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_3 : ∀ j : Fin 32, codeDot 3 (j : Fin 32) = if (3 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_4 : ∀ j : Fin 32, codeDot 4 (j : Fin 32) = if (4 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_5 : ∀ j : Fin 32, codeDot 5 (j : Fin 32) = if (5 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_6 : ∀ j : Fin 32, codeDot 6 (j : Fin 32) = if (6 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_7 : ∀ j : Fin 32, codeDot 7 (j : Fin 32) = if (7 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_8 : ∀ j : Fin 32, codeDot 8 (j : Fin 32) = if (8 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_9 : ∀ j : Fin 32, codeDot 9 (j : Fin 32) = if (9 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_10 : ∀ j : Fin 32, codeDot 10 (j : Fin 32) = if (10 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_11 : ∀ j : Fin 32, codeDot 11 (j : Fin 32) = if (11 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_12 : ∀ j : Fin 32, codeDot 12 (j : Fin 32) = if (12 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_13 : ∀ j : Fin 32, codeDot 13 (j : Fin 32) = if (13 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_14 : ∀ j : Fin 32, codeDot 14 (j : Fin 32) = if (14 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_15 : ∀ j : Fin 32, codeDot 15 (j : Fin 32) = if (15 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_16 : ∀ j : Fin 32, codeDot 16 (j : Fin 32) = if (16 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_17 : ∀ j : Fin 32, codeDot 17 (j : Fin 32) = if (17 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_18 : ∀ j : Fin 32, codeDot 18 (j : Fin 32) = if (18 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_19 : ∀ j : Fin 32, codeDot 19 (j : Fin 32) = if (19 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_20 : ∀ j : Fin 32, codeDot 20 (j : Fin 32) = if (20 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_21 : ∀ j : Fin 32, codeDot 21 (j : Fin 32) = if (21 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_22 : ∀ j : Fin 32, codeDot 22 (j : Fin 32) = if (22 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_23 : ∀ j : Fin 32, codeDot 23 (j : Fin 32) = if (23 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_24 : ∀ j : Fin 32, codeDot 24 (j : Fin 32) = if (24 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_25 : ∀ j : Fin 32, codeDot 25 (j : Fin 32) = if (25 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_26 : ∀ j : Fin 32, codeDot 26 (j : Fin 32) = if (26 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_27 : ∀ j : Fin 32, codeDot 27 (j : Fin 32) = if (27 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_28 : ∀ j : Fin 32, codeDot 28 (j : Fin 32) = if (28 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_29 : ∀ j : Fin 32, codeDot 29 (j : Fin 32) = if (29 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_30 : ∀ j : Fin 32, codeDot 30 (j : Fin 32) = if (30 : Fin 32)=j then 1 else 0 := by decide +kernel
private theorem codeDot_row_31 : ∀ j : Fin 32, codeDot 31 (j : Fin 32) = if (31 : Fin 32)=j then 1 else 0 := by decide +kernel
theorem codeDot_eq (i j : Fin 32) : codeDot i j = if i=j then 1 else 0 := by
  fin_cases i
  · exact codeDot_row_0 j
  · exact codeDot_row_1 j
  · exact codeDot_row_2 j
  · exact codeDot_row_3 j
  · exact codeDot_row_4 j
  · exact codeDot_row_5 j
  · exact codeDot_row_6 j
  · exact codeDot_row_7 j
  · exact codeDot_row_8 j
  · exact codeDot_row_9 j
  · exact codeDot_row_10 j
  · exact codeDot_row_11 j
  · exact codeDot_row_12 j
  · exact codeDot_row_13 j
  · exact codeDot_row_14 j
  · exact codeDot_row_15 j
  · exact codeDot_row_16 j
  · exact codeDot_row_17 j
  · exact codeDot_row_18 j
  · exact codeDot_row_19 j
  · exact codeDot_row_20 j
  · exact codeDot_row_21 j
  · exact codeDot_row_22 j
  · exact codeDot_row_23 j
  · exact codeDot_row_24 j
  · exact codeDot_row_25 j
  · exact codeDot_row_26 j
  · exact codeDot_row_27 j
  · exact codeDot_row_28 j
  · exact codeDot_row_29 j
  · exact codeDot_row_30 j
  · exact codeDot_row_31 j
section Consequences
variable {R : Type*} [CommRing R] [CharP R 2] (t : R)

theorem decode_codeSum (xs : List Code) :
    decode t (codeSum xs) = (xs.map (decode t)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [codeSum, decode_add, List.map_cons, List.sum_cons, ih]

theorem matrix_mul_inverse_apply (ht : t^4+t+1=0) (i j : Fin 32) :
    (matrix t * inverseMatrix t) i j = decode t (codeDot i j) := by
  simp only [codeDot, decode_codeSum, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, decode_mul t ht, Matrix.mul_apply, matrix, inverseMatrix]

/-- The literal specialized matrix has the displayed explicit inverse. -/
theorem matrix_mul_inverse (ht : t^4+t+1=0) : matrix t * inverseMatrix t = 1 := by
  ext i j
  rw [matrix_mul_inverse_apply t ht, codeDot_eq]
  change decode t (if i=j then 1 else 0) = (if i=j then (1:R) else 0)
  split_ifs <;> rfl

/-- The fixed specialized determinant is nonzero over any nontrivial ring with this root. -/
theorem det_matrix_ne_zero [Nontrivial R] (ht : t^4+t+1=0) : (matrix t).det ≠ 0 := by
  have h := congrArg Matrix.det (matrix_mul_inverse t ht)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- Entrywise Frobenius square, retaining the matrix type. -/
def squareMatrix : Matrix (Fin 32) (Fin 32) R :=
  Matrix.of fun i j => (matrix t i j)^2

def squareInverseMatrix : Matrix (Fin 32) (Fin 32) R :=
  Matrix.of fun i j => (inverseMatrix t i j)^2

/-- Entrywise squaring preserves the explicit inverse identity in characteristic two. -/
theorem square_matrix_mul_inverse (ht : t^4+t+1=0) :
    squareMatrix t * squareInverseMatrix t = 1 := by
  have h := congrArg (fun M : Matrix (Fin 32) (Fin 32) R => M.map (frobenius R 2))
    (matrix_mul_inverse t ht)
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h

/-- The squared matrix needed for the final differential rows also has nonzero determinant. -/
theorem det_square_matrix_ne_zero [Nontrivial R] (ht : t^4+t+1=0) :
    (squareMatrix t).det ≠ 0 := by
  have h := congrArg Matrix.det (square_matrix_mul_inverse t ht)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

end Consequences

/-- A concrete nontrivial ring containing the required quartic root. -/
def modulus : Polynomial (ZMod 2) := Polynomial.X^4+Polynomial.X+1
abbrev RootRing := AdjoinRoot modulus

instance : Nontrivial RootRing := by
  apply AdjoinRoot.nontrivial modulus
  have hc : modulus.coeff 4 ≠ 0 := by
    norm_num [modulus, Polynomial.coeff_X, Polynomial.coeff_one]
  have hd := Polynomial.le_degree_of_ne_zero hc
  intro hz
  rw [hz] at hd
  norm_num at hd

instance : CharP RootRing 2 :=
  CharP.of_ringHom_of_ne_zero (AdjoinRoot.of modulus) 2 (by decide)

def root : RootRing := AdjoinRoot.root modulus

theorem root_relation : root^4+root+1=0 := by
  have h := AdjoinRoot.mk_self (f := modulus)
  change (AdjoinRoot.mk modulus) (Polynomial.X^4+Polynomial.X+1) = 0 at h
  simpa only [root, map_add, map_pow, map_one, AdjoinRoot.mk_X] using h

theorem specialized_det_ne_zero : (matrix root).det ≠ 0 :=
  det_matrix_ne_zero root root_relation

theorem specialized_square_det_ne_zero :
    (squareMatrix root).det ≠ 0 :=
  det_square_matrix_ne_zero root root_relation
end TernaryPoly.OrbitMinorCertificate
