module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Topology.WithTopology

@[expose] public section




/-! Genuine finite adeles and coordinate maps for the rational GL3 boundary comparison. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open IsDedekindDomain Matrix

abbrev FiniteAdeles := FiniteAdeleRing ℤ ℚ
abbrev FinitePlace := HeightOneSpectrum ℤ
abbrev FiniteGL := GeneralLinearGroup (Fin 3) FiniteAdeles
abbrev RationalGL := GeneralLinearGroup (Fin 3) ℚ
abbrev IntegralGL := GeneralLinearGroup (Fin 3) ℤ

def finiteEvaluation (v : FinitePlace) : FiniteAdeles →+* v.adicCompletion ℚ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def rationalFinite : RationalGL →* FiniteGL :=
  GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)

def integralRational : IntegralGL →* RationalGL :=
  GeneralLinearGroup.map (Int.castRingHom ℚ)

def integralFinite : IntegralGL →* FiniteGL := rationalFinite.comp integralRational

def finiteGLAt (v : FinitePlace) : FiniteGL →* GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ) :=
  GeneralLinearGroup.map (finiteEvaluation v)

@[simp] theorem finiteEvaluation_rational (v : FinitePlace) (q : ℚ) :
    finiteEvaluation v (algebraMap ℚ FiniteAdeles q) = algebraMap ℚ (v.adicCompletion ℚ) q :=
  RingHom.map_rat_algebraMap (finiteEvaluation v) q

@[simp] theorem rationalFinite_entry (g : RationalGL) (v : FinitePlace) (i j : Fin 3) :
    finiteEvaluation v ((rationalFinite g).val i j) = algebraMap ℚ (v.adicCompletion ℚ) (g.val i j) :=
  finiteEvaluation_rational v (g.val i j)

end GeneralEisenstein.Adelic

end
