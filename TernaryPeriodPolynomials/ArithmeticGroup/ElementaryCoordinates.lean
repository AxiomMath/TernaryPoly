module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Finsupp.Notation
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

variable {R : Type*} [CommRing R]

private theorem rename_eq_bind_three (φ : Fin 3 → Fin 3) (f : MvPolynomial (Fin 3) R) :
    rename φ f = bind₁ ![X (φ 0),X (φ 1),X (φ 2)] f := by
  have h : (rename φ : MvPolynomial (Fin 3) R →ₐ[R] _) = bind₁ ![X (φ 0),X (φ 1),X (φ 2)] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact DFunLike.congr_fun h f

/-- Literal cyclic and swap invariance generate all ternary permutations, over any ring. -/
theorem isSymmetric_of_cyclic_swap {f : MvPolynomial (Fin 3) R}
    (hc : bind₁ ![X 1,X 2,X 0] f = f) (hs : bind₁ ![X 1,X 0,X 2] f = f) :
    f.IsSymmetric := by
  have hcomp (φ ψ : Fin 3 → Fin 3) (hφ : rename φ f = f) (hψ : rename ψ f = f) :
      rename (φ ∘ ψ) f = f := by rw [← rename_rename,hψ,hφ]
  have hc' : rename (![1,2,0] : Fin 3 → Fin 3) f = f := by
    simpa only [rename_eq_bind_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hc
  have hs' : rename (![1,0,2] : Fin 3 → Fin 3) f = f := by
    simpa only [rename_eq_bind_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hs
  have hcc : bind₁ ![X 2,X 0,X 1] f = f := by
    have h := hcomp _ _ hc' hc'
    simpa [rename_eq_bind_three,Function.comp_def] using h
  have hcs : bind₁ ![X 2,X 1,X 0] f = f := by
    have h := hcomp _ _ hc' hs'
    simpa [rename_eq_bind_three,Function.comp_def] using h
  have hsc : bind₁ ![X 0,X 2,X 1] f = f := by
    have h := hcomp _ _ hs' hc'
    simpa [rename_eq_bind_three,Function.comp_def] using h
  have hi : bind₁ ![X 0,X 1,X 2] f = f := by
    have hv : (![X 0,X 1,X 2] : Fin 3 → MvPolynomial (Fin 3) R) = X := by
      funext i; fin_cases i <;> rfl
    simp only [hv,bind₁_X_left,AlgHom.id_apply]
  intro σ
  rw [rename_eq_bind_three]
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  generalize h0 : σ 0 = i0 at *
  generalize h1 : σ 1 = i1 at *
  generalize h2 : σ 2 = i2 at *
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp_all

/-- Elementary-coordinate evaluation over any coefficient ring. -/
def ternaryElementaryEval : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  bind₁ ![X 0+X 1+X 2, X 0*X 1+X 0*X 2+X 1*X 2, X 0*X 1*X 2]

private theorem esymm_two_three : esymm (Fin 3) R 2 = X 0*X 1+X 0*X 2+X 1*X 2 := by
  have h : (Finset.univ : Finset (Fin 3)).powersetCard 2 = {{0,1},{0,2},{1,2}} := by decide
  rw [esymm,h]
  have h01 : ({0,1} : Finset (Fin 3)) ∉ ({{0,2},{1,2}} : Finset (Finset (Fin 3))) := by decide
  have h02 : ({0,2} : Finset (Fin 3)) ∉ ({{1,2}} : Finset (Finset (Fin 3))) := by decide
  rw [Finset.sum_insert h01,Finset.sum_insert h02,Finset.sum_singleton]
  simp
  ring

private theorem esymm_three_three : esymm (Fin 3) R 3 = X 0*X 1*X 2 := by
  have h : (Finset.univ : Finset (Fin 3)).powersetCard 3 = {{0,1,2}} := by decide
  rw [esymm,h]
  simp [mul_assoc]

private theorem esymmAlgHom_eq_ternaryElementaryEval (p : MvPolynomial (Fin 3) R) :
    ((esymmAlgHom (Fin 3) R 3 p : symmetricSubalgebra (Fin 3) R) : MvPolynomial (Fin 3) R) =
      ternaryElementaryEval p := by
  rw [esymmAlgHom_apply,aeval_eq_bind₁]
  unfold ternaryElementaryEval
  congr 2
  funext i
  fin_cases i
  · simp [esymm_one,Fin.sum_univ_three]
  · exact esymm_two_three
  · exact esymm_three_three

theorem ternaryElementaryEval_injective : Function.Injective (ternaryElementaryEval (R := R)) := by
  intro p q hpq
  apply (esymmAlgHom_fin_bijective R 3).1
  apply Subtype.ext
  simpa only [esymmAlgHom_eq_ternaryElementaryEval] using hpq

/-- Integer symmetric polynomials therefore admit genuine integer elementary-coordinate lifts. -/
theorem exists_ternaryElementaryEval {f : MvPolynomial (Fin 3) R} (hs : f.IsSymmetric) :
    ∃ p, ternaryElementaryEval p = f := by
  obtain ⟨p,hp⟩ := (esymmAlgHom_fin_bijective R 3).2 ⟨f,hs⟩
  refine ⟨p,?_⟩
  have h := congrArg (fun g : symmetricSubalgebra (Fin 3) R => (g : MvPolynomial (Fin 3) R)) hp
  simpa only [esymmAlgHom_eq_ternaryElementaryEval] using h

/-- Elementary coordinates commute with every coefficient-ring homomorphism. -/
theorem map_ternaryElementaryEval {S : Type*} [CommRing S] (φ : R →+* S)
    (p : MvPolynomial (Fin 3) R) :
    map φ (ternaryElementaryEval p) = ternaryElementaryEval (map φ p) := by
  rw [ternaryElementaryEval,map_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

end TernaryPoly
