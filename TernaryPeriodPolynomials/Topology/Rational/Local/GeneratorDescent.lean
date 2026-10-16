module

public import TernaryPeriodPolynomials.Topology.Rational.Local.HomologyTotal

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLocalMap
open CategoryTheory HomologicalComplex RationalLocalChartHomology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X]

/-- Each fiber contains an actual pushed local class when the local homeomorphism is surjective. -/
theorem exists_pushed_local_class (p : C(X,Y)) (hp : IsLocalHomeomorph p)
    (hs : Function.Surjective p) (k : ℕ) (o : ∀ x : X, (localChains x).homology k) (y : Y) :
    ∃ c : (localChains y).homology k, ∃ x : X,
      totalLocalMap p hp k ⟨x,o x⟩ = (⟨y,c⟩ : LocalHomologyTotal Y k) := by
  obtain ⟨x,rfl⟩ := hs y
  exact ⟨localHomeomorphMap p hp x k (o x),x,rfl⟩

/-- A pointwise descended generator selected from an actual lifted point. Independence and
local representability must be supplied by the corresponding theorems. -/
def descendedGenerator (p : C(X,Y)) (hp : IsLocalHomeomorph p)
    (hs : Function.Surjective p) (k : ℕ) (o : ∀ x : X, (localChains x).homology k) (y : Y) :
    (localChains y).homology k :=
  (exists_pushed_local_class p hp hs k o y).choose

/-- Fiberwise equality of pushed total classes proves the exact descent formula for every lift. -/
theorem descendedGenerator_total (p : C(X,Y)) (hp : IsLocalHomeomorph p)
    (hs : Function.Surjective p) (k : ℕ) (o : ∀ x : X, (localChains x).homology k)
    (hinv : ∀ x x', p x = p x' → totalLocalMap p hp k ⟨x,o x⟩ = totalLocalMap p hp k ⟨x',o x'⟩)
    (x : X) : totalLocalMap p hp k ⟨x,o x⟩ =
      (⟨p x,descendedGenerator p hp hs k o (p x)⟩ : LocalHomologyTotal Y k) := by
  obtain ⟨x',he⟩ := (exists_pushed_local_class p hp hs k o (p x)).choose_spec
  have hb : p x' = p x := congrArg Sigma.fst he
  exact (hinv x x' hb.symm).trans he

/-- The actual local homology map at every lift gives the descended generator. -/
theorem descendedGenerator_apply (p : C(X,Y)) (hp : IsLocalHomeomorph p)
    (hs : Function.Surjective p) (k : ℕ) (o : ∀ x : X, (localChains x).homology k)
    (hinv : ∀ x x', p x = p x' → totalLocalMap p hp k ⟨x,o x⟩ = totalLocalMap p hp k ⟨x',o x'⟩)
    (x : X) : localHomeomorphMap p hp x k (o x) = descendedGenerator p hp hs k o (p x) := by
  exact eq_of_heq (Sigma.mk.inj (descendedGenerator_total p hp hs k o hinv x)).2

variable [T1Space Y]

/-- A fiber-independent descended family of nonzero actual generators remains nonzero. -/
theorem descendedGenerator_ne_zero (p : C(X,Y)) (hp : IsLocalHomeomorph p)
    (hs : Function.Surjective p) (k : ℕ) (o : ∀ x : X, (localChains x).homology k)
    (hinv : ∀ x x', p x = p x' → totalLocalMap p hp k ⟨x,o x⟩ = totalLocalMap p hp k ⟨x',o x'⟩)
    (ho : ∀ x, o x ≠ 0) (y : Y) : descendedGenerator p hp hs k o y ≠ 0 := by
  obtain ⟨x,rfl⟩ := hs y
  rw [← descendedGenerator_apply p hp hs k o hinv x]
  intro he
  apply ho x
  apply (ModuleCat.mono_iff_injective (localHomeomorphMap p hp x k)).mp inferInstance
  simpa using he

end TernaryPoly.RationalLocalMap
