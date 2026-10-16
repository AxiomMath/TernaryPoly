module

public import TernaryPeriodPolynomials.Topology.Rational.Local.Homeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLocalMap
open CategoryTheory HomologicalComplex
open RationalLocalChartHomology
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The disjoint union of the actual point-local homology groups. No topology is asserted here. -/
abbrev LocalHomologyTotal (X : Type) [TopologicalSpace X] (k : ℕ) :=
  Σ x : X, (localChains x).homology k

variable [T1Space X]

/-- The actual induced map on the disjoint union of point-local homology groups. -/
def totalLocalMap (f : C(X,Y)) (hf : IsLocalHomeomorph f) (k : ℕ) :
    LocalHomologyTotal X k → LocalHomologyTotal Y k :=
  fun z => ⟨f z.1,localHomeomorphMap f hf z.1 k z.2⟩

variable [T1Space Y]

/-- The actual total local-homology maps compose, including their base points. -/
theorem totalLocalMap_comp (f : C(X,Y)) (g : C(Y,Z))
    (hf : IsLocalHomeomorph f) (hg : IsLocalHomeomorph g) (k : ℕ) (z : LocalHomologyTotal X k) :
    totalLocalMap g hg k (totalLocalMap f hf k z) = totalLocalMap (g.comp f) (hg.comp hf) k z := by
  rcases z with ⟨x,c⟩
  unfold totalLocalMap
  apply congrArg (Sigma.mk (g (f x)))
  exact congrArg (fun h => h c) (localHomeomorphMap_comp f g hf hg x k)

omit [T1Space Y] in
/-- A generator family preserved by a deck homeomorphism has identical pushed total classes.
This statement records equality of both the point and its genuine local homology class. -/
theorem totalLocalMap_deck (p : C(X,Y)) (hp : IsLocalHomeomorph p) (e : X ≃ₜ X)
    (hpe : p.comp ⟨e,e.continuous⟩ = p) (k : ℕ)
    (o : ∀ x : X, (localChains x).homology k)
    (ho : ∀ x, homologyMap (homeomorphLocalIso e x).hom k (o x) = o (e x)) (x : X) :
    totalLocalMap p hp k ⟨e x,o (e x)⟩ = totalLocalMap p hp k ⟨x,o x⟩ := by
  have he : totalLocalMap (⟨e,e.continuous⟩ : C(X,X)) e.isLocalHomeomorph k ⟨x,o x⟩ =
      (⟨e x,o (e x)⟩ : LocalHomologyTotal X k) := by
    unfold totalLocalMap
    apply congrArg (Sigma.mk (e x))
    exact (congrArg (fun f => f (o x)) (localHomeomorphMap_homeomorph e x k)).trans (ho x)
  rw [← he,totalLocalMap_comp]
  simp only [hpe]

end TernaryPoly.RationalLocalMap
