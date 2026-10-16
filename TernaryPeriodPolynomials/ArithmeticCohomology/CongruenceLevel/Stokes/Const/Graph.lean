module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.CoordRes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Orbits

@[expose] public section


/-!
# Connectivity of the orbit incidence graph of `Γ(6)`

Formalized by Claude Sonnet 5.5.

The bipartite graph whose vertices are the `Γ(6)`-orbits of rational lines and of rational planes and whose edges are the `Γ(6)`-orbits of complete flags is connected: it is the quotient of the
connected incidence graph of rational lines and planes (two lines span a plane, two planes meet in a line).  Consequently an assignment of a value to each line orbit and to each plane orbit which is
compatible with every flag orbit is constant (`orbit_invariant_const`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

/-- A value on every rational line and every rational plane which agrees at the two ends of every flag is constant on the vertices of the incidence graph. -/
theorem vertex_invariant_const {X : Type} (f : Line → X) (g : Plane → X)
    (h : ∀ F : Flag, f F.val.1 = g F.val.2) (u v : Line ⊕ Plane) :
    Sum.elim f g u = Sum.elim f g v := by
  obtain ⟨p⟩ := TernaryPoly.OrdinaryIncidence.connected.preconnected u v
  induction p with
  | nil => rfl
  | @cons a b c hadj _ ih =>
    refine Eq.trans ?_ ih
    cases a <;> cases b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact absurd hadj (by intro h; exact h)
    · exact h ⟨(_, _), hadj⟩
    · exact (h ⟨(_, _), hadj⟩).symm
    · exact absurd hadj (by intro h; exact h)

/-- **The orbit incidence graph is connected.**  If `f` on the `Γ(6)`-orbits of lines and `g` on the `Γ(6)`-orbits of planes agree at the two orbits of every flag, then all values of `f` and `g` are
equal. -/
theorem orbit_invariant_const {X : Type} (f : labelOrbits Γ6 Line → X) (g : labelOrbits Γ6 Plane → X)
    (h : ∀ F : Flag, f (Quotient.mk'' F.val.1) = g (Quotient.mk'' F.val.2)) :
    (∀ a b, f a = f b) ∧ (∀ a b, g a = g b) ∧ ∀ a b, f a = g b := by
  have key := vertex_invariant_const (fun L : Line => f (Quotient.mk'' L)) (fun P : Plane => g (Quotient.mk'' P)) h
  have hL : ∀ a b, f a = f b := by
    intro a b
    have := key (Sum.inl a.out) (Sum.inl b.out)
    simpa using this
  have hP : ∀ a b, g a = g b := by
    intro a b
    have := key (Sum.inr a.out) (Sum.inr b.out)
    simpa using this
  refine ⟨hL, hP, fun a b => ?_⟩
  have := key (Sum.inl a.out) (Sum.inr b.out)
  simpa using this

end TernaryPeriodPolynomials.Argument.GammaNStokes
