module

public import TernaryPeriodPolynomials.Building.BadVertex.LinkFilling
public import TernaryPeriodPolynomials.Building.BadVertex.SimplexNormalForm
public import TernaryPeriodPolynomials.Building.AugmentedFrame.PrismCaps

@[expose] public section


/-!
# Lemma A.1: the bad-vertex link `L_b` and its sphere families (definitions)

Formalized by Claude Sonnet 5.5.
Paper: Lemma A.1
(`lem:bad-link-generators`) and the setup of Appendix A.2.

Dictionary between the library and the paper.

* `badLink b = TernaryPoly.GoodLinkExtraction.augmentedGoodLink {b}` is the good link
  `L_b = lk_X(b^±) ∩ Y` inside `TernaryPoly.AugmentedFrameComplex.ambient` (the partial
  augmented-frame complex `X`), for a bad line `b`.  A face is a nonempty finite set of Good
  lines `s` with `{b} ∪ s ∈ ambient`.  Chains are `OrientedListChains.chains (badLink b) n`, where
  `n` is the number of vertices of a simplex (so `n = 1, 2, 3` are the vertices, edges and
  triangles of `L_b`, and `n = 0` is the augmented degree `-1`).
* Every bad line is `augmentedLine g 0` for an integral basis `g = (b, X, Y)`.  For such a basis
  `xFiber g k = ⟨X + k b⟩`, `yFiber g l = ⟨Y + l b⟩`, `zFiber g m = ⟨X + Y + m b⟩`
  (`CoherentPrismReduction.fiberLine`).  In the paper's notation, `u = ⟨X⟩, v = ⟨Y⟩` are the
  endpoints of a base edge, `u_k = xFiber g k`, `v_l = yFiber g l`, and the base triangle is
  `(u_1, u_2, u_0) = (⟨X⟩, ⟨Y⟩, ⟨X+Y⟩)` with `θ_{k,l} = [xFiber g k, yFiber g l, zFiber g (k+l)]`
  (`CoherentPrismReduction.coherent`).
* `tetraSphere g k l = ∂[u_k,u_{k+1},v_l,v_{l+1}]`.
* `AugmentedPrismCaps.prismSphere g` is the prism boundary
  `θ_{1,0} - θ_{0,0} + (four side faces)`, the boundary of the two augmented tetrahedra
  `[X,Y,Z,X'] + [Y,Z,X',Z']` of the paper (`eq:prism-cap`); for the basis
  `affineBasis g (k,l)` it is the prism joining `θ_{k,l}` to `θ_{k+1,l}`, and for
  `affineBasis (g * swapGL) (l,k)` the one joining `θ_{k,l}` to `θ_{k,l+1}`.
  Because the sets below range over *all* integral bases with first line `b`, both families of the
  lemma occur.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction

/-- The good link `L_b = lk_X(b^±) ∩ Y` of the line `b` in the augmented-frame complex. -/
abbrev badLink (b : RationalLine) : PreAbstractSimplicialComplex RationalLine :=
  augmentedGoodLink {b}

/-- The tetrahedral sphere `∂[u_k,u_{k+1},v_l,v_{l+1}]` over the base edge `(⟨X⟩,⟨Y⟩)` of the
integral basis `g = (b, X, Y)`, with `u_k = ⟨X + k b⟩` and `v_l = ⟨Y + l b⟩`. -/
def tetraSphere (g : IntegralGL) (k l : ℤ) : Chain RationalLine :=
  boundary (simplex [xFiber g k, xFiber g (k+1), yFiber g l, yFiber g (l+1)])

/-- The tetrahedral generators of `H₂(L_b)`: `∂[u_k,u_{k+1},v_l,v_{l+1}]` over every base edge,
i.e. for every integral basis `(b, X, Y)` whose lines `⟨X⟩, ⟨Y⟩` are Good. -/
def tetraSpheres (b : RationalLine) : Set (Chain RationalLine) :=
  {c | ∃ (g : IntegralGL) (k l : ℤ), augmentedLine g 0 = b ∧ Good (xFiber g 0).val ∧
      Good (yFiber g 0).val ∧ c = tetraSphere g k l}

/-- The prism generators of `H₂(L_b)`: the boundary of the two augmented tetrahedra
`[X,Y,Z,X'] + [Y,Z,X',Z']` (`Z = X+Y`, `X' = X+b`, `Z' = Z+b`) for every integral basis
`(b, X, Y)` whose lines `⟨X⟩, ⟨Y⟩, ⟨X+Y⟩` are Good (an augmented base triangle). -/
def prismSpheres (b : RationalLine) : Set (Chain RationalLine) :=
  {c | ∃ g : IntegralGL, augmentedLine g 0 = b ∧ Good (xFiber g 0).val ∧
      Good (yFiber g 0).val ∧ Good (zFiber g 0).val ∧ c = AugmentedPrismCaps.prismSphere g}

/-- The `ℚ`-span of both generator families. -/
def sphereSpan (b : RationalLine) : Submodule ℚ (Chain RationalLine) :=
  Submodule.span ℚ (tetraSpheres b ∪ prismSpheres b)

end TernaryPeriodPolynomials.Argument.AppendixALink
