module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HomModel
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Geometry
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Reduction
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.WellRounded
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Fiber
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Stabilizer
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Levi
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.CompositeOdd
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeResidue
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeTwist
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Shapiro
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Induced
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.CosetNote
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Duality

@[expose] public section


/-!
# Lemma B.1 (`lem:literal-residue-comparison`): the literal residue comparison

Formalized by Claude Sonnet 5.5.
Paper: Lemma B.1
(`lem:literal-residue-comparison`, statement, proof through 3178, Hecke transfer
and individual period), with the setting of Section 4.4.

> **Lemma B.1.** Let `G = GL₃(ℤ)`, `H = {a = 0}` and `P_H` its stabilizer.  The literal residue
> coordinate `res_H : H₃(G, 𝓡_n ⊗ det) → 𝓓_{n+1}` at `a = 0` equals `edge₂ ∘ κ ∘ Sh` up to one fixed
> nonzero scalar independent of the polynomial, where `Sh` is the Shapiro isomorphism
> `H₃(P_H, 𝓡_{n,H} ⊗ det) ≅ H₃(G, 𝓡_n ⊗ det)` inverted, `κ` the restriction to the binary
> (plane-cone) Steinberg module, and `edge₂` the coefficient of the standard binary edge.  The
> composite is the usual odd period polynomial in the variables `b, c`.

## What this file proves and what it does not

**The statement is proved in the Hom model, not in group homology.**  The library carries out all
of Section 4.4 in the dual (Hom) picture: the group-homology groups `H₃(G, M ⊗ det)` are replaced by
`Hom_G(St, M)`, where `St` is the Steinberg module of the rational Tits building (the ordinary
incidence cycles `TernaryPoly.OrdinaryIncidenceChains.Cycles`, with `OrdinaryIncidenceChains.cycleAction`).
The identification `H₃(G, M ⊗ det) ≅ Hom_G(St, M)` (rational Borel–Serre duality for the group
`G = GL₃(ℤ)` with torsion) is *not* available in the library for `G` (only for the neat group
`Γ(6)`; see `Revision/Exports/FiberModel.lean`, `H3_neat_iso`).  This
file therefore proves the Hom-model square, with every arrow an actual named map and the
normalization scalar equal to `1`, together with all the geometry of the proof and the Hecke
transfer in the residue coordinate, and states below exactly what remains for the literal
homology square.

## Dictionary: paper ↔ library

* **`G`, `P_H`.**  `G = IntegralGL = GL₃(ℤ)` (`ModThreeGoodAction.IntegralGL`); `P_H = PH` is the
  stabilizer of the normal line `axis 0` for the library's action `rowAction` on normals, equivalently
  the matrices with first row `(±1, 0, 0)` (`mem_PH_iff_row`).  It contains the block-embedded
  `GL₂(ℤ)` (`blockEmbed_mem_PH`).
* **`𝓡_n`, `𝓡_{n,H}`, `det`.**  `𝓡_n = Residues n = ⨁_H ResidueFiber n H` with the integral action
  `integralResidueAction n e`; the exponent `e = -1` is the determinant twist `⊗ det` that makes
  `Hom_G(St, 𝓡_n ⊗ det⁻¹)` the dual of the paper's `H₃(G, 𝓡_n ⊗ det)`.  `𝓡_{n,H} =
  ResidueFiber n (axis 0)` carries the action `fiberAction n g` of `P_H` (`component_equivariant`).
  `𝓓_{n+1}` is `BinaryV (n+1)`, homogeneous forms in `(b, c)` of degree `n+1`, identified with
  `ResidueFiber n H` by `literalFiberMap n 0` (the literal coordinate).  The period space is
  `OrdinaryResiduePeriod.periodSpace (n+1)`.
* **`H₃(G, 𝓡_n ⊗ det)`** is `OrdinaryFullCoefficient.ResidueHom n (-1) = Hom_G(St, 𝓡_n ⊗ det⁻¹)`;
  **`H₃(P_H, 𝓡_{n,H} ⊗ det)`** is `StabHom n = Hom_{P_H}(St, 𝓡_{n,H})`; the binary group
  `H₃(GL₂(ℤ), 𝓓_{n+1} ⊗ det)` is `BinaryModularSymbol.PeriodHom (n+1)`.
* **`res_H`** is `resH n`, the literal residue coordinate at `a = 0` of the value on the reference
  apartment: `resH_val`.
* **`Sh`** is `Sh n`, Frobenius reciprocity from `G` to `P_H`: restrict the `G`-equivariant map to
  `P_H` and project onto the `H`-summand of `𝓡_n`.
* **`κ`** is `kappa n`: restriction of a `P_H`-equivariant map to the binary Steinberg module along
  the plane cone `OrdinaryPlaneEdge.binaryCone` (which is `blockEmbed`-equivariant), followed by the
  literal coordinate.  Its binary equivariance is exactly the determinant-twisted residue action of
  the Levi quotient (`fiber_block`).
* **`edge₂`** is `edge2 n`, the value of a binary modular symbol on the reference (standard)
  edge.

## Canonical version and relation to `Exports/AppendixLemmas`

This file is the canonical Lemma B.1 export: it states the square with the four arrows `Sh`,
`κ`, `res_H`, `edge₂` as separate named maps.  Worker D's `Exports/AppendixLemmas.lean`
(`residue_comparison_diagram`, `residue_comparison_coordinate`, `residue_comparison_bijective`,
`residue_comparison_equiv`, `residue_comparison_period_relations`, `residue_comparison_hecke`)
states the same Hom-model facts for the composite `κ ∘ Sh = toBinaryHom`, which is this file's
`kappa_Sh`; `residue_comparison_diagram` is `residue_comparison_square` rewritten with `kappa_Sh`
and `resH n = OrdinaryResiduePeriod.periodEquiv n` (`resH_eq_periodEquiv`).  The two agree, and no
statement is duplicated with a different meaning.

## The statement in code

```
theorem residue_comparison_square (n : ℕ) (F : ResidueHom n (-1)) :
    edge2 n (kappa n (Sh n F)) = resH n F                 -- scalar exactly 1
```

The scalar is `1`, independent of `n` and of `F`, and the equality is an equality of period
polynomials in `b, c`: no coefficient is mixed and no map is defined as the other side.

## What is proved

1. **The Hom-model square** (`residue_comparison_square`, `residue_comparison_square_scalar`), each
   arrow an actual map (`Sh`, `kappa`, `resH`, `edge2`); `κ ∘ Sh` is the library's literal restriction
   to the plane cone `toBinaryHom` (`kappa_Sh`); `Sh` is injective (`Sh_injective`) and an isomorphism
   onto the finite-support maps (`shapiroEquiv`).
2. **The composite is the usual odd period polynomial** in the same variables `b, c`: if the complexified
   residue coordinate of `F` is the period `periodMap f` of a cusp form `f` then the complexified symbol
   `κ(Sh F)` is the odd cusp symbol `oddHom f`, and its value on the standard edge is the `Argument.oddPeriodPart` (`composite_is_odd_period`, via the analytic `oddHom_reference`).
3. **Geometry**: the explicit map `i(w, C) = G(w, C)` and Schur-complement positivity;
   the covering radius `1/(2(1+|t|))` for `C(t) = [[1,t],[t,1]]`, `|t| ≤ 1/2` and the Voronoi bounds;
   minimum one and well-roundedness for every minimum-one binary `C`; `P_H`-equivariance
   `pᵗ G(w,C) p = G(w', C')`, `C' = DᵗCD`, `w' = D⁻¹(u + ηw)`; injectivity; the image of `i` is the
   union of integral-parabolic translates of the standard ternary top cell; the radical `ℤ²` acts by
   translation with covolume one, the Jacobian `det C(t) = 1 - t² > 0`; stabilizer orders `48`, `16` and
   the three cosets; radical conjugation and the factor `λ²`.
4. **The Hecke transfer in the residue coordinate** (`resH_hecke_prime`): `T₃(p,1) = p T₂(p) + 1`
   in the library's left convention, and the cusp-form compatibility `periodMap_hecke`
   (`p^{d+1}` normalization).

## What is not proved

* Proved: the group-homology Shapiro isomorphism for the residue
  module (`shapiroHomologyIso`, from Mathlib's `groupHomology.indIso` and `indResiduesIso`); the Hom-model
  Shapiro isomorphism (`shapiroEquiv`); and the CONDITIONAL duality `dualityG n h : H₃(G, 𝓡_n ⊗ det⁻¹) ≃
  ResidueHom n (-1)` for `h : NeatDualityG n`, the `G`-equivariance of the library's neat-level duality for
  the residue module.  Missing for the literal square: (S-A) `NeatDualityG n` (geometry);
  (S-B) the Hochschild-Serre isomorphism `H₃(P_H, 𝓡_{n,H}) ≅ H₁(L, H₂(U) ⊗ 𝓡_{n,H})` (`P_H = U ⋊ L`,
  `U = ℤ²`, `L = ±1 × GL₂(ℤ)`; over `ℚ` it is an isomorphism since `H_p(L, -) = 0` for `p ≥ 2`), which
  Mathlib does not have; (S-C) the duality `H₁(GL₂(ℤ), D ⊗ det) ≅ Hom_{GL₂(ℤ)}(St₂, D)` and the identification
  of `edge₂` with evaluation on the standard edge; (S-D) the compatibilities `Θ_{P_H} ∘ Shapiro = shapiroEquiv ∘ Θ_G`
  and `Θ_{GL₂} ∘ κ = kappa ∘ Θ_{P_H}`.  Given (S-A)-(S-D) the literal square follows from
  `residue_comparison_square` with scalar one.
* Let `St` be the Steinberg module.  The missing statement is
  the duality `H₃(G, M ⊗ det) ≅ Hom_G(St, M)`, natural in `M`, compatible with Shapiro and with
  Hochschild–Serre for `P_H ⊂ G`.  With it, `res_H`, `Sh`, `κ`, `edge₂` of the paper
  are the transports of `resH`, `Sh`, `kappa`, `edge2` and the square holds with scalar `1` (the
  orientation and cellular averaging scalar is absorbed in the duality iso).
* **Shapiro in the Hom model is an isomorphism onto the finite-support maps (proved, `shapiroEquiv`).**
  `Hom_G(St, ⨁_H 𝓡_H) → Hom_{P_H}(St, 𝓡_H)` is Frobenius reciprocity for *co*-induction, and `⨁_H` is the
  induced (not the coinduced) module, so a `P_H`-equivariant `φ` comes from `G` exactly when it has
  *finite support*: for every cycle `c`, only finitely many hyperplanes `ν x = H₀ x` have `φ(x c) ≠ 0`
  (`HasFiniteSupport`).  `Sh` is an isomorphism `ResidueHom n (-1) ≃ₗ StabHomFin n` onto these
  (`shapiroEquiv`, with explicit inverse `F(c) = ∑ᶠ_H ρ(x_H⁻¹) lof_{H₀} φ(x_H c)`, `ν x_H = H`);
  `κ` is injective on `StabHomFin` (`kappa_injective_on_fin`).  Injectivity of `κ` on all of `StabHom`
  is not claimed (it would say that `St` is generated over `P_H` by the plane-cone cycles).  The
  homology Shapiro isomorphism `H₃(P_H, 𝓡_{n,H}) ≅ H₃(G, 𝓡_n)` has no finiteness condition and is
  part of Stage 2.
* **Hecke normalization (investigated, see `HeckeTwist.lean`).**  The library's Hom operator for the
  representatives of `diag(p,1,1)` and the determinant exponent `e` has fibre terms `λ^{e+1}` times the
  binary term (`fibre_term_twist`), is `p^{e+1}` times the exponent `-1` one (`hecke_twist`: `e ↦ e+2`
  multiplies by `p²`), and in the exponent `-1` is `T₃ = p T₂ + 1` (`resH_hecke_prime`).  With the
  analytic Hecke operator, `p^d res_H(T₃ F) = periodMap (T_p f) + p^d periodMap f`, `d = n + 1`
  (`resH_hecke_cusp`): the shape is `T_p + p^d`.  The paper's `p T₂ + p² I` is exactly the
  exponent `+1` identity for the natural unnormalized binary operator `T₂^{(+1)} = p^{1-d} T_p`; with
  the analytic `T_p` the ratio (constant term)/(coefficient of `T_p`) is `p^d` in the Hom model and `p`
  in the paper.  Rescaling `T₃` alone preserves this ratio; rescaling `T_p` changes it but breaks the fixed
  analytic normalization of `T_p`.  This is a model/paper-normalization discrepancy, not a proved error of
  the paper: the literal `p T_p + p² I` is not decided until the `H₃ ↔ Hom` Hecke naturality is proved.
  Further, the paper calls its representatives `(1 0 0; 0 1 0; b c p)` "right-coset representatives",
  but they all lie in one right coset `GL₃(ℤ)·δ` (`lowerFamily_same_right_coset`); they represent the
  distinct left cosets `δ·GL₃(ℤ)`, the right decomposition for an operator on invariants (the Hom model)
  and the wrong one for a sum over coinvariants (group homology), where right cosets `Γδ` are summed.
  This left/right mismatch is a possible (unproved) source of the paper's constant `p²`.  If the duality
  is natural in the subgroup (corestriction `↔` trace) and under conjugation, the Hom operator is the homology
  operator of the SAME double coset; if instead it exchanges an operator with its transpose, the shapes would
  be those of `T(p,1)` and `T(p,2)`.  Which of the two holds is decided by the Stage 2 naturality, which is
  not available (it needs the equivariance of the neat-level duality); nothing here decides it.  Stability
  of liftable residues needs only a nonzero coefficient of `T_p`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixBResidue

open scoped Matrix
open TernaryPoly TernaryPoly.OrdinaryFullCoefficient TernaryPoly.SinglePole
  TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry

/-! ### The Hom model of the square -/

/-- **Lemma B.1, Hom model**: `edge₂ ∘ κ ∘ Sh = res_H`, with the fixed scalar `1` (independent of
`n` and of the residue functional). -/
theorem residue_comparison_square (n : ℕ) (F : ResidueHom n (-1)) :
    edge2 n (kappa n (Sh n F)) = resH n F :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.residue_comparison_square n F

/-- The same with the scalar made explicit: one fixed nonzero rational scalar, independent of `n`
and of `F`, such that `edge₂ ∘ κ ∘ Sh = c • res_H`. -/
theorem residue_comparison_square_scalar :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ (n : ℕ) (F : ResidueHom n (-1)),
      edge2 n (kappa n (Sh n F)) = c • resH n F :=
  ⟨1, one_ne_zero, fun n F => by rw [one_smul]; exact _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.residue_comparison_square n F⟩

/-- `κ ∘ Sh` is the library's literal restriction to the plane cone. -/
theorem kappa_Sh (n : ℕ) (F : ResidueHom n (-1)) :
    kappa n (Sh n F) = OrdinaryResidueSymbol.toBinaryHom n F :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.kappa_Sh n F

/-- `res_H` is the literal residue coordinate at `a = 0` of the value on the reference apartment. -/
theorem resH_val (n : ℕ) (F : ResidueHom n (-1)) :
    (resH n F).val = SinglePoleCoordinate.literalFiberMap n 0
      (SinglePoleSupport.component n (OrdinaryResidueSupport.axis 0)
        (F.val (OrdinaryApartmentPresentation.frameCycle 1))) :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.resH_val n F

/-- Frobenius reciprocity from `G` to `P_H` is injective. -/
theorem Sh_injective (n : ℕ) : Function.Injective (Sh n) :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.Sh_injective n

/-- The stabilizer `P_H` is the group of integral matrices with first row `(±1, 0, 0)`. -/
theorem mem_PH_iff_row (g : ModThreeGoodAction.IntegralGL) :
    g ∈ PH ↔ g.val 0 1 = 0 ∧ g.val 0 2 = 0 :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.mem_PH_iff_row g

/-- The block-embedded `GL₂(ℤ)` lies in `P_H`. -/
theorem blockEmbed_mem_PH (g : RankTwoAugmentedFrames.IntegralGL) :
    OrdinaryPlaneEdge.blockEmbed g ∈ PH :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.blockEmbed_mem_PH g

/-- **The determinant-twisted residue action on the Levi quotient**: the block-embedded `GL₂(ℤ)` acts
on the fibre `𝓡_{n,H} ≅ 𝓓_{n+1}` by the determinant-inverse twisted substitution, exactly the binary
coefficient action; this is what makes `κ` land in binary modular symbols. -/
theorem fiber_block (n : ℕ) (g : RankTwoAugmentedFrames.IntegralGL)
    (x : ResidueFiber n (OrdinaryResidueSupport.axis 0)) :
    SinglePoleCoordinate.literalFiberMap n 0 (fiberAction n (OrdinaryPlaneEdge.blockEmbed g) x) =
      BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1)
        (BinaryModularSymbol.integral g) (SinglePoleCoordinate.literalFiberMap n 0 x) :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.fiber_block n g x

/-- **Shapiro's lemma in the Hom model**: Frobenius reciprocity is an isomorphism from
`Hom_G(St, 𝓡_n ⊗ det⁻¹)` onto the finite-support part `StabHomFin n` of `Hom_{P_H}(St, 𝓡_{n,H})`. -/
def shapiroEquiv (n : ℕ) : ResidueHom n (-1) ≃ₗ[ℚ] StabHomFin n :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.shapiroEquiv n

/-- The Shapiro isomorphism is `F ↦ component_{H₀} ∘ F`. -/
theorem shapiroEquiv_apply (n : ℕ) (F : ResidueHom n (-1)) :
    ((shapiroEquiv n F : StabHomFin n) :
        OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (OrdinaryResidueSupport.axis 0)) =
      (Sh n F).val :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.shapiroEquiv_apply n F

/-- The inverse of Frobenius reciprocity: the image of `Sh` consists exactly of the finite-support maps
and `Sh` of the explicit preimage is the given map. -/
theorem Sh_invShapiro (n : ℕ)
    {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (OrdinaryResidueSupport.axis 0)}
    (hφ : φ ∈ StabHom n) (hfin : _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.HasFiniteSupport n φ) :
    (Sh n (_root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.invShapiro n hφ hfin)).val = φ :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.Sh_invShapiro n hφ hfin

/-- The image of `Sh` has finite support. -/
theorem Sh_finiteSupport (n : ℕ) (F : ResidueHom n (-1)) :
    _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.HasFiniteSupport n (Sh n F).val :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.Sh_finiteSupport n F

/-- `κ` is injective on the finite-support maps. -/
theorem kappa_injective_on_fin (n : ℕ) (φ ψ : StabHomFin n)
    (h : kappa n ⟨φ.1, φ.2.1⟩ = kappa n ⟨ψ.1, ψ.2.1⟩) : φ = ψ :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.kappa_injective_on_fin n φ ψ h

/-- **`𝓡_n ≅ Ind_{P_H}^G 𝓡_{n,H₀}` as `G`-representations** (Mathlib's `Rep.ind` along
`P_H ↪ G`): the residue module is the induced module of its `H₀`-summand. -/
def indResiduesIso (n : ℕ) :
    Rep.ind PH.subtype (_root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.FibRep n) ≅ _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.ResRep n :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.indResiduesIso n

/-- **Shapiro in group homology for the residue module**:
`H_k(G, 𝓡_n ⊗ det⁻¹) ≅ H_k(P_H, 𝓡_{n,H₀})` (Mathlib's `groupHomology.indIso` transported along
`indResiduesIso`).  Together with the duality `H₃ ≅ Hom(St, ·)` (Stage 2) this is the homological
counterpart of `shapiroEquiv`. -/
def shapiroHomologyIso (n k : ℕ) :
    groupHomology (_root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.ResRep n) k ≅ groupHomology (_root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.FibRep n) k :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.shapiroHomologyIso n k

/-- **CONDITIONAL (Stage 2).**  The `G`-equivariance of the library's neat-level duality for the residue
module `𝓡_n ⊗ det⁻¹`; the single missing geometric input of the literal group-homology square. -/
def NeatDualityG (n : ℕ) : Prop := _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.NeatDualityG n

/-- **CONDITIONAL (Stage 2).**  If the neat-level duality is `G`-equivariant for the residue module, then
`H₃(G, 𝓡_n ⊗ det⁻¹) ≃ Hom_G(St, 𝓡_n ⊗ det⁻¹) = ResidueHom n (-1)`. -/
def dualityG (n : ℕ) (h : NeatDualityG n) :
    groupHomology (_root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.ResRep n) 3 ≃ₗ[ℚ] ResidueHom n (-1) :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.dualityG n h

/-! ### The composite is the odd period polynomial -/

/-- **The composite `edge₂ ∘ κ ∘ Sh` is the odd period polynomial.**  If the complexified residue
coordinate of `F` is the period `periodMap f` of a cusp form `f` of degree `n + 1`, then the
complexification of the binary symbol `κ(Sh F)` is the odd cusp symbol of `f`, and the complexified
residue polynomial in `b, c` (`X 0, X 1`) is the odd period polynomial `oddPeriodPart (n+1) f`. -/
theorem composite_is_odd_period (n : ℕ) (hd : Even (n + 1)) (F : ResidueHom n (-1))
    (f : BinaryCuspPeriod.Forms (n + 1))
    (h : BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F) = BinaryCuspPeriod.periodMap (n + 1) hd f) :
    BinaryCuspSymbol.rationalFunctionHom (n + 1) (kappa n (Sh n F)) = BinaryCuspSymbol.oddHom f ∧
    (BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F)).val =
      TernaryPeriodPolynomials.Argument.oddPeriodPart (n + 1) f :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.composite_is_odd_period n hd F f h

/-! ### The Hecke transfer in the residue coordinate -/

/-- **`T₃(p,1) = p T₂(p) + 1` in the literal residue coordinate** (library left convention). -/
theorem resH_hecke_prime (n p : ℕ) [Fact p.Prime] (F : ResidueHom n (-1)) :
    resH n (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
        (SinglePole.residueAction n (-1)) F) =
      (p : ℚ) • BinaryRationalHecke.periodHecke (n + 1)
        (BinaryRationalHeckePrime.primeDiagonal p) (resH n F) + resH n F :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.resH_hecke_prime n p F

/-- **Individual-period compatibility**: the analytic prime Hecke operator `T_p` of
weight `d + 2` acts on the odd period polynomial through the binary prime correspondence, with the
normalization `p^{d+1}` (library: `TernaryPoly.BinaryCuspPeriod.periodMap_hecke`). -/
theorem periodMap_hecke {d : ℕ} (hd : Even d) (f : BinaryCuspPeriod.Forms d) (p : ℕ)
    [Fact p.Prime] :
    BinaryCuspPeriod.periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) =
      (p : ℂ) ^ (d + 1) • BinaryComplexPeriod.complexHecke d
        (BinaryRationalHeckePrime.primeDiagonal p) (BinaryCuspPeriod.periodMap d hd f) :=
  BinaryCuspPeriod.periodMap_hecke hd f p

/-- **Fibre factor.** For the exponent `-1 + k` the contribution of a representative
`g = (λ 0; u C)` on the plane cone is `λ^k` times the binary term of `C` (`k = 2`: the paper's
`λ²`; `k = 0`: the library's convention). -/
theorem fibre_term_twist (n : ℕ) (k : ℤ) (F : ResidueHom n (-1))
    (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : BinaryModularSymbol.GL2)
    (hg : g.val = OrdinaryResidueParabolic.blockMatrix lam u C) (c : BinaryModularSymbol.St) :
    OrdinaryResidueParabolic.zeroCoordinate n
        (OrdinaryHomHecke.linearAction (residueAction n (-1 + k)) g F.val
          (OrdinaryPlaneEdge.binaryCone c)) =
      (lam : ℚ) ^ k • BinaryModularSymbol.homAction
        (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + k)) C
        (OrdinaryResidueSymbol.toBinaryHom n F).val c :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.fibre_term_twist n k F g lam u C hg c

/-- **Uniform `p²`**: raising the determinant exponent by two multiplies the prime Hecke operator
by `p²`. -/
theorem hecke_twist (n : ℕ) (e : ℤ) (p : ℕ) [Fact p.Prime] (F : ResidueHom n e) :
    (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
        (residueAction n (e + 2)) (twistHom n e F)).val =
      (p : ℚ) ^ 2 • (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
        (residueAction n e) F).val :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.hecke_twist n e p F

/-- **Hom-model Hecke shape on cusp periods**: `p^d res_H(T₃ F) = periodMap (T_p f) + p^d periodMap f`
(`d = n + 1`) when `res_H F` is the period of the cusp form `f`. -/
theorem resH_hecke_cusp (n p : ℕ) [Fact p.Prime] (hd : Even (n + 1)) (F : ResidueHom n (-1))
    (f : BinaryCuspPeriod.Forms (n + 1))
    (h : BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F) = BinaryCuspPeriod.periodMap (n + 1) hd f) :
    (p : ℂ) ^ (n + 1) • BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n
          (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
            (residueAction n (-1)) F)) =
      BinaryCuspPeriod.periodMap (n + 1) hd (BinaryCuspHeckeEndomorphism.T (n + 1) p f) +
        (p : ℂ) ^ (n + 1) • BinaryCuspPeriod.periodMap (n + 1) hd f :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.resH_hecke_cusp n p hd F f h

/-- The paper's lower-triangular representatives `(1 0 0; 0 1 0; b c p)` lie in one right coset
`GL₃(ℤ)·δ`: they are left-coset representatives. -/
theorem lowerFamily_same_right_coset (p : ℕ) [Fact p.Prime] (b c b' c' : ZMod p) :
    ∃ u : ModThreeGoodAction.IntegralGL,
      (OrdinaryHeckeCosets.primeRepresentative p (Sum.inl (b, c))).val =
        (OrdinaryFullAction.integral u).val *
          (OrdinaryHeckeCosets.primeRepresentative p (Sum.inl (b', c'))).val :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.lowerFamily_same_right_coset p b c b' c'

/-! ### Geometry: the map `i(w, C) = G(w, C)` -/

/-- Schur complement: `G(w,C)` has Schur complement `1 - δ_C(w)²` over `C`. -/
theorem Gmat_schur (w : Vec2) (C : Mat2) :
    Gmat w C 0 0 - quad C w = 1 - deltaSq C w :=
  Geometry.Gmat_schur w C

/-- Squared length of `(k, z)` for `G(w,C)`: `k²(1 - δ²) + (z + kw)ᵗC(z + kw)`. -/
theorem Gmat_quad {C : Mat2} (hC : C 1 0 = C 0 1) (w : Vec2) (k : ℝ) (z : Vec2) :
    vec3 k z ⬝ᵥ (Gmat w C *ᵥ vec3 k z) = k ^ 2 * (1 - deltaSq C w) + quad C (z + k • w) :=
  Geometry.Gmat_quad hC w k z

/-- Voronoi inequalities for a point nearest to the origin. -/
theorem voronoi_inequalities {t : ℝ} (x : Vec2)
    (hx : ∀ z : Fin 2 → ℤ, quad (Ct t) x ≤ quad (Ct t) (x - intVec z)) :
    |x 0 + t * x 1| ≤ 1 / 2 ∧ |t * x 0 + x 1| ≤ 1 / 2 ∧
      (t < 1 → |x 0 - x 1| ≤ 1) ∧ (-1 < t → |x 0 + x 1| ≤ 1) :=
  Geometry.voronoi_inequalities x hx

/-- **Covering radius** `δ² ≤ 1/(2(1+|t|))` for `C(t)`, `|t| ≤ 1/2`. -/
theorem deltaSq_Ct_le {t : ℝ} (ht : |t| ≤ 1 / 2) (w : Vec2) :
    deltaSq (Ct t) w ≤ 1 / (2 * (1 + |t|)) :=
  Geometry.deltaSq_Ct_le ht w

/-- `G(w, C(t))` is positive definite (the Schur complement `1 - δ² ≥ 1/2` is positive). -/
theorem Gmat_posDef {t : ℝ} (ht : |t| ≤ 1 / 2) (w : Vec2) : PosDefQ (Gmat w (Ct t)) :=
  Geometry.Gmat_posDef ht w

/-- **Minimum one**: every nonzero integral `(k, z)` has squared length `≥ 1` when `C` has minimum
one and covering radius `≤ 1/2`. -/
theorem Gmat_min_one {C : Mat2} (hC : C 1 0 = C 0 1) (hpsd : ∀ v, 0 ≤ quad C v)
    (hmin : ∀ z : Fin 2 → ℤ, z ≠ 0 → 1 ≤ quad C (intVec z)) (w : Vec2)
    (hδ : deltaSq C w ≤ 1 / 2) (k : ℤ) (z : Fin 2 → ℤ) (hkz : k ≠ 0 ∨ z ≠ 0) :
    1 ≤ vec3 (k : ℝ) (intVec z) ⬝ᵥ (Gmat w C *ᵥ vec3 (k : ℝ) (intVec z)) :=
  Geometry.Gmat_min_one hC hpsd hmin w hδ k z hkz

/-- **Well-rounded** for every minimum-one binary form `C` (`BinWR`): positive definite, minimum
one, and the three vectors `(1, z₀)`, `(0, v₁)`, `(0, v₂)` of length one form a basis of `ℤ³`. -/
theorem Gmat_wellRounded {C : Mat2} (hC : BinWR C) (w : Vec2) :
    PosDefQ (Gmat w C) ∧
    (∀ (k : ℤ) (z : Fin 2 → ℤ), (k ≠ 0 ∨ z ≠ 0) →
      1 ≤ vec3 (k : ℝ) (intVec z) ⬝ᵥ (Gmat w C *ᵥ vec3 (k : ℝ) (intVec z))) ∧
    ∃ z₀ v₁ v₂ : Fin 2 → ℤ,
      vec3 1 (intVec z₀) ⬝ᵥ (Gmat w C *ᵥ vec3 1 (intVec z₀)) = 1 ∧
      vec3 0 (intVec v₁) ⬝ᵥ (Gmat w C *ᵥ vec3 0 (intVec v₁)) = 1 ∧
      vec3 0 (intVec v₂) ⬝ᵥ (Gmat w C *ᵥ vec3 0 (intVec v₂)) = 1 ∧
      ((!![1, 0, 0; z₀ 0, v₁ 0, v₂ 0; z₀ 1, v₁ 1, v₂ 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 ∨
       (!![1, 0, 0; z₀ 0, v₁ 0, v₂ 0; z₀ 1, v₁ 1, v₂ 1] : Matrix (Fin 3) (Fin 3) ℤ).det = -1) :=
  Geometry.Gmat_wellRounded hC w

/-- **`P_H`-equivariance**: for `p = [[η,0],[u,D]]` with `η = ±1`, `u ∈ ℤ²`, `D ∈ GL₂(ℤ)` and
`D w' = u + η w`: `pᵗ G(w,C) p = G(w', DᵗCD)`. -/
theorem Gmat_equivariant {C : Mat2} (hC : Cᵀ = C) (D E : IMat2) (hDE : D * E = 1)
    (hED : E * D = 1) (u : Fin 2 → ℤ) (η : ℤ) (hη : η = 1 ∨ η = -1) (w w' : Vec2)
    (hw : castMat D *ᵥ w' = intVec u + (η : ℝ) • w) :
    (parab η u D)ᵀ * Gmat w C * parab η u D = Gmat w' ((castMat D)ᵀ * C * castMat D) :=
  Geometry.Gmat_equivariant hC D E hDE hED u η hη w w' hw

/-- The covering radius is invariant under the change of variables. -/
theorem deltaSq_conj (C : Mat2) (D E : IMat2) (hDE : D * E = 1) (hED : E * D = 1)
    (u : Fin 2 → ℤ) (η : ℤ) (hη : η = 1 ∨ η = -1) (w w' : Vec2)
    (hw : castMat D *ᵥ w' = intVec u + (η : ℝ) • w) :
    deltaSq ((castMat D)ᵀ * C * castMat D) w' = deltaSq C w :=
  Geometry.deltaSq_conj C D E hDE hED u η hη w w' hw

/-- **Injectivity** of `i`: `G(w,C)` determines `C` and `w`. -/
theorem Gmat_injective {C C' : Mat2} (hC : ∀ v, v ≠ 0 → 0 < quad C v) {w w' : Vec2}
    (h : Gmat w C = Gmat w' C') : C = C' ∧ w = w' :=
  Geometry.Gmat_injective hC h

/-- The Voronoi polygon of `C(t)` is mapped into the standard ternary top cell. -/
theorem Gmat_mem_Tcell {t : ℝ} (ht : |t| ≤ 1 / 2) {w : Vec2} (hw : w ∈ Voronoi (Ct t)) :
    Gmat w (Ct t) ∈ Tcell :=
  Geometry.Gmat_mem_Tcell ht hw

/-- Conversely every point of the standard top cell is `G(w, C(t))` with `w` in the Voronoi
polygon. -/
theorem Tcell_eq_Gmat {A : Mat3} (hA : A ∈ Tcell) :
    ∃ t : ℝ, |t| ≤ 1 / 2 ∧ ∃ w ∈ Voronoi (Ct t), A = Gmat w (Ct t) :=
  Geometry.Tcell_eq_Gmat hA

/-- A minimum-one binary form is `DᵗC(t)D` with `D ∈ GL₂(ℤ)` and `|t| ≤ 1/2`. -/
theorem BinWR_reduce {C : Mat2} (hC : BinWR C) :
    ∃ t : ℝ, |t| ≤ 1 / 2 ∧ ∃ D D' : IMat2, D * D' = 1 ∧ D' * D = 1 ∧
      C = (castMat D)ᵀ * Ct t * castMat D :=
  Geometry.BinWR_reduce hC

/-- **The image of `i` is the union of integral-parabolic translates of the standard ternary top
cell.** -/
theorem image_eq_translates : GImage = Translates :=
  Geometry.image_eq_translates

/-! ### The fibre: radical torus, Jacobian, stabilizers, `λ²` -/

/-- The integral radical acts on the fibre coordinate by translation. -/
theorem Gmat_translate {C : Mat2} (hC : Cᵀ = C) (u : Fin 2 → ℤ) (w : Vec2) :
    (parab 1 u 1)ᵀ * Gmat w C * parab 1 u 1 = Gmat (w + intVec u) C :=
  Geometry.Gmat_translate hC u w

/-- The fibre torus `ℝ²/ℤ²` of the radical has covolume one. -/
theorem torus_volume :
    MeasureTheory.volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2))) = 1 :=
  Geometry.torus_volume

/-- The Jacobian of `w ↦ C(t) w` is `1 - t² > 0`. -/
theorem jacobian_Ct_pos {t : ℝ} (ht : |t| ≤ 1 / 2) :
    0 < LinearMap.det (Matrix.toLin' (Ct t)) :=
  Geometry.jacobian_Ct_pos ht

/-- The stabilizer of the ternary top cell in `GL₃(ℤ)` has order `48`. -/
theorem stabilizer_card : Set.ncard {g : IMat3 | StabCell g} = 48 :=
  Geometry.stabilizer_card

/-- The stabilizer of the cell which also preserves `H` has order `16`. -/
theorem stabilizer_H_card :
    Set.ncard {g : IMat3 | StabCell g ∧ g 0 1 = 0 ∧ g 0 2 = 0} = 16 :=
  Geometry.stabilizer_H_card

/-- The three cosets (first row supported at the `i`-th coordinate) have order `16` each: these are
the three coordinate residues. -/
theorem stabilizer_cosets (i : Fin 3) :
    Set.ncard {g : IMat3 | StabCell g ∧ ∀ j, j ≠ i → g 0 j = 0} = 16 :=
  Geometry.stabilizer_cosets i

/-- Conjugation of the radical `U(v)` by `g = (λ 0; u C)`: `g U(v) g⁻¹ = U(λ⁻¹ C v)`. -/
theorem radical_conj (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : OrdinaryResidueParabolic.GL2)
    (hg : g.val = OrdinaryResidueParabolic.blockMatrix lam u C) (v : Fin 2 → ℚ) :
    g.val * radical v * (g⁻¹).val = radical ((lam : ℚ)⁻¹ • (C.val *ᵥ v)) :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.radical_conj g lam u C hg v

/-- **The factor `λ²`**: inverse conjugation on `H₂(radical)` contributes `λ²/det C`, the
determinant-twisted residue coefficient `det C`; the product is `λ²`. -/
theorem H2_factor (lam : ℚˣ) (C : OrdinaryResidueParabolic.GL2) :
    (Matrix.det ((lam : ℚ)⁻¹ • C.val))⁻¹ * C.val.det = (lam : ℚ) ^ 2 :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.H2_factor lam C

/-- On the integral Levi (`λ = ±1`) the combined factor is one. -/
theorem H2_factor_integral (lam : ℚˣ) (hlam : (lam : ℚ) = 1 ∨ (lam : ℚ) = -1)
    (C : OrdinaryResidueParabolic.GL2) :
    (Matrix.det ((lam : ℚ)⁻¹ • C.val))⁻¹ * C.val.det = 1 :=
  _root_.TernaryPeriodPolynomials.Argument.AppendixBResidue.H2_factor_integral lam hlam C

end TernaryPeriodPolynomials.Argument.Statements.AppendixBResidue
