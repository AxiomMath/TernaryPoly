module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.OneCocycleExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleDetection

@[expose] public section


/-!
# Mixed two-cocycles of a split extension realise every strict Levi family

Let `1 → N → E → L → 1` be a split extension with section `s`, and `V` a representation of `E`.
Write every `x ∈ E` as `x = n(x) s(π x)` with `n(x) ∈ N`, and let `κ : L → Aut N` be conjugation
through `s`.  A family `F : L → Z¹(N, V)` satisfying the strict crossed-homomorphism law
`F(ℓ₁ℓ₂)(r) = ρ(s ℓ₁) F(ℓ₂)(κ(ℓ₁)⁻¹ r) + F(ℓ₁)(r)` defines the two-cochain

`f(x, y) = ρ(n(x)) F(π x)(κ(π x) n(y))`,

which is a two-cocycle vanishing on `N × N`, and whose Hochschild–Serre mixed part
`ℓ ↦ [r ↦ f(s ℓ, κ(ℓ)⁻¹ r) - f(r, s ℓ)]` is exactly `F` (`splitEdgeCycle_mixedRelative`).

Given an `L`-representation `W` and an equivariant linear map `σ : W → Z¹(N, V)` (a cocycle-level
section of the radical cohomology), every one-cocycle `c` of `L` with values in `W` gives the strict
family `ℓ ↦ σ(c ℓ)`.  Hence every Levi class that comes through `σ` is a Hochschild–Serre edge class,
with no obstruction in `H³(L, V^N)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjSplit

variable {N E L : Type} [Group N] [Group E] [Group L]

/-- Conjugation through the section moves a radical element past the section. -/
theorem splitting_mul_inl {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (levi : L) (radical : N) :
    splitting levi * extension.inl radical =
      extension.inl (splitting.conjAct levi radical) * splitting levi := by
  have conjugation := extension.inl_conjAct_comm (e := splitting levi) (n := radical)
  change extension.inl (splitting.conjAct levi radical) =
    splitting levi * extension.inl radical * (splitting levi)⁻¹ at conjugation
  rw [conjugation, inv_mul_cancel_right]

/-- The conjugation action composes multiplicatively. -/
theorem conjAct_conjAct {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (first second : L) (radical : N) :
    splitting.conjAct first (splitting.conjAct second radical) =
      splitting.conjAct (first * second) radical := by
  rw [map_mul, MulAut.mul_apply]

/-- The radical input of `ℓ` undoes conjugation by `ℓ`. -/
theorem splitRadicalInput_conjAct_mul {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (first second : L) (radical : N) :
    splitRadicalInput splitting first (splitting.conjAct (first * second) radical) =
      splitting.conjAct second radical := by
  change splitting.conjAct first⁻¹ (splitting.conjAct (first * second) radical) = _
  rw [conjAct_conjAct, inv_mul_cancel_left]

/-- Conjugation by `ℓ` undoes the radical input of `ℓ`. -/
theorem conjAct_splitRadicalInput {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (levi : L) (radical : N) :
    splitting.conjAct levi (splitRadicalInput splitting levi radical) = radical := by
  change splitting.conjAct levi (splitting.conjAct levi⁻¹ radical) = radical
  rw [conjAct_conjAct, mul_inv_cancel, map_one, MulAut.one_apply]

/-- The strict crossed-homomorphism law for a family of radical one-cocycles. -/
def StrictLaw {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation)) : Prop :=
  ∀ first second radical, family (first * second) radical =
    representation.ρ (splitting first) (family second (splitRadicalInput splitting first radical)) +
      family first radical

/-- A strict family vanishes at the identity. -/
theorem strictLaw_one_apply {extension : GroupExtension N E L} {splitting : extension.Splitting}
    {representation : Rep ℂ E}
    {family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation)}
    (law : StrictLaw splitting representation family) (radical : N) : family 1 radical = 0 := by
  have equality := law 1 1 radical
  rw [mul_one, splitRadicalInput_one, map_one, map_one, Module.End.one_apply] at equality
  exact add_left_cancel (equality.symm.trans (add_zero (family 1 radical)).symm)

/-- The mixed two-cochain `f(x, y) = ρ(n(x)) F(π x)(κ(π x) n(y))` of a family. -/
def mixedValue {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (pair : E × E) : representation :=
  representation.ρ (extension.inl (splitRadicalCoordinate splitting pair.1))
    (family (extension.rightHom pair.1)
      (splitting.conjAct (extension.rightHom pair.1) (splitRadicalCoordinate splitting pair.2)))

theorem mixedValue_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation)) (first second : E) :
    mixedValue splitting representation family (first, second) =
      representation.ρ (extension.inl (splitRadicalCoordinate splitting first))
        (family (extension.rightHom first)
          (splitting.conjAct (extension.rightHom first) (splitRadicalCoordinate splitting second))) := rfl

/-- The representation applied along the decomposition `x = n(x) s(π x)`. -/
theorem rho_decomposition {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (element : E) (vector : representation) :
    representation.ρ element vector =
      representation.ρ (extension.inl (splitRadicalCoordinate splitting element))
        (representation.ρ (splitting (extension.rightHom element)) vector) := by
  have equality := congrArg (fun group_element => representation.ρ group_element vector)
    (split_coordinate_decomposition splitting element)
  simp only [map_mul, Module.End.mul_apply] at equality
  exact equality.symm

/-- The representation applied along `s(ℓ) r = κ(ℓ)(r) s(ℓ)`. -/
theorem rho_splitting_inl {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (levi : L) (radical : N) (vector : representation) :
    representation.ρ (splitting levi) (representation.ρ (extension.inl radical) vector) =
      representation.ρ (extension.inl (splitting.conjAct levi radical))
        (representation.ρ (splitting levi) vector) := by
  have equality := congrArg (fun group_element => representation.ρ group_element vector)
    (splitting_mul_inl splitting levi radical)
  simp only [map_mul, Module.End.mul_apply] at equality
  exact equality

/-- A radical one-cocycle evaluated at a product. -/
theorem radicalCocycle_mul {extension : GroupExtension N E L} (representation : Rep ℂ E)
    (cycle : groupCohomology.cocycles₁ (Rep.res extension.inl representation)) (first second : N) :
    cycle (first * second) =
      representation.ρ (extension.inl first) (cycle second) + cycle first :=
  oneCocycle_mul (Rep.res extension.inl representation) cycle first second

/-- The mixed two-cochain of a strict family is a two-cocycle. -/
theorem mixedValue_mem {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (law : StrictLaw splitting representation family) :
    mixedValue splitting representation family ∈ groupCohomology.cocycles₂ representation := by
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro x y z
  have first_term : mixedValue splitting representation family (x * y, z) =
      representation.ρ (extension.inl (splitRadicalCoordinate splitting x))
        (representation.ρ (extension.inl (splitting.conjAct (extension.rightHom x)
            (splitRadicalCoordinate splitting y)))
          (representation.ρ (splitting (extension.rightHom x))
              (family (extension.rightHom y)
                (splitting.conjAct (extension.rightHom y) (splitRadicalCoordinate splitting z))) +
            family (extension.rightHom x)
              (splitting.conjAct (extension.rightHom x * extension.rightHom y)
                (splitRadicalCoordinate splitting z)))) := by
    rw [mixedValue_apply, splitRadicalCoordinate_mul, map_mul extension.rightHom,
      law (extension.rightHom x) (extension.rightHom y), splitRadicalInput_conjAct_mul, map_mul extension.inl, map_mul representation.ρ,
      Module.End.mul_apply]
  have third_term : representation.ρ x (mixedValue splitting representation family (y, z)) =
      representation.ρ (extension.inl (splitRadicalCoordinate splitting x))
        (representation.ρ (extension.inl (splitting.conjAct (extension.rightHom x)
            (splitRadicalCoordinate splitting y)))
          (representation.ρ (splitting (extension.rightHom x))
            (family (extension.rightHom y)
              (splitting.conjAct (extension.rightHom y) (splitRadicalCoordinate splitting z))))) := by
    rw [mixedValue_apply, rho_decomposition splitting representation x, rho_splitting_inl]
  have fourth_term : mixedValue splitting representation family (x, y * z) =
      representation.ρ (extension.inl (splitRadicalCoordinate splitting x))
        (representation.ρ (extension.inl (splitting.conjAct (extension.rightHom x)
            (splitRadicalCoordinate splitting y)))
          (family (extension.rightHom x)
            (splitting.conjAct (extension.rightHom x * extension.rightHom y)
              (splitRadicalCoordinate splitting z))) +
          family (extension.rightHom x)
            (splitting.conjAct (extension.rightHom x) (splitRadicalCoordinate splitting y))) := by
    rw [mixedValue_apply, splitRadicalCoordinate_mul splitting y z,
      map_mul (splitting.conjAct (extension.rightHom x)) (splitRadicalCoordinate splitting y),
      conjAct_conjAct, radicalCocycle_mul representation (family (extension.rightHom x))]
  rw [first_term, third_term, fourth_term, mixedValue_apply]
  simp only [map_add]
  abel

/-- The mixed relative two-cocycle of a strict family. -/
def mixedRelative {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (law : StrictLaw splitting representation family) :
    relativeTwoCocycles extension.inl representation :=
  ⟨⟨mixedValue splitting representation family, mixedValue_mem splitting representation family law⟩, by
    intro first second
    change mixedValue splitting representation family (extension.inl first, extension.inl second) = 0
    rw [mixedValue_apply, extension.rightHom_inl, strictLaw_one_apply law, map_zero]⟩

theorem mixedRelative_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (law : StrictLaw splitting representation family) (first second : E) :
    (mixedRelative splitting representation family law).val (first, second) =
      mixedValue splitting representation family (first, second) := rfl

/-- **The mixed part of the mixed relative cocycle is the family itself.** -/
theorem splitEdgeCycle_mixedRelative {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E)
    (family : L → groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (law : StrictLaw splitting representation family) (levi : L) :
    splitEdgeCycle splitting representation levi (mixedRelative splitting representation family law) =
      family levi := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  rw [splitEdgeCycle_apply, mixedRelative_apply, mixedRelative_apply, mixedValue_apply,
    mixedValue_apply]
  simp only [splitRadicalCoordinate_splitting, splitting.rightHom_splitting, splitRadicalCoordinate_inl,
    extension.rightHom_inl, conjAct_splitRadicalInput, strictLaw_one_apply law, map_one, map_zero,
    Module.End.one_apply, sub_zero]

/-! ### Families from an equivariant cocycle-level section -/

/-- The family `ℓ ↦ σ(c ℓ)` attached to a Levi one-cocycle and a cocycle-level section. -/
def sectionFamily {extension : GroupExtension N E L} (representation : Rep ℂ E) (W : Rep ℂ L)
    (cocycleSection : W →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (cycle : groupCohomology.cocycles₁ W) (levi : L) :
    groupCohomology.cocycles₁ (Rep.res extension.inl representation) :=
  cocycleSection (cycle levi)

/-- An equivariant section turns Levi one-cocycles into strict families. -/
theorem sectionFamily_law {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (W : Rep ℂ L)
    (cocycleSection : W →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (equivariant : ∀ levi vector, cocycleSection (W.ρ levi vector) =
      splitRadicalCocycleAction splitting representation levi (cocycleSection vector))
    (cycle : groupCohomology.cocycles₁ W) :
    StrictLaw splitting representation (sectionFamily representation W cocycleSection cycle) := by
  intro first second radical
  change cocycleSection (cycle (first * second)) radical = _
  rw [oneCocycle_mul W cycle first second, map_add, equivariant]
  rfl

/-- The relative two-cocycle realising a Levi one-cocycle through an equivariant section. -/
def sectionRelative {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (W : Rep ℂ L)
    (cocycleSection : W →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (equivariant : ∀ levi vector, cocycleSection (W.ρ levi vector) =
      splitRadicalCocycleAction splitting representation levi (cocycleSection vector))
    (cycle : groupCohomology.cocycles₁ W) : relativeTwoCocycles extension.inl representation :=
  mixedRelative splitting representation (sectionFamily representation W cocycleSection cycle)
    (sectionFamily_law splitting representation W cocycleSection equivariant cycle)

/-- **Every section family is a Hochschild–Serre mixed part.** -/
theorem splitEdgeCycle_sectionRelative {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E) (W : Rep ℂ L)
    (cocycleSection : W →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res extension.inl representation))
    (equivariant : ∀ levi vector, cocycleSection (W.ρ levi vector) =
      splitRadicalCocycleAction splitting representation levi (cocycleSection vector))
    (cycle : groupCohomology.cocycles₁ W) (levi : L) :
    splitEdgeCycle splitting representation levi
        (sectionRelative splitting representation W cocycleSection equivariant cycle) =
      cocycleSection (cycle levi) :=
  splitEdgeCycle_mixedRelative splitting representation _ _ levi

end TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjSplit
