module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolEquiv
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Equiv
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Parabolic

@[expose] public section


/-!
# Lemma B.1, Stage 1: the Hom model of the residue comparison square

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3
(`app:Hecke-coordinate`), `lem:literal-residue-comparison`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction
open TernaryPoly.OrdinaryResidueSupport (rowAction rowAction_mul rowAction_one axis)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPoly.OrdinaryFullAction TernaryPoly.OrdinaryFullCoefficient

/-- `P_H`: the stabilizer in `G = GL₃(ℤ)` of the hyperplane `H = {a = 0}`, i.e. of its normal line
`axis 0`, for the library's action of integral matrices on rational normals. -/
def PH : Subgroup IntegralGL where
  carrier := {g | rowAction g (axis 0) = axis 0}
  mul_mem' := by
    intro g h hg hh
    change rowAction (g * h) (axis 0) = axis 0
    rw [rowAction_mul]
    have hg' : rowAction g (axis 0) = axis 0 := hg
    have hh' : rowAction h (axis 0) = axis 0 := hh
    rw [hg', hh']
  one_mem' := rowAction_one _
  inv_mem' := by
    intro g hg
    have hg' : rowAction g (axis 0) = axis 0 := hg
    change rowAction g⁻¹ (axis 0) = axis 0
    nth_rewrite 1 [← hg']
    rw [← rowAction_mul, mul_inv_cancel, rowAction_one]

theorem mem_PH {g : IntegralGL} : g ∈ PH ↔ rowAction g (axis 0) = axis 0 := Iff.rfl

/-- The action of `P_H` on the `H`-summand `R_{n,H}` of the residue module `R_n ⊗ det⁻¹`:
act by the full residue action and read off the `H`-component. -/
def fiberAction (n : ℕ) (g : IntegralGL) :
    ResidueFiber n (axis 0) →ₗ[ℚ] ResidueFiber n (axis 0) :=
  (component n (axis 0)).comp ((integralResidueAction n (-1) g).comp
    (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0)))

/-- The `H`-component of the residue action of `g ∈ P_H` only sees the `H`-component of the
argument: the radical and the other hyperplanes do not interfere. -/
theorem component_equivariant (n : ℕ) (g : IntegralGL) (hg : g ∈ PH) (r : Residues n) :
    component n (axis 0) (integralResidueAction n (-1) g r) =
      fiberAction n g (component n (axis 0) r) := by
  have h := component_action_factor n (-1) g (axis 0)
  have hg' : rowAction g (axis 0) = axis 0 := hg
  rw [hg'] at h
  exact LinearMap.congr_fun h r

/-- `Hom_{P_H}(St, R_{n,H} ⊗ det⁻¹)`: linear maps from the Steinberg module (the ordinary incidence
cycles) to the `H`-fibre, equivariant for the stabilizer `P_H` of `H = {a = 0}`. -/
def StabHom (n : ℕ) :
    Submodule ℚ (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)) where
  carrier := {φ | ∀ g ∈ PH, ∀ c, φ (cycleAction (integral g) c) = fiberAction n g (φ c)}
  zero_mem' := by intro g _ c; simp
  add_mem' := by
    intro f h hf hh g hg c
    simp only [LinearMap.add_apply, map_add]
    rw [hf g hg c, hh g hg c]
  smul_mem' := by
    intro q f hf g hg c
    simp only [LinearMap.smul_apply, map_smul]
    rw [hf g hg c]

/-- **Sh** (Frobenius reciprocity for `Hom`): restrict a `G`-equivariant map to the stabilizer and
project onto the `H`-summand of `R_n = ⊕_H R_{n,H}`. -/
def Sh (n : ℕ) : ResidueHom n (-1) →ₗ[ℚ] StabHom n where
  toFun F := ⟨(component n (axis 0)).comp F.val, by
    intro g hg c
    change component n (axis 0) (F.val (cycleAction (integral g) c)) =
      fiberAction n g (component n (axis 0) (F.val c))
    rw [F.property g c]
    exact component_equivariant n g hg _⟩
  map_add' F G := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    change component n (axis 0) ((F.val + G.val) c) = _
    simp only [LinearMap.add_apply, map_add]
    rfl
  map_smul' a F := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    change component n (axis 0) ((a • F.val) c) = _
    simp only [LinearMap.smul_apply, map_smul]
    rfl

theorem blockEmbed_mem_PH (g : RankTwoAugmentedFrames.IntegralGL) :
    OrdinaryPlaneEdge.blockEmbed g ∈ PH := by
  rw [mem_PH]
  have hv : Matrix.vecMul (Pi.single 0 (1 : ℤ)) (OrdinaryPlaneEdge.blockEmbed g).val =
      Pi.single 0 1 := by
    funext j
    fin_cases j <;> simp [OrdinaryPlaneEdge.blockEmbed, OrdinaryPlaneEdge.diagonalBlock,
      Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  change rowAction _ (OrdinaryResidueSupport.normalOfRow _ _) = OrdinaryResidueSupport.normalOfRow _ _
  rw [OrdinaryResidueSupport.rowAction_normalOfRow]
  exact (OrdinaryResidueSupport.normalOfRow_eq_iff _ _).mpr (Or.inl hv)

/-- The Levi quotient: the block-embedded `GL₂(ℤ)` acts on the fibre by the determinant-inverse
twisted substitution `q ↦ det(C)⁻¹ q(C⁻¹(b,c))`, exactly the binary coefficient action. -/
theorem fiber_block (n : ℕ) (g : RankTwoAugmentedFrames.IntegralGL) (x : ResidueFiber n (axis 0)) :
    literalFiberMap n 0 (fiberAction n (OrdinaryPlaneEdge.blockEmbed g) x) =
      BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1)
        (BinaryModularSymbol.integral g) (literalFiberMap n 0 x) := by
  have hg3 : (integral (OrdinaryPlaneEdge.blockEmbed g)).val =
      OrdinaryResidueParabolic.blockMatrix 1 0 (BinaryModularSymbol.integral g) := by
    rw [OrdinaryPlaneEdge.blockEmbed_integral]
    rfl
  have h := OrdinaryResidueParabolic.coordinateTuple_action n (integral (OrdinaryPlaneEdge.blockEmbed g))
    1 0 (BinaryModularSymbol.integral g) hg3
    (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) x)
  rw [OrdinaryResidueSymbol.coefficient_action] at h
  have e : coordinateTuple n (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) x) 0 =
      literalFiberMap n 0 x := by
    simp [coordinateTuple]
  rw [e] at h
  exact h

/-- **κ**: restriction of a `P_H`-equivariant map to the binary Steinberg module along the plane
cone (`OrdinaryPlaneEdge.binaryCone`: a binary modular symbol is coned to the incidence cycles
through the exterior line `⟨e₁⟩`), followed by the literal coordinate `R_{n,H} ≅ D_{n+1}`. -/
def kappa (n : ℕ) : StabHom n →ₗ[ℚ] BinaryModularSymbol.PeriodHom (n+1) where
  toFun φ := ⟨(literalFiberMap n 0).comp (φ.val.comp OrdinaryPlaneEdge.binaryCone), by
    intro g c
    change literalFiberMap n 0 (φ.val (OrdinaryPlaneEdge.binaryCone
      (BinaryModularSymbol.action (BinaryModularSymbol.integral g) c))) =
      BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1)
        (BinaryModularSymbol.integral g) (literalFiberMap n 0 (φ.val (OrdinaryPlaneEdge.binaryCone c)))
    rw [OrdinaryPlaneEdge.binaryCone_equivariant, ← OrdinaryPlaneEdge.blockEmbed_integral,
      φ.property _ (blockEmbed_mem_PH g), fiber_block]⟩
  map_add' φ ψ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    change literalFiberMap n 0 ((φ.val + ψ.val) _) = _
    simp only [LinearMap.add_apply, map_add]
    rfl
  map_smul' a φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    change literalFiberMap n 0 ((a • φ.val) _) = _
    simp only [LinearMap.smul_apply, map_smul]
    rfl

/-- The composite `κ ∘ Sh` is the library's literal plane-cone restriction `toBinaryHom`. -/
theorem kappa_Sh (n : ℕ) (F : ResidueHom n (-1)) :
    kappa n (Sh n F) = OrdinaryResidueSymbol.toBinaryHom n F := rfl

/-- **`res_H`**: the literal residue coordinate at `a = 0` of the value on the reference apartment. -/
def resH (n : ℕ) : ResidueHom n (-1) →ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n+1) :=
  OrdinaryResiduePeriod.coordinateMap n

theorem resH_val (n : ℕ) (F : ResidueHom n (-1)) :
    (resH n F).val = literalFiberMap n 0
      (component n (axis 0) (F.val (OrdinaryApartmentPresentation.frameCycle 1))) := rfl

/-- **`edge₂`**: the value of a binary modular-symbol Hom on the standard well-rounded edge, i.e. on
the reference symbol (the symbol joining the first and second coordinate lines). -/
def edge2 (n : ℕ) : BinaryModularSymbol.PeriodHom (n+1) →ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n+1) :=
  BinaryModularSymbol.periodEvaluation (n+1)

/-- **Lemma B.1, Hom model**: `edge₂ ∘ κ ∘ Sh = res_H`, with scalar exactly `1`. -/
theorem residue_comparison_square (n : ℕ) (F : ResidueHom n (-1)) :
    edge2 n (kappa n (Sh n F)) = resH n F := by
  rw [kappa_Sh]
  exact BinaryModularSymbol.periodEvaluation_restriction n F

theorem Sh_injective (n : ℕ) : Function.Injective (Sh n) := by
  intro F G h
  apply OrdinaryResidueSymbol.toBinaryHom_injective
  rw [← kappa_Sh, ← kappa_Sh, h]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
