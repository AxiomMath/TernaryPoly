module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.StDelta
public import TernaryPeriodPolynomials.Building.RankTwo.HeightOne
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap

@[expose] public section


/-!
# Oriented chains of the Farey complex and the edge chains of oriented dual edges

Formalized by Claude Sonnet 5.5.

* `chAct`, `chD`: the action of `GL₂(ℤ)` on the library's oriented chains of cusps (`OrientedChainMap.map`), and its
  determinant twist.
* `orbVec`: the equivariant function on a transitive `Γ`-set with prescribed base value (generic).
* `iota`: finite divisors as zero-dimensional chains; `boundary_edge`: `∂[a, b] = [b] - [a]`.
* `theta1 q`: the oriented edge chain of an oriented dual edge (`det γ · [γ cusp₁, γ cusp₂]` for `q = γ • p0`),
  `Th1` its linear extension, and `boundary_Th1 : ∂ (Th1 x) = ι (piT x)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeDuality

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree
open scoped MonoidAlgebra Classical

/-- Relabeling of oriented chains of cusps by an integral matrix. -/
def chAct (g : IntegralGL) : OrientedListChains.Chain Line →ₗ[ℚ] OrientedListChains.Chain Line :=
  OrientedChainMap.map (fun L : Line => g • L)

theorem chAct_simplex (g : IntegralGL) (l : List Line) :
    chAct g (OrientedListChains.simplex l) = OrientedListChains.simplex (l.map (fun L => g • L)) :=
  OrientedChainMap.map_simplex _ _

theorem chAct_mul (g h : IntegralGL) (c : OrientedListChains.Chain Line) :
    chAct g (chAct h c) = chAct (g * h) c := by
  unfold chAct
  rw [OrientedChainMap.map_comp_apply]
  congr 2
  funext L
  exact (mul_smul g h L).symm

theorem chAct_one (c : OrientedListChains.Chain Line) : chAct 1 c = c := by
  unfold chAct
  have : (fun L : Line => (1 : IntegralGL) • L) = id := by funext L; exact one_smul _ L
  rw [this, OrientedChainMap.map_id]; rfl

theorem boundary_chAct (g : IntegralGL) (c : OrientedListChains.Chain Line) :
    OrientedListChains.boundary (chAct g c) = chAct g (OrientedListChains.boundary c) :=
  OrientedChainMap.boundary_map _ c

theorem chAct_cons (g : IntegralGL) (a : Line) (c : OrientedListChains.Chain Line) :
    chAct g (OrientedListChains.cons a c) = OrientedListChains.cons (g • a) (chAct g c) :=
  OrientedChainMap.map_cons _ a c

/-- The determinant-twisted action on oriented chains. -/
def chD : Representation ℚ IntegralGL (OrientedListChains.Chain Line) where
  toFun g := detQ g • chAct g
  map_one' := by
    apply LinearMap.ext
    intro c
    simp [chAct_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    simp only [map_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul, chAct_mul,
      mul_comm (detQ g)]

theorem chD_apply (g : IntegralGL) (c : OrientedListChains.Chain Line) :
    chD g c = detQ g • chAct g c := rfl

section Orbit

variable {X N : Type*} [MulAction IntegralGL X] [AddCommGroup N] [Module ℚ N]

/-- The equivariant function on a transitive `Γ`-set with prescribed value at the base point. -/
def orbVec (ρ : Representation ℚ IntegralGL N) (x0 : X) (htr : ∀ y : X, ∃ g : IntegralGL, g • x0 = y)
    (v0 : N) (y : X) : N :=
  ρ (Classical.choose (htr y)) v0

theorem orbVec_apply (ρ : Representation ℚ IntegralGL N) (x0 : X)
    (htr : ∀ y : X, ∃ g : IntegralGL, g • x0 = y) (v0 : N)
    (hv : ∀ s : IntegralGL, s • x0 = x0 → ρ s v0 = v0) (g : IntegralGL) :
    orbVec ρ x0 htr v0 (g • x0) = ρ g v0 := by
  set a := Classical.choose (htr (g • x0)) with ha
  have h : a • x0 = g • x0 := Classical.choose_spec (htr (g • x0))
  have hs : (g⁻¹ * a) • x0 = x0 := by rw [mul_smul, h, inv_smul_smul]
  unfold orbVec
  rw [← ha]
  calc ρ a v0 = ρ (g * (g⁻¹ * a)) v0 := by rw [mul_inv_cancel_left]
    _ = ρ g (ρ (g⁻¹ * a) v0) := by rw [map_mul]; rfl
    _ = ρ g v0 := by rw [hv _ hs]

theorem orbVec_smul (ρ : Representation ℚ IntegralGL N) (x0 : X)
    (htr : ∀ y : X, ∃ g : IntegralGL, g • x0 = y) (v0 : N)
    (hv : ∀ s : IntegralGL, s • x0 = x0 → ρ s v0 = v0) (g : IntegralGL) (y : X) :
    orbVec ρ x0 htr v0 (g • y) = ρ g (orbVec ρ x0 htr v0 y) := by
  obtain ⟨γ, rfl⟩ := htr y
  rw [← mul_smul, orbVec_apply ρ x0 htr v0 hv, orbVec_apply ρ x0 htr v0 hv, map_mul]
  rfl

end Orbit


/-- The finite divisors as zero-dimensional chains. -/
def iota : Divisors →ₗ[ℚ] OrientedListChains.Chain Line :=
  Finsupp.linearCombination ℚ (fun L : Line => OrientedListChains.simplex [L])

theorem iota_single (L : Line) (r : ℚ) :
    iota (Finsupp.single L r) = r • OrientedListChains.simplex [L] := by
  simp [iota]

theorem iota_symbol (L M : Line) :
    iota (symbol L M).val = OrientedListChains.simplex [M] - OrientedListChains.simplex [L] := by
  rw [symbol_val, map_sub, iota_single, iota_single, one_smul, one_smul]

theorem chAct_iota (g : IntegralGL) (c : Divisors) :
    chAct g (iota c) = iota (divisorAction (integral g) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | single L r =>
    rw [iota_single, divisorAction_single, iota_single, map_smul, chAct_simplex]
    rfl

theorem boundary_edge (a b : Line) :
    OrientedListChains.boundary (OrientedListChains.simplex [a, b]) =
      OrientedListChains.simplex [b] - OrientedListChains.simplex [a] := by
  simp [OrientedListChains.boundary_cons, OrientedListChains.cons_simplex]

/-- The reference edge chain. -/
def sig1 : OrientedListChains.Chain Line := OrientedListChains.simplex [cusp1, cusp2]

theorem boundary_sig1 : OrientedListChains.boundary sig1 = iota reference.val := by
  rw [sig1, boundary_edge, reference_eq, iota_symbol]

theorem chD_stab_sig1 (s : IntegralGL) (hs : s • p0 = p0) : chD s sig1 = sig1 := by
  rcases stab_p0_cusps s (MulAction.mem_stabilizer_iff.mpr hs) with ⟨h1, h2, hd⟩ | ⟨h1, h2, hd⟩
  · rw [chD_apply, sig1, chAct_simplex]
    simp only [List.map_cons, List.map_nil, h1, h2, hd, one_smul]
  · rw [chD_apply, sig1, chAct_simplex]
    simp only [List.map_cons, List.map_nil, h1, h2, hd]
    rw [OrientedListChains.simplex_swap_eq_neg cusp2 cusp1 []]
    exact (neg_one_smul ℚ _).trans (neg_neg _)

/-- The oriented edge chain of an oriented dual edge. -/
def theta1 : OTE → OrientedListChains.Chain Line := orbVec chD p0 ote_transitive sig1

theorem theta1_apply (γ : IntegralGL) : theta1 (γ • p0) = chD γ sig1 :=
  orbVec_apply chD p0 ote_transitive sig1 chD_stab_sig1 γ

theorem theta1_smul (g : IntegralGL) (q : OTE) : theta1 (g • q) = chD g (theta1 q) :=
  orbVec_smul chD p0 ote_transitive sig1 chD_stab_sig1 g q

/-- The edge chain map on the permutation module of oriented dual edges. -/
def Th1 : MonoidAlgebra ℚ OTE →ₗ[ℚ] OrientedListChains.Chain Line :=
  Finsupp.linearCombination ℚ theta1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem Th1_single (q : OTE) (r : ℚ) : Th1 (MonoidAlgebra.single q r) = r • theta1 q := by
  simp [Th1]

theorem boundary_theta1 (q : OTE) :
    OrientedListChains.boundary (theta1 q) = iota (edgeSym q).val := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  rw [theta1_apply, edgeSym_apply, chD_apply, map_smul, boundary_chAct, boundary_sig1,
    chAct_iota, stD_apply, Submodule.coe_smul, map_smul]
  rfl

theorem boundary_Th1 (x : MonoidAlgebra ℚ OTE) :
    OrientedListChains.boundary (Th1 x) = iota (piT.hom x).val := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]
  | single q r =>
    rw [Th1_single, piT_single, map_smul, boundary_theta1]
    simp

end TernaryPeriodPolynomials.Argument.HeckeDuality
