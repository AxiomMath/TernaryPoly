module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLRel
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDLefschetz
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviCrossedAction

@[expose] public section


/-!
# Poincare-Lefschetz pairings `H¹_c(E) × H¹(E*)` and `H¹(E) × H¹_c(E*)`, and the pairing of the images

Formalized by Claude Sonnet 5.5.

For a group `Γ` with `ι : N → Γ` and two elements `a, g₂ ∈ N` (the fundamental group of the three-punctured sphere, triple model of
`AxiomCodeBoundaryDuality`), a representation `ρ` with a dual representation `ρ'` and an invariant perfect pairing `B`, and cohomology
models of `H¹(Γ, ρ)`, `H¹(Γ, ρ')` (a `Model`: linear surjection `f` from a module `K` of cocycles with kernel the coboundaries):

* `Setup.j : Hc ρ → H¹(Γ, ρ)` (`jMap`) is the TRUE compact-support map: `Hc` is the cone of the restriction to the cyclic peripheral
  subgroups (`relCocycles`, `relBoundaries` of `FacePDBinaryPLRel`), and `j` forgets the primitives.  Its kernel is the image of `H⁰`
  of the cusp subgroups (`Model.jMap_eq_zero_iff`); its image is the space of parabolic classes (`Model.range_jMap`), the classes
  whose values at the cusps are coboundaries;
* `Setup.PD : Hc ρ × H¹(Γ, ρ') → ℂ` is the Poincare-Lefschetz cup formula, `Setup.PDt : H¹(Γ, ρ) × Hc ρ' → ℂ` is minus the transpose of the
  pairing for the dual system, and `Setup.hT` (`PD a (j' b) = PDt (j a) b`: `j'` is the transpose of `j`) is the skew-symmetry of the
  cup product (`pdRaw_skew`);
* `Setup.PDt_nondegenerate`, `Setup.PD_nondegenerate`: the `H¹` side of each Poincare-Lefschetz pairing has zero kernel: the classes of
  `H⁰` of the cusp subgroups force a class annihilating `Hc` to be parabolic (`Setup.exists_primitive_of_PDt_zero`), and then the
  library's parabolic Poincare duality (`CochainNondegenerate`) applies;
* For the index-two groups (`Γ₁'(3)`, `GL₂(ℤ)`) the cohomology `Hc` is taken relative to the cyclic cusp subgroups of the index-two
  subgroup `ι N` (the primitives are those of the restrictions to `ι N`); `j` still has exactly the parabolic classes as image and
  `PD`, `PDt` are the cup pairings of the groups themselves, but the kernel of `j` is the image of `H⁰` of the cyclic subgroups
  (fixed vectors of `T`), which is larger than the image of `H⁰` of the full cusp stabilizers (which contain a reflection);
  neither the image of `j`, nor the pairing of the images, nor the nondegeneracy statements are affected;
* `Setup.imagePairing` is the abstract Lefschetz pairing (`Lefschetz.imagePairing`) of the images, nondegenerate on both sides
  (`Setup.imagePairing_left_nondegenerate`, `_right_nondegenerate`), and it is the library's parabolic cup pairing
  (`Setup.imagePairing_eq_parabolicPairing`, `Setup.imagePairing_mk`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL

open TernaryPeriodPolynomials.BoundaryDuality
open TripleModel LinearDuality CocycleBridge EpsilonSplit ParabolicDuality
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers (crossedCocycles)

section ModelSec

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V]

/-- A cohomology model of `H¹(Γ, ρ)`: a linear surjection `f` from a module `K` of one-cocycles (identified with the crossed
homomorphisms through the injective `c` with the full range) onto `H`, with kernel the coboundaries. -/
structure Model (ρ : Representation ℂ Γ V) (K H : Type) [AddCommGroup K] [Module ℂ K] [AddCommGroup H]
    [Module ℂ H] where
  c : K →ₗ[ℂ] (Γ → V)
  f : K →ₗ[ℂ] H
  isCocycle : ∀ y, IsCocycle ρ (c y)
  inj : Function.Injective c
  surj : ∀ Z, IsCocycle ρ Z → ∃ y, c y = Z
  ker : ∀ y, f y = 0 ↔ ∃ u : V, ∀ γ, c y γ = ρ γ u - u
  fsurj : Function.Surjective f

variable {ρ : Representation ℂ Γ V} {K H : Type} [AddCommGroup K] [Module ℂ K] [AddCommGroup H]
  [Module ℂ H]

/-- The model's cocycles are the crossed homomorphisms. -/
def Model.cocycleEquiv (M : Model ρ K H) : K ≃ₗ[ℂ] crossedCocycles ρ :=
  LinearEquiv.ofBijective (M.c.codRestrict (crossedCocycles ρ) M.isCocycle)
    ⟨fun y₁ y₂ h => M.inj (congrArg Subtype.val h), fun Z => by
      obtain ⟨y, hy⟩ := M.surj Z.1 Z.2
      exact ⟨y, Subtype.ext hy⟩⟩

theorem Model.cocycleEquiv_apply (M : Model ρ K H) (y : K) : (M.cocycleEquiv y).1 = M.c y := rfl

end ModelSec


section Maps

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {ι : N →* Γ} {ρ : Representation ℂ Γ V} {ρ' : Representation ℂ Γ W} {a g₂ : N}
  {K H K' H' : Type} [AddCommGroup K] [Module ℂ K] [AddCommGroup H] [Module ℂ H] [AddCommGroup K']
  [Module ℂ K'] [AddCommGroup H'] [Module ℂ H']

/-- The underlying crossed homomorphism of a relative cocycle. -/
def relToCocycle (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N) :
    relCocycles ι ρ a g₂ →ₗ[ℂ] crossedCocycles ρ :=
  ((LinearMap.fst ℂ (Γ → V) (V × V × V)).comp (relCocycles ι ρ a g₂).subtype).codRestrict
    (crossedCocycles ρ) (fun x => x.2.1)

/-- The cohomology-model element of a relative cocycle. -/
def relToK (M : Model ρ K H) (ι : N →* Γ) (a g₂ : N) : relCocycles ι ρ a g₂ →ₗ[ℂ] K :=
  M.cocycleEquiv.symm.toLinearMap.comp (relToCocycle ι ρ a g₂)

theorem c_relToK (M : Model ρ K H) (x : relCocycles ι ρ a g₂) :
    M.c (relToK M ι a g₂ x) = x.1.1 := by
  have h := congrArg Subtype.val (M.cocycleEquiv.apply_symm_apply (relToCocycle ι ρ a g₂ x))
  exact h

/-- **The map `j : H¹_c(Γ, ρ) → H¹(Γ, ρ)`** forgetting the primitives. -/
def jMap (M : Model ρ K H) (ι : N →* Γ) (a g₂ : N) (F : Submodule ℂ (V × V × V)) :
    Hc ι ρ a g₂ F →ₗ[ℂ] H :=
  (relBoundaries ι ρ a g₂ F).liftQ (M.f.comp (relToK M ι a g₂)) (by
    rintro x ⟨u, f, hf, hx1, hx2⟩
    show M.f (relToK M ι a g₂ x) = 0
    exact (M.ker _).2 ⟨u, fun γ => by rw [c_relToK, hx1]⟩)

theorem jMap_mk (M : Model ρ K H) (F : Submodule ℂ (V × V × V)) (x : relCocycles ι ρ a g₂) :
    jMap M ι a g₂ F (Submodule.Quotient.mk x) = M.f (relToK M ι a g₂ x) := rfl

end Maps


section Pairings

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {K H K' H' : Type} [AddCommGroup K] [Module ℂ K] [AddCommGroup H] [Module ℂ H]
  [AddCommGroup K'] [Module ℂ K'] [AddCommGroup H'] [Module ℂ H']

/-- The condition on the ignored subspace `F`: its vectors pair to zero with the values of crossed homomorphisms of the dual
system at the special elements (true for fixed vectors of torsion special elements). -/
def IgnoredFor (ι : N →* Γ) (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (F : Submodule ℂ (V × V × V)) : Prop :=
  ∀ f ∈ F, ∀ Z' : Γ → W, IsCocycle ρ' Z' →
    B f.1 (Z' (ι a)) + B f.2.1 (Z' (ι g₂)) + B f.2.2 (Z' (ι (a * g₂)⁻¹)) = 0

/-- The pairing of `H¹_c(Γ, ρ)` with the cocycles of the model of the dual system. -/
def pdQ (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (a g₂ : N) (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (F : Submodule ℂ (V × V × V))
    (hF : IgnoredFor ι ρ' B a g₂ F) (M' : Model ρ' K' H') : Hc ι ρ a g₂ F →ₗ[ℂ] K' →ₗ[ℂ] ℂ :=
  (relBoundaries ι ρ a g₂ F).liftQ ((pdRaw ι ρ ρ' B a g₂).compl₂ M'.c) (by
    intro x hx
    ext y'
    exact pdRaw_boundary_left hinv hF hx (M'.isCocycle y'))

theorem pdQ_mk (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    (F : Submodule ℂ (V × V × V)) (hF : IgnoredFor ι ρ' B a g₂ F) (M' : Model ρ' K' H')
    (x : relCocycles ι ρ a g₂) (y : K') :
    pdQ ι ρ ρ' B a g₂ hinv F hF M' (Submodule.Quotient.mk x) y = pdRaw ι ρ ρ' B a g₂ x (M'.c y) := rfl

theorem pdQ_ker (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    (F : Submodule ℂ (V × V × V)) (hF : IgnoredFor ι ρ' B a g₂ F) (M' : Model ρ' K' H')
    (c : Hc ι ρ a g₂ F) (y : K') (hy : M'.f y = 0) : pdQ ι ρ ρ' B a g₂ hinv F hF M' c y = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨w, hw⟩ := (M'.ker y).1 hy
  rw [pdQ_mk]
  have : M'.c y = fun g => ρ' g w - w := funext hw
  rw [this]
  exact pdRaw_boundary_right hinv x w

/-- **The Poincare-Lefschetz pairing `H¹_c(E) × H¹(E*) → ℂ`.** -/
def PD (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (a g₂ : N) (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (F : Submodule ℂ (V × V × V))
    (hF : IgnoredFor ι ρ' B a g₂ F) (M' : Model ρ' K' H') : Hc ι ρ a g₂ F →ₗ[ℂ] H' →ₗ[ℂ] ℂ :=
  ((((LinearMap.ker M'.f).liftQ (pdQ ι ρ ρ' B a g₂ hinv F hF M').flip (by
    intro y hy
    refine LinearMap.ext fun c => ?_
    exact pdQ_ker ι ρ ρ' B a g₂ hinv F hF M' c y hy)).comp
      (M'.f.quotKerEquivOfSurjective M'.fsurj).symm.toLinearMap).flip)

theorem PD_apply (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    (F : Submodule ℂ (V × V × V)) (hF : IgnoredFor ι ρ' B a g₂ F) (M' : Model ρ' K' H')
    (x : relCocycles ι ρ a g₂) (y : K') :
    PD ι ρ ρ' B a g₂ hinv F hF M' (Submodule.Quotient.mk x) (M'.f y) =
      pdRaw ι ρ ρ' B a g₂ x (M'.c y) := by
  have h : (M'.f.quotKerEquivOfSurjective M'.fsurj).symm (M'.f y) = Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [PD, LinearMap.flip_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h]
  rfl

end Pairings


section Skew

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

/-- **Transposition for relative cocycles**: the Poincare-Lefschetz cup formula of two relative cocycles is skew-symmetric
under exchanging the roles of the system and its dual. -/
theorem pdRaw_skew (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    (x : relCocycles ι ρ a g₂) (x' : relCocycles ι ρ' a g₂) :
    pdRaw ι ρ ρ' B a g₂ x x'.1.1 = -pdRaw ι ρ' ρ B.flip a g₂ x' x.1.1 := by
  have hinv₁ : ∀ (n : N) (x : V) (y : W), B ((ρ.comp ι) n x) ((ρ'.comp ι) n y) = B x y := hinv
  have hinv₂ : ∀ (n : N) (y : W) (x : V),
      B.flip ((ρ'.comp ι) n y) ((ρ.comp ι) n x) = B.flip y x := fun n y x => hinv n x y
  have hz : IsCocycle (ρ.comp ι) (fun n => x.1.1 (ι n)) := isCocycle_comp x.2.1 ι
  have hz' : IsCocycle (ρ'.comp ι) (fun n => x'.1.1 (ι n)) := isCocycle_comp x'.2.1 ι
  rw [pdRaw_apply, pdRaw_apply,
    cupFormula_eq_tripleForm hinv₁ hz x.2.2 x'.2.2,
    cupFormula_eq_tripleForm hinv₂ hz' x'.2.2 x.2.2]
  have := tripleForm_skew hinv₁ a g₂ (x.2.2.mem_tripleCycles hz) (x'.2.2.mem_tripleCycles hz')
  exact eq_neg_of_add_eq_zero_left this

end Skew


section SetupSec

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {K H K' H' : Type} [AddCommGroup K] [Module ℂ K] [AddCommGroup H] [Module ℂ H]
  [AddCommGroup K'] [Module ℂ K'] [AddCommGroup H'] [Module ℂ H']

/-- **The data of a Poincare-Lefschetz instance for the binary Levi**: a group `Γ` with a homomorphism `ι : N → Γ` and two elements
`a, g₂ ∈ N` (the three special elements of the triple model), a system `ρ` and a dual system `ρ'` with an invariant pairing `B`,
cohomology models of both, and the ignored subspaces `F ⊆ V³`, `F' ⊆ W³`. -/
structure Setup (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (K H K' H' : Type) [AddCommGroup K] [Module ℂ K]
    [AddCommGroup H] [Module ℂ H] [AddCommGroup K'] [Module ℂ K'] [AddCommGroup H'] [Module ℂ H'] where
  hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w
  M : Model ρ K H
  M' : Model ρ' K' H'
  F : Submodule ℂ (V × V × V)
  F' : Submodule ℂ (W × W × W)
  hF : IgnoredFor ι ρ' B a g₂ F
  hF' : IgnoredFor ι ρ B.flip a g₂ F'

variable {ι : N →* Γ} {ρ : Representation ℂ Γ V} {ρ' : Representation ℂ Γ W}
  {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {a g₂ : N}

/-- The setup with the roles of the system and its dual exchanged. -/
def Setup.swap (S : Setup ι ρ ρ' B a g₂ K H K' H') : Setup ι ρ' ρ B.flip a g₂ K' H' K H where
  hinv := fun n w v => S.hinv n v w
  M := S.M'
  M' := S.M
  F := S.F'
  F' := S.F
  hF := S.hF'
  hF' := S.hF

/-- **`j : H¹_c(Γ, ρ) → H¹(Γ, ρ)`.** -/
def Setup.j (S : Setup ι ρ ρ' B a g₂ K H K' H') : Hc ι ρ a g₂ S.F →ₗ[ℂ] H :=
  jMap S.M ι a g₂ S.F

/-- **`j' : H¹_c(Γ, ρ') → H¹(Γ, ρ')`** for the dual system. -/
def Setup.j' (S : Setup ι ρ ρ' B a g₂ K H K' H') : Hc ι ρ' a g₂ S.F' →ₗ[ℂ] H' :=
  jMap S.M' ι a g₂ S.F'

/-- **The Poincare-Lefschetz pairing `PD : H¹_c(E) × H¹(E*) → ℂ`.** -/
def Setup.PD (S : Setup ι ρ ρ' B a g₂ K H K' H') : Hc ι ρ a g₂ S.F →ₗ[ℂ] H' →ₗ[ℂ] ℂ :=
  BinaryPL.PD ι ρ ρ' B a g₂ S.hinv S.F S.hF S.M'

/-- **The Poincare-Lefschetz pairing `PD' : H¹(E) × H¹_c(E*) → ℂ`**, minus the transpose of the pairing for the dual system. -/
def Setup.PDt (S : Setup ι ρ ρ' B a g₂ K H K' H') : H →ₗ[ℂ] Hc ι ρ' a g₂ S.F' →ₗ[ℂ] ℂ :=
  -(S.swap.PD).flip

theorem Setup.PD_mk (S : Setup ι ρ ρ' B a g₂ K H K' H') (x : relCocycles ι ρ a g₂) (y : K') :
    S.PD (Submodule.Quotient.mk x) (S.M'.f y) = pdRaw ι ρ ρ' B a g₂ x (S.M'.c y) :=
  PD_apply ι ρ ρ' B a g₂ S.hinv S.F S.hF S.M' x y

theorem Setup.PDt_mk (S : Setup ι ρ ρ' B a g₂ K H K' H') (y : K) (x' : relCocycles ι ρ' a g₂) :
    S.PDt (S.M.f y) (Submodule.Quotient.mk x') = -pdRaw ι ρ' ρ B.flip a g₂ x' (S.M.c y) := by
  exact congrArg Neg.neg (Setup.PD_mk S.swap x' y)

/-- **`j'` is the transpose of `j`** for the Poincare-Lefschetz pairings. -/
theorem Setup.hT (S : Setup ι ρ ρ' B a g₂ K H K' H') (c : Hc ι ρ a g₂ S.F) (c' : Hc ι ρ' a g₂ S.F') :
    S.PD c (S.j' c') = S.PDt (S.j c) c' := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  have e1 : S.j' (Submodule.Quotient.mk x') = S.M'.f (relToK S.M' ι a g₂ x') := rfl
  have e2 : S.j (Submodule.Quotient.mk x) = S.M.f (relToK S.M ι a g₂ x) := rfl
  rw [e1, e2, Setup.PD_mk, Setup.PDt_mk, c_relToK, c_relToK]
  exact pdRaw_skew ι ρ ρ' B a g₂ S.hinv x x'

end SetupSec


section Slots

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

/-- The relative cocycle `(0, f)` supported at the cusps: the zero crossed homomorphism with primitives `f`, which are fixed
vectors of the special elements.  These are the classes of `H⁰` of the peripheral subgroups. -/
def slotClass (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N) (f : V × V × V)
    (hf : IsPrimitive (ρ.comp ι) a g₂ (fun _ : N => (0 : V)) f) : relCocycles ι ρ a g₂ :=
  ⟨(0, f), ⟨fun g h => by simp, hf⟩⟩

theorem pdRaw_slotClass (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (f : V × V × V)
    (hf : IsPrimitive (ρ.comp ι) a g₂ (fun _ : N => (0 : V)) f) (Z' : Γ → W) :
    pdRaw ι ρ ρ' B a g₂ (slotClass ι ρ a g₂ f hf) Z' =
      -(B f.1 (Z' (ι a)) + B f.2.1 (Z' (ι g₂)) + B f.2.2 (Z' (ι (a * g₂)⁻¹))) := by
  rw [pdRaw_apply]
  simp [slotClass, cupFormula]

theorem isPrimitive_slot₁ (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N) {w : V}
    (hw : ρ (ι a) w = w) : IsPrimitive (ρ.comp ι) a g₂ (fun _ : N => (0 : V)) (w, 0, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : V) = (ρ (ι a) - 1) w
    simp [hw]
  · show (0 : V) = (ρ (ι g₂) - 1) 0
    simp
  · show (0 : V) = (ρ (ι (a * g₂)⁻¹) - 1) 0
    simp

theorem isPrimitive_slot₂ (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N) {w : V}
    (hw : ρ (ι g₂) w = w) : IsPrimitive (ρ.comp ι) a g₂ (fun _ : N => (0 : V)) (0, w, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : V) = (ρ (ι a) - 1) 0
    simp
  · show (0 : V) = (ρ (ι g₂) - 1) w
    simp [hw]
  · show (0 : V) = (ρ (ι (a * g₂)⁻¹) - 1) 0
    simp

theorem isPrimitive_slot₃ (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N) {w : V}
    (hw : ρ (ι (a * g₂)⁻¹) w = w) :
    IsPrimitive (ρ.comp ι) a g₂ (fun _ : N => (0 : V)) (0, 0, w) := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : V) = (ρ (ι a) - 1) 0
    simp
  · show (0 : V) = (ρ (ι g₂) - 1) 0
    simp
  · show (0 : V) = (ρ (ι (a * g₂)⁻¹) - 1) w
    rw [LinearMap.sub_apply, Module.End.one_apply, hw, sub_self]

end Slots

section PerfectAlgebra

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ρ : Representation ℂ G V}
  {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- **Duality for the image of `g - 1`**: a vector orthogonal to the fixed vectors of the dual action is a coboundary
`(g - 1) t` (perfect invariant pairing of finite-dimensional spaces). -/
theorem exists_sub_of_pair_fixed (hL : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hR : ∀ w, (∀ v, B v w = 0) → w = 0) (g : G) (hinv : ∀ v w, B (ρ g v) (ρ' g w) = B v w)
    {u : V} (h : ∀ w, ρ' g w = w → B u w = 0) : ∃ t, u = (ρ g - 1) t := by
  by_contra hne
  have hnot : u ∉ LinearMap.range (ρ g - 1) := fun hm => by
    obtain ⟨t, ht⟩ := hm
    exact hne ⟨t, ht.symm⟩
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_notMem hnot
  obtain ⟨w, hw⟩ := exists_pairing_right hL hR φ
  have hfix : ρ' g w = w := by
    have h1 : ∀ t, B t ((ρ' g⁻¹ - 1) w) = 0 := by
      intro t
      have h0 : φ ((ρ g - 1) t) = 0 := LinearMap.mem_ker.1 (hle ⟨t, rfl⟩)
      rw [hw] at h0
      have e : B (ρ g t) w = B t (ρ' g⁻¹ w) := by
        have := hinv t (ρ' g⁻¹ w)
        rw [rep_apply_inv ρ'] at this
        exact this
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub] at h0 ⊢
      linear_combination h0 - e
    have h2 : (ρ' g⁻¹ - 1) w = 0 := hR _ h1
    have h3 : ρ' g⁻¹ w = w := by
      simpa [sub_eq_zero] using h2
    calc ρ' g w = ρ' g (ρ' g⁻¹ w) := by rw [h3]
      _ = w := rep_apply_inv ρ' g w
  exact hφ (by rw [hw]; exact h w hfix)

end PerfectAlgebra


section Kernels

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {K H K' H' : Type}
  [AddCommGroup K] [Module ℂ K] [AddCommGroup H] [Module ℂ H] [AddCommGroup K'] [Module ℂ K']
  [AddCommGroup H'] [Module ℂ H'] {ι : N →* Γ} {ρ : Representation ℂ Γ V}
  {ρ' : Representation ℂ Γ W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {a g₂ : N}

/-- **The cusp step.**  A class of `H¹(Γ, ρ)` which pairs to zero with all of `H¹_c(Γ, ρ')` has a representative with a
primitive triple, i.e. it is parabolic: the classes of `H⁰` of the peripheral subgroups detect the failure to be a
coboundary at each special element. -/
theorem Setup.exists_primitive_of_PDt_zero (S : Setup ι ρ ρ' B a g₂ K H K' H')
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0) (y : K)
    (h : ∀ c', S.PDt (S.M.f y) c' = 0) :
    ∃ v : V × V × V, IsPrimitive (ρ.comp ι) a g₂ (fun n => S.M.c y (ι n)) v := by
  have key : ∀ (f : W × W × W) (hf : IsPrimitive (ρ'.comp ι) a g₂ (fun _ : N => (0 : W)) f),
      B (S.M.c y (ι a)) f.1 + B (S.M.c y (ι g₂)) f.2.1 + B (S.M.c y (ι (a * g₂)⁻¹)) f.2.2 = 0 := by
    intro f hf
    have := h (Submodule.Quotient.mk (slotClass ι ρ' a g₂ f hf))
    rw [Setup.PDt_mk, pdRaw_slotClass] at this
    simpa using this
  obtain ⟨t₁, ht₁⟩ := exists_sub_of_pair_fixed (ρ := ρ) (ρ' := ρ') hL hR (ι a) (S.hinv a)
    (u := S.M.c y (ι a)) (fun w hw => by
      have := key (w, 0, 0) (isPrimitive_slot₁ ι ρ' a g₂ hw)
      simpa using this)
  obtain ⟨t₂, ht₂⟩ := exists_sub_of_pair_fixed (ρ := ρ) (ρ' := ρ') hL hR (ι g₂) (S.hinv g₂)
    (u := S.M.c y (ι g₂)) (fun w hw => by
      have := key (0, w, 0) (isPrimitive_slot₂ ι ρ' a g₂ hw)
      simpa using this)
  obtain ⟨t₃, ht₃⟩ := exists_sub_of_pair_fixed (ρ := ρ) (ρ' := ρ') hL hR (ι (a * g₂)⁻¹)
    (S.hinv (a * g₂)⁻¹) (u := S.M.c y (ι (a * g₂)⁻¹)) (fun w hw => by
      have := key (0, 0, w) (isPrimitive_slot₃ ι ρ' a g₂ hw)
      simpa using this)
  exact ⟨(t₁, t₂, t₃), ht₁, ht₂, ht₃⟩

/-- **Nondegeneracy of `PD' : H¹(E) × H¹_c(E*) → ℂ` on the `H¹(E)` side**: a class pairing to zero with all of `H¹_c(E*)` is zero.
This is the left parabolic Poincare duality of the library (`CochainNondegenerate`) after the cusp step. -/
theorem Setup.PDt_nondegenerate (S : Setup ι ρ ρ' B a g₂ K H K' H')
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (nd : CochainNondegenerate ι ρ ρ' B a g₂) (x : H) (h : ∀ c', S.PDt x c' = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := S.M.fsurj x
  obtain ⟨v, hv⟩ := S.exists_primitive_of_PDt_zero hL hR y h
  refine (S.M.ker y).2 (nd (S.M.c y) ⟨S.M.isCocycle y, v, hv⟩ ?_)
  rintro Z' ⟨hZ', v', hv'⟩
  have e := pairFun_eq_cupFormula ι ρ ρ' B a g₂ S.hinv (S.M.isCocycle y) hv ⟨hZ', v', hv'⟩
  let x0 : relCocycles ι ρ a g₂ := ⟨(S.M.c y, v), S.M.isCocycle y, hv⟩
  let x' : relCocycles ι ρ' a g₂ := ⟨(Z', v'), hZ', hv'⟩
  have e2 : pdRaw ι ρ ρ' B a g₂ x0 x'.1.1 = -pdRaw ι ρ' ρ B.flip a g₂ x' x0.1.1 :=
    pdRaw_skew ι ρ ρ' B a g₂ S.hinv x0 x'
  have e3 := h (Submodule.Quotient.mk x')
  rw [Setup.PDt_mk] at e3
  rw [e]
  have e4 : pdRaw ι ρ ρ' B a g₂ x0 Z' = 0 := by
    have : -pdRaw ι ρ' ρ B.flip a g₂ x' (S.M.c y) = 0 := e3
    exact e2.trans this
  exact e4

/-- **Nondegeneracy of `PD : H¹_c(E) × H¹(E*) → ℂ` on the `H¹(E*)` side** (the previous theorem for the dual system). -/
theorem Setup.PD_nondegenerate (S : Setup ι ρ ρ' B a g₂ K H K' H')
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (nd : CochainNondegenerate ι ρ' ρ B.flip a g₂) (y : H') (h : ∀ c, S.PD c y = 0) : y = 0 :=
  S.swap.PDt_nondegenerate (B := B.flip) (fun w hw => hR w (fun v => hw v)) (fun v hv => hL v (fun w => hv w))
    nd y (fun c => by
      have : S.PD c y = 0 := h c
      exact neg_eq_zero.2 this)

end Kernels


section Identification

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {K H K' H' : Type}
  [AddCommGroup K] [Module ℂ K] [AddCommGroup H] [Module ℂ H] [AddCommGroup K'] [Module ℂ K']
  [AddCommGroup H'] [Module ℂ H'] {ι : N →* Γ} {ρ : Representation ℂ Γ V}
  {ρ' : Representation ℂ Γ W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {a g₂ : N}

/-- **The image of `j` is the space of parabolic (cuspidal) classes**: the classes of `H¹(Γ, ρ)` represented by a crossed
homomorphism whose values at the cusps are coboundaries (equivalently: whose restriction to the cyclic cusp subgroups is a
coboundary).  This is the paper's "the long exact sequence identifies cuspidal cohomology with the image of compactly supported
cohomology" for these groups. -/
theorem Model.range_jMap (M : Model ρ K H) (F : Submodule ℂ (V × V × V)) :
    LinearMap.range (jMap M ι a g₂ F) = parabolicClasses ι ρ a g₂ M.c M.f := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    refine Submodule.mem_map.2 ⟨relToK M ι a g₂ x, ?_, rfl⟩
    rw [mem_parabolicSub, c_relToK]
    exact ⟨x.2.1, x.1.2, x.2.2⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hZ, v, hv⟩ := mem_parabolicCochains.mp (mem_parabolicSub.mp hy)
    let x : relCocycles ι ρ a g₂ := ⟨(M.c y, v), hZ, hv⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    have : relToK M ι a g₂ x = y := M.inj (c_relToK M x)
    rw [jMap_mk, this]

/-- **The kernel of `j`**: the classes of `H¹_c` mapping to zero are those whose crossed homomorphism is a coboundary (so that the
relative class comes from `H⁰` of the cusp subgroups: the fixed vectors of the special elements modulo the global invariants). -/
theorem Model.jMap_eq_zero_iff (M : Model ρ K H) (F : Submodule ℂ (V × V × V)) (x : relCocycles ι ρ a g₂) :
    jMap M ι a g₂ F (Submodule.Quotient.mk x) = 0 ↔ ∃ u : V, ∀ γ, x.1.1 γ = ρ γ u - u := by
  rw [jMap_mk, M.ker]
  simp only [c_relToK]

end Identification


section ImagePairing

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {K H K' H' : Type}
  [AddCommGroup K] [Module ℂ K] [AddCommGroup H] [Module ℂ H] [AddCommGroup K'] [Module ℂ K']
  [AddCommGroup H'] [Module ℂ H'] {ι : N →* Γ} {ρ : Representation ℂ Γ V}
  {ρ' : Representation ℂ Γ W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {a g₂ : N}

theorem Setup.range_j (S : Setup ι ρ ρ' B a g₂ K H K' H') :
    LinearMap.range S.j = parabolicClasses ι ρ a g₂ S.M.c S.M.f :=
  S.M.range_jMap S.F

theorem Setup.range_j' (S : Setup ι ρ ρ' B a g₂ K H K' H') :
    LinearMap.range S.j' = parabolicClasses ι ρ' a g₂ S.M'.c S.M'.f :=
  S.M'.range_jMap S.F'

/-- **The induced pairing between the images of compactly supported cohomology** (the abstract Lefschetz pairing for the true
`j`, `j'`, `PD`, `PD'`). -/
def Setup.imagePairing (S : Setup ι ρ ρ' B a g₂ K H K' H') :
    LinearMap.range S.j →ₗ[ℂ] LinearMap.range S.j' →ₗ[ℂ] ℂ :=
  Glue.FacePD.Lefschetz.imagePairing S.PD S.PDt S.j S.j' S.hT

/-- **The library's parabolic cup pairing** of the parabolic classes of the model, in the form built from the setup. -/
def Setup.parabolicPairing (S : Setup ι ρ ρ' B a g₂ K H K' H') :
    parabolicClasses ι ρ a g₂ S.M.c S.M.f →ₗ[ℂ] parabolicClasses ι ρ' a g₂ S.M'.c S.M'.f →ₗ[ℂ] ℂ :=
  classPairing ι ρ ρ' B a g₂ S.hinv S.M.c S.M'.c S.M.f S.M'.f (fun x hx => (S.M.ker x).1 hx)
    (fun y hy => (S.M'.ker y).1 hy)

/-- The identifications of the images with the parabolic classes. -/
def Setup.toParabolic (S : Setup ι ρ ρ' B a g₂ K H K' H') :
    LinearMap.range S.j ≃ₗ[ℂ] parabolicClasses ι ρ a g₂ S.M.c S.M.f :=
  LinearEquiv.ofEq _ _ S.range_j

def Setup.toParabolic' (S : Setup ι ρ ρ' B a g₂ K H K' H') :
    LinearMap.range S.j' ≃ₗ[ℂ] parabolicClasses ι ρ' a g₂ S.M'.c S.M'.f :=
  LinearEquiv.ofEq _ _ S.range_j'

/-- **The Lefschetz pairing of the images is the cup pairing**: on the image of a relative class `(Z, v)` and of a relative class
`(Z', v')` the induced pairing is the cup formula of `Z` with `Z'` corrected by the primitives `v`. -/
theorem Setup.imagePairing_mk (S : Setup ι ρ ρ' B a g₂ K H K' H') (x : relCocycles ι ρ a g₂)
    (x' : relCocycles ι ρ' a g₂) :
    S.imagePairing ⟨S.j (Submodule.Quotient.mk x), _, rfl⟩ ⟨S.j' (Submodule.Quotient.mk x'), _, rfl⟩ =
      cupFormula B (ρ'.comp ι) a g₂ (fun n => x.1.1 (ι n)) (fun n => x'.1.1 (ι n)) x.1.2 := by
  rw [Setup.imagePairing, Glue.FacePD.Lefschetz.imagePairing_apply]
  have e1 : S.j' (Submodule.Quotient.mk x') = S.M'.f (relToK S.M' ι a g₂ x') := rfl
  rw [e1, Setup.PD_mk, c_relToK]
  rfl

/-- **The induced pairing is the library's parabolic cup pairing**, under the identification of the images with the parabolic
classes. -/
theorem Setup.imagePairing_eq_parabolicPairing (S : Setup ι ρ ρ' B a g₂ K H K' H')
    (x : LinearMap.range S.j) (y : LinearMap.range S.j') :
    S.imagePairing x y = S.parabolicPairing (S.toParabolic x) (S.toParabolic' y) := by
  obtain ⟨_, c, rfl⟩ := x
  obtain ⟨_, c', rfl⟩ := y
  obtain ⟨x0, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨x0', rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  rw [Setup.imagePairing_mk]
  have hx : relToK S.M ι a g₂ x0 ∈ parabolicSub ι ρ a g₂ S.M.c := by
    rw [mem_parabolicSub, c_relToK]
    exact ⟨x0.2.1, x0.1.2, x0.2.2⟩
  have hy : relToK S.M' ι a g₂ x0' ∈ parabolicSub ι ρ' a g₂ S.M'.c := by
    rw [mem_parabolicSub, c_relToK]
    exact ⟨x0'.2.1, x0'.1.2, x0'.2.2⟩
  have := classPairing_eq_cupFormula ι ρ ρ' B a g₂ S.hinv S.M.c S.M'.c S.M.f S.M'.f
    (fun x hx => (S.M.ker x).1 hx) (fun y hy => (S.M'.ker y).1 hy)
    ⟨relToK S.M ι a g₂ x0, hx⟩ ⟨relToK S.M' ι a g₂ x0', hy⟩ (Submodule.mem_map_of_mem hx)
    (Submodule.mem_map_of_mem hy) (v := x0.1.2) (by
      show IsPrimitive (ρ.comp ι) a g₂ (fun n => S.M.c (relToK S.M ι a g₂ x0) (ι n)) x0.1.2
      rw [c_relToK]
      exact x0.2.2)
  refine Eq.trans ?_ this.symm
  simp only [c_relToK]

end ImagePairing


section Perfect

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {K H K' H' : Type}
  [AddCommGroup K] [Module ℂ K] [AddCommGroup H] [Module ℂ H] [AddCommGroup K'] [Module ℂ K']
  [AddCommGroup H'] [Module ℂ H'] {ι : N →* Γ} {ρ : Representation ℂ Γ V}
  {ρ' : Representation ℂ Γ W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {a g₂ : N}

/-- **Poincare-Lefschetz for the binary Levi, left nondegeneracy of the pairing of the images.**  The annihilator of
`Im j'` in `Im j` is zero: from the nondegeneracy of `PD' : H¹(E) × H¹_c(E*) → ℂ` (the cusp step and the library's parabolic
Poincare duality `CochainNondegenerate`) and `j' = jᵀ`. -/
theorem Setup.imagePairing_left_nondegenerate (S : Setup ι ρ ρ' B a g₂ K H K' H')
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (nd : CochainNondegenerate ι ρ ρ' B a g₂) (x : LinearMap.range S.j)
    (h : ∀ y : LinearMap.range S.j', S.imagePairing x y = 0) : x = 0 :=
  Glue.FacePD.Lefschetz.imagePairing_left_nondegenerate S.PD S.PDt S.j S.j' S.hT
    (fun x hx => S.PDt_nondegenerate hL hR nd x hx) x h

/-- **Right nondegeneracy** of the pairing of the images. -/
theorem Setup.imagePairing_right_nondegenerate (S : Setup ι ρ ρ' B a g₂ K H K' H')
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (nd : CochainNondegenerate ι ρ' ρ B.flip a g₂) (y : LinearMap.range S.j')
    (h : ∀ x : LinearMap.range S.j, S.imagePairing x y = 0) : y = 0 :=
  Glue.FacePD.Lefschetz.imagePairing_right_nondegenerate S.PD S.PDt S.j S.j' S.hT
    (fun y hy => S.PD_nondegenerate hL hR nd y hy) y h

end Perfect

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL
