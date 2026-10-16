module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.DeRhamNatural

@[expose] public section


/-!
# Naturality of the de Rham class under a coefficient intertwiner

Paper: "the same letters
for the rational conjugates".

If `T : F →L F` intertwines two representations `ρ, ρ'` of `G` (`ρ' g ∘ T = T ∘ ρ g`), then
`twForm T` carries closed `ρ`-equivariant forms to closed `ρ'`-equivariant forms (`twInv`), carries zig-zag
data to zig-zag data (`twDatum`) with cochain `T ∘ cochain` (`cochain_twDatum`), and
`deRhamClass_twist`: `[T ω]_{ρ'} = H²(id; T) [ω]_ρ`. This is the generalization of `deRhamClass_natural`
to a coefficient comparison; used for the plane cusps (`T = ρ(h⁻¹)`), the antiholomorphic seed
(`T = ` coefficientwise conjugation) and complex scalars (`T = ` multiplication by `c ∈ ℂ`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothSingularComparison
open scoped ContDiff Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {s : Set E} {G : Type} [Group G]
  {hs : IsOpen s} {A : Action G s} {ρ ρ' : Representation ℝ G F} {T : F →L[ℝ] F}

/-- `T` intertwines the representations `ρ` and `ρ'`. -/
def Intertwines (T : F →L[ℝ] F) (ρ ρ' : Representation ℝ G F) : Prop :=
  ∀ g v, ρ' g (T v) = T (ρ g v)

omit [CompleteSpace F] in
theorem repCLM_comp_twist (hT : Intertwines T ρ ρ') (g : G) :
    (repCLM ρ' g).comp T = T.comp (repCLM ρ g) := by
  ext v
  simp [repCLM, hT g v]

/-- **Coefficient twist of an invariant closed form.** -/
def twInv (hT : Intertwines T ρ ρ') (om : invClosed hs A ρ) : invClosed hs A ρ' :=
  ⟨twForm T 2 om.1, by rw [d_twForm hs, om.2.1, map_zero], fun g => by
    rw [pullForm_twForm hs A g, om.2.2 g, ← twForm_mul, ← twForm_mul]
    exact congrArg (fun L => twForm L 2 om.1) (repCLM_comp_twist hT g).symm⟩

/-- The twist of a zig-zag datum. -/
def twDatum (hT : Intertwines T ρ ρ') (om : invClosed hs A ρ)
    (Dt : Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) (om : Form (F := F) s 2)) :
    Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1) (fun g => twForm (repCLM ρ' g) 1)
      (twInv hT om : Form (F := F) s 2) where
  η := twForm T 1 Dt.η
  θ g := twForm T 0 (Dt.θ g)
  dη := by
    change d hs 1 _ = twForm T 2 om.1
    rw [d_twForm hs, Dt.dη]
  dθ g := by
    rw [d_twForm hs, Dt.dθ g, map_sub, pullForm_twForm hs A g, ← twForm_mul, ← twForm_mul,
      ← repCLM_comp_twist hT g]

/-- The twist of a representation intertwiner as a morphism `Res_id (ρ) ⟶ ρ'`. -/
def twMor (hT : Intertwines T ρ ρ') : Rep.res (MonoidHom.id G) (Rep.of ρ) ⟶ Rep.of ρ' :=
  Rep.ofHom ⟨T.toLinearMap, fun g => by
    ext v
    simp [hT g v]⟩

/-- The cochain of the twisted datum is the twist of the cochain. -/
theorem cochain_twDatum (hc : Convex ℝ s) (hne : s.Nonempty) (hT : Intertwines T ρ ρ')
    (om : invClosed hs A ρ)
    (Dt : Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) (om : Form (F := F) s 2)) (g h : G) :
    cochain (laws hs hc hne A ρ') (twDatum hT om Dt) g h =
      T (cochain (laws hs hc hne A ρ) Dt g h) := by
  apply (laws hs hc hne A ρ').c_injective
  rw [c_cochain (laws hs hc hne A ρ') (twDatum hT om Dt) g h]
  have e := c_cochain (laws hs hc hne A ρ) Dt g h
  have hX : deRhamConstant s (T (cochain (laws hs hc hne A ρ) Dt g h)) =
      twForm T 0 (deRhamConstant s (cochain (laws hs hc hne A ρ) Dt g h)) :=
    (twForm_constant T _).symm
  rw [hX, e, map_sub, map_add]
  show pullForm hs A h 0 (twForm T 0 (Dt.θ g)) + twForm (repCLM ρ' g) 0 (twForm T 0 (Dt.θ h)) -
      twForm T 0 (Dt.θ (g * h)) = _
  rw [← twForm_mul, repCLM_comp_twist hT g, twForm_mul, pullForm_twForm hs A h]

/-- **Naturality of the de Rham class under a coefficient intertwiner**: the class of the twisted
form is the image of the class under the induced map of group cohomology. -/
theorem deRhamClass_twist (hc : Convex ℝ s) (hne : s.Nonempty) (hT : Intertwines T ρ ρ')
    (om : invClosed hs A ρ) :
    deRhamClass hs hc hne A ρ' (twInv hT om) =
      (groupCohomology.map (MonoidHom.id G) (twMor hT) 2).hom (deRhamClass hs hc hne A ρ om) := by
  obtain ⟨Dt⟩ := exists_datum_deRham hs hc hne A ρ om
  rw [deRhamClass_eq hs hc hne A ρ' _ (twDatum hT om Dt), deRhamClass_eq hs hc hne A ρ om Dt]
  unfold zigzagClass
  rw [groupCohomology.H2π_comp_map_apply (MonoidHom.id G) (twMor hT)]
  congr 1
  apply Subtype.ext
  funext p
  change cochain (laws hs hc hne A ρ') (twDatum hT om Dt) p.1 p.2 = _
  rw [cochain_twDatum hc hne hT om Dt]
  rfl

omit [CompleteSpace F] in
theorem twInv_coe (hT : Intertwines T ρ ρ') (om : invClosed hs A ρ) :
    ((twInv hT om : invClosed hs A ρ') : Form (F := F) s 2) = twForm T 2 om.1 := rfl

omit [CompleteSpace F] in
theorem twInv_sub (hT : Intertwines T ρ ρ') (a b : invClosed hs A ρ) :
    twInv hT (a - b) = twInv hT a - twInv hT b := by
  apply Subtype.ext
  change twForm T 2 (a.1 - b.1) = twForm T 2 a.1 - twForm T 2 b.1
  rw [map_sub]

omit [CompleteSpace F] in
theorem twInv_add (hT : Intertwines T ρ ρ') (a b : invClosed hs A ρ) :
    twInv hT (a + b) = twInv hT a + twInv hT b := by
  apply Subtype.ext
  change twForm T 2 (a.1 + b.1) = twForm T 2 a.1 + twForm T 2 b.1
  rw [map_add]

/-- A twist of a form of zero class has zero class. -/
theorem deRhamClass_twist_eq_zero (hc : Convex ℝ s) (hne : s.Nonempty) (hT : Intertwines T ρ ρ')
    (om : invClosed hs A ρ) (h0 : deRhamClass hs hc hne A ρ om = 0) :
    deRhamClass hs hc hne A ρ' (twInv hT om) = 0 := by
  rw [deRhamClass_twist hc hne hT om, h0, map_zero]

end TernaryPeriodPolynomials.Argument.EisensteinClass
