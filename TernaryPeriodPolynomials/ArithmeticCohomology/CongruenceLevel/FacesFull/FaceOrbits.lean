module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaces

@[expose] public section


/-!
# Faces of `Γ(N)` as orbits, finiteness, and the direct sums `𝒞_P(E)`, `𝒞_Q(E)`

Formalized by Claude Sonnet 5.5.
Paper: Appendix C,: "`𝒞_R(E)` is the direct sum
over faces of type `R` of the subspaces `H¹(L_R, H¹(N_R, E))` ... They inject into degree-two face cohomology by Hochschild-Serre";
"the finitely many other plane cusps".

* `LineFaces N`: the `Γ(N)`-orbits of rational lines (`h ~ q h γ`, `q ∈ lineBorel`, `γ ∈ Γ(N)`); `lineFaces_finite`;
  `exists_lineFace_rep` (every rational line is covered by a face, with its stabilizer the line group of the representative);
  `lineFaceCuspidalInH2_of_rel` (independence of the representative: a bijection of the `H²` groups carrying the classes with cuspidal
  edge onto each other), the line analogue of `SeedC3S4c.faceCuspidalInH2_orbit`.
* Plane side: `faceEdgeEquiv`, `faceCuspidalEmbedding` (the injection `𝒞_{P'}(E) → H²`), `faceCuspidalInH2_eq_range`,
  `faceCuspidalInH2_of_rel` (using the existing `PlaneFaces`, `planeFaces_finite`).
* `LineCuspSum N n = ⨁_{faces} 𝒞_{Q'}(E)`, `PlaneCuspSum N n = ⨁_{faces} 𝒞_{P'}(E)`, their injections into `⨁ H²` of the face groups
  (`lineCuspSumEmbedding_injective`, `planeCuspSumEmbedding_injective`), with the range being the family of the face groups
  (`mem_range_lineCuspSumEmbedding`, `mem_range_planeCuspSumEmbedding`).
-/

open CategoryTheory
open scoped MatrixGroups DirectSum

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section LineFaces

/-- Two integral conjugators give the same face of type `Q` of the locally symmetric space of `Γ(N)` iff they differ by `h ↦ q h γ`
with `q ∈ Q(ℚ) ∩ SL₃(ℤ)` and `γ ∈ Γ(N)`. -/
def lineFaceSetoid (N : ℕ) : Setoid SL(3, ℤ) where
  r h h' := ∃ q ∈ lineBorel, ∃ γ ∈ gammaN N, h' = q * h * γ
  iseqv := by
    refine ⟨fun h => ⟨1, lineBorel.one_mem, 1, (gammaN N).one_mem, by simp⟩, ?_, ?_⟩
    · rintro h h' ⟨q, hq, γ, hγ, rfl⟩
      exact ⟨q⁻¹, lineBorel.inv_mem hq, γ⁻¹, (gammaN N).inv_mem hγ, by group⟩
    · rintro h h' h'' ⟨q, hq, γ, hγ, rfl⟩ ⟨q', hq', γ', hγ', rfl⟩
      exact ⟨q' * q, lineBorel.mul_mem hq' hq, γ * γ', (gammaN N).mul_mem hγ hγ', by group⟩

/-- **The faces of type `Q` of the locally symmetric space of `Γ(N)`**: `Γ(N)`-orbits of rational lines, as the quotient of
`SL₃(ℤ)` by `h ~ q h γ`. -/
def LineFaces (N : ℕ) : Type := Quotient (lineFaceSetoid N)

instance lineFaces_finite (N : ℕ) [NeZero N] : Finite (LineFaces N) := by
  let f : SL(3, ℤ) ⧸ gammaN N → LineFaces N :=
    Quotient.lift (fun h => (Quotient.mk (lineFaceSetoid N) h : LineFaces N)) (by
      intro a b hab
      apply Quotient.sound
      have : a⁻¹ * b ∈ gammaN N := (QuotientGroup.leftRel_apply).mp hab
      exact ⟨1, lineBorel.one_mem, a⁻¹ * b, this, by group⟩)
  have hf : Function.Surjective f := by
    intro x
    induction x using Quotient.inductionOn with
    | h h => exact ⟨QuotientGroup.mk h, rfl⟩
  exact Finite.of_surjective f hf

/-- The face of the conjugator `h`. -/
def LineFaces.mk {N : ℕ} (h : SL(3, ℤ)) : LineFaces N := Quotient.mk (lineFaceSetoid N) h

/-- The chosen representative (conjugator) of a face of type `Q`. -/
def LineFaces.rep {N : ℕ} (i : LineFaces N) : SL(3, ℤ) := Quotient.out i

theorem LineFaces.rel_rep {N : ℕ} (h : SL(3, ℤ)) : (lineFaceSetoid N).r h (LineFaces.mk (N := N) h).rep :=
  (lineFaceSetoid N).iseqv.symm (Quotient.mk_out (s := lineFaceSetoid N) h)

noncomputable instance lineFaces_fintype (N : ℕ) [NeZero N] : Fintype (LineFaces N) :=
  @Fintype.ofFinite _ (lineFaces_finite N)

/-- Every rational line cusp of `Γ(N)`, `N ≥ 3`, is represented by a face of `LineFaces N`: there is an integral conjugator `h` with
the stabilizer of the line `gQg⁻¹` in `Γ(N)` equal to the line group of `h⁻¹Qh`, and the chosen representative of the face of `h`
differs from `h` by `q h γ`, `q ∈ Q(ℚ) ∩ SL₃(ℤ)`, `γ ∈ Γ(N)`. -/
theorem exists_lineFace_rep (N : ℕ) [NeZero N] (hN : 3 ≤ N) (g : GL (Fin 3) ℚ) :
    ∃ (i : LineFaces N) (h : SL(3, ℤ)),
      (∀ p ∈ gammaN N,
        InQQ (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ↔ p ∈ gammaNQAt N h) ∧
      ∃ q ∈ lineBorel, ∃ γ ∈ gammaN N, i.rep = q * h * γ := by
  obtain ⟨h, h1⟩ := exists_lineFace_of_rational_line N hN g
  exact ⟨LineFaces.mk h, h, h1, LineFaces.rel_rep h⟩

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **Transport between two conjugators of the same face of type `Q`**: a linear isomorphism of the `H²` groups carrying the classes
with cuspidal edge of one onto those of the other (`lineFaceCuspidalInH2_orbit`). -/
theorem lineFaceCuspidalInH2_of_rel {h h' : SL(3, ℤ)} (hrel : (lineFaceSetoid N).r h h') :
    ∃ φ : groupCohomology.H2 (lineFaceRep N h n) →ₗ[ℂ] groupCohomology.H2 (lineFaceRep N h' n),
      Function.Bijective φ ∧ Submodule.map φ (lineFaceCuspidalInH2 N h n) = lineFaceCuspidalInH2 N h' n := by
  obtain ⟨q, hq, γ, -, hh'⟩ := hrel
  subst hh'
  have b1 : Function.Bijective (EdgeNat.h2Map (frameHomQ N h q hq) (lineFaceRep N h n)
      (lineFaceRep N (q * h) n) (frameT n) (frameTQ_intertwines N h n q hq)) :=
    ⟨EdgeNat.h2Map_injective _ _ _ _ _ (frameHomQ_bijective N h q hq) Function.bijective_id,
      EdgeNat.h2Map_surjective _ _ _ _ _ (frameHomQ_bijective N h q hq) Function.bijective_id⟩
  have b2 : Function.Bijective (EdgeNat.h2Map (conjGammaHomQ N (q * h) γ) (lineFaceRep N (q * h) n)
      (lineFaceRep N (q * h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N (q * h) γ n)) :=
    ⟨EdgeNat.h2Map_injective _ _ _ _ _ (conjGammaHomQ_bijective N (q * h) γ) (faceConjT_bijective γ n),
      EdgeNat.h2Map_surjective _ _ _ _ _ (conjGammaHomQ_bijective N (q * h) γ) (faceConjT_bijective γ n)⟩
  refine ⟨(EdgeNat.h2Map (conjGammaHomQ N (q * h) γ) (lineFaceRep N (q * h) n)
      (lineFaceRep N (q * h * γ) n) (faceConjT γ n) (faceConjTQ_intertwines N (q * h) γ n)).comp
    (EdgeNat.h2Map (frameHomQ N h q hq) (lineFaceRep N h n) (lineFaceRep N (q * h) n)
      (frameT n) (frameTQ_intertwines N h n q hq)), ?_, ?_⟩
  · rw [LinearMap.coe_comp]
    exact b2.comp b1
  · rw [Submodule.map_comp]
    exact lineFaceCuspidalInH2_orbit N n h q γ hq

end LineFaces

section PlaneFaces

/-- The chosen representative (conjugator) of a face of type `P`. -/
def planeFaceRepr {N : ℕ} (i : PlaneFaces N) : SL(3, ℤ) := Quotient.out i

noncomputable instance planeFaces_fintype (N : ℕ) [NeZero N] : Fintype (PlaneFaces N) :=
  @Fintype.ofFinite _ (planeFaces_finite N)

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The Hochschild-Serre isomorphism of the plane cusp `h⁻¹ P h`. -/
def faceEdgeEquiv (h : SL(3, ℤ)) :
    (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker ≃ₗ[ℂ]
      groupCohomology.H1 (faceRadH1 N h n) :=
  LinearEquiv.ofBijective (faceEdge N h n) ⟨faceEdge_injective N h n, faceEdge_surjective N h n⟩

/-- The injection `𝒞_{P'}(E) → H²(Γ_{P'}, E)` of the paper. -/
def faceCuspidalEmbedding (h : SL(3, ℤ)) : faceCuspidal N h n →ₗ[ℂ] groupCohomology.H2 (faceRep N h n) :=
  (LinearMap.ker (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n))).subtype ∘ₗ
    (faceEdgeEquiv N n h).symm.toLinearMap ∘ₗ (faceCuspidal N h n).subtype

theorem faceCuspidalEmbedding_injective (h : SL(3, ℤ)) : Function.Injective (faceCuspidalEmbedding N n h) := by
  intro a b hab
  have h1 : (faceEdgeEquiv N n h).symm (a : groupCohomology.H1 (faceRadH1 N h n)) =
      (faceEdgeEquiv N n h).symm (b : groupCohomology.H1 (faceRadH1 N h n)) :=
    Subtype.ext hab
  exact Subtype.ext ((faceEdgeEquiv N n h).symm.injective h1)

theorem faceCuspidalInH2_eq_range (h : SL(3, ℤ)) :
    faceCuspidalInH2 N h n = LinearMap.range (faceCuspidalEmbedding N n h) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨faceEdge N h n x, hx⟩, ?_⟩
    change ((faceEdgeEquiv N n h).symm (faceEdge N h n x) :
      (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker).1 = x.1
    have : (faceEdgeEquiv N n h).symm (faceEdge N h n x) = x :=
      (faceEdgeEquiv N n h).symm_apply_apply x
    rw [this]
  · rintro ⟨c, rfl⟩
    refine ⟨(faceEdgeEquiv N n h).symm c.1, ?_, rfl⟩
    change faceEdge N h n ((faceEdgeEquiv N n h).symm c.1) ∈ faceCuspidal N h n
    have : faceEdge N h n ((faceEdgeEquiv N n h).symm c.1) = c.1 :=
      (faceEdgeEquiv N n h).apply_symm_apply c.1
    rw [this]
    exact c.2

/-- **Transport between two conjugators of the same face of type `P`.** -/
theorem faceCuspidalInH2_of_rel {h h' : SL(3, ℤ)} (hrel : (planeFaceSetoid N).r h h') :
    ∃ φ : groupCohomology.H2 (faceRep N h n) →ₗ[ℂ] groupCohomology.H2 (faceRep N h' n),
      Function.Bijective φ ∧ Submodule.map φ (faceCuspidalInH2 N h n) = faceCuspidalInH2 N h' n := by
  obtain ⟨q, hq, γ, -, hh'⟩ := hrel
  subst hh'
  have b1 : Function.Bijective (EdgeNat.h2Map (frameHom N h q hq) (faceRep N h n)
      (faceRep N (q * h) n) (frameT n) (frameT_intertwines N h n q hq)) :=
    ⟨EdgeNat.h2Map_injective _ _ _ _ _ (frameHom_bijective N h q hq) Function.bijective_id,
      EdgeNat.h2Map_surjective _ _ _ _ _ (frameHom_bijective N h q hq) Function.bijective_id⟩
  have b2 : Function.Bijective (EdgeNat.h2Map (conjGammaHom N (q * h) γ) (faceRep N (q * h) n)
      (faceRep N (q * h * γ) n) (faceConjT γ n) (faceConjT_intertwines N (q * h) γ n)) :=
    ⟨EdgeNat.h2Map_injective _ _ _ _ _ (conjGammaHom_bijective N (q * h) γ) (faceConjT_bijective γ n),
      EdgeNat.h2Map_surjective _ _ _ _ _ (conjGammaHom_bijective N (q * h) γ) (faceConjT_bijective γ n)⟩
  refine ⟨(EdgeNat.h2Map (conjGammaHom N (q * h) γ) (faceRep N (q * h) n)
      (faceRep N (q * h * γ) n) (faceConjT γ n) (faceConjT_intertwines N (q * h) γ n)).comp
    (EdgeNat.h2Map (frameHom N h q hq) (faceRep N h n) (faceRep N (q * h) n)
      (frameT n) (frameT_intertwines N h n q hq)), ?_, ?_⟩
  · rw [LinearMap.coe_comp]
    exact b2.comp b1
  · rw [Submodule.map_comp]
    exact faceCuspidalInH2_orbit N n h q γ hq

end PlaneFaces

section DirectSums

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **`𝒞_Q(E)` for `Γ(N)`**: the direct sum, over the faces of type `Q` (representatives `LineFaces.rep`), of the
mixed cuspidal groups `𝒞_{Q'}(E) ⊂ H¹(L_{Q'}, H¹(N_{Q'}, E))` of the faces. -/
abbrev LineCuspSum : Type := ⨁ i : LineFaces N, lineFaceCuspidal N i.rep n

/-- **`𝒞_P(E)` for `Γ(N)`**: the direct sum over the faces of type `P`. -/
abbrev PlaneCuspSum : Type := ⨁ i : PlaneFaces N, faceCuspidal N (planeFaceRepr i) n

/-- The degree-two cohomology of the line groups of all the faces of type `Q`. -/
abbrev LineFaceH2 : Type := ⨁ i : LineFaces N, groupCohomology.H2 (lineFaceRep N i.rep n)

/-- The degree-two cohomology of the plane groups of all the faces of type `P`. -/
abbrev PlaneFaceH2 : Type := ⨁ i : PlaneFaces N, groupCohomology.H2 (faceRep N (planeFaceRepr i) n)

/-- The injection `𝒞_Q(E) → ⨁_faces H²(Γ_{Q'}, E)` (summed over the faces). -/
def lineCuspSumEmbedding : LineCuspSum N n →ₗ[ℂ] LineFaceH2 N n :=
  DirectSum.lmap fun i => lineFaceCuspidalEmbedding N i.rep n

/-- The injection `𝒞_P(E) → ⨁_faces H²(Γ_{P'}, E)`. -/
def planeCuspSumEmbedding : PlaneCuspSum N n →ₗ[ℂ] PlaneFaceH2 N n :=
  DirectSum.lmap fun i => faceCuspidalEmbedding N n (planeFaceRepr i)

theorem lineCuspSumEmbedding_injective : Function.Injective (lineCuspSumEmbedding N n) :=
  (DirectSum.lmap_injective _).mpr fun i => lineFaceCuspidalEmbedding_injective N i.rep n

theorem planeCuspSumEmbedding_injective : Function.Injective (planeCuspSumEmbedding N n) :=
  (DirectSum.lmap_injective _).mpr fun i => faceCuspidalEmbedding_injective N n (planeFaceRepr i)

/-- The image of `𝒞_Q(E)` is the direct sum of the groups `lineFaceCuspidalInH2` of the faces. -/
theorem mem_range_lineCuspSumEmbedding (x : LineFaceH2 N n) :
    x ∈ LinearMap.range (lineCuspSumEmbedding N n) ↔
      ∀ i, x i ∈ lineFaceCuspidalInH2 N i.rep n := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [lineFaceCuspidalInH2_eq_range]
    exact ⟨c i, rfl⟩
  · intro hx
    have key : ∀ i : LineFaces N,
        x i ∈ LinearMap.range (lineFaceCuspidalEmbedding N i.rep n) := fun i => by
      rw [← lineFaceCuspidalInH2_eq_range]
      exact hx i
    choose c hc using key
    let c' : LineCuspSum N n := ∑ i : LineFaces N,
      DirectSum.of (fun j : LineFaces N => lineFaceCuspidal N j.rep n) i (c i)
    refine ⟨c', ?_⟩
    rw [map_sum]
    conv_rhs => rw [← DirectSum.sum_univ_of x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lineCuspSumEmbedding, DirectSum.lmap_of, hc]

/-- The image of `𝒞_P(E)` is the direct sum of the groups `faceCuspidalInH2` of the faces. -/
theorem mem_range_planeCuspSumEmbedding (x : PlaneFaceH2 N n) :
    x ∈ LinearMap.range (planeCuspSumEmbedding N n) ↔
      ∀ i, x i ∈ faceCuspidalInH2 N (planeFaceRepr i) n := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [faceCuspidalInH2_eq_range]
    exact ⟨c i, rfl⟩
  · intro hx
    have key : ∀ i : PlaneFaces N,
        x i ∈ LinearMap.range (faceCuspidalEmbedding N n (planeFaceRepr i)) := fun i => by
      rw [← faceCuspidalInH2_eq_range]
      exact hx i
    choose c hc using key
    refine ⟨∑ i, DirectSum.of (fun i => faceCuspidal N (planeFaceRepr i) n) i (c i), ?_⟩
    rw [map_sum]
    conv_rhs => rw [← DirectSum.sum_univ_of x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [planeCuspSumEmbedding, DirectSum.lmap_of, hc]

end DirectSums

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
