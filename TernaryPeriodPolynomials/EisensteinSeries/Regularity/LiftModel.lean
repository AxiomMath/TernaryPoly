module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.LiftModelCore
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.LiftFields
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.LiftSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Petersson

@[expose] public section


/-!
# The finite-adelic model of the adelic lifts

For a set `S` of weight-`k` cusp forms of `Γ₁(3)` the span `liftSpan S` of the right
`GL₂(𝔸_f)`-translates of the adelic lifts lies in the Petersson space `petSpace (centralChar k)`.
Its closure `E` for the Petersson norm is a Hilbert space with a unitary, strongly continuous
representation `σ` of `GL₂(𝔸_f)` (`liftSigma`), by completion of the pre-unitary representation
`liftRep` on the span (`LiftModelCore`).  If the spaces of `U`-invariant functions in the span are
finite dimensional for every open compact `U` (`LiftLevelFinite S`), then so are the `σ`-fixed
spaces of `E`; every smooth vector of `E` is a vector of the span, and the inclusion into
functions on `GL₂(𝔸)` is the injective, equivariant realization `liftEps` required by
`FiniteModel`.  The result is `liftModel S hfin : FiniteModel k`, and `liftModel_ε_lift` shows that
`adelicLift f` (for `f ∈ S`) is realized.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.Automorphic.CompletionRepresentation
open TernaryPeriodPolynomials.Automorphic.Petersson
open TernaryPeriodPolynomials.CuspIntegral
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryRealGammaOneThree)

namespace TernaryPeriodPolynomials.Regularity

/-! ### Right translation by `GL₂(𝔸_f)` -/

theorem atFinite_one_eq : atFinite (1 : BinaryFiniteGL) = 1 :=
  map_one finGL

theorem atFinite_mul_eq (u v : BinaryFiniteGL) :
    atFinite (u * v) = atFinite u * atFinite v :=
  map_mul finGL u v

/-- Right translation by `GL₂(𝔸_f)` on functions on `GL₂(𝔸)`. -/
def rtRep : Representation ℂ BinaryFiniteGL (BinaryAdelicGL → ℂ) where
  toFun u :=
    { toFun := fun φ x => φ (x * atFinite u)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * atFinite 1) = φ x
    rw [atFinite_one_eq, mul_one]
  map_mul' a b := LinearMap.ext fun φ => funext fun x => by
    show φ (x * atFinite (a * b)) = φ (x * atFinite a * atFinite b)
    rw [atFinite_mul_eq, mul_assoc]

theorem rtRep_apply (u : BinaryFiniteGL) (φ : BinaryAdelicGL → ℂ) (x : BinaryAdelicGL) :
    rtRep u φ x = φ (x * atFinite u) :=
  rfl

section Span

variable {k : ℕ} (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ)))

theorem generator_mem_liftSpan {f : CuspForm binaryRealGammaOneThree (k : ℤ)} (hf : f ∈ S)
    (u : BinaryFiniteGL) : (fun x => adelicLift f (x * atFinite u)) ∈ liftSpan S :=
  Submodule.subset_span ⟨f, hf, u, rfl⟩

/-- The span of the translates of the lifts is stable under right translation. -/
theorem rtRep_mem_liftSpan (u : BinaryFiniteGL) {ψ : BinaryAdelicGL → ℂ} (h : ψ ∈ liftSpan S) :
    rtRep u ψ ∈ liftSpan S := by
  have hle : liftSpan S ≤ (liftSpan S).comap (rtRep u) := by
    refine Submodule.span_le.2 ?_
    rintro φ ⟨f, hf, v, rfl⟩
    show rtRep u (fun x => adelicLift f (x * atFinite v)) ∈ liftSpan S
    have heq : rtRep u (fun x => adelicLift f (x * atFinite v)) =
        fun x => adelicLift f (x * atFinite (u * v)) := by
      funext x
      show adelicLift f (x * atFinite u * atFinite v) = adelicLift f (x * atFinite (u * v))
      rw [atFinite_mul_eq, mul_assoc]
    rw [heq]
    exact generator_mem_liftSpan S hf (u * v)
  exact hle h

/-- `levelGroup` is an open compact subgroup of `GL₂(𝔸_f)`. -/
theorem levelGroup_isOpenCompact : IsOpenCompact levelGroup := by
  have hopen : IsOpen (levelGroup : Set BinaryFiniteGL) :=
    Automorphic.Petersson.isOpen_levelGroup
  have hle : (levelGroup : Set BinaryFiniteGL) ⊆ (integralLevel : Set BinaryFiniteGL) := by
    intro κ hκ
    have hκ' : κ ∈ levelGroup := hκ
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.mp hκ'
    exact ⟨m, rfl⟩
  exact ⟨hopen, integralLevel_isOpenCompact.2.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hopen) hle⟩

/-- Every vector of the span of translates of lifts is fixed by an open compact subgroup. -/
theorem liftSpan_le_finiteSmooth : liftSpan S ≤ finiteSmooth rtRep := by
  unfold liftSpan
  refine Submodule.span_le.2 ?_
  rintro φ ⟨f, hf, v, rfl⟩
  change (fun x => adelicLift f (x * atFinite v)) ∈ finiteSmooth rtRep
  refine ⟨levelGroup.map (MulAut.conj v).toMonoidHom, levelGroup_isOpenCompact.map_conj v, ?_⟩
  rintro ⟨_, hmem⟩
  obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.mp hmem
  funext x
  show adelicLift f (x * atFinite (v * κ * v⁻¹) * atFinite v) = adelicLift f (x * atFinite v)
  have h1 : atFinite (v * κ * v⁻¹ * v) = atFinite v * atFinite κ := by
    rw [inv_mul_cancel_right, atFinite_mul_eq]
  rw [mul_assoc x, ← atFinite_mul_eq, h1, ← mul_assoc]
  have h2 := adelicLift_mul_levelGroup f (x * atFinite v) hκ
  rw [finGL_apply] at h2
  exact h2

end Span

/-! ### The Petersson space as a pre-Hilbert space -/

/-- The Petersson space `petSpace (centralChar k)`, as a type synonym so that it carries the
pre-Hilbert structure of `petCore` and not the pointwise topology of the function space. -/
def PetSpace (k : ℕ) : Type := petSpace (centralChar (k : ℤ))

namespace PetSpace

variable {k : ℕ}

instance : AddCommGroup (PetSpace k) :=
  inferInstanceAs (AddCommGroup (petSpace (centralChar (k : ℤ))))

instance : Module ℂ (PetSpace k) :=
  inferInstanceAs (Module ℂ (petSpace (centralChar (k : ℤ))))

instance : FunLike (PetSpace k) BinaryAdelicGL ℂ where
  coe φ := (φ : petSpace (centralChar (k : ℤ))).1
  coe_injective := fun _ _ h => Subtype.ext h

@[ext] theorem ext {φ ψ : PetSpace k} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext _ _ h

theorem isPet (φ : PetSpace k) : PetMem (centralChar (k : ℤ)) ⇑φ :=
  petMem_of_mem (φ : petSpace (centralChar (k : ℤ)))

/-- An element of `PetSpace k` from a function with the defining properties. -/
def mk (φ : BinaryAdelicGL → ℂ) (h : PetMem (centralChar (k : ℤ)) φ) : PetSpace k :=
  (⟨φ, h⟩ : petSpace (centralChar (k : ℤ)))

@[simp] theorem coe_mk (φ : BinaryAdelicGL → ℂ) (h : PetMem (centralChar (k : ℤ)) φ) :
    ⇑(mk φ h : PetSpace k) = φ :=
  rfl

/-- The Petersson pairing as an `InnerProductSpace.Core` on `PetSpace k`. -/
@[instance_reducible] def petSpaceCore (k : ℕ) : InnerProductSpace.Core ℂ (PetSpace k) :=
  petCore (centralChar (k : ℤ)) (norm_centralChar (k : ℤ))

instance : NormedAddCommGroup (PetSpace k) := by
  letI : InnerProductSpace.Core ℂ (PetSpace k) := petSpaceCore k
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (PetSpace k) := by
  letI : InnerProductSpace.Core ℂ (PetSpace k) := petSpaceCore k
  exact InnerProductSpace.ofCore (petSpaceCore k).toCore

theorem inner_def (φ ψ : PetSpace k) : inner ℂ φ ψ = pet ⇑φ ⇑ψ :=
  rfl

/-- Right translation by `GL₂(𝔸_f)` on `PetSpace k`. -/
def translate (u : BinaryFiniteGL) : PetSpace k →ₗ[ℂ] PetSpace k :=
  petTranslate (centralChar (k : ℤ)) (atFinite u)

theorem translate_apply (u : BinaryFiniteGL) (φ : PetSpace k) (x : BinaryAdelicGL) :
    translate u φ x = φ (x * atFinite u) :=
  rfl

theorem inner_translate (u : BinaryFiniteGL) (φ ψ : PetSpace k) :
    inner ℂ (translate u φ) (translate u ψ) = inner ℂ φ ψ := by
  rw [inner_def, inner_def]
  exact pet_petTranslate (norm_centralChar (k : ℤ)) (atFinite u) φ ψ

/-- Right translation by `GL₂(𝔸_f)` preserves the Petersson norm. -/
theorem norm_translate (u : BinaryFiniteGL) (φ : PetSpace k) : ‖translate u φ‖ = ‖φ‖ :=
  (LinearMap.isometryOfInner (translate u) (inner_translate u)).norm_map φ

end PetSpace

/-! ### The pre-Hilbert space spanned by the translates of the lifts -/

section PreHilbert

variable {k : ℕ} (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ)))

/-- The subspace of `PetSpace k` spanned by the right translates of the lifts of `S`. -/
def liftSubmodule : Submodule ℂ (PetSpace k) where
  carrier := {φ | (⇑φ : BinaryAdelicGL → ℂ) ∈ liftSpan S}
  add_mem' {a b} ha hb := by
    have ha' : (⇑a : BinaryAdelicGL → ℂ) ∈ liftSpan S := ha
    have hb' : (⇑b : BinaryAdelicGL → ℂ) ∈ liftSpan S := hb
    exact (liftSpan S).add_mem ha' hb'
  zero_mem' := show (⇑(0 : PetSpace k) : BinaryAdelicGL → ℂ) ∈ liftSpan S from
    (liftSpan S).zero_mem
  smul_mem' c φ hφ := by
    have hφ' : (⇑φ : BinaryAdelicGL → ℂ) ∈ liftSpan S := hφ
    exact (liftSpan S).smul_mem c hφ'

theorem translate_mem_liftSubmodule (u : BinaryFiniteGL) {φ : PetSpace k}
    (h : φ ∈ liftSubmodule S) : PetSpace.translate u φ ∈ liftSubmodule S := by
  have h' : (⇑φ : BinaryAdelicGL → ℂ) ∈ liftSpan S := h
  exact rtRep_mem_liftSpan S u h'

/-- Right translation by `u` on the span of translates of lifts. -/
def liftTranslate (u : BinaryFiniteGL) : liftSubmodule S →ₗ[ℂ] liftSubmodule S :=
  (PetSpace.translate u).restrict fun _ h => translate_mem_liftSubmodule S u h

theorem liftTranslate_coe (u : BinaryFiniteGL) (m : liftSubmodule S) :
    ((liftTranslate S u m : liftSubmodule S) : PetSpace k) =
      PetSpace.translate u (m : PetSpace k) :=
  rfl

/-- The pre-unitary representation of `GL₂(𝔸_f)` on the span of translates of lifts. -/
def liftRep : Representation ℂ BinaryFiniteGL (liftSubmodule S) where
  toFun := liftTranslate S
  map_one' := LinearMap.ext fun m => Subtype.ext (PetSpace.ext fun x => by
    show (m : PetSpace k) (x * atFinite 1) = (m : PetSpace k) x
    rw [atFinite_one_eq, mul_one])
  map_mul' a b := LinearMap.ext fun m => Subtype.ext (PetSpace.ext fun x => by
    show (m : PetSpace k) (x * atFinite (a * b)) = (m : PetSpace k) (x * atFinite a * atFinite b)
    rw [atFinite_mul_eq, mul_assoc])

theorem liftRep_norm (g : BinaryFiniteGL) (m : liftSubmodule S) : ‖liftRep S g m‖ = ‖m‖ := by
  show ‖PetSpace.translate g (m : PetSpace k)‖ = ‖(m : PetSpace k)‖
  exact PetSpace.norm_translate g _

/-- The functions on `GL₂(𝔸)` underlying the elements of the span. -/
def liftFn : liftSubmodule S →ₗ[ℂ] (BinaryAdelicGL → ℂ) where
  toFun m := ⇑(m : PetSpace k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem liftFn_injective : Function.Injective (liftFn S) := fun _ _ h =>
  Subtype.ext (PetSpace.ext fun x => congrFun h x)

theorem liftFn_liftRep (u : BinaryFiniteGL) (m : liftSubmodule S) :
    liftFn S (liftRep S u m) = rtRep u (liftFn S m) :=
  rfl

theorem liftFn_mem (m : liftSubmodule S) : liftFn S m ∈ liftSpan S :=
  m.2

/-- Every vector of the span is fixed by an open compact subgroup. -/
theorem liftRep_allSmooth : CompletionFixed.AllSmooth (liftRep S) := by
  intro m
  obtain ⟨W, hW, hWm⟩ := liftSpan_le_finiteSmooth S (liftFn_mem S m)
  exact ⟨W, hW, fun w => liftFn_injective S (hWm w)⟩

/-- The fixed spaces of the pre-unitary representation embed into the level subspaces. -/
theorem liftRep_fixed_finite (hfin : LiftLevelFinite S) {U : Subgroup BinaryFiniteGL}
    (hU : IsOpenCompact U) : FiniteDimensional ℂ (fixedSubmodule (liftRep S) U) := by
  have := hfin U hU.1 hU.2
  have hmem : ∀ m ∈ fixedSubmodule (liftRep S) U, liftFn S m ∈ levelSubmodule S U := by
    intro m hm
    refine ⟨liftFn_mem S m, fun u hu => ?_⟩
    exact congrArg (liftFn S) (hm ⟨u, hu⟩)
  have hinj : Function.Injective ((liftFn S).restrict hmem) := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    exact Subtype.ext (liftFn_injective S
      (show liftFn S (a : liftSubmodule S) = liftFn S (b : liftSubmodule S) from h'))
  exact FiniteDimensional.of_injective ((liftFn S).restrict hmem) hinj

end PreHilbert

/-! ### The completion -/

section Completion

variable {k : ℕ} (S : Set (CuspForm binaryRealGammaOneThree (k : ℤ)))

/-- The Hilbert space completion of the span of translates of the lifts. -/
abbrev LiftE : Type := UniformSpace.Completion (liftSubmodule S)

/-- The unitary representation of `GL₂(𝔸_f)` on the Hilbert space completion. -/
def liftSigma : Representation ℂ BinaryFiniteGL (LiftE S) :=
  completionRep (liftRep S) (liftRep_norm S)

theorem liftSigma_continuous (e : LiftE S) : Continuous fun g => liftSigma S g e := by
  refine continuous_completionRep (liftRep S) (liftRep_norm S) (fun m => ?_) e
  obtain ⟨W, hW, hWm⟩ := liftRep_allSmooth S m
  exact CompletionFixed.continuous_orbit_of_fixed (liftRep S) m hW.1 hWm

theorem liftSigma_finite (hfin : LiftLevelFinite S) {U : Subgroup BinaryFiniteGL}
    (hU : IsOpenCompact U) : FiniteDimensional ℂ (fixedSubmodule (liftSigma S) U) :=
  CompletionFixed.finiteDimensional_fixed_completion (liftRep S) (liftRep_norm S)
    (liftRep_allSmooth S) (fun _ hU' => liftRep_fixed_finite S hfin hU') hU

theorem liftSigma_smooth_le (hfin : LiftLevelFinite S) :
    finiteSmooth (liftSigma S) ≤ LinearMap.range (CompletionFixed.coeLin (liftSubmodule S)) :=
  CompletionFixed.finiteSmooth_completion_le (liftRep S) (liftRep_norm S)
    (liftRep_allSmooth S) (fun _ hU' => liftRep_fixed_finite S hfin hU')

/-- The inverse of the inclusion of the span into its completion, on smooth vectors. -/
def liftEpsM (hfin : LiftLevelFinite S) : finiteSmooth (liftSigma S) →ₗ[ℂ] liftSubmodule S :=
  (LinearEquiv.ofInjective (CompletionFixed.coeLin (liftSubmodule S))
    CompletionFixed.coeLin_injective).symm.toLinearMap.comp
    (Submodule.inclusion (liftSigma_smooth_le S hfin))

theorem coeLin_liftEpsM (hfin : LiftLevelFinite S) (e : finiteSmooth (liftSigma S)) :
    CompletionFixed.coeLin (liftSubmodule S) (liftEpsM S hfin e) = (e : LiftE S) := by
  have h := (LinearEquiv.ofInjective (CompletionFixed.coeLin (liftSubmodule S))
    CompletionFixed.coeLin_injective).apply_symm_apply
      (Submodule.inclusion (liftSigma_smooth_le S hfin) e)
  exact congrArg Subtype.val h

/-- The realization of the smooth vectors of the completion as functions on `GL₂(𝔸)`. -/
def liftEps (hfin : LiftLevelFinite S) : finiteSmooth (liftSigma S) →ₗ[ℂ] (BinaryAdelicGL → ℂ) :=
  (liftFn S).comp (liftEpsM S hfin)

theorem liftEps_injective (hfin : LiftLevelFinite S) : Function.Injective (liftEps S hfin) := by
  intro a b hab
  have hab' : liftFn S (liftEpsM S hfin a) = liftFn S (liftEpsM S hfin b) := hab
  have h1 : liftEpsM S hfin a = liftEpsM S hfin b := liftFn_injective S hab'
  refine Subtype.ext ?_
  calc (a : LiftE S) = CompletionFixed.coeLin (liftSubmodule S) (liftEpsM S hfin a) :=
        (coeLin_liftEpsM S hfin a).symm
    _ = CompletionFixed.coeLin (liftSubmodule S) (liftEpsM S hfin b) := by rw [h1]
    _ = (b : LiftE S) := coeLin_liftEpsM S hfin b

theorem liftEpsM_stable (hfin : LiftLevelFinite S) (g : BinaryFiniteGL)
    (e : finiteSmooth (liftSigma S)) :
    liftEpsM S hfin ⟨liftSigma S g e, finiteSmooth_stable (liftSigma S) g e.property⟩ =
      liftRep S g (liftEpsM S hfin e) := by
  refine CompletionFixed.coeLin_injective ?_
  have h1 := coeLin_liftEpsM S hfin
    ⟨liftSigma S g e, finiteSmooth_stable (liftSigma S) g e.property⟩
  have h2 := coeLin_liftEpsM S hfin e
  have h3 : CompletionFixed.coeLin (liftSubmodule S) (liftRep S g (liftEpsM S hfin e)) =
      liftSigma S g (CompletionFixed.coeLin (liftSubmodule S) (liftEpsM S hfin e)) := by
    rw [CompletionFixed.coeLin_apply, CompletionFixed.coeLin_apply]
    exact (completionRep_coe (liftRep S) (liftRep_norm S) g _).symm
  exact h1.trans (h3.trans (congrArg (liftSigma S g) h2)).symm

theorem liftEps_equivariant (hfin : LiftLevelFinite S) (g : BinaryFiniteGL)
    (e : finiteSmooth (liftSigma S)) (x : BinaryAdelicGL) :
    liftEps S hfin ⟨liftSigma S g e, finiteSmooth_stable (liftSigma S) g e.property⟩ x =
      liftEps S hfin e (x * atFinite g) :=
  congrFun (congrArg (liftFn S) (liftEpsM_stable S hfin g e)) x

theorem liftEps_mem (hfin : LiftLevelFinite S) (e : finiteSmooth (liftSigma S)) :
    liftEps S hfin e ∈ liftSpan S :=
  liftFn_mem S _

theorem liftEps_cuspidal (hfin : LiftLevelFinite S) (e : finiteSmooth (liftSigma S)) :
    IsCuspidalLike (centralChar (k : ℤ)) (liftEps S hfin e) :=
  (Submodule.mem_inf.1 (span_translates_le_cuspidalLike_inf S (liftEps_mem S hfin e))).1

theorem liftEps_holomorphic (hfin : LiftLevelFinite S) (e : finiteSmooth (liftSigma S)) :
    IsHolomorphicWeight k (liftEps S hfin e) :=
  (Submodule.mem_inf.1 (span_translates_le_cuspidalLike_inf S (liftEps_mem S hfin e))).2

/-- **The finite-adelic model of the adelic lifts**: the Petersson completion of the span of the
`GL₂(𝔸_f)`-translates of the lifts of the cusp forms in `S`, given finite dimensionality of the
level subspaces (`LiftLevelFinite S`). -/
def liftModel (hfin : LiftLevelFinite S) : FiniteModel k where
  E := LiftE S
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  σ := liftSigma S
  unitary := completionRep_norm (liftRep S) (liftRep_norm S)
  continuous := liftSigma_continuous S
  finiteDimensional := fun _ hU => liftSigma_finite S hfin hU
  ε := liftEps S hfin
  injective := liftEps_injective S hfin
  equivariant := liftEps_equivariant S hfin
  χ := centralChar (k : ℤ)
  χ_unitary := norm_centralChar (k : ℤ)
  like := liftEps_cuspidal S hfin
  continuous_ε := fun e => (liftEps_holomorphic S hfin e).continuous
  weight := fun e x a b hab => (liftEps_holomorphic S hfin e).weight x a b hab
  holomorphic := fun e x => (liftEps_holomorphic S hfin e).holomorphic x

/-- Every right translate `x ↦ adelicLift f (x · u)` of a lift of `f ∈ S` is realized by a smooth
vector of the model. -/
theorem liftModel_ε_translate (hfin : LiftLevelFinite S)
    {f : CuspForm binaryRealGammaOneThree (k : ℤ)} (hf : f ∈ S) (u : BinaryFiniteGL) :
    ∃ e, (liftModel S hfin).ε e = fun x => adelicLift f (x * atFinite u) := by
  have hpet : PetMem (centralChar (k : ℤ)) (fun x => adelicLift f (x * atFinite u)) :=
    (petMem_adelicLift f).translate (atFinite u)
  have hmem : (fun x => adelicLift f (x * atFinite u)) ∈ liftSpan S :=
    generator_mem_liftSpan S hf u
  let m : liftSubmodule S := ⟨PetSpace.mk _ hpet, hmem⟩
  have hsm : CompletionFixed.coeLin (liftSubmodule S) m ∈ finiteSmooth (liftSigma S) :=
    CompletionFixed.coe_mem_finiteSmooth (liftRep S) (liftRep_norm S) (liftRep_allSmooth S) m
  refine ⟨⟨_, hsm⟩, ?_⟩
  have h1 : liftEpsM S hfin ⟨_, hsm⟩ = m :=
    CompletionFixed.coeLin_injective (coeLin_liftEpsM S hfin ⟨_, hsm⟩)
  exact (congrArg (liftFn S) h1).trans rfl

/-- Every adelic lift of a cusp form in `S` is realized by a smooth vector of the model. -/
theorem liftModel_ε_lift (hfin : LiftLevelFinite S)
    {f : CuspForm binaryRealGammaOneThree (k : ℤ)} (hf : f ∈ S) :
    ∃ e, (liftModel S hfin).ε e = adelicLift f := by
  obtain ⟨e, he⟩ := liftModel_ε_translate S hfin hf 1
  refine ⟨e, ?_⟩
  rw [he]
  funext x
  show adelicLift f (x * atFinite 1) = adelicLift f x
  rw [atFinite_one_eq, mul_one]

end Completion

end TernaryPeriodPolynomials.Regularity

end
