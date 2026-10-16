module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Plane.EdgeProjection
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Hom
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportNormals

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryPlaneEdge

/-- The ordered embedding (b,c) ↦ (0,b,c). -/
def embed : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun x := ![0,x 0,x 1]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

def tail : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := ![x 1,x 2]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

@[simp] theorem tail_embed (x : Fin 2 → ℚ) : tail (embed x) = x := by
  ext i
  fin_cases i <;> simp [tail,embed]

theorem embed_injective : Function.Injective embed := by
  intro x y h
  simpa only [tail_embed] using congrArg tail h

/-- The actual rational plane a=0, equipped with the ordinary incidence-plane subtype. -/
def planeZero : OrdinaryIncidence.Plane :=
  ⟨embed.range,(OrdinaryIncidence.plane_iff embed.range).mpr (by
    rw [LinearMap.finrank_range_of_inj embed_injective]
    simp)⟩

@[simp] theorem mem_planeZero (x : Fin 3 → ℚ) : x ∈ planeZero.val ↔ x 0 = 0 := by
  constructor
  · rintro ⟨y,rfl⟩
    rfl
  · intro hx
    refine ⟨tail x,?_⟩
    ext i
    fin_cases i
    · exact hx.symm
    · simp [tail,embed]
    · simp [tail,embed]

theorem planeZero_eq_hyperplane_axis : planeZero.val = OrdinaryResidueSupport.hyperplane
    (OrdinaryResidueSupport.axis 0) := by
  ext x
  rw [mem_planeZero,OrdinaryResidueSupport.mem_hyperplane_axis]

/-- Embedding the actual binary rational line gives an incident ordinary rational line. -/
def embedLine (L : BinaryModularSymbol.Line) : StarLine planeZero :=
  ⟨⟨L.val.map embed,(Submodule.equivMapOfInjective embed embed_injective L.val).finrank_eq.symm.trans
      L.property,trivial⟩,LinearMap.map_le_range⟩

theorem embedLine_injective : Function.Injective embedLine := by
  intro L M h
  apply Subtype.ext
  apply Submodule.map_injective_of_injective embed_injective
  exact congrArg (fun L : StarLine planeZero => L.val.val) h

theorem embedLine_surjective : Function.Surjective embedLine := by
  intro L
  let K := L.val.val.comap embed
  have hK : K.map embed = L.val.val := Submodule.map_comap_eq_of_le L.property
  have hd : Module.finrank ℚ K = 1 := by
    rw [(Submodule.equivMapOfInjective embed embed_injective K).finrank_eq,hK]
    exact L.val.property.1
  refine ⟨⟨K,hd⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hK

/-- The actual binary projective line is exactly the line-star of the plane a=0. -/
def lineEquiv : BinaryModularSymbol.Line ≃ StarLine planeZero :=
  Equiv.ofBijective embedLine ⟨embedLine_injective,embedLine_surjective⟩

/-- This identification transports the actual finite-support divisor modules. -/
def divisorEquiv : BinaryModularSymbol.Divisors ≃ₗ[ℚ] Divisors planeZero :=
  Finsupp.domLCongr lineEquiv

@[simp] theorem divisorEquiv_single (L : BinaryModularSymbol.Line) (q : ℚ) :
    divisorEquiv (Finsupp.single L q) = Finsupp.single (embedLine L) q :=
  Finsupp.domLCongr_single lineEquiv L q

theorem augmentation_divisorEquiv (c : BinaryModularSymbol.Divisors) :
    augmentation planeZero (divisorEquiv c) = BinaryModularSymbol.augmentation c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single L q => simp

/-- Restrict the literal divisor equivalence to the two actual augmentation kernels. -/
def symbolEquiv : BinaryModularSymbol.St ≃ₗ[ℚ] St planeZero where
  toFun c := ⟨divisorEquiv c.val,by rw [LinearMap.mem_ker,augmentation_divisorEquiv]; exact c.property⟩
  invFun c := ⟨divisorEquiv.symm c.val,by
    change BinaryModularSymbol.augmentation (divisorEquiv.symm c.val) = 0
    rw [←augmentation_divisorEquiv,LinearEquiv.apply_symm_apply]
    exact c.property⟩
  left_inv _ := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (LinearEquiv.apply_symm_apply _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem symbolEquiv_symbol (L M : BinaryModularSymbol.Line) :
    symbolEquiv (BinaryModularSymbol.symbol L M) = symbol planeZero (embedLine L) (embedLine M) := by
  apply Subtype.ext
  change divisorEquiv (_ - _) = _ - _
  rw [map_sub,divisorEquiv_single,divisorEquiv_single]

/-- The exterior coordinate line spanned by (1,0,0). -/
def exterior : OrdinaryIncidence.Line :=
  ⟨Submodule.span ℚ {![1,0,0]},by
    apply finrank_span_singleton
    intro h
    have he := congrFun h 0
    norm_num at he,trivial⟩

theorem exterior_outside : ¬exterior.val ≤ planeZero.val := by
  intro h
  have hm : (![1,0,0] : Fin 3 → ℚ) ∈ exterior.val := Submodule.subset_span (Set.mem_singleton _)
  have he := (mem_planeZero _).mp (h hm)
  norm_num at he

/-- Actual incidence cycles project to the actual binary modular-symbol module. -/
def binaryProject : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] BinaryModularSymbol.St :=
  symbolEquiv.symm.toLinearMap.comp (project planeZero)

/-- Actual binary modular symbols cone into incidence cycles through the exterior coordinate line. -/
def binaryCone : BinaryModularSymbol.St →ₗ[ℚ] OrdinaryIncidenceChains.Cycles :=
  (cone planeZero exterior).comp symbolEquiv.toLinearMap

@[simp] theorem binaryProject_binaryCone (c : BinaryModularSymbol.St) : binaryProject (binaryCone c) = c := by
  change symbolEquiv.symm (project planeZero (cone planeZero exterior (symbolEquiv c))) = c
  rw [project_cone planeZero exterior exterior_outside,LinearEquiv.symm_apply_apply]

@[simp] theorem binaryCone_symbol (L M : BinaryModularSymbol.Line) :
    binaryCone (BinaryModularSymbol.symbol L M) =
      GoodApartmentCycles.apartmentCycle (fun _ => True) exterior (embedLine L).val (embedLine M).val := by
  change cone planeZero exterior (symbolEquiv (BinaryModularSymbol.symbol L M)) = _
  rw [symbolEquiv_symbol,cone_symbol]

end TernaryPoly.OrdinaryPlaneEdge
