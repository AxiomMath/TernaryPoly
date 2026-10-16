module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.Chains
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.ComparisonSigns
public import TernaryPeriodPolynomials.Building.Span.ChainComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryApartmentEvaluation
open ModThreeGoodAction AugmentedFrameComplex GoodRelativeChains
open OrdinaryApartmentFrames OrdinaryRelativeChains OrientedListChains
local instance : DecidableEq RationalLine := Classical.decEq _

/-- Literal frame data satisfying the integral apartment relations, including every column sign. -/
structure FrameValues (E : Type*) [AddCommGroup E] [Module ℚ E] where
  value : IntegralGL → E
  lines : ∀ g h, triangleList g=triangleList h → value g=value h
  cyclic : ∀ g, value (g*ReferenceCoefficientMatrices.c)=value g
  swap : ∀ g, value (g*ReferenceCoefficientMatrices.s)= -value g
  norm : ∀ g, value g+value (g*ReferenceCoefficientMatrices.a)+
    value (g*ReferenceCoefficientMatrices.a^2)=0

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (v : FrameValues E)

/-- A list receives its representative-independent frame value, and every other list receives zero. -/
def listValue (l : List RationalLine) : E := by
  classical
  exact if h : ∃ g : IntegralGL, triangleList g = l then v.value h.choose else 0

local notation "value" => listValue v

@[simp] theorem value_triangle (g : IntegralGL) : value (triangleList g) = v.value g := by
  have h : ∃ h : IntegralGL, triangleList h = triangleList g := ⟨g,rfl⟩
  rw [listValue,dite_eq_left h]
  exact v.lines h.choose g h.choose_spec

theorem value_of_frame (g : IntegralGL) (l : List RationalLine) (hg : triangleList g = l) :
    value l = v.value g := by rw [← hg,value_triangle v]

theorem value_eq_zero_of_no_frame (l : List RationalLine)
    (h : ¬∃ g : IntegralGL, triangleList g = l) : value l = 0 := by rw [listValue,dite_eq_right h]

theorem value_swap_first (L M N : RationalLine) : value [M,L,N] = -value [L,M,N] := by
  by_cases h : ∃ g : IntegralGL, triangleList g = [L,M,N]
  · obtain ⟨g,hg⟩ := h
    rw [value_of_frame v g _ hg,value_of_frame v (g*ReferenceCoefficientMatrices.s) _ (triangleList_swap_of_eq g L M N hg)]
    exact v.swap g
  · have h' : ¬∃ g : IntegralGL, triangleList g = [M,L,N] := by
      rintro ⟨g,hg⟩
      exact h ⟨g*ReferenceCoefficientMatrices.s,triangleList_swap_of_eq g M L N hg⟩
    rw [value_eq_zero_of_no_frame v _ h,value_eq_zero_of_no_frame v _ h',neg_zero]

theorem value_cyclic (L M N : RationalLine) : value [M,N,L] = value [L,M,N] := by
  by_cases h : ∃ g : IntegralGL, triangleList g = [L,M,N]
  · obtain ⟨g,hg⟩ := h
    rw [value_of_frame v g _ hg,value_of_frame v (g*ReferenceCoefficientMatrices.c) _ (triangleList_cycle_of_eq g L M N hg)]
    exact v.cyclic g
  · have h' : ¬∃ g : IntegralGL, triangleList g = [M,N,L] := by
      rintro ⟨g,hg⟩
      exact h ⟨(g*ReferenceCoefficientMatrices.c)*ReferenceCoefficientMatrices.c,triangleList_cycle_of_eq (g*ReferenceCoefficientMatrices.c) N L M
        (triangleList_cycle_of_eq g M N L hg)⟩
    rw [value_eq_zero_of_no_frame v _ h,value_eq_zero_of_no_frame v _ h']

theorem value_swap_last (L M N : RationalLine) : value [L,N,M] = -value [L,M,N] := by
  calc
    value [L,N,M] = value [N,M,L] := (value_cyclic v L N M).symm
    _ = -value [M,N,L] := value_swap_first v M N L
    _ = -value [L,M,N] := congrArg Neg.neg (value_cyclic v L M N)

theorem value_eq_zero_of_length (l : List RationalLine) (hl : l.length ≠ 3) : value l = 0 := by
  apply value_eq_zero_of_no_frame v
  rintro ⟨g,hg⟩
  apply hl
  rw [← hg]
  rfl

/-- The actual finite-list evaluator satisfies every orientation relation, at every prefix. -/
theorem value_alternating : SpanChainComparison.AlternatingLists value := by
  intro p L M s
  by_cases hlen : (p ++ L :: M :: s).length = 3
  · have hlen' : p.length + s.length = 1 := by
      simp only [List.length_append,List.length_cons] at hlen
      omega
    cases p with
    | nil =>
      have hs : s.length = 1 := by simpa using hlen'
      obtain ⟨N,rfl⟩ := List.length_eq_one_iff.mp hs
      change value [L,M,N] + value [M,L,N] = 0
      rw [value_swap_first v L M N,add_neg_cancel]
    | cons N p =>
      have hp : p = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen'; omega)
      have hs : s = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen'; omega)
      subst p
      subst s
      change value [N,L,M] + value [N,M,L] = 0
      rw [value_swap_last v N L M,add_neg_cancel]
  · have hlen' : (p ++ M :: L :: s).length ≠ 3 := by
      simpa only [List.length_append,List.length_cons] using hlen
    rw [value_eq_zero_of_length v _ hlen,value_eq_zero_of_length v _ hlen',add_zero]

/-- The evaluator on the genuine oriented-list quotient. -/
def chainEvaluator : Chain RationalLine →ₗ[ℚ] E :=
  SpanChainComparison.evaluate value (value_alternating v)

local notation "evaluator" => chainEvaluator v

@[simp] theorem evaluator_simplex (l : List RationalLine) : evaluator (simplex l) = value l :=
  SpanChainComparison.evaluate_simplex value (value_alternating v) l

@[simp] theorem evaluator_triangle (g : IntegralGL) : evaluator (simplex (triangleList g)) = v.value g := by
  rw [evaluator_simplex v,value_triangle v]

/-- Proper-span triangles have no independent integral-frame representative and evaluate to zero. -/
theorem evaluator_proper_simplex (l : List RationalLine)
    (hd : Module.finrank ℚ (faceSpan l.toFinset) ≤ 2) : evaluator (simplex l) = 0 := by
  rw [evaluator_simplex v]
  exact value_eq_zero_of_no_frame v l (not_triangleList_of_proper l hd)

/-- Every finite proper ambient triangle chain evaluates to zero. -/
theorem evaluator_proper_chain {c : Chain RationalLine} (hc : c ∈ chains properAmbient 3) :
    evaluator c = 0 := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    rcases hl with rfl | hl
    · simp at hlen
    · exact evaluator_proper_simplex v l hl.2
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]


/-- Every integral augmented tetrahedron gives exactly the proved norm relation. -/
theorem evaluator_tetrahedron_boundary (g : IntegralGL) :
    evaluator (boundary (simplex (tetrahedronList g)))=0 := by
  have he := congrArg evaluator (OrdinaryRelativeChains.triangle_norm_boundary g)
  simp only [map_add,evaluator_triangle,evaluator_proper_simplex v _ (coreList_finrank g),add_zero] at he
  rw [v.norm] at he
  exact he.symm

/-- All orders and degeneracies of actual ambient tetrahedra have zero boundary value. -/
theorem evaluator_ambient_four_boundary (l : List RationalLine) (hlen : l.length=4)
    (hl : Allowed ambient l) : evaluator (boundary (simplex l))=0 := by
  by_cases hn : l.Nodup
  · have hf : l.toFinset∈ambient := by
      rcases hl with rfl | hl
      · simp at hlen
      · exact hl
    obtain ⟨g,hg⟩ := ambient_tetrahedron_perm l hlen hn hf
    obtain ⟨q,hq⟩ := OrientedSimplexPermutation.simplex_perm_smul hg
    rw [hq,map_smul,map_smul,evaluator_tetrahedron_boundary,smul_zero]
  · rw [simplex_eq_zero_of_not_nodup l hn,map_zero,map_zero]

theorem evaluator_ambient_boundary {c : Chain RationalLine} (hc : c∈chains ambient 4) :
    evaluator (boundary c)=0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    exact evaluator_ambient_four_boundary v l hlen hl
  | zero => rw [map_zero,map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- Evaluate the actual ambient triangle submodule. -/
def ambientEvaluator : AmbientTwo →ₗ[ℚ] E := (chainEvaluator v).comp AmbientTwo.subtype

theorem nullSubmodule_le_ker : OrdinaryRelativeChains.nullSubmodule≤LinearMap.ker (ambientEvaluator v) := by
  apply sup_le
  · rintro x ⟨p,rfl⟩
    exact evaluator_proper_chain v p.property
  · rintro x ⟨c,rfl⟩
    exact evaluator_ambient_boundary v c.property

/-- An actual map on ambient triangles modulo proper triangles and tetrahedron boundaries. -/
def relativeEvaluator : OrdinaryRelativeChains.RelativeBoundaryTwo →ₗ[ℚ] E :=
  OrdinaryRelativeChains.nullSubmodule.liftQ (ambientEvaluator v) (nullSubmodule_le_ker v)

@[simp] theorem relativeEvaluator_quotientMap (x : AmbientTwo) :
    relativeEvaluator v (OrdinaryRelativeChains.quotientMap x)=evaluator x.val := rfl

@[simp] theorem relativeEvaluator_triangle (g : IntegralGL) :
    relativeEvaluator v (OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle g))=v.value g :=
  evaluator_triangle v g

/-- The actual homogeneous polynomial fibers supply all integral frame relations. -/
def fiberFrameValues (n : ℕ) (F : OrdinaryCovectors.Covector → TernaryPolynomial)
    (h : OrdinaryPolynomialFiberSystem.System F) (hF : ∀ r,(F r).IsHomogeneous n) :
    FrameValues (PolynomialGLAction.HomogeneousPoly n) :=
  ⟨OrdinaryFiberComparison.frameValue n F hF,
    OrdinaryFiberComparison.frameValue_eq_of_triangleList n h hF,
    OrdinaryFiberComparison.frameValue_cyclic n h hF,
    OrdinaryFiberComparison.frameValue_swap n h hF,
    OrdinaryFiberComparison.frameValue_norm n h hF⟩

end TernaryPoly.OrdinaryApartmentEvaluation
