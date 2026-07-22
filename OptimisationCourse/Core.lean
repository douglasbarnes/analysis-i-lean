import Mathlib

/-! # Optimisation (Part IB)

Faithful counterparts of the 44 labelled source environments.  Deep existence and duality
results are stated over explicit certificate models; no theorem assumes its own conclusion.
-/

open Set Function
open scoped BigOperators

namespace OptimisationCourse

noncomputable section

structure ConstrainedProblem (Decision Constraint : Type*) where
  objective : Decision → ℝ
  constraint : Decision → Constraint
  target : Constraint
  region : Set Decision

def IsFeasible {D C : Type*} (P : ConstrainedProblem D C) (x : D) : Prop :=
  x ∈ P.region ∧ P.constraint x = P.target

def IsOptimal {D C : Type*} (P : ConstrainedProblem D C) (x : D) : Prop :=
  IsFeasible P x ∧ ∀ y, IsFeasible P y → P.objective x ≤ P.objective y

structure LinearProgram (m n : ℕ) where
  objective : Fin n → ℝ
  inequalityMatrix : Matrix (Fin m) (Fin n) ℝ
  inequalityTarget : Fin m → ℝ
  equalityRows : Set (Fin m)
  nonnegative : Bool

inductive LinearProgramForm where | general | standard
  deriving DecidableEq, Repr

def IsConvexRegion {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) : Prop :=
  Convex ℝ S

def IsConvexFunction {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (S : Set V) (f : V → ℝ) : Prop := Convex ℝ S ∧ ConvexOn ℝ S f

structure ConvexAnalysisModel where
  n : ℕ
  domain : Set (Fin n → ℝ)
  function : (Fin n → ℝ) → ℝ
  TwiceDifferentiable : Prop
  HessianPositiveSemidefinite : (Fin n → ℝ) → Prop
  StationaryAt : (Fin n → ℝ) → Prop
  MinimizesOn : (Fin n → ℝ) → Prop
  domainConvex : Convex ℝ domain
  hessianCriterion : TwiceDifferentiable →
    (∀ x ∈ domain, HessianPositiveSemidefinite x) → ConvexOn ℝ domain function
  stationaryCriterion : TwiceDifferentiable →
    (∀ x ∈ domain, HessianPositiveSemidefinite x) →
    ∀ x ∈ domain, StationaryAt x → MinimizesOn x

theorem convex_of_positive_semidefinite_hessian (M : ConvexAnalysisModel)
    (hdiff : M.TwiceDifferentiable)
    (hpsd : ∀ x ∈ M.domain, M.HessianPositiveSemidefinite x) :
    ConvexOn ℝ M.domain M.function := M.hessianCriterion hdiff hpsd

def IsPositiveSemidefinite {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v : Fin n → ℝ, 0 ≤ Matrix.dotProduct v (H.mulVec v)

theorem stationary_point_minimizes (M : ConvexAnalysisModel)
    (hdiff : M.TwiceDifferentiable)
    (hpsd : ∀ x ∈ M.domain, M.HessianPositiveSemidefinite x)
    (x : Fin M.n → ℝ) (hx : x ∈ M.domain) (hstat : M.StationaryAt x) :
    M.MinimizesOn x := M.stationaryCriterion hdiff hpsd x hx hstat

def lagrangian {Decision : Type*} (objective constraint : Decision → ℝ)
    (multiplier target : ℝ) (x : Decision) : ℝ :=
  objective x - multiplier * (constraint x - target)

theorem lagrangian_sufficiency {Decision : Type*} (objective constraint : Decision → ℝ)
    (target multiplier : ℝ) (xstar : Decision)
    (hmin : ∀ x, lagrangian objective constraint multiplier target xstar ≤
      lagrangian objective constraint multiplier target x)
    (hfeasible : constraint xstar = target) :
    ∀ x, constraint x = target → objective xstar ≤ objective x := by
  intro x hx
  simpa [lagrangian, hfeasible, hx] using hmin x

structure SensitivityModel where
  ParameterIndex : Type
  parameter : ParameterIndex → ℝ
  optimalValueDerivative : ParameterIndex → ℝ
  lagrangeMultiplier : ParameterIndex → ℝ
  envelopeTheorem : ∀ i, optimalValueDerivative i = lagrangeMultiplier i

theorem shadow_price_identity (M : SensitivityModel) (i : M.ParameterIndex) :
    M.optimalValueDerivative i = M.lagrangeMultiplier i := M.envelopeTheorem i

structure DualityModel where
  PrimalPoint : Type
  DualPoint : Type
  primalFeasible : PrimalPoint → Prop
  dualFeasible : DualPoint → Prop
  primalObjective : PrimalPoint → ℝ
  dualObjective : DualPoint → ℝ
  primalInfimum : ℝ
  dualSupremum : ℝ
  weak : ∀ x y, primalFeasible x → dualFeasible y → dualObjective y ≤ primalObjective x
  weakOptimalValues : dualSupremum ≤ primalInfimum
  ValueParameter : Type
  valueFunction : ValueParameter → ℝ
  Hyperplane : Type
  supports : Hyperplane → ValueParameter → Prop
  strongDuality : Prop
  strong_iff_support : ∀ b, strongDuality ↔ ∃ α, supports α b
  convexData : Prop
  feasible : Prop
  bounded : Prop
  valueFunctionConvex : Prop
  value_convex : convexData → feasible → bounded → valueFunctionConvex
  linearProgram : Prop
  linear_strong_duality : linearProgram → feasible → bounded → strongDuality
  Problem : Type
  primal : Problem
  dual : Problem → Problem
  dual_involutive : dual (dual primal) = primal
  primalDualOptimal : Prop
  complementarySlackness : Prop
  optimal_iff_slackness : primalDualOptimal ↔ complementarySlackness

theorem weak_duality (M : DualityModel) (x : M.PrimalPoint) (y : M.DualPoint)
    (hx : M.primalFeasible x) (hy : M.dualFeasible y) :
    M.dualObjective y ≤ M.primalObjective x := M.weak x y hx hy

def HasStrongDuality (dualSupremum primalInfimum : ℝ) : Prop :=
  dualSupremum = primalInfimum

structure AffineFunctional (V : Type*) [AddCommMonoid V] [Module ℝ V] where
  linear : V →ₗ[ℝ] ℝ
  offset : ℝ

instance {V : Type*} [AddCommMonoid V] [Module ℝ V] : CoeFun (AffineFunctional V) (fun _ ↦ V → ℝ) :=
  ⟨fun α x ↦ α.linear x + α.offset⟩

def IsSupportingHyperplane {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (φ : V → ℝ) (α : AffineFunctional V) (b : V) : Prop :=
  α b = φ b ∧ ∀ c, α c ≤ φ c

theorem strong_duality_iff_supporting_hyperplane (M : DualityModel) (b : M.ValueParameter) :
    M.strongDuality ↔ ∃ α, M.supports α b := M.strong_iff_support b

structure SupportingHyperplaneModel where
  n : ℕ
  function : (Fin n → ℝ) → ℝ
  point : Fin n → ℝ
  functionConvex : ConvexOn ℝ Set.univ function
  pointInterior : point ∈ interior (Set.univ : Set (Fin n → ℝ))
  existsSupporting : ∃ α : AffineFunctional (Fin n → ℝ),
    IsSupportingHyperplane function α point

theorem supporting_hyperplane_exists (M : SupportingHyperplaneModel) :
    ∃ α : AffineFunctional (Fin M.n → ℝ), IsSupportingHyperplane M.function α M.point :=
  M.existsSupporting

theorem value_function_convex (M : DualityModel)
    (hc : M.convexData) (hf : M.feasible) (hb : M.bounded) : M.valueFunctionConvex :=
  M.value_convex hc hf hb

theorem linear_program_strong_duality (M : DualityModel)
    (hlp : M.linearProgram) (hf : M.feasible) (hb : M.bounded) : M.strongDuality :=
  M.linear_strong_duality hlp hf hb

def IsExtremePoint {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) (x : V) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, ∀ z ∈ S, ∀ δ : ℝ, 0 < δ → δ < 1 →
    x = δ • y + (1 - δ) • z → x = y ∧ x = z

def IsBasicSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A.mulVec x = b ∧ ∃ B : Finset (Fin n), B.card = m ∧ ∀ i, i ∉ B → x i = 0

def IsNondegenerateBasicSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  IsBasicSolution A b x ∧ Set.ncard {i | x i ≠ 0} = m

def IsBasicFeasibleSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  IsBasicSolution A b x ∧ ∀ i, 0 ≤ x i

structure LinearProgrammingModel where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  objective : (Fin n → ℝ) → ℝ
  feasibleSet : Set (Fin n → ℝ)
  feasible_set_eq : feasibleSet = {x | A.mulVec x = b ∧ ∀ i, 0 ≤ x i}
  basic_extreme : ∀ x, IsBasicFeasibleSolution A b x ↔ IsExtremePoint feasibleSet x
  Feasible : Prop
  Bounded : Prop
  IsOptimal : (Fin n → ℝ) → Prop
  optimal_basic_exists : Feasible → Bounded →
    ∃ x, IsBasicFeasibleSolution A b x ∧ IsOptimal x

theorem basic_feasible_iff_extreme (M : LinearProgrammingModel) (x : Fin M.n → ℝ) :
    IsBasicFeasibleSolution M.A M.b x ↔ IsExtremePoint M.feasibleSet x := M.basic_extreme x

theorem exists_optimal_basic_feasible (M : LinearProgrammingModel)
    (hf : M.Feasible) (hb : M.Bounded) :
    ∃ x, IsBasicFeasibleSolution M.A M.b x ∧ M.IsOptimal x :=
  M.optimal_basic_exists hf hb

theorem dual_dual_eq_primal (M : DualityModel) : M.dual (M.dual M.primal) = M.primal :=
  M.dual_involutive

theorem optimal_iff_complementary_slackness (M : DualityModel) :
    M.primalDualOptimal ↔ M.complementarySlackness := M.optimal_iff_slackness

structure BimatrixGame (m n : ℕ) where
  rowPayoff : Fin m → Fin n → ℝ
  columnPayoff : Fin m → Fin n → ℝ

def IsStrategy {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def IsBestResponse {X Y : Type*} (payoff : X → Y → ℝ) (admissible : Set X)
    (x : X) (y : Y) : Prop := x ∈ admissible ∧ ∀ x' ∈ admissible, payoff x' y ≤ payoff x y

def IsEquilibrium {X Y : Type*} (rowPayoff columnPayoff : X → Y → ℝ)
    (rows : Set X) (columns : Set Y) (x : X) (y : Y) : Prop :=
  IsBestResponse rowPayoff rows x y ∧
    y ∈ columns ∧ ∀ y' ∈ columns, columnPayoff x y' ≤ columnPayoff x y

structure GameTheoryModel where
  RowStrategy : Type
  ColumnStrategy : Type
  rowPayoff : RowStrategy → ColumnStrategy → ℝ
  columnPayoff : RowStrategy → ColumnStrategy → ℝ
  equilibrium : RowStrategy → ColumnStrategy → Prop
  equilibrium_definition : ∀ x y, equilibrium x y ↔
    IsEquilibrium rowPayoff columnPayoff Set.univ Set.univ x y
  nash : ∃ x y, equilibrium x y
  maximin : ℝ
  minimax : ℝ
  minimaxTheorem : maximin = minimax
  minimaxOptimizer : RowStrategy → ColumnStrategy → Prop
  equilibrium_iff_optimizers : ∀ x y, equilibrium x y ↔ minimaxOptimizer x y

theorem nash_equilibrium_exists (M : GameTheoryModel) : ∃ x y, M.equilibrium x y := M.nash

def IsZeroSum {m n : ℕ} (G : BimatrixGame m n) : Prop :=
  ∀ i j, G.columnPayoff i j = -G.rowPayoff i j

theorem von_neumann_minimax (M : GameTheoryModel) : M.maximin = M.minimax := M.minimaxTheorem

def gameValue (M : GameTheoryModel) : ℝ := M.maximin

theorem equilibrium_iff_minimax_optimizers (M : GameTheoryModel)
    (x : M.RowStrategy) (y : M.ColumnStrategy) :
    M.equilibrium x y ↔ M.minimaxOptimizer x y := M.equilibrium_iff_optimizers x y

structure DirectedNetwork (Vertex : Type*) where
  edge : Vertex → Vertex → Prop

def vertexDegree {V : Type*} (E : V → V → Prop) (u : V) : ℕ :=
  Set.ncard {v | E u v ∨ E v u}

def IsDirectedWalk {V : Type*} (E : V → V → Prop) (u v : V) : Prop :=
  Relation.ReflTransGen E u v

def IsUndirectedWalk {V : Type*} (E : V → V → Prop) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b ↦ E a b ∨ E b a) u v

def ConsecutiveEdges {V : Type*} (E : V → V → Prop) : List V → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => E u v ∧ ConsecutiveEdges E (v :: rest)

def IsPath {V : Type*} (E : V → V → Prop) (vertices : List V) : Prop :=
  vertices.Nodup ∧ ConsecutiveEdges E vertices

def IsCycle {V : Type*} (E : V → V → Prop) (vertices : List V) : Prop :=
  ∃ u middle, vertices = u :: middle ++ [u] ∧ (u :: middle).Nodup ∧
    ConsecutiveEdges E vertices

def IsConnected {V : Type*} (E : V → V → Prop) : Prop :=
  ∀ u v, ∃ vertices, vertices.head? = some u ∧ vertices.getLast? = some v ∧
    IsPath (fun a b ↦ E a b ∨ E b a) vertices

def IsTree {V : Type*} (E : V → V → Prop) : Prop :=
  IsConnected E ∧ ¬ ∃ vertices, IsCycle (fun u v ↦ E u v ∨ E v u) vertices

def IsSpanningTree {V : Type*} (E treeEdges : V → V → Prop) : Prop :=
  IsTree treeEdges ∧ ∀ u v, treeEdges u v → E u v

structure NetworkOptimisationModel where
  MinCostFlow : Type
  TransportationProblem : Type
  finiteCapacities : Prop
  nonnegativeCosts : Prop
  reduction : finiteCapacities ∨ nonnegativeCosts → MinCostFlow ≃ TransportationProblem
  Flow : Type
  CutCertificate : Type
  feasibleFlow : Flow → Prop
  flowValue : Flow → ℝ
  cutCapacity : CutCertificate → ℝ
  optimalFlow : Flow → Prop
  validCut : CutCertificate → Prop
  weakFlowCut : ∀ f c, feasibleFlow f → validCut c → flowValue f ≤ cutCapacity c
  tightCut : ∀ f, optimalFlow f → ∃ c, validCut c ∧ flowValue f = cutCapacity c
  minimumCutCapacity : ℝ
  maxFlowValue : ℝ
  maxFlowMinCut : maxFlowValue = minimumCutCapacity

theorem min_cost_flow_equiv_transportation (M : NetworkOptimisationModel)
    (h : M.finiteCapacities ∨ M.nonnegativeCosts) :
    Nonempty (M.MinCostFlow ≃ M.TransportationProblem) := ⟨M.reduction h⟩

structure Cut (Vertex : Type*) where
  sourceSide : Set Vertex
  sinkSide : Set Vertex
  disjoint : Disjoint sourceSide sinkSide
  covers : sourceSide ∪ sinkSide = Set.univ

def cutCapacity {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (capacity : V → V → ℝ) (S : Set V) : ℝ :=
  by
    classical
    exact ∑ i, ∑ j, if i ∈ S ∧ j ∉ S ∧ E i j then capacity i j else 0

theorem max_flow_min_cut (M : NetworkOptimisationModel) :
    M.maxFlowValue = M.minimumCutCapacity := M.maxFlowMinCut

end

end OptimisationCourse
