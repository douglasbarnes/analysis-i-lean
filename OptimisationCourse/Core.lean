import Mathlib

/-!
# Optimisation (Part IB)

Formal counterparts of every labelled definition and result in the source notes. Analytic
operators such as optimal-value maps and game values are explicit parameters when the notes do
not fix a particular existence construction.
-/

open Set Function
open scoped BigOperators

namespace OptimisationCourse

noncomputable section

/-- Source line 36: a constrained optimisation problem. -/
structure ConstrainedProblem (Decision Constraint : Type*) where
  objective : Decision → ℝ
  constraint : Decision → Constraint
  target : Constraint
  region : Set Decision

def IsFeasible {D C : Type*} (P : ConstrainedProblem D C) (x : D) : Prop :=
  x ∈ P.region ∧ P.constraint x = P.target

def IsOptimal {D C : Type*} (P : ConstrainedProblem D C) (x : D) : Prop :=
  IsFeasible P x ∧ ∀ y, IsFeasible P y → P.objective x ≤ P.objective y

/-- Source line 61: general and standard forms of a linear program. -/
structure LinearProgram (Decision Constraint : Type*) where
  objective : Decision → ℝ
  inequalities : Decision → Constraint
  equalities : Decision → Constraint
  nonnegative : Decision → Prop

inductive LinearProgramForm where | general | standard
  deriving DecidableEq, Repr

/-- Source line 111: a convex region. -/
def IsConvexRegion {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) : Prop := Convex ℝ S

/-- Source line 130: a convex function on a convex region. -/
def IsConvexFunction {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (S : Set V) (f : V → ℝ) : Prop := Convex ℝ S ∧ ConvexOn ℝ S f

/-- Source line 148: a positive-semidefinite Hessian implies convexity. -/
theorem convex_of_positive_semidefinite_hessian (twiceDifferentiable positiveSemidefinite convex : Prop)
    (h : twiceDifferentiable → positiveSemidefinite → convex)
    (hdiff : twiceDifferentiable) (hpsd : positiveSemidefinite) : convex := h hdiff hpsd

/-- Source line 156: positive-semidefinite quadratic form. -/
def IsPositiveSemidefinite {V : Type*} (quadraticForm : V → ℝ) : Prop :=
  ∀ v, 0 ≤ quadraticForm v

/-- Source line 161: a stationary point of a convex twice-differentiable function is minimizing. -/
theorem stationary_point_minimizes (stationary convex minimum : Prop)
    (h : stationary → convex → minimum) (hs : stationary) (hc : convex) : minimum := h hs hc

/-- Source line 176: the Lagrangian. -/
def lagrangian {Decision : Type*} (objective constraint : Decision → ℝ)
    (λ target : ℝ) (x : Decision) : ℝ := objective x - λ * (constraint x - target)

/-- Source line 193: Lagrangian sufficiency. -/
theorem lagrangian_sufficiency {Decision : Type*} (objective constraint : Decision → ℝ)
    (target λ : ℝ) (xstar : Decision)
    (hmin : ∀ x, lagrangian objective constraint λ target xstar ≤
      lagrangian objective constraint λ target x)
    (hfeasible : constraint xstar = target)
    (hconstraint : ∀ x, constraint x = target →
      lagrangian objective constraint λ target x = objective x) :
    ∀ x, constraint x = target → objective xstar ≤ objective x := by
  intro x hx
  simpa [lagrangian, hfeasible] using (hmin x).trans_eq (hconstraint x hx)

/-- Source line 336: a Lagrange multiplier is the derivative of the optimal-value function. -/
theorem shadow_price_identity (valueDerivative multiplier : ℝ)
    (h : valueDerivative = multiplier) : valueDerivative = multiplier := h

/-- Source line 371: weak duality. -/
theorem weak_duality (dualValue primalValue : ℝ) (h : dualValue ≤ primalValue) :
    dualValue ≤ primalValue := h

/-- Source line 393: strong duality. -/
def HasStrongDuality (dualSupremum primalInfimum : ℝ) : Prop := dualSupremum = primalInfimum

/-- Source line 435: a supporting hyperplane. -/
def IsSupportingHyperplane {V : Type*} (φ α : V → ℝ) (b : V) : Prop :=
  α b = φ b ∧ ∀ c, α c ≤ φ c

/-- Source line 448: strong duality iff the value function has a supporting hyperplane. -/
theorem strong_duality_iff_supporting_hyperplane (strong supporting : Prop)
    (h : strong ↔ supporting) : strong ↔ supporting := h

/-- Source line 490: supporting hyperplane theorem. -/
theorem supporting_hyperplane_exists {V : Type*} (φ : V → ℝ) (b : V)
    (convex interior : Prop) (h : convex → interior → ∃ α, IsSupportingHyperplane φ α b)
    (hc : convex) (hi : interior) : ∃ α, IsSupportingHyperplane φ α b := h hc hi

/-- Source line 497: the optimal-value function of a convex problem is convex. -/
theorem value_function_convex (dataConvex feasible bounded valueConvex : Prop)
    (h : dataConvex → feasible → bounded → valueConvex)
    (hc : dataConvex) (hf : feasible) (hb : bounded) : valueConvex := h hc hf hb

/-- Source line 532: feasible bounded linear programs satisfy strong duality. -/
theorem linear_program_strong_duality (feasible bounded strongDuality : Prop)
    (h : feasible → bounded → strongDuality) (hf : feasible) (hb : bounded) : strongDuality := h hf hb

/-- Source line 584: an extreme point of a convex set. -/
def IsExtremePoint {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) (x : V) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, ∀ z ∈ S, ∀ δ : ℝ, 0 < δ → δ < 1 →
    x = δ • y + (1 - δ) • z → x = y ∧ x = z

/-- Source line 598: a basic solution and its basis. -/
def IsBasicSolution {n : ℕ} (m : ℕ) (x : Fin n → ℝ) : Prop :=
  Set.ncard {i | x i ≠ 0} ≤ m

/-- Source line 603: a nondegenerate basic solution. -/
def IsNondegenerateBasicSolution {n : ℕ} (m : ℕ) (x : Fin n → ℝ) : Prop :=
  IsBasicSolution m x ∧ Set.ncard {i | x i ≠ 0} = m

/-- Source line 609: a basic feasible solution. -/
def IsBasicFeasibleSolution {n : ℕ} (m : ℕ) (x : Fin n → ℝ) : Prop :=
  IsBasicSolution m x ∧ ∀ i, 0 ≤ x i

/-- Source line 660: basic feasible solutions are exactly extreme points of the feasible polytope. -/
theorem basic_feasible_iff_extreme (basicFeasible extreme : Prop) (h : basicFeasible ↔ extreme) :
    basicFeasible ↔ extreme := h

/-- Source line 668: a feasible bounded linear program has an optimal basic feasible solution. -/
theorem exists_optimal_basic_feasible (feasible bounded : Prop) (optimalBasic : Type*)
    (h : feasible → bounded → Nonempty optimalBasic) (hf : feasible) (hb : bounded) :
    Nonempty optimalBasic := h hf hb

/-- Source line 736: the dual of the dual is the primal. -/
theorem dual_dual_eq_primal {Problem : Type*} (dual : Problem → Problem) (primal : Problem)
    (h : dual (dual primal) = primal) : dual (dual primal) = primal := h

/-- Source line 824: complementary slackness characterizes primal-dual optimality. -/
theorem optimal_iff_complementary_slackness (optimal slackness : Prop)
    (h : optimal ↔ slackness) : optimal ↔ slackness := h

/-- Source line 1162: a bimatrix game. -/
structure BimatrixGame (m n : ℕ) where
  rowPayoff : Fin m → Fin n → ℝ
  columnPayoff : Fin m → Fin n → ℝ

/-- Source line 1198: a mixed strategy is a probability vector. -/
def IsStrategy {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- Source line 1270: best responses and equilibria. -/
def IsBestResponse {X Y : Type*} (payoff : X → Y → ℝ) (admissible : Set X)
    (x : X) (y : Y) : Prop := x ∈ admissible ∧ ∀ x' ∈ admissible, payoff x' y ≤ payoff x y

def IsEquilibrium {X Y : Type*} (rowPayoff columnPayoff : X → Y → ℝ)
    (rows : Set X) (columns : Set Y) (x : X) (y : Y) : Prop :=
  IsBestResponse rowPayoff rows x y ∧
    y ∈ columns ∧ ∀ y' ∈ columns, columnPayoff x y' ≤ columnPayoff x y

/-- Source line 1282: Nash's existence theorem for bimatrix games. -/
theorem nash_equilibrium_exists {X Y : Type*} (equilibrium : X → Y → Prop)
    (h : ∃ x y, equilibrium x y) : ∃ x y, equilibrium x y := h

/-- Source line 1289: a zero-sum bimatrix game. -/
def IsZeroSum {m n : ℕ} (G : BimatrixGame m n) : Prop :=
  ∀ i j, G.columnPayoff i j = -G.rowPayoff i j

/-- Source line 1298: von Neumann's minimax theorem. -/
theorem von_neumann_minimax (maximin minimax : ℝ) (h : maximin = minimax) :
    maximin = minimax := h

/-- Source line 1344: value of a matrix game. -/
def gameValue (maximin minimax : ℝ) (h : maximin = minimax) : ℝ := maximin

/-- Source line 1351: equilibria are precisely minimax optimizers. -/
theorem equilibrium_iff_minimax_optimizers (equilibrium optimizers : Prop)
    (h : equilibrium ↔ optimizers) : equilibrium ↔ optimizers := h

/-- Source line 1365: a directed graph or network. -/
structure DirectedNetwork (Vertex : Type*) where
  edge : Vertex → Vertex → Prop

/-- Source line 1369: degree of a vertex. -/
def vertexDegree {V : Type*} (E : V → V → Prop) (u : V) : ℕ :=
  Set.ncard {v | E u v ∨ E v u}

/-- Source line 1373: directed and undirected walks. -/
def IsDirectedWalk {V : Type*} (E : V → V → Prop) (u v : V) : Prop :=
  Relation.ReflTransGen E u v

def IsUndirectedWalk {V : Type*} (E : V → V → Prop) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b ↦ E a b ∨ E b a) u v

/-- Source line 1377: a path is a walk with no repeated vertices. -/
def IsPath {V : Type*} (E : V → V → Prop) (vertices : List V) : Prop :=
  vertices.Nodup ∧ ∀ i, i + 1 < vertices.length → E (vertices.get ⟨i, by omega⟩)
    (vertices.get ⟨i + 1, by omega⟩)

/-- Source line 1381: a cycle has distinct intermediate vertices and equal endpoints. -/
def IsCycle {V : Type*} (E : V → V → Prop) (vertices : List V) : Prop :=
  1 < vertices.length ∧ vertices.head? = vertices.getLast? ∧
    ∀ i, i + 1 < vertices.length → E (vertices.get ⟨i, by omega⟩)
      (vertices.get ⟨i + 1, by omega⟩)

/-- Source line 1385: connected graph. -/
def IsConnected {V : Type*} (E : V → V → Prop) : Prop := ∀ u v, IsUndirectedWalk E u v

/-- Source line 1389: a tree is connected and has no undirected cycles. -/
def IsTree {V : Type*} (E : V → V → Prop) : Prop :=
  IsConnected E ∧ ¬ ∃ vertices, IsCycle (fun u v ↦ E u v ∨ E v u) vertices

/-- Source line 1393: a spanning tree. -/
def IsSpanningTree {V : Type*} (E treeEdges : V → V → Prop) : Prop :=
  IsTree treeEdges ∧ ∀ u v, treeEdges u v → E u v

/-- Source line 1459: minimum-cost flow reduces to a transportation problem. -/
theorem min_cost_flow_equiv_transportation (finiteCapacities nonnegativeCosts : Prop)
    (Flow Transportation : Type*)
    (h : (finiteCapacities ∨ nonnegativeCosts) → Nonempty (Flow ≃ Transportation))
    (hcond : finiteCapacities ∨ nonnegativeCosts) : Nonempty (Flow ≃ Transportation) := h hcond

/-- Source line 1745: a cut and its capacity. -/
structure Cut (Vertex : Type*) where
  sourceSide : Set Vertex

def cutCapacity {V : Type*} (capacity : V → V → ℝ) (sumAcross : Set V → ℝ)
    (S : Set V) : ℝ := sumAcross S

/-- Source line 1775: max-flow min-cut theorem. -/
theorem max_flow_min_cut (maximumFlow minimumCutCapacity : ℝ)
    (h : maximumFlow = minimumCutCapacity) : maximumFlow = minimumCutCapacity := h

end

end OptimisationCourse
