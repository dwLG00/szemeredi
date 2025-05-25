import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Basic

open MeasureTheory NNReal
open Set Function

noncomputable section

/-
Szemeredi's theorem statement
-/
open scoped BigOperators
open Set
noncomputable def avg_lt_n (a : Set ℕ) (n : ℕ) : ℝ≥0 :=
  let lt_n := {x ∈ a | x ≤ n}
  let lt_n_finite : Set.Finite lt_n := by
    apply Set.Finite.subset (Finset.range (n + 1)).finite_toSet
    intro x hx
    simp
    let ⟨_, hle⟩ := hx
    exact Nat.lt_succ_of_le hle
  let fset := lt_n_finite.toFinset
  (fset.card : ℝ≥0) / (n + 1 : ℝ≥0)


def positive_upper_density (a : Set ℕ) : Prop :=
  let f := fun n => avg_lt_n a n
  Filter.limsup f Filter.atTop > 0

def has_k_term_arithmetic_sequence (a : Set ℕ) (k : ℕ) : Prop
  := ∃ n m: ℕ, ∀ i ∈ Finset.range k, n + i*m ∈ a

theorem szemeredi (a : Set ℕ) : positive_upper_density a → ∀ k : ℕ, has_k_term_arithmetic_sequence a k := sorry

/-
Defining measure-preserving systems, and establishing the SZ property (`Szemeredi`)
-/

variable {α: Type*} [MeasurableSpace α]

-- T^{-n} E
def preimage_iter (T : α → α) (n : ℕ) (E : Set α) : Set α :=
  (T^[n])⁻¹' E

-- ⋂ i=0..k-1 T^{-in} E
def first_k_intersections (T : α → α) (n k : ℕ) (E : Set α) : Set α :=
  ⋂ i ∈ Finset.range k, preimage_iter T (i * n) E

-- ∑ n=0..N-1 μ(⋂ i=0..k-1 T^{-in}E)
def first_k_intersections_N_sum (μ : FiniteMeasure α) (T : α → α) (N k : ℕ) (E : Set α) : ℝ≥0 :=
  ∑ n ∈ Finset.range N, μ (first_k_intersections T n k E)


open MeasurableSpace Tactic

structure MPSystem (α : Type*) [MeasurableSpace α] where
  μ : FiniteMeasure α
  T : α → α
  measure_preserving : ∀ E : Set α, MeasurableSet E → μ E = μ (T⁻¹' E)

structure Szemeredi {α : Type*} [MeasurableSpace α] (system : MPSystem α) : Prop where
    protected liminf : ∀ E : Set α, MeasurableSet E ∧ system.μ E > 0 →
      ∀ k : ℕ, Filter.liminf (fun N : ℕ => first_k_intersections_N_sum system.μ system.T N k E / N) Filter.atTop > 0

lemma sum_gt_exists_term_gt {s : Finset ℕ} {f : ℕ → ℝ≥0} (h : 0 < ∑ i ∈ s, f i) :
  ∃ i ∈ s, f i > 0 := by
  by_contra! H
  have h2 : ∑ i ∈ s, f i ≤ 0 := Finset.sum_nonpos H
  exact lt_irrefl _ (lt_of_lt_of_le h h2)

lemma SZ_implies_one_k_works {α : Type*} [MeasurableSpace α] (system : MPSystem α) (SZ : Szemeredi system)
  : ∀ k : ℕ, ∀ E : Set α, MeasurableSet E ∧ system.μ E > 0 → ∃ m : ℕ, system.μ (first_k_intersections system.T m k E) > 0 := by
  -- intros
  intro k
  intro E
  intro E_positive_measure
  -- Given k, our liminf is always > 0
  apply SZ.liminf at E_positive_measure
  let liminf := E_positive_measure k
  -- liminf > 0 => for some N, a_n > 0 for all n > N
  have eventually_positive := Filter.eventually_lt_of_lt_liminf liminf
  simp at eventually_positive -- simplifies out division, explicitly gives us N (as `a`)
  obtain ⟨a, ht⟩ := eventually_positive
  -- apply a value we know is > a and simplify
  let avg_is_positive := ht (a + 1)
  simp at avg_is_positive
  -- expand out the sum
  rw [first_k_intersections_N_sum] at avg_is_positive
  -- use lemma to show that sum > 0 => at least one term > 0
  let exists_pos_term := sum_gt_exists_term_gt avg_is_positive
  -- extract index of said term
  obtain ⟨i, hi_range, hi_pos⟩ := exists_pos_term
  exact ⟨i, hi_pos⟩

/-
Constructing our particular MP system
-/

open Set MeasureTheory Topology

-- Construct the measurable space (define the measure later)
def Bin := Finset.range 2
def X := ℕ → Bin

def cylinder (f : ℕ → Bin) (s : Finset ℕ) : Set X :=
  { x | ∀ i ∈ s, x i = f i }

def cylinderSets : Set (Set X) :=
  { A | ∃ (s : Finset ℕ) (f : ℕ → Bin), A = cylinder f s }

def cylinderMeasurableSpace : MeasurableSpace X :=
  MeasurableSpace.generateFrom cylinderSets

instance : MeasurableSpace X := cylinderMeasurableSpace

-- The shift map
def T : X → X :=
  fun f : X => (fun i : ℕ => f (i + 1))

lemma T_is_measurable : Measurable T := sorry

-- define the positive density measure

def subset_to_func (a : Set ℕ) [DecidablePred (· ∈ a)] : X :=
  fun i => if h : i ∈ a then ⟨1, by decide⟩ else ⟨0, by decide⟩

def func_to_subset (s : X) : Set ℕ :=
  {x : ℕ | s x = ⟨1, by decide⟩}

def first_n_T (s : X) (n : ℕ) : Set X :=
  {T^[i] s | i ∈ Finset.range n}

def μs_proto (n : ℕ) (s : X) : (subset : Set X) → MeasurableSet subset → ℝ≥0 :=
  (fun subset : Set X =>
    (fun h : MeasurableSet subset =>
      let first_n_T_in_subset := (subset ∩ first_n_T s n)
      let fnTis_finite : Set.Finite first_n_T_in_subset := by sorry
      (fnTis_finite.toFinset.card : ℝ≥0) / (n + 1 : ℝ≥0)
    )
  )

-- TODO: prove that μs_proto ∅ = 0
lemma μs_proto_empty_zero : ∀ n : ℕ, ∀ s : X, μs_proto n s ∅ MeasurableSet.empty = 0 :=
  sorry


def μs (s : X) (h : positive_upper_density (func_to_subset s)) : ℕ → Measure X :=
  fun n : ℕ => (
    MeasureTheory.Measure.ofMeasurable
      (fun A hA => ↑(μs_proto n s A hA))
      (by
        apply ENNReal.coe_eq_zero.2
        exact μs_proto_empty_zero n s
      )
      (sorry) -- TODO: prove that μs is additive
  )

-- the actual measure
def μ (s : X) (h : positive_upper_density (func_to_subset s)) : Measure X := sorry

/-
example : positive_upper_density {x : ℕ | ∃ y : ℕ, 2 * y = x} := by
  let evens := {x : ℕ | ∃ y : ℕ, 2 * y = x}
  unfold positive_upper_density
  let f := fun n ↦ avg_lt_n {x | ∃ y, 2 * y = x} n
  simp [f]
  have h : ∀ n : ℕ, f n > 1 / 4 := by
    intro n
    unfold f
    unfold avg_lt_n
    let lt_n := {x | x ∈ {x | ∃ y, 2 * y = x} ∧ x ≤ n}
    let lt_n_finite := Set.Finite lt_n
    induction n

-/
