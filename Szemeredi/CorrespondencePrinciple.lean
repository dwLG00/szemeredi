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

import Szemeredi.AuxMeasureTheory
import Szemeredi.Aux

open MeasureTheory NNReal
open Set Function

noncomputable section


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

structure SZSystem {α : Type*} [MeasurableSpace α] (system : MPSystem α) : Prop where
    protected liminf : ∀ E : Set α, MeasurableSet E ∧ system.μ E > 0 →
      ∀ k : ℕ, Filter.liminf (fun N : ℕ => first_k_intersections_N_sum system.μ system.T N k E / N) Filter.atTop > 0

lemma sum_gt_exists_term_gt {s : Finset ℕ} {f : ℕ → ℝ≥0} (h : 0 < ∑ i ∈ s, f i) :
  ∃ i ∈ s, f i > 0 := by
  by_contra! H
  have h2 : ∑ i ∈ s, f i ≤ 0 := Finset.sum_nonpos H
  exact lt_irrefl _ (lt_of_lt_of_le h h2)

lemma SZ_implies_one_k_works {α : Type*} [MeasurableSpace α] (system : MPSystem α) (SZ : SZSystem system)
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

@[simp]
def cylinder (f : ℕ → Bin) (s : Finset ℕ) : Set X :=
  { x | ∀ i ∈ s, x i = f i }

@[simp]
def cylinderSets : Set (Set X) :=
  { A | ∃ (s : Finset ℕ) (f : ℕ → Bin), A = cylinder f s }

def cylinderMeasurableSpace : MeasurableSpace X :=
  MeasurableSpace.generateFrom cylinderSets

def cylinderTopologicalSpace : TopologicalSpace X :=
  TopologicalSpace.generateFrom cylinderSets

instance : MeasurableSpace X := cylinderMeasurableSpace
instance : TopologicalSpace X := cylinderTopologicalSpace

-- The shift map, and proving the shift map is measurable
def T : X → X :=
  fun f : X => (fun i : ℕ => f (i + 1))

lemma preimage_of_cylinder_is_measurable (b : Set X) (hb : b ∈ cylinderSets)
  : MeasurableSet (T⁻¹' b) := by
  rcases hb with ⟨s, f, rfl⟩
  let s' : Finset ℕ := s.image Nat.succ
  let g := f ∘ Nat.pred
  have : T ⁻¹' cylinder f s = cylinder g s' := by
    ext x
    simp [cylinder, Set.preimage, s', g]
    unfold T
    rfl
  rw [this]
  let b := cylinder g s'
  change MeasurableSet b
  have h: b ∈ cylinderSets := ⟨s', g, rfl⟩
  apply GenerateMeasurable.basic
  exact h

lemma T_is_measurable : Measurable T := by
  intro a
  intro h
  unfold MeasurableSet at h
  unfold instMeasurableSpaceX at h
  unfold cylinderMeasurableSpace at h
  -- h : (generateFrom cylinderSets).MeasurableSet' a
  dsimp only [MeasurableSpace.generateFrom, MeasurableSpace.MeasurableSet'] at h
  induction h with
  | basic b h₁ => exact preimage_of_cylinder_is_measurable b h₁
  | empty => dsimp only [Set.preimage_empty]; exact MeasurableSet.empty
  | compl t ht htinv =>
    dsimp
    let t' := T ⁻¹' t
    apply GenerateMeasurable.compl t'
    exact htinv
  | iUnion f h h₁ =>
    simp
    apply GenerateMeasurable.iUnion
    exact h₁

-- define the positive density measure

def subset_to_func (a : Set ℕ) [DecidablePred (· ∈ a)] : X :=
  fun i => if h : i ∈ a then ⟨1, by decide⟩ else ⟨0, by decide⟩

def func_to_subset (s : X) : Set ℕ :=
  {x : ℕ | s x = ⟨1, by decide⟩} -- Need to do because of how we defined Bin

def first_n_T (s : X) (n : ℕ) : Set X :=
  (Finset.range n).toSet.image (fun i => T^[i] s)

def μs_proto (n : ℕ) (s : X) : (subset : Set X) → MeasurableSet subset → ℝ≥0 :=
  (fun subset : Set X =>
    (fun h : MeasurableSet subset =>
      let first_n_T_in_subset := (subset ∩ first_n_T s n)
      let fnTis_finite : Set.Finite first_n_T_in_subset := by
        have h₁ : first_n_T_in_subset ⊆ first_n_T s n := by
          unfold first_n_T_in_subset
          simp
        have h₂ : (first_n_T s n).Finite := by
          unfold first_n_T
          exact (Finset.finite_toSet (Finset.range n)).image (fun i => T^[i] s)
        apply Set.Finite.subset
        . exact h₂
        . exact h₁
      (fnTis_finite.toFinset.card : ℝ≥0) / (n + 1 : ℝ≥0)
    )
  )

lemma μs_proto_empty_zero
  : ∀ n : ℕ, ∀ s : X, μs_proto n s ∅ MeasurableSet.empty = 0 := by
  intro n s
  unfold μs_proto
  simp

open BigOperators

def μs (s : X) (h : positive_upper_density (func_to_subset s)) : ℕ → Measure X :=
  fun n : ℕ => (
    MeasureTheory.Measure.ofMeasurable
      (fun A hA => ↑(μs_proto n s A hA))
      (by
        apply ENNReal.coe_eq_zero.2
        exact μs_proto_empty_zero n s
      )
      (by
        intro f h h₁
        simp
        unfold μs_proto
        have h_ne : (↑n + 1 : ENNReal) ≠ 0 := by simp
        simp
        sorry
        --rw [tsum_div_const (fun i => (μs_proto._proof_4 n s (f i)).toFinset.card) h_ne]
      ) -- TODO: prove that μs is additive
  )

-- the actual measure
def μ (s : X) (h : positive_upper_density (func_to_subset s)) : FiniteMeasure X := sorry

--lemma μ_is_μs_weak_limit (s : X) (h : positive_upper_density (func_to_subset s)): AuxMeasureTheory.IsWeakLimit (μs s h) (μ s h) := sorry


end
