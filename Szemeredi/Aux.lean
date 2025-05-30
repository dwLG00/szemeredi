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


open scoped BigOperators
open NNReal
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
