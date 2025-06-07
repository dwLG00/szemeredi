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
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-
Additional measure theory structures I need
-/

namespace auxMeasureTheory

open MeasureTheory NNReal
open Set Function

open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

open scoped Topology
open scoped BoundedContinuousFunction NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

def IsWeakLimit (μs : ℕ → Measure X) (μ : Measure X) : Prop :=
  ∀ {f : BoundedContinuousFunction X ℝ}, Filter.Tendsto (fun n => ∫ a, f a ∂(μs n)) Filter.atTop (𝓝 (∫ a, f a ∂μ))

lemma compact_support_NNReal_continuous_integrable
  (m : Measure X) [IsFiniteMeasureOnCompacts m] (f : C_c(X, ℝ≥0))
  : Integrable (fun a => (f a : ℝ)) m := by
    have h_cont : Continuous fun a => (f a : ℝ) := continuous_subtype_val.comp f.continuous
    have h_supp : HasCompactSupport fun a => (f a : ℝ) := by
      have : NNReal.toReal 0 = 0 := by rfl
      exact (f.hasCompactSupport).comp_left this
    exact h_cont.integrable_of_hasCompactSupport h_supp

noncomputable def integralNNReal (m : Measure X) [IsFiniteMeasureOnCompacts m] : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ where
  toFun      f := ∫ x, (f x) ∂m
  map_add'   := by
    intro x y
    have hx : Integrable (fun a => (x a : ℝ)) m := compact_support_NNReal_continuous_integrable m x
    have hy : Integrable (fun a => (y a : ℝ)) m := compact_support_NNReal_continuous_integrable m y
    simp
    apply integral_add hx hy
  map_smul'  := by
    intro c x
    simp
    have hx : Integrable (fun a => (x a : ℝ)) m := compact_support_NNReal_continuous_integrable m x
    apply integral_const_mul

noncomputable def functionalsFromMeasures
  (ms : ℕ → Measure X) (hms : ∀ i, IsFiniteMeasureOnCompacts (ms i))
  : ℕ → (C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ) := (fun i =>
    integralNNReal (ms i)
  )
end auxMeasureTheory
