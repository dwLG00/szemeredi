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

/-
Additional measure theory structures I need
-/

namespace auxMeasureTheory

open MeasureTheory NNReal
open Set Function

open scoped Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

def IsWeakLimit (μs : ℕ → Measure X) (μ : Measure X) : Prop :=
  ∀ {f : BoundedContinuousFunction X ℝ}, Filter.Tendsto (fun n => ∫ a, f a ∂(μs n)) Filter.atTop (𝓝 (∫ a, f a ∂μ))

end auxMeasureTheory
