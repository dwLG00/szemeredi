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
import Szemeredi.CorrespondencePrinciple

open MeasureTheory NNReal
open Set Function

noncomputable section

/-
Szemeredi's theorem statement
-/

theorem szemeredi (a : Set ℕ) : positive_upper_density a → ∀ k : ℕ, has_k_term_arithmetic_sequence a k := sorry
