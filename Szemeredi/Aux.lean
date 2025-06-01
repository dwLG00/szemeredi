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

-- Combinatorics
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

-- Topology
open TopologicalSpace
open Finset
variable {X : Type*}

lemma open_sets_are_infinite_unions_of_finite_intersections :
  @IsOpen X (TopologicalSpace.generateFrom G) U →
  ∃ (C : Set (Set X)), (∀ V ∈ C, ∃ (F : Finset (Set X)), (↑F : Set (Set X)) ⊆ G ∧ V = ⋂₀ (↑F))
  ∧ U = ⋃₀ C := by
    intro hu
    induction hu with
    | basic a ha =>
      let C : Finset (Set X) := {a}
      use C
      have : ∀ V ∈ C, ∃ F : Finset (Set X), ↑F ⊆ G ∧ V = ⋂₀ F := by
        intro V hV
        unfold C at hV
        simp at hV
        use C
        unfold C
        simp
        exact ⟨ha, hV⟩
      apply And.intro this
      unfold C
      simp
    | univ =>
      let C : Finset (Set X) := {univ}
      use C
      have : ∀ V ∈ C, ∃ F : Finset (Set X), ↑F ⊆ G ∧ V = ⋂₀ F := by
        intro V hV
        unfold C at hV
        simp at hV
        let F : Finset (Set X) := ∅
        use F
        unfold F
        simp
        exact hV
      apply And.intro this
      unfold C
      simp
    | inter S T hS hT hS' hT' =>
      let ⟨Cs, hS_inter, hS_union⟩ := hS'
      let ⟨Ct, hT_inter, hT_union⟩ := hT'
      let C : Set (Set X) := Set.image2 (· ∩ ·) Cs Ct
      use C
      have : (∀ V ∈ C, ∃ F : Finset (Set X), ↑F ⊆ G ∧ V = ⋂₀ ↑F) := by
        intro V hV
        unfold C at hV
        simp at hV
        let ⟨s, hs, t, ht, hst⟩ := hV
        -- s, t are both intersections of elts in G. So we want to give s ∪ t,
        -- which corresponds to the intersection ⋂₀ s ∩ ⋂₀ t
        specialize hS_inter s hs
        let ⟨Fs, hFsG, hFs_inter⟩ := hS_inter
        specialize hT_inter t ht
        let ⟨Ft, hFtG, hFt_inter⟩ := hT_inter
        -- For whatever reason i couldnt just take the union of finsets...
        let F' := (↑Fs : Set (Set X)) ∪ (↑Ft)
        have : F'.Finite := by
          unfold F'
          simp
        let F := this.toFinset
        use F
        unfold F
        simp
        unfold F'
        simp
        apply And.intro ⟨hFsG, hFtG⟩
        rw [hFs_inter, hFt_inter] at hst
        rw [←hst]
        exact (Set.sInter_union (↑Fs : Set (Set X)) ↑Ft).symm
      apply And.intro this
      unfold C
      simp
      ext z
      constructor
      . intro hz
        let ⟨hzS, hzT⟩ := hz
        rw [hS_union] at hzS
        rw [hT_union] at hzT
        let ⟨S', hS', hs'⟩ := (Set.mem_sUnion).1 hzS
        let ⟨T', hT', ht'⟩ := (Set.mem_sUnion).1 hzT
        simp
        exact ⟨ S', hs', hS', T', hT', ht'⟩
      . simp
        intros S' hzS' hS'Cs T' hT'Ct hzT'
        have hS' : S' ⊆ ⋃₀ Cs := Set.subset_sUnion_of_mem hS'Cs
        rw [←hS_union] at hS'
        apply hS' at hzS'
        have hT' : T' ⊆ ⋃₀ Ct := Set.subset_sUnion_of_mem hT'Ct
        rw [←hT_union] at hT'
        apply hT' at hzT'
        exact ⟨hzS', hzT'⟩
    | sUnion S hS hS' =>
      choose f hf using hS'
      set g : Subtype S → Set (Set X) := fun x => f x.1 x.2 -- aux function
      set C : Set (Set X) := ⋃₀ (g '' (univ : Set (Subtype S)))
      use C
      have hVF : (∀ V ∈ C, ∃ F : Finset (Set X), ↑F ⊆ G ∧ V = ⋂₀ ↑F) := by
        intro V hV
        have ⟨Y, hY_in_image, hY_in_union⟩ :
          ∃ Y, Y ∈ (g '' (Set.univ : Set (Subtype S))) ∧ V ∈ Y :=
          (Set.mem_sUnion.1 hV)
        rcases (Set.mem_image g Set.univ Y).1 hY_in_image with ⟨x, hx_univ, hgY⟩
        have Y_def : Y = f x.1 x.2 := by dsimp [g] at hgY; exact Eq.symm hgY
        let ⟨s, a⟩ := x
        simp at Y_def
        have : ∀ V' ∈ f s a, ∃ F : Finset (Set X), ↑F ⊆ G ∧ V' = ⋂₀ ↑F := by
          specialize hf s a
          exact hf.left
        rw [Y_def] at hY_in_union
        specialize this V hY_in_union
        exact this
      have hSC : ⋃₀ S = ⋃₀ C := by
        unfold C
        unfold g
        simp
        ext z
        constructor
        . intro hz
          let ⟨S', hS', hz'⟩ := (Set.mem_sUnion).1 hz
          specialize hf S' hS'
          let ⟨hV_construct, hS'_construct⟩ := hf
          rw [hS'_construct] at hz'
          have hsub : f S' hS' ⊆ (⋃ x : Subtype S, f x.1 x.2) := by
            intro Y hY
            -- we need to show Y ∈ ⋃ x, f x.1 x.2.
            -- but `x = ⟨S', hS'⟩` is a valid index, since `S' ∈ S` by hS'.
            apply Set.mem_iUnion.2
            use (⟨S', hS'⟩ : Subtype S)
          let ⟨Z', hZ', hzZ⟩ := (Set.mem_sUnion).1 hz'
          apply hsub at hZ'
          exact Set.mem_sUnion.2 ⟨Z', hZ', hzZ⟩
        . intro hz
          let ⟨S', hS', hz'⟩ := (Set.mem_sUnion).1 hz
          apply Set.mem_iUnion.1 at hS'
          let ⟨x, hx⟩ := hS'
          specialize hf x x.2
          have ⟨hV1, hV2⟩ := hf
          have : S' ⊆ ⋃₀ f ↑x x.2 := Set.subset_sUnion_of_mem hx
          rw [←hV2] at this
          apply this at hz'
          have hx' : ↑x ⊆ ⋃₀ S := Set.subset_sUnion_of_mem x.2
          apply hx' at hz'
          exact hz'
      exact ⟨hVF, hSC⟩
