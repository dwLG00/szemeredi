import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Init.Classical

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

-- Want to define topological structure on Bin so we can use Tychonoff's theorem
--   to prove cylinder sets in X are compact
def binTopologicalSpace : TopologicalSpace Bin := ⊥
instance : TopologicalSpace Bin := binTopologicalSpace
instance : TopologicalSpace X := Pi.topologicalSpace
instance : MeasurableSpace X := borel X

-- still want to define cylinder sets for the sake of ease
@[simp]
def cylinder (f : ℕ → Bin) (s : Finset ℕ) : Set X :=
  { x | ∀ i ∈ s, x i = f i }

@[simp]
def cylinderSets : Set (Set X) :=
  { A | ∃ (s : Finset ℕ) (f : ℕ → Bin), A = cylinder f s }

lemma cylinder_contains (f : X) (s : Finset ℕ) : f ∈ cylinder f s := by
  unfold cylinder
  simp

-- Need X to be locally compact hausdorff in order to guarantee existence of weak-* measure
def prodHausdorffSpace : T2Space X := {
  t2 := by
    unfold Pairwise
    simp
    intro f g hfg
    have : ∃ i : ℕ, f i ≠ g i := by
      by_contra!
      have : f = g := funext this
      exact hfg this
    let ⟨i, hi⟩ := this
    let u := cylinder f {i}
    let v := cylinder g {i}
    -- "set" funtions used to show u, v are open under Pi topology
    let U : ℕ → Set Bin := fun j => if j = i then {f i} else Set.univ
    let V : ℕ → Set Bin := fun j => if j = i then {g i} else Set.univ
    have hu : IsOpen u := by
      have : u = { f : X | ∀ i, f i ∈ U i } := by
        unfold U
        dsimp [u]
        simp
      apply isOpen_pi_iff.mpr
      intro f' hf'
      use {i}, U
      simp
      have : (IsOpen (U i) ∧ f' i ∈ U i) := by
        dsimp [U]
        rw [if_pos rfl]
        dsimp [u] at hf'
        simp at hf'
        have hf'₁ : f' i = f i := Set.mem_setOf.mp hf'
        simp
        apply And.intro _ hf'₁
        trivial -- all subsets of Bin are open
      apply And.intro this
      have : eval i ⁻¹' U i = { x : X | x i ∈ U i} := by
        rw [Set.eval_preimage']
        apply Set.ext
        intro x
        simp [update_self, mem_singleton_iff]
        rfl
      rw [this]
      dsimp [u, U]
      rw [if_pos rfl]
      simp
    have hv : IsOpen v := by
      have : v = { g : X | ∀ i, g i ∈ V i } := by
        unfold V
        dsimp [v]
        simp
      apply isOpen_pi_iff.mpr
      intro g' hg'
      use {i}, V
      simp
      have : (IsOpen (V i) ∧ g' i ∈ V i) := by
        dsimp [V]
        rw [if_pos rfl]
        dsimp [v] at hg'
        simp at hg'
        have hg'₁ : g' i = g i := Set.mem_setOf.mp hg'
        simp
        apply And.intro _ hg'₁
        trivial -- all subsets of Bin are open
      apply And.intro this
      have : eval i ⁻¹' V i = { x : X | x i ∈ V i} := by
        rw [Set.eval_preimage']
        apply Set.ext
        intro x
        simp [update_self, mem_singleton_iff]
        rfl
      rw [this]
      dsimp [v, V]
      rw [if_pos rfl]
      simp
    use u
    apply And.intro hu
    use v
    apply And.intro hv
    apply And.intro (cylinder_contains f {i})
    apply And.intro (cylinder_contains g {i})
    apply disjoint_iff.mpr
    simp
    by_contra! H
    have ⟨x, hx⟩ := H
    dsimp [u, v] at hx
    simp at hx
    rw [←And.left hx] at hi
    rw [And.right hx] at hi
    simp at hi


}

def prodCompactSpace : CompactSpace X := {
  isCompact_univ := by
    sorry
    /-
    unfold IsCompact
    intro cover h_cover_nontrivial h_cover_finer_than_univ
    /-
    let f : X := strongInduction (fun n ih =>
      match n with
      | 0 =>
        if ∃ A ∈ cover, ∃ f' ∈ A, f' 0 = ⟨0, by decide⟩
        then ⟨0, by decide⟩
        else ⟨1, by decide⟩
      | n + 1 =>
        if ∃ A ∈ cover, ∃ f' ∈ A, ∀ m < n, f' m = ih m ()
        then ⟨0, by decide⟩
        else ⟨1, by decide⟩
    )
    -/
    let f' : ℕ → X := by
      intro n
      induction n with
      | zero =>
        by_cases h : ∀ A ∈ cover, ∃ f' ∈ A, f' 0 = ⟨0, by decide⟩
        . exact (fun i => ⟨0, by decide⟩)
        . exact (fun i => ⟨1, by decide⟩)
      | succ N f =>
        let f' : X := (fun i => if i < N then f i else ⟨0, by decide⟩)
        by_cases h : ∀ A ∈ cover, ∃ f'' ∈ A, ∀ i ∈ Finset.range (N + 1), f' i = f'' i
        . exact f'
        . exact (fun i => if i < N then f i else ⟨1, by decide⟩)
    let f : X := fun i => f' i i
    use f
    apply And.intro (Set.mem_univ f)
    unfold ClusterPt
    by_contra! H
    simp at H
    apply Filter.inf_eq_bot_iff.mp at H
    let ⟨U, hU, V, hV, hUV⟩ := H
    apply mem_nhds_iff.mp at hU
    have ⟨T, hT, hT_open, hfT⟩ := hU
    let ⟨A, hA, hTA⟩ := open_sets_are_infinite_unions_of_cylinders T hT_open
    rw [hTA] at hfT
    apply Set.mem_sUnion.mp at hfT
    have ⟨T', hT', hfT'⟩ := hfT
    have hT'_cylinder : T' ∈ cylinderSets := by
      apply hA
      exact hT'
    unfold cylinderSets at hT'_cylinder
    simp at hT'_cylinder
    have ⟨s, f_T', hT'₁⟩ := hT'_cylinder
    have : s.Nonempty := by
      by_contra! H
      simp at H
      rw [H] at hT'₁
      simp at hT'₁
      rw [hT'₁] at hT'
      have hT_univ: T = Set.univ := by
        have h_union : (⋃₀ A) = univ := by
          ext x
          constructor
          · intro hx
            -- if x ∈ ⋃₀ A then certainly x ∈ univ
            trivial
          · intro _
            -- since univ ∈ A and x ∈ univ, x ∈ ⋃₀ A
            use univ, hT'
        -- now rewrite T = ⋃₀ A using hTA and replace ⋃₀ A with univ
        rw [h_union] at hTA
        exact hTA
      rw [hT_univ] at hT
      simp at hT
      rw [hT] at hUV
      simp at hUV
      rw [hUV] at hV
      have := Filter.empty_mem_iff_bot.mp hV
      rw [this] at h_cover_nontrivial
      exact h_cover_nontrivial.ne rfl
    let N : ℕ := s.max' this -- s = {i₁, i₂, ..., iₖ = N}
    let s' := Finset.range (N + 1) -- s' = {0, ..., N}
    let T'' := cylinder f s' -- f ∈ T ⊆ T' = cylinder (f' N) s'
    have hT'T'' : T'' ⊆ T' := by
      dsimp [T'']
      rw [hT'₁]
      simp
      intro a h
      have : s ⊆ s' := by
        dsimp [s']
        intro z hz
        have : z ≤ N := by
          dsimp [N]
          exact s.le_max' z hz
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr this)
      intro i hi
      have hi' : i ∈ s' := this hi
      specialize h i hi'
      rw [h]
      rw [hT'₁] at hfT'
      simp at hfT'
      exact hfT' i hi
    have hT''U : T'' ⊆ U := by
      have : T' ⊆ T := by
        rw [hTA]
        exact Set.subset_sUnion_of_mem hT'
      exact (hT'T''.trans this).trans hT
    have hT''V : T'' ∩ V = ∅ := by
      have h₁ : T'' ∩ V ⊆ U ∩ V := Set.inter_subset_inter_left _ hT''U
      have h₂ : T'' ∩ V ⊆ ∅ := by rwa [hUV] at h₁
      exact (Set.subset_empty_iff.mp h₂)
    have : ∃ V' ∈ cover, ∀ g ∈ V', ∃ i ∈ s', g i ≠ f i := by
      use V
      apply And.intro hV
      intro g hg
      by_contra! H
      have : g ∈ cylinder f s' := by
        sorry
      unfold T'' at hT''V
      have this' : g ∈ (cylinder f s') ∩ V := And.intro this hg
      rw [hT''V] at this'
      simp at this'
    unfold f at this
    unfold f' at this
    simp at this

    sorry
  -/
}

def prodLocallyCompactSpace : LocallyCompactSpace X := {
  local_compact_nhds := by
    sorry
    /-
    intros x n' hn'
    rcases mem_nhds_iff.mp hn' with ⟨n, hnn', hno, hn⟩
    have hn₁ : n ∈ 𝓝 x := mem_nhds_iff.mpr ⟨n, subset_rfl, hno, hn⟩
    -- cylinderSets is a basis bc finite intersections are cylinder sets or ∅
    have : ∃ (A : Set (Set X)), A ⊆ cylinderSets ∧ n = ⋃₀ A
      := open_sets_are_infinite_unions_of_cylinders n hno
    -- A is a set of cylinder sets, and x ∈ ⋃₀ A, so A isn't empty
    --   => ∃ a ∈ A which is a cylinder set -> compact, and x ∈ a
    let ⟨A, h_Acylinder, hnA⟩ := this
    have hAu : A.Nonempty := by
      by_contra! H
      rw [H] at hnA
      simp at hnA
      rw [hnA] at hn
      exact hn
    have hnx : x ∈ n := by
      rcases mem_nhds_iff.mp hn₁ with ⟨_, htn, _, hxt⟩
      exact htn hxt
    rw [hnA] at hnx
    obtain ⟨a, ha, hax⟩ := Set.mem_sUnion.1 hnx
    have han' : a ⊆ n' := by
      apply subset_trans _ hnn'
      rw [hnA]
      exact Set.subset_sUnion_of_mem ha
    use a
    apply h_Acylinder at ha
    have a_open : IsOpen a := TopologicalSpace.GenerateOpen.basic a ha
    have a_nhd : a ∈ 𝓝 x := a_open.mem_nhds hax
    have a_compact : IsCompact a := cylinderCompact a ha
    exact ⟨a_nhd, han', a_compact⟩
  -/
}

instance : T2Space X := prodHausdorffSpace
instance : LocallyCompactSpace X := prodLocallyCompactSpace

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
