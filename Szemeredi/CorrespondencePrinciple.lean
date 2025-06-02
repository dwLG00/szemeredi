import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

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

lemma cylinder_sets_non_empty : ∀ a ∈ cylinderSets, a.Nonempty := by
  intro a ha
  unfold cylinderSets at ha
  simp at ha
  have ⟨s, f, hsf⟩ := ha
  rw [hsf]
  unfold Set.Nonempty
  exact ⟨f, by simp⟩

def cylinderMeasurableSpace : MeasurableSpace X :=
  MeasurableSpace.generateFrom cylinderSets

def cylinderTopologicalSpace : TopologicalSpace X :=
  TopologicalSpace.generateFrom cylinderSets

instance : MeasurableSpace X := cylinderMeasurableSpace
instance : TopologicalSpace X := cylinderTopologicalSpace

-- Need X to be locally compact hausdorff in order to guarantee existence of weak-* measure
def cylinderHausdorffSpace : T2Space X := {
  t2 := by
    intro x y
    intro h
    have h₁ : ∃ i : ℕ, x i ≠ y i := Function.ne_iff.mp h
    let ⟨i, hi⟩ := h₁
    set u := cylinder x {i} with u'
    set v := cylinder y {i} with v'
    have uv_disjoint : Disjoint u v := by
      unfold Disjoint
      intros a hau hav
      simp
      by_contra! H
      rcases H with ⟨a', ha⟩
      have haiu : a' i = x i := by
        let ha' := ha
        apply hau at ha'
        unfold u at ha'
        unfold cylinder at ha'
        simp at ha'
        exact ha'
      have haiv : a' i = y i := by
        apply hav at ha
        unfold v at ha
        unfold cylinder at ha
        simp at ha
        exact ha
      have xiyi : x i = y i := Eq.trans haiu.symm haiv
      absurd xiyi
      exact hi
    have hu : IsOpen u := by
      have : u ∈ cylinderSets := ⟨{i}, x, rfl⟩
      exact TopologicalSpace.GenerateOpen.basic u this
    have hv : IsOpen v := by
      have : v ∈ cylinderSets := ⟨{i}, y, rfl⟩
      exact TopologicalSpace.GenerateOpen.basic v this
    have hu_x : x ∈ u := by
      unfold cylinder at u'
      rw [u']
      simp
    have hv_y : y ∈ v := by
      unfold cylinder at v'
      rw [v']
      simp
    exact ⟨u, v, hu, hv, hu_x, hv_y, uv_disjoint⟩
}

open Std
open Finset
open Set

lemma finite_intersections_of_cylinders_is_cylinder
  (a : Set (Set X)) (ha : a ≤ cylinderSets) (ha' : Set.Finite a)
  : ⋂₀ a ∈ cylinderSets ∨ ⋂₀ a = ∅ := by
    induction a, ha' using Set.Finite.induction_on with
    | empty => -- Cylinder taken over an empty set is the full set
      simp
      apply Or.intro_left
      let f : X := (fun i => ⟨1, by decide⟩)
      have : Set.univ = cylinder f ∅ := by
        unfold cylinder
        simp
      exact ⟨∅, f, this⟩
    | @insert x s h_notin_s h_finite h_main_implication =>
      have ⟨hx, s_cylinder⟩ := Set.insert_subset_iff.mp ha
      apply h_main_implication at s_cylinder
      have h_cap : x ∩ ⋂₀ s = ⋂₀ insert x s := by -- useful lemma
        ext b
        simp
      rcases s_cylinder with h₁ | h₂ -- split on ⋂₀ s being cylinder or empty
      . simp at h₁ -- case: ⋂₀ s is a cylinder
        obtain ⟨ss, fs, hs⟩ := h₁
        simp at hx
        obtain ⟨sx, fx, hx'⟩ := hx
        by_cases H : ∀ i ∈ ss ∩ sx, fs i = fx i -- split on if fs, fx agree on ss ∩ sx
        . let susx := ss ∪ sx -- case : fs i = fx i on ss ∩ sx
          have h_susx : susx = ss ∪ sx := by rfl
          -- Intersection of two cylinders: cylinder susx f
          --   where f is piecewise defined by fs, fx on ss, sx resp.
          --   and agree on ss ∩ sx
          let f : X := (fun i =>
            if i ∈ sx then fx i else
            if i ∈ ss then fs i else
            ⟨1, by decide⟩ -- throwaway
          )
          let new_cylinder := cylinder f susx
          have h_new_cylinder : new_cylinder = cylinder f susx := rfl
          have : new_cylinder ∈ cylinderSets := by exact ⟨susx, f, h_new_cylinder⟩
          have h_nc : new_cylinder = x ∩ ⋂₀ s := by -- need to prove both directions
            rw [h_new_cylinder]
            unfold cylinder
            ext z
            constructor
            . intro hz
              simp at hz
              have hzx : z ∈ x := by
                rw [h_susx] at hz
                have : ∀ i ∈ sx, z i = f i := by
                  intro i hi
                  apply hz i
                  exact Finset.mem_union_right _ hi
                have : ∀ i ∈ sx, z i = fx i := by
                  intro i hi
                  unfold f at this
                  let goal := this i hi
                  simp [hi] at goal
                  exact goal
                rw [hx']
                exact this
              have hzs : z ∈ ⋂₀ s := by
                rw [h_susx] at hz
                have : ∀ i ∈ ss, z i = f i := by
                  intro i hi
                  apply hz i
                  exact Finset.mem_union_left _ hi
                have : ∀ i ∈ ss, z i = fs i := by
                  intro i hi
                  unfold f at this
                  let goal := this i hi
                  split_ifs at goal with in_x
                  . have : i ∈ ss ∩ sx := by exact Finset.mem_inter.2 ⟨hi, in_x⟩
                    apply H at this
                    rw [←this] at goal
                    exact goal
                  . exact goal
                rw [hs]
                exact this
              exact ⟨hzx, hzs⟩
            . intro hz
              rw [hx', hs] at hz
              simp at hz
              have ⟨hzx, hzs⟩ := hz
              have : ∀ i ∈ susx, z i = f i := by
                have hzx' : ∀ i ∈ sx, z i = f i := by
                  unfold f
                  intro i hi
                  simp [hi]
                  apply hzx at hi
                  exact hi
                have hzs' : ∀ i ∈ ss, z i = f i := by
                  unfold f
                  intro i hi
                  simp [hi]
                  split_ifs with in_x
                  . apply hzx at in_x
                    exact in_x
                  . apply hzs at hi
                    exact hi
                rw [Finset.forall_mem_union]
                change ((∀ i ∈ ss, z i = f i) ∧ ∀ i ∈ sx, z i = f i)
                exact ⟨hzs', hzx'⟩
              exact this
          rw [h_nc, h_cap] at this
          exact Or.inl this
        . simp at H -- case : fx and fs don't agree -> the intersection is empty
          obtain ⟨x', hxss, hxsx, hnf⟩ := H
          have : x ∩ ⋂₀ s = ∅ := by
            by_contra! H'
            let ⟨y, hy⟩ := H'
            let ⟨hyx, hyis⟩ := hy
            rw [hx'] at hyx
            simp at hyx
            rw [hs] at hyis
            simp at hyis
            specialize hyx x' hxsx
            specialize hyis x' hxss
            rw [hyx] at hyis
            exact hnf hyis.symm
          rw [h_cap] at this
          exact Or.inr this
      . have : x ∩ ⋂₀ s = ∅ := by -- case : ⋂₀ s = ∅
          rw [h₂]
          exact Set.inter_empty x
        rw [h_cap] at this
        exact Or.inr this

-- Because intersections of cylinders are cylinders or empty, we can
--   improve our explicit formula for open sets
lemma open_sets_are_infinite_unions_of_cylinders (a : Set X) (ha : IsOpen a)
  : ∃ A : Set (Set X), A ⊆ cylinderSets ∧ a = ⋃₀ A := by
    have : ∃ (C : Set (Set X)), (∀ V ∈ C, ∃ (F : Finset (Set X)),
      (↑F : Set (Set X)) ⊆ cylinderSets ∧ V = ⋂₀ (↑F)) ∧ a = ⋃₀ C :=
        open_sets_are_infinite_unions_of_finite_intersections ha
    let ⟨C, hC₁, hC₂⟩ := this
    have : ∀ V ∈ C, V ∈ cylinderSets ∨ V = ∅ := by
      intro V hV
      specialize hC₁ V hV
      let ⟨F, hF₁, hF₂⟩ := hC₁
      have : ⋂₀ ↑F ∈ cylinderSets ∨ ⋂₀ (↑F : Set (Set X)) = ∅ := by
        have hF : (↑F : Set (Set X)).Finite := by simp
        exact finite_intersections_of_cylinders_is_cylinder F hF₁ hF
      rw [←hF₂] at this
      exact this
    let A : Set (Set X) := {x | x ∈ C ∧ x ≠ ∅}
    use A
    apply And.intro
    . intro z hz
      unfold A at hz
      simp at hz
      specialize this z hz.1
      exact Or.resolve_right this hz.2
    . unfold A
      simp
      ext x
      constructor
      . rw [hC₂]
        intro hC
        let ⟨C', hxC, hxC'⟩ := Set.mem_sUnion.1 hC
        simp
        use C'
        apply And.intro _ hxC'
        have : C' ≠ ∅ := by
          have h_nonempty : C'.Nonempty := ⟨x, hxC'⟩
          exact (Set.nonempty_iff_ne_empty).1 h_nonempty
        exact ⟨hxC, this⟩
      . intro hx
        simp at hx
        let ⟨t, ht₁, ht₂⟩ := hx
        rw [hC₂]
        let ⟨ht, _⟩ := ht₁
        exact Set.mem_sUnion.2 ⟨t, ht, ht₂⟩

lemma cylinderCompact (a : Set X) (ha : a ∈ cylinderSets) : IsCompact a := by
  unfold IsCompact
  intro cover h_cover h_cover_sub
  -- Compact if for any "cover" filter of a (i.e. filter containing every superset of a),
  --   there exists a "cluster point" x ∈ a (i.e. any neighborhood of x intersects with
  --   the cover)
  simp [ClusterPt]
  unfold cylinderSets at ha
  simp at ha
  have ⟨s, f, hA⟩ := ha
  use f
  have : f ∈ a := by
    rw [hA]
    sorry
  apply And.intro this
  by_contra! H
  simp at H
  apply Filter.inf_eq_bot_iff.mp at H
  have ⟨U, hU, V, hV, hUV⟩ := H
  let ⟨T, hT, hT_open, hfT⟩ := mem_nhds_iff.mp hU
  sorry

def cylinderLocallyCompactSpace : LocallyCompactSpace X := {
  local_compact_nhds := by
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
}

instance : T2Space X := cylinderHausdorffSpace
instance : LocallyCompactSpace X := cylinderLocallyCompactSpace

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
