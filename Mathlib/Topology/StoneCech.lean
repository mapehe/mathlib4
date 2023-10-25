/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.UrysohnsLemma

#align_import topology.stone_cech from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

Parts of the formalization are based on "Ultrafilters and Topology"
by Marius Stekelenburg, particularly section 5.
-/


noncomputable section

open Filter Set

open Topology

universe u v

section Ultrafilter

/- The set of ultrafilters on α carries a natural topology which makes
  it the Stone-Čech compactification of α (viewed as a discrete space). -/
/-- Basis for the topology on `Ultrafilter α`. -/
def ultrafilterBasis (α : Type u) : Set (Set (Ultrafilter α)) :=
  range fun s : Set α => { u | s ∈ u }
#align ultrafilter_basis ultrafilterBasis

variable {α : Type u}

instance Ultrafilter.topologicalSpace : TopologicalSpace (Ultrafilter α) :=
  TopologicalSpace.generateFrom (ultrafilterBasis α)
#align ultrafilter.topological_space Ultrafilter.topologicalSpace

theorem ultrafilterBasis_is_basis : TopologicalSpace.IsTopologicalBasis (ultrafilterBasis α) :=
  ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine' ⟨_, ⟨a ∩ b, rfl⟩, inter_mem ua ub, fun v hv => ⟨_, _⟩⟩ <;> apply mem_of_superset hv <;>
      simp [inter_subset_right a b],
    eq_univ_of_univ_subset <| subset_sUnion_of_mem <| ⟨univ, eq_univ_of_forall fun u => univ_mem⟩,
    rfl⟩
#align ultrafilter_basis_is_basis ultrafilterBasis_is_basis

/-- The basic open sets for the topology on ultrafilters are open. -/
theorem ultrafilter_isOpen_basic (s : Set α) : IsOpen { u : Ultrafilter α | s ∈ u } :=
  ultrafilterBasis_is_basis.isOpen ⟨s, rfl⟩
#align ultrafilter_is_open_basic ultrafilter_isOpen_basic

/-- The basic open sets for the topology on ultrafilters are also closed. -/
theorem ultrafilter_isClosed_basic (s : Set α) : IsClosed { u : Ultrafilter α | s ∈ u } := by
  rw [← isOpen_compl_iff]
  convert ultrafilter_isOpen_basic sᶜ using 1
  ext u
  exact Ultrafilter.compl_mem_iff_not_mem.symm
#align ultrafilter_is_closed_basic ultrafilter_isClosed_basic

/-- Every ultrafilter `u` on `Ultrafilter α` converges to a unique
  point of `Ultrafilter α`, namely `joinM u`. -/
theorem ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α} :
    ↑u ≤ 𝓝 x ↔ x = joinM u := by
  rw [eq_comm, ← Ultrafilter.coe_le_coe]
  change ↑u ≤ 𝓝 x ↔ ∀ s ∈ x, { v : Ultrafilter α | s ∈ v } ∈ u
  simp only [TopologicalSpace.nhds_generateFrom, le_iInf_iff, ultrafilterBasis, le_principal_iff,
    mem_setOf_eq]
  constructor
  · intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  · rintro h a ⟨xi, a, rfl⟩
    exact h _ xi
#align ultrafilter_converges_iff ultrafilter_converges_iff

instance ultrafilter_compact : CompactSpace (Ultrafilter α) :=
  ⟨isCompact_iff_ultrafilter_le_nhds.mpr fun f _ =>
      ⟨joinM f, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩
#align ultrafilter_compact ultrafilter_compact

instance Ultrafilter.t2Space : T2Space (Ultrafilter α) :=
  t2_iff_ultrafilter.mpr @fun x y f fx fy =>
    have hx : x = joinM f := ultrafilter_converges_iff.mp fx
    have hy : y = joinM f := ultrafilter_converges_iff.mp fy
    hx.trans hy.symm
#align ultrafilter.t2_space Ultrafilter.t2Space

instance : TotallyDisconnectedSpace (Ultrafilter α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro A
  simp only [Set.eq_singleton_iff_unique_mem, mem_connectedComponent, true_and_iff]
  intro B hB
  rw [← Ultrafilter.coe_le_coe]
  intro s hs
  rw [connectedComponent_eq_iInter_clopen, Set.mem_iInter] at hB
  let Z := { F : Ultrafilter α | s ∈ F }
  have hZ : IsClopen Z := ⟨ultrafilter_isOpen_basic s, ultrafilter_isClosed_basic s⟩
  exact hB ⟨Z, hZ, hs⟩

@[simp] theorem Ultrafilter.tendsto_pure_self (b : Ultrafilter α) : Tendsto pure b (𝓝 b) := by
  rw [Tendsto, ← coe_map, ultrafilter_converges_iff]
  ext s
  change s ∈ b ↔ {t | s ∈ t} ∈ map pure b
  simp_rw [mem_map, preimage_setOf_eq, mem_pure, setOf_mem_eq]

theorem ultrafilter_comap_pure_nhds (b : Ultrafilter α) : comap pure (𝓝 b) ≤ b := by
  rw [TopologicalSpace.nhds_generateFrom]
  simp only [comap_iInf, comap_principal]
  intro s hs
  rw [← le_principal_iff]
  refine' iInf_le_of_le { u | s ∈ u } _
  refine' iInf_le_of_le ⟨hs, ⟨s, rfl⟩⟩ _
  exact principal_mono.2 fun a => id
#align ultrafilter_comap_pure_nhds ultrafilter_comap_pure_nhds

section Embedding

theorem ultrafilter_pure_injective : Function.Injective (pure : α → Ultrafilter α) := by
  intro x y h
  have : {x} ∈ (pure x : Ultrafilter α) := singleton_mem_pure
  rw [h] at this
  exact (mem_singleton_iff.mp (mem_pure.mp this)).symm
#align ultrafilter_pure_injective ultrafilter_pure_injective

open TopologicalSpace

/-- The range of `pure : α → Ultrafilter α` is dense in `Ultrafilter α`. -/
theorem denseRange_pure : DenseRange (pure : α → Ultrafilter α) := fun x =>
  mem_closure_iff_ultrafilter.mpr
    ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pure x).symm⟩
#align dense_range_pure denseRange_pure

/-- The map `pure : α → Ultrafilter α` induces on `α` the discrete topology. -/
theorem induced_topology_pure :
    TopologicalSpace.induced (pure : α → Ultrafilter α) Ultrafilter.topologicalSpace = ⊥ := by
  apply eq_bot_of_singletons_open
  intro x
  use { u : Ultrafilter α | {x} ∈ u }, ultrafilter_isOpen_basic _
  simp
#align induced_topology_pure induced_topology_pure

/-- `pure : α → Ultrafilter α` defines a dense inducing of `α` in `Ultrafilter α`. -/
theorem denseInducing_pure : @DenseInducing _ _ ⊥ _ (pure : α → Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  ⟨⟨induced_topology_pure.symm⟩, denseRange_pure⟩
#align dense_inducing_pure denseInducing_pure

-- The following refined version will never be used
/-- `pure : α → Ultrafilter α` defines a dense embedding of `α` in `Ultrafilter α`. -/
theorem denseEmbedding_pure : @DenseEmbedding _ _ ⊥ _ (pure : α → Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  { denseInducing_pure with inj := ultrafilter_pure_injective }
#align dense_embedding_pure denseEmbedding_pure

end Embedding

section Extension

/- Goal: Any function `α → γ` to a compact Hausdorff space `γ` has a
  unique extension to a continuous function `Ultrafilter α → γ`. We
  already know it must be unique because `α → Ultrafilter α` is a
  dense embedding and `γ` is Hausdorff. For existence, we will invoke
  `DenseInducing.continuous_extend`. -/
variable {γ : Type*} [TopologicalSpace γ]

/-- The extension of a function `α → γ` to a function `Ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
def Ultrafilter.extend (f : α → γ) : Ultrafilter α → γ :=
  letI : TopologicalSpace α := ⊥
  denseInducing_pure.extend f
#align ultrafilter.extend Ultrafilter.extend

variable [T2Space γ]

theorem ultrafilter_extend_extends (f : α → γ) : Ultrafilter.extend f ∘ pure = f := by
  letI : TopologicalSpace α := ⊥
  haveI : DiscreteTopology α := ⟨rfl⟩
  exact funext (denseInducing_pure.extend_eq continuous_of_discreteTopology)
#align ultrafilter_extend_extends ultrafilter_extend_extends

variable [CompactSpace γ]

theorem continuous_ultrafilter_extend (f : α → γ) : Continuous (Ultrafilter.extend f) := by
  have h : ∀ b : Ultrafilter α, ∃ c, Tendsto f (comap pure (𝓝 b)) (𝓝 c) := fun b =>
    -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
    let ⟨c, _, h'⟩ :=
      isCompact_univ.ultrafilter_le_nhds (b.map f) (by rw [le_principal_iff]; exact univ_mem)
    ⟨c, le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h'⟩
  letI : TopologicalSpace α := ⊥
  exact denseInducing_pure.continuous_extend h
#align continuous_ultrafilter_extend continuous_ultrafilter_extend

/-- The value of `Ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
theorem ultrafilter_extend_eq_iff {f : α → γ} {b : Ultrafilter α} {c : γ} :
    Ultrafilter.extend f b = c ↔ ↑(b.map f) ≤ 𝓝 c :=
  ⟨fun h => by
    -- Write b as an ultrafilter limit of pure ultrafilters, and use
    -- the facts that ultrafilter.extend is a continuous extension of f.
    let b' : Ultrafilter (Ultrafilter α) := b.map pure
    have t : ↑b' ≤ 𝓝 b := ultrafilter_converges_iff.mpr (bind_pure _).symm
    rw [← h]
    have := (continuous_ultrafilter_extend f).tendsto b
    refine' le_trans _ (le_trans (map_mono t) this)
    change _ ≤ map (Ultrafilter.extend f ∘ pure) ↑b
    rw [ultrafilter_extend_extends]
    exact le_rfl, fun h =>
    letI : TopologicalSpace α := ⊥
    denseInducing_pure.extend_eq_of_tendsto
      (le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h)⟩
#align ultrafilter_extend_eq_iff ultrafilter_extend_eq_iff

end Extension

end Ultrafilter

section StoneCech

/- Now, we start with a (not necessarily discrete) topological space α
  and we want to construct its Stone-Čech compactification. We can
  build it as a quotient of `Ultrafilter α` by the relation which
  identifies two points if the extension of every continuous function
  α → γ to a compact Hausdorff space sends the two points to the same
  point of γ. -/
variable (α : Type u) [TopologicalSpace α]

instance stoneCechSetoid : Setoid (Ultrafilter α)
    where
  r x y :=
    ∀ (γ : Type u) [TopologicalSpace γ],
      ∀ [T2Space γ] [CompactSpace γ] (f : α → γ) (_ : Continuous f),
        Ultrafilter.extend f x = Ultrafilter.extend f y
  iseqv :=
    ⟨fun _ _ _ _ _ _ _ => rfl, @fun _ _ xy γ _ _ _ f hf => (xy γ f hf).symm,
      @fun _ _ _ xy yz γ _ _ _ f hf => (xy γ f hf).trans (yz γ f hf)⟩
#align stone_cech_setoid stoneCechSetoid

/-- The Stone-Čech compactification of a topological space. -/
def StoneCech : Type u :=
  Quotient (stoneCechSetoid α)
#align stone_cech StoneCech

variable {α}

instance : TopologicalSpace (StoneCech α) := by unfold StoneCech; infer_instance

instance [Inhabited α] : Inhabited (StoneCech α) := by unfold StoneCech; infer_instance

/-- The natural map from α to its Stone-Čech compactification. -/
def stoneCechUnit (x : α) : StoneCech α :=
  ⟦pure x⟧
#align stone_cech_unit stoneCechUnit

/-- The image of stone_cech_unit is dense. (But stone_cech_unit need
  not be an embedding, for example if α is not Hausdorff.) -/
theorem denseRange_stoneCechUnit : DenseRange (stoneCechUnit : α → StoneCech α) :=
  denseRange_pure.quotient
#align dense_range_stone_cech_unit denseRange_stoneCechUnit
variable {γ : Type u} [TopologicalSpace γ] [T2Space γ] [CompactSpace γ]

class CompletelyRegularSpace (α : Type u) [TopologicalSpace α] [T1Space α] : Prop where
  completely_regular :
  ∀ (x : α), ∀ (K : Set α) (_: IsClosed K), Disjoint K {x} →
    ∃ (f : C(α, ℝ)), EqOn f 0 {x} ∧ EqOn f 1 K ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1

lemma sep [TopologicalSpace α] [T1Space α] [CompletelyRegularSpace α] :
    ∀ (x y : α), x ≠ y →
    ∃ (Z : Type u)
    (_ : TopologicalSpace Z) (_ : T2Space Z) (_ : CompactSpace Z),
    ∃ (f : C(α, Z)), f x ≠ f y := by
  intros x y hxy
  have cx : IsClosed {x} := by apply T1Space.t1
  have cy : Disjoint {x} ({y} : Set α) := by
    rw [disjoint_singleton_left, mem_singleton_iff]
    exact hxy
  let ⟨f, hfy, hfx, hficc⟩ := CompletelyRegularSpace.completely_regular y {x} cx cy
  let Z := ULift.{u} <| Set.Icc (0 : ℝ) 1
  have A1 : CompactSpace Z := Homeomorph.ulift.symm.compactSpace
  have : T2Space Z := Homeomorph.ulift.symm.t2Space
  let g : α → Z := fun y' => ⟨f y', hficc y'⟩
  have hg : Continuous g := continuous_uLift_up.comp (f.2.subtype_mk hficc)
  have A2: T2Space Z := Homeomorph.ulift.symm.t2Space
  have O : g x ≠ g y := by
    have P3 : f y = 0 := by
      apply hfy
      rw [mem_singleton_iff]
    have P4 : f x = 1 := by
      apply hfx
      rw [mem_singleton_iff]
    simp only [ne_eq, ULift.up_inj, Subtype.mk.injEq]
    rw [P3, P4]
    exact one_ne_zero
  exact ⟨Z, ULift.topologicalSpace, A2, A1, ⟨g, hg⟩, O⟩

lemma eq_if_stoneCechUnit_eq {a b : α} {γ : Type u} [TopologicalSpace γ] [T2Space γ]
    [CompactSpace γ] : stoneCechUnit a = stoneCechUnit b
    → ∀ (f : α → γ), Continuous f → f a = f b := by
  intros h f hf
  have asd : Ultrafilter.extend f (pure a) =  Ultrafilter.extend f (pure b)
      → f a = f b := by
    have K : ∀ (a : α), Ultrafilter.extend f (pure a) = f a := by
      letI : TopologicalSpace α := ⊥
      haveI : DiscreteTopology α := ⟨rfl⟩
      exact let_fun O := continuous_of_discreteTopology;
        DenseInducing.extend_eq denseInducing_pure O
    intro h
    have G : Ultrafilter.extend f (pure a) = f a := by apply K a
    have G2 : Ultrafilter.extend f (pure b) = f b := by apply K b
    rw [←G, ←G2]
    exact h
  have U : (stoneCechSetoid α).1 (pure a) (pure b) := by
    have U: Quotient.mk (stoneCechSetoid α) (pure a) =
      Quotient.mk (stoneCechSetoid α) (pure b) → (stoneCechSetoid α).1 (pure a)
        (pure b):= by
      rw [Quotient.eq]
      exact fun rel γ [TopologicalSpace γ] [T2Space γ] [CompactSpace γ] f ↦ rel γ f
    exact U h
  exact asd (U γ f hf)

lemma injective_stoneCechUnit [TopologicalSpace α] [T1Space α] [CompletelyRegularSpace α] :
    Function.Injective (stoneCechUnit : α → StoneCech α) := by
  intros a b hab
  have O : ∀ (Z : Type u)
  (_ : TopologicalSpace Z) (_ : T2Space Z) (_ : CompactSpace Z),
  ∀ (f : C(α, Z)), f a = f b := by
    intros h _ _ _ f
    apply eq_if_stoneCechUnit_eq
    exact hab
    exact f.2
  contrapose O
  simp only [not_forall, exists_and_left]
  exact sep a b O


section Extension

variable {γ : Type u} [TopologicalSpace γ] [T2Space γ] [CompactSpace γ]

variable {γ' : Type u} [TopologicalSpace γ'] [T2Space γ']

variable {f : α → γ} (hf : Continuous f)

-- Porting note: missing attribute
--attribute [local elab_with_expected_type] Quotient.lift

/-- The extension of a continuous function from α to a compact
  Hausdorff space γ to the Stone-Čech compactification of α. -/
def stoneCechExtend : StoneCech α → γ :=
  Quotient.lift (Ultrafilter.extend f) fun _ _ xy => xy γ f hf
#align stone_cech_extend stoneCechExtend

theorem stoneCechExtend_extends : stoneCechExtend hf ∘ stoneCechUnit = f :=
  ultrafilter_extend_extends f
#align stone_cech_extend_extends stoneCechExtend_extends

theorem continuous_stoneCechExtend : Continuous (stoneCechExtend hf) :=
  continuous_quot_lift _ (continuous_ultrafilter_extend f)
#align continuous_stone_cech_extend continuous_stoneCechExtend

theorem stoneCech_hom_ext {g₁ g₂ : StoneCech α → γ'} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ stoneCechUnit = g₂ ∘ stoneCechUnit) : g₁ = g₂ := by
  apply Continuous.ext_on denseRange_stoneCechUnit h₁ h₂
  rintro x ⟨x, rfl⟩
  apply congr_fun h x
#align stone_cech_hom_ext stoneCech_hom_ext

end Extension

theorem convergent_eqv_pure {u : Ultrafilter α} {x : α} (ux : ↑u ≤ 𝓝 x) : u ≈ pure x :=
  fun γ tγ h₁ h₂ f hf => by
  skip
  trans f x; swap; symm
  all_goals refine' ultrafilter_extend_eq_iff.mpr (le_trans (map_mono _) (hf.tendsto _))
  · apply pure_le_nhds
  · exact ux
#align convergent_eqv_pure convergent_eqv_pure

theorem continuous_stoneCechUnit : Continuous (stoneCechUnit : α → StoneCech α) :=
  continuous_iff_ultrafilter.mpr fun x g gx => by
    have : (g.map pure).toFilter ≤ 𝓝 g := by
      rw [ultrafilter_converges_iff]
      exact (bind_pure _).symm
    have : (g.map stoneCechUnit : Filter (StoneCech α)) ≤ 𝓝 ⟦g⟧ :=
      continuousAt_iff_ultrafilter.mp (continuous_quotient_mk'.tendsto g) _ this
    rwa [show ⟦g⟧ = ⟦pure x⟧ from Quotient.sound <| convergent_eqv_pure gx] at this
#align continuous_stone_cech_unit continuous_stoneCechUnit

theorem open_stoneCechUnit [TopologicalSpace α] [T1Space α] [CompletelyRegularSpace α]
    : ∀ (s : Set α), IsOpen s → ∃ (t : Set (StoneCech α)), IsOpen t ∧
      stoneCechUnit '' s ⊆ t ∧ stoneCechUnit ⁻¹' t = s := by
    intros s hs
    have H : ∀ (x : StoneCech α), ∃ (U : Set (StoneCech α)),
      IsOpen U ∧ stoneCechUnit ⁻¹' (U) ⊆ s ∧ {x} ∩ (stoneCechUnit '' s) ⊆ U := by
        intro x
        have hx : (x ∈ stoneCechUnit '' s) ∨ (x ∉ stoneCechUnit '' s) := by apply or_not
        cases hx
        have A : ∃ (a : α), a ∈ s ∧ stoneCechUnit a = x := by
          have B : x ∈ stoneCechUnit '' s := by assumption
          rw [mem_image] at B
          let b := B.choose
          let hb := B.choose_spec
          use b
        let a := A.choose
        let ⟨ha, _⟩ := A.choose_spec
        let K := sᶜ
        have Kc : IsClosed K := by
          rw [isClosed_compl_iff]
          exact hs
        have Kd : Disjoint K {a} := by
          simp
          exact ha
        let fact := CompletelyRegularSpace.completely_regular a K Kc Kd
        let f := fact.choose
        let ⟨hf, hhf, hhhf⟩ := fact.choose_spec
        let Z := ULift.{u} <| Set.Icc (0 : ℝ) 1
        have hZ : CompactSpace Z := Homeomorph.ulift.symm.compactSpace
        have : T2Space Z := Homeomorph.ulift.symm.t2Space
        let g : α → Z := fun y' => ⟨f y', hhhf y'⟩
        have hg : Continuous g := continuous_uLift_up.comp (f.2.subtype_mk hhhf)
        have hhZ: T2Space Z := Homeomorph.ulift.symm.t2Space
        let z1 : Z := ⟨0, by simp⟩
        let z2 : Z := ⟨1, by simp⟩
        have hz12 : z1 ≠ z2 := by simp
        let ⟨u, v, hu, _, hhu, hhv, huv⟩ := T2Space.t2 z1 z2 hz12
        let φ := stoneCechExtend hg
        use φ ⁻¹' u
        have P2 : (g ⁻¹' v) ∩ (g ⁻¹' u) = ∅ := by
          rw [←preimage_inter]
          have D : v ∩ u = ∅ := by
            rw [disjoint_iff] at huv
            have B : u ⊓ v = ⊥ → v ∩ u = ∅ := by
              exact
                id
                  (let_fun refl := inter_comm u v;
                  fun h ↦ Eq.mpr (id (refl.symm ▸ Eq.refl (v ∩ u = ∅))) h)
            apply B
            exact huv
          rw [D]
          apply preimage_empty
        have fact1 := IsOpen.preimage (continuous_stoneCechExtend hg) hu
        have fact2 : stoneCechUnit ⁻¹' (φ ⁻¹' u) ⊆ s := by
          rw [←preimage_comp]
          have P : φ ∘ stoneCechUnit = g := by apply stoneCechExtend_extends
          rw [P]
          have C1 : sᶜ ⊆  g ⁻¹' v := by
            intro a ha
            rw [mem_preimage]
            have val : g a = z2 := by
              simp only [eqOn_singleton, Pi.zero_apply, ge_iff_le, zero_le_one, not_true, gt_iff_lt,
                mem_Icc, ULift.up_inj, Subtype.mk.injEq]
              let p := hhf ha
              simp at p
              exact p
            rw [val]
            exact hhv
          have C2 : g ⁻¹' u ∩ sᶜ = ∅ := by
            have W : g ⁻¹' u ∩ g ⁻¹' v = ∅ → g ⁻¹' u ∩ sᶜ = ∅ := by
              intro h
              replace C1 := (inter_subset_inter_right (g ⁻¹' u) C1)
              rw [h] at C1
              rw [subset_empty_iff] at C1
              exact C1
            apply W
            rw [inter_comm] at P2
            exact P2
          contrapose C2
          have R : (g ⁻¹' u ∩ sᶜ).Nonempty → ¬g ⁻¹' u ∩ sᶜ = ∅ := by
            rw [←not_nonempty_iff_eq_empty]
            rw [not_not]
            exact fun h ↦ h
          apply R
          rw [inter_compl_nonempty_iff]
          exact C2
        have fact3 : {x} ∩ stoneCechUnit '' s ⊆ φ ⁻¹' u := by
          let ⟨_, ha⟩ := A.choose_spec
          rw [←ha, ←image_singleton, ←image_inter injective_stoneCechUnit]
          rw [image_subset_iff, ←preimage_comp]
          have P : φ ∘ stoneCechUnit = g := by apply stoneCechExtend_extends
          rw [P]
          intro b hb
          rw [mem_inter_iff] at hb
          let ⟨hhb, _⟩ := hb
          rw [mem_preimage]
          have P : g b = z1 := by
            simp
            let p := hf hhb
            simp at p
            exact p
          rw [P]
          exact hhu
        exact ⟨fact1, fact2, fact3⟩
        use ∅
        have e : {x} ∩ stoneCechUnit '' s = ∅ := by
          rw [singleton_inter_eq_empty]
          assumption
        have e2 : {x} ∩ stoneCechUnit '' s ⊆ ∅ := by
          rw [subset_empty_iff]
          exact e
        exact ⟨isOpen_empty, by simp, e2⟩
    let F := fun (x : StoneCech α) => (H x).choose
    have hf : ∀ (x : StoneCech α), IsOpen (F x) := by
      intro x
      let ⟨o, _⟩ := (H x).choose_spec
      exact o
    have O : IsOpen (⋃ i, (F i)) := by apply isOpen_iUnion hf
    have sf : ∀ (x : StoneCech α), x ∈ stoneCechUnit '' s → x ∈ (F x) := by
      intro x hx
      let ⟨_, _, inc⟩ := (H x).choose_spec
      have L : {x} ∩ stoneCechUnit '' s = {x} := by
        simp only [mem_image] at hx
        simp only [inter_eq_left, singleton_subset_iff, mem_image]
        exact hx
      rw [←singleton_subset_iff, ←L]
      exact inc
    have ssub : stoneCechUnit '' s ⊆ (⋃ i, (F i)) := by
      intro x hx
      specialize sf x hx
      rw [mem_iUnion]
      use x
    have J : s ⊆ stoneCechUnit ⁻¹' (⋃ i, (F i)) := by
      intro a ha
      let ⟨_, _, sub2⟩ := (H (stoneCechUnit a)).choose_spec
      rw [←singleton_subset_iff]
      rw [←singleton_subset_iff] at ha
      rw [←image_subset_image_iff injective_stoneCechUnit]
      simp
      use a
      apply And.intro
      use stoneCechUnit a
      rw [←singleton_subset_iff]
      have Q2 : {stoneCechUnit a} ⊆ {stoneCechUnit a} ∩ stoneCechUnit '' s := by
        simp
        use a
        simp
        rw [singleton_subset_iff] at ha
        exact ha
      apply Subset.trans Q2 sub2
      rfl
    have P : stoneCechUnit ⁻¹' (⋃ i, (F i)) = s := by
      have P2 : stoneCechUnit ⁻¹' ⋃ i, F i ⊆ s := by
        simp
        intro x
        let ⟨_, sub, _⟩ := (H x).choose_spec
        exact sub
      exact Subset.antisymm P2 J
    use (⋃ i, (F i))

theorem inducing_stoneCechUnit [TopologicalSpace α] [T1Space α] [CompletelyRegularSpace α]
    : Inducing (stoneCechUnit : α → StoneCech α) := by
    rw [inducing_iff_nhds]
    intro a
    ext x
    rw [mem_comap]
    apply Iff.intro
    intro hx
    rw [mem_nhds_iff] at hx
    let ⟨s, sx, so, mem⟩ := hx
    let ⟨t, ⟨ot, ct, st⟩⟩ := open_stoneCechUnit s so
    use t
    have Q : stoneCechUnit ⁻¹' t ⊆ x := by
      rw [st]
      exact sx
    have Q2 : t ∈ 𝓝 (stoneCechUnit a) := by
      rw [mem_nhds_iff]
      use t
      have S : t ⊆ t := by apply Subset.refl
      have S2 : stoneCechUnit a ∈ t := by
        exact
          let_fun mem := mem_image_of_mem stoneCechUnit mem;
          let_fun mem := mem_of_subset_of_mem ct mem;
          mem
      exact ⟨S, ot, S2⟩
    exact ⟨Q2, Q⟩
    intro ⟨t, ⟨ht, ht2⟩⟩
    have T : stoneCechUnit ⁻¹' t ∈ (𝓝 a)  := by
      rw [mem_nhds_iff]
      rw [mem_nhds_iff] at ht
      let ⟨s, st, so, mem⟩ := ht
      use (stoneCechUnit ⁻¹' s)
      rw [mem_preimage]
      have O : IsOpen (stoneCechUnit ⁻¹' s) := by
        apply IsOpen.preimage
        exact continuous_stoneCechUnit
        exact so
      have Q : stoneCechUnit ⁻¹' s ⊆ stoneCechUnit ⁻¹' t := by
        apply preimage_mono
        exact st
      exact ⟨Q, O, mem⟩
    replace ht2 := sets_of_superset (𝓝 a) T ht2
    exact ht2

theorem denseInducing_stoneCechUnit [TopologicalSpace α] [T1Space α] [CompletelyRegularSpace α] :
  @DenseInducing _ _ _ _ (stoneCechUnit : α → StoneCech α) :=
  ⟨inducing_stoneCechUnit, denseRange_stoneCechUnit⟩

theorem denseEmbedding_stoneCechUnit [TopologicalSpace α] [T1Space α] [CompletelyRegularSpace α] :
    @DenseEmbedding _ _ _ _ (stoneCechUnit : α → StoneCech α) :=
  { denseInducing_stoneCechUnit with inj := injective_stoneCechUnit }

instance StoneCech.t2Space : T2Space (StoneCech α) := by
  rw [t2_iff_ultrafilter]
  rintro ⟨x⟩ ⟨y⟩ g gx gy
  apply Quotient.sound
  intro γ tγ h₁ h₂ f hf
  skip
  let ff := stoneCechExtend hf
  change ff ⟦x⟧ = ff ⟦y⟧
  have lim := fun (z : Ultrafilter α) (gz : (g : Filter (StoneCech α)) ≤ 𝓝 ⟦z⟧) =>
    ((continuous_stoneCechExtend hf).tendsto _).mono_left gz
  exact tendsto_nhds_unique (lim x gx) (lim y gy)
#align stone_cech.t2_space StoneCech.t2Space

instance StoneCech.compactSpace : CompactSpace (StoneCech α) :=
  Quotient.compactSpace
#align stone_cech.compact_space StoneCech.compactSpace

end StoneCech
