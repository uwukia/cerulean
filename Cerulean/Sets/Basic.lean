module

-- classical reasoning is necessary, basically to fulfill the DeMorgan laws
-- see for example, inter_compl
open Classical

-- inspired by the actual mathlib implementation

@[expose]
public def Set (α : Type) := α → Prop

public def Mem (s : Set α) (a : α) : Prop :=
  s a

public instance (α : Type) : Membership α (Set α) where
  mem := Mem

variable { α : Type }
variable { x : α }
variable { s s₁ s₂ s₃ : Set α }

public theorem mem_iff : x ∈ s ↔ s x := Iff.rfl

@[ext]
public theorem ext :  (∀ x : α, x ∈ s₁ ↔ x ∈ s₂) → s₁ = s₂ :=
  fun h => funext (fun x => propext (h x))

public theorem mem_left : s₁ = s₂ → x ∈ s₁ → x ∈ s₂ := by
  intro equals s1; rw [← equals]; assumption

public theorem mem_right : s₁ = s₂ → x ∈ s₂ → x ∈ s₁ := by
  intro equals s1; rw [equals]; assumption

/- ========================= EMPTY SET AND UNIVERSE ========================= -/

public def empty : Set α := fun _ => False

public def univ : Set α := fun _ => True

public instance (α : Type) : EmptyCollection (Set α) where
  emptyCollection := empty

@[simp]
public theorem empty_iff : (x ∈ (∅ : Set α)) = False :=
  propext Iff.rfl

@[simp]
public theorem univ_iff : (x ∈ univ) = True :=
  propext Iff.rfl

/- ================================ SUBSETS ================================= -/

-- the reason I went for `∀ {x : α}` instead of `∀ x : α` is because
-- then I can prove things like `subset_rfl` as simply `id` instead of
-- having to do `fun _ => id`
public instance (α : Type) : HasSubset (Set α) where
  Subset (s₁ s₂ : Set α) := ∀ {x : α}, x ∈ s₁ → x ∈ s₂

public theorem empty_subset (s : Set α) : ∅ ⊆ s := by
  intro _ _
  contradiction

public theorem subset_univ (s : Set α) : s ⊆ univ := by
  intro _ _
  trivial

public theorem subset_rfl (s : Set α) : s ⊆ s := id

public theorem subset_antisymm : s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂ := by
  intro s12 s21
  ext x
  exact Iff.intro s12 s21

public theorem subset_trans : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  fun s12 s23 _ x_in_s1 => (s23 ∘ s12) x_in_s1

public instance (α : Type) : HasSSubset (Set α) where
  SSubset (s₁ s₂ : Set α) := s₁ ⊆ s₂ ∧ s₁ ≠ s₂

public theorem ssubset_asymm : s₁ ⊂ s₂ → ¬ s₂ ⊂ s₁ := by
  intro s12 s21
  have neq : s₁ ≠ s₂ := s12.right
  have eq : s₁ = s₂ := subset_antisymm s12.left s21.left
  contradiction

/- ============================== BINARY UNION ============================== -/

public instance (α : Type) : Union (Set α) where
  union (s₁ s₂ : Set α) (x : α) := x ∈ s₁ ∨ x ∈ s₂

@[simp]
public theorem union_iff : (x ∈ s₁ ∪ s₂) = (x ∈ s₁ ∨ x ∈ s₂) :=
  propext Iff.rfl

public theorem union_comm (s₁ s₂ : Set α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
  have lemma (s₁ s₂ : Set α) : s₁ ∪ s₂ ⊆ s₂ ∪ s₁ := or_comm.mp
  subset_antisymm (lemma s₁ s₂) (lemma s₂ s₁)

public theorem subset_union_left (s₁ s₂ : Set α) : s₁ ⊆ s₁ ∪ s₂ := by
  intro x h; left; exact h

public theorem subset_union_right (s₁ s₂ : Set α) : s₂ ⊆ s₁ ∪ s₂ := by
  intro x h; right; exact h

public theorem subset_cup : s₁ ⊆ s₂ → s₁ ∪ s₂ = s₂ := by
  intro s1_subset_s2
  ext x
  simp
  exact s1_subset_s2

public theorem cup_subset : s₁ ⊆ s₂ → s₂ ∪ s₁ = s₂ := by
  rw [union_comm]
  exact subset_cup

public theorem empty_cup (s : Set α) : ∅ ∪ s = s :=
  subset_cup (empty_subset s)

public theorem cup_empty (s : Set α) : s ∪ ∅ = s :=
  cup_subset (empty_subset s)

public theorem univ_cup (s : Set α) : univ ∪ s = univ :=
  cup_subset (subset_univ s)

public theorem cup_univ (s : Set α) : s ∪ univ = univ :=
  subset_cup (subset_univ s)

public theorem union_assoc (s₁ s₂ s₃ : Set α)
  : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  ext x
  exact or_assoc

/- ========================== BINARY INTERSECTION =========================== -/

public instance (α : Type) : Inter (Set α) where
  inter (s₁ s₂ : Set α) (x : α) := x ∈ s₁ ∧ x ∈ s₂

@[simp]
public theorem inter_iff : (x ∈ s₁ ∩ s₂) = (x ∈ s₁ ∧ x ∈ s₂) :=
  propext Iff.rfl

public theorem inter_comm (s₁ s₂ : Set α) : s₁ ∩ s₂ = s₂ ∩ s₁ := by
  have lemma (s₁ s₂ : Set α) : s₁ ∩ s₂ ⊆ s₂ ∩ s₁ := fun h => ⟨h.right, h.left⟩
  exact subset_antisymm (lemma s₁ s₂) (lemma s₂ s₁)

public theorem subset_inter_left (s₁ s₂ : Set α) : s₁ ∩ s₂ ⊆ s₁ :=
  fun h => h.left

public theorem subset_inter_right (s₁ s₂ : Set α) : s₁ ∩ s₂ ⊆ s₂ :=
  fun h => h.right

public theorem subset_cap : s₁ ⊆ s₂ → s₁ ∩ s₂ = s₁ := by
  intro s1_subset_s2; ext x; simp; exact s1_subset_s2

public theorem cap_subset : s₁ ⊆ s₂ → s₂ ∩ s₁ = s₁ := by
  rw [inter_comm]; exact subset_cap

public theorem empty_cap (s : Set α) : ∅ ∩ s = ∅ := subset_cap (empty_subset s)

public theorem cap_empty (s : Set α) : s ∩ ∅ = ∅ := cap_subset (empty_subset s)

public theorem univ_cap (s : Set α) : univ ∩ s = s := cap_subset (subset_univ s)

public theorem cap_univ (s : Set α) : s ∩ univ = s := subset_cap (subset_univ s)

public theorem inter_assoc (s₁ s₂ s₃ : Set α)
  : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := by
  ext x
  exact and_assoc

@[simp]
public theorem inter_cup (s₁ s₂ s₃ : Set α)
  : (s₁ ∩ s₂) ∪ s₃ = (s₁ ∪ s₃) ∩ (s₂ ∪ s₃) := by
  ext x
  exact and_or_right

@[simp]
public theorem cup_inter (s₁ s₂ s₃ : Set α)
  : s₃ ∪ (s₁ ∩ s₂) = (s₃ ∪ s₁) ∩ (s₃ ∪ s₂) := by
  ext x
  exact or_and_left

@[simp]
public theorem union_cap (s₁ s₂ s₃ : Set α)
  : (s₁ ∪ s₂) ∩ s₃ = (s₁ ∩ s₃) ∪ (s₂ ∩ s₃) := by
  ext x
  exact or_and_right

@[simp]
public theorem cap_union (s₁ s₂ s₃ : Set α)
  : s₃ ∩ (s₁ ∪ s₂) = (s₃ ∩ s₁) ∪ (s₃ ∩ s₂):= by
  ext x
  exact and_or_left

/- ============================= SET DIFFERENCE ============================= -/

public instance (α : Type) : SDiff (Set α) where
  sdiff (s₁ s₂ : Set α) (x : α) := x ∈ s₁ ∧ x ∉ s₂

@[simp]
public theorem sdiff_iff : (x ∈ s₁ \ s₂) = (x ∈ s₁ ∧ x ∉ s₂) :=
  propext Iff.rfl

-- todo

/- ============================ SET CONSTRUCTION ============================ -/

-- x ∈ {p} iff x = p
public instance (α : Type) : Singleton α (Set α) where
  singleton (p : α) (x : α) := x = p

@[simp]
public theorem singleton_iff {p : α} : (x ∈ ({p} : Set α)) = (x = p) :=
  propext Iff.rfl

public instance (α : Type) : Insert α (Set α) where
  insert (x : α) (s : Set α) := {x} ∪ s

@[simp]
public theorem insert_iff {p : α} : (x ∈ insert p s) = (x = p ∨ x ∈ s) := by
  have by_rfl : (x ∈ insert p s) = (x ∈ {p} ∪ s) := propext Iff.rfl
  simp at by_rfl
  exact propext by_rfl

theorem lawful_singleton (p : α) : (insert p ∅ : Set α) = {p}
  := cup_empty {p}

instance (α : Type) : LawfulSingleton α (Set α) where
  insert_empty_eq := lawful_singleton

-- { a ∈ s | p a } (TODO: i can't get this to work)
-- instance (α : Type) : Sep α (Set α) where
-- sep (p : α → Prop) (s : Set α) := s ∩ p

/- ============================ ARBITRARY UNION ============================= -/

variable {S S₁ S₂ : Set (Set α)}

public def sUnion (S : Set (Set α)) : Set α :=
  fun x : α => ∃ s ∈ S, x ∈ s

prefix:110 "⋃₀ " => sUnion

@[simp]
public theorem sunion_iff : (x ∈ ⋃₀ S) = (∃ s ∈ S, x ∈ s) := propext Iff.rfl

theorem two_union : ⋃₀ {s₁, s₂} = s₁ ∪ s₂ := by ext x; simp

/- ========================= ARBITRARY INTERSECTION ========================= -/

public def sInter (S : Set (Set α)) : Set α :=
  fun x : α => ∀ s ∈ S, x ∈ s

prefix:110 "⋂₀ " => sInter

@[simp]
public theorem sinter_iff : (x ∈ ⋂₀ S) = (∀ s ∈ S, x ∈ s) := propext Iff.rfl

theorem two_inter : ⋂₀ {s₁, s₂} = s₁ ∩ s₂ := by ext x; simp

/- =============================== COMPLEMENT =============================== -/

public def compl (s : Set α) : Set α := univ \ s

postfix:1024 "ᶜ" => compl

@[simp]
public theorem compl_iff : (x ∈ sᶜ) = (x ∉ s) := by
  unfold compl
  simp

@[simp]
public theorem compl_compl (s : Set α) : (sᶜ)ᶜ = s := by
  unfold compl
  ext x
  simp

@[simp]
public theorem union_compl : (s₁ ∪ s₂)ᶜ = s₁ᶜ ∩ s₂ᶜ := by
  ext x
  simp

@[simp]
public theorem inter_compl : (s₁ ∩ s₂)ᶜ = s₁ᶜ ∪ s₂ᶜ := by
  ext x
  simp
  constructor
  intro h
  cases em (x ∈ s₁)
  case _ in_s1 => right; exact h in_s1
  case _ not_in_s1 => left; assumption
  intro h
  exact h.neg_resolve_left

@[simp]
public theorem subset_compl : (s₁ᶜ ⊆ s₂ᶜ) = (s₂ ⊆ s₁) :=
  have lemma₁ {s₁ s₂ : Set α} : s₂ ⊆ s₁ → s₁ᶜ ⊆ s₂ᶜ := by
    intro h x
    simp
    intro x_notin_s1 x_in_s2
    have yet : x ∈ s₁ := h x_in_s2
    contradiction
  have lemma₂ {s₁ s₂ : Set α} : s₁ᶜ ⊆ s₂ᶜ → s₂ ⊆ s₁ := by
    have tauto : s₂ᶜᶜ ⊆ s₁ᶜᶜ → s₂ ⊆ s₁ := by
      rw [compl_compl, compl_compl]; exact id
    have by_above : s₁ᶜ ⊆ s₂ᶜ → s₂ᶜᶜ ⊆ s₁ᶜᶜ := lemma₁
    exact tauto ∘ by_above
  propext (Iff.intro lemma₂ lemma₁)

/- =============================== POWER SET ================================ -/

public def powerset (s : Set α) : Set (Set α) := fun t : Set α => t ⊆ s

prefix:100 "𝒫 " => powerset

@[simp]
public theorem powerset_iff {t : Set α} : (s ∈ 𝒫 t) = (s ⊆ t) := by
  rfl

public theorem powerset_empty : 𝒫 (∅ : Set α) = {∅} := by
  ext s
  simp
  constructor
  intro h; exact subset_antisymm h (empty_subset s)
  intro h; rw [h]; exact subset_rfl ∅

public theorem powerset_univ : (𝒫 (univ : Set α)) = (univ : Set (Set α)) := by
  ext s
  simp
  exact subset_univ s

/- ================================ SUBTYPES ================================ -/

-- this is a little magical to me, honestly
public instance : CoeSort (Set α) Type := ⟨fun s => { x // x ∈ s }⟩

public def restrict (f : α → β) (s : Set α) : s → β := fun x => f x

infix:85 " ↾ " => restrict
