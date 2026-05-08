module

public import Cerulean.Sets.Basic

variable { α β ι : Type }
variable { x : α }
variable { y : β }
variable { s : Set α }
variable { t : Set β }
variable { S : Set (Set α) }
variable { f : α → β }
variable { X X₁ X₂ : ι → Set α }
variable { Y : ι → Set β }

public def image (f : α → β) (s : Set α) : Set β :=
  fun y : β => ∃ x ∈ s, f x = y

public def preimage (f : α → β) (s : Set β) : Set α :=
  fun x : α => f x ∈ s

infixr:80 " '' " => image

infixr:80 " ⁻¹' " => preimage

public def range (f : α → β) : Set β := f '' univ

@[simp]
theorem image_iff : (y ∈ f '' s) = (∃ x ∈ s, f x = y) := by
  unfold image
  simp
  rw [mem_iff]

@[simp]
theorem preimage_iff : (x ∈ f ⁻¹' t) = (f x ∈ t) := by
  unfold preimage
  simp
  rw [mem_iff]

@[simp]
theorem range_iff : (y ∈ range f) = (∃ x : α, f x = y) := by
  unfold range
  simp

/- ======================== UNIONS AND INTERSECTIONS ======================== -/

public def iUnion (X : ι → Set α) := ⋃₀ range X

public def iInter (X : ι → Set α) := ⋂₀ range X

@[simp]
theorem iunion_iff : (x ∈ iUnion X) = (x ∈ ⋃₀ (range X)) := rfl

@[simp]
theorem iinter_iff : (x ∈ iInter X) = (x ∈ ⋂₀ (range X)) := rfl

macro:max "⋃" x:ident " : " s:term ", " t:term : term =>
  `(iUnion (fun $x : $s => $t))

macro:max "⋂" x:ident " : " s:term ", " t:term : term =>
  `(iInter (fun $x : $s => $t))

@[simp]
public theorem iunion_compl : (⋃ i : ι, X i)ᶜ = ⋂ i : ι, (X i)ᶜ := by
  ext x
  simp

theorem iinter_lemma₁ : (⋂ i : ι, X i)ᶜ ⊆ ⋃ i : ι, (X i)ᶜ := by
  intro x
  simp
  intro i x_notin_xi
  exists (X i)ᶜ
  constructor
  exists i
  simp
  assumption

theorem iinter_lemma₂ : (⋂ i : ι, X i)ᶜ ⊇ ⋃ i : ι, (X i)ᶜ := by
  intro x
  simp
  intro i x_notin_xi
  exists i

@[simp]
public theorem iinter_compl : (⋂ i : ι, X i)ᶜ = ⋃ i : ι, (X i)ᶜ :=
  subset_antisymm iinter_lemma₁ iinter_lemma₂

public theorem sunion_as_iunion : ⋃₀ S = ⋃ x : S, x := by ext t; simp

public theorem sinter_as_iinter : ⋂₀ S = ⋂ x : S, x := by ext t; simp

@[simp]
public theorem sunion_compl : (⋃₀ S)ᶜ = ⋂ x : S, xᶜ := by
  rw [sunion_as_iunion]
  simp

@[simp]
public theorem sinter_compl : (⋂₀ S)ᶜ = ⋃ x : S, xᶜ := by
  rw [sinter_as_iinter]
  simp

public theorem subset_iunion : (∃ i : ι, s ⊆ X i) → s ⊆ ⋃ i : ι, X i := by
  intro h x x_in_s
  obtain ⟨i, hi⟩ := h
  simp
  exists X i
  constructor
  exists i
  apply hi
  assumption

public theorem iunion_subset : (∀ i : ι, X i ⊆ s) → (⋃ i : ι, X i) ⊆ s := by
  intro xi_sub_s x
  simp
  intro i
  exact xi_sub_s i

public theorem subset_iinter : (∀ i : ι, s ⊆ X i) → s ⊆ ⋂ i : ι, X i := by
  intro s_sub_xi x
  simp
  intro x_in_s i
  apply s_sub_xi
  assumption

public theorem iinter_subset : (∃ i : ι, X i ⊆ s) → (⋂ i : ι, X i) ⊆ s := by
  intro h x
  obtain ⟨i, hi⟩ := h
  simp
  intro x_in_xi
  apply hi
  exact x_in_xi i

public theorem empty_iunion : ¬Nonempty ι → (⋃ i : ι, X i) = ∅ := by
  intro iota_empty
  ext x
  simp
  intro i x_in_xi
  have thus : Nonempty ι := Nonempty.intro i
  exact iota_empty thus

public theorem empty_iinter : ¬Nonempty ι → (⋂ i : ι, X i) = univ := by
  intro iota_empty
  ext x
  simp
  intro i
  have thus : Nonempty ι := Nonempty.intro i
  have anything_is_true : False := iota_empty thus
  trivial

public theorem iunion_subsets
  : (∀ i : ι, X₁ i ⊆ X₂ i) → (⋃ i : ι, X₁ i) ⊆ (⋃ i : ι, X₂ i) := by
  intro x1i_subset_x2i x
  simp
  intro i x_in_x1i
  exists X₂ i
  constructor
  exists i
  exact (x1i_subset_x2i i) x_in_x1i

public theorem iinter_subsets
  : (∀ i : ι, X₁ i ⊆ X₂ i) → (⋂ i : ι, X₁ i) ⊆ (⋂ i : ι, X₂ i) := by
  intro x1i_subset_x2i x
  simp
  intro x_in_x1i i
  exact (x1i_subset_x2i i) (x_in_x1i i)

/- ================================= IMAGES ================================= -/

public theorem image_iunion : f '' (⋃ i : ι, X i) = ⋃ i : ι, f '' (X i) := by
  ext y
  simp
  constructor

  intro h
  obtain ⟨x, ⟨⟨s, ⟨⟨i, xi_eq_s⟩, x_in_s⟩⟩, fx_eq_y⟩⟩ := h
  exists f '' s
  constructor
  exists i; rw [xi_eq_s]; simp; exists x

  intro h
  obtain ⟨t, ⟨⟨i, f_xi_eq_t⟩, y_in_t⟩⟩ := h
  have y_in_f_xi : y ∈ f '' X i := mem_right f_xi_eq_t y_in_t
  simp at y_in_f_xi
  obtain ⟨x, hx⟩ := y_in_f_xi
  exists x
  constructor
  exists X i
  constructor
  exists i
  exact hx.left
  exact hx.right

public theorem image_iinter : f '' (⋂ i : ι, X i) ⊆ ⋂ i : ι, f '' (X i) := by
  intro y
  simp
  intro x x_in_all_xi fx_eq_y i
  exists x
  constructor
  exact x_in_all_xi i
  assumption

public theorem image_iinter_injective
  (iota_nonempty: Nonempty ι) (f_injective: Function.Injective f)
  : f '' (⋂ i : ι, X i) = ⋂ i : ι, f '' (X i) := by
  apply subset_antisymm
  -- ⊆ always true
  exact image_iinter
  -- ⊇ uses left inverse
  obtain ⟨i⟩ := iota_nonempty
  intro y
  simp
  intro y_in_inter_of_images
  obtain ⟨x, hx⟩ := y_in_inter_of_images i
  exists x
  constructor
  intro j
  obtain ⟨x', hx'⟩ := y_in_inter_of_images j
  rw [← hx'.right] at hx
  have x_eq_x' : x = x' := f_injective hx.right
  rw [x_eq_x']
  exact hx'.left
  exact hx.right

/- =============================== PREIMAGES ================================ -/

public theorem preimage_iunion
  : f ⁻¹' (⋃ i : ι, Y i) = ⋃ i : ι, f ⁻¹' (Y i) := by
  ext x
  simp
  constructor

  intro h
  obtain ⟨t, ⟨⟨i, yi_eq_t⟩, fx_in_t⟩⟩ := h
  exists f ⁻¹' t
  constructor
  exists i
  rw [yi_eq_t]
  simp
  assumption

  intro h
  obtain ⟨s, ⟨⟨i, pre_yi_eq_s⟩, x_in_s⟩⟩ := h
  exists Y i
  constructor
  exists i
  have fx_in_yi : x ∈ f ⁻¹' Y i := mem_right pre_yi_eq_s x_in_s
  rw [← preimage_iff]
  assumption

public theorem preimage_iinter
  : f ⁻¹' (⋂ i : ι, Y i) = ⋂ i : ι, f ⁻¹' (Y i) := by
  ext x
  simp
