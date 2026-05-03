import Cerulean.Numbers.Natural

structure PreInt where
  p : ω
  m : ω

def PreInt.zero := PreInt.mk 0 0

def PreInt.one := PreInt.mk 1 0

def PreInt.two := PreInt.mk 2 0

def PreInt.equiv (a b : PreInt) : Prop := a.p + b.m = b.p + a.m

local infix:50 " ~ " => PreInt.equiv

theorem PreInt.equiv_rfl (a : PreInt) : a ~ a := by
  rfl

theorem PreInt.equiv_symm {a b : PreInt} : a ~ b → b ~ a := by
  unfold PreInt.equiv
  intro h
  symm
  assumption

theorem PreInt.equiv_trans {a b c : PreInt} : a ~ b → b ~ c → a ~ c := by
  unfold PreInt.equiv
  intro hab
  intro hbc
  let extra := b.m + b.p
  let h_calc : a.p + c.m + extra = a.p + (c.m + extra)
    := ω.add_assoc a.p c.m extra
  -- ugly, but the point is to prove
  -- (a.p + c.m) + extra = (b.p + a.m) + extra, and cancel extra
  rw [
    ← ω.add_assoc c.m, ω.add_comm c.m b.m, ω.add_assoc b.m, ← ω.add_assoc a.p,
    ω.add_comm c.m b.p, hab, hbc, ω.add_assoc b.p, ← ω.add_assoc a.m,
    ω.add_comm a.m c.p, ← ω.add_assoc b.p, ω.add_comm b.p, ω.add_assoc _ b.p,
    ω.add_comm b.p
  ] at h_calc
  apply ω.add_cancel
  assumption

instance : Trans PreInt.equiv PreInt.equiv PreInt.equiv where
  trans := PreInt.equiv_trans

def PreIntEquiv := Equivalence.mk
  PreInt.equiv_rfl PreInt.equiv_symm PreInt.equiv_trans

@[reducible]
def IntSet := Setoid.mk PreInt.equiv PreIntEquiv

def ℤ := Quotient IntSet

public instance : OfNat ℤ 0 where
  ofNat := Quotient.mk IntSet PreInt.zero

public instance : OfNat ℤ 1 where
  ofNat := Quotient.mk IntSet PreInt.one

public instance : OfNat ℤ 2 where
  ofNat := Quotient.mk IntSet PreInt.two

def quot (x : PreInt) : ℤ := Quotient.mk IntSet x

theorem ℤ.eq_or_not (a b : ℤ) : a = b ∨ a ≠ b := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  cases ω.eq_or_not (a.p + b.m) (b.p + a.m)
  case inl equals =>
    left
    apply Quotient.sound
    exact equals
  case inr not_equal =>
    right
    intro assume_eq
    have thus : a ~ b := Quotient.exact assume_eq
    exact not_equal thus

theorem ℤ.one_ne_zero : (1 : ℤ) ≠ 0 := by
  have since : ¬PreInt.one ~ PreInt.zero := by
    unfold PreInt.one PreInt.zero
    exact ω.one_ne_zero
  intro h
  have yet : PreInt.one ~ PreInt.zero := Quotient.exact h
  contradiction

/- =============================== NEGATION ================================= -/

def pre_neg (x : PreInt) : PreInt := PreInt.mk x.m x.p

def neg (x : PreInt) : ℤ := quot (pre_neg x)

theorem neg_equiv (a b : PreInt) : a ~ b → neg a = neg b :=
  have lemma (a b : PreInt) : a ~ b → pre_neg a ~ pre_neg b := by
    unfold PreInt.equiv
    intro h
    rw [ω.add_comm, ω.add_comm (pre_neg b).p]
    symm
    assumption
  Quotient.sound ∘ lemma a b

public instance : Neg ℤ where
  neg := Quotient.lift neg neg_equiv

theorem PreInt.negneg (a : PreInt) : pre_neg (pre_neg a) ~ a := rfl

public theorem ℤ.negneg (a : ℤ) : -(-a) = a := by
  refine Quotient.inductionOn a ?_; intro a
  apply Quotient.sound
  exact PreInt.negneg a

public theorem ℤ.neg_zero : -0 = (0 : ℤ) := by
  apply Quotient.sound
  rfl

public theorem ℤ.neg_move {a b : ℤ} : a = -b ↔ -a = b := by
  have lemma {a b : ℤ} : a = -b → -a = b := by
    intro h
    rw [h, negneg]
  constructor
  exact lemma
  have converse : -a = -(-b) → -(-a) = -b := lemma
  repeat rw [negneg] at converse
  assumption

public theorem ℤ.neg_eq_zero {a : ℤ} : a = 0 ↔ -a = 0 := by
  have expr : a = -0 ↔ -a = 0 := neg_move
  rw [neg_zero] at expr
  exact expr

/- =============================== ADDITION ================================= -/

def pre_add (x y : PreInt) := PreInt.mk (x.p + y.p) (x.m + y.m)

def add (x y : PreInt) : ℤ := quot (pre_add x y)

theorem pre_add_equiv (a₁ b₁ a₂ b₂ : PreInt)
  : a₁ ~ a₂ → b₁ ~ b₂ → pre_add a₁ b₁ ~ pre_add a₂ b₂ := by
  intro ha hb
  unfold PreInt.equiv at *
  unfold pre_add
  rw [ω.abcd_to_acbd a₁.p, ω.abcd_to_acbd a₂.p, ha, hb]

theorem add_equiv (a₁ b₁ a₂ b₂ : PreInt)
  : a₁ ~ a₂ → b₁ ~ b₂ → add a₁ b₁ = add a₂ b₂ := by
  intro ha hb
  apply Quotient.sound
  exact pre_add_equiv a₁ b₁ a₂ b₂ ha hb

public instance : Add ℤ where
  add (x y : ℤ) : ℤ := Quotient.lift₂ add add_equiv x y

theorem ℤ.add_zero (a : ℤ) : a + 0 = a := by
  refine Quotient.inductionOn a ?_; intro a
  rfl

theorem PreInt.add_comm (a b : PreInt) : pre_add a b ~ pre_add b a := by
  unfold PreInt.equiv pre_add
  simp
  rw [ω.add_comm a.p, ω.add_comm a.m]

theorem ℤ.add_comm (a b : ℤ) : a + b = b + a := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  apply Quotient.sound
  exact PreInt.add_comm a b

theorem ℤ.zero_add (a : ℤ) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem PreInt.add_assoc (a b c : PreInt)
  : pre_add (pre_add a b) c ~ pre_add a (pre_add b c) := by
  unfold PreInt.equiv pre_add
  simp
  rw [ω.add_assoc a.p, ω.add_assoc a.m]

theorem ℤ.add_assoc (a b c : ℤ) : (a + b) + c = a + (b + c) := by
  refine Quotient.inductionOn₃ a b c ?_; intro a b c
  apply Quotient.sound
  exact PreInt.add_assoc a b c

theorem ℤ.sum_inner_swap (a b c d : ℤ)
  : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc, ← add_assoc b, add_comm b, add_assoc, ← add_assoc]

theorem PreInt.add_sub (a : PreInt) : pre_add a (pre_neg a) ~ zero := by
  unfold PreInt.equiv pre_add pre_neg zero
  simp
  rw [ω.add_zero, ω.zero_add, ω.add_comm]

theorem ℤ.add_neg_cancel (a : ℤ) : a + (-a) = 0 := by
  refine Quotient.inductionOn a ?_; intro a
  apply Quotient.sound
  exact PreInt.add_sub a

theorem ℤ.neg_add_cancel (a : ℤ) : (-a) + a = 0 := by
  rw [add_comm, add_neg_cancel]

theorem ℤ.two_ne_zero : (2 : ℤ) ≠ 0 := by
  have since : ¬PreInt.two ~ PreInt.zero := by
    unfold PreInt.two PreInt.zero
    exact ω.two_ne_zero
  intro h
  have yet : PreInt.two ~ PreInt.zero := Quotient.exact h
  contradiction

/- ============================== SUBTRACTION =============================== -/

instance : Sub ℤ where
  sub (x y : ℤ) := x + (-y)

theorem ℤ.sub (a b : ℤ) : a - b = a + (-b) := by
  rfl

theorem PreInt.neg_add (a b : PreInt)
  : pre_neg (pre_add a b) ~ pre_add (pre_neg a) (pre_neg b) := by
  unfold PreInt.equiv pre_add pre_neg
  simp

theorem ℤ.neg_add (a b : ℤ) : -(a + b) = (-a) + (-b) := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  apply Quotient.sound
  exact PreInt.neg_add a b

theorem ℤ.neg_sub (a b : ℤ) : -(a - b) = b - a := by
  rw [sub, neg_add, negneg, add_comm, ← sub]

theorem ℤ.sub_cancel (a : ℤ) : a - a = 0 := by
  rw [sub, add_neg_cancel]

theorem ℤ.add_sub_assoc (a b c : ℤ) : (a + b) - c = a + (b - c) := by
  rw [sub, add_assoc, ← sub]

theorem ℤ.sub_add_assoc (a b c : ℤ) : (a - b) + c = a + (c - b) := by
  rw [sub, add_assoc, add_comm (-b), ← sub]

theorem ℤ.sub_sub_assoc (a b c : ℤ) : (a - b) - c = a - (b + c) := by
  rw [sub, sub, add_assoc, ← neg_add, ← sub]

theorem ℤ.add_sub_cancel (a b : ℤ) : (a + b) - b = a := by
  rw [add_sub_assoc, sub_cancel, add_zero]

theorem ℤ.sub_add_cancel (a b : ℤ) : (a - b) + b = a := by
  rw [sub_add_assoc, sub_cancel, add_zero]

theorem ℤ.add_right_cancel {a b c : ℤ} : a + c = b + c → a = b := by
  intro h
  have thus : a + c - c = b + c - c := congrArg (fun x => x - c) h
  rw [add_sub_cancel, add_sub_cancel] at thus
  assumption

theorem ℤ.add_left_cancel {a b c : ℤ} : c + a = c + b → a = b := by
  intro h
  rw [add_comm, add_comm c] at h
  exact add_right_cancel h

theorem ℤ.sub_right_cancel {a b c : ℤ} : a - c = b - c → a = b := by
  intro h
  rw [sub, sub] at h
  exact add_right_cancel h

theorem ℤ.eq_iff_sub_eq_zero {a b : ℤ} : a = b ↔ a - b = 0 := by
  constructor

  intro h
  have thus : a - b = b - b := congrArg (fun x => x - b) h
  rw [sub_cancel] at thus
  assumption

  intro h
  symm
  have thus : b = (a - b) + b := by
    have expr : (a - b) + b = 0 + b := congrArg (fun x => x + b) h
    symm
    rw [zero_add] at expr
    assumption
  have thus2 : (a - b) + b = a := sub_add_cancel a b
  calc b = (a - b) + b := thus
    _    = a           := thus2

/- ============================= MULTIPLICATION ============================= -/

-- (xp - xm)(yp - ym) = (xp yp + xm ym) - (xp ym + xm yp)
def pre_mul (x y : PreInt) : PreInt :=
  PreInt.mk (x.p * y.p + x.m * y.m) (x.p * y.m + x.m * y.p)

def mul (x y : PreInt) : ℤ := quot (pre_mul x y)

theorem pre_mul_equiv₁ (a₁ a₂ b : PreInt)
  : a₁ ~ a₂ → pre_mul a₁ b ~ pre_mul a₂ b := by
  unfold PreInt.equiv pre_mul
  simp
  intro h
  rw [
    ω.add_comm (a₂.p * b.m), ω.abcd_to_acbd, ← ω.add_mul, ← ω.add_mul, h,
    ω.add_mul, ω.add_comm a₁.m, ← h, ω.add_mul, ω.add_comm (a₁.p * b.m),
    ω.abcd_to_acbd, ω.add_comm (a₁.m * b.p)
  ]

theorem pre_mul_comm (a b : PreInt) : pre_mul a b ~ pre_mul b a := by
  unfold PreInt.equiv pre_mul
  simp
  rw [
    ω.mul_comm a.p, ω.mul_comm a.m, ω.mul_comm b.m a.p, ω.mul_comm b.p a.m,
    ω.add_comm (a.m * b.p)
  ]

-- nightmare expression
theorem pre_mul_equiv (a₁ b₁ a₂ b₂ : PreInt)
  : a₁ ~ a₂ → b₁ ~ b₂ → pre_mul a₁ b₁ ~ pre_mul a₂ b₂ := by
  intro ha hb
  calc
    pre_mul a₁ b₁ ~ pre_mul a₂ b₁ := pre_mul_equiv₁ a₁ a₂ b₁ ha
    _             ~ pre_mul b₁ a₂ := pre_mul_comm a₂ b₁
    _             ~ pre_mul b₂ a₂ := pre_mul_equiv₁ b₁ b₂ a₂ hb
    _             ~ pre_mul a₂ b₂ := pre_mul_comm b₂ a₂

theorem mul_equiv (a₁ b₁ a₂ b₂ : PreInt)
  : a₁ ~ a₂ → b₁ ~ b₂ → mul a₁ b₁ = mul a₂ b₂ := by
  intro ha hb
  apply Quotient.sound
  exact pre_mul_equiv a₁ b₁ a₂ b₂ ha hb

public instance : Mul ℤ where
  mul (x y : ℤ) : ℤ := Quotient.lift₂ mul mul_equiv x y

theorem ℤ.mul_comm (a b : ℤ) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  apply Quotient.sound
  exact pre_mul_comm a b

theorem ℤ.mul_zero (a : ℤ) : a * 0 = 0 := by
  refine Quotient.inductionOn a ?_; intro a
  rfl

theorem ℤ.zero_mul (a : ℤ) : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

theorem ℤ.mul_one (a : ℤ) : a * 1 = a := by
  refine Quotient.inductionOn a ?_; intro a
  apply Quotient.sound
  unfold pre_mul PreInt.one
  simp
  rw [ω.mul_one, ω.mul_one, ω.mul_zero, ω.mul_zero, ω.add_zero, ω.zero_add]
  rfl

theorem ℤ.one_mul (a : ℤ) : 1 * a = a := by
  rw [mul_comm, mul_one]

theorem PreInt.neg_mul (a b : PreInt)
  : pre_mul (pre_neg a) b ~ pre_neg (pre_mul a b) := by
  unfold equiv pre_neg pre_mul
  simp
  rw [ω.add_comm (a.m * b.p), ω.add_comm (a.p * b.p)]

theorem ℤ.neg_mul (a b : ℤ) : (-a) * b = -(a * b) := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  apply Quotient.sound
  exact PreInt.neg_mul a b

theorem ℤ.mul_neg (a b : ℤ) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem ℤ.neg_one_mul (a : ℤ) : (-1) * a = -a := by
  rw [neg_mul, one_mul]

theorem ℤ.mul_neg_one (a : ℤ) : a * (-1) = -a := by
  rw [mul_neg, mul_one]

-- nightmare moment since i can't use ring
theorem PreInt.mul_assoc (a b c : PreInt)
  : pre_mul (pre_mul a b) c ~ pre_mul a (pre_mul b c) := by
  unfold PreInt.equiv pre_mul
  simp
  repeat rw [ω.mul_add, ω.add_mul, ω.mul_assoc]
  repeat rw [ω.mul_assoc]
  rw [ω.abcd_to_acbd (a.p * (b.p * c.p))]
  rw [ω.add_comm (a.m * (b.p * c.m))]
  rw [ω.abcd_to_adbc (a.p * (b.p * c.m))]

theorem ℤ.mul_assoc (a b c : ℤ) : (a * b) * c = a * (b * c) := by
  refine Quotient.inductionOn₃ a b c ?_; intro a b c
  apply Quotient.sound
  exact PreInt.mul_assoc a b c

theorem PreInt.add_mul (a b c : PreInt)
  : pre_mul (pre_add a b) c ~ pre_add (pre_mul a c) (pre_mul b c) := by
  unfold equiv pre_mul pre_add
  simp
  repeat rw [ω.add_mul]
  rw [ω.abcd_to_acbd (a.p * c.p)]
  rw [ω.abcd_to_acbd (a.p * c.m)]

theorem ℤ.add_mul (a b c : ℤ) : (a + b) * c = a * c + b * c := by
  refine Quotient.inductionOn₃ a b c ?_; intro a b c
  apply Quotient.sound
  exact PreInt.add_mul a b c

theorem ℤ.mul_add (a b c : ℤ) : a * (b + c) = a * b + a * c := by
  rw [mul_comm, add_mul, mul_comm, mul_comm c]

theorem ℤ.sub_mul (a b c : ℤ) : (a - b) * c = a * c - b * c := by
  rw [sub, add_mul, neg_mul, sub]

theorem ℤ.mul_sub (a b c : ℤ) : a * (b - c) = a * b - a * c := by
  rw [sub, mul_add, mul_neg, sub]

theorem PreInt.mul_eq_zero {a b : PreInt}
  : pre_mul a b ~ zero → a ~ zero ∨ b ~ zero := by
  unfold equiv zero pre_mul
  simp [ω.add_zero, ω.zero_add]
  have lemma {a b c d : ω}
    : a ≤ b → a * c + b * d = a * d + b * c → a = b ∨ c = d := by
    intro a_le_b h
    obtain ⟨t, ht⟩ := a_le_b
    rw [
      ht, ω.add_mul, ω.add_mul, ← ω.add_assoc, ← ω.add_assoc,
      ω.add_comm (a * c)] at h
    cases ω.zero_or_not t
    case inl t_eq_0 =>
      left
      rw [t_eq_0, ω.add_zero] at ht
      symm
      assumption
    case inr t_ne_0 =>
      right
      have thus : t * d = t * c := ω.cancel_add h
      have therefore : d = c := ω.cancel_mul t_ne_0 thus
      symm
      assumption
  have one_of : a.p ≤ a.m ∨ a.m ≤ a.p := ω.le_dichotomy
  cases one_of
  case inl ap_le_am =>
    intro h
    exact lemma ap_le_am h
  case inr am_le_ap =>
    intro h
    rw [ω.add_comm, ω.add_comm (a.p * b.m)] at h
    have thus : a.m = a.p ∨ b.m = b.p := lemma am_le_ap h
    cases thus
    case inl h => symm at h; left; assumption
    case inr h => symm at h; right; assumption

theorem ℤ.mul_eq_zero {a b : ℤ} : a * b = 0 → a = 0 ∨ b = 0 := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  intro h
  have h_equiv : pre_mul a b ~ PreInt.zero := Quotient.exact h
  cases PreInt.mul_eq_zero h_equiv
  case inl a_equiv_0 =>
    left
    apply Quotient.sound
    assumption
  case inr b_equiv_0 =>
    right
    apply Quotient.sound
    assumption

theorem ℤ.mul_cancel {a b k : ℤ} : k ≠ 0 → a * k = b * k → a = b := by
  intro k_ne_0 ak_eq_bk
  rw [eq_iff_sub_eq_zero, ← sub_mul] at ak_eq_bk
  have thus : a - b = 0 := (mul_eq_zero ak_eq_bk).resolve_right k_ne_0
  rw [← eq_iff_sub_eq_zero] at thus
  assumption

theorem ℤ.cancel_mul {a b k : ℤ} : k ≠ 0 → k * a = k * b → a = b := by
  intro k_ne_0 ak_eq_bk
  rw [mul_comm, mul_comm k] at ak_eq_bk
  exact mul_cancel k_ne_0 ak_eq_bk

theorem ℤ.nonzero_mul {a b : ℤ} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  intro _ _ hab
  cases mul_eq_zero hab
  case inl _ => contradiction
  case inr _ => contradiction

theorem ℤ.two_mul (a : ℤ) : 2 * a = a + a := by
  refine Quotient.inductionOn a ?_; intro a
  apply Quotient.sound
  unfold pre_mul pre_add PreInt.two
  simp
  rw [ω.two_mul, ω.two_mul, ω.zero_mul, ω.zero_mul, ω.add_zero, ω.add_zero]
  rfl

theorem ℤ.eq_neg_self {a : ℤ} : -a = a → a = 0 := by
  intro h
  have expr : -a + a = a + a := by rw [h]
  rw [neg_add_cancel, ← two_mul] at expr
  symm at expr
  have thus : (2 : ℤ) = 0 ∨ a = 0 := mul_eq_zero expr
  have yet : (2 : ℤ) ≠ 0 := two_ne_zero
  exact thus.resolve_left yet

/- =================================== LE =================================== -/

-- xp - xm ≤ yp - ym <-> xp + ym ≤ yp + xm
def pre_le (x y : PreInt) : Prop := x.p + y.m ≤ y.p + x.m

theorem le_equiv₁ (a₁ a₂ b : PreInt)
  : a₁ ~ a₂ → (pre_le a₁ b → pre_le a₂ b) := by
  unfold pre_le PreInt.equiv
  intro ha hle
  obtain ⟨k, hle⟩ := hle
  have expr : b.p + a₁.m + a₂.p = a₁.p + b.m + k + a₂.p :=
    congrArg (fun x => x + a₂.p) hle
  rw [
    ω.add_assoc, ω.add_comm a₁.m, ← ha, ω.add_comm a₁.p, ← ω.add_assoc,
    ω.add_assoc a₁.p, ω.add_assoc a₁.p, ω.add_comm a₁.p,
    ω.add_assoc b.m, ω.add_comm k, ← ω.add_assoc, ω.add_comm b.m
  ] at expr
  have thus : b.p + a₂.m = a₂.p + b.m + k := ω.add_cancel expr
  exists k

theorem le_equiv₂ (a₁ a₂ b : PreInt)
  : a₁ ~ a₂ → (pre_le b a₁ → pre_le b a₂) := by
  unfold pre_le PreInt.equiv
  intro ha hle
  obtain ⟨k, hle⟩ := hle
  have expr : a₁.p + b.m + a₂.m = b.p + a₁.m + k + a₂.m :=
    congrArg (fun x => x + a₂.m) hle
  rw [
    ω.add_comm a₁.p, ω.add_assoc, ha, ← ω.add_assoc,
    ω.add_assoc (b.p + a₁.m), ω.abcd_to_adcb, ← ω.add_assoc, ω.add_comm b.m
  ] at expr
  have thus : a₂.p + b.m = b.p + a₂.m + k := ω.add_cancel expr
  exists k

theorem le_equiv_lemma {a₁ b₁ a₂ b₂ : PreInt}
  : a₁ ~ a₂ → b₁ ~ b₂ → (pre_le a₁ b₁ → pre_le a₂ b₂) := by
  intro ha hb
  exact (le_equiv₂ b₁ b₂ a₂ hb) ∘ (le_equiv₁ a₁ a₂ b₁ ha)

theorem le_equiv {a₁ b₁ a₂ b₂ : PreInt}
  : a₁ ~ a₂ → b₁ ~ b₂ → (pre_le a₁ b₁ ↔ pre_le a₂ b₂) := by
  intro ha hb
  constructor
  exact le_equiv_lemma ha hb
  have ha : a₂ ~ a₁ := PreInt.equiv_symm ha
  have hb : b₂ ~ b₁ := PreInt.equiv_symm hb
  exact le_equiv_lemma ha hb

theorem le_equiv_ext (a₁ b₁ a₂ b₂ : PreInt)
  : a₁ ~ a₂ → b₁ ~ b₂ → (pre_le a₁ b₁ = pre_le a₂ b₂) :=
  fun a => fun b => propext (le_equiv a b)

public instance : LE ℤ where
  le x y := Quotient.lift₂ pre_le le_equiv_ext x y

theorem PreInt.le_rfl (a : PreInt) : pre_le a a := by
  unfold pre_le
  rw [ω.add_comm]
  exists 0

theorem PreInt.le_antisymm {a b : PreInt}
  : pre_le a b → pre_le b a → a ~ b := by
  unfold pre_le
  intro a_le_b b_le_a
  have thus : a.p + b.m = b.p + a.m := ω.le_antisymm a_le_b b_le_a
  assumption

theorem PreInt.le_trans {a b c : PreInt}
  (a_le_b : pre_le a b) (b_le_c : pre_le b c) : pre_le a c := by
  unfold pre_le at *
  obtain ⟨k₁, h₁⟩ := a_le_b
  obtain ⟨k₂, h₂⟩ := b_le_c

  have feq (x : ω) : (c.p + b.m) + x = (b.p + c.m + k₂) + x := by
    rw [h₂]
  have expr : (c.p + b.m) + (b.p + a.m) = (b.p + c.m + k₂) + (a.p + b.m + k₁)
    := congr (funext feq) h₁
  rw [
    ω.abcd_to_adcb, ω.add_comm (b.p + c.m + k₂), ω.add_assoc a.p,
    ω.add_assoc a.p, ω.abcd_to_cabd b.m, ω.add_comm b.p c.m,
    ω.add_assoc c.m, ω.add_assoc c.m, ← ω.add_assoc a.p,
    ω.add_comm (b.p + b.m), ← ω.add_assoc (a.p + c.m)
  ] at expr
  have thus : c.p + a.m = a.p + c.m + (k₁ + k₂) := ω.add_cancel expr
  exists k₁ + k₂

theorem lift_le {a b : PreInt} : pre_le a b → quot a ≤ quot b := by
  intro a_le_b
  assumption

public theorem ℤ.le_rfl (a : ℤ) : a ≤ a := by
  refine Quotient.inductionOn a ?_; intro a
  exact PreInt.le_rfl a

public theorem ℤ.eq_then_le {a b : ℤ} : a = b → a ≤ b := by
  intro h
  rw [h]
  exact le_rfl b

public theorem ℤ.le_antisymm {a b : ℤ} : a ≤ b → b ≤ a → a = b := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  intro ha hb
  apply Quotient.sound
  have a_le_b : pre_le a b := ha
  have b_le_a : pre_le b a := hb
  exact PreInt.le_antisymm a_le_b b_le_a

public theorem ℤ.le_trans {a b c : ℤ} : a ≤ b → b ≤ c → a ≤ c := by
  refine Quotient.inductionOn₃ a b c ?_; intro a b c
  intro hab hbc
  have a_le_b : pre_le a b := hab
  have b_le_c : pre_le b c := hbc
  exact PreInt.le_trans a_le_b b_le_c

theorem PreInt.le_add {a b c d : PreInt}
  : pre_le a b → pre_le c d → pre_le (pre_add a c) (pre_add b d) := by
  unfold pre_le pre_add
  simp
  intro hab hcd
  obtain ⟨k₁, hab⟩ := hab
  obtain ⟨k₂, hcd⟩ := hcd

  have feq (x : ω) : (d.p + c.m) + x = (c.p + d.m + k₂) + x := by rw [hcd]
  have expr : (d.p + c.m) + (b.p + a.m) = (c.p + d.m + k₂) + (a.p + b.m + k₁)
    := congr (funext feq) hab
  rw [
    ω.add_comm, ω.abcd_to_acbd, ω.add_assoc c.p, ω.add_comm (c.p + (d.m + k₂)),
    ω.add_assoc a.p, ω.abcd_to_acbd a.p, ω.abcd_to_acbd b.m,
    ← ω.add_assoc (a.p + c.p)
  ] at expr
  exists k₁ + k₂

public theorem ℤ.le_add {a b c d : ℤ} : a ≤ b → c ≤ d → a + c ≤ b + d := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  refine Quotient.inductionOn₂ c d ?_; intro c d
  intro a_le_b c_le_d
  have a_le_b : pre_le a b := a_le_b
  have c_le_d : pre_le c d := c_le_d
  exact PreInt.le_add a_le_b c_le_d

public theorem ℤ.le_iff_zero_le_add {a b : ℤ}
  : a ≤ b ↔ 0 ≤ b - a := by
  constructor

  intro h
  have clearly : -a ≤ -a := le_rfl (-a)
  have thus : a + (-a) ≤ b + (-a) := le_add h clearly
  rw [add_neg_cancel, ← sub] at thus
  assumption

  intro h
  have clearly : a ≤ a := le_rfl a
  have thus : 0 + a ≤ (b - a) + a := le_add h clearly
  rw [zero_add, sub_add_cancel] at thus
  assumption

public theorem ℤ.le_neg {a b : ℤ} : a ≤ b ↔ -b ≤ -a := by
  have lemma (a b : ℤ) : a ≤ b → -b ≤ -a := by
    intro a_le_b
    have clearly : -(a + b) ≤ -(a + b) := le_rfl (-(a + b))
    have thus : -(a + b) + a ≤ -(a + b) + b := le_add clearly a_le_b
    rw [
      neg_add, add_assoc, add_assoc, add_comm, ← sub,
      add_sub_cancel, neg_add_cancel, add_zero
    ] at thus
    assumption
  constructor
  exact lemma a b
  intro nb_le_na
  have almost : -(-a) ≤ -(-b) := lemma (-b) (-a) nb_le_na
  repeat rw [negneg] at almost
  assumption

public theorem ℤ.le_nonneg {a : ℤ} : 0 ≤ a ↔ -a ≤ 0 := by
  constructor
  intro h
  have expr : -a ≤ -0 := le_neg.mp h
  rw [neg_zero] at expr
  assumption
  intro h
  have expr : -0 ≤ -(-a) := le_neg.mp h
  rw [neg_zero, negneg] at expr
  assumption

public theorem ℤ.le_nonpos {a : ℤ} : a ≤ 0 ↔ 0 ≤ -a := by
  rw [← negneg a, negneg (-a)]
  symm
  exact le_nonneg

public theorem ℤ.le_sub {a b c d : ℤ} : a ≤ b → c ≤ d → a - d ≤ b - c := by
  intro a_le_b c_le_d
  have nd_le_nc : -d ≤ -c := le_neg.mp c_le_d
  exact le_add a_le_b nd_le_nc

public theorem ℤ.le_add_cancel {a b k : ℤ} : a + k ≤ b + k → a ≤ b := by
  intro h
  have clearly : k ≤ k := ℤ.le_rfl k
  have thus : (a + k) - k ≤ (b + k) - k := le_sub h clearly
  repeat rw [add_sub_cancel] at thus
  assumption

public theorem ℤ.le_cancel_add {a b k : ℤ} : k + a ≤ k + b → a ≤ b := by
  repeat rw [add_comm k]
  exact le_add_cancel

public theorem ℤ.le_sub_cancel {a b k : ℤ} : a - k ≤ b - k → a ≤ b := by
  repeat rw [sub]
  exact le_add_cancel

public theorem ℤ.le_cancel_sub {a b k : ℤ} : k - a ≤ k - b → b ≤ a := by
  intro h
  repeat rw [sub]
  have thus : -a ≤ -b := le_cancel_add h
  exact le_neg.mpr thus

theorem PreInt.mul_nonneg {a b : PreInt}
  : pre_le zero a → pre_le zero b → pre_le zero (pre_mul a b) := by
  unfold pre_le zero pre_mul
  simp
  repeat rw [ω.zero_add]
  repeat rw [ω.add_zero]
  intro ha hb
  obtain ⟨k₁, ha⟩ := ha
  obtain ⟨k₂, hb⟩ := hb
  have expr : a.p * b.p + (a.m * b.m) = (a.m + k₁) * (b.m + k₂) + (a.m * b.m)
    := by rw [ha, hb]
  rw [
    ω.add_mul, ω.mul_add, ω.mul_add, ← ω.mul_add, ← hb,
    ω.add_assoc (a.m * b.p), ω.add_assoc, ω.add_comm (k₁ * k₂),
    ← ω.add_assoc (k₁ * b.m), ← ω.add_mul, ω.add_comm k₁, ← ha,
    ← ω.add_assoc, ω.add_comm (a.m * b.p)
  ] at expr
  exists k₁ * k₂

public theorem ℤ.mul_nonneg {a b : ℤ} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  intro ha hb
  have ha : pre_le PreInt.zero a := ha
  have hb : pre_le PreInt.zero b := hb
  exact PreInt.mul_nonneg ha hb

public theorem ℤ.nonpos_mul_nonneg {a b : ℤ} : a ≤ 0 → 0 ≤ b → a * b ≤ 0 := by
  intro ha hb
  have hna : 0 ≤ -a := le_nonpos.mp ha
  have expr : 0 ≤ (-a) * b := mul_nonneg hna hb
  rw [neg_mul, ← le_nonpos] at expr
  assumption

public theorem ℤ.nonneg_mul_nonpos {a b : ℤ} : a ≤ 0 → 0 ≤ b → b * a ≤ 0 := by
  rw [mul_comm]
  exact nonpos_mul_nonneg

public theorem ℤ.mul_nonpos {a b : ℤ} : a ≤ 0 → b ≤ 0 → 0 ≤ a * b := by
  intro ha hb
  have hna : 0 ≤ -a := le_nonpos.mp ha
  have hnb : 0 ≤ -b := le_nonpos.mp hb
  have expr : 0 ≤ (-a) * (-b) := mul_nonneg hna hnb
  rw [neg_mul, mul_neg, negneg] at expr
  exact expr

public theorem ℤ.le_dichotomy {a b : ℤ} : a ≤ b ∨ b ≤ a := by
  refine Quotient.inductionOn₂ a b ?_; intro a b
  exact ω.le_dichotomy

/- =================================== LT =================================== -/

public instance : LT ℤ where
  lt m n := m ≤ n ∧ m ≠ n

public theorem ℤ.le_iff {a b : ℤ} : a ≤ b ↔ a < b ∨ a = b := by
  constructor
  intro h
  cases eq_or_not a b
  case inl eq => right; assumption
  case inr neq => left; exact ⟨h, neq⟩
  intro h
  cases h
  case inl leq => exact leq.left
  case inr eq => rw [eq]; exact le_rfl b

public theorem ℤ.lt_trichotomy {a b : ℤ} : a < b ∨ a = b ∨ b < a := by
  cases le_dichotomy
  case inl a_le_b =>
    have thus : a < b ∨ a = b := le_iff.mp a_le_b
    cases thus
    case inl _ => left; assumption
    case inr _ => right; left; assumption
  case inr b_le_a =>
    have thus : b < a ∨ b = a := le_iff.mp b_le_a
    cases thus
    case inl _ => right; right; assumption
    case inr _ => right; left; symm; assumption

public theorem ℤ.not_le {a b : ℤ} : ¬ a ≤ b ↔ b < a := by
  constructor

  intro h
  have b_le_a : b ≤ a := Or.resolve_left le_dichotomy h
  have b_ne_a : b ≠ a := by
    intro h
    have a_le_b : a ≤ b := by rw [h]; exact le_rfl a
    contradiction
  exact ⟨b_le_a, b_ne_a⟩

  intro h
  obtain ⟨b_le_a, b_ne_a⟩ := h
  intro a_le_b
  have b_eq_a : b = a := le_antisymm b_le_a a_le_b
  contradiction

public theorem ℤ.not_lt {a b : ℤ} : ¬ a < b ↔ b ≤ a := by
  constructor

  intro h
  have h : b < a ∨ b = a := (or_assoc.mpr lt_trichotomy).resolve_right h
  exact le_iff.mpr h

  intro b_le_a a_lt_b
  have a_le_b : a ≤ b := le_iff.mpr (Or.inl a_lt_b)
  have thus : a = b := le_antisymm a_le_b b_le_a
  have yet : a ≠ b := a_lt_b.right
  contradiction

theorem no_in_between_lemma {x y : ℤ} : x < y → x + 1 ≤ y := by
  unfold LT.lt instLTℤ
  simp
  refine Quotient.inductionOn₂ x y ?_; intro x y
  intro x_le_y x_ne_y
  obtain ⟨k, hk⟩ := x_le_y
  have x_le_y : x.p + y.m ≤ y.p + x.m := by exists k
  have x_ne_y : x.p + y.m ≠ y.p + x.m := by
    intro h
    have thus : x ~ y := h
    exact x_ne_y (Quotient.sound thus)
  have thus : x.p + y.m < y.p + x.m := ⟨x_le_y, x_ne_y⟩
  have thus : (x.p + 1) + y.m ≤ y.p + x.m := by
    have expr : x.p + y.m + 1 ≤ y.p + x.m := ω.lt_then_succ_le thus
    rw [ω.add_assoc, ω.add_comm 1, ← ω.add_assoc]
    assumption
  have therefore : pre_le (pre_add x PreInt.one) y := by
    unfold pre_add PreInt.one
    simp
    rw [ω.add_zero]
    exact thus
  exact therefore

public theorem ℤ.no_in_between (x : ℤ) : ¬ ∃ y : ℤ, x < y ∧ y < x + 1 := by
  simp
  intro y x_lt_y
  have thus : x + 1 ≤ y := by
    exact no_in_between_lemma x_lt_y
  exact not_lt.mpr thus

public theorem ℤ.no_in_between₂ (x y : ℤ) : y ≤ x ∨ x + 1 ≤ y := by
  have trichotomy : y < x ∨ y = x ∨ x < y := lt_trichotomy
  cases or_assoc.mpr trichotomy
  case inl y_le_x  =>
    left
    exact le_iff.mpr y_le_x
  case inr x_lt_y =>
    right
    exact no_in_between_lemma x_lt_y

/- =============================== DECIDABLE ================================ -/

def pre_ble (x y : PreInt) : Bool := ω.ble (x.p + y.m) (y.p + x.m)

theorem pre_ble_iff_le {x y : PreInt} : pre_ble x y ↔ pre_le x y := by
  unfold pre_ble pre_le
  exact ω.ble_iff_le (x.p + y.m) (y.p + x.m)

theorem ble_equiv {x₁ y₁ x₂ y₂ : PreInt}
  : x₁ ~ x₂ → y₁ ~ y₂ → (pre_ble x₁ y₁ ↔ pre_ble x₂ y₂) := by
  intro ha hb
  calc pre_ble x₁ y₁ ↔ pre_le x₁ y₁ := pre_ble_iff_le
    _ ↔ pre_le x₂ y₂ := le_equiv ha hb
    _ ↔ pre_ble x₂ y₂ := Iff.symm pre_ble_iff_le

theorem ble_equiv_ext (x₁ y₁ x₂ y₂ : PreInt)
  : x₁ ~ x₂ → y₁ ~ y₂ → (pre_ble x₁ y₁ = pre_ble x₂ y₂) :=
  fun a => fun b => Bool.eq_iff_iff.mpr (ble_equiv a b)

def ℤ.ble (x y : ℤ) : Bool :=
  Quotient.lift₂ pre_ble ble_equiv_ext x y

theorem ℤ.ble_iff_le {x y : ℤ} : ℤ.ble x y ↔ x ≤ y := by
  refine Quotient.inductionOn₂ x y ?_; intro a b
  exact pre_ble_iff_le

instance (x y : ℤ) : Decidable (ℤ.ble x y) :=
  if h : ℤ.ble x y then isTrue h else isFalse h

def abs (x : ℤ) : ℤ := if ℤ.ble 0 x then x else -x

theorem ℤ.abs_nonneg {a : ℤ} : 0 ≤ a ↔ abs a = a := by
  unfold abs
  rw [← ble_iff_le]
  constructor
  intro h
  exact if_pos h
  intro h
  simp at h
  cases hb : ble 0 a <;>
  simp
  have thus : a = 0 := eq_neg_self (h hb)
  have therefore : ble 0 a = true := by rw [thus]; trivial
  rw [therefore] at hb
  contradiction

theorem ℤ.abs_nonpos {a : ℤ} : a ≤ 0 ↔ abs a = -a := by
  sorry

/- ============================== DIVISIBILITY ============================== -/

def ℤ.divides (a b : ℤ) := ∃ k : ℤ, b = a * k

infix:100 " ∣ " => ℤ.divides

theorem ℤ.all_div_zero (x : ℤ) : x ∣ 0 := by
  exists 0
  rw [mul_zero]

-- don't take this too literally, that doesn't mean 0/0 is a well-defined
-- rational number
theorem ℤ.zero_div_zero : (0 : ℤ) ∣ 0 := all_div_zero 0

theorem ℤ.one_div_all (x : ℤ) : 1 ∣ x := by
  exists x
  rw [one_mul]

/- =========================== MODULAR ARITHMETIC =========================== -/

-- todo

/- ================================= PRIMES ================================= -/

def ℤ.isPrime (p : ℤ) := 1 < p ∧ ∀ x : ℤ, x ∣ p → (1 = x ∨ 1 = p)
