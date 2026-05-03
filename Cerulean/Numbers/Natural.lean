module

public inductive ω
  | zero
  | succ (n : ω)
  deriving DecidableEq

public instance : OfNat ω 0 where
  ofNat := ω.zero

public instance : OfNat ω 1 where
  ofNat := ω.succ ω.zero

public instance : OfNat ω 2 where
  ofNat := ω.succ (ω.succ ω.zero)

public theorem ω.zero_def : ω.zero = 0 := by
  rfl

public theorem ω.one_def : ω.succ 0 = 1 := by
  rfl

public theorem ω.succ_inj {m n : ω} : m.succ = n.succ → m = n := by
  intro h
  exact ω.noConfusion h id

public theorem ω.succ_nonzero (n : ω) : n.succ ≠ 0 := by
  exact ω.noConfusion

public theorem ω.ne_succ (n : ω) : n ≠ n.succ := by
  induction n
  case zero =>
    symm
    exact succ_nonzero 0
  case succ n hn =>
    intro contradict
    have : n = n.succ := succ_inj contradict
    contradiction

theorem ω.succ_iff {m n : ω} : m.succ = n.succ ↔ m = n := by
  constructor
  exact succ_inj
  intro h
  rw [h]

public theorem ω.one_ne_zero : (1 : ω) ≠ 0 := by
  rw [← one_def]
  exact succ_nonzero 0

public theorem ω.zero_or_not (n : ω) : n = 0 ∨ n ≠ 0 := by
  cases n
  case zero =>
    left
    rw [zero_def]
  case succ n =>
    right
    exact succ_nonzero n

/- =============================== ADDITION ================================= -/

public def ω.add (m n : ω) :=
  match m,n with
  | m, zero => m
  | m, succ k => ω.succ (ω.add m k)

public instance : Add ω where
  add := ω.add

public theorem ω.add_zero (n : ω) : n + 0 = n := by
  rfl

public theorem ω.succ_def (n : ω) : ω.succ n = n + 1 := by
  rfl

theorem ω.add_succ (m n : ω) : m + (n + 1) = (m + n) + 1 := by
  rfl

public theorem ω.zero_add (n : ω) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n h =>
  rw [succ_def, add_succ, h]

theorem ω.succ_add (m n : ω) : (m + 1) + n = (m + n) + 1 := by
  induction n
  case zero => rfl
  case succ n h =>
  rw [succ_def, add_succ, add_succ, h]

public theorem ω.add_comm (m n : ω) : m + n = n + m := by
  induction n
  case zero =>
    rw [zero_def, zero_add]
    rfl
  case succ n h =>
    rw [succ_def, add_succ, succ_add, h]

public theorem ω.add_assoc (m n k : ω) : (m + n) + k = m + (n + k) := by
  induction k
  case zero =>
    rw [zero_def]
    rfl
  case succ k h =>
    rw [succ_def]
    repeat rw [add_succ]
    rw [h]

public theorem ω.add_cancel {m n k : ω} : m + k = n + k → m = n := by
  induction k
  case zero =>
    rw [zero_def, add_zero, add_zero]
    exact id
  case succ k hk =>
    rw [succ_def, add_succ, add_succ, ← succ_def, ← succ_def, succ_iff]
    assumption

public theorem ω.cancel_add {m n k : ω} : k + m = k + n → m = n := by
  intro h
  rw [add_comm k m, add_comm k n] at h
  exact add_cancel h

public theorem ω.cancel_add_eq_zero {n k : ω} : k + n = n → k = 0 := by
  intro h
  rw [← zero_add n, ← add_assoc, add_zero] at h
  exact add_cancel h

public theorem ω.sum_zero_left {m n : ω} : m + n = 0 → m = 0 := by
  induction n
  case zero =>
    rw [zero_def, add_zero]
    exact id
  case succ n h =>
    rw [succ_def, add_succ, ← succ_def]
    intro f
    have : (m + n).succ ≠ 0 := succ_nonzero (m+n)
    contradiction

public theorem ω.sum_zero_right {m n : ω} : m + n = 0 → n = 0 := by
  rw [add_comm]
  exact sum_zero_left

public theorem ω.abcd_to_acbd (a b c d : ω)
  : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc, ← add_assoc b, add_comm b, add_assoc, ← add_assoc]

public theorem ω.abcd_to_adbc (a b c d : ω)
  : (a + b) + (c + d) = (a + d) + (b + c) := by
  rw [add_comm c, abcd_to_acbd]

public theorem ω.abcd_to_adcb (a b c d : ω)
  : (a + b) + (c + d) = (a + d) + (c + b) := by
  rw [abcd_to_adbc, add_comm b c]

public theorem ω.abcd_to_cabd (a b c d : ω)
  : (a + b) + (c + d) = (c + a) + (b + d) := by
  rw [add_comm, add_comm a, abcd_to_adcb]

/- =================================== LE =================================== -/

public instance : LE ω where
  le m n := ∃ k : ω, n = m + k

public theorem ω.zero_le (n : ω) : 0 ≤ n := by
  exists n
  rw [zero_add]

public theorem ω.one_le {n : ω} : n ≠ 0 ↔ 1 ≤ n := by
  constructor
  intro nonzero
  induction n
  case zero =>
    have nzero : zero = 0 := by rfl
    contradiction
  case succ n h =>
    rw [succ_def]
    exists n
    rw [add_comm]
  intro h
  obtain ⟨k, h⟩ := h
  rw [add_comm, ← succ_def] at h
  have nonzero : k.succ ≠ 0 := succ_nonzero k
  rw [← h] at nonzero
  assumption

public theorem ω.le_rfl (n : ω) : n ≤ n := by
  exists 0

public theorem ω.eq_then_le {m n : ω} : m = n → m ≤ n := by
  intro h
  rw [h]
  exact le_rfl n

theorem ω.succ_le_succ {m n : ω} : m ≤ n → m.succ ≤ n.succ := by
  intro h
  obtain ⟨k, hk⟩ := h
  exists k
  rw [succ_def, succ_def, succ_add, hk]

public theorem ω.le_antisymm {m n : ω} (hm : m ≤ n) (hn : n ≤ m) : m = n := by
  obtain ⟨k₁, h₁⟩ := hm
  obtain ⟨k₂, h₂⟩ := hn
  rw [h₁, add_assoc] at h₂
  have hk : 0 = k₁ + k₂ := by
    apply cancel_add
    assumption
  have hk₁ : k₁ = 0 := by
    symm at hk
    exact sum_zero_left hk
  rw [hk₁, add_zero] at h₁
  symm
  assumption

public theorem ω.le_trans {m n k : ω} (h₁ : m ≤ n) (h₂ : n ≤ k) : m ≤ k := by
  obtain ⟨k₁, h₁⟩ := h₁
  obtain ⟨k₂, h₂⟩ := h₂
  rw [h₁, add_assoc] at h₂
  exists (k₁ + k₂)

public theorem ω.le_add_cancel {m n k : ω} : m + k ≤ n + k → m ≤ n := by
  intro h
  obtain ⟨l, h⟩ := h
  rw [add_assoc, add_comm k l, ← add_assoc] at h
  exists l
  apply add_cancel
  assumption

public theorem ω.le_cancel_add {m n k : ω} : k + m ≤ k + n → m ≤ n := by
  intro h
  obtain ⟨l, h⟩ := h
  rw [add_assoc] at h
  exists l
  apply cancel_add
  assumption

public theorem ω.le_add {a b c d : ω}
  (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by

  obtain ⟨k₁, h₁⟩ := h₁
  obtain ⟨k₂, h₂⟩ := h₂
  exists (k₁ + k₂)
  rw [h₁, h₂, add_assoc, ← add_assoc k₁, add_comm k₁, add_assoc, ← add_assoc]

/- =================================== LT =================================== -/

public instance : LT ω where
  lt m n := m ≤ n ∧ m ≠ n

public theorem ω.zero_lt {n : ω} : n ≠ 0 → 0 < n := by
  intro h₂
  symm at h₂
  have h₁ : 0 ≤ n := zero_le n
  exact ⟨h₁, h₂⟩

theorem ω.zero_lt_one : (0 : ω) < 1 := by
  exact zero_lt one_ne_zero

public theorem ω.lt_iff {m n : ω} : m < n ↔ ∃ k : ω, k ≠ 0 ∧ n = m + k := by
  constructor

  intro m_lt_n
  obtain ⟨m_le_n, m_ne_n⟩ := m_lt_n
  obtain ⟨k, hk⟩ := m_le_n
  have k_ne_0 : k ≠ 0 := by
    intro k_eq_0
    rw [k_eq_0, add_zero] at hk
    symm at hk
    contradiction
  exists k

  intro h
  obtain ⟨k, ⟨k_ne_0, hk⟩⟩ := h
  have m_le_n : m ≤ n := by
    exists k
  have m_ne_n : m ≠ n := by
    intro m_eq_n
    rw [m_eq_n, ← add_zero n, add_assoc, zero_add] at hk
    have thus : 0 = k := by
      exact cancel_add hk
    symm at thus
    contradiction
  exact ⟨m_le_n, m_ne_n⟩

theorem ω.lt_succ (n : ω) : n < n.succ := by
  have h₁ : n ≤ n.succ := by
    rw [succ_def]
    exists 1
  have h₂ : n ≠ n.succ := ne_succ n
  exact ⟨h₁, h₂⟩

public theorem ω.lt_then_succ_le {m n : ω} : n < m → n.succ ≤ m := by
  intro h
  obtain ⟨k, ⟨k_ne_0, m_eq_nk⟩⟩ := lt_iff.mp h
  obtain ⟨l, hl⟩ := one_le.mp k_ne_0
  rw [hl, ← add_assoc] at m_eq_nk
  rw [succ_def]
  exists l

theorem ω.le_then_lt_or_eq {m n : ω} : m ≤ n → m < n ∨ m = n := by
  intro h
  obtain ⟨k, hk⟩ := h
  cases k
  case zero =>
    rw [zero_def, add_zero] at hk
    right
    symm
    assumption
  case succ k =>
    let nonzero : k.succ ≠ 0 := succ_nonzero k
    left
    apply lt_iff.mpr
    exists k.succ

public theorem ω.le_iff {m n : ω} : m ≤ n ↔ m < n ∨ m = n := by
  constructor
  exact le_then_lt_or_eq
  intro h
  cases h
  case inl m_lt_n => exact m_lt_n.left
  case inr m_eq_n => exact eq_then_le m_eq_n

public theorem ω.le_dichotomy {m n : ω} : m ≤ n ∨ n ≤ m := by
  induction n
  case zero =>
    rw [zero_def]
    right
    exact zero_le m
  case succ n hn =>
    rw [succ_def]
    cases hn
    case inl m_le_n =>
      left
      obtain ⟨k, hk⟩ := m_le_n
      exists k+1
      rw [← add_assoc, hk]
    case inr n_le_m =>
      cases le_iff.mp n_le_m
      case inl n_lt_m =>
        right
        have thus : n.succ ≤ m := lt_then_succ_le n_lt_m
        rw [succ_def] at thus
        assumption
      case inr n_eq_m =>
        left
        rw [n_eq_m]
        exists 1

public theorem ω.not_le {m n : ω} : ¬ m ≤ n ↔ n < m := by
  constructor

  intro h
  have n_le_m : n ≤ m := le_dichotomy.resolve_left h
  have n_ne_m : n ≠ m := by
    intro h
    have m_le_n : m ≤ n := by exists 0
    contradiction
  exact ⟨n_le_m, n_ne_m⟩

  intro h
  obtain ⟨n_le_m, n_ne_m⟩ := h
  intro m_le_n
  have n_eq_m : n = m := le_antisymm n_le_m m_le_n
  contradiction

public theorem ω.lt_trichotomy {m n : ω} : m < n ∨ m = n ∨ n < m := by
  cases le_dichotomy
  case inl m_le_n =>
    have thus : m < n ∨ m = n := le_iff.mp m_le_n
    cases thus
    case inl m_lt_n => left; assumption
    case inr m_eq_n => right; left; assumption
  case inr n_le_m =>
    have thus : n < m ∨ n = m := le_iff.mp n_le_m
    cases thus
    case inl n_lt_m => right; right; assumption
    case inr n_eq_m => right; left; symm; assumption

public theorem ω.not_lt {m n : ω} : ¬ m < n ↔ n ≤ m := by
  constructor

  intro h
  have h : m = n ∨ n < m := lt_trichotomy.resolve_left h
  cases h
  case inl heq => symm at heq; exact eq_then_le heq
  case inr evident => exact evident.left

  intro n_le_m
  intro m_lt_n
  obtain ⟨m_le_n, m_ne_n⟩ := m_lt_n
  have n_eq_m : m = n := le_antisymm m_le_n n_le_m
  contradiction

public theorem ω.eq_or_not (m n : ω) : m = n ∨ m ≠ n := by
  let trichotomy : m < n ∨ m = n ∨ n < m := lt_trichotomy
  cases trichotomy
  case inl not_eq => right; exact not_eq.right
  case inr maybe =>
    cases maybe
    case inl equal => left; assumption
    case inr not_eq => right; symm; exact not_eq.right

public theorem ω.no_in_between (x : ω) : ¬ ∃ y : ω, x < y ∧ y < x + 1 := by
  simp
  intro y x_lt_y
  have thus : x + 1 ≤ y := by
    rw [← succ_def]
    exact lt_then_succ_le x_lt_y
  exact not_lt.mpr thus

public theorem ω.no_in_between₂ (x y : ω) : y ≤ x ∨ x + 1 ≤ y := by
  have trichotomy : y < x ∨ y = x ∨ x < y := lt_trichotomy
  cases or_assoc.mpr trichotomy
  case inl y_le_x  =>
    left
    exact le_iff.mpr y_le_x
  case inr x_lt_y =>
    right
    rw [← succ_def]
    exact lt_then_succ_le x_lt_y

/- ============================= MULTIPLICATION ============================= -/

public def ω.mul (m n : ω) :=
  match m,n with
  | _, zero => 0
  | m, succ n => (mul m n) + m

public instance : Mul ω where
  mul := ω.mul

public theorem ω.mul_zero (n : ω) : n * 0 = 0 := by
  rfl

theorem ω.mul_succ (m n : ω) : m * (n + 1) = m * n + m := by
  rw [← succ_def]
  rfl

theorem ω.succ_mul (m n : ω) : (m + 1) * n = m * n + n := by
  induction n
  case zero => rfl
  case succ n h =>
  rw [
    succ_def, mul_succ, mul_succ, h, add_assoc, add_assoc,
    ← add_assoc m n, add_comm m n, add_assoc
  ]

public theorem ω.mul_one (n : ω) : n * 1 = n := by
  have by_def : n * ω.succ 0 = n * 0 + n := rfl
  rw [← zero_add 1, ← succ_def, by_def, mul_zero, zero_add]

public theorem ω.zero_mul (n : ω) : 0 * n = 0 := by
  induction n
  case zero => rfl
  case succ n h =>
  have by_def : 0 * ω.succ n = 0 * n + 0 := rfl
  rw [by_def, add_zero]
  assumption

public theorem ω.mul_comm (m n : ω) : m * n = n * m := by
  induction n
  case zero =>
    rw [zero_def, zero_mul]
    rfl
  case succ n h =>
    rw [succ_def, mul_succ, succ_mul, h]

public theorem ω.one_mul (n : ω) : 1 * n = n := by
  rw [mul_comm, mul_one]

public theorem ω.mul_add (m n k : ω) : m * (n + k) = m * n + m * k := by
  induction k
  case zero => rfl
  case succ k h =>
  rw [succ_def, mul_succ, ← add_assoc, mul_succ, h, ← add_assoc]

public theorem ω.add_mul (m n k : ω) : (m + n) * k = m * k + n * k := by
  rw [mul_comm, mul_add, mul_comm k, mul_comm k]

public theorem ω.mul_assoc (m n k : ω) : (m * n) * k = m * (n * k) := by
  induction k
  case zero => rfl
  case succ k h =>
  rw [succ_def, mul_succ, mul_succ, mul_add, h]

public theorem ω.mul_eq_zero {m n : ω} : m * n = 0 → m = 0 ∨ n = 0 := by
  intro h
  cases n
  case zero => rw [zero_def]; right; rfl
  case succ n =>
    left
    rw [succ_def, mul_add, mul_one] at h
    apply sum_zero_right h

public theorem ω.nonzero_mul {m n : ω} : m ≠ 0 → n ≠ 0 → m * n ≠ 0 := by
  intro hm hn hmn
  cases mul_eq_zero hmn
  case inl _ => contradiction
  case inr _ => contradiction

public theorem ω.le_mul {a b c d : ω}
  (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := by

  obtain ⟨k₁, h₁⟩ := h₁
  obtain ⟨k₂, h₂⟩ := h₂
  rw [h₁, h₂, add_mul, mul_add, mul_add, add_assoc]
  exists (a * k₂ + (k₁ * c + k₁ * k₂))

public theorem ω.le_mul_cancel {m n k : ω}
  (k_ne_0 : k ≠ 0) (h : m * k ≤ n * k) : m ≤ n := by
  apply not_lt.mp
  intro n_le_m -- we prove that n < m is a contradiction
  obtain ⟨l, ⟨l_ne_0, m_eq_nl⟩⟩ := lt_iff.mp n_le_m
  have thus : m * k = n * k + l * k := by
    rw [m_eq_nl, add_mul]
  have lk_ne_0 : l * k ≠ 0 := nonzero_mul l_ne_0 k_ne_0
  have therefore : ∃ x : ω, x ≠ 0 ∧ m * k = n * k + x := by
    exists l * k
  rw [← lt_iff, ← not_le] at therefore
  contradiction

public theorem ω.le_cancel_mul {m n k : ω}
  (hk : k ≠ 0) (h : k * m ≤ k * n) : m ≤ n := by

  rw [mul_comm k m, mul_comm k n] at h
  exact le_mul_cancel hk h

public theorem ω.mul_cancel {m n k : ω} : k ≠ 0 → m * k = n * k → m = n := by
  intro hk
  intro h
  have mk_le_nk : m * k ≤ n * k := eq_then_le h
  have m_le_n : m ≤ n := le_mul_cancel hk mk_le_nk
  have nk_le_mk : n * k ≤ m * k := by
    symm at h
    exact eq_then_le h
  have n_le_m := le_mul_cancel hk nk_le_mk
  exact le_antisymm m_le_n n_le_m

public theorem ω.cancel_mul {m n k : ω} : k ≠ 0 → k * m = k * n → m = n := by
  intro hk
  intro h
  rw [mul_comm k m, mul_comm k n] at h
  exact mul_cancel hk h

public theorem ω.super_amazing_theorem : 1 + 1 = (2 : ω) := by
  rw [← succ_def]
  rfl

public theorem ω.two_mul (n : ω) : 2 * n = n + n := by
  rw [← super_amazing_theorem, add_mul, one_mul]

public theorem ω.two_ne_zero : (2 : ω) ≠ 0 := by
  have this := succ_nonzero 1
  have that : succ 1 = 2 := rfl
  rw [that] at this
  assumption

public theorem ω.one_is_unique {k n : ω} : k * n = n → n ≠ 0 → k = 1 := by
  intro kn_eq_n n_ne_0
  cases k
  case zero =>
    rw [zero_def, zero_mul] at kn_eq_n
    symm at kn_eq_n
    contradiction
  case succ k =>
    rw [succ_def, succ_mul] at kn_eq_n
    have kn_eq_0 : k * n = 0 := cancel_add_eq_zero kn_eq_n
    have k_eq_0 : k = 0 := (mul_eq_zero kn_eq_0).resolve_right n_ne_0
    rw [k_eq_0]
    rfl

/- ================================= PARITY ================================= -/

public def Even (n : ω) := ∃ x : ω, n = 2 * x

public def Odd (n : ω) := ∃ x : ω, n = 2 * x + 1

theorem ω.zero_is_even : Even 0 := by
  exists 0

theorem ω.zero_is_not_odd : ¬ Odd 0 := by
  intro suppose_it_is
  obtain ⟨x, h⟩ := suppose_it_is
  symm at h
  have thus : (1 : ω) = 0 := sum_zero_right h
  have yet : (1 : ω) ≠ 0 := one_ne_zero
  contradiction

public theorem ω.even_iff_succ_odd {n : ω} : Even n ↔ Odd (n + 1) := by
  constructor

  intro h
  obtain ⟨x, even_n⟩ := h
  exists x
  rw [even_n]

  intro h
  obtain ⟨x, odd_succ⟩ := h
  exists x
  apply add_cancel
  assumption

public theorem ω.odd_iff_succ_even {n : ω} : Odd n ↔ Even (n + 1) := by
  constructor

  intro h
  obtain ⟨x, odd_n⟩ := h
  exists x + 1
  rw [mul_add, two_mul 1, ← add_assoc, odd_n]

  intro h
  obtain ⟨x, hx⟩ := h
  cases x
  case zero =>
    rw [zero_def, mul_zero, ← succ_def] at hx
    have yet : n.succ ≠ 0 := succ_nonzero n
    contradiction
  case succ x =>
  rw [succ_def, mul_add, mul_one] at hx
  rw [two_mul, ← super_amazing_theorem, ← two_mul] at hx -- janky, i know
  rw [← add_assoc] at hx
  exists x
  apply add_cancel
  assumption

public theorem ω.even_or_odd (n : ω) : Even n ∨ Odd n := by
  induction n
  case zero => rw [zero_def]; left; exact zero_is_even
  case succ n hn =>
    cases hn
    case inl even_n => right; exact even_iff_succ_odd.mp even_n
    case inr odd_n  => left;  exact odd_iff_succ_even.mp odd_n

public theorem ω.not_even {n : ω} : ¬ Even n ↔ Odd n := by
  constructor
  exact (even_or_odd n).resolve_left
  induction n
  case zero =>
    intro assume_odd
    have yet := zero_is_not_odd
    contradiction
  case succ n hn =>
    intro odd_succ
    intro even_succ
    rw [succ_def] at odd_succ
    rw [succ_def] at even_succ
    have odd_n : Odd n := odd_iff_succ_even.mpr even_succ
    have even_n : Even n := even_iff_succ_odd.mpr odd_succ
    have not_even_n : ¬ Even n := hn odd_n
    contradiction

public theorem ω.not_odd {n : ω} : ¬ Odd n ↔ Even n := by
  constructor
  exact (even_or_odd n).resolve_right
  induction n
  case zero => intro _; exact zero_is_not_odd
  case succ n hn =>
    intro even_succ
    intro odd_succ
    rw [succ_def] at even_succ
    rw [succ_def] at odd_succ
    have even_n : Even n := even_iff_succ_odd.mpr odd_succ
    have odd_n : Odd n := odd_iff_succ_even.mpr even_succ
    have not_odd_n : ¬ Odd n := hn even_n
    contradiction

/- =============================== DECIDABLE ================================ -/

public def ω.ble : ω → ω → Bool
  | zero,   _      => true
  | succ _, zero   => false
  | succ n, succ m => ble n m

public theorem ω.ble_iff_le (m n : ω) : ω.ble m n ↔ m ≤ n := by
  induction m generalizing n
  case zero =>
    constructor
    intro _
    exists n
    rw [zero_def, zero_add]
    intro _
    trivial
  case succ m ih =>
    cases n
    case zero =>
      constructor
      intro h
      contradiction
      rw [zero_def]
      intro h
      have yet : 0 ≤ m.succ := zero_le m.succ
      have thus : m.succ = 0 := le_antisymm h yet
      have but : m.succ ≠ 0 := succ_nonzero m
      contradiction
    case succ n =>
      constructor
      intro h
      have thus : m ≤ n := (ih n).mp h
      exact succ_le_succ thus
      intro h
      rw [succ_def, succ_def] at h
      have thus : m ≤ n := le_add_cancel h
      have therefore := (ih n).mpr thus
      trivial

public instance (m n : ω) : Decidable (ω.ble m n) :=
  if h : ω.ble m n then isTrue h else isFalse h
