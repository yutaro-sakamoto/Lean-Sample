import data.int.basic
import data.nat.basic

namespace Section4_2
  variables x y z : ℤ

  example (x y z : ℕ) : x * (y + z) = x * y + x * z :=
    mul_add x y z
  example (x y z : ℕ) : (x + y) * z = x * z + y * z :=
    add_mul x y z
  example (x y z : ℕ) : x + y + z = x + (y + z) :=
    add_assoc x y z
  
  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
    from mul_add (x + y) x y,
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
    from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
  h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm
end Section4_2

namespace Section4_3
  variables (a b c d e: ℕ)
  variable h1 : a = b
  variable h2 : b = c + 1
  variable h3 : c = d
  variable h4 : e = 1 + d

  theorem T : a = e :=
  calc
    a   = b : h1
    ... = c + 1 : h2
    ... = d + 1 : congr_arg _ h3
    ... = 1 + d : add_comm d (1 : ℕ)
    ... = e     : eq.symm h4
  

  include h1 h2 h3 h4
  theorem T2 : a = e :=
  calc
    a     = b      : by rw h1
      ... = c + 1  : by rw h2
      ... = d + 1  : by rw h3
      ... = 1 + d  : by rw add_comm
      ... =  e     : by rw h4
  
  theorem T3 : a = e :=
  calc
    a     = d + 1 : by rw [h1, h2, h3]
      ... = 1 + d : by rw add_comm
      ... = e : by rw h4
  
  theorem T4 : a = e :=
  by rw [h1, h2, h3, add_comm, h4]

  theorem T5: a = e :=
  by rw [h1, h2, h3, h4, add_comm]

end Section4_3

namespace Section4_3_1
  theorem TT2 (a b c d : ℕ)
    (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a     = b     : h1
      ... < b + 1 : nat.lt_succ_self b
      ... ≤ c + 1 : nat.succ_le_succ h2
      ... < d     : h3
  
  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  : by rw mul_add
      ... = x * x + y * x + (x + y) * y            : by rw add_mul
      ... = x * x + y * x + (x * y + y * y)        : by rw add_mul
      ... = x * x + y * x + x * y + y * y          : by rw ←add_assoc

  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [mul_add, add_mul, add_mul, ←add_assoc]

  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [mul_add, add_mul, add_assoc, add_left_comm]
end Section4_3_1

namespace Section4_4
  open nat

  example : ∃ x : ℕ, x > 0 :=
  have h : 1 > 0, from zero_lt_succ 0,
  exists.intro 1 h

  example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
  exists.intro 0 h

  example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
    exists.intro y (and.intro hxy hyz)
  
  #check @exists.intro

  example : ∃ x : ℕ, x > 0 :=
  ⟨1, zero_lt_succ 0⟩

  example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

  example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

  variable g : ℕ → ℕ → ℕ
  variable hg : g 0 0 = 0

  theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.implicit true
  #print gex1
  #print gex2
  #print gex3
  #print gex4

  variables (α : Type*) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  exists.elim h
    (assume w,
      assume hw : p w ∧ q w,
      show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)
  
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, hw⟩ :=
    ⟨w, hw.right, hw.left⟩
  end

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨(w : α), (hw : p w ∧ q w)⟩ :=
    ⟨w, hw.right, hw.left⟩
  end

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, hpw, hqw⟩ :=
    ⟨w, hqw, hpw⟩
  end

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

  example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩

  def is_even (a : nat) := ∃ b, a = 2 * b

  theorem even_plus_even {a b : nat}
    (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  exists.elim h1 (assume w1, assume hw1 : a = 2 * w1,
  exists.elim h2 (assume w2, assume hw2 : b = 2 * w2,
    exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2 : by rw [hw1, hw2]
          ... = 2 * (w1 + w2)   : by rw mul_add)))
  
  theorem even_plus_even2 {a b : nat}
    (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    match h1, h2 with
      ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
    end
  
  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  by_contradiction
    (assume h1 : ¬ ∃ x, p x,
      have h2 : ∀ x, ¬ p x, from
        assume x,
        assume h3 : p x,
        have h4 : ∃ x, p x, from ⟨x, h3⟩,
        show false, from h1 h4,
      show false, from h h2)
end Section4_4

namespace Section4_5
  variable f : ℕ → ℕ
  variable h : ∀ x : ℕ, f x ≤ f (x + 1)
  
  example : f 0 ≤ f 3 :=
  have f 0 ≤ f 1, from h 0,
  have f 0 ≤ f 2, from le_trans this (h 1),
  show f 0 ≤ f 3, from le_trans this (h 2)

  example : f 0 ≤ f 3 :=
  have f 0 ≤ f 1, from h 0,
  have f 0 ≤ f 2, from le_trans (by assumption) (h 1),
  show f 0 ≤ f 3, from le_trans (by assumption) (h 2)

  example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
    assume : f 0 ≥ f 1,
    assume : f 1 ≥ f 2,
    have f 0 ≥ f 2, from le_trans this ‹f 0 ≥ f 1›,
    have f 0 ≤ f 2, from le_trans (h 0) (h 1),
    show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›
  
  example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 1 ≤ f 2, from h 1,
    have f 2 ≤ f 3, from h 2,
    show f 0 ≤ f 3, from le_trans ‹f 0 ≤ f 1›
                           (le_trans ‹f 1 ≤ f 2› ‹f 2 ≤ f 3›)
  example (n : ℕ) : ℕ := ‹ℕ›

  example : f 0 ≥ f 1 → f 0 = f 1 :=
  assume : f 0 ≥ f 1,
  show f 0 = f 1, from le_antisymm (h 0) this

  example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  assume : f 0 ≥ f 1,
  assume : f 1 ≥ f 2,
  have f 0 ≥ f 2, from le_trans ‹f 2 ≤ f 1› ‹f 1 ≤ f 0›,
  have f 0 ≤ f 2, from le_trans (h 0) (h 1),
  show f 0 = f 2, from le_antisymm ‹f 0 ≤ f 2› ‹f 0 ≥ f 2›
end Section4_5

namespace Section5_1
  theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  begin
    apply and.intro,
    exact hp,
    apply and.intro,
    exact hq,
    exact hp
  end

  theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  begin
    apply and.intro hp,
    exact and.intro hq hp
  end

  theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  begin
    apply and.intro hp; exact and.intro hq hp
  end
  #print test3

  theorem test4 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by exact and.intro hp (and.intro hq hp)

  namespace sub
    variables {p q : Prop} (hp : p) (hq : q)
    include hp hq
    example : p ∧ q ∧ p :=
    begin
      apply and.intro hp,
      exact and.intro hq hp
    end
  end sub

  variables {p q : Prop} (hp : p) (hq : q)

  example : p ∧ q ∧ p :=
  let hp := hp, hq := hq in
  begin
    apply and.intro hp,
    exact and.intro hq hp
  end
end Section5_1

namespace Section5_2
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
      intro h,
      apply or.elim (and.right h),
        intro hq,
        apply or.inl,
        apply and.intro,
          exact and.left h,
        exact hq,
      intro hr,
      apply or.inr,
      apply and.intro,
        exact and.left h,
      exact hr,
    intro h,
    apply or.elim h,
      intro hpq,
      apply and.intro,
        exact and.left hpq,
      apply or.inl,
      exact and.right hpq,
    intro hpr,
    apply and.intro,
      exact and.left hpr,
    apply or.inr,
    exact and.right hpr
  end

  example (α : Type*) : α → α :=
  begin
    intro a,
    exact a
  end

  example : ∀ a b c : ℕ, a = b → a = c → c = b :=
  begin
    intros a b c h₁ h₂,
    exact eq.trans (eq.symm h₂)  h₁
  end

  variables x y z w : ℕ

  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
  begin
    apply eq.trans h₁,
    apply eq.trans h₂,
    assumption
  end

  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
  begin
    apply eq.trans,
    assumption,
    apply eq.trans,
    assumption,
    assumption
  end

  example : ∀ a b c : ℕ, a = b → a = c → c = b :=
  begin
    intros,
    apply eq.trans,
    apply eq.symm,
    assumption,
    assumption
  end

  example (y : ℕ) : (λ x : ℕ, 0) y = 0 :=
  begin
    refl
  end

  example (x : ℕ) : x ≤ x :=
  begin
    refl
  end

  example : ∀ a b c : ℕ, a = b → a = c → c = b :=
  begin
    intros a b c h₁ h₂,
    transitivity a,
    symmetry,
    assumption,
    assumption,
  end

  example : ∀ a b c : ℕ, a = b → a = c → c = b :=
  begin
    intros,
    transitivity,
    symmetry,
    assumption,
    assumption
  end

  example : ∀ a b c : ℕ, a = b → a = c → c = b :=
  begin
    intros a b c h₁ h₂,
    transitivity a,
    symmetry,
    assumption,
    assumption
  end

  example : ∀ a b c : ℕ, a = b → a = c → c = b :=
  begin
    intros a b c h₁ h₂,
    transitivity a,
    symmetry,
    repeat {assumption},
  end

  example : ∃ a : ℕ, 5 = a :=
  begin
    apply exists.intro,
    reflexivity
  end

  example : ∃ a : ℕ, a = a :=
  begin
    fapply exists.intro,
    exact 0,
    reflexivity
  end

  example (x : ℕ) : x = x :=
  begin
    revert x,
    intro y,
    reflexivity
  end

  example (x y : ℕ) (h : x = y) : y = x :=
  begin
    revert h,
    intro h₁,
    symmetry,
    assumption
  end

  example (x y : ℕ) (h : x = y) : y = x :=
  begin
    revert x,
    intros,
    symmetry,
    assumption
  end
  example (x y : ℕ) (h : x = y) : y = x :=
  begin
    revert x y,
    intros,
    symmetry,
    assumption
  end

  example : 3 = 3 :=
  begin
    generalize : 3 = x,
    revert x,
    intro y,
    reflexivity
  end

  example : 2 + 3 = 5 :=
  begin
    generalize h : 3 = x,
    rw ←h
  end

  example : 2 + 3 = 5 :=
  begin
    reflexivity
  end
end Section5_2

namespace Section5_3
  example (p q : Prop) : p ∨ q → q ∨ p :=
  begin
    intro h,
    cases h with hp hq,
    -- case hp : p
    right, exact hp,
    -- case hq : q
    left, exact hq
  end

  example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro h,
    cases h with hp hq,
    constructor, exact hq, exact hp
  end

  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
    intro h,
      cases h with hp hqr,
      cases hqr with hq hr,
        left, constructor, repeat { assumption },
        right, constructor, repeat { assumption },
    intro h,
      cases h with hpq hpr,
        cases hpq with hp hq,
          constructor, exact hp, left, exact hq,
        cases hpr with hp hr,
          constructor, exact hp, right, exact hr
  end

  example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
  begin
    intro h,
    cases h with x px,
    constructor, left, exact px,
  end
  example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
  begin
    intro h,
    cases h with x px,
    existsi x, left, exact px,
  end

  example (p q : ℕ → Prop) :
    (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  begin
    intro h,
    cases h with x hpq,
    cases hpq with hp hq,
    existsi x,
    split; assumption
  end

  universes u v

  def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
  begin
    intro p,
    cases p with ha hb,
    constructor, exact hb, exact ha
  end

  def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
  begin
    intro p,
    cases p with ha hb,
      right, exact ha,
      left, exact hb
  end

  open nat

  example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) :
    P m :=
  begin
    cases m with m', exact h₀, exact h₁ m'
  end

  example (p q : Prop) : p ∧ ¬ p → q :=
  begin
    intro h, cases h, contradiction
  end
end Section5_3