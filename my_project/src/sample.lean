import data.int.basic
import data.nat.basic
import data.list.basic

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

namespace Section5_4
  example (p q r : Prop) : p ∧ (q ∨ r ) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    exact
      have hp : p, from h.left,
      have hqr : q ∨ r, from h.right,
      show (p ∧ q) ∨ (p ∧ r),
      begin
        cases hqr with hq hr,
          exact or.inl ⟨hp, hq⟩,
        exact or.inr ⟨hp, hr⟩
      end
  end

  example (p q r : Prop) : p ∧ (q ∨ r ) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
      intro h,
      cases h.right with hq hr,
        exact or.inl ⟨h.left, hq⟩,
      exact or.inr ⟨h.left, hr⟩,
    intro h,
    cases h with hpq hpr,
      exact ⟨hpq.left, or.inl hpq.right⟩,
    exact ⟨hpr.left, or.inr hpr.right⟩
  end

  example (p q r : Prop) : p ∧ (q ∨ r ) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
      intro h,
      cases h.right with hq hr,
        show (p ∧ q) ∨ (p ∧ r),
          from or.inl ⟨h.left, hq⟩,
        show (p ∧ q) ∨ (p ∧ r),
          from or.inr ⟨h.left, hr⟩,
    intro h,
    cases h with hpq hpr,
      show p ∧ (q ∨ r),
        from ⟨hpq.left, or.inl hpq.right⟩,
      show p ∧ (q ∨ r),
        from ⟨hpr.left, or.inr hpr.right⟩,
  end


  example (p q r : Prop) : p ∧ (q ∨ r ) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
      intro h,
      cases h.right with hp hr,
        show (p ∧ q) ∨ (p ∧ r),
          { left, split, exact h.left, assumption },
        show (p ∧ q) ∨ (p ∧ r),
          { right, split, exact h.left, assumption },
    intro h,
    cases h with hpq hpr,
      show p ∧ (q ∨ r),
        { cases hpq, split, assumption, left, assumption},
      show p ∧ (q ∨ r),
        { cases hpr, split, assumption, right, assumption}
  end

  example (n : ℕ) : n + 1 = nat.succ n :=
  begin
    show nat.succ n = nat.succ n,
    reflexivity
  end

  example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro h,
    cases h with hp hq,
    split,
    show q, from hq,
    show p, from hp,
  end

  example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro h,
    cases h with hp hq,
    split,
    show p, from hp,
    show q, from hq
  end

  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
      have hpq : p ∧ q,
        from and.intro hp hq,
      left, exact hpq,
    have hpr : p ∧ r,
      from ⟨hp, hr⟩,
    right, exact hpr
  end

  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
      have hpq : p ∧ q,
        split; assumption,
      left, exact hpq,
    have hpr : p ∧ r,
      split; assumption,
    right, exact hpr
  end

  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
      have : p ∧ q,
        split; assumption,
      left, exact this,
    have : p ∧ r,
      split; assumption,
    right, exact this
  end

  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    have hp : p := h.left,
    have hqr : q ∨ r := h.right,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
      exact or.inl ⟨hp, hq⟩,
    exact or.inr ⟨hp, hr⟩,
  end

  example : ∃ x, x + 2 = 8 :=
  begin
    let a : ℕ := 3 * 2,
    existsi a,
    reflexivity
  end

  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
    begin
    intro h,
    cases h.right with hq hr,
    begin
      show (p ∧ q) ∨ (p ∧ r),
        exact or.inl ⟨h.left, hq⟩
    end,
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩
  end,
  intro h,
  cases h with hpq hpr,
  begin
    show p ∧ (q ∨ r),
      exact ⟨hpq.left, or.inl hpq.right⟩
  end,
  show p ∧ (q ∨ r),
    exact ⟨hpr.left, or.inr hpr.right⟩
  end

  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
    {
    intro h,
    cases h.right with hq hr,
    {
      show (p ∧ q) ∨ (p ∧ r),
        exact or.inl ⟨h.left, hq⟩
    },
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩
    },
  intro h,
  cases h with hpq hpr,
  {
    show p ∧ (q ∨ r),
      exact ⟨hpq.left, or.inl hpq.right⟩
  },
  show p ∧ (q ∨ r),
    exact ⟨hpr.left, or.inr hpr.right⟩
  end

  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
    { intro h,
      cases h.right with hq hr,
      { show (p ∧ q) ∨ (p ∧ r),
        exact or.inl ⟨h.left, hq⟩ },
      { show (p ∧ q) ∨ (p ∧ r),
        exact or.inr ⟨h.left, hr⟩}},
    { intro h,
      cases h with hpq hpr,
    { show p ∧ (q ∨ r),
      exact ⟨hpq.left, or.inl hpq.right⟩ },
    { show p ∧ (q ∨ r),
      exact ⟨hpr.left, or.inr hpr.right⟩}}
  end

  example (p q : Prop) : p ∧ q ↔ q ∧ p :=
  begin
    apply iff.intro,
    { intro h,
      have hp : p := h.left,
      have hq : q := h.right,
      show q ∧ p,
        exact ⟨hq, hp⟩ },
    { intro h,
      have hp : p := h.right,
      have hq : q := h.left,
      show p ∧ q,
        exact ⟨hp, hq⟩ }
  end
end Section5_4

namespace Section5_5
  example (p q : Prop) (hp : p) : p ∨ q :=
  begin left, assumption end

  example (p q : Prop) (hp : p) : p ∨ q :=
  by { left, assumption }

  example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by split; assumption

  example (p q : Prop) (hp : p) : p ∨ q :=
  by { left, assumption } <|> { right, assumption }

  example (p q : Prop) (hq : q) : p ∨ q :=
  by { left, assumption } <|> { right, assumption }

  example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat { {left, assumption} <|> right <|> assumption }

  example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat { {left, assumption} <|> right <|> assumption }

  example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat { {left, assumption} <|> right <|> assumption }

  meta def my_tac : tactic unit :=
  `[ repeat { {left, assumption} <|> right <|> assumption } ]

  example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by my_tac

  example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by my_tac

  example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by my_tac

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
  by split; try {split}; assumption

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
  begin
  split,
  all_goals { try {split} },
  all_goals { assumption }
  end

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
  begin
    split,
    any_goals { split },
    any_goals { assumption }
  end

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
  begin
    repeat {any_goals {split}},
    all_goals { assumption }
  end

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
  by repeat { any_goals { split <|> assumption }}
end Section5_5

namespace Section5_6
  variables (f : ℕ → ℕ) (k : ℕ)

  example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  begin
    rw h₂,
    rw h₁
  end

  example (x y : ℕ) (p : ℕ → Prop) (q : Prop) (h : q → x = y)
    (h' : p y) (hq : q) : p x :=
  by { rw (h hq), assumption }

  example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  by rw [h₂, h₁]

  variables (a b : ℕ)
  example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 :=
  begin
    rw [←h₁, h₂]
  end

  example (a b c: ℕ) : a + b + c = a + c + b :=
  begin
    rw [add_assoc, add_comm b, ←add_assoc]
  end

  example (a b c: ℕ) : a + b + c = a + c + b :=
  begin
    rw [add_assoc, add_assoc, add_comm b]
  end

  example (a b c: ℕ) : a + b + c = a + c + b :=
  begin
    rw [add_assoc, add_assoc, add_comm _ b]
  end

  example (h : a + 0 = 0) : f a = f 0 :=
  by { rw add_zero at h, rw h}

  def tuple (α : Type*) (n : ℕ) :=
    { l : list α // l.length = n}
  
  variables {α : Type*} {n : ℕ}
  example (h : n = 0) (t : tuple α n) : tuple α 0 :=
  begin
    rw h at t,
    exact t
  end
end Section5_6

namespace Section5_7
  variables (x y z : ℕ) (p : ℕ → Prop)
  variable (h : p (x * y))

  example : (x + 0) * (0 + y * 1 + z * 0) = x * y :=
  by simp

  include h
  example : p ((x + 0) * (0 + y * 1 + z * 0)) :=
  by { simp, assumption }

  variable {α : Type*}
  open list

  example (xs : list ℕ) :
    reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs :=
  by simp

  example (xs ys : list α) :
    length (reverse (xs ++ ys)) = length xs + length ys :=
  by simp [add_comm]

  example (h : p ((x + 0) * (0 + y * 1 + z * 0))) :
    p (x * y) :=
  by { simp at h, assumption }

  variables {w : ℕ} [comm_ring α]
  local attribute [simp] mul_comm mul_assoc mul_left_comm
  local attribute [simp] add_assoc add_comm add_left_comm

  example (h : p (x * y + z * w * x)) : (x - x) * y + z = z :=
  begin simp end

end Section5_7

namespace Section5_7_1

  def f (m n : ℕ) : ℕ := m + n + m

  example {m n : ℕ} (h : n = 1) (h' : 0 = m) : (f m n) = n :=
  by simp [h, h'.symm, f]

  variables (f : ℕ → ℕ) (k : ℕ)
  example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  by simp [h₁, h₂]

  example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  by simp *

  example (u w x y z : ℕ) (h₁ : x = y + z) (h₂ : w = u + x) :
    w = z + y + u :=
  by simp [*, add_assoc, add_comm, add_left_comm]

  variables (p q r : Prop)

  example (hp : p) : p ∧ q ↔ q :=
  by simp *

  example (hp : p) : p ∨ q :=
  by simp *

  example (hp : p) (hq : q) : p ∧ (q ∨ r) :=
  by simp *
end Section5_7_1

namespace Section5_7_2
  variables (u w x x' y y' z : ℕ) (p : ℕ → Prop)
  example (h₁ : x + 0 = x') (h₂ : y + 0 = y') :
    x + y + 0 = x' + y' :=
  by { simp at *, simp * }


end Section5_7_2

namespace Section5_7_3
  open list
  variables {α : Type*} (x y z : α) (xs ys zs : list α)

  def mk_symm (xs : list α) := xs ++ reverse xs

  theorem reverse_mk_symm (xs : list α) :
    reverse (mk_symm xs) = mk_symm xs :=
  by simp [mk_symm]
  
  section
  local attribute [simp] reverse_mk_symm

  example (xs ys : list ℕ) : 
    reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
  by simp

  example (xs ys : list ℕ) (p :list ℕ → Prop)
      (h : p (reverse (xs ++ (mk_symm ys)))) :
    p (mk_symm ys ++ reverse xs) :=
  by simp at h; assumption
  end

  run_cmd mk_simp_attr `my_simps

  attribute [my_simps] reverse_mk_symm

  example (xs ys : list ℕ) :
    reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
  by simp with my_simps

  example (xs ys : list ℕ) (p : list ℕ → Prop)
    (h : p (reverse (xs ++ (mk_symm ys)))) :
      p (mk_symm ys ++ reverse xs) :=
  by simp with my_simps at h; assumption
end Section5_7_3