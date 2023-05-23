constant m: nat -- m is a natural number
constant n: nat
constants b1 b2 : bool -- declare two constants at once

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check tt

constant f: nat → nat
constant f': nat → nat
constant p : nat × nat
constant q : prod nat nat
constant g : nat → nat → nat
constant g' : nat → (nat → nat)
constant h : nat × nat → nat

constant F: (nat → nat) → nat

#check f
#check f n
#check g m n
#check g m
#check (m, n)
#check p.1
#check p.2
#check (m, n).1
#check (p.1, n)
#check F f

namespace Section2_2
#check nat
#check bool
#check nat → bool
#check nat × bool
#check nat × nat → nat

constants α β : Type
constant F: Type → Type
constant G: Type → Type → Type
#check α
#check F α
#check F nat
#check G α
#check G α β
#check G α nat

#check prod α β
#check prod nat nat

#check list α
#check list nat

#check Type
#check Type 0
#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Prop

#check list
#check prod

universe u
-- constant aa : Type u
-- constant aa : Type _
constant aa : Type*
#check aa
end Section2_2

namespace Section2_3

#check fun x : nat, x + 5
#check λ x : nat, x + 5

constants α β γ : Type
constants a1 a2 : α
constants b1 b2 : β

constant f : α → α
constant g : α → β
constant h : α → β → α
constant p : α → α → β

#check fun x : α, f x
#check λ x : α, f x
#check λ x : α, f (f x)
#check λ (x : α) (y : β), h (f x) y

#check λ b : β, λ x : α, x
#check λ (b : β) (x : α), x
#check λ (g : β → γ) (f : α → β) (x : α), g (f x)

#check λ (α β : Type*) (b : β) (x : α), x
#check λ (α β γ : Type*) (g : β → γ) (f : α → β) (x : α), g (f x)

namespace Reduce_Section
  constants α β γ : Type
  constant f : α → β
  constant g : β → γ
  constant h : α → α
  constants (a : α) (b : β)
  
  #check (λ x : α, x) a
  #reduce (λ x : α, x) a
  
  #check (λ x : α, g (f x)) a
  #reduce (λ x : α, g (f x)) a
end Reduce_Section
#eval 12345 * 54321
end Section2_3

namespace Section2_4
def foo: (ℕ → ℕ) → ℕ := λ f, f 0

#check foo
#print foo

def foo' := λ f : ℕ → ℕ, f 0

def double (x: ℕ) : ℕ := x + x
#print double
#check double 3
#reduce double 3

def square (x : ℕ) := x * x
#print square
#check square 3
#reduce square 3

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

#reduce do_twice double 2

def compose (α β γ : Type*) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := sorry
def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := sorry
end Section2_4

namespace Section2_5
  #check let y := 2 + 2 in y * y
  #reduce let y := 2 + 2 in y * y

  def t (x: ℕ) : ℕ :=
  let y := x + x in y * y

  #reduce t 2

  #check let y := 2 + 2, z := y + y in z * z
  #reduce let y := 2 + 2, z := y + y in z * z

  def foo := let a := ℕ in λ x : a, x + 2
end Section2_5

namespace Section2_6
  def compose (α β γ: Type*) (g :β → γ) (f: α → β) (x: α) : γ := g (f x)
  def do_twice(α : Type*) (h: α → α) (x: α): α := h (h x)
  def do_thrice(α: Type*) (h: α → α) (x: α) :α := h(h(h(x)))

  namespace Sub1
    variables (α β γ: Type*)
    def compose (g :β → γ) (f: α → β) (x: α) : γ := g (f x)
    def do_twice (h: α → α) (x: α): α := h (h x)
    def do_thrice (h: α → α) (x: α) :α := h(h(h(x)))
  end Sub1

  namespace Sub2
    variables (α β γ: Type*)
    variables (g: β → γ) (f: α → β) (h: α → α)
    variable x : α

    def compose := g (f x)
    def do_twice := h (h x)
    def do_thrice := h(h(h(x)))

    #print compose
    #print do_twice
    #print do_thrice
  end Sub2

end Section2_6

section Section2_6_useful
  variables (α β γ: Type*)
  variables (g: β → γ) (f: α → β) (h: α → α)
  variable x : α

  def compose := g (f x)
  def do_twice := h (h x)
  def do_thrice := h(h(h(x)))

  #print compose
  #print do_twice
  #print do_thrice   
end Section2_6_useful

namespace hidden
  universe u
  constant list : Type u → Type u

  constant cons : Π α : Type u, α → list α → list α
  constant nil : Π α : Type u, list α
  constant head : Π α : Type u, list α
  constant tail   : Π α : Type u, list α → list α
  constant append : Π α : Type u, list α → list α → list α
end hidden

namespace Section2_8
  open list
  #check list
  #check @cons
  #check @nil
  #check @head
  #check @tail
  #check @append
end Section2_8

namespace Section2_8_1
  universe u
  constant vec : Type u → ℕ → Type u
  namespace vec
    constant empty : Π α : Type u, vec α 0
    constant cons :
      Π (α : Type u) (n: ℕ), α → vec α n → vec α (n + 1)
    constant append :
      Π (α : Type u) (n m : ℕ), vec α m → vec α n → vec α (n + m)
  end vec

  variable α : Type
  variable β : α → Type
  variable a : α
  variable b : β a

  #check sigma.mk a b
  #check (sigma.mk a b).1
  #check (sigma.mk a b).2

  #reduce (sigma.mk a b).1
  #reduce (sigma.mk a b).2
end Section2_8_1

namespace Section2_9
  namespace hidden
    universe u
    constant list : Type u → Type u
    
    namespace list
    constant cons   : Π α : Type u, α → list α → list α
    constant nil    : Π α : Type u, list α
    constant append : Π α : Type u, list α → list α → list α
    end list
  end hidden

  namespace sub1
    open hidden.list
    variable α : Type
    variable a : α
    variables l1 l2 : hidden.list α

    #check cons α a (nil α)
    #check append α (cons α a (nil α)) l1
    #check append α (append α (cons α a (nil α)) l1) l2

    #check cons _ a (nil _)
    #check append _ (cons _ a (nil _)) l1
    #check append _ (append _ (cons _ a (nil _)) l1) l2
  end sub1

  namespace sub2
    universe u
    constant cons   : Π {α : Type u}, α → list α → list α
    constant nil    : Π {α : Type u}, list α
    constant append : Π {α : Type u}, list α → list α → list α

    variable  α : Type
    variable  a : α
    variables l1 l2 : list α

    #check cons a nil
    #check append (cons a nil) l1
    #check append (append (cons a nil) l1) l2
  end sub2

  namespace sub3
    universe u
    def ident {α : Type u} (x : α) := x

    variables α β : Type u
    variables (a : α) (b : β)

    #check ident
    #check ident a
    #check ident b
  end sub3

  namespace sub4
    universe u
    section
      variable {α : Type u}
      variable x : α
      def ident := x
    end

    variables α β : Type u
    variables (a : α) (b : β)

    #check ident
    #check ident a
    #check ident b

    #check list.nil
    #check id
    #check (list.nil : list ℕ)
    #check (id : ℕ → ℕ)

    #check 2
    #check (2 : ℕ)
    #check (2 : ℤ)

    #check @id
    #check @id α
    #check @id β
    #check @id α a
    #check @id β b
  end sub4
end Section2_9

namespace Section3_1
  constant and : Prop → Prop → Prop
  constant or : Prop → Prop → Prop
  constant not : Prop → Prop
  constant implies : Prop → Prop → Prop

  variables p q r : Prop
  #check and p q
  #check or (and p q) r
  #check implies (and p q) (and q p)

  constant Proof : Prop → Type

  constant and_comm : Π p q : Prop,
    Proof (implies (and p q) (and q p))
  
  #check and_comm p q

  constant modus_ponens : Π p q : Prop,
    Proof (implies p q) → Proof p → Proof q

  constant implies_intro :
    Π p q : Prop, (Proof p → Proof q) → Proof (implies p q)
end Section3_1

namespace Section3_2
  constants p q : Prop

  theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

  #print t1

  theorem t11 : p → q → p :=
  assume hp : p,
  assume hq : q,
  hp

  theorem t12 : p → q → p :=
    assume hp : p,
    assume hq : q,
    show p, from hp

  lemma t13 : p → q → p :=
    assume hp : p,
    assume hq : q,
    show p, from hp
  
  theorem t14 (hp : p) (hq : q) : p:= hp

  axiom hp : p
  theorem t2 : q → p := t1 hp

  theorem t15 (p q : Prop) (hp : p) (hq : q) : p := hp
  #check t15

  theorem t16 : ∀ (p q : Prop), p → q → p :=
    λ (p q : Prop) (hp : p) (hq : q), hp

  variables p q : Prop
  theorem t17 : p → q → p := λ (hp : p) (hq : q), hp

  variable hp : p
  theorem t18 : q → p := λ (hq : q), hp

  theorem t19 (p q : Prop) (hp : p) (hq : q) : p := hp
  variables r s : Prop

  #check t19 p q
  #check t19 r s
  #check t19 (r → s) (s → r)

  variable h : r → s
  #check t19 (r → s) (s → r) h

  theorem t21 (h₁ : q → r) (h₂ : p → q) : p → r :=
    assume h₃ : p,
    show r, from h₁ (h₂ h₃)
end Section3_2

namespace Section3_3
  variables p q : Prop
  #check p → q → p ∧ q
  #check ¬p → p ↔ false
  #check p ∨ q → q ∨ p

  example (hp : p) (hq : q) : p ∧ q := and.intro hp hq
  #check assume (hp : p) (hq :q), and.intro hp hq

  example (h : p ∧ q) : p := and.elim_left h
  example (h: p ∧ q) : q := and.elim_right h

  example (h : p ∧ q) : q ∧ p :=
    and.intro (and.right h) (and.left h)
  
  variables (hp : p) (hq :q)
  #check (⟨hp, hq⟩ : p ∧ q)

  variable l : list ℕ
  #check list.head l
  #check l.head

  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩
  
  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, ⟨h.left, h.right⟩⟩
  
  example (h: p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, h.left, h.right⟩
  
  example (hp : p) : p ∨ q := or.intro_left q hp
  example (hq : q) : p ∨ q := or.intro_right p hq

  example (h: p ∨ q) : q ∨ p :=
    or.elim h
      (assume hp : p,
        show q ∨ p, from or.intro_right q hp)
      (assume hq : q,
        show q ∨ p, from or.intro_left p hq)
  
  example (h : p ∨ q) : q ∨ p :=
    or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)
  
  example (h : p ∨ q) : q ∨ p :=
    h.elim
      (assume hp : p, or.inr hp)
      (assume hq : q, or.inl hq)
  
  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    assume hp : p,
    show false, from hnq (hpq hp)
  
  example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)

  variables r : Prop
  example (hp : p) (hnq : ¬p) : q := absurd hp hnq
  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp
  
  theorem and_swap : p ∧ q ↔ q ∧ p :=
  iff.intro
    (assume h : p ∧ q,
      show q ∧ p, from and.intro (and.right h) (and.left h))
    (assume h : q ∧ p,
      show p ∧ q, from and.intro (and.right h) (and.left h))
  
  variable h : p ∧ q
  example : q ∧ p := iff.mp (and_swap p q) h

  theorem and_swap1 : p ∧ q ↔ q ∧ p :=
    ⟨ λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩⟩
  
  example (h : p ∧ q) : q ∧ p := (and_swap1 p q).mp h
end Section3_3

namespace Section3_4
  variables p q : Prop

  example (h: p ∧ q) : q ∧ p :=
    have hp : p, from and.left h,
    have hq : q, from and.right h,
    show q ∧ p, from and.intro hq hp
  
  example (h : p ∧ q) : q ∧ p :=
   have hp : p, from h.left,
   suffices hq : q, from ⟨hq, hp⟩,
   show q, from h.right
end Section3_4

namespace Section3_5
  open classical

  variables p q : Prop
  #check em p

  theorem dne {p: Prop} (h: ¬¬p) : p :=
  or.elim (em p)
    (assume hp : p, hp)
    (assume hnp : ¬p, absurd hnp h)
  
  example (h : ¬¬p) : p :=
    by_cases
      (assume h1 : p, h1)
      (assume h1 : ¬p, absurd h1 h)
  
  example (h : ¬¬p) : p :=
    by_contradiction
      (assume h1 : ¬p,
        show false, from h h1)
  
  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    or.elim (em p)
      (assume hp : p,
        or.inr
          (show ¬q, from
            assume hq : q,
            h ⟨hp, hq⟩))
      (assume hnp : ¬p,
        or.inl hnp)
end Section3_5

namespace Section3_7
  open classical
  variables p q : Prop

  -- Use Classical Logic
  example : ¬(p ↔ ¬p) :=
  assume hiff : p ↔ ¬p,
  by_cases
    (assume hp : p,
      have p2np : p → ¬p, from iff.elim_left hiff,
      (p2np hp) hp)
    (assume hnp : ¬p,
      have np2p : ¬p → p, from iff.elim_right hiff,
      have hp : p, from np2p hnp,
      have p2np : p → ¬p, from iff.elim_left hiff,
      (p2np hp) hp)
end Section3_7

namespace Section4_1
  variables (α : Type*) (p q : α → Prop)

  example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    assume h : ∀ x : α, p x ∧ q x,
    assume y : α,
    show p y, from (h y).left
  
  example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
    assume h : ∀ x : α , p x ∧ q x,
    assume z : α,
    show p z, from and.elim_left (h z)
  
  variable r : α → α → Prop
  variable trans_r : ∀ {x y z}, r x y → r y z → r x z

  variables a b c : α
  variables (hab : r a b) (hbc : r b c)

  variable refl_r : ∀ x, r x x
  variable symm_r : ∀ {x y}, r x y → r y x

  #check trans_r
  #check trans_r hab
  #check trans_r hab hbc

  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
end Section4_1