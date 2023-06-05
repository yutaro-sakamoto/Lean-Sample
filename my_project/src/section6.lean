import data.nat.basic
import algebra.group.basic

section
variables x y : ℕ

def double := x + x

#check double y
#check double (2 * x)

local attribute [simp] add_assoc add_comm add_left_comm

theorem t1 : double (x +y) = double x + double y :=
by simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y :=
by simp [double, add_mul]
end

section
variables (x y z : ℕ)
variables (h₁ : x = y) (h₂ : y = z)

include h₁ h₂
theorem foo : x = z :=
begin
  rw [h₁, h₂]
end
omit h₁ h₂

theorem bar : x = z :=
eq.trans h₁ h₂

theorem baz : x = x := rfl

#check @foo
#check @bar
#check @baz
end

namespace section6_2_1
section
variables (x y z : ℕ)
variables (h₁ : x = y) (h₂ : y = z)

section
variables {x y z}
include h₁ h₂
theorem foo : x = z :=
begin
  rw [h₁, h₂]
end
end

theorem bar : x = z :=
eq.trans h₁ h₂

variable {x}
theorem baz : x = x := rfl

#check @foo
#check @bar
#check @baz
end

section
parameters {α: Type*} (r : α → α → Prop)
parameter transr : ∀ {x y z}, r x y → r y z → r x z

variables {a b c d e : α}

theorem t1 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) : r a d :=
transr (transr h₁ h₂) h₃

theorem t2 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) (h₄ : r d e) :
  r a e :=
  transr h₁ (t1 h₂ h₃ h₄)

#check t1
#check t2
end

#check t1
#check t2
end section6_2_1

namespace Section6_3
  namespace foo
  def bar : ℕ := 1
  end foo
  open foo
  #check foo.bar

  def foo1.bar : ℕ := 1
  open foo

  #check foo1.bar

  #check add_sub_cancel
  #check nat.add_sub_cancel
  #check _root_.add_sub_cancel

  namespace foo2
  protected def bar : ℕ := 1
  end foo2
  open foo2
  #check foo2.bar

  open nat (renaming mul → times) (renaming add → plus)
    (hiding succ sub)
  export nat (succ add sub)
end Section6_3

namespace Section6_4
  variable {α : Type*}
  def is_prefix (l₁ : list α) (l₂ : list α) : Prop :=
  ∃ t, l₁ ++ t = l₂
  infix ` <<+: `:50 := is_prefix

  local attribute [simp]
  theorem list.is_prefix_refl (l : list α) : l <<+: l :=
  ⟨[], by simp⟩

  example : [1, 2, 3] <<+: [1, 2, 3] := by simp

  instance list_has_le : has_le (list α) := ⟨is_prefix⟩


  theorem list.is_prefix_refl2 (l : list α) : l ≤ l :=
  ⟨[], by simp⟩

  namespace sub
    def list_has_le : has_le (list α) := ⟨is_prefix⟩
    local attribute [instance] list_has_le

    theorem foo (l : list α) : l ≤ l := ⟨[], by simp⟩
  end sub

  @[simp, refl]
  theorem list.is_prefix_refl3 (l : list α) : l <<+: l :=
  ⟨[], by simp⟩

  example : [1, 2, 3] <<+: [1, 2, 3] := by reflexivity
end Section6_4

namespace Section6_5
  namespace hidden
    variables {α : Type*} (r : α → α → Prop)

    definition reflexive : Prop := ∀ (a : α), r a a
    definition symmetric : Prop := ∀ {a b : α}, r a b → r b a
    definition transitive : Prop :=
      ∀ {a b c : α}, r a b → r b c → r a c
    definition euclidean : Prop :=
      ∀ {a b c : α}, r a b → r a c → r b c
    
    variable {r}

    theorem th1 (reflr : reflexive r) (euclr : euclidean r) :
      symmetric r :=
    assume a b : α, assume : r a b,
    show r b a, from euclr this (reflr _)

    theorem th2 (symmr : symmetric r) (euclr : euclidean r) :
      transitive r :=
    assume (a b c : α), assume (rab : r a b) (rbc : r b c),
    euclr (symmr rab) (rbc)

    theorem th3 (reflr : reflexive r) (euclr : euclidean r) :
      transitive r :=
    @th2 _ _ (@th1 _ _ reflr @euclr) @euclr
  end hidden

  namespace hidden2
    variables {α : Type*} (r : α → α → Prop)

    definition reflexive : Prop := ∀ (a : α), r a a
    definition symmetric : Prop := ∀ ⦃a b : α⦄, r a b → r b a
    definition transitive : Prop :=
      ∀ ⦃a b c : α⦄, r a b → r b c → r a c
    definition euclidean : Prop :=
      ∀ ⦃a b c : α⦄, r a b → r a c → r b c
    
    variable {r}

    theorem th1 (reflr : reflexive r) (euclr : euclidean r) :
      symmetric r :=
    assume a b : α, assume : r a b,
    show r b a, from euclr this (reflr _)

    theorem th2 (symmr : symmetric r) (euclr : euclidean r) :
      transitive r :=
    assume (a b c : α), assume (rab : r a b) (rbc : r b c),
    euclr (symmr rab) (rbc)

    theorem th3 (reflr : reflexive r) (euclr : euclidean r) :
      transitive r :=
    th2 (th1 reflr euclr) euclr
  end hidden2
end Section6_5