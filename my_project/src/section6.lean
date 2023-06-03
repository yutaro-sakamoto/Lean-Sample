import data.nat.basic

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

