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