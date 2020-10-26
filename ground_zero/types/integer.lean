import ground_zero.theorems.nat
open ground_zero.structures (hset)
open ground_zero.theorems

hott theory

namespace ground_zero.types

/-
  +2 = pos 2
  +1 = pos 1
   0 = pos 0
  −1 = neg 0
  −2 = neg 1
-/
def integer := ℕ + ℕ
@[pattern] abbreviation integer.pos : ℕ → integer := coproduct.inl
@[pattern] abbreviation integer.neg : ℕ → integer := coproduct.inr
namespace integer

instance : has_zero integer := ⟨pos 0⟩
instance : has_one integer := ⟨pos 1⟩

instance : has_repr integer :=
⟨λ x, match x with
| (pos n) := to_string n
| (neg n) := "−" ++ to_string (n + 1)
end⟩
instance : has_to_string integer := ⟨repr⟩

def abs : integer → ℕ
| (pos n) := n
| (neg n) := n + 1

def plus : ℕ → integer := integer.pos
def minus : ℕ → integer
|    0    := pos 0
| (n + 1) := neg n

def negate : integer → integer
| (pos $ n + 1) := neg n
| (pos 0)       := pos 0
| (neg n)       := pos (n + 1)

instance : has_neg integer := ⟨negate⟩
instance : has_coe ℕ integer := ⟨integer.pos⟩

def sgn : integer → integer
| (pos $ n + 1) := 1
| (pos 0) := 0
| (neg n) := -1

def signum : integer → (nat → integer)
| (pos _) := plus
| (neg _) := minus

def auxsucc : ℕ → integer
|    0    := pos 0
| (n + 1) := neg n

def succ : integer → integer
| (neg u) := auxsucc u
| (pos v) := pos (v + 1)

def auxpred : ℕ → integer
|    0    := neg 0
| (n + 1) := pos n

def pred : integer → integer
| (neg u) := neg (u + 1)
| (pos v) := auxpred v

@[hott] def succ_equiv : integer ≃ integer :=
begin
  existsi succ, split; existsi pred,
  repeat { intro n, repeat { trivial <|> induction n } }
end

@[hott] def auxsub : nat → nat → integer
|    m       0    := pos m
|    0    (n + 1) := neg n
| (m + 1) (n + 1) := auxsub m n

@[hott] def add : integer → integer → integer
| (neg x) (neg y) := neg (x + y)
| (neg x) (pos y) := auxsub y (x + 1)
| (pos x) (neg y) := auxsub x (y + 1)
| (pos x) (pos y) := pos (x + y)
instance : has_add integer := ⟨add⟩

@[hott] def sub (x y : integer) := x + (-y)
instance : has_sub integer := ⟨sub⟩

@[hott] def mul : integer → integer → integer
| (neg x) (neg y) := plus  ((x + 1) * (y + 1))
| (neg x) (pos y) := minus ((x + 1) * y)
| (pos x) (neg y) := minus (x * (y + 1))
| (pos x) (pos y) := plus  (x * y)
instance : has_mul integer := ⟨mul⟩

@[hott] def le : integer → integer → Prop
| (neg x) (neg y) := y ≤ x
| (neg x) (pos y) := true
| (pos x) (neg y) := false
| (pos x) (pos y) := x ≤ y
instance : has_le integer := ⟨le⟩

@[hott] def add_zero (x : integer) : x + 0 = x :=
begin induction x; trivial end

@[hott] def zero_add (x : integer) : 0 + x = x :=
begin
  induction x,
  { apply Id.map pos, apply nat.zero_plus_i },
  { apply Id.map neg, reflexivity }
end

@[hott] def auxsub_asymm : Π x y, auxsub x y = negate (auxsub y x) :=
begin
  intro x, induction x with x ih; intro y; induction y with y ih',
  repeat { reflexivity }, { apply ih }
end

@[hott] def add_comm (x y : integer) : x + y = y + x :=
begin
  induction x; induction y;
  try { trivial <|> apply Id.map pos <|> apply Id.map neg },
  repeat { apply nat.comm }
end

@[hott] def auxsub_zero_right (n : nat) : auxsub n 0 = pos n :=
begin induction n; trivial end

@[hott] def auxsub_succ : Π (n m : nat), auxsub (n + 1) m = auxsub n m + 1
|    0       0    := by trivial
|    0    (m + 1) := by trivial
| (n + 1)    0    := by trivial
| (n + 1) (m + 1) := auxsub_succ n m

@[hott] def auxsub_neg : Π (n m : nat), auxsub n m = negate (auxsub m n)
|    0       0    := by trivial
|    0    (m + 1) := by trivial
| (n + 1)    0    := by trivial
| (n + 1) (m + 1) := auxsub_neg n m

@[hott] noncomputable def set : hset integer :=
begin
  apply ground_zero.ua.coproduct_set;
  apply ground_zero.theorems.nat.nat_is_set
end

@[hott] def {u} indsp {π : integer → Type u}
  (π₀ : π 0) (πsucc : Π x, π x → π (integer.succ x))
  (πpred : Π x, π x → π (integer.pred x)) : Π x, π x :=
begin
  intro x, induction x,
  { induction x with x ih,
    { exact π₀ }, { apply πsucc x ih } },
  { induction x with x ih,
    { exact πpred 0 π₀ },
    { apply πpred (integer.neg x) ih } }
end

end integer

end ground_zero.types