
inductive NatP
| zero: NatP
| succ: NatP → NatP

open NatP

def add: NatP → NatP → NatP
| zero, y => y
| succ x, y => succ (add x y)

def one := succ zero
def two := succ one

def rep
| zero => "0"
| succ x => "S"++ rep x

def mul
| zero, _ => zero
| succ x, y => add y (mul x y)

#eval rep $ mul one two
#eval rep $ mul one zero
#eval rep $ mul zero two

def eq
| zero, zero => true
| succ x, succ y => eq x y
| _, _ => false

def neq | x, y => not (eq x y)

def lt
| zero, zero => false
| zero, succ _ => true
| succ _, zero => false
| succ x, succ y => lt x y


theorem succ_zero : neq (succ zero) zero := rfl

theorem succ_neq : ∀ x, neq (succ x) zero := by
  intro x
  induction x with
  | zero => rfl
  | succ x ih => rfl


theorem add_zero_x: ∀ (x:NatP), add zero x = x := by
  intro x
  induction x with
  | zero => rfl
  | succ x ih => rfl

theorem add_x_zero: ∀ (x:NatP), add x zero = x := by
  intro x
  induction x with
  | zero => rfl
  | succ x ih =>
    show succ (add x zero) = succ x
    simp [add]
    show add x zero = x
    exact ih





-- theorem add_zero_cumm: ∀ (x:NatP), add x zero = add zero x := by
--   intro x
--   induction x with
--   | zero =>
--     show add zero zero = add zero zero
--     exact rfl
--   | succ x ih =>
--     show add (succ x) zero = add zero (succ x)
--     show add (succ x) zero = (succ x)
--     show add (succ x) zero = add (succ x) zero
--     exact rfl


-- -- theorem add_cumm: ∀ (x y:NatP), add x y = add y x := by
-- --   intro x y
-- --   induction x with
-- --   | zero => rfl
