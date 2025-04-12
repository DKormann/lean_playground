
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


theorem add_zero (x : NatP) : add x zero = x := by
  induction x with
  | zero => rfl
  | succ x ih => simp [add, ih]

theorem add_succ (x y : NatP) : add x (succ y) = succ (add x y) := by
  induction x with
  | zero => rfl
  | succ x ih => simp [add, ih]

theorem add_comm (x y : NatP) : add x y = add y x := by
  induction x with
  | zero =>
    -- show add zero y = add y zero
    simp [add]
    rw [add_zero]
  | succ x ih =>
    -- show add (succ x) y = add y (succ x)
    simp [add]
    -- show succ (add x y) = add y (succ x)
    rw [ih]
    -- show succ (add y x) = add y (succ x)
    rw [add_succ y x]
