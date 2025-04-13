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
  | zero => simp [add, add_zero]
  | succ x ih => simp [add, ih, add_succ y x]

theorem add_assoc_zero (x y : NatP) : add x (add y zero) = add x y := by
  induction x with
  | zero => simp [add, add_zero]
  | succ x ih => simp [add, ih]

theorem add_assoc (x y z : NatP) : add x (add y z) = add (add x y) z := by
  induction x with
  | zero => simp [add]
  | succ x' ih => simp [add, ih]

theorem mull_zero (x : NatP) : mul x zero = zero := by
  induction x with
  | zero => rfl
  | succ x ih => simp [mul, ih, add_zero]

theorem mul_succ (x y : NatP) : mul x (succ y) = add (mul x y) x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    show add (succ y) (mul x (succ y)) = add (add y (mul x y)) (succ x)
    rw [ih, add_succ]
    show succ (add y (add (mul x y) x)) = succ (add (add y (mul x y)) x)
    rw [add_assoc]

theorem mul_comm (x y : NatP) : mul x y = mul y x := by
  induction x with
  | zero => rw [mul, mull_zero]
  | succ x ih =>
    show mul (succ x) y = mul y (succ x)
    rw [mul_succ]
    -- show mul (succ x) y = add (mul y x) y
    rw [mul]
    -- show add y (mul x y) = add (mul y x) y
    rw [add_comm]
    -- show add (mul x y) y = add (mul y x) y
    rw [ih]

theorem mul_add (x y z : NatP) : mul x (add y z) = add (mul x y) (mul x z) := by
  induction x with
  | zero => rfl
  | succ x ih =>
    show mul (succ x) (add y z) = add (mul (succ x) y) (mul (succ x) z)
    simp only [mul]
    -- show add (add y z) (mul x (add y z)) = add (add y (mul x y)) (add z (mul x z))
    rw [ih]
    -- show add (add y z) (add (mul x y) (mul x z)) = add (add y (mul x y)) (add z (mul x z))
    rw [add_assoc]
    -- show add (add (add y z) (mul x y)) (mul x z) = add (add y (mul x y)) (add z (mul x z))
    rw [<-add_assoc]
    -- show add (add y z) (add (mul x y) (mul x z)) = add (add y (mul x y)) (add z (mul x z))
    rw [<- add_assoc]
    -- show add y (add z (add (mul x y) (mul x z))) = add (add y (mul x y)) (add z (mul x z))
    rw [add_comm (mul x y)]
    -- show add y (add z (add (mul x z) (mul x y) )) = add (add y (mul x y)) (add z (mul x z))
    rw [add_assoc z]
    -- show add y (add (add z (mul x z)) (mul x y)) = add (add y (mul x y)) (add z (mul x z))
    rw [<-add_comm (mul x y)]
    -- show add y (add (mul x y) (add z (mul x z))) = add (add y (mul x y)) (add z (mul x z))
    rw [add_assoc y]

theorem mul_assoc (x y z : NatP) : mul x (mul y z) = mul (mul x y) z := by
  induction x with
  | zero => rfl
  | succ x ih =>
    -- show mul (succ x) (mul y z) = mul (mul (succ x) y) z
    simp [mul]
    -- show add (mul y z) (mul x (mul y z)) = mul (add y (mul x y)) z
    rw [ih]
    -- show add (mul y z) (mul (mul x y) z) = mul (add y (mul x y)) z
    rw [mul_comm y, mul_comm (mul x y)]
    -- show add (mul z y) (mul z (mul x y)) = mul (add y (mul x y)) z
    rw [<-mul_add z]
    -- show mul z (add y (mul x y)) = mul (add y (mul x y)) z
    rw [mul_comm]
