inductive Vec (a: Type) : Nat -> Type
| nil : Vec a 0
| cons : (x:a) -> Vec a n -> Vec a (n + 1)

open Vec

inductive plainCirc: (depth: Nat) -> Type
| T: plainCirc 0
| F: plainCirc 0
| X0: plainCirc 0
| X1: plainCirc 0
| node {n} : (a b: plainCirc n) -> plainCirc (n + 1)

def n: plainCirc 1 := plainCirc.node plainCirc.X0 plainCirc.X1
def n0: plainCirc 2 := plainCirc.node n n
def nt: plainCirc 1 := plainCirc.node plainCirc.F plainCirc.F

def eval {n: Nat} (c: plainCirc n) (x0 x1: Bool): Bool :=  match c with
  | plainCirc.F => false
  | plainCirc.T => true
  | plainCirc.X0 => x0
  | plainCirc.X1 => x1
  | plainCirc.node a b => !((eval a x0 x1) && (eval b x0 x1))

def map {a b : Type} {n : Nat} (fn: a->b) (v :Vec a n) : (Vec b n) := match v with
  | nil => nil
  | cons x xs => cons (fn x) (map fn xs)

theorem node_comm: ∀(x0 x1: Bool), ∀(d0: Nat), ∀(n0 n1:plainCirc d0 ),
  eval (plainCirc.node n0 n1) x0 x1 = eval (plainCirc.node n1 n0) x0 x1 := by
  intro x0 x1 n0 n1
  simp [eval]
  show ∀ (n1_1 : plainCirc n0), (!eval n1 x0 x1 || !eval n1_1 x0 x1) = (!eval n1_1 x0 x1 || !eval n1 x0 x1)
  simp[Bool.or_comm]
