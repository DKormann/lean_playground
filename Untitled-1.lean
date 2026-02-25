

inductive Vec (A : Type) : Nat → Type
| nil : Vec A 0
| cons : A → Vec A n → Vec A (n + 1)






-- instance {A : Type} : ToString (Vec A n) where
--   toString
--     | Vec.nil => "[]"
--     | Vec.cons x xs => "[" ++ toString x ++ formatTail xs
--     where
--       formatTail : Vec A m → String
--       | Vec.nil => "]"
--       | Vec.cons y ys => ", " ++ toString y ++ formatTail ys






def Vec.len : Vec A n → Nat
| .nil => 0
| .cons _ xs => xs.len + 1


def Shape := Vec Nat

inductive Tensor {dim:Nat} : (shp : Shape dim) → Type
