In this project I want to learn LEAN from the very basics, coming from a programmers perspective.

I want to try to work towards a formalization of the ZFC axioms using only programmer style proofs eg. no tactics or buildins or libraries. focusing on inductive types and functions only.


example of a theorem in this style:

``` lean

def extensionality (α β :PSet) (h: (x:PSet) → Mem x α ↔ Mem x β): Equiv α β :=
  let (pset A fa) := α
  let (pset B fb) := β
  mkand
    (fun a =>
      let (mkexs b p) := (h (fa a)).mp (mkexs a (Equiv.refl (fa a)));
      (mkexs b (Equiv.symm p)))
    fun b => (h (fb b)).mpr (mkexs b (Equiv.refl (fb b)))

```

The goal is for me to learn specification and proving. please don't spoil me the definitions or proofs.