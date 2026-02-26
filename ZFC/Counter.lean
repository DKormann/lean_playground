
structure CTX S I where
  state: S
  input: I

structure EFF S O where
  state: S
  out: O

inductive CounterInput
  | get
  | inc

def Counter :=
  (ctx: CTX Nat CounterInput) →
  match ctx.input with
  | .get => {e: EFF Nat Nat // e.state = ctx.state ∧ e.out = ctx.state}
  | .inc => {e: EFF Nat Unit // e.state = ctx.state + 1}


def counter : Counter
  | ⟨state, .get⟩ => ⟨⟨state, state⟩, ⟨rfl, rfl⟩⟩
  | ⟨state, .inc⟩ => ⟨⟨state + 1, ()⟩, rfl⟩
