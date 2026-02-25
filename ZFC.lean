
inductive PSet : Type 1 where
  | pset (α : Type) (f : α → PSet) : PSet

namespace PSet

def fst: PSet → Type | ⟨a,_⟩ => a
def snd: (x:PSet) → (x.fst) → PSet := fun ⟨_,f⟩ => f

def zero : PSet := pset Empty (fun e => e.elim)
def one : PSet := pset Nat (fun _ => zero)
def two : PSet := pset Nat (fun e => if e > 0 then zero else one)

def idx: PSet → Type
  | pset a _ => a

def fn : (s : PSet) → s.idx → PSet
  | pset _ f => f

def Equiv : PSet → PSet → Prop
  | pset α f, pset β g =>
    (∀ a : α, ∃ b: β, Equiv (f a) (g b)) ∧
    (∀ b : β, ∃ a: α, Equiv (f a) (g b))

theorem Equiv.refl : ∀ s : PSet, Equiv s s := by
  intro s
  induction s with
  | pset α f ih =>
    constructor
    · intro a; exact ⟨a, ih a⟩
    · intro a; exact ⟨a, ih a⟩

theorem Equiv.symm : ∀ {s t : PSet}, Equiv s t → Equiv t s := by
  intro ⟨S,sf⟩ ⟨T,tf⟩ ⟨h1, h2⟩
  constructor
  · intro t
    let ⟨s, h⟩ := (h2 t)
    exact ⟨s, (Equiv.symm h)⟩
  · intro s
    let ⟨t, h⟩ := (h1 s)
    exact ⟨t, Equiv.symm h⟩

theorem Equiv.trans : ∀ {s t u}, Equiv s t → Equiv t u → Equiv s u := by
  intro ⟨S,sf⟩ ⟨T,tf⟩ ⟨U, uf⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
  constructor
  · intro s
    let ⟨t, h⟩ := (h1 s)
    let ⟨u, hh⟩ := (h3 t)
    exact ⟨u, Equiv.trans h hh⟩
  · intro u
    let ⟨t, h⟩ := (h4 u)
    let ⟨s, hh⟩ := (h2 t)
    exact ⟨s, Equiv.trans hh h⟩

def foo := fun (x:Nat) => x

def Mem : PSet -> PSet -> Prop
  | x, ⟨α, f⟩ => ∃ a:α, Equiv (f a) x

instance : Membership PSet PSet := ⟨Mem⟩


theorem Mem.congr_right {x y z: PSet} (h: Equiv y z) (hm : x ∈ y) : x ∈ z := by

  let ⟨yi, yf⟩ := y;
  let ⟨zi, zf⟩ := z;

  let ⟨h1, h2⟩ := h;



  exact sorry
