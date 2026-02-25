
set_option linter.unusedVariables false

inductive PSet : Type 1 where
  | pset (T:Type) (f: T → PSet) : PSet

def p0 := PSet.pset Empty (Empty.elim)
def p1 := PSet.pset Unit (fun _ => p0)
def p2 := PSet.pset Bool (fun b => if b then p0 else p1)

@[match_pattern]
def mkand :{a b:Prop} -> (left:a) -> (right:b) -> a ∧ b := And.intro
@[match_pattern]
def mkexs : {p: a -> Prop} ->  (w: a) -> (h : p w ) -> Exists p := Exists.intro

namespace PSet

def idx (x: PSet) : Type := let (pset A f) := x; A
def elm (x: PSet) : x.idx → PSet := let (pset A f) := x; f

def Equiv: PSet → PSet → Prop
  | pset A fa, pset B fb =>
    ((a:A) → (∃b:B, Equiv (fa a) (fb b))) ∧
    ((b:B) → (∃a:A, Equiv (fa a) (fb b)))

def Equiv.symm {x y :PSet} (h: Equiv x y) : Equiv y x :=
  let (pset X fx) := x;
  let (pset Y fy) := y;
  mkand
    (fun y => let (mkexs x eq) := h.right y; mkexs x (Equiv.symm eq))
    (fun x => let (mkexs y eq) := h.left x; mkexs y (Equiv.symm eq))


theorem Equiv.trans: {x y z: PSet} → Equiv x y → Equiv y z → Equiv x z
  | ⟨X, fx⟩, ⟨Y, fy⟩, ⟨Z, fz⟩, ⟨h1, h2⟩ , ⟨h3, h4⟩ =>
  And.intro
    (fun x:X =>
      let (Exists.intro y eq) := h1 x;
      let (Exists.intro z eq2) := h3 y;
      Exists.intro z (Equiv.trans eq eq2))
    fun z:Z =>
      let (Exists.intro y eq) := h4 z;
      let (Exists.intro x eq2) := h2 y;
      Exists.intro x (Equiv.trans eq2 eq)

theorem Equiv.refl: (x: PSet) → Equiv x x
  | ⟨X, fx⟩ =>
    (.intro
      (fun x=> Exists.intro x $ .refl $ fx x)
      fun x=> Exists.intro x $ .refl $ fx x)

def Mem : PSet → PSet → Prop
  | a, pset _B fb => ∃b, Equiv (fb b) a

theorem Mem.cong_right: {x y y': PSet} → Mem x y → Equiv y y' → Mem x y'
  | ⟨X, fx⟩, ⟨Y, fy⟩, ⟨Y', fy'⟩, ⟨y, eq⟩, ⟨h3,h4⟩ =>
    let (.intro y' eqyy') := h3 y;
    (.intro y' (.trans (.symm eqyy') eq))

theorem Mem.cong_left: {x x' y: PSet} → Mem x y → Equiv x x' → Mem x' y
  | ⟨X, fx⟩, ⟨X', fx'⟩, ⟨Y, fy⟩, ⟨y, eq⟩, h =>
    (.intro y (.trans eq h))


def empty := pset Empty Empty.elim
theorem empty_exists: ∃e: PSet, (x:PSet) → ¬ Mem x e :=
  let f := fun E ⟨e,_⟩ => e.elim
  .intro empty f


def extensionality (α β :PSet) (h: (x:PSet) → Mem x α ↔ Mem x β): Equiv α β :=
  let (pset A fa) := α
  let (pset B fb) := β
  mkand
    (fun a =>
      let (mkexs b p) := (h (fa a)).mp (mkexs a (Equiv.refl (fa a)));
      (mkexs b (Equiv.symm p)))
    fun b => (h (fb b)).mpr (mkexs b (Equiv.refl (fb b)))


def pair (α β: PSet) : ∃γ, ((x: PSet) → (Mem x γ) ↔ (Equiv x α ∨ Equiv x β)) :=
  let γ := pset Bool (fun i => if i then α else β)
  let p := fun i => Iff.intro
    (fun (mkexs x k)=>
      match x with
      | true =>
        let p : Equiv α i  := k;
        Or.inl (Equiv.symm p)
      | false => Or.inr (Equiv.symm k))
    fun h =>
      match h with
      | .inr k => (mkexs false (Equiv.symm k))
      | .inl k => (mkexs true (Equiv.symm k))
  (mkexs γ p)

def Subset (α β: PSet) : Prop := (x:PSet) → Mem x α → Mem x β

-- Mem e U
-- Mem e k
-- Mem k α

inductive QQ (a: PSet) : Prop
  | mkqq (e: PSet)

def Union : PSet → PSet
  | pset AI af => pset (Σ ai : AI, (af ai).idx) (fun ⟨ai, ki⟩ => (af ai).elm ki)

theorem mem_fn (s : PSet) (i : s.idx) : Mem (s.elm i) s :=
  match s with
  | ⟨SI,sf⟩ => ⟨i, Equiv.refl (sf i)⟩

theorem mem_unpack (s : PSet) (e : PSet) (h : Mem e s) : ∃ i : s.idx, Equiv (s.elm i) e :=
  match s with | ⟨SI, sf⟩ => h

theorem mem_mk (s : PSet) (i : s.idx) (e : PSet) (h : Equiv (s.elm i) e) : Mem e s :=
  match s with | ⟨_,_⟩ => ⟨i, h⟩

theorem union_spec (a : PSet) : (e : PSet) → Mem e (Union a) ↔ ∃k, Mem e k ∧ Mem k a :=
  fun e=>
    Iff.intro
      (
        fun h=>
          let ⟨AI, af⟩ := a
          let ⟨⟨ai, ki⟩, h2⟩ := h
          let h3 : ((af ai).elm ki).Equiv e := h2;
          let ⟨KI, kf⟩ := af ai
          let pr : Mem ((af ai).elm ki) (af ai) := mem_fn (af ai) ki
          let pp : Mem e (af ai) := Mem.cong_left pr h3;
          let p3: (af ai).Mem (pset AI af) := ⟨ai, Equiv.refl (af ai)⟩
          ⟨(af ai), ⟨pp, p3⟩⟩
      )
      (
        fun ⟨k, ⟨h1, h2⟩⟩ =>
        match a with
        | ⟨AI, af⟩ =>
        match h2 with
        | ⟨ai, h3⟩ =>
        let h4 : Mem e (af ai) := Mem.cong_right h1 (h3.symm);
        let ⟨ki, h5⟩ := mem_unpack (af ai) e h4;
        ⟨⟨ai, ki⟩, h5⟩
      )
