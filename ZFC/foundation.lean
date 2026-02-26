set_option linter.unusedVariables false


-- the empty type
inductive EMPTY

def EMPTY.elim {P} : EMPTY → P
  | e => nomatch e

inductive AND (A B: Prop) : Prop
  | intro : A → B → AND A B

inductive EXISTS {A:Type} (P: A → Prop) : Prop
  | intro : (a:A) → P a → EXISTS P

structure PSET :Type 1 where
  I : Type
  f : I → PSET

namespace PSET

def EQ : (a b: PSET) → Prop
  | ⟨AI, af⟩, ⟨BI, bf⟩ =>
    AND
      ((i1:AI) → EXISTS fun (i2:BI) => EQ (af i1) (bf i2))
      ((i1:BI) → EXISTS fun (i2:AI) => EQ (af i2) (bf i1))


def EQ.symm : {a b:PSET} → EQ a b → EQ b a
  | ⟨AI, af⟩, ⟨BI, bf⟩, ⟨h1, h2⟩ =>
    AND.intro
      (fun bi => let ⟨ai, j⟩ := h2 bi; ⟨ai, j.symm⟩)
      (fun ai => let ⟨bi,h⟩ := h1 ai; ⟨bi, h.symm⟩)

def EQ.trans : {a b c:PSET} → EQ a b → EQ b c → EQ a c
  | ⟨AI, af⟩, ⟨BI, bf⟩, ⟨CI, cf⟩, ⟨h1, h2⟩, ⟨h3, h4⟩ =>
    AND.intro
      (fun ai =>
        let ⟨bi, abeq⟩ := h1 ai
        let ⟨ci, bceq⟩ := h3 bi
        ⟨ci, (.trans abeq bceq)⟩
      )
      (fun ci =>
        let ⟨bi, bceq⟩ := h4 ci
        let ⟨ai, abeq⟩ := h2 bi
        ⟨ai, (.trans abeq bceq)⟩
      )

def EQ.refl : (a: PSET) → EQ a a
  | ⟨AI, af⟩ => ⟨
    fun ai => ⟨ai, EQ.refl (af ai)⟩,
    fun ai => ⟨ai, EQ.refl (af ai)⟩
  ⟩


def zero := PSET.mk EMPTY (fun e => e.elim)


def Mem : PSET → PSET → Prop
  | a, b => EXISTS fun (x: b.I) => EQ a (b.f x)


def Mem.cong_right: {a b b': PSET} → Mem a b → EQ b b' →  Mem a b'
  | a, ⟨BI, bf⟩, ⟨BI', bf'⟩, ⟨bi, h⟩, ⟨e1, e2⟩ =>
    let ⟨bi',e'⟩ := e1 bi;
    let p : EQ a (bf' bi') := EQ.trans h e'
    ⟨bi', p⟩


def Mem.cong_left: {a a' b: PSET} → Mem a b → EQ a a' →  Mem a' b
  | ⟨AI, af⟩, ⟨AI', af'⟩, ⟨BI, bf⟩, ⟨(bi:BI), (h: EQ ⟨AI, af⟩ (bf bi) )⟩, e =>
    ⟨bi, EQ.trans e.symm h⟩


def Mem.ext (a b a' b': PSET)  (h1: EQ a a') (h2: EQ b b'): Mem a b = Mem a' b' :=
  propext ⟨fun h => (h.cong_left h1).cong_right h2, fun h => (h.cong_left h1.symm).cong_right h2.symm⟩


instance : Setoid PSET where
  r := EQ
  iseqv := {
    refl  := EQ.refl
    symm  := EQ.symm
    trans := EQ.trans
  }

end PSET


def SET := Quotient (inferInstance : Setoid PSET)

def PSET.set (a:PSET) : SET := Quotient.mk (inferInstance : Setoid PSET) a

namespace SET

def zero : SET := PSET.zero.set

def Mem : SET → SET → Prop := Quotient.lift₂ PSET.Mem PSET.Mem.ext
