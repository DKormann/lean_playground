

axiom SET: Type

axiom Mem : SET → SET → Prop

axiom zero_exists : ∃z, (x :SET) → (Mem x z → False)

axiom pairing : (x y: SET) → ∃p, Mem x p ∧ Mem y p

axiom union : (a e: SET) → (∃U, Mem e U ↔ ∃k, Mem e k ∧ Mem k a)

axiom extensionality : {a b : SET} → ((x:SET) →  Mem x a ↔ Mem x b) → a = b

axiom specification : (a:SET) → (p: SET → Prop) → ∃s, (e:SET) → Mem e s ↔ Mem e a ∧ p e

def unique_zero (x y:SET) (hx: (z:SET) → Mem z x → False) (hy: (z:SET) → Mem z y → False) : x = y :=
  extensionality (fun e => ⟨fun m => (hx e m).elim, fun m => (hy e m).elim⟩)

noncomputable def pair (a b : SET): SET :=
  Classical.choose $ specification (Classical.choose $ pairing a b) fun x => x = a ∨ x = b

theorem pair_spec (a b : SET) : ∀ e, Mem e (pair a b) ↔ Mem e (Classical.choose (pairing a b)) ∧ (e = a ∨ e = b) :=
  Classical.choose_spec (specification (Classical.choose (pairing a b)) (fun e => e = a ∨ e = b))

theorem mem_pair (a b : SET) : ∀ e, Mem e (pair a b) ↔ e = a ∨ e = b
  | (e:SET) => ⟨
    fun h=> ((pair_spec a b e).mp h).right,
    fun h=>
    let q := ((pair_spec a b e).mpr);
    let ⟨sa, sb⟩ := Classical.choose_spec (pairing a b);
    let mempair := (fun (x:SET) => Mem x (Classical.choose (pairing a b)))
    let r : mempair e :=
      match h with
      | .inr eb => Eq.subst eb.symm sb
      | .inl ea => Eq.subst ea.symm sa
    q ⟨r, h⟩

  ⟩


noncomputable def opair (a b:SET) := pair (pair a a) (pair a b)

theorem selfpair (a e:SET) : Mem e (pair a a ) ↔ e = a :=
  let l := (mem_pair a a e)
  ⟨
  fun h=>
  match l.mp h with
  | .inl h => h
  | .inr h => h,
  fun h => l.mpr (.inl h)
  ⟩

theorem pair.symm: (pair a b) = pair b a :=
  let h := fun x =>
    let r := (mem_pair a b x).trans (Iff.intro Or.symm Or.symm)
    let r' := r.trans (mem_pair b a x).symm
    r'
  extensionality h

theorem pair_aa_bc (a b: SET) (h:pair a a = pair b c): b=a :=
  (selfpair a b).mp (Eq.subst h.symm (((mem_pair b c) b).mpr (.inl $ .refl b)) )

theorem opair_eq (a b c d : SET) : opair a b = opair c d ↔ a = c ∧ b = d :=
  let aa := pair a a
  let ab := pair a b
  let ad := pair a d
  let cc := pair c c
  let cd := pair c d

  ⟨
    fun h =>
      let h' : pair aa ab = pair cc cd  := h;
      let q := fun e =>
        let t := mem_pair aa ab e
        let t' : Mem e (pair cc cd) ↔ e = aa ∨ e = ab := Eq.substr h'.symm t;
        let u : e = cc ∨ e = cd ↔ e = aa ∨ e = ab := (mem_pair cc cd e).symm.trans t'
        u

      let hcc := (q cc).mp (.inl rfl);

      let a_c : a=c := match hcc with
        | .inl h => pair_aa_bc c a h
        | .inr h => pair_aa_bc c a h

      let q : (e:SET)-> (e=aa ∨ e= ad ↔ e =aa ∨ e =ab) := Eq.substr
        (p :=(fun c=> ((e : SET)-> ( e = (pair c c) ∨ e = (pair c d) ↔ e = aa ∨ e = ab))))
        a_c q



      let f := fun (b_a:b=a) =>
        match (q ad).mp (.inr rfl) with
          |.inl h=>b_a.trans (pair_aa_bc a d ( h.symm.trans pair.symm)).symm
          |.inr h=>
          b_a.trans (pair_aa_bc a d ((Eq.subst (motive := fun x=>ad=pair a x) b_a h).symm.trans pair.symm)).symm
      ⟨
        a_c,
        match (q ab).mpr (.inr rfl) with
        | .inl h => f (pair_aa_bc a b (h.symm.trans pair.symm))
        | .inr h =>
          let k:= fun (e:SET) =>
            Eq.subst (motive:= fun x=> Mem e x ↔ e = a ∨ e = b) h (mem_pair a b e)
          let l := (k b).mpr (.inr rfl)
          match (mem_pair a d b).mp l  with
          | .inl b_a => f b_a
          | .inr h => h
      ⟩,
    fun h =>
      Eq.subst (motive := fun x => opair a b = opair c x) h.right
      (Eq.subst (motive := fun x => opair a b = opair x b) h.left rfl)
  ⟩
