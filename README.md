# RevCHAC

> **Lean Version:** `leanprover/lean4:v4.26.0-rc2`
> **Main File:** `RevCHAC/RevCHAC.lean`

This repository currently consists of a single Lean file implementing the following architecture:

* a purely semantic Galois layer over a satisfaction relation,
* a dynamic halting layer built from traces and a “reverse halting” operator `Rev`,
* a local reading `LR` that realises semantic consequence as halting of traces,
* an abstract Turing–Gödel context encoding the standard diagonal obstruction,
* a `RevCHACSystem` that aligns real halting, a Rev-based halting profile, a CH-local profile, and a dynamic choice operator,
* two levels of “non-internalisation” meta-theorems: one for halting, one for the specific operative AC built from this system.

The result is a precise Lean formalisation of the slogan:

> **There is a concrete dynamic halting/choice structure, definable from ℕ and basic semantics, that no recursive consistent theory of ZFC-strength can fully internalise as a single total, correct and complete predicate.**

Level 2 is stated in a Turing–Gödel context equipped with a *local* reflection principle that applies specifically to the meta-level halting predicate induced by an attempted internalisation of this dynamic AC.

---

## 1. Static semantic layer: `ModE`, `ThE`, `CloE`

The file starts by fixing:

* a type `Sentence`,
* a type `Model`,
* a satisfaction relation

  ```lean
  Sat : Model → Sentence → Prop
  ```

From this, it defines the usual Galois connection between sets of sentences and classes of models:

```lean
def ModE (Γ : Set Sentence) : Set Model :=
  { M | ∀ φ ∈ Γ, Sat M φ }

def ThE (K : Set Model) : Set Sentence :=
  { φ | ∀ M ∈ K, Sat M φ }

def CloE (Γ : Set Sentence) : Set Sentence :=
  ThE Sat (ModE Sat Γ)
```

In the namespace `LogicDissoc`, it proves the standard closure-operator properties:

* `subset_CloE`   : extensivity `Γ ⊆ CloE Sat Γ`,
* `CloE_mono`     : monotonicity in `Γ`,
* `CloE_idem`     : idempotence `CloE Sat (CloE Sat Γ) ⊆ CloE Sat Γ`.

Semantic consequence is packaged as:

```lean
def SemConsequences (Γ : Set Sentence) (φ : Sentence) : Prop :=
  φ ∈ CloE Sat Γ
```

This is the static “ZFC-style” layer: models, theories, semantic closure.

---

## 2. Dynamic layer: traces, `up`, halting, and `Rev`

A **trace** is a time-indexed proposition:

```lean
abbrev Trace := ℕ → Prop
```

For a trace `T`, the temporal closure `up T` records whether something has happened *by* time `n`:

```lean
def up (T : Trace) : Trace :=
  fun n => ∃ k ≤ n, T k
```

Basic properties:

* `up_mono`      : monotonicity of `up T n` in `n`,
* `exists_up_iff`: `(∃ n, up T n) ↔ ∃ n, T n`.

Direct halting is:

```lean
def Halts (T : Trace) : Prop := ∃ n : ℕ, T n
```

Then a **reverse-halting kit** is introduced as an abstract projection on families `(ℕ → Prop)`:

```lean
structure RHKit where
  Proj : (ℕ → Prop) → Prop
```

The admissibility condition is `DetectsMonotone K`:

```lean
structure DetectsMonotone (K : RHKit) : Prop where
  proj_of_mono :
    ∀ X : ℕ → Prop,
      (∀ {n m}, n ≤ m → X n → X m) →
      (K.Proj X ↔ ∃ n, X n)
```

Given such a kit `(K, DK)`, the dynamic operator `Rev` is:

```lean
def Rev (T : Trace) : Prop :=
  K.Proj (fun n => up T n)

def Rev0 (T : Trace) : Prop :=
  Rev K T
```

The core invariance lemmas show that `Rev`/`Rev0` are *extensionally equal* to `Halts`:

* `Rev_iff_exists` : `Rev K T ↔ ∃ n, T n`,
* `Rev_iff_Halts`  : `Rev K T ↔ Halts T`,
* `Rev0_iff_Halts` : `Rev0 K T ↔ Halts T`,
* `Rev0_eq_Halts`  : pointwise equality `∀ T, Rev0 K T ↔ Halts T`.

So any reverse–halting mechanism that correctly detects eventual truth on all monotone families, once fed through `up`, necessarily collapses to ordinary halting on traces.

---

## 3. Local readings, provability, and the dynamic bridge

A **local reading** abstracts the dynamic realisation of consequence:

```lean
abbrev LocalReading (Context : Type v') (Sentence : Type u') :=
  Context → Sentence → Trace
```

Given `LR`, the file defines:

* dynamic provability:

  ```lean
  def Prov (LR : LocalReading Context Sentence) (Γ : Context) (φ : Sentence) : Prop :=
    ∃ n : ℕ, LR Γ φ n
  ```

* the **robust verdict** induced by `Rev0`:

  ```lean
  def verdict (LR : LocalReading Context Sentence) (Γ : Context) (φ : Sentence) : Prop :=
    Rev0 K (LR Γ φ)
  ```

Using `Rev0_iff_Halts`, one gets:

```lean
lemma verdict_iff_Prov
  (DK : DetectsMonotone K)
  (LR : LocalReading Context Sentence)
  (Γ : Context) (φ : Sentence) :
  verdict K LR Γ φ ↔ Prov LR Γ φ
```

Specialising contexts to sets of sentences, the **dynamic bridge** is:

```lean
def DynamicBridge (LR : LocalReading (Set Sentence) Sentence) : Prop :=
  ∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ)
```

Assuming such an `LR`, the main lemma is:

```lean
lemma semantic_iff_verdict
    {K : RHKit} (DK : DetectsMonotone K)
    (LR : LocalReading (Set Sentence) Sentence)
    (bridge : DynamicBridge Sat LR) :
  ∀ (Γ : Set Sentence) (φ : Sentence),
    SemConsequences Sat Γ φ ↔
      verdict K LR Γ φ
```

Under the bridge, semantic consequence `φ ∈ CloE Γ` coincides with the Rev-based verdict on the trace `LR Γ φ`, uniformly in all admissible kits `K`.

This cleanly separates:

* the static Galois/ZFC layer `(ModE, ThE, CloE)`,
* the dynamic halting layer `(Trace, Halts, Rev, Rev0)`,
* and the specific local reading `LR` which ties them together.

---

## 4. Turing–Gödel meta-context

The next part formalises an abstract Turing–Gödel setting in Lean. This is purely meta-theoretic: the structures and theorems are stated over abstract types and not instantiated inside the file.

### 4.1. `TuringGodelContext'`

The file defines:

```lean
structure TuringGodelContext' (Code PropT : Type) where
  RealHalts : Code → Prop
  Provable  : PropT → Prop
  FalseT    : PropT
  Not       : PropT → PropT
  consistent : ¬ Provable FalseT
  absurd     : ∀ {p}, Provable p → Provable (Not p) → Provable FalseT
  diagonal_program :
    ∀ (H : Code → PropT), ∃ e : Code, RealHalts e ↔ Provable (Not (H e))
```

Using this, it proves the classical impossibility of a *total, correct and complete* internal halting predicate:

```lean
theorem no_internal_halting_predicate'
  {Code PropT : Type}
  (ctx : TuringGodelContext' Code PropT) :
  ¬ ∃ _ : InternalHaltingPredicate ctx, True
```

The proof is the standard diagonal argument: apply `diagonal_program` to `H`, then split on `RealHalts e` and contradict consistency in both cases.

### 4.2. `InternalHaltingPredicate`

An internal halting predicate is:

```lean
structure InternalHaltingPredicate (ctx : TuringGodelContext' Code PropT) where
  H        : Code → PropT
  total    : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct  : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))
```

The theorem

```lean
theorem no_internal_halting_predicate'
  (ctx : TuringGodelContext' Code PropT) :
  ¬ ∃ _ : InternalHaltingPredicate ctx, True
```

is the diagonal argument packaged via `InternalHaltingPredicate`. This is the main input for Level 1 of the non-internalisation result.

---

## 5. Rev–CH–AC systems and dynamic AC on codes

The `RevCH` section introduces abstract structures to talk about “Rev halting” and a “CH-profile” on the same type of programs:

```lean
structure RevHalting (Prog : Type) where
  Halts : Prog → Prop

structure CHProfile (Prog : Type) where
  CHFlag : Prog → Prop
```

An isomorphism between them is:

```lean
structure RevCHIso {Prog : Type}
    (R : RevHalting Prog) (C : CHProfile Prog) : Prop where
  iso : ∀ p : Prog, R.Halts p ↔ C.CHFlag p
```

From such an `iso`:

* `RevCHIso.toEquiv` gives an equivalence `{p // R.Halts p} ≃ {p // C.CHFlag p}`,
* `RevCHIso.ofEquiv` reconstructs a `RevCHIso` from such an equivalence that preserves the underlying `Prog`.

This formalises precisely the slogan “Rev halting is isomorphic to CH”.

### 5.1. `RevCHACSystem`

Over a `TuringGodelContext'`, the file defines:

```lean
structure RevCHACSystem (ctx : TuringGodelContext' Code PropT) where
  Prog      : Type
  Witness   : Type
  embed     : Code → Prog
  Halts_rev : Prog → Prop
  CH_local  : Prog → Prop
  F_dyn     : {p : Prog // CH_local p} → Witness
  iso_real_rev : ∀ e : Code, ctx.RealHalts e ↔ Halts_rev (embed e)
  iso_rev_CH   : ∀ p : Prog, Halts_rev p ↔ CH_local p
```

Here:

* `RealHalts : Code → Prop` is the “real-world” halting predicate,
* `Halts_rev : Prog → Prop` is the Rev-based halting predicate,
* `CH_local : Prog → Prop` is the local CH-profile,
* `F_dyn` is a dynamic choice operator defined on the CH-local fragment,
* `iso_real_rev` and `iso_rev_CH` identify the three halting/CH profiles.

Pulling back along `embed` gives:

```lean
def H_forbidden (ctx : TuringGodelContext' Code PropT) : Code → Prop :=
  ctx.RealHalts

def CH_on_code (S : RevCHACSystem ctx) : Code → Prop :=
  fun e => S.CH_local (S.embed e)

theorem H_forbidden_iff_CH_on_code (e : Code) :
    H_forbidden ctx e ↔ CH_on_code S e
```

and the **dynamic AC on codes**:

```lean
def AC_dyn (e : Code) (h : ctx.RealHalts e) : S.Witness :=
  let p := S.embed e
  have h_rev : S.Halts_rev p :=
    (S.iso_real_rev e).mp h
  have h_CH : S.CH_local p :=
    (S.iso_rev_CH p).mp h_rev
  S.F_dyn ⟨p, h_CH⟩
```

So `AC_dyn` is defined exactly on those `e` that really halt, and is canonically induced from the Rev–CH–AC structure.

---

## 6. Internalisation theorems

### 6.1. Level 1: no full internalisation of halting

A candidate internalisation of the dynamic halting profile is:

```lean
structure InternalisationCandidate where
  H        : Code → PropT
  total    : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct  : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))
```

This has exactly the same shape as `InternalHaltingPredicate ctx`, and the theorem

```lean
theorem no_full_internalisation :
    ¬ ∃ _ : InternalisationCandidate ctx, True
```

is obtained by reusing `no_internal_halting_predicate' ctx`.

Interpretation:

> Even before mentioning CH or AC, there is no way for `T` to have a single internal predicate `H(e)` that is total, correct and complete for the real halting profile `RealHalts(e)`.

### 6.2. Level 2: AC operative internalisation impossibility

To discuss the **operative AC** coming from `AC_dyn`, the file introduces:

```lean
structure InternalisationWithAC where
  W_int  : Type
  F_int  : Code → W_int
  Decode : W_int → S.Witness
  correct_on_halting :
    ∀ (e : Code) (h : ctx.RealHalts e),
      Decode (F_int e) = AC_dyn ctx S e h
```

Here:

* `F_int` is an internal choice-like function on codes (total),
* `Decode` maps internal witnesses to external `S.Witness`,
* `correct_on_halting` requires that, whenever `e` really halts, `Decode (F_int e)` *matches* the dynamically defined `AC_dyn ctx S e h`.

From such an `InternalisationWithAC`, define the meta-level predicate:

```lean
def H_from_Fint (I : InternalisationWithAC ctx S) (e : Code) : Prop :=
  ∃ h : ctx.RealHalts e, I.Decode (I.F_int e) = AC_dyn ctx S e h
```

One proves:

```lean
lemma H_from_Fint_iff_RealHalts
    (I : InternalisationWithAC ctx S) (e : Code) :
    H_from_Fint ctx S I e ↔ ctx.RealHalts e
```

So `H_from_Fint` decides exactly the real halting predicate at the meta-level, *assuming* we have an internalisation kit `I`.

To connect this with the internal theory `T`, the file introduces an explicit **local reflection axiom**:

```lean
axiom reflect_for_this_H :
  ∀ {Code PropT : Type}
    (ctx : TuringGodelContext' Code PropT)
    (S   : RevCHACSystem ctx)
    (I   : InternalisationWithAC ctx S),
    ∃ H_enc : Code → PropT,
      (∀ e, H_from_Fint ctx S I e → ctx.Provable (H_enc e)) ∧
      (∀ e, ¬ H_from_Fint ctx S I e → ctx.Provable (ctx.Not (H_enc e))) ∧
      (∀ e, ctx.Provable (H_enc e) ∨ ctx.Provable (ctx.Not (H_enc e)))
```

This axiom is **local** in two senses:

* it is postulated only in the presence of a chosen `ctx`, `S`, and `I`,
* it reflects precisely the predicate `H_from_Fint ctx S I` into the theory `T`, yielding:

  * correctness: if `H_from_Fint e` holds meta-theoretically, then `T ⊢ H_enc(e)`,
  * completeness: if `¬ H_from_Fint e` holds meta-theoretically, then `T ⊢ ¬H_enc(e)`,
  * totality: for each `e`, `T` proves either `H_enc(e)` or `¬H_enc(e)`.

Using `reflect_for_this_H`, the proof of the Level 2 theorem proceeds as follows:

1. Assume an internalisation kit `I : InternalisationWithAC ctx S`.

2. By `reflect_for_this_H`, obtain `H_enc : Code → PropT` with the three properties above.

3. Combine this with `H_from_Fint_iff_RealHalts` to build an `InternalisationCandidate ctx` with:

   * `H := H_enc`,
   * totality from the third conjunct of `reflect_for_this_H`,
   * correctness and completeness via the first two conjuncts plus the equivalence with `RealHalts`.

4. This contradicts `no_full_internalisation ctx`.

The final theorem is:

```lean
theorem no_AC_operative_internalisation :
    ¬ ∃ _ : InternalisationWithAC ctx S, True
```

Informal reading:

> There is no way, in a recursive consistent theory of ZFC-strength, to internalise a total choice function `F_int : Code → W_int` whose behaviour on halting codes exactly matches the dynamic AC `AC_dyn` built from the Rev–CH–AC structure, **provided** we also assume the local reflection principle `reflect_for_this_H` for the resulting meta-level halting predicate.
> Otherwise, we would obtain an internal predicate that is total, correct and complete for `RealHalts`, contradicting Turing–Gödel.

---

## 7. Logical status of the components

* The **BasicSemantics** layer (`ModE`/`ThE`/`CloE`) and the **Rev/Trace** layer are fully constructive modulo standard `Mathlib` imports (`Set`, `Nat`).
* The **Turing–Gödel contexts** and the theorem `no_internal_halting_predicate'` are formalised entirely as Lean theorems over abstract structures; they encode the classical diagonal argument.
* The **RevCHACSystem** and `AC_dyn` are definitional: they package assumptions about isomorphisms between `RealHalts`, Rev-halting, CH-local, and a dynamic choice function.
* The Level 2 theorem `no_AC_operative_internalisation` uses an explicit **local reflection axiom** `reflect_for_this_H` to link the specific meta-level halting predicate `H_from_Fint ctx S I` back into the internal theory `T`. This makes explicit the extra meta-logical assumption needed to talk about internalisation of the *specific* operative AC determined by a given `RevCHACSystem` and internalisation kit.

This separation keeps the formal core clean while showing exactly where meta-level reasoning is imported into the internal theory.

---

## 8. How to use / extend

* The current file is self-contained modulo `Mathlib` and the explicit meta-axiom `reflect_for_this_H`.
* To adapt the framework to a concrete theory `T` (e.g. PA or ZFC), one would:

  * choose concrete types `Code` and `PropT`,
  * interpret `Provable`, `FalseT`, `Not`, and `RealHalts`,
  * check that the `TuringGodelContext'` hypotheses are met (via standard arithmetisation),
  * instantiate a concrete `RevCHACSystem` capturing the intended dynamic CH-profile and choice operator,
  * decide in which form a reflection principle analogous to `reflect_for_this_H` is acceptable.

Possible extensions:

* constructing explicit local readings `LR` from proof systems and establishing a `DynamicBridge` in concrete situations,
* connecting the CH-local profile with more familiar formulations of CH or variants,
* exploring variants of the local reflection axiom (weaker, stronger, or differently scoped).

At this stage, the file provides a complete, formal skeleton of the two-level meta-theorem:

1. No perfect internal halting predicate for `RealHalts`.
2. Consequently, under the local reflection assumption `reflect_for_this_H`, no perfect internalisation of the **specific operative AC** induced by the Rev–CH–AC dynamic architecture.
