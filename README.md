# RevCHAC

> **Lean Version:** `leanprover/lean4:v4.26.0-rc2`
> **Main File:** `RevCHAC/RevCHAC.lean`

This repository currently consists of a single Lean file implementing the following architecture:

- a purely semantic Galois layer over a satisfaction relation,
- a dynamic halting layer built from traces and a “reverse halting” operator `Rev`,
- a local reading `LR` that realises semantic consequence as halting of traces,
- an abstract Turing–Gödel context encoding the standard diagonal obstruction,
- a `RevCHACSystem` that aligns real halting, a Rev-based halting profile, a CH-local profile, and a dynamic choice operator,
- two levels of “non-internalisation” meta-theorems for halting and for the specific operative AC built from this system.

The result is a precise Lean formalisation of the slogan: **there is a concrete dynamic halting/choice structure, definable from ℕ and basic semantics, that no recursive consistent theory of ZFC-strength can fully internalise as a single total, correct and complete predicate.**

---

## 1. Static semantic layer: `ModE`, `ThE`, `CloE`

The file starts by fixing:

- a type `Sentence`,
- a type `Model`,
- a satisfaction relation
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

In the namespace `LogicDissoc`, it proves the usual closure-operator properties:

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

A **trace** is defined as a time-indexed proposition:

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

The intended admissibility condition is `DetectsMonotone K`:

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

Thus:

> Any “reverse-halting” mechanism that correctly detects eventual truth on all monotone families, once fed through `up`, necessarily collapses to ordinary halting on traces.

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
* and the **robust verdict** induced by `Rev0`:

  ```lean
  def verdict (LR : LocalReading Context Sentence) (Γ : Context) (φ : Sentence) : Prop :=
    Rev0 K (LR Γ φ)
  ```

Using the `Rev0_iff_Halts` lemma, one gets:

```lean
lemma verdict_iff_Prov
  (DK : DetectsMonotone K)
  (LR : LocalReading Context Sentence)
  (Γ : Context) (φ : Sentence) :
  verdict K LR Γ φ ↔ Prov LR Γ φ
```

Specialising contexts to sets of sentences, the file introduces the **dynamic bridge**:

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

So, under the bridge, semantic consequence `φ ∈ CloE Γ` coincides with the Rev-based verdict on the trace `LR Γ φ`, uniformly in all admissible kits `K`.

This cleanly separates:

* the static Galois/ZFC layer `(ModE, ThE, CloE)`,
* the dynamic halting layer `(Trace, Halts, Rev, Rev0)`,
* and the specific local reading `LR` which ties them together.

---

## 4. Turing–Gödel meta-context

The next part formalises an abstract Turing–Gödel setting in Lean.

### 4.1. First version: `TuringGodelContext`

In the inner `MetaTheorem` section, the file defines:

```lean
structure TuringGodelContext where
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
theorem no_internal_halting_predicate
  (ctx : TuringGodelContext Code PropT) :
  ¬ ∃ (H : Code → PropT),
      (∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))) ∧
      (∀ e, ctx.RealHalts e → ctx.Provable (H e)) ∧
      (∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e)))
```

The proof follows the standard diagonal argument:
apply `diagonal_program` to `H`, then case-split on `RealHalts e` and derive a contradiction with consistency in both cases.

### 4.2. Second version: `TuringGodelContext'` and `InternalHaltingPredicate`

For the later layers, a slightly re-packaged context is introduced:

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

An internal halting predicate with the expected properties is:

```lean
structure InternalHaltingPredicate (ctx : TuringGodelContext' Code PropT) where
  H       : Code → PropT
  total   : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))
```

The theorem:

```lean
theorem no_internal_halting_predicate'
  (ctx : TuringGodelContext' Code PropT) :
  ¬ ∃ _ : InternalHaltingPredicate ctx, True
```

is again proved by the diagonal argument, now phrased via the `InternalHaltingPredicate` structure.

This will be the main input for Level 1 of the non-internalisation result.

---

## 5. Rev–CH–AC systems and dynamic AC on codes

The `RevCH` section introduces abstract structures to talk about “Rev halting” and “CH-profile” on the same type of programs:

```lean
structure RevHalting (Prog : Type) where
  Halts : Prog → Prop

structure CHProfile (Prog : Type) where
  CHFlag : Prog → Prop
```

An isomorphism between the two is:

```lean
structure RevCHIso {Prog : Type}
    (R : RevHalting Prog) (C : CHProfile Prog) : Prop where
  iso : ∀ p : Prog, R.Halts p ↔ C.CHFlag p
```

From such an `iso`, one extracts:

* an equivalence of subtypes `{p // R.Halts p} ≃ {p // C.CHFlag p}` (`RevCHIso.toEquiv`),
* and conversely, given such an equivalence preserving the underlying `Prog`, one reconstructs a `RevCHIso` (`RevCHIso.ofEquiv`).

This formalises precisely the slogan “Rev halting is isomorphic to CH”.

### 5.1. `RevCHACSystem`

Over a `TuringGodelContext'`, the file then defines:

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
* `Halts_rev : Prog → Prop` is the Rev-based halting predicate on programs,
* `CH_local : Prog → Prop` is the local CH-profile,
* `F_dyn` is a dynamic choice operator defined on the CH-local fragment,
* `iso_real_rev` and `iso_rev_CH` identify the three profiles: real halting, Rev-halting, and CH-local.

From this, the meta profile on codes and the dynamic AC are defined by pullback:

```lean
def H_forbidden (ctx : TuringGodelContext' Code PropT) : Code → Prop :=
  ctx.RealHalts

def CH_on_code (S : RevCHACSystem ctx) : Code → Prop :=
  fun e => S.CH_local (S.embed e)

theorem H_forbidden_iff_CH_on_code (e : Code) :
    H_forbidden ctx e ↔ CH_on_code S e
```

and

```lean
def AC_dyn (e : Code) (h : ctx.RealHalts e) : S.Witness :=
  let p := S.embed e
  have h_rev : S.Halts_rev p :=
    (S.iso_real_rev e).mp h
  have h_CH : S.CH_local p :=
    (S.iso_rev_CH p).mp h_rev
  S.F_dyn ⟨p, h_CH⟩
```

So `AC_dyn` is a **dynamic AC on codes**, defined exactly on those `e` that really halt, and given canonically by:

`RealHalts(e)` → `Halts_rev(embed e)` → `CH_local(embed e)` → `F_dyn`.

---

## 6. Internalisation theorems

### 6.1. Level 1: no full internalisation

A candidate internalisation of the dynamic halting profile is:

```lean
structure InternalisationCandidate where
  H       : Code → PropT
  total   : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))
```

This has exactly the same shape as `InternalHaltingPredicate ctx`, and the theorem:

```lean
theorem no_full_internalisation :
    ¬ ∃ _ : InternalisationCandidate ctx, True
```

is obtained by reusing `no_internal_halting_predicate' ctx` via a simple packaging argument.

Interpretation:

> Even before mentioning CH or AC, there is no way for `T` to have a single internal predicate `H(e)` that is total, correct and complete for the real halting profile `RealHalts(e)`, in the presence of the Turing–Gödel context.

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

* `F_int` is an internal choice-like function on codes,
* `Decode` maps internal witnesses to external `S.Witness`,
* the axiom `correct_on_halting` requires that, whenever `e` really halts, `Decode (F_int e)` *matches* the dynamically defined `AC_dyn ctx S e h` (for that code and its real halting witness).

From such an `InternalisationWithAC`, one can define a meta-level predicate:

```lean
def H_from_Fint (I : InternalisationWithAC ctx S) (e : Code) : Prop :=
  ∃ h : ctx.RealHalts e, I.Decode (I.F_int e) = AC_dyn ctx S e h
```

This satisfies:

```lean
lemma H_from_Fint_iff_RealHalts
    (I : InternalisationWithAC ctx S) (e : Code) :
    H_from_Fint ctx S I e ↔ ctx.RealHalts e
```

So `H_from_Fint` **decides exactly** the real halting predicate at the meta-level.

To connect this with the internal theory `T`, an explicit reflection axiom is introduced:

```lean
axiom reflect_RealHalts :
  ∀ {Code PropT : Type}
    (ctx : TuringGodelContext' Code PropT)
    (H : Code → Prop),
    (∀ e, H e ↔ ctx.RealHalts e) →
    ∃ H_enc : Code → PropT,
      (∀ e, ctx.RealHalts e → ctx.Provable (H_enc e)) ∧
      (∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H_enc e)))
```

This expresses:

> If a meta-level predicate `H` is extensionally equal to `RealHalts`, then there is an **internal** predicate `H_enc` that is correct and complete for `RealHalts` as seen by `T`.

Using `reflect_RealHalts` with `H := H_from_Fint ctx S I`, one gets an internal `H_enc` and builds an `InternalisationCandidate ctx` from it. This contradicts `no_full_internalisation`.

The final theorem is:

```lean
theorem no_AC_operative_internalisation :
    ¬ ∃ _ : InternalisationWithAC ctx S, True
```

Informal reading:

> There is no way, in a recursive consistent theory of Turing–Gödel strength, to internalise a total choice function `F_int : Code → W_int` whose behaviour on halting codes exactly matches the dynamic AC `AC_dyn` built from the Rev–CH–AC structure.
> Otherwise, via reflection, one would reconstruct an internal predicate that is total, correct and complete for `RealHalts`, contradicting Turing–Gödel.

---

## 7. Logical status of the components

* The **BasicSemantics** layer (ModE/ThE/CloE) and the **Rev/Trace** layer are fully constructive and require only standard `Mathlib` imports (`Set`, `Nat`, classical choice).
* The **Turing–Gödel contexts** and the impossibility theorems `no_internal_halting_predicate` and `no_internal_halting_predicate'` are formalised entirely in Lean as theorems over abstract structures; they encode the classical diagonal argument.
* The **RevCHACSystem** and `AC_dyn` are definitional: they package assumptions about isomorphisms between RealHalts, Rev-halting, CH-local, and a dynamic choice function.
* The Level 2 theorem `no_AC_operative_internalisation` uses an explicit **reflection axiom** `reflect_RealHalts` to link meta-level predicates back into `PropT`. This isolates the extra meta-logical assumption needed to talk about internalisation of the specific operative AC.

This distinction keeps the formal core clean while making explicit where meta-level reasoning is imported into the internal theory.

---

## 8. How to use / extend

* The current file is self-contained modulo `Mathlib` and the two abstract axioms (`Classical` choice and `reflect_RealHalts`).
* To adapt the framework to a concrete theory `T` (e.g. PA or ZFC), one would:

  * choose concrete types `Code` and `PropT`,
  * interpret `Provable`, `FalseT`, `Not`, and `RealHalts`,
  * check that the `TuringGodelContext'` hypotheses are met (typically via standard arithmetisation),
  * instantiate a concrete `RevCHACSystem` capturing the intended dynamic CH-profile and choice operator.

Further development could include:

* constructing explicit local readings `LR` from proof systems, and establishing a `DynamicBridge` in concrete situations,
* connecting the CH-local profile with more familiar formulations of CH or variants,
* exploring variants of `reflect_RealHalts` with weaker or different reflection principles.

At this stage, the file already provides a complete, formal skeleton of the two-level meta-theorem:

1. No perfect internal halting predicate for `RealHalts`.
2. Consequently, no perfect internalisation of the **specific operative AC** induced by the Rev–CH–AC dynamic architecture.

