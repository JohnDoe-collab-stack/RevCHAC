## 0. High-level overview

**What is formalised?**

- A static Galois-style semantics (`ModE`, `ThE`, `CloE`) over a satisfaction relation `Sat`.
- A dynamic halting layer (`Trace`, `up`, `Halts`) plus a reverse halting operator `Rev` built from an abstract kit `RHKit`.
- A local reading `LR : (Set Sentence) → Sentence → Trace` and a bridge saying:
  \[
    φ ∈ CloE(Γ) \;\Longleftrightarrow\; Halts(LR\,Γ\,φ),
  \]
  which transfers semantic consequence into halting of traces.
- An abstract Turing–Gödel context encoding the diagonal argument against total, correct and complete internal halting predicates.
- A `RevCHACSystem` tying together:
  - real halting `RealHalts`,
  - a Rev-based halting predicate on programs,
  - a CH-local profile on the same programs,
  - a dynamic choice operator `F_dyn` on the CH-local sector.

**Key outputs inside Lean**

1. At the “semantic + dynamic” level:

   - `Rev0 K` is extensionally equal to `Halts` on traces for any `RHKit` satisfying `DetectsMonotone K`.
   - Given a local reading `LR` and a `DynamicBridge`, one gets:
     \[
       φ ∈ CloE(Γ) \;\Longleftrightarrow\; verdict\,K\,LR\,Γ\,φ
     \]
     for every admissible kit `K`.

2. At the “meta-theoretic” level (Turing–Gödel context):

   - `no_internal_halting_predicate` / `no_internal_halting_predicate'`:
     there is no single internal predicate `H(e)` that is total, correct and complete for the *real* halting profile `RealHalts(e)`.

3. For a fixed Rev–CH–AC system `S`:

   - One defines a canonical dynamic choice `AC_dyn` on halting codes by transporting `RealHalts` through the Rev-halting and CH-local layers into `F_dyn`.

4. Non-internalisation theorems:

   - **Level 1** (`no_full_internalisation`): no internal predicate in a Turing–Gödel context can perfectly internalise `RealHalts`.
   - **Level 2** (`no_AC_operative_internalisation`): assuming a reflection principle `reflect_RealHalts`, no internal pair `(F_int, Decode)` can reproduce the specific external dynamic choice `AC_dyn` as a single total internal mechanism without contradicting Turing–Gödel.

The remainder of this README explains each layer and theorem in detail.
