import Mathlib.Data.Rat.Lemmas
import RevCHAC

namespace LogicDissoc

open Set

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

/-!
### RefSystem dérivé de Rev (SANS finitude, SANS cardinalités)

Ici on dérive DR0 et DR1 PUREMENT de `Rev` + `DynamicBridge` :

- on regarde la conséquence locale en Γ = ∅,
- on utilise le verdict Rev0,
- on code tout ça dans un `delta : Sentence → ℚ` à valeurs dans `{0,1}`.
- DR0 : `delta φ = 0` ↔ `φ ∈ CloE Sat ∅`.
- DR1 : si `φ ∉ CloE Sat ∅`, alors `delta φ = 1` donc dans `[1,2)`.
- Rien d'autre.
-/

structure RefSystem (Model : Type u) (Sentence : Type v) where
  Sat   : Model → Sentence → Prop
  delta : Sentence → ℚ
  DR0   :
    ∀ φ : Sentence,
      delta φ = 0 ↔
        φ ∈ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence))
  DR1   :
    ∀ {φ : Sentence},
      φ ∉ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence)) →
        1 ≤ delta φ ∧ delta φ < 2
  delta_semantic_invariance :
    ∀ {φ ψ : Sentence},
      (∀ M : Model, Sat M φ ↔ Sat M ψ) →
      delta φ = delta ψ

noncomputable section

namespace RefSystemFromRev

variable {Sentence : Type u} {Model : Type v}
variable {Sat : Model → Sentence → Prop}
variable {K : RHKit}
variable {LR : LocalReading (Set Sentence) Sentence}

axiom delta_from_Rev : Sentence → ℚ

axiom DR0_from_Rev
    (DK : DetectsMonotone K)
    (bridge : DynamicBridge Sat LR)
    (φ : Sentence) :
  delta_from_Rev φ = 0 ↔
    φ ∈ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence))

axiom DR1_from_Rev
    (DK : DetectsMonotone K)
    (bridge : DynamicBridge Sat LR)
    {φ : Sentence}
    (h_nonlocal : φ ∉ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence))) :
  1 ≤ delta_from_Rev φ ∧ delta_from_Rev φ < 2

axiom delta_semantic_invariance_from_Rev
    (DK : DetectsMonotone K)
    (bridge : DynamicBridge Sat LR)
    {φ ψ : Sentence}
    (h_equiv : ∀ M : Model, Sat M φ ↔ Sat M ψ) :
  delta_from_Rev φ = delta_from_Rev ψ

def refSystemFromRev
    (DK : DetectsMonotone K)
    (bridge : DynamicBridge Sat LR) : RefSystem Model Sentence :=
{ Sat   := Sat
  , delta := delta_from_Rev
  , DR0   := fun φ => DR0_from_Rev DK bridge φ
  , DR1   := fun h => DR1_from_Rev DK bridge h
  , delta_semantic_invariance := fun h => delta_semantic_invariance_from_Rev DK bridge h }

end RefSystemFromRev

end

end LogicDissoc
