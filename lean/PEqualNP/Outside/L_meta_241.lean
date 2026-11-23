import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta241Aux

open PEqualNP.MetaComplexity

/-- The circuit whose gate list is empty and whose output wire is `o`. -/
def nilCircuit (o : ℕ) : BinaryCircuit := ⟨[], o⟩

/-- A circuit with no gates evaluates to the value its output wire already has. -/
theorem eval_gates_nil (C : BinaryCircuit) (x : List Bool) :
    C.gates = [] → C.eval x = x.getD C.output false := by
  intro h
  cases C with
  | mk g o =>
    cases g with
    | nil => exact rfl
    | cons hd tl => cases h

/-- Reading an input bit below `n` gives that bit. -/
theorem getD_ofFn_lt (n : ℕ) (x : Fin n → Bool) {i : ℕ} (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  have hl : i < (List.ofFn x).length := by simpa [List.length_ofFn] using h
  exact (List.getD_eq_getElem _ _ hl).trans (List.getElem_ofFn hl)

/-- Reading past the input bits gives the default. -/
theorem getD_ofFn_ge (n : ℕ) (x : Fin n → Bool) {i : ℕ} (h : ¬ i < n) :
    (List.ofFn x).getD i false = false :=
  List.getD_eq_default _ _ (by simpa [List.length_ofFn] using h)

/-- Every bit of the all true input reads true. -/
theorem getD_all_true (n : ℕ) (i : ℕ) (h : i < n) :
    (List.ofFn (fun _ : Fin n => true)).getD i false = true :=
  getD_ofFn_lt n _ h

/-- Any read of the all false input gives false. -/
theorem getD_all_false (n : ℕ) (i : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD i false = false := by
  rcases Nat.lt_or_ge i n with h | h
  · exact getD_ofFn_lt n _ h
  · exact getD_ofFn_ge n _ (by omega)

/-- The circuit with no gates adds no wire: its wire list is the input list. -/
theorem nilCircuit_eval (n : ℕ) (x : List Bool) : (nilCircuit n).eval x = x.getD n false := rfl

/-- The empty circuit on n inputs computes false: its output wire n does not exist. -/
theorem false_eval (n : ℕ) (x : Fin n → Bool) :
    (nilCircuit n).eval (List.ofFn x) = false := by
  rw [nilCircuit_eval, getD_ofFn_ge n x (h := by omega)]

end PEqualNP.Outside.LMeta241Aux

theorem PEqualNP.Outside.L_meta_241 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨PEqualNP.Outside.LMeta241Aux.nilCircuit n, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.BinaryCircuit.size, PEqualNP.Outside.LMeta241Aux.nilCircuit]
  · intro x
    exact PEqualNP.Outside.LMeta241Aux.false_eval n x
