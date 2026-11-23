import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta238Aux

open PEqualNP.MetaComplexity

theorem getD_ofFn_lt (n : ℕ) (x : Fin n → Bool) {i : ℕ} (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  have hl : i < (List.ofFn x).length := by simpa [List.length_ofFn] using h
  exact (List.getD_eq_getElem _ _ hl).trans (List.getElem_ofFn hl)

theorem getD_ofFn_ge (n : ℕ) (x : Fin n → Bool) {i : ℕ} (h : ¬ i < n) :
    (List.ofFn x).getD i false = false :=
  List.getD_eq_default _ _ (by simpa [List.length_ofFn] using h)

theorem getD_all_true (n : ℕ) (i : ℕ) (h : i < n) :
    (List.ofFn (fun _ : Fin n => true)).getD i false = true :=
  getD_ofFn_lt n _ h

theorem eval_gates_nil (C : BinaryCircuit) (x : List Bool) :
    C.gates = [] → C.eval x = x.getD C.output false := by
  intro h
  cases C with
  | mk g o =>
    cases g with
    | nil => exact rfl
    | cons hd tl => cases h

/-- The input that is true on wire 0 and false on wire 1. -/
def tf : Fin 2 → Bool := fun i => decide (i = 0)

theorem tf_zero : xor (tf 0) (tf 1) = true := by decide

theorem tt_xor : xor ((fun _ : Fin 2 => true) 0) ((fun _ : Fin 2 => true) 1) = false := by
  decide

/-- Reading the wire a one gate circuit appends. -/
theorem getD_append_self (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  rw [List.getD_append_right l [b] false l.length (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Reading the wire a one gate circuit appends, at any index equal to the length. -/
theorem getD_append_at (l : List Bool) (b : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [b]).getD n false = b := by
  rw [← h, getD_append_self]

/-- The gate that xors the first two wires. -/
def xorGate : BinaryGate :=
  { op := xor
    left := 0
    right := 1 }

/-- That one gate, with output wire 2: the wire the gate itself produces. -/
def xorCircuit : BinaryCircuit := ⟨[xorGate], 2⟩

theorem xorCircuit_eval (x : List Bool) :
    (xorCircuit).eval x = (x ++ [xor (x.getD 0 false) (x.getD 1 false)]).getD 2 false := rfl

theorem xor_eval (x : Fin 2 → Bool) :
    (xorCircuit).eval (List.ofFn x) = xor (x 0) (x 1) := by
  have h0 : (List.ofFn x).getD 0 false = x 0 := getD_ofFn_lt 2 x (by decide)
  have h1 : (List.ofFn x).getD 1 false = x 1 := getD_ofFn_lt 2 x (by decide)
  rw [xorCircuit_eval, getD_append_at _ _ _ List.length_ofFn, h0, h1]

end PEqualNP.Outside.LMeta238Aux

theorem PEqualNP.Outside.L_meta_238 :
    ∀ s : ℕ,
      PEqualNP.MetaComplexity.HasBinarySize 2
        (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hsize, heval⟩
    by_contra h
    have hs : s = 0 := by omega
    have hlen : C.gates.length = 0 := by
      simpa [PEqualNP.MetaComplexity.BinaryCircuit.size, hs] using hsize
    have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hlen
    have heq : ∀ x : Fin 2 → Bool,
        (List.ofFn x).getD C.output false = xor (x 0) (x 1) := by
      intro x
      exact (PEqualNP.Outside.LMeta238Aux.eval_gates_nil C _ hnil).symm.trans (heval x)
    rcases Nat.lt_or_ge C.output 2 with ho | ho
    · have h1 := heq (fun _ : Fin 2 => true)
      rw [PEqualNP.Outside.LMeta238Aux.getD_all_true 2 _ ho,
        PEqualNP.Outside.LMeta238Aux.tt_xor] at h1
      exact Bool.noConfusion h1
    · have h1 := heq PEqualNP.Outside.LMeta238Aux.tf
      rw [PEqualNP.Outside.LMeta238Aux.getD_ofFn_ge 2 _ (h := by omega),
        PEqualNP.Outside.LMeta238Aux.tf_zero] at h1
      exact Bool.noConfusion h1
  · intro hs
    refine ⟨PEqualNP.Outside.LMeta238Aux.xorCircuit, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.BinaryCircuit.size,
        PEqualNP.Outside.LMeta238Aux.xorCircuit, PEqualNP.Outside.LMeta238Aux.xorGate]
      exact hs
    · intro x
      exact PEqualNP.Outside.LMeta238Aux.xor_eval x
