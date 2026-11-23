import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta240Aux

open PEqualNP.MetaComplexity

theorem getD_ofFn_lt (n : ℕ) (x : Fin n → Bool) {i : ℕ} (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  have hl : i < (List.ofFn x).length := by simpa [List.length_ofFn] using h
  exact (List.getD_eq_getElem _ _ hl).trans (List.getElem_ofFn hl)

theorem getD_ofFn_ge (n : ℕ) (x : Fin n → Bool) {i : ℕ} (h : ¬ i < n) :
    (List.ofFn x).getD i false = false :=
  List.getD_eq_default _ _ (by simpa [List.length_ofFn] using h)

theorem getD_all_false (n : ℕ) (i : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD i false = false := by
  rcases Nat.lt_or_ge i n with h | h
  · exact getD_ofFn_lt n _ h
  · exact getD_ofFn_ge n _ (by omega)

theorem eval_gates_nil (C : BinaryCircuit) (x : List Bool) :
    C.gates = [] → C.eval x = x.getD C.output false := by
  intro h
  cases C with
  | mk g o =>
    cases g with
    | nil => exact rfl
    | cons hd tl => cases h

/-- The gate that ignores both wires and carries true. -/
def trueGate : BinaryGate :=
  { op := fun _ _ => true
    left := 0
    right := 0 }

/-- The one gate circuit reading that gate, with output wire `o`. -/
def trueCircuit (o : ℕ) : BinaryCircuit := ⟨[trueGate], o⟩

/-- Reading the wire a one gate circuit appends. -/
theorem getD_append_self (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  rw [List.getD_append_right l [b] false l.length (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Reading the wire a one gate circuit appends, at any index equal to the length. -/
theorem getD_append_at (l : List Bool) (b : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [b]).getD n false = b := by
  rw [← h, getD_append_self]

/-- The one gate circuit appends exactly one wire, whose value is true. -/
theorem trueCircuit_eval (o : ℕ) (x : List Bool) :
    (trueCircuit o).eval x = (x ++ [true]).getD o false := rfl

/-- On n inputs the one gate circuit with output wire n computes true. -/
theorem true_eval (n : ℕ) (x : Fin n → Bool) : (trueCircuit n).eval (List.ofFn x) = true := by
  rw [trueCircuit_eval]
  exact getD_append_at _ _ _ List.length_ofFn

end PEqualNP.Outside.LMeta240Aux

theorem PEqualNP.Outside.L_meta_240 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨C, hsize, heval⟩
    by_contra h
    have hs : s = 0 := by omega
    have hlen : C.gates.length = 0 := by
      simpa [PEqualNP.MetaComplexity.BinaryCircuit.size, hs] using hsize
    have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hlen
    have he := heval (fun _ : Fin n => false)
    rw [PEqualNP.Outside.LMeta240Aux.eval_gates_nil C _ hnil] at he
    rw [PEqualNP.Outside.LMeta240Aux.getD_all_false] at he
    exact Bool.noConfusion he
  · intro hs
    refine ⟨PEqualNP.Outside.LMeta240Aux.trueCircuit n, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.BinaryCircuit.size,
        PEqualNP.Outside.LMeta240Aux.trueCircuit, PEqualNP.Outside.LMeta240Aux.trueGate]
      exact hs
    · intro x
      exact PEqualNP.Outside.LMeta240Aux.true_eval n x
