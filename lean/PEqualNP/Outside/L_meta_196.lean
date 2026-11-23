import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_196

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).length
      = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

lemma fold_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).getD i false
      = x.getD i false := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), step_getD _ _ _ hi]

end PEqualNP.Outside.L_meta_196

open PEqualNP.Outside.L_meta_196

theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hj hh x hne
  obtain ⟨gates, out⟩ := C
  simp only at hj
  have hjl : j < gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hg : gates[j] = ⟨GateOp.or, [a, h]⟩ := by
    rw [List.getElem?_eq_getElem hjl] at hj
    exact Option.some.inj hj
  set s := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)] with hs
  set x0 := List.ofFn x with hx0
  have hsplit : ∀ g : Gate, gates.set j g = gates.take j ++ g :: gates.drop (j + 1) := by
    intro g
    rw [List.set_eq_take_append_cons_drop]
    simp [hjl]
  have horig : gates = gates.take j ++ gates[j] :: gates.drop (j + 1) := by
    rw [← hsplit, List.set_getElem_self]
  set P := (gates.take j).foldl s x0 with hP
  have hPlen : P.length = n + j := by
    rw [hP, fold_length]
    simp [hx0, List.length_take]
    omega
  have hW : ∀ g : Gate, (gates.take j ++ g :: gates.drop (j + 1)).foldl s x0
      = (gates.drop (j + 1)).foldl s (s P g) := by
    intro g
    rw [List.foldl_append, List.foldl_cons]
  have hval : ∀ g : Gate,
      ((gates.take j ++ g :: gates.drop (j + 1)).foldl s x0).getD h false = P.getD h false := by
    intro g
    rw [hW, fold_getD _ _ _ (by simp [hs]; omega), hs, step_getD _ _ _ (by omega)]
  have hCw : (Circuit.wires ⟨gates, out⟩ x0) = (gates.take j ++ gates[j] :: gates.drop (j + 1)).foldl s x0 := by
    conv_lhs => rw [Circuit.wires, horig]
  set W' := (gates.take j ++ (⟨GateOp.or, [a]⟩ : Gate) :: gates.drop (j + 1)).foldl s x0 with hW'
  have hW'len : W'.length = n + gates.length := by
    rw [hW', fold_length]
    simp [hx0, List.length_take, List.length_drop]
    omega
  have hmod : PEqualNP.MetaComplexity.circuitFun n
      { gates := gates.set j ⟨GateOp.or, [a]⟩ ++ [⟨GateOp.or, [out, h]⟩], output := n + gates.length } x
      = (W'.getD out false || W'.getD h false) := by
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires]
    rw [List.foldl_append, hsplit, ← hx0]
    change (s W' ⟨GateOp.or, [out, h]⟩).getD (n + gates.length) false = _
    simp [hs, List.getD_eq_getElem?_getD, hW'len, GateOp.eval]
  have hhC : (Circuit.wires ⟨gates, out⟩ x0).getD h false = P.getD h false := by
    rw [hCw, hval]
  simp only [Circuit.size] at hne
  rw [hmod] at hne
  have hW'h : W'.getD h false = P.getD h false := by rw [hW', hval]
  cases hPh : P.getD h false with
  | true =>
    right
    refine ⟨by rw [hhC, hPh], ?_⟩
    rw [hW'h, hPh, Bool.or_true] at hne
    cases hf : f x
    · rfl
    · exact absurd hf.symm hne
  | false =>
    left
    have hgate : s P ⟨GateOp.or, [a]⟩ = s P gates[j] := by
      rw [hg]
      have hPh' : P[h]?.getD false = false := by rwa [List.getD_eq_getElem?_getD] at hPh
      simp [hs, GateOp.eval, hPh']
    have hsame : W' = Circuit.wires ⟨gates, out⟩ x0 := by
      rw [hCw, hW', hW, hW, hgate]
    rw [hW'h, hPh, Bool.or_false, hsame] at hne
    simpa [PEqualNP.MetaComplexity.circuitFun, Circuit.eval] using hne
