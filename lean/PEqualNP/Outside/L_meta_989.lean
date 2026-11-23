import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_989

open Matrix MvPolynomial

lemma multiple_of_cross_zero {F : Type} [Field F] {x y : Fin 3 → F}
    (hx : x ≠ 0) (h : x ⨯₃ y = 0) : ∃ c : F, c • x = y := by
  by_contra! hn
  exact (crossProduct_ne_zero_iff_linearIndependent.mpr
    ((LinearIndependent.pair_iff' hx).mpr hn)) h

lemma unique_line {F : Type} [Field F] {p q u v : Fin 3 → F}
    (hp : p ≠ 0) (hq : ∀ c : F, q ≠ c • p) (hu : u ≠ 0)
    (hpu : p ⬝ᵥ u = 0) (hqu : q ⬝ᵥ u = 0)
    (hpv : p ⬝ᵥ v = 0) (hqv : q ⬝ᵥ v = 0) : ∃ c : F, v = c • u := by
  have hn : p ⨯₃ q ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    ((LinearIndependent.pair_iff' hp).mpr fun c => (hq c).symm)
  obtain ⟨a, ha⟩ := multiple_of_cross_zero hn (y := u) (by
    rw [cross_cross_eq_smul_sub_smul, hpu, hqu]; simp)
  obtain ⟨d, hd⟩ := multiple_of_cross_zero hn (y := v) (by
    rw [cross_cross_eq_smul_sub_smul, hpv, hqv]; simp)
  have ha0 : a ≠ 0 := by rintro rfl; simp_all
  exact ⟨d / a, by rw [← ha, ← hd, smul_smul, div_mul_cancel₀ _ ha0]⟩

lemma two_choose (b : ℕ) : 2 * (b + 2).choose 2 = (b + 1) * (b + 2) := by
  have h := Nat.choose_succ_right_eq (b + 2) 1
  simpa [Nat.mul_comm] using h

lemma interpolation {F : Type} [Field F] (k b : ℕ)
    (P : Fin k → MvPolynomial (Fin 3) F) (l : Fin k → Fin 3 → F)
    (hom : ∀ i, (P i).IsHomogeneous b)
    (diag : ∀ i, eval (l i) (P i) ≠ 0)
    (off : ∀ i j, i ≠ j → eval (l j) (P i) = 0) :
    2 * k ≤ (b + 1) * (b + 2) := by
  classical
  let coeffs (i : Fin k) (s : Sym (Fin 3) b) := (P i).coeff s.val.toFinsupp
  have li : LinearIndependent F coeffs := by
    apply Fintype.linearIndependent_iff.mpr
    intro w hw j
    have hz : ∑ i, w i • P i = 0 := by
      ext d
      by_cases hd : d.degree = b
      · let s : Sym (Fin 3) b := ⟨d.toMultiset, by rw [Finsupp.card_toMultiset]; exact hd⟩
        have heq := congrFun hw s
        change (∑ i, w i • coeffs i) s = (0 : F) at heq
        rw [Finset.sum_apply] at heq
        change ∑ i, w i * (P i).coeff (d.toMultiset.toFinsupp) = 0 at heq
        simpa using heq
      · simp [fun i => (hom i).coeff_eq_zero hd]
    have he := congrArg (eval (l j)) hz
    simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, map_zero] at he
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [off i j hij, mul_zero])
      (by simp)] at he
    exact (mul_eq_zero.mp he).resolve_right (diag j)
  have bound := li.fintype_card_le_finrank
  simp only [Module.finrank_pi, Fintype.card_fin, Sym.card_sym_eq_choose] at bound
  rw [show 3 + b - 1 = b + 2 by omega, ← Nat.choose_symm (show b ≤ b+2 by omega), show b+2-b = 2 by omega] at bound
  rw [← two_choose]
  omega

lemma upper : ∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2) := by
  classical
  intro F _ n k b pt l y g hpt hdpt hl hdl hcard hbase hsafe htwo
  have hit (i j : Fin k) (hij : i ≠ j) : ∃ p ∈ y i, pt p ⬝ᵥ l j = 0 := by
    by_contra! hmiss
    obtain ⟨p, q, hpq, hp, hq, hgp, hgq⟩ := htwo i
    have on_other (r : Fin n) (hg : g (fun v => decide (v ∈ y i ∨ v = r)) = true) :
        pt r ⬝ᵥ l j = 0 := by
      obtain ⟨s, hs, h0⟩ := hsafe j _ hg
      rcases of_decide_eq_true hs with hy | rfl
      · exact False.elim (hmiss s hy h0)
      · exact h0
    obtain ⟨c, hc⟩ := unique_line (hpt p) (hdpt p q hpq) (hl i) hp hq
      (on_other p hgp) (on_other q hgq)
    exact hdl i j hij c hc
  have coord (i : Fin k) : ∃ t, l i t ≠ 0 := by
    by_contra! h
    exact hl i (funext h)
  choose t ht using coord
  let form (p : Fin n) : MvPolynomial (Fin 3) F := ∑ s, C (pt p s) * X s
  have ev (p : Fin n) (j : Fin k) : eval (l j) (form p) = pt p ⬝ᵥ l j := by
    simp [form, dotProduct]
  let P (i : Fin k) := (∏ p ∈ y i, form p) * X (t i) ^ (b - (y i).card)
  apply interpolation k b P l
  · intro i
    have hform (p : Fin n) : (form p).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun s _ => isHomogeneous_C_mul_X _ _
    have prodhom : (∏ p ∈ y i, form p).IsHomogeneous (y i).card := by
      simpa using IsHomogeneous.prod (y i) form (fun _ => 1) (fun p _ => hform p)
    have he := prodhom.mul (isHomogeneous_X_pow (t i) (b - (y i).card))
    simpa [P, Nat.add_sub_of_le (hcard i)] using he
  · intro i
    simp only [P, map_mul, map_prod, map_pow, eval_X, ev]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (hbase i)) (pow_ne_zero _ (ht i))
  · intro i j hij
    obtain ⟨p, hpy, hp⟩ := hit i j hij
    simp only [P, map_mul, map_prod, ev]
    rw [Finset.prod_eq_zero hpy hp, zero_mul]

open Matrix

def point {F : Type} [Field F] : (F × F ⊕ Option F) → Fin 3 → F
  | .inl (x, y) => ![1, x, y]
  | .inr (.some z) => ![0, 1, z]
  | .inr .none => ![0, 0, 1]

lemma point_ne {F : Type} [Field F] (p : F × F ⊕ Option F) : point p ≠ 0 := by
  rcases p with ⟨x,y⟩ | (_ | z) <;> simp [point, funext_iff, Fin.forall_fin_succ]

lemma point_unique {F : Type} [Field F] (p q : F × F ⊕ Option F) (c : F)
    (h : point q = c • point p) : p = q := by
  rcases p with ⟨x,y⟩ | (_ | z) <;> rcases q with ⟨a,b⟩ | (_ | d) <;>
    simp_all [point, funext_iff, Fin.forall_fin_succ] <;> grind

lemma point_covers {F : Type} [Field F] (v : Fin 3 → F) :
    ∃ (p : F × F ⊕ Option F) (c : F), v = c • point p := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · exact ⟨.inr .none, v 2, by ext i; fin_cases i <;> simp [point, h0, h1]⟩
    · exact ⟨.inr (.some (v 2 / v 1)), v 1, by
        ext i; fin_cases i <;> simp [point, h0, mul_comm (v 1), h1]⟩
  · exact ⟨.inl (v 1 / v 0, v 2 / v 0), v 0, by
      ext i; fin_cases i <;> simp [point, mul_comm (v 0), h0]⟩

def arc {F A : Type} [Field F] (f : A ↪ F) : Option A → (F × F ⊕ Option F)
  | .some a => .inl (f a, (f a)^2)
  | .none => .inr .none

lemma arc_inj {F A : Type} [Field F] (f : A ↪ F) : Function.Injective (arc f) := by
  rintro (_ | a) (_ | b) h <;> simp_all [arc]

def chord {F A : Type} [Field F] (f : A ↪ F) : Option A → Option A → Fin 3 → F
  | .some a, .some b => ![f a * f b, -(f a + f b), 1]
  | .none, .some a | .some a, .none => ![-f a, 1, 0]
  | .none, .none => ![0, 0, 1]

lemma chord_ne {F A : Type} [Field F] (f : A ↪ F) (a b : Option A) :
    chord f a b ≠ 0 := by
  cases a <;> cases b <;> simp [chord, funext_iff, Fin.forall_fin_succ]

lemma on_chord {F A : Type} [Field F] (f : A ↪ F) (a b z : Option A) (hab : a ≠ b) :
    point (arc f z) ⬝ᵥ chord f a b = 0 ↔ z = a ∨ z = b := by
  cases a <;> cases b <;> cases z <;>
    simp_all [point, arc, chord] <;> try grind
  rename_i a b z
  rw [show f a * f b + (f z * (-f b + -f a) + f z ^ 2) =
    (f z - f a) * (f z - f b) by ring]
  simp [sub_eq_zero]
lemma attainable : ∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2) := by
  classical
  intro F _ _ b hsize
  let f : Fin (b+1) ↪ F := (Fin.castLEEmb hsize).trans (Fintype.equivFin F).symm.toEmbedding
  let A := Option (Fin (b+1))
  let U := F × F ⊕ Option F
  let E := (Finset.univ : Finset A).powersetCard 2
  let pe := Fintype.equivFin U
  let edges := (Fintype.equivFin (↥E)).symm
  let ends (i : Fin (Fintype.card (↥E))) : Finset A := (edges i).val
  have cardA : Fintype.card A = b + 2 := by simp [A]
  have cardE (i) : (ends i).card = 2 := (Finset.mem_powersetCard.mp (edges i).property).2
  have pair (i) := Finset.card_eq_two.mp (cardE i)
  choose a d distinct pairEq using pair
  let vertex (z : A) := pe (arc f z)
  have vinj : Function.Injective vertex := pe.injective.comp (arc_inj f)
  let pt (v : Fin (Fintype.card U)) := point (pe.symm v)
  let line (i : Fin (Fintype.card (↥E))) := chord f (a i) (d i)
  let base (i : Fin (Fintype.card (↥E))) := (Finset.univ \ ends i).image vertex
  let g (x : Fin (Fintype.card U) → Bool) := decide (∃ z : A, ∀ w, w ≠ z → x (vertex w) = true)
  have inc (z : A) (i) : pt (vertex z) ⬝ᵥ line i = 0 ↔ z ∈ ends i := by
    simpa [pt, vertex, line, pairEq, pe] using on_chord f (a i) (d i) z (distinct i)
  have base_mem (i) (z : A) : vertex z ∈ base i ↔ z ∉ ends i := by
    simp [base, Finset.mem_image, vinj.eq_iff]
  refine ⟨_, _, pt, line, base, g, fun p => point_ne _, ?_, ?_, fun i => chord_ne _ _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hpq c hc
    exact hpq (pe.symm.injective (point_unique _ _ c hc))
  · intro v _
    obtain ⟨p,c,h⟩ := point_covers v
    exact ⟨pe p, c, by simpa [pt] using h⟩
  · intro i j hij c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact chord_ne f (a j) (d j) (hc.trans (zero_smul _ _))
    apply hij
    apply edges.injective
    apply Subtype.ext
    change ends i = ends j
    ext z
    rw [← inc, ← inc, hc, dotProduct_smul, smul_eq_mul]
    simp [hc0]
  · intro i
    calc
      (base i).card ≤ (Finset.univ \ ends i).card := Finset.card_image_le
      _ = b := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, cardA, cardE]; omega
  · intro i p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    exact fun h => (Finset.mem_sdiff.mp hz).2 ((inc _ _).mp h)
  · intro x x' hxx hx
    obtain ⟨z,hz⟩ := of_decide_eq_true hx
    exact decide_eq_true ⟨z, fun w hw => hxx _ (hz w hw)⟩
  · intro i x hx
    obtain ⟨z,hz⟩ := of_decide_eq_true hx
    by_cases ha : a i = z
    · exact ⟨vertex (d i), hz _ (ha ▸ (distinct i).symm), (inc _ _).mpr (by simp [pairEq])⟩
    · exact ⟨vertex (a i), hz _ ha, (inc _ _).mpr (by simp [pairEq])⟩
  · intro i
    refine ⟨vertex (a i), vertex (d i), fun h => distinct i (vinj h),
      (inc _ _).mpr (by simp [pairEq]), (inc _ _).mpr (by simp [pairEq]), ?_, ?_⟩
    · apply decide_eq_true
      refine ⟨d i, fun w hw => decide_eq_true ?_⟩
      by_cases h : w = a i
      · exact Or.inr (congrArg vertex h)
      · exact Or.inl ((base_mem _ _).mpr (by simp [pairEq, h, hw]))
    · apply decide_eq_true
      refine ⟨a i, fun w hw => decide_eq_true ?_⟩
      by_cases h : w = d i
      · exact Or.inr (congrArg vertex h)
      · exact Or.inl ((base_mem _ _).mpr (by simp [pairEq, h, hw]))
  · simpa [E, Finset.card_powersetCard, cardA] using two_choose b

end PEqualNP.Outside.L_meta_989

theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) :=
  ⟨PEqualNP.Outside.L_meta_989.upper, PEqualNP.Outside.L_meta_989.attainable⟩
