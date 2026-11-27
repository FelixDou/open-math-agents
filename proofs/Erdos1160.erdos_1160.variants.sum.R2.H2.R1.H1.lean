import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Abel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Data.Set.Card

/-!
# Nilpotent groups below a power of two

For m ≥ 256 this file bounds the combined contribution of every nilpotent group
of odd order below 2^m. The pointwise bound also applies to even orders when
11 * v₂(n) ≤ 7 * m and compares with the counts at m, m-1, and m-2.
At infinitely many dyadic endpoints the proof covers all nilpotent groups
of smaller order, including all smaller powers of two.

The lower-bound construction below is reproduced from @kamaleshanantha, PR
393, revision 32f058d79b9fa0970b1a92cc8894b281af5fd849. The central-extension
count is reproduced from @michelzerasafadaum-gif, PR 3102, revision
13a838bca951536da420d70057678a1bfb4a4f8d. The Sylow counting argument,
exponent comparison, and interval estimate are in Erdos1160.NilpotentCount.
-/


/-
A direct proof of the Higman-type lower bound for the number of groups of
order 2^m, by counting class-two central extensions over the binary field.
The lower bound and its infinite-subsequence corollary use only this count.
-/

/- Relating the canonical count of group isomorphism classes to finite
multiplication tables modulo simultaneous relabeling of their entries. -/

namespace Erdos1160.Tables

open CategoryTheory

/-- The group isomorphism classes counted by the upstream function. -/
def orderClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}

/-- A labeled multiplication table which is realized by a group law. -/
def GroupTable (n : ℕ) :=
  { t : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = t }

instance {n : ℕ} : Finite (GroupTable n) := by
  unfold GroupTable
  infer_instance

/-- Bundle a labeled table as a finite group. -/
noncomputable abbrev model {n : ℕ} (t : GroupTable n) : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin n) t.property.choose inferInstance

/-- Evaluate a product using the multiplication of the specified bundled group. -/
def product (G : FiniteGrp) (a b : G) : G := a * b

theorem model_mul {n : ℕ} (t : GroupTable n) (a b : Fin n) :
    product (model t) a b = t.val a b :=
  congrFun (congrFun t.property.choose_spec a) b

/-- The isomorphism class of a labeled table. -/
noncomputable def groupClass {n : ℕ} (t : GroupTable n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (model t)

/-- A multiplication-preserving bijection gives an isomorphism in the category
of finite groups. -/
theorem iso_of_mul_equiv {G H : FiniteGrp} (e : G ≃ H)
    (h : ∀ a b, e (product G a b) = product H (e a) (e b)) : Nonempty (G ≅ H) := by
  let f : G ≃* H := { e with map_mul' := h }
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩

/-- Every group of order n can be labeled with the elements of Fin n. -/
theorem range_groupClass (n : ℕ) : Set.range (@groupClass n) = orderClasses n := by
  ext c
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨model t, Nat.card_fin n, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : GroupTable n := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (model_mul t a b)).trans (e.apply_symm_apply (e a * e b))

theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_groupClass]
  exact Set.finite_range _

end Erdos1160.Tables

/-
Counting abstract groups using marked presentations. A finite family may
contain several isomorphic groups. If an isomorphism preserving all marks
determines the parameter, each class has at most as many parameters as
there are ordered tuples of marks in one representative.
-/

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- Count by the fibers of a map between finite types. -/
theorem card_le_of_fiber_bound {A B : Type*} [Finite A] [Finite B] (f : A → B)
    (M : ℕ) (h : ∀ b : B, Nat.card {a : A // f a = b} ≤ M) :
    Nat.card A ≤ Nat.card B * M := by
  classical
  let : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _b : B, M := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * M := by simp [Nat.card_eq_fintype_card]

end Erdos1160.PresentationCount

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- If comparisons with one fixed representative have finite codes, and a
code determines the source parameter, the number of isomorphic parameters
in each class is at most the size of the code space. -/
theorem card_le_of_relative_codes {A C : Type*} [Finite A] [Finite C] {n : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (code : ∀ a b : A, (X a ≃* X b) → C)
    (sep : ∀ (a b r : A) (e : X a ≃* X r) (f : X b ≃* X r),
      code a r e = code b r f → a = b) :
    Nat.card A ≤ Erdos1160.g n * Nat.card C := by
  classical
  let classOf (a : A) : Tables.orderClasses n := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  let : Finite (Tables.orderClasses n) := (Tables.orderClasses_finite n).to_subtype
  apply card_le_of_fiber_bound classOf (Nat.card C)
  intro c
  let F := {a : A // classOf a = c}
  by_cases hn : Nonempty F
  · let r := Classical.choice hn
    have sameClass (a : F) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (X a.val)
        = Quotient.mk _ (X r.val) :=
      congrArg Subtype.val (a.property.trans r.property.symm)
    let transport (a : F) : X a.val ≃* X r.val :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact (sameClass a)))).groupIsoToMulEquiv
    let encode (a : F) : C := code a.val r.val (transport a)
    exact Nat.card_le_card_of_injective encode (fun {a b} h =>
      Subtype.ext (sep a.val b.val r.val (transport a) (transport b) h))
  · have empty : IsEmpty F := not_nonempty_iff.mp hn
    change Nat.card F ≤ Nat.card C
    simp

end Erdos1160.PresentationCount

namespace Erdos1160Growth

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The central extension built from an arbitrary biadditive map, with two visible coordinates. -/
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BilinearExtension

variable {B : V →+ V →+ W}

theorem ext {x y : BilinearExtension B} (hb : x.base = y.base) (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  simp_all

instance : Mul (BilinearExtension B) :=
  ⟨fun x y => ⟨x.base + y.base, x.fiber + y.fiber + B x.base y.base⟩⟩

instance : One (BilinearExtension B) := ⟨⟨0,0⟩⟩

instance : Inv (BilinearExtension B) :=
  ⟨fun x => ⟨-x.base, -x.fiber + B x.base x.base⟩⟩

@[simp] theorem mul_base (x y : BilinearExtension B) :
    (x*y).base = x.base + y.base := rfl
@[simp] theorem mul_fiber (x y : BilinearExtension B) :
    (x*y).fiber = x.fiber + y.fiber + B x.base y.base := rfl
@[simp] theorem inv_base (x : BilinearExtension B) : (x⁻¹).base = -x.base := rfl
@[simp] theorem inv_fiber (x : BilinearExtension B) :
    (x⁻¹).fiber = -x.fiber + B x.base x.base := rfl
@[simp] theorem one_base : (1 : BilinearExtension B).base = 0 := rfl
@[simp] theorem one_fiber : (1 : BilinearExtension B).fiber = 0 := rfl

instance : Group (BilinearExtension B) where
  mul_assoc x y z := by
    apply BilinearExtension.ext <;> simp [map_add] <;> abel
  one_mul x := by
    apply BilinearExtension.ext <;> simp
  mul_one x := by
    apply BilinearExtension.ext <;> simp
  inv_mul_cancel x := by
    apply BilinearExtension.ext <;> simp

def coordinateEquiv (B : V →+ V →+ W) : BilinearExtension B ≃ V × W where
  toFun x := (x.base, x.fiber)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card (B : V →+ V →+ W) :
    Nat.card (BilinearExtension B) = Nat.card V * Nat.card W := by
  rw [Nat.card_congr (coordinateEquiv B), Nat.card_prod]

open scoped commutatorElement

theorem commutator_formula (x y : BilinearExtension B) :
    ⁅x, y⁆ = ⟨0, B x.base y.base - B y.base x.base⟩ := by
  rw [commutatorElement_def]
  apply BilinearExtension.ext <;> simp [map_add, map_neg]
  abel

end BilinearExtension

end Erdos1160Growth

namespace Erdos1160Growth.BilinearExtension

open scoped commutatorElement

private theorem double_zero {s : ℕ} (w : Fin s → ZMod 2) : w+w = 0 := by
  funext i
  have h : ∀ z : ZMod 2, z+z = 0 := by decide
  exact h (w i)

theorem lift_square_eq_of_base_eq {V : Type*} [AddCommGroup V] {s : ℕ}
    {B : V →+ V →+ (Fin s → ZMod 2)} {a b : BilinearExtension B} (h : a.base = b.base) :
    a * a = b * b := by
  apply BilinearExtension.ext
  · simp only [mul_base, h]
  · simp only [mul_fiber, double_zero, zero_add, h]

theorem lift_commutator_eq_of_base_eq {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {B : V →+ V →+ W} {a b c d : BilinearExtension B}
    (hac : a.base = c.base) (hbd : b.base = d.base) :
    ⁅a,b⁆ = ⁅c,d⁆ := by
  rw [commutator_formula, commutator_formula, hac, hbd]

end Erdos1160Growth.BilinearExtension

open scoped BigOperators commutatorElement

namespace Erdos1160Growth.SharpFamily

abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Slot (d s : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin (d-s)
abbrev Param (d s : ℕ) := Slot d s → V s

variable {d s : ℕ}

def basis {k : ℕ} (i : Fin k) : V k := Pi.single i 1

def entry (t : Param d s) (i j : Fin d) : V s :=
  if h : j < i then t (.inl ⟨i, ⟨j.val,h⟩⟩)
  else if i = j then
    if hl : i.val < s then basis ⟨i.val, hl⟩
    else t (.inr ⟨i.val - s, by have := i.isLt; omega⟩)
  else 0

theorem entry_fixed {t : Param d s} (i : Fin s) (hs : s ≤ d) :
    entry t (Fin.castLE hs i) (Fin.castLE hs i) = basis i := by
  simp [entry, i.isLt]

theorem entry_upper {t : Param d s} {i j : Fin d} (h : i < j) : entry t i j = 0 := by
  simp [entry, not_lt_of_ge (le_of_lt h), ne_of_lt h]

theorem entry_injective {t u : Param d s} (h : ∀ i j, entry t i j = entry u i j) : t = u := by
  funext k
  rcases k with ⟨i,j⟩ | k
  · let j' : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hj : j' < i := j.isLt
    simpa [entry,hj,j'] using h i j'
  · have hk : s + k.val < d := by have := k.isLt; omega
    let i : Fin d := ⟨s + k.val, hk⟩
    have hi : ¬ i.val < s := by simp [i]
    simpa [entry,hi,i] using h i i

def form (t : Param d s) : V d →+ V d →+ V s where
  toFun a :=
    { toFun := fun b k => ∑ i, ∑ j, a i * b j * entry t i j k
      map_zero' := by funext k; simp
      map_add' := by
        intro b c
        funext k
        simp [mul_add, add_mul, Finset.sum_add_distrib] }
  map_zero' := by ext b k; simp
  map_add' := by
    intro a b
    ext c k
    simp [add_mul, Finset.sum_add_distrib]

abbrev G (t : Param d s) := BilinearExtension (form t)

def gen (t : Param d s) (i : Fin d) : G t := ⟨basis i, 0⟩
def Z (t : Param d s) (z : V s) : G t := ⟨0, z⟩

lemma eval_basis (t : Param d s) (i j : Fin d) :
    form t (basis i) (basis j) = entry t i j := by
  funext k
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b k) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

theorem double_zero {k : ℕ} (v : V k) : v + v = 0 := by
  funext j
  exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v j)

theorem gen_sq (t : Param d s) (i : Fin d) : gen t i * gen t i = Z t (entry t i i) := by
  apply BilinearExtension.ext
  · exact double_zero (basis i)
  · change 0 + 0 + form t (basis i) (basis i) = entry t i i
    rw [zero_add, zero_add, eval_basis]

theorem gen_comm (t : Param d s) (i j : Fin d) (h : j < i) :
    ⁅gen t i, gen t j⁆ = Z t (entry t i j) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  · change form t (basis i) (basis j) - form t (basis j) (basis i) = _
    rw [eval_basis, eval_basis, entry_upper h, sub_zero]
    rfl

theorem Z_injective (t : Param d s) : Function.Injective (Z t) :=
  fun _ _ h => congrArg BilinearExtension.fiber h

theorem Z_add (t : Param d s) (u v : V s) : Z t (u + v) = Z t u * Z t v := by
  apply BilinearExtension.ext <;> simp [Z]

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

open scoped commutatorElement

variable {d s : ℕ}

/-- Two homomorphisms from different presentations that agree on all coordinate fibers
agree on every element of the common central vector space. -/
theorem map_Z_agree {R : Type*} [Group R] {t u : Param d s}
    (e : G t →* R) (f : G u →* R)
    (h : ∀ i : Fin s, e (Z t (basis i)) = f (Z u (basis i))) (w : V s) :
    e (Z t w) = f (Z u w) := by
  have hz : e (Z t 0) = f (Z u 0) := e.map_one.trans f.map_one.symm
  induction w using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb => rw [Z_add, Z_add, map_mul, map_mul, ha, hb]
  | single i x =>
    have bit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases bit x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact h i

/-- Projecting the images of the d generators into the elementary abelian quotient
gives a complete code for presentations mapping isomorphically into one fixed target. -/
theorem recover_of_equal_base (hs : s ≤ d) (t u r : Param d s)
    (e : G t ≃* G r) (f : G u ≃* G r)
    (h : ∀ i : Fin d, (e (gen t i)).base = (f (gen u i)).base) : t = u := by
  have hsquare (i : Fin d) : e (Z t (entry t i i)) = f (Z u (entry u i i)) := by
    rw [← gen_sq, ← gen_sq, map_mul, map_mul]
    exact BilinearExtension.lift_square_eq_of_base_eq (h i)
  have hfix (i : Fin s) : e (Z t (basis i)) = f (Z u (basis i)) := by
    simpa only [entry_fixed i hs] using hsquare (Fin.castLE hs i)
  have recover {v w : V s} (hv : e (Z t v) = f (Z u w)) : v = w := by
    have hsame := map_Z_agree e.toMonoidHom f.toMonoidHom hfix v
    exact Z_injective u (f.injective (hsame.symm.trans hv))
  apply entry_injective
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [entry_upper hij, entry_upper hij]
  · exact recover (hsquare i)
  · apply recover
    rw [← gen_comm t i j hji, ← gen_comm u i j hji, map_commutatorElement, map_commutatorElement]
    exact BilinearExtension.lift_commutator_eq_of_base_eq (h i) (h j)

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

private instance {d s : ℕ} (t : Param d s) : Finite (G t) :=
  Finite.of_equiv _ (BilinearExtension.coordinateEquiv (form t)).symm

private def bundled {d s : ℕ} (t : Param d s) : FiniteGrp.{0} := FiniteGrp.of (G t)

private theorem bundled_order {d s : ℕ} (t : Param d s) : Nat.card (bundled t) = 2 ^ (d+s) := by
  change Nat.card (BilinearExtension (form t)) = _
  rw [BilinearExtension.card]
  simp only [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_add]

theorem parameter_card {d s : ℕ} (hs : s ≤ d) :
    Nat.card (Param d s) = 2 ^ (s * (d * (d - 1) / 2 + d - s)) := by
  change Nat.card (Slot d s → Fin s → ZMod 2) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]
  unfold Slot
  rw [Nat.card_sum, triangular_card, Nat.card_fin]
  have h : d * (d - 1) / 2 + (d - s) = d * (d - 1) / 2 + d - s := by omega
  rw [h]

/-- Lower bound from the explicit family with s diagonal squares fixed to a
fiber basis. A comparison with a representative needs only d base vectors
of d bits each. -/
theorem sharp_parameter_lower {d s : ℕ} (hs : s ≤ d) :
    2 ^ (s * (d * (d - 1) / 2 + d - s)) ≤
      Erdos1160.g (2 ^ (d+s)) * 2 ^ (d*d) := by
  let code (a r : Param d s) (e : bundled a ≃* bundled r) (i : Fin d) : V d :=
    (e (gen a i) : G r).base
  have sep (a b r : Param d s) (e : bundled a ≃* bundled r) (f : bundled b ≃* bundled r)
      (h : code a r e = code b r f) : a = b :=
    recover_of_equal_base hs a b r e f (congrFun h)
  have h := Erdos1160.PresentationCount.card_le_of_relative_codes bundled bundled_order code sep
  rw [parameter_card hs] at h
  change _ ≤ _ * Nat.card (Fin d → Fin d → ZMod 2) at h
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

private theorem converted_bound (m d s : ℕ) (hs : s ≤ d) (horder : d+s=m)
    (hexp : 2*m^3 + (d*d)*27 ≤ (s*(d*(d-1)/2+d-s))*27 + 12*m^2) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  have count := Nat.pow_le_pow_left (sharp_parameter_lower hs) 27
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, horder] at count
  apply Nat.le_of_mul_le_mul_right (c := 2^((d*d)*27)) _ (Nat.pow_pos (by decide))
  calc
    2^(2*m^3) * 2^((d*d)*27) = 2^(2*m^3+(d*d)*27) := (pow_add _ _ _).symm
    _ ≤ 2^((s*(d*(d-1)/2+d-s))*27+12*m^2) := Nat.pow_le_pow_right (by decide) hexp
    _ = _ := pow_add _ _ _
    _ ≤ (Erdos1160.g (2^m)^27 * 2^((d*d)*27)) * 2^(12*m^2) :=
      Nat.mul_le_mul_right _ count
    _ = _ := Nat.mul_right_comm _ _ _

private theorem triangle_even (u : ℕ) :
    (2*u)*(2*u-1)/2 = u*(2*u-1) := by
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]

private theorem triangle_odd (u : ℕ) :
    (2*u+1)*(2*u+1-1)/2 = (2*u+1)*u := by
  have h : 2*u+1-1 = 2*u := by omega
  rw [h, show (2*u+1)*(2*u) = (2*u+1)*u*2 by ring, Nat.mul_div_cancel _ (by decide)]

/-- The sharp cubic and quadratic terms of Higman's lower bound, with all denominators
cleared and a single estimate valid in each of the three residue classes. -/
theorem higman_lower_all (m : ℕ) (hm : 3 ≤ m) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  let k := m/3-1
  have cases_m : m=3*(k+1) ∨ m=3*(k+1)+1 ∨ m=3*(k+1)+2 := by
    dsimp [k]
    omega
  have even_pred : 2*(k+1)-1 = 2*k+1 := by omega
  rcases cases_m with h | h | h
  · apply converted_bound m (2*(k+1)) (k+1) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+1) = (k+1)*(2*k+1)+(k+1) := by omega
    rw [sub_id]
    exact le_of_eq (by ring)
  · apply converted_bound m (2*(k+1)) (k+2) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+2) = (k+1)*(2*k+1)+k := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 27*k+10)
    ring
  · apply converted_bound m (2*(k+1)+1) (k+2) (by omega) (by omega)
    rw [h, triangle_odd]
    have sub_id : (2*(k+1)+1)*(k+1)+(2*(k+1)+1)-(k+2) =
        (2*(k+1)+1)*(k+1)+(k+1) := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 18*k+23)
    ring

end Erdos1160Growth.SharpFamily


/-
# Contagem de grupos de ordem potência de primo por extensões centrais

Ao retirar um subgrupo central de ordem p, cada relação da apresentação do
quociente recebe uma correção em Fin p. O novo gerador central acrescenta
uma relação de potência e uma relação de comutação por gerador anterior.
-/


open CategoryTheory

abbrev Erdos1160.FixedCofactor.OrderClasses (n : ℕ) := ↥(Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
  {G : FiniteGrp.{0} | Nat.card G = n})

namespace Erdos1160.FixedCofactor
noncomputable def orderRepresentative {n : ℕ} (i : OrderClasses n) : FiniteGrp.{0} := i.property.choose

theorem orderRepresentative_spec {n : ℕ} (i : OrderClasses n) :
    Nat.card (orderRepresentative i) = n ∧
      Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) (orderRepresentative i) = i.val :=
  i.property.choose_spec

end Erdos1160.FixedCofactor

namespace Erdos1160.PrimePower

private abbrev letter {X : Type} (x : X) := FreeGroup.of x

private def nextWord {X R : Type} (p : ℕ) (r : R → FreeGroup X) (v : R → Fin p) :
    Unit ⊕ (X ⊕ R) → FreeGroup (Option X)
  | .inl _ => letter none ^ p
  | .inr (.inl x) => (letter none * letter (some x)) * (letter (some x) * letter none)⁻¹
  | .inr (.inr i) => FreeGroup.map some (r i) * (letter none ^ (v i).val)⁻¹

private abbrev Model {X R : Type} (r : R → FreeGroup X) := PresentedGroup (Set.range r)

private def newLetter {X R : Type} {p : ℕ} (r : R → FreeGroup X) (v : R → Fin p) :
    Model (nextWord p r v) := PresentedGroup.of none

private theorem new_properties {X R : Type} {p : ℕ} (r : R → FreeGroup X) (v : R → Fin p) :
    newLetter r v ^ p = 1 ∧ newLetter r v ∈ Subgroup.center (Model (nextWord p r v)) ∧
    ∀ i, PresentedGroup.mk (Set.range (nextWord p r v)) (FreeGroup.map some (r i)) =
      newLetter r v ^ (v i).val := by
  let w := nextWord p r v
  let z := newLetter r v
  have hz : z^p = 1 := by
    have h := PresentedGroup.one_of_mem (Set.mem_range_self (Sum.inl ()) :
      w (Sum.inl ()) ∈ Set.range w)
    simpa only [w, nextWord, map_pow, z, newLetter, PresentedGroup.of, letter] using h
  have comm (x : X) : z * PresentedGroup.of (some x) = PresentedGroup.of (some x) * z := by
    have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range_self (Sum.inr (Sum.inl x)) :
      w (Sum.inr (Sum.inl x)) ∈ Set.range w)
    simpa only [map_mul, z, newLetter, PresentedGroup.of, letter, w] using h
  have cen : z ∈ Subgroup.center (Model w) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have h := PresentedGroup.generated_by (Set.range w) (Subgroup.centralizer {z}) (fun j => by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      cases j with
      | none => rfl
      | some x => exact (comm x).symm) y
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  refine ⟨hz,cen,fun i => ?_⟩
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range_self (Sum.inr (Sum.inr i)) :
    w (Sum.inr (Sum.inr i)) ∈ Set.range w)
  simpa only [map_pow, w, newLetter, PresentedGroup.of, letter] using h

private theorem lift_old {X G : Type} [Group G] (f : Option X → G) :
    (FreeGroup.lift f).comp (FreeGroup.map some) = FreeGroup.lift (fun x => f (some x)) :=
  FreeGroup.ext_hom _ _ fun x => by simp

private theorem centralNormal {G : Type*} [Group G] {K : Subgroup G} (h : K ≤ Subgroup.center G) :
    K.Normal where
  conj_mem x hx g := by
    rw [Subgroup.mem_center_iff.mp (h hx) g, mul_assoc, mul_inv_cancel, mul_one]
    exact hx

private theorem next_card {X R : Type} {p : ℕ} (hp : 0 < p) (r : R → FreeGroup X)
    (v : R → Fin p) [Finite (Model r)] :
    Finite (Model (nextWord p r v)) ∧ Nat.card (Model (nextWord p r v)) ≤ p * Nat.card (Model r) := by
  let w := nextWord p r v
  let E := Model w
  let z := newLetter r v
  obtain ⟨hz,hcen,hword⟩ := new_properties r v
  let K := Subgroup.zpowers z
  have hKC : K ≤ Subgroup.center E := (Subgroup.zpowers_le).mpr hcen
  let : K.Normal := centralNormal hKC
  let π := QuotientGroup.mk' K
  have hzq : π z = 1 := (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  let f (x : X) := π (PresentedGroup.of (some x))
  have comp : ((π.comp (PresentedGroup.mk (Set.range w))).comp (FreeGroup.map some)) =
      FreeGroup.lift f := FreeGroup.ext_hom _ _ fun x => by rfl
  have rel (u : FreeGroup X) (hu : u ∈ Set.range r) : FreeGroup.lift f u = 1 := by
    obtain ⟨i,rfl⟩ := hu
    rw [← comp]
    change π (PresentedGroup.mk _ (FreeGroup.map some (r i))) = 1
    rw [hword i, map_pow, hzq, one_pow]
  let old := PresentedGroup.toGroup rel
  have onto : Function.Surjective old := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective K y
    have h := PresentedGroup.generated_by (Set.range w) (old.range.comap π) (fun j => by
      cases j with
      | none => change π z ∈ old.range; rw [hzq]; exact old.range.one_mem
      | some j => exact ⟨PresentedGroup.of j, PresentedGroup.toGroup.of rel⟩) x
    exact h
  let : Finite (E ⧸ K) := Finite.of_surjective old onto
  have hk : Nat.card K = orderOf z := Nat.card_zpowers z
  have hdiv := orderOf_dvd_of_pow_eq_one hz
  have hcard : Nat.card E = Nat.card K * Nat.card (E ⧸ K) := by
    rw [← K.index_eq_card, K.card_mul_index]
  have hnonzero : orderOf z ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hdiv; omega
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard,hk]; exact Nat.mul_ne_zero hnonzero Nat.card_pos.ne'), ?_⟩
  rw [hcard,hk]
  exact Nat.mul_le_mul (Nat.le_of_dvd hp hdiv) (Nat.card_le_card_of_surjective old onto)

private theorem lift_code {X R G : Type} [Group G] [Finite G] {p : ℕ}
    (r : R → FreeGroup X) (z : G) (hz : orderOf z = p) (hc : z ∈ Subgroup.center G)
    [(Subgroup.zpowers z).Normal] (e : Model r ≃* (G ⧸ Subgroup.zpowers z)) :
    ∃ v : R → Fin p, ∃ F : Model (nextWord p r v) →* G, Function.Surjective F := by
  classical
  let K := Subgroup.zpowers z
  let π := QuotientGroup.mk' K
  have lifts (x : X) := QuotientGroup.mk'_surjective K (e (PresentedGroup.of x))
  choose l hl using lifts
  let old := FreeGroup.lift l
  have proj : π.comp old = e.toMonoidHom.comp (PresentedGroup.mk (Set.range r)) := by
    apply FreeGroup.ext_hom
    intro x
    simpa only [MonoidHom.comp_apply, old, FreeGroup.lift_apply_of, MulEquiv.coe_toMonoidHom, π, PresentedGroup.of] using hl x
  have exp (i : R) : ∃ v : Fin p, old (r i) = z^v.val := by
    have hzero : π (old (r i)) = 1 := by
      change π.comp old (r i) = 1
      rw [proj,MonoidHom.comp_apply,PresentedGroup.one_of_mem (Set.mem_range_self i),map_one]
    have hmem := (QuotientGroup.eq_one_iff _).mp hzero
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hmem)
    exact ⟨⟨j, hz ▸ Finset.mem_range.mp hj⟩, he.symm⟩
  choose v hv using exp
  let f : Option X → G := fun o => o.elim z l
  have hold : (FreeGroup.lift f).comp (FreeGroup.map some) = old := lift_old f
  let w := nextWord p r v
  have rel (u) (hu : u ∈ Set.range w) : FreeGroup.lift f u = 1 := by
    obtain ⟨j,rfl⟩ := hu
    rcases j with j | (x | i)
    · change FreeGroup.lift f (FreeGroup.of none ^ p) = 1
      rw [map_pow, FreeGroup.lift_apply_of]
      exact hz ▸ pow_orderOf_eq_one z
    · change FreeGroup.lift f ((letter none * letter (some x)) * (letter (some x) * letter none)⁻¹) = 1
      simp only [map_mul,map_inv,letter,FreeGroup.lift_apply_of,mul_inv_eq_one]
      exact (Subgroup.mem_center_iff.mp hc (l x)).symm
    · change FreeGroup.lift f (FreeGroup.map some (r i) * (letter none ^ (v i).val)⁻¹) = 1
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one, letter, FreeGroup.lift_apply_of]
      change (FreeGroup.lift f).comp (FreeGroup.map some) (r i) = z^(v i).val
      rw [hold, hv]
  let F := PresentedGroup.toGroup rel
  have fgen (j : Option X) : F (PresentedGroup.of j) = f j := PresentedGroup.toGroup.of rel
  have hzF : z ∈ F.range := ⟨PresentedGroup.of none, fgen none⟩
  have hKF : K ≤ F.range := Subgroup.zpowers_le.mpr hzF
  have allOld (b : Model r) : e b ∈ (π.comp F).range := by
    apply PresentedGroup.generated_by (Set.range r) ((π.comp F).range.comap e.toMonoidHom) _ b
    intro x
    refine ⟨PresentedGroup.of (some x), ?_⟩
    rw [MonoidHom.comp_apply, fgen]
    exact hl x
  refine ⟨v,F,fun g => ?_⟩
  have h := allOld (e.symm (π g))
  rw [e.apply_symm_apply] at h
  obtain ⟨w,hw⟩ := h
  have hv : g*(F w)⁻¹ ∈ K := (QuotientGroup.eq_one_iff _).mp (by
    change π (g*(F w)⁻¹) = 1
    rw [map_mul,map_inv,← MonoidHom.comp_apply, hw, mul_inv_cancel])
  have hm := F.range.mul_mem (hKF hv) (show F w ∈ F.range from ⟨w,rfl⟩)
  change g ∈ F.range
  simpa using hm

private def Letters : ℕ → Type
  | 0 => Empty
  | a+1 => Option (Letters a)

private def Relations : ℕ → Type
  | 0 => Empty
  | a+1 => Unit ⊕ (Letters a ⊕ Relations a)

private def Code (p : ℕ) : ℕ → Type
  | 0 => Unit
  | a+1 => Code p a × (Relations a → Fin p)

private def words (p : ℕ) : (a : ℕ) → Code p a → Relations a → FreeGroup (Letters a)
  | 0, _, x => Empty.elim x
  | a+1, w, i => nextWord p (words p a w.1) w.2 i

private abbrev family {p a : ℕ} (c : Code p a) := Model (words p a c)

private theorem baseSubsingleton (p : ℕ) : Subsingleton (family (p := p) (a := 0) ()) := by
  let one (x : family (p := p) (a := 0) ()) : x = 1 :=
    PresentedGroup.generated_by _ ⊥ (fun i => Empty.elim i) x
  exact ⟨fun x y => (one x).trans (one y).symm⟩

private theorem modelBound (p : ℕ) (hp : 0 < p) (a : ℕ) (w : Code p a) :
    Finite (family w) ∧ Nat.card (family w) ≤ p^a := by
  induction a with
  | zero =>
    cases w
    let : Subsingleton (family (p := p) (a := 0) ()) := baseSubsingleton p
    exact ⟨inferInstance,by simp⟩
  | succ a ih =>
    obtain ⟨hfin,hcard⟩ := ih w.1
    let : Finite (family w.1) := hfin
    obtain ⟨hfinite,hb⟩ := next_card hp (words p a w.1) w.2
    exact ⟨hfinite,hb.trans (by rw [pow_succ, Nat.mul_comm (p^a)]; exact Nat.mul_le_mul_left p hcard)⟩

private theorem cover (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (G : Type) [Group G] [Finite G]
    (hG : Nat.card G = p^a) : ∃ c : Code p a, Nonempty (family c ≃* G) := by
  classical
  induction a generalizing G with
  | zero =>
    let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hG)).1
    let : Subsingleton (family (p := p) (a := 0) ()) := baseSubsingleton p
    let f : family (p := p) (a := 0) () →* G := 1
    exact ⟨(),⟨MulEquiv.ofBijective f ⟨fun _ _ _ => Subsingleton.elim ..,
      fun y => ⟨1,Subsingleton.elim ..⟩⟩⟩⟩
  | succ a ih =>
    obtain ⟨b,hb,hbcard⟩ := IsPGroup.card_center_eq_prime_pow hG (Nat.succ_pos _)
    have hdiv : p ∣ Nat.card (Subgroup.center G) := by rw [hbcard]; exact dvd_pow_self p hb.ne'
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' p hdiv
    have ho : orderOf (z : G) = p :=
      (orderOf_injective (Subgroup.center G).subtype Subtype.val_injective z).trans hz
    let K := Subgroup.zpowers (z : G)
    let : K.Normal := centralNormal ((Subgroup.zpowers_le).mpr z.property)
    have hK : Nat.card K = p := (Nat.card_zpowers _).trans ho
    have hQ : Nat.card (G ⧸ K) = p^a := by
      apply Nat.eq_of_mul_eq_mul_right hp.out.pos
      rw [← K.index_eq_card, ← hK, K.index_mul_card, hG, hK,pow_succ]
    obtain ⟨c,⟨e⟩⟩ := ih (G ⧸ K) hQ
    obtain ⟨v,F,hF⟩ := lift_code (words p a c) (z : G) ho z.property e
    let c' : Code p (a+1) := (c,v)
    obtain ⟨hf,hc⟩ := modelBound p hp.out.pos (a+1) c'
    let : Finite (family c') := hf
    have hbnd : Nat.card (family c') ≤ Nat.card G := hG ▸ hc
    let : Finite (Model (nextWord p (words p a c) v)) := hf
    exact ⟨c',⟨MulEquiv.ofBijective F (hF.bijective_of_nat_card_le hbnd)⟩⟩

private instance lettersFintype : (a : ℕ) → Fintype (Letters a)
  | 0 => inferInstanceAs (Fintype Empty)
  | a+1 => letI := lettersFintype a; inferInstanceAs (Fintype (Option (Letters a)))

private instance relationsFintype : (a : ℕ) → Fintype (Relations a)
  | 0 => inferInstanceAs (Fintype Empty)
  | a+1 => letI := relationsFintype a; inferInstanceAs (Fintype (Unit ⊕ (Letters a ⊕ Relations a)))

private noncomputable instance codesFintype (p : ℕ) : (a : ℕ) → Fintype (Code p a)
  | 0 => inferInstanceAs (Fintype Unit)
  | a+1 => by
    classical
    letI := codesFintype p a
    exact inferInstanceAs (Fintype (Code p a × (Relations a → Fin p)))

private theorem letterCount (a : ℕ) : Fintype.card (Letters a) = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change Fintype.card (Option (Letters a)) = _
    rw [Fintype.card_option, ih]

private theorem relCount (a : ℕ) : 2 * Fintype.card (Relations a) = a*(a+1) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change 2 * Fintype.card (Unit ⊕ (Letters a ⊕ Relations a)) = _
    rw [Fintype.card_sum,Fintype.card_sum,letterCount,Fintype.card_unit]
    nlinarith only [ih]

private def exponent : ℕ → ℕ
  | 0 => 0
  | a+1 => exponent a + Fintype.card (Relations a)

private theorem exponent_identity (a : ℕ) : 6*exponent a+a = a^3 := by
  induction a with
  | zero => rfl
  | succ a ih => dsimp only [exponent]; nlinarith only [ih,relCount a]

private theorem codeCount (p a : ℕ) : Fintype.card (Code p a) = p^exponent a := by
  classical
  induction a with
  | zero => rfl
  | succ a ih =>
    change Fintype.card (Code p a × (Relations a → Fin p)) = _
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ih,exponent,pow_add]

/-- Cota uniforme para o número de grupos de ordem p^a, válida também para a = 0. -/
theorem group_count_prime_power (p a : ℕ) (hp : p.Prime) :
    (Nat.card (FixedCofactor.OrderClasses (p^a)))^6 * p^a ≤ p^(a^3) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let I := FixedCofactor.OrderClasses (p^a)
  have h (i : I) := cover p a (FixedCofactor.orderRepresentative i) (FixedCofactor.orderRepresentative_spec i).1
  choose code iso using h
  have hinj : Function.Injective code := by
    intro i j hij
    obtain ⟨e⟩ := iso i
    obtain ⟨f⟩ := iso j
    let t : family (code i) ≃* family (code j) := hij ▸ MulEquiv.refl _
    let eqv := (e.symm.trans t).trans f
    apply Subtype.ext
    rw [← (FixedCofactor.orderRepresentative_spec i).2, ← (FixedCofactor.orderRepresentative_spec j).2]
    exact Quotient.sound ⟨CategoryTheory.InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (FixedCofactor.orderRepresentative i).toGrp)
        (Y := (FixedCofactor.orderRepresentative j).toGrp) eqv)⟩
  have hc := Nat.card_le_card_of_injective code hinj
  rw [Nat.card_eq_fintype_card (α := Code p a),codeCount] at hc
  calc
    _ ≤ (p^exponent a)^6*p^a := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc _)
    _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm (exponent a), exponent_identity]


end Erdos1160.PrimePower

open CategoryTheory Filter Finset
open Erdos1160 Erdos1160.FixedCofactor

namespace Erdos1160.NilpotentCount

/-- Classes of nilpotent groups of a fixed order. -/
def classes (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}

private noncomputable def productClass {n : ℕ}
    (s : ∀ p : n.primeFactors, OrderClasses ((p : ℕ) ^ n.factorization p)) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (FiniteGrp.of (∀ p, orderRepresentative (s p)))

/-- A nilpotent group is determined by the isomorphism types of its Sylow subgroups. -/
theorem sylow_product_bound (n : ℕ) :
    (classes n).ncard ≤ ∏ p ∈ n.primeFactors, g (p ^ n.factorization p) := by
  classical
  let (p : n.primeFactors) : Finite (OrderClasses ((p : ℕ) ^ n.factorization p)) :=
    (Tables.orderClasses_finite _).to_subtype
  have hs : classes n ⊆ Set.range (@productClass n) := by
    rintro _ ⟨G, ⟨rfl, hG⟩, rfl⟩
    let : Group.IsNilpotent G := hG
    let P (p : (Nat.card G).primeFactors) : Sylow (p : ℕ) G := default
    let S (p : (Nat.card G).primeFactors) := FiniteGrp.of (P p)
    have size (p : (Nat.card G).primeFactors) :
        Nat.card (S p) = (p : ℕ) ^ (Nat.card G).factorization p :=
      @Sylow.card_eq_multiplicity _ _ _ (p : ℕ) ⟨Nat.prime_of_mem_primeFactors p.2⟩ (P p)
    let s (p : (Nat.card G).primeFactors) : OrderClasses ((p : ℕ) ^ (Nat.card G).factorization p) :=
      ⟨Quotient.mk _ (S p), S p, size p, rfl⟩
    have component (p : (Nat.card G).primeFactors) : orderRepresentative (s p) ≃* (P p) :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact ((orderRepresentative_spec (s p)).2 :
          Quotient.mk _ (orderRepresentative (s p)) = Quotient.mk _ (S p))))).groupIsoToMulEquiv
    have combine (p : (Nat.card G).primeFactors) :
        (P p) ≃* (∀ Q : Sylow (p : ℕ) G, Q) := by
      haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      letI := Sylow.unique_of_normal (P p) (inferInstance : (P p).Normal)
      exact (MulEquiv.piUnique (fun Q : Sylow (p : ℕ) G => (Q : Type _))).symm
    let e := (MulEquiv.piCongrRight (fun p => (component p).trans (combine p))).trans
      (Sylow.directProductOfNormal (G := G) fun _ => inferInstance)
    refine ⟨s, Quotient.sound ⟨?_⟩⟩
    exact InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (FiniteGrp.of (∀ p, orderRepresentative (s p))).toGrp) (Y := G.toGrp) e)
  calc
    _ ≤ (Set.range (@productClass n)).ncard := Set.ncard_le_ncard hs (Set.finite_range _)
    _ ≤ Nat.card _ := Finite.card_range_le (@productClass n)
    _ = ∏ p : n.primeFactors, g ((p : ℕ) ^ n.factorization p) := Nat.card_pi
    _ = _ := Finset.prod_coe_sort n.primeFactors (fun p : ℕ => g (p ^ n.factorization p))

/-- Since 3^7 ≥ 2^11, an odd prime power below 2^m has exponent at most 7m/11. -/
theorem odd_prime_exponent {p a m : ℕ} (hp : 3 ≤ p) (ha : p^a ≤ 2^m) :
    11*a ≤ 7*m := by
  apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
  calc
    2^(11*a) = (2^11)^a := pow_mul ..
    _ ≤ (p^7)^a := Nat.pow_le_pow_left ((by decide : 2^11 ≤ 3^7).trans
      (Nat.pow_le_pow_left hp 7)) a
    _ = (p^a)^7 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 7 a]
    _ ≤ (2^m)^7 := Nat.pow_le_pow_left ha 7
    _ = 2^(7*m) := by rw [← pow_mul, Nat.mul_comm]

private theorem prime_count_from_exponent {p k t : ℕ} (hp : p.Prime) (hk : k ≤ t) :
    g (p^k)^6 ≤ (p^k)^(t^2) := by
  calc
    g (p^k)^6 ≤ g (p^k)^6*p^k := Nat.le_mul_of_pos_right _ (pow_pos hp.pos k)
    _ ≤ p^(k^3) := PrimePower.group_count_prime_power p k hp
    _ = (p^k)^(k^2) := by rw [← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos hp.pos _) (Nat.pow_le_pow_left hk 2)

theorem product_budget {n t : ℕ} (hn : 0 < n)
    (ht : ∀ p ∈ n.primeFactors, n.factorization p ≤ t) :
    (∏ p ∈ n.primeFactors, g (p ^ n.factorization p))^6 ≤ n^(t^2) := by
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (p ^ n.factorization p) ^ (t^2) := by
      exact Finset.prod_le_prod' fun p hp =>
        prime_count_from_exponent (Nat.prime_of_mem_primeFactors hp) (ht p hp)
    _ = _ := by rw [Finset.prod_pow, ← Nat.prod_primeFactors_pow_factorization hn.ne']

/-- Uniform slack suffices to compare even the total number across a dyadic interval
with the Higman construction two exponents earlier. -/
theorem dyadic_budget {m j t u : ℕ} (hm : 256 ≤ m) (hjm : j ≤ m) (hmj : m ≤ j+2)
    (ht : 11*t ≤ 7*m) (hu : u^6 ≤ (2^m)^(t^2)) :
    2^(2*m)*u ≤ g (2^j) := by
  have sq := Nat.pow_le_pow_left ht 2
  have sc := Nat.mul_le_mul_left m sq
  have q2 := Nat.pow_le_pow_left hjm 2
  have j0 : 3 ≤ j := by omega
  have hlo := Erdos1160Growth.SharpFamily.higman_lower_all j j0
  have j1 : m-2 ≤ j := by omega
  have cub := Nat.pow_le_pow_left j1 3
  have ep : 108*m + 9*m*t^2 + 24*j^2 ≤ 4*j^3 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hsub : 256+k-2 = 254+k := by omega
    rw [hsub] at cub
    nlinarith only [sc, q2, cub, Nat.zero_le k, Nat.zero_le (k^2), Nat.zero_le (k^3)]
  apply (Nat.pow_le_pow_iff_left (by decide : 54 ≠ 0)).mp
  apply Nat.le_of_mul_le_mul_right (c := 2^(24*j^2)) _ (by positivity)
  calc
    (2^(2*m)*u)^54*2^(24*j^2) = 2^(108*m) * (u^6)^9 * 2^(24*j^2) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]; congr 3; ring
    _ ≤ 2^(108*m) * ((2^m)^(t^2))^9 * 2^(24*j^2) := by gcongr
    _ = 2^(108*m + 9*m*t^2 + 24*j^2) := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ 2^(4*j^3) := Nat.pow_le_pow_right (by decide) ep
    _ = (2^(2*j^3))^2 := by rw [← pow_mul]; congr 1; ring
    _ ≤ (g (2^j)^27 * 2^(12*j^2))^2 := Nat.pow_le_pow_left hlo 2
    _ = g (2^j)^54 * 2^(24*j^2) := by rw [mul_pow, ← pow_mul, ← pow_mul]; congr 2; ring

theorem small_two_part {n m j : ℕ} (hm : 256 ≤ m) (hjm : j ≤ m) (hmj : m ≤ j+2)
    (hn : 0 < n) (hnm : n ≤ 2^m) (h2 : 11*n.factorization 2 ≤ 7*m) :
    2^(2*m) * (classes n).ncard ≤ g (2^j) := by
  let t := 7*m/11
  have ht : 11*t ≤ 7*m := by dsimp [t]; omega
  apply dyadic_budget hm hjm hmj ht
  have hp (p : ℕ) (h : p ∈ n.primeFactors) : n.factorization p ≤ t := by
    have hp2 := (Nat.prime_of_mem_primeFactors h).two_le
    by_cases h' : p = 2
    · subst p; dsimp [t]; omega
    have hpow := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
    have := odd_prime_exponent (by omega : 3 ≤ p) (hpow.trans hnm)
    dsimp [t]; omega
  exact ((Nat.pow_le_pow_left (sylow_product_bound n) 6).trans (product_budget hn hp)).trans
    (Nat.pow_le_pow_left hnm _)


private theorem sum_of_uniform {m j : ℕ} (s : Finset ℕ) (hc : s.card ≤ 2^m)
    (pointwise : ∀ n ∈ s, 2^(2*m)*(classes n).ncard ≤ g (2^j)) :
    2^m * (∑ n ∈ s, (classes n).ncard) ≤ g (2^j) := by
  let b := g (2^j) / 2^(2*m)
  have hb (n : ℕ) (hn : n ∈ s) : (classes n).ncard ≤ b := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(2*m))).2
    rw [Nat.mul_comm]
    exact pointwise n hn
  calc
    _ ≤ 2^m * (s.card*b) := Nat.mul_le_mul_left _ (s.sum_le_card_nsmul _ _ hb)
    _ ≤ 2^m * (2^m * b) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
    _ = 2^(2*m) * b := by rw [← mul_assoc, ← pow_add, two_mul]
    _ ≤ _ := Nat.mul_div_le _ _

/-- The same estimate summed over any set of eligible orders. -/
theorem sum_small_two_part {m j : ℕ} (hm : 256 ≤ m) (hjm : j ≤ m) (hmj : m ≤ j+2)
    (s : Finset ℕ) (hs : s ⊆ Finset.Ico 1 (2^m))
    (h2 : ∀ n ∈ s, 11*n.factorization 2 ≤ 7*m) :
    2^m * (∑ n ∈ s, (classes n).ncard) ≤ g (2^j) := by
  apply sum_of_uniform s ((Finset.card_le_card hs).trans (by simp))
  intro n hn
  have hn' := Finset.mem_Ico.mp (hs hn)
  exact small_two_part hm hjm hmj hn'.1 hn'.2.le (h2 n hn)

theorem odd_nilpotent_sum (m : ℕ) (hm : 256 ≤ m) :
    2^m * (∑ n ∈ (Finset.Ico 1 (2^m)).filter Odd, (classes n).ncard) ≤ g (2^m) := by
  apply sum_small_two_part hm (by omega) (by omega) _ (Finset.filter_subset _ _)
  intro n hn
  have hodd := (Finset.mem_filter.mp hn).2
  have h := Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ n by
    rintro ⟨k, hk⟩
    obtain ⟨j,hj⟩ := hodd
    omega)
  simp [h]

theorem prime_power_classes (p a : ℕ) (hp : p.Prime) :
    (classes (p^a)).ncard = g (p^a) := by
  have : Fact p.Prime := ⟨hp⟩
  unfold classes g
  congr 2
  ext G
  exact ⟨fun h => h.1, fun h => ⟨h, (IsPGroup.of_card h).isNilpotent⟩⟩

end Erdos1160.NilpotentCount

open Filter Finset
namespace Erdos1160.NilpotentCount

/-- No constant can absorb the gap between the cubic coefficient 1/14
and Higman's 2/27. -/
private theorem unbounded_scores :
    ¬ ∃ B : ℕ, ∀ m : ℕ, g (2^m)^14 ≤ 2^(m^3+B) := by
  rintro ⟨B,hB⟩
  let m := 200+27*B
  have hL := Nat.pow_le_pow_left
    (Erdos1160Growth.SharpFamily.higman_lower_all m (by dsimp [m]; omega)) 14
  have hU := Nat.pow_le_pow_left (hB m) 27
  have hP : 2^(28*m^3) ≤ 2^(27*(m^3+B)+168*m^2) := by
    calc
      _ = (2^(2*m^3))^14 := by rw [← pow_mul]; congr 1; ring
      _ ≤ _ := hL
      _ = (g (2^m)^14)^27 * 2^(168*m^2) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; congr 2; ring
      _ ≤ (2^(m^3+B))^27 * 2^(168*m^2) := Nat.mul_le_mul_right _ hU
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have hc := (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp hP
  dsimp [m] at hc
  nlinarith only [hc, Nat.zero_le B, Nat.zero_le (B^2), Nat.zero_le (B^3)]

private theorem frequent_records : ∃ᶠ m : ℕ in atTop, ∀ a < m,
    g (2^a)^14 * 2^(m^3) ≤ g (2^m)^14 * 2^(a^3) := by
  rw [Filter.frequently_atTop]
  intro N
  by_contra! h
  let B := ∑ i ∈ Finset.range N, g (2^i)^14
  apply unbounded_scores
  refine ⟨B, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < N
    · have hB : g (2^m)^14 ≤ B :=
        Finset.single_le_sum (f := fun i : ℕ => g (2^i)^14) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hm)
      exact hB.trans ((Nat.le_of_lt (Nat.lt_two_pow_self (n := B))).trans
        (Nat.pow_le_pow_right (by decide) (by omega)))
    · obtain ⟨a,ha,hma⟩ := h m (by omega)
      apply Nat.le_of_mul_le_mul_right (c := 2^(a^3)) _ (by positivity)
      calc
        _ ≤ _ := hma.le
        _ ≤ 2^(a^3+B) * 2^(m^3) := Nat.mul_le_mul_right _ (ih a ha)
        _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

private theorem record_budget {a m d t U : ℕ} (hm : 1024 ≤ m) (ham : a+d=m)
    (hd : 0 < d) (ht : 11*t ≤ 7*d) (hU : U^6 ≤ (2^d)^(t^2))
    (rec : g (2^a)^14 * 2^(m^3) ≤ g (2^m)^14 * 2^(a^3)) :
    2^(2*m) * (g (2^a)*U) ≤ g (2^m) := by
  have htm : 11*t ≤ 7*m := by omega
  have sq := Nat.mul_le_mul_left d (Nat.pow_le_pow_left htm 2)
  have hmarg : 10164*m ≤ 20*m^2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
    nlinarith only [Nat.zero_le k, Nat.zero_le (k^2)]
  have hscale := Nat.mul_le_mul_right (20*m^2) (show 1 ≤ d by omega)
  have gap : d*m^2 + a^3 ≤ m^3 := by
    rw [← ham]; nlinarith only [Nat.zero_le (a^2*d), Nat.zero_le (a*d^2)]
  have expo : 3*a^3 + 7*d*t^2 + 84*m ≤ 3*m^3 := by
    nlinarith only [sq, hmarg, hscale, gap]
  have hr : g (2^a)^42 * 2^(3*m^3) ≤ g (2^m)^42 * 2^(3*a^3) := by
    have h := Nat.pow_le_pow_left rec 3
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm (m^3) 3, Nat.mul_comm (a^3) 3] using h
  have hu : (U^6)^7 ≤ 2^(7*d*t^2) := by
    calc
      _ ≤ ((2^d)^(t^2))^7 := Nat.pow_le_pow_left hU 7
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 1; ring
  apply (Nat.pow_le_pow_iff_left (by decide : 42 ≠ 0)).mp
  apply Nat.le_of_mul_le_mul_right (c := 2^(3*m^3)) _ (by positivity)
  calc
    _ = (g (2^a)^42 * 2^(3*m^3)) * (U^6)^7 * 2^(84*m) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, show 2*m*42 = 84*m by ring, show 6*7 = 42 by decide]
      ring
    _ ≤ (g (2^m)^42 * 2^(3*a^3)) * 2^(7*d*t^2) * 2^(84*m) := by gcongr
    _ = g (2^m)^42 * 2^(3*a^3 + 7*d*t^2 + 84*m) := by rw [pow_add, pow_add]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) expo)

/-- On a record dyadic order every nilpotent population of smaller order is small. -/
private theorem nilpotent_at_record {m n : ℕ} (hm : 1024 ≤ m) (hn : 0 < n) (hnm : n < 2^m)
    (rec : ∀ a < m, g (2^a)^14 * 2^(m^3) ≤ g (2^m)^14 * 2^(a^3)) :
    2^(2*m)*(classes n).ncard ≤ g (2^m) := by
  classical
  by_cases even : 2 ∈ n.primeFactors
  · let a := n.factorization 2
    let d := m-a
    let ps := n.primeFactors.erase 2
    let q := ∏ p ∈ ps, p ^ n.factorization p
    let U := ∏ p ∈ ps, g (p ^ n.factorization p)
    have hq : 2^a*q = n := by
      exact (Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) even).trans
        (Nat.prod_primeFactors_pow_factorization hn.ne').symm
    have qpos : 0 < q := Nat.pos_of_mul_pos_left (hq.symm ▸ hn)
    have hlow : 2^a ≤ n := hq ▸ Nat.le_mul_of_pos_right _ qpos
    have ha := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp (hlow.trans_lt hnm)
    have ham : a+d=m := by dsimp [d]; omega
    have qsmall : q ≤ 2^d := by
      apply Nat.le_of_mul_le_mul_left (c := 2^a) _ (by positivity)
      rw [hq, ← pow_add, ham]
      omega
    let t := 7*d/11
    have hprime (p : ℕ) (hp : p ∈ ps) := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
    have each (p : ℕ) (hp : p ∈ ps) : n.factorization p ≤ t := by
      have neq := (Finset.mem_erase.mp hp).1
      have pp := (hprime p hp).two_le
      have dvd : p ^ n.factorization p ∣ q := Finset.dvd_prod_of_mem _ hp
      have := odd_prime_exponent (by omega : 3 ≤ p) ((Nat.le_of_dvd qpos dvd).trans qsmall)
      dsimp [t]; omega
    have budget : U^6 ≤ (2^d)^(t^2) := by
      dsimp only [U]
      rw [← Finset.prod_pow]
      calc
        _ ≤ ∏ p ∈ ps, (p ^ n.factorization p)^(t^2) := by
          exact Finset.prod_le_prod' fun p hp => prime_count_from_exponent (hprime p hp) (each p hp)
        _ = q^(t^2) := Finset.prod_pow ..
        _ ≤ _ := Nat.pow_le_pow_left qsmall _
    have size : (classes n).ncard ≤ g (2^a)*U := (sylow_product_bound n).trans_eq
      (Finset.mul_prod_erase n.primeFactors (fun p => g (p ^ n.factorization p)) even).symm
    exact (Nat.mul_le_mul_left _ size).trans
      (record_budget hm ham (by dsimp [d]; omega) (by dsimp [t]; omega) budget (rec a ha))
  · have h2 : n.factorization 2 = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact even (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,hd,hn.ne'⟩)
    exact small_two_part (by omega) (le_refl m) (by omega) hn hnm.le (by simp [h2])

/-- Infinitely many dyadic orders dominate all smaller nilpotent groups combined
by a factor of at least 2^m. -/
theorem frequently_nilpotent_sum : ∃ᶠ m : ℕ in atTop,
    2^m * (∑ n ∈ Finset.Ico 1 (2^m), (classes n).ncard) ≤ g (2^m) := by
  apply (frequent_records.and_eventually (eventually_ge_atTop 1024)).mono
  rintro m ⟨rec,hm⟩
  apply sum_of_uniform _ (by simp)
  intro n hn
  exact nilpotent_at_record hm (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2 rec

/-- In particular the pure powers of two satisfy a strengthened R2.H1 infinitely often. -/
theorem frequently_power_sum : ∃ᶠ m : ℕ in atTop,
    2^m * (∑ k ∈ Finset.range m, g (2^k)) ≤ g (2^m) := by
  apply frequently_nilpotent_sum.mono
  intro m h
  apply le_trans (Nat.mul_le_mul_left _ ?_) h
  let s := (Finset.range m).image (fun k : ℕ => 2^k)
  have subset : s ⊆ Finset.Ico 1 (2^m) := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ico.mpr ⟨Nat.one_le_two_pow, Nat.pow_lt_pow_right (by decide) (Finset.mem_range.mp hk)⟩
  calc
    _ = ∑ k ∈ Finset.range m, (classes (2^k)).ncard :=
      Finset.sum_congr rfl (fun k _ => (prime_power_classes 2 k Nat.prime_two).symm)
    _ = ∑ n ∈ s, (classes n).ncard := by
      dsimp only [s]
      rw [Finset.sum_image (fun i _ j _ hij => (Nat.pow_right_injective (by decide : 2 ≤ 2)) hij)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)

end Erdos1160.NilpotentCount

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1.H1 := by
  filter_upwards [Filter.eventually_ge_atTop 256] with m hm
  intro n hn h2
  obtain ⟨hn1, hnm⟩ := Finset.mem_Ico.mp hn
  exact Erdos1160.NilpotentCount.small_two_part hm (Nat.sub_le m 2) (by omega) hn1 hnm.le h2
