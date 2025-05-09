import Carleson.ToMathlib.RealInterpolation.Minkowski

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open ENNReal Set MeasureTheory
open scoped NNReal

variable {𝓐 : Type*} [AddCommMonoid 𝓐] {𝓑 : Type*} [AddCommMonoid 𝓑]

variable (𝓐) in
structure QuasiENorm where
  protected enorm : ENorm 𝓐
  protected C : ℝ≥0∞
  protected C_lt : C < ∞ := by finiteness
  protected enorm_zero : ‖(0 : 𝓐)‖ₑ = 0
  enorm_add_le_mul : ∀ x y : 𝓐, ‖x + y‖ₑ ≤ C * (‖x‖ₑ + ‖y‖ₑ)


-- Feel free to assume `θ ∈ Icc 0 1`, `1 ≤ q` and `q < ∞ → θ ∈ Ioo 0 1` whenever needed
variable {A A₀ A₁ A' A₀' A₁' : QuasiENorm 𝓐} {t s : ℝ≥0∞} {x y z : 𝓐} {θ : ℝ} {q : ℝ≥0∞}
  {B B₀ B₁ B' B₀' B₁' : QuasiENorm 𝓑} {C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}

namespace QuasiENorm

attribute [simp] QuasiENorm.enorm_zero
attribute [aesop (rule_sets := [finiteness]) safe] QuasiENorm.C_lt max_lt

-- Todo: we need a delaborator for this.

notation "‖" e "‖ₑ[" A "]" => @enorm _ (QuasiENorm.enorm A) e

-- todo: make constant explicit
instance : LE (QuasiENorm 𝓐) :=
  ⟨fun A₀ A₁ => ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, ‖x‖ₑ[A₁] ≤ C * ‖x‖ₑ[A₀]⟩

instance : Preorder (QuasiENorm 𝓐) where
  le_refl A := ⟨1, by simp⟩
  le_trans A₀ A₁ A₂ := by
    intro ⟨C, h1C, h2C⟩ ⟨D, h1D, h2D⟩
    refine ⟨D * C, mul_ne_top h1D h1C, fun x ↦ ?_⟩
    calc ‖x‖ₑ[A₂] ≤ D * ‖x‖ₑ[A₁] := h2D x
      _ ≤ D * C * ‖x‖ₑ[A₀] := by
        rw [mul_assoc]
        gcongr
        apply h2C

-- the equivalence relation stating that two norms are equivalent
instance : Setoid (QuasiENorm 𝓐) := AntisymmRel.setoid _ (· ≤ ·)

-- example (h : A₀ ≈ A₁) : A₀ ≤ A₁ := h.le
-- example (h : A₀ ≈ A₁) : A₁ ≤ A₀ := h.ge

-- Two spaces are compatible if they can both be embedded into the same topological additive monoid.
-- Hopefully this is vacuous in our reformulation.
-- def Compatible (A₀ A₁ : QuasiENorm 𝓐) : Prop :=

/-- the submonoid of finite elements -/
def finiteElements (A : QuasiENorm 𝓐) : AddSubmonoid 𝓐 where
  carrier := { x | ‖x‖ₑ[A] < ∞ }
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    calc
      ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) := by apply enorm_add_le_mul
      _ < ∞ := by finiteness

example : ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) :=
  A.enorm_add_le_mul x y

instance : Min (QuasiENorm 𝓐) :=
  ⟨fun A₀ A₁ => {
    enorm := ⟨fun x ↦ max ‖x‖ₑ[A₀] ‖x‖ₑ[A₁]⟩
    C := max A₀.C A₁.C
    enorm_zero := by simp_rw [QuasiENorm.enorm_zero, max_self]
    enorm_add_le_mul x y :=
      calc
        max ‖x + y‖ₑ[A₀] ‖x + y‖ₑ[A₁] ≤
          max (A₀.C * (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀])) (A₁.C * (‖x‖ₑ[A₁] + ‖y‖ₑ[A₁])) := by
            gcongr <;> apply enorm_add_le_mul
        _ ≤ max A₀.C A₁.C * max (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀]) (‖x‖ₑ[A₁] + ‖y‖ₑ[A₁]) :=
            max_mul_mul_le_max_mul_max'
        _ ≤ max A₀.C A₁.C * (max ‖x‖ₑ[A₀] ‖x‖ₑ[A₁] + max ‖y‖ₑ[A₀] ‖y‖ₑ[A₁]) := by
            gcongr
            exact max_add_add_le_max_add_max }⟩

lemma inf_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ ⊓ A₁ ≤ A₀' ⊓ A₁' := by
  obtain ⟨C₀, ⟨hC₀₀, hC₀₁⟩⟩ := h₀
  obtain ⟨C₁, ⟨hC₁₀, hC₁₁⟩⟩ := h₁
  use max C₀ C₁
  exact ⟨by finiteness,
         fun x ↦ Trans.trans (sup_le_sup (hC₀₁ x) (hC₁₁ x)) max_mul_mul_le_max_mul_max'⟩

lemma inf_equiv_inf (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ ⊓ A₁ ≈ A₀' ⊓ A₁' :=
  ⟨inf_mono h₀.le h₁.le, inf_mono h₀.ge h₁.ge⟩

/-- `K(t,x)` in Section 3.1. For `t = 1` this is the norm of `A₀ + A₁`. -/
def addNorm (A₀ A₁ : QuasiENorm 𝓐) (t : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  ⨅ (x₀ : 𝓐) (x₁ : 𝓐) (_h : x₀ + x₁ = x), ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁]

lemma trivial_QuasiENorm (A : QuasiENorm 𝓐) (h : A.C = 0) :
    ∀ x : 𝓐, ‖x‖ₑ[A] = 0 := by
  intro x
  rw [← add_zero x]
  exact nonpos_iff_eq_zero.mp <| le_of_le_of_eq (A.enorm_add_le_mul x 0) (by simp_all)

lemma trivial_QuasiENorm₀ (A : QuasiENorm 𝓐) (h : A.C < 1) :
    ∀ x : 𝓐, ‖x‖ₑ[A] ≠ ∞ → ‖x‖ₑ[A] = 0 := by
  intro x hx
  have teq := A.enorm_add_le_mul x 0
  rw [QuasiENorm.enorm_zero, add_zero, add_zero, ← tsub_nonpos, nonpos_iff_eq_zero] at teq
  nth_rw 1 [← one_mul ‖x‖ₑ[A], ← ENNReal.sub_mul (fun _ _ ↦ hx)] at teq
  exact (mul_eq_zero_iff_left (ne_of_gt (tsub_pos_of_lt h))).mp teq




/-- The addition `A₀ + A₁` equipped with the norm `K(t,-)` -/
def skewedAdd (A₀ A₁ : QuasiENorm 𝓐) (t : ℝ≥0∞) : QuasiENorm 𝓐 where
  enorm := ⟨addNorm A₀ A₁ t⟩
  C := max A₀.C A₁.C
  enorm_zero := by
    simp_rw [← le_zero_iff]
    apply iInf₂_le_of_le 0 0
    simp
  enorm_add_le_mul x y := by
    by_cases h : A₀.C = 0
    · simp only [h, add_zero, zero_mul]
      exact iInf₂_le_of_le (x + y) 0 <| iInf_le_of_le (by simp)
          (by rw [trivial_QuasiENorm _ h]; simp_all)
    · calc
      ⨅ (a₀ : 𝓐) (a₁ : 𝓐) (_h : a₀ + a₁ = x + y), ‖a₀‖ₑ[A₀] + t * ‖a₁‖ₑ[A₁]
        ≤ ⨅ (x₀ : 𝓐) (x₁ : 𝓐) (y₀ : 𝓐) (y₁ : 𝓐) (_h₀ : x₀ + x₁ = x) (_h₁ : y₀ + y₁ = y),
          (max A₀.C A₁.C) * (‖x₀‖ₑ[A₀] + ‖y₀‖ₑ[A₀]) +
          t * ((max A₀.C A₁.C) * (‖x₁‖ₑ[A₁] + ‖y₁‖ₑ[A₁])) := by
        refine le_iInf fun x₀ ↦ le_iInf fun x₁ ↦ le_iInf fun y₀ ↦ le_iInf fun y₁ ↦ le_iInf
            fun _h₀ ↦ le_iInf fun _h₁ ↦ ?_
        have _h : (x₀ + y₀) + (x₁ + y₁) = x + y := by
          rw [← _h₀, ← _h₁, add_assoc, add_assoc]; congr 1; rw [← add_assoc, ← add_assoc,
              add_comm y₀]
        apply iInf₂_le_of_le (x₀ + y₀) (x₁ + y₁)
        apply iInf_le_of_le _h
        gcongr
        · calc
          _ ≤ _ := A₀.enorm_add_le_mul x₀ y₀
          _ ≤ _ := by gcongr; exact le_max_left A₀.C A₁.C
        · calc
          _ ≤ _ := A₁.enorm_add_le_mul x₁ y₁
          _ ≤ _ := by gcongr; exact le_max_right A₀.C A₁.C
      _ ≤ ⨅ (x₀ : 𝓐) (x₁ : 𝓐) (y₀ : 𝓐) (y₁ : 𝓐) (_h₀ : x₀ + x₁ = x) (_h₁ : y₀ + y₁ = y),
          (max A₀.C A₁.C) * (‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁] + (‖y₀‖ₑ[A₀] + t * ‖y₁‖ₑ[A₁])) := by
        gcongr ⨅ (x₀ : 𝓐) (x₁ : 𝓐) (y₀ : 𝓐) (y₁ : 𝓐) (_h₀ : x₀ + x₁ = x) (_h₁ : y₀ + y₁ = y), ?_
            with x₀ x₁ y₀ y₁ _h₀ _h₁
        apply le_of_eq; ring
      _ ≤ (max A₀.C A₁.C) *
          ⨅ (x₀ : 𝓐) (x₁ : 𝓐) (y₀ : 𝓐) (y₁ : 𝓐) (_h₀ : x₀ + x₁ = x) (_h₁ : y₀ + y₁ = y),
          (‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁] + (‖y₀‖ₑ[A₀] + t * ‖y₁‖ₑ[A₁])) := by
        have h_ne_zero : max A₀.C A₁.C ≠ 0 := by simp [h]
        have h_ne_top : max A₀.C A₁.C ≠ ⊤ := by finiteness
        simp_rw [ENNReal.mul_iInf_of_ne h_ne_zero h_ne_top]; rfl
      _ ≤ (max A₀.C A₁.C) *
          ((⨅ (x₀ : 𝓐) (x₁ : 𝓐) (y₀ : 𝓐) (y₁ : 𝓐) (_h₀ : x₀ + x₁ = x) (_h₁ : y₀ + y₁ = y),
            ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁]) +
            ⨅ (x₀ : 𝓐) (x₁ : 𝓐) (y₀ : 𝓐) (y₁ : 𝓐) (_h₀ : x₀ + x₁ = x) (_h₁ : y₀ + y₁ = y),
            ‖y₀‖ₑ[A₀] + t * ‖y₁‖ₑ[A₁]) := by
        apply mul_le_mul_left'
        rw [iInf_add_iInf]
        · gcongr with x₀
          rw [iInf_add_iInf]
          · gcongr with x₁
            rw [iInf_add_iInf]
            · gcongr with y₀
              rw [iInf_add_iInf]
              · gcongr with y₁
                rw [iInf_add_iInf]
                · gcongr with _h₀
                  rw [iInf_add_iInf]
                  intro heq _
                  use heq
                · intro heq _
                  use heq
              · intro i y₁
                use y₁
                by_cases y₀ + y₁ = y
                · gcongr; simp_all
                · simp_all
            · intro i y₀
              use y₀
              by_cases hex : ∃ y₁, y₀ + y₁ = y
              · obtain ⟨y₁, hy₁⟩ := hex
                gcongr ?_ + _
                apply le_iInf
                intro y₂
                apply iInf_le_of_le y₁
                simp_all
              · simp_all
          · intro x₁ j
            use x₁
            by_cases x₀ + x₁ = x
            · gcongr; simp_all
            · simp_all
        · intro x₀ j
          use x₀
          by_cases hex : ∃ x₁, x₀ + x₁ = x
          · obtain ⟨x₁, hx₁⟩ := hex
            gcongr _ + ?_
            apply le_iInf
            intro x₂
            apply iInf_le_of_le x₁
            gcongr
            simp_all
          · simp_all
      _ ≤ (max A₀.C A₁.C) * ((⨅ (x₀ : 𝓐) (x₁ : 𝓐) (_h₀ : x₀ + x₁ = x),
            ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁]) +
            ⨅ (y₀ : 𝓐) (y₁ : 𝓐) (_h₁ : y₀ + y₁ = y), ‖y₀‖ₑ[A₀] + t * ‖y₁‖ₑ[A₁]) := by
        apply mul_le_mul_left'
        gcongr ?_ + ?_
        · exact iInf_mono fun x₀ ↦ iInf_mono fun x₁ ↦ iInf₂_le_of_le y 0
              (le_iInf fun h ↦ iInf₂_le_of_le h (add_zero y) (le_refl (‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁])))
        · apply iInf₂_le_of_le x 0
          simp_all



lemma skewedAdd_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') :
    skewedAdd A₀ A₁ t ≤ skewedAdd A₀' A₁' t := by
  obtain ⟨C₀, ⟨hC₀₀, hC₀₁⟩⟩ := h₀
  obtain ⟨C₁, ⟨hC₁₀, hC₁₁⟩⟩ := h₁
  use C₀ + C₁
  refine ⟨by finiteness, fun x ↦ ?_⟩
  by_cases hCs: C₀ + C₁ = 0
  · have hC₀ : C₀ = 0 := by exact eq_zero_of_add_right hCs
    have hC₁ : C₁ = 0 := (eq_zero_iff_eq_zero_of_add_eq_zero hCs).mp hC₀
    simp_rw [hC₀, hC₁, zero_mul, nonpos_iff_eq_zero] at hC₀₁ hC₁₁
    unfold skewedAdd addNorm
    dsimp only
    simp_rw [hC₀₁, hC₁₁, hCs, mul_zero, add_zero, zero_mul]
    exact iInf₂_le_of_le x 0 (iInf_le_of_le (AddMonoid.add_zero x) (zero_le 0))
  · refine (ENNReal.inv_mul_le_iff hCs (by finiteness)).mp <|
        le_iInf₂ fun x₀ x₁ ↦ le_iInf fun _h ↦ (ENNReal.inv_mul_le_iff hCs (by finiteness)).mpr <|
        iInf₂_le_of_le x₀ x₁ <| iInf_le_of_le _h ?_
    calc
    ‖x₀‖ₑ[A₀'] + t * ‖x₁‖ₑ[A₁']
      ≤ C₀ * ‖x₀‖ₑ[A₀] + t * C₁ * ‖x₁‖ₑ[A₁] := by
      gcongr ?_ + ?_
      · exact hC₀₁ x₀
      · rw [mul_assoc]; gcongr; exact hC₁₁ x₁
    _ ≤ (C₀ + C₁) * ‖x₀‖ₑ[A₀] + t * (C₀ + C₁) * ‖x₁‖ₑ[A₁] := by
      gcongr
      · exact le_self_add
      · exact le_add_self
    _ = _ := by ring

lemma skewedAdd_equiv_skewedAdd (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') :
    skewedAdd A₀ A₁ t ≈ skewedAdd A₀' A₁' t :=
  ⟨skewedAdd_mono h₀.le h₁.le, skewedAdd_mono h₀.ge h₁.ge⟩

instance : Add (QuasiENorm 𝓐) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedAdd A₁ 1⟩

lemma add_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ + A₁ ≤ A₀' + A₁' :=
  skewedAdd_mono h₀ h₁

lemma add_equiv_add (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ + A₁ ≈ A₀' + A₁' :=
  skewedAdd_equiv_skewedAdd h₀ h₁

-- Part of Lemma 3.1.1
-- assume t ≠ ∞ if needed
lemma monotone_addNorm : Monotone (addNorm A₀ A₁ · x) := by
  intro a b hab
  exact le_iInf₂ fun x₀ x₁ ↦ le_iInf fun _h ↦ iInf₂_le_of_le x₀ x₁ <| iInf_le_of_le _h (by gcongr)

-- Part of Lemma 3.1.1 (if convenient: make the scalar ring `ℝ≥0`)
-- assume t ≠ ∞ if needed
lemma concave_addNorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) : ConcaveOn ℝ≥0∞ univ (addNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1
-- assume s ≠ 0, s ≠ ∞, t ≠ ∞ if needed
-- probably this is more useful if reformulated without division
lemma addNorm_le_mul (hx : ‖x‖ₑ[A₀ + A₁] < ∞) :
    addNorm A₀ A₁ t x ≤ max 1 (t / s) * addNorm A₀ A₁ s x := by
  sorry

/-- The functional `Φ` in Section 3.1. Todo: better name. Todo: generalize type of `f`?
If we put a σ-algebra + measure on `ℝ≥0∞` we can get rid of the `ofReal`s. -/
def functional (θ : ℝ) (q : ℝ≥0∞) (f : ℝ≥0∞ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm ((Ioi 0).indicator fun t ↦ ENNReal.ofReal t ^ (- θ) * f (ENNReal.ofReal t)) q
    (volume.withDensity fun t ↦ (ENNReal.ofReal t)⁻¹)

/- ‖-‖_{θ, q, K} in Section 3.1. -/
def KNorm (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  functional θ q (addNorm A₀ A₁ · x)

/-- The space K_{θ,q}(\bar{A}) in Section 3.1.
In the book, this is defined to only be submonoid of the elements with finite norm.
We could do that as well, but actually, since we allow for infinite norms, we can take all elements.
-/
def KMethod (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) : QuasiENorm 𝓐 where
  enorm := ⟨KNorm A₀ A₁ θ q⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

structure IsIntermediateSpace (A A₀ A₁ : QuasiENorm 𝓐) : Prop where
  inf_le : A₀ ⊓ A₁ ≤ A
  le_add : A ≤ A₀ + A₁

namespace IsIntermediateSpace

protected lemma equiv (hI : IsIntermediateSpace A A₀ A₁) (h : A ≈ A') (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') :
  IsIntermediateSpace A' A₀' A₁' where
    inf_le := inf_equiv_inf h₀ h₁ |>.ge.trans hI.inf_le |>.trans h.le
    le_add := h.ge.trans hI.le_add |>.trans <| add_equiv_add h₀ h₁ |>.le

end IsIntermediateSpace

-- Todo: find better name?
-- question: how do we get real interpolation with a.e.-subadditivity:
-- probably this works if we apply it to L^p-spaces (i.e. quotients of functions)
structure IsSubadditiveOn (T : 𝓐 → 𝓑) (A : QuasiENorm 𝓐) (B : QuasiENorm 𝓑) (C D : ℝ≥0∞) :
    Prop where
  bounded : ∀ x, ‖T x‖ₑ[B] ≤ C * ‖x‖ₑ[A]
  subadditive : ∀ x y, ‖T (x + y)‖ₑ[B] ≤ D * (‖T x‖ₑ[B] + ‖T y‖ₑ[B])

-- `C = ‖T‖_{A, B}`
-- perhaps we don't have to let `C` and `D` depend on all other parameters.
structure AreInterpolationSpaces (A A₀ A₁ : QuasiENorm 𝓐) (B B₀ B₁ : QuasiENorm 𝓑)
    (C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop where
  isIntermediateSpace_fst : IsIntermediateSpace A A₀ A₁
  isIntermediateSpace_snd : IsIntermediateSpace B B₀ B₁
  prop : ∀ C₀ D₀ C₁ D₁ (T : 𝓐 → 𝓑), IsSubadditiveOn T A₀ B₀ C₀ D₀ → IsSubadditiveOn T A₁ B₁ C₁ D₁ →
    IsSubadditiveOn T A B (C C₀ D₀ C₁ D₁) (D C₀ D₀ C₁ D₁)

/-- `T` is of exponent `θ` w.r.t. constant `E` if `C ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ` -/
def IsOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) (E : ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ

/-- `T` is exact of exponent `θ` -/
def IsExactOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) : Prop :=
  IsOfExponent C θ 1

/-- `T` is exact -/
def IsExact (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ max C₀ C₁


namespace AreInterpolationSpaces

protected lemma equiv (hI : AreInterpolationSpaces A A₀ A₁ B B₀ B₁ C D)
    (h : A ≈ A') (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') (h' : B ≈ B') (h₀' : B₀ ≈ B₀') (h₁' : B₁ ≈ B₁') :
  AreInterpolationSpaces A' A₀' A₁' B' B₀' B₁' C D where
    isIntermediateSpace_fst := hI.isIntermediateSpace_fst.equiv h h₀ h₁
    isIntermediateSpace_snd := hI.isIntermediateSpace_snd.equiv h' h₀' h₁'
    prop := sorry

end AreInterpolationSpaces


/-- The boundedness constant for the K-method. -/
def C_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- The subadditivity constant for the K-method. -/
def D_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Theorem 3.1.2: The K-method in an interpolation functor. -/
lemma areInterpolationSpaces_kmethod : AreInterpolationSpaces
    (KMethod A₀ A₁ θ q) A₀ A₁ (KMethod B₀ B₁ θ q) B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) := by
  sorry

/-- Part of Theorem 3.1.2 -/
lemma isExactOfExponent_kmethod : IsExactOfExponent (C_KMethod θ q) θ := by
  sorry

/-- The constant of inequality (6). -/
def γKMethod' (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Part of Theorem 3.1.2 -/
lemma addNorm_le_knorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) :
    addNorm A₀ A₁ t x ≤ γKMethod' θ q * t ^ θ * KNorm A₀ A₁ θ q x  := by
  sorry

-- Todo: ⊓, +, IsIntermediateSpace, AreInterpolationSpaces respect ≈

/-- Theorem 3.1.2: If intermediate spaces are equivalent to the ones obtained by the K-method,
then this gives rise to an interpolation space. -/
lemma areInterpolationSpaces_of_le_kmethod
    (hA : A ≈ KMethod A₀ A₁ θ q) (hB : B ≈ KMethod B₀ B₁ θ q) :
    AreInterpolationSpaces A A₀ A₁ B B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) :=
  areInterpolationSpaces_kmethod.equiv hA.symm .rfl .rfl hB.symm .rfl .rfl


end QuasiENorm
