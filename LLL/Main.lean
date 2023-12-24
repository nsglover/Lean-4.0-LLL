-- A Formal Proof of the Lovász Local Lemma and Symmetric Lovász Local Lemma

-- This import covers everything we need; finite sets, measure theory, extended reals, and probability theory.
import Mathlib.Probability.Independence.Basic

/-
  Since we are constantly dealing with finite sets, measures, and big products/intersections, it will make the proof
  much more readable if we open these libraries
-/
open Finset MeasureTheory BigOperators

/-
  If the events Eᵢ are all independent and occur with probability less than 1, then it's obviously true that one can
  avoid them all with nonzero probability, simply due to the fact that a product of positive quantities is positive.
  The Lovasz Local Lemma says the same holds if the events are "almost independent", a notion captured by some
  "pseudo-probabilities" X and a dependency digraph Γ. I'm following the proof from these notes (and, for readability,
  using it's notation as well): https://theory.stanford.edu/~jvondrak/MATH233A-2018/Math233-lec02.pdf

  To be more precise, here is the full theorem statement in English: Suppose we have a probability space Ω with
  probability measure ℙ, as well as events E₁,…,Eₙ. Let G be a dependency digraph for these events, and let Γ(i) be
  the neighborhood of Eᵢ in G. In other words, Γ(i) lists all other event indices j such that j ≠ i and Eᵢ depends on
  Eⱼ. Also, assume that we have real numbers X₁,…,Xₙ in the open interval (0, 1) such that, for each i, we have that
  ℙ(Eᵢ) ≤ Xᵢ * (∏ j, 1 - Xⱼ), where the product is taken over all j ∈ Γ(i). Given all of this, theorem says that we
  can avoid all the events; the probability of the intersection of their complements is nonzero. In particular, it is
  bounded from below by (∏ j, 1 - Xⱼ), where the product is taken over all j ∈ {1,…,n}.
-/
theorem lovasz_local_lemma
  {Ω : Type*}
  [MeasurableSpace Ω]
  {ℙ : Measure Ω}
  [IsProbabilityMeasure ℙ]
  {n : ℕ}
  {E : Fin n → Set Ω}
  (h_events : ∀ i, MeasurableSet (E i))
  {Γ : Fin n → Finset (Fin n)}
  (h_no_self_loops : ∀ i, i ∉ Γ i)
  (h_dependency_digraph : ∀ i, ∀ J ⊆ ({i} ∪ (Γ i))ᶜ, ProbabilityTheory.IndepSet (E i) (⋂ j ∈ J, (E j)ᶜ) ℙ)
  {X : Fin n → ENNReal}
  (h_pseudo_probability : ∀ i, 0 < X i ∧ X i < 1)
  (h_independence_bound : ∀ i, ℙ (E i) ≤ X i * ∏ j in Γ i, (1 - X j)) :
  ℙ (⋂ i, (E i)ᶜ) ≠ 0 ∧ ∏ i, (1 - X i) ≤ ℙ (⋂ i, (E i)ᶜ) := by
  /-
    To make life easier, we make a few local definitions:
    - Firstly, we extend the dependency digraph Γ to include self-loops; after all, nontrivial
      events are dependent on themselves. Call this new digraph Γ'.
    - Secondly, we define shorthand for the intersection of the complements some subset of our events,
      since we'll be using it a lot.
    - Thirdly, we define shorthand for the probability of the above intersection. This is the probability of avoiding
      all events in the given subset.
  -/
  let Γ' : (Fin n → Finset (Fin n)) := fun i ↦ insert i (Γ i)
  let inter_over_comp : (Finset (Fin n) → Set Ω) := fun S ↦ ⋂ i ∈ S, (E i)ᶜ
  let P : (Finset (Fin n) → ENNReal) := fun S ↦ ℙ (inter_over_comp S)

  /-
    We'll also prove a few helpful lemmas about these definitions and the definitions in the theorem statement.
    - 1. The probability of the empty intersection is 1.
    - 2. The intersection of more sets is smaller than the intersection of fewer sets.
    - 3. We have 0 < 1 - X i < 1 for all i.
    - 4. P Finset.univ is the probability of the intersection of the complements.
    - 5. Given S, a ∈ S, and any set T, (S \ insert a T) is of course a subset of (S.erase a). We use this a lot.
    - 6. Given S, a ∈ S, and any set T, (S \ insert a T) is of course a strict subset of S. We also use this a lot.
    All of these lemmas have simple proofs, so I didn't think any annotations were necessary.
  -/

  /- Lemma 1 -/
  have P_empty_eq_one : P ∅ = 1 := by
    have inter_over_empty_eq_univ : inter_over_comp ∅ = Set.univ := by
      rw [Set.iInter_eq_univ]
      intro i
      ext x
      apply Iff.intro
      {
        intro _
        exact Set.mem_univ x
      }
      {
        intro _
        rw [Set.mem_iInter]
        intro i_in_empty
        exfalso
        exact Finset.not_mem_empty i i_in_empty
      }

    simp only [P]
    simp only [inter_over_comp] at inter_over_empty_eq_univ
    rw [inter_over_empty_eq_univ]
    exact measure_univ

  /- Lemma 2 -/
  have inter_subset_of_supset : ∀ M N : Finset (Fin n), N ⊆ M → inter_over_comp M ⊆ inter_over_comp N := by
    intros M N N_subset_M
    intros x hx
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hi
    rw [Set.mem_iInter] at hx
    specialize hx i
    rw [Set.mem_iInter] at hx
    exact hx (mem_of_subset N_subset_M hi)

  /- Lemma 3 -/
  have one_minus_pprob_is_pprob : ∀ i, 0 < 1 - X i ∧ 1 - X i < 1 := by
    intro i
    apply And.intro
    {
      rw [tsub_pos_iff_lt]
      exact (h_pseudo_probability i).2
    }
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt (h_pseudo_probability i).1)

  /- Lemma 4 -/
  have P_univ_eq_prob_inter : P univ = ℙ (⋂ i, (E i)ᶜ) := by
    simp only [P, inter_over_comp]
    simp only [mem_univ, Set.iInter_true]

  /- Lemma 5 -/
  have sdiff_subset : ∀ S : Finset (Fin n), ∀ a ∈ S, ∀ T : Finset (Fin n), S \ insert a T ⊆ S.erase a := by
    intros S a _ T
    rw [← sdiff_singleton_eq_erase]
    exact sdiff_subset_sdiff (subset_refl S) (singleton_subset_iff.2 (mem_insert_self a T))

  /- Lemma 6 -/
  have sdiff_ssubset : ∀ S : Finset (Fin n), ∀ a ∈ S, ∀ T : Finset (Fin n), S \ insert a T ⊂ S := by
    intros S a a_in_S T
    apply Finset.ssubset_of_subset_of_ssubset
    exact sdiff_subset _ _ a_in_S _
    exact erase_ssubset a_in_S

  /-
    The bulk of the work is done by the following lemma: For all S ⊆ {1,...,n}, we have that the probability of
    avoiding all events Eₐ for a ∈ S is nonzero, as well as the fact that the probability of avoiding all events Eₐ
    for a ∈ S is more than (1 - Xₐ) times the probability of avoiding all events Eᵢ for i ∈ S \ {a}.
  -/
  have main_lemma : ∀ S : Finset (Fin n), P S ≠ 0 ∧ ∀ a ∈ S, P (S.erase a) * (1 - X a) ≤ P S := by
    -- We go by strong induction on S; the predicate we're trying to prove is of course:
    let predicate : (Finset (Fin n) → Prop) := fun S ↦ P S ≠ 0 ∧ ∀ a ∈ S, P (S.erase a) * (1 - X a) ≤ P S

    -- As is typical in strong induction, the induction step absorbs the base case.
    have induction_step : ∀ S : Finset (Fin n), (∀ T ⊂ S, predicate T) → predicate S := by
       -- Stop using predicate notation.
      simp only [predicate]
      clear predicate

      -- Let S be arbitrary and assume the claim holds for all strictly smaller sets.
      intros S induction_hypothesis

      /-
        We now prove the main part of our goal as a lemma, for convenience (it implies the other part). This section
        contains nearly all of the hard work for proving the Lovasz Local Lemma. It is split into three main parts:
        1. Establishing the lower bound P (S \ {a}) - ℙ (E a) * P (S \ Γ' a) ≤ P S for all a ∈ S
        2. Dividing the above bound by P (S \ {a}) and rewriting P (S \ Γ' a) / P (S \ {a}) as a telescoping product,
           we can apply the induction hypothesis to each term in the product.
        3. Cancel out the ratio of two big products into one big products over a difference of the two product sets.
      -/
      have main_inequality : ∀ a ∈ S, P (S.erase a) * (1 - X a) ≤ P S := by
        intros a a_in_S

        -- Part 1: We use independence and probability basics to get a lower bound on P S.
        have lower_bound : P (S.erase a) - ℙ (E a) * P (S \ Γ' a) ≤ P S := by
          -- We pull (E a)ᶜ out of the intersection over S.
          have inter_over_S_split : inter_over_comp S = (E a)ᶜ ∩ inter_over_comp (S.erase a) := by
            simp only [inter_over_comp]
            rw [← insert_erase a_in_S, set_biInter_insert a (S.erase a), insert_erase a_in_S]

          -- Using the above, we pull (E a)ᶜ out and use complementary measure.
          have P_S_split : P S = P (S.erase a) - ℙ ((E a) ∩ inter_over_comp (S.erase a)) := by
            simp only [P]
            simp only [inter_over_comp] at inter_over_S_split
            rw [inter_over_S_split]
            apply Eq.symm
            apply ENNReal.sub_eq_of_eq_add
            exact ne_of_lt (measure_lt_top ℙ _)
            apply Eq.symm
            rw [← Set.diff_eq_compl_inter, Set.inter_comm]
            apply measure_diff_add_inter
            exact h_events a

          -- We have a simple inequality arising from monotonicity of measure.
          have inequality : P (S.erase a) - ℙ ((E a) ∩ inter_over_comp (S \ Γ' a)) ≤
                            P (S.erase a) - ℙ ((E a) ∩ inter_over_comp (S.erase a)) := by
            -- This immediately follows from lemma (2).
            have subset : (E a) ∩ inter_over_comp (S.erase a) ⊆
                          (E a) ∩ inter_over_comp (S \ Γ' a) := by
              intros x hx
              apply And.intro
              exact hx.1
              have subset := sdiff_subset S a a_in_S (Γ a)
              exact Set.mem_of_subset_of_mem (inter_subset_of_supset (S.erase a) (S \ Γ' a) subset) hx.2

            exact tsub_le_tsub_left (ℙ.mono subset) _

          -- Finally, we use independence to separate (E a) from its independent sets as given by S \ Γ' a.
          have prob_inter_eq_prod : ℙ ((E a) ∩ inter_over_comp (S \ Γ' a)) = ℙ (E a) * P (S \ Γ' a) := by
            specialize h_dependency_digraph a (S \ Γ' a)
            have subset : S \ Γ' a ⊆ (Γ' a)ᶜ := by
              rw [sdiff_eq_inter_compl]
              intros x hx
              rw [mem_inter] at hx
              exact hx.2

            have inter_meas : MeasurableSet (inter_over_comp (S \ Γ' a)) := by
              simp only [inter_over_comp]
              apply MeasurableSet.iInter
              intro i
              apply MeasurableSet.iInter
              intro _
              apply MeasurableSet.compl
              exact h_events i

            simp only [inter_over_comp] at inter_meas
            have indep := h_dependency_digraph subset
            exact (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul (h_events a) inter_meas ℙ).1 indep

          -- We combine the above to complete the proof.
          rw [← P_S_split] at inequality
          rw [← prob_inter_eq_prod]
          exact inequality


        /-
          Part 2: Now, we write P (S \ Γ' a) / P (S.erase a) as a telescoping product, and apply induction_hypothesis to
          each of the terms. In practice, we'll do this one term at a time using another induction.
        -/
        have product_bound : P (S \ Γ' a) ≤ P (S.erase a) * (∏ i in (S ∩ (Γ a)), (1 - X i)⁻¹) := by
          -- We go by induction on T; the predicate we're trying to prove is:
          let predicate : (Finset (Fin n) → Prop) :=
            fun T ↦ P (S \ Γ' a) ≤ P (S.erase a) * (∏ i in T, (1 - X i)⁻¹) * P (S \ Γ' a) * (P (S \ (insert a T)))⁻¹

          have induction_lemma : predicate (S ∩ Γ a) := by
            -- The base case is more or less immediate.
            have base_case : predicate ∅ := by
              -- Stop using predicate notation.
              simp only [predicate]
              clear predicate

              rw [
                insert_eq, prod_empty, mul_one, insert_empty, sdiff_singleton_eq_erase a S,
                mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul
              ]
              exact (induction_hypothesis (S.erase a) (erase_ssubset a_in_S)).1
              exact ne_of_lt (measure_lt_top ℙ _)

            -- The induction step makes use of induction_hypothesis to show the upper bound for one more term.
            have induction_step :
              ∀ { b : Fin n }, ∀ { T : Finset (Fin n) }, b ∈ S ∩ Γ a → T ⊆ S ∩ Γ a → b ∉ T → predicate T → predicate (insert b T) := by

              -- Stop using predicate notation.
              simp only [predicate]
              clear base_case
              clear predicate

              -- Let T and b be arbitrary such that b ∉ T, and assume the claim holds for S.
              intros b T b_in_S_cap_Gam_a _ b_notin_T ih_lem

              -- First, we pull b out of the product.
              rw [prod_insert b_notin_T, mul_comm (1 - X b)⁻¹ _, mul_assoc]

              /-
                Next, (1 - X b)⁻¹ is lower bounded by the desired ratio; this follows from the inductive_hypothesis.
                Although this ends up being rather difficult in Lean, it's not anything mathematically interesting;
                it's an immediate application of the inductive hypothesis to (S \ insert a T) and basic inequality
                manipulation. So, I didn't feel it necessary to provide annotations here.
              -/
              have ih_lower_bound :  P (S \ insert a (insert b T)) * (P (S \ insert a T))⁻¹ ≤ (1 - X b)⁻¹ := by
                specialize induction_hypothesis (S \ insert a T) (sdiff_ssubset S a a_in_S T)
                have induction_bound := induction_hypothesis.2 b
                rw [
                  ENNReal.le_inv_iff_mul_le, mul_assoc, mul_comm _ (1 - X b), ← mul_assoc,
                  ← ENNReal.le_inv_iff_mul_le, inv_inv
                ]
                rw [insert_eq, insert_eq, insert_eq]
                rw [← sdiff_insert] at induction_bound
                rw [insert_eq, insert_eq] at induction_bound
                rw [union_comm, union_assoc, union_comm T _]
                have b_in_set : b ∈ S \ ({a} ∪ T) := by
                  rw [mem_sdiff]
                  apply And.intro
                  {
                    rw [mem_inter] at b_in_S_cap_Gam_a
                    exact b_in_S_cap_Gam_a.1
                  }
                  rw [not_mem_union]
                  apply And.intro
                  {
                    rw [not_mem_singleton]
                    apply by_contradiction
                    intro not_be_neq_a
                    rw [Ne.def] at not_be_neq_a
                    have b_eq_a := by_contradiction not_be_neq_a
                    rw [b_eq_a] at b_in_S_cap_Gam_a
                    exact (not_mem_mono (inter_subset_right S (Γ a)) (h_no_self_loops a)) b_in_S_cap_Gam_a
                  }
                  exact b_notin_T

                exact induction_bound b_in_set

              -- To make what follows easier, we move the term (1 - X b)⁻¹ all the way to the right.
              rw [mul_assoc, mul_assoc _ (1 - X b)⁻¹ _, mul_comm (1 - X b)⁻¹ _]
              repeat { rw [← mul_assoc] }

              -- We can use transitivity with the lemma's induction hypothesis to reduce the inequality.
              apply le_trans ih_lem _

              -- We split a ratio (i.e. use a/c = a/b * b/c) to prepare the inequality for applying ih_lower_bound.
              nth_rewrite 1 [← mul_one (ℙ (⋂ i ∈ S \ insert a (Γ a), (E i)ᶜ))]
              have ne_zero : P (S \ insert a (insert b T)) ≠ 0 :=
                (induction_hypothesis (S \ insert a (insert b T)) (sdiff_ssubset S a a_in_S (insert b T))).1
              have ne_top : P (S \ insert a (insert b T)) ≠ ⊤ := ne_of_lt (measure_lt_top ℙ _)
              nth_rewrite 2 [← ENNReal.inv_mul_cancel ne_zero ne_top]
              rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
              rw [mul_assoc _ _ (P (S \ insert a T))⁻¹]

              -- Finally, we apply ih_lower_bound, which completes the induction step.
              apply mul_le_mul _ ih_lower_bound
              exact zero_le _
              exact zero_le _
              rw [mul_assoc]

            -- Invoking the induction theorem for finite sets completes the proof.
            exact Finset.induction_on' (S ∩ Γ a) base_case induction_step

          -- Stop using predicate notation.
          simp only [predicate] at induction_lemma
          clear predicate

          -- The desired bound follows easily from the induction_lemma; we just need to cancel the division.
          have same_set : S \ (insert a (S ∩ Γ a)) = S \ Γ' a := by
            simp only [Γ']
            rw [
              insert_eq, insert_eq, union_distrib_left, sdiff_inter_distrib_right,
              union_eq_right.2 (singleton_subset_iff.2 a_in_S), sdiff_self, bot_eq_empty, empty_union
            ]

          rwa [same_set, mul_assoc, ENNReal.mul_inv_cancel, mul_one] at induction_lemma
          {
            have ssubset := Finset.ssubset_of_subset_of_ssubset (sdiff_subset S a a_in_S (Γ a)) (erase_ssubset a_in_S)
            exact (induction_hypothesis (S \ Γ' a) ssubset).1
          }
          exact ne_of_lt (measure_lt_top ℙ _)


        /-
          Part 3: Cancel out the ratio of two big products into one big products over a difference of the two product
          sets. Namely, the product over Γ a divided by the product over S ∩ Γ a should yield a product over Γ a \ S.
        -/
        have prod_cancel : (∏ i in Γ a, (1 - X i)) * (∏ i in S ∩ Γ a, (1 - X i)⁻¹) = ∏ i in Γ a \ S, (1 - X i) := by
          have prod_split : (∏ i in Γ a, (1 - X i)) = (∏ i in Γ a \ S, (1 - X i)) * (∏ i in S ∩ Γ a, (1 - X i)) := by
            rw [inter_comm, mul_comm, eq_comm]
            exact Finset.prod_inter_mul_prod_diff _ _ _

          have cancel : ∀ i ∈ S ∩ Γ a, (1 - X i) * (1 - X i)⁻¹ = 1 := by
            intros i _
            rw [ENNReal.mul_inv_cancel]
            exact ne_of_gt (one_minus_pprob_is_pprob i).1
            exact ne_of_lt (lt_trans (one_minus_pprob_is_pprob i).2 ENNReal.one_lt_top)

          rw [prod_split, mul_assoc, ← prod_mul_distrib, prod_eq_one cancel, mul_one]

        -- And now we can of course upper bound this resulting product by 1.
        have prod_le_one : (∏ i in Γ a \ S, (1 - X i)) ≤ 1 := by
          have le_one : ∀ i ∈ Γ a \ S, 1 - X i ≤ 1 := by
            intros i _
            exact le_of_lt (one_minus_pprob_is_pprob i).2

          exact prod_le_one' le_one

        -- Using the above work, we combine the independence and product bounds and then simplify the big products.
        have two_products :
          ℙ (E a) * P (S \ Γ' a) ≤
          (X a * ∏ j : Fin n in Γ a, (1 - X j)) * ((∏ i : Fin n in S ∩ Γ a, (1 - X i)⁻¹) * P (S.erase a)) := by
            apply mul_le_mul
            exact h_independence_bound a
            {
              rw [mul_comm] at product_bound
              exact product_bound
            }
            exact zero_le _
            exact zero_le _

        rw [← mul_assoc _ _ (P (S.erase a))] at two_products
        rw [mul_assoc (X a) _ _] at two_products
        rw [prod_cancel] at two_products
        rw [mul_comm _ (P (S.erase a))] at two_products

        -- From here, we can upper bound the product by 1 and conclude that P (S.erase a) * (1 - X a) ≤ P S.
        -- rw [mul_comm _ (P (S.erase a)), ← mul_assoc _ (P (S.erase a)) _, mul_comm _ (P (S.erase a))] at two_products
        have no_products : P (S.erase a) * X a * ∏ i : Fin n in Γ a \ S, (1 - X i) ≤ P (S.erase a) * X a * 1 := by
          apply mul_le_mul
          exact le_refl _
          exact prod_le_one
          exact zero_le _
          exact zero_le _

        rw [mul_one, mul_assoc] at no_products
        have final_inequality := le_trans two_products no_products

        -- Combining final_inequality with the lower_bound from earlier, we complete the proof of the main inequality!
        rw [ENNReal.mul_sub]
        swap
        {
          intros _ _
          exact ne_of_lt (measure_lt_top ℙ _)
        }
        rw [mul_one]
        exact le_trans (tsub_le_tsub_left final_inequality (P (S.erase a))) lower_bound

      -- Using the main part of our goal, we can now quickly prove the easier part of our goal (that P S ≠ 0).
      apply And.intro
      {
        by_cases S_empty : S = ∅
        {
          simp only [P] at P_empty_eq_one
          rw [S_empty, P_empty_eq_one]
          exact one_ne_zero
        }
        cases nonempty_iff_ne_empty.2 S_empty with | intro a a_in_S =>
        apply ne_of_gt
        specialize main_inequality a a_in_S
        specialize induction_hypothesis (S.erase a) (erase_ssubset a_in_S)
        apply lt_of_le_of_lt'
        exact main_inequality
        exact ENNReal.mul_pos induction_hypothesis.1 (ne_of_gt (one_minus_pprob_is_pprob a).1)
      }

      -- Finally, we complete the proof; we've already finished proving the second part of the goal.
      exact main_inequality

    intro S
    exact Finset.strongInductionOn S induction_step

  -- Now that we've proven the lemma, we can immediately conclude the first part the theorem.
  apply And.intro
  {
    have events_avoidable := (main_lemma univ).1
    rwa [P_univ_eq_prob_inter] at events_avoidable
  }

  /-
    We'll now use induction to prove an iterated version of our lemma: For all S ⊆ {1,...,n}, the probability of
    avoiding all n events is lower bounded by the probability of avoiding those events not in S times the product of
    (1 - Xₐ) over all a ∈ S.
  -/
  have main_lemma_iterated : ∀ S : Finset (Fin n), P Sᶜ * ∏ i in S, (1 - X i) ≤ P univ := by
    -- We go by induction on S; the predicate we're trying to prove is of course:
    let predicate : (Finset (Fin n) → Prop) := fun S ↦ P Sᶜ * ∏ i in S, (1 - X i) ≤ P univ

    have base_case : predicate ∅ := by
      -- Stop using predicate notation.
      simp only [predicate]
      clear predicate

      rw [Finset.prod_empty, mul_one, compl_empty]

    have induction_step : ∀ a : Fin n, ∀ S : Finset (Fin n), a ∉ S → predicate S → predicate (insert a S) := by
      -- Stop using predicate notation.
      simp only [predicate]
      clear base_case
      clear predicate

      -- Let S and a be arbitrary such that a ∉ S, and assume the claim holds for S.
      intros a S a_notin_S induction_hypothesis

      -- We pull an element out of Sᶜ, which is the same as adding an element to S, and apply the main lemma to it.
      specialize main_lemma Sᶜ
      have main_lemma_ineq := main_lemma.2
      clear main_lemma
      specialize main_lemma_ineq a (mem_compl.2 a_notin_S)
      rw [← compl_insert] at main_lemma_ineq

      -- Now we turn the product over (insert a S) into the product over S times the term at a
      rw [prod_insert a_notin_S, ← mul_assoc]

      -- Transitivity and multiplicativity of ≤ for nonnegative reals completes the proof.
      apply le_trans _ induction_hypothesis
      apply mul_le_mul
      exact main_lemma_ineq
      exact le_refl _
      exact prod_nonneg (fun i _ ↦ le_of_lt (one_minus_pprob_is_pprob i).1)
      exact zero_le _

    -- Invoking the induction theorem for finite sets completes the proof.
    exact Finset.induction base_case induction_step


  -- Finally, we can use this iterated version to conclude the proof of the theorem!
  specialize main_lemma_iterated univ
  rwa [P_univ_eq_prob_inter, ← compl_empty, compl_involutive, P_empty_eq_one, one_mul] at main_lemma_iterated



/-
  There is also a "symmetric" version of the theorem, which is typically the one used in practice since it only
  deals with an upper the number of other events that an event is dependent on rather than the specific events.

  To be precise, it says if each event is individually avoidable (probability strictly less than 1, call it p), each
  event depends on at most d other events, and ep(d + 1) ≤ 1 (where e is Euler's number), then the events are
  collectively avoidable; the probability of the intersection of their complements is nonzero.

  NOTE: I couldn't find anything on Euler's number in Lean, so I decided to just use the slightly tighter bound
  p ≤ (1 - 1/(d + 1))^d / (d + 1) for some d ∈ ℕ. Indeed, if ep(d + 1) ≤ 1, we have p(d + 1) ≤ e^(-1) ≤ e^(-d/(d + 1)).
  By a classical inequality, this is at most (1 - 1/(d + 1))^d, so our assumption is indeed stronger.
-/
theorem symmetric_lovasz_local_lemma
  {Ω : Type*}
  [MeasurableSpace Ω]
  {ℙ : Measure Ω}
  [IsProbabilityMeasure ℙ]
  {n : ℕ}
  {E : Fin n → Set Ω}
  (h_events : ∀ i, MeasurableSet (E i))
  {Γ : Fin n → Finset (Fin n)}
  (h_no_self_loops : ∀ i, i ∉ Γ i)
  (h_dependency_digraph : ∀ i, ∀ J ⊆ ({i} ∪ (Γ i))ᶜ, ProbabilityTheory.IndepSet (E i) (⋂ j ∈ J, (E j)ᶜ) ℙ)
  (p : ENNReal)
  (h_event_probability_bound : ∀ i, ℙ (E i) ≤ p)
  (d : ℕ)
  (h_d_pos : 1 ≤ d)
  (h_maximum_dependence : ∀ i, (Γ i).card ≤ d)
  (h_p_bound : p ≤ (↑(d + 1))⁻¹ * (1 - (↑(d + 1))⁻¹)^d) :
  ℙ (⋂ i, (E i)ᶜ) ≠ 0 := by
    -- We take our pseudo-probabiliies to be Xᵢ = 1 / (d + 1)
    let X : Fin n → ENNReal := fun _ ↦ (↑(d + 1))⁻¹

    -- First, we need to show that X actually gives pseudo-probabilities.
    have h_pseudo_probability : ∀ i, 0 < X i ∧ X i < 1 := by
      intro i
      simp only [X]
      apply And.intro
      {
        rw [ENNReal.inv_pos]
        exact ENNReal.coe_ne_top
      }
      rw [ENNReal.inv_lt_one]
      apply lt_of_lt_of_le
      exact ENNReal.one_lt_two
      rw [← one_add_one_eq_two]
      norm_cast
      apply add_le_add
      exact h_d_pos
      exact le_refl _

    -- The main work here is showing that X actually gives an independence bound; it uses a classical inequality.
    have h_independence_bound : ∀ i, ℙ (E i) ≤ X i * ∏ j in Γ i, (1 - X j) := by
      intro i
      apply le_trans
      exact h_event_probability_bound i

      -- We upper bound p using the h_p_bound,
      apply le_trans
      exact h_p_bound

      -- We now simplify the right-hand side using the definition of X.
      simp only [X]
      apply mul_le_mul
      exact le_refl _
      {
        -- Finally, we're just left with a constant product over Γ i.
        rw [prod_const]
        apply pow_le_pow_of_le_one
        exact zero_le _
        simp
        exact h_maximum_dependence i
      }
      exact zero_le _
      exact zero_le _

    -- From here, it's just a direct aplication of the (asymmetric) Lovasz Local Lemma.
    exact (lovasz_local_lemma h_events h_no_self_loops h_dependency_digraph h_pseudo_probability h_independence_bound).1
