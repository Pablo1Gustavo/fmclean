
section propositional

variables P Q R : Prop

------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro Np,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro NNp,
  by_cases Hp: P,
    exact Hp,

    by_contradiction,
    contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
    exact doubleneg_elim P,

    exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro Dpq,
  cases Dpq with p q,
    right,
    exact p,

    left,
    exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro Cpq,
  cases Cpq with p q,
  split,
    exact q,

    exact p,
end

------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro DNpq,
  intro p,
  cases DNpq with Np q,
    contradiction,

    exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro Dpq,
  intro Np,
  cases Dpq with p q,
    contradiction,

    exact q,
end

------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros Ipq Nq p,
  exact Nq (Ipq p),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros INqNp p,
  by_cases Hq: Q,
    exact Hq,

    have Np := INqNp Hq,
    contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
    exact impl_as_contrapositive P Q,

    exact impl_as_contrapositive_converse P Q,
end

------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro NDpNp,
  have DpNp: P ∨ ¬P,
    right,
    intro p,
    have DpNp: P ∨ ¬P,
      left,
      exact p,

      exact NDpNp DpNp,
  exact NDpNp DpNp,
end

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros IIpqp Np,
  have Ipq: P → Q,
    intro p,
    contradiction,

  exact Np (IIpqp Ipq),
end

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros Dpq CNpNq,
  cases CNpNq with Np Nq,
  cases Dpq with p q,
    contradiction,

    contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros Cpq DNpNq,
  cases Cpq with p q,
  cases DNpNq with Np Nq,
    contradiction,

    contradiction,
end

------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intros NDpq,
  split,
    intro p,
    have Dpq: P ∨ Q,
      left,
      exact p,
    exact NDpq Dpq,

    intro q,
    have Dpq: P ∨ Q,
      right,
      exact q,
    exact NDpq Dpq,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros CNpNq Dpq,
  cases CNpNq with Np Nq,
  cases Dpq,
    contradiction,

    contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro NCpq,
  by_cases P,
    left,
    intro q,
    have Cpq: P ∧ Q,
      split,
        exact h,

        exact q,
    exact NCpq Cpq,
  
    right,
    exact h,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros DNqNp Cpq,
  cases Cpq with p q,
  cases DNqNp,
    contradiction,

    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
    exact demorgan_conj P Q,
    
    exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
    exact demorgan_disj P Q,

    exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro CpDqr,
  cases CpDqr with p Dqr,
  cases Dqr with q r,
    left,
    split,
      exact p,

      exact q,

    right,
    split,
      exact p,

      exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro DCpqCpr,
  cases DCpqCpr with Cpq Cpr,
  split,
    exact Cpq.left,

    left,
    exact Cpq.right,

    split,
      exact Cpr.left,

      right,
      exact Cpr.right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro DpCqr,
  cases DpCqr with p Cqr,
    split,
      left,
      exact p,

      left,
      exact p,

    cases Cqr with q r,
    split,
      right,
      exact q,

      right,
      exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro CDpqDpr,
  cases CDpqDpr with Dpq Dpr,
  cases Dpq with p q,
    left,
    exact p,

    cases Dpr with p r,
      left,
      exact p,
      
      right,
      split,
        exact q,

        exact r,
end

------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros ICpqr p q,
  have Cpq : P ∧ Q,
    split,
      exact p,

      exact q,
  exact ICpqr Cpq,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros IpIqr Cpq,
  cases Cpq with p q,
  exact (IpIqr p) q,
end

------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro Cpq,
  exact Cpq.left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro Cpq,
  exact Cpq.2,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
    intro Cpp,
    exact Cpp.right,

    intro p,
    split,
      exact p,

      exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
    intro Dpp,
    cases Dpp with p p,
      exact p,

      exact p,
    intro p,
    left,
    exact p,
end

end propositional

----------------------------------------------------------------

section predicate

variable U : Type
variables P Q : U -> Prop

------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros NEPx x Px, 
  have EPx: ∃x, P x,
    existsi x,
    exact Px,
  contradiction,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros AxNPx ExPx,
  cases ExPx with x Px,
  exact (AxNPx x) Px,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  rw [contrapositive_law, doubleneg_law],
  intros NExNPx x,
  by_cases HPx: P x,
    exact HPx,
    
    have ExNPx: ∃x, ¬P x,
      existsi x,
      exact HPx,
    contradiction,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros ExNPx AxPx,
  cases ExNPx with x NPx,
  exact NPx (AxPx x),
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
    exact demorgan_forall U P,

    exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
    exact demorgan_exists U P,

    exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros EPx AxNPx,
  cases EPx with x Px,
  exact (AxNPx x) Px,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros AxPx ExNPx,
  cases ExNPx with x NPx,
  exact NPx (AxPx x),
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros NExNPx x,
  by_contradiction NPx,
  have ExNPx: ∃x, ¬P x,
    existsi x,
    exact NPx,
  exact NExNPx ExNPx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro NAxNPx,
  by_contradiction NExPx,
  exact NAxNPx ((demorgan_exists U P) NExPx),
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
     exact forall_as_neg_exists U P,

     exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
    exact exists_as_neg_forall U P,
    
    exact exists_as_neg_forall_converse U P,
end

------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro ExCPxQx,
  cases ExCPxQx with x CPxQx,
  cases CPxQx with Px Qx,
  split,
    existsi x,
    exact Px,

    existsi x,
    exact Qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro ExDPxQx,
  cases ExDPxQx with x DPxQx,
  cases DPxQx with Px Qx,
    left,
    existsi x,
    exact Px,

    right,
    existsi x,
    exact Qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro DExPxExQx,
  cases DExPxExQx with ExPx ExQx,
    cases ExPx with x Px,
    existsi x,
    left,
    exact Px,

    cases ExQx with x Qx,
    existsi x,
    right,
    exact Qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro AxCPxQx,
  split,
    intro x,
    exact (AxCPxQx x).left,

    intro x,
    exact (AxCPxQx x).right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros CAxPxAxQx x,
  split,
    exact CAxPxAxQx.left x,

    exact CAxPxAxQx.right x,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros DAxPxAxQx x,
  cases DAxPxAxQx with AxPx AxQx,
    left,
    exact AxPx x,

    right,
    exact AxQx x,
end

/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
