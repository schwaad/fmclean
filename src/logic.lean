
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro np,
  apply np,
  exact p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_cases p : P,
  exact p,
  exfalso,
  apply nnp,
  exact p,
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
    split,
    intro nnp,
    by_cases p : P,
    exact p,
    exfalso,
    apply nnp,
    exact p,
    intro p,
    intro np,
    apply np,
    exact p,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with p q,
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
  intro h,
  cases h with np q,
  intro p,
  exfalso,
  have boom := np(p),
  exact boom,
  intro p,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  cases h with p q,
  intro np,
  exfalso,
  have boom := np(p),
  exact boom,
  intro np,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro h,
  intro nq,
  intro p,
  have q := h(p),
  have boom := nq(q),
  exact boom,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  by_cases q : Q,
  intro p,
  exact q,
  have np := h(q),
  intro p,
  exfalso,
  have boom := np(p),
  exact boom,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro h,
  intro nq,
  intro p,
  have q := h(p),
  have boom := nq(q),
  exact boom,
   intro h,
  by_cases q : Q,
  intro p,
  exact q,
  have np := h(q),
  intro p,
  exfalso,
  have boom := np(p),
  exact boom,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  right,
  intro p,
  apply h,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro np,
  apply np,
  apply h,
  intro p,
  exfalso,
  have boom := np(p),
  exact boom,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro h,
  cases h with p q,
  intro f,
  cases f with m n,
  exact m(p),
  intro f,
  cases f with m n,
  exact n(q),
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h,
  cases h with p q,
  intro f,
  cases f with m n,
  exact m(p),
  exact n(q),
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro p,
  apply h,
  left,
  exact p,
  intro q,
  apply h,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  intro f,
  cases f with p q,
  cases h with m n,
 exact m(p),
 cases h with m n,
 exact n(q),
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_contra g,
  apply g,
  right,
  intro p,
  apply h,
  split,
  exact p,
  exfalso,
  apply g,
  left,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h,
  intro f,
  cases f with p q,
  cases h with m n,
  exact m(q),
  exact n(p),
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro h,
  by_contra g,
  apply g,
  right,
  intro p,
  apply h,
  split,
  exact p,
  exfalso,
  apply g,
  left,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
  intro h,
  intro f,
  cases f with p q,
  cases h with m n,
  exact m(q),
  exact n(p),
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro h,
  split,
  intro p,
  apply h,
  left,
  exact p,
  intro q,
  apply h,
  right,
  exact q,
  intro h,
  intro f,
  cases f with p q,
  cases h with m n,
  exact m(p),
  cases h with m n,
  exact n(q),
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p q,
  cases q,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact q,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with p q,
  cases p,
  split,
  exact p_left,
  left,
  exact p_right,
  cases q,
  split,
  exact q_left,
  right,
  exact q_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h,
  split,
  left,
  exact h,
  left,
  exact h,
  cases h,
  split,
  right,
  exact h_left,
  right,
  exact h_right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with p q,
  cases p,
  cases q,
  left,
  exact p,
  left,
  exact p,
  cases q,
  left,
  exact q,
  right,
  split,
  exact p,
  exact q,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro p,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
   intro h,
   intro pq,
   cases pq with p q,
   have g := h(p),
   have r := g(q),
   exact r,
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
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,
  intro p,
  split,
  repeat {exact p},
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp with p p,
  repeat {exact p},
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
  intro h,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro g,
  cases g with m n,
  have npm := h(m),
  apply npm,
  exact n,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contra g,
  apply h,
  intro u,
  by_contra,
  apply g,
  existsi u,
  exact h,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  intro f,
  cases h with m n,
  have px := f(m),
  apply n,
  exact px,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro h,
  by_contra g,
  apply h,
  intro u,
  by_contra,
  apply g,
  existsi u,
  exact h,
  intro h,
  intro f,
  cases h with m n,
  have px := f(m),
  apply n,
  exact px,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro h,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
  intro h,
  intro g,
  cases g with m n,
  have npm := h(m),
  apply npm,
  exact n,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h,
  intro g,
  cases h with m n,
  have npx := g(m),
  apply npx,
  exact n,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h,
  intro g,
  cases g with m n,
  have px := h(m),
  apply n,
  exact px,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro u,
  by_contra g,
  apply h,
  existsi u,
  apply g,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  by_contra g,
  apply h,
  intro u,
  intro pu,
  apply g,
  existsi u,
  exact pu,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  have p := forall_as_neg_exists U P,
  exact p,
  have p := forall_as_neg_exists_converse U P,
  exact p,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  have p := exists_as_neg_forall U P,
  exact p,
  have p := exists_as_neg_forall_converse U P,
  exact p,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  split,
  cases h with p q,
  existsi p,
  cases q with p q,
  exact p,
  cases h with p q,
  existsi p,
  cases q with p q,
  exact q,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with p q,
  cases q with m n,
  left,
  existsi p,
  exact m,
  right,
  existsi p,
  exact n,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with p q,
  cases p with m n,
  split,
  left,
  exact n,
  cases q with m n,
  split,
  right,
  exact n,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro u,
  have g := h(u),
  cases g with p q,
  exact p,
  intro u,
  have g := h(u),
  cases g with p q,
  exact q,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  intro u,
  split,
  cases h with p q,
  exact p(u),
  cases h with p q,
  exact q(u),
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with p q,
  intro u,
  left,
  exact p(u),
  intro u,
  right,
  exact q(u),
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
