Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAST_CLAUSES_term_abbrevs.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm1098347_spec.
Require Import thm1098348_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1111524 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1111525 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1111526 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1111525 A h) (@lem1111524 A h)). Qed.
Lemma lem1111527 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1111526 A h t). Qed.
Lemma lem1111528 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1111529 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1111528 A h t) (@lem1111527 A h t)). Qed.
Lemma lem1111530 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1111548 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1111549 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (@lem1111548 A h t). Qed.
Lemma lem1111550 {A : Type'} (h : A) : (term7 A h) = (term8 A h).
Proof. exact (@lem1111549 A h (@nil A)). Qed.
Lemma lem1111552 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term9 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1111553 {A : Type'} (x : list A) (z : A) (y : A) : (term10 A x y z) = y.
Proof. exact (@lem1111552 A (list A) x z y). Qed.
Lemma lem1111554 {A : Type'} (h : A) : (term8 A h) = h.
Proof. exact (@lem1111553 A (@nil A) (@LAST A (@nil A)) h). Qed.
Lemma lem1111555 {A : Type'} (h : A) : (term7 A h) = h.
Proof. exact (TRANS (@lem1111550 A h) (@lem1111554 A h)). Qed.
Lemma lem1111556 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1111557 {A : Type'} (h : A) : (term11 A h) = (@eq A h).
Proof. exact (MK_COMB (@lem1111556 A) (@lem1111555 A h)). Qed.
Lemma lem1111558 {A : Type'} (h : A) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1111559 {A : Type'} (h : A) : ((term7 A h) = h) = (h = h).
Proof. exact (MK_COMB (@lem1111557 A h) (@lem1111558 A h)). Qed.
Lemma lem1111561 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1111562 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1111561 A x). Qed.
Lemma lem1111563 {A : Type'} (h : A) : (h = h) = True.
Proof. exact (@lem1111562 A h). Qed.
Lemma lem1111564 {A : Type'} (h : A) : ((term7 A h) = h) = True.
Proof. exact (TRANS (@lem1111559 A h) (@lem1111563 A h)). Qed.
Lemma lem1111565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1111566 {A : Type'} (h : A) : (term12 A h) = (and True).
Proof. exact (MK_COMB (@lem1111565) (@lem1111564 A h)). Qed.
Lemma lem1111570 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1111571 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (@lem1111570 A h t). Qed.
Lemma lem1111572 {A : Type'} (h : A) (k : A) (t : list A) : (term13 A h k t) = (term14 A h k t).
Proof. exact (@lem1111571 A h (@cons A k t)). Qed.
Lemma lem1111576 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1111530 A h t (@lem1111529 A h t)). Qed.
Lemma lem1111577 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1111576 A h t). Qed.
Lemma lem1111578 {A : Type'} (k : A) (t : list A) : ((@cons A k t) = (@nil A)) = False.
Proof. exact (@lem1111577 A k t). Qed.
Lemma lem1111579 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem1111580 {A : Type'} (k : A) (t : list A) : (term15 A k t) = (@COND A False).
Proof. exact (MK_COMB (@lem1111579 A) (@lem1111578 A k t)). Qed.
Lemma lem1111581 {A : Type'} (h : A) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1111582 {A : Type'} (k : A) (t : list A) (h : A) : (term16 A k t h) = (@COND A False h).
Proof. exact (MK_COMB (@lem1111580 A k t) (@lem1111581 A h)). Qed.
Lemma lem1111584 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1111585 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (@lem1111584 A h t). Qed.
Lemma lem1111586 {A : Type'} (k : A) (t : list A) : (term5 A k t) = (term6 A k t).
Proof. exact (@lem1111585 A k t). Qed.
Lemma lem1111591 {A : Type'} (h : A) (k : A) (t : list A) : (term14 A h k t) = (term17 A h k t).
Proof. exact (MK_COMB (@lem1111582 A k t h) (@lem1111586 A k t)). Qed.
Lemma lem1111593 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1111594 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem1111593 A t1 t2). Qed.
Lemma lem1111595 {A : Type'} (h : A) (k : A) (t : list A) : (term17 A h k t) = (term6 A k t).
Proof. exact (@lem1111594 A h (term6 A k t)). Qed.
Lemma lem1111600 {A : Type'} (h : A) (k : A) (t : list A) : (term14 A h k t) = (term6 A k t).
Proof. exact (TRANS (@lem1111591 A h k t) (@lem1111595 A h k t)). Qed.
Lemma lem1111601 {A : Type'} (h : A) (k : A) (t : list A) : (term13 A h k t) = (term6 A k t).
Proof. exact (TRANS (@lem1111572 A h k t) (@lem1111600 A h k t)). Qed.
Lemma lem1111602 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1111603 {A : Type'} (h : A) (k : A) (t : list A) : (term18 A h k t) = (term19 A k t).
Proof. exact (MK_COMB (@lem1111602 A) (@lem1111601 A h k t)). Qed.
Lemma lem1111605 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1111606 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A h t).
Proof. exact (@lem1111605 A h t). Qed.
Lemma lem1111607 {A : Type'} (k : A) (t : list A) : (term5 A k t) = (term6 A k t).
Proof. exact (@lem1111606 A k t). Qed.
Lemma lem1111612 {A : Type'} (h : A) (k : A) (t : list A) : ((term13 A h k t) = (term5 A k t)) = ((term6 A k t) = (term6 A k t)).
Proof. exact (MK_COMB (@lem1111603 A h k t) (@lem1111607 A k t)). Qed.
Lemma lem1111614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1111615 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1111614 A x). Qed.
Lemma lem1111616 {A : Type'} (k : A) (t : list A) : ((term6 A k t) = (term6 A k t)) = True.
Proof. exact (@lem1111615 A (term6 A k t)). Qed.
Lemma lem1111617 {A : Type'} (h : A) (k : A) (t : list A) : ((term13 A h k t) = (term5 A k t)) = True.
Proof. exact (TRANS (@lem1111612 A h k t) (@lem1111616 A k t)). Qed.
Lemma lem1111618 {A : Type'} (h : A) (k : A) (t : list A) : (term20 A h k t) = (True /\ True).
Proof. exact (MK_COMB (@lem1111566 A h) (@lem1111617 A h k t)). Qed.
Lemma lem1111620 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1111621 : (True /\ True) = True.
Proof. exact (@lem1111620 True). Qed.
Lemma lem1111622 {A : Type'} (h : A) (k : A) (t : list A) : (term20 A h k t) = True.
Proof. exact (TRANS (@lem1111618 A h k t) (@lem1111621)). Qed.
Lemma lem1111623 {A : Type'} (h : A) (k : A) (t : list A) : True = (term20 A h k t).
Proof. exact (SYM (@lem1111622 A h k t)). Qed.
Lemma lem1111624 {A : Type'} (h : A) (k : A) (t : list A) : term20 A h k t.
Proof. exact (EQ_MP (@lem1111623 A h k t) (@lem0)). Qed.
