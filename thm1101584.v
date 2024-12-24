Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101584_term_abbrevs.
Require Import thm1101159_spec.
Require Import thm1101527_spec.
Lemma lem1101528 {_25328 : Type'} : (term0 _25328) = (term1 _25328).
Proof. exact (eq_refl (term0 _25328)). Qed.
Lemma lem1101529 {_25328 : Type'} : term1 _25328.
Proof. exact (EQ_MP (@lem1101528 _25328) (@lem1101159 _25328)). Qed.
Lemma lem1101530 {_25328 : Type'} : term2 _25328.
Proof. exact (@lem1101529 _25328 term3). Qed.
Lemma lem1101531 {_25328 : Type'} : (term2 _25328) = (term4 _25328).
Proof. exact (eq_refl (term2 _25328)). Qed.
Lemma lem1101532 {_25328 : Type'} : term4 _25328.
Proof. exact (EQ_MP (@lem1101531 _25328) (@lem1101530 _25328)). Qed.
Lemma lem1101533 {_25328 : Type'} (h1 : (@EX _25328) = (term5 _25328)) : (@EX _25328) = (term5 _25328).
Proof. exact (h1). Qed.
Lemma lem1101534 {_25328 : Type'} (h1 : (@EX _25328) = (term5 _25328)) : (term5 _25328) = (@EX _25328).
Proof. exact (SYM (@lem1101533 _25328 h1)). Qed.
Lemma lem1101535 {_25328 : Type'} (h1 : (term5 _25328) = (@EX _25328)) : (term5 _25328) = (@EX _25328).
Proof. exact (h1). Qed.
Lemma lem1101536 {_25328 : Type'} (h1 : (term5 _25328) = (@EX _25328)) : (@EX _25328) = (term5 _25328).
Proof. exact (SYM (@lem1101535 _25328 h1)). Qed.
Lemma lem1101537 {_25328 : Type'} : ((@EX _25328) = (term5 _25328)) = ((term5 _25328) = (@EX _25328)).
Proof. exact (prop_ext (fun h1 : (@EX _25328) = (term5 _25328) => @lem1101534 _25328 h1) (fun h1 : (term5 _25328) = (@EX _25328) => @lem1101536 _25328 h1)). Qed.
Lemma lem1101540 {_25328 : Type'} : (term5 _25328) = (@EX _25328).
Proof. exact (EQ_MP (@lem1101537 _25328) (@lem1101527 _25328)). Qed.
Lemma lem1101541 {_25328 : Type'} : (term5 _25328) = (@EX _25328).
Proof. exact (@lem1101540 _25328). Qed.
Lemma lem1101542 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1101543 {_25328 : Type'} (P : _25328 -> Prop) : (term6 _25328 P) = (@EX _25328 P).
Proof. exact (MK_COMB (@lem1101541 _25328) (@lem1101542 _25328 P)). Qed.
Lemma lem1101544 {_25328 : Type'} : (@nil _25328) = (@nil _25328).
Proof. exact (eq_refl (@nil _25328)). Qed.
Lemma lem1101545 {_25328 : Type'} (P : _25328 -> Prop) : (term7 _25328 P) = (@EX _25328 P (@nil _25328)).
Proof. exact (MK_COMB (@lem1101543 _25328 P) (@lem1101544 _25328)). Qed.
Lemma lem1101546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1101547 {_25328 : Type'} (P : _25328 -> Prop) : (term8 _25328 P) = (term9 _25328 P).
Proof. exact (MK_COMB (@lem1101546) (@lem1101545 _25328 P)). Qed.
Lemma lem1101548 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1101549 {_25328 : Type'} (P : _25328 -> Prop) : ((term7 _25328 P) = False) = ((@EX _25328 P (@nil _25328)) = False).
Proof. exact (MK_COMB (@lem1101547 _25328 P) (@lem1101548)). Qed.
Lemma lem1101550 {_25328 : Type'} : (term10 _25328) = (term11 _25328).
Proof. exact (fun_ext (fun P : _25328 -> Prop => @lem1101549 _25328 P)). Qed.
Lemma lem1101551 {_25328 : Type'} : (@all (_25328 -> Prop)) = (@all (_25328 -> Prop)).
Proof. exact (eq_refl (@all (_25328 -> Prop))). Qed.
Lemma lem1101552 {_25328 : Type'} : (term12 _25328) = (term13 _25328).
Proof. exact (MK_COMB (@lem1101551 _25328) (@lem1101550 _25328)). Qed.
Lemma lem1101553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1101554 {_25328 : Type'} : (term14 _25328) = (term15 _25328).
Proof. exact (MK_COMB (@lem1101553) (@lem1101552 _25328)). Qed.
Lemma lem1101556 {_25328 : Type'} : (term5 _25328) = (@EX _25328).
Proof. exact (EQ_MP (@lem1101537 _25328) (@lem1101527 _25328)). Qed.
Lemma lem1101557 {_25328 : Type'} : (term5 _25328) = (@EX _25328).
Proof. exact (@lem1101556 _25328). Qed.
Lemma lem1101558 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1101559 {_25328 : Type'} (P : _25328 -> Prop) : (term6 _25328 P) = (@EX _25328 P).
Proof. exact (MK_COMB (@lem1101557 _25328) (@lem1101558 _25328 P)). Qed.
Lemma lem1101560 {_25328 : Type'} (h : _25328) (t : list _25328) : (@cons _25328 h t) = (@cons _25328 h t).
Proof. exact (eq_refl (@cons _25328 h t)). Qed.
Lemma lem1101561 {_25328 : Type'} (P : _25328 -> Prop) (h : _25328) (t : list _25328) : (term16 _25328 P h t) = (term17 _25328 P h t).
Proof. exact (MK_COMB (@lem1101559 _25328 P) (@lem1101560 _25328 h t)). Qed.
Lemma lem1101562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1101563 {_25328 : Type'} (P : _25328 -> Prop) (h : _25328) (t : list _25328) : (term18 _25328 P h t) = (term19 _25328 P h t).
Proof. exact (MK_COMB (@lem1101562) (@lem1101561 _25328 P h t)). Qed.
Lemma lem1101565 {_25328 : Type'} : (term5 _25328) = (@EX _25328).
Proof. exact (EQ_MP (@lem1101537 _25328) (@lem1101527 _25328)). Qed.
Lemma lem1101566 {_25328 : Type'} : (term5 _25328) = (@EX _25328).
Proof. exact (@lem1101565 _25328). Qed.
Lemma lem1101567 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1101568 {_25328 : Type'} (P : _25328 -> Prop) : (term6 _25328 P) = (@EX _25328 P).
Proof. exact (MK_COMB (@lem1101566 _25328) (@lem1101567 _25328 P)). Qed.
Lemma lem1101569 {_25328 : Type'} (t : list _25328) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1101570 {_25328 : Type'} (P : _25328 -> Prop) (t : list _25328) : (term20 _25328 P t) = (@EX _25328 P t).
Proof. exact (MK_COMB (@lem1101568 _25328 P) (@lem1101569 _25328 t)). Qed.
Lemma lem1101571 {_25328 : Type'} (P : _25328 -> Prop) (h : _25328) : (term21 _25328 P h) = (term21 _25328 P h).
Proof. exact (eq_refl (term21 _25328 P h)). Qed.
Lemma lem1101572 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term22 _25328 h P t) = (term23 _25328 h P t).
Proof. exact (MK_COMB (@lem1101571 _25328 P h) (@lem1101570 _25328 P t)). Qed.
Lemma lem1101573 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : ((term16 _25328 P h t) = (term22 _25328 h P t)) = ((term17 _25328 P h t) = (term23 _25328 h P t)).
Proof. exact (MK_COMB (@lem1101563 _25328 P h t) (@lem1101572 _25328 h P t)). Qed.
Lemma lem1101574 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) : (term24 _25328 h P) = (term25 _25328 h P).
Proof. exact (fun_ext (fun t : list _25328 => @lem1101573 _25328 h P t)). Qed.
Lemma lem1101575 {_25328 : Type'} : (@all (list _25328)) = (@all (list _25328)).
Proof. exact (eq_refl (@all (list _25328))). Qed.
Lemma lem1101576 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) : (term26 _25328 h P) = (term27 _25328 h P).
Proof. exact (MK_COMB (@lem1101575 _25328) (@lem1101574 _25328 h P)). Qed.
Lemma lem1101577 {_25328 : Type'} (h : _25328) : (term28 _25328 h) = (term29 _25328 h).
Proof. exact (fun_ext (fun P : _25328 -> Prop => @lem1101576 _25328 h P)). Qed.
Lemma lem1101578 {_25328 : Type'} : (@all (_25328 -> Prop)) = (@all (_25328 -> Prop)).
Proof. exact (eq_refl (@all (_25328 -> Prop))). Qed.
Lemma lem1101579 {_25328 : Type'} (h : _25328) : (term30 _25328 h) = (term31 _25328 h).
Proof. exact (MK_COMB (@lem1101578 _25328) (@lem1101577 _25328 h)). Qed.
Lemma lem1101580 {_25328 : Type'} : (term32 _25328) = (term33 _25328).
Proof. exact (fun_ext (fun h : _25328 => @lem1101579 _25328 h)). Qed.
Lemma lem1101581 {_25328 : Type'} : (@all _25328) = (@all _25328).
Proof. exact (eq_refl (@all _25328)). Qed.
Lemma lem1101582 {_25328 : Type'} : (term34 _25328) = (term35 _25328).
Proof. exact (MK_COMB (@lem1101581 _25328) (@lem1101580 _25328)). Qed.
Lemma lem1101583 {_25328 : Type'} : (term4 _25328) = (term36 _25328).
Proof. exact (MK_COMB (@lem1101554 _25328) (@lem1101582 _25328)). Qed.
Lemma lem1101584 {_25328 : Type'} : term36 _25328.
Proof. exact (EQ_MP (@lem1101583 _25328) (@lem1101532 _25328)). Qed.
