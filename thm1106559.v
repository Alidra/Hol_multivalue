Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106559_term_abbrevs.
Require Import thm1106112_spec.
Require Import thm1106492_spec.
Lemma lem1106493 {_25594 : Type'} : (term0 _25594) = (term1 _25594).
Proof. exact (eq_refl (term0 _25594)). Qed.
Lemma lem1106494 {_25594 : Type'} : term1 _25594.
Proof. exact (EQ_MP (@lem1106493 _25594) (@lem1106112 _25594)). Qed.
Lemma lem1106495 {_25594 : Type'} : term2 _25594.
Proof. exact (@lem1106494 _25594 term3). Qed.
Lemma lem1106496 {_25594 : Type'} : (term2 _25594) = (term4 _25594).
Proof. exact (eq_refl (term2 _25594)). Qed.
Lemma lem1106497 {_25594 : Type'} : term4 _25594.
Proof. exact (EQ_MP (@lem1106496 _25594) (@lem1106495 _25594)). Qed.
Lemma lem1106498 {_25594 : Type'} (h1 : (@FILTER _25594) = (term5 _25594)) : (@FILTER _25594) = (term5 _25594).
Proof. exact (h1). Qed.
Lemma lem1106499 {_25594 : Type'} (h1 : (@FILTER _25594) = (term5 _25594)) : (term5 _25594) = (@FILTER _25594).
Proof. exact (SYM (@lem1106498 _25594 h1)). Qed.
Lemma lem1106500 {_25594 : Type'} (h1 : (term5 _25594) = (@FILTER _25594)) : (term5 _25594) = (@FILTER _25594).
Proof. exact (h1). Qed.
Lemma lem1106501 {_25594 : Type'} (h1 : (term5 _25594) = (@FILTER _25594)) : (@FILTER _25594) = (term5 _25594).
Proof. exact (SYM (@lem1106500 _25594 h1)). Qed.
Lemma lem1106502 {_25594 : Type'} : ((@FILTER _25594) = (term5 _25594)) = ((term5 _25594) = (@FILTER _25594)).
Proof. exact (prop_ext (fun h1 : (@FILTER _25594) = (term5 _25594) => @lem1106499 _25594 h1) (fun h1 : (term5 _25594) = (@FILTER _25594) => @lem1106501 _25594 h1)). Qed.
Lemma lem1106505 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (EQ_MP (@lem1106502 _25594) (@lem1106492 _25594)). Qed.
Lemma lem1106506 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (@lem1106505 _25594). Qed.
Lemma lem1106507 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1106508 {_25594 : Type'} (P : _25594 -> Prop) : (term6 _25594 P) = (@FILTER _25594 P).
Proof. exact (MK_COMB (@lem1106506 _25594) (@lem1106507 _25594 P)). Qed.
Lemma lem1106509 {_25594 : Type'} : (@nil _25594) = (@nil _25594).
Proof. exact (eq_refl (@nil _25594)). Qed.
Lemma lem1106510 {_25594 : Type'} (P : _25594 -> Prop) : (term7 _25594 P) = (@FILTER _25594 P (@nil _25594)).
Proof. exact (MK_COMB (@lem1106508 _25594 P) (@lem1106509 _25594)). Qed.
Lemma lem1106511 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1106512 {_25594 : Type'} (P : _25594 -> Prop) : (term8 _25594 P) = (term9 _25594 P).
Proof. exact (MK_COMB (@lem1106511 _25594) (@lem1106510 _25594 P)). Qed.
Lemma lem1106513 {_25594 : Type'} : (@nil _25594) = (@nil _25594).
Proof. exact (eq_refl (@nil _25594)). Qed.
Lemma lem1106514 {_25594 : Type'} (P : _25594 -> Prop) : ((term7 _25594 P) = (@nil _25594)) = ((@FILTER _25594 P (@nil _25594)) = (@nil _25594)).
Proof. exact (MK_COMB (@lem1106512 _25594 P) (@lem1106513 _25594)). Qed.
Lemma lem1106515 {_25594 : Type'} : (term10 _25594) = (term11 _25594).
Proof. exact (fun_ext (fun P : _25594 -> Prop => @lem1106514 _25594 P)). Qed.
Lemma lem1106516 {_25594 : Type'} : (@all (_25594 -> Prop)) = (@all (_25594 -> Prop)).
Proof. exact (eq_refl (@all (_25594 -> Prop))). Qed.
Lemma lem1106517 {_25594 : Type'} : (term12 _25594) = (term13 _25594).
Proof. exact (MK_COMB (@lem1106516 _25594) (@lem1106515 _25594)). Qed.
Lemma lem1106518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1106519 {_25594 : Type'} : (term14 _25594) = (term15 _25594).
Proof. exact (MK_COMB (@lem1106518) (@lem1106517 _25594)). Qed.
Lemma lem1106521 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (EQ_MP (@lem1106502 _25594) (@lem1106492 _25594)). Qed.
Lemma lem1106522 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (@lem1106521 _25594). Qed.
Lemma lem1106523 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1106524 {_25594 : Type'} (P : _25594 -> Prop) : (term6 _25594 P) = (@FILTER _25594 P).
Proof. exact (MK_COMB (@lem1106522 _25594) (@lem1106523 _25594 P)). Qed.
Lemma lem1106525 {_25594 : Type'} (h : _25594) (t : list _25594) : (@cons _25594 h t) = (@cons _25594 h t).
Proof. exact (eq_refl (@cons _25594 h t)). Qed.
Lemma lem1106526 {_25594 : Type'} (P : _25594 -> Prop) (h : _25594) (t : list _25594) : (term16 _25594 P h t) = (term17 _25594 P h t).
Proof. exact (MK_COMB (@lem1106524 _25594 P) (@lem1106525 _25594 h t)). Qed.
Lemma lem1106527 {_25594 : Type'} : (@eq (list _25594)) = (@eq (list _25594)).
Proof. exact (eq_refl (@eq (list _25594))). Qed.
Lemma lem1106528 {_25594 : Type'} (P : _25594 -> Prop) (h : _25594) (t : list _25594) : (term18 _25594 P h t) = (term19 _25594 P h t).
Proof. exact (MK_COMB (@lem1106527 _25594) (@lem1106526 _25594 P h t)). Qed.
Lemma lem1106530 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (EQ_MP (@lem1106502 _25594) (@lem1106492 _25594)). Qed.
Lemma lem1106531 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (@lem1106530 _25594). Qed.
Lemma lem1106532 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1106533 {_25594 : Type'} (P : _25594 -> Prop) : (term6 _25594 P) = (@FILTER _25594 P).
Proof. exact (MK_COMB (@lem1106531 _25594) (@lem1106532 _25594 P)). Qed.
Lemma lem1106534 {_25594 : Type'} (t : list _25594) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1106535 {_25594 : Type'} (P : _25594 -> Prop) (t : list _25594) : (term20 _25594 P t) = (@FILTER _25594 P t).
Proof. exact (MK_COMB (@lem1106533 _25594 P) (@lem1106534 _25594 t)). Qed.
Lemma lem1106536 {_25594 : Type'} (h : _25594) : (@cons _25594 h) = (@cons _25594 h).
Proof. exact (eq_refl (@cons _25594 h)). Qed.
Lemma lem1106537 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term21 _25594 h P t) = (term22 _25594 h P t).
Proof. exact (MK_COMB (@lem1106536 _25594 h) (@lem1106535 _25594 P t)). Qed.
Lemma lem1106538 {_25594 : Type'} (P : _25594 -> Prop) (h : _25594) : (term23 _25594 P h) = (term23 _25594 P h).
Proof. exact (eq_refl (term23 _25594 P h)). Qed.
Lemma lem1106539 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term24 _25594 h P t) = (term25 _25594 h P t).
Proof. exact (MK_COMB (@lem1106538 _25594 P h) (@lem1106537 _25594 h P t)). Qed.
Lemma lem1106541 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (EQ_MP (@lem1106502 _25594) (@lem1106492 _25594)). Qed.
Lemma lem1106542 {_25594 : Type'} : (term5 _25594) = (@FILTER _25594).
Proof. exact (@lem1106541 _25594). Qed.
Lemma lem1106543 {_25594 : Type'} (P : _25594 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1106544 {_25594 : Type'} (P : _25594 -> Prop) : (term6 _25594 P) = (@FILTER _25594 P).
Proof. exact (MK_COMB (@lem1106542 _25594) (@lem1106543 _25594 P)). Qed.
Lemma lem1106545 {_25594 : Type'} (t : list _25594) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1106546 {_25594 : Type'} (P : _25594 -> Prop) (t : list _25594) : (term20 _25594 P t) = (@FILTER _25594 P t).
Proof. exact (MK_COMB (@lem1106544 _25594 P) (@lem1106545 _25594 t)). Qed.
Lemma lem1106547 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term26 _25594 h P t) = (term27 _25594 h P t).
Proof. exact (MK_COMB (@lem1106539 _25594 h P t) (@lem1106546 _25594 P t)). Qed.
Lemma lem1106548 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : ((term16 _25594 P h t) = (term26 _25594 h P t)) = ((term17 _25594 P h t) = (term27 _25594 h P t)).
Proof. exact (MK_COMB (@lem1106528 _25594 P h t) (@lem1106547 _25594 h P t)). Qed.
Lemma lem1106549 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) : (term28 _25594 h P) = (term29 _25594 h P).
Proof. exact (fun_ext (fun t : list _25594 => @lem1106548 _25594 h P t)). Qed.
Lemma lem1106550 {_25594 : Type'} : (@all (list _25594)) = (@all (list _25594)).
Proof. exact (eq_refl (@all (list _25594))). Qed.
Lemma lem1106551 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) : (term30 _25594 h P) = (term31 _25594 h P).
Proof. exact (MK_COMB (@lem1106550 _25594) (@lem1106549 _25594 h P)). Qed.
Lemma lem1106552 {_25594 : Type'} (h : _25594) : (term32 _25594 h) = (term33 _25594 h).
Proof. exact (fun_ext (fun P : _25594 -> Prop => @lem1106551 _25594 h P)). Qed.
Lemma lem1106553 {_25594 : Type'} : (@all (_25594 -> Prop)) = (@all (_25594 -> Prop)).
Proof. exact (eq_refl (@all (_25594 -> Prop))). Qed.
Lemma lem1106554 {_25594 : Type'} (h : _25594) : (term34 _25594 h) = (term35 _25594 h).
Proof. exact (MK_COMB (@lem1106553 _25594) (@lem1106552 _25594 h)). Qed.
Lemma lem1106555 {_25594 : Type'} : (term36 _25594) = (term37 _25594).
Proof. exact (fun_ext (fun h : _25594 => @lem1106554 _25594 h)). Qed.
Lemma lem1106556 {_25594 : Type'} : (@all _25594) = (@all _25594).
Proof. exact (eq_refl (@all _25594)). Qed.
Lemma lem1106557 {_25594 : Type'} : (term38 _25594) = (term39 _25594).
Proof. exact (MK_COMB (@lem1106556 _25594) (@lem1106555 _25594)). Qed.
Lemma lem1106558 {_25594 : Type'} : (term4 _25594) = (term40 _25594).
Proof. exact (MK_COMB (@lem1106519 _25594) (@lem1106557 _25594)). Qed.
Lemma lem1106559 {_25594 : Type'} : term40 _25594.
Proof. exact (EQ_MP (@lem1106558 _25594) (@lem1106497 _25594)). Qed.
