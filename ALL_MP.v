Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_MP_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1842_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem1129591 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1129592 {_26690 : Type'} (P : type1143 _26690) : term0 _26690 P.
Proof. exact (@lem1129591 _26690 P). Qed.
Lemma lem1129593 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : term1 _26690 P Q.
Proof. exact (@lem1129592 _26690 (term2 _26690 P Q)). Qed.
Lemma lem1129594 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term3 _26690 P Q) = (term4 _26690 P Q).
Proof. exact (eq_refl (term3 _26690 P Q)). Qed.
Lemma lem1129595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129596 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term5 _26690 P Q) = (term6 _26690 P Q).
Proof. exact (MK_COMB (@lem1129595) (@lem1129594 _26690 P Q)). Qed.
Lemma lem1129597 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term7 _26690 P Q t) = (term8 _26690 P Q t).
Proof. exact (eq_refl (term7 _26690 P Q t)). Qed.
Lemma lem1129598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129599 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term9 _26690 P Q t) = (term10 _26690 P Q t).
Proof. exact (MK_COMB (@lem1129598) (@lem1129597 _26690 P Q t)). Qed.
Lemma lem1129600 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) (t : list _26690) : (term11 _26690 P Q h t) = (term12 _26690 P Q h t).
Proof. exact (eq_refl (term11 _26690 P Q h t)). Qed.
Lemma lem1129601 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) (t : list _26690) : (term13 _26690 P Q h t) = (term14 _26690 P Q h t).
Proof. exact (MK_COMB (@lem1129599 _26690 P Q t) (@lem1129600 _26690 P Q h t)). Qed.
Lemma lem1129602 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term15 _26690 P Q h) = (term16 _26690 P Q h).
Proof. exact (fun_ext (fun t : list _26690 => @lem1129601 _26690 P Q h t)). Qed.
Lemma lem1129603 {_26690 : Type'} : (@all (list _26690)) = (@all (list _26690)).
Proof. exact (eq_refl (@all (list _26690))). Qed.
Lemma lem1129604 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term17 _26690 P Q h) = (term18 _26690 P Q h).
Proof. exact (MK_COMB (@lem1129603 _26690) (@lem1129602 _26690 P Q h)). Qed.
Lemma lem1129605 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term19 _26690 P Q) = (term20 _26690 P Q).
Proof. exact (fun_ext (fun h : _26690 => @lem1129604 _26690 P Q h)). Qed.
Lemma lem1129606 {_26690 : Type'} : (@all _26690) = (@all _26690).
Proof. exact (eq_refl (@all _26690)). Qed.
Lemma lem1129607 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term21 _26690 P Q) = (term22 _26690 P Q).
Proof. exact (MK_COMB (@lem1129606 _26690) (@lem1129605 _26690 P Q)). Qed.
Lemma lem1129608 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term23 _26690 P Q) = (term24 _26690 P Q).
Proof. exact (MK_COMB (@lem1129596 _26690 P Q) (@lem1129607 _26690 P Q)). Qed.
Lemma lem1129609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129610 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term25 _26690 P Q) = (term26 _26690 P Q).
Proof. exact (MK_COMB (@lem1129609) (@lem1129608 _26690 P Q)). Qed.
Lemma lem1129611 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (l : list _26690) : (term7 _26690 P Q l) = (term8 _26690 P Q l).
Proof. exact (eq_refl (term7 _26690 P Q l)). Qed.
Lemma lem1129612 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term27 _26690 P Q) = (term2 _26690 P Q).
Proof. exact (fun_ext (fun l : list _26690 => @lem1129611 _26690 P Q l)). Qed.
Lemma lem1129613 {_26690 : Type'} : (@all (list _26690)) = (@all (list _26690)).
Proof. exact (eq_refl (@all (list _26690))). Qed.
Lemma lem1129614 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term28 _26690 P Q) = (term29 _26690 P Q).
Proof. exact (MK_COMB (@lem1129613 _26690) (@lem1129612 _26690 P Q)). Qed.
Lemma lem1129615 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term1 _26690 P Q) = (term30 _26690 P Q).
Proof. exact (MK_COMB (@lem1129610 _26690 P Q) (@lem1129614 _26690 P Q)). Qed.
Lemma lem1129616 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : term30 _26690 P Q.
Proof. exact (EQ_MP (@lem1129615 _26690 P Q) (@lem1129593 _26690 P Q)). Qed.
Lemma lem1129617 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term8 _26690 P Q t) : term8 _26690 P Q t.
Proof. exact (h1). Qed.
Lemma lem1129623 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1129624 {_26690 : Type'} (P : _26690 -> Prop) : (@List.Forall _26690 P (@nil _26690)) = True.
Proof. exact (@lem1129623 _26690 P). Qed.
Lemma lem1129625 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term31 _26690 P Q) = True.
Proof. exact (@lem1129624 _26690 (term32 _26690 P Q)). Qed.
Lemma lem1129626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129627 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term33 _26690 P Q) = (and True).
Proof. exact (MK_COMB (@lem1129626) (@lem1129625 _26690 P Q)). Qed.
Lemma lem1129629 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1129630 {_26690 : Type'} (P : _26690 -> Prop) : (@List.Forall _26690 P (@nil _26690)) = True.
Proof. exact (@lem1129629 _26690 P). Qed.
Lemma lem1129631 {_26690 : Type'} (Q : _26690 -> Prop) (P : _26690 -> Prop) : (term34 _26690 Q P) = (True /\ True).
Proof. exact (MK_COMB (@lem1129627 _26690 P Q) (@lem1129630 _26690 P)). Qed.
Lemma lem1129633 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1129634 : (True /\ True) = True.
Proof. exact (@lem1129633 True). Qed.
Lemma lem1129635 {_26690 : Type'} (Q : _26690 -> Prop) (P : _26690 -> Prop) : (term34 _26690 Q P) = True.
Proof. exact (TRANS (@lem1129631 _26690 Q P) (@lem1129634)). Qed.
Lemma lem1129636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129637 {_26690 : Type'} (Q : _26690 -> Prop) (P : _26690 -> Prop) : (term35 _26690 Q P) = (imp True).
Proof. exact (MK_COMB (@lem1129636) (@lem1129635 _26690 Q P)). Qed.
Lemma lem1129639 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1129640 {_26690 : Type'} (P : _26690 -> Prop) : (@List.Forall _26690 P (@nil _26690)) = True.
Proof. exact (@lem1129639 _26690 P). Qed.
Lemma lem1129641 {_26690 : Type'} (Q : _26690 -> Prop) : (@List.Forall _26690 Q (@nil _26690)) = True.
Proof. exact (@lem1129640 _26690 Q). Qed.
Lemma lem1129642 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term4 _26690 P Q) = (True -> True).
Proof. exact (MK_COMB (@lem1129637 _26690 Q P) (@lem1129641 _26690 Q)). Qed.
Lemma lem1129644 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1129645 : (True -> True) = True.
Proof. exact (@lem1129644 True). Qed.
Lemma lem1129646 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term4 _26690 P Q) = True.
Proof. exact (TRANS (@lem1129642 _26690 P Q) (@lem1129645)). Qed.
Lemma lem1129647 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : True = (term4 _26690 P Q).
Proof. exact (SYM (@lem1129646 _26690 P Q)). Qed.
Lemma lem1129648 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : term4 _26690 P Q.
Proof. exact (EQ_MP (@lem1129647 _26690 P Q) (@lem0)). Qed.
Lemma lem1129654 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term36 _25307 P h t) = (term37 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1129655 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term36 _26690 P h t) = (term37 _26690 h P t).
Proof. exact (@lem1129654 _26690 h P t). Qed.
Lemma lem1129656 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term38 _26690 P Q h t) = (term39 _26690 h P Q t).
Proof. exact (@lem1129655 _26690 h (term32 _26690 P Q) t). Qed.
Lemma lem1129660 {A B : Type'} (f : A -> B) (y : A) : (term40 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1129661 {_26690 : Type'} (f : _26690 -> Prop) (y : _26690) : (term41 _26690 f y) = (f y).
Proof. exact (@lem1129660 _26690 Prop f y). Qed.
Lemma lem1129662 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term42 _26690 P Q h) = (term43 _26690 P Q h).
Proof. exact (@lem1129661 _26690 (term32 _26690 P Q) h). Qed.
Lemma lem1129663 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (x : _26690) : (term43 _26690 P Q x) = (term44 _26690 P Q x).
Proof. exact (eq_refl (term43 _26690 P Q x)). Qed.
Lemma lem1129664 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term45 _26690 P Q) = (term32 _26690 P Q).
Proof. exact (fun_ext (fun x : _26690 => @lem1129663 _26690 P Q x)). Qed.
Lemma lem1129665 {_26690 : Type'} (h : _26690) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1129666 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term42 _26690 P Q h) = (term43 _26690 P Q h).
Proof. exact (MK_COMB (@lem1129664 _26690 P Q) (@lem1129665 _26690 h)). Qed.
Lemma lem1129667 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129668 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term46 _26690 P Q h) = (term47 _26690 P Q h).
Proof. exact (MK_COMB (@lem1129667) (@lem1129666 _26690 P Q h)). Qed.
Lemma lem1129669 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term43 _26690 P Q h) = (term44 _26690 P Q h).
Proof. exact (eq_refl (term43 _26690 P Q h)). Qed.
Lemma lem1129670 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : ((term42 _26690 P Q h) = (term43 _26690 P Q h)) = ((term43 _26690 P Q h) = (term44 _26690 P Q h)).
Proof. exact (MK_COMB (@lem1129668 _26690 P Q h) (@lem1129669 _26690 P Q h)). Qed.
Lemma lem1129671 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term43 _26690 P Q h) = (term44 _26690 P Q h).
Proof. exact (EQ_MP (@lem1129670 _26690 P Q h) (@lem1129662 _26690 P Q h)). Qed.
Lemma lem1129674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129675 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term48 _26690 P Q h) = (term49 _26690 P Q h).
Proof. exact (MK_COMB (@lem1129674) (@lem1129671 _26690 P Q h)). Qed.
Lemma lem1129678 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term50 _26690 P Q t) = (term50 _26690 P Q t).
Proof. exact (eq_refl (term50 _26690 P Q t)). Qed.
Lemma lem1129679 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term39 _26690 h P Q t) = (term51 _26690 h P Q t).
Proof. exact (MK_COMB (@lem1129675 _26690 P Q h) (@lem1129678 _26690 P Q t)). Qed.
Lemma lem1129682 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term38 _26690 P Q h t) = (term51 _26690 h P Q t).
Proof. exact (TRANS (@lem1129656 _26690 h P Q t) (@lem1129679 _26690 h P Q t)). Qed.
Lemma lem1129683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129684 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term52 _26690 P Q h t) = (term53 _26690 h P Q t).
Proof. exact (MK_COMB (@lem1129683) (@lem1129682 _26690 h P Q t)). Qed.
Lemma lem1129686 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term36 _25307 P h t) = (term37 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1129687 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term36 _26690 P h t) = (term37 _26690 h P t).
Proof. exact (@lem1129686 _26690 h P t). Qed.
Lemma lem1129690 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term54 _26690 Q P h t) = (term55 _26690 Q h P t).
Proof. exact (MK_COMB (@lem1129684 _26690 h P Q t) (@lem1129687 _26690 h P t)). Qed.
Lemma lem1129693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129694 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term56 _26690 Q P h t) = (term57 _26690 Q h P t).
Proof. exact (MK_COMB (@lem1129693) (@lem1129690 _26690 Q h P t)). Qed.
Lemma lem1129696 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term36 _25307 P h t) = (term37 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1129697 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term36 _26690 P h t) = (term37 _26690 h P t).
Proof. exact (@lem1129696 _26690 h P t). Qed.
Lemma lem1129698 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term36 _26690 Q h t) = (term37 _26690 h Q t).
Proof. exact (@lem1129697 _26690 h Q t). Qed.
Lemma lem1129701 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term12 _26690 P Q h t) = (term58 _26690 P h Q t).
Proof. exact (MK_COMB (@lem1129694 _26690 Q h P t) (@lem1129698 _26690 h Q t)). Qed.
Lemma lem1129704 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) (t : list _26690) : (term58 _26690 P h Q t) = (term12 _26690 P Q h t).
Proof. exact (SYM (@lem1129701 _26690 P h Q t)). Qed.
Lemma lem1129706 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1129707 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term58 _26690 P h Q t) = (term60 _26690 P h Q t).
Proof. exact (@lem1129706 (term58 _26690 P h Q t)). Qed.
Lemma lem1129708 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term60 _26690 P h Q t) = (term58 _26690 P h Q t).
Proof. exact (SYM (@lem1129707 _26690 P h Q t)). Qed.
Lemma lem1129709 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term61 _26690 P h Q t) : term61 _26690 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1129712 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term62 _26690 P h Q t) : term62 _26690 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1129713 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term63 _26690 P h Q t.
Proof. exact (fun h0 : term62 _26690 P h Q t => @lem1129712 _26690 P h Q t h0). Qed.
Lemma lem1129714 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term63 _26690 P h Q t) : term63 _26690 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1129715 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term62 _26690 P h Q t) : term62 _26690 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1129716 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term62 _26690 P h Q t) (h2 : term63 _26690 P h Q t) : term62 _26690 P h Q t.
Proof. exact (@lem1129714 _26690 P h Q t h2 (@lem1129715 _26690 P h Q t h1)). Qed.
Lemma lem1129717 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term62 _26690 P h Q t) : term64 _26690 P h Q t.
Proof. exact (fun h0 : term63 _26690 P h Q t => @lem1129716 _26690 P h Q t h1 h0). Qed.
Lemma lem1129718 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term63 _26690 P h Q t) : term63 _26690 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1129719 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term62 _26690 P h Q t) (h2 : term63 _26690 P h Q t) : term62 _26690 P h Q t.
Proof. exact (@lem1129717 _26690 P h Q t h1 (@lem1129718 _26690 P h Q t h2)). Qed.
Lemma lem1129720 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term63 _26690 P h Q t) : term63 _26690 P h Q t.
Proof. exact (fun h0 : term62 _26690 P h Q t => @lem1129719 _26690 P h Q t h0 h1). Qed.
Lemma lem1129721 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term65 _26690 P h Q t.
Proof. exact (fun h0 : term63 _26690 P h Q t => @lem1129720 _26690 P h Q t h0). Qed.
Lemma lem1129724 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term63 _26690 P h Q t.
Proof. exact (@lem1129721 _26690 P h Q t (@lem1129713 _26690 P h Q t)). Qed.
Lemma lem1129725 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term63 _26690 P h Q t.
Proof. exact (@lem1129724 _26690 P h Q t). Qed.
Lemma lem1129751 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1129752 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term60 _26690 P h Q t) = (term66 _26690 P h Q t).
Proof. exact (@lem1129751 (term61 _26690 P h Q t)). Qed.
Lemma lem1129754 (t : Prop) : (term67 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1129755 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term66 _26690 P h Q t) = (term58 _26690 P h Q t).
Proof. exact (@lem1129754 (term58 _26690 P h Q t)). Qed.
Lemma lem1129758 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term60 _26690 P h Q t) = (term58 _26690 P h Q t).
Proof. exact (TRANS (@lem1129752 _26690 P h Q t) (@lem1129755 _26690 P h Q t)). Qed.
Lemma lem1129771 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term10 _26690 P Q t) = (term10 _26690 P Q t).
Proof. exact (eq_refl (term10 _26690 P Q t)). Qed.
Lemma lem1129772 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term62 _26690 P h Q t) = (term68 _26690 P h Q t).
Proof. exact (MK_COMB (@lem1129771 _26690 P Q t) (@lem1129758 _26690 P h Q t)). Qed.
Lemma lem1129775 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term69 _26690 h Q t) = (term70 _26690 h Q t).
Proof. exact (fun_ext (fun P : _26690 -> Prop => @lem1129772 _26690 P h Q t)). Qed.
Lemma lem1129776 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129777 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term71 _26690 h Q t) = (term72 _26690 h Q t).
Proof. exact (MK_COMB (@lem1129776 _26690) (@lem1129775 _26690 h Q t)). Qed.
Lemma lem1129782 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term73 _26690 Q t) = (term74 _26690 Q t).
Proof. exact (fun_ext (fun h : _26690 => @lem1129777 _26690 h Q t)). Qed.
Lemma lem1129783 {_26690 : Type'} : (@all _26690) = (@all _26690).
Proof. exact (eq_refl (@all _26690)). Qed.
Lemma lem1129784 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term75 _26690 Q t) = (term76 _26690 Q t).
Proof. exact (MK_COMB (@lem1129783 _26690) (@lem1129782 _26690 Q t)). Qed.
Lemma lem1129789 {_26690 : Type'} (t : list _26690) : (term77 _26690 t) = (term78 _26690 t).
Proof. exact (fun_ext (fun Q : _26690 -> Prop => @lem1129784 _26690 Q t)). Qed.
Lemma lem1129790 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129791 {_26690 : Type'} (t : list _26690) : (term79 _26690 t) = (term80 _26690 t).
Proof. exact (MK_COMB (@lem1129790 _26690) (@lem1129789 _26690 t)). Qed.
Lemma lem1129796 {_26690 : Type'} : (term81 _26690) = (term82 _26690).
Proof. exact (fun_ext (fun t : list _26690 => @lem1129791 _26690 t)). Qed.
Lemma lem1129797 {_26690 : Type'} : (@all (list _26690)) = (@all (list _26690)).
Proof. exact (eq_refl (@all (list _26690))). Qed.
Lemma lem1129804 {_26690 : Type'} : (term83 _26690) = (term84 _26690).
Proof. exact (MK_COMB (@lem1129797 _26690) (@lem1129796 _26690)). Qed.
Lemma lem1129805 {_26690 : Type'} (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : _18588 = (term85 _26690).
Proof. exact (h1). Qed.
Lemma lem1129806 {_26690 : Type'} (P : _26690 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1129807 {_26690 : Type'} (P : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (_18588 P) = (term86 _26690 P).
Proof. exact (MK_COMB (@lem1129805 _26690 _18588 h1) (@lem1129806 _26690 P)). Qed.
Lemma lem1129808 {_26690 : Type'} (P : _26690 -> Prop) : (term86 _26690 P) = (term87 _26690 P).
Proof. exact (eq_refl (term86 _26690 P)). Qed.
Lemma lem1129809 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term88 _26690 _18588 P) = (term88 _26690 _18588 P).
Proof. exact (eq_refl (term88 _26690 _18588 P)). Qed.
Lemma lem1129810 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : ((_18588 P) = (term86 _26690 P)) = ((_18588 P) = (term87 _26690 P)).
Proof. exact (MK_COMB (@lem1129809 _26690 _18588 P) (@lem1129808 _26690 P)). Qed.
Lemma lem1129811 {_26690 : Type'} (P : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (_18588 P) = (term87 _26690 P).
Proof. exact (EQ_MP (@lem1129810 _26690 _18588 P) (@lem1129807 _26690 P _18588 h1)). Qed.
Lemma lem1129812 {_26690 : Type'} (Q : _26690 -> Prop) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem1129813 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (_18588 P Q) = (term89 _26690 P Q).
Proof. exact (MK_COMB (@lem1129811 _26690 P _18588 h1) (@lem1129812 _26690 Q)). Qed.
Lemma lem1129814 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term89 _26690 P Q) = (term32 _26690 P Q).
Proof. exact (eq_refl (term89 _26690 P Q)). Qed.
Lemma lem1129815 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term90 _26690 _18588 P Q) = (term90 _26690 _18588 P Q).
Proof. exact (eq_refl (term90 _26690 _18588 P Q)). Qed.
Lemma lem1129816 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : ((_18588 P Q) = (term89 _26690 P Q)) = ((_18588 P Q) = (term32 _26690 P Q)).
Proof. exact (MK_COMB (@lem1129815 _26690 _18588 P Q) (@lem1129814 _26690 P Q)). Qed.
Lemma lem1129817 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (_18588 P Q) = (term32 _26690 P Q).
Proof. exact (EQ_MP (@lem1129816 _26690 _18588 P Q) (@lem1129813 _26690 P Q _18588 h1)). Qed.
Lemma lem1129829 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term37 _26690 h Q t) = (term37 _26690 h Q t).
Proof. exact (eq_refl (term37 _26690 h Q t)). Qed.
Lemma lem1129840 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term37 _26690 h P t) = (term37 _26690 h P t).
Proof. exact (eq_refl (term37 _26690 h P t)). Qed.
Lemma lem1129841 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1129843 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term32 _26690 P Q) = (_18588 P Q).
Proof. exact (SYM (@lem1129817 _26690 P Q _18588 h1)). Qed.
Lemma lem1129844 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term32 _26690 P Q) = (_18588 P Q).
Proof. exact (@lem1129843 _26690 P Q _18588 h1). Qed.
Lemma lem1129845 {_26690 : Type'} : (@List.Forall _26690) = (@List.Forall _26690).
Proof. exact (eq_refl (@List.Forall _26690)). Qed.
Lemma lem1129846 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term91 _26690 P Q) = (term92 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1129845 _26690) (@lem1129844 _26690 P Q _18588 h1)). Qed.
Lemma lem1129847 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term50 _26690 P Q t) = (term93 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1129846 _26690 P Q _18588 h1) (@lem1129841 _26690 t)). Qed.
Lemma lem1129858 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term49 _26690 P Q h) = (term49 _26690 P Q h).
Proof. exact (eq_refl (term49 _26690 P Q h)). Qed.
Lemma lem1129859 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term51 _26690 h P Q t) = (term94 _26690 h _18588 P Q t).
Proof. exact (MK_COMB (@lem1129858 _26690 P Q h) (@lem1129847 _26690 P Q t _18588 h1)). Qed.
Lemma lem1129860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129861 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term53 _26690 h P Q t) = (term95 _26690 h _18588 P Q t).
Proof. exact (MK_COMB (@lem1129860) (@lem1129859 _26690 h P Q t _18588 h1)). Qed.
Lemma lem1129862 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term55 _26690 Q h P t) = (term96 _26690 _18588 Q h P t).
Proof. exact (MK_COMB (@lem1129861 _26690 h P Q t _18588 h1) (@lem1129840 _26690 h P t)). Qed.
Lemma lem1129863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129864 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term57 _26690 Q h P t) = (term97 _26690 _18588 Q h P t).
Proof. exact (MK_COMB (@lem1129863) (@lem1129862 _26690 Q h P t _18588 h1)). Qed.
Lemma lem1129865 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term58 _26690 P h Q t) = (term98 _26690 _18588 P h Q t).
Proof. exact (MK_COMB (@lem1129864 _26690 Q h P t _18588 h1) (@lem1129829 _26690 h Q t)). Qed.
Lemma lem1129870 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 Q t) = (@List.Forall _26690 Q t).
Proof. exact (eq_refl (@List.Forall _26690 Q t)). Qed.
Lemma lem1129875 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 P t) = (@List.Forall _26690 P t).
Proof. exact (eq_refl (@List.Forall _26690 P t)). Qed.
Lemma lem1129876 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1129878 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term32 _26690 P Q) = (_18588 P Q).
Proof. exact (SYM (@lem1129817 _26690 P Q _18588 h1)). Qed.
Lemma lem1129879 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term32 _26690 P Q) = (_18588 P Q).
Proof. exact (@lem1129878 _26690 P Q _18588 h1). Qed.
Lemma lem1129880 {_26690 : Type'} : (@List.Forall _26690) = (@List.Forall _26690).
Proof. exact (eq_refl (@List.Forall _26690)). Qed.
Lemma lem1129881 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term91 _26690 P Q) = (term92 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1129880 _26690) (@lem1129879 _26690 P Q _18588 h1)). Qed.
Lemma lem1129882 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term50 _26690 P Q t) = (term93 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1129881 _26690 P Q _18588 h1) (@lem1129876 _26690 t)). Qed.
Lemma lem1129883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129884 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term99 _26690 P Q t) = (term100 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1129883) (@lem1129882 _26690 P Q t _18588 h1)). Qed.
Lemma lem1129885 {_26690 : Type'} (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term101 _26690 Q P t) = (term102 _26690 _18588 Q P t).
Proof. exact (MK_COMB (@lem1129884 _26690 P Q t _18588 h1) (@lem1129875 _26690 P t)). Qed.
Lemma lem1129886 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129887 {_26690 : Type'} (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term103 _26690 Q P t) = (term104 _26690 _18588 Q P t).
Proof. exact (MK_COMB (@lem1129886) (@lem1129885 _26690 Q P t _18588 h1)). Qed.
Lemma lem1129888 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term8 _26690 P Q t) = (term105 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1129887 _26690 Q P t _18588 h1) (@lem1129870 _26690 Q t)). Qed.
Lemma lem1129889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129890 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term10 _26690 P Q t) = (term106 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1129889) (@lem1129888 _26690 P Q t _18588 h1)). Qed.
Lemma lem1129891 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term68 _26690 P h Q t) = (term107 _26690 _18588 P h Q t).
Proof. exact (MK_COMB (@lem1129890 _26690 P Q t _18588 h1) (@lem1129865 _26690 P h Q t _18588 h1)). Qed.
Lemma lem1129892 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term70 _26690 h Q t) = (term108 _26690 _18588 h Q t).
Proof. exact (fun_ext (fun P : _26690 -> Prop => @lem1129891 _26690 P h Q t _18588 h1)). Qed.
Lemma lem1129893 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129894 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term72 _26690 h Q t) = (term109 _26690 _18588 h Q t).
Proof. exact (MK_COMB (@lem1129893 _26690) (@lem1129892 _26690 h Q t _18588 h1)). Qed.
Lemma lem1129895 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term74 _26690 Q t) = (term110 _26690 _18588 Q t).
Proof. exact (fun_ext (fun h : _26690 => @lem1129894 _26690 h Q t _18588 h1)). Qed.
Lemma lem1129896 {_26690 : Type'} : (@all _26690) = (@all _26690).
Proof. exact (eq_refl (@all _26690)). Qed.
Lemma lem1129897 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term76 _26690 Q t) = (term111 _26690 _18588 Q t).
Proof. exact (MK_COMB (@lem1129896 _26690) (@lem1129895 _26690 Q t _18588 h1)). Qed.
Lemma lem1129898 {_26690 : Type'} (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term78 _26690 t) = (term112 _26690 _18588 t).
Proof. exact (fun_ext (fun Q : _26690 -> Prop => @lem1129897 _26690 Q t _18588 h1)). Qed.
Lemma lem1129899 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129900 {_26690 : Type'} (t : list _26690) (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term80 _26690 t) = (term113 _26690 _18588 t).
Proof. exact (MK_COMB (@lem1129899 _26690) (@lem1129898 _26690 t _18588 h1)). Qed.
Lemma lem1129901 {_26690 : Type'} (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term82 _26690) = (term114 _26690 _18588).
Proof. exact (fun_ext (fun t : list _26690 => @lem1129900 _26690 t _18588 h1)). Qed.
Lemma lem1129902 {_26690 : Type'} : (@all (list _26690)) = (@all (list _26690)).
Proof. exact (eq_refl (@all (list _26690))). Qed.
Lemma lem1129903 {_26690 : Type'} (_18588 : type636 _26690) (h1 : _18588 = (term85 _26690)) : (term84 _26690) = (term115 _26690 _18588).
Proof. exact (MK_COMB (@lem1129902 _26690) (@lem1129901 _26690 _18588 h1)). Qed.
Lemma lem1129904 {_26690 : Type'} (_18588 : type636 _26690) : term116 _26690 _18588.
Proof. exact (fun h0 : _18588 = (term85 _26690) => @lem1129903 _26690 _18588 h0). Qed.
Lemma lem1129905 {_26690 : Type'} : term117 _26690.
Proof. exact (fun _18588 : type636 _26690 => @lem1129904 _26690 _18588). Qed.
Lemma lem1129907 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term118 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1129908 {_26690 : Type'} (P : Prop) (c : type636 _26690) (Q : type138 _26690) : term119 _26690 P c Q.
Proof. exact (@lem1129907 (type636 _26690) P c Q). Qed.
Lemma lem1129909 {_26690 : Type'} : term120 _26690.
Proof. exact (@lem1129908 _26690 (term84 _26690) (term85 _26690) (term121 _26690)). Qed.
Lemma lem1129910 {_26690 : Type'} (_18588 : type636 _26690) : (term122 _26690 _18588) = (term115 _26690 _18588).
Proof. exact (eq_refl (term122 _26690 _18588)). Qed.
Lemma lem1129911 {_26690 : Type'} : (term123 _26690) = (term123 _26690).
Proof. exact (eq_refl (term123 _26690)). Qed.
Lemma lem1129912 {_26690 : Type'} (_18588 : type636 _26690) : ((term84 _26690) = (term122 _26690 _18588)) = ((term84 _26690) = (term115 _26690 _18588)).
Proof. exact (MK_COMB (@lem1129911 _26690) (@lem1129910 _26690 _18588)). Qed.
Lemma lem1129913 {_26690 : Type'} (_18588 : type636 _26690) : (term124 _26690 _18588) = (term124 _26690 _18588).
Proof. exact (eq_refl (term124 _26690 _18588)). Qed.
Lemma lem1129914 {_26690 : Type'} (_18588 : type636 _26690) : (term125 _26690 _18588) = (term116 _26690 _18588).
Proof. exact (MK_COMB (@lem1129913 _26690 _18588) (@lem1129912 _26690 _18588)). Qed.
Lemma lem1129915 {_26690 : Type'} : (term126 _26690) = (term127 _26690).
Proof. exact (fun_ext (fun _18588 : type636 _26690 => @lem1129914 _26690 _18588)). Qed.
Lemma lem1129916 {_26690 : Type'} : (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)) = (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)).
Proof. exact (eq_refl (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop))). Qed.
Lemma lem1129917 {_26690 : Type'} : (term128 _26690) = (term117 _26690).
Proof. exact (MK_COMB (@lem1129916 _26690) (@lem1129915 _26690)). Qed.
Lemma lem1129918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129919 {_26690 : Type'} : (term129 _26690) = (term130 _26690).
Proof. exact (MK_COMB (@lem1129918) (@lem1129917 _26690)). Qed.
Lemma lem1129920 {_26690 : Type'} (_18588 : type636 _26690) : (term122 _26690 _18588) = (term115 _26690 _18588).
Proof. exact (eq_refl (term122 _26690 _18588)). Qed.
Lemma lem1129921 {_26690 : Type'} (_18588 : type636 _26690) : (term124 _26690 _18588) = (term124 _26690 _18588).
Proof. exact (eq_refl (term124 _26690 _18588)). Qed.
Lemma lem1129922 {_26690 : Type'} (_18588 : type636 _26690) : (term131 _26690 _18588) = (term132 _26690 _18588).
Proof. exact (MK_COMB (@lem1129921 _26690 _18588) (@lem1129920 _26690 _18588)). Qed.
Lemma lem1129923 {_26690 : Type'} : (term133 _26690) = (term134 _26690).
Proof. exact (fun_ext (fun _18588 : type636 _26690 => @lem1129922 _26690 _18588)). Qed.
Lemma lem1129924 {_26690 : Type'} : (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)) = (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)).
Proof. exact (eq_refl (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop))). Qed.
Lemma lem1129925 {_26690 : Type'} : (term135 _26690) = (term136 _26690).
Proof. exact (MK_COMB (@lem1129924 _26690) (@lem1129923 _26690)). Qed.
Lemma lem1129926 {_26690 : Type'} : (term123 _26690) = (term123 _26690).
Proof. exact (eq_refl (term123 _26690)). Qed.
Lemma lem1129927 {_26690 : Type'} : ((term84 _26690) = (term135 _26690)) = ((term84 _26690) = (term136 _26690)).
Proof. exact (MK_COMB (@lem1129926 _26690) (@lem1129925 _26690)). Qed.
Lemma lem1129928 {_26690 : Type'} : (term120 _26690) = (term137 _26690).
Proof. exact (MK_COMB (@lem1129919 _26690) (@lem1129927 _26690)). Qed.
Lemma lem1129929 {_26690 : Type'} : term137 _26690.
Proof. exact (EQ_MP (@lem1129928 _26690) (@lem1129909 _26690)). Qed.
Lemma lem1129930 {_26690 : Type'} : (term84 _26690) = (term136 _26690).
Proof. exact (@lem1129929 _26690 (@lem1129905 _26690)). Qed.
Lemma lem1129932 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term138 _3571 _3575 t)) = (term139 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1129933 {_26690 : Type'} (s : type636 _26690) (t : type636 _26690) : (s = (term140 _26690 t)) = (term141 _26690 s t).
Proof. exact (@lem1129932 (type672 _26690) (_26690 -> Prop) s t). Qed.
Lemma lem1129934 {_26690 : Type'} (_18588 : type636 _26690) : (_18588 = (term142 _26690)) = (term143 _26690 _18588).
Proof. exact (@lem1129933 _26690 _18588 (term85 _26690)). Qed.
Lemma lem1129935 {_26690 : Type'} (P : _26690 -> Prop) : (term86 _26690 P) = (term87 _26690 P).
Proof. exact (eq_refl (term86 _26690 P)). Qed.
Lemma lem1129936 {_26690 : Type'} : (term142 _26690) = (term85 _26690).
Proof. exact (fun_ext (fun P : _26690 -> Prop => @lem1129935 _26690 P)). Qed.
Lemma lem1129937 {_26690 : Type'} (_18588 : type636 _26690) : (@eq ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588) = (@eq ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588).
Proof. exact (eq_refl (@eq ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588)). Qed.
Lemma lem1129938 {_26690 : Type'} (_18588 : type636 _26690) : (_18588 = (term142 _26690)) = (_18588 = (term85 _26690)).
Proof. exact (MK_COMB (@lem1129937 _26690 _18588) (@lem1129936 _26690)). Qed.
Lemma lem1129939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129940 {_26690 : Type'} (_18588 : type636 _26690) : (term144 _26690 _18588) = (term145 _26690 _18588).
Proof. exact (MK_COMB (@lem1129939) (@lem1129938 _26690 _18588)). Qed.
Lemma lem1129941 {_26690 : Type'} (P : _26690 -> Prop) : (term86 _26690 P) = (term87 _26690 P).
Proof. exact (eq_refl (term86 _26690 P)). Qed.
Lemma lem1129942 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term88 _26690 _18588 P) = (term88 _26690 _18588 P).
Proof. exact (eq_refl (term88 _26690 _18588 P)). Qed.
Lemma lem1129943 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : ((_18588 P) = (term86 _26690 P)) = ((_18588 P) = (term87 _26690 P)).
Proof. exact (MK_COMB (@lem1129942 _26690 _18588 P) (@lem1129941 _26690 P)). Qed.
Lemma lem1129944 {_26690 : Type'} (_18588 : type636 _26690) : (term146 _26690 _18588) = (term147 _26690 _18588).
Proof. exact (fun_ext (fun P : _26690 -> Prop => @lem1129943 _26690 _18588 P)). Qed.
Lemma lem1129945 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129946 {_26690 : Type'} (_18588 : type636 _26690) : (term143 _26690 _18588) = (term148 _26690 _18588).
Proof. exact (MK_COMB (@lem1129945 _26690) (@lem1129944 _26690 _18588)). Qed.
Lemma lem1129947 {_26690 : Type'} (_18588 : type636 _26690) : ((_18588 = (term142 _26690)) = (term143 _26690 _18588)) = ((_18588 = (term85 _26690)) = (term148 _26690 _18588)).
Proof. exact (MK_COMB (@lem1129940 _26690 _18588) (@lem1129946 _26690 _18588)). Qed.
Lemma lem1129948 {_26690 : Type'} (_18588 : type636 _26690) : (_18588 = (term85 _26690)) = (term148 _26690 _18588).
Proof. exact (EQ_MP (@lem1129947 _26690 _18588) (@lem1129934 _26690 _18588)). Qed.
Lemma lem1129950 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term138 _3571 _3575 t)) = (term139 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1129951 {_26690 : Type'} (s : type672 _26690) (t : type672 _26690) : (s = (term149 _26690 t)) = (term150 _26690 s t).
Proof. exact (@lem1129950 (_26690 -> Prop) (_26690 -> Prop) s t). Qed.
Lemma lem1129952 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : ((_18588 P) = (term151 _26690 P)) = (term152 _26690 _18588 P).
Proof. exact (@lem1129951 _26690 (_18588 P) (term87 _26690 P)). Qed.
Lemma lem1129953 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term89 _26690 P Q) = (term32 _26690 P Q).
Proof. exact (eq_refl (term89 _26690 P Q)). Qed.
Lemma lem1129954 {_26690 : Type'} (P : _26690 -> Prop) : (term151 _26690 P) = (term87 _26690 P).
Proof. exact (fun_ext (fun Q : _26690 -> Prop => @lem1129953 _26690 P Q)). Qed.
Lemma lem1129955 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term88 _26690 _18588 P) = (term88 _26690 _18588 P).
Proof. exact (eq_refl (term88 _26690 _18588 P)). Qed.
Lemma lem1129956 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : ((_18588 P) = (term151 _26690 P)) = ((_18588 P) = (term87 _26690 P)).
Proof. exact (MK_COMB (@lem1129955 _26690 _18588 P) (@lem1129954 _26690 P)). Qed.
Lemma lem1129957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129958 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term153 _26690 _18588 P) = (term154 _26690 _18588 P).
Proof. exact (MK_COMB (@lem1129957) (@lem1129956 _26690 _18588 P)). Qed.
Lemma lem1129959 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term89 _26690 P Q) = (term32 _26690 P Q).
Proof. exact (eq_refl (term89 _26690 P Q)). Qed.
Lemma lem1129960 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term90 _26690 _18588 P Q) = (term90 _26690 _18588 P Q).
Proof. exact (eq_refl (term90 _26690 _18588 P Q)). Qed.
Lemma lem1129961 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : ((_18588 P Q) = (term89 _26690 P Q)) = ((_18588 P Q) = (term32 _26690 P Q)).
Proof. exact (MK_COMB (@lem1129960 _26690 _18588 P Q) (@lem1129959 _26690 P Q)). Qed.
Lemma lem1129962 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term155 _26690 _18588 P) = (term156 _26690 _18588 P).
Proof. exact (fun_ext (fun Q : _26690 -> Prop => @lem1129961 _26690 _18588 P Q)). Qed.
Lemma lem1129963 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129964 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term152 _26690 _18588 P) = (term157 _26690 _18588 P).
Proof. exact (MK_COMB (@lem1129963 _26690) (@lem1129962 _26690 _18588 P)). Qed.
Lemma lem1129965 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (((_18588 P) = (term151 _26690 P)) = (term152 _26690 _18588 P)) = (((_18588 P) = (term87 _26690 P)) = (term157 _26690 _18588 P)).
Proof. exact (MK_COMB (@lem1129958 _26690 _18588 P) (@lem1129964 _26690 _18588 P)). Qed.
Lemma lem1129966 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : ((_18588 P) = (term87 _26690 P)) = (term157 _26690 _18588 P).
Proof. exact (EQ_MP (@lem1129965 _26690 _18588 P) (@lem1129952 _26690 _18588 P)). Qed.
Lemma lem1129968 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term138 _3571 _3575 t)) = (term139 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1129969 {_26690 : Type'} (s : _26690 -> Prop) (t : _26690 -> Prop) : (s = (term158 _26690 t)) = (term159 _26690 s t).
Proof. exact (@lem1129968 Prop _26690 s t). Qed.
Lemma lem1129970 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : ((_18588 P Q) = (term45 _26690 P Q)) = (term160 _26690 _18588 P Q).
Proof. exact (@lem1129969 _26690 (_18588 P Q) (term32 _26690 P Q)). Qed.
Lemma lem1129971 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (x : _26690) : (term43 _26690 P Q x) = (term44 _26690 P Q x).
Proof. exact (eq_refl (term43 _26690 P Q x)). Qed.
Lemma lem1129972 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term45 _26690 P Q) = (term32 _26690 P Q).
Proof. exact (fun_ext (fun x : _26690 => @lem1129971 _26690 P Q x)). Qed.
Lemma lem1129973 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term90 _26690 _18588 P Q) = (term90 _26690 _18588 P Q).
Proof. exact (eq_refl (term90 _26690 _18588 P Q)). Qed.
Lemma lem1129974 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : ((_18588 P Q) = (term45 _26690 P Q)) = ((_18588 P Q) = (term32 _26690 P Q)).
Proof. exact (MK_COMB (@lem1129973 _26690 _18588 P Q) (@lem1129972 _26690 P Q)). Qed.
Lemma lem1129975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129976 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term161 _26690 _18588 P Q) = (term162 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1129975) (@lem1129974 _26690 _18588 P Q)). Qed.
Lemma lem1129977 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (x : _26690) : (term43 _26690 P Q x) = (term44 _26690 P Q x).
Proof. exact (eq_refl (term43 _26690 P Q x)). Qed.
Lemma lem1129978 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (x : _26690) : (term163 _26690 _18588 P Q x) = (term163 _26690 _18588 P Q x).
Proof. exact (eq_refl (term163 _26690 _18588 P Q x)). Qed.
Lemma lem1129979 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (x : _26690) : ((_18588 P Q x) = (term43 _26690 P Q x)) = ((_18588 P Q x) = (term44 _26690 P Q x)).
Proof. exact (MK_COMB (@lem1129978 _26690 _18588 P Q x) (@lem1129977 _26690 P Q x)). Qed.
Lemma lem1129980 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term164 _26690 _18588 P Q) = (term165 _26690 _18588 P Q).
Proof. exact (fun_ext (fun x : _26690 => @lem1129979 _26690 _18588 P Q x)). Qed.
Lemma lem1129981 {_26690 : Type'} : (@all _26690) = (@all _26690).
Proof. exact (eq_refl (@all _26690)). Qed.
Lemma lem1129982 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term160 _26690 _18588 P Q) = (term166 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1129981 _26690) (@lem1129980 _26690 _18588 P Q)). Qed.
Lemma lem1129983 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (((_18588 P Q) = (term45 _26690 P Q)) = (term160 _26690 _18588 P Q)) = (((_18588 P Q) = (term32 _26690 P Q)) = (term166 _26690 _18588 P Q)).
Proof. exact (MK_COMB (@lem1129976 _26690 _18588 P Q) (@lem1129982 _26690 _18588 P Q)). Qed.
Lemma lem1129984 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : ((_18588 P Q) = (term32 _26690 P Q)) = (term166 _26690 _18588 P Q).
Proof. exact (EQ_MP (@lem1129983 _26690 _18588 P Q) (@lem1129970 _26690 _18588 P Q)). Qed.
Lemma lem1129985 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (x : _26690) : ((_18588 P Q x) = (term44 _26690 P Q x)) = ((_18588 P Q x) = (term44 _26690 P Q x)).
Proof. exact (eq_refl ((_18588 P Q x) = (term44 _26690 P Q x))). Qed.
Lemma lem1129986 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term165 _26690 _18588 P Q) = (term165 _26690 _18588 P Q).
Proof. exact (fun_ext (fun x : _26690 => @lem1129985 _26690 _18588 P Q x)). Qed.
Lemma lem1129987 {_26690 : Type'} : (@all _26690) = (@all _26690).
Proof. exact (eq_refl (@all _26690)). Qed.
Lemma lem1129988 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term166 _26690 _18588 P Q) = (term166 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1129987 _26690) (@lem1129986 _26690 _18588 P Q)). Qed.
Lemma lem1129989 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : ((_18588 P Q) = (term32 _26690 P Q)) = (term166 _26690 _18588 P Q).
Proof. exact (TRANS (@lem1129984 _26690 _18588 P Q) (@lem1129988 _26690 _18588 P Q)). Qed.
Lemma lem1129990 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term156 _26690 _18588 P) = (term167 _26690 _18588 P).
Proof. exact (fun_ext (fun Q : _26690 -> Prop => @lem1129989 _26690 _18588 P Q)). Qed.
Lemma lem1129991 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129992 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term157 _26690 _18588 P) = (term168 _26690 _18588 P).
Proof. exact (MK_COMB (@lem1129991 _26690) (@lem1129990 _26690 _18588 P)). Qed.
Lemma lem1129993 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : ((_18588 P) = (term87 _26690 P)) = (term168 _26690 _18588 P).
Proof. exact (TRANS (@lem1129966 _26690 _18588 P) (@lem1129992 _26690 _18588 P)). Qed.
Lemma lem1129994 {_26690 : Type'} (_18588 : type636 _26690) : (term147 _26690 _18588) = (term169 _26690 _18588).
Proof. exact (fun_ext (fun P : _26690 -> Prop => @lem1129993 _26690 _18588 P)). Qed.
Lemma lem1129995 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1129996 {_26690 : Type'} (_18588 : type636 _26690) : (term148 _26690 _18588) = (term170 _26690 _18588).
Proof. exact (MK_COMB (@lem1129995 _26690) (@lem1129994 _26690 _18588)). Qed.
Lemma lem1129997 {_26690 : Type'} (_18588 : type636 _26690) : (_18588 = (term85 _26690)) = (term170 _26690 _18588).
Proof. exact (TRANS (@lem1129948 _26690 _18588) (@lem1129996 _26690 _18588)). Qed.
Lemma lem1129998 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129999 {_26690 : Type'} (_18588 : type636 _26690) : (term124 _26690 _18588) = (term171 _26690 _18588).
Proof. exact (MK_COMB (@lem1129998) (@lem1129997 _26690 _18588)). Qed.
Lemma lem1130000 {_26690 : Type'} (_18588 : type636 _26690) : (term115 _26690 _18588) = (term115 _26690 _18588).
Proof. exact (eq_refl (term115 _26690 _18588)). Qed.
Lemma lem1130001 {_26690 : Type'} (_18588 : type636 _26690) : (term132 _26690 _18588) = (term172 _26690 _18588).
Proof. exact (MK_COMB (@lem1129999 _26690 _18588) (@lem1130000 _26690 _18588)). Qed.
Lemma lem1130002 {_26690 : Type'} : (term134 _26690) = (term173 _26690).
Proof. exact (fun_ext (fun _18588 : type636 _26690 => @lem1130001 _26690 _18588)). Qed.
Lemma lem1130003 {_26690 : Type'} : (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)) = (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)).
Proof. exact (eq_refl (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop))). Qed.
Lemma lem1130004 {_26690 : Type'} : (term136 _26690) = (term174 _26690).
Proof. exact (MK_COMB (@lem1130003 _26690) (@lem1130002 _26690)). Qed.
Lemma lem1130005 {_26690 : Type'} : (term123 _26690) = (term123 _26690).
Proof. exact (eq_refl (term123 _26690)). Qed.
Lemma lem1130006 {_26690 : Type'} : ((term84 _26690) = (term136 _26690)) = ((term84 _26690) = (term174 _26690)).
Proof. exact (MK_COMB (@lem1130005 _26690) (@lem1130004 _26690)). Qed.
Lemma lem1130009 {_26690 : Type'} : (term84 _26690) = (term174 _26690).
Proof. exact (EQ_MP (@lem1130006 _26690) (@lem1129930 _26690)). Qed.
Lemma lem1130010 {_26690 : Type'} : (term83 _26690) = (term174 _26690).
Proof. exact (TRANS (@lem1129804 _26690) (@lem1130009 _26690)). Qed.
Lemma lem1130047 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term107 _26690 _18588 P h Q t) = (term107 _26690 _18588 P h Q t).
Proof. exact (eq_refl (term107 _26690 _18588 P h Q t)). Qed.
Lemma lem1130048 {_26690 : Type'} (_18588 : type636 _26690) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term108 _26690 _18588 h Q t) = (term108 _26690 _18588 h Q t).
Proof. exact (fun_ext (fun P : _26690 -> Prop => @lem1130047 _26690 _18588 P h Q t)). Qed.
Lemma lem1130049 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1130050 {_26690 : Type'} (_18588 : type636 _26690) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term109 _26690 _18588 h Q t) = (term109 _26690 _18588 h Q t).
Proof. exact (MK_COMB (@lem1130049 _26690) (@lem1130048 _26690 _18588 h Q t)). Qed.
Lemma lem1130051 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (t : list _26690) : (term110 _26690 _18588 Q t) = (term110 _26690 _18588 Q t).
Proof. exact (fun_ext (fun h : _26690 => @lem1130050 _26690 _18588 h Q t)). Qed.
Lemma lem1130052 {_26690 : Type'} : (@all _26690) = (@all _26690).
Proof. exact (eq_refl (@all _26690)). Qed.
Lemma lem1130053 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (t : list _26690) : (term111 _26690 _18588 Q t) = (term111 _26690 _18588 Q t).
Proof. exact (MK_COMB (@lem1130052 _26690) (@lem1130051 _26690 _18588 Q t)). Qed.
Lemma lem1130054 {_26690 : Type'} (_18588 : type636 _26690) (t : list _26690) : (term112 _26690 _18588 t) = (term112 _26690 _18588 t).
Proof. exact (fun_ext (fun Q : _26690 -> Prop => @lem1130053 _26690 _18588 Q t)). Qed.
Lemma lem1130055 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1130056 {_26690 : Type'} (_18588 : type636 _26690) (t : list _26690) : (term113 _26690 _18588 t) = (term113 _26690 _18588 t).
Proof. exact (MK_COMB (@lem1130055 _26690) (@lem1130054 _26690 _18588 t)). Qed.
Lemma lem1130057 {_26690 : Type'} (_18588 : type636 _26690) : (term114 _26690 _18588) = (term114 _26690 _18588).
Proof. exact (fun_ext (fun t : list _26690 => @lem1130056 _26690 _18588 t)). Qed.
Lemma lem1130058 {_26690 : Type'} : (@all (list _26690)) = (@all (list _26690)).
Proof. exact (eq_refl (@all (list _26690))). Qed.
Lemma lem1130059 {_26690 : Type'} (_18588 : type636 _26690) : (term115 _26690 _18588) = (term115 _26690 _18588).
Proof. exact (MK_COMB (@lem1130058 _26690) (@lem1130057 _26690 _18588)). Qed.
Lemma lem1130068 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (x : _26690) : ((_18588 P Q x) = (term44 _26690 P Q x)) = ((_18588 P Q x) = (term44 _26690 P Q x)).
Proof. exact (eq_refl ((_18588 P Q x) = (term44 _26690 P Q x))). Qed.
Lemma lem1130069 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term165 _26690 _18588 P Q) = (term165 _26690 _18588 P Q).
Proof. exact (fun_ext (fun x : _26690 => @lem1130068 _26690 _18588 P Q x)). Qed.
Lemma lem1130070 {_26690 : Type'} : (@all _26690) = (@all _26690).
Proof. exact (eq_refl (@all _26690)). Qed.
Lemma lem1130071 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term166 _26690 _18588 P Q) = (term166 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1130070 _26690) (@lem1130069 _26690 _18588 P Q)). Qed.
Lemma lem1130072 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term167 _26690 _18588 P) = (term167 _26690 _18588 P).
Proof. exact (fun_ext (fun Q : _26690 -> Prop => @lem1130071 _26690 _18588 P Q)). Qed.
Lemma lem1130073 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1130074 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (term168 _26690 _18588 P) = (term168 _26690 _18588 P).
Proof. exact (MK_COMB (@lem1130073 _26690) (@lem1130072 _26690 _18588 P)). Qed.
Lemma lem1130075 {_26690 : Type'} (_18588 : type636 _26690) : (term169 _26690 _18588) = (term169 _26690 _18588).
Proof. exact (fun_ext (fun P : _26690 -> Prop => @lem1130074 _26690 _18588 P)). Qed.
Lemma lem1130076 {_26690 : Type'} : (@all (_26690 -> Prop)) = (@all (_26690 -> Prop)).
Proof. exact (eq_refl (@all (_26690 -> Prop))). Qed.
Lemma lem1130077 {_26690 : Type'} (_18588 : type636 _26690) : (term170 _26690 _18588) = (term170 _26690 _18588).
Proof. exact (MK_COMB (@lem1130076 _26690) (@lem1130075 _26690 _18588)). Qed.
Lemma lem1130078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1130079 {_26690 : Type'} (_18588 : type636 _26690) : (term171 _26690 _18588) = (term171 _26690 _18588).
Proof. exact (MK_COMB (@lem1130078) (@lem1130077 _26690 _18588)). Qed.
Lemma lem1130080 {_26690 : Type'} (_18588 : type636 _26690) : (term172 _26690 _18588) = (term172 _26690 _18588).
Proof. exact (MK_COMB (@lem1130079 _26690 _18588) (@lem1130059 _26690 _18588)). Qed.
Lemma lem1130081 {_26690 : Type'} : (term173 _26690) = (term173 _26690).
Proof. exact (fun_ext (fun _18588 : type636 _26690 => @lem1130080 _26690 _18588)). Qed.
Lemma lem1130082 {_26690 : Type'} : (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)) = (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop)).
Proof. exact (eq_refl (@all ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop))). Qed.
Lemma lem1130083 {_26690 : Type'} : (term174 _26690) = (term174 _26690).
Proof. exact (MK_COMB (@lem1130082 _26690) (@lem1130081 _26690)). Qed.
Lemma lem1130156 {_26690 : Type'} : (term83 _26690) = (term174 _26690).
Proof. exact (TRANS (@lem1130010 _26690) (@lem1130083 _26690)). Qed.
Lemma lem1130157 {_26690 : Type'} : (term174 _26690) = (term83 _26690).
Proof. exact (SYM (@lem1130156 _26690)). Qed.
Lemma lem1130159 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term105 _26690 _18588 P Q t) : term105 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1130160 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term96 _26690 _18588 Q h P t.
Proof. exact (h1). Qed.
Lemma lem1130162 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1130163 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term37 _26690 h Q t) = (term175 _26690 h Q t).
Proof. exact (@lem1130162 (term37 _26690 h Q t)). Qed.
Lemma lem1130164 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term175 _26690 h Q t) = (term37 _26690 h Q t).
Proof. exact (SYM (@lem1130163 _26690 h Q t)). Qed.
Lemma lem1130165 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term176 _26690 h Q t) : term176 _26690 h Q t.
Proof. exact (h1). Qed.
Lemma lem1130621 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) : (term177 _26690 _18588 Q P t) = (term178 _26690 _18588 Q P t).
Proof. exact (@lem17045 (term93 _26690 _18588 P Q t) (@List.Forall _26690 P t)). Qed.
Lemma lem1130622 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 Q t) = (@List.Forall _26690 Q t).
Proof. exact (eq_refl (@List.Forall _26690 Q t)). Qed.
Lemma lem1130623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1130624 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) : (term179 _26690 _18588 Q P t) = (term180 _26690 _18588 Q P t).
Proof. exact (MK_COMB (@lem1130623) (@lem1130621 _26690 _18588 Q P t)). Qed.
Lemma lem1130625 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term181 _26690 _18588 P Q t) = (term182 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130624 _26690 _18588 Q P t) (@lem1130622 _26690 Q t)). Qed.
Lemma lem1130626 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term105 _26690 _18588 P Q t) = (term181 _26690 _18588 P Q t).
Proof. exact (@lem17265 (term102 _26690 _18588 Q P t) (@List.Forall _26690 Q t)). Qed.
Lemma lem1130631 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term105 _26690 _18588 P Q t) = (term182 _26690 _18588 P Q t).
Proof. exact (TRANS (@lem1130626 _26690 _18588 P Q t) (@lem1130625 _26690 _18588 P Q t)). Qed.
Lemma lem1130632 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term105 _26690 _18588 P Q t) : term182 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1130631 _26690 _18588 P Q t) (@lem1130159 _26690 _18588 P Q t h1)). Qed.
Lemma lem1130639 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term44 _26690 P Q h) = (term183 _26690 P Q h).
Proof. exact (@lem17265 (P h) (Q h)). Qed.
Lemma lem1130640 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term93 _26690 _18588 P Q t) = (term93 _26690 _18588 P Q t).
Proof. exact (eq_refl (term93 _26690 _18588 P Q t)). Qed.
Lemma lem1130641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1130642 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term49 _26690 P Q h) = (term184 _26690 P Q h).
Proof. exact (MK_COMB (@lem1130641) (@lem1130639 _26690 P Q h)). Qed.
Lemma lem1130643 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term94 _26690 h _18588 P Q t) = (term185 _26690 h _18588 P Q t).
Proof. exact (MK_COMB (@lem1130642 _26690 P Q h) (@lem1130640 _26690 _18588 P Q t)). Qed.
Lemma lem1130648 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term37 _26690 h P t) = (term37 _26690 h P t).
Proof. exact (eq_refl (term37 _26690 h P t)). Qed.
Lemma lem1130649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1130650 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term95 _26690 h _18588 P Q t) = (term186 _26690 h _18588 P Q t).
Proof. exact (MK_COMB (@lem1130649) (@lem1130643 _26690 h _18588 P Q t)). Qed.
Lemma lem1130655 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term96 _26690 _18588 Q h P t) = (term187 _26690 _18588 Q h P t).
Proof. exact (MK_COMB (@lem1130650 _26690 h _18588 P Q t) (@lem1130648 _26690 h P t)). Qed.
Lemma lem1130656 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term187 _26690 _18588 Q h P t.
Proof. exact (EQ_MP (@lem1130655 _26690 _18588 Q h P t) (@lem1130160 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1130667 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term176 _26690 h Q t) = (term188 _26690 h Q t).
Proof. exact (@lem17045 (Q h) (@List.Forall _26690 Q t)). Qed.
Lemma lem1130668 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term176 _26690 h Q t) : term188 _26690 h Q t.
Proof. exact (EQ_MP (@lem1130667 _26690 h Q t) (@lem1130165 _26690 h Q t h1)). Qed.
Lemma lem1130799 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130800 {_26690 : Type'} (f : type663 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) f x).
Proof. exact (@lem1130799 (_26690 -> Prop) (type1143 _26690) f x). Qed.
Lemma lem1130801 {_26690 : Type'} (Q : _26690 -> Prop) : (@List.Forall _26690 Q) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q).
Proof. exact (@lem1130800 _26690 (@List.Forall _26690) Q). Qed.
Lemma lem1130802 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130803 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 Q t) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q t).
Proof. exact (MK_COMB (@lem1130801 _26690 Q) (@lem1130802 _26690 t)). Qed.
Lemma lem1130805 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130806 {_26690 : Type'} (f : type1143 _26690) (x : list _26690) : (f x) = (@I ((list _26690) -> Prop) f x).
Proof. exact (@lem1130805 (list _26690) Prop f x). Qed.
Lemma lem1130807 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q t) = (term189 _26690 Q t).
Proof. exact (@lem1130806 _26690 (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q) t). Qed.
Lemma lem1130809 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 Q t) = (term189 _26690 Q t).
Proof. exact (TRANS (@lem1130803 _26690 Q t) (@lem1130807 _26690 Q t)). Qed.
Lemma lem1130810 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1130817 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130818 {_26690 : Type'} (f : type663 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) f x).
Proof. exact (@lem1130817 (_26690 -> Prop) (type1143 _26690) f x). Qed.
Lemma lem1130819 {_26690 : Type'} (P : _26690 -> Prop) : (@List.Forall _26690 P) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P).
Proof. exact (@lem1130818 _26690 (@List.Forall _26690) P). Qed.
Lemma lem1130820 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130821 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 P t) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P t).
Proof. exact (MK_COMB (@lem1130819 _26690 P) (@lem1130820 _26690 t)). Qed.
Lemma lem1130823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130824 {_26690 : Type'} (f : type1143 _26690) (x : list _26690) : (f x) = (@I ((list _26690) -> Prop) f x).
Proof. exact (@lem1130823 (list _26690) Prop f x). Qed.
Lemma lem1130825 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P t) = (term189 _26690 P t).
Proof. exact (@lem1130824 _26690 (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P) t). Qed.
Lemma lem1130827 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 P t) = (term189 _26690 P t).
Proof. exact (TRANS (@lem1130821 _26690 P t) (@lem1130825 _26690 P t)). Qed.
Lemma lem1130828 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term190 _26690 P t) = (term191 _26690 P t).
Proof. exact (MK_COMB (@lem1130810) (@lem1130827 _26690 P t)). Qed.
Lemma lem1130829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1130830 {_26690 : Type'} : (@List.Forall _26690) = (@List.Forall _26690).
Proof. exact (eq_refl (@List.Forall _26690)). Qed.
Lemma lem1130837 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130838 {_26690 : Type'} (f : type636 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) f x).
Proof. exact (@lem1130837 (_26690 -> Prop) (type672 _26690) f x). Qed.
Lemma lem1130839 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (_18588 P) = (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P).
Proof. exact (@lem1130838 _26690 _18588 P). Qed.
Lemma lem1130840 {_26690 : Type'} (Q : _26690 -> Prop) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem1130841 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (_18588 P Q) = (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P Q).
Proof. exact (MK_COMB (@lem1130839 _26690 _18588 P) (@lem1130840 _26690 Q)). Qed.
Lemma lem1130843 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130844 {_26690 : Type'} (f : type672 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> _26690 -> Prop) f x).
Proof. exact (@lem1130843 (_26690 -> Prop) (_26690 -> Prop) f x). Qed.
Lemma lem1130845 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P Q) = (term192 _26690 _18588 P Q).
Proof. exact (@lem1130844 _26690 (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P) Q). Qed.
Lemma lem1130847 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (_18588 P Q) = (term192 _26690 _18588 P Q).
Proof. exact (TRANS (@lem1130841 _26690 _18588 P Q) (@lem1130845 _26690 _18588 P Q)). Qed.
Lemma lem1130848 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130849 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term92 _26690 _18588 P Q) = (term193 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1130830 _26690) (@lem1130847 _26690 _18588 P Q)). Qed.
Lemma lem1130850 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term93 _26690 _18588 P Q t) = (term194 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130849 _26690 _18588 P Q) (@lem1130848 _26690 t)). Qed.
Lemma lem1130852 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130853 {_26690 : Type'} (f : type663 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) f x).
Proof. exact (@lem1130852 (_26690 -> Prop) (type1143 _26690) f x). Qed.
Lemma lem1130854 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term193 _26690 _18588 P Q) = (term195 _26690 _18588 P Q).
Proof. exact (@lem1130853 _26690 (@List.Forall _26690) (term192 _26690 _18588 P Q)). Qed.
Lemma lem1130855 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130856 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term194 _26690 _18588 P Q t) = (term196 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130854 _26690 _18588 P Q) (@lem1130855 _26690 t)). Qed.
Lemma lem1130858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130859 {_26690 : Type'} (f : type1143 _26690) (x : list _26690) : (f x) = (@I ((list _26690) -> Prop) f x).
Proof. exact (@lem1130858 (list _26690) Prop f x). Qed.
Lemma lem1130860 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term196 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (@lem1130859 _26690 (term195 _26690 _18588 P Q) t). Qed.
Lemma lem1130861 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term194 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (TRANS (@lem1130856 _26690 _18588 P Q t) (@lem1130860 _26690 _18588 P Q t)). Qed.
Lemma lem1130862 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term93 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (TRANS (@lem1130850 _26690 _18588 P Q t) (@lem1130861 _26690 _18588 P Q t)). Qed.
Lemma lem1130863 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term198 _26690 _18588 P Q t) = (term199 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130829) (@lem1130862 _26690 _18588 P Q t)). Qed.
Lemma lem1130864 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1130865 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term200 _26690 _18588 P Q t) = (term201 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130864) (@lem1130863 _26690 _18588 P Q t)). Qed.
Lemma lem1130866 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) : (term178 _26690 _18588 Q P t) = (term202 _26690 _18588 Q P t).
Proof. exact (MK_COMB (@lem1130865 _26690 _18588 P Q t) (@lem1130828 _26690 P t)). Qed.
Lemma lem1130867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1130868 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) : (term180 _26690 _18588 Q P t) = (term203 _26690 _18588 Q P t).
Proof. exact (MK_COMB (@lem1130867) (@lem1130866 _26690 _18588 Q P t)). Qed.
Lemma lem1130869 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term182 _26690 _18588 P Q t) = (term204 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130868 _26690 _18588 Q P t) (@lem1130809 _26690 Q t)). Qed.
Lemma lem1130870 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term105 _26690 _18588 P Q t) : term204 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1130869 _26690 _18588 P Q t) (@lem1130632 _26690 _18588 P Q t h1)). Qed.
Lemma lem1130877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130878 {_26690 : Type'} (f : type663 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) f x).
Proof. exact (@lem1130877 (_26690 -> Prop) (type1143 _26690) f x). Qed.
Lemma lem1130879 {_26690 : Type'} (P : _26690 -> Prop) : (@List.Forall _26690 P) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P).
Proof. exact (@lem1130878 _26690 (@List.Forall _26690) P). Qed.
Lemma lem1130880 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130881 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 P t) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P t).
Proof. exact (MK_COMB (@lem1130879 _26690 P) (@lem1130880 _26690 t)). Qed.
Lemma lem1130883 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130884 {_26690 : Type'} (f : type1143 _26690) (x : list _26690) : (f x) = (@I ((list _26690) -> Prop) f x).
Proof. exact (@lem1130883 (list _26690) Prop f x). Qed.
Lemma lem1130885 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P t) = (term189 _26690 P t).
Proof. exact (@lem1130884 _26690 (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) P) t). Qed.
Lemma lem1130887 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 P t) = (term189 _26690 P t).
Proof. exact (TRANS (@lem1130881 _26690 P t) (@lem1130885 _26690 P t)). Qed.
Lemma lem1130892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130893 {_26690 : Type'} (f : _26690 -> Prop) (x : _26690) : (f x) = (@I (_26690 -> Prop) f x).
Proof. exact (@lem1130892 _26690 Prop f x). Qed.
Lemma lem1130895 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) : (P h) = (@I (_26690 -> Prop) P h).
Proof. exact (@lem1130893 _26690 P h). Qed.
Lemma lem1130896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1130897 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) : (term205 _26690 P h) = (term206 _26690 P h).
Proof. exact (MK_COMB (@lem1130896) (@lem1130895 _26690 P h)). Qed.
Lemma lem1130898 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term37 _26690 h P t) = (term207 _26690 h P t).
Proof. exact (MK_COMB (@lem1130897 _26690 P h) (@lem1130887 _26690 P t)). Qed.
Lemma lem1130899 {_26690 : Type'} : (@List.Forall _26690) = (@List.Forall _26690).
Proof. exact (eq_refl (@List.Forall _26690)). Qed.
Lemma lem1130906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130907 {_26690 : Type'} (f : type636 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) f x).
Proof. exact (@lem1130906 (_26690 -> Prop) (type672 _26690) f x). Qed.
Lemma lem1130908 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) : (_18588 P) = (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P).
Proof. exact (@lem1130907 _26690 _18588 P). Qed.
Lemma lem1130909 {_26690 : Type'} (Q : _26690 -> Prop) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem1130910 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (_18588 P Q) = (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P Q).
Proof. exact (MK_COMB (@lem1130908 _26690 _18588 P) (@lem1130909 _26690 Q)). Qed.
Lemma lem1130912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130913 {_26690 : Type'} (f : type672 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> _26690 -> Prop) f x).
Proof. exact (@lem1130912 (_26690 -> Prop) (_26690 -> Prop) f x). Qed.
Lemma lem1130914 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P Q) = (term192 _26690 _18588 P Q).
Proof. exact (@lem1130913 _26690 (@I ((_26690 -> Prop) -> (_26690 -> Prop) -> _26690 -> Prop) _18588 P) Q). Qed.
Lemma lem1130916 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (_18588 P Q) = (term192 _26690 _18588 P Q).
Proof. exact (TRANS (@lem1130910 _26690 _18588 P Q) (@lem1130914 _26690 _18588 P Q)). Qed.
Lemma lem1130917 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130918 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term92 _26690 _18588 P Q) = (term193 _26690 _18588 P Q).
Proof. exact (MK_COMB (@lem1130899 _26690) (@lem1130916 _26690 _18588 P Q)). Qed.
Lemma lem1130919 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term93 _26690 _18588 P Q t) = (term194 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130918 _26690 _18588 P Q) (@lem1130917 _26690 t)). Qed.
Lemma lem1130921 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130922 {_26690 : Type'} (f : type663 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) f x).
Proof. exact (@lem1130921 (_26690 -> Prop) (type1143 _26690) f x). Qed.
Lemma lem1130923 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) : (term193 _26690 _18588 P Q) = (term195 _26690 _18588 P Q).
Proof. exact (@lem1130922 _26690 (@List.Forall _26690) (term192 _26690 _18588 P Q)). Qed.
Lemma lem1130924 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130925 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term194 _26690 _18588 P Q t) = (term196 _26690 _18588 P Q t).
Proof. exact (MK_COMB (@lem1130923 _26690 _18588 P Q) (@lem1130924 _26690 t)). Qed.
Lemma lem1130927 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130928 {_26690 : Type'} (f : type1143 _26690) (x : list _26690) : (f x) = (@I ((list _26690) -> Prop) f x).
Proof. exact (@lem1130927 (list _26690) Prop f x). Qed.
Lemma lem1130929 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term196 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (@lem1130928 _26690 (term195 _26690 _18588 P Q) t). Qed.
Lemma lem1130930 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term194 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (TRANS (@lem1130925 _26690 _18588 P Q t) (@lem1130929 _26690 _18588 P Q t)). Qed.
Lemma lem1130931 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term93 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (TRANS (@lem1130919 _26690 _18588 P Q t) (@lem1130930 _26690 _18588 P Q t)). Qed.
Lemma lem1130936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130937 {_26690 : Type'} (f : _26690 -> Prop) (x : _26690) : (f x) = (@I (_26690 -> Prop) f x).
Proof. exact (@lem1130936 _26690 Prop f x). Qed.
Lemma lem1130939 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) : (Q h) = (@I (_26690 -> Prop) Q h).
Proof. exact (@lem1130937 _26690 Q h). Qed.
Lemma lem1130940 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1130945 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130946 {_26690 : Type'} (f : _26690 -> Prop) (x : _26690) : (f x) = (@I (_26690 -> Prop) f x).
Proof. exact (@lem1130945 _26690 Prop f x). Qed.
Lemma lem1130948 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) : (P h) = (@I (_26690 -> Prop) P h).
Proof. exact (@lem1130946 _26690 P h). Qed.
Lemma lem1130949 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) : (term208 _26690 P h) = (term209 _26690 P h).
Proof. exact (MK_COMB (@lem1130940) (@lem1130948 _26690 P h)). Qed.
Lemma lem1130950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1130951 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) : (term210 _26690 P h) = (term211 _26690 P h).
Proof. exact (MK_COMB (@lem1130950) (@lem1130949 _26690 P h)). Qed.
Lemma lem1130952 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term183 _26690 P Q h) = (term212 _26690 P Q h).
Proof. exact (MK_COMB (@lem1130951 _26690 P h) (@lem1130939 _26690 Q h)). Qed.
Lemma lem1130953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1130954 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : (term184 _26690 P Q h) = (term213 _26690 P Q h).
Proof. exact (MK_COMB (@lem1130953) (@lem1130952 _26690 P Q h)). Qed.
Lemma lem1130955 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term185 _26690 h _18588 P Q t) = (term214 _26690 h _18588 P Q t).
Proof. exact (MK_COMB (@lem1130954 _26690 P Q h) (@lem1130931 _26690 _18588 P Q t)). Qed.
Lemma lem1130956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1130957 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term186 _26690 h _18588 P Q t) = (term215 _26690 h _18588 P Q t).
Proof. exact (MK_COMB (@lem1130956) (@lem1130955 _26690 h _18588 P Q t)). Qed.
Lemma lem1130958 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) : (term187 _26690 _18588 Q h P t) = (term216 _26690 _18588 Q h P t).
Proof. exact (MK_COMB (@lem1130957 _26690 h _18588 P Q t) (@lem1130898 _26690 h P t)). Qed.
Lemma lem1130959 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term216 _26690 _18588 Q h P t.
Proof. exact (EQ_MP (@lem1130958 _26690 _18588 Q h P t) (@lem1130656 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1130960 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1130967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130968 {_26690 : Type'} (f : type663 _26690) (x : _26690 -> Prop) : (f x) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) f x).
Proof. exact (@lem1130967 (_26690 -> Prop) (type1143 _26690) f x). Qed.
Lemma lem1130969 {_26690 : Type'} (Q : _26690 -> Prop) : (@List.Forall _26690 Q) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q).
Proof. exact (@lem1130968 _26690 (@List.Forall _26690) Q). Qed.
Lemma lem1130970 {_26690 : Type'} (t : list _26690) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1130971 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 Q t) = (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q t).
Proof. exact (MK_COMB (@lem1130969 _26690 Q) (@lem1130970 _26690 t)). Qed.
Lemma lem1130973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130974 {_26690 : Type'} (f : type1143 _26690) (x : list _26690) : (f x) = (@I ((list _26690) -> Prop) f x).
Proof. exact (@lem1130973 (list _26690) Prop f x). Qed.
Lemma lem1130975 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q t) = (term189 _26690 Q t).
Proof. exact (@lem1130974 _26690 (@I ((_26690 -> Prop) -> (list _26690) -> Prop) (@List.Forall _26690) Q) t). Qed.
Lemma lem1130977 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (@List.Forall _26690 Q t) = (term189 _26690 Q t).
Proof. exact (TRANS (@lem1130971 _26690 Q t) (@lem1130975 _26690 Q t)). Qed.
Lemma lem1130978 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term190 _26690 Q t) = (term191 _26690 Q t).
Proof. exact (MK_COMB (@lem1130960) (@lem1130977 _26690 Q t)). Qed.
Lemma lem1130979 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1130984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1130985 {_26690 : Type'} (f : _26690 -> Prop) (x : _26690) : (f x) = (@I (_26690 -> Prop) f x).
Proof. exact (@lem1130984 _26690 Prop f x). Qed.
Lemma lem1130987 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) : (Q h) = (@I (_26690 -> Prop) Q h).
Proof. exact (@lem1130985 _26690 Q h). Qed.
Lemma lem1130988 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) : (term208 _26690 Q h) = (term209 _26690 Q h).
Proof. exact (MK_COMB (@lem1130979) (@lem1130987 _26690 Q h)). Qed.
Lemma lem1130989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1130990 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) : (term210 _26690 Q h) = (term211 _26690 Q h).
Proof. exact (MK_COMB (@lem1130989) (@lem1130988 _26690 Q h)). Qed.
Lemma lem1130991 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term188 _26690 h Q t) = (term217 _26690 h Q t).
Proof. exact (MK_COMB (@lem1130990 _26690 Q h) (@lem1130978 _26690 Q t)). Qed.
Lemma lem1130992 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (h1 : term176 _26690 h Q t) : term217 _26690 h Q t.
Proof. exact (EQ_MP (@lem1130991 _26690 h Q t) (@lem1130668 _26690 h Q t h1)). Qed.
Lemma lem1130993 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term207 _26690 h P t.
Proof. exact (proj2 (@lem1130959 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1130994 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term214 _26690 h _18588 P Q t.
Proof. exact (proj1 (@lem1130959 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1130998 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term212 _26690 P Q h.
Proof. exact (proj1 (@lem1130994 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1131005 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term202 _26690 _18588 Q P t) : term202 _26690 _18588 Q P t.
Proof. exact (h1). Qed.
Lemma lem1131009 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term202 _26690 _18588 Q P t) : term202 _26690 _18588 Q P t.
Proof. exact (h1). Qed.
Lemma lem1131015 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term202 _26690 _18588 Q P t) : term202 _26690 _18588 Q P t.
Proof. exact (h1). Qed.
Lemma lem1131019 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term202 _26690 _18588 Q P t) : term202 _26690 _18588 Q P t.
Proof. exact (h1). Qed.
Lemma lem1131100 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1131178 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1131248 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 P h) : term209 _26690 P h.
Proof. exact (h1). Qed.
Lemma lem1131334 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1131412 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1131486 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) : term191 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1131490 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1131568 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1131646 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1131716 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : @I (_26690 -> Prop) Q h) : @I (_26690 -> Prop) Q h.
Proof. exact (h1). Qed.
Lemma lem1131720 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) : term209 _26690 Q h.
Proof. exact (h1). Qed.
Lemma lem1131802 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1131880 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1131954 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) : term191 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1131958 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1132220 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1132254 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1132284 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 P h) : term209 _26690 P h.
Proof. exact (h1). Qed.
Lemma lem1132322 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1132356 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1132388 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) : term191 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1132390 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1132424 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1132458 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1132488 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : @I (_26690 -> Prop) Q h) : @I (_26690 -> Prop) Q h.
Proof. exact (h1). Qed.
Lemma lem1132490 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) : term209 _26690 Q h.
Proof. exact (h1). Qed.
Lemma lem1132526 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term199 _26690 _18588 P Q t.
Proof. exact (h1). Qed.
Lemma lem1132560 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term191 _26690 P t.
Proof. exact (h1). Qed.
Lemma lem1132592 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) : term191 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1132594 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1132608 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (proj2 (@lem1130994 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132609 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term218 _26690 _18588 P Q t.
Proof. exact (fun h0 : term199 _26690 _18588 P Q t => @lem1132608 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132611 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132612 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term218 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (@lem1132611 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132613 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132612 _26690 _18588 P Q t) (@lem1132609 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132616 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132618 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term199 _26690 _18588 P Q t) = (term220 _26690 _18588 P Q t).
Proof. exact (@lem1132616 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132621 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term220 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132618 _26690 _18588 P Q t) (@lem1132220 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132624 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132621 _26690 _18588 P Q t h1 (@lem1132613 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132625 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132624 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132627 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132628 : term221 = False.
Proof. exact (@lem1132627 False). Qed.
Lemma lem1132629 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132628) (@lem1132625 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132631 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (proj2 (@lem1130993 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132632 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term222 _26690 P t.
Proof. exact (fun h0 : term191 _26690 P t => @lem1132631 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132634 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132635 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term222 _26690 P t) = (term189 _26690 P t).
Proof. exact (@lem1132634 (term189 _26690 P t)). Qed.
Lemma lem1132636 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (EQ_MP (@lem1132635 _26690 P t) (@lem1132632 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132639 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132641 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term191 _26690 P t) = (term223 _26690 P t).
Proof. exact (@lem1132639 (term189 _26690 P t)). Qed.
Lemma lem1132644 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term223 _26690 P t.
Proof. exact (EQ_MP (@lem1132641 _26690 P t) (@lem1132254 _26690 P t h1)). Qed.
Lemma lem1132647 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132644 _26690 P t h1 (@lem1132636 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132648 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132647 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132650 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132651 : term221 = False.
Proof. exact (@lem1132650 False). Qed.
Lemma lem1132652 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132651) (@lem1132648 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132654 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : @I (_26690 -> Prop) P h.
Proof. exact (proj1 (@lem1130993 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132655 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term224 _26690 P h.
Proof. exact (fun h0 : term209 _26690 P h => @lem1132654 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132657 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132658 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) : (term224 _26690 P h) = (@I (_26690 -> Prop) P h).
Proof. exact (@lem1132657 (@I (_26690 -> Prop) P h)). Qed.
Lemma lem1132659 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : @I (_26690 -> Prop) P h.
Proof. exact (EQ_MP (@lem1132658 _26690 P h) (@lem1132655 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132662 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132664 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) : (term209 _26690 P h) = (term225 _26690 P h).
Proof. exact (@lem1132662 (@I (_26690 -> Prop) P h)). Qed.
Lemma lem1132667 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 P h) : term225 _26690 P h.
Proof. exact (EQ_MP (@lem1132664 _26690 P h) (@lem1132284 _26690 P h h1)). Qed.
Lemma lem1132670 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132667 _26690 P h h1 (@lem1132659 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132671 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132670 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132673 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132674 : term221 = False.
Proof. exact (@lem1132673 False). Qed.
Lemma lem1132675 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132674) (@lem1132671 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132677 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (proj2 (@lem1130994 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132678 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term218 _26690 _18588 P Q t.
Proof. exact (fun h0 : term199 _26690 _18588 P Q t => @lem1132677 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132680 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132681 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term218 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (@lem1132680 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132682 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132681 _26690 _18588 P Q t) (@lem1132678 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132685 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132687 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term199 _26690 _18588 P Q t) = (term220 _26690 _18588 P Q t).
Proof. exact (@lem1132685 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132690 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term220 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132687 _26690 _18588 P Q t) (@lem1132322 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132693 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132690 _26690 _18588 P Q t h1 (@lem1132682 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132694 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132693 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132696 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132697 : term221 = False.
Proof. exact (@lem1132696 False). Qed.
Lemma lem1132698 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132697) (@lem1132694 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132700 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (proj2 (@lem1130993 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132701 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term222 _26690 P t.
Proof. exact (fun h0 : term191 _26690 P t => @lem1132700 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132703 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132704 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term222 _26690 P t) = (term189 _26690 P t).
Proof. exact (@lem1132703 (term189 _26690 P t)). Qed.
Lemma lem1132705 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (EQ_MP (@lem1132704 _26690 P t) (@lem1132701 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132708 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132710 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term191 _26690 P t) = (term223 _26690 P t).
Proof. exact (@lem1132708 (term189 _26690 P t)). Qed.
Lemma lem1132713 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term223 _26690 P t.
Proof. exact (EQ_MP (@lem1132710 _26690 P t) (@lem1132356 _26690 P t h1)). Qed.
Lemma lem1132716 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132713 _26690 P t h1 (@lem1132705 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132717 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132716 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132719 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132720 : term221 = False.
Proof. exact (@lem1132719 False). Qed.
Lemma lem1132721 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132720) (@lem1132717 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132723 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1132724 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term222 _26690 Q t.
Proof. exact (fun h0 : term191 _26690 Q t => @lem1132723 _26690 Q t h1). Qed.
Lemma lem1132726 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132727 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term222 _26690 Q t) = (term189 _26690 Q t).
Proof. exact (@lem1132726 (term189 _26690 Q t)). Qed.
Lemma lem1132728 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (EQ_MP (@lem1132727 _26690 Q t) (@lem1132724 _26690 Q t h1)). Qed.
Lemma lem1132731 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132733 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term191 _26690 Q t) = (term223 _26690 Q t).
Proof. exact (@lem1132731 (term189 _26690 Q t)). Qed.
Lemma lem1132736 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) : term223 _26690 Q t.
Proof. exact (EQ_MP (@lem1132733 _26690 Q t) (@lem1132388 _26690 Q t h1)). Qed.
Lemma lem1132739 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (@lem1132736 _26690 Q t h1 (@lem1132728 _26690 Q t h2)). Qed.
Lemma lem1132740 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132739 _26690 Q t h1 h2). Qed.
Lemma lem1132742 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132743 : term221 = False.
Proof. exact (@lem1132742 False). Qed.
Lemma lem1132744 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132743) (@lem1132740 _26690 Q t h1 h2)). Qed.
Lemma lem1132746 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (proj2 (@lem1130994 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132747 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term218 _26690 _18588 P Q t.
Proof. exact (fun h0 : term199 _26690 _18588 P Q t => @lem1132746 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132749 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132750 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term218 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (@lem1132749 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132751 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132750 _26690 _18588 P Q t) (@lem1132747 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132754 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132756 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term199 _26690 _18588 P Q t) = (term220 _26690 _18588 P Q t).
Proof. exact (@lem1132754 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132759 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term220 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132756 _26690 _18588 P Q t) (@lem1132424 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132762 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132759 _26690 _18588 P Q t h1 (@lem1132751 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132763 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132762 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132765 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132766 : term221 = False.
Proof. exact (@lem1132765 False). Qed.
Lemma lem1132767 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132766) (@lem1132763 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132769 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (proj2 (@lem1130993 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132770 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term222 _26690 P t.
Proof. exact (fun h0 : term191 _26690 P t => @lem1132769 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132772 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132773 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term222 _26690 P t) = (term189 _26690 P t).
Proof. exact (@lem1132772 (term189 _26690 P t)). Qed.
Lemma lem1132774 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (EQ_MP (@lem1132773 _26690 P t) (@lem1132770 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132777 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132779 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term191 _26690 P t) = (term223 _26690 P t).
Proof. exact (@lem1132777 (term189 _26690 P t)). Qed.
Lemma lem1132782 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term223 _26690 P t.
Proof. exact (EQ_MP (@lem1132779 _26690 P t) (@lem1132458 _26690 P t h1)). Qed.
Lemma lem1132785 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132782 _26690 P t h1 (@lem1132774 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132786 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132785 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132788 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132789 : term221 = False.
Proof. exact (@lem1132788 False). Qed.
Lemma lem1132790 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132789) (@lem1132786 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132792 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : @I (_26690 -> Prop) Q h) : @I (_26690 -> Prop) Q h.
Proof. exact (h1). Qed.
Lemma lem1132793 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : @I (_26690 -> Prop) Q h) : term224 _26690 Q h.
Proof. exact (fun h0 : term209 _26690 Q h => @lem1132792 _26690 Q h h1). Qed.
Lemma lem1132795 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132796 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) : (term224 _26690 Q h) = (@I (_26690 -> Prop) Q h).
Proof. exact (@lem1132795 (@I (_26690 -> Prop) Q h)). Qed.
Lemma lem1132797 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : @I (_26690 -> Prop) Q h) : @I (_26690 -> Prop) Q h.
Proof. exact (EQ_MP (@lem1132796 _26690 Q h) (@lem1132793 _26690 Q h h1)). Qed.
Lemma lem1132800 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132802 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) : (term209 _26690 Q h) = (term225 _26690 Q h).
Proof. exact (@lem1132800 (@I (_26690 -> Prop) Q h)). Qed.
Lemma lem1132805 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) : term225 _26690 Q h.
Proof. exact (EQ_MP (@lem1132802 _26690 Q h) (@lem1132490 _26690 Q h h1)). Qed.
Lemma lem1132808 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (@lem1132805 _26690 Q h h1 (@lem1132797 _26690 Q h h2)). Qed.
Lemma lem1132809 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : term221.
Proof. exact (fun h0 : ~ False => @lem1132808 _26690 Q h h1 h2). Qed.
Lemma lem1132811 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132812 : term221 = False.
Proof. exact (@lem1132811 False). Qed.
Lemma lem1132813 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (EQ_MP (@lem1132812) (@lem1132809 _26690 Q h h1 h2)). Qed.
Lemma lem1132815 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (proj2 (@lem1130994 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132816 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term218 _26690 _18588 P Q t.
Proof. exact (fun h0 : term199 _26690 _18588 P Q t => @lem1132815 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132818 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132819 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term218 _26690 _18588 P Q t) = (term197 _26690 _18588 P Q t).
Proof. exact (@lem1132818 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132820 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term197 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132819 _26690 _18588 P Q t) (@lem1132816 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132823 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132825 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) : (term199 _26690 _18588 P Q t) = (term220 _26690 _18588 P Q t).
Proof. exact (@lem1132823 (term197 _26690 _18588 P Q t)). Qed.
Lemma lem1132828 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) : term220 _26690 _18588 P Q t.
Proof. exact (EQ_MP (@lem1132825 _26690 _18588 P Q t) (@lem1132526 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132831 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132828 _26690 _18588 P Q t h1 (@lem1132820 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132832 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132831 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132834 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132835 : term221 = False.
Proof. exact (@lem1132834 False). Qed.
Lemma lem1132836 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132835) (@lem1132832 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132838 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (proj2 (@lem1130993 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132839 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term222 _26690 P t.
Proof. exact (fun h0 : term191 _26690 P t => @lem1132838 _26690 _18588 Q h P t h1). Qed.
Lemma lem1132841 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132842 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term222 _26690 P t) = (term189 _26690 P t).
Proof. exact (@lem1132841 (term189 _26690 P t)). Qed.
Lemma lem1132843 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) : term189 _26690 P t.
Proof. exact (EQ_MP (@lem1132842 _26690 P t) (@lem1132839 _26690 _18588 Q h P t h1)). Qed.
Lemma lem1132846 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132848 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) : (term191 _26690 P t) = (term223 _26690 P t).
Proof. exact (@lem1132846 (term189 _26690 P t)). Qed.
Lemma lem1132851 {_26690 : Type'} (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) : term223 _26690 P t.
Proof. exact (EQ_MP (@lem1132848 _26690 P t) (@lem1132560 _26690 P t h1)). Qed.
Lemma lem1132854 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (@lem1132851 _26690 P t h1 (@lem1132843 _26690 _18588 Q h P t h2)). Qed.
Lemma lem1132855 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132854 _26690 _18588 Q h P t h1 h2). Qed.
Lemma lem1132857 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132858 : term221 = False.
Proof. exact (@lem1132857 False). Qed.
Lemma lem1132859 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132858) (@lem1132855 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132861 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (h1). Qed.
Lemma lem1132862 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term222 _26690 Q t.
Proof. exact (fun h0 : term191 _26690 Q t => @lem1132861 _26690 Q t h1). Qed.
Lemma lem1132864 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132865 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term222 _26690 Q t) = (term189 _26690 Q t).
Proof. exact (@lem1132864 (term189 _26690 Q t)). Qed.
Lemma lem1132866 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term189 _26690 Q t) : term189 _26690 Q t.
Proof. exact (EQ_MP (@lem1132865 _26690 Q t) (@lem1132862 _26690 Q t h1)). Qed.
Lemma lem1132869 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1132871 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term191 _26690 Q t) = (term223 _26690 Q t).
Proof. exact (@lem1132869 (term189 _26690 Q t)). Qed.
Lemma lem1132874 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) : term223 _26690 Q t.
Proof. exact (EQ_MP (@lem1132871 _26690 Q t) (@lem1132592 _26690 Q t h1)). Qed.
Lemma lem1132877 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (@lem1132874 _26690 Q t h1 (@lem1132866 _26690 Q t h2)). Qed.
Lemma lem1132878 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : term221.
Proof. exact (fun h0 : ~ False => @lem1132877 _26690 Q t h1 h2). Qed.
Lemma lem1132880 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1132881 : term221 = False.
Proof. exact (@lem1132880 False). Qed.
Lemma lem1132882 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132881) (@lem1132878 _26690 Q t h1 h2)). Qed.
Lemma lem1132883 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term189 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term189 _26690 Q t => @lem1132882 _26690 Q t h1 h2) (fun h3 : False => @lem1132594 _26690 Q t h2)). Qed.
Lemma lem1132884 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132883 _26690 Q t h1 h2) (@lem1132594 _26690 Q t h2)). Qed.
Lemma lem1132885 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term191 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 Q t => @lem1132884 _26690 Q t h1 h2) (fun h3 : False => @lem1132592 _26690 Q t h1)). Qed.
Lemma lem1132886 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132885 _26690 Q t h1 h2) (@lem1132592 _26690 Q t h1)). Qed.
Lemma lem1132887 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132859 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132560 _26690 P t h1)). Qed.
Lemma lem1132888 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132887 _26690 _18588 Q h P t h1 h2) (@lem1132560 _26690 P t h1)). Qed.
Lemma lem1132889 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132836 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132526 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132890 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132889 _26690 _18588 Q h P t h1 h2) (@lem1132526 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132891 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : (term209 _26690 Q h) = False.
Proof. exact (prop_ext (fun h3 : term209 _26690 Q h => @lem1132813 _26690 Q h h1 h2) (fun h3 : False => @lem1132490 _26690 Q h h1)). Qed.
Lemma lem1132892 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (EQ_MP (@lem1132891 _26690 Q h h1 h2) (@lem1132490 _26690 Q h h1)). Qed.
Lemma lem1132893 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : (@I (_26690 -> Prop) Q h) = False.
Proof. exact (prop_ext (fun h3 : @I (_26690 -> Prop) Q h => @lem1132892 _26690 Q h h1 h2) (fun h3 : False => @lem1132488 _26690 Q h h2)). Qed.
Lemma lem1132894 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (EQ_MP (@lem1132893 _26690 Q h h1 h2) (@lem1132488 _26690 Q h h2)). Qed.
Lemma lem1132895 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132790 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132458 _26690 P t h1)). Qed.
Lemma lem1132896 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132895 _26690 _18588 Q h P t h1 h2) (@lem1132458 _26690 P t h1)). Qed.
Lemma lem1132897 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132767 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132424 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132898 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132897 _26690 _18588 Q h P t h1 h2) (@lem1132424 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132899 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term189 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term189 _26690 Q t => @lem1132744 _26690 Q t h1 h2) (fun h3 : False => @lem1132390 _26690 Q t h2)). Qed.
Lemma lem1132900 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132899 _26690 Q t h1 h2) (@lem1132390 _26690 Q t h2)). Qed.
Lemma lem1132901 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term191 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 Q t => @lem1132900 _26690 Q t h1 h2) (fun h3 : False => @lem1132388 _26690 Q t h1)). Qed.
Lemma lem1132902 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132901 _26690 Q t h1 h2) (@lem1132388 _26690 Q t h1)). Qed.
Lemma lem1132903 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132721 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132356 _26690 P t h1)). Qed.
Lemma lem1132904 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132903 _26690 _18588 Q h P t h1 h2) (@lem1132356 _26690 P t h1)). Qed.
Lemma lem1132905 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132698 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132322 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132906 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132905 _26690 _18588 Q h P t h1 h2) (@lem1132322 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132907 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : (term209 _26690 P h) = False.
Proof. exact (prop_ext (fun h3 : term209 _26690 P h => @lem1132675 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132284 _26690 P h h1)). Qed.
Lemma lem1132908 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132907 _26690 _18588 Q h P t h1 h2) (@lem1132284 _26690 P h h1)). Qed.
Lemma lem1132909 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132652 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132254 _26690 P t h1)). Qed.
Lemma lem1132910 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132909 _26690 _18588 Q h P t h1 h2) (@lem1132254 _26690 P t h1)). Qed.
Lemma lem1132911 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132629 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1132220 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132912 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132911 _26690 _18588 Q h P t h1 h2) (@lem1132220 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132913 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term189 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term189 _26690 Q t => @lem1132886 _26690 Q t h1 h2) (fun h3 : False => @lem1131958 _26690 Q t h2)). Qed.
Lemma lem1132914 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132913 _26690 Q t h1 h2) (@lem1131958 _26690 Q t h2)). Qed.
Lemma lem1132915 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term191 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 Q t => @lem1132914 _26690 Q t h1 h2) (fun h3 : False => @lem1131954 _26690 Q t h1)). Qed.
Lemma lem1132916 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132915 _26690 Q t h1 h2) (@lem1131954 _26690 Q t h1)). Qed.
Lemma lem1132917 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132888 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131880 _26690 P t h1)). Qed.
Lemma lem1132918 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132917 _26690 _18588 Q h P t h1 h2) (@lem1131880 _26690 P t h1)). Qed.
Lemma lem1132919 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132890 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131802 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132920 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132919 _26690 _18588 Q h P t h1 h2) (@lem1131802 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132921 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : (term209 _26690 Q h) = False.
Proof. exact (prop_ext (fun h3 : term209 _26690 Q h => @lem1132894 _26690 Q h h1 h2) (fun h3 : False => @lem1131720 _26690 Q h h1)). Qed.
Lemma lem1132922 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (EQ_MP (@lem1132921 _26690 Q h h1 h2) (@lem1131720 _26690 Q h h1)). Qed.
Lemma lem1132923 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : (@I (_26690 -> Prop) Q h) = False.
Proof. exact (prop_ext (fun h3 : @I (_26690 -> Prop) Q h => @lem1132922 _26690 Q h h1 h2) (fun h3 : False => @lem1131716 _26690 Q h h2)). Qed.
Lemma lem1132924 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (EQ_MP (@lem1132923 _26690 Q h h1 h2) (@lem1131716 _26690 Q h h2)). Qed.
Lemma lem1132925 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132896 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131646 _26690 P t h1)). Qed.
Lemma lem1132926 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132925 _26690 _18588 Q h P t h1 h2) (@lem1131646 _26690 P t h1)). Qed.
Lemma lem1132927 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132898 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131568 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132928 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132927 _26690 _18588 Q h P t h1 h2) (@lem1131568 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132929 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term189 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term189 _26690 Q t => @lem1132902 _26690 Q t h1 h2) (fun h3 : False => @lem1131490 _26690 Q t h2)). Qed.
Lemma lem1132930 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132929 _26690 Q t h1 h2) (@lem1131490 _26690 Q t h2)). Qed.
Lemma lem1132931 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term191 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 Q t => @lem1132930 _26690 Q t h1 h2) (fun h3 : False => @lem1131486 _26690 Q t h1)). Qed.
Lemma lem1132932 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132931 _26690 Q t h1 h2) (@lem1131486 _26690 Q t h1)). Qed.
Lemma lem1132933 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132904 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131412 _26690 P t h1)). Qed.
Lemma lem1132934 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132933 _26690 _18588 Q h P t h1 h2) (@lem1131412 _26690 P t h1)). Qed.
Lemma lem1132935 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132906 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131334 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132936 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132935 _26690 _18588 Q h P t h1 h2) (@lem1131334 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132937 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : (term209 _26690 P h) = False.
Proof. exact (prop_ext (fun h3 : term209 _26690 P h => @lem1132908 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131248 _26690 P h h1)). Qed.
Lemma lem1132938 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132937 _26690 _18588 Q h P t h1 h2) (@lem1131248 _26690 P h h1)). Qed.
Lemma lem1132939 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132910 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131178 _26690 P t h1)). Qed.
Lemma lem1132940 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132939 _26690 _18588 Q h P t h1 h2) (@lem1131178 _26690 P t h1)). Qed.
Lemma lem1132941 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132912 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131100 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132942 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132941 _26690 _18588 Q h P t h1 h2) (@lem1131100 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132943 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term189 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term189 _26690 Q t => @lem1132916 _26690 Q t h1 h2) (fun h3 : False => @lem1131958 _26690 Q t h2)). Qed.
Lemma lem1132944 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132943 _26690 Q t h1 h2) (@lem1131958 _26690 Q t h2)). Qed.
Lemma lem1132945 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term191 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 Q t => @lem1132944 _26690 Q t h1 h2) (fun h3 : False => @lem1131954 _26690 Q t h1)). Qed.
Lemma lem1132946 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132945 _26690 Q t h1 h2) (@lem1131954 _26690 Q t h1)). Qed.
Lemma lem1132947 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132918 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131880 _26690 P t h1)). Qed.
Lemma lem1132948 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132947 _26690 _18588 Q h P t h1 h2) (@lem1131880 _26690 P t h1)). Qed.
Lemma lem1132949 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132920 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131802 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132950 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132949 _26690 _18588 Q h P t h1 h2) (@lem1131802 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132951 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : (term209 _26690 Q h) = False.
Proof. exact (prop_ext (fun h3 : term209 _26690 Q h => @lem1132924 _26690 Q h h1 h2) (fun h3 : False => @lem1131720 _26690 Q h h1)). Qed.
Lemma lem1132952 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (EQ_MP (@lem1132951 _26690 Q h h1 h2) (@lem1131720 _26690 Q h h1)). Qed.
Lemma lem1132953 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : (@I (_26690 -> Prop) Q h) = False.
Proof. exact (prop_ext (fun h3 : @I (_26690 -> Prop) Q h => @lem1132952 _26690 Q h h1 h2) (fun h3 : False => @lem1131716 _26690 Q h h2)). Qed.
Lemma lem1132954 {_26690 : Type'} (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (EQ_MP (@lem1132953 _26690 Q h h1 h2) (@lem1131716 _26690 Q h h2)). Qed.
Lemma lem1132955 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132926 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131646 _26690 P t h1)). Qed.
Lemma lem1132956 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132955 _26690 _18588 Q h P t h1 h2) (@lem1131646 _26690 P t h1)). Qed.
Lemma lem1132957 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132928 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131568 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132958 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132957 _26690 _18588 Q h P t h1 h2) (@lem1131568 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132959 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term189 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term189 _26690 Q t => @lem1132932 _26690 Q t h1 h2) (fun h3 : False => @lem1131490 _26690 Q t h2)). Qed.
Lemma lem1132960 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132959 _26690 Q t h1 h2) (@lem1131490 _26690 Q t h2)). Qed.
Lemma lem1132961 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : (term191 _26690 Q t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 Q t => @lem1132960 _26690 Q t h1 h2) (fun h3 : False => @lem1131486 _26690 Q t h1)). Qed.
Lemma lem1132962 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term189 _26690 Q t) : False.
Proof. exact (EQ_MP (@lem1132961 _26690 Q t h1 h2) (@lem1131486 _26690 Q t h1)). Qed.
Lemma lem1132963 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132934 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131412 _26690 P t h1)). Qed.
Lemma lem1132964 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132963 _26690 _18588 Q h P t h1 h2) (@lem1131412 _26690 P t h1)). Qed.
Lemma lem1132965 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132936 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131334 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132966 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132965 _26690 _18588 Q h P t h1 h2) (@lem1131334 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132967 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : (term209 _26690 P h) = False.
Proof. exact (prop_ext (fun h3 : term209 _26690 P h => @lem1132938 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131248 _26690 P h h1)). Qed.
Lemma lem1132968 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132967 _26690 _18588 Q h P t h1 h2) (@lem1131248 _26690 P h h1)). Qed.
Lemma lem1132969 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : (term191 _26690 P t) = False.
Proof. exact (prop_ext (fun h3 : term191 _26690 P t => @lem1132940 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131178 _26690 P t h1)). Qed.
Lemma lem1132970 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 P t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132969 _26690 _18588 Q h P t h1 h2) (@lem1131178 _26690 P t h1)). Qed.
Lemma lem1132971 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : (term199 _26690 _18588 P Q t) = False.
Proof. exact (prop_ext (fun h3 : term199 _26690 _18588 P Q t => @lem1132942 _26690 _18588 Q h P t h1 h2) (fun h3 : False => @lem1131100 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132972 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (h : _26690) (P : _26690 -> Prop) (t : list _26690) (h1 : term199 _26690 _18588 P Q t) (h2 : term96 _26690 _18588 Q h P t) : False.
Proof. exact (EQ_MP (@lem1132971 _26690 _18588 Q h P t h1 h2) (@lem1131100 _26690 _18588 P Q t h1)). Qed.
Lemma lem1132973 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) (h2 : term202 _26690 _18588 Q P t) : False.
Proof. exact (or_elim (@lem1131019 _26690 _18588 Q P t h2) (fun h0 : term199 _26690 _18588 P Q t => @lem1132950 _26690 _18588 Q h P t h0 h1) (fun h0 : term191 _26690 P t => @lem1132948 _26690 _18588 Q h P t h0 h1)). Qed.
Lemma lem1132974 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) : False.
Proof. exact (or_elim (@lem1130870 _26690 _18588 P Q t h3) (fun h0 : term202 _26690 _18588 Q P t => @lem1132973 _26690 h _18588 Q P t h2 h0) (fun h0 : term189 _26690 Q t => @lem1132946 _26690 Q t h1 h0)). Qed.
Lemma lem1132975 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) (h2 : term202 _26690 _18588 Q P t) : False.
Proof. exact (or_elim (@lem1131015 _26690 _18588 Q P t h2) (fun h0 : term199 _26690 _18588 P Q t => @lem1132958 _26690 _18588 Q h P t h0 h1) (fun h0 : term191 _26690 P t => @lem1132956 _26690 _18588 Q h P t h0 h1)). Qed.
Lemma lem1132976 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (t : list _26690) (Q : _26690 -> Prop) (h : _26690) (h1 : term209 _26690 Q h) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) (h4 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (or_elim (@lem1130870 _26690 _18588 P Q t h3) (fun h0 : term202 _26690 _18588 Q P t => @lem1132975 _26690 h _18588 Q P t h2 h0) (fun h0 : term189 _26690 Q t => @lem1132954 _26690 Q h h1 h4)). Qed.
Lemma lem1132977 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (t : list _26690) (Q : _26690 -> Prop) (h : _26690) (h1 : term176 _26690 h Q t) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) (h4 : @I (_26690 -> Prop) Q h) : False.
Proof. exact (or_elim (@lem1130992 _26690 h Q t h1) (fun h0 : term209 _26690 Q h => @lem1132976 _26690 _18588 P t Q h h0 h2 h3 h4) (fun h0 : term191 _26690 Q t => @lem1132974 _26690 h _18588 P Q t h0 h2 h3)). Qed.
Lemma lem1132978 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) (h2 : term202 _26690 _18588 Q P t) : False.
Proof. exact (or_elim (@lem1131009 _26690 _18588 Q P t h2) (fun h0 : term199 _26690 _18588 P Q t => @lem1132966 _26690 _18588 Q h P t h0 h1) (fun h0 : term191 _26690 P t => @lem1132964 _26690 _18588 Q h P t h0 h1)). Qed.
Lemma lem1132979 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term191 _26690 Q t) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) : False.
Proof. exact (or_elim (@lem1130870 _26690 _18588 P Q t h3) (fun h0 : term202 _26690 _18588 Q P t => @lem1132978 _26690 h _18588 Q P t h2 h0) (fun h0 : term189 _26690 Q t => @lem1132962 _26690 Q t h1 h0)). Qed.
Lemma lem1132980 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (Q : _26690 -> Prop) (P : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) (h2 : term202 _26690 _18588 Q P t) : False.
Proof. exact (or_elim (@lem1131005 _26690 _18588 Q P t h2) (fun h0 : term199 _26690 _18588 P Q t => @lem1132972 _26690 _18588 Q h P t h0 h1) (fun h0 : term191 _26690 P t => @lem1132970 _26690 _18588 Q h P t h0 h1)). Qed.
Lemma lem1132981 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term209 _26690 P h) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) : False.
Proof. exact (or_elim (@lem1130870 _26690 _18588 P Q t h3) (fun h0 : term202 _26690 _18588 Q P t => @lem1132980 _26690 h _18588 Q P t h2 h0) (fun h0 : term189 _26690 Q t => @lem1132968 _26690 _18588 Q h P t h1 h2)). Qed.
Lemma lem1132982 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term176 _26690 h Q t) (h2 : term209 _26690 P h) (h3 : term96 _26690 _18588 Q h P t) (h4 : term105 _26690 _18588 P Q t) : False.
Proof. exact (or_elim (@lem1130992 _26690 h Q t h1) (fun h0 : term209 _26690 Q h => @lem1132981 _26690 h _18588 P Q t h2 h3 h4) (fun h0 : term191 _26690 Q t => @lem1132979 _26690 h _18588 P Q t h0 h3 h4)). Qed.
Lemma lem1132983 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term176 _26690 h Q t) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) : False.
Proof. exact (or_elim (@lem1130998 _26690 _18588 Q h P t h2) (fun h0 : term209 _26690 P h => @lem1132982 _26690 h _18588 P Q t h1 h0 h2 h3) (fun h0 : @I (_26690 -> Prop) Q h => @lem1132977 _26690 _18588 P t Q h h1 h2 h3 h0)). Qed.
Lemma lem1132984 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term176 _26690 h Q t) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) : (term176 _26690 h Q t) = False.
Proof. exact (prop_ext (fun h4 : term176 _26690 h Q t => @lem1132983 _26690 h _18588 P Q t h1 h2 h3) (fun h4 : False => @lem1130165 _26690 h Q t h1)). Qed.
Lemma lem1132985 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term176 _26690 h Q t) (h2 : term96 _26690 _18588 Q h P t) (h3 : term105 _26690 _18588 P Q t) : False.
Proof. exact (EQ_MP (@lem1132984 _26690 h _18588 P Q t h1 h2 h3) (@lem1130165 _26690 h Q t h1)). Qed.
Lemma lem1132986 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) (h2 : term105 _26690 _18588 P Q t) : term175 _26690 h Q t.
Proof. exact (fun h0 : term176 _26690 h Q t => @lem1132985 _26690 h _18588 P Q t h0 h1 h2). Qed.
Lemma lem1132987 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term96 _26690 _18588 Q h P t) (h2 : term105 _26690 _18588 P Q t) : term37 _26690 h Q t.
Proof. exact (EQ_MP (@lem1130164 _26690 h Q t) (@lem1132986 _26690 h _18588 P Q t h1 h2)). Qed.
Lemma lem1132988 {_26690 : Type'} (h : _26690) (_18588 : type636 _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term105 _26690 _18588 P Q t) : term98 _26690 _18588 P h Q t.
Proof. exact (fun h0 : term96 _26690 _18588 Q h P t => @lem1132987 _26690 h _18588 P Q t h0 h1). Qed.
Lemma lem1132989 {_26690 : Type'} (_18588 : type636 _26690) (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term107 _26690 _18588 P h Q t.
Proof. exact (fun h0 : term105 _26690 _18588 P Q t => @lem1132988 _26690 h _18588 P Q t h0). Qed.
Lemma lem1132994 {_26690 : Type'} (_18588 : type636 _26690) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term109 _26690 _18588 h Q t.
Proof. exact (fun P : _26690 -> Prop => @lem1132989 _26690 _18588 P h Q t). Qed.
Lemma lem1132999 {_26690 : Type'} (_18588 : type636 _26690) (Q : _26690 -> Prop) (t : list _26690) : term111 _26690 _18588 Q t.
Proof. exact (fun h : _26690 => @lem1132994 _26690 _18588 h Q t). Qed.
Lemma lem1133004 {_26690 : Type'} (_18588 : type636 _26690) (t : list _26690) : term113 _26690 _18588 t.
Proof. exact (fun Q : _26690 -> Prop => @lem1132999 _26690 _18588 Q t). Qed.
Lemma lem1133009 {_26690 : Type'} (_18588 : type636 _26690) : term115 _26690 _18588.
Proof. exact (fun t : list _26690 => @lem1133004 _26690 _18588 t). Qed.
Lemma lem1133010 {_26690 : Type'} (_18588 : type636 _26690) : term172 _26690 _18588.
Proof. exact (fun h0 : term170 _26690 _18588 => @lem1133009 _26690 _18588). Qed.
Lemma lem1133015 {_26690 : Type'} : term174 _26690.
Proof. exact (fun _18588 : type636 _26690 => @lem1133010 _26690 _18588). Qed.
Lemma lem1133016 {_26690 : Type'} : term83 _26690.
Proof. exact (EQ_MP (@lem1130157 _26690) (@lem1133015 _26690)). Qed.
Lemma lem1133017 {_26690 : Type'} (t : list _26690) : term226 _26690 t.
Proof. exact (@lem1133016 _26690 t). Qed.
Lemma lem1133018 {_26690 : Type'} (t : list _26690) : (term226 _26690 t) = (term79 _26690 t).
Proof. exact (eq_refl (term226 _26690 t)). Qed.
Lemma lem1133019 {_26690 : Type'} (t : list _26690) : term79 _26690 t.
Proof. exact (EQ_MP (@lem1133018 _26690 t) (@lem1133017 _26690 t)). Qed.
Lemma lem1133020 {_26690 : Type'} (t : list _26690) (Q : _26690 -> Prop) : term227 _26690 t Q.
Proof. exact (@lem1133019 _26690 t Q). Qed.
Lemma lem1133021 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : (term227 _26690 t Q) = (term75 _26690 Q t).
Proof. exact (eq_refl (term227 _26690 t Q)). Qed.
Lemma lem1133022 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) : term75 _26690 Q t.
Proof. exact (EQ_MP (@lem1133021 _26690 Q t) (@lem1133020 _26690 t Q)). Qed.
Lemma lem1133023 {_26690 : Type'} (Q : _26690 -> Prop) (t : list _26690) (h : _26690) : term228 _26690 Q t h.
Proof. exact (@lem1133022 _26690 Q t h). Qed.
Lemma lem1133024 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term228 _26690 Q t h) = (term71 _26690 h Q t).
Proof. exact (eq_refl (term228 _26690 Q t h)). Qed.
Lemma lem1133025 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term71 _26690 h Q t.
Proof. exact (EQ_MP (@lem1133024 _26690 h Q t) (@lem1133023 _26690 Q t h)). Qed.
Lemma lem1133026 {_26690 : Type'} (h : _26690) (Q : _26690 -> Prop) (t : list _26690) (P : _26690 -> Prop) : term229 _26690 h Q t P.
Proof. exact (@lem1133025 _26690 h Q t P). Qed.
Lemma lem1133027 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : (term229 _26690 h Q t P) = (term62 _26690 P h Q t).
Proof. exact (eq_refl (term229 _26690 h Q t P)). Qed.
Lemma lem1133028 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term62 _26690 P h Q t.
Proof. exact (EQ_MP (@lem1133027 _26690 P h Q t) (@lem1133026 _26690 h Q t P)). Qed.
Lemma lem1133030 {_26690 : Type'} (P : _26690 -> Prop) (h : _26690) (Q : _26690 -> Prop) (t : list _26690) : term62 _26690 P h Q t.
Proof. exact (@lem1129725 _26690 P h Q t (@lem1133028 _26690 P h Q t)). Qed.
Lemma lem1133031 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term8 _26690 P Q t) : term60 _26690 P h Q t.
Proof. exact (@lem1133030 _26690 P h Q t (@lem1129617 _26690 P Q t h1)). Qed.
Lemma lem1133032 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term61 _26690 P h Q t) (h2 : term8 _26690 P Q t) : False.
Proof. exact (@lem1133031 _26690 h P Q t h2 (@lem1129709 _26690 P h Q t h1)). Qed.
Lemma lem1133033 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term61 _26690 P h Q t) (h2 : term8 _26690 P Q t) : (term61 _26690 P h Q t) = False.
Proof. exact (prop_ext (fun h3 : term61 _26690 P h Q t => @lem1133032 _26690 h P Q t h1 h2) (fun h3 : False => @lem1129709 _26690 P h Q t h1)). Qed.
Lemma lem1133034 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term61 _26690 P h Q t) (h2 : term8 _26690 P Q t) : False.
Proof. exact (EQ_MP (@lem1133033 _26690 h P Q t h1 h2) (@lem1129709 _26690 P h Q t h1)). Qed.
Lemma lem1133035 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term8 _26690 P Q t) : term60 _26690 P h Q t.
Proof. exact (fun h0 : term61 _26690 P h Q t => @lem1133034 _26690 h P Q t h0 h1). Qed.
Lemma lem1133036 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term8 _26690 P Q t) : term58 _26690 P h Q t.
Proof. exact (EQ_MP (@lem1129708 _26690 P h Q t) (@lem1133035 _26690 h P Q t h1)). Qed.
Lemma lem1133037 {_26690 : Type'} (h : _26690) (P : _26690 -> Prop) (Q : _26690 -> Prop) (t : list _26690) (h1 : term8 _26690 P Q t) : term12 _26690 P Q h t.
Proof. exact (EQ_MP (@lem1129704 _26690 P Q h t) (@lem1133036 _26690 h P Q t h1)). Qed.
Lemma lem1133038 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) (t : list _26690) : term14 _26690 P Q h t.
Proof. exact (fun h0 : term8 _26690 P Q t => @lem1133037 _26690 h P Q t h0). Qed.
Lemma lem1133043 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) (h : _26690) : term18 _26690 P Q h.
Proof. exact (fun t : list _26690 => @lem1133038 _26690 P Q h t). Qed.
Lemma lem1133048 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : term22 _26690 P Q.
Proof. exact (fun h : _26690 => @lem1133043 _26690 P Q h). Qed.
Lemma lem1133049 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : term24 _26690 P Q.
Proof. exact (conj (@lem1129648 _26690 P Q) (@lem1133048 _26690 P Q)). Qed.
Lemma lem1133050 {_26690 : Type'} (P : _26690 -> Prop) (Q : _26690 -> Prop) : term29 _26690 P Q.
Proof. exact (@lem1129616 _26690 P Q (@lem1133049 _26690 P Q)). Qed.
Lemma lem1133055 {_26690 : Type'} (P : _26690 -> Prop) : term230 _26690 P.
Proof. exact (fun Q : _26690 -> Prop => @lem1133050 _26690 P Q). Qed.
Lemma lem1133060 {_26690 : Type'} : term231 _26690.
Proof. exact (fun P : _26690 -> Prop => @lem1133055 _26690 P). Qed.
