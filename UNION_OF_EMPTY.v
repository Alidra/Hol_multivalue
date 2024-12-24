Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_OF_EMPTY_term_abbrevs.
Require Import NOT_IN_EMPTY_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4851596 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4851597 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4851598 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4851597 A P) (@lem4851596 A P)). Qed.
Lemma lem4851599 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4851598 A P Q). Qed.
Lemma lem4851600 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@UNION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4851602 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : P (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4851604 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4851600 A P Q) (@lem4851599 A P Q)). Qed.
Lemma lem4851605 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4851604 A P Q). Qed.
Lemma lem4851622 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4851623 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q (@EMPTY A)) = (term4 A P Q).
Proof. exact (MK_COMB (@lem4851605 A P Q) (@lem4851622 A)). Qed.
Lemma lem4851625 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4851626 {A : Type'} (f : type686 A) (y : A -> Prop) : (term6 A f y) = (f y).
Proof. exact (@lem4851625 (A -> Prop) Prop f y). Qed.
Lemma lem4851627 {A : Type'} (P : type180 A) (Q : type686 A) : (term7 A P Q) = (term4 A P Q).
Proof. exact (@lem4851626 A (term3 A P Q) (@EMPTY A)). Qed.
Lemma lem4851628 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term8 A P Q s) = (term9 A P Q s).
Proof. exact (eq_refl (term8 A P Q s)). Qed.
Lemma lem4851629 {A : Type'} (P : type180 A) (Q : type686 A) : (term10 A P Q) = (term3 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4851628 A P Q s)). Qed.
Lemma lem4851630 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4851631 {A : Type'} (P : type180 A) (Q : type686 A) : (term7 A P Q) = (term4 A P Q).
Proof. exact (MK_COMB (@lem4851629 A P Q) (@lem4851630 A)). Qed.
Lemma lem4851632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4851633 {A : Type'} (P : type180 A) (Q : type686 A) : (term11 A P Q) = (term12 A P Q).
Proof. exact (MK_COMB (@lem4851632) (@lem4851631 A P Q)). Qed.
Lemma lem4851634 {A : Type'} (P : type180 A) (Q : type686 A) : (term4 A P Q) = (term13 A P Q).
Proof. exact (eq_refl (term4 A P Q)). Qed.
Lemma lem4851635 {A : Type'} (P : type180 A) (Q : type686 A) : ((term7 A P Q) = (term4 A P Q)) = ((term4 A P Q) = (term13 A P Q)).
Proof. exact (MK_COMB (@lem4851633 A P Q) (@lem4851634 A P Q)). Qed.
Lemma lem4851636 {A : Type'} (P : type180 A) (Q : type686 A) : (term4 A P Q) = (term13 A P Q).
Proof. exact (EQ_MP (@lem4851635 A P Q) (@lem4851627 A P Q)). Qed.
Lemma lem4851653 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q (@EMPTY A)) = (term13 A P Q).
Proof. exact (TRANS (@lem4851623 A P Q) (@lem4851636 A P Q)). Qed.
Lemma lem4851654 {A : Type'} (P : type180 A) (Q : type686 A) : (term13 A P Q) = (@UNION_OF A P Q (@EMPTY A)).
Proof. exact (SYM (@lem4851653 A P Q)). Qed.
Lemma lem4851655 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4851656 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem4851657 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem4851656 A x) (@lem4851655 A x)). Qed.
Lemma lem4851658 {A : Type'} (x : A) : term16 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4851660 {A : Type'} (P : type180 A) : (P (@EMPTY (A -> Prop))) = ((P (@EMPTY (A -> Prop))) = True).
Proof. exact (@lem7 (P (@EMPTY (A -> Prop)))). Qed.
Lemma lem4851665 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (P (@EMPTY (A -> Prop))) = True.
Proof. exact (EQ_MP (@lem4851660 A P) (@lem4851602 A P h1)). Qed.
Lemma lem4851666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851667 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (term17 A P) = (and True).
Proof. exact (MK_COMB (@lem4851666) (@lem4851665 A P h1)). Qed.
Lemma lem4851677 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4851658 A x (@lem4851657 A x)). Qed.
Lemma lem4851678 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem4851677 (A -> Prop) x). Qed.
Lemma lem4851679 {A : Type'} (c : A -> Prop) : (@IN (A -> Prop) c (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem4851678 A c). Qed.
Lemma lem4851680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4851681 {A : Type'} (c : A -> Prop) : (term18 A c) = (imp False).
Proof. exact (MK_COMB (@lem4851680) (@lem4851679 A c)). Qed.
Lemma lem4851682 {A : Type'} (Q : type686 A) (c : A -> Prop) : (Q c) = (Q c).
Proof. exact (eq_refl (Q c)). Qed.
Lemma lem4851683 {A : Type'} (Q : type686 A) (c : A -> Prop) : (term19 A Q c) = (term20 A Q c).
Proof. exact (MK_COMB (@lem4851681 A c) (@lem4851682 A Q c)). Qed.
Lemma lem4851685 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4851686 {A : Type'} (Q : type686 A) (c : A -> Prop) : (term20 A Q c) = True.
Proof. exact (@lem4851685 (Q c)). Qed.
Lemma lem4851687 {A : Type'} (Q : type686 A) (c : A -> Prop) : (term19 A Q c) = True.
Proof. exact (TRANS (@lem4851683 A Q c) (@lem4851686 A Q c)). Qed.
Lemma lem4851688 {A : Type'} (Q : type686 A) : (term21 A Q) = (term22 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4851687 A Q c)). Qed.
Lemma lem4851689 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4851690 {A : Type'} (Q : type686 A) : (term23 A Q) = (term24 A).
Proof. exact (MK_COMB (@lem4851689 A) (@lem4851688 A Q)). Qed.
Lemma lem4851692 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4851693 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem4851692 (A -> Prop) t). Qed.
Lemma lem4851694 {A : Type'} : (term24 A) = True.
Proof. exact (@lem4851693 A True). Qed.
Lemma lem4851695 {A : Type'} (Q : type686 A) : (term23 A Q) = True.
Proof. exact (TRANS (@lem4851690 A Q) (@lem4851694 A)). Qed.
Lemma lem4851696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851697 {A : Type'} (Q : type686 A) : (term27 A Q) = (and True).
Proof. exact (MK_COMB (@lem4851696) (@lem4851695 A Q)). Qed.
Lemma lem4851701 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem4851702 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem4851701 A). Qed.
Lemma lem4851703 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4851704 {A : Type'} : (term28 A) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem4851703 A) (@lem4851702 A)). Qed.
Lemma lem4851705 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4851706 {A : Type'} : ((@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4851704 A) (@lem4851705 A)). Qed.
Lemma lem4851708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4851709 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4851708 (A -> Prop) x). Qed.
Lemma lem4851710 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem4851709 A (@EMPTY A)). Qed.
Lemma lem4851711 {A : Type'} : ((@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem4851706 A) (@lem4851710 A)). Qed.
Lemma lem4851712 {A : Type'} (Q : type686 A) : (term29 A Q) = (True /\ True).
Proof. exact (MK_COMB (@lem4851697 A Q) (@lem4851711 A)). Qed.
Lemma lem4851714 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4851715 : (True /\ True) = True.
Proof. exact (@lem4851714 True). Qed.
Lemma lem4851716 {A : Type'} (Q : type686 A) : (term29 A Q) = True.
Proof. exact (TRANS (@lem4851712 A Q) (@lem4851715)). Qed.
Lemma lem4851717 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (term30 A P Q) = (True /\ True).
Proof. exact (MK_COMB (@lem4851667 A P h1) (@lem4851716 A Q)). Qed.
Lemma lem4851719 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4851720 : (True /\ True) = True.
Proof. exact (@lem4851719 True). Qed.
Lemma lem4851721 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (term30 A P Q) = True.
Proof. exact (TRANS (@lem4851717 A Q P h1) (@lem4851720)). Qed.
Lemma lem4851722 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : True = (term30 A P Q).
Proof. exact (SYM (@lem4851721 A Q P h1)). Qed.
Lemma lem4851723 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : term30 A P Q.
Proof. exact (EQ_MP (@lem4851722 A Q P h1) (@lem0)). Qed.
Lemma lem4851724 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : term13 A P Q.
Proof. exact (ex_intro (term31 A P Q) (@EMPTY (A -> Prop)) (@lem4851723 A Q P h1)). Qed.
Lemma lem4851725 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @UNION_OF A P Q (@EMPTY A).
Proof. exact (EQ_MP (@lem4851654 A P Q) (@lem4851724 A Q P h1)). Qed.
Lemma lem4851726 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (P (@EMPTY (A -> Prop))) = (@UNION_OF A P Q (@EMPTY A)).
Proof. exact (prop_ext (fun h2 : P (@EMPTY (A -> Prop)) => @lem4851725 A Q P h1) (fun h2 : @UNION_OF A P Q (@EMPTY A) => @lem4851602 A P h1)). Qed.
Lemma lem4851727 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @UNION_OF A P Q (@EMPTY A).
Proof. exact (EQ_MP (@lem4851726 A Q P h1) (@lem4851602 A P h1)). Qed.
Lemma lem4851728 {A : Type'} (P : type180 A) (Q : type686 A) : term32 A P Q.
Proof. exact (fun h0 : P (@EMPTY (A -> Prop)) => @lem4851727 A Q P h0). Qed.
Lemma lem4851733 {A : Type'} (P : type180 A) : term33 A P.
Proof. exact (fun Q : type686 A => @lem4851728 A P Q). Qed.
Lemma lem4851738 {A : Type'} : term34 A.
Proof. exact (fun P : type180 A => @lem4851733 A P). Qed.
