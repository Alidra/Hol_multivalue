Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import sum_INDUCT_term_abbrevs.
Require Import thm1066938_spec.
Require Import thm1066939_spec.
Require Import thm1066989_spec.
Require Import thm1066993_spec.
Require Import thm1067676_spec.
Require Import thm1067682_spec.
Lemma lem1067683 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term1 A B INL' INR' sum' P.
Proof. exact (@lem1066939 A B sum' INL' INR' h1 (term2 A B sum' P)). Qed.
Lemma lem1067684 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (sum' : type1333 A B) (P : type10 A B) : (term1 A B INL' INR' sum' P) = (term3 A B INL' INR' sum' P).
Proof. exact (eq_refl (term1 A B INL' INR' sum' P)). Qed.
Lemma lem1067685 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term3 A B INL' INR' sum' P.
Proof. exact (EQ_MP (@lem1067684 A B INL' INR' sum' P) (@lem1067683 A B P sum' INL' INR' h1)). Qed.
Lemma lem1067686 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term4 A B sum' INR'.
Proof. exact (proj2 (@lem1066938 A B sum' INL' INR' h1)). Qed.
Lemma lem1067687 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term5 A B sum' INL'.
Proof. exact (proj1 (@lem1066938 A B sum' INL' INR' h1)). Qed.
Lemma lem1067690 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (INL' : type1431 A B) (a : A) : (term6 A B sum' P INL' a) = (term7 A B sum' P INL' a).
Proof. exact (eq_refl (term6 A B sum' P INL' a)). Qed.
Lemma lem1067691 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term8 A B sum' INL' a.
Proof. exact (@lem1067687 A B sum' INL' INR' h1 a). Qed.
Lemma lem1067692 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) : (term8 A B sum' INL' a) = (term9 A B sum' INL' a).
Proof. exact (eq_refl (term8 A B sum' INL' a)). Qed.
Lemma lem1067695 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term9 A B sum' INL' a.
Proof. exact (EQ_MP (@lem1067692 A B sum' INL' a) (@lem1067691 A B a sum' INL' INR' h1)). Qed.
Lemma lem1067696 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term9 A B sum' INL' a.
Proof. exact (@lem1067695 A B a sum' INL' INR' h1). Qed.
Lemma lem1067698 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : (term11 A B INL' a) = (@inl A B a).
Proof. exact (SYM (@lem1067676 A B a INL' h1)). Qed.
Lemma lem1067699 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : (term11 A B INL' a) = (@inl A B a).
Proof. exact (@lem1067698 A B a INL' h1). Qed.
Lemma lem1067700 {A B : Type'} (P : type10 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1067701 {A B : Type'} (P : type10 A B) (a : A) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : (term12 A B P INL' a) = (term13 A B P a).
Proof. exact (MK_COMB (@lem1067700 A B P) (@lem1067699 A B a INL' h1)). Qed.
Lemma lem1067702 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) : (term14 A B sum' INL' a) = (term14 A B sum' INL' a).
Proof. exact (eq_refl (term14 A B sum' INL' a)). Qed.
Lemma lem1067703 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : A) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : (term7 A B sum' P INL' a) = (term15 A B sum' INL' P a).
Proof. exact (MK_COMB (@lem1067702 A B sum' INL' a) (@lem1067701 A B P a INL' h1)). Qed.
Lemma lem1067704 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (INL' : type1431 A B) (a : A) : (term16 A B sum' P INL' a) = (term16 A B sum' P INL' a).
Proof. exact (eq_refl (term16 A B sum' P INL' a)). Qed.
Lemma lem1067705 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : A) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : ((term6 A B sum' P INL' a) = (term7 A B sum' P INL' a)) = ((term6 A B sum' P INL' a) = (term15 A B sum' INL' P a)).
Proof. exact (MK_COMB (@lem1067704 A B sum' P INL' a) (@lem1067703 A B sum' P a INL' h1)). Qed.
Lemma lem1067706 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : A) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : (term6 A B sum' P INL' a) = (term15 A B sum' INL' P a).
Proof. exact (EQ_MP (@lem1067705 A B sum' P a INL' h1) (@lem1067690 A B sum' P INL' a)). Qed.
Lemma lem1067707 {A B : Type'} (P : type10 A B) (h1 : term17 A B P) : term17 A B P.
Proof. exact (h1). Qed.
Lemma lem1067708 {A B : Type'} (a : A) (P : type10 A B) (h1 : term17 A B P) : term18 A B P a.
Proof. exact (@lem1067707 A B P h1 a). Qed.
Lemma lem1067709 {A B : Type'} (P : type10 A B) (a : A) : (term18 A B P a) = (term13 A B P a).
Proof. exact (eq_refl (term18 A B P a)). Qed.
Lemma lem1067710 {A B : Type'} (a : A) (P : type10 A B) (h1 : term17 A B P) : term13 A B P a.
Proof. exact (EQ_MP (@lem1067709 A B P a) (@lem1067708 A B a P h1)). Qed.
Lemma lem1067711 {A B : Type'} (a : A) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term17 A B P) (h2 : sum' = (term0 A B INL' INR')) : term15 A B sum' INL' P a.
Proof. exact (conj (@lem1067696 A B a sum' INL' INR' h2) (@lem1067710 A B a P h1)). Qed.
Lemma lem1067712 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : A) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : (term15 A B sum' INL' P a) = (term6 A B sum' P INL' a).
Proof. exact (SYM (@lem1067706 A B sum' P a INL' h1)). Qed.
Lemma lem1067713 {A B : Type'} (a : A) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term17 A B P) (h2 : INL' = (term10 A B)) (h3 : sum' = (term0 A B INL' INR')) : term6 A B sum' P INL' a.
Proof. exact (EQ_MP (@lem1067712 A B sum' P a INL' h2) (@lem1067711 A B a P sum' INL' INR' h1 h3)). Qed.
Lemma lem1067714 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term17 A B P) (h2 : INL' = (term10 A B)) (h3 : sum' = (term0 A B INL' INR')) : term19 A B sum' P INL'.
Proof. exact (fun a : A => @lem1067713 A B a P sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067715 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : sum' = (term0 A B INL' INR')) : term20 A B sum' P INL'.
Proof. exact (fun h0 : term17 A B P => @lem1067714 A B P sum' INL' INR' h0 h1 h2). Qed.
Lemma lem1067716 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (INR' : type1479 A B) (a : B) : (term21 A B sum' P INR' a) = (term22 A B sum' P INR' a).
Proof. exact (eq_refl (term21 A B sum' P INR' a)). Qed.
Lemma lem1067717 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term23 A B sum' INR' a.
Proof. exact (@lem1067686 A B sum' INL' INR' h1 a). Qed.
Lemma lem1067718 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (a : B) : (term23 A B sum' INR' a) = (term24 A B sum' INR' a).
Proof. exact (eq_refl (term23 A B sum' INR' a)). Qed.
Lemma lem1067721 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term24 A B sum' INR' a.
Proof. exact (EQ_MP (@lem1067718 A B sum' INR' a) (@lem1067717 A B a sum' INL' INR' h1)). Qed.
Lemma lem1067722 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term24 A B sum' INR' a.
Proof. exact (@lem1067721 A B a sum' INL' INR' h1). Qed.
Lemma lem1067724 {A B : Type'} (a : B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) : (term26 A B INR' a) = (@inr A B a).
Proof. exact (SYM (@lem1067682 A B a INR' h1)). Qed.
Lemma lem1067725 {A B : Type'} (a : B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) : (term26 A B INR' a) = (@inr A B a).
Proof. exact (@lem1067724 A B a INR' h1). Qed.
Lemma lem1067726 {A B : Type'} (P : type10 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1067727 {A B : Type'} (P : type10 A B) (a : B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) : (term27 A B P INR' a) = (term28 A B P a).
Proof. exact (MK_COMB (@lem1067726 A B P) (@lem1067725 A B a INR' h1)). Qed.
Lemma lem1067728 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (a : B) : (term29 A B sum' INR' a) = (term29 A B sum' INR' a).
Proof. exact (eq_refl (term29 A B sum' INR' a)). Qed.
Lemma lem1067729 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) : (term22 A B sum' P INR' a) = (term30 A B sum' INR' P a).
Proof. exact (MK_COMB (@lem1067728 A B sum' INR' a) (@lem1067727 A B P a INR' h1)). Qed.
Lemma lem1067730 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (INR' : type1479 A B) (a : B) : (term31 A B sum' P INR' a) = (term31 A B sum' P INR' a).
Proof. exact (eq_refl (term31 A B sum' P INR' a)). Qed.
Lemma lem1067731 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) : ((term21 A B sum' P INR' a) = (term22 A B sum' P INR' a)) = ((term21 A B sum' P INR' a) = (term30 A B sum' INR' P a)).
Proof. exact (MK_COMB (@lem1067730 A B sum' P INR' a) (@lem1067729 A B sum' P a INR' h1)). Qed.
Lemma lem1067732 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) : (term21 A B sum' P INR' a) = (term30 A B sum' INR' P a).
Proof. exact (EQ_MP (@lem1067731 A B sum' P a INR' h1) (@lem1067716 A B sum' P INR' a)). Qed.
Lemma lem1067733 {A B : Type'} (P : type10 A B) (h1 : term32 A B P) : term32 A B P.
Proof. exact (h1). Qed.
Lemma lem1067734 {A B : Type'} (a : B) (P : type10 A B) (h1 : term32 A B P) : term33 A B P a.
Proof. exact (@lem1067733 A B P h1 a). Qed.
Lemma lem1067735 {A B : Type'} (P : type10 A B) (a : B) : (term33 A B P a) = (term28 A B P a).
Proof. exact (eq_refl (term33 A B P a)). Qed.
Lemma lem1067736 {A B : Type'} (a : B) (P : type10 A B) (h1 : term32 A B P) : term28 A B P a.
Proof. exact (EQ_MP (@lem1067735 A B P a) (@lem1067734 A B a P h1)). Qed.
Lemma lem1067737 {A B : Type'} (a : B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term32 A B P) (h2 : sum' = (term0 A B INL' INR')) : term30 A B sum' INR' P a.
Proof. exact (conj (@lem1067722 A B a sum' INL' INR' h2) (@lem1067736 A B a P h1)). Qed.
Lemma lem1067738 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (a : B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) : (term30 A B sum' INR' P a) = (term21 A B sum' P INR' a).
Proof. exact (SYM (@lem1067732 A B sum' P a INR' h1)). Qed.
Lemma lem1067739 {A B : Type'} (a : B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term32 A B P) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : term21 A B sum' P INR' a.
Proof. exact (EQ_MP (@lem1067738 A B sum' P a INR' h2) (@lem1067737 A B a P sum' INL' INR' h1 h3)). Qed.
Lemma lem1067740 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term32 A B P) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : term34 A B sum' P INR'.
Proof. exact (fun a : B => @lem1067739 A B a P sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067741 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INR' = (term25 A B)) (h2 : sum' = (term0 A B INL' INR')) : term35 A B sum' P INR'.
Proof. exact (fun h0 : term32 A B P => @lem1067740 A B P sum' INL' INR' h0 h1 h2). Qed.
Lemma lem1067742 {A B : Type'} (P : type10 A B) (h1 : term36 A B P) : term36 A B P.
Proof. exact (h1). Qed.
Lemma lem1067743 {A B : Type'} (P : type10 A B) (h1 : term36 A B P) : term32 A B P.
Proof. exact (proj2 (@lem1067742 A B P h1)). Qed.
Lemma lem1067744 {A B : Type'} (P : type10 A B) (h1 : term36 A B P) : term17 A B P.
Proof. exact (proj1 (@lem1067742 A B P h1)). Qed.
Lemma lem1067745 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : sum' = (term0 A B INL' INR')) : term19 A B sum' P INL'.
Proof. exact (@lem1067715 A B P sum' INL' INR' h2 h3 (@lem1067744 A B P h1)). Qed.
Lemma lem1067746 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : term34 A B sum' P INR'.
Proof. exact (@lem1067741 A B P sum' INL' INR' h2 h3 (@lem1067743 A B P h1)). Qed.
Lemma lem1067747 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term37 A B INL' sum' P INR'.
Proof. exact (conj (@lem1067745 A B P sum' INL' INR' h1 h2 h4) (@lem1067746 A B P sum' INL' INR' h1 h3 h4)). Qed.
Lemma lem1067748 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term38 A B sum' P.
Proof. exact (@lem1067685 A B P sum' INL' INR' h4 (@lem1067747 A B P sum' INL' INR' h1 h2 h3 h4)). Qed.
Lemma lem1067749 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term39 A B sum' P x.
Proof. exact (@lem1067748 A B P sum' INL' INR' h1 h2 h3 h4 (@_dest_sum A B x)). Qed.
Lemma lem1067750 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (x : Datatypes.sum A B) : (term39 A B sum' P x) = (term40 A B sum' P x).
Proof. exact (eq_refl (term39 A B sum' P x)). Qed.
Lemma lem1067751 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term40 A B sum' P x.
Proof. exact (EQ_MP (@lem1067750 A B sum' P x) (@lem1067749 A B x P sum' INL' INR' h1 h2 h3 h4)). Qed.
Lemma lem1067753 {A B : Type'} (r : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : (sum' r) = ((term41 A B r) = r).
Proof. exact (TRANS (@lem1066993 A B r sum' INL' INR' h1 h2 h3) (@lem1066989 A B r)). Qed.
Lemma lem1067754 {A B : Type'} (r : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : (sum' r) = ((term41 A B r) = r).
Proof. exact (@lem1067753 A B r sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067755 {A B : Type'} (x : Datatypes.sum A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : (term42 A B sum' x) = ((term43 A B x) = (@_dest_sum A B x)).
Proof. exact (@lem1067754 A B (@_dest_sum A B x) sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1067757 {A B : Type'} (x : Datatypes.sum A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : (term44 A B sum' x) = (term45 A B x).
Proof. exact (MK_COMB (@lem1067756) (@lem1067755 A B x sum' INL' INR' h1 h2 h3)). Qed.
Lemma lem1067758 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (x : Datatypes.sum A B) : (term46 A B sum' P x) = (term46 A B sum' P x).
Proof. exact (eq_refl (term46 A B sum' P x)). Qed.
Lemma lem1067759 {A B : Type'} (P : type10 A B) (x : Datatypes.sum A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : (term40 A B sum' P x) = (term47 A B sum' P x).
Proof. exact (MK_COMB (@lem1067757 A B x sum' INL' INR' h1 h2 h3) (@lem1067758 A B sum' P x)). Qed.
Lemma lem1067760 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term47 A B sum' P x.
Proof. exact (EQ_MP (@lem1067759 A B P x sum' INL' INR' h2 h3 h4) (@lem1067751 A B x P sum' INL' INR' h1 h2 h3 h4)). Qed.
Lemma lem1067762 {A B : Type'} (a : Datatypes.sum A B) : (term48 A B a) = a.
Proof. exact (@axiom_11 A B a). Qed.
Lemma lem1067763 {A B : Type'} (a : Datatypes.sum A B) : (term48 A B a) = a.
Proof. exact (@lem1067762 A B a). Qed.
Lemma lem1067764 {A B : Type'} (x : Datatypes.sum A B) : (term48 A B x) = x.
Proof. exact (@lem1067763 A B x). Qed.
Lemma lem1067765 {A B : Type'} : (@_dest_sum A B) = (@_dest_sum A B).
Proof. exact (eq_refl (@_dest_sum A B)). Qed.
Lemma lem1067766 {A B : Type'} (x : Datatypes.sum A B) : (term43 A B x) = (@_dest_sum A B x).
Proof. exact (MK_COMB (@lem1067765 A B) (@lem1067764 A B x)). Qed.
Lemma lem1067767 {A B : Type'} : (@eq (recspace (prod A B))) = (@eq (recspace (prod A B))).
Proof. exact (eq_refl (@eq (recspace (prod A B)))). Qed.
Lemma lem1067768 {A B : Type'} (x : Datatypes.sum A B) : (term49 A B x) = (term50 A B x).
Proof. exact (MK_COMB (@lem1067767 A B) (@lem1067766 A B x)). Qed.
Lemma lem1067769 {A B : Type'} (x : Datatypes.sum A B) : (@_dest_sum A B x) = (@_dest_sum A B x).
Proof. exact (eq_refl (@_dest_sum A B x)). Qed.
Lemma lem1067770 {A B : Type'} (x : Datatypes.sum A B) : ((term43 A B x) = (@_dest_sum A B x)) = ((@_dest_sum A B x) = (@_dest_sum A B x)).
Proof. exact (MK_COMB (@lem1067768 A B x) (@lem1067769 A B x)). Qed.
Lemma lem1067771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1067772 {A B : Type'} (x : Datatypes.sum A B) : (term45 A B x) = (term51 A B x).
Proof. exact (MK_COMB (@lem1067771) (@lem1067770 A B x)). Qed.
Lemma lem1067773 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (x : Datatypes.sum A B) : (term46 A B sum' P x) = (term46 A B sum' P x).
Proof. exact (eq_refl (term46 A B sum' P x)). Qed.
Lemma lem1067774 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (x : Datatypes.sum A B) : (term47 A B sum' P x) = (term52 A B sum' P x).
Proof. exact (MK_COMB (@lem1067772 A B x) (@lem1067773 A B sum' P x)). Qed.
Lemma lem1067775 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term52 A B sum' P x.
Proof. exact (EQ_MP (@lem1067774 A B sum' P x) (@lem1067760 A B x P sum' INL' INR' h1 h2 h3 h4)). Qed.
Lemma lem1067776 {A B : Type'} (x : Datatypes.sum A B) : (@_dest_sum A B x) = (@_dest_sum A B x).
Proof. exact (eq_refl (@_dest_sum A B x)). Qed.
Lemma lem1067777 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term46 A B sum' P x.
Proof. exact (@lem1067775 A B x P sum' INL' INR' h1 h2 h3 h4 (@lem1067776 A B x)). Qed.
Lemma lem1067778 {A B : Type'} (sum' : type1333 A B) (P : type10 A B) (x : Datatypes.sum A B) : (term46 A B sum' P x) = (term53 A B sum' P x).
Proof. exact (eq_refl (term46 A B sum' P x)). Qed.
Lemma lem1067779 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term53 A B sum' P x.
Proof. exact (EQ_MP (@lem1067778 A B sum' P x) (@lem1067777 A B x P sum' INL' INR' h1 h2 h3 h4)). Qed.
Lemma lem1067780 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term54 A B P x.
Proof. exact (proj2 (@lem1067779 A B x P sum' INL' INR' h1 h2 h3 h4)). Qed.
Lemma lem1067782 {A B : Type'} (a : Datatypes.sum A B) : (term48 A B a) = a.
Proof. exact (@axiom_11 A B a). Qed.
Lemma lem1067783 {A B : Type'} (a : Datatypes.sum A B) : (term48 A B a) = a.
Proof. exact (@lem1067782 A B a). Qed.
Lemma lem1067784 {A B : Type'} (x : Datatypes.sum A B) : (term48 A B x) = x.
Proof. exact (@lem1067783 A B x). Qed.
Lemma lem1067785 {A B : Type'} (P : type10 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1067786 {A B : Type'} (P : type10 A B) (x : Datatypes.sum A B) : (term54 A B P x) = (P x).
Proof. exact (MK_COMB (@lem1067785 A B P) (@lem1067784 A B x)). Qed.
Lemma lem1067787 {A B : Type'} (x : Datatypes.sum A B) (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : P x.
Proof. exact (EQ_MP (@lem1067786 A B P x) (@lem1067780 A B x P sum' INL' INR' h1 h2 h3 h4)). Qed.
Lemma lem1067788 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : term36 A B P) (h2 : INL' = (term10 A B)) (h3 : INR' = (term25 A B)) (h4 : sum' = (term0 A B INL' INR')) : term55 A B P.
Proof. exact (fun x : Datatypes.sum A B => @lem1067787 A B x P sum' INL' INR' h1 h2 h3 h4). Qed.
Lemma lem1067789 {A B : Type'} (P : type10 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : term56 A B P.
Proof. exact (fun h0 : term36 A B P => @lem1067788 A B P sum' INL' INR' h0 h1 h2 h3). Qed.
Lemma lem1067790 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) (h3 : sum' = (term0 A B INL' INR')) : term57 A B.
Proof. exact (fun P : type10 A B => @lem1067789 A B P sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067791 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term10 A B)) (h2 : INR' = (term25 A B)) : term58 A B sum' INL' INR'.
Proof. exact (fun h0 : sum' = (term0 A B INL' INR') => @lem1067790 A B sum' INL' INR' h1 h2 h0). Qed.
Lemma lem1067792 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (eq_refl (term25 A B)). Qed.
Lemma lem1067793 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : term59 A B sum' INL' INR'.
Proof. exact (fun h0 : INR' = (term25 A B) => @lem1067791 A B sum' INL' INR' h1 h0). Qed.
Lemma lem1067794 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : term60 A B sum' INL'.
Proof. exact (@lem1067793 A B sum' (term25 A B) INL' h1). Qed.
Lemma lem1067795 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (h1 : INL' = (term10 A B)) : term61 A B sum' INL'.
Proof. exact (@lem1067794 A B sum' INL' h1 (@lem1067792 A B)). Qed.
Lemma lem1067796 {A B : Type'} : (term10 A B) = (term10 A B).
Proof. exact (eq_refl (term10 A B)). Qed.
Lemma lem1067797 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) : term62 A B sum' INL'.
Proof. exact (fun h0 : INL' = (term10 A B) => @lem1067795 A B sum' INL' h0). Qed.
Lemma lem1067798 {A B : Type'} (sum' : type1333 A B) : term63 A B sum'.
Proof. exact (@lem1067797 A B sum' (term10 A B)). Qed.
Lemma lem1067799 {A B : Type'} (sum' : type1333 A B) : term64 A B sum'.
Proof. exact (@lem1067798 A B sum' (@lem1067796 A B)). Qed.
Lemma lem1067800 {A B : Type'} (sum' : type1333 A B) (h1 : sum' = (term65 A B)) : sum' = (term65 A B).
Proof. exact (h1). Qed.
Lemma lem1067801 {A B : Type'} (sum' : type1333 A B) (h1 : sum' = (term65 A B)) : term57 A B.
Proof. exact (@lem1067799 A B sum' (@lem1067800 A B sum' h1)). Qed.
Lemma lem1067802 {A B : Type'} : (term65 A B) = (term65 A B).
Proof. exact (eq_refl (term65 A B)). Qed.
Lemma lem1067803 {A B : Type'} (sum' : type1333 A B) : term64 A B sum'.
Proof. exact (fun h0 : sum' = (term65 A B) => @lem1067801 A B sum' h0). Qed.
Lemma lem1067804 {A B : Type'} : term66 A B.
Proof. exact (@lem1067803 A B (term65 A B)). Qed.
Lemma lem1067805 {A B : Type'} : term57 A B.
Proof. exact (@lem1067804 A B (@lem1067802 A B)). Qed.
