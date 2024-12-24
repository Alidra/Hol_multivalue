Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LE_1_term_abbrevs.
Require Import REAL_POS_spec.
Require Import REAL_POW_LE2_spec.
Require Import REAL_POW_ONE_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1636715 (n : nat) : term0 n.
Proof. exact (@lem1636714 n). Qed.
Lemma lem1636716 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1636717 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1636716 n) (@lem1636715 n)). Qed.
Lemma lem1636718 (n : nat) : term2 n.
Proof. exact (@lem1636717 n term3). Qed.
Lemma lem1636719 (n : nat) : (term2 n) = (term4 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1636720 (n : nat) : term4 n.
Proof. exact (EQ_MP (@lem1636719 n) (@lem1636718 n)). Qed.
Lemma lem1636721 (n : nat) (x : real) : term5 n x.
Proof. exact (@lem1636720 n x). Qed.
Lemma lem1636722 (x : real) (n : nat) : (term5 n x) = (term6 x n).
Proof. exact (eq_refl (term5 n x)). Qed.
Lemma lem1636723 (x : real) (n : nat) : term6 x n.
Proof. exact (EQ_MP (@lem1636722 x n) (@lem1636721 n x)). Qed.
Lemma lem1636724 (x : real) (h1 : term7 x) : term7 x.
Proof. exact (h1). Qed.
Lemma lem1636725 (n : nat) : term8 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1636726 (n : nat) : (term8 n) = (term9 n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem1636727 (n : nat) : term9 n.
Proof. exact (EQ_MP (@lem1636726 n) (@lem1636725 n)). Qed.
Lemma lem1636728 (n : nat) : (term9 n) = ((term9 n) = True).
Proof. exact (@lem7 (term9 n)). Qed.
Lemma lem1636730 (n : nat) : term10 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem1636731 (n : nat) : (term10 n) = ((term11 n) = term3).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1636733 (x : real) : (term7 x) = ((term7 x) = True).
Proof. exact (@lem7 (term7 x)). Qed.
Lemma lem1636742 (n : nat) : (term9 n) = True.
Proof. exact (EQ_MP (@lem1636728 n) (@lem1636727 n)). Qed.
Lemma lem1636743 : term12 = True.
Proof. exact (@lem1636742 term13). Qed.
Lemma lem1636744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1636745 : term14 = (and True).
Proof. exact (MK_COMB (@lem1636744) (@lem1636743)). Qed.
Lemma lem1636747 (x : real) (h1 : term7 x) : (term7 x) = True.
Proof. exact (EQ_MP (@lem1636733 x) (@lem1636724 x h1)). Qed.
Lemma lem1636748 (x : real) (h1 : term7 x) : (term15 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1636745) (@lem1636747 x h1)). Qed.
Lemma lem1636750 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1636751 : (True /\ True) = True.
Proof. exact (@lem1636750 True). Qed.
Lemma lem1636752 (x : real) (h1 : term7 x) : (term15 x) = True.
Proof. exact (TRANS (@lem1636748 x h1) (@lem1636751)). Qed.
Lemma lem1636753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1636754 (x : real) (h1 : term7 x) : (term16 x) = (imp True).
Proof. exact (MK_COMB (@lem1636753) (@lem1636752 x h1)). Qed.
Lemma lem1636756 (n : nat) : (term11 n) = term3.
Proof. exact (EQ_MP (@lem1636731 n) (@lem1636730 n)). Qed.
Lemma lem1636757 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1636758 (n : nat) : (term17 n) = term18.
Proof. exact (MK_COMB (@lem1636757) (@lem1636756 n)). Qed.
Lemma lem1636759 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1636760 (x : real) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (MK_COMB (@lem1636758 n) (@lem1636759 x n)). Qed.
Lemma lem1636761 (n : nat) (x : real) (h1 : term7 x) : (term6 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem1636754 x h1) (@lem1636760 x n)). Qed.
Lemma lem1636763 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1636764 (x : real) (n : nat) : (term21 x n) = (term20 x n).
Proof. exact (@lem1636763 (term20 x n)). Qed.
Lemma lem1636765 (n : nat) (x : real) (h1 : term7 x) : (term6 x n) = (term20 x n).
Proof. exact (TRANS (@lem1636761 n x h1) (@lem1636764 x n)). Qed.
Lemma lem1636766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1636767 (n : nat) (x : real) (h1 : term7 x) : (term22 x n) = (term23 x n).
Proof. exact (MK_COMB (@lem1636766) (@lem1636765 n x h1)). Qed.
Lemma lem1636768 (x : real) (n : nat) : (term20 x n) = (term20 x n).
Proof. exact (eq_refl (term20 x n)). Qed.
Lemma lem1636769 (n : nat) (x : real) (h1 : term7 x) : (term24 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem1636767 n x h1) (@lem1636768 x n)). Qed.
Lemma lem1636771 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1636772 (x : real) (n : nat) : (term25 x n) = True.
Proof. exact (@lem1636771 (term20 x n)). Qed.
Lemma lem1636773 (n : nat) (x : real) (h1 : term7 x) : (term24 x n) = True.
Proof. exact (TRANS (@lem1636769 n x h1) (@lem1636772 x n)). Qed.
Lemma lem1636774 (n : nat) (x : real) (h1 : term7 x) : True = (term24 x n).
Proof. exact (SYM (@lem1636773 n x h1)). Qed.
Lemma lem1636775 (n : nat) (x : real) (h1 : term7 x) : term24 x n.
Proof. exact (EQ_MP (@lem1636774 n x h1) (@lem0)). Qed.
Lemma lem1636776 (n : nat) (x : real) (h1 : term7 x) : term20 x n.
Proof. exact (@lem1636775 n x h1 (@lem1636723 x n)). Qed.
Lemma lem1636777 (n : nat) (x : real) (h1 : term7 x) : (term7 x) = (term20 x n).
Proof. exact (prop_ext (fun h2 : term7 x => @lem1636776 n x h1) (fun h2 : term20 x n => @lem1636724 x h1)). Qed.
Lemma lem1636778 (n : nat) (x : real) (h1 : term7 x) : term20 x n.
Proof. exact (EQ_MP (@lem1636777 n x h1) (@lem1636724 x h1)). Qed.
Lemma lem1636779 (x : real) (n : nat) : term26 x n.
Proof. exact (fun h0 : term7 x => @lem1636778 n x h0). Qed.
Lemma lem1636784 (n : nat) : term27 n.
Proof. exact (fun x : real => @lem1636779 x n). Qed.
Lemma lem1636789 : term28.
Proof. exact (fun n : nat => @lem1636784 n). Qed.
