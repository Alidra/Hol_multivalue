Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367839_term_abbrevs.
Require Import REAL_OF_NUM_POW_spec.
Require Import REAL_POW_NEG_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1367780 (x : real) : term0 x.
Proof. exact (@lem1362863 x). Qed.
Lemma lem1367781 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1367782 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1367781 x) (@lem1367780 x)). Qed.
Lemma lem1367783 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem1367782 x n). Qed.
Lemma lem1367784 (x : real) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem1367786 (x : nat) : term5 x.
Proof. exact (@lem1362595 x). Qed.
Lemma lem1367787 (x : nat) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1367788 (x : nat) : term6 x.
Proof. exact (EQ_MP (@lem1367787 x) (@lem1367786 x)). Qed.
Lemma lem1367789 (x : nat) (n : nat) : term7 x n.
Proof. exact (@lem1367788 x n). Qed.
Lemma lem1367790 (x : nat) (n : nat) : (term7 x n) = ((term8 x n) = (term9 x n)).
Proof. exact (eq_refl (term7 x n)). Qed.
Lemma lem1367797 (x : nat) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (EQ_MP (@lem1367790 x n) (@lem1367789 x n)). Qed.
Lemma lem1367798 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367799 (x : nat) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (MK_COMB (@lem1367798) (@lem1367797 x n)). Qed.
Lemma lem1367800 (x : nat) (n : nat) : (term9 x n) = (term9 x n).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem1367801 (x : nat) (n : nat) : ((term8 x n) = (term9 x n)) = ((term9 x n) = (term9 x n)).
Proof. exact (MK_COMB (@lem1367799 x n) (@lem1367800 x n)). Qed.
Lemma lem1367803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367804 (x : real) : (x = x) = True.
Proof. exact (@lem1367803 real x). Qed.
Lemma lem1367805 (x : nat) (n : nat) : ((term9 x n) = (term9 x n)) = True.
Proof. exact (@lem1367804 (term9 x n)). Qed.
Lemma lem1367806 (x : nat) (n : nat) : ((term8 x n) = (term9 x n)) = True.
Proof. exact (TRANS (@lem1367801 x n) (@lem1367805 x n)). Qed.
Lemma lem1367807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367808 (x : nat) (n : nat) : (term12 x n) = (and True).
Proof. exact (MK_COMB (@lem1367807) (@lem1367806 x n)). Qed.
Lemma lem1367812 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem1367784 x n) (@lem1367783 x n)). Qed.
Lemma lem1367813 (x : nat) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (@lem1367812 (real_of_num x) n). Qed.
Lemma lem1367815 (x : nat) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (EQ_MP (@lem1367790 x n) (@lem1367789 x n)). Qed.
Lemma lem1367816 (n : nat) : (term15 n) = (term15 n).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem1367817 (x : nat) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem1367816 n) (@lem1367815 x n)). Qed.
Lemma lem1367819 (x : nat) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (EQ_MP (@lem1367790 x n) (@lem1367789 x n)). Qed.
Lemma lem1367820 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1367821 (x : nat) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem1367820) (@lem1367819 x n)). Qed.
Lemma lem1367822 (x : nat) (n : nat) : (term14 x n) = (term20 x n).
Proof. exact (MK_COMB (@lem1367817 x n) (@lem1367821 x n)). Qed.
Lemma lem1367823 (x : nat) (n : nat) : (term13 x n) = (term20 x n).
Proof. exact (TRANS (@lem1367813 x n) (@lem1367822 x n)). Qed.
Lemma lem1367824 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367825 (x : nat) (n : nat) : (term21 x n) = (term22 x n).
Proof. exact (MK_COMB (@lem1367824) (@lem1367823 x n)). Qed.
Lemma lem1367826 (x : nat) (n : nat) : (term20 x n) = (term20 x n).
Proof. exact (eq_refl (term20 x n)). Qed.
Lemma lem1367827 (x : nat) (n : nat) : ((term13 x n) = (term20 x n)) = ((term20 x n) = (term20 x n)).
Proof. exact (MK_COMB (@lem1367825 x n) (@lem1367826 x n)). Qed.
Lemma lem1367829 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367830 (x : real) : (x = x) = True.
Proof. exact (@lem1367829 real x). Qed.
Lemma lem1367831 (x : nat) (n : nat) : ((term20 x n) = (term20 x n)) = True.
Proof. exact (@lem1367830 (term20 x n)). Qed.
Lemma lem1367832 (x : nat) (n : nat) : ((term13 x n) = (term20 x n)) = True.
Proof. exact (TRANS (@lem1367827 x n) (@lem1367831 x n)). Qed.
Lemma lem1367833 (x : nat) (n : nat) : (term23 x n) = (True /\ True).
Proof. exact (MK_COMB (@lem1367808 x n) (@lem1367832 x n)). Qed.
Lemma lem1367835 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367836 : (True /\ True) = True.
Proof. exact (@lem1367835 True). Qed.
Lemma lem1367837 (x : nat) (n : nat) : (term23 x n) = True.
Proof. exact (TRANS (@lem1367833 x n) (@lem1367836)). Qed.
Lemma lem1367838 (x : nat) (n : nat) : True = (term23 x n).
Proof. exact (SYM (@lem1367837 x n)). Qed.
Lemma lem1367839 (x : nat) (n : nat) : term23 x n.
Proof. exact (EQ_MP (@lem1367838 x n) (@lem0)). Qed.
