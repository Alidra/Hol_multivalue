Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_MOD_THM_term_abbrevs.
Require Import EXISTS_LT_MOD_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem245820 (P : nat -> Prop) : term0 P.
Proof. exact (@lem245819 P). Qed.
Lemma lem245821 (P : nat -> Prop) : (term0 P) = (term1 P).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem245822 (P : nat -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem245821 P) (@lem245820 P)). Qed.
Lemma lem245823 (P : nat -> Prop) (n : nat) : term2 P n.
Proof. exact (@lem245822 P n). Qed.
Lemma lem245824 (P : nat -> Prop) (n : nat) : (term2 P n) = ((term3 n P) = (term4 P n)).
Proof. exact (eq_refl (term2 P n)). Qed.
Lemma lem245837 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term5 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem245838 (p : Prop) (q : Prop) (p' : Prop) : term6 p q p'.
Proof. exact (fun q' : Prop => @lem245837 p q p' q'). Qed.
Lemma lem245839 (p : Prop) (q : Prop) : term7 p q.
Proof. exact (fun p' : Prop => @lem245838 p q p'). Qed.
Lemma lem245840 (n : nat) (P : nat -> Prop) : term8 n P.
Proof. exact (@lem245839 (term9 n) ((term10 P n) = (term3 n P))). Qed.
Lemma lem245841 (n : nat) (P : nat -> Prop) (p' : Prop) : term11 n P p'.
Proof. exact (@lem245840 n P p'). Qed.
Lemma lem245842 (n : nat) (P : nat -> Prop) (p' : Prop) : (term11 n P p') = (term12 n P p').
Proof. exact (eq_refl (term11 n P p')). Qed.
Lemma lem245843 (n : nat) (P : nat -> Prop) (p' : Prop) : term12 n P p'.
Proof. exact (EQ_MP (@lem245842 n P p') (@lem245841 n P p')). Qed.
Lemma lem245844 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term13 n P p' q'.
Proof. exact (@lem245843 n P p' q'). Qed.
Lemma lem245845 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : (term13 n P p' q') = (term14 n P p' q').
Proof. exact (eq_refl (term13 n P p' q')). Qed.
Lemma lem245846 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term14 n P p' q'.
Proof. exact (EQ_MP (@lem245845 n P p' q') (@lem245844 n P p' q')). Qed.
Lemma lem245849 (n : nat) : (term9 n) = (term9 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem245850 (P : nat -> Prop) (n : nat) (q' : Prop) : term15 P n q'.
Proof. exact (@lem245846 n P (term9 n) q'). Qed.
Lemma lem245851 (P : nat -> Prop) (n : nat) (q' : Prop) : term16 P n q'.
Proof. exact (@lem245850 P n q' (@lem245849 n)). Qed.
Lemma lem245852 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem245853 (n : nat) : term17 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem245873 (P : nat -> Prop) (n : nat) : (term3 n P) = (term4 P n).
Proof. exact (EQ_MP (@lem245824 P n) (@lem245823 P n)). Qed.
Lemma lem245877 (n : nat) (h1 : term9 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem245853 n (@lem245852 n h1)). Qed.
Lemma lem245878 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem245879 (n : nat) (h1 : term9 n) : (term9 n) = (~ False).
Proof. exact (MK_COMB (@lem245878) (@lem245877 n h1)). Qed.
Lemma lem245881 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem245882 (n : nat) (h1 : term9 n) : (term9 n) = True.
Proof. exact (TRANS (@lem245879 n h1) (@lem245881)). Qed.
Lemma lem245883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem245884 (n : nat) (h1 : term9 n) : (term18 n) = (and True).
Proof. exact (MK_COMB (@lem245883) (@lem245882 n h1)). Qed.
Lemma lem245889 (P : nat -> Prop) (n : nat) : (term10 P n) = (term10 P n).
Proof. exact (eq_refl (term10 P n)). Qed.
Lemma lem245890 (P : nat -> Prop) (n : nat) (h1 : term9 n) : (term4 P n) = (term19 P n).
Proof. exact (MK_COMB (@lem245884 n h1) (@lem245889 P n)). Qed.
Lemma lem245892 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem245893 (P : nat -> Prop) (n : nat) : (term19 P n) = (term10 P n).
Proof. exact (@lem245892 (term10 P n)). Qed.
Lemma lem245898 (P : nat -> Prop) (n : nat) (h1 : term9 n) : (term4 P n) = (term10 P n).
Proof. exact (TRANS (@lem245890 P n h1) (@lem245893 P n)). Qed.
Lemma lem245899 (P : nat -> Prop) (n : nat) (h1 : term9 n) : (term3 n P) = (term10 P n).
Proof. exact (TRANS (@lem245873 P n) (@lem245898 P n h1)). Qed.
Lemma lem245900 (P : nat -> Prop) (n : nat) : (term20 P n) = (term20 P n).
Proof. exact (eq_refl (term20 P n)). Qed.
Lemma lem245901 (P : nat -> Prop) (n : nat) (h1 : term9 n) : ((term10 P n) = (term3 n P)) = ((term10 P n) = (term10 P n)).
Proof. exact (MK_COMB (@lem245900 P n) (@lem245899 P n h1)). Qed.
Lemma lem245903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem245904 (x : Prop) : (x = x) = True.
Proof. exact (@lem245903 Prop x). Qed.
Lemma lem245905 (P : nat -> Prop) (n : nat) : ((term10 P n) = (term10 P n)) = True.
Proof. exact (@lem245904 (term10 P n)). Qed.
Lemma lem245906 (P : nat -> Prop) (n : nat) (h1 : term9 n) : ((term10 P n) = (term3 n P)) = True.
Proof. exact (TRANS (@lem245901 P n h1) (@lem245905 P n)). Qed.
Lemma lem245907 (n : nat) (P : nat -> Prop) : term21 n P.
Proof. exact (fun h0 : term9 n => @lem245906 P n h0). Qed.
Lemma lem245908 (P : nat -> Prop) (n : nat) : term22 P n.
Proof. exact (@lem245851 P n True). Qed.
Lemma lem245909 (P : nat -> Prop) (n : nat) : (term23 n P) = (term24 n).
Proof. exact (@lem245908 P n (@lem245907 n P)). Qed.
Lemma lem245911 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem245912 (n : nat) : (term24 n) = True.
Proof. exact (@lem245911 (term9 n)). Qed.
Lemma lem245913 (n : nat) (P : nat -> Prop) : (term23 n P) = True.
Proof. exact (TRANS (@lem245909 P n) (@lem245912 n)). Qed.
Lemma lem245914 (P : nat -> Prop) : (term25 P) = term26.
Proof. exact (fun_ext (fun n : nat => @lem245913 n P)). Qed.
Lemma lem245915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem245916 (P : nat -> Prop) : (term27 P) = term28.
Proof. exact (MK_COMB (@lem245915) (@lem245914 P)). Qed.
Lemma lem245918 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem245919 (t : Prop) : (term30 t) = t.
Proof. exact (@lem245918 nat t). Qed.
Lemma lem245920 : term28 = True.
Proof. exact (@lem245919 True). Qed.
Lemma lem245921 (P : nat -> Prop) : (term27 P) = True.
Proof. exact (TRANS (@lem245916 P) (@lem245920)). Qed.
Lemma lem245922 : term31 = term32.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem245921 P)). Qed.
Lemma lem245923 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem245924 : term33 = term34.
Proof. exact (MK_COMB (@lem245923) (@lem245922)). Qed.
Lemma lem245926 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem245927 (t : Prop) : (term35 t) = t.
Proof. exact (@lem245926 (nat -> Prop) t). Qed.
Lemma lem245928 : term34 = True.
Proof. exact (@lem245927 True). Qed.
Lemma lem245929 : term33 = True.
Proof. exact (TRANS (@lem245924) (@lem245928)). Qed.
Lemma lem245930 : True = term33.
Proof. exact (SYM (@lem245929)). Qed.
Lemma lem245931 : term33.
Proof. exact (EQ_MP (@lem245930) (@lem0)). Qed.
