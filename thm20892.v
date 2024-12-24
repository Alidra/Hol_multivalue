Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20892_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20828_spec.
Lemma lem20866 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem20867 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem20866 b). Qed.
Lemma lem20868 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem20869 (b : Prop) : (term0 b) = (~ b).
Proof. exact (MK_COMB (@lem20868) (@lem20867 b)). Qed.
Lemma lem20870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20871 (b : Prop) : (term1 b) = (term2 b).
Proof. exact (MK_COMB (@lem20870) (@lem20869 b)). Qed.
Lemma lem20875 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem20876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20877 : term3 = (and True).
Proof. exact (MK_COMB (@lem20876) (@lem20875)). Qed.
Lemma lem20878 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem20879 (b : Prop) : (term4 b) = (term5 b).
Proof. exact (MK_COMB (@lem20877) (@lem20878 b)). Qed.
Lemma lem20881 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem20882 (b : Prop) : (term5 b) = (~ b).
Proof. exact (@lem20881 (~ b)). Qed.
Lemma lem20883 (b : Prop) : (term4 b) = (~ b).
Proof. exact (TRANS (@lem20879 b) (@lem20882 b)). Qed.
Lemma lem20884 (b : Prop) : ((term0 b) = (term4 b)) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem20871 b) (@lem20883 b)). Qed.
Lemma lem20886 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem20887 (x : Prop) : (x = x) = True.
Proof. exact (@lem20886 Prop x). Qed.
Lemma lem20888 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem20887 (~ b)). Qed.
Lemma lem20889 (b : Prop) : ((term0 b) = (term4 b)) = True.
Proof. exact (TRANS (@lem20884 b) (@lem20888 b)). Qed.
Lemma lem20890 (b : Prop) : True = ((term0 b) = (term4 b)).
Proof. exact (SYM (@lem20889 b)). Qed.
Lemma lem20891 (b : Prop) : (term0 b) = (term4 b).
Proof. exact (EQ_MP (@lem20890 b) (@lem0)). Qed.
Lemma lem20892 (b : Prop) (a : Prop) (h1 : a = False) : (term6 a b) = (term7 a b).
Proof. exact (EQ_MP (@lem20828 b a h1) (@lem20891 b)). Qed.
