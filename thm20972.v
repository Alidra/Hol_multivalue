Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20972_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem20949 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem20950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem20951 : term0 = (or False).
Proof. exact (MK_COMB (@lem20950) (@lem20949)). Qed.
Lemma lem20952 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem20953 (b : Prop) : (term1 b) = (term2 b).
Proof. exact (MK_COMB (@lem20951) (@lem20952 b)). Qed.
Lemma lem20955 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem20956 (b : Prop) : (term2 b) = (~ b).
Proof. exact (@lem20955 (~ b)). Qed.
Lemma lem20957 (b : Prop) : (term1 b) = (~ b).
Proof. exact (TRANS (@lem20953 b) (@lem20956 b)). Qed.
Lemma lem20958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20959 (b : Prop) : (term3 b) = (term4 b).
Proof. exact (MK_COMB (@lem20958) (@lem20957 b)). Qed.
Lemma lem20961 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem20962 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem20961 b). Qed.
Lemma lem20963 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem20964 (b : Prop) : (term5 b) = (~ b).
Proof. exact (MK_COMB (@lem20963) (@lem20962 b)). Qed.
Lemma lem20965 (b : Prop) : ((term1 b) = (term5 b)) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem20959 b) (@lem20964 b)). Qed.
Lemma lem20967 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem20968 (x : Prop) : (x = x) = True.
Proof. exact (@lem20967 Prop x). Qed.
Lemma lem20969 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem20968 (~ b)). Qed.
Lemma lem20970 (b : Prop) : ((term1 b) = (term5 b)) = True.
Proof. exact (TRANS (@lem20965 b) (@lem20969 b)). Qed.
Lemma lem20971 (b : Prop) : True = ((term1 b) = (term5 b)).
Proof. exact (SYM (@lem20970 b)). Qed.
Lemma lem20972 (b : Prop) : (term1 b) = (term5 b).
Proof. exact (EQ_MP (@lem20971 b) (@lem0)). Qed.
