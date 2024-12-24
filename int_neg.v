Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_neg_term_abbrevs.
Lemma lem2272623 : int_neg = term0.
Proof. exact (@int_neg_def). Qed.
Lemma lem2272624 (_28667 : int) : _28667 = _28667.
Proof. exact (eq_refl _28667). Qed.
Lemma lem2272625 (_28667 : int) : (int_neg _28667) = (term1 _28667).
Proof. exact (MK_COMB (@lem2272623) (@lem2272624 _28667)). Qed.
Lemma lem2272626 (_28667 : int) : (term1 _28667) = (term2 _28667).
Proof. exact (eq_refl (term1 _28667)). Qed.
Lemma lem2272627 (_28667 : int) : (int_neg _28667) = (term2 _28667).
Proof. exact (TRANS (@lem2272625 _28667) (@lem2272626 _28667)). Qed.
Lemma lem2272628 : term3.
Proof. exact (fun _28667 : int => @lem2272627 _28667). Qed.
Lemma lem2272629 (_28667 : int) : term4 _28667.
Proof. exact (@lem2272628 _28667). Qed.
Lemma lem2272630 (_28667 : int) : (term4 _28667) = ((int_neg _28667) = (term2 _28667)).
Proof. exact (eq_refl (term4 _28667)). Qed.
Lemma lem2272631 (_28667 : int) : (int_neg _28667) = (term2 _28667).
Proof. exact (EQ_MP (@lem2272630 _28667) (@lem2272629 _28667)). Qed.
Lemma lem2272661 (i : int) : (int_neg i) = (term2 i).
Proof. exact (@lem2272631 i). Qed.
Lemma lem2272662 : term3.
Proof. exact (fun i : int => @lem2272661 i). Qed.
