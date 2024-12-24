Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import nadd_rinv_term_abbrevs.
Lemma lem1300934 : nadd_rinv = term0.
Proof. exact (@nadd_rinv_def). Qed.
Lemma lem1300935 (_23335 : nadd) : _23335 = _23335.
Proof. exact (eq_refl _23335). Qed.
Lemma lem1300936 (_23335 : nadd) : (nadd_rinv _23335) = (term1 _23335).
Proof. exact (MK_COMB (@lem1300934) (@lem1300935 _23335)). Qed.
Lemma lem1300937 (_23335 : nadd) : (term1 _23335) = (term2 _23335).
Proof. exact (eq_refl (term1 _23335)). Qed.
Lemma lem1300938 (_23335 : nadd) : (nadd_rinv _23335) = (term2 _23335).
Proof. exact (TRANS (@lem1300936 _23335) (@lem1300937 _23335)). Qed.
Lemma lem1300939 : term3.
Proof. exact (fun _23335 : nadd => @lem1300938 _23335). Qed.
Lemma lem1300940 (_23335 : nadd) : term4 _23335.
Proof. exact (@lem1300939 _23335). Qed.
Lemma lem1300941 (_23335 : nadd) : (term4 _23335) = ((nadd_rinv _23335) = (term2 _23335)).
Proof. exact (eq_refl (term4 _23335)). Qed.
Lemma lem1300942 (_23335 : nadd) : (nadd_rinv _23335) = (term2 _23335).
Proof. exact (EQ_MP (@lem1300941 _23335) (@lem1300940 _23335)). Qed.
Lemma lem1300972 (x : nadd) : (nadd_rinv x) = (term2 x).
Proof. exact (@lem1300942 x). Qed.
Lemma lem1300973 : term3.
Proof. exact (fun x : nadd => @lem1300972 x). Qed.
