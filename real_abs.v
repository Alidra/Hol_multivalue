Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_abs_term_abbrevs.
Lemma lem1343320 : real_abs = term0.
Proof. exact (@real_abs_def). Qed.
Lemma lem1343321 (_23947 : real) : _23947 = _23947.
Proof. exact (eq_refl _23947). Qed.
Lemma lem1343322 (_23947 : real) : (real_abs _23947) = (term1 _23947).
Proof. exact (MK_COMB (@lem1343320) (@lem1343321 _23947)). Qed.
Lemma lem1343323 (_23947 : real) : (term1 _23947) = (term2 _23947).
Proof. exact (eq_refl (term1 _23947)). Qed.
Lemma lem1343324 (_23947 : real) : (real_abs _23947) = (term2 _23947).
Proof. exact (TRANS (@lem1343322 _23947) (@lem1343323 _23947)). Qed.
Lemma lem1343325 : term3.
Proof. exact (fun _23947 : real => @lem1343324 _23947). Qed.
Lemma lem1343326 (_23947 : real) : term4 _23947.
Proof. exact (@lem1343325 _23947). Qed.
Lemma lem1343327 (_23947 : real) : (term4 _23947) = ((real_abs _23947) = (term2 _23947)).
Proof. exact (eq_refl (term4 _23947)). Qed.
Lemma lem1343328 (_23947 : real) : (real_abs _23947) = (term2 _23947).
Proof. exact (EQ_MP (@lem1343327 _23947) (@lem1343326 _23947)). Qed.
Lemma lem1343358 (x : real) : (real_abs x) = (term2 x).
Proof. exact (@lem1343328 x). Qed.
Lemma lem1343359 : term3.
Proof. exact (fun x : real => @lem1343358 x). Qed.
