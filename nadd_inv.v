Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import nadd_inv_term_abbrevs.
Lemma lem1307969 : nadd_inv = term0.
Proof. exact (@nadd_inv_def). Qed.
Lemma lem1307970 (_23349 : nadd) : _23349 = _23349.
Proof. exact (eq_refl _23349). Qed.
Lemma lem1307971 (_23349 : nadd) : (nadd_inv _23349) = (term1 _23349).
Proof. exact (MK_COMB (@lem1307969) (@lem1307970 _23349)). Qed.
Lemma lem1307972 (_23349 : nadd) : (term1 _23349) = (term2 _23349).
Proof. exact (eq_refl (term1 _23349)). Qed.
Lemma lem1307973 (_23349 : nadd) : (nadd_inv _23349) = (term2 _23349).
Proof. exact (TRANS (@lem1307971 _23349) (@lem1307972 _23349)). Qed.
Lemma lem1307974 : term3.
Proof. exact (fun _23349 : nadd => @lem1307973 _23349). Qed.
Lemma lem1307975 (_23349 : nadd) : term4 _23349.
Proof. exact (@lem1307974 _23349). Qed.
Lemma lem1307976 (_23349 : nadd) : (term4 _23349) = ((nadd_inv _23349) = (term2 _23349)).
Proof. exact (eq_refl (term4 _23349)). Qed.
Lemma lem1307977 (_23349 : nadd) : (nadd_inv _23349) = (term2 _23349).
Proof. exact (EQ_MP (@lem1307976 _23349) (@lem1307975 _23349)). Qed.
Lemma lem1308007 (x : nadd) : (nadd_inv x) = (term2 x).
Proof. exact (@lem1307977 x). Qed.
Lemma lem1308008 : term3.
Proof. exact (fun x : nadd => @lem1308007 x). Qed.
