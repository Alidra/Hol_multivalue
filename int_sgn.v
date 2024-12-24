Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_sgn_term_abbrevs.
Lemma lem2288949 : int_sgn = term0.
Proof. exact (@int_sgn_def). Qed.
Lemma lem2288950 (_28751 : int) : _28751 = _28751.
Proof. exact (eq_refl _28751). Qed.
Lemma lem2288951 (_28751 : int) : (int_sgn _28751) = (term1 _28751).
Proof. exact (MK_COMB (@lem2288949) (@lem2288950 _28751)). Qed.
Lemma lem2288952 (_28751 : int) : (term1 _28751) = (term2 _28751).
Proof. exact (eq_refl (term1 _28751)). Qed.
Lemma lem2288953 (_28751 : int) : (int_sgn _28751) = (term2 _28751).
Proof. exact (TRANS (@lem2288951 _28751) (@lem2288952 _28751)). Qed.
Lemma lem2288954 : term3.
Proof. exact (fun _28751 : int => @lem2288953 _28751). Qed.
Lemma lem2288955 (_28751 : int) : term4 _28751.
Proof. exact (@lem2288954 _28751). Qed.
Lemma lem2288956 (_28751 : int) : (term4 _28751) = ((int_sgn _28751) = (term2 _28751)).
Proof. exact (eq_refl (term4 _28751)). Qed.
Lemma lem2288957 (_28751 : int) : (int_sgn _28751) = (term2 _28751).
Proof. exact (EQ_MP (@lem2288956 _28751) (@lem2288955 _28751)). Qed.
Lemma lem2288987 (x : int) : (int_sgn x) = (term2 x).
Proof. exact (@lem2288957 x). Qed.
Lemma lem2288988 : term3.
Proof. exact (fun x : int => @lem2288987 x). Qed.
