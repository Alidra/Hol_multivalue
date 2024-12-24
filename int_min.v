Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_min_term_abbrevs.
Lemma lem2293098 : int_min = term0.
Proof. exact (@int_min_def). Qed.
Lemma lem2293099 (_28829 : int) : _28829 = _28829.
Proof. exact (eq_refl _28829). Qed.
Lemma lem2293100 (_28829 : int) : (int_min _28829) = (term1 _28829).
Proof. exact (MK_COMB (@lem2293098) (@lem2293099 _28829)). Qed.
Lemma lem2293101 (_28829 : int) : (term1 _28829) = (term2 _28829).
Proof. exact (eq_refl (term1 _28829)). Qed.
Lemma lem2293102 (_28829 : int) : (int_min _28829) = (term2 _28829).
Proof. exact (TRANS (@lem2293100 _28829) (@lem2293101 _28829)). Qed.
Lemma lem2293103 (_28830 : int) : _28830 = _28830.
Proof. exact (eq_refl _28830). Qed.
Lemma lem2293104 (_28829 : int) (_28830 : int) : (int_min _28829 _28830) = (term3 _28829 _28830).
Proof. exact (MK_COMB (@lem2293102 _28829) (@lem2293103 _28830)). Qed.
Lemma lem2293105 (_28829 : int) (_28830 : int) : (term3 _28829 _28830) = (term4 _28829 _28830).
Proof. exact (eq_refl (term3 _28829 _28830)). Qed.
Lemma lem2293106 (_28829 : int) (_28830 : int) : (int_min _28829 _28830) = (term4 _28829 _28830).
Proof. exact (TRANS (@lem2293104 _28829 _28830) (@lem2293105 _28829 _28830)). Qed.
Lemma lem2293107 (_28829 : int) : term5 _28829.
Proof. exact (fun _28830 : int => @lem2293106 _28829 _28830). Qed.
Lemma lem2293108 : term6.
Proof. exact (fun _28829 : int => @lem2293107 _28829). Qed.
Lemma lem2293109 (_28829 : int) : term7 _28829.
Proof. exact (@lem2293108 _28829). Qed.
Lemma lem2293110 (_28829 : int) : (term7 _28829) = (term5 _28829).
Proof. exact (eq_refl (term7 _28829)). Qed.
Lemma lem2293111 (_28829 : int) : term5 _28829.
Proof. exact (EQ_MP (@lem2293110 _28829) (@lem2293109 _28829)). Qed.
Lemma lem2293112 (_28829 : int) (_28830 : int) : term8 _28829 _28830.
Proof. exact (@lem2293111 _28829 _28830). Qed.
Lemma lem2293113 (_28829 : int) (_28830 : int) : (term8 _28829 _28830) = ((int_min _28829 _28830) = (term4 _28829 _28830)).
Proof. exact (eq_refl (term8 _28829 _28830)). Qed.
Lemma lem2293114 (_28829 : int) (_28830 : int) : (int_min _28829 _28830) = (term4 _28829 _28830).
Proof. exact (EQ_MP (@lem2293113 _28829 _28830) (@lem2293112 _28829 _28830)). Qed.
Lemma lem2293157 (x : int) (y : int) : (int_min x y) = (term4 x y).
Proof. exact (@lem2293114 x y). Qed.
Lemma lem2293158 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2293157 x y). Qed.
Lemma lem2293159 : term6.
Proof. exact (fun x : int => @lem2293158 x). Qed.
