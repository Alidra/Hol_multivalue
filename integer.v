Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import integer_term_abbrevs.
Lemma lem2259314 : integer = term0.
Proof. exact (@integer_def). Qed.
Lemma lem2259315 (_28588 : real) : _28588 = _28588.
Proof. exact (eq_refl _28588). Qed.
Lemma lem2259316 (_28588 : real) : (integer _28588) = (term1 _28588).
Proof. exact (MK_COMB (@lem2259314) (@lem2259315 _28588)). Qed.
Lemma lem2259317 (_28588 : real) : (term1 _28588) = (term2 _28588).
Proof. exact (eq_refl (term1 _28588)). Qed.
Lemma lem2259318 (_28588 : real) : (integer _28588) = (term2 _28588).
Proof. exact (TRANS (@lem2259316 _28588) (@lem2259317 _28588)). Qed.
Lemma lem2259319 : term3.
Proof. exact (fun _28588 : real => @lem2259318 _28588). Qed.
Lemma lem2259320 (_28588 : real) : term4 _28588.
Proof. exact (@lem2259319 _28588). Qed.
Lemma lem2259321 (_28588 : real) : (term4 _28588) = ((integer _28588) = (term2 _28588)).
Proof. exact (eq_refl (term4 _28588)). Qed.
Lemma lem2259322 (_28588 : real) : (integer _28588) = (term2 _28588).
Proof. exact (EQ_MP (@lem2259321 _28588) (@lem2259320 _28588)). Qed.
Lemma lem2259352 (x : real) : (integer x) = (term2 x).
Proof. exact (@lem2259322 x). Qed.
Lemma lem2259353 : term3.
Proof. exact (fun x : real => @lem2259352 x). Qed.
