Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEASURE_term_abbrevs.
Lemma lem365378 {_16406 : Type'} : (@MEASURE _16406) = (term0 _16406).
Proof. exact (@MEASURE_def _16406). Qed.
Lemma lem365379 {_16406 : Type'} (_7931 : _16406 -> nat) : _7931 = _7931.
Proof. exact (eq_refl _7931). Qed.
Lemma lem365380 {_16406 : Type'} (_7931 : _16406 -> nat) : (@MEASURE _16406 _7931) = (term1 _16406 _7931).
Proof. exact (MK_COMB (@lem365378 _16406) (@lem365379 _16406 _7931)). Qed.
Lemma lem365381 {_16406 : Type'} (_7931 : _16406 -> nat) : (term1 _16406 _7931) = (term2 _16406 _7931).
Proof. exact (eq_refl (term1 _16406 _7931)). Qed.
Lemma lem365382 {_16406 : Type'} (_7931 : _16406 -> nat) : (@MEASURE _16406 _7931) = (term2 _16406 _7931).
Proof. exact (TRANS (@lem365380 _16406 _7931) (@lem365381 _16406 _7931)). Qed.
Lemma lem365383 {_16406 : Type'} : term3 _16406.
Proof. exact (fun _7931 : _16406 -> nat => @lem365382 _16406 _7931). Qed.
Lemma lem365384 {_16406 : Type'} (_7931 : _16406 -> nat) : term4 _16406 _7931.
Proof. exact (@lem365383 _16406 _7931). Qed.
Lemma lem365385 {_16406 : Type'} (_7931 : _16406 -> nat) : (term4 _16406 _7931) = ((@MEASURE _16406 _7931) = (term2 _16406 _7931)).
Proof. exact (eq_refl (term4 _16406 _7931)). Qed.
Lemma lem365386 {_16406 : Type'} (_7931 : _16406 -> nat) : (@MEASURE _16406 _7931) = (term2 _16406 _7931).
Proof. exact (EQ_MP (@lem365385 _16406 _7931) (@lem365384 _16406 _7931)). Qed.
Lemma lem365416 {_16406 : Type'} (m : _16406 -> nat) : (@MEASURE _16406 m) = (term2 _16406 m).
Proof. exact (@lem365386 _16406 m). Qed.
Lemma lem365417 {_16406 : Type'} : term3 _16406.
Proof. exact (fun m : _16406 -> nat => @lem365416 _16406 m). Qed.
