Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1102439_term_abbrevs.
Require Import thm1102422_spec.
Lemma lem1102430 {_25350 _25351 : Type'} (h : _25351) : term0 _25350 _25351 h.
Proof. exact (@lem1102422 _25350 _25351 h). Qed.
Lemma lem1102431 {_25350 _25351 : Type'} (h : _25351) : (term0 _25350 _25351 h) = (term1 _25350 _25351 h).
Proof. exact (eq_refl (term0 _25350 _25351 h)). Qed.
Lemma lem1102432 {_25350 _25351 : Type'} (h : _25351) : term1 _25350 _25351 h.
Proof. exact (EQ_MP (@lem1102431 _25350 _25351 h) (@lem1102430 _25350 _25351 h)). Qed.
Lemma lem1102433 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) : term2 _25350 _25351 h f.
Proof. exact (@lem1102432 _25350 _25351 h f). Qed.
Lemma lem1102434 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) : (term2 _25350 _25351 h f) = (term3 _25350 _25351 h f).
Proof. exact (eq_refl (term2 _25350 _25351 h f)). Qed.
Lemma lem1102435 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) : term3 _25350 _25351 h f.
Proof. exact (EQ_MP (@lem1102434 _25350 _25351 h f) (@lem1102433 _25350 _25351 h f)). Qed.
Lemma lem1102436 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) : term4 _25350 _25351 h f t.
Proof. exact (@lem1102435 _25350 _25351 h f t). Qed.
Lemma lem1102437 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) : (term4 _25350 _25351 h f t) = (term5 _25350 _25351 h f t).
Proof. exact (eq_refl (term4 _25350 _25351 h f t)). Qed.
Lemma lem1102438 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) : term5 _25350 _25351 h f t.
Proof. exact (EQ_MP (@lem1102437 _25350 _25351 h f t) (@lem1102436 _25350 _25351 h f t)). Qed.
Lemma lem1102439 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : term6 _25350 _25351 h f t b.
Proof. exact (@lem1102438 _25350 _25351 h f t b). Qed.
