Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101596_term_abbrevs.
Require Import thm1101585_spec.
Lemma lem1101590 {_25328 : Type'} (h : _25328) : term0 _25328 h.
Proof. exact (@lem1101585 _25328 h). Qed.
Lemma lem1101591 {_25328 : Type'} (h : _25328) : (term0 _25328 h) = (term1 _25328 h).
Proof. exact (eq_refl (term0 _25328 h)). Qed.
Lemma lem1101592 {_25328 : Type'} (h : _25328) : term1 _25328 h.
Proof. exact (EQ_MP (@lem1101591 _25328 h) (@lem1101590 _25328 h)). Qed.
Lemma lem1101593 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) : term2 _25328 h P.
Proof. exact (@lem1101592 _25328 h P). Qed.
Lemma lem1101594 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) : (term2 _25328 h P) = (term3 _25328 h P).
Proof. exact (eq_refl (term2 _25328 h P)). Qed.
Lemma lem1101595 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) : term3 _25328 h P.
Proof. exact (EQ_MP (@lem1101594 _25328 h P) (@lem1101593 _25328 h P)). Qed.
Lemma lem1101596 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : term4 _25328 h P t.
Proof. exact (@lem1101595 _25328 h P t). Qed.
