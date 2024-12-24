Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106571_term_abbrevs.
Require Import thm1106560_spec.
Lemma lem1106565 {_25594 : Type'} (h : _25594) : term0 _25594 h.
Proof. exact (@lem1106560 _25594 h). Qed.
Lemma lem1106566 {_25594 : Type'} (h : _25594) : (term0 _25594 h) = (term1 _25594 h).
Proof. exact (eq_refl (term0 _25594 h)). Qed.
Lemma lem1106567 {_25594 : Type'} (h : _25594) : term1 _25594 h.
Proof. exact (EQ_MP (@lem1106566 _25594 h) (@lem1106565 _25594 h)). Qed.
Lemma lem1106568 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) : term2 _25594 h P.
Proof. exact (@lem1106567 _25594 h P). Qed.
Lemma lem1106569 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) : (term2 _25594 h P) = (term3 _25594 h P).
Proof. exact (eq_refl (term2 _25594 h P)). Qed.
Lemma lem1106570 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) : term3 _25594 h P.
Proof. exact (EQ_MP (@lem1106569 _25594 h P) (@lem1106568 _25594 h P)). Qed.
Lemma lem1106571 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : term4 _25594 h P t.
Proof. exact (@lem1106570 _25594 h P t). Qed.
