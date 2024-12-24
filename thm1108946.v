Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108946_term_abbrevs.
Require Import thm1108935_spec.
Lemma lem1108940 {_25719 _25727 : Type'} (h1' : _25719) : term0 _25719 _25727 h1'.
Proof. exact (@lem1108935 _25719 _25727 h1'). Qed.
Lemma lem1108941 {_25719 _25727 : Type'} (h1' : _25719) : (term0 _25719 _25727 h1') = (term1 _25719 _25727 h1').
Proof. exact (eq_refl (term0 _25719 _25727 h1')). Qed.
Lemma lem1108942 {_25719 _25727 : Type'} (h1' : _25719) : term1 _25719 _25727 h1'.
Proof. exact (EQ_MP (@lem1108941 _25719 _25727 h1') (@lem1108940 _25719 _25727 h1')). Qed.
Lemma lem1108943 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) : term2 _25719 _25727 h1' t1.
Proof. exact (@lem1108942 _25719 _25727 h1' t1). Qed.
Lemma lem1108944 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) : (term2 _25719 _25727 h1' t1) = (term3 _25719 _25727 h1' t1).
Proof. exact (eq_refl (term2 _25719 _25727 h1' t1)). Qed.
Lemma lem1108945 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) : term3 _25719 _25727 h1' t1.
Proof. exact (EQ_MP (@lem1108944 _25719 _25727 h1' t1) (@lem1108943 _25719 _25727 h1' t1)). Qed.
Lemma lem1108946 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : term4 _25719 _25727 h1' t1 l2.
Proof. exact (@lem1108945 _25719 _25727 h1' t1 l2). Qed.
