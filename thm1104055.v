Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1104055_term_abbrevs.
Require Import thm1104038_spec.
Lemma lem1104046 {_25409 _25416 : Type'} (h1' : _25409) : term0 _25409 _25416 h1'.
Proof. exact (@lem1104038 _25409 _25416 h1'). Qed.
Lemma lem1104047 {_25409 _25416 : Type'} (h1' : _25409) : (term0 _25409 _25416 h1') = (term1 _25409 _25416 h1').
Proof. exact (eq_refl (term0 _25409 _25416 h1')). Qed.
Lemma lem1104048 {_25409 _25416 : Type'} (h1' : _25409) : term1 _25409 _25416 h1'.
Proof. exact (EQ_MP (@lem1104047 _25409 _25416 h1') (@lem1104046 _25409 _25416 h1')). Qed.
Lemma lem1104049 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) : term2 _25409 _25416 h1' P.
Proof. exact (@lem1104048 _25409 _25416 h1' P). Qed.
Lemma lem1104050 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) : (term2 _25409 _25416 h1' P) = (term3 _25409 _25416 h1' P).
Proof. exact (eq_refl (term2 _25409 _25416 h1' P)). Qed.
Lemma lem1104051 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) : term3 _25409 _25416 h1' P.
Proof. exact (EQ_MP (@lem1104050 _25409 _25416 h1' P) (@lem1104049 _25409 _25416 h1' P)). Qed.
Lemma lem1104052 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) : term4 _25409 _25416 h1' P t1.
Proof. exact (@lem1104051 _25409 _25416 h1' P t1). Qed.
Lemma lem1104053 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) : (term4 _25409 _25416 h1' P t1) = (term5 _25409 _25416 h1' P t1).
Proof. exact (eq_refl (term4 _25409 _25416 h1' P t1)). Qed.
Lemma lem1104054 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) : term5 _25409 _25416 h1' P t1.
Proof. exact (EQ_MP (@lem1104053 _25409 _25416 h1' P t1) (@lem1104052 _25409 _25416 h1' P t1)). Qed.
Lemma lem1104055 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : term6 _25409 _25416 h1' P t1 l2.
Proof. exact (@lem1104054 _25409 _25416 h1' P t1 l2). Qed.
