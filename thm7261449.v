Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261449_term_abbrevs.
Require Import thm7261440_spec.
Lemma lem7261443 {_137613 : Type'} (f : _137613 -> real) : term0 _137613 f.
Proof. exact (@lem7261440 _137613 f). Qed.
Lemma lem7261444 {_137613 : Type'} (f : _137613 -> real) : (term0 _137613 f) = (term1 _137613 f).
Proof. exact (eq_refl (term0 _137613 f)). Qed.
Lemma lem7261445 {_137613 : Type'} (f : _137613 -> real) : term1 _137613 f.
Proof. exact (EQ_MP (@lem7261444 _137613 f) (@lem7261443 _137613 f)). Qed.
Lemma lem7261446 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) : term2 _137613 f g.
Proof. exact (@lem7261445 _137613 f g). Qed.
Lemma lem7261447 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) : (term2 _137613 f g) = (term3 _137613 f g).
Proof. exact (eq_refl (term2 _137613 f g)). Qed.
Lemma lem7261448 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) : term3 _137613 f g.
Proof. exact (EQ_MP (@lem7261447 _137613 f g) (@lem7261446 _137613 f g)). Qed.
Lemma lem7261449 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (s : _137613 -> Prop) : term4 _137613 f g s.
Proof. exact (@lem7261448 _137613 f g s). Qed.
