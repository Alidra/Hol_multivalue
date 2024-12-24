Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import vector_term_abbrevs.
Lemma lem8001275 {A N : Type'} : (@vector A N) = (term0 A N).
Proof. exact (@vector_def A N). Qed.
Lemma lem8001276 {A : Type'} (_105592 : list A) : _105592 = _105592.
Proof. exact (eq_refl _105592). Qed.
Lemma lem8001277 {A N : Type'} (_105592 : list A) : (@vector A N _105592) = (term1 A N _105592).
Proof. exact (MK_COMB (@lem8001275 A N) (@lem8001276 A _105592)). Qed.
Lemma lem8001278 {A N : Type'} (_105592 : list A) : (term1 A N _105592) = (term2 A N _105592).
Proof. exact (eq_refl (term1 A N _105592)). Qed.
Lemma lem8001279 {A N : Type'} (_105592 : list A) : (@vector A N _105592) = (term2 A N _105592).
Proof. exact (TRANS (@lem8001277 A N _105592) (@lem8001278 A N _105592)). Qed.
Lemma lem8001280 {A N : Type'} : term3 A N.
Proof. exact (fun _105592 : list A => @lem8001279 A N _105592). Qed.
Lemma lem8001281 {A N : Type'} (_105592 : list A) : term4 A N _105592.
Proof. exact (@lem8001280 A N _105592). Qed.
Lemma lem8001282 {A N : Type'} (_105592 : list A) : (term4 A N _105592) = ((@vector A N _105592) = (term2 A N _105592)).
Proof. exact (eq_refl (term4 A N _105592)). Qed.
Lemma lem8001283 {A N : Type'} (_105592 : list A) : (@vector A N _105592) = (term2 A N _105592).
Proof. exact (EQ_MP (@lem8001282 A N _105592) (@lem8001281 A N _105592)). Qed.
Lemma lem8001313 {A N : Type'} (l : list A) : (@vector A N l) = (term2 A N l).
Proof. exact (@lem8001283 A N l). Qed.
Lemma lem8001314 {A N : Type'} : term3 A N.
Proof. exact (fun l : list A => @lem8001313 A N l). Qed.
