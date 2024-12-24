Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import o_DEF_term_abbrevs.
Lemma lem15387 {A B C : Type'} : (@o A B C) = (term0 A B C).
Proof. exact (@o_def A B C). Qed.
Lemma lem15388 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem15389 {A B C : Type'} (f : B -> C) : (@o A B C f) = (term1 A B C f).
Proof. exact (MK_COMB (@lem15387 A B C) (@lem15388 B C f)). Qed.
Lemma lem15390 {A B C : Type'} (f : B -> C) : (term1 A B C f) = (term2 A B C f).
Proof. exact (eq_refl (term1 A B C f)). Qed.
Lemma lem15391 {A B C : Type'} (f : B -> C) : (@o A B C f) = (term2 A B C f).
Proof. exact (TRANS (@lem15389 A B C f) (@lem15390 A B C f)). Qed.
Lemma lem15392 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem15393 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (MK_COMB (@lem15391 A B C f) (@lem15392 A B g)). Qed.
Lemma lem15394 {A B C : Type'} (f : B -> C) (g : A -> B) : (term3 A B C f g) = (term4 A B C f g).
Proof. exact (eq_refl (term3 A B C f g)). Qed.
Lemma lem15395 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term4 A B C f g).
Proof. exact (TRANS (@lem15393 A B C f g) (@lem15394 A B C f g)). Qed.
Lemma lem15396 {A B C : Type'} (f : B -> C) : term5 A B C f.
Proof. exact (fun g : A -> B => @lem15395 A B C f g). Qed.
Lemma lem15397 {A B C : Type'} : term6 A B C.
Proof. exact (fun f : B -> C => @lem15396 A B C f). Qed.
