Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import pastecart_term_abbrevs.
Lemma lem7632588 {A M N : Type'} : (@pastecart A M N) = (term0 A M N).
Proof. exact (@pastecart_def A M N). Qed.
Lemma lem7632589 {A M : Type'} (_98356 : cart A M) : _98356 = _98356.
Proof. exact (eq_refl _98356). Qed.
Lemma lem7632590 {A M N : Type'} (_98356 : cart A M) : (@pastecart A M N _98356) = (term1 A M N _98356).
Proof. exact (MK_COMB (@lem7632588 A M N) (@lem7632589 A M _98356)). Qed.
Lemma lem7632591 {A M N : Type'} (_98356 : cart A M) : (term1 A M N _98356) = (term2 A M N _98356).
Proof. exact (eq_refl (term1 A M N _98356)). Qed.
Lemma lem7632592 {A M N : Type'} (_98356 : cart A M) : (@pastecart A M N _98356) = (term2 A M N _98356).
Proof. exact (TRANS (@lem7632590 A M N _98356) (@lem7632591 A M N _98356)). Qed.
Lemma lem7632593 {A N : Type'} (_98357 : cart A N) : _98357 = _98357.
Proof. exact (eq_refl _98357). Qed.
Lemma lem7632594 {A M N : Type'} (_98356 : cart A M) (_98357 : cart A N) : (@pastecart A M N _98356 _98357) = (term3 A M N _98356 _98357).
Proof. exact (MK_COMB (@lem7632592 A M N _98356) (@lem7632593 A N _98357)). Qed.
Lemma lem7632595 {A M N : Type'} (_98356 : cart A M) (_98357 : cart A N) : (term3 A M N _98356 _98357) = (term4 A M N _98356 _98357).
Proof. exact (eq_refl (term3 A M N _98356 _98357)). Qed.
Lemma lem7632596 {A M N : Type'} (_98356 : cart A M) (_98357 : cart A N) : (@pastecart A M N _98356 _98357) = (term4 A M N _98356 _98357).
Proof. exact (TRANS (@lem7632594 A M N _98356 _98357) (@lem7632595 A M N _98356 _98357)). Qed.
Lemma lem7632597 {A M N : Type'} (_98356 : cart A M) : term5 A M N _98356.
Proof. exact (fun _98357 : cart A N => @lem7632596 A M N _98356 _98357). Qed.
Lemma lem7632598 {A M N : Type'} : term6 A M N.
Proof. exact (fun _98356 : cart A M => @lem7632597 A M N _98356). Qed.
Lemma lem7632599 {A M N : Type'} (_98356 : cart A M) : term7 A M N _98356.
Proof. exact (@lem7632598 A M N _98356). Qed.
Lemma lem7632600 {A M N : Type'} (_98356 : cart A M) : (term7 A M N _98356) = (term5 A M N _98356).
Proof. exact (eq_refl (term7 A M N _98356)). Qed.
Lemma lem7632601 {A M N : Type'} (_98356 : cart A M) : term5 A M N _98356.
Proof. exact (EQ_MP (@lem7632600 A M N _98356) (@lem7632599 A M N _98356)). Qed.
Lemma lem7632602 {A M N : Type'} (_98356 : cart A M) (_98357 : cart A N) : term8 A M N _98356 _98357.
Proof. exact (@lem7632601 A M N _98356 _98357). Qed.
Lemma lem7632603 {A M N : Type'} (_98356 : cart A M) (_98357 : cart A N) : (term8 A M N _98356 _98357) = ((@pastecart A M N _98356 _98357) = (term4 A M N _98356 _98357)).
Proof. exact (eq_refl (term8 A M N _98356 _98357)). Qed.
Lemma lem7632604 {A M N : Type'} (_98356 : cart A M) (_98357 : cart A N) : (@pastecart A M N _98356 _98357) = (term4 A M N _98356 _98357).
Proof. exact (EQ_MP (@lem7632603 A M N _98356 _98357) (@lem7632602 A M N _98356 _98357)). Qed.
Lemma lem7632647 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term4 A M N f g).
Proof. exact (@lem7632604 A M N f g). Qed.
Lemma lem7632648 {A M N : Type'} (f : cart A M) : term5 A M N f.
Proof. exact (fun g : cart A N => @lem7632647 A M N f g). Qed.
Lemma lem7632649 {A M N : Type'} : term6 A M N.
Proof. exact (fun f : cart A M => @lem7632648 A M N f). Qed.
