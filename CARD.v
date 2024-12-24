Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_term_abbrevs.
Lemma lem3840338 {_99571 : Type'} : (@CARD _99571) = (term0 _99571).
Proof. exact (@CARD_def _99571). Qed.
Lemma lem3840339 {_99571 : Type'} (_44539 : _99571 -> Prop) : _44539 = _44539.
Proof. exact (eq_refl _44539). Qed.
Lemma lem3840340 {_99571 : Type'} (_44539 : _99571 -> Prop) : (@CARD _99571 _44539) = (term1 _99571 _44539).
Proof. exact (MK_COMB (@lem3840338 _99571) (@lem3840339 _99571 _44539)). Qed.
Lemma lem3840341 {_99571 : Type'} (_44539 : _99571 -> Prop) : (term1 _99571 _44539) = (term2 _99571 _44539).
Proof. exact (eq_refl (term1 _99571 _44539)). Qed.
Lemma lem3840342 {_99571 : Type'} (_44539 : _99571 -> Prop) : (@CARD _99571 _44539) = (term2 _99571 _44539).
Proof. exact (TRANS (@lem3840340 _99571 _44539) (@lem3840341 _99571 _44539)). Qed.
Lemma lem3840343 {_99571 : Type'} : term3 _99571.
Proof. exact (fun _44539 : _99571 -> Prop => @lem3840342 _99571 _44539). Qed.
Lemma lem3840344 {_99571 : Type'} (_44539 : _99571 -> Prop) : term4 _99571 _44539.
Proof. exact (@lem3840343 _99571 _44539). Qed.
Lemma lem3840345 {_99571 : Type'} (_44539 : _99571 -> Prop) : (term4 _99571 _44539) = ((@CARD _99571 _44539) = (term2 _99571 _44539)).
Proof. exact (eq_refl (term4 _99571 _44539)). Qed.
Lemma lem3840346 {_99571 : Type'} (_44539 : _99571 -> Prop) : (@CARD _99571 _44539) = (term2 _99571 _44539).
Proof. exact (EQ_MP (@lem3840345 _99571 _44539) (@lem3840344 _99571 _44539)). Qed.
Lemma lem3840376 {_99571 : Type'} (s : _99571 -> Prop) : (@CARD _99571 s) = (term2 _99571 s).
Proof. exact (@lem3840346 _99571 s). Qed.
Lemma lem3840377 {_99571 : Type'} : term3 _99571.
Proof. exact (fun s : _99571 -> Prop => @lem3840376 _99571 s). Qed.
