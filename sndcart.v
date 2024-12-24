Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import sndcart_term_abbrevs.
Lemma lem7635215 {A M N : Type'} : (@sndcart A M N) = (term0 A M N).
Proof. exact (@sndcart_def A M N). Qed.
Lemma lem7635216 {A M N : Type'} (_98373 : type2 A M N) : _98373 = _98373.
Proof. exact (eq_refl _98373). Qed.
Lemma lem7635217 {A M N : Type'} (_98373 : type2 A M N) : (@sndcart A M N _98373) = (term1 A M N _98373).
Proof. exact (MK_COMB (@lem7635215 A M N) (@lem7635216 A M N _98373)). Qed.
Lemma lem7635218 {A M N : Type'} (_98373 : type2 A M N) : (term1 A M N _98373) = (term2 A M N _98373).
Proof. exact (eq_refl (term1 A M N _98373)). Qed.
Lemma lem7635219 {A M N : Type'} (_98373 : type2 A M N) : (@sndcart A M N _98373) = (term2 A M N _98373).
Proof. exact (TRANS (@lem7635217 A M N _98373) (@lem7635218 A M N _98373)). Qed.
Lemma lem7635220 {A M N : Type'} : term3 A M N.
Proof. exact (fun _98373 : type2 A M N => @lem7635219 A M N _98373). Qed.
Lemma lem7635221 {A M N : Type'} (_98373 : type2 A M N) : term4 A M N _98373.
Proof. exact (@lem7635220 A M N _98373). Qed.
Lemma lem7635222 {A M N : Type'} (_98373 : type2 A M N) : (term4 A M N _98373) = ((@sndcart A M N _98373) = (term2 A M N _98373)).
Proof. exact (eq_refl (term4 A M N _98373)). Qed.
Lemma lem7635223 {A M N : Type'} (_98373 : type2 A M N) : (@sndcart A M N _98373) = (term2 A M N _98373).
Proof. exact (EQ_MP (@lem7635222 A M N _98373) (@lem7635221 A M N _98373)). Qed.
Lemma lem7635253 {A M N : Type'} (f : type2 A M N) : (@sndcart A M N f) = (term2 A M N f).
Proof. exact (@lem7635223 A M N f). Qed.
Lemma lem7635254 {A M N : Type'} : term3 A M N.
Proof. exact (fun f : type2 A M N => @lem7635253 A M N f). Qed.
