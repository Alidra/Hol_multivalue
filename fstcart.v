Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import fstcart_term_abbrevs.
Lemma lem7633910 {A M N : Type'} : (@fstcart A M N) = (term0 A M N).
Proof. exact (@fstcart_def A M N). Qed.
Lemma lem7633911 {A M N : Type'} (_98368 : type2 A M N) : _98368 = _98368.
Proof. exact (eq_refl _98368). Qed.
Lemma lem7633912 {A M N : Type'} (_98368 : type2 A M N) : (@fstcart A M N _98368) = (term1 A M N _98368).
Proof. exact (MK_COMB (@lem7633910 A M N) (@lem7633911 A M N _98368)). Qed.
Lemma lem7633913 {A M N : Type'} (_98368 : type2 A M N) : (term1 A M N _98368) = (term2 A M N _98368).
Proof. exact (eq_refl (term1 A M N _98368)). Qed.
Lemma lem7633914 {A M N : Type'} (_98368 : type2 A M N) : (@fstcart A M N _98368) = (term2 A M N _98368).
Proof. exact (TRANS (@lem7633912 A M N _98368) (@lem7633913 A M N _98368)). Qed.
Lemma lem7633915 {A M N : Type'} : term3 A M N.
Proof. exact (fun _98368 : type2 A M N => @lem7633914 A M N _98368). Qed.
Lemma lem7633916 {A M N : Type'} (_98368 : type2 A M N) : term4 A M N _98368.
Proof. exact (@lem7633915 A M N _98368). Qed.
Lemma lem7633917 {A M N : Type'} (_98368 : type2 A M N) : (term4 A M N _98368) = ((@fstcart A M N _98368) = (term2 A M N _98368)).
Proof. exact (eq_refl (term4 A M N _98368)). Qed.
Lemma lem7633918 {A M N : Type'} (_98368 : type2 A M N) : (@fstcart A M N _98368) = (term2 A M N _98368).
Proof. exact (EQ_MP (@lem7633917 A M N _98368) (@lem7633916 A M N _98368)). Qed.
Lemma lem7633948 {A M N : Type'} (f : type2 A M N) : (@fstcart A M N f) = (term2 A M N f).
Proof. exact (@lem7633918 A M N f). Qed.
Lemma lem7633949 {A M N : Type'} : term3 A M N.
Proof. exact (fun f : type2 A M N => @lem7633948 A M N f). Qed.
