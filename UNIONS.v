Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_term_abbrevs.
Lemma lem3189218 {A : Type'} : (@UNIONS A) = (term0 A).
Proof. exact (@UNIONS_def A). Qed.
Lemma lem3189219 {A : Type'} (_32763 : type686 A) : _32763 = _32763.
Proof. exact (eq_refl _32763). Qed.
Lemma lem3189220 {A : Type'} (_32763 : type686 A) : (@UNIONS A _32763) = (term1 A _32763).
Proof. exact (MK_COMB (@lem3189218 A) (@lem3189219 A _32763)). Qed.
Lemma lem3189221 {A : Type'} (_32763 : type686 A) : (term1 A _32763) = (term2 A _32763).
Proof. exact (eq_refl (term1 A _32763)). Qed.
Lemma lem3189222 {A : Type'} (_32763 : type686 A) : (@UNIONS A _32763) = (term2 A _32763).
Proof. exact (TRANS (@lem3189220 A _32763) (@lem3189221 A _32763)). Qed.
Lemma lem3189223 {A : Type'} : term3 A.
Proof. exact (fun _32763 : type686 A => @lem3189222 A _32763). Qed.
Lemma lem3189224 {A : Type'} (_32763 : type686 A) : term4 A _32763.
Proof. exact (@lem3189223 A _32763). Qed.
Lemma lem3189225 {A : Type'} (_32763 : type686 A) : (term4 A _32763) = ((@UNIONS A _32763) = (term2 A _32763)).
Proof. exact (eq_refl (term4 A _32763)). Qed.
Lemma lem3189226 {A : Type'} (_32763 : type686 A) : (@UNIONS A _32763) = (term2 A _32763).
Proof. exact (EQ_MP (@lem3189225 A _32763) (@lem3189224 A _32763)). Qed.
Lemma lem3189256 {A : Type'} (s : type686 A) : (@UNIONS A s) = (term2 A s).
Proof. exact (@lem3189226 A s). Qed.
Lemma lem3189257 {A : Type'} : term3 A.
Proof. exact (fun s : type686 A => @lem3189256 A s). Qed.
