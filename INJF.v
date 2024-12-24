Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJF_term_abbrevs.
Lemma lem1056405 {A : Type'} : (@INJF A) = (term0 A).
Proof. exact (@INJF_def A). Qed.
Lemma lem1056406 {A : Type'} (_17386 : type1600 A) : _17386 = _17386.
Proof. exact (eq_refl _17386). Qed.
Lemma lem1056407 {A : Type'} (_17386 : type1600 A) : (@INJF A _17386) = (term1 A _17386).
Proof. exact (MK_COMB (@lem1056405 A) (@lem1056406 A _17386)). Qed.
Lemma lem1056408 {A : Type'} (_17386 : type1600 A) : (term1 A _17386) = (term2 A _17386).
Proof. exact (eq_refl (term1 A _17386)). Qed.
Lemma lem1056409 {A : Type'} (_17386 : type1600 A) : (@INJF A _17386) = (term2 A _17386).
Proof. exact (TRANS (@lem1056407 A _17386) (@lem1056408 A _17386)). Qed.
Lemma lem1056410 {A : Type'} : term3 A.
Proof. exact (fun _17386 : type1600 A => @lem1056409 A _17386). Qed.
Lemma lem1056411 {A : Type'} (_17386 : type1600 A) : term4 A _17386.
Proof. exact (@lem1056410 A _17386). Qed.
Lemma lem1056412 {A : Type'} (_17386 : type1600 A) : (term4 A _17386) = ((@INJF A _17386) = (term2 A _17386)).
Proof. exact (eq_refl (term4 A _17386)). Qed.
Lemma lem1056413 {A : Type'} (_17386 : type1600 A) : (@INJF A _17386) = (term2 A _17386).
Proof. exact (EQ_MP (@lem1056412 A _17386) (@lem1056411 A _17386)). Qed.
Lemma lem1056443 {A : Type'} (f : type1600 A) : (@INJF A f) = (term2 A f).
Proof. exact (@lem1056413 A f). Qed.
Lemma lem1056444 {A : Type'} : term3 A.
Proof. exact (fun f : type1600 A => @lem1056443 A f). Qed.
