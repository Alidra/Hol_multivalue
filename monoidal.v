Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import monoidal_term_abbrevs.
Lemma lem5712763 {A : Type'} : (@monoidal A) = (term0 A).
Proof. exact (@monoidal_def A). Qed.
Lemma lem5712764 {A : Type'} (_71609 : type1400 A) : _71609 = _71609.
Proof. exact (eq_refl _71609). Qed.
Lemma lem5712765 {A : Type'} (_71609 : type1400 A) : (@monoidal A _71609) = (term1 A _71609).
Proof. exact (MK_COMB (@lem5712763 A) (@lem5712764 A _71609)). Qed.
Lemma lem5712766 {A : Type'} (_71609 : type1400 A) : (term1 A _71609) = (term2 A _71609).
Proof. exact (eq_refl (term1 A _71609)). Qed.
Lemma lem5712767 {A : Type'} (_71609 : type1400 A) : (@monoidal A _71609) = (term2 A _71609).
Proof. exact (TRANS (@lem5712765 A _71609) (@lem5712766 A _71609)). Qed.
Lemma lem5712768 {A : Type'} : term3 A.
Proof. exact (fun _71609 : type1400 A => @lem5712767 A _71609). Qed.
Lemma lem5712769 {A : Type'} (_71609 : type1400 A) : term4 A _71609.
Proof. exact (@lem5712768 A _71609). Qed.
Lemma lem5712770 {A : Type'} (_71609 : type1400 A) : (term4 A _71609) = ((@monoidal A _71609) = (term2 A _71609)).
Proof. exact (eq_refl (term4 A _71609)). Qed.
Lemma lem5712771 {A : Type'} (_71609 : type1400 A) : (@monoidal A _71609) = (term2 A _71609).
Proof. exact (EQ_MP (@lem5712770 A _71609) (@lem5712769 A _71609)). Qed.
Lemma lem5712801 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term2 A op).
Proof. exact (@lem5712771 A op). Qed.
Lemma lem5712802 {A : Type'} : term3 A.
Proof. exact (fun op : type1400 A => @lem5712801 A op). Qed.
