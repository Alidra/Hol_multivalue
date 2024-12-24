Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import is_nadd_term_abbrevs.
Lemma lem1262576 : is_nadd = term0.
Proof. exact (@is_nadd_def). Qed.
Lemma lem1262577 (_23130 : nat -> nat) : _23130 = _23130.
Proof. exact (eq_refl _23130). Qed.
Lemma lem1262578 (_23130 : nat -> nat) : (is_nadd _23130) = (term1 _23130).
Proof. exact (MK_COMB (@lem1262576) (@lem1262577 _23130)). Qed.
Lemma lem1262579 (_23130 : nat -> nat) : (term1 _23130) = (term2 _23130).
Proof. exact (eq_refl (term1 _23130)). Qed.
Lemma lem1262580 (_23130 : nat -> nat) : (is_nadd _23130) = (term2 _23130).
Proof. exact (TRANS (@lem1262578 _23130) (@lem1262579 _23130)). Qed.
Lemma lem1262581 : term3.
Proof. exact (fun _23130 : nat -> nat => @lem1262580 _23130). Qed.
Lemma lem1262582 (_23130 : nat -> nat) : term4 _23130.
Proof. exact (@lem1262581 _23130). Qed.
Lemma lem1262583 (_23130 : nat -> nat) : (term4 _23130) = ((is_nadd _23130) = (term2 _23130)).
Proof. exact (eq_refl (term4 _23130)). Qed.
Lemma lem1262584 (_23130 : nat -> nat) : (is_nadd _23130) = (term2 _23130).
Proof. exact (EQ_MP (@lem1262583 _23130) (@lem1262582 _23130)). Qed.
Lemma lem1262614 (x : nat -> nat) : (is_nadd x) = (term2 x).
Proof. exact (@lem1262584 x). Qed.
Lemma lem1262615 : term3.
Proof. exact (fun x : nat -> nat => @lem1262614 x). Qed.
