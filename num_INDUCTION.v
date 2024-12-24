Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_INDUCTION_term_abbrevs.
Require Import thm0_spec.
Require Import thm73444_spec.
Require Import thm75559_spec.
Lemma lem75572 : 0 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem75559) (@lem0)). Qed.
Lemma lem75573 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem75574 (P : nat -> Prop) : (P 0) = (term0 P).
Proof. exact (MK_COMB (@lem75573 P) (@lem75572)). Qed.
Lemma lem75575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem75576 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (MK_COMB (@lem75575) (@lem75574 P)). Qed.
Lemma lem75577 (P : nat -> Prop) : (term3 P) = (term3 P).
Proof. exact (eq_refl (term3 P)). Qed.
Lemma lem75578 (P : nat -> Prop) : (term4 P) = (term5 P).
Proof. exact (MK_COMB (@lem75576 P) (@lem75577 P)). Qed.
Lemma lem75579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem75580 (P : nat -> Prop) : (term6 P) = (term7 P).
Proof. exact (MK_COMB (@lem75579) (@lem75578 P)). Qed.
Lemma lem75581 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (eq_refl (term8 P)). Qed.
Lemma lem75582 (P : nat -> Prop) : (term9 P) = (term10 P).
Proof. exact (MK_COMB (@lem75580 P) (@lem75581 P)). Qed.
Lemma lem75583 : term11 = term12.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem75582 P)). Qed.
Lemma lem75584 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem75585 : term13 = term14.
Proof. exact (MK_COMB (@lem75584) (@lem75583)). Qed.
Lemma lem75586 : term14.
Proof. exact (EQ_MP (@lem75585) (@lem73444)). Qed.
