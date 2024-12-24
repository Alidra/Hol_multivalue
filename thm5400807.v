Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400807_term_abbrevs.
Require Import thm13473_spec.
Lemma lem5400790 (_474 : nat -> Prop) (_475 : Prop) (_476 : type993) (_477 : nat -> Prop) : (term0 _476 _475 _474 _477) = (term1 _474 _475 _476 _477).
Proof. exact (@lem13473 (nat -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5400791 (_474 : nat -> Prop) (_475 : Prop) (m : nat) (_477 : nat -> Prop) : (term2 m _475 _474 _477) = (term3 _474 _475 m _477).
Proof. exact (@lem5400790 _474 _475 (term4 m) _477). Qed.
Lemma lem5400792 (m : nat) : (term5 m) = (term6 m).
Proof. exact (@lem5400791 term7 (m = (NUMERAL 0)) m (@EMPTY nat)). Qed.
Lemma lem5400793 (m : nat) : (term8 m) = ((term9 m) = (@EMPTY nat)).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem5400794 (m : nat) : (term10 m) = (term10 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem5400795 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem5400794 m) (@lem5400793 m)). Qed.
Lemma lem5400796 (m : nat) : (term13 m) = ((term9 m) = term7).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem5400797 (m : nat) : (term14 m) = (term14 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem5400798 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem5400797 m) (@lem5400796 m)). Qed.
Lemma lem5400799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5400800 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem5400799) (@lem5400798 m)). Qed.
Lemma lem5400801 (m : nat) : (term6 m) = (term19 m).
Proof. exact (MK_COMB (@lem5400800 m) (@lem5400795 m)). Qed.
Lemma lem5400802 (m : nat) : (term5 m) = ((term9 m) = (term20 m)).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem5400803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5400804 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem5400803) (@lem5400802 m)). Qed.
Lemma lem5400805 (m : nat) : ((term5 m) = (term6 m)) = (((term9 m) = (term20 m)) = (term19 m)).
Proof. exact (MK_COMB (@lem5400804 m) (@lem5400801 m)). Qed.
Lemma lem5400806 (m : nat) : ((term9 m) = (term20 m)) = (term19 m).
Proof. exact (EQ_MP (@lem5400805 m) (@lem5400792 m)). Qed.
Lemma lem5400807 (m : nat) : (term19 m) = ((term9 m) = (term20 m)).
Proof. exact (SYM (@lem5400806 m)). Qed.
