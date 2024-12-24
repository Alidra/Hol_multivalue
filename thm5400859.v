Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400859_term_abbrevs.
Require Import thm13473_spec.
Lemma lem5400842 (_474 : nat -> Prop) (_475 : Prop) (_476 : type993) (_477 : nat -> Prop) : (term0 _476 _475 _474 _477) = (term1 _474 _475 _476 _477).
Proof. exact (@lem13473 (nat -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5400843 (_474 : nat -> Prop) (_475 : Prop) (m : nat) (n : nat) (_477 : nat -> Prop) : (term2 m n _475 _474 _477) = (term3 _474 _475 m n _477).
Proof. exact (@lem5400842 _474 _475 (term4 m n) _477). Qed.
Lemma lem5400844 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (@lem5400843 (term7 m n) (term8 m n) m n (dotdot m n)). Qed.
Lemma lem5400845 (m : nat) (n : nat) : (term9 m n) = ((term10 m n) = (dotdot m n)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem5400846 (m : nat) (n : nat) : (term11 m n) = (term11 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem5400847 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem5400846 m n) (@lem5400845 m n)). Qed.
Lemma lem5400848 (m : nat) (n : nat) : (term14 m n) = ((term10 m n) = (term7 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem5400849 (m : nat) (n : nat) : (term15 m n) = (term15 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem5400850 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem5400849 m n) (@lem5400848 m n)). Qed.
Lemma lem5400851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5400852 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem5400851) (@lem5400850 m n)). Qed.
Lemma lem5400853 (m : nat) (n : nat) : (term6 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem5400852 m n) (@lem5400847 m n)). Qed.
Lemma lem5400854 (m : nat) (n : nat) : (term5 m n) = ((term10 m n) = (term21 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem5400855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5400856 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem5400855) (@lem5400854 m n)). Qed.
Lemma lem5400857 (m : nat) (n : nat) : ((term5 m n) = (term6 m n)) = (((term10 m n) = (term21 m n)) = (term20 m n)).
Proof. exact (MK_COMB (@lem5400856 m n) (@lem5400853 m n)). Qed.
Lemma lem5400858 (m : nat) (n : nat) : ((term10 m n) = (term21 m n)) = (term20 m n).
Proof. exact (EQ_MP (@lem5400857 m n) (@lem5400844 m n)). Qed.
Lemma lem5400859 (m : nat) (n : nat) : (term20 m n) = ((term10 m n) = (term21 m n)).
Proof. exact (SYM (@lem5400858 m n)). Qed.
