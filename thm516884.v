Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516884_term_abbrevs.
Require Import LE_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem516865 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516866 : (NUMERAL 0) = 0.
Proof. exact (@lem516865 0). Qed.
Lemma lem516867 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem516868 (m : nat) : (term0 m) = (Peano.le m 0).
Proof. exact (MK_COMB (@lem516867 m) (@lem516866)). Qed.
Lemma lem516869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem516870 (m : nat) : (term1 m) = (term2 m).
Proof. exact (MK_COMB (@lem516869) (@lem516868 m)). Qed.
Lemma lem516872 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516873 : (NUMERAL 0) = 0.
Proof. exact (@lem516872 0). Qed.
Lemma lem516874 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem516875 (m : nat) : (m = (NUMERAL 0)) = (m = 0).
Proof. exact (MK_COMB (@lem516874 m) (@lem516873)). Qed.
Lemma lem516876 (m : nat) : ((term0 m) = (m = (NUMERAL 0))) = ((Peano.le m 0) = (m = 0)).
Proof. exact (MK_COMB (@lem516870 m) (@lem516875 m)). Qed.
Lemma lem516877 : term3 = term4.
Proof. exact (fun_ext (fun m : nat => @lem516876 m)). Qed.
Lemma lem516878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516879 : term5 = term6.
Proof. exact (MK_COMB (@lem516878) (@lem516877)). Qed.
Lemma lem516880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516881 : term7 = term8.
Proof. exact (MK_COMB (@lem516880) (@lem516879)). Qed.
Lemma lem516882 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem516883 : term10 = term11.
Proof. exact (MK_COMB (@lem516881) (@lem516882)). Qed.
Lemma lem516884 : term11.
Proof. exact (EQ_MP (@lem516883) (@lem89501)). Qed.
