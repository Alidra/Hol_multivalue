Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MIN_term_abbrevs.
Lemma lem90900 : Nat.min = term0.
Proof. exact (@MIN_def). Qed.
Lemma lem90901 (_2285 : nat) : _2285 = _2285.
Proof. exact (eq_refl _2285). Qed.
Lemma lem90902 (_2285 : nat) : (Nat.min _2285) = (term1 _2285).
Proof. exact (MK_COMB (@lem90900) (@lem90901 _2285)). Qed.
Lemma lem90903 (_2285 : nat) : (term1 _2285) = (term2 _2285).
Proof. exact (eq_refl (term1 _2285)). Qed.
Lemma lem90904 (_2285 : nat) : (Nat.min _2285) = (term2 _2285).
Proof. exact (TRANS (@lem90902 _2285) (@lem90903 _2285)). Qed.
Lemma lem90905 (_2286 : nat) : _2286 = _2286.
Proof. exact (eq_refl _2286). Qed.
Lemma lem90906 (_2285 : nat) (_2286 : nat) : (Nat.min _2285 _2286) = (term3 _2285 _2286).
Proof. exact (MK_COMB (@lem90904 _2285) (@lem90905 _2286)). Qed.
Lemma lem90907 (_2285 : nat) (_2286 : nat) : (term3 _2285 _2286) = (term4 _2285 _2286).
Proof. exact (eq_refl (term3 _2285 _2286)). Qed.
Lemma lem90908 (_2285 : nat) (_2286 : nat) : (Nat.min _2285 _2286) = (term4 _2285 _2286).
Proof. exact (TRANS (@lem90906 _2285 _2286) (@lem90907 _2285 _2286)). Qed.
Lemma lem90909 (_2285 : nat) : term5 _2285.
Proof. exact (fun _2286 : nat => @lem90908 _2285 _2286). Qed.
Lemma lem90910 : term6.
Proof. exact (fun _2285 : nat => @lem90909 _2285). Qed.
Lemma lem90911 (_2285 : nat) : term7 _2285.
Proof. exact (@lem90910 _2285). Qed.
Lemma lem90912 (_2285 : nat) : (term7 _2285) = (term5 _2285).
Proof. exact (eq_refl (term7 _2285)). Qed.
Lemma lem90913 (_2285 : nat) : term5 _2285.
Proof. exact (EQ_MP (@lem90912 _2285) (@lem90911 _2285)). Qed.
Lemma lem90914 (_2285 : nat) (_2286 : nat) : term8 _2285 _2286.
Proof. exact (@lem90913 _2285 _2286). Qed.
Lemma lem90915 (_2285 : nat) (_2286 : nat) : (term8 _2285 _2286) = ((Nat.min _2285 _2286) = (term4 _2285 _2286)).
Proof. exact (eq_refl (term8 _2285 _2286)). Qed.
Lemma lem90916 (_2285 : nat) (_2286 : nat) : (Nat.min _2285 _2286) = (term4 _2285 _2286).
Proof. exact (EQ_MP (@lem90915 _2285 _2286) (@lem90914 _2285 _2286)). Qed.
Lemma lem90959 (m : nat) (n : nat) : (Nat.min m n) = (term4 m n).
Proof. exact (@lem90916 m n). Qed.
Lemma lem90960 (m : nat) : term5 m.
Proof. exact (fun n : nat => @lem90959 m n). Qed.
Lemma lem90961 : term6.
Proof. exact (fun m : nat => @lem90960 m). Qed.
