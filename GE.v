Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import GE_term_abbrevs.
Lemma lem90165 : Peano.ge = term0.
Proof. exact (@ge_def). Qed.
Lemma lem90166 (_2249 : nat) : _2249 = _2249.
Proof. exact (eq_refl _2249). Qed.
Lemma lem90167 (_2249 : nat) : (Peano.ge _2249) = (term1 _2249).
Proof. exact (MK_COMB (@lem90165) (@lem90166 _2249)). Qed.
Lemma lem90168 (_2249 : nat) : (term1 _2249) = (term2 _2249).
Proof. exact (eq_refl (term1 _2249)). Qed.
Lemma lem90169 (_2249 : nat) : (Peano.ge _2249) = (term2 _2249).
Proof. exact (TRANS (@lem90167 _2249) (@lem90168 _2249)). Qed.
Lemma lem90170 (_2250 : nat) : _2250 = _2250.
Proof. exact (eq_refl _2250). Qed.
Lemma lem90171 (_2249 : nat) (_2250 : nat) : (Peano.ge _2249 _2250) = (term3 _2249 _2250).
Proof. exact (MK_COMB (@lem90169 _2249) (@lem90170 _2250)). Qed.
Lemma lem90172 (_2250 : nat) (_2249 : nat) : (term3 _2249 _2250) = (Peano.le _2250 _2249).
Proof. exact (eq_refl (term3 _2249 _2250)). Qed.
Lemma lem90173 (_2250 : nat) (_2249 : nat) : (Peano.ge _2249 _2250) = (Peano.le _2250 _2249).
Proof. exact (TRANS (@lem90171 _2249 _2250) (@lem90172 _2250 _2249)). Qed.
Lemma lem90174 (_2249 : nat) : term4 _2249.
Proof. exact (fun _2250 : nat => @lem90173 _2250 _2249). Qed.
Lemma lem90175 : term5.
Proof. exact (fun _2249 : nat => @lem90174 _2249). Qed.
Lemma lem90176 (_2249 : nat) : term6 _2249.
Proof. exact (@lem90175 _2249). Qed.
Lemma lem90177 (_2249 : nat) : (term6 _2249) = (term4 _2249).
Proof. exact (eq_refl (term6 _2249)). Qed.
Lemma lem90178 (_2249 : nat) : term4 _2249.
Proof. exact (EQ_MP (@lem90177 _2249) (@lem90176 _2249)). Qed.
Lemma lem90179 (_2249 : nat) (_2250 : nat) : term7 _2249 _2250.
Proof. exact (@lem90178 _2249 _2250). Qed.
Lemma lem90180 (_2250 : nat) (_2249 : nat) : (term7 _2249 _2250) = ((Peano.ge _2249 _2250) = (Peano.le _2250 _2249)).
Proof. exact (eq_refl (term7 _2249 _2250)). Qed.
Lemma lem90181 (_2250 : nat) (_2249 : nat) : (Peano.ge _2249 _2250) = (Peano.le _2250 _2249).
Proof. exact (EQ_MP (@lem90180 _2250 _2249) (@lem90179 _2249 _2250)). Qed.
Lemma lem90224 (n : nat) (m : nat) : (Peano.ge m n) = (Peano.le n m).
Proof. exact (@lem90181 n m). Qed.
Lemma lem90225 (n : nat) : term8 n.
Proof. exact (fun m : nat => @lem90224 n m). Qed.
Lemma lem90226 : term9.
Proof. exact (fun n : nat => @lem90225 n). Qed.
