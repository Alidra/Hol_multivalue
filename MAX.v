Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAX_term_abbrevs.
Lemma lem90647 : Nat.max = term0.
Proof. exact (@MAX_def). Qed.
Lemma lem90648 (_2273 : nat) : _2273 = _2273.
Proof. exact (eq_refl _2273). Qed.
Lemma lem90649 (_2273 : nat) : (Nat.max _2273) = (term1 _2273).
Proof. exact (MK_COMB (@lem90647) (@lem90648 _2273)). Qed.
Lemma lem90650 (_2273 : nat) : (term1 _2273) = (term2 _2273).
Proof. exact (eq_refl (term1 _2273)). Qed.
Lemma lem90651 (_2273 : nat) : (Nat.max _2273) = (term2 _2273).
Proof. exact (TRANS (@lem90649 _2273) (@lem90650 _2273)). Qed.
Lemma lem90652 (_2274 : nat) : _2274 = _2274.
Proof. exact (eq_refl _2274). Qed.
Lemma lem90653 (_2273 : nat) (_2274 : nat) : (Nat.max _2273 _2274) = (term3 _2273 _2274).
Proof. exact (MK_COMB (@lem90651 _2273) (@lem90652 _2274)). Qed.
Lemma lem90654 (_2274 : nat) (_2273 : nat) : (term3 _2273 _2274) = (term4 _2274 _2273).
Proof. exact (eq_refl (term3 _2273 _2274)). Qed.
Lemma lem90655 (_2274 : nat) (_2273 : nat) : (Nat.max _2273 _2274) = (term4 _2274 _2273).
Proof. exact (TRANS (@lem90653 _2273 _2274) (@lem90654 _2274 _2273)). Qed.
Lemma lem90656 (_2273 : nat) : term5 _2273.
Proof. exact (fun _2274 : nat => @lem90655 _2274 _2273). Qed.
Lemma lem90657 : term6.
Proof. exact (fun _2273 : nat => @lem90656 _2273). Qed.
Lemma lem90658 (_2273 : nat) : term7 _2273.
Proof. exact (@lem90657 _2273). Qed.
Lemma lem90659 (_2273 : nat) : (term7 _2273) = (term5 _2273).
Proof. exact (eq_refl (term7 _2273)). Qed.
Lemma lem90660 (_2273 : nat) : term5 _2273.
Proof. exact (EQ_MP (@lem90659 _2273) (@lem90658 _2273)). Qed.
Lemma lem90661 (_2273 : nat) (_2274 : nat) : term8 _2273 _2274.
Proof. exact (@lem90660 _2273 _2274). Qed.
Lemma lem90662 (_2274 : nat) (_2273 : nat) : (term8 _2273 _2274) = ((Nat.max _2273 _2274) = (term4 _2274 _2273)).
Proof. exact (eq_refl (term8 _2273 _2274)). Qed.
Lemma lem90663 (_2274 : nat) (_2273 : nat) : (Nat.max _2273 _2274) = (term4 _2274 _2273).
Proof. exact (EQ_MP (@lem90662 _2274 _2273) (@lem90661 _2273 _2274)). Qed.
Lemma lem90706 (n : nat) (m : nat) : (Nat.max m n) = (term4 n m).
Proof. exact (@lem90663 n m). Qed.
Lemma lem90707 (m : nat) : term5 m.
Proof. exact (fun n : nat => @lem90706 n m). Qed.
Lemma lem90708 : term6.
Proof. exact (fun m : nat => @lem90707 m). Qed.
