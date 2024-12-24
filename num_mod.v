Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_mod_term_abbrevs.
Lemma lem2837441 : num_mod = term0.
Proof. exact (@num_mod_def). Qed.
Lemma lem2837442 (_31151 : nat) : _31151 = _31151.
Proof. exact (eq_refl _31151). Qed.
Lemma lem2837443 (_31151 : nat) : (num_mod _31151) = (term1 _31151).
Proof. exact (MK_COMB (@lem2837441) (@lem2837442 _31151)). Qed.
Lemma lem2837444 (_31151 : nat) : (term1 _31151) = (term2 _31151).
Proof. exact (eq_refl (term1 _31151)). Qed.
Lemma lem2837445 (_31151 : nat) : (num_mod _31151) = (term2 _31151).
Proof. exact (TRANS (@lem2837443 _31151) (@lem2837444 _31151)). Qed.
Lemma lem2837446 (_31152 : nat) : _31152 = _31152.
Proof. exact (eq_refl _31152). Qed.
Lemma lem2837447 (_31151 : nat) (_31152 : nat) : (num_mod _31151 _31152) = (term3 _31151 _31152).
Proof. exact (MK_COMB (@lem2837445 _31151) (@lem2837446 _31152)). Qed.
Lemma lem2837448 (_31151 : nat) (_31152 : nat) : (term3 _31151 _31152) = (term4 _31151 _31152).
Proof. exact (eq_refl (term3 _31151 _31152)). Qed.
Lemma lem2837449 (_31151 : nat) (_31152 : nat) : (num_mod _31151 _31152) = (term4 _31151 _31152).
Proof. exact (TRANS (@lem2837447 _31151 _31152) (@lem2837448 _31151 _31152)). Qed.
Lemma lem2837450 (_31153 : nat) : _31153 = _31153.
Proof. exact (eq_refl _31153). Qed.
Lemma lem2837451 (_31151 : nat) (_31152 : nat) (_31153 : nat) : (num_mod _31151 _31152 _31153) = (term5 _31151 _31152 _31153).
Proof. exact (MK_COMB (@lem2837449 _31151 _31152) (@lem2837450 _31153)). Qed.
Lemma lem2837452 (_31151 : nat) (_31152 : nat) (_31153 : nat) : (term5 _31151 _31152 _31153) = (term6 _31151 _31152 _31153).
Proof. exact (eq_refl (term5 _31151 _31152 _31153)). Qed.
Lemma lem2837453 (_31151 : nat) (_31152 : nat) (_31153 : nat) : (num_mod _31151 _31152 _31153) = (term6 _31151 _31152 _31153).
Proof. exact (TRANS (@lem2837451 _31151 _31152 _31153) (@lem2837452 _31151 _31152 _31153)). Qed.
Lemma lem2837454 (_31151 : nat) (_31152 : nat) : term7 _31151 _31152.
Proof. exact (fun _31153 : nat => @lem2837453 _31151 _31152 _31153). Qed.
Lemma lem2837455 (_31151 : nat) : term8 _31151.
Proof. exact (fun _31152 : nat => @lem2837454 _31151 _31152). Qed.
Lemma lem2837456 : term9.
Proof. exact (fun _31151 : nat => @lem2837455 _31151). Qed.
Lemma lem2837457 (_31151 : nat) : term10 _31151.
Proof. exact (@lem2837456 _31151). Qed.
Lemma lem2837458 (_31151 : nat) : (term10 _31151) = (term8 _31151).
Proof. exact (eq_refl (term10 _31151)). Qed.
Lemma lem2837459 (_31151 : nat) : term8 _31151.
Proof. exact (EQ_MP (@lem2837458 _31151) (@lem2837457 _31151)). Qed.
Lemma lem2837460 (_31151 : nat) (_31152 : nat) : term11 _31151 _31152.
Proof. exact (@lem2837459 _31151 _31152). Qed.
Lemma lem2837461 (_31151 : nat) (_31152 : nat) : (term11 _31151 _31152) = (term7 _31151 _31152).
Proof. exact (eq_refl (term11 _31151 _31152)). Qed.
Lemma lem2837462 (_31151 : nat) (_31152 : nat) : term7 _31151 _31152.
Proof. exact (EQ_MP (@lem2837461 _31151 _31152) (@lem2837460 _31151 _31152)). Qed.
Lemma lem2837463 (_31151 : nat) (_31152 : nat) (_31153 : nat) : term12 _31151 _31152 _31153.
Proof. exact (@lem2837462 _31151 _31152 _31153). Qed.
Lemma lem2837464 (_31151 : nat) (_31152 : nat) (_31153 : nat) : (term12 _31151 _31152 _31153) = ((num_mod _31151 _31152 _31153) = (term6 _31151 _31152 _31153)).
Proof. exact (eq_refl (term12 _31151 _31152 _31153)). Qed.
Lemma lem2837465 (_31151 : nat) (_31152 : nat) (_31153 : nat) : (num_mod _31151 _31152 _31153) = (term6 _31151 _31152 _31153).
Proof. exact (EQ_MP (@lem2837464 _31151 _31152 _31153) (@lem2837463 _31151 _31152 _31153)). Qed.
Lemma lem2837521 (n : nat) (x : nat) (y : nat) : (num_mod n x y) = (term6 n x y).
Proof. exact (@lem2837465 n x y). Qed.
Lemma lem2837522 (n : nat) (x : nat) : term7 n x.
Proof. exact (fun y : nat => @lem2837521 n x y). Qed.
Lemma lem2837523 (n : nat) : term8 n.
Proof. exact (fun x : nat => @lem2837522 n x). Qed.
Lemma lem2837524 : term9.
Proof. exact (fun n : nat => @lem2837523 n). Qed.
