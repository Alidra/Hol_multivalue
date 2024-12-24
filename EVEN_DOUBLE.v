Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_DOUBLE_term_abbrevs.
Require Import BIT0_THM_spec.
Require Import BIT1_THM_spec.
Require Import EVEN_ADD_spec.
Require Import EVEN_MULT_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem128322 (m : nat) : term0 m.
Proof. exact (@lem125496 m). Qed.
Lemma lem128323 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem128324 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem128323 m) (@lem128322 m)). Qed.
Lemma lem128325 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem128324 m n). Qed.
Lemma lem128326 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem128333 (n : nat) : term4 n.
Proof. exact (@lem80210 n). Qed.
Lemma lem128334 (n : nat) : (term4 n) = ((term5 n) = (term6 n)).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem128336 (n : nat) : term7 n.
Proof. exact (@lem80165 n). Qed.
Lemma lem128337 (n : nat) : (term7 n) = ((term8 n) = (term9 n)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem128339 (m : nat) : term10 m.
Proof. exact (@lem126076 m). Qed.
Lemma lem128340 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem128341 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem128340 m) (@lem128339 m)). Qed.
Lemma lem128342 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem128341 m n). Qed.
Lemma lem128343 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem128346 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem128343 m n) (@lem128342 m n)). Qed.
Lemma lem128347 (n : nat) : (term15 n) = (term16 n).
Proof. exact (@lem128346 term17 n). Qed.
Lemma lem128350 (n : nat) : (term16 n) = (term15 n).
Proof. exact (SYM (@lem128347 n)). Qed.
Lemma lem128352 (n : nat) : (term8 n) = (term9 n).
Proof. exact (EQ_MP (@lem128337 n) (@lem128336 n)). Qed.
Lemma lem128353 : term17 = term18.
Proof. exact (@lem128352 (BIT1 0)). Qed.
Lemma lem128355 (n : nat) : (term5 n) = (term6 n).
Proof. exact (EQ_MP (@lem128334 n) (@lem128333 n)). Qed.
Lemma lem128356 : term19 = term20.
Proof. exact (@lem128355 0). Qed.
Lemma lem128357 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem128358 : term21 = term22.
Proof. exact (MK_COMB (@lem128357) (@lem128356)). Qed.
Lemma lem128360 (n : nat) : (term5 n) = (term6 n).
Proof. exact (EQ_MP (@lem128334 n) (@lem128333 n)). Qed.
Lemma lem128361 : term19 = term20.
Proof. exact (@lem128360 0). Qed.
Lemma lem128362 : term18 = term23.
Proof. exact (MK_COMB (@lem128358) (@lem128361)). Qed.
Lemma lem128363 : term17 = term23.
Proof. exact (TRANS (@lem128353) (@lem128362)). Qed.
Lemma lem128364 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem128365 : term24 = term25.
Proof. exact (MK_COMB (@lem128364) (@lem128363)). Qed.
Lemma lem128366 : term25 = term24.
Proof. exact (SYM (@lem128365)). Qed.
Lemma lem128368 (m : nat) (n : nat) : (term3 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem128326 m n) (@lem128325 m n)). Qed.
Lemma lem128369 : term25 = (term26 = term26).
Proof. exact (@lem128368 term20 term20). Qed.
Lemma lem128371 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem128372 (x : Prop) : (x = x) = True.
Proof. exact (@lem128371 Prop x). Qed.
Lemma lem128373 : (term26 = term26) = True.
Proof. exact (@lem128372 term26). Qed.
Lemma lem128374 : term25 = True.
Proof. exact (TRANS (@lem128369) (@lem128373)). Qed.
Lemma lem128375 : True = term25.
Proof. exact (SYM (@lem128374)). Qed.
Lemma lem128376 : term25.
Proof. exact (EQ_MP (@lem128375) (@lem0)). Qed.
Lemma lem128377 : term24.
Proof. exact (EQ_MP (@lem128366) (@lem128376)). Qed.
Lemma lem128378 (n : nat) : term16 n.
Proof. exact (or_intro1 (@lem128377) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem128379 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem128350 n) (@lem128378 n)). Qed.
Lemma lem128384 : term27.
Proof. exact (fun n : nat => @lem128379 n). Qed.
