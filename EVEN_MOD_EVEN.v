Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_MOD_EVEN_term_abbrevs.
Require Import EVEN_MOD_spec.
Require Import MOD_EVEN_2_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem204488 (n : nat) : term0 n.
Proof. exact (@lem201634 n). Qed.
Lemma lem204489 (n : nat) : (term0 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = ((term1 n) = (NUMERAL 0))).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem204491 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem204495 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((term1 n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem204489 n) (@lem204488 n)). Qed.
Lemma lem204496 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (NUMERAL 0)).
Proof. exact (@lem204495 (Nat.modulo m n)). Qed.
Lemma lem204499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem204500 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem204499) (@lem204496 m n)). Qed.
Lemma lem204502 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((term1 n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem204489 n) (@lem204488 n)). Qed.
Lemma lem204503 (m : nat) : (Coq.Arith.PeanoNat.Nat.Even m) = ((term1 m) = (NUMERAL 0)).
Proof. exact (@lem204502 m). Qed.
Lemma lem204506 (n : nat) (m : nat) : ((term2 m n) = (Coq.Arith.PeanoNat.Nat.Even m)) = (((term3 m n) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem204500 m n) (@lem204503 m)). Qed.
Lemma lem204509 (n : nat) (m : nat) : (((term3 m n) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0))) = ((term2 m n) = (Coq.Arith.PeanoNat.Nat.Even m)).
Proof. exact (SYM (@lem204506 n m)). Qed.
Lemma lem204510 (m : nat) : term6 m.
Proof. exact (@lem184261 m). Qed.
Lemma lem204511 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem204512 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem204511 m) (@lem204510 m)). Qed.
Lemma lem204513 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem204512 m n). Qed.
Lemma lem204514 (n : nat) (m : nat) : (term8 m n) = (term9 n m).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem204515 (n : nat) (m : nat) : term9 n m.
Proof. exact (EQ_MP (@lem204514 n m) (@lem204513 m n)). Qed.
Lemma lem204516 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem204517 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term3 m n) = (term1 m).
Proof. exact (@lem204515 n m (@lem204516 n h1)). Qed.
Lemma lem204523 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((Coq.Arith.PeanoNat.Nat.Even n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem204530 (n : nat) (m : nat) : term9 n m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem204517 m n h0). Qed.
Lemma lem204532 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (EQ_MP (@lem204523 n) (@lem204491 n h1)). Qed.
Lemma lem204533 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : True = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (SYM (@lem204532 n h1)). Qed.
Lemma lem204534 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem204533 n h1) (@lem0)). Qed.
Lemma lem204535 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term3 m n) = (term1 m).
Proof. exact (@lem204530 n m (@lem204534 n h1)). Qed.
Lemma lem204536 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem204537 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term10 m n) = (term11 m).
Proof. exact (MK_COMB (@lem204536) (@lem204535 m n h1)). Qed.
Lemma lem204538 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem204539 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term3 m n) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem204537 m n h1) (@lem204538)). Qed.
Lemma lem204542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem204543 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term5 m n) = (term12 m).
Proof. exact (MK_COMB (@lem204542) (@lem204539 m n h1)). Qed.
Lemma lem204548 (m : nat) : ((term1 m) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term1 m) = (NUMERAL 0))). Qed.
Lemma lem204549 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (((term3 m n) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0))) = (((term1 m) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem204543 m n h1) (@lem204548 m)). Qed.
Lemma lem204551 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem204552 (x : Prop) : (x = x) = True.
Proof. exact (@lem204551 Prop x). Qed.
Lemma lem204553 (m : nat) : (((term1 m) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0))) = True.
Proof. exact (@lem204552 ((term1 m) = (NUMERAL 0))). Qed.
Lemma lem204554 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (((term3 m n) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem204549 m n h1) (@lem204553 m)). Qed.
Lemma lem204555 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : True = (((term3 m n) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0))).
Proof. exact (SYM (@lem204554 m n h1)). Qed.
Lemma lem204556 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term3 m n) = (NUMERAL 0)) = ((term1 m) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem204555 m n h1) (@lem0)). Qed.
Lemma lem204557 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term2 m n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (EQ_MP (@lem204509 n m) (@lem204556 m n h1)). Qed.
Lemma lem204558 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = ((term2 m n) = (Coq.Arith.PeanoNat.Nat.Even m)).
Proof. exact (prop_ext (fun h2 : Coq.Arith.PeanoNat.Nat.Even n => @lem204557 m n h1) (fun h2 : (term2 m n) = (Coq.Arith.PeanoNat.Nat.Even m) => @lem204491 n h1)). Qed.
Lemma lem204559 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term2 m n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (EQ_MP (@lem204558 m n h1) (@lem204491 n h1)). Qed.
Lemma lem204560 (n : nat) (m : nat) : term13 n m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem204559 m n h0). Qed.
Lemma lem204565 (m : nat) : term14 m.
Proof. exact (fun n : nat => @lem204560 n m). Qed.
Lemma lem204570 : term15.
Proof. exact (fun m : nat => @lem204565 m). Qed.
