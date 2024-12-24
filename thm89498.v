Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm89498_term_abbrevs.
Require Import thm89268_spec.
Require Import thm89447_spec.
Lemma lem89448 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem89449 : term1.
Proof. exact (EQ_MP (@lem89448) (@lem89268)). Qed.
Lemma lem89450 : term2.
Proof. exact (@lem89449 term3). Qed.
Lemma lem89451 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem89452 : term4.
Proof. exact (EQ_MP (@lem89451) (@lem89450)). Qed.
Lemma lem89453 (h1 : Peano.le = term5) : Peano.le = term5.
Proof. exact (h1). Qed.
Lemma lem89454 (h1 : Peano.le = term5) : term5 = Peano.le.
Proof. exact (SYM (@lem89453 h1)). Qed.
Lemma lem89455 (h1 : term5 = Peano.le) : term5 = Peano.le.
Proof. exact (h1). Qed.
Lemma lem89456 (h1 : term5 = Peano.le) : Peano.le = term5.
Proof. exact (SYM (@lem89455 h1)). Qed.
Lemma lem89457 : (Peano.le = term5) = (term5 = Peano.le).
Proof. exact (prop_ext (fun h1 : Peano.le = term5 => @lem89454 h1) (fun h1 : term5 = Peano.le => @lem89456 h1)). Qed.
Lemma lem89460 : term5 = Peano.le.
Proof. exact (EQ_MP (@lem89457) (@lem89447)). Qed.
Lemma lem89461 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89462 (m : nat) : (term6 m) = (Peano.le m).
Proof. exact (MK_COMB (@lem89460) (@lem89461 m)). Qed.
Lemma lem89463 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem89464 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem89462 m) (@lem89463)). Qed.
Lemma lem89465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89466 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem89465) (@lem89464 m)). Qed.
Lemma lem89467 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem89468 (m : nat) : ((term7 m) = (m = (NUMERAL 0))) = ((term8 m) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem89466 m) (@lem89467 m)). Qed.
Lemma lem89469 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem89468 m)). Qed.
Lemma lem89470 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89471 : term13 = term14.
Proof. exact (MK_COMB (@lem89470) (@lem89469)). Qed.
Lemma lem89472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem89473 : term15 = term16.
Proof. exact (MK_COMB (@lem89472) (@lem89471)). Qed.
Lemma lem89475 : term5 = Peano.le.
Proof. exact (EQ_MP (@lem89457) (@lem89447)). Qed.
Lemma lem89476 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89477 (m : nat) : (term6 m) = (Peano.le m).
Proof. exact (MK_COMB (@lem89475) (@lem89476 m)). Qed.
Lemma lem89478 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem89479 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem89477 m) (@lem89478 n)). Qed.
Lemma lem89480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89481 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem89480) (@lem89479 m n)). Qed.
Lemma lem89483 : term5 = Peano.le.
Proof. exact (EQ_MP (@lem89457) (@lem89447)). Qed.
Lemma lem89484 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89485 (m : nat) : (term6 m) = (Peano.le m).
Proof. exact (MK_COMB (@lem89483) (@lem89484 m)). Qed.
Lemma lem89486 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89487 (m : nat) (n : nat) : (term21 m n) = (Peano.le m n).
Proof. exact (MK_COMB (@lem89485 m) (@lem89486 n)). Qed.
Lemma lem89488 (m : nat) (n : nat) : (term22 m n) = (term22 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem89489 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem89488 m n) (@lem89487 m n)). Qed.
Lemma lem89490 (m : nat) (n : nat) : ((term17 m n) = (term23 m n)) = ((term18 m n) = (term24 m n)).
Proof. exact (MK_COMB (@lem89481 m n) (@lem89489 m n)). Qed.
Lemma lem89491 (m : nat) : (term25 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem89490 m n)). Qed.
Lemma lem89492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89493 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem89492) (@lem89491 m)). Qed.
Lemma lem89494 : term29 = term30.
Proof. exact (fun_ext (fun m : nat => @lem89493 m)). Qed.
Lemma lem89495 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89496 : term31 = term32.
Proof. exact (MK_COMB (@lem89495) (@lem89494)). Qed.
Lemma lem89497 : term4 = term33.
Proof. exact (MK_COMB (@lem89473) (@lem89496)). Qed.
Lemma lem89498 : term33.
Proof. exact (EQ_MP (@lem89497) (@lem89452)). Qed.
