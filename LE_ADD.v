Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import LE_REFL_spec.
Require Import thm0_spec.
Require Import thm1832_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Lemma lem100363 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem100364 (m : nat) : term1 m.
Proof. exact (@lem100363 (term2 m)). Qed.
Lemma lem100365 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem100366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem100367 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem100366) (@lem100365 m)). Qed.
Lemma lem100368 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem100369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100370 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (MK_COMB (@lem100369) (@lem100368 m n)). Qed.
Lemma lem100371 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem100372 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem100370 m n) (@lem100371 m n)). Qed.
Lemma lem100373 (m : nat) : (term15 m) = (term16 m).
Proof. exact (fun_ext (fun n : nat => @lem100372 m n)). Qed.
Lemma lem100374 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100375 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem100374) (@lem100373 m)). Qed.
Lemma lem100376 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem100367 m) (@lem100375 m)). Qed.
Lemma lem100377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100378 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem100377) (@lem100376 m)). Qed.
Lemma lem100379 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem100380 (m : nat) : (term23 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem100379 m n)). Qed.
Lemma lem100381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100382 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem100381) (@lem100380 m)). Qed.
Lemma lem100383 (m : nat) : (term1 m) = (term26 m).
Proof. exact (MK_COMB (@lem100378 m) (@lem100382 m)). Qed.
Lemma lem100384 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem100383 m) (@lem100364 m)). Qed.
Lemma lem100385 (m : nat) (n : nat) (h1 : term8 m n) : term8 m n.
Proof. exact (h1). Qed.
Lemma lem100386 (n : nat) : term27 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem100387 (n : nat) : (term27 n) = (Peano.le n n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem100388 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem100387 n) (@lem100386 n)). Qed.
Lemma lem100389 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem100391 : term28.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem100407 : term29.
Proof. exact (proj1 (@lem100391)). Qed.
Lemma lem100408 (m : nat) : term30 m.
Proof. exact (@lem100407 m). Qed.
Lemma lem100409 (m : nat) : (term30 m) = ((term31 m) = m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem100429 (m : nat) : (term31 m) = m.
Proof. exact (EQ_MP (@lem100409 m) (@lem100408 m)). Qed.
Lemma lem100430 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem100431 (m : nat) : (term4 m) = (Peano.le m m).
Proof. exact (MK_COMB (@lem100430 m) (@lem100429 m)). Qed.
Lemma lem100433 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem100389 n) (@lem100388 n)). Qed.
Lemma lem100434 (m : nat) : (Peano.le m m) = True.
Proof. exact (@lem100433 m). Qed.
Lemma lem100435 (m : nat) : (term4 m) = True.
Proof. exact (TRANS (@lem100431 m) (@lem100434 m)). Qed.
Lemma lem100436 (m : nat) : True = (term4 m).
Proof. exact (SYM (@lem100435 m)). Qed.
Lemma lem100437 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem100436 m) (@lem0)). Qed.
Lemma lem100443 : term28.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem100444 : term32.
Proof. exact (proj2 (@lem100443)). Qed.
Lemma lem100445 : term33.
Proof. exact (proj2 (@lem100444)). Qed.
Lemma lem100446 (m : nat) : term34 m.
Proof. exact (@lem100445 m). Qed.
Lemma lem100447 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem100448 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem100447 m) (@lem100446 m)). Qed.
Lemma lem100449 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem100448 m n). Qed.
Lemma lem100450 (m : nat) (n : nat) : (term36 m n) = ((term37 m n) = (term38 m n)).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem100467 : term39.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem100468 (m : nat) : term40 m.
Proof. exact (@lem100467 m). Qed.
Lemma lem100469 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem100470 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem100469 m) (@lem100468 m)). Qed.
Lemma lem100471 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem100470 m n). Qed.
Lemma lem100472 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (term44 m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem100478 (m : nat) (n : nat) : (term8 m n) = ((term8 m n) = True).
Proof. exact (@lem7 (term8 m n)). Qed.
Lemma lem100483 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (EQ_MP (@lem100450 m n) (@lem100449 m n)). Qed.
Lemma lem100484 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem100485 (m : nat) (n : nat) : (term12 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem100484 m) (@lem100483 m n)). Qed.
Lemma lem100487 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem100472 m n) (@lem100471 m n)). Qed.
Lemma lem100488 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (@lem100487 m (Nat.add m n)). Qed.
Lemma lem100494 (m : nat) (n : nat) (h1 : term8 m n) : (term8 m n) = True.
Proof. exact (EQ_MP (@lem100478 m n) (@lem100385 m n h1)). Qed.
Lemma lem100495 (m : nat) (n : nat) : (term47 m n) = (term47 m n).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem100496 (m : nat) (n : nat) (h1 : term8 m n) : (term46 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem100495 m n) (@lem100494 m n h1)). Qed.
Lemma lem100498 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem100499 (m : nat) (n : nat) : (term48 m n) = True.
Proof. exact (@lem100498 (m = (term38 m n))). Qed.
Lemma lem100500 (m : nat) (n : nat) (h1 : term8 m n) : (term46 m n) = True.
Proof. exact (TRANS (@lem100496 m n h1) (@lem100499 m n)). Qed.
Lemma lem100501 (m : nat) (n : nat) (h1 : term8 m n) : (term45 m n) = True.
Proof. exact (TRANS (@lem100488 m n) (@lem100500 m n h1)). Qed.
Lemma lem100502 (m : nat) (n : nat) (h1 : term8 m n) : (term12 m n) = True.
Proof. exact (TRANS (@lem100485 m n) (@lem100501 m n h1)). Qed.
Lemma lem100503 (m : nat) (n : nat) (h1 : term8 m n) : True = (term12 m n).
Proof. exact (SYM (@lem100502 m n h1)). Qed.
Lemma lem100504 (m : nat) (n : nat) (h1 : term8 m n) : term12 m n.
Proof. exact (EQ_MP (@lem100503 m n h1) (@lem0)). Qed.
Lemma lem100505 (m : nat) (n : nat) : term14 m n.
Proof. exact (fun h0 : term8 m n => @lem100504 m n h0). Qed.
Lemma lem100510 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem100505 m n). Qed.
Lemma lem100511 (m : nat) : term20 m.
Proof. exact (conj (@lem100437 m) (@lem100510 m)). Qed.
Lemma lem100512 (m : nat) : term25 m.
Proof. exact (@lem100384 m (@lem100511 m)). Qed.
Lemma lem100517 : term49.
Proof. exact (fun m : nat => @lem100512 m). Qed.
