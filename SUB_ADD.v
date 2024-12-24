Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_ADD_term_abbrevs.
Require Import ADD_SUB_spec.
Require Import ADD_SYM_spec.
Require Import LE_EXISTS_spec.
Lemma lem136357 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem136358 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem136359 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem136358 m) (@lem136357 m)). Qed.
Lemma lem136360 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem136359 m n). Qed.
Lemma lem136361 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem136374 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem136361 n m) (@lem136360 m n)). Qed.
Lemma lem136375 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem136376 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (MK_COMB (@lem136375) (@lem136374 n m)). Qed.
Lemma lem136377 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem136378 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem136376 n m) (@lem136377 n)). Qed.
Lemma lem136379 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136380 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem136379) (@lem136378 m n)). Qed.
Lemma lem136381 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem136382 (n : nat) (m : nat) : ((term4 m n) = m) = ((term5 m n) = m).
Proof. exact (MK_COMB (@lem136380 m n) (@lem136381 m)). Qed.
Lemma lem136383 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem136382 n m)). Qed.
Lemma lem136384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136385 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem136384) (@lem136383 m)). Qed.
Lemma lem136386 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem136385 m)). Qed.
Lemma lem136387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136388 : term14 = term15.
Proof. exact (MK_COMB (@lem136387) (@lem136386)). Qed.
Lemma lem136389 : term15.
Proof. exact (EQ_MP (@lem136388) (@lem135886)). Qed.
Lemma lem136390 (m : nat) : term16 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem136391 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem136392 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem136391 m) (@lem136390 m)). Qed.
Lemma lem136393 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem136392 m n). Qed.
Lemma lem136394 (n : nat) (m : nat) : (term18 m n) = ((Peano.le m n) = (term19 n m)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem136407 (n : nat) (m : nat) : (Peano.le m n) = (term19 n m).
Proof. exact (EQ_MP (@lem136394 n m) (@lem136393 m n)). Qed.
Lemma lem136408 (m : nat) (n : nat) : (Peano.le n m) = (term19 m n).
Proof. exact (@lem136407 m n). Qed.
Lemma lem136415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem136416 (m : nat) (n : nat) : (term20 n m) = (term21 m n).
Proof. exact (MK_COMB (@lem136415) (@lem136408 m n)). Qed.
Lemma lem136419 (n : nat) (m : nat) : ((term22 m n) = m) = ((term22 m n) = m).
Proof. exact (eq_refl ((term22 m n) = m)). Qed.
Lemma lem136420 (n : nat) (m : nat) : (term23 n m) = (term24 n m).
Proof. exact (MK_COMB (@lem136416 m n) (@lem136419 n m)). Qed.
Lemma lem136423 (m : nat) : (term25 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem136420 n m)). Qed.
Lemma lem136424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136425 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem136424) (@lem136423 m)). Qed.
Lemma lem136430 : term29 = term30.
Proof. exact (fun_ext (fun m : nat => @lem136425 m)). Qed.
Lemma lem136431 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136432 : term31 = term32.
Proof. exact (MK_COMB (@lem136431) (@lem136430)). Qed.
Lemma lem136437 : term32 = term31.
Proof. exact (SYM (@lem136432)). Qed.
Lemma lem136438 (m : nat) (n : nat) (h1 : term19 m n) : term19 m n.
Proof. exact (h1). Qed.
Lemma lem136439 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem136440 (m : nat) : term33 m.
Proof. exact (@lem136389 m). Qed.
Lemma lem136441 (m : nat) : (term33 m) = (term11 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem136442 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem136441 m) (@lem136440 m)). Qed.
Lemma lem136443 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem136442 m n). Qed.
Lemma lem136444 (n : nat) (m : nat) : (term34 m n) = ((term5 m n) = m).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem136449 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem136450 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem136451 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (Nat.sub m) = (term3 n d).
Proof. exact (MK_COMB (@lem136450) (@lem136449 m n d h1)). Qed.
Lemma lem136452 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem136453 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (Nat.sub m n) = (term5 d n).
Proof. exact (MK_COMB (@lem136451 m n d h1) (@lem136452 n)). Qed.
Lemma lem136455 (n : nat) (m : nat) : (term5 m n) = m.
Proof. exact (EQ_MP (@lem136444 n m) (@lem136443 m n)). Qed.
Lemma lem136456 (n : nat) (d : nat) : (term5 d n) = d.
Proof. exact (@lem136455 n d). Qed.
Lemma lem136457 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (Nat.sub m n) = d.
Proof. exact (TRANS (@lem136453 m n d h1) (@lem136456 n d)). Qed.
Lemma lem136458 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem136459 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term35 m n) = (Nat.add d).
Proof. exact (MK_COMB (@lem136458) (@lem136457 m n d h1)). Qed.
Lemma lem136460 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem136461 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term22 m n) = (Nat.add d n).
Proof. exact (MK_COMB (@lem136459 m n d h1) (@lem136460 n)). Qed.
Lemma lem136462 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136463 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term36 m n) = (term37 d n).
Proof. exact (MK_COMB (@lem136462) (@lem136461 m n d h1)). Qed.
Lemma lem136465 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem136466 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((term22 m n) = m) = ((Nat.add d n) = (Nat.add n d)).
Proof. exact (MK_COMB (@lem136463 m n d h1) (@lem136465 m n d h1)). Qed.
Lemma lem136469 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((Nat.add d n) = (Nat.add n d)) = ((term22 m n) = m).
Proof. exact (SYM (@lem136466 m n d h1)). Qed.
Lemma lem136470 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem136471 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem136472 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem136471 m) (@lem136470 m)). Qed.
Lemma lem136473 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem136472 m n). Qed.
Lemma lem136474 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem136477 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem136474 n m) (@lem136473 m n)). Qed.
Lemma lem136478 (n : nat) (d : nat) : (Nat.add d n) = (Nat.add n d).
Proof. exact (@lem136477 n d). Qed.
Lemma lem136479 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term22 m n) = m.
Proof. exact (EQ_MP (@lem136469 m n d h1) (@lem136478 n d)). Qed.
Lemma lem136480 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (m = (Nat.add n d)) = ((term22 m n) = m).
Proof. exact (prop_ext (fun h2 : m = (Nat.add n d) => @lem136479 m n d h1) (fun h2 : (term22 m n) = m => @lem136439 m n d h1)). Qed.
Lemma lem136481 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term22 m n) = m.
Proof. exact (EQ_MP (@lem136480 m n d h1) (@lem136439 m n d h1)). Qed.
Lemma lem136482 (m : nat) (n : nat) (h1 : term19 m n) : (term22 m n) = m.
Proof. exact (ex_elim (@lem136438 m n h1) (fun d : nat => fun h0 : term38 m n d => @lem136481 m n d h0)). Qed.
Lemma lem136483 (n : nat) (m : nat) : term24 n m.
Proof. exact (fun h0 : term19 m n => @lem136482 m n h0). Qed.
Lemma lem136488 (m : nat) : term28 m.
Proof. exact (fun n : nat => @lem136483 n m). Qed.
Lemma lem136493 : term32.
Proof. exact (fun m : nat => @lem136488 m). Qed.
Lemma lem136494 : term31.
Proof. exact (EQ_MP (@lem136437) (@lem136493)). Qed.
