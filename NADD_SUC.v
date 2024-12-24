Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_SUC_term_abbrevs.
Require Import ADD1_spec.
Require Import DIST_LADD_0_spec.
Require Import LE_ADD2_spec.
Require Import LE_REFL_spec.
Require Import NADD_ADDITIVE_spec.
Require Import thm0_spec.
Require Import thm1259719_spec.
Require Import thm1842_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1266354 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1266355 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1266354 h1 m). Qed.
Lemma lem1266356 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1266357 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1266356 m) (@lem1266355 m h1)). Qed.
Lemma lem1266358 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1266357 m h1 n). Qed.
Lemma lem1266359 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1266360 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem1266359 m n) (@lem1266358 m n h1)). Qed.
Lemma lem1266361 (m : nat) (n : nat) (p : nat) (h1 : term0) : term5 m n p.
Proof. exact (@lem1266360 m n h1 p). Qed.
Lemma lem1266362 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1266363 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (EQ_MP (@lem1266362 m n p) (@lem1266361 m n p h1)). Qed.
Lemma lem1266364 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term7 m n p q.
Proof. exact (@lem1266363 m n p h1 q). Qed.
Lemma lem1266365 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1266366 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (EQ_MP (@lem1266365 m n p q) (@lem1266364 m n p q h1)). Qed.
Lemma lem1266367 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term9 m p n q.
Proof. exact (h1). Qed.
Lemma lem1266368 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1266366 m n p q h1 (@lem1266367 m p n q h2)). Qed.
Lemma lem1266369 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term11 m n p q.
Proof. exact (fun h0 : term0 => @lem1266368 m p n q h0 h1). Qed.
Lemma lem1266370 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1266371 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1266369 m p n q h2 (@lem1266370 h1)). Qed.
Lemma lem1266372 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (fun h0 : term9 m p n q => @lem1266371 m p n q h1 h0). Qed.
Lemma lem1266373 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (fun q : nat => @lem1266372 m n p q h1). Qed.
Lemma lem1266374 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun p : nat => @lem1266373 m n p h1). Qed.
Lemma lem1266375 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem1266374 m n h1). Qed.
Lemma lem1266376 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem1266375 m h1). Qed.
Lemma lem1266377 : term12.
Proof. exact (fun h0 : term0 => @lem1266376 h0). Qed.
Lemma lem1266378 : term0.
Proof. exact (@lem1266377 (@lem101399)). Qed.
Lemma lem1266379 (m : nat) : term1 m.
Proof. exact (@lem1266378 m). Qed.
Lemma lem1266380 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1266381 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1266380 m) (@lem1266379 m)). Qed.
Lemma lem1266382 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1266381 m n). Qed.
Lemma lem1266383 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1266384 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1266383 m n) (@lem1266382 m n)). Qed.
Lemma lem1266385 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1266384 m n p). Qed.
Lemma lem1266386 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1266387 (m : nat) (n : nat) (p : nat) : term6 m n p.
Proof. exact (EQ_MP (@lem1266386 m n p) (@lem1266385 m n p)). Qed.
Lemma lem1266388 (m : nat) (n : nat) (p : nat) (q : nat) : term7 m n p q.
Proof. exact (@lem1266387 m n p q). Qed.
Lemma lem1266389 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1266391 (m : nat) : term13 m.
Proof. exact (@lem1259719 m). Qed.
Lemma lem1266392 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1266393 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1266392 m) (@lem1266391 m)). Qed.
Lemma lem1266394 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1266393 m n). Qed.
Lemma lem1266395 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1266396 (m : nat) (n : nat) : term16 m n.
Proof. exact (EQ_MP (@lem1266395 m n) (@lem1266394 m n)). Qed.
Lemma lem1266397 (m : nat) (n : nat) (p : nat) : term17 m n p.
Proof. exact (@lem1266396 m n p). Qed.
Lemma lem1266398 (m : nat) (n : nat) (p : nat) : (term17 m n p) = (term18 m n p).
Proof. exact (eq_refl (term17 m n p)). Qed.
Lemma lem1266399 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (EQ_MP (@lem1266398 m n p) (@lem1266397 m n p)). Qed.
Lemma lem1266400 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1266401 (m : nat) (h1 : term19) : term20 m.
Proof. exact (@lem1266400 h1 m). Qed.
Lemma lem1266402 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1266403 (m : nat) (h1 : term19) : term21 m.
Proof. exact (EQ_MP (@lem1266402 m) (@lem1266401 m h1)). Qed.
Lemma lem1266404 (m : nat) (n : nat) (h1 : term19) : term22 m n.
Proof. exact (@lem1266403 m h1 n). Qed.
Lemma lem1266405 (n : nat) (m : nat) : (term22 m n) = (term23 n m).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1266406 (n : nat) (m : nat) (h1 : term19) : term23 n m.
Proof. exact (EQ_MP (@lem1266405 n m) (@lem1266404 m n h1)). Qed.
Lemma lem1266407 (n : nat) (m : nat) (p : nat) (h1 : term19) : term24 n m p.
Proof. exact (@lem1266406 n m h1 p). Qed.
Lemma lem1266408 (n : nat) (m : nat) (p : nat) : (term24 n m p) = (term25 n m p).
Proof. exact (eq_refl (term24 n m p)). Qed.
Lemma lem1266409 (n : nat) (m : nat) (p : nat) (h1 : term19) : term25 n m p.
Proof. exact (EQ_MP (@lem1266408 n m p) (@lem1266407 n m p h1)). Qed.
Lemma lem1266410 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1266411 (p : nat) (m : nat) (n : nat) (h1 : term19) (h2 : Peano.le m n) : term26 n m p.
Proof. exact (@lem1266409 n m p h1 (@lem1266410 m n h2)). Qed.
Lemma lem1266412 (m : nat) (n : nat) (h1 : term19) (h2 : Peano.le m n) : term27 n m.
Proof. exact (fun p : nat => @lem1266411 p m n h1 h2). Qed.
Lemma lem1266413 (n : nat) (m : nat) (h1 : term19) : term28 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1266412 m n h1 h0). Qed.
Lemma lem1266414 (m : nat) (h1 : term19) : term29 m.
Proof. exact (fun n : nat => @lem1266413 n m h1). Qed.
Lemma lem1266415 (h1 : term19) : term30.
Proof. exact (fun m : nat => @lem1266414 m h1). Qed.
Lemma lem1266416 : term31.
Proof. exact (fun h0 : term19 => @lem1266415 h0). Qed.
Lemma lem1266417 : term30.
Proof. exact (@lem1266416 (@lem272809)). Qed.
Lemma lem1266418 (m : nat) : term32 m.
Proof. exact (@lem1266417 m). Qed.
Lemma lem1266419 (m : nat) : (term32 m) = (term29 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1266420 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1266419 m) (@lem1266418 m)). Qed.
Lemma lem1266421 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1266420 m n). Qed.
Lemma lem1266422 (n : nat) (m : nat) : (term33 m n) = (term28 n m).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1266425 (n : nat) (m : nat) : term28 n m.
Proof. exact (EQ_MP (@lem1266422 n m) (@lem1266421 m n)). Qed.
Lemma lem1266426 (n : nat) (m : nat) (p : nat) : term34 n m p.
Proof. exact (@lem1266425 (term35 m n p) (term36 m p)). Qed.
Lemma lem1266427 (n : nat) (m : nat) (p : nat) : term37 n m p.
Proof. exact (@lem1266426 n m p (@lem1266399 m n p)). Qed.
Lemma lem1266428 (n : nat) (m : nat) : term38 n m.
Proof. exact (fun p : nat => @lem1266427 n m p). Qed.
Lemma lem1266429 (n : nat) : term39 n.
Proof. exact (fun m : nat => @lem1266428 n m). Qed.
Lemma lem1266430 : term40.
Proof. exact (fun n : nat => @lem1266429 n). Qed.
Lemma lem1266431 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1266432 (n : nat) (h1 : term40) : term41 n.
Proof. exact (@lem1266431 h1 n). Qed.
Lemma lem1266433 (n : nat) : (term41 n) = (term39 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem1266434 (n : nat) (h1 : term40) : term39 n.
Proof. exact (EQ_MP (@lem1266433 n) (@lem1266432 n h1)). Qed.
Lemma lem1266435 (n : nat) (m : nat) (h1 : term40) : term42 n m.
Proof. exact (@lem1266434 n h1 m). Qed.
Lemma lem1266436 (n : nat) (m : nat) : (term42 n m) = (term38 n m).
Proof. exact (eq_refl (term42 n m)). Qed.
Lemma lem1266437 (n : nat) (m : nat) (h1 : term40) : term38 n m.
Proof. exact (EQ_MP (@lem1266436 n m) (@lem1266435 n m h1)). Qed.
Lemma lem1266438 (n : nat) (m : nat) (p : nat) (h1 : term40) : term43 n m p.
Proof. exact (@lem1266437 n m h1 p). Qed.
Lemma lem1266439 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term37 n m p).
Proof. exact (eq_refl (term43 n m p)). Qed.
Lemma lem1266440 (n : nat) (m : nat) (p : nat) (h1 : term40) : term37 n m p.
Proof. exact (EQ_MP (@lem1266439 n m p) (@lem1266438 n m p h1)). Qed.
Lemma lem1266441 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term40) : term44 n m p p'.
Proof. exact (@lem1266440 n m p h1 p'). Qed.
Lemma lem1266442 (n : nat) (m : nat) (p : nat) (p' : nat) : (term44 n m p p') = (term45 n m p p').
Proof. exact (eq_refl (term44 n m p p')). Qed.
Lemma lem1266443 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term40) : term45 n m p p'.
Proof. exact (EQ_MP (@lem1266442 n m p p') (@lem1266441 n m p p' h1)). Qed.
Lemma lem1266444 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term46 m n p p') : term46 m n p p'.
Proof. exact (h1). Qed.
Lemma lem1266445 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term40) (h2 : term46 m n p p') : term47 m p p'.
Proof. exact (@lem1266443 n m p p' h1 (@lem1266444 m n p p' h2)). Qed.
Lemma lem1266446 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term46 m n p p') : term48 m p p'.
Proof. exact (fun h0 : term40 => @lem1266445 m n p p' h0 h1). Qed.
Lemma lem1266447 (m : nat) (p : nat) (p' : nat) (h1 : term49 m p p') : term49 m p p'.
Proof. exact (h1). Qed.
Lemma lem1266448 (m : nat) (p : nat) (p' : nat) (h1 : term49 m p p') : term48 m p p'.
Proof. exact (ex_elim (@lem1266447 m p p' h1) (fun n : nat => fun h0 : term50 m p p' n => @lem1266446 m n p p' h0)). Qed.
Lemma lem1266449 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1266450 (m : nat) (p : nat) (p' : nat) (h1 : term40) (h2 : term49 m p p') : term47 m p p'.
Proof. exact (@lem1266448 m p p' h2 (@lem1266449 h1)). Qed.
Lemma lem1266451 (m : nat) (p : nat) (p' : nat) (h1 : term40) : term51 m p p'.
Proof. exact (fun h0 : term49 m p p' => @lem1266450 m p p' h1 h0). Qed.
Lemma lem1266452 (m : nat) (p : nat) (h1 : term40) : term52 m p.
Proof. exact (fun p' : nat => @lem1266451 m p p' h1). Qed.
Lemma lem1266453 (m : nat) (h1 : term40) : term53 m.
Proof. exact (fun p : nat => @lem1266452 m p h1). Qed.
Lemma lem1266454 (h1 : term40) : term54.
Proof. exact (fun m : nat => @lem1266453 m h1). Qed.
Lemma lem1266455 : term55.
Proof. exact (fun h0 : term40 => @lem1266454 h0). Qed.
Lemma lem1266456 : term54.
Proof. exact (@lem1266455 (@lem1266430)). Qed.
Lemma lem1266457 (m : nat) : term56 m.
Proof. exact (@lem1266456 m). Qed.
Lemma lem1266458 (m : nat) : (term56 m) = (term53 m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem1266459 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem1266458 m) (@lem1266457 m)). Qed.
Lemma lem1266460 (m : nat) (p : nat) : term57 m p.
Proof. exact (@lem1266459 m p). Qed.
Lemma lem1266461 (m : nat) (p : nat) : (term57 m p) = (term52 m p).
Proof. exact (eq_refl (term57 m p)). Qed.
Lemma lem1266462 (m : nat) (p : nat) : term52 m p.
Proof. exact (EQ_MP (@lem1266461 m p) (@lem1266460 m p)). Qed.
Lemma lem1266463 (m : nat) (p : nat) (p' : nat) : term58 m p p'.
Proof. exact (@lem1266462 m p p'). Qed.
Lemma lem1266464 (m : nat) (p : nat) (p' : nat) : (term58 m p p') = (term51 m p p').
Proof. exact (eq_refl (term58 m p p')). Qed.
Lemma lem1266466 (x : nadd) : term59 x.
Proof. exact (@lem1266353 x). Qed.
Lemma lem1266467 (x : nadd) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1266468 (x : nadd) : term60 x.
Proof. exact (EQ_MP (@lem1266467 x) (@lem1266466 x)). Qed.
Lemma lem1266469 (x : nadd) (B : nat) (h1 : term61 x B) : term61 x B.
Proof. exact (h1). Qed.
Lemma lem1266471 (m : nat) (p : nat) (p' : nat) : term51 m p p'.
Proof. exact (EQ_MP (@lem1266464 m p p') (@lem1266463 m p p')). Qed.
Lemma lem1266472 (n : nat) (B : nat) (x : nadd) : term62 n B x.
Proof. exact (@lem1266471 (term63 x n) (dest_nadd x n) (term64 B x)). Qed.
Lemma lem1266473 (m : nat) : term65 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem1266474 (m : nat) : (term65 m) = ((S m) = (term66 m)).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem1266485 (m : nat) : (S m) = (term66 m).
Proof. exact (EQ_MP (@lem1266474 m) (@lem1266473 m)). Qed.
Lemma lem1266486 (n : nat) : (S n) = (term66 n).
Proof. exact (@lem1266485 n). Qed.
Lemma lem1266487 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1266488 (x : nadd) (n : nat) : (term63 x n) = (term67 x n).
Proof. exact (MK_COMB (@lem1266487 x) (@lem1266486 n)). Qed.
Lemma lem1266489 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1266490 (x : nadd) (n : nat) : (term68 x n) = (term69 x n).
Proof. exact (MK_COMB (@lem1266489) (@lem1266488 x n)). Qed.
Lemma lem1266491 (n : nat) (x : nadd) : (term70 n x) = (term70 n x).
Proof. exact (eq_refl (term70 n x)). Qed.
Lemma lem1266492 (n : nat) (x : nadd) : (term71 n x) = (term72 n x).
Proof. exact (MK_COMB (@lem1266490 x n) (@lem1266491 n x)). Qed.
Lemma lem1266493 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1266494 (n : nat) (x : nadd) : (term73 n x) = (term74 n x).
Proof. exact (MK_COMB (@lem1266493) (@lem1266492 n x)). Qed.
Lemma lem1266495 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1266496 (n : nat) (x : nadd) : (term75 n x) = (term76 n x).
Proof. exact (MK_COMB (@lem1266495) (@lem1266494 n x)). Qed.
Lemma lem1266497 (x : nadd) (n : nat) : (term77 x n) = (term77 x n).
Proof. exact (eq_refl (term77 x n)). Qed.
Lemma lem1266498 (x : nadd) (n : nat) : (term78 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem1266496 n x) (@lem1266497 x n)). Qed.
Lemma lem1266499 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1266500 (x : nadd) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem1266499) (@lem1266498 x n)). Qed.
Lemma lem1266501 (B : nat) (x : nadd) : (term64 B x) = (term64 B x).
Proof. exact (eq_refl (term64 B x)). Qed.
Lemma lem1266502 (n : nat) (B : nat) (x : nadd) : (term82 n B x) = (term83 n B x).
Proof. exact (MK_COMB (@lem1266500 x n) (@lem1266501 B x)). Qed.
Lemma lem1266503 (n : nat) (B : nat) (x : nadd) : (term83 n B x) = (term82 n B x).
Proof. exact (SYM (@lem1266502 n B x)). Qed.
Lemma lem1266505 (m : nat) (n : nat) (p : nat) (q : nat) : term8 m n p q.
Proof. exact (EQ_MP (@lem1266389 m n p q) (@lem1266388 m n p q)). Qed.
Lemma lem1266506 (n : nat) (B : nat) (x : nadd) : term84 n B x.
Proof. exact (@lem1266505 (term74 n x) (term77 x n) B (term85 x)). Qed.
Lemma lem1266507 (n : nat) : term86 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem1266508 (n : nat) : (term86 n) = (Peano.le n n).
Proof. exact (eq_refl (term86 n)). Qed.
Lemma lem1266509 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem1266508 n) (@lem1266507 n)). Qed.
Lemma lem1266510 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem1266512 (m : nat) : term87 m.
Proof. exact (@lem1245246 m). Qed.
Lemma lem1266513 (m : nat) : (term87 m) = (term88 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem1266514 (m : nat) : term88 m.
Proof. exact (EQ_MP (@lem1266513 m) (@lem1266512 m)). Qed.
Lemma lem1266515 (m : nat) (n : nat) : term89 m n.
Proof. exact (@lem1266514 m n). Qed.
Lemma lem1266516 (m : nat) (n : nat) : (term89 m n) = ((term90 n m) = n).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem1266518 (m : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term91 x B m.
Proof. exact (@lem1266469 x B h1 m). Qed.
Lemma lem1266519 (m : nat) (x : nadd) (B : nat) : (term91 x B m) = (term92 m x B).
Proof. exact (eq_refl (term91 x B m)). Qed.
Lemma lem1266520 (m : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term92 m x B.
Proof. exact (EQ_MP (@lem1266519 m x B) (@lem1266518 m x B h1)). Qed.
Lemma lem1266521 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term93 m x B n.
Proof. exact (@lem1266520 m x B h1 n). Qed.
Lemma lem1266522 (m : nat) (x : nadd) (n : nat) (B : nat) : (term93 m x B n) = (term94 m x n B).
Proof. exact (eq_refl (term93 m x B n)). Qed.
Lemma lem1266523 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term94 m x n B.
Proof. exact (EQ_MP (@lem1266522 m x n B) (@lem1266521 m n x B h1)). Qed.
Lemma lem1266524 (m : nat) (x : nadd) (n : nat) (B : nat) : (term94 m x n B) = ((term94 m x n B) = True).
Proof. exact (@lem7 (term94 m x n B)). Qed.
Lemma lem1266529 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : (term94 m x n B) = True.
Proof. exact (EQ_MP (@lem1266524 m x n B) (@lem1266523 m n x B h1)). Qed.
Lemma lem1266530 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : (term95 n x B) = True.
Proof. exact (@lem1266529 n term96 x B h1). Qed.
Lemma lem1266531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1266532 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : (term97 n x B) = (and True).
Proof. exact (MK_COMB (@lem1266531) (@lem1266530 n x B h1)). Qed.
Lemma lem1266536 (m : nat) (n : nat) : (term90 n m) = n.
Proof. exact (EQ_MP (@lem1266516 m n) (@lem1266515 m n)). Qed.
Lemma lem1266537 (n : nat) (x : nadd) : (term77 x n) = (term85 x).
Proof. exact (@lem1266536 (dest_nadd x n) (term85 x)). Qed.
Lemma lem1266538 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1266539 (n : nat) (x : nadd) : (term98 x n) = (term99 x).
Proof. exact (MK_COMB (@lem1266538) (@lem1266537 n x)). Qed.
Lemma lem1266540 (x : nadd) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem1266541 (n : nat) (x : nadd) : (term100 n x) = (term101 x).
Proof. exact (MK_COMB (@lem1266539 n x) (@lem1266540 x)). Qed.
Lemma lem1266543 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem1266510 n) (@lem1266509 n)). Qed.
Lemma lem1266544 (x : nadd) : (term101 x) = True.
Proof. exact (@lem1266543 (term85 x)). Qed.
Lemma lem1266545 (n : nat) (x : nadd) : (term100 n x) = True.
Proof. exact (TRANS (@lem1266541 n x) (@lem1266544 x)). Qed.
Lemma lem1266546 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : (term102 B n x) = (True /\ True).
Proof. exact (MK_COMB (@lem1266532 n x B h1) (@lem1266545 n x)). Qed.
Lemma lem1266548 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1266549 : (True /\ True) = True.
Proof. exact (@lem1266548 True). Qed.
Lemma lem1266550 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : (term102 B n x) = True.
Proof. exact (TRANS (@lem1266546 n x B h1) (@lem1266549)). Qed.
Lemma lem1266551 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : True = (term102 B n x).
Proof. exact (SYM (@lem1266550 n x B h1)). Qed.
Lemma lem1266552 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term102 B n x.
Proof. exact (EQ_MP (@lem1266551 n x B h1) (@lem0)). Qed.
Lemma lem1266553 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term83 n B x.
Proof. exact (@lem1266506 n B x (@lem1266552 n x B h1)). Qed.
Lemma lem1266554 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term82 n B x.
Proof. exact (EQ_MP (@lem1266503 n B x) (@lem1266553 n x B h1)). Qed.
Lemma lem1266555 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term103 n B x.
Proof. exact (ex_intro (term104 n B x) (term70 n x) (@lem1266554 n x B h1)). Qed.
Lemma lem1266556 (n : nat) (x : nadd) (B : nat) (h1 : term61 x B) : term105 n B x.
Proof. exact (@lem1266472 n B x (@lem1266555 n x B h1)). Qed.
Lemma lem1266561 (x : nadd) (B : nat) (h1 : term61 x B) : term106 B x.
Proof. exact (fun n : nat => @lem1266556 n x B h1). Qed.
Lemma lem1266562 (x : nadd) (B : nat) (h1 : term61 x B) : term107 x.
Proof. exact (ex_intro (term108 x) (term64 B x) (@lem1266561 x B h1)). Qed.
Lemma lem1266563 (x : nadd) : term107 x.
Proof. exact (ex_elim (@lem1266468 x) (fun B : nat => fun h0 : term109 x B => @lem1266562 x B h0)). Qed.
Lemma lem1266568 : term110.
Proof. exact (fun x : nadd => @lem1266563 x). Qed.
