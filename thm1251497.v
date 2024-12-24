Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1251497_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1251287 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1251288 (x : nat) : (x = x) = True.
Proof. exact (@lem1251287 nat x). Qed.
Lemma lem1251289 (m : nat) (d' : nat) : ((Nat.add m d') = (Nat.add m d')) = True.
Proof. exact (@lem1251288 (Nat.add m d')). Qed.
Lemma lem1251290 (m : nat) (d' : nat) : True = ((Nat.add m d') = (Nat.add m d')).
Proof. exact (SYM (@lem1251289 m d')). Qed.
Lemma lem1251291 (m : nat) (d' : nat) : (Nat.add m d') = (Nat.add m d').
Proof. exact (EQ_MP (@lem1251290 m d') (@lem0)). Qed.
Lemma lem1251295 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251296 (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term2 m d' d''' d'') = (term3 m d' d''' d'').
Proof. exact (@lem1251295 m (term4 d' d'' d''') d''). Qed.
Lemma lem1251304 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251305 (d' : nat) (d''' : nat) (d'' : nat) : (term5 d' d''' d'') = (term6 d' d''' d'').
Proof. exact (@lem1251304 (Nat.add d' d'') (S d''') d''). Qed.
Lemma lem1251307 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251308 (d' : nat) (d''' : nat) (d'' : nat) : (term6 d' d''' d'') = (term7 d' d''' d'').
Proof. exact (@lem1251307 d' d'' (term8 d''' d'')). Qed.
Lemma lem1251315 (d' : nat) (d''' : nat) (d'' : nat) : (term5 d' d''' d'') = (term7 d' d''' d'').
Proof. exact (TRANS (@lem1251305 d' d''' d'') (@lem1251308 d' d''' d'')). Qed.
Lemma lem1251323 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1251324 (d'' : nat) (d''' : nat) : (term8 d''' d'') = (term9 d'' d''').
Proof. exact (@lem1251323 d'' (S d''')). Qed.
Lemma lem1251328 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251329 (d'' : nat) (d''' : nat) : (term10 d''' d'') = (term11 d'' d''').
Proof. exact (MK_COMB (@lem1251328 d'') (@lem1251324 d'' d''')). Qed.
Lemma lem1251336 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251337 (d' : nat) (d'' : nat) (d''' : nat) : (term7 d' d''' d'') = (term12 d' d'' d''').
Proof. exact (MK_COMB (@lem1251336 d') (@lem1251329 d'' d''')). Qed.
Lemma lem1251344 (d' : nat) (d'' : nat) (d''' : nat) : (term5 d' d''' d'') = (term12 d' d'' d''').
Proof. exact (TRANS (@lem1251315 d' d''' d'') (@lem1251337 d' d'' d''')). Qed.
Lemma lem1251345 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1251346 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m d' d''' d'') = (term13 m d' d'' d''').
Proof. exact (MK_COMB (@lem1251345 m) (@lem1251344 d' d'' d''')). Qed.
Lemma lem1251348 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251349 (d' : nat) (m : nat) (d'' : nat) (d''' : nat) : (term13 m d' d'' d''') = (term13 d' m d'' d''').
Proof. exact (@lem1251348 d' m (term11 d'' d''')). Qed.
Lemma lem1251357 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251358 (m : nat) (d'' : nat) (d''' : nat) : (term12 m d'' d''') = (term14 m d'' d''').
Proof. exact (@lem1251357 d'' m (term9 d'' d''')). Qed.
Lemma lem1251366 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251367 (d'' : nat) (m : nat) (d''' : nat) : (term15 m d'' d''') = (term15 d'' m d''').
Proof. exact (@lem1251366 d'' m (S d''')). Qed.
Lemma lem1251377 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251378 (d'' : nat) (m : nat) (d''' : nat) : (term14 m d'' d''') = (term16 d'' m d''').
Proof. exact (MK_COMB (@lem1251377 d'') (@lem1251367 d'' m d''')). Qed.
Lemma lem1251385 (d'' : nat) (m : nat) (d''' : nat) : (term12 m d'' d''') = (term16 d'' m d''').
Proof. exact (TRANS (@lem1251358 m d'' d''') (@lem1251378 d'' m d''')). Qed.
Lemma lem1251386 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251387 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term13 d' m d'' d''') = (term17 d' d'' m d''').
Proof. exact (MK_COMB (@lem1251386 d') (@lem1251385 d'' m d''')). Qed.
Lemma lem1251394 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term13 m d' d'' d''') = (term17 d' d'' m d''').
Proof. exact (TRANS (@lem1251349 d' m d'' d''') (@lem1251387 d' d'' m d''')). Qed.
Lemma lem1251395 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term3 m d' d''' d'') = (term17 d' d'' m d''').
Proof. exact (TRANS (@lem1251346 m d' d'' d''') (@lem1251394 d' d'' m d''')). Qed.
Lemma lem1251396 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term2 m d' d''' d'') = (term17 d' d'' m d''').
Proof. exact (TRANS (@lem1251296 m d' d''' d'') (@lem1251395 d' d'' m d''')). Qed.
Lemma lem1251397 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251398 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term18 m d' d''' d'') = (term19 d' d'' m d''').
Proof. exact (MK_COMB (@lem1251397) (@lem1251396 d' d'' m d''')). Qed.
Lemma lem1251400 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251401 (d' : nat) (m : nat) (d'' : nat) (d''' : nat) : (term13 m d' d'' d''') = (term13 d' m d'' d''').
Proof. exact (@lem1251400 d' m (term11 d'' d''')). Qed.
Lemma lem1251409 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251410 (m : nat) (d'' : nat) (d''' : nat) : (term12 m d'' d''') = (term14 m d'' d''').
Proof. exact (@lem1251409 d'' m (term9 d'' d''')). Qed.
Lemma lem1251418 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251419 (d'' : nat) (m : nat) (d''' : nat) : (term15 m d'' d''') = (term15 d'' m d''').
Proof. exact (@lem1251418 d'' m (S d''')). Qed.
Lemma lem1251429 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251430 (d'' : nat) (m : nat) (d''' : nat) : (term14 m d'' d''') = (term16 d'' m d''').
Proof. exact (MK_COMB (@lem1251429 d'') (@lem1251419 d'' m d''')). Qed.
Lemma lem1251437 (d'' : nat) (m : nat) (d''' : nat) : (term12 m d'' d''') = (term16 d'' m d''').
Proof. exact (TRANS (@lem1251410 m d'' d''') (@lem1251430 d'' m d''')). Qed.
Lemma lem1251438 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251439 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term13 d' m d'' d''') = (term17 d' d'' m d''').
Proof. exact (MK_COMB (@lem1251438 d') (@lem1251437 d'' m d''')). Qed.
Lemma lem1251446 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term13 m d' d'' d''') = (term17 d' d'' m d''').
Proof. exact (TRANS (@lem1251401 d' m d'' d''') (@lem1251439 d' d'' m d''')). Qed.
Lemma lem1251447 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : ((term2 m d' d''' d'') = (term13 m d' d'' d''')) = ((term17 d' d'' m d''') = (term17 d' d'' m d''')).
Proof. exact (MK_COMB (@lem1251398 d' d'' m d''') (@lem1251446 d' d'' m d''')). Qed.
Lemma lem1251449 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1251450 (x : nat) : (x = x) = True.
Proof. exact (@lem1251449 nat x). Qed.
Lemma lem1251451 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : ((term17 d' d'' m d''') = (term17 d' d'' m d''')) = True.
Proof. exact (@lem1251450 (term17 d' d'' m d''')). Qed.
Lemma lem1251452 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 m d' d''' d'') = (term13 m d' d'' d''')) = True.
Proof. exact (TRANS (@lem1251447 d' d'' m d''') (@lem1251451 d' d'' m d''')). Qed.
Lemma lem1251453 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : True = ((term2 m d' d''' d'') = (term13 m d' d'' d''')).
Proof. exact (SYM (@lem1251452 m d' d'' d''')). Qed.
Lemma lem1251454 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term2 m d' d''' d'') = (term13 m d' d'' d''').
Proof. exact (EQ_MP (@lem1251453 m d' d'' d''') (@lem0)). Qed.
Lemma lem1251455 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251456 (m : nat) (d' : nat) : (term20 m d') = (term20 m d').
Proof. exact (MK_COMB (@lem1251455) (@lem1251291 m d')). Qed.
Lemma lem1251457 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add m d') = (term2 m d' d''' d'')) = ((Nat.add m d') = (term13 m d' d'' d''')).
Proof. exact (MK_COMB (@lem1251456 m d') (@lem1251454 m d' d'' d''')). Qed.
Lemma lem1251458 (m : nat) : term21 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1251459 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1251460 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1251459 m) (@lem1251458 m)). Qed.
Lemma lem1251461 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1251460 m n). Qed.
Lemma lem1251462 (m : nat) (n : nat) : (term23 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1251470 (m : nat) : term24 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1251471 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1251472 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1251471 m) (@lem1251470 m)). Qed.
Lemma lem1251473 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1251472 m n). Qed.
Lemma lem1251474 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1251475 (m : nat) (n : nat) : term27 m n.
Proof. exact (EQ_MP (@lem1251474 m n) (@lem1251473 m n)). Qed.
Lemma lem1251476 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (@lem1251475 m n p). Qed.
Lemma lem1251477 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term28 m n p)). Qed.
Lemma lem1251480 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1251477 m n p) (@lem1251476 m n p)). Qed.
Lemma lem1251481 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add m d') = (term13 m d' d'' d''')) = (d' = (term12 d' d'' d''')).
Proof. exact (@lem1251480 m d' (term12 d' d'' d''')). Qed.
Lemma lem1251483 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251462 m n) (@lem1251461 m n)). Qed.
Lemma lem1251488 (d' : nat) (d'' : nat) (d''' : nat) : (d' = (term12 d' d'' d''')) = ((term11 d'' d''') = (NUMERAL 0)).
Proof. exact (@lem1251483 d' (term11 d'' d''')). Qed.
Lemma lem1251489 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add m d') = (term13 m d' d'' d''')) = ((term11 d'' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1251481 m d' d'' d''') (@lem1251488 d' d'' d''')). Qed.
Lemma lem1251490 (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term29 m d' d''' d'') = (term29 m d' d''' d'').
Proof. exact (eq_refl (term29 m d' d''' d'')). Qed.
Lemma lem1251491 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (((Nat.add m d') = (term2 m d' d''' d'')) = ((Nat.add m d') = (term13 m d' d'' d'''))) = (((Nat.add m d') = (term2 m d' d''' d'')) = ((term11 d'' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1251490 m d' d''' d'') (@lem1251489 m d' d'' d''')). Qed.
Lemma lem1251492 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add m d') = (term2 m d' d''' d'')) = ((term11 d'' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251491 m d' d'' d''') (@lem1251457 m d' d'' d''')). Qed.
Lemma lem1251493 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1251494 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term30 m d' d''' d'') = (term31 d'' d''').
Proof. exact (MK_COMB (@lem1251493) (@lem1251492 m d' d'' d''')). Qed.
Lemma lem1251495 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1251496 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term32 m d' d''' d'') = (term33 d'' d''').
Proof. exact (MK_COMB (@lem1251494 m d' d'' d''') (@lem1251495)). Qed.
Lemma lem1251497 (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term33 d'' d''') = (term32 m d' d''' d'').
Proof. exact (SYM (@lem1251496 m d' d'' d''')). Qed.
