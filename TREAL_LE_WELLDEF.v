Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_LE_WELLDEF_term_abbrevs.
Require Import TREAL_EQ_IMP_LE_spec.
Require Import TREAL_EQ_SYM_spec.
Require Import TREAL_LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm1843_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1334363 (x : prod hreal hreal) : term0 x.
Proof. exact (@lem1326359 x). Qed.
Lemma lem1334364 (x : prod hreal hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1334365 (x : prod hreal hreal) : term1 x.
Proof. exact (EQ_MP (@lem1334364 x) (@lem1334363 x)). Qed.
Lemma lem1334366 (x : prod hreal hreal) (y : prod hreal hreal) : term2 x y.
Proof. exact (@lem1334365 x y). Qed.
Lemma lem1334367 (y : prod hreal hreal) (x : prod hreal hreal) : (term2 x y) = ((treal_eq x y) = (treal_eq y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1334369 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334370 (x : prod hreal hreal) (h1 : term3) : term4 x.
Proof. exact (@lem1334369 h1 x). Qed.
Lemma lem1334371 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334372 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (EQ_MP (@lem1334371 x) (@lem1334370 x h1)). Qed.
Lemma lem1334373 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term6 x y.
Proof. exact (@lem1334372 x h1 y). Qed.
Lemma lem1334374 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334375 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (EQ_MP (@lem1334374 x y) (@lem1334373 x y h1)). Qed.
Lemma lem1334376 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : treal_eq x y.
Proof. exact (h1). Qed.
Lemma lem1334377 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334375 x y h1 (@lem1334376 x y h2)). Qed.
Lemma lem1334378 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : term8 x y.
Proof. exact (fun h0 : term3 => @lem1334377 x y h0 h1). Qed.
Lemma lem1334379 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334380 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334378 x y h2 (@lem1334379 h1)). Qed.
Lemma lem1334381 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (fun h0 : treal_eq x y => @lem1334380 x y h1 h0). Qed.
Lemma lem1334382 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (fun y : prod hreal hreal => @lem1334381 x y h1). Qed.
Lemma lem1334383 (h1 : term3) : term3.
Proof. exact (fun x : prod hreal hreal => @lem1334382 x h1). Qed.
Lemma lem1334384 : term9.
Proof. exact (fun h0 : term3 => @lem1334383 h0). Qed.
Lemma lem1334385 : term3.
Proof. exact (@lem1334384 (@lem1334362)). Qed.
Lemma lem1334386 (x : prod hreal hreal) : term4 x.
Proof. exact (@lem1334385 x). Qed.
Lemma lem1334387 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334388 (x : prod hreal hreal) : term5 x.
Proof. exact (EQ_MP (@lem1334387 x) (@lem1334386 x)). Qed.
Lemma lem1334389 (x : prod hreal hreal) (y : prod hreal hreal) : term6 x y.
Proof. exact (@lem1334388 x y). Qed.
Lemma lem1334390 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334392 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334393 (x : prod hreal hreal) (h1 : term3) : term4 x.
Proof. exact (@lem1334392 h1 x). Qed.
Lemma lem1334394 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334395 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (EQ_MP (@lem1334394 x) (@lem1334393 x h1)). Qed.
Lemma lem1334396 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term6 x y.
Proof. exact (@lem1334395 x h1 y). Qed.
Lemma lem1334397 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334398 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (EQ_MP (@lem1334397 x y) (@lem1334396 x y h1)). Qed.
Lemma lem1334399 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : treal_eq x y.
Proof. exact (h1). Qed.
Lemma lem1334400 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334398 x y h1 (@lem1334399 x y h2)). Qed.
Lemma lem1334401 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : term8 x y.
Proof. exact (fun h0 : term3 => @lem1334400 x y h0 h1). Qed.
Lemma lem1334402 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334403 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334401 x y h2 (@lem1334402 h1)). Qed.
Lemma lem1334404 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (fun h0 : treal_eq x y => @lem1334403 x y h1 h0). Qed.
Lemma lem1334405 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (fun y : prod hreal hreal => @lem1334404 x y h1). Qed.
Lemma lem1334406 (h1 : term3) : term3.
Proof. exact (fun x : prod hreal hreal => @lem1334405 x h1). Qed.
Lemma lem1334407 : term9.
Proof. exact (fun h0 : term3 => @lem1334406 h0). Qed.
Lemma lem1334408 : term3.
Proof. exact (@lem1334407 (@lem1334362)). Qed.
Lemma lem1334409 (x : prod hreal hreal) : term4 x.
Proof. exact (@lem1334408 x). Qed.
Lemma lem1334410 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334411 (x : prod hreal hreal) : term5 x.
Proof. exact (EQ_MP (@lem1334410 x) (@lem1334409 x)). Qed.
Lemma lem1334412 (x : prod hreal hreal) (y : prod hreal hreal) : term6 x y.
Proof. exact (@lem1334411 x y). Qed.
Lemma lem1334413 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334415 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334416 (x : prod hreal hreal) (h1 : term10) : term11 x.
Proof. exact (@lem1334415 h1 x). Qed.
Lemma lem1334417 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1334418 (x : prod hreal hreal) (h1 : term10) : term12 x.
Proof. exact (EQ_MP (@lem1334417 x) (@lem1334416 x h1)). Qed.
Lemma lem1334419 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term10) : term13 x y.
Proof. exact (@lem1334418 x h1 y). Qed.
Lemma lem1334420 (y : prod hreal hreal) (x : prod hreal hreal) : (term13 x y) = (term14 y x).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1334421 (y : prod hreal hreal) (x : prod hreal hreal) (h1 : term10) : term14 y x.
Proof. exact (EQ_MP (@lem1334420 y x) (@lem1334419 x y h1)). Qed.
Lemma lem1334422 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term15 y x z.
Proof. exact (@lem1334421 y x h1 z). Qed.
Lemma lem1334423 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term15 y x z) = (term16 y x z).
Proof. exact (eq_refl (term15 y x z)). Qed.
Lemma lem1334424 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term16 y x z.
Proof. exact (EQ_MP (@lem1334423 y x z) (@lem1334422 y x z h1)). Qed.
Lemma lem1334425 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term17 x y z.
Proof. exact (h1). Qed.
Lemma lem1334426 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term17 x y z) : treal_le x z.
Proof. exact (@lem1334424 y x z h1 (@lem1334425 x y z h2)). Qed.
Lemma lem1334427 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term18 x z.
Proof. exact (fun h0 : term10 => @lem1334426 x y z h0 h1). Qed.
Lemma lem1334428 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term19 x z.
Proof. exact (h1). Qed.
Lemma lem1334429 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term18 x z.
Proof. exact (ex_elim (@lem1334428 x z h1) (fun y : prod hreal hreal => fun h0 : term20 x z y => @lem1334427 x y z h0)). Qed.
Lemma lem1334430 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334431 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term19 x z) : treal_le x z.
Proof. exact (@lem1334429 x z h2 (@lem1334430 h1)). Qed.
Lemma lem1334432 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term21 x z.
Proof. exact (fun h0 : term19 x z => @lem1334431 x z h1 h0). Qed.
Lemma lem1334433 (x : prod hreal hreal) (h1 : term10) : term22 x.
Proof. exact (fun z : prod hreal hreal => @lem1334432 x z h1). Qed.
Lemma lem1334434 (h1 : term10) : term23.
Proof. exact (fun x : prod hreal hreal => @lem1334433 x h1). Qed.
Lemma lem1334435 : term24.
Proof. exact (fun h0 : term10 => @lem1334434 h0). Qed.
Lemma lem1334436 : term23.
Proof. exact (@lem1334435 (@lem1330544)). Qed.
Lemma lem1334437 (x : prod hreal hreal) : term25 x.
Proof. exact (@lem1334436 x). Qed.
Lemma lem1334438 (x : prod hreal hreal) : (term25 x) = (term22 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1334439 (x : prod hreal hreal) : term22 x.
Proof. exact (EQ_MP (@lem1334438 x) (@lem1334437 x)). Qed.
Lemma lem1334440 (x : prod hreal hreal) (z : prod hreal hreal) : term26 x z.
Proof. exact (@lem1334439 x z). Qed.
Lemma lem1334441 (x : prod hreal hreal) (z : prod hreal hreal) : (term26 x z) = (term21 x z).
Proof. exact (eq_refl (term26 x z)). Qed.
Lemma lem1334443 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334444 (x : prod hreal hreal) (h1 : term10) : term11 x.
Proof. exact (@lem1334443 h1 x). Qed.
Lemma lem1334445 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1334446 (x : prod hreal hreal) (h1 : term10) : term12 x.
Proof. exact (EQ_MP (@lem1334445 x) (@lem1334444 x h1)). Qed.
Lemma lem1334447 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term10) : term13 x y.
Proof. exact (@lem1334446 x h1 y). Qed.
Lemma lem1334448 (y : prod hreal hreal) (x : prod hreal hreal) : (term13 x y) = (term14 y x).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1334449 (y : prod hreal hreal) (x : prod hreal hreal) (h1 : term10) : term14 y x.
Proof. exact (EQ_MP (@lem1334448 y x) (@lem1334447 x y h1)). Qed.
Lemma lem1334450 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term15 y x z.
Proof. exact (@lem1334449 y x h1 z). Qed.
Lemma lem1334451 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term15 y x z) = (term16 y x z).
Proof. exact (eq_refl (term15 y x z)). Qed.
Lemma lem1334452 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term16 y x z.
Proof. exact (EQ_MP (@lem1334451 y x z) (@lem1334450 y x z h1)). Qed.
Lemma lem1334453 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term17 x y z.
Proof. exact (h1). Qed.
Lemma lem1334454 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term17 x y z) : treal_le x z.
Proof. exact (@lem1334452 y x z h1 (@lem1334453 x y z h2)). Qed.
Lemma lem1334455 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term18 x z.
Proof. exact (fun h0 : term10 => @lem1334454 x y z h0 h1). Qed.
Lemma lem1334456 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term19 x z.
Proof. exact (h1). Qed.
Lemma lem1334457 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term18 x z.
Proof. exact (ex_elim (@lem1334456 x z h1) (fun y : prod hreal hreal => fun h0 : term20 x z y => @lem1334455 x y z h0)). Qed.
Lemma lem1334458 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334459 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term19 x z) : treal_le x z.
Proof. exact (@lem1334457 x z h2 (@lem1334458 h1)). Qed.
Lemma lem1334460 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term21 x z.
Proof. exact (fun h0 : term19 x z => @lem1334459 x z h1 h0). Qed.
Lemma lem1334461 (x : prod hreal hreal) (h1 : term10) : term22 x.
Proof. exact (fun z : prod hreal hreal => @lem1334460 x z h1). Qed.
Lemma lem1334462 (h1 : term10) : term23.
Proof. exact (fun x : prod hreal hreal => @lem1334461 x h1). Qed.
Lemma lem1334463 : term24.
Proof. exact (fun h0 : term10 => @lem1334462 h0). Qed.
Lemma lem1334464 : term23.
Proof. exact (@lem1334463 (@lem1330544)). Qed.
Lemma lem1334465 (x : prod hreal hreal) : term25 x.
Proof. exact (@lem1334464 x). Qed.
Lemma lem1334466 (x : prod hreal hreal) : (term25 x) = (term22 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1334467 (x : prod hreal hreal) : term22 x.
Proof. exact (EQ_MP (@lem1334466 x) (@lem1334465 x)). Qed.
Lemma lem1334468 (x : prod hreal hreal) (z : prod hreal hreal) : term26 x z.
Proof. exact (@lem1334467 x z). Qed.
Lemma lem1334469 (x : prod hreal hreal) (z : prod hreal hreal) : (term26 x z) = (term21 x z).
Proof. exact (eq_refl (term26 x z)). Qed.
Lemma lem1334471 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334472 (x : prod hreal hreal) (h1 : term3) : term4 x.
Proof. exact (@lem1334471 h1 x). Qed.
Lemma lem1334473 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334474 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (EQ_MP (@lem1334473 x) (@lem1334472 x h1)). Qed.
Lemma lem1334475 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term6 x y.
Proof. exact (@lem1334474 x h1 y). Qed.
Lemma lem1334476 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334477 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (EQ_MP (@lem1334476 x y) (@lem1334475 x y h1)). Qed.
Lemma lem1334478 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : treal_eq x y.
Proof. exact (h1). Qed.
Lemma lem1334479 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334477 x y h1 (@lem1334478 x y h2)). Qed.
Lemma lem1334480 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : term8 x y.
Proof. exact (fun h0 : term3 => @lem1334479 x y h0 h1). Qed.
Lemma lem1334481 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334482 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334480 x y h2 (@lem1334481 h1)). Qed.
Lemma lem1334483 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (fun h0 : treal_eq x y => @lem1334482 x y h1 h0). Qed.
Lemma lem1334484 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (fun y : prod hreal hreal => @lem1334483 x y h1). Qed.
Lemma lem1334485 (h1 : term3) : term3.
Proof. exact (fun x : prod hreal hreal => @lem1334484 x h1). Qed.
Lemma lem1334486 : term9.
Proof. exact (fun h0 : term3 => @lem1334485 h0). Qed.
Lemma lem1334487 : term3.
Proof. exact (@lem1334486 (@lem1334362)). Qed.
Lemma lem1334488 (x : prod hreal hreal) : term4 x.
Proof. exact (@lem1334487 x). Qed.
Lemma lem1334489 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334490 (x : prod hreal hreal) : term5 x.
Proof. exact (EQ_MP (@lem1334489 x) (@lem1334488 x)). Qed.
Lemma lem1334491 (x : prod hreal hreal) (y : prod hreal hreal) : term6 x y.
Proof. exact (@lem1334490 x y). Qed.
Lemma lem1334492 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334494 (x : prod hreal hreal) : term0 x.
Proof. exact (@lem1326359 x). Qed.
Lemma lem1334495 (x : prod hreal hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1334496 (x : prod hreal hreal) : term1 x.
Proof. exact (EQ_MP (@lem1334495 x) (@lem1334494 x)). Qed.
Lemma lem1334497 (x : prod hreal hreal) (y : prod hreal hreal) : term2 x y.
Proof. exact (@lem1334496 x y). Qed.
Lemma lem1334498 (y : prod hreal hreal) (x : prod hreal hreal) : (term2 x y) = ((treal_eq x y) = (treal_eq y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1334500 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334501 (x : prod hreal hreal) (h1 : term3) : term4 x.
Proof. exact (@lem1334500 h1 x). Qed.
Lemma lem1334502 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334503 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (EQ_MP (@lem1334502 x) (@lem1334501 x h1)). Qed.
Lemma lem1334504 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term6 x y.
Proof. exact (@lem1334503 x h1 y). Qed.
Lemma lem1334505 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334506 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (EQ_MP (@lem1334505 x y) (@lem1334504 x y h1)). Qed.
Lemma lem1334507 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : treal_eq x y.
Proof. exact (h1). Qed.
Lemma lem1334508 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334506 x y h1 (@lem1334507 x y h2)). Qed.
Lemma lem1334509 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : treal_eq x y) : term8 x y.
Proof. exact (fun h0 : term3 => @lem1334508 x y h0 h1). Qed.
Lemma lem1334510 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1334511 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) (h2 : treal_eq x y) : treal_le x y.
Proof. exact (@lem1334509 x y h2 (@lem1334510 h1)). Qed.
Lemma lem1334512 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term3) : term7 x y.
Proof. exact (fun h0 : treal_eq x y => @lem1334511 x y h1 h0). Qed.
Lemma lem1334513 (x : prod hreal hreal) (h1 : term3) : term5 x.
Proof. exact (fun y : prod hreal hreal => @lem1334512 x y h1). Qed.
Lemma lem1334514 (h1 : term3) : term3.
Proof. exact (fun x : prod hreal hreal => @lem1334513 x h1). Qed.
Lemma lem1334515 : term9.
Proof. exact (fun h0 : term3 => @lem1334514 h0). Qed.
Lemma lem1334516 : term3.
Proof. exact (@lem1334515 (@lem1334362)). Qed.
Lemma lem1334517 (x : prod hreal hreal) : term4 x.
Proof. exact (@lem1334516 x). Qed.
Lemma lem1334518 (x : prod hreal hreal) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1334519 (x : prod hreal hreal) : term5 x.
Proof. exact (EQ_MP (@lem1334518 x) (@lem1334517 x)). Qed.
Lemma lem1334520 (x : prod hreal hreal) (y : prod hreal hreal) : term6 x y.
Proof. exact (@lem1334519 x y). Qed.
Lemma lem1334521 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1334523 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334524 (x : prod hreal hreal) (h1 : term10) : term11 x.
Proof. exact (@lem1334523 h1 x). Qed.
Lemma lem1334525 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1334526 (x : prod hreal hreal) (h1 : term10) : term12 x.
Proof. exact (EQ_MP (@lem1334525 x) (@lem1334524 x h1)). Qed.
Lemma lem1334527 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term10) : term13 x y.
Proof. exact (@lem1334526 x h1 y). Qed.
Lemma lem1334528 (y : prod hreal hreal) (x : prod hreal hreal) : (term13 x y) = (term14 y x).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1334529 (y : prod hreal hreal) (x : prod hreal hreal) (h1 : term10) : term14 y x.
Proof. exact (EQ_MP (@lem1334528 y x) (@lem1334527 x y h1)). Qed.
Lemma lem1334530 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term15 y x z.
Proof. exact (@lem1334529 y x h1 z). Qed.
Lemma lem1334531 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term15 y x z) = (term16 y x z).
Proof. exact (eq_refl (term15 y x z)). Qed.
Lemma lem1334532 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term16 y x z.
Proof. exact (EQ_MP (@lem1334531 y x z) (@lem1334530 y x z h1)). Qed.
Lemma lem1334533 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term17 x y z.
Proof. exact (h1). Qed.
Lemma lem1334534 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term17 x y z) : treal_le x z.
Proof. exact (@lem1334532 y x z h1 (@lem1334533 x y z h2)). Qed.
Lemma lem1334535 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term18 x z.
Proof. exact (fun h0 : term10 => @lem1334534 x y z h0 h1). Qed.
Lemma lem1334536 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term19 x z.
Proof. exact (h1). Qed.
Lemma lem1334537 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term18 x z.
Proof. exact (ex_elim (@lem1334536 x z h1) (fun y : prod hreal hreal => fun h0 : term20 x z y => @lem1334535 x y z h0)). Qed.
Lemma lem1334538 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334539 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term19 x z) : treal_le x z.
Proof. exact (@lem1334537 x z h2 (@lem1334538 h1)). Qed.
Lemma lem1334540 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term21 x z.
Proof. exact (fun h0 : term19 x z => @lem1334539 x z h1 h0). Qed.
Lemma lem1334541 (x : prod hreal hreal) (h1 : term10) : term22 x.
Proof. exact (fun z : prod hreal hreal => @lem1334540 x z h1). Qed.
Lemma lem1334542 (h1 : term10) : term23.
Proof. exact (fun x : prod hreal hreal => @lem1334541 x h1). Qed.
Lemma lem1334543 : term24.
Proof. exact (fun h0 : term10 => @lem1334542 h0). Qed.
Lemma lem1334544 : term23.
Proof. exact (@lem1334543 (@lem1330544)). Qed.
Lemma lem1334545 (x : prod hreal hreal) : term25 x.
Proof. exact (@lem1334544 x). Qed.
Lemma lem1334546 (x : prod hreal hreal) : (term25 x) = (term22 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1334547 (x : prod hreal hreal) : term22 x.
Proof. exact (EQ_MP (@lem1334546 x) (@lem1334545 x)). Qed.
Lemma lem1334548 (x : prod hreal hreal) (z : prod hreal hreal) : term26 x z.
Proof. exact (@lem1334547 x z). Qed.
Lemma lem1334549 (x : prod hreal hreal) (z : prod hreal hreal) : (term26 x z) = (term21 x z).
Proof. exact (eq_refl (term26 x z)). Qed.
Lemma lem1334551 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334552 (x : prod hreal hreal) (h1 : term10) : term11 x.
Proof. exact (@lem1334551 h1 x). Qed.
Lemma lem1334553 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1334554 (x : prod hreal hreal) (h1 : term10) : term12 x.
Proof. exact (EQ_MP (@lem1334553 x) (@lem1334552 x h1)). Qed.
Lemma lem1334555 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term10) : term13 x y.
Proof. exact (@lem1334554 x h1 y). Qed.
Lemma lem1334556 (y : prod hreal hreal) (x : prod hreal hreal) : (term13 x y) = (term14 y x).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1334557 (y : prod hreal hreal) (x : prod hreal hreal) (h1 : term10) : term14 y x.
Proof. exact (EQ_MP (@lem1334556 y x) (@lem1334555 x y h1)). Qed.
Lemma lem1334558 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term15 y x z.
Proof. exact (@lem1334557 y x h1 z). Qed.
Lemma lem1334559 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term15 y x z) = (term16 y x z).
Proof. exact (eq_refl (term15 y x z)). Qed.
Lemma lem1334560 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term16 y x z.
Proof. exact (EQ_MP (@lem1334559 y x z) (@lem1334558 y x z h1)). Qed.
Lemma lem1334561 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term17 x y z.
Proof. exact (h1). Qed.
Lemma lem1334562 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term17 x y z) : treal_le x z.
Proof. exact (@lem1334560 y x z h1 (@lem1334561 x y z h2)). Qed.
Lemma lem1334563 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term17 x y z) : term18 x z.
Proof. exact (fun h0 : term10 => @lem1334562 x y z h0 h1). Qed.
Lemma lem1334564 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term19 x z.
Proof. exact (h1). Qed.
Lemma lem1334565 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term19 x z) : term18 x z.
Proof. exact (ex_elim (@lem1334564 x z h1) (fun y : prod hreal hreal => fun h0 : term20 x z y => @lem1334563 x y z h0)). Qed.
Lemma lem1334566 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1334567 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) (h2 : term19 x z) : treal_le x z.
Proof. exact (@lem1334565 x z h2 (@lem1334566 h1)). Qed.
Lemma lem1334568 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term10) : term21 x z.
Proof. exact (fun h0 : term19 x z => @lem1334567 x z h1 h0). Qed.
Lemma lem1334569 (x : prod hreal hreal) (h1 : term10) : term22 x.
Proof. exact (fun z : prod hreal hreal => @lem1334568 x z h1). Qed.
Lemma lem1334570 (h1 : term10) : term23.
Proof. exact (fun x : prod hreal hreal => @lem1334569 x h1). Qed.
Lemma lem1334571 : term24.
Proof. exact (fun h0 : term10 => @lem1334570 h0). Qed.
Lemma lem1334572 : term23.
Proof. exact (@lem1334571 (@lem1330544)). Qed.
Lemma lem1334573 (x : prod hreal hreal) : term25 x.
Proof. exact (@lem1334572 x). Qed.
Lemma lem1334574 (x : prod hreal hreal) : (term25 x) = (term22 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1334575 (x : prod hreal hreal) : term22 x.
Proof. exact (EQ_MP (@lem1334574 x) (@lem1334573 x)). Qed.
Lemma lem1334576 (x : prod hreal hreal) (z : prod hreal hreal) : term26 x z.
Proof. exact (@lem1334575 x z). Qed.
Lemma lem1334577 (x : prod hreal hreal) (z : prod hreal hreal) : (term26 x z) = (term21 x z).
Proof. exact (eq_refl (term26 x z)). Qed.
Lemma lem1334579 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term27 x1 x2 y1 y2) : term27 x1 x2 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1334580 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : treal_eq y1 y2.
Proof. exact (h1). Qed.
Lemma lem1334581 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_eq x1 x2.
Proof. exact (h1). Qed.
Lemma lem1334582 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_le x1 y1) : treal_le x1 y1.
Proof. exact (h1). Qed.
Lemma lem1334583 (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_le x2 y2) : treal_le x2 y2.
Proof. exact (h1). Qed.
Lemma lem1334585 (x : prod hreal hreal) (z : prod hreal hreal) : term21 x z.
Proof. exact (EQ_MP (@lem1334577 x z) (@lem1334576 x z)). Qed.
Lemma lem1334586 (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term21 x2 y2.
Proof. exact (@lem1334585 x2 y2). Qed.
Lemma lem1334588 (x : prod hreal hreal) (z : prod hreal hreal) : term21 x z.
Proof. exact (EQ_MP (@lem1334549 x z) (@lem1334548 x z)). Qed.
Lemma lem1334589 (x2 : prod hreal hreal) (y1 : prod hreal hreal) : term21 x2 y1.
Proof. exact (@lem1334588 x2 y1). Qed.
Lemma lem1334594 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = ((treal_le x1 y1) = True).
Proof. exact (@lem7 (treal_le x1 y1)). Qed.
Lemma lem1334599 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_le x1 y1) : (treal_le x1 y1) = True.
Proof. exact (EQ_MP (@lem1334594 x1 y1) (@lem1334582 x1 y1 h1)). Qed.
Lemma lem1334600 (x2 : prod hreal hreal) (x1 : prod hreal hreal) : (term28 x2 x1) = (term28 x2 x1).
Proof. exact (eq_refl (term28 x2 x1)). Qed.
Lemma lem1334601 (x2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_le x1 y1) : (term17 x2 x1 y1) = (term29 x2 x1).
Proof. exact (MK_COMB (@lem1334600 x2 x1) (@lem1334599 x1 y1 h1)). Qed.
Lemma lem1334603 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1334604 (x2 : prod hreal hreal) (x1 : prod hreal hreal) : (term29 x2 x1) = (treal_le x2 x1).
Proof. exact (@lem1334603 (treal_le x2 x1)). Qed.
Lemma lem1334605 (x2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_le x1 y1) : (term17 x2 x1 y1) = (treal_le x2 x1).
Proof. exact (TRANS (@lem1334601 x2 x1 y1 h1) (@lem1334604 x2 x1)). Qed.
Lemma lem1334606 (x2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_le x1 y1) : (treal_le x2 x1) = (term17 x2 x1 y1).
Proof. exact (SYM (@lem1334605 x2 x1 y1 h1)). Qed.
Lemma lem1334608 (x : prod hreal hreal) (y : prod hreal hreal) : term7 x y.
Proof. exact (EQ_MP (@lem1334521 x y) (@lem1334520 x y)). Qed.
Lemma lem1334609 (x2 : prod hreal hreal) (x1 : prod hreal hreal) : term7 x2 x1.
Proof. exact (@lem1334608 x2 x1). Qed.
Lemma lem1334611 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_eq x y) = (treal_eq y x).
Proof. exact (EQ_MP (@lem1334498 y x) (@lem1334497 x y)). Qed.
Lemma lem1334612 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (treal_eq x2 x1) = (treal_eq x1 x2).
Proof. exact (@lem1334611 x1 x2). Qed.
Lemma lem1334613 (x2 : prod hreal hreal) (x1 : prod hreal hreal) : (treal_eq x1 x2) = (treal_eq x2 x1).
Proof. exact (SYM (@lem1334612 x1 x2)). Qed.
Lemma lem1334615 (x : prod hreal hreal) (y : prod hreal hreal) : term7 x y.
Proof. exact (EQ_MP (@lem1334492 x y) (@lem1334491 x y)). Qed.
Lemma lem1334616 (y1 : prod hreal hreal) (y2 : prod hreal hreal) : term7 y1 y2.
Proof. exact (@lem1334615 y1 y2). Qed.
Lemma lem1334618 (x : prod hreal hreal) (z : prod hreal hreal) : term21 x z.
Proof. exact (EQ_MP (@lem1334469 x z) (@lem1334468 x z)). Qed.
Lemma lem1334619 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term21 x1 y1.
Proof. exact (@lem1334618 x1 y1). Qed.
Lemma lem1334621 (x : prod hreal hreal) (z : prod hreal hreal) : term21 x z.
Proof. exact (EQ_MP (@lem1334441 x z) (@lem1334440 x z)). Qed.
Lemma lem1334622 (x1 : prod hreal hreal) (y2 : prod hreal hreal) : term21 x1 y2.
Proof. exact (@lem1334621 x1 y2). Qed.
Lemma lem1334627 (x2 : prod hreal hreal) (y2 : prod hreal hreal) : (treal_le x2 y2) = ((treal_le x2 y2) = True).
Proof. exact (@lem7 (treal_le x2 y2)). Qed.
Lemma lem1334632 (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_le x2 y2) : (treal_le x2 y2) = True.
Proof. exact (EQ_MP (@lem1334627 x2 y2) (@lem1334583 x2 y2 h1)). Qed.
Lemma lem1334633 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term28 x1 x2) = (term28 x1 x2).
Proof. exact (eq_refl (term28 x1 x2)). Qed.
Lemma lem1334634 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_le x2 y2) : (term17 x1 x2 y2) = (term29 x1 x2).
Proof. exact (MK_COMB (@lem1334633 x1 x2) (@lem1334632 x2 y2 h1)). Qed.
Lemma lem1334636 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1334637 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term29 x1 x2) = (treal_le x1 x2).
Proof. exact (@lem1334636 (treal_le x1 x2)). Qed.
Lemma lem1334638 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_le x2 y2) : (term17 x1 x2 y2) = (treal_le x1 x2).
Proof. exact (TRANS (@lem1334634 x1 x2 y2 h1) (@lem1334637 x1 x2)). Qed.
Lemma lem1334639 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_le x2 y2) : (treal_le x1 x2) = (term17 x1 x2 y2).
Proof. exact (SYM (@lem1334638 x1 x2 y2 h1)). Qed.
Lemma lem1334641 (x : prod hreal hreal) (y : prod hreal hreal) : term7 x y.
Proof. exact (EQ_MP (@lem1334413 x y) (@lem1334412 x y)). Qed.
Lemma lem1334642 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term7 x1 x2.
Proof. exact (@lem1334641 x1 x2). Qed.
Lemma lem1334644 (x : prod hreal hreal) (y : prod hreal hreal) : term7 x y.
Proof. exact (EQ_MP (@lem1334390 x y) (@lem1334389 x y)). Qed.
Lemma lem1334645 (y2 : prod hreal hreal) (y1 : prod hreal hreal) : term7 y2 y1.
Proof. exact (@lem1334644 y2 y1). Qed.
Lemma lem1334647 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_eq x y) = (treal_eq y x).
Proof. exact (EQ_MP (@lem1334367 y x) (@lem1334366 x y)). Qed.
Lemma lem1334648 (y1 : prod hreal hreal) (y2 : prod hreal hreal) : (treal_eq y2 y1) = (treal_eq y1 y2).
Proof. exact (@lem1334647 y1 y2). Qed.
Lemma lem1334649 (y2 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_eq y1 y2) = (treal_eq y2 y1).
Proof. exact (SYM (@lem1334648 y1 y2)). Qed.
Lemma lem1334650 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (treal_eq x1 x2) = ((treal_eq x1 x2) = True).
Proof. exact (@lem7 (treal_eq x1 x2)). Qed.
Lemma lem1334657 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : (treal_eq x1 x2) = True.
Proof. exact (EQ_MP (@lem1334650 x1 x2) (@lem1334581 x1 x2 h1)). Qed.
Lemma lem1334658 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : True = (treal_eq x1 x2).
Proof. exact (SYM (@lem1334657 x1 x2 h1)). Qed.
Lemma lem1334659 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_eq x1 x2.
Proof. exact (EQ_MP (@lem1334658 x1 x2 h1) (@lem0)). Qed.
Lemma lem1334662 (y1 : prod hreal hreal) (y2 : prod hreal hreal) : (treal_eq y1 y2) = ((treal_eq y1 y2) = True).
Proof. exact (@lem7 (treal_eq y1 y2)). Qed.
Lemma lem1334667 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : (treal_eq y1 y2) = True.
Proof. exact (EQ_MP (@lem1334662 y1 y2) (@lem1334580 y1 y2 h1)). Qed.
Lemma lem1334668 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : True = (treal_eq y1 y2).
Proof. exact (SYM (@lem1334667 y1 y2 h1)). Qed.
Lemma lem1334669 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : treal_eq y1 y2.
Proof. exact (EQ_MP (@lem1334668 y1 y2 h1) (@lem0)). Qed.
Lemma lem1334670 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (treal_eq x1 x2) = ((treal_eq x1 x2) = True).
Proof. exact (@lem7 (treal_eq x1 x2)). Qed.
Lemma lem1334677 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : (treal_eq x1 x2) = True.
Proof. exact (EQ_MP (@lem1334670 x1 x2) (@lem1334581 x1 x2 h1)). Qed.
Lemma lem1334678 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : True = (treal_eq x1 x2).
Proof. exact (SYM (@lem1334677 x1 x2 h1)). Qed.
Lemma lem1334679 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_eq x1 x2.
Proof. exact (EQ_MP (@lem1334678 x1 x2 h1) (@lem0)). Qed.
Lemma lem1334682 (y1 : prod hreal hreal) (y2 : prod hreal hreal) : (treal_eq y1 y2) = ((treal_eq y1 y2) = True).
Proof. exact (@lem7 (treal_eq y1 y2)). Qed.
Lemma lem1334687 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : (treal_eq y1 y2) = True.
Proof. exact (EQ_MP (@lem1334682 y1 y2) (@lem1334580 y1 y2 h1)). Qed.
Lemma lem1334688 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : True = (treal_eq y1 y2).
Proof. exact (SYM (@lem1334687 y1 y2 h1)). Qed.
Lemma lem1334689 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : treal_eq y1 y2.
Proof. exact (EQ_MP (@lem1334688 y1 y2 h1) (@lem0)). Qed.
Lemma lem1334690 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : treal_eq y2 y1.
Proof. exact (EQ_MP (@lem1334649 y2 y1) (@lem1334689 y1 y2 h1)). Qed.
Lemma lem1334691 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : treal_le y2 y1.
Proof. exact (@lem1334645 y2 y1 (@lem1334690 y1 y2 h1)). Qed.
Lemma lem1334692 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_le x1 x2.
Proof. exact (@lem1334642 x1 x2 (@lem1334679 x1 x2 h1)). Qed.
Lemma lem1334693 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_le x2 y2) : term17 x1 x2 y2.
Proof. exact (EQ_MP (@lem1334639 x1 x2 y2 h2) (@lem1334692 x1 x2 h1)). Qed.
Lemma lem1334694 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_le x2 y2) : term19 x1 y2.
Proof. exact (ex_intro (term20 x1 y2) x2 (@lem1334693 x1 x2 y2 h1 h2)). Qed.
Lemma lem1334695 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_le x2 y2) : treal_le x1 y2.
Proof. exact (@lem1334622 x1 y2 (@lem1334694 x1 x2 y2 h1 h2)). Qed.
Lemma lem1334696 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x2 y2) : term17 x1 y2 y1.
Proof. exact (conj (@lem1334695 x1 x2 y2 h1 h3) (@lem1334691 y1 y2 h2)). Qed.
Lemma lem1334697 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x2 y2) : term19 x1 y1.
Proof. exact (ex_intro (term20 x1 y1) y2 (@lem1334696 x1 y1 x2 y2 h1 h2 h3)). Qed.
Lemma lem1334698 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x2 y2) : treal_le x1 y1.
Proof. exact (@lem1334619 x1 y1 (@lem1334697 x1 y1 x2 y2 h1 h2 h3)). Qed.
Lemma lem1334699 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq y1 y2) : treal_le y1 y2.
Proof. exact (@lem1334616 y1 y2 (@lem1334669 y1 y2 h1)). Qed.
Lemma lem1334700 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_eq x2 x1.
Proof. exact (EQ_MP (@lem1334613 x2 x1) (@lem1334659 x1 x2 h1)). Qed.
Lemma lem1334701 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_le x2 x1.
Proof. exact (@lem1334609 x2 x1 (@lem1334700 x1 x2 h1)). Qed.
Lemma lem1334702 (x2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_le x1 y1) : term17 x2 x1 y1.
Proof. exact (EQ_MP (@lem1334606 x2 x1 y1 h2) (@lem1334701 x1 x2 h1)). Qed.
Lemma lem1334703 (x2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_le x1 y1) : term19 x2 y1.
Proof. exact (ex_intro (term20 x2 y1) x1 (@lem1334702 x2 x1 y1 h1 h2)). Qed.
Lemma lem1334704 (x2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_le x1 y1) : treal_le x2 y1.
Proof. exact (@lem1334589 x2 y1 (@lem1334703 x2 x1 y1 h1 h2)). Qed.
Lemma lem1334705 (x2 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x1 y1) : term17 x2 y1 y2.
Proof. exact (conj (@lem1334704 x2 x1 y1 h1 h3) (@lem1334699 y1 y2 h2)). Qed.
Lemma lem1334706 (x2 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x1 y1) : term19 x2 y2.
Proof. exact (ex_intro (term20 x2 y2) y1 (@lem1334705 x2 y2 x1 y1 h1 h2 h3)). Qed.
Lemma lem1334707 (x2 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x1 y1) : treal_le x2 y2.
Proof. exact (@lem1334586 x2 y2 (@lem1334706 x2 y2 x1 y1 h1 h2 h3)). Qed.
Lemma lem1334708 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x2 y2) : (treal_le x2 y2) = (treal_le x1 y1).
Proof. exact (prop_ext (fun h4 : treal_le x2 y2 => @lem1334698 x1 y1 x2 y2 h1 h2 h3) (fun h4 : treal_le x1 y1 => @lem1334583 x2 y2 h3)). Qed.
Lemma lem1334709 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x2 y2) : treal_le x1 y1.
Proof. exact (EQ_MP (@lem1334708 x1 y1 x2 y2 h1 h2 h3) (@lem1334583 x2 y2 h3)). Qed.
Lemma lem1334710 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : term30 x2 y2 x1 y1.
Proof. exact (fun h0 : treal_le x2 y2 => @lem1334709 x1 y1 x2 y2 h1 h2 h0). Qed.
Lemma lem1334711 (x2 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x1 y1) : (treal_le x1 y1) = (treal_le x2 y2).
Proof. exact (prop_ext (fun h4 : treal_le x1 y1 => @lem1334707 x2 y2 x1 y1 h1 h2 h3) (fun h4 : treal_le x2 y2 => @lem1334582 x1 y1 h3)). Qed.
Lemma lem1334712 (x2 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) (h3 : treal_le x1 y1) : treal_le x2 y2.
Proof. exact (EQ_MP (@lem1334711 x2 y2 x1 y1 h1 h2 h3) (@lem1334582 x1 y1 h3)). Qed.
Lemma lem1334713 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : term30 x1 y1 x2 y2.
Proof. exact (fun h0 : treal_le x1 y1 => @lem1334712 x2 y2 x1 y1 h1 h2 h0). Qed.
Lemma lem1334714 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : term31 x2 y2 x1 y1.
Proof. exact (conj (@lem1334713 x1 x2 y1 y2 h1 h2) (@lem1334710 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1334715 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : (term31 x2 y2 x1 y1) = ((treal_le x1 y1) = (treal_le x2 y2)).
Proof. exact (@lem32 (treal_le x1 y1) (treal_le x2 y2)). Qed.
Lemma lem1334716 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : (treal_le x1 y1) = (treal_le x2 y2).
Proof. exact (EQ_MP (@lem1334715 x1 y1 x2 y2) (@lem1334714 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1334717 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term27 x1 x2 y1 y2) : treal_eq y1 y2.
Proof. exact (proj2 (@lem1334579 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334718 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term27 x1 x2 y1 y2) : treal_eq x1 x2.
Proof. exact (proj1 (@lem1334579 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334719 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : (treal_eq y1 y2) = ((treal_le x1 y1) = (treal_le x2 y2)).
Proof. exact (prop_ext (fun h3 : treal_eq y1 y2 => @lem1334716 x1 x2 y1 y2 h1 h2) (fun h3 : (treal_le x1 y1) = (treal_le x2 y2) => @lem1334580 y1 y2 h2)). Qed.
Lemma lem1334720 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : (treal_le x1 y1) = (treal_le x2 y2).
Proof. exact (EQ_MP (@lem1334719 x1 x2 y1 y2 h1 h2) (@lem1334580 y1 y2 h2)). Qed.
Lemma lem1334721 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : (treal_eq x1 x2) = ((treal_le x1 y1) = (treal_le x2 y2)).
Proof. exact (prop_ext (fun h3 : treal_eq x1 x2 => @lem1334720 x1 x2 y1 y2 h1 h2) (fun h3 : (treal_le x1 y1) = (treal_le x2 y2) => @lem1334581 x1 x2 h1)). Qed.
Lemma lem1334722 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : treal_eq x1 x2) (h2 : treal_eq y1 y2) : (treal_le x1 y1) = (treal_le x2 y2).
Proof. exact (EQ_MP (@lem1334721 x1 x2 y1 y2 h1 h2) (@lem1334581 x1 x2 h1)). Qed.
Lemma lem1334723 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term27 x1 x2 y1 y2) (h2 : treal_eq x1 x2) : (treal_eq y1 y2) = ((treal_le x1 y1) = (treal_le x2 y2)).
Proof. exact (prop_ext (fun h3 : treal_eq y1 y2 => @lem1334722 x1 x2 y1 y2 h2 h3) (fun h3 : (treal_le x1 y1) = (treal_le x2 y2) => @lem1334717 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334724 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term27 x1 x2 y1 y2) (h2 : treal_eq x1 x2) : (treal_le x1 y1) = (treal_le x2 y2).
Proof. exact (EQ_MP (@lem1334723 y1 y2 x1 x2 h1 h2) (@lem1334717 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334725 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term27 x1 x2 y1 y2) : (treal_eq x1 x2) = ((treal_le x1 y1) = (treal_le x2 y2)).
Proof. exact (prop_ext (fun h2 : treal_eq x1 x2 => @lem1334724 y1 y2 x1 x2 h1 h2) (fun h2 : (treal_le x1 y1) = (treal_le x2 y2) => @lem1334718 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334726 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term27 x1 x2 y1 y2) : (treal_le x1 y1) = (treal_le x2 y2).
Proof. exact (EQ_MP (@lem1334725 x1 x2 y1 y2 h1) (@lem1334718 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334727 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term32 x1 y1 x2 y2.
Proof. exact (fun h0 : term27 x1 x2 y1 y2 => @lem1334726 x1 x2 y1 y2 h0). Qed.
Lemma lem1334732 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : term33 x1 y1 x2.
Proof. exact (fun y2 : prod hreal hreal => @lem1334727 x1 y1 x2 y2). Qed.
Lemma lem1334737 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term34 x1 x2.
Proof. exact (fun y1 : prod hreal hreal => @lem1334732 x1 y1 x2). Qed.
Lemma lem1334742 (x1 : prod hreal hreal) : term35 x1.
Proof. exact (fun x2 : prod hreal hreal => @lem1334737 x1 x2). Qed.
Lemma lem1334747 : term36.
Proof. exact (fun x1 : prod hreal hreal => @lem1334742 x1). Qed.
