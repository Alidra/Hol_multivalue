Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_WELLDEF_term_abbrevs.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_LE_WELLDEF_LEMMA_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1270267 (x : nadd) : term0 x.
Proof. exact (@lem1268060 x). Qed.
Lemma lem1270268 (x : nadd) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1270269 (x : nadd) : term1 x.
Proof. exact (EQ_MP (@lem1270268 x) (@lem1270267 x)). Qed.
Lemma lem1270270 (x : nadd) (y : nadd) : term2 x y.
Proof. exact (@lem1270269 x y). Qed.
Lemma lem1270271 (y : nadd) (x : nadd) : (term2 x y) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1270273 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1270274 (x : nadd) (h1 : term3) : term4 x.
Proof. exact (@lem1270273 h1 x). Qed.
Lemma lem1270275 (x : nadd) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1270276 (x : nadd) (h1 : term3) : term5 x.
Proof. exact (EQ_MP (@lem1270275 x) (@lem1270274 x h1)). Qed.
Lemma lem1270277 (x : nadd) (x' : nadd) (h1 : term3) : term6 x x'.
Proof. exact (@lem1270276 x h1 x'). Qed.
Lemma lem1270278 (x : nadd) (x' : nadd) : (term6 x x') = (term7 x x').
Proof. exact (eq_refl (term6 x x')). Qed.
Lemma lem1270279 (x : nadd) (x' : nadd) (h1 : term3) : term7 x x'.
Proof. exact (EQ_MP (@lem1270278 x x') (@lem1270277 x x' h1)). Qed.
Lemma lem1270280 (x : nadd) (x' : nadd) (y : nadd) (h1 : term3) : term8 x x' y.
Proof. exact (@lem1270279 x x' h1 y). Qed.
Lemma lem1270281 (x : nadd) (y : nadd) (x' : nadd) : (term8 x x' y) = (term9 x y x').
Proof. exact (eq_refl (term8 x x' y)). Qed.
Lemma lem1270282 (x : nadd) (y : nadd) (x' : nadd) (h1 : term3) : term9 x y x'.
Proof. exact (EQ_MP (@lem1270281 x y x') (@lem1270280 x x' y h1)). Qed.
Lemma lem1270283 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term3) : term10 x y x' y'.
Proof. exact (@lem1270282 x y x' h1 y'). Qed.
Lemma lem1270284 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term10 x y x' y') = (term11 x y x' y').
Proof. exact (eq_refl (term10 x y x' y')). Qed.
Lemma lem1270285 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term3) : term11 x y x' y'.
Proof. exact (EQ_MP (@lem1270284 x y x' y') (@lem1270283 x y x' y' h1)). Qed.
Lemma lem1270286 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term12 x' y' x y) : term12 x' y' x y.
Proof. exact (h1). Qed.
Lemma lem1270287 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term3) (h2 : term12 x' y' x y) : nadd_le x' y'.
Proof. exact (@lem1270285 x y x' y' h1 (@lem1270286 x' y' x y h2)). Qed.
Lemma lem1270288 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term12 x' y' x y) : term13 x' y'.
Proof. exact (fun h0 : term3 => @lem1270287 x' y' x y h0 h1). Qed.
Lemma lem1270289 (x' : nadd) (y' : nadd) (x : nadd) (h1 : term14 x' y' x) : term14 x' y' x.
Proof. exact (h1). Qed.
Lemma lem1270290 (x' : nadd) (y' : nadd) (x : nadd) (h1 : term14 x' y' x) : term13 x' y'.
Proof. exact (ex_elim (@lem1270289 x' y' x h1) (fun y : nadd => fun h0 : term15 x' y' x y => @lem1270288 x' y' x y h0)). Qed.
Lemma lem1270291 (x' : nadd) (y' : nadd) (h1 : term16 x' y') : term16 x' y'.
Proof. exact (h1). Qed.
Lemma lem1270292 (x' : nadd) (y' : nadd) (h1 : term16 x' y') : term13 x' y'.
Proof. exact (ex_elim (@lem1270291 x' y' h1) (fun x : nadd => fun h0 : term17 x' y' x => @lem1270290 x' y' x h0)). Qed.
Lemma lem1270293 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1270294 (x' : nadd) (y' : nadd) (h1 : term3) (h2 : term16 x' y') : nadd_le x' y'.
Proof. exact (@lem1270292 x' y' h2 (@lem1270293 h1)). Qed.
Lemma lem1270295 (x' : nadd) (y' : nadd) (h1 : term3) : term18 x' y'.
Proof. exact (fun h0 : term16 x' y' => @lem1270294 x' y' h1 h0). Qed.
Lemma lem1270296 (x' : nadd) (h1 : term3) : term19 x'.
Proof. exact (fun y' : nadd => @lem1270295 x' y' h1). Qed.
Lemma lem1270297 (h1 : term3) : term20.
Proof. exact (fun x' : nadd => @lem1270296 x' h1). Qed.
Lemma lem1270298 : term21.
Proof. exact (fun h0 : term3 => @lem1270297 h0). Qed.
Lemma lem1270299 : term20.
Proof. exact (@lem1270298 (@lem1270266)). Qed.
Lemma lem1270300 (x' : nadd) : term22 x'.
Proof. exact (@lem1270299 x'). Qed.
Lemma lem1270301 (x' : nadd) : (term22 x') = (term19 x').
Proof. exact (eq_refl (term22 x')). Qed.
Lemma lem1270302 (x' : nadd) : term19 x'.
Proof. exact (EQ_MP (@lem1270301 x') (@lem1270300 x')). Qed.
Lemma lem1270303 (x' : nadd) (y' : nadd) : term23 x' y'.
Proof. exact (@lem1270302 x' y'). Qed.
Lemma lem1270304 (x' : nadd) (y' : nadd) : (term23 x' y') = (term18 x' y').
Proof. exact (eq_refl (term23 x' y')). Qed.
Lemma lem1270306 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term24 x x' y y') : term24 x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1270307 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : nadd_eq y y'.
Proof. exact (h1). Qed.
Lemma lem1270308 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : nadd_eq x x'.
Proof. exact (h1). Qed.
Lemma lem1270309 (x : nadd) (y : nadd) (h1 : nadd_le x y) : nadd_le x y.
Proof. exact (h1). Qed.
Lemma lem1270310 (x' : nadd) (y' : nadd) (h1 : nadd_le x' y') : nadd_le x' y'.
Proof. exact (h1). Qed.
Lemma lem1270312 (x' : nadd) (y' : nadd) : term18 x' y'.
Proof. exact (EQ_MP (@lem1270304 x' y') (@lem1270303 x' y')). Qed.
Lemma lem1270314 (x' : nadd) (y' : nadd) : term18 x' y'.
Proof. exact (EQ_MP (@lem1270304 x' y') (@lem1270303 x' y')). Qed.
Lemma lem1270315 (x : nadd) (y : nadd) : term18 x y.
Proof. exact (@lem1270314 x y). Qed.
Lemma lem1270446 (y : nadd) (x : nadd) : (nadd_eq x y) = (nadd_eq y x).
Proof. exact (EQ_MP (@lem1270271 y x) (@lem1270270 x y)). Qed.
Lemma lem1270447 (x : nadd) (x' : nadd) : (nadd_eq x' x) = (nadd_eq x x').
Proof. exact (@lem1270446 x x'). Qed.
Lemma lem1270448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270449 (x : nadd) (x' : nadd) : (term25 x' x) = (term25 x x').
Proof. exact (MK_COMB (@lem1270448) (@lem1270447 x x')). Qed.
Lemma lem1270453 (y : nadd) (x : nadd) : (nadd_eq x y) = (nadd_eq y x).
Proof. exact (EQ_MP (@lem1270271 y x) (@lem1270270 x y)). Qed.
Lemma lem1270454 (y : nadd) (y' : nadd) : (nadd_eq y' y) = (nadd_eq y y').
Proof. exact (@lem1270453 y y'). Qed.
Lemma lem1270455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270456 (y : nadd) (y' : nadd) : (term25 y' y) = (term25 y y').
Proof. exact (MK_COMB (@lem1270455) (@lem1270454 y y')). Qed.
Lemma lem1270457 (x' : nadd) (y' : nadd) : (nadd_le x' y') = (nadd_le x' y').
Proof. exact (eq_refl (nadd_le x' y')). Qed.
Lemma lem1270458 (y : nadd) (x' : nadd) (y' : nadd) : (term26 y x' y') = (term27 y x' y').
Proof. exact (MK_COMB (@lem1270456 y y') (@lem1270457 x' y')). Qed.
Lemma lem1270459 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term12 x y x' y') = (term28 x y x' y').
Proof. exact (MK_COMB (@lem1270449 x x') (@lem1270458 y x' y')). Qed.
Lemma lem1270460 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term28 x y x' y') = (term12 x y x' y').
Proof. exact (SYM (@lem1270459 x y x' y')). Qed.
Lemma lem1270461 (x : nadd) (x' : nadd) : (nadd_eq x x') = ((nadd_eq x x') = True).
Proof. exact (@lem7 (nadd_eq x x')). Qed.
Lemma lem1270463 (y : nadd) (y' : nadd) : (nadd_eq y y') = ((nadd_eq y y') = True).
Proof. exact (@lem7 (nadd_eq y y')). Qed.
Lemma lem1270465 (x : nadd) (y : nadd) : (nadd_le x y) = ((nadd_le x y) = True).
Proof. exact (@lem7 (nadd_le x y)). Qed.
Lemma lem1270470 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : (nadd_eq x x') = True.
Proof. exact (EQ_MP (@lem1270461 x x') (@lem1270308 x x' h1)). Qed.
Lemma lem1270471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270472 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : (term25 x x') = (and True).
Proof. exact (MK_COMB (@lem1270471) (@lem1270470 x x' h1)). Qed.
Lemma lem1270476 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : (nadd_eq y y') = True.
Proof. exact (EQ_MP (@lem1270463 y y') (@lem1270307 y y' h1)). Qed.
Lemma lem1270477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270478 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : (term25 y y') = (and True).
Proof. exact (MK_COMB (@lem1270477) (@lem1270476 y y' h1)). Qed.
Lemma lem1270480 (x : nadd) (y : nadd) (h1 : nadd_le x y) : (nadd_le x y) = True.
Proof. exact (EQ_MP (@lem1270465 x y) (@lem1270309 x y h1)). Qed.
Lemma lem1270481 (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq y y') (h2 : nadd_le x y) : (term26 y' x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1270478 y y' h1) (@lem1270480 x y h2)). Qed.
Lemma lem1270483 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1270484 : (True /\ True) = True.
Proof. exact (@lem1270483 True). Qed.
Lemma lem1270485 (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq y y') (h2 : nadd_le x y) : (term26 y' x y) = True.
Proof. exact (TRANS (@lem1270481 y' x y h1 h2) (@lem1270484)). Qed.
Lemma lem1270486 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x y) : (term12 x' y' x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1270472 x x' h1) (@lem1270485 y' x y h2 h3)). Qed.
Lemma lem1270488 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1270489 : (True /\ True) = True.
Proof. exact (@lem1270488 True). Qed.
Lemma lem1270490 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x y) : (term12 x' y' x y) = True.
Proof. exact (TRANS (@lem1270486 x' y' x y h1 h2 h3) (@lem1270489)). Qed.
Lemma lem1270491 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x y) : True = (term12 x' y' x y).
Proof. exact (SYM (@lem1270490 x' y' x y h1 h2 h3)). Qed.
Lemma lem1270492 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x y) : term12 x' y' x y.
Proof. exact (EQ_MP (@lem1270491 x' y' x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1270493 (x : nadd) (x' : nadd) : (nadd_eq x x') = ((nadd_eq x x') = True).
Proof. exact (@lem7 (nadd_eq x x')). Qed.
Lemma lem1270495 (y : nadd) (y' : nadd) : (nadd_eq y y') = ((nadd_eq y y') = True).
Proof. exact (@lem7 (nadd_eq y y')). Qed.
Lemma lem1270497 (x' : nadd) (y' : nadd) : (nadd_le x' y') = ((nadd_le x' y') = True).
Proof. exact (@lem7 (nadd_le x' y')). Qed.
Lemma lem1270502 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : (nadd_eq x x') = True.
Proof. exact (EQ_MP (@lem1270493 x x') (@lem1270308 x x' h1)). Qed.
Lemma lem1270503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270504 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : (term25 x x') = (and True).
Proof. exact (MK_COMB (@lem1270503) (@lem1270502 x x' h1)). Qed.
Lemma lem1270508 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : (nadd_eq y y') = True.
Proof. exact (EQ_MP (@lem1270495 y y') (@lem1270307 y y' h1)). Qed.
Lemma lem1270509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270510 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : (term25 y y') = (and True).
Proof. exact (MK_COMB (@lem1270509) (@lem1270508 y y' h1)). Qed.
Lemma lem1270512 (x' : nadd) (y' : nadd) (h1 : nadd_le x' y') : (nadd_le x' y') = True.
Proof. exact (EQ_MP (@lem1270497 x' y') (@lem1270310 x' y' h1)). Qed.
Lemma lem1270513 (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq y y') (h2 : nadd_le x' y') : (term27 y x' y') = (True /\ True).
Proof. exact (MK_COMB (@lem1270510 y y' h1) (@lem1270512 x' y' h2)). Qed.
Lemma lem1270515 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1270516 : (True /\ True) = True.
Proof. exact (@lem1270515 True). Qed.
Lemma lem1270517 (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq y y') (h2 : nadd_le x' y') : (term27 y x' y') = True.
Proof. exact (TRANS (@lem1270513 y x' y' h1 h2) (@lem1270516)). Qed.
Lemma lem1270518 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : (term28 x y x' y') = (True /\ True).
Proof. exact (MK_COMB (@lem1270504 x x' h1) (@lem1270517 y x' y' h2 h3)). Qed.
Lemma lem1270520 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1270521 : (True /\ True) = True.
Proof. exact (@lem1270520 True). Qed.
Lemma lem1270522 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : (term28 x y x' y') = True.
Proof. exact (TRANS (@lem1270518 x y x' y' h1 h2 h3) (@lem1270521)). Qed.
Lemma lem1270523 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : True = (term28 x y x' y').
Proof. exact (SYM (@lem1270522 x y x' y' h1 h2 h3)). Qed.
Lemma lem1270524 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : term28 x y x' y'.
Proof. exact (EQ_MP (@lem1270523 x y x' y' h1 h2 h3) (@lem0)). Qed.
Lemma lem1270525 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : term12 x y x' y'.
Proof. exact (EQ_MP (@lem1270460 x y x' y') (@lem1270524 x y x' y' h1 h2 h3)). Qed.
Lemma lem1270526 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : term14 x y x'.
Proof. exact (ex_intro (term15 x y x') y' (@lem1270525 x y x' y' h1 h2 h3)). Qed.
Lemma lem1270528 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x y) : term14 x' y' x.
Proof. exact (ex_intro (term15 x' y' x) y (@lem1270492 x' y' x y h1 h2 h3)). Qed.
Lemma lem1270530 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : term16 x y.
Proof. exact (ex_intro (term17 x y) x' (@lem1270526 x y x' y' h1 h2 h3)). Qed.
Lemma lem1270531 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x y) : term16 x' y'.
Proof. exact (ex_intro (term17 x' y') x (@lem1270528 x' y' x y h1 h2 h3)). Qed.
Lemma lem1270532 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x' y') : nadd_le x y.
Proof. exact (@lem1270315 x y (@lem1270530 x y x' y' h1 h2 h3)). Qed.
Lemma lem1270533 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') (h3 : nadd_le x y) : nadd_le x' y'.
Proof. exact (@lem1270312 x' y' (@lem1270531 x' y' x y h1 h2 h3)). Qed.
Lemma lem1270534 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term29 x' y' x y.
Proof. exact (fun h0 : nadd_le x' y' => @lem1270532 x y x' y' h1 h2 h0). Qed.
Lemma lem1270535 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term29 x y x' y'.
Proof. exact (fun h0 : nadd_le x y => @lem1270533 x' y' x y h1 h2 h0). Qed.
Lemma lem1270536 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term30 x' y' x y.
Proof. exact (conj (@lem1270535 x x' y y' h1 h2) (@lem1270534 x x' y y' h1 h2)). Qed.
Lemma lem1270537 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term30 x' y' x y) = ((nadd_le x y) = (nadd_le x' y')).
Proof. exact (@lem32 (nadd_le x y) (nadd_le x' y')). Qed.
Lemma lem1270538 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : (nadd_le x y) = (nadd_le x' y').
Proof. exact (EQ_MP (@lem1270537 x y x' y') (@lem1270536 x x' y y' h1 h2)). Qed.
Lemma lem1270539 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term24 x x' y y') : nadd_eq y y'.
Proof. exact (proj2 (@lem1270306 x x' y y' h1)). Qed.
Lemma lem1270540 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term24 x x' y y') : nadd_eq x x'.
Proof. exact (proj1 (@lem1270306 x x' y y' h1)). Qed.
Lemma lem1270541 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : (nadd_eq y y') = ((nadd_le x y) = (nadd_le x' y')).
Proof. exact (prop_ext (fun h3 : nadd_eq y y' => @lem1270538 x x' y y' h1 h2) (fun h3 : (nadd_le x y) = (nadd_le x' y') => @lem1270307 y y' h2)). Qed.
Lemma lem1270542 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : (nadd_le x y) = (nadd_le x' y').
Proof. exact (EQ_MP (@lem1270541 x x' y y' h1 h2) (@lem1270307 y y' h2)). Qed.
Lemma lem1270543 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : (nadd_eq x x') = ((nadd_le x y) = (nadd_le x' y')).
Proof. exact (prop_ext (fun h3 : nadd_eq x x' => @lem1270542 x x' y y' h1 h2) (fun h3 : (nadd_le x y) = (nadd_le x' y') => @lem1270308 x x' h1)). Qed.
Lemma lem1270544 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : (nadd_le x y) = (nadd_le x' y').
Proof. exact (EQ_MP (@lem1270543 x x' y y' h1 h2) (@lem1270308 x x' h1)). Qed.
Lemma lem1270545 (y : nadd) (y' : nadd) (x : nadd) (x' : nadd) (h1 : term24 x x' y y') (h2 : nadd_eq x x') : (nadd_eq y y') = ((nadd_le x y) = (nadd_le x' y')).
Proof. exact (prop_ext (fun h3 : nadd_eq y y' => @lem1270544 x x' y y' h2 h3) (fun h3 : (nadd_le x y) = (nadd_le x' y') => @lem1270539 x x' y y' h1)). Qed.
Lemma lem1270546 (y : nadd) (y' : nadd) (x : nadd) (x' : nadd) (h1 : term24 x x' y y') (h2 : nadd_eq x x') : (nadd_le x y) = (nadd_le x' y').
Proof. exact (EQ_MP (@lem1270545 y y' x x' h1 h2) (@lem1270539 x x' y y' h1)). Qed.
Lemma lem1270547 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term24 x x' y y') : (nadd_eq x x') = ((nadd_le x y) = (nadd_le x' y')).
Proof. exact (prop_ext (fun h2 : nadd_eq x x' => @lem1270546 y y' x x' h1 h2) (fun h2 : (nadd_le x y) = (nadd_le x' y') => @lem1270540 x x' y y' h1)). Qed.
Lemma lem1270548 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term24 x x' y y') : (nadd_le x y) = (nadd_le x' y').
Proof. exact (EQ_MP (@lem1270547 x x' y y' h1) (@lem1270540 x x' y y' h1)). Qed.
Lemma lem1270549 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term31 x y x' y'.
Proof. exact (fun h0 : term24 x x' y y' => @lem1270548 x x' y y' h0). Qed.
Lemma lem1270554 (x : nadd) (y : nadd) (x' : nadd) : term32 x y x'.
Proof. exact (fun y' : nadd => @lem1270549 x y x' y'). Qed.
Lemma lem1270559 (x : nadd) (x' : nadd) : term33 x x'.
Proof. exact (fun y : nadd => @lem1270554 x y x'). Qed.
Lemma lem1270564 (x : nadd) : term34 x.
Proof. exact (fun x' : nadd => @lem1270559 x x'). Qed.
Lemma lem1270569 : term35.
Proof. exact (fun x : nadd => @lem1270564 x). Qed.
