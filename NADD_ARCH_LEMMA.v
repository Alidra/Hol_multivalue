Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ARCH_LEMMA_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NADD_ADD_LID_spec.
Require Import NADD_ADD_SYM_spec.
Require Import NADD_ADD_WELLDEF_spec.
Require Import NADD_ARCH_ZERO_spec.
Require Import NADD_EQ_IMP_LE_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_LDISTRIB_spec.
Require Import NADD_LE_EXISTS_spec.
Require Import NADD_LE_LADD_spec.
Require Import NADD_LE_TOTAL_spec.
Require Import NADD_LE_WELLDEF_spec.
Require Import NADD_MUL_WELLDEF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1292369 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1292370 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1292371 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1292370 t1) (@lem1292369 t1)). Qed.
Lemma lem1292372 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1292371 t1 t2). Qed.
Lemma lem1292373 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1292374 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1292373 t1 t2) (@lem1292372 t1 t2)). Qed.
Lemma lem1292375 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1292374 t1 t2 t3). Qed.
Lemma lem1292376 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1292377 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1292376 t1 t2 t3) (@lem1292375 t1 t2 t3)). Qed.
Lemma lem1292378 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1292377 t1 t2 t3)). Qed.
Lemma lem1292379 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1292380 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1292381 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1292380 t1) (@lem1292379 t1)). Qed.
Lemma lem1292382 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1292381 t1 t2). Qed.
Lemma lem1292383 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1292384 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1292383 t1 t2) (@lem1292382 t1 t2)). Qed.
Lemma lem1292385 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1292384 t1 t2 t3). Qed.
Lemma lem1292386 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1292387 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1292386 t1 t2 t3) (@lem1292385 t1 t2 t3)). Qed.
Lemma lem1292388 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1292387 t1 t2 t3)). Qed.
Lemma lem1292389 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1292390 (x : nadd) (h1 : term7) : term8 x.
Proof. exact (@lem1292389 h1 x). Qed.
Lemma lem1292391 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1292392 (x : nadd) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1292391 x) (@lem1292390 x h1)). Qed.
Lemma lem1292393 (x : nadd) (k : nadd) (h1 : term7) : term10 x k.
Proof. exact (@lem1292392 x h1 k). Qed.
Lemma lem1292394 (k : nadd) (x : nadd) : (term10 x k) = (term11 k x).
Proof. exact (eq_refl (term10 x k)). Qed.
Lemma lem1292395 (k : nadd) (x : nadd) (h1 : term7) : term11 k x.
Proof. exact (EQ_MP (@lem1292394 k x) (@lem1292393 x k h1)). Qed.
Lemma lem1292396 (x : nadd) (k : nadd) (h1 : term12 x k) : term12 x k.
Proof. exact (h1). Qed.
Lemma lem1292397 (x : nadd) (k : nadd) (h1 : term7) (h2 : term12 x k) : term13 x.
Proof. exact (@lem1292395 k x h1 (@lem1292396 x k h2)). Qed.
Lemma lem1292398 (x : nadd) (k : nadd) (h1 : term12 x k) : term14 x.
Proof. exact (fun h0 : term7 => @lem1292397 x k h0 h1). Qed.
Lemma lem1292399 (x : nadd) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1292400 (x : nadd) (h1 : term15 x) : term14 x.
Proof. exact (ex_elim (@lem1292399 x h1) (fun k : nadd => fun h0 : term16 x k => @lem1292398 x k h0)). Qed.
Lemma lem1292401 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1292402 (x : nadd) (h1 : term7) (h2 : term15 x) : term13 x.
Proof. exact (@lem1292400 x h2 (@lem1292401 h1)). Qed.
Lemma lem1292403 (x : nadd) (h1 : term7) : term17 x.
Proof. exact (fun h0 : term15 x => @lem1292402 x h1 h0). Qed.
Lemma lem1292404 (h1 : term7) : term18.
Proof. exact (fun x : nadd => @lem1292403 x h1). Qed.
Lemma lem1292405 : term19.
Proof. exact (fun h0 : term7 => @lem1292404 h0). Qed.
Lemma lem1292406 : term18.
Proof. exact (@lem1292405 (@lem1292368)). Qed.
Lemma lem1292407 (x : nadd) : term20 x.
Proof. exact (@lem1292406 x). Qed.
Lemma lem1292408 (x : nadd) : (term20 x) = (term17 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1292410 (x : nadd) : term21 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1292411 (x : nadd) : (term21 x) = (nadd_eq x x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1292412 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1292411 x) (@lem1292410 x)). Qed.
Lemma lem1292413 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1292415 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1292416 (x : nadd) (h1 : term22) : term23 x.
Proof. exact (@lem1292415 h1 x). Qed.
Lemma lem1292417 (x : nadd) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1292418 (x : nadd) (h1 : term22) : term24 x.
Proof. exact (EQ_MP (@lem1292417 x) (@lem1292416 x h1)). Qed.
Lemma lem1292419 (x : nadd) (x' : nadd) (h1 : term22) : term25 x x'.
Proof. exact (@lem1292418 x h1 x'). Qed.
Lemma lem1292420 (x : nadd) (x' : nadd) : (term25 x x') = (term26 x x').
Proof. exact (eq_refl (term25 x x')). Qed.
Lemma lem1292421 (x : nadd) (x' : nadd) (h1 : term22) : term26 x x'.
Proof. exact (EQ_MP (@lem1292420 x x') (@lem1292419 x x' h1)). Qed.
Lemma lem1292422 (x : nadd) (x' : nadd) (y : nadd) (h1 : term22) : term27 x x' y.
Proof. exact (@lem1292421 x x' h1 y). Qed.
Lemma lem1292423 (x : nadd) (y : nadd) (x' : nadd) : (term27 x x' y) = (term28 x y x').
Proof. exact (eq_refl (term27 x x' y)). Qed.
Lemma lem1292424 (x : nadd) (y : nadd) (x' : nadd) (h1 : term22) : term28 x y x'.
Proof. exact (EQ_MP (@lem1292423 x y x') (@lem1292422 x x' y h1)). Qed.
Lemma lem1292425 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term22) : term29 x y x' y'.
Proof. exact (@lem1292424 x y x' h1 y'). Qed.
Lemma lem1292426 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term29 x y x' y') = (term30 x y x' y').
Proof. exact (eq_refl (term29 x y x' y')). Qed.
Lemma lem1292427 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term22) : term30 x y x' y'.
Proof. exact (EQ_MP (@lem1292426 x y x' y') (@lem1292425 x y x' y' h1)). Qed.
Lemma lem1292428 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term31 x x' y y') : term31 x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1292429 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term22) (h2 : term31 x x' y y') : term32 x y x' y'.
Proof. exact (@lem1292427 x y x' y' h1 (@lem1292428 x x' y y' h2)). Qed.
Lemma lem1292430 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term31 x x' y y') : term33 x y x' y'.
Proof. exact (fun h0 : term22 => @lem1292429 x x' y y' h0 h1). Qed.
Lemma lem1292431 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1292432 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term22) (h2 : term31 x x' y y') : term32 x y x' y'.
Proof. exact (@lem1292430 x x' y y' h2 (@lem1292431 h1)). Qed.
Lemma lem1292433 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term22) : term30 x y x' y'.
Proof. exact (fun h0 : term31 x x' y y' => @lem1292432 x x' y y' h1 h0). Qed.
Lemma lem1292434 (x : nadd) (y : nadd) (x' : nadd) (h1 : term22) : term28 x y x'.
Proof. exact (fun y' : nadd => @lem1292433 x y x' y' h1). Qed.
Lemma lem1292435 (x : nadd) (y : nadd) (h1 : term22) : term34 x y.
Proof. exact (fun x' : nadd => @lem1292434 x y x' h1). Qed.
Lemma lem1292436 (x : nadd) (h1 : term22) : term35 x.
Proof. exact (fun y : nadd => @lem1292435 x y h1). Qed.
Lemma lem1292437 (h1 : term22) : term36.
Proof. exact (fun x : nadd => @lem1292436 x h1). Qed.
Lemma lem1292438 : term37.
Proof. exact (fun h0 : term22 => @lem1292437 h0). Qed.
Lemma lem1292439 : term36.
Proof. exact (@lem1292438 (@lem1274424)). Qed.
Lemma lem1292440 (x : nadd) : term38 x.
Proof. exact (@lem1292439 x). Qed.
Lemma lem1292441 (x : nadd) : (term38 x) = (term35 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1292442 (x : nadd) : term35 x.
Proof. exact (EQ_MP (@lem1292441 x) (@lem1292440 x)). Qed.
Lemma lem1292443 (x : nadd) (y : nadd) : term39 x y.
Proof. exact (@lem1292442 x y). Qed.
Lemma lem1292444 (x : nadd) (y : nadd) : (term39 x y) = (term34 x y).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1292445 (x : nadd) (y : nadd) : term34 x y.
Proof. exact (EQ_MP (@lem1292444 x y) (@lem1292443 x y)). Qed.
Lemma lem1292446 (x : nadd) (y : nadd) (x' : nadd) : term40 x y x'.
Proof. exact (@lem1292445 x y x'). Qed.
Lemma lem1292447 (x : nadd) (y : nadd) (x' : nadd) : (term40 x y x') = (term28 x y x').
Proof. exact (eq_refl (term40 x y x')). Qed.
Lemma lem1292448 (x : nadd) (y : nadd) (x' : nadd) : term28 x y x'.
Proof. exact (EQ_MP (@lem1292447 x y x') (@lem1292446 x y x')). Qed.
Lemma lem1292449 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term29 x y x' y'.
Proof. exact (@lem1292448 x y x' y'). Qed.
Lemma lem1292450 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term29 x y x' y') = (term30 x y x' y').
Proof. exact (eq_refl (term29 x y x' y')). Qed.
Lemma lem1292452 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1292453 (x : nadd) (h1 : term41) : term42 x.
Proof. exact (@lem1292452 h1 x). Qed.
Lemma lem1292454 (x : nadd) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1292455 (x : nadd) (h1 : term41) : term43 x.
Proof. exact (EQ_MP (@lem1292454 x) (@lem1292453 x h1)). Qed.
Lemma lem1292456 (x : nadd) (y : nadd) (h1 : term41) : term44 x y.
Proof. exact (@lem1292455 x h1 y). Qed.
Lemma lem1292457 (y : nadd) (x : nadd) : (term44 x y) = (term45 y x).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1292458 (y : nadd) (x : nadd) (h1 : term41) : term45 y x.
Proof. exact (EQ_MP (@lem1292457 y x) (@lem1292456 x y h1)). Qed.
Lemma lem1292459 (y : nadd) (x : nadd) (z : nadd) (h1 : term41) : term46 y x z.
Proof. exact (@lem1292458 y x h1 z). Qed.
Lemma lem1292460 (y : nadd) (x : nadd) (z : nadd) : (term46 y x z) = (term47 y x z).
Proof. exact (eq_refl (term46 y x z)). Qed.
Lemma lem1292461 (y : nadd) (x : nadd) (z : nadd) (h1 : term41) : term47 y x z.
Proof. exact (EQ_MP (@lem1292460 y x z) (@lem1292459 y x z h1)). Qed.
Lemma lem1292462 (x : nadd) (y : nadd) (z : nadd) (h1 : term48 x y z) : term48 x y z.
Proof. exact (h1). Qed.
Lemma lem1292463 (x : nadd) (y : nadd) (z : nadd) (h1 : term41) (h2 : term48 x y z) : nadd_eq x z.
Proof. exact (@lem1292461 y x z h1 (@lem1292462 x y z h2)). Qed.
Lemma lem1292464 (x : nadd) (y : nadd) (z : nadd) (h1 : term48 x y z) : term49 x z.
Proof. exact (fun h0 : term41 => @lem1292463 x y z h0 h1). Qed.
Lemma lem1292465 (x : nadd) (z : nadd) (h1 : term50 x z) : term50 x z.
Proof. exact (h1). Qed.
Lemma lem1292466 (x : nadd) (z : nadd) (h1 : term50 x z) : term49 x z.
Proof. exact (ex_elim (@lem1292465 x z h1) (fun y : nadd => fun h0 : term51 x z y => @lem1292464 x y z h0)). Qed.
Lemma lem1292467 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1292468 (x : nadd) (z : nadd) (h1 : term41) (h2 : term50 x z) : nadd_eq x z.
Proof. exact (@lem1292466 x z h2 (@lem1292467 h1)). Qed.
Lemma lem1292469 (x : nadd) (z : nadd) (h1 : term41) : term52 x z.
Proof. exact (fun h0 : term50 x z => @lem1292468 x z h1 h0). Qed.
Lemma lem1292470 (x : nadd) (h1 : term41) : term53 x.
Proof. exact (fun z : nadd => @lem1292469 x z h1). Qed.
Lemma lem1292471 (h1 : term41) : term54.
Proof. exact (fun x : nadd => @lem1292470 x h1). Qed.
Lemma lem1292472 : term55.
Proof. exact (fun h0 : term41 => @lem1292471 h0). Qed.
Lemma lem1292473 : term54.
Proof. exact (@lem1292472 (@lem1268295)). Qed.
Lemma lem1292474 (x : nadd) : term56 x.
Proof. exact (@lem1292473 x). Qed.
Lemma lem1292475 (x : nadd) : (term56 x) = (term53 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1292476 (x : nadd) : term53 x.
Proof. exact (EQ_MP (@lem1292475 x) (@lem1292474 x)). Qed.
Lemma lem1292477 (x : nadd) (z : nadd) : term57 x z.
Proof. exact (@lem1292476 x z). Qed.
Lemma lem1292478 (x : nadd) (z : nadd) : (term57 x z) = (term52 x z).
Proof. exact (eq_refl (term57 x z)). Qed.
Lemma lem1292480 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1292481 (x : nadd) (h1 : term41) : term42 x.
Proof. exact (@lem1292480 h1 x). Qed.
Lemma lem1292482 (x : nadd) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1292483 (x : nadd) (h1 : term41) : term43 x.
Proof. exact (EQ_MP (@lem1292482 x) (@lem1292481 x h1)). Qed.
Lemma lem1292484 (x : nadd) (y : nadd) (h1 : term41) : term44 x y.
Proof. exact (@lem1292483 x h1 y). Qed.
Lemma lem1292485 (y : nadd) (x : nadd) : (term44 x y) = (term45 y x).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1292486 (y : nadd) (x : nadd) (h1 : term41) : term45 y x.
Proof. exact (EQ_MP (@lem1292485 y x) (@lem1292484 x y h1)). Qed.
Lemma lem1292487 (y : nadd) (x : nadd) (z : nadd) (h1 : term41) : term46 y x z.
Proof. exact (@lem1292486 y x h1 z). Qed.
Lemma lem1292488 (y : nadd) (x : nadd) (z : nadd) : (term46 y x z) = (term47 y x z).
Proof. exact (eq_refl (term46 y x z)). Qed.
Lemma lem1292489 (y : nadd) (x : nadd) (z : nadd) (h1 : term41) : term47 y x z.
Proof. exact (EQ_MP (@lem1292488 y x z) (@lem1292487 y x z h1)). Qed.
Lemma lem1292490 (x : nadd) (y : nadd) (z : nadd) (h1 : term48 x y z) : term48 x y z.
Proof. exact (h1). Qed.
Lemma lem1292491 (x : nadd) (y : nadd) (z : nadd) (h1 : term41) (h2 : term48 x y z) : nadd_eq x z.
Proof. exact (@lem1292489 y x z h1 (@lem1292490 x y z h2)). Qed.
Lemma lem1292492 (x : nadd) (y : nadd) (z : nadd) (h1 : term48 x y z) : term49 x z.
Proof. exact (fun h0 : term41 => @lem1292491 x y z h0 h1). Qed.
Lemma lem1292493 (x : nadd) (z : nadd) (h1 : term50 x z) : term50 x z.
Proof. exact (h1). Qed.
Lemma lem1292494 (x : nadd) (z : nadd) (h1 : term50 x z) : term49 x z.
Proof. exact (ex_elim (@lem1292493 x z h1) (fun y : nadd => fun h0 : term51 x z y => @lem1292492 x y z h0)). Qed.
Lemma lem1292495 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1292496 (x : nadd) (z : nadd) (h1 : term41) (h2 : term50 x z) : nadd_eq x z.
Proof. exact (@lem1292494 x z h2 (@lem1292495 h1)). Qed.
Lemma lem1292497 (x : nadd) (z : nadd) (h1 : term41) : term52 x z.
Proof. exact (fun h0 : term50 x z => @lem1292496 x z h1 h0). Qed.
Lemma lem1292498 (x : nadd) (h1 : term41) : term53 x.
Proof. exact (fun z : nadd => @lem1292497 x z h1). Qed.
Lemma lem1292499 (h1 : term41) : term54.
Proof. exact (fun x : nadd => @lem1292498 x h1). Qed.
Lemma lem1292500 : term55.
Proof. exact (fun h0 : term41 => @lem1292499 h0). Qed.
Lemma lem1292501 : term54.
Proof. exact (@lem1292500 (@lem1268295)). Qed.
Lemma lem1292502 (x : nadd) : term56 x.
Proof. exact (@lem1292501 x). Qed.
Lemma lem1292503 (x : nadd) : (term56 x) = (term53 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1292504 (x : nadd) : term53 x.
Proof. exact (EQ_MP (@lem1292503 x) (@lem1292502 x)). Qed.
Lemma lem1292505 (x : nadd) (z : nadd) : term57 x z.
Proof. exact (@lem1292504 x z). Qed.
Lemma lem1292506 (x : nadd) (z : nadd) : (term57 x z) = (term52 x z).
Proof. exact (eq_refl (term57 x z)). Qed.
Lemma lem1292508 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem1292509 (x : nadd) (h1 : term58) : term59 x.
Proof. exact (@lem1292508 h1 x). Qed.
Lemma lem1292510 (x : nadd) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1292511 (x : nadd) (h1 : term58) : term60 x.
Proof. exact (EQ_MP (@lem1292510 x) (@lem1292509 x h1)). Qed.
Lemma lem1292512 (x : nadd) (y : nadd) (h1 : term58) : term61 x y.
Proof. exact (@lem1292511 x h1 y). Qed.
Lemma lem1292513 (x : nadd) (y : nadd) : (term61 x y) = (term62 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1292514 (x : nadd) (y : nadd) (h1 : term58) : term62 x y.
Proof. exact (EQ_MP (@lem1292513 x y) (@lem1292512 x y h1)). Qed.
Lemma lem1292515 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1292516 (x : nadd) (y : nadd) (h1 : term58) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1292514 x y h1 (@lem1292515 x y h2)). Qed.
Lemma lem1292517 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term63 x y.
Proof. exact (fun h0 : term58 => @lem1292516 x y h0 h1). Qed.
Lemma lem1292518 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem1292519 (x : nadd) (y : nadd) (h1 : term58) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1292517 x y h2 (@lem1292518 h1)). Qed.
Lemma lem1292520 (x : nadd) (y : nadd) (h1 : term58) : term62 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1292519 x y h1 h0). Qed.
Lemma lem1292521 (x : nadd) (h1 : term58) : term60 x.
Proof. exact (fun y : nadd => @lem1292520 x y h1). Qed.
Lemma lem1292522 (h1 : term58) : term58.
Proof. exact (fun x : nadd => @lem1292521 x h1). Qed.
Lemma lem1292523 : term64.
Proof. exact (fun h0 : term58 => @lem1292522 h0). Qed.
Lemma lem1292524 : term58.
Proof. exact (@lem1292523 (@lem1279763)). Qed.
Lemma lem1292525 (x : nadd) : term59 x.
Proof. exact (@lem1292524 x). Qed.
Lemma lem1292526 (x : nadd) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1292527 (x : nadd) : term60 x.
Proof. exact (EQ_MP (@lem1292526 x) (@lem1292525 x)). Qed.
Lemma lem1292528 (x : nadd) (y : nadd) : term61 x y.
Proof. exact (@lem1292527 x y). Qed.
Lemma lem1292529 (x : nadd) (y : nadd) : (term61 x y) = (term62 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1292531 (x : nadd) : term65 x.
Proof. exact (@lem1276037 x). Qed.
Lemma lem1292532 (x : nadd) : (term65 x) = (term66 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1292533 (x : nadd) : term66 x.
Proof. exact (EQ_MP (@lem1292532 x) (@lem1292531 x)). Qed.
Lemma lem1292534 (x : nadd) (y : nadd) : term67 x y.
Proof. exact (@lem1292533 x y). Qed.
Lemma lem1292535 (y : nadd) (x : nadd) : (term67 x y) = (term68 y x).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1292537 (x : nadd) : term69 x.
Proof. exact (@lem1273055 x). Qed.
Lemma lem1292538 (x : nadd) : (term69 x) = (term70 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1292539 (x : nadd) : term70 x.
Proof. exact (EQ_MP (@lem1292538 x) (@lem1292537 x)). Qed.
Lemma lem1292540 (x : nadd) (y : nadd) : term71 x y.
Proof. exact (@lem1292539 x y). Qed.
Lemma lem1292541 (y : nadd) (x : nadd) : (term71 x y) = (term72 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1292542 (y : nadd) (x : nadd) : term72 y x.
Proof. exact (EQ_MP (@lem1292541 y x) (@lem1292540 x y)). Qed.
Lemma lem1292543 (x : nadd) (y : nadd) (h1 : nadd_le x y) : nadd_le x y.
Proof. exact (h1). Qed.
Lemma lem1292544 (y : nadd) (x : nadd) (h1 : nadd_le y x) : nadd_le y x.
Proof. exact (h1). Qed.
Lemma lem1292545 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term73 x y z.
Proof. exact (h1). Qed.
Lemma lem1292551 (x : nadd) (y : nadd) : (nadd_le x y) = ((nadd_le x y) = True).
Proof. exact (@lem7 (nadd_le x y)). Qed.
Lemma lem1292554 (x : nadd) (y : nadd) (h1 : nadd_le x y) : (nadd_le x y) = True.
Proof. exact (EQ_MP (@lem1292551 x y) (@lem1292543 x y h1)). Qed.
Lemma lem1292555 (x : nadd) (y : nadd) (h1 : nadd_le x y) : True = (nadd_le x y).
Proof. exact (SYM (@lem1292554 x y h1)). Qed.
Lemma lem1292556 (x : nadd) (y : nadd) (h1 : nadd_le x y) : nadd_le x y.
Proof. exact (EQ_MP (@lem1292555 x y h1) (@lem0)). Qed.
Lemma lem1292567 (y : nadd) (x : nadd) : term68 y x.
Proof. exact (EQ_MP (@lem1292535 y x) (@lem1292534 x y)). Qed.
Lemma lem1292568 (x : nadd) (y : nadd) : term68 x y.
Proof. exact (@lem1292567 x y). Qed.
Lemma lem1292569 (y : nadd) (x : nadd) (h1 : nadd_le y x) : term74 x y.
Proof. exact (@lem1292568 x y (@lem1292544 y x h1)). Qed.
Lemma lem1292570 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term75 x y d.
Proof. exact (h1). Qed.
Lemma lem1292572 (x : nadd) (y : nadd) : term62 x y.
Proof. exact (EQ_MP (@lem1292529 x y) (@lem1292528 x y)). Qed.
Lemma lem1292574 (x : nadd) (z : nadd) : term52 x z.
Proof. exact (EQ_MP (@lem1292506 x z) (@lem1292505 x z)). Qed.
Lemma lem1292575 (x : nadd) (y : nadd) : term52 x y.
Proof. exact (@lem1292574 x y). Qed.
Lemma lem1292583 (x : nadd) (y : nadd) (d : nadd) : (term75 x y d) = ((term75 x y d) = True).
Proof. exact (@lem7 (term75 x y d)). Qed.
Lemma lem1292588 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : (term75 x y d) = True.
Proof. exact (EQ_MP (@lem1292583 x y d) (@lem1292570 x y d h1)). Qed.
Lemma lem1292589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1292590 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : (term76 x y d) = (and True).
Proof. exact (MK_COMB (@lem1292589) (@lem1292588 x y d h1)). Qed.
Lemma lem1292591 (d : nadd) (y : nadd) : (term77 d y) = (term77 d y).
Proof. exact (eq_refl (term77 d y)). Qed.
Lemma lem1292592 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : (term78 x d y) = (term79 d y).
Proof. exact (MK_COMB (@lem1292590 x y d h1) (@lem1292591 d y)). Qed.
Lemma lem1292594 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1292595 (d : nadd) (y : nadd) : (term79 d y) = (term77 d y).
Proof. exact (@lem1292594 (term77 d y)). Qed.
Lemma lem1292596 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : (term78 x d y) = (term77 d y).
Proof. exact (TRANS (@lem1292592 x y d h1) (@lem1292595 d y)). Qed.
Lemma lem1292597 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : (term77 d y) = (term78 x d y).
Proof. exact (SYM (@lem1292596 x y d h1)). Qed.
Lemma lem1292599 (x : nadd) (z : nadd) : term52 x z.
Proof. exact (EQ_MP (@lem1292478 x z) (@lem1292477 x z)). Qed.
Lemma lem1292600 (d : nadd) (y : nadd) : term80 d y.
Proof. exact (@lem1292599 (nadd_add y d) y). Qed.
Lemma lem1292602 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term30 x y x' y'.
Proof. exact (EQ_MP (@lem1292450 x y x' y') (@lem1292449 x y x' y')). Qed.
Lemma lem1292603 (d : nadd) (y : nadd) : term81 d y.
Proof. exact (@lem1292602 y d y term82). Qed.
Lemma lem1292607 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1292413 x) (@lem1292412 x)). Qed.
Lemma lem1292608 (y : nadd) : (nadd_eq y y) = True.
Proof. exact (@lem1292607 y). Qed.
Lemma lem1292609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1292610 (y : nadd) : (term83 y) = (and True).
Proof. exact (MK_COMB (@lem1292609) (@lem1292608 y)). Qed.
Lemma lem1292613 (d : nadd) : (term13 d) = (term13 d).
Proof. exact (eq_refl (term13 d)). Qed.
Lemma lem1292614 (y : nadd) (d : nadd) : (term84 y d) = (term85 d).
Proof. exact (MK_COMB (@lem1292610 y) (@lem1292613 d)). Qed.
Lemma lem1292616 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1292617 (d : nadd) : (term85 d) = (term13 d).
Proof. exact (@lem1292616 (term13 d)). Qed.
Lemma lem1292620 (y : nadd) (d : nadd) : (term84 y d) = (term13 d).
Proof. exact (TRANS (@lem1292614 y d) (@lem1292617 d)). Qed.
Lemma lem1292621 (y : nadd) (d : nadd) : (term13 d) = (term84 y d).
Proof. exact (SYM (@lem1292620 y d)). Qed.
Lemma lem1292623 (x : nadd) : term17 x.
Proof. exact (EQ_MP (@lem1292408 x) (@lem1292407 x)). Qed.
Lemma lem1292624 (d : nadd) : term17 d.
Proof. exact (@lem1292623 d). Qed.
Lemma lem1292626 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1292627 (d : nadd) (z : nadd) : (term12 d z) = (term87 d z).
Proof. exact (@lem1292626 (term12 d z)). Qed.
Lemma lem1292628 (d : nadd) (z : nadd) : (term87 d z) = (term12 d z).
Proof. exact (SYM (@lem1292627 d z)). Qed.
Lemma lem1292629 (d : nadd) (z : nadd) (h1 : term88 d z) : term88 d z.
Proof. exact (h1). Qed.
Lemma lem1292632 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term89 x y d z) : term89 x y d z.
Proof. exact (h1). Qed.
Lemma lem1292633 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : term90 x y d z.
Proof. exact (fun h0 : term89 x y d z => @lem1292632 x y d z h0). Qed.
Lemma lem1292634 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term90 x y d z) : term90 x y d z.
Proof. exact (h1). Qed.
Lemma lem1292635 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term89 x y d z) : term89 x y d z.
Proof. exact (h1). Qed.
Lemma lem1292636 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term89 x y d z) (h2 : term90 x y d z) : term89 x y d z.
Proof. exact (@lem1292634 x y d z h2 (@lem1292635 x y d z h1)). Qed.
Lemma lem1292637 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term89 x y d z) : term91 x y d z.
Proof. exact (fun h0 : term90 x y d z => @lem1292636 x y d z h1 h0). Qed.
Lemma lem1292638 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term90 x y d z) : term90 x y d z.
Proof. exact (h1). Qed.
Lemma lem1292639 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term89 x y d z) (h2 : term90 x y d z) : term89 x y d z.
Proof. exact (@lem1292637 x y d z h1 (@lem1292638 x y d z h2)). Qed.
Lemma lem1292640 (x : nadd) (y : nadd) (d : nadd) (z : nadd) (h1 : term90 x y d z) : term90 x y d z.
Proof. exact (fun h0 : term89 x y d z => @lem1292639 x y d z h0 h1). Qed.
Lemma lem1292641 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : term92 x y d z.
Proof. exact (fun h0 : term90 x y d z => @lem1292640 x y d z h0). Qed.
Lemma lem1292644 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : term90 x y d z.
Proof. exact (@lem1292641 x y d z (@lem1292633 x y d z)). Qed.
Lemma lem1292734 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1292735 : term93 = term94.
Proof. exact (@lem1292734 term95). Qed.
Lemma lem1292756 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1292757 : term97 = term98.
Proof. exact (MK_COMB (@lem1292756) (@lem1292735)). Qed.
Lemma lem1292760 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem1292761 : term100 = term101.
Proof. exact (MK_COMB (@lem1292760) (@lem1292757)). Qed.
Lemma lem1292764 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem1292765 : term103 = term104.
Proof. exact (MK_COMB (@lem1292764) (@lem1292761)). Qed.
Lemma lem1292768 : term105 = term105.
Proof. exact (eq_refl term105). Qed.
Lemma lem1292769 : term106 = term107.
Proof. exact (MK_COMB (@lem1292768) (@lem1292765)). Qed.
Lemma lem1292772 (d : nadd) (z : nadd) : (term108 d z) = (term108 d z).
Proof. exact (eq_refl (term108 d z)). Qed.
Lemma lem1292773 (d : nadd) (z : nadd) : (term109 d z) = (term110 d z).
Proof. exact (MK_COMB (@lem1292772 d z) (@lem1292769)). Qed.
Lemma lem1292776 (x : nadd) (y : nadd) (d : nadd) : (term111 x y d) = (term111 x y d).
Proof. exact (eq_refl (term111 x y d)). Qed.
Lemma lem1292777 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : (term112 x y d z) = (term113 x y d z).
Proof. exact (MK_COMB (@lem1292776 x y d) (@lem1292773 d z)). Qed.
Lemma lem1292780 (y : nadd) (x : nadd) : (term114 y x) = (term114 y x).
Proof. exact (eq_refl (term114 y x)). Qed.
Lemma lem1292781 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : (term115 x y d z) = (term116 x y d z).
Proof. exact (MK_COMB (@lem1292780 y x) (@lem1292777 x y d z)). Qed.
Lemma lem1292784 (x : nadd) (y : nadd) (z : nadd) : (term117 x y z) = (term117 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1292785 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : (term89 x y d z) = (term118 x y d z).
Proof. exact (MK_COMB (@lem1292784 x y z) (@lem1292781 x y d z)). Qed.
Lemma lem1292788 (y : nadd) (d : nadd) (z : nadd) : (term119 y d z) = (term120 y d z).
Proof. exact (fun_ext (fun x : nadd => @lem1292785 x y d z)). Qed.
Lemma lem1292789 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292790 (y : nadd) (d : nadd) (z : nadd) : (term121 y d z) = (term122 y d z).
Proof. exact (MK_COMB (@lem1292789) (@lem1292788 y d z)). Qed.
Lemma lem1292795 (d : nadd) (z : nadd) : (term123 d z) = (term124 d z).
Proof. exact (fun_ext (fun y : nadd => @lem1292790 y d z)). Qed.
Lemma lem1292796 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292797 (d : nadd) (z : nadd) : (term125 d z) = (term126 d z).
Proof. exact (MK_COMB (@lem1292796) (@lem1292795 d z)). Qed.
Lemma lem1292802 (z : nadd) : (term127 z) = (term128 z).
Proof. exact (fun_ext (fun d : nadd => @lem1292797 d z)). Qed.
Lemma lem1292803 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292804 (z : nadd) : (term129 z) = (term130 z).
Proof. exact (MK_COMB (@lem1292803) (@lem1292802 z)). Qed.
Lemma lem1292809 : term131 = term132.
Proof. exact (fun_ext (fun z : nadd => @lem1292804 z)). Qed.
Lemma lem1292810 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292819 : term133 = term134.
Proof. exact (MK_COMB (@lem1292810) (@lem1292809)). Qed.
Lemma lem1292828 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term135 x y x' y') = (term135 x y x' y').
Proof. exact (eq_refl (term135 x y x' y')). Qed.
Lemma lem1292829 (x : nadd) (y : nadd) (x' : nadd) : (term136 x y x') = (term136 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1292828 x y x' y')). Qed.
Lemma lem1292830 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292831 (x : nadd) (y : nadd) (x' : nadd) : (term137 x y x') = (term137 x y x').
Proof. exact (MK_COMB (@lem1292830) (@lem1292829 x y x')). Qed.
Lemma lem1292832 (x : nadd) (x' : nadd) : (term138 x x') = (term138 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1292831 x y x')). Qed.
Lemma lem1292833 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292834 (x : nadd) (x' : nadd) : (term139 x x') = (term139 x x').
Proof. exact (MK_COMB (@lem1292833) (@lem1292832 x x')). Qed.
Lemma lem1292835 (x : nadd) : (term140 x) = (term140 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1292834 x x')). Qed.
Lemma lem1292836 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292837 (x : nadd) : (term141 x) = (term141 x).
Proof. exact (MK_COMB (@lem1292836) (@lem1292835 x)). Qed.
Lemma lem1292838 : term142 = term142.
Proof. exact (fun_ext (fun x : nadd => @lem1292837 x)). Qed.
Lemma lem1292839 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292840 : term95 = term95.
Proof. exact (MK_COMB (@lem1292839) (@lem1292838)). Qed.
Lemma lem1292841 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1292842 : term94 = term94.
Proof. exact (MK_COMB (@lem1292841) (@lem1292840)). Qed.
Lemma lem1292855 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term143 x y x' y') = (term143 x y x' y').
Proof. exact (eq_refl (term143 x y x' y')). Qed.
Lemma lem1292856 (x : nadd) (y : nadd) (x' : nadd) : (term144 x y x') = (term144 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1292855 x y x' y')). Qed.
Lemma lem1292857 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292858 (x : nadd) (y : nadd) (x' : nadd) : (term145 x y x') = (term145 x y x').
Proof. exact (MK_COMB (@lem1292857) (@lem1292856 x y x')). Qed.
Lemma lem1292859 (x : nadd) (x' : nadd) : (term146 x x') = (term146 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1292858 x y x')). Qed.
Lemma lem1292860 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292861 (x : nadd) (x' : nadd) : (term147 x x') = (term147 x x').
Proof. exact (MK_COMB (@lem1292860) (@lem1292859 x x')). Qed.
Lemma lem1292862 (x : nadd) : (term148 x) = (term148 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1292861 x x')). Qed.
Lemma lem1292863 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292864 (x : nadd) : (term149 x) = (term149 x).
Proof. exact (MK_COMB (@lem1292863) (@lem1292862 x)). Qed.
Lemma lem1292865 : term150 = term150.
Proof. exact (fun_ext (fun x : nadd => @lem1292864 x)). Qed.
Lemma lem1292866 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292867 : term151 = term151.
Proof. exact (MK_COMB (@lem1292866) (@lem1292865)). Qed.
Lemma lem1292868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292869 : term96 = term96.
Proof. exact (MK_COMB (@lem1292868) (@lem1292867)). Qed.
Lemma lem1292870 : term98 = term98.
Proof. exact (MK_COMB (@lem1292869) (@lem1292842)). Qed.
Lemma lem1292871 (y : nadd) (x : nadd) (z : nadd) : (term152 y x z) = (term152 y x z).
Proof. exact (eq_refl (term152 y x z)). Qed.
Lemma lem1292872 (y : nadd) (x : nadd) : (term153 y x) = (term153 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1292871 y x z)). Qed.
Lemma lem1292873 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292874 (y : nadd) (x : nadd) : (term154 y x) = (term154 y x).
Proof. exact (MK_COMB (@lem1292873) (@lem1292872 y x)). Qed.
Lemma lem1292875 (x : nadd) : (term155 x) = (term155 x).
Proof. exact (fun_ext (fun y : nadd => @lem1292874 y x)). Qed.
Lemma lem1292876 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292877 (x : nadd) : (term156 x) = (term156 x).
Proof. exact (MK_COMB (@lem1292876) (@lem1292875 x)). Qed.
Lemma lem1292878 : term157 = term157.
Proof. exact (fun_ext (fun x : nadd => @lem1292877 x)). Qed.
Lemma lem1292879 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292880 : term158 = term158.
Proof. exact (MK_COMB (@lem1292879) (@lem1292878)). Qed.
Lemma lem1292881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292882 : term99 = term99.
Proof. exact (MK_COMB (@lem1292881) (@lem1292880)). Qed.
Lemma lem1292883 : term101 = term101.
Proof. exact (MK_COMB (@lem1292882) (@lem1292870)). Qed.
Lemma lem1292888 (x : nadd) (y : nadd) (z : nadd) : ((term159 y x z) = (nadd_le y z)) = ((term159 y x z) = (nadd_le y z)).
Proof. exact (eq_refl ((term159 y x z) = (nadd_le y z))). Qed.
Lemma lem1292889 (x : nadd) (y : nadd) : (term160 x y) = (term160 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1292888 x y z)). Qed.
Lemma lem1292890 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292891 (x : nadd) (y : nadd) : (term161 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem1292890) (@lem1292889 x y)). Qed.
Lemma lem1292892 (x : nadd) : (term162 x) = (term162 x).
Proof. exact (fun_ext (fun y : nadd => @lem1292891 x y)). Qed.
Lemma lem1292893 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292894 (x : nadd) : (term163 x) = (term163 x).
Proof. exact (MK_COMB (@lem1292893) (@lem1292892 x)). Qed.
Lemma lem1292895 : term164 = term164.
Proof. exact (fun_ext (fun x : nadd => @lem1292894 x)). Qed.
Lemma lem1292896 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292897 : term165 = term165.
Proof. exact (MK_COMB (@lem1292896) (@lem1292895)). Qed.
Lemma lem1292898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292899 : term102 = term102.
Proof. exact (MK_COMB (@lem1292898) (@lem1292897)). Qed.
Lemma lem1292900 : term104 = term104.
Proof. exact (MK_COMB (@lem1292899) (@lem1292883)). Qed.
Lemma lem1292901 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1292902 : term166 = term166.
Proof. exact (fun_ext (fun x : nadd => @lem1292901 x)). Qed.
Lemma lem1292903 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292904 : term167 = term167.
Proof. exact (MK_COMB (@lem1292903) (@lem1292902)). Qed.
Lemma lem1292905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292906 : term105 = term105.
Proof. exact (MK_COMB (@lem1292905) (@lem1292904)). Qed.
Lemma lem1292907 : term107 = term107.
Proof. exact (MK_COMB (@lem1292906) (@lem1292900)). Qed.
Lemma lem1292908 (n : nat) (d : nadd) (z : nadd) : (term168 n d z) = (term168 n d z).
Proof. exact (eq_refl (term168 n d z)). Qed.
Lemma lem1292909 (d : nadd) (z : nadd) : (term169 d z) = (term169 d z).
Proof. exact (fun_ext (fun n : nat => @lem1292908 n d z)). Qed.
Lemma lem1292910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1292911 (d : nadd) (z : nadd) : (term12 d z) = (term12 d z).
Proof. exact (MK_COMB (@lem1292910) (@lem1292909 d z)). Qed.
Lemma lem1292912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1292913 (d : nadd) (z : nadd) : (term88 d z) = (term88 d z).
Proof. exact (MK_COMB (@lem1292912) (@lem1292911 d z)). Qed.
Lemma lem1292914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292915 (d : nadd) (z : nadd) : (term108 d z) = (term108 d z).
Proof. exact (MK_COMB (@lem1292914) (@lem1292913 d z)). Qed.
Lemma lem1292916 (d : nadd) (z : nadd) : (term110 d z) = (term110 d z).
Proof. exact (MK_COMB (@lem1292915 d z) (@lem1292907)). Qed.
Lemma lem1292919 (x : nadd) (y : nadd) (d : nadd) : (term111 x y d) = (term111 x y d).
Proof. exact (eq_refl (term111 x y d)). Qed.
Lemma lem1292920 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : (term113 x y d z) = (term113 x y d z).
Proof. exact (MK_COMB (@lem1292919 x y d) (@lem1292916 d z)). Qed.
Lemma lem1292923 (y : nadd) (x : nadd) : (term114 y x) = (term114 y x).
Proof. exact (eq_refl (term114 y x)). Qed.
Lemma lem1292924 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : (term116 x y d z) = (term116 x y d z).
Proof. exact (MK_COMB (@lem1292923 y x) (@lem1292920 x y d z)). Qed.
Lemma lem1292925 (x : nadd) (n : nat) (y : nadd) (z : nadd) : (term170 x n y z) = (term170 x n y z).
Proof. exact (eq_refl (term170 x n y z)). Qed.
Lemma lem1292926 (x : nadd) (y : nadd) (z : nadd) : (term171 x y z) = (term171 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1292925 x n y z)). Qed.
Lemma lem1292927 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1292928 (x : nadd) (y : nadd) (z : nadd) : (term73 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1292927) (@lem1292926 x y z)). Qed.
Lemma lem1292929 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1292930 (x : nadd) (y : nadd) (z : nadd) : (term117 x y z) = (term117 x y z).
Proof. exact (MK_COMB (@lem1292929) (@lem1292928 x y z)). Qed.
Lemma lem1292931 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : (term118 x y d z) = (term118 x y d z).
Proof. exact (MK_COMB (@lem1292930 x y z) (@lem1292924 x y d z)). Qed.
Lemma lem1292932 (y : nadd) (d : nadd) (z : nadd) : (term120 y d z) = (term120 y d z).
Proof. exact (fun_ext (fun x : nadd => @lem1292931 x y d z)). Qed.
Lemma lem1292933 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292934 (y : nadd) (d : nadd) (z : nadd) : (term122 y d z) = (term122 y d z).
Proof. exact (MK_COMB (@lem1292933) (@lem1292932 y d z)). Qed.
Lemma lem1292935 (d : nadd) (z : nadd) : (term124 d z) = (term124 d z).
Proof. exact (fun_ext (fun y : nadd => @lem1292934 y d z)). Qed.
Lemma lem1292936 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292937 (d : nadd) (z : nadd) : (term126 d z) = (term126 d z).
Proof. exact (MK_COMB (@lem1292936) (@lem1292935 d z)). Qed.
Lemma lem1292938 (z : nadd) : (term128 z) = (term128 z).
Proof. exact (fun_ext (fun d : nadd => @lem1292937 d z)). Qed.
Lemma lem1292939 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292940 (z : nadd) : (term130 z) = (term130 z).
Proof. exact (MK_COMB (@lem1292939) (@lem1292938 z)). Qed.
Lemma lem1292941 : term132 = term132.
Proof. exact (fun_ext (fun z : nadd => @lem1292940 z)). Qed.
Lemma lem1292942 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1292943 : term134 = term134.
Proof. exact (MK_COMB (@lem1292942) (@lem1292941)). Qed.
Lemma lem1293096 : term133 = term134.
Proof. exact (TRANS (@lem1292819) (@lem1292943)). Qed.
Lemma lem1293097 : term134 = term133.
Proof. exact (SYM (@lem1293096)). Qed.
Lemma lem1293098 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term73 x y z.
Proof. exact (h1). Qed.
Lemma lem1293101 (d : nadd) (z : nadd) (h1 : term88 d z) : term88 d z.
Proof. exact (h1). Qed.
Lemma lem1293102 (h1 : term167) : term167.
Proof. exact (h1). Qed.
Lemma lem1293103 (h1 : term165) : term165.
Proof. exact (h1). Qed.
Lemma lem1293104 (h1 : term158) : term158.
Proof. exact (h1). Qed.
Lemma lem1293105 (h1 : term151) : term151.
Proof. exact (h1). Qed.
Lemma lem1293106 (h1 : term95) : term95.
Proof. exact (h1). Qed.
Lemma lem1293107 (x : nadd) (n : nat) (y : nadd) (z : nadd) : (term170 x n y z) = (term170 x n y z).
Proof. exact (eq_refl (term170 x n y z)). Qed.
Lemma lem1293108 (x : nadd) (y : nadd) (z : nadd) : (term171 x y z) = (term171 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1293107 x n y z)). Qed.
Lemma lem1293109 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1293118 (x : nadd) (y : nadd) (z : nadd) : (term73 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1293109) (@lem1293108 x y z)). Qed.
Lemma lem1293119 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term73 x y z.
Proof. exact (EQ_MP (@lem1293118 x y z) (@lem1293098 x y z h1)). Qed.
Lemma lem1293131 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term75 x y d.
Proof. exact (h1). Qed.
Lemma lem1293133 (P : nat -> Prop) : (term172 P) = (term173 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1293134 (d : nadd) (z : nadd) : (term88 d z) = (term174 d z).
Proof. exact (@lem1293133 (term169 d z)). Qed.
Lemma lem1293135 (n : nat) (d : nadd) (z : nadd) : (term175 d z n) = (term168 n d z).
Proof. exact (eq_refl (term175 d z n)). Qed.
Lemma lem1293136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1293138 (n : nat) (d : nadd) (z : nadd) : (term176 d z n) = (term177 n d z).
Proof. exact (MK_COMB (@lem1293136) (@lem1293135 n d z)). Qed.
Lemma lem1293139 (d : nadd) (z : nadd) : (term178 d z) = (term179 d z).
Proof. exact (fun_ext (fun n : nat => @lem1293138 n d z)). Qed.
Lemma lem1293140 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1293141 (d : nadd) (z : nadd) : (term174 d z) = (term180 d z).
Proof. exact (MK_COMB (@lem1293140) (@lem1293139 d z)). Qed.
Lemma lem1293150 (d : nadd) (z : nadd) : (term88 d z) = (term180 d z).
Proof. exact (TRANS (@lem1293134 d z) (@lem1293141 d z)). Qed.
Lemma lem1293151 (d : nadd) (z : nadd) (h1 : term88 d z) : term180 d z.
Proof. exact (EQ_MP (@lem1293150 d z) (@lem1293101 d z h1)). Qed.
Lemma lem1293152 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1293153 : term166 = term166.
Proof. exact (fun_ext (fun x : nadd => @lem1293152 x)). Qed.
Lemma lem1293154 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293163 : term167 = term167.
Proof. exact (MK_COMB (@lem1293154) (@lem1293153)). Qed.
Lemma lem1293164 (h1 : term167) : term167.
Proof. exact (EQ_MP (@lem1293163) (@lem1293102 h1)). Qed.
Lemma lem1293179 (x : nadd) (y : nadd) (z : nadd) : ((term159 y x z) = (nadd_le y z)) = (term181 x y z).
Proof. exact (@lem17784 (term159 y x z) (nadd_le y z)). Qed.
Lemma lem1293180 (x : nadd) (y : nadd) : (term160 x y) = (term182 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1293179 x y z)). Qed.
Lemma lem1293181 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293182 (x : nadd) (y : nadd) : (term161 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1293181) (@lem1293180 x y)). Qed.
Lemma lem1293183 (x : nadd) : (term162 x) = (term184 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293182 x y)). Qed.
Lemma lem1293184 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293185 (x : nadd) : (term163 x) = (term185 x).
Proof. exact (MK_COMB (@lem1293184) (@lem1293183 x)). Qed.
Lemma lem1293186 : term164 = term186.
Proof. exact (fun_ext (fun x : nadd => @lem1293185 x)). Qed.
Lemma lem1293187 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293188 : term165 = term187.
Proof. exact (MK_COMB (@lem1293187) (@lem1293186)). Qed.
Lemma lem1293198 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1293199 (P : nadd -> Prop) (Q : nadd -> Prop) : (term190 P Q) = (term191 P Q).
Proof. exact (@lem1293198 nadd P Q). Qed.
Lemma lem1293200 (x : nadd) (y : nadd) : (term192 x y) = (term193 x y).
Proof. exact (@lem1293199 (term194 x y) (term195 x y)). Qed.
Lemma lem1293201 (x : nadd) (y : nadd) (z : nadd) : (term196 x y z) = (term197 x y z).
Proof. exact (eq_refl (term196 x y z)). Qed.
Lemma lem1293202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1293203 (x : nadd) (y : nadd) (z : nadd) : (term198 x y z) = (term199 x y z).
Proof. exact (MK_COMB (@lem1293202) (@lem1293201 x y z)). Qed.
Lemma lem1293204 (x : nadd) (y : nadd) (z : nadd) : (term200 x y z) = (term201 x y z).
Proof. exact (eq_refl (term200 x y z)). Qed.
Lemma lem1293205 (x : nadd) (y : nadd) (z : nadd) : (term202 x y z) = (term181 x y z).
Proof. exact (MK_COMB (@lem1293203 x y z) (@lem1293204 x y z)). Qed.
Lemma lem1293206 (x : nadd) (y : nadd) : (term203 x y) = (term182 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1293205 x y z)). Qed.
Lemma lem1293207 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293208 (x : nadd) (y : nadd) : (term192 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1293207) (@lem1293206 x y)). Qed.
Lemma lem1293209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1293210 (x : nadd) (y : nadd) : (term204 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1293209) (@lem1293208 x y)). Qed.
Lemma lem1293211 (x : nadd) (y : nadd) (z : nadd) : (term196 x y z) = (term197 x y z).
Proof. exact (eq_refl (term196 x y z)). Qed.
Lemma lem1293212 (x : nadd) (y : nadd) : (term206 x y) = (term194 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1293211 x y z)). Qed.
Lemma lem1293213 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293214 (x : nadd) (y : nadd) : (term207 x y) = (term208 x y).
Proof. exact (MK_COMB (@lem1293213) (@lem1293212 x y)). Qed.
Lemma lem1293215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1293216 (x : nadd) (y : nadd) : (term209 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1293215) (@lem1293214 x y)). Qed.
Lemma lem1293217 (x : nadd) (y : nadd) (z : nadd) : (term200 x y z) = (term201 x y z).
Proof. exact (eq_refl (term200 x y z)). Qed.
Lemma lem1293218 (x : nadd) (y : nadd) : (term211 x y) = (term195 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1293217 x y z)). Qed.
Lemma lem1293219 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293220 (x : nadd) (y : nadd) : (term212 x y) = (term213 x y).
Proof. exact (MK_COMB (@lem1293219) (@lem1293218 x y)). Qed.
Lemma lem1293221 (x : nadd) (y : nadd) : (term193 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1293216 x y) (@lem1293220 x y)). Qed.
Lemma lem1293222 (x : nadd) (y : nadd) : ((term192 x y) = (term193 x y)) = ((term183 x y) = (term214 x y)).
Proof. exact (MK_COMB (@lem1293210 x y) (@lem1293221 x y)). Qed.
Lemma lem1293223 (x : nadd) (y : nadd) : (term183 x y) = (term214 x y).
Proof. exact (EQ_MP (@lem1293222 x y) (@lem1293200 x y)). Qed.
Lemma lem1293320 (x : nadd) : (term184 x) = (term215 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293223 x y)). Qed.
Lemma lem1293321 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293322 (x : nadd) : (term185 x) = (term216 x).
Proof. exact (MK_COMB (@lem1293321) (@lem1293320 x)). Qed.
Lemma lem1293324 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1293325 (P : nadd -> Prop) (Q : nadd -> Prop) : (term190 P Q) = (term191 P Q).
Proof. exact (@lem1293324 nadd P Q). Qed.
Lemma lem1293326 (x : nadd) : (term217 x) = (term218 x).
Proof. exact (@lem1293325 (term219 x) (term220 x)). Qed.
Lemma lem1293327 (x : nadd) (y : nadd) : (term221 x y) = (term208 x y).
Proof. exact (eq_refl (term221 x y)). Qed.
Lemma lem1293328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1293329 (x : nadd) (y : nadd) : (term222 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1293328) (@lem1293327 x y)). Qed.
Lemma lem1293330 (x : nadd) (y : nadd) : (term223 x y) = (term213 x y).
Proof. exact (eq_refl (term223 x y)). Qed.
Lemma lem1293331 (x : nadd) (y : nadd) : (term224 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1293329 x y) (@lem1293330 x y)). Qed.
Lemma lem1293332 (x : nadd) : (term225 x) = (term215 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293331 x y)). Qed.
Lemma lem1293333 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293334 (x : nadd) : (term217 x) = (term216 x).
Proof. exact (MK_COMB (@lem1293333) (@lem1293332 x)). Qed.
Lemma lem1293335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1293336 (x : nadd) : (term226 x) = (term227 x).
Proof. exact (MK_COMB (@lem1293335) (@lem1293334 x)). Qed.
Lemma lem1293337 (x : nadd) (y : nadd) : (term221 x y) = (term208 x y).
Proof. exact (eq_refl (term221 x y)). Qed.
Lemma lem1293338 (x : nadd) : (term228 x) = (term219 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293337 x y)). Qed.
Lemma lem1293339 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293340 (x : nadd) : (term229 x) = (term230 x).
Proof. exact (MK_COMB (@lem1293339) (@lem1293338 x)). Qed.
Lemma lem1293341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1293342 (x : nadd) : (term231 x) = (term232 x).
Proof. exact (MK_COMB (@lem1293341) (@lem1293340 x)). Qed.
Lemma lem1293343 (x : nadd) (y : nadd) : (term223 x y) = (term213 x y).
Proof. exact (eq_refl (term223 x y)). Qed.
Lemma lem1293344 (x : nadd) : (term233 x) = (term220 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293343 x y)). Qed.
Lemma lem1293345 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293346 (x : nadd) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1293345) (@lem1293344 x)). Qed.
Lemma lem1293347 (x : nadd) : (term218 x) = (term236 x).
Proof. exact (MK_COMB (@lem1293342 x) (@lem1293346 x)). Qed.
Lemma lem1293348 (x : nadd) : ((term217 x) = (term218 x)) = ((term216 x) = (term236 x)).
Proof. exact (MK_COMB (@lem1293336 x) (@lem1293347 x)). Qed.
Lemma lem1293349 (x : nadd) : (term216 x) = (term236 x).
Proof. exact (EQ_MP (@lem1293348 x) (@lem1293326 x)). Qed.
Lemma lem1293454 (x : nadd) : (term185 x) = (term236 x).
Proof. exact (TRANS (@lem1293322 x) (@lem1293349 x)). Qed.
Lemma lem1293455 : term186 = term237.
Proof. exact (fun_ext (fun x : nadd => @lem1293454 x)). Qed.
Lemma lem1293456 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293457 : term187 = term238.
Proof. exact (MK_COMB (@lem1293456) (@lem1293455)). Qed.
Lemma lem1293459 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1293460 (P : nadd -> Prop) (Q : nadd -> Prop) : (term190 P Q) = (term191 P Q).
Proof. exact (@lem1293459 nadd P Q). Qed.
Lemma lem1293461 : term239 = term240.
Proof. exact (@lem1293460 term241 term242). Qed.
Lemma lem1293462 (x : nadd) : (term243 x) = (term230 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1293463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1293464 (x : nadd) : (term244 x) = (term232 x).
Proof. exact (MK_COMB (@lem1293463) (@lem1293462 x)). Qed.
Lemma lem1293465 (x : nadd) : (term245 x) = (term235 x).
Proof. exact (eq_refl (term245 x)). Qed.
Lemma lem1293466 (x : nadd) : (term246 x) = (term236 x).
Proof. exact (MK_COMB (@lem1293464 x) (@lem1293465 x)). Qed.
Lemma lem1293467 : term247 = term237.
Proof. exact (fun_ext (fun x : nadd => @lem1293466 x)). Qed.
Lemma lem1293468 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293469 : term239 = term238.
Proof. exact (MK_COMB (@lem1293468) (@lem1293467)). Qed.
Lemma lem1293470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1293471 : term248 = term249.
Proof. exact (MK_COMB (@lem1293470) (@lem1293469)). Qed.
Lemma lem1293472 (x : nadd) : (term243 x) = (term230 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1293473 : term250 = term241.
Proof. exact (fun_ext (fun x : nadd => @lem1293472 x)). Qed.
Lemma lem1293474 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293475 : term251 = term252.
Proof. exact (MK_COMB (@lem1293474) (@lem1293473)). Qed.
Lemma lem1293476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1293477 : term253 = term254.
Proof. exact (MK_COMB (@lem1293476) (@lem1293475)). Qed.
Lemma lem1293478 (x : nadd) : (term245 x) = (term235 x).
Proof. exact (eq_refl (term245 x)). Qed.
Lemma lem1293479 : term255 = term242.
Proof. exact (fun_ext (fun x : nadd => @lem1293478 x)). Qed.
Lemma lem1293480 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293481 : term256 = term257.
Proof. exact (MK_COMB (@lem1293480) (@lem1293479)). Qed.
Lemma lem1293482 : term240 = term258.
Proof. exact (MK_COMB (@lem1293477) (@lem1293481)). Qed.
Lemma lem1293483 : (term239 = term240) = (term238 = term258).
Proof. exact (MK_COMB (@lem1293471) (@lem1293482)). Qed.
Lemma lem1293484 : term238 = term258.
Proof. exact (EQ_MP (@lem1293483) (@lem1293461)). Qed.
Lemma lem1293599 : term187 = term258.
Proof. exact (TRANS (@lem1293457) (@lem1293484)). Qed.
Lemma lem1293600 : term165 = term258.
Proof. exact (TRANS (@lem1293188) (@lem1293599)). Qed.
Lemma lem1293601 (h1 : term165) : term258.
Proof. exact (EQ_MP (@lem1293600) (@lem1293103 h1)). Qed.
Lemma lem1293602 (y : nadd) (x : nadd) (z : nadd) : (term152 y x z) = (term152 y x z).
Proof. exact (eq_refl (term152 y x z)). Qed.
Lemma lem1293603 (y : nadd) (x : nadd) : (term153 y x) = (term153 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1293602 y x z)). Qed.
Lemma lem1293604 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293605 (y : nadd) (x : nadd) : (term154 y x) = (term154 y x).
Proof. exact (MK_COMB (@lem1293604) (@lem1293603 y x)). Qed.
Lemma lem1293606 (x : nadd) : (term155 x) = (term155 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293605 y x)). Qed.
Lemma lem1293607 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293608 (x : nadd) : (term156 x) = (term156 x).
Proof. exact (MK_COMB (@lem1293607) (@lem1293606 x)). Qed.
Lemma lem1293609 : term157 = term157.
Proof. exact (fun_ext (fun x : nadd => @lem1293608 x)). Qed.
Lemma lem1293610 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293627 : term158 = term158.
Proof. exact (MK_COMB (@lem1293610) (@lem1293609)). Qed.
Lemma lem1293628 (h1 : term158) : term158.
Proof. exact (EQ_MP (@lem1293627) (@lem1293104 h1)). Qed.
Lemma lem1293635 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term259 x x' y y') = (term260 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1293650 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : ((nadd_le x y) = (nadd_le x' y')) = (term261 x y x' y').
Proof. exact (@lem17784 (nadd_le x y) (nadd_le x' y')). Qed.
Lemma lem1293651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1293652 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term262 x x' y y') = (term263 x x' y y').
Proof. exact (MK_COMB (@lem1293651) (@lem1293635 x x' y y')). Qed.
Lemma lem1293653 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term264 x y x' y') = (term265 x y x' y').
Proof. exact (MK_COMB (@lem1293652 x x' y y') (@lem1293650 x y x' y')). Qed.
Lemma lem1293654 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term143 x y x' y') = (term264 x y x' y').
Proof. exact (@lem17265 (term31 x x' y y') ((nadd_le x y) = (nadd_le x' y'))). Qed.
Lemma lem1293655 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term143 x y x' y') = (term265 x y x' y').
Proof. exact (TRANS (@lem1293654 x y x' y') (@lem1293653 x y x' y')). Qed.
Lemma lem1293656 (x : nadd) (y : nadd) (x' : nadd) : (term144 x y x') = (term266 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1293655 x y x' y')). Qed.
Lemma lem1293657 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293658 (x : nadd) (y : nadd) (x' : nadd) : (term145 x y x') = (term267 x y x').
Proof. exact (MK_COMB (@lem1293657) (@lem1293656 x y x')). Qed.
Lemma lem1293659 (x : nadd) (x' : nadd) : (term146 x x') = (term268 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1293658 x y x')). Qed.
Lemma lem1293660 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293661 (x : nadd) (x' : nadd) : (term147 x x') = (term269 x x').
Proof. exact (MK_COMB (@lem1293660) (@lem1293659 x x')). Qed.
Lemma lem1293662 (x : nadd) : (term148 x) = (term270 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1293661 x x')). Qed.
Lemma lem1293663 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293664 (x : nadd) : (term149 x) = (term271 x).
Proof. exact (MK_COMB (@lem1293663) (@lem1293662 x)). Qed.
Lemma lem1293665 : term150 = term272.
Proof. exact (fun_ext (fun x : nadd => @lem1293664 x)). Qed.
Lemma lem1293666 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293731 : term151 = term273.
Proof. exact (MK_COMB (@lem1293666) (@lem1293665)). Qed.
Lemma lem1293732 (h1 : term151) : term273.
Proof. exact (EQ_MP (@lem1293731) (@lem1293105 h1)). Qed.
Lemma lem1293739 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term259 x x' y y') = (term260 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1293740 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term274 x y x' y') = (term274 x y x' y').
Proof. exact (eq_refl (term274 x y x' y')). Qed.
Lemma lem1293741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1293742 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term262 x x' y y') = (term263 x x' y y').
Proof. exact (MK_COMB (@lem1293741) (@lem1293739 x x' y y')). Qed.
Lemma lem1293743 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term275 x y x' y') = (term276 x y x' y').
Proof. exact (MK_COMB (@lem1293742 x x' y y') (@lem1293740 x y x' y')). Qed.
Lemma lem1293744 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term135 x y x' y') = (term275 x y x' y').
Proof. exact (@lem17265 (term31 x x' y y') (term274 x y x' y')). Qed.
Lemma lem1293745 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term135 x y x' y') = (term276 x y x' y').
Proof. exact (TRANS (@lem1293744 x y x' y') (@lem1293743 x y x' y')). Qed.
Lemma lem1293746 (x : nadd) (y : nadd) (x' : nadd) : (term136 x y x') = (term277 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1293745 x y x' y')). Qed.
Lemma lem1293747 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293748 (x : nadd) (y : nadd) (x' : nadd) : (term137 x y x') = (term278 x y x').
Proof. exact (MK_COMB (@lem1293747) (@lem1293746 x y x')). Qed.
Lemma lem1293749 (x : nadd) (x' : nadd) : (term138 x x') = (term279 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1293748 x y x')). Qed.
Lemma lem1293750 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293751 (x : nadd) (x' : nadd) : (term139 x x') = (term280 x x').
Proof. exact (MK_COMB (@lem1293750) (@lem1293749 x x')). Qed.
Lemma lem1293752 (x : nadd) : (term140 x) = (term281 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1293751 x x')). Qed.
Lemma lem1293753 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293754 (x : nadd) : (term141 x) = (term282 x).
Proof. exact (MK_COMB (@lem1293753) (@lem1293752 x)). Qed.
Lemma lem1293755 : term142 = term283.
Proof. exact (fun_ext (fun x : nadd => @lem1293754 x)). Qed.
Lemma lem1293756 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293821 : term95 = term284.
Proof. exact (MK_COMB (@lem1293756) (@lem1293755)). Qed.
Lemma lem1293822 (h1 : term95) : term284.
Proof. exact (EQ_MP (@lem1293821) (@lem1293106 h1)). Qed.
Lemma lem1293844 (x : nadd) (n : nat) (y : nadd) (z : nadd) : (term170 x n y z) = (term170 x n y z).
Proof. exact (eq_refl (term170 x n y z)). Qed.
Lemma lem1293845 (x : nadd) (y : nadd) (z : nadd) : (term171 x y z) = (term171 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1293844 x n y z)). Qed.
Lemma lem1293846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1293847 (x : nadd) (y : nadd) (z : nadd) : (term73 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1293846) (@lem1293845 x y z)). Qed.
Lemma lem1293848 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term73 x y z.
Proof. exact (EQ_MP (@lem1293847 x y z) (@lem1293119 x y z h1)). Qed.
Lemma lem1293864 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term75 x y d.
Proof. exact (h1). Qed.
Lemma lem1293869 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1293870 : term166 = term166.
Proof. exact (fun_ext (fun x : nadd => @lem1293869 x)). Qed.
Lemma lem1293871 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293872 : term167 = term167.
Proof. exact (MK_COMB (@lem1293871) (@lem1293870)). Qed.
Lemma lem1293873 (h1 : term167) : term167.
Proof. exact (EQ_MP (@lem1293872) (@lem1293164 h1)). Qed.
Lemma lem1293896 (x : nadd) (y : nadd) (z : nadd) : (term201 x y z) = (term201 x y z).
Proof. exact (eq_refl (term201 x y z)). Qed.
Lemma lem1293897 (x : nadd) (y : nadd) : (term195 x y) = (term195 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1293896 x y z)). Qed.
Lemma lem1293898 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293899 (x : nadd) (y : nadd) : (term213 x y) = (term213 x y).
Proof. exact (MK_COMB (@lem1293898) (@lem1293897 x y)). Qed.
Lemma lem1293900 (x : nadd) : (term220 x) = (term220 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293899 x y)). Qed.
Lemma lem1293901 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293902 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (MK_COMB (@lem1293901) (@lem1293900 x)). Qed.
Lemma lem1293903 : term242 = term242.
Proof. exact (fun_ext (fun x : nadd => @lem1293902 x)). Qed.
Lemma lem1293904 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293905 : term257 = term257.
Proof. exact (MK_COMB (@lem1293904) (@lem1293903)). Qed.
Lemma lem1293928 (x : nadd) (y : nadd) (z : nadd) : (term197 x y z) = (term197 x y z).
Proof. exact (eq_refl (term197 x y z)). Qed.
Lemma lem1293929 (x : nadd) (y : nadd) : (term194 x y) = (term194 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1293928 x y z)). Qed.
Lemma lem1293930 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293931 (x : nadd) (y : nadd) : (term208 x y) = (term208 x y).
Proof. exact (MK_COMB (@lem1293930) (@lem1293929 x y)). Qed.
Lemma lem1293932 (x : nadd) : (term219 x) = (term219 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293931 x y)). Qed.
Lemma lem1293933 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293934 (x : nadd) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1293933) (@lem1293932 x)). Qed.
Lemma lem1293935 : term241 = term241.
Proof. exact (fun_ext (fun x : nadd => @lem1293934 x)). Qed.
Lemma lem1293936 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293937 : term252 = term252.
Proof. exact (MK_COMB (@lem1293936) (@lem1293935)). Qed.
Lemma lem1293938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1293939 : term254 = term254.
Proof. exact (MK_COMB (@lem1293938) (@lem1293937)). Qed.
Lemma lem1293940 : term258 = term258.
Proof. exact (MK_COMB (@lem1293939) (@lem1293905)). Qed.
Lemma lem1293941 (h1 : term165) : term258.
Proof. exact (EQ_MP (@lem1293940) (@lem1293601 h1)). Qed.
Lemma lem1293966 (y : nadd) (x : nadd) (z : nadd) : (term152 y x z) = (term152 y x z).
Proof. exact (eq_refl (term152 y x z)). Qed.
Lemma lem1293967 (y : nadd) (x : nadd) : (term153 y x) = (term153 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1293966 y x z)). Qed.
Lemma lem1293968 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293969 (y : nadd) (x : nadd) : (term154 y x) = (term154 y x).
Proof. exact (MK_COMB (@lem1293968) (@lem1293967 y x)). Qed.
Lemma lem1293970 (x : nadd) : (term155 x) = (term155 x).
Proof. exact (fun_ext (fun y : nadd => @lem1293969 y x)). Qed.
Lemma lem1293971 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293972 (x : nadd) : (term156 x) = (term156 x).
Proof. exact (MK_COMB (@lem1293971) (@lem1293970 x)). Qed.
Lemma lem1293973 : term157 = term157.
Proof. exact (fun_ext (fun x : nadd => @lem1293972 x)). Qed.
Lemma lem1293974 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1293975 : term158 = term158.
Proof. exact (MK_COMB (@lem1293974) (@lem1293973)). Qed.
Lemma lem1293976 (h1 : term158) : term158.
Proof. exact (EQ_MP (@lem1293975) (@lem1293628 h1)). Qed.
Lemma lem1294029 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term265 x y x' y') = (term265 x y x' y').
Proof. exact (eq_refl (term265 x y x' y')). Qed.
Lemma lem1294030 (x : nadd) (y : nadd) (x' : nadd) : (term266 x y x') = (term266 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1294029 x y x' y')). Qed.
Lemma lem1294031 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294032 (x : nadd) (y : nadd) (x' : nadd) : (term267 x y x') = (term267 x y x').
Proof. exact (MK_COMB (@lem1294031) (@lem1294030 x y x')). Qed.
Lemma lem1294033 (x : nadd) (x' : nadd) : (term268 x x') = (term268 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1294032 x y x')). Qed.
Lemma lem1294034 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294035 (x : nadd) (x' : nadd) : (term269 x x') = (term269 x x').
Proof. exact (MK_COMB (@lem1294034) (@lem1294033 x x')). Qed.
Lemma lem1294036 (x : nadd) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1294035 x x')). Qed.
Lemma lem1294037 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294038 (x : nadd) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem1294037) (@lem1294036 x)). Qed.
Lemma lem1294039 : term272 = term272.
Proof. exact (fun_ext (fun x : nadd => @lem1294038 x)). Qed.
Lemma lem1294040 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294041 : term273 = term273.
Proof. exact (MK_COMB (@lem1294040) (@lem1294039)). Qed.
Lemma lem1294042 (h1 : term151) : term273.
Proof. exact (EQ_MP (@lem1294041) (@lem1293732 h1)). Qed.
Lemma lem1294075 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term276 x y x' y') = (term276 x y x' y').
Proof. exact (eq_refl (term276 x y x' y')). Qed.
Lemma lem1294076 (x : nadd) (y : nadd) (x' : nadd) : (term277 x y x') = (term277 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1294075 x y x' y')). Qed.
Lemma lem1294077 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294078 (x : nadd) (y : nadd) (x' : nadd) : (term278 x y x') = (term278 x y x').
Proof. exact (MK_COMB (@lem1294077) (@lem1294076 x y x')). Qed.
Lemma lem1294079 (x : nadd) (x' : nadd) : (term279 x x') = (term279 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1294078 x y x')). Qed.
Lemma lem1294080 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294081 (x : nadd) (x' : nadd) : (term280 x x') = (term280 x x').
Proof. exact (MK_COMB (@lem1294080) (@lem1294079 x x')). Qed.
Lemma lem1294082 (x : nadd) : (term281 x) = (term281 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1294081 x x')). Qed.
Lemma lem1294083 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294084 (x : nadd) : (term282 x) = (term282 x).
Proof. exact (MK_COMB (@lem1294083) (@lem1294082 x)). Qed.
Lemma lem1294085 : term283 = term283.
Proof. exact (fun_ext (fun x : nadd => @lem1294084 x)). Qed.
Lemma lem1294086 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294087 : term284 = term284.
Proof. exact (MK_COMB (@lem1294086) (@lem1294085)). Qed.
Lemma lem1294088 (h1 : term95) : term284.
Proof. exact (EQ_MP (@lem1294087) (@lem1293822 h1)). Qed.
Lemma lem1294102 (n : nat) (d : nadd) (z : nadd) (h1 : term177 n d z) : term177 n d z.
Proof. exact (h1). Qed.
Lemma lem1294103 (h1 : term165) : term257.
Proof. exact (proj2 (@lem1293941 h1)). Qed.
Lemma lem1294106 (x : nadd) (n : nat) (y : nadd) (z : nadd) : (term170 x n y z) = (term170 x n y z).
Proof. exact (eq_refl (term170 x n y z)). Qed.
Lemma lem1294107 (x : nadd) (y : nadd) (z : nadd) : (term171 x y z) = (term171 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1294106 x n y z)). Qed.
Lemma lem1294108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1294110 (x : nadd) (y : nadd) (z : nadd) : (term73 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1294108) (@lem1294107 x y z)). Qed.
Lemma lem1294111 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term73 x y z.
Proof. exact (EQ_MP (@lem1294110 x y z) (@lem1293848 x y z h1)). Qed.
Lemma lem1294119 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term75 x y d.
Proof. exact (h1). Qed.
Lemma lem1294121 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1294122 : term166 = term166.
Proof. exact (fun_ext (fun x : nadd => @lem1294121 x)). Qed.
Lemma lem1294123 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294125 : term167 = term167.
Proof. exact (MK_COMB (@lem1294123) (@lem1294122)). Qed.
Lemma lem1294126 (h1 : term167) : term167.
Proof. exact (EQ_MP (@lem1294125) (@lem1293873 h1)). Qed.
Lemma lem1294128 (y : nadd) (x : nadd) (z : nadd) : (term152 y x z) = (term152 y x z).
Proof. exact (eq_refl (term152 y x z)). Qed.
Lemma lem1294129 (y : nadd) (x : nadd) : (term153 y x) = (term153 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1294128 y x z)). Qed.
Lemma lem1294130 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294131 (y : nadd) (x : nadd) : (term154 y x) = (term154 y x).
Proof. exact (MK_COMB (@lem1294130) (@lem1294129 y x)). Qed.
Lemma lem1294132 (x : nadd) : (term155 x) = (term155 x).
Proof. exact (fun_ext (fun y : nadd => @lem1294131 y x)). Qed.
Lemma lem1294133 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294134 (x : nadd) : (term156 x) = (term156 x).
Proof. exact (MK_COMB (@lem1294133) (@lem1294132 x)). Qed.
Lemma lem1294135 : term157 = term157.
Proof. exact (fun_ext (fun x : nadd => @lem1294134 x)). Qed.
Lemma lem1294136 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294138 : term158 = term158.
Proof. exact (MK_COMB (@lem1294136) (@lem1294135)). Qed.
Lemma lem1294139 (h1 : term158) : term158.
Proof. exact (EQ_MP (@lem1294138) (@lem1293976 h1)). Qed.
Lemma lem1294175 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term265 x y x' y') = (term285 x y x' y').
Proof. exact (@lem19490 (term286 x y x' y') (term260 x x' y y') (term287 x y x' y')). Qed.
Lemma lem1294176 (x : nadd) (y : nadd) (x' : nadd) : (term266 x y x') = (term288 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1294175 x y x' y')). Qed.
Lemma lem1294177 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294178 (x : nadd) (y : nadd) (x' : nadd) : (term267 x y x') = (term289 x y x').
Proof. exact (MK_COMB (@lem1294177) (@lem1294176 x y x')). Qed.
Lemma lem1294179 (x : nadd) (x' : nadd) : (term268 x x') = (term290 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1294178 x y x')). Qed.
Lemma lem1294180 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294181 (x : nadd) (x' : nadd) : (term269 x x') = (term291 x x').
Proof. exact (MK_COMB (@lem1294180) (@lem1294179 x x')). Qed.
Lemma lem1294182 (x : nadd) : (term270 x) = (term292 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1294181 x x')). Qed.
Lemma lem1294183 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294184 (x : nadd) : (term271 x) = (term293 x).
Proof. exact (MK_COMB (@lem1294183) (@lem1294182 x)). Qed.
Lemma lem1294185 : term272 = term294.
Proof. exact (fun_ext (fun x : nadd => @lem1294184 x)). Qed.
Lemma lem1294186 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294188 : term273 = term295.
Proof. exact (MK_COMB (@lem1294186) (@lem1294185)). Qed.
Lemma lem1294189 (h1 : term151) : term295.
Proof. exact (EQ_MP (@lem1294188) (@lem1294042 h1)). Qed.
Lemma lem1294203 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term276 x y x' y') = (term276 x y x' y').
Proof. exact (eq_refl (term276 x y x' y')). Qed.
Lemma lem1294204 (x : nadd) (y : nadd) (x' : nadd) : (term277 x y x') = (term277 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1294203 x y x' y')). Qed.
Lemma lem1294205 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294206 (x : nadd) (y : nadd) (x' : nadd) : (term278 x y x') = (term278 x y x').
Proof. exact (MK_COMB (@lem1294205) (@lem1294204 x y x')). Qed.
Lemma lem1294207 (x : nadd) (x' : nadd) : (term279 x x') = (term279 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1294206 x y x')). Qed.
Lemma lem1294208 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294209 (x : nadd) (x' : nadd) : (term280 x x') = (term280 x x').
Proof. exact (MK_COMB (@lem1294208) (@lem1294207 x x')). Qed.
Lemma lem1294210 (x : nadd) : (term281 x) = (term281 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1294209 x x')). Qed.
Lemma lem1294211 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294212 (x : nadd) : (term282 x) = (term282 x).
Proof. exact (MK_COMB (@lem1294211) (@lem1294210 x)). Qed.
Lemma lem1294213 : term283 = term283.
Proof. exact (fun_ext (fun x : nadd => @lem1294212 x)). Qed.
Lemma lem1294214 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294216 : term284 = term284.
Proof. exact (MK_COMB (@lem1294214) (@lem1294213)). Qed.
Lemma lem1294217 (h1 : term95) : term284.
Proof. exact (EQ_MP (@lem1294216) (@lem1294088 h1)). Qed.
Lemma lem1294221 (n : nat) (d : nadd) (z : nadd) (h1 : term177 n d z) : term177 n d z.
Proof. exact (h1). Qed.
Lemma lem1294248 (x : nadd) (y : nadd) (z : nadd) : (term201 x y z) = (term201 x y z).
Proof. exact (eq_refl (term201 x y z)). Qed.
Lemma lem1294249 (x : nadd) (y : nadd) : (term195 x y) = (term195 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1294248 x y z)). Qed.
Lemma lem1294250 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294251 (x : nadd) (y : nadd) : (term213 x y) = (term213 x y).
Proof. exact (MK_COMB (@lem1294250) (@lem1294249 x y)). Qed.
Lemma lem1294252 (x : nadd) : (term220 x) = (term220 x).
Proof. exact (fun_ext (fun y : nadd => @lem1294251 x y)). Qed.
Lemma lem1294253 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294254 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (MK_COMB (@lem1294253) (@lem1294252 x)). Qed.
Lemma lem1294255 : term242 = term242.
Proof. exact (fun_ext (fun x : nadd => @lem1294254 x)). Qed.
Lemma lem1294256 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1294258 : term257 = term257.
Proof. exact (MK_COMB (@lem1294256) (@lem1294255)). Qed.
Lemma lem1294259 (h1 : term165) : term257.
Proof. exact (EQ_MP (@lem1294258) (@lem1294103 h1)). Qed.
Lemma lem1294260 (_23303 : nat) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term296 x y z _23303.
Proof. exact (@lem1294111 x y z h1 _23303). Qed.
Lemma lem1294261 (x : nadd) (_23303 : nat) (y : nadd) (z : nadd) : (term296 x y z _23303) = (term170 x _23303 y z).
Proof. exact (eq_refl (term296 x y z _23303)). Qed.
Lemma lem1294263 (_23304 : nadd) (h1 : term167) : term21 _23304.
Proof. exact (@lem1294126 h1 _23304). Qed.
Lemma lem1294264 (_23304 : nadd) : (term21 _23304) = (nadd_eq _23304 _23304).
Proof. exact (eq_refl (term21 _23304)). Qed.
Lemma lem1294266 (_23305 : nadd) (h1 : term158) : term297 _23305.
Proof. exact (@lem1294139 h1 _23305). Qed.
Lemma lem1294267 (_23305 : nadd) : (term297 _23305) = (term156 _23305).
Proof. exact (eq_refl (term297 _23305)). Qed.
Lemma lem1294268 (_23305 : nadd) (h1 : term158) : term156 _23305.
Proof. exact (EQ_MP (@lem1294267 _23305) (@lem1294266 _23305 h1)). Qed.
Lemma lem1294269 (_23305 : nadd) (_23306 : nadd) (h1 : term158) : term298 _23305 _23306.
Proof. exact (@lem1294268 _23305 h1 _23306). Qed.
Lemma lem1294270 (_23306 : nadd) (_23305 : nadd) : (term298 _23305 _23306) = (term154 _23306 _23305).
Proof. exact (eq_refl (term298 _23305 _23306)). Qed.
Lemma lem1294271 (_23306 : nadd) (_23305 : nadd) (h1 : term158) : term154 _23306 _23305.
Proof. exact (EQ_MP (@lem1294270 _23306 _23305) (@lem1294269 _23305 _23306 h1)). Qed.
Lemma lem1294272 (_23306 : nadd) (_23305 : nadd) (_23307 : nadd) (h1 : term158) : term299 _23306 _23305 _23307.
Proof. exact (@lem1294271 _23306 _23305 h1 _23307). Qed.
Lemma lem1294273 (_23306 : nadd) (_23305 : nadd) (_23307 : nadd) : (term299 _23306 _23305 _23307) = (term152 _23306 _23305 _23307).
Proof. exact (eq_refl (term299 _23306 _23305 _23307)). Qed.
Lemma lem1294275 (_23308 : nadd) (h1 : term151) : term300 _23308.
Proof. exact (@lem1294189 h1 _23308). Qed.
Lemma lem1294276 (_23308 : nadd) : (term300 _23308) = (term293 _23308).
Proof. exact (eq_refl (term300 _23308)). Qed.
Lemma lem1294277 (_23308 : nadd) (h1 : term151) : term293 _23308.
Proof. exact (EQ_MP (@lem1294276 _23308) (@lem1294275 _23308 h1)). Qed.
Lemma lem1294278 (_23308 : nadd) (_23309 : nadd) (h1 : term151) : term301 _23308 _23309.
Proof. exact (@lem1294277 _23308 h1 _23309). Qed.
Lemma lem1294279 (_23308 : nadd) (_23309 : nadd) : (term301 _23308 _23309) = (term291 _23308 _23309).
Proof. exact (eq_refl (term301 _23308 _23309)). Qed.
Lemma lem1294280 (_23308 : nadd) (_23309 : nadd) (h1 : term151) : term291 _23308 _23309.
Proof. exact (EQ_MP (@lem1294279 _23308 _23309) (@lem1294278 _23308 _23309 h1)). Qed.
Lemma lem1294281 (_23308 : nadd) (_23309 : nadd) (_23310 : nadd) (h1 : term151) : term302 _23308 _23309 _23310.
Proof. exact (@lem1294280 _23308 _23309 h1 _23310). Qed.
Lemma lem1294282 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) : (term302 _23308 _23309 _23310) = (term289 _23308 _23310 _23309).
Proof. exact (eq_refl (term302 _23308 _23309 _23310)). Qed.
Lemma lem1294283 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (h1 : term151) : term289 _23308 _23310 _23309.
Proof. exact (EQ_MP (@lem1294282 _23308 _23310 _23309) (@lem1294281 _23308 _23309 _23310 h1)). Qed.
Lemma lem1294284 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) (h1 : term151) : term303 _23308 _23310 _23309 _23311.
Proof. exact (@lem1294283 _23308 _23310 _23309 h1 _23311). Qed.
Lemma lem1294285 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) : (term303 _23308 _23310 _23309 _23311) = (term285 _23308 _23310 _23309 _23311).
Proof. exact (eq_refl (term303 _23308 _23310 _23309 _23311)). Qed.
Lemma lem1294286 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) (h1 : term151) : term285 _23308 _23310 _23309 _23311.
Proof. exact (EQ_MP (@lem1294285 _23308 _23310 _23309 _23311) (@lem1294284 _23308 _23310 _23309 _23311 h1)). Qed.
Lemma lem1294287 (_23312 : nadd) (h1 : term95) : term304 _23312.
Proof. exact (@lem1294217 h1 _23312). Qed.
Lemma lem1294288 (_23312 : nadd) : (term304 _23312) = (term282 _23312).
Proof. exact (eq_refl (term304 _23312)). Qed.
Lemma lem1294289 (_23312 : nadd) (h1 : term95) : term282 _23312.
Proof. exact (EQ_MP (@lem1294288 _23312) (@lem1294287 _23312 h1)). Qed.
Lemma lem1294290 (_23312 : nadd) (_23313 : nadd) (h1 : term95) : term305 _23312 _23313.
Proof. exact (@lem1294289 _23312 h1 _23313). Qed.
Lemma lem1294291 (_23312 : nadd) (_23313 : nadd) : (term305 _23312 _23313) = (term280 _23312 _23313).
Proof. exact (eq_refl (term305 _23312 _23313)). Qed.
Lemma lem1294292 (_23312 : nadd) (_23313 : nadd) (h1 : term95) : term280 _23312 _23313.
Proof. exact (EQ_MP (@lem1294291 _23312 _23313) (@lem1294290 _23312 _23313 h1)). Qed.
Lemma lem1294293 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (h1 : term95) : term306 _23312 _23313 _23314.
Proof. exact (@lem1294292 _23312 _23313 h1 _23314). Qed.
Lemma lem1294294 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) : (term306 _23312 _23313 _23314) = (term278 _23312 _23314 _23313).
Proof. exact (eq_refl (term306 _23312 _23313 _23314)). Qed.
Lemma lem1294295 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (h1 : term95) : term278 _23312 _23314 _23313.
Proof. exact (EQ_MP (@lem1294294 _23312 _23314 _23313) (@lem1294293 _23312 _23313 _23314 h1)). Qed.
Lemma lem1294296 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) (h1 : term95) : term307 _23312 _23314 _23313 _23315.
Proof. exact (@lem1294295 _23312 _23314 _23313 h1 _23315). Qed.
Lemma lem1294297 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) : (term307 _23312 _23314 _23313 _23315) = (term276 _23312 _23314 _23313 _23315).
Proof. exact (eq_refl (term307 _23312 _23314 _23313 _23315)). Qed.
Lemma lem1294298 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) (h1 : term95) : term276 _23312 _23314 _23313 _23315.
Proof. exact (EQ_MP (@lem1294297 _23312 _23314 _23313 _23315) (@lem1294296 _23312 _23314 _23313 _23315 h1)). Qed.
Lemma lem1294308 (_23319 : nadd) (h1 : term165) : term245 _23319.
Proof. exact (@lem1294259 h1 _23319). Qed.
Lemma lem1294309 (_23319 : nadd) : (term245 _23319) = (term235 _23319).
Proof. exact (eq_refl (term245 _23319)). Qed.
Lemma lem1294310 (_23319 : nadd) (h1 : term165) : term235 _23319.
Proof. exact (EQ_MP (@lem1294309 _23319) (@lem1294308 _23319 h1)). Qed.
Lemma lem1294311 (_23319 : nadd) (_23320 : nadd) (h1 : term165) : term223 _23319 _23320.
Proof. exact (@lem1294310 _23319 h1 _23320). Qed.
Lemma lem1294312 (_23319 : nadd) (_23320 : nadd) : (term223 _23319 _23320) = (term213 _23319 _23320).
Proof. exact (eq_refl (term223 _23319 _23320)). Qed.
Lemma lem1294313 (_23319 : nadd) (_23320 : nadd) (h1 : term165) : term213 _23319 _23320.
Proof. exact (EQ_MP (@lem1294312 _23319 _23320) (@lem1294311 _23319 _23320 h1)). Qed.
Lemma lem1294314 (_23319 : nadd) (_23320 : nadd) (_23321 : nadd) (h1 : term165) : term200 _23319 _23320 _23321.
Proof. exact (@lem1294313 _23319 _23320 h1 _23321). Qed.
Lemma lem1294315 (_23319 : nadd) (_23320 : nadd) (_23321 : nadd) : (term200 _23319 _23320 _23321) = (term201 _23319 _23320 _23321).
Proof. exact (eq_refl (term200 _23319 _23320 _23321)). Qed.
Lemma lem1294317 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) (h1 : term151) : term308 _23308 _23310 _23309 _23311.
Proof. exact (proj2 (@lem1294286 _23308 _23310 _23309 _23311 h1)). Qed.
Lemma lem1294324 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term75 x y d.
Proof. exact (h1). Qed.
Lemma lem1294339 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) : (term276 _23312 _23314 _23313 _23315) = (term309 _23312 _23314 _23313 _23315).
Proof. exact (@lem1292388 (term310 _23312 _23313) (term310 _23314 _23315) (term274 _23312 _23314 _23313 _23315)). Qed.
Lemma lem1294340 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) (h1 : term95) : term309 _23312 _23314 _23313 _23315.
Proof. exact (EQ_MP (@lem1294339 _23312 _23314 _23313 _23315) (@lem1294298 _23312 _23314 _23313 _23315 h1)). Qed.
Lemma lem1294342 (n : nat) (d : nadd) (z : nadd) (h1 : term177 n d z) : term177 n d z.
Proof. exact (h1). Qed.
Lemma lem1294354 (_23319 : nadd) (_23320 : nadd) (_23321 : nadd) (h1 : term165) : term201 _23319 _23320 _23321.
Proof. exact (EQ_MP (@lem1294315 _23319 _23320 _23321) (@lem1294314 _23319 _23320 _23321 h1)). Qed.
Lemma lem1294385 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) : (term308 _23308 _23310 _23309 _23311) = (term311 _23308 _23310 _23309 _23311).
Proof. exact (@lem1292388 (term310 _23308 _23309) (term310 _23310 _23311) (term287 _23308 _23310 _23309 _23311)). Qed.
Lemma lem1294386 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) (h1 : term151) : term311 _23308 _23310 _23309 _23311.
Proof. exact (EQ_MP (@lem1294385 _23308 _23310 _23309 _23311) (@lem1294317 _23308 _23310 _23309 _23311 h1)). Qed.
Lemma lem1294388 (_23306 : nadd) (_23305 : nadd) (_23307 : nadd) (h1 : term158) : term152 _23306 _23305 _23307.
Proof. exact (EQ_MP (@lem1294273 _23306 _23305 _23307) (@lem1294272 _23306 _23305 _23307 h1)). Qed.
Lemma lem1294389 (y : nadd) (n : nat) (d : nadd) (h1 : term158) : term312 y n d.
Proof. exact (@lem1294388 y (nadd_of_num n) d h1). Qed.
Lemma lem1294390 (y : nadd) (n : nat) (d : nadd) (h1 : term158) : term313 y n d.
Proof. exact (fun h0 : term314 y n d => @lem1294389 y n d h1). Qed.
Lemma lem1294392 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294393 (y : nadd) (n : nat) (d : nadd) : (term313 y n d) = (term312 y n d).
Proof. exact (@lem1294392 (term312 y n d)). Qed.
Lemma lem1294394 (y : nadd) (n : nat) (d : nadd) (h1 : term158) : term312 y n d.
Proof. exact (EQ_MP (@lem1294393 y n d) (@lem1294390 y n d h1)). Qed.
Lemma lem1294396 (_23304 : nadd) (h1 : term167) : nadd_eq _23304 _23304.
Proof. exact (EQ_MP (@lem1294264 _23304) (@lem1294263 _23304 h1)). Qed.
Lemma lem1294397 (n : nat) (y : nadd) (z : nadd) (h1 : term167) : term316 n y z.
Proof. exact (@lem1294396 (term317 n y z) h1). Qed.
Lemma lem1294398 (n : nat) (y : nadd) (z : nadd) (h1 : term167) : term318 n y z.
Proof. exact (fun h0 : term319 n y z => @lem1294397 n y z h1). Qed.
Lemma lem1294400 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294401 (n : nat) (y : nadd) (z : nadd) : (term318 n y z) = (term316 n y z).
Proof. exact (@lem1294400 (term316 n y z)). Qed.
Lemma lem1294402 (n : nat) (y : nadd) (z : nadd) (h1 : term167) : term316 n y z.
Proof. exact (EQ_MP (@lem1294401 n y z) (@lem1294398 n y z h1)). Qed.
Lemma lem1294404 (_23304 : nadd) (h1 : term167) : nadd_eq _23304 _23304.
Proof. exact (EQ_MP (@lem1294264 _23304) (@lem1294263 _23304 h1)). Qed.
Lemma lem1294405 (n : nat) (h1 : term167) : term320 n.
Proof. exact (@lem1294404 (nadd_of_num n) h1). Qed.
Lemma lem1294406 (n : nat) (h1 : term167) : term321 n.
Proof. exact (fun h0 : term322 n => @lem1294405 n h1). Qed.
Lemma lem1294408 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294409 (n : nat) : (term321 n) = (term320 n).
Proof. exact (@lem1294408 (term320 n)). Qed.
Lemma lem1294410 (n : nat) (h1 : term167) : term320 n.
Proof. exact (EQ_MP (@lem1294409 n) (@lem1294406 n h1)). Qed.
Lemma lem1294412 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term75 x y d.
Proof. exact (h1). Qed.
Lemma lem1294413 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term323 x y d.
Proof. exact (fun h0 : term324 x y d => @lem1294412 x y d h1). Qed.
Lemma lem1294415 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294416 (x : nadd) (y : nadd) (d : nadd) : (term323 x y d) = (term75 x y d).
Proof. exact (@lem1294415 (term75 x y d)). Qed.
Lemma lem1294417 (x : nadd) (y : nadd) (d : nadd) (h1 : term75 x y d) : term75 x y d.
Proof. exact (EQ_MP (@lem1294416 x y d) (@lem1294413 x y d h1)). Qed.
Lemma lem1294433 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1294434 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term325 _23312 _23314 _23313 _23315) = (term326 _23312 _23313 _23314 _23315).
Proof. exact (@lem1294433 (term274 _23312 _23314 _23313 _23315) (term310 _23314 _23315)). Qed.
Lemma lem1294440 (_23312 : nadd) (_23313 : nadd) : (term327 _23312 _23313) = (term327 _23312 _23313).
Proof. exact (eq_refl (term327 _23312 _23313)). Qed.
Lemma lem1294441 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term309 _23312 _23314 _23313 _23315) = (term328 _23312 _23313 _23314 _23315).
Proof. exact (MK_COMB (@lem1294440 _23312 _23313) (@lem1294434 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294445 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1294446 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term328 _23312 _23313 _23314 _23315) = (term329 _23312 _23313 _23314 _23315).
Proof. exact (@lem1294445 (term274 _23312 _23314 _23313 _23315) (term310 _23312 _23313) (term310 _23314 _23315)). Qed.
Lemma lem1294462 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term309 _23312 _23314 _23313 _23315) = (term329 _23312 _23313 _23314 _23315).
Proof. exact (TRANS (@lem1294441 _23312 _23313 _23314 _23315) (@lem1294446 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1294464 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term330 _23312 _23314 _23313 _23315) = (term331 _23312 _23313 _23314 _23315).
Proof. exact (MK_COMB (@lem1294463) (@lem1294462 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294480 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term329 _23312 _23313 _23314 _23315) = (term329 _23312 _23313 _23314 _23315).
Proof. exact (eq_refl (term329 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294481 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : ((term309 _23312 _23314 _23313 _23315) = (term329 _23312 _23313 _23314 _23315)) = ((term329 _23312 _23313 _23314 _23315) = (term329 _23312 _23313 _23314 _23315)).
Proof. exact (MK_COMB (@lem1294464 _23312 _23313 _23314 _23315) (@lem1294480 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294483 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1294484 (x : Prop) : (x = x) = True.
Proof. exact (@lem1294483 Prop x). Qed.
Lemma lem1294485 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : ((term329 _23312 _23313 _23314 _23315) = (term329 _23312 _23313 _23314 _23315)) = True.
Proof. exact (@lem1294484 (term329 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294486 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : ((term309 _23312 _23314 _23313 _23315) = (term329 _23312 _23313 _23314 _23315)) = True.
Proof. exact (TRANS (@lem1294481 _23312 _23313 _23314 _23315) (@lem1294485 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294487 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : True = ((term309 _23312 _23314 _23313 _23315) = (term329 _23312 _23313 _23314 _23315)).
Proof. exact (SYM (@lem1294486 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294488 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term309 _23312 _23314 _23313 _23315) = (term329 _23312 _23313 _23314 _23315).
Proof. exact (EQ_MP (@lem1294487 _23312 _23313 _23314 _23315) (@lem0)). Qed.
Lemma lem1294489 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) (h1 : term95) : term329 _23312 _23313 _23314 _23315.
Proof. exact (EQ_MP (@lem1294488 _23312 _23313 _23314 _23315) (@lem1294340 _23312 _23314 _23313 _23315 h1)). Qed.
Lemma lem1294491 (b : Prop) (a : Prop) : (a \/ b) = (term332 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1294492 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) : (term329 _23312 _23313 _23314 _23315) = (term333 _23312 _23314 _23313 _23315).
Proof. exact (@lem1294491 (term260 _23312 _23313 _23314 _23315) (term274 _23312 _23314 _23313 _23315)). Qed.
Lemma lem1294494 (a : Prop) (b : Prop) : (term334 a b) = (term335 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1294495 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term336 _23312 _23313 _23314 _23315) = (term337 _23312 _23313 _23314 _23315).
Proof. exact (@lem1294494 (term310 _23312 _23313) (term310 _23314 _23315)). Qed.
Lemma lem1294497 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1294498 (_23312 : nadd) (_23313 : nadd) : (term339 _23312 _23313) = (nadd_eq _23312 _23313).
Proof. exact (@lem1294497 (nadd_eq _23312 _23313)). Qed.
Lemma lem1294499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1294500 (_23312 : nadd) (_23313 : nadd) : (term340 _23312 _23313) = (term341 _23312 _23313).
Proof. exact (MK_COMB (@lem1294499) (@lem1294498 _23312 _23313)). Qed.
Lemma lem1294502 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1294503 (_23314 : nadd) (_23315 : nadd) : (term339 _23314 _23315) = (nadd_eq _23314 _23315).
Proof. exact (@lem1294502 (nadd_eq _23314 _23315)). Qed.
Lemma lem1294504 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term337 _23312 _23313 _23314 _23315) = (term31 _23312 _23313 _23314 _23315).
Proof. exact (MK_COMB (@lem1294500 _23312 _23313) (@lem1294503 _23314 _23315)). Qed.
Lemma lem1294505 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term336 _23312 _23313 _23314 _23315) = (term31 _23312 _23313 _23314 _23315).
Proof. exact (TRANS (@lem1294495 _23312 _23313 _23314 _23315) (@lem1294504 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294506 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1294507 (_23312 : nadd) (_23313 : nadd) (_23314 : nadd) (_23315 : nadd) : (term342 _23312 _23313 _23314 _23315) = (term343 _23312 _23313 _23314 _23315).
Proof. exact (MK_COMB (@lem1294506) (@lem1294505 _23312 _23313 _23314 _23315)). Qed.
Lemma lem1294508 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) : (term274 _23312 _23314 _23313 _23315) = (term274 _23312 _23314 _23313 _23315).
Proof. exact (eq_refl (term274 _23312 _23314 _23313 _23315)). Qed.
Lemma lem1294509 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) : (term333 _23312 _23314 _23313 _23315) = (term135 _23312 _23314 _23313 _23315).
Proof. exact (MK_COMB (@lem1294507 _23312 _23313 _23314 _23315) (@lem1294508 _23312 _23314 _23313 _23315)). Qed.
Lemma lem1294510 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) : (term329 _23312 _23313 _23314 _23315) = (term135 _23312 _23314 _23313 _23315).
Proof. exact (TRANS (@lem1294492 _23312 _23314 _23313 _23315) (@lem1294509 _23312 _23314 _23313 _23315)). Qed.
Lemma lem1294512 (n : nat) (x : nadd) (y : nadd) (d : nadd) (h1 : term167) (h2 : term75 x y d) : term344 n x y d.
Proof. exact (conj (@lem1294410 n h1) (@lem1294417 x y d h2)). Qed.
Lemma lem1294514 (_23312 : nadd) (_23314 : nadd) (_23313 : nadd) (_23315 : nadd) (h1 : term95) : term135 _23312 _23314 _23313 _23315.
Proof. exact (EQ_MP (@lem1294510 _23312 _23314 _23313 _23315) (@lem1294489 _23312 _23313 _23314 _23315 h1)). Qed.
Lemma lem1294515 (x : nadd) (n : nat) (y : nadd) (d : nadd) (h1 : term95) : term345 x n y d.
Proof. exact (@lem1294514 (nadd_of_num n) x (nadd_of_num n) (nadd_add y d) h1). Qed.
Lemma lem1294518 (n : nat) (x : nadd) (y : nadd) (d : nadd) (h1 : term95) (h2 : term167) (h3 : term75 x y d) : term346 x n y d.
Proof. exact (@lem1294515 x n y d h1 (@lem1294512 n x y d h2 h3)). Qed.
Lemma lem1294519 (n : nat) (x : nadd) (y : nadd) (d : nadd) (h1 : term95) (h2 : term167) (h3 : term75 x y d) : term347 x n y d.
Proof. exact (fun h0 : term348 x n y d => @lem1294518 n x y d h1 h2 h3). Qed.
Lemma lem1294521 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294522 (x : nadd) (n : nat) (y : nadd) (d : nadd) : (term347 x n y d) = (term346 x n y d).
Proof. exact (@lem1294521 (term346 x n y d)). Qed.
Lemma lem1294523 (n : nat) (x : nadd) (y : nadd) (d : nadd) (h1 : term95) (h2 : term167) (h3 : term75 x y d) : term346 x n y d.
Proof. exact (EQ_MP (@lem1294522 x n y d) (@lem1294519 n x y d h1 h2 h3)). Qed.
Lemma lem1294525 (_23304 : nadd) (h1 : term167) : nadd_eq _23304 _23304.
Proof. exact (EQ_MP (@lem1294264 _23304) (@lem1294263 _23304 h1)). Qed.
Lemma lem1294526 (n : nat) (y : nadd) (z : nadd) (h1 : term167) : term316 n y z.
Proof. exact (@lem1294525 (term317 n y z) h1). Qed.
Lemma lem1294527 (n : nat) (y : nadd) (z : nadd) (h1 : term167) : term318 n y z.
Proof. exact (fun h0 : term319 n y z => @lem1294526 n y z h1). Qed.
Lemma lem1294529 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294530 (n : nat) (y : nadd) (z : nadd) : (term318 n y z) = (term316 n y z).
Proof. exact (@lem1294529 (term316 n y z)). Qed.
Lemma lem1294531 (n : nat) (y : nadd) (z : nadd) (h1 : term167) : term316 n y z.
Proof. exact (EQ_MP (@lem1294530 n y z) (@lem1294527 n y z h1)). Qed.
Lemma lem1294533 (_23303 : nat) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term170 x _23303 y z.
Proof. exact (EQ_MP (@lem1294261 x _23303 y z) (@lem1294260 _23303 x y z h1)). Qed.
Lemma lem1294534 (n : nat) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term170 x n y z.
Proof. exact (@lem1294533 n x y z h1). Qed.
Lemma lem1294535 (n : nat) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term349 x n y z.
Proof. exact (fun h0 : term350 x n y z => @lem1294534 n x y z h1). Qed.
Lemma lem1294537 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294538 (x : nadd) (n : nat) (y : nadd) (z : nadd) : (term349 x n y z) = (term170 x n y z).
Proof. exact (@lem1294537 (term170 x n y z)). Qed.
Lemma lem1294539 (n : nat) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term170 x n y z.
Proof. exact (EQ_MP (@lem1294538 x n y z) (@lem1294535 n x y z h1)). Qed.
Lemma lem1294565 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1294566 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term287 _23308 _23310 _23309 _23311) = (term286 _23309 _23311 _23308 _23310).
Proof. exact (@lem1294565 (nadd_le _23309 _23311) (term351 _23308 _23310)). Qed.
Lemma lem1294572 (_23310 : nadd) (_23311 : nadd) : (term327 _23310 _23311) = (term327 _23310 _23311).
Proof. exact (eq_refl (term327 _23310 _23311)). Qed.
Lemma lem1294573 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term352 _23308 _23310 _23309 _23311) = (term353 _23309 _23311 _23308 _23310).
Proof. exact (MK_COMB (@lem1294572 _23310 _23311) (@lem1294566 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294577 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1294578 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term353 _23309 _23311 _23308 _23310) = (term354 _23309 _23311 _23308 _23310).
Proof. exact (@lem1294577 (nadd_le _23309 _23311) (term310 _23310 _23311) (term351 _23308 _23310)). Qed.
Lemma lem1294594 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term352 _23308 _23310 _23309 _23311) = (term354 _23309 _23311 _23308 _23310).
Proof. exact (TRANS (@lem1294573 _23309 _23311 _23308 _23310) (@lem1294578 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294595 (_23308 : nadd) (_23309 : nadd) : (term327 _23308 _23309) = (term327 _23308 _23309).
Proof. exact (eq_refl (term327 _23308 _23309)). Qed.
Lemma lem1294596 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term311 _23308 _23310 _23309 _23311) = (term355 _23309 _23311 _23308 _23310).
Proof. exact (MK_COMB (@lem1294595 _23308 _23309) (@lem1294594 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294600 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1294601 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term355 _23309 _23311 _23308 _23310) = (term356 _23309 _23311 _23308 _23310).
Proof. exact (@lem1294600 (nadd_le _23309 _23311) (term310 _23308 _23309) (term357 _23311 _23308 _23310)). Qed.
Lemma lem1294627 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term311 _23308 _23310 _23309 _23311) = (term356 _23309 _23311 _23308 _23310).
Proof. exact (TRANS (@lem1294596 _23309 _23311 _23308 _23310) (@lem1294601 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1294629 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term358 _23308 _23310 _23309 _23311) = (term359 _23309 _23311 _23308 _23310).
Proof. exact (MK_COMB (@lem1294628) (@lem1294627 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294655 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term356 _23309 _23311 _23308 _23310) = (term356 _23309 _23311 _23308 _23310).
Proof. exact (eq_refl (term356 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294656 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : ((term311 _23308 _23310 _23309 _23311) = (term356 _23309 _23311 _23308 _23310)) = ((term356 _23309 _23311 _23308 _23310) = (term356 _23309 _23311 _23308 _23310)).
Proof. exact (MK_COMB (@lem1294629 _23309 _23311 _23308 _23310) (@lem1294655 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294658 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1294659 (x : Prop) : (x = x) = True.
Proof. exact (@lem1294658 Prop x). Qed.
Lemma lem1294660 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : ((term356 _23309 _23311 _23308 _23310) = (term356 _23309 _23311 _23308 _23310)) = True.
Proof. exact (@lem1294659 (term356 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294661 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : ((term311 _23308 _23310 _23309 _23311) = (term356 _23309 _23311 _23308 _23310)) = True.
Proof. exact (TRANS (@lem1294656 _23309 _23311 _23308 _23310) (@lem1294660 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294662 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : True = ((term311 _23308 _23310 _23309 _23311) = (term356 _23309 _23311 _23308 _23310)).
Proof. exact (SYM (@lem1294661 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294663 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term311 _23308 _23310 _23309 _23311) = (term356 _23309 _23311 _23308 _23310).
Proof. exact (EQ_MP (@lem1294662 _23309 _23311 _23308 _23310) (@lem0)). Qed.
Lemma lem1294664 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) (h1 : term151) : term356 _23309 _23311 _23308 _23310.
Proof. exact (EQ_MP (@lem1294663 _23309 _23311 _23308 _23310) (@lem1294386 _23308 _23310 _23309 _23311 h1)). Qed.
Lemma lem1294666 (b : Prop) (a : Prop) : (a \/ b) = (term332 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1294667 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) : (term356 _23309 _23311 _23308 _23310) = (term360 _23308 _23310 _23309 _23311).
Proof. exact (@lem1294666 (term361 _23309 _23311 _23308 _23310) (nadd_le _23309 _23311)). Qed.
Lemma lem1294669 (a : Prop) (b : Prop) : (term334 a b) = (term335 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1294670 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term362 _23309 _23311 _23308 _23310) = (term363 _23309 _23311 _23308 _23310).
Proof. exact (@lem1294669 (term310 _23308 _23309) (term357 _23311 _23308 _23310)). Qed.
Lemma lem1294672 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1294673 (_23308 : nadd) (_23309 : nadd) : (term339 _23308 _23309) = (nadd_eq _23308 _23309).
Proof. exact (@lem1294672 (nadd_eq _23308 _23309)). Qed.
Lemma lem1294674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1294675 (_23308 : nadd) (_23309 : nadd) : (term340 _23308 _23309) = (term341 _23308 _23309).
Proof. exact (MK_COMB (@lem1294674) (@lem1294673 _23308 _23309)). Qed.
Lemma lem1294677 (a : Prop) (b : Prop) : (term334 a b) = (term335 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1294678 (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term364 _23311 _23308 _23310) = (term365 _23311 _23308 _23310).
Proof. exact (@lem1294677 (term310 _23310 _23311) (term351 _23308 _23310)). Qed.
Lemma lem1294680 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1294681 (_23310 : nadd) (_23311 : nadd) : (term339 _23310 _23311) = (nadd_eq _23310 _23311).
Proof. exact (@lem1294680 (nadd_eq _23310 _23311)). Qed.
Lemma lem1294682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1294683 (_23310 : nadd) (_23311 : nadd) : (term340 _23310 _23311) = (term341 _23310 _23311).
Proof. exact (MK_COMB (@lem1294682) (@lem1294681 _23310 _23311)). Qed.
Lemma lem1294685 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1294686 (_23308 : nadd) (_23310 : nadd) : (term366 _23308 _23310) = (nadd_le _23308 _23310).
Proof. exact (@lem1294685 (nadd_le _23308 _23310)). Qed.
Lemma lem1294687 (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term365 _23311 _23308 _23310) = (term367 _23311 _23308 _23310).
Proof. exact (MK_COMB (@lem1294683 _23310 _23311) (@lem1294686 _23308 _23310)). Qed.
Lemma lem1294688 (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term364 _23311 _23308 _23310) = (term367 _23311 _23308 _23310).
Proof. exact (TRANS (@lem1294678 _23311 _23308 _23310) (@lem1294687 _23311 _23308 _23310)). Qed.
Lemma lem1294689 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term363 _23309 _23311 _23308 _23310) = (term368 _23309 _23311 _23308 _23310).
Proof. exact (MK_COMB (@lem1294675 _23308 _23309) (@lem1294688 _23311 _23308 _23310)). Qed.
Lemma lem1294690 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term362 _23309 _23311 _23308 _23310) = (term368 _23309 _23311 _23308 _23310).
Proof. exact (TRANS (@lem1294670 _23309 _23311 _23308 _23310) (@lem1294689 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1294692 (_23309 : nadd) (_23311 : nadd) (_23308 : nadd) (_23310 : nadd) : (term369 _23309 _23311 _23308 _23310) = (term370 _23309 _23311 _23308 _23310).
Proof. exact (MK_COMB (@lem1294691) (@lem1294690 _23309 _23311 _23308 _23310)). Qed.
Lemma lem1294693 (_23309 : nadd) (_23311 : nadd) : (nadd_le _23309 _23311) = (nadd_le _23309 _23311).
Proof. exact (eq_refl (nadd_le _23309 _23311)). Qed.
Lemma lem1294694 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) : (term360 _23308 _23310 _23309 _23311) = (term371 _23308 _23310 _23309 _23311).
Proof. exact (MK_COMB (@lem1294692 _23309 _23311 _23308 _23310) (@lem1294693 _23309 _23311)). Qed.
Lemma lem1294695 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) : (term356 _23309 _23311 _23308 _23310) = (term371 _23308 _23310 _23309 _23311).
Proof. exact (TRANS (@lem1294667 _23308 _23310 _23309 _23311) (@lem1294694 _23308 _23310 _23309 _23311)). Qed.
Lemma lem1294697 (n : nat) (x : nadd) (y : nadd) (z : nadd) (h1 : term167) (h2 : term73 x y z) : term372 x n y z.
Proof. exact (conj (@lem1294531 n y z h1) (@lem1294539 n x y z h2)). Qed.
Lemma lem1294698 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term95) (h2 : term167) (h3 : term73 x y z) (h4 : term75 x y d) : term373 d x n y z.
Proof. exact (conj (@lem1294523 n x y d h1 h2 h4) (@lem1294697 n x y z h2 h3)). Qed.
Lemma lem1294700 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) (h1 : term151) : term371 _23308 _23310 _23309 _23311.
Proof. exact (EQ_MP (@lem1294695 _23308 _23310 _23309 _23311) (@lem1294664 _23309 _23311 _23308 _23310 h1)). Qed.
Lemma lem1294701 (x : nadd) (d : nadd) (n : nat) (y : nadd) (z : nadd) (h1 : term151) : term374 x d n y z.
Proof. exact (@lem1294700 (term375 n x) (term317 n y z) (term376 n y d) (term317 n y z) h1). Qed.
Lemma lem1294704 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term167) (h4 : term73 x y z) (h5 : term75 x y d) : term377 d n y z.
Proof. exact (@lem1294701 x d n y z h1 (@lem1294698 n z x y d h2 h3 h4 h5)). Qed.
Lemma lem1294705 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term167) (h4 : term73 x y z) (h5 : term75 x y d) : term378 d n y z.
Proof. exact (fun h0 : term379 d n y z => @lem1294704 n z x y d h1 h2 h3 h4 h5). Qed.
Lemma lem1294707 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294708 (d : nadd) (n : nat) (y : nadd) (z : nadd) : (term378 d n y z) = (term377 d n y z).
Proof. exact (@lem1294707 (term377 d n y z)). Qed.
Lemma lem1294709 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term167) (h4 : term73 x y z) (h5 : term75 x y d) : term377 d n y z.
Proof. exact (EQ_MP (@lem1294708 d n y z) (@lem1294705 n z x y d h1 h2 h3 h4 h5)). Qed.
Lemma lem1294710 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term167) (h4 : term73 x y z) (h5 : term75 x y d) : term380 d n y z.
Proof. exact (conj (@lem1294402 n y z h3) (@lem1294709 n z x y d h1 h2 h3 h4 h5)). Qed.
Lemma lem1294711 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term158) (h4 : term167) (h5 : term73 x y z) (h6 : term75 x y d) : term381 d n y z.
Proof. exact (conj (@lem1294394 y n d h3) (@lem1294710 n z x y d h1 h2 h4 h5 h6)). Qed.
Lemma lem1294713 (_23308 : nadd) (_23310 : nadd) (_23309 : nadd) (_23311 : nadd) (h1 : term151) : term371 _23308 _23310 _23309 _23311.
Proof. exact (EQ_MP (@lem1294695 _23308 _23310 _23309 _23311) (@lem1294664 _23309 _23311 _23308 _23310 h1)). Qed.
Lemma lem1294714 (d : nadd) (n : nat) (y : nadd) (z : nadd) (h1 : term151) : term382 d n y z.
Proof. exact (@lem1294713 (term376 n y d) (term317 n y z) (term383 y n d) (term317 n y z) h1). Qed.
Lemma lem1294717 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term158) (h4 : term167) (h5 : term73 x y z) (h6 : term75 x y d) : term384 d n y z.
Proof. exact (@lem1294714 d n y z h1 (@lem1294711 n z x y d h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1294718 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term158) (h4 : term167) (h5 : term73 x y z) (h6 : term75 x y d) : term385 d n y z.
Proof. exact (fun h0 : term386 d n y z => @lem1294717 n z x y d h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1294720 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294721 (d : nadd) (n : nat) (y : nadd) (z : nadd) : (term385 d n y z) = (term384 d n y z).
Proof. exact (@lem1294720 (term384 d n y z)). Qed.
Lemma lem1294722 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term158) (h4 : term167) (h5 : term73 x y z) (h6 : term75 x y d) : term384 d n y z.
Proof. exact (EQ_MP (@lem1294721 d n y z) (@lem1294718 n z x y d h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1294728 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1294729 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : (term201 _23319 _23320 _23321) = (term387 _23320 _23319 _23321).
Proof. exact (@lem1294728 (nadd_le _23320 _23321) (term388 _23320 _23319 _23321)). Qed.
Lemma lem1294735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1294736 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : (term389 _23319 _23320 _23321) = (term390 _23320 _23319 _23321).
Proof. exact (MK_COMB (@lem1294735) (@lem1294729 _23320 _23319 _23321)). Qed.
Lemma lem1294742 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : (term387 _23320 _23319 _23321) = (term387 _23320 _23319 _23321).
Proof. exact (eq_refl (term387 _23320 _23319 _23321)). Qed.
Lemma lem1294743 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : ((term201 _23319 _23320 _23321) = (term387 _23320 _23319 _23321)) = ((term387 _23320 _23319 _23321) = (term387 _23320 _23319 _23321)).
Proof. exact (MK_COMB (@lem1294736 _23320 _23319 _23321) (@lem1294742 _23320 _23319 _23321)). Qed.
Lemma lem1294745 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1294746 (x : Prop) : (x = x) = True.
Proof. exact (@lem1294745 Prop x). Qed.
Lemma lem1294747 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : ((term387 _23320 _23319 _23321) = (term387 _23320 _23319 _23321)) = True.
Proof. exact (@lem1294746 (term387 _23320 _23319 _23321)). Qed.
Lemma lem1294748 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : ((term201 _23319 _23320 _23321) = (term387 _23320 _23319 _23321)) = True.
Proof. exact (TRANS (@lem1294743 _23320 _23319 _23321) (@lem1294747 _23320 _23319 _23321)). Qed.
Lemma lem1294749 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : True = ((term201 _23319 _23320 _23321) = (term387 _23320 _23319 _23321)).
Proof. exact (SYM (@lem1294748 _23320 _23319 _23321)). Qed.
Lemma lem1294750 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : (term201 _23319 _23320 _23321) = (term387 _23320 _23319 _23321).
Proof. exact (EQ_MP (@lem1294749 _23320 _23319 _23321) (@lem0)). Qed.
Lemma lem1294751 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) (h1 : term165) : term387 _23320 _23319 _23321.
Proof. exact (EQ_MP (@lem1294750 _23320 _23319 _23321) (@lem1294354 _23319 _23320 _23321 h1)). Qed.
Lemma lem1294753 (b : Prop) (a : Prop) : (a \/ b) = (term332 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1294754 (_23319 : nadd) (_23320 : nadd) (_23321 : nadd) : (term387 _23320 _23319 _23321) = (term391 _23319 _23320 _23321).
Proof. exact (@lem1294753 (term388 _23320 _23319 _23321) (nadd_le _23320 _23321)). Qed.
Lemma lem1294756 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1294757 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : (term392 _23320 _23319 _23321) = (term159 _23320 _23319 _23321).
Proof. exact (@lem1294756 (term159 _23320 _23319 _23321)). Qed.
Lemma lem1294758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1294759 (_23320 : nadd) (_23319 : nadd) (_23321 : nadd) : (term393 _23320 _23319 _23321) = (term394 _23320 _23319 _23321).
Proof. exact (MK_COMB (@lem1294758) (@lem1294757 _23320 _23319 _23321)). Qed.
Lemma lem1294760 (_23320 : nadd) (_23321 : nadd) : (nadd_le _23320 _23321) = (nadd_le _23320 _23321).
Proof. exact (eq_refl (nadd_le _23320 _23321)). Qed.
Lemma lem1294761 (_23319 : nadd) (_23320 : nadd) (_23321 : nadd) : (term391 _23319 _23320 _23321) = (term395 _23319 _23320 _23321).
Proof. exact (MK_COMB (@lem1294759 _23320 _23319 _23321) (@lem1294760 _23320 _23321)). Qed.
Lemma lem1294762 (_23319 : nadd) (_23320 : nadd) (_23321 : nadd) : (term387 _23320 _23319 _23321) = (term395 _23319 _23320 _23321).
Proof. exact (TRANS (@lem1294754 _23319 _23320 _23321) (@lem1294761 _23319 _23320 _23321)). Qed.
Lemma lem1294765 (_23319 : nadd) (_23320 : nadd) (_23321 : nadd) (h1 : term165) : term395 _23319 _23320 _23321.
Proof. exact (EQ_MP (@lem1294762 _23319 _23320 _23321) (@lem1294751 _23320 _23319 _23321 h1)). Qed.
Lemma lem1294766 (y : nadd) (n : nat) (d : nadd) (z : nadd) (h1 : term165) : term396 y n d z.
Proof. exact (@lem1294765 (term375 n y) (term375 n d) z h1). Qed.
Lemma lem1294769 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term75 x y d) : term168 n d z.
Proof. exact (@lem1294766 y n d z h3 (@lem1294722 n z x y d h1 h2 h4 h5 h6 h7)). Qed.
Lemma lem1294770 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term75 x y d) : term397 n d z.
Proof. exact (fun h0 : term177 n d z => @lem1294769 n z x y d h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem1294772 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294773 (n : nat) (d : nadd) (z : nadd) : (term397 n d z) = (term168 n d z).
Proof. exact (@lem1294772 (term168 n d z)). Qed.
Lemma lem1294774 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term75 x y d) : term168 n d z.
Proof. exact (EQ_MP (@lem1294773 n d z) (@lem1294770 n z x y d h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1294777 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1294779 (n : nat) (d : nadd) (z : nadd) : (term177 n d z) = (term398 n d z).
Proof. exact (@lem1294777 (term168 n d z)). Qed.
Lemma lem1294782 (n : nat) (d : nadd) (z : nadd) (h1 : term177 n d z) : term398 n d z.
Proof. exact (EQ_MP (@lem1294779 n d z) (@lem1294342 n d z h1)). Qed.
Lemma lem1294785 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (@lem1294782 n d z h7 (@lem1294774 n z x y d h1 h2 h3 h4 h5 h6 h8)). Qed.
Lemma lem1294786 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : term399.
Proof. exact (fun h0 : ~ False => @lem1294785 n z x y d h1 h2 h3 h4 h5 h6 h7 h8). Qed.
Lemma lem1294788 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1294789 : term399 = False.
Proof. exact (@lem1294788 False). Qed.
Lemma lem1294790 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294789) (@lem1294786 n z x y d h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1294791 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term177 n d z) = False.
Proof. exact (prop_ext (fun h9 : term177 n d z => @lem1294790 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294342 n d z h7)). Qed.
Lemma lem1294792 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294791 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294342 n d z h7)). Qed.
Lemma lem1294793 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term75 x y d) = False.
Proof. exact (prop_ext (fun h9 : term75 x y d => @lem1294792 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294324 x y d h8)). Qed.
Lemma lem1294794 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294793 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294324 x y d h8)). Qed.
Lemma lem1294795 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term177 n d z) = False.
Proof. exact (prop_ext (fun h9 : term177 n d z => @lem1294794 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294221 n d z h7)). Qed.
Lemma lem1294796 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294795 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294221 n d z h7)). Qed.
Lemma lem1294797 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term75 x y d) = False.
Proof. exact (prop_ext (fun h9 : term75 x y d => @lem1294796 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294119 x y d h8)). Qed.
Lemma lem1294798 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294797 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294119 x y d h8)). Qed.
Lemma lem1294799 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term177 n d z) = False.
Proof. exact (prop_ext (fun h9 : term177 n d z => @lem1294798 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294221 n d z h7)). Qed.
Lemma lem1294800 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294799 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294221 n d z h7)). Qed.
Lemma lem1294801 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : term158 = False.
Proof. exact (prop_ext (fun h9 : term158 => @lem1294800 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294139 h4)). Qed.
Lemma lem1294802 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294801 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294139 h4)). Qed.
Lemma lem1294803 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : term167 = False.
Proof. exact (prop_ext (fun h9 : term167 => @lem1294802 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294126 h5)). Qed.
Lemma lem1294804 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294803 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294126 h5)). Qed.
Lemma lem1294805 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term75 x y d) = False.
Proof. exact (prop_ext (fun h9 : term75 x y d => @lem1294804 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294119 x y d h8)). Qed.
Lemma lem1294806 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294805 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294119 x y d h8)). Qed.
Lemma lem1294807 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term73 x y z) = False.
Proof. exact (prop_ext (fun h9 : term73 x y z => @lem1294806 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294111 x y z h6)). Qed.
Lemma lem1294808 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294807 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294111 x y z h6)). Qed.
Lemma lem1294809 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term177 n d z) = False.
Proof. exact (prop_ext (fun h9 : term177 n d z => @lem1294808 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1294102 n d z h7)). Qed.
Lemma lem1294810 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294809 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1294102 n d z h7)). Qed.
Lemma lem1294811 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : term158 = False.
Proof. exact (prop_ext (fun h9 : term158 => @lem1294810 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293976 h4)). Qed.
Lemma lem1294812 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294811 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293976 h4)). Qed.
Lemma lem1294813 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : term167 = False.
Proof. exact (prop_ext (fun h9 : term167 => @lem1294812 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293873 h5)). Qed.
Lemma lem1294814 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294813 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293873 h5)). Qed.
Lemma lem1294815 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term75 x y d) = False.
Proof. exact (prop_ext (fun h9 : term75 x y d => @lem1294814 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293864 x y d h8)). Qed.
Lemma lem1294816 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294815 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293864 x y d h8)). Qed.
Lemma lem1294817 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : (term73 x y z) = False.
Proof. exact (prop_ext (fun h9 : term73 x y z => @lem1294816 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293848 x y z h6)). Qed.
Lemma lem1294818 (n : nat) (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term177 n d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294817 n z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293848 x y z h6)). Qed.
Lemma lem1294819 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : False.
Proof. exact (ex_elim (@lem1293151 d z h7) (fun n : nat => fun h0 : term179 d z n => @lem1294818 n z x y d h1 h2 h3 h4 h5 h6 h0 h8)). Qed.
Lemma lem1294820 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : term158 = False.
Proof. exact (prop_ext (fun h9 : term158 => @lem1294819 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293628 h4)). Qed.
Lemma lem1294821 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294820 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293628 h4)). Qed.
Lemma lem1294822 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : term167 = False.
Proof. exact (prop_ext (fun h9 : term167 => @lem1294821 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293164 h5)). Qed.
Lemma lem1294823 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294822 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293164 h5)). Qed.
Lemma lem1294824 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : (term75 x y d) = False.
Proof. exact (prop_ext (fun h9 : term75 x y d => @lem1294823 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293131 x y d h8)). Qed.
Lemma lem1294825 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294824 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293131 x y d h8)). Qed.
Lemma lem1294826 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : (term73 x y z) = False.
Proof. exact (prop_ext (fun h9 : term73 x y z => @lem1294825 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1293119 x y z h6)). Qed.
Lemma lem1294827 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term95) (h3 : term165) (h4 : term158) (h5 : term167) (h6 : term73 x y z) (h7 : term88 d z) (h8 : term75 x y d) : False.
Proof. exact (EQ_MP (@lem1294826 z x y d h1 h2 h3 h4 h5 h6 h7 h8) (@lem1293119 x y z h6)). Qed.
Lemma lem1294828 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term165) (h3 : term158) (h4 : term167) (h5 : term73 x y z) (h6 : term88 d z) (h7 : term75 x y d) : term93.
Proof. exact (fun h0 : term95 => @lem1294827 z x y d h1 h0 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem1294829 : term93 = term94.
Proof. exact (@lem69 term95). Qed.
Lemma lem1294830 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term151) (h2 : term165) (h3 : term158) (h4 : term167) (h5 : term73 x y z) (h6 : term88 d z) (h7 : term75 x y d) : term94.
Proof. exact (EQ_MP (@lem1294829) (@lem1294828 z x y d h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1294831 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term165) (h2 : term158) (h3 : term167) (h4 : term73 x y z) (h5 : term88 d z) (h6 : term75 x y d) : term98.
Proof. exact (fun h0 : term151 => @lem1294830 z x y d h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1294832 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term165) (h2 : term167) (h3 : term73 x y z) (h4 : term88 d z) (h5 : term75 x y d) : term101.
Proof. exact (fun h0 : term158 => @lem1294831 z x y d h1 h0 h2 h3 h4 h5). Qed.
Lemma lem1294833 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term167) (h2 : term73 x y z) (h3 : term88 d z) (h4 : term75 x y d) : term104.
Proof. exact (fun h0 : term165 => @lem1294832 z x y d h0 h1 h2 h3 h4). Qed.
Lemma lem1294834 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) : term107.
Proof. exact (fun h0 : term167 => @lem1294833 z x y d h0 h1 h2 h3). Qed.
Lemma lem1294835 (z : nadd) (x : nadd) (y : nadd) (d : nadd) (h1 : term73 x y z) (h2 : term75 x y d) : term110 d z.
Proof. exact (fun h0 : term88 d z => @lem1294834 z x y d h1 h0 h2). Qed.
Lemma lem1294836 (d : nadd) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term113 x y d z.
Proof. exact (fun h0 : term75 x y d => @lem1294835 z x y d h1 h0). Qed.
Lemma lem1294837 (d : nadd) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term116 x y d z.
Proof. exact (fun h0 : nadd_le y x => @lem1294836 d x y z h1). Qed.
Lemma lem1294838 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : term118 x y d z.
Proof. exact (fun h0 : term73 x y z => @lem1294837 d x y z h0). Qed.
Lemma lem1294843 (y : nadd) (d : nadd) (z : nadd) : term122 y d z.
Proof. exact (fun x : nadd => @lem1294838 x y d z). Qed.
Lemma lem1294848 (d : nadd) (z : nadd) : term126 d z.
Proof. exact (fun y : nadd => @lem1294843 y d z). Qed.
Lemma lem1294853 (z : nadd) : term130 z.
Proof. exact (fun d : nadd => @lem1294848 d z). Qed.
Lemma lem1294858 : term134.
Proof. exact (fun z : nadd => @lem1294853 z). Qed.
Lemma lem1294859 : term133.
Proof. exact (EQ_MP (@lem1293097) (@lem1294858)). Qed.
Lemma lem1294860 (z : nadd) : term400 z.
Proof. exact (@lem1294859 z). Qed.
Lemma lem1294861 (z : nadd) : (term400 z) = (term129 z).
Proof. exact (eq_refl (term400 z)). Qed.
Lemma lem1294862 (z : nadd) : term129 z.
Proof. exact (EQ_MP (@lem1294861 z) (@lem1294860 z)). Qed.
Lemma lem1294863 (z : nadd) (d : nadd) : term401 z d.
Proof. exact (@lem1294862 z d). Qed.
Lemma lem1294864 (d : nadd) (z : nadd) : (term401 z d) = (term125 d z).
Proof. exact (eq_refl (term401 z d)). Qed.
Lemma lem1294865 (d : nadd) (z : nadd) : term125 d z.
Proof. exact (EQ_MP (@lem1294864 d z) (@lem1294863 z d)). Qed.
Lemma lem1294866 (d : nadd) (z : nadd) (y : nadd) : term402 d z y.
Proof. exact (@lem1294865 d z y). Qed.
Lemma lem1294867 (y : nadd) (d : nadd) (z : nadd) : (term402 d z y) = (term121 y d z).
Proof. exact (eq_refl (term402 d z y)). Qed.
Lemma lem1294868 (y : nadd) (d : nadd) (z : nadd) : term121 y d z.
Proof. exact (EQ_MP (@lem1294867 y d z) (@lem1294866 d z y)). Qed.
Lemma lem1294869 (y : nadd) (d : nadd) (z : nadd) (x : nadd) : term403 y d z x.
Proof. exact (@lem1294868 y d z x). Qed.
Lemma lem1294870 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : (term403 y d z x) = (term89 x y d z).
Proof. exact (eq_refl (term403 y d z x)). Qed.
Lemma lem1294871 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : term89 x y d z.
Proof. exact (EQ_MP (@lem1294870 x y d z) (@lem1294869 y d z x)). Qed.
Lemma lem1294873 (x : nadd) (y : nadd) (d : nadd) (z : nadd) : term89 x y d z.
Proof. exact (@lem1292644 x y d z (@lem1294871 x y d z)). Qed.
Lemma lem1294874 (d : nadd) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term115 x y d z.
Proof. exact (@lem1294873 x y d z (@lem1292545 x y z h1)). Qed.
Lemma lem1294875 (d : nadd) (z : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : nadd_le y x) : term112 x y d z.
Proof. exact (@lem1294874 d x y z h1 (@lem1292544 y x h2)). Qed.
Lemma lem1294876 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term109 d z.
Proof. exact (@lem1294875 d z y x h1 h3 (@lem1292570 x y d h2)). Qed.
Lemma lem1294877 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : term106.
Proof. exact (@lem1294876 z d y x h1 h3 h4 (@lem1292629 d z h2)). Qed.
Lemma lem1294878 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : term103.
Proof. exact (@lem1294877 z d y x h1 h2 h3 h4 (@lem1267990)). Qed.
Lemma lem1294879 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : term100.
Proof. exact (@lem1294878 z d y x h1 h2 h3 h4 (@lem1284107)). Qed.
Lemma lem1294880 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : term97.
Proof. exact (@lem1294879 z d y x h1 h2 h3 h4 (@lem1278840)). Qed.
Lemma lem1294881 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : term93.
Proof. exact (@lem1294880 z d y x h1 h2 h3 h4 (@lem1270569)). Qed.
Lemma lem1294882 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : False.
Proof. exact (@lem1294881 z d y x h1 h2 h3 h4 (@lem1279298)). Qed.
Lemma lem1294883 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : (term88 d z) = False.
Proof. exact (prop_ext (fun h5 : term88 d z => @lem1294882 z d y x h1 h2 h3 h4) (fun h5 : False => @lem1292629 d z h2)). Qed.
Lemma lem1294884 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term88 d z) (h3 : term75 x y d) (h4 : nadd_le y x) : False.
Proof. exact (EQ_MP (@lem1294883 z d y x h1 h2 h3 h4) (@lem1292629 d z h2)). Qed.
Lemma lem1294885 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term87 d z.
Proof. exact (fun h0 : term88 d z => @lem1294884 z d y x h1 h0 h2 h3). Qed.
Lemma lem1294886 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term12 d z.
Proof. exact (EQ_MP (@lem1292628 d z) (@lem1294885 z d y x h1 h2 h3)). Qed.
Lemma lem1294887 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term15 d.
Proof. exact (ex_intro (term16 d) z (@lem1294886 z d y x h1 h2 h3)). Qed.
Lemma lem1294888 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term13 d.
Proof. exact (@lem1292624 d (@lem1294887 z d y x h1 h2 h3)). Qed.
Lemma lem1294889 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term84 y d.
Proof. exact (EQ_MP (@lem1292621 y d) (@lem1294888 z d y x h1 h2 h3)). Qed.
Lemma lem1294890 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term404 d y.
Proof. exact (@lem1292603 d y (@lem1294889 z d y x h1 h2 h3)). Qed.
Lemma lem1294892 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1294893 (y : nadd) : (term405 y) = (term406 y).
Proof. exact (@lem1294892 (term405 y)). Qed.
Lemma lem1294894 (y : nadd) : (term406 y) = (term405 y).
Proof. exact (SYM (@lem1294893 y)). Qed.
Lemma lem1294895 (y : nadd) (h1 : term407 y) : term407 y.
Proof. exact (h1). Qed.
Lemma lem1294898 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term408 z x d y) : term408 z x d y.
Proof. exact (h1). Qed.
Lemma lem1294899 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : term409 z x d y.
Proof. exact (fun h0 : term408 z x d y => @lem1294898 z x d y h0). Qed.
Lemma lem1294900 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term409 z x d y) : term409 z x d y.
Proof. exact (h1). Qed.
Lemma lem1294901 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term408 z x d y) : term408 z x d y.
Proof. exact (h1). Qed.
Lemma lem1294902 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term408 z x d y) (h2 : term409 z x d y) : term408 z x d y.
Proof. exact (@lem1294900 z x d y h2 (@lem1294901 z x d y h1)). Qed.
Lemma lem1294903 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term408 z x d y) : term410 z x d y.
Proof. exact (fun h0 : term409 z x d y => @lem1294902 z x d y h1 h0). Qed.
Lemma lem1294904 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term409 z x d y) : term409 z x d y.
Proof. exact (h1). Qed.
Lemma lem1294905 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term408 z x d y) (h2 : term409 z x d y) : term408 z x d y.
Proof. exact (@lem1294903 z x d y h1 (@lem1294904 z x d y h2)). Qed.
Lemma lem1294906 (z : nadd) (x : nadd) (d : nadd) (y : nadd) (h1 : term409 z x d y) : term409 z x d y.
Proof. exact (fun h0 : term408 z x d y => @lem1294905 z x d y h0 h1). Qed.
Lemma lem1294907 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : term411 z x d y.
Proof. exact (fun h0 : term409 z x d y => @lem1294906 z x d y h0). Qed.
Lemma lem1294910 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : term409 z x d y.
Proof. exact (@lem1294907 z x d y (@lem1294899 z x d y)). Qed.
Lemma lem1294990 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1294991 : term412 = term413.
Proof. exact (@lem1294990 term414). Qed.
Lemma lem1294996 : term415 = term415.
Proof. exact (eq_refl term415). Qed.
Lemma lem1294997 : term416 = term417.
Proof. exact (MK_COMB (@lem1294996) (@lem1294991)). Qed.
Lemma lem1295000 : term418 = term418.
Proof. exact (eq_refl term418). Qed.
Lemma lem1295001 : term419 = term420.
Proof. exact (MK_COMB (@lem1295000) (@lem1294997)). Qed.
Lemma lem1295004 : term421 = term421.
Proof. exact (eq_refl term421). Qed.
Lemma lem1295005 : term422 = term423.
Proof. exact (MK_COMB (@lem1295004) (@lem1295001)). Qed.
Lemma lem1295008 (y : nadd) : (term424 y) = (term424 y).
Proof. exact (eq_refl (term424 y)). Qed.
Lemma lem1295009 (y : nadd) : (term425 y) = (term426 y).
Proof. exact (MK_COMB (@lem1295008 y) (@lem1295005)). Qed.
Lemma lem1295012 (x : nadd) (y : nadd) (d : nadd) : (term111 x y d) = (term111 x y d).
Proof. exact (eq_refl (term111 x y d)). Qed.
Lemma lem1295013 (x : nadd) (d : nadd) (y : nadd) : (term427 x d y) = (term428 x d y).
Proof. exact (MK_COMB (@lem1295012 x y d) (@lem1295009 y)). Qed.
Lemma lem1295016 (y : nadd) (x : nadd) : (term114 y x) = (term114 y x).
Proof. exact (eq_refl (term114 y x)). Qed.
Lemma lem1295017 (x : nadd) (d : nadd) (y : nadd) : (term429 x d y) = (term430 x d y).
Proof. exact (MK_COMB (@lem1295016 y x) (@lem1295013 x d y)). Qed.
Lemma lem1295020 (x : nadd) (y : nadd) (z : nadd) : (term117 x y z) = (term117 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1295021 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : (term408 z x d y) = (term431 z x d y).
Proof. exact (MK_COMB (@lem1295020 x y z) (@lem1295017 x d y)). Qed.
Lemma lem1295024 (x : nadd) (d : nadd) (y : nadd) : (term432 x d y) = (term433 x d y).
Proof. exact (fun_ext (fun z : nadd => @lem1295021 z x d y)). Qed.
Lemma lem1295025 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295026 (x : nadd) (d : nadd) (y : nadd) : (term434 x d y) = (term435 x d y).
Proof. exact (MK_COMB (@lem1295025) (@lem1295024 x d y)). Qed.
Lemma lem1295031 (d : nadd) (y : nadd) : (term436 d y) = (term437 d y).
Proof. exact (fun_ext (fun x : nadd => @lem1295026 x d y)). Qed.
Lemma lem1295032 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295033 (d : nadd) (y : nadd) : (term438 d y) = (term439 d y).
Proof. exact (MK_COMB (@lem1295032) (@lem1295031 d y)). Qed.
Lemma lem1295038 (y : nadd) : (term440 y) = (term441 y).
Proof. exact (fun_ext (fun d : nadd => @lem1295033 d y)). Qed.
Lemma lem1295039 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295040 (y : nadd) : (term442 y) = (term443 y).
Proof. exact (MK_COMB (@lem1295039) (@lem1295038 y)). Qed.
Lemma lem1295045 : term444 = term445.
Proof. exact (fun_ext (fun y : nadd => @lem1295040 y)). Qed.
Lemma lem1295046 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295055 : term446 = term447.
Proof. exact (MK_COMB (@lem1295046) (@lem1295045)). Qed.
Lemma lem1295056 (x : nadd) : (term448 x) = (term448 x).
Proof. exact (eq_refl (term448 x)). Qed.
Lemma lem1295057 : term449 = term449.
Proof. exact (fun_ext (fun x : nadd => @lem1295056 x)). Qed.
Lemma lem1295058 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295059 : term414 = term414.
Proof. exact (MK_COMB (@lem1295058) (@lem1295057)). Qed.
Lemma lem1295060 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1295061 : term413 = term413.
Proof. exact (MK_COMB (@lem1295060) (@lem1295059)). Qed.
Lemma lem1295070 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term30 x y x' y') = (term30 x y x' y').
Proof. exact (eq_refl (term30 x y x' y')). Qed.
Lemma lem1295071 (x : nadd) (y : nadd) (x' : nadd) : (term450 x y x') = (term450 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1295070 x y x' y')). Qed.
Lemma lem1295072 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295073 (x : nadd) (y : nadd) (x' : nadd) : (term28 x y x') = (term28 x y x').
Proof. exact (MK_COMB (@lem1295072) (@lem1295071 x y x')). Qed.
Lemma lem1295074 (x : nadd) (x' : nadd) : (term451 x x') = (term451 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1295073 x y x')). Qed.
Lemma lem1295075 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295076 (x : nadd) (x' : nadd) : (term26 x x') = (term26 x x').
Proof. exact (MK_COMB (@lem1295075) (@lem1295074 x x')). Qed.
Lemma lem1295077 (x : nadd) : (term452 x) = (term452 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1295076 x x')). Qed.
Lemma lem1295078 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295079 (x : nadd) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1295078) (@lem1295077 x)). Qed.
Lemma lem1295080 : term453 = term453.
Proof. exact (fun_ext (fun x : nadd => @lem1295079 x)). Qed.
Lemma lem1295081 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295082 : term22 = term22.
Proof. exact (MK_COMB (@lem1295081) (@lem1295080)). Qed.
Lemma lem1295083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1295084 : term415 = term415.
Proof. exact (MK_COMB (@lem1295083) (@lem1295082)). Qed.
Lemma lem1295085 : term417 = term417.
Proof. exact (MK_COMB (@lem1295084) (@lem1295061)). Qed.
Lemma lem1295094 (y : nadd) (x : nadd) (z : nadd) : (term47 y x z) = (term47 y x z).
Proof. exact (eq_refl (term47 y x z)). Qed.
Lemma lem1295095 (y : nadd) (x : nadd) : (term454 y x) = (term454 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1295094 y x z)). Qed.
Lemma lem1295096 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295097 (y : nadd) (x : nadd) : (term45 y x) = (term45 y x).
Proof. exact (MK_COMB (@lem1295096) (@lem1295095 y x)). Qed.
Lemma lem1295098 (x : nadd) : (term455 x) = (term455 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295097 y x)). Qed.
Lemma lem1295099 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295100 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1295099) (@lem1295098 x)). Qed.
Lemma lem1295101 : term456 = term456.
Proof. exact (fun_ext (fun x : nadd => @lem1295100 x)). Qed.
Lemma lem1295102 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295103 : term41 = term41.
Proof. exact (MK_COMB (@lem1295102) (@lem1295101)). Qed.
Lemma lem1295104 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1295105 : term418 = term418.
Proof. exact (MK_COMB (@lem1295104) (@lem1295103)). Qed.
Lemma lem1295106 : term420 = term420.
Proof. exact (MK_COMB (@lem1295105) (@lem1295085)). Qed.
Lemma lem1295107 (y : nadd) (x : nadd) : (term457 y x) = (term457 y x).
Proof. exact (eq_refl (term457 y x)). Qed.
Lemma lem1295108 (x : nadd) : (term458 x) = (term458 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295107 y x)). Qed.
Lemma lem1295109 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295110 (x : nadd) : (term459 x) = (term459 x).
Proof. exact (MK_COMB (@lem1295109) (@lem1295108 x)). Qed.
Lemma lem1295111 : term460 = term460.
Proof. exact (fun_ext (fun x : nadd => @lem1295110 x)). Qed.
Lemma lem1295112 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295113 : term461 = term461.
Proof. exact (MK_COMB (@lem1295112) (@lem1295111)). Qed.
Lemma lem1295114 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1295115 : term421 = term421.
Proof. exact (MK_COMB (@lem1295114) (@lem1295113)). Qed.
Lemma lem1295116 : term423 = term423.
Proof. exact (MK_COMB (@lem1295115) (@lem1295106)). Qed.
Lemma lem1295121 (y : nadd) : (term424 y) = (term424 y).
Proof. exact (eq_refl (term424 y)). Qed.
Lemma lem1295122 (y : nadd) : (term426 y) = (term426 y).
Proof. exact (MK_COMB (@lem1295121 y) (@lem1295116)). Qed.
Lemma lem1295125 (x : nadd) (y : nadd) (d : nadd) : (term111 x y d) = (term111 x y d).
Proof. exact (eq_refl (term111 x y d)). Qed.
Lemma lem1295126 (x : nadd) (d : nadd) (y : nadd) : (term428 x d y) = (term428 x d y).
Proof. exact (MK_COMB (@lem1295125 x y d) (@lem1295122 y)). Qed.
Lemma lem1295129 (y : nadd) (x : nadd) : (term114 y x) = (term114 y x).
Proof. exact (eq_refl (term114 y x)). Qed.
Lemma lem1295130 (x : nadd) (d : nadd) (y : nadd) : (term430 x d y) = (term430 x d y).
Proof. exact (MK_COMB (@lem1295129 y x) (@lem1295126 x d y)). Qed.
Lemma lem1295131 (x : nadd) (n : nat) (y : nadd) (z : nadd) : (term170 x n y z) = (term170 x n y z).
Proof. exact (eq_refl (term170 x n y z)). Qed.
Lemma lem1295132 (x : nadd) (y : nadd) (z : nadd) : (term171 x y z) = (term171 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1295131 x n y z)). Qed.
Lemma lem1295133 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1295134 (x : nadd) (y : nadd) (z : nadd) : (term73 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1295133) (@lem1295132 x y z)). Qed.
Lemma lem1295135 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1295136 (x : nadd) (y : nadd) (z : nadd) : (term117 x y z) = (term117 x y z).
Proof. exact (MK_COMB (@lem1295135) (@lem1295134 x y z)). Qed.
Lemma lem1295137 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : (term431 z x d y) = (term431 z x d y).
Proof. exact (MK_COMB (@lem1295136 x y z) (@lem1295130 x d y)). Qed.
Lemma lem1295138 (x : nadd) (d : nadd) (y : nadd) : (term433 x d y) = (term433 x d y).
Proof. exact (fun_ext (fun z : nadd => @lem1295137 z x d y)). Qed.
Lemma lem1295139 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295140 (x : nadd) (d : nadd) (y : nadd) : (term435 x d y) = (term435 x d y).
Proof. exact (MK_COMB (@lem1295139) (@lem1295138 x d y)). Qed.
Lemma lem1295141 (d : nadd) (y : nadd) : (term437 d y) = (term437 d y).
Proof. exact (fun_ext (fun x : nadd => @lem1295140 x d y)). Qed.
Lemma lem1295142 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295143 (d : nadd) (y : nadd) : (term439 d y) = (term439 d y).
Proof. exact (MK_COMB (@lem1295142) (@lem1295141 d y)). Qed.
Lemma lem1295144 (y : nadd) : (term441 y) = (term441 y).
Proof. exact (fun_ext (fun d : nadd => @lem1295143 d y)). Qed.
Lemma lem1295145 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295146 (y : nadd) : (term443 y) = (term443 y).
Proof. exact (MK_COMB (@lem1295145) (@lem1295144 y)). Qed.
Lemma lem1295147 : term445 = term445.
Proof. exact (fun_ext (fun y : nadd => @lem1295146 y)). Qed.
Lemma lem1295148 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295149 : term447 = term447.
Proof. exact (MK_COMB (@lem1295148) (@lem1295147)). Qed.
Lemma lem1295264 : term446 = term447.
Proof. exact (TRANS (@lem1295055) (@lem1295149)). Qed.
Lemma lem1295265 : term447 = term446.
Proof. exact (SYM (@lem1295264)). Qed.
Lemma lem1295270 (h1 : term461) : term461.
Proof. exact (h1). Qed.
Lemma lem1295271 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1295273 (h1 : term414) : term414.
Proof. exact (h1). Qed.
Lemma lem1295304 (y : nadd) (h1 : term407 y) : term407 y.
Proof. exact (h1). Qed.
Lemma lem1295305 (y : nadd) (x : nadd) : (term457 y x) = (term457 y x).
Proof. exact (eq_refl (term457 y x)). Qed.
Lemma lem1295306 (x : nadd) : (term458 x) = (term458 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295305 y x)). Qed.
Lemma lem1295307 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295308 (x : nadd) : (term459 x) = (term459 x).
Proof. exact (MK_COMB (@lem1295307) (@lem1295306 x)). Qed.
Lemma lem1295309 : term460 = term460.
Proof. exact (fun_ext (fun x : nadd => @lem1295308 x)). Qed.
Lemma lem1295310 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295323 : term461 = term461.
Proof. exact (MK_COMB (@lem1295310) (@lem1295309)). Qed.
Lemma lem1295324 (h1 : term461) : term461.
Proof. exact (EQ_MP (@lem1295323) (@lem1295270 h1)). Qed.
Lemma lem1295331 (x : nadd) (y : nadd) (z : nadd) : (term462 x y z) = (term463 x y z).
Proof. exact (@lem17045 (nadd_eq x y) (nadd_eq y z)). Qed.
Lemma lem1295332 (x : nadd) (z : nadd) : (nadd_eq x z) = (nadd_eq x z).
Proof. exact (eq_refl (nadd_eq x z)). Qed.
Lemma lem1295333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1295334 (x : nadd) (y : nadd) (z : nadd) : (term464 x y z) = (term465 x y z).
Proof. exact (MK_COMB (@lem1295333) (@lem1295331 x y z)). Qed.
Lemma lem1295335 (y : nadd) (x : nadd) (z : nadd) : (term466 y x z) = (term467 y x z).
Proof. exact (MK_COMB (@lem1295334 x y z) (@lem1295332 x z)). Qed.
Lemma lem1295336 (y : nadd) (x : nadd) (z : nadd) : (term47 y x z) = (term466 y x z).
Proof. exact (@lem17265 (term48 x y z) (nadd_eq x z)). Qed.
Lemma lem1295337 (y : nadd) (x : nadd) (z : nadd) : (term47 y x z) = (term467 y x z).
Proof. exact (TRANS (@lem1295336 y x z) (@lem1295335 y x z)). Qed.
Lemma lem1295338 (y : nadd) (x : nadd) : (term454 y x) = (term468 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1295337 y x z)). Qed.
Lemma lem1295339 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295340 (y : nadd) (x : nadd) : (term45 y x) = (term469 y x).
Proof. exact (MK_COMB (@lem1295339) (@lem1295338 y x)). Qed.
Lemma lem1295341 (x : nadd) : (term455 x) = (term470 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295340 y x)). Qed.
Lemma lem1295342 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295343 (x : nadd) : (term43 x) = (term471 x).
Proof. exact (MK_COMB (@lem1295342) (@lem1295341 x)). Qed.
Lemma lem1295344 : term456 = term472.
Proof. exact (fun_ext (fun x : nadd => @lem1295343 x)). Qed.
Lemma lem1295345 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295406 : term41 = term473.
Proof. exact (MK_COMB (@lem1295345) (@lem1295344)). Qed.
Lemma lem1295407 (h1 : term41) : term473.
Proof. exact (EQ_MP (@lem1295406) (@lem1295271 h1)). Qed.
Lemma lem1295498 (x : nadd) : (term448 x) = (term448 x).
Proof. exact (eq_refl (term448 x)). Qed.
Lemma lem1295499 : term449 = term449.
Proof. exact (fun_ext (fun x : nadd => @lem1295498 x)). Qed.
Lemma lem1295500 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295509 : term414 = term414.
Proof. exact (MK_COMB (@lem1295500) (@lem1295499)). Qed.
Lemma lem1295510 (h1 : term414) : term414.
Proof. exact (EQ_MP (@lem1295509) (@lem1295273 h1)). Qed.
Lemma lem1295567 (y : nadd) (h1 : term407 y) : term407 y.
Proof. exact (h1). Qed.
Lemma lem1295580 (y : nadd) (x : nadd) : (term457 y x) = (term457 y x).
Proof. exact (eq_refl (term457 y x)). Qed.
Lemma lem1295581 (x : nadd) : (term458 x) = (term458 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295580 y x)). Qed.
Lemma lem1295582 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295583 (x : nadd) : (term459 x) = (term459 x).
Proof. exact (MK_COMB (@lem1295582) (@lem1295581 x)). Qed.
Lemma lem1295584 : term460 = term460.
Proof. exact (fun_ext (fun x : nadd => @lem1295583 x)). Qed.
Lemma lem1295585 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295586 : term461 = term461.
Proof. exact (MK_COMB (@lem1295585) (@lem1295584)). Qed.
Lemma lem1295587 (h1 : term461) : term461.
Proof. exact (EQ_MP (@lem1295586) (@lem1295324 h1)). Qed.
Lemma lem1295612 (y : nadd) (x : nadd) (z : nadd) : (term467 y x z) = (term467 y x z).
Proof. exact (eq_refl (term467 y x z)). Qed.
Lemma lem1295613 (y : nadd) (x : nadd) : (term468 y x) = (term468 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1295612 y x z)). Qed.
Lemma lem1295614 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295615 (y : nadd) (x : nadd) : (term469 y x) = (term469 y x).
Proof. exact (MK_COMB (@lem1295614) (@lem1295613 y x)). Qed.
Lemma lem1295616 (x : nadd) : (term470 x) = (term470 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295615 y x)). Qed.
Lemma lem1295617 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295618 (x : nadd) : (term471 x) = (term471 x).
Proof. exact (MK_COMB (@lem1295617) (@lem1295616 x)). Qed.
Lemma lem1295619 : term472 = term472.
Proof. exact (fun_ext (fun x : nadd => @lem1295618 x)). Qed.
Lemma lem1295620 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295621 : term473 = term473.
Proof. exact (MK_COMB (@lem1295620) (@lem1295619)). Qed.
Lemma lem1295622 (h1 : term41) : term473.
Proof. exact (EQ_MP (@lem1295621) (@lem1295407 h1)). Qed.
Lemma lem1295681 (x : nadd) : (term448 x) = (term448 x).
Proof. exact (eq_refl (term448 x)). Qed.
Lemma lem1295682 : term449 = term449.
Proof. exact (fun_ext (fun x : nadd => @lem1295681 x)). Qed.
Lemma lem1295683 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295684 : term414 = term414.
Proof. exact (MK_COMB (@lem1295683) (@lem1295682)). Qed.
Lemma lem1295685 (h1 : term414) : term414.
Proof. exact (EQ_MP (@lem1295684) (@lem1295510 h1)). Qed.
Lemma lem1295704 (y : nadd) (h1 : term407 y) : term407 y.
Proof. exact (h1). Qed.
Lemma lem1295706 (y : nadd) (x : nadd) : (term457 y x) = (term457 y x).
Proof. exact (eq_refl (term457 y x)). Qed.
Lemma lem1295707 (x : nadd) : (term458 x) = (term458 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295706 y x)). Qed.
Lemma lem1295708 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295709 (x : nadd) : (term459 x) = (term459 x).
Proof. exact (MK_COMB (@lem1295708) (@lem1295707 x)). Qed.
Lemma lem1295710 : term460 = term460.
Proof. exact (fun_ext (fun x : nadd => @lem1295709 x)). Qed.
Lemma lem1295711 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295713 : term461 = term461.
Proof. exact (MK_COMB (@lem1295711) (@lem1295710)). Qed.
Lemma lem1295714 (h1 : term461) : term461.
Proof. exact (EQ_MP (@lem1295713) (@lem1295587 h1)). Qed.
Lemma lem1295728 (y : nadd) (x : nadd) (z : nadd) : (term467 y x z) = (term467 y x z).
Proof. exact (eq_refl (term467 y x z)). Qed.
Lemma lem1295729 (y : nadd) (x : nadd) : (term468 y x) = (term468 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1295728 y x z)). Qed.
Lemma lem1295730 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295731 (y : nadd) (x : nadd) : (term469 y x) = (term469 y x).
Proof. exact (MK_COMB (@lem1295730) (@lem1295729 y x)). Qed.
Lemma lem1295732 (x : nadd) : (term470 x) = (term470 x).
Proof. exact (fun_ext (fun y : nadd => @lem1295731 y x)). Qed.
Lemma lem1295733 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295734 (x : nadd) : (term471 x) = (term471 x).
Proof. exact (MK_COMB (@lem1295733) (@lem1295732 x)). Qed.
Lemma lem1295735 : term472 = term472.
Proof. exact (fun_ext (fun x : nadd => @lem1295734 x)). Qed.
Lemma lem1295736 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295738 : term473 = term473.
Proof. exact (MK_COMB (@lem1295736) (@lem1295735)). Qed.
Lemma lem1295739 (h1 : term41) : term473.
Proof. exact (EQ_MP (@lem1295738) (@lem1295622 h1)). Qed.
Lemma lem1295769 (x : nadd) : (term448 x) = (term448 x).
Proof. exact (eq_refl (term448 x)). Qed.
Lemma lem1295770 : term449 = term449.
Proof. exact (fun_ext (fun x : nadd => @lem1295769 x)). Qed.
Lemma lem1295771 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1295773 : term414 = term414.
Proof. exact (MK_COMB (@lem1295771) (@lem1295770)). Qed.
Lemma lem1295774 (h1 : term414) : term414.
Proof. exact (EQ_MP (@lem1295773) (@lem1295685 h1)). Qed.
Lemma lem1295778 (_23323 : nadd) (h1 : term461) : term474 _23323.
Proof. exact (@lem1295714 h1 _23323). Qed.
Lemma lem1295779 (_23323 : nadd) : (term474 _23323) = (term459 _23323).
Proof. exact (eq_refl (term474 _23323)). Qed.
Lemma lem1295780 (_23323 : nadd) (h1 : term461) : term459 _23323.
Proof. exact (EQ_MP (@lem1295779 _23323) (@lem1295778 _23323 h1)). Qed.
Lemma lem1295781 (_23323 : nadd) (_23324 : nadd) (h1 : term461) : term475 _23323 _23324.
Proof. exact (@lem1295780 _23323 h1 _23324). Qed.
Lemma lem1295782 (_23324 : nadd) (_23323 : nadd) : (term475 _23323 _23324) = (term457 _23324 _23323).
Proof. exact (eq_refl (term475 _23323 _23324)). Qed.
Lemma lem1295784 (_23325 : nadd) (h1 : term41) : term476 _23325.
Proof. exact (@lem1295739 h1 _23325). Qed.
Lemma lem1295785 (_23325 : nadd) : (term476 _23325) = (term471 _23325).
Proof. exact (eq_refl (term476 _23325)). Qed.
Lemma lem1295786 (_23325 : nadd) (h1 : term41) : term471 _23325.
Proof. exact (EQ_MP (@lem1295785 _23325) (@lem1295784 _23325 h1)). Qed.
Lemma lem1295787 (_23325 : nadd) (_23326 : nadd) (h1 : term41) : term477 _23325 _23326.
Proof. exact (@lem1295786 _23325 h1 _23326). Qed.
Lemma lem1295788 (_23326 : nadd) (_23325 : nadd) : (term477 _23325 _23326) = (term469 _23326 _23325).
Proof. exact (eq_refl (term477 _23325 _23326)). Qed.
Lemma lem1295789 (_23326 : nadd) (_23325 : nadd) (h1 : term41) : term469 _23326 _23325.
Proof. exact (EQ_MP (@lem1295788 _23326 _23325) (@lem1295787 _23325 _23326 h1)). Qed.
Lemma lem1295790 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) (h1 : term41) : term478 _23326 _23325 _23327.
Proof. exact (@lem1295789 _23326 _23325 h1 _23327). Qed.
Lemma lem1295791 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) : (term478 _23326 _23325 _23327) = (term467 _23326 _23325 _23327).
Proof. exact (eq_refl (term478 _23326 _23325 _23327)). Qed.
Lemma lem1295792 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) (h1 : term41) : term467 _23326 _23325 _23327.
Proof. exact (EQ_MP (@lem1295791 _23326 _23325 _23327) (@lem1295790 _23326 _23325 _23327 h1)). Qed.
Lemma lem1295805 (_23332 : nadd) (h1 : term414) : term479 _23332.
Proof. exact (@lem1295774 h1 _23332). Qed.
Lemma lem1295806 (_23332 : nadd) : (term479 _23332) = (term448 _23332).
Proof. exact (eq_refl (term479 _23332)). Qed.
Lemma lem1295815 (y : nadd) (h1 : term407 y) : term407 y.
Proof. exact (h1). Qed.
Lemma lem1295828 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) : (term467 _23326 _23325 _23327) = (term480 _23326 _23325 _23327).
Proof. exact (@lem1292378 (term310 _23325 _23326) (term310 _23326 _23327) (nadd_eq _23325 _23327)). Qed.
Lemma lem1295829 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) (h1 : term41) : term480 _23326 _23325 _23327.
Proof. exact (EQ_MP (@lem1295828 _23326 _23325 _23327) (@lem1295792 _23326 _23325 _23327 h1)). Qed.
Lemma lem1295845 (_23324 : nadd) (_23323 : nadd) (h1 : term461) : term457 _23324 _23323.
Proof. exact (EQ_MP (@lem1295782 _23324 _23323) (@lem1295781 _23323 _23324 h1)). Qed.
Lemma lem1295846 (y : nadd) (h1 : term461) : term481 y.
Proof. exact (@lem1295845 term82 y h1). Qed.
Lemma lem1295847 (y : nadd) (h1 : term461) : term482 y.
Proof. exact (fun h0 : term483 y => @lem1295846 y h1). Qed.
Lemma lem1295849 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1295850 (y : nadd) : (term482 y) = (term481 y).
Proof. exact (@lem1295849 (term481 y)). Qed.
Lemma lem1295851 (y : nadd) (h1 : term461) : term481 y.
Proof. exact (EQ_MP (@lem1295850 y) (@lem1295847 y h1)). Qed.
Lemma lem1295853 (_23332 : nadd) (h1 : term414) : term448 _23332.
Proof. exact (EQ_MP (@lem1295806 _23332) (@lem1295805 _23332 h1)). Qed.
Lemma lem1295854 (y : nadd) (h1 : term414) : term448 y.
Proof. exact (@lem1295853 y h1). Qed.
Lemma lem1295855 (y : nadd) (h1 : term414) : term484 y.
Proof. exact (fun h0 : term485 y => @lem1295854 y h1). Qed.
Lemma lem1295857 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1295858 (y : nadd) : (term484 y) = (term448 y).
Proof. exact (@lem1295857 (term448 y)). Qed.
Lemma lem1295859 (y : nadd) (h1 : term414) : term448 y.
Proof. exact (EQ_MP (@lem1295858 y) (@lem1295855 y h1)). Qed.
Lemma lem1295875 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1295876 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term486 _23326 _23325 _23327) = (term487 _23325 _23326 _23327).
Proof. exact (@lem1295875 (nadd_eq _23325 _23327) (term310 _23326 _23327)). Qed.
Lemma lem1295882 (_23325 : nadd) (_23326 : nadd) : (term327 _23325 _23326) = (term327 _23325 _23326).
Proof. exact (eq_refl (term327 _23325 _23326)). Qed.
Lemma lem1295883 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term480 _23326 _23325 _23327) = (term488 _23325 _23326 _23327).
Proof. exact (MK_COMB (@lem1295882 _23325 _23326) (@lem1295876 _23325 _23326 _23327)). Qed.
Lemma lem1295887 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1295888 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term488 _23325 _23326 _23327) = (term489 _23325 _23326 _23327).
Proof. exact (@lem1295887 (nadd_eq _23325 _23327) (term310 _23325 _23326) (term310 _23326 _23327)). Qed.
Lemma lem1295904 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term480 _23326 _23325 _23327) = (term489 _23325 _23326 _23327).
Proof. exact (TRANS (@lem1295883 _23325 _23326 _23327) (@lem1295888 _23325 _23326 _23327)). Qed.
Lemma lem1295905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1295906 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term490 _23326 _23325 _23327) = (term491 _23325 _23326 _23327).
Proof. exact (MK_COMB (@lem1295905) (@lem1295904 _23325 _23326 _23327)). Qed.
Lemma lem1295922 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term489 _23325 _23326 _23327) = (term489 _23325 _23326 _23327).
Proof. exact (eq_refl (term489 _23325 _23326 _23327)). Qed.
Lemma lem1295923 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : ((term480 _23326 _23325 _23327) = (term489 _23325 _23326 _23327)) = ((term489 _23325 _23326 _23327) = (term489 _23325 _23326 _23327)).
Proof. exact (MK_COMB (@lem1295906 _23325 _23326 _23327) (@lem1295922 _23325 _23326 _23327)). Qed.
Lemma lem1295925 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1295926 (x : Prop) : (x = x) = True.
Proof. exact (@lem1295925 Prop x). Qed.
Lemma lem1295927 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : ((term489 _23325 _23326 _23327) = (term489 _23325 _23326 _23327)) = True.
Proof. exact (@lem1295926 (term489 _23325 _23326 _23327)). Qed.
Lemma lem1295928 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : ((term480 _23326 _23325 _23327) = (term489 _23325 _23326 _23327)) = True.
Proof. exact (TRANS (@lem1295923 _23325 _23326 _23327) (@lem1295927 _23325 _23326 _23327)). Qed.
Lemma lem1295929 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : True = ((term480 _23326 _23325 _23327) = (term489 _23325 _23326 _23327)).
Proof. exact (SYM (@lem1295928 _23325 _23326 _23327)). Qed.
Lemma lem1295930 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term480 _23326 _23325 _23327) = (term489 _23325 _23326 _23327).
Proof. exact (EQ_MP (@lem1295929 _23325 _23326 _23327) (@lem0)). Qed.
Lemma lem1295931 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) (h1 : term41) : term489 _23325 _23326 _23327.
Proof. exact (EQ_MP (@lem1295930 _23325 _23326 _23327) (@lem1295829 _23326 _23325 _23327 h1)). Qed.
Lemma lem1295933 (b : Prop) (a : Prop) : (a \/ b) = (term332 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1295934 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) : (term489 _23325 _23326 _23327) = (term492 _23326 _23325 _23327).
Proof. exact (@lem1295933 (term463 _23325 _23326 _23327) (nadd_eq _23325 _23327)). Qed.
Lemma lem1295936 (a : Prop) (b : Prop) : (term334 a b) = (term335 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1295937 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term493 _23325 _23326 _23327) = (term494 _23325 _23326 _23327).
Proof. exact (@lem1295936 (term310 _23325 _23326) (term310 _23326 _23327)). Qed.
Lemma lem1295939 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1295940 (_23325 : nadd) (_23326 : nadd) : (term339 _23325 _23326) = (nadd_eq _23325 _23326).
Proof. exact (@lem1295939 (nadd_eq _23325 _23326)). Qed.
Lemma lem1295941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1295942 (_23325 : nadd) (_23326 : nadd) : (term340 _23325 _23326) = (term341 _23325 _23326).
Proof. exact (MK_COMB (@lem1295941) (@lem1295940 _23325 _23326)). Qed.
Lemma lem1295944 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1295945 (_23326 : nadd) (_23327 : nadd) : (term339 _23326 _23327) = (nadd_eq _23326 _23327).
Proof. exact (@lem1295944 (nadd_eq _23326 _23327)). Qed.
Lemma lem1295946 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term494 _23325 _23326 _23327) = (term48 _23325 _23326 _23327).
Proof. exact (MK_COMB (@lem1295942 _23325 _23326) (@lem1295945 _23326 _23327)). Qed.
Lemma lem1295947 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term493 _23325 _23326 _23327) = (term48 _23325 _23326 _23327).
Proof. exact (TRANS (@lem1295937 _23325 _23326 _23327) (@lem1295946 _23325 _23326 _23327)). Qed.
Lemma lem1295948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1295949 (_23325 : nadd) (_23326 : nadd) (_23327 : nadd) : (term495 _23325 _23326 _23327) = (term496 _23325 _23326 _23327).
Proof. exact (MK_COMB (@lem1295948) (@lem1295947 _23325 _23326 _23327)). Qed.
Lemma lem1295950 (_23325 : nadd) (_23327 : nadd) : (nadd_eq _23325 _23327) = (nadd_eq _23325 _23327).
Proof. exact (eq_refl (nadd_eq _23325 _23327)). Qed.
Lemma lem1295951 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) : (term492 _23326 _23325 _23327) = (term47 _23326 _23325 _23327).
Proof. exact (MK_COMB (@lem1295949 _23325 _23326 _23327) (@lem1295950 _23325 _23327)). Qed.
Lemma lem1295952 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) : (term489 _23325 _23326 _23327) = (term47 _23326 _23325 _23327).
Proof. exact (TRANS (@lem1295934 _23326 _23325 _23327) (@lem1295951 _23326 _23325 _23327)). Qed.
Lemma lem1295954 (y : nadd) (h1 : term461) (h2 : term414) : term497 y.
Proof. exact (conj (@lem1295851 y h1) (@lem1295859 y h2)). Qed.
Lemma lem1295956 (_23326 : nadd) (_23325 : nadd) (_23327 : nadd) (h1 : term41) : term47 _23326 _23325 _23327.
Proof. exact (EQ_MP (@lem1295952 _23326 _23325 _23327) (@lem1295931 _23325 _23326 _23327 h1)). Qed.
Lemma lem1295957 (y : nadd) (h1 : term41) : term498 y.
Proof. exact (@lem1295956 (term499 y) (term500 y) y h1). Qed.
Lemma lem1295960 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) : term405 y.
Proof. exact (@lem1295957 y h1 (@lem1295954 y h2 h3)). Qed.
Lemma lem1295961 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) : term501 y.
Proof. exact (fun h0 : term407 y => @lem1295960 y h1 h2 h3). Qed.
Lemma lem1295963 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1295964 (y : nadd) : (term501 y) = (term405 y).
Proof. exact (@lem1295963 (term405 y)). Qed.
Lemma lem1295965 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) : term405 y.
Proof. exact (EQ_MP (@lem1295964 y) (@lem1295961 y h1 h2 h3)). Qed.
Lemma lem1295968 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1295970 (y : nadd) : (term407 y) = (term502 y).
Proof. exact (@lem1295968 (term405 y)). Qed.
Lemma lem1295973 (y : nadd) (h1 : term407 y) : term502 y.
Proof. exact (EQ_MP (@lem1295970 y) (@lem1295815 y h1)). Qed.
Lemma lem1295976 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (@lem1295973 y h4 (@lem1295965 y h1 h2 h3)). Qed.
Lemma lem1295977 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : term399.
Proof. exact (fun h0 : ~ False => @lem1295976 y h1 h2 h3 h4). Qed.
Lemma lem1295979 (p : Prop) : (term315 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1295980 : term399 = False.
Proof. exact (@lem1295979 False). Qed.
Lemma lem1295981 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295980) (@lem1295977 y h1 h2 h3 h4)). Qed.
Lemma lem1295982 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : (term407 y) = False.
Proof. exact (prop_ext (fun h5 : term407 y => @lem1295981 y h1 h2 h3 h4) (fun h5 : False => @lem1295815 y h4)). Qed.
Lemma lem1295983 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295982 y h1 h2 h3 h4) (@lem1295815 y h4)). Qed.
Lemma lem1295984 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : (term407 y) = False.
Proof. exact (prop_ext (fun h5 : term407 y => @lem1295983 y h1 h2 h3 h4) (fun h5 : False => @lem1295704 y h4)). Qed.
Lemma lem1295985 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295984 y h1 h2 h3 h4) (@lem1295704 y h4)). Qed.
Lemma lem1295986 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : term414 = False.
Proof. exact (prop_ext (fun h5 : term414 => @lem1295985 y h1 h2 h3 h4) (fun h5 : False => @lem1295774 h3)). Qed.
Lemma lem1295987 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295986 y h1 h2 h3 h4) (@lem1295774 h3)). Qed.
Lemma lem1295988 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : term461 = False.
Proof. exact (prop_ext (fun h5 : term461 => @lem1295987 y h1 h2 h3 h4) (fun h5 : False => @lem1295714 h2)). Qed.
Lemma lem1295989 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295988 y h1 h2 h3 h4) (@lem1295714 h2)). Qed.
Lemma lem1295990 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : (term407 y) = False.
Proof. exact (prop_ext (fun h5 : term407 y => @lem1295989 y h1 h2 h3 h4) (fun h5 : False => @lem1295704 y h4)). Qed.
Lemma lem1295991 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295990 y h1 h2 h3 h4) (@lem1295704 y h4)). Qed.
Lemma lem1295992 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : term414 = False.
Proof. exact (prop_ext (fun h5 : term414 => @lem1295991 y h1 h2 h3 h4) (fun h5 : False => @lem1295685 h3)). Qed.
Lemma lem1295993 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295992 y h1 h2 h3 h4) (@lem1295685 h3)). Qed.
Lemma lem1295994 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : term461 = False.
Proof. exact (prop_ext (fun h5 : term461 => @lem1295993 y h1 h2 h3 h4) (fun h5 : False => @lem1295587 h2)). Qed.
Lemma lem1295995 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295994 y h1 h2 h3 h4) (@lem1295587 h2)). Qed.
Lemma lem1295996 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : (term407 y) = False.
Proof. exact (prop_ext (fun h5 : term407 y => @lem1295995 y h1 h2 h3 h4) (fun h5 : False => @lem1295567 y h4)). Qed.
Lemma lem1295997 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295996 y h1 h2 h3 h4) (@lem1295567 y h4)). Qed.
Lemma lem1295998 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : term414 = False.
Proof. exact (prop_ext (fun h5 : term414 => @lem1295997 y h1 h2 h3 h4) (fun h5 : False => @lem1295510 h3)). Qed.
Lemma lem1295999 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1295998 y h1 h2 h3 h4) (@lem1295510 h3)). Qed.
Lemma lem1296000 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : term461 = False.
Proof. exact (prop_ext (fun h5 : term461 => @lem1295999 y h1 h2 h3 h4) (fun h5 : False => @lem1295324 h2)). Qed.
Lemma lem1296001 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1296000 y h1 h2 h3 h4) (@lem1295324 h2)). Qed.
Lemma lem1296002 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : (term407 y) = False.
Proof. exact (prop_ext (fun h5 : term407 y => @lem1296001 y h1 h2 h3 h4) (fun h5 : False => @lem1295304 y h4)). Qed.
Lemma lem1296003 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term414) (h4 : term407 y) : False.
Proof. exact (EQ_MP (@lem1296002 y h1 h2 h3 h4) (@lem1295304 y h4)). Qed.
Lemma lem1296004 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term407 y) : term412.
Proof. exact (fun h0 : term414 => @lem1296003 y h1 h2 h0 h3). Qed.
Lemma lem1296005 : term412 = term413.
Proof. exact (@lem69 term414). Qed.
Lemma lem1296006 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term407 y) : term413.
Proof. exact (EQ_MP (@lem1296005) (@lem1296004 y h1 h2 h3)). Qed.
Lemma lem1296007 (y : nadd) (h1 : term41) (h2 : term461) (h3 : term407 y) : term417.
Proof. exact (fun h0 : term22 => @lem1296006 y h1 h2 h3). Qed.
Lemma lem1296008 (y : nadd) (h1 : term461) (h2 : term407 y) : term420.
Proof. exact (fun h0 : term41 => @lem1296007 y h0 h1 h2). Qed.
Lemma lem1296009 (y : nadd) (h1 : term407 y) : term423.
Proof. exact (fun h0 : term461 => @lem1296008 y h0 h1). Qed.
Lemma lem1296010 (y : nadd) : term426 y.
Proof. exact (fun h0 : term407 y => @lem1296009 y h0). Qed.
Lemma lem1296011 (x : nadd) (d : nadd) (y : nadd) : term428 x d y.
Proof. exact (fun h0 : term75 x y d => @lem1296010 y). Qed.
Lemma lem1296012 (x : nadd) (d : nadd) (y : nadd) : term430 x d y.
Proof. exact (fun h0 : nadd_le y x => @lem1296011 x d y). Qed.
Lemma lem1296013 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : term431 z x d y.
Proof. exact (fun h0 : term73 x y z => @lem1296012 x d y). Qed.
Lemma lem1296018 (x : nadd) (d : nadd) (y : nadd) : term435 x d y.
Proof. exact (fun z : nadd => @lem1296013 z x d y). Qed.
Lemma lem1296023 (d : nadd) (y : nadd) : term439 d y.
Proof. exact (fun x : nadd => @lem1296018 x d y). Qed.
Lemma lem1296028 (y : nadd) : term443 y.
Proof. exact (fun d : nadd => @lem1296023 d y). Qed.
Lemma lem1296033 : term447.
Proof. exact (fun y : nadd => @lem1296028 y). Qed.
Lemma lem1296034 : term446.
Proof. exact (EQ_MP (@lem1295265) (@lem1296033)). Qed.
Lemma lem1296035 (y : nadd) : term503 y.
Proof. exact (@lem1296034 y). Qed.
Lemma lem1296036 (y : nadd) : (term503 y) = (term442 y).
Proof. exact (eq_refl (term503 y)). Qed.
Lemma lem1296037 (y : nadd) : term442 y.
Proof. exact (EQ_MP (@lem1296036 y) (@lem1296035 y)). Qed.
Lemma lem1296038 (y : nadd) (d : nadd) : term504 y d.
Proof. exact (@lem1296037 y d). Qed.
Lemma lem1296039 (d : nadd) (y : nadd) : (term504 y d) = (term438 d y).
Proof. exact (eq_refl (term504 y d)). Qed.
Lemma lem1296040 (d : nadd) (y : nadd) : term438 d y.
Proof. exact (EQ_MP (@lem1296039 d y) (@lem1296038 y d)). Qed.
Lemma lem1296041 (d : nadd) (y : nadd) (x : nadd) : term505 d y x.
Proof. exact (@lem1296040 d y x). Qed.
Lemma lem1296042 (x : nadd) (d : nadd) (y : nadd) : (term505 d y x) = (term434 x d y).
Proof. exact (eq_refl (term505 d y x)). Qed.
Lemma lem1296043 (x : nadd) (d : nadd) (y : nadd) : term434 x d y.
Proof. exact (EQ_MP (@lem1296042 x d y) (@lem1296041 d y x)). Qed.
Lemma lem1296044 (x : nadd) (d : nadd) (y : nadd) (z : nadd) : term506 x d y z.
Proof. exact (@lem1296043 x d y z). Qed.
Lemma lem1296045 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : (term506 x d y z) = (term408 z x d y).
Proof. exact (eq_refl (term506 x d y z)). Qed.
Lemma lem1296046 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : term408 z x d y.
Proof. exact (EQ_MP (@lem1296045 z x d y) (@lem1296044 x d y z)). Qed.
Lemma lem1296048 (z : nadd) (x : nadd) (d : nadd) (y : nadd) : term408 z x d y.
Proof. exact (@lem1294910 z x d y (@lem1296046 z x d y)). Qed.
Lemma lem1296049 (d : nadd) (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : term429 x d y.
Proof. exact (@lem1296048 z x d y (@lem1292545 x y z h1)). Qed.
Lemma lem1296050 (d : nadd) (z : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : nadd_le y x) : term427 x d y.
Proof. exact (@lem1296049 d x y z h1 (@lem1292544 y x h2)). Qed.
Lemma lem1296051 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term425 y.
Proof. exact (@lem1296050 d z y x h1 h3 (@lem1292570 x y d h2)). Qed.
Lemma lem1296052 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term407 y) (h3 : term75 x y d) (h4 : nadd_le y x) : term422.
Proof. exact (@lem1296051 z d y x h1 h3 h4 (@lem1294895 y h2)). Qed.
Lemma lem1296053 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term407 y) (h3 : term75 x y d) (h4 : nadd_le y x) : term419.
Proof. exact (@lem1296052 z d y x h1 h2 h3 h4 (@lem1274476)). Qed.
Lemma lem1296054 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term407 y) (h3 : term75 x y d) (h4 : nadd_le y x) : term416.
Proof. exact (@lem1296053 z d y x h1 h2 h3 h4 (@lem1268295)). Qed.
Lemma lem1296055 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term407 y) (h3 : term75 x y d) (h4 : nadd_le y x) : term412.
Proof. exact (@lem1296054 z d y x h1 h2 h3 h4 (@lem1274424)). Qed.
Lemma lem1296056 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term407 y) (h3 : term75 x y d) (h4 : nadd_le y x) : False.
Proof. exact (@lem1296055 z d y x h1 h2 h3 h4 (@lem1274816)). Qed.
Lemma lem1296057 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term407 y) (h3 : term75 x y d) (h4 : nadd_le y x) : (term407 y) = False.
Proof. exact (prop_ext (fun h5 : term407 y => @lem1296056 z d y x h1 h2 h3 h4) (fun h5 : False => @lem1294895 y h2)). Qed.
Lemma lem1296058 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term407 y) (h3 : term75 x y d) (h4 : nadd_le y x) : False.
Proof. exact (EQ_MP (@lem1296057 z d y x h1 h2 h3 h4) (@lem1294895 y h2)). Qed.
Lemma lem1296059 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term406 y.
Proof. exact (fun h0 : term407 y => @lem1296058 z d y x h1 h0 h2 h3). Qed.
Lemma lem1296060 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term405 y.
Proof. exact (EQ_MP (@lem1294894 y) (@lem1296059 z d y x h1 h2 h3)). Qed.
Lemma lem1296061 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term507 d y.
Proof. exact (conj (@lem1294890 z d y x h1 h2 h3) (@lem1296060 z d y x h1 h2 h3)). Qed.
Lemma lem1296062 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term508 d y.
Proof. exact (ex_intro (term509 d y) (term500 y) (@lem1296061 z d y x h1 h2 h3)). Qed.
Lemma lem1296063 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term77 d y.
Proof. exact (@lem1292600 d y (@lem1296062 z d y x h1 h2 h3)). Qed.
Lemma lem1296064 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term78 x d y.
Proof. exact (EQ_MP (@lem1292597 x y d h2) (@lem1296063 z d y x h1 h2 h3)). Qed.
Lemma lem1296065 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : term50 x y.
Proof. exact (ex_intro (term51 x y) (nadd_add y d) (@lem1296064 z d y x h1 h2 h3)). Qed.
Lemma lem1296066 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : nadd_eq x y.
Proof. exact (@lem1292575 x y (@lem1296065 z d y x h1 h2 h3)). Qed.
Lemma lem1296067 (z : nadd) (d : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : term75 x y d) (h3 : nadd_le y x) : nadd_le x y.
Proof. exact (@lem1292572 x y (@lem1296066 z d y x h1 h2 h3)). Qed.
Lemma lem1296069 (z : nadd) (y : nadd) (x : nadd) (h1 : term73 x y z) (h2 : nadd_le y x) : nadd_le x y.
Proof. exact (ex_elim (@lem1292569 y x h2) (fun d : nadd => fun h0 : term510 x y d => @lem1296067 z d y x h1 h0 h2)). Qed.
Lemma lem1296070 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : nadd_le x y.
Proof. exact (or_elim (@lem1292542 y x) (fun h0 : nadd_le x y => @lem1292556 x y h0) (fun h0 : nadd_le y x => @lem1296069 z y x h1 h0)). Qed.
Lemma lem1296071 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : (term73 x y z) = (nadd_le x y).
Proof. exact (prop_ext (fun h2 : term73 x y z => @lem1296070 x y z h1) (fun h2 : nadd_le x y => @lem1292545 x y z h1)). Qed.
Lemma lem1296072 (x : nadd) (y : nadd) (z : nadd) (h1 : term73 x y z) : nadd_le x y.
Proof. exact (EQ_MP (@lem1296071 x y z h1) (@lem1292545 x y z h1)). Qed.
Lemma lem1296073 (z : nadd) (x : nadd) (y : nadd) : term511 z x y.
Proof. exact (fun h0 : term73 x y z => @lem1296072 x y z h0). Qed.
Lemma lem1296078 (x : nadd) (y : nadd) : term512 x y.
Proof. exact (fun z : nadd => @lem1296073 z x y). Qed.
Lemma lem1296083 (x : nadd) : term513 x.
Proof. exact (fun y : nadd => @lem1296078 x y). Qed.
Lemma lem1296088 : term514.
Proof. exact (fun x : nadd => @lem1296083 x). Qed.
