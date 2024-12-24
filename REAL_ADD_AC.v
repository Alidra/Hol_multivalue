Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ADD_AC_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338238_spec.
Require Import thm1338438_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1351382 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1351383 (n : real) (m : real) (p : real) : (term1 n m p) = (term2 n m p).
Proof. exact (@lem1351382 (term1 n m p)). Qed.
Lemma lem1351384 (n : real) (m : real) (p : real) : (term2 n m p) = (term1 n m p).
Proof. exact (SYM (@lem1351383 n m p)). Qed.
Lemma lem1351385 (n : real) (m : real) (p : real) (h1 : term3 n m p) : term3 n m p.
Proof. exact (h1). Qed.
Lemma lem1351388 (n : real) (m : real) (p : real) (h1 : term4 n m p) : term4 n m p.
Proof. exact (h1). Qed.
Lemma lem1351389 (n : real) (m : real) (p : real) : term5 n m p.
Proof. exact (fun h0 : term4 n m p => @lem1351388 n m p h0). Qed.
Lemma lem1351390 (n : real) (m : real) (p : real) (h1 : term5 n m p) : term5 n m p.
Proof. exact (h1). Qed.
Lemma lem1351391 (n : real) (m : real) (p : real) (h1 : term4 n m p) : term4 n m p.
Proof. exact (h1). Qed.
Lemma lem1351392 (n : real) (m : real) (p : real) (h1 : term4 n m p) (h2 : term5 n m p) : term4 n m p.
Proof. exact (@lem1351390 n m p h2 (@lem1351391 n m p h1)). Qed.
Lemma lem1351393 (n : real) (m : real) (p : real) (h1 : term4 n m p) : term6 n m p.
Proof. exact (fun h0 : term5 n m p => @lem1351392 n m p h1 h0). Qed.
Lemma lem1351394 (n : real) (m : real) (p : real) (h1 : term5 n m p) : term5 n m p.
Proof. exact (h1). Qed.
Lemma lem1351395 (n : real) (m : real) (p : real) (h1 : term4 n m p) (h2 : term5 n m p) : term4 n m p.
Proof. exact (@lem1351393 n m p h1 (@lem1351394 n m p h2)). Qed.
Lemma lem1351396 (n : real) (m : real) (p : real) (h1 : term5 n m p) : term5 n m p.
Proof. exact (fun h0 : term4 n m p => @lem1351395 n m p h0 h1). Qed.
Lemma lem1351397 (n : real) (m : real) (p : real) : term7 n m p.
Proof. exact (fun h0 : term5 n m p => @lem1351396 n m p h0). Qed.
Lemma lem1351400 (n : real) (m : real) (p : real) : term5 n m p.
Proof. exact (@lem1351397 n m p (@lem1351389 n m p)). Qed.
Lemma lem1351430 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1351431 : term8 = term9.
Proof. exact (@lem1351430 term10). Qed.
Lemma lem1351444 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1351445 : term12 = term13.
Proof. exact (MK_COMB (@lem1351444) (@lem1351431)). Qed.
Lemma lem1351448 (n : real) (m : real) (p : real) : (term14 n m p) = (term14 n m p).
Proof. exact (eq_refl (term14 n m p)). Qed.
Lemma lem1351449 (n : real) (m : real) (p : real) : (term4 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem1351448 n m p) (@lem1351445)). Qed.
Lemma lem1351452 (m : real) (p : real) : (term16 m p) = (term17 m p).
Proof. exact (fun_ext (fun n : real => @lem1351449 n m p)). Qed.
Lemma lem1351453 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351454 (m : real) (p : real) : (term18 m p) = (term19 m p).
Proof. exact (MK_COMB (@lem1351453) (@lem1351452 m p)). Qed.
Lemma lem1351459 (p : real) : (term20 p) = (term21 p).
Proof. exact (fun_ext (fun m : real => @lem1351454 m p)). Qed.
Lemma lem1351460 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351461 (p : real) : (term22 p) = (term23 p).
Proof. exact (MK_COMB (@lem1351460) (@lem1351459 p)). Qed.
Lemma lem1351466 : term24 = term25.
Proof. exact (fun_ext (fun p : real => @lem1351461 p)). Qed.
Lemma lem1351467 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351476 : term26 = term27.
Proof. exact (MK_COMB (@lem1351467) (@lem1351466)). Qed.
Lemma lem1351477 (x : real) (y : real) (z : real) : ((term28 x y z) = (term29 x y z)) = ((term28 x y z) = (term29 x y z)).
Proof. exact (eq_refl ((term28 x y z) = (term29 x y z))). Qed.
Lemma lem1351478 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (fun_ext (fun z : real => @lem1351477 x y z)). Qed.
Lemma lem1351479 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351480 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1351479) (@lem1351478 x y)). Qed.
Lemma lem1351481 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1351480 x y)). Qed.
Lemma lem1351482 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351483 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1351482) (@lem1351481 x)). Qed.
Lemma lem1351484 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1351483 x)). Qed.
Lemma lem1351485 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351486 : term10 = term10.
Proof. exact (MK_COMB (@lem1351485) (@lem1351484)). Qed.
Lemma lem1351487 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1351488 : term9 = term9.
Proof. exact (MK_COMB (@lem1351487) (@lem1351486)). Qed.
Lemma lem1351489 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1351490 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1351489 y x)). Qed.
Lemma lem1351491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351492 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1351491) (@lem1351490 x)). Qed.
Lemma lem1351493 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1351492 x)). Qed.
Lemma lem1351494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351495 : term38 = term38.
Proof. exact (MK_COMB (@lem1351494) (@lem1351493)). Qed.
Lemma lem1351496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1351497 : term11 = term11.
Proof. exact (MK_COMB (@lem1351496) (@lem1351495)). Qed.
Lemma lem1351498 : term13 = term13.
Proof. exact (MK_COMB (@lem1351497) (@lem1351488)). Qed.
Lemma lem1351511 (n : real) (m : real) (p : real) : (term14 n m p) = (term14 n m p).
Proof. exact (eq_refl (term14 n m p)). Qed.
Lemma lem1351512 (n : real) (m : real) (p : real) : (term15 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem1351511 n m p) (@lem1351498)). Qed.
Lemma lem1351513 (m : real) (p : real) : (term17 m p) = (term17 m p).
Proof. exact (fun_ext (fun n : real => @lem1351512 n m p)). Qed.
Lemma lem1351514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351515 (m : real) (p : real) : (term19 m p) = (term19 m p).
Proof. exact (MK_COMB (@lem1351514) (@lem1351513 m p)). Qed.
Lemma lem1351516 (p : real) : (term21 p) = (term21 p).
Proof. exact (fun_ext (fun m : real => @lem1351515 m p)). Qed.
Lemma lem1351517 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351518 (p : real) : (term23 p) = (term23 p).
Proof. exact (MK_COMB (@lem1351517) (@lem1351516 p)). Qed.
Lemma lem1351519 : term25 = term25.
Proof. exact (fun_ext (fun p : real => @lem1351518 p)). Qed.
Lemma lem1351520 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351521 : term27 = term27.
Proof. exact (MK_COMB (@lem1351520) (@lem1351519)). Qed.
Lemma lem1351580 : term26 = term27.
Proof. exact (TRANS (@lem1351476) (@lem1351521)). Qed.
Lemma lem1351581 : term27 = term26.
Proof. exact (SYM (@lem1351580)). Qed.
Lemma lem1351582 (n : real) (m : real) (p : real) (h1 : term3 n m p) : term3 n m p.
Proof. exact (h1). Qed.
Lemma lem1351583 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1351584 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1351592 (n : real) (m : real) (p : real) : (term39 n m p) = (term40 n m p).
Proof. exact (@lem17045 ((term29 m n p) = (term28 m n p)) ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem1351594 (n : real) (m : real) : (term41 n m) = (term41 n m).
Proof. exact (eq_refl (term41 n m)). Qed.
Lemma lem1351595 (n : real) (m : real) (p : real) : (term42 n m p) = (term43 n m p).
Proof. exact (MK_COMB (@lem1351594 n m) (@lem1351592 n m p)). Qed.
Lemma lem1351596 (n : real) (m : real) (p : real) : (term3 n m p) = (term42 n m p).
Proof. exact (@lem17045 ((real_add m n) = (real_add n m)) (term44 n m p)). Qed.
Lemma lem1351601 (n : real) (m : real) (p : real) : (term3 n m p) = (term43 n m p).
Proof. exact (TRANS (@lem1351596 n m p) (@lem1351595 n m p)). Qed.
Lemma lem1351603 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1351604 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1351603 y x)). Qed.
Lemma lem1351605 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351606 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1351605) (@lem1351604 x)). Qed.
Lemma lem1351607 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1351606 x)). Qed.
Lemma lem1351608 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351621 : term38 = term38.
Proof. exact (MK_COMB (@lem1351608) (@lem1351607)). Qed.
Lemma lem1351622 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1351621) (@lem1351583 h1)). Qed.
Lemma lem1351623 (x : real) (y : real) (z : real) : ((term28 x y z) = (term29 x y z)) = ((term28 x y z) = (term29 x y z)).
Proof. exact (eq_refl ((term28 x y z) = (term29 x y z))). Qed.
Lemma lem1351624 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (fun_ext (fun z : real => @lem1351623 x y z)). Qed.
Lemma lem1351625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351626 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1351625) (@lem1351624 x y)). Qed.
Lemma lem1351627 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1351626 x y)). Qed.
Lemma lem1351628 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351629 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1351628) (@lem1351627 x)). Qed.
Lemma lem1351630 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1351629 x)). Qed.
Lemma lem1351631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351648 : term10 = term10.
Proof. exact (MK_COMB (@lem1351631) (@lem1351630)). Qed.
Lemma lem1351649 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1351648) (@lem1351584 h1)). Qed.
Lemma lem1351717 (n : real) (m : real) (p : real) (h1 : term3 n m p) : term43 n m p.
Proof. exact (EQ_MP (@lem1351601 n m p) (@lem1351582 n m p h1)). Qed.
Lemma lem1351730 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1351731 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1351730 y x)). Qed.
Lemma lem1351732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351733 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1351732) (@lem1351731 x)). Qed.
Lemma lem1351734 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1351733 x)). Qed.
Lemma lem1351735 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351736 : term38 = term38.
Proof. exact (MK_COMB (@lem1351735) (@lem1351734)). Qed.
Lemma lem1351737 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1351736) (@lem1351622 h1)). Qed.
Lemma lem1351758 (x : real) (y : real) (z : real) : ((term28 x y z) = (term29 x y z)) = ((term28 x y z) = (term29 x y z)).
Proof. exact (eq_refl ((term28 x y z) = (term29 x y z))). Qed.
Lemma lem1351759 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (fun_ext (fun z : real => @lem1351758 x y z)). Qed.
Lemma lem1351760 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351761 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1351760) (@lem1351759 x y)). Qed.
Lemma lem1351762 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1351761 x y)). Qed.
Lemma lem1351763 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351764 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1351763) (@lem1351762 x)). Qed.
Lemma lem1351765 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1351764 x)). Qed.
Lemma lem1351766 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351767 : term10 = term10.
Proof. exact (MK_COMB (@lem1351766) (@lem1351765)). Qed.
Lemma lem1351768 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1351767) (@lem1351649 h1)). Qed.
Lemma lem1351770 (n : real) (m : real) (p : real) (h1 : term40 n m p) : term40 n m p.
Proof. exact (h1). Qed.
Lemma lem1351774 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1351775 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1351774 y x)). Qed.
Lemma lem1351776 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351777 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1351776) (@lem1351775 x)). Qed.
Lemma lem1351778 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1351777 x)). Qed.
Lemma lem1351779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351781 : term38 = term38.
Proof. exact (MK_COMB (@lem1351779) (@lem1351778)). Qed.
Lemma lem1351782 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1351781) (@lem1351737 h1)). Qed.
Lemma lem1351799 (n : real) (m : real) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1351811 (x : real) (y : real) (z : real) : ((term28 x y z) = (term29 x y z)) = ((term28 x y z) = (term29 x y z)).
Proof. exact (eq_refl ((term28 x y z) = (term29 x y z))). Qed.
Lemma lem1351812 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (fun_ext (fun z : real => @lem1351811 x y z)). Qed.
Lemma lem1351813 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351814 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1351813) (@lem1351812 x y)). Qed.
Lemma lem1351815 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1351814 x y)). Qed.
Lemma lem1351816 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351817 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1351816) (@lem1351815 x)). Qed.
Lemma lem1351818 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1351817 x)). Qed.
Lemma lem1351819 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351821 : term10 = term10.
Proof. exact (MK_COMB (@lem1351819) (@lem1351818)). Qed.
Lemma lem1351822 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1351821) (@lem1351768 h1)). Qed.
Lemma lem1351826 (m : real) (n : real) (p : real) (h1 : term46 m n p) : term46 m n p.
Proof. exact (h1). Qed.
Lemma lem1351828 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1351829 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1351828 y x)). Qed.
Lemma lem1351830 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351831 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1351830) (@lem1351829 x)). Qed.
Lemma lem1351832 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1351831 x)). Qed.
Lemma lem1351833 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351835 : term38 = term38.
Proof. exact (MK_COMB (@lem1351833) (@lem1351832)). Qed.
Lemma lem1351836 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1351835) (@lem1351737 h1)). Qed.
Lemma lem1351838 (x : real) (y : real) (z : real) : ((term28 x y z) = (term29 x y z)) = ((term28 x y z) = (term29 x y z)).
Proof. exact (eq_refl ((term28 x y z) = (term29 x y z))). Qed.
Lemma lem1351839 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (fun_ext (fun z : real => @lem1351838 x y z)). Qed.
Lemma lem1351840 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351841 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1351840) (@lem1351839 x y)). Qed.
Lemma lem1351842 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1351841 x y)). Qed.
Lemma lem1351843 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351844 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1351843) (@lem1351842 x)). Qed.
Lemma lem1351845 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1351844 x)). Qed.
Lemma lem1351846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1351848 : term10 = term10.
Proof. exact (MK_COMB (@lem1351846) (@lem1351845)). Qed.
Lemma lem1351849 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1351848) (@lem1351768 h1)). Qed.
Lemma lem1351853 (n : real) (m : real) (p : real) (h1 : term47 n m p) : term47 n m p.
Proof. exact (h1). Qed.
Lemma lem1351854 (_24043 : real) (h1 : term38) : term48 _24043.
Proof. exact (@lem1351782 h1 _24043). Qed.
Lemma lem1351855 (_24043 : real) : (term48 _24043) = (term36 _24043).
Proof. exact (eq_refl (term48 _24043)). Qed.
Lemma lem1351856 (_24043 : real) (h1 : term38) : term36 _24043.
Proof. exact (EQ_MP (@lem1351855 _24043) (@lem1351854 _24043 h1)). Qed.
Lemma lem1351857 (_24043 : real) (_24044 : real) (h1 : term38) : term49 _24043 _24044.
Proof. exact (@lem1351856 _24043 h1 _24044). Qed.
Lemma lem1351858 (_24044 : real) (_24043 : real) : (term49 _24043 _24044) = ((real_add _24043 _24044) = (real_add _24044 _24043)).
Proof. exact (eq_refl (term49 _24043 _24044)). Qed.
Lemma lem1351875 (_24050 : real) (h1 : term10) : term50 _24050.
Proof. exact (@lem1351822 h1 _24050). Qed.
Lemma lem1351876 (_24050 : real) : (term50 _24050) = (term33 _24050).
Proof. exact (eq_refl (term50 _24050)). Qed.
Lemma lem1351877 (_24050 : real) (h1 : term10) : term33 _24050.
Proof. exact (EQ_MP (@lem1351876 _24050) (@lem1351875 _24050 h1)). Qed.
Lemma lem1351878 (_24050 : real) (_24051 : real) (h1 : term10) : term51 _24050 _24051.
Proof. exact (@lem1351877 _24050 h1 _24051). Qed.
Lemma lem1351879 (_24050 : real) (_24051 : real) : (term51 _24050 _24051) = (term31 _24050 _24051).
Proof. exact (eq_refl (term51 _24050 _24051)). Qed.
Lemma lem1351880 (_24050 : real) (_24051 : real) (h1 : term10) : term31 _24050 _24051.
Proof. exact (EQ_MP (@lem1351879 _24050 _24051) (@lem1351878 _24050 _24051 h1)). Qed.
Lemma lem1351881 (_24050 : real) (_24051 : real) (_24052 : real) (h1 : term10) : term52 _24050 _24051 _24052.
Proof. exact (@lem1351880 _24050 _24051 h1 _24052). Qed.
Lemma lem1351882 (_24050 : real) (_24051 : real) (_24052 : real) : (term52 _24050 _24051 _24052) = ((term28 _24050 _24051 _24052) = (term29 _24050 _24051 _24052)).
Proof. exact (eq_refl (term52 _24050 _24051 _24052)). Qed.
Lemma lem1351884 (_24053 : real) (h1 : term38) : term48 _24053.
Proof. exact (@lem1351836 h1 _24053). Qed.
Lemma lem1351885 (_24053 : real) : (term48 _24053) = (term36 _24053).
Proof. exact (eq_refl (term48 _24053)). Qed.
Lemma lem1351886 (_24053 : real) (h1 : term38) : term36 _24053.
Proof. exact (EQ_MP (@lem1351885 _24053) (@lem1351884 _24053 h1)). Qed.
Lemma lem1351887 (_24053 : real) (_24054 : real) (h1 : term38) : term49 _24053 _24054.
Proof. exact (@lem1351886 _24053 h1 _24054). Qed.
Lemma lem1351888 (_24054 : real) (_24053 : real) : (term49 _24053 _24054) = ((real_add _24053 _24054) = (real_add _24054 _24053)).
Proof. exact (eq_refl (term49 _24053 _24054)). Qed.
Lemma lem1351890 (_24055 : real) (h1 : term10) : term50 _24055.
Proof. exact (@lem1351849 h1 _24055). Qed.
Lemma lem1351891 (_24055 : real) : (term50 _24055) = (term33 _24055).
Proof. exact (eq_refl (term50 _24055)). Qed.
Lemma lem1351892 (_24055 : real) (h1 : term10) : term33 _24055.
Proof. exact (EQ_MP (@lem1351891 _24055) (@lem1351890 _24055 h1)). Qed.
Lemma lem1351893 (_24055 : real) (_24056 : real) (h1 : term10) : term51 _24055 _24056.
Proof. exact (@lem1351892 _24055 h1 _24056). Qed.
Lemma lem1351894 (_24055 : real) (_24056 : real) : (term51 _24055 _24056) = (term31 _24055 _24056).
Proof. exact (eq_refl (term51 _24055 _24056)). Qed.
Lemma lem1351895 (_24055 : real) (_24056 : real) (h1 : term10) : term31 _24055 _24056.
Proof. exact (EQ_MP (@lem1351894 _24055 _24056) (@lem1351893 _24055 _24056 h1)). Qed.
Lemma lem1351896 (_24055 : real) (_24056 : real) (_24057 : real) (h1 : term10) : term52 _24055 _24056 _24057.
Proof. exact (@lem1351895 _24055 _24056 h1 _24057). Qed.
Lemma lem1351897 (_24055 : real) (_24056 : real) (_24057 : real) : (term52 _24055 _24056 _24057) = ((term28 _24055 _24056 _24057) = (term29 _24055 _24056 _24057)).
Proof. exact (eq_refl (term52 _24055 _24056 _24057)). Qed.
Lemma lem1351904 (n : real) (m : real) (h1 : term45 n m) : term45 n m.
Proof. exact (h1). Qed.
Lemma lem1351910 (m : real) (n : real) (p : real) (h1 : term46 m n p) : term46 m n p.
Proof. exact (h1). Qed.
Lemma lem1351916 (n : real) (m : real) (p : real) (h1 : term47 n m p) : term47 n m p.
Proof. exact (h1). Qed.
Lemma lem1351935 (_24044 : real) (_24043 : real) (h1 : term38) : (real_add _24043 _24044) = (real_add _24044 _24043).
Proof. exact (EQ_MP (@lem1351858 _24044 _24043) (@lem1351857 _24043 _24044 h1)). Qed.
Lemma lem1351936 (n : real) (m : real) (h1 : term38) : (real_add m n) = (real_add n m).
Proof. exact (@lem1351935 n m h1). Qed.
Lemma lem1351937 (n : real) (m : real) (h1 : term38) : term53 n m.
Proof. exact (fun h0 : term45 n m => @lem1351936 n m h1). Qed.
Lemma lem1351939 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1351940 (n : real) (m : real) : (term53 n m) = ((real_add m n) = (real_add n m)).
Proof. exact (@lem1351939 ((real_add m n) = (real_add n m))). Qed.
Lemma lem1351941 (n : real) (m : real) (h1 : term38) : (real_add m n) = (real_add n m).
Proof. exact (EQ_MP (@lem1351940 n m) (@lem1351937 n m h1)). Qed.
Lemma lem1351944 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1351946 (n : real) (m : real) : (term45 n m) = (term55 n m).
Proof. exact (@lem1351944 ((real_add m n) = (real_add n m))). Qed.
Lemma lem1351949 (n : real) (m : real) (h1 : term45 n m) : term55 n m.
Proof. exact (EQ_MP (@lem1351946 n m) (@lem1351904 n m h1)). Qed.
Lemma lem1351952 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (@lem1351949 n m h2 (@lem1351941 n m h1)). Qed.
Lemma lem1351953 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : term56.
Proof. exact (fun h0 : ~ False => @lem1351952 n m h1 h2). Qed.
Lemma lem1351955 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1351956 : term56 = False.
Proof. exact (@lem1351955 False). Qed.
Lemma lem1351957 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1351956) (@lem1351953 n m h1 h2)). Qed.
Lemma lem1351974 (x : real) (y : real) (z : real) : term57 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1351976 (_24050 : real) (_24051 : real) (_24052 : real) (h1 : term10) : (term28 _24050 _24051 _24052) = (term29 _24050 _24051 _24052).
Proof. exact (EQ_MP (@lem1351882 _24050 _24051 _24052) (@lem1351881 _24050 _24051 _24052 h1)). Qed.
Lemma lem1351977 (m : real) (n : real) (p : real) (h1 : term10) : (term28 m n p) = (term29 m n p).
Proof. exact (@lem1351976 m n p h1). Qed.
Lemma lem1351978 (m : real) (n : real) (p : real) (h1 : term10) : term58 m n p.
Proof. exact (fun h0 : term59 m n p => @lem1351977 m n p h1). Qed.
Lemma lem1351980 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1351981 (m : real) (n : real) (p : real) : (term58 m n p) = ((term28 m n p) = (term29 m n p)).
Proof. exact (@lem1351980 ((term28 m n p) = (term29 m n p))). Qed.
Lemma lem1351982 (m : real) (n : real) (p : real) (h1 : term10) : (term28 m n p) = (term29 m n p).
Proof. exact (EQ_MP (@lem1351981 m n p) (@lem1351978 m n p h1)). Qed.
Lemma lem1351984 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1351985 (m : real) (n : real) (p : real) : (term28 m n p) = (term28 m n p).
Proof. exact (@lem1351984 (term28 m n p)). Qed.
Lemma lem1351986 (m : real) (n : real) (p : real) : term60 m n p.
Proof. exact (fun h0 : term61 m n p => @lem1351985 m n p). Qed.
Lemma lem1351988 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1351989 (m : real) (n : real) (p : real) : (term60 m n p) = ((term28 m n p) = (term28 m n p)).
Proof. exact (@lem1351988 ((term28 m n p) = (term28 m n p))). Qed.
Lemma lem1351990 (m : real) (n : real) (p : real) : (term28 m n p) = (term28 m n p).
Proof. exact (EQ_MP (@lem1351989 m n p) (@lem1351986 m n p)). Qed.
Lemma lem1352008 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1352009 (y : real) (x : real) (z : real) : (term62 x y z) = (term63 y x z).
Proof. exact (@lem1352008 (y = z) (term64 x z)). Qed.
Lemma lem1352019 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1352020 (y : real) (x : real) (z : real) : (term57 x y z) = (term66 y x z).
Proof. exact (MK_COMB (@lem1352019 x y) (@lem1352009 y x z)). Qed.
Lemma lem1352024 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1352025 (y : real) (x : real) (z : real) : (term66 y x z) = (term68 y x z).
Proof. exact (@lem1352024 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem1352047 (y : real) (x : real) (z : real) : (term57 x y z) = (term68 y x z).
Proof. exact (TRANS (@lem1352020 y x z) (@lem1352025 y x z)). Qed.
Lemma lem1352048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1352049 (y : real) (x : real) (z : real) : (term69 x y z) = (term70 y x z).
Proof. exact (MK_COMB (@lem1352048) (@lem1352047 y x z)). Qed.
Lemma lem1352071 (y : real) (x : real) (z : real) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem1352072 (y : real) (x : real) (z : real) : ((term57 x y z) = (term68 y x z)) = ((term68 y x z) = (term68 y x z)).
Proof. exact (MK_COMB (@lem1352049 y x z) (@lem1352071 y x z)). Qed.
Lemma lem1352074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1352075 (x : Prop) : (x = x) = True.
Proof. exact (@lem1352074 Prop x). Qed.
Lemma lem1352076 (y : real) (x : real) (z : real) : ((term68 y x z) = (term68 y x z)) = True.
Proof. exact (@lem1352075 (term68 y x z)). Qed.
Lemma lem1352077 (y : real) (x : real) (z : real) : ((term57 x y z) = (term68 y x z)) = True.
Proof. exact (TRANS (@lem1352072 y x z) (@lem1352076 y x z)). Qed.
Lemma lem1352078 (y : real) (x : real) (z : real) : True = ((term57 x y z) = (term68 y x z)).
Proof. exact (SYM (@lem1352077 y x z)). Qed.
Lemma lem1352079 (y : real) (x : real) (z : real) : (term57 x y z) = (term68 y x z).
Proof. exact (EQ_MP (@lem1352078 y x z) (@lem0)). Qed.
Lemma lem1352080 (y : real) (x : real) (z : real) : term68 y x z.
Proof. exact (EQ_MP (@lem1352079 y x z) (@lem1351974 x y z)). Qed.
Lemma lem1352082 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1352083 (x : real) (y : real) (z : real) : (term68 y x z) = (term72 x y z).
Proof. exact (@lem1352082 (term73 y x z) (y = z)). Qed.
Lemma lem1352085 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1352086 (y : real) (x : real) (z : real) : (term76 y x z) = (term77 y x z).
Proof. exact (@lem1352085 (term64 x y) (term64 x z)). Qed.
Lemma lem1352088 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352089 (x : real) (y : real) : (term79 x y) = (x = y).
Proof. exact (@lem1352088 (x = y)). Qed.
Lemma lem1352090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1352091 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1352090) (@lem1352089 x y)). Qed.
Lemma lem1352093 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352094 (x : real) (z : real) : (term79 x z) = (x = z).
Proof. exact (@lem1352093 (x = z)). Qed.
Lemma lem1352095 (y : real) (x : real) (z : real) : (term77 y x z) = (term82 y x z).
Proof. exact (MK_COMB (@lem1352091 x y) (@lem1352094 x z)). Qed.
Lemma lem1352096 (y : real) (x : real) (z : real) : (term76 y x z) = (term82 y x z).
Proof. exact (TRANS (@lem1352086 y x z) (@lem1352095 y x z)). Qed.
Lemma lem1352097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1352098 (y : real) (x : real) (z : real) : (term83 y x z) = (term84 y x z).
Proof. exact (MK_COMB (@lem1352097) (@lem1352096 y x z)). Qed.
Lemma lem1352099 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1352100 (x : real) (y : real) (z : real) : (term72 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem1352098 y x z) (@lem1352099 y z)). Qed.
Lemma lem1352101 (x : real) (y : real) (z : real) : (term68 y x z) = (term85 x y z).
Proof. exact (TRANS (@lem1352083 x y z) (@lem1352100 x y z)). Qed.
Lemma lem1352103 (m : real) (n : real) (p : real) (h1 : term10) : term86 m n p.
Proof. exact (conj (@lem1351982 m n p h1) (@lem1351990 m n p)). Qed.
Lemma lem1352105 (x : real) (y : real) (z : real) : term85 x y z.
Proof. exact (EQ_MP (@lem1352101 x y z) (@lem1352080 y x z)). Qed.
Lemma lem1352106 (m : real) (n : real) (p : real) : term87 m n p.
Proof. exact (@lem1352105 (term28 m n p) (term29 m n p) (term28 m n p)). Qed.
Lemma lem1352109 (m : real) (n : real) (p : real) (h1 : term10) : (term29 m n p) = (term28 m n p).
Proof. exact (@lem1352106 m n p (@lem1352103 m n p h1)). Qed.
Lemma lem1352110 (m : real) (n : real) (p : real) (h1 : term10) : term88 m n p.
Proof. exact (fun h0 : term46 m n p => @lem1352109 m n p h1). Qed.
Lemma lem1352112 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352113 (m : real) (n : real) (p : real) : (term88 m n p) = ((term29 m n p) = (term28 m n p)).
Proof. exact (@lem1352112 ((term29 m n p) = (term28 m n p))). Qed.
Lemma lem1352114 (m : real) (n : real) (p : real) (h1 : term10) : (term29 m n p) = (term28 m n p).
Proof. exact (EQ_MP (@lem1352113 m n p) (@lem1352110 m n p h1)). Qed.
Lemma lem1352117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1352119 (m : real) (n : real) (p : real) : (term46 m n p) = (term89 m n p).
Proof. exact (@lem1352117 ((term29 m n p) = (term28 m n p))). Qed.
Lemma lem1352122 (m : real) (n : real) (p : real) (h1 : term46 m n p) : term89 m n p.
Proof. exact (EQ_MP (@lem1352119 m n p) (@lem1351910 m n p h1)). Qed.
Lemma lem1352125 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (@lem1352122 m n p h2 (@lem1352114 m n p h1)). Qed.
Lemma lem1352126 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : term56.
Proof. exact (fun h0 : ~ False => @lem1352125 m n p h1 h2). Qed.
Lemma lem1352128 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352129 : term56 = False.
Proof. exact (@lem1352128 False). Qed.
Lemma lem1352130 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem1352129) (@lem1352126 m n p h1 h2)). Qed.
Lemma lem1352131 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1352132 (_24066 : real) (_24068 : real) (h1 : _24066 = _24068) : _24066 = _24068.
Proof. exact (h1). Qed.
Lemma lem1352133 (_24067 : real) (_24069 : real) (h1 : _24067 = _24069) : _24067 = _24069.
Proof. exact (h1). Qed.
Lemma lem1352134 (_24066 : real) (_24068 : real) (h1 : _24066 = _24068) : (real_add _24066) = (real_add _24068).
Proof. exact (MK_COMB (@lem1352131) (@lem1352132 _24066 _24068 h1)). Qed.
Lemma lem1352135 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) (h1 : _24066 = _24068) (h2 : _24067 = _24069) : (real_add _24066 _24067) = (real_add _24068 _24069).
Proof. exact (MK_COMB (@lem1352134 _24066 _24068 h1) (@lem1352133 _24067 _24069 h2)). Qed.
Lemma lem1352136 (_24067 : real) (_24069 : real) (_24066 : real) (_24068 : real) (h1 : _24066 = _24068) : term90 _24066 _24067 _24068 _24069.
Proof. exact (fun h0 : _24067 = _24069 => @lem1352135 _24066 _24068 _24067 _24069 h1 h0). Qed.
Lemma lem1352138 (a : Prop) (b : Prop) : (a -> b) = (term91 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1352139 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : (term90 _24066 _24067 _24068 _24069) = (term92 _24066 _24067 _24068 _24069).
Proof. exact (@lem1352138 (_24067 = _24069) ((real_add _24066 _24067) = (real_add _24068 _24069))). Qed.
Lemma lem1352140 (_24067 : real) (_24069 : real) (_24066 : real) (_24068 : real) (h1 : _24066 = _24068) : term92 _24066 _24067 _24068 _24069.
Proof. exact (EQ_MP (@lem1352139 _24066 _24067 _24068 _24069) (@lem1352136 _24067 _24069 _24066 _24068 h1)). Qed.
Lemma lem1352141 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : term93 _24066 _24067 _24068 _24069.
Proof. exact (fun h0 : _24066 = _24068 => @lem1352140 _24067 _24069 _24066 _24068 h0). Qed.
Lemma lem1352143 (a : Prop) (b : Prop) : (a -> b) = (term91 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1352144 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : (term93 _24066 _24067 _24068 _24069) = (term94 _24066 _24067 _24068 _24069).
Proof. exact (@lem1352143 (_24066 = _24068) (term92 _24066 _24067 _24068 _24069)). Qed.
Lemma lem1352145 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : term94 _24066 _24067 _24068 _24069.
Proof. exact (EQ_MP (@lem1352144 _24066 _24067 _24068 _24069) (@lem1352141 _24066 _24067 _24068 _24069)). Qed.
Lemma lem1352147 (x : real) (y : real) (z : real) : term57 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1352149 (_24054 : real) (_24053 : real) (h1 : term38) : (real_add _24053 _24054) = (real_add _24054 _24053).
Proof. exact (EQ_MP (@lem1351888 _24054 _24053) (@lem1351887 _24053 _24054 h1)). Qed.
Lemma lem1352150 (m : real) (n : real) (p : real) (h1 : term38) : (term29 n p m) = (term28 m n p).
Proof. exact (@lem1352149 m (real_add n p) h1). Qed.
Lemma lem1352151 (m : real) (n : real) (p : real) (h1 : term38) : term95 m n p.
Proof. exact (fun h0 : term96 m n p => @lem1352150 m n p h1). Qed.
Lemma lem1352153 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352154 (m : real) (n : real) (p : real) : (term95 m n p) = ((term29 n p m) = (term28 m n p)).
Proof. exact (@lem1352153 ((term29 n p m) = (term28 m n p))). Qed.
Lemma lem1352155 (m : real) (n : real) (p : real) (h1 : term38) : (term29 n p m) = (term28 m n p).
Proof. exact (EQ_MP (@lem1352154 m n p) (@lem1352151 m n p h1)). Qed.
Lemma lem1352157 (_24055 : real) (_24056 : real) (_24057 : real) (h1 : term10) : (term28 _24055 _24056 _24057) = (term29 _24055 _24056 _24057).
Proof. exact (EQ_MP (@lem1351897 _24055 _24056 _24057) (@lem1351896 _24055 _24056 _24057 h1)). Qed.
Lemma lem1352158 (n : real) (p : real) (m : real) (h1 : term10) : (term28 n p m) = (term29 n p m).
Proof. exact (@lem1352157 n p m h1). Qed.
Lemma lem1352159 (n : real) (p : real) (m : real) (h1 : term10) : term58 n p m.
Proof. exact (fun h0 : term59 n p m => @lem1352158 n p m h1). Qed.
Lemma lem1352161 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352162 (n : real) (p : real) (m : real) : (term58 n p m) = ((term28 n p m) = (term29 n p m)).
Proof. exact (@lem1352161 ((term28 n p m) = (term29 n p m))). Qed.
Lemma lem1352163 (n : real) (p : real) (m : real) (h1 : term10) : (term28 n p m) = (term29 n p m).
Proof. exact (EQ_MP (@lem1352162 n p m) (@lem1352159 n p m h1)). Qed.
Lemma lem1352165 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1352166 (n : real) : n = n.
Proof. exact (@lem1352165 n). Qed.
Lemma lem1352167 (n : real) : term97 n.
Proof. exact (fun h0 : term98 n => @lem1352166 n). Qed.
Lemma lem1352169 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352170 (n : real) : (term97 n) = (n = n).
Proof. exact (@lem1352169 (n = n)). Qed.
Lemma lem1352171 (n : real) : n = n.
Proof. exact (EQ_MP (@lem1352170 n) (@lem1352167 n)). Qed.
Lemma lem1352173 (_24054 : real) (_24053 : real) (h1 : term38) : (real_add _24053 _24054) = (real_add _24054 _24053).
Proof. exact (EQ_MP (@lem1351888 _24054 _24053) (@lem1351887 _24053 _24054 h1)). Qed.
Lemma lem1352174 (m : real) (p : real) (h1 : term38) : (real_add p m) = (real_add m p).
Proof. exact (@lem1352173 m p h1). Qed.
Lemma lem1352175 (m : real) (p : real) (h1 : term38) : term53 m p.
Proof. exact (fun h0 : term45 m p => @lem1352174 m p h1). Qed.
Lemma lem1352177 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352178 (m : real) (p : real) : (term53 m p) = ((real_add p m) = (real_add m p)).
Proof. exact (@lem1352177 ((real_add p m) = (real_add m p))). Qed.
Lemma lem1352179 (m : real) (p : real) (h1 : term38) : (real_add p m) = (real_add m p).
Proof. exact (EQ_MP (@lem1352178 m p) (@lem1352175 m p h1)). Qed.
Lemma lem1352197 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1352198 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term92 _24066 _24067 _24068 _24069) = (term99 _24066 _24068 _24067 _24069).
Proof. exact (@lem1352197 ((real_add _24066 _24067) = (real_add _24068 _24069)) (term64 _24067 _24069)). Qed.
Lemma lem1352208 (_24066 : real) (_24068 : real) : (term65 _24066 _24068) = (term65 _24066 _24068).
Proof. exact (eq_refl (term65 _24066 _24068)). Qed.
Lemma lem1352209 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term94 _24066 _24067 _24068 _24069) = (term100 _24066 _24068 _24067 _24069).
Proof. exact (MK_COMB (@lem1352208 _24066 _24068) (@lem1352198 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352213 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1352214 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term100 _24066 _24068 _24067 _24069) = (term101 _24066 _24068 _24067 _24069).
Proof. exact (@lem1352213 ((real_add _24066 _24067) = (real_add _24068 _24069)) (term64 _24066 _24068) (term64 _24067 _24069)). Qed.
Lemma lem1352236 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term94 _24066 _24067 _24068 _24069) = (term101 _24066 _24068 _24067 _24069).
Proof. exact (TRANS (@lem1352209 _24066 _24068 _24067 _24069) (@lem1352214 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1352238 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term102 _24066 _24067 _24068 _24069) = (term103 _24066 _24068 _24067 _24069).
Proof. exact (MK_COMB (@lem1352237) (@lem1352236 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352260 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term101 _24066 _24068 _24067 _24069) = (term101 _24066 _24068 _24067 _24069).
Proof. exact (eq_refl (term101 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352261 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : ((term94 _24066 _24067 _24068 _24069) = (term101 _24066 _24068 _24067 _24069)) = ((term101 _24066 _24068 _24067 _24069) = (term101 _24066 _24068 _24067 _24069)).
Proof. exact (MK_COMB (@lem1352238 _24066 _24068 _24067 _24069) (@lem1352260 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352263 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1352264 (x : Prop) : (x = x) = True.
Proof. exact (@lem1352263 Prop x). Qed.
Lemma lem1352265 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : ((term101 _24066 _24068 _24067 _24069) = (term101 _24066 _24068 _24067 _24069)) = True.
Proof. exact (@lem1352264 (term101 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352266 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : ((term94 _24066 _24067 _24068 _24069) = (term101 _24066 _24068 _24067 _24069)) = True.
Proof. exact (TRANS (@lem1352261 _24066 _24068 _24067 _24069) (@lem1352265 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352267 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : True = ((term94 _24066 _24067 _24068 _24069) = (term101 _24066 _24068 _24067 _24069)).
Proof. exact (SYM (@lem1352266 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352268 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term94 _24066 _24067 _24068 _24069) = (term101 _24066 _24068 _24067 _24069).
Proof. exact (EQ_MP (@lem1352267 _24066 _24068 _24067 _24069) (@lem0)). Qed.
Lemma lem1352269 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : term101 _24066 _24068 _24067 _24069.
Proof. exact (EQ_MP (@lem1352268 _24066 _24068 _24067 _24069) (@lem1352145 _24066 _24067 _24068 _24069)). Qed.
Lemma lem1352271 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1352272 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : (term101 _24066 _24068 _24067 _24069) = (term104 _24066 _24067 _24068 _24069).
Proof. exact (@lem1352271 (term105 _24066 _24068 _24067 _24069) ((real_add _24066 _24067) = (real_add _24068 _24069))). Qed.
Lemma lem1352274 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1352275 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term106 _24066 _24068 _24067 _24069) = (term107 _24066 _24068 _24067 _24069).
Proof. exact (@lem1352274 (term64 _24066 _24068) (term64 _24067 _24069)). Qed.
Lemma lem1352277 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352278 (_24066 : real) (_24068 : real) : (term79 _24066 _24068) = (_24066 = _24068).
Proof. exact (@lem1352277 (_24066 = _24068)). Qed.
Lemma lem1352279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1352280 (_24066 : real) (_24068 : real) : (term80 _24066 _24068) = (term81 _24066 _24068).
Proof. exact (MK_COMB (@lem1352279) (@lem1352278 _24066 _24068)). Qed.
Lemma lem1352282 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352283 (_24067 : real) (_24069 : real) : (term79 _24067 _24069) = (_24067 = _24069).
Proof. exact (@lem1352282 (_24067 = _24069)). Qed.
Lemma lem1352284 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term107 _24066 _24068 _24067 _24069) = (term108 _24066 _24068 _24067 _24069).
Proof. exact (MK_COMB (@lem1352280 _24066 _24068) (@lem1352283 _24067 _24069)). Qed.
Lemma lem1352285 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term106 _24066 _24068 _24067 _24069) = (term108 _24066 _24068 _24067 _24069).
Proof. exact (TRANS (@lem1352275 _24066 _24068 _24067 _24069) (@lem1352284 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1352287 (_24066 : real) (_24068 : real) (_24067 : real) (_24069 : real) : (term109 _24066 _24068 _24067 _24069) = (term110 _24066 _24068 _24067 _24069).
Proof. exact (MK_COMB (@lem1352286) (@lem1352285 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352288 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : ((real_add _24066 _24067) = (real_add _24068 _24069)) = ((real_add _24066 _24067) = (real_add _24068 _24069)).
Proof. exact (eq_refl ((real_add _24066 _24067) = (real_add _24068 _24069))). Qed.
Lemma lem1352289 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : (term104 _24066 _24067 _24068 _24069) = (term111 _24066 _24067 _24068 _24069).
Proof. exact (MK_COMB (@lem1352287 _24066 _24068 _24067 _24069) (@lem1352288 _24066 _24067 _24068 _24069)). Qed.
Lemma lem1352290 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : (term101 _24066 _24068 _24067 _24069) = (term111 _24066 _24067 _24068 _24069).
Proof. exact (TRANS (@lem1352272 _24066 _24067 _24068 _24069) (@lem1352289 _24066 _24067 _24068 _24069)). Qed.
Lemma lem1352292 (n : real) (m : real) (p : real) (h1 : term38) : term112 n m p.
Proof. exact (conj (@lem1352171 n) (@lem1352179 m p h1)). Qed.
Lemma lem1352294 (_24066 : real) (_24067 : real) (_24068 : real) (_24069 : real) : term111 _24066 _24067 _24068 _24069.
Proof. exact (EQ_MP (@lem1352290 _24066 _24067 _24068 _24069) (@lem1352269 _24066 _24068 _24067 _24069)). Qed.
Lemma lem1352295 (n : real) (m : real) (p : real) : term113 n m p.
Proof. exact (@lem1352294 n (real_add p m) n (real_add m p)). Qed.
Lemma lem1352298 (n : real) (m : real) (p : real) (h1 : term38) : (term28 n p m) = (term28 n m p).
Proof. exact (@lem1352295 n m p (@lem1352292 n m p h1)). Qed.
Lemma lem1352299 (n : real) (m : real) (p : real) (h1 : term38) : term114 n m p.
Proof. exact (fun h0 : term115 n m p => @lem1352298 n m p h1). Qed.
Lemma lem1352301 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352302 (n : real) (m : real) (p : real) : (term114 n m p) = ((term28 n p m) = (term28 n m p)).
Proof. exact (@lem1352301 ((term28 n p m) = (term28 n m p))). Qed.
Lemma lem1352303 (n : real) (m : real) (p : real) (h1 : term38) : (term28 n p m) = (term28 n m p).
Proof. exact (EQ_MP (@lem1352302 n m p) (@lem1352299 n m p h1)). Qed.
Lemma lem1352321 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1352322 (y : real) (x : real) (z : real) : (term62 x y z) = (term63 y x z).
Proof. exact (@lem1352321 (y = z) (term64 x z)). Qed.
Lemma lem1352332 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1352333 (y : real) (x : real) (z : real) : (term57 x y z) = (term66 y x z).
Proof. exact (MK_COMB (@lem1352332 x y) (@lem1352322 y x z)). Qed.
Lemma lem1352337 (q : Prop) (p : Prop) (r : Prop) : (term67 p q r) = (term67 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1352338 (y : real) (x : real) (z : real) : (term66 y x z) = (term68 y x z).
Proof. exact (@lem1352337 (y = z) (term64 x y) (term64 x z)). Qed.
Lemma lem1352360 (y : real) (x : real) (z : real) : (term57 x y z) = (term68 y x z).
Proof. exact (TRANS (@lem1352333 y x z) (@lem1352338 y x z)). Qed.
Lemma lem1352361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1352362 (y : real) (x : real) (z : real) : (term69 x y z) = (term70 y x z).
Proof. exact (MK_COMB (@lem1352361) (@lem1352360 y x z)). Qed.
Lemma lem1352384 (y : real) (x : real) (z : real) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem1352385 (y : real) (x : real) (z : real) : ((term57 x y z) = (term68 y x z)) = ((term68 y x z) = (term68 y x z)).
Proof. exact (MK_COMB (@lem1352362 y x z) (@lem1352384 y x z)). Qed.
Lemma lem1352387 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1352388 (x : Prop) : (x = x) = True.
Proof. exact (@lem1352387 Prop x). Qed.
Lemma lem1352389 (y : real) (x : real) (z : real) : ((term68 y x z) = (term68 y x z)) = True.
Proof. exact (@lem1352388 (term68 y x z)). Qed.
Lemma lem1352390 (y : real) (x : real) (z : real) : ((term57 x y z) = (term68 y x z)) = True.
Proof. exact (TRANS (@lem1352385 y x z) (@lem1352389 y x z)). Qed.
Lemma lem1352391 (y : real) (x : real) (z : real) : True = ((term57 x y z) = (term68 y x z)).
Proof. exact (SYM (@lem1352390 y x z)). Qed.
Lemma lem1352392 (y : real) (x : real) (z : real) : (term57 x y z) = (term68 y x z).
Proof. exact (EQ_MP (@lem1352391 y x z) (@lem0)). Qed.
Lemma lem1352393 (y : real) (x : real) (z : real) : term68 y x z.
Proof. exact (EQ_MP (@lem1352392 y x z) (@lem1352147 x y z)). Qed.
Lemma lem1352395 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1352396 (x : real) (y : real) (z : real) : (term68 y x z) = (term72 x y z).
Proof. exact (@lem1352395 (term73 y x z) (y = z)). Qed.
Lemma lem1352398 (a : Prop) (b : Prop) : (term74 a b) = (term75 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1352399 (y : real) (x : real) (z : real) : (term76 y x z) = (term77 y x z).
Proof. exact (@lem1352398 (term64 x y) (term64 x z)). Qed.
Lemma lem1352401 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352402 (x : real) (y : real) : (term79 x y) = (x = y).
Proof. exact (@lem1352401 (x = y)). Qed.
Lemma lem1352403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1352404 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1352403) (@lem1352402 x y)). Qed.
Lemma lem1352406 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352407 (x : real) (z : real) : (term79 x z) = (x = z).
Proof. exact (@lem1352406 (x = z)). Qed.
Lemma lem1352408 (y : real) (x : real) (z : real) : (term77 y x z) = (term82 y x z).
Proof. exact (MK_COMB (@lem1352404 x y) (@lem1352407 x z)). Qed.
Lemma lem1352409 (y : real) (x : real) (z : real) : (term76 y x z) = (term82 y x z).
Proof. exact (TRANS (@lem1352399 y x z) (@lem1352408 y x z)). Qed.
Lemma lem1352410 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1352411 (y : real) (x : real) (z : real) : (term83 y x z) = (term84 y x z).
Proof. exact (MK_COMB (@lem1352410) (@lem1352409 y x z)). Qed.
Lemma lem1352412 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1352413 (x : real) (y : real) (z : real) : (term72 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem1352411 y x z) (@lem1352412 y z)). Qed.
Lemma lem1352414 (x : real) (y : real) (z : real) : (term68 y x z) = (term85 x y z).
Proof. exact (TRANS (@lem1352396 x y z) (@lem1352413 x y z)). Qed.
Lemma lem1352416 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : term116 n m p.
Proof. exact (conj (@lem1352163 n p m h1) (@lem1352303 n m p h2)). Qed.
Lemma lem1352418 (x : real) (y : real) (z : real) : term85 x y z.
Proof. exact (EQ_MP (@lem1352414 x y z) (@lem1352393 y x z)). Qed.
Lemma lem1352419 (n : real) (m : real) (p : real) : term117 n m p.
Proof. exact (@lem1352418 (term28 n p m) (term29 n p m) (term28 n m p)). Qed.
Lemma lem1352422 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : (term29 n p m) = (term28 n m p).
Proof. exact (@lem1352419 n m p (@lem1352416 n m p h1 h2)). Qed.
Lemma lem1352423 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : term118 n m p.
Proof. exact (fun h0 : term119 n m p => @lem1352422 n m p h1 h2). Qed.
Lemma lem1352425 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352426 (n : real) (m : real) (p : real) : (term118 n m p) = ((term29 n p m) = (term28 n m p)).
Proof. exact (@lem1352425 ((term29 n p m) = (term28 n m p))). Qed.
Lemma lem1352427 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : (term29 n p m) = (term28 n m p).
Proof. exact (EQ_MP (@lem1352426 n m p) (@lem1352423 n m p h1 h2)). Qed.
Lemma lem1352428 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : term120 n m p.
Proof. exact (conj (@lem1352155 m n p h2) (@lem1352427 n m p h1 h2)). Qed.
Lemma lem1352430 (x : real) (y : real) (z : real) : term85 x y z.
Proof. exact (EQ_MP (@lem1352414 x y z) (@lem1352393 y x z)). Qed.
Lemma lem1352431 (n : real) (m : real) (p : real) : term121 n m p.
Proof. exact (@lem1352430 (term29 n p m) (term28 m n p) (term28 n m p)). Qed.
Lemma lem1352434 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : (term28 m n p) = (term28 n m p).
Proof. exact (@lem1352431 n m p (@lem1352428 n m p h1 h2)). Qed.
Lemma lem1352435 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : term122 n m p.
Proof. exact (fun h0 : term47 n m p => @lem1352434 n m p h1 h2). Qed.
Lemma lem1352437 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352438 (n : real) (m : real) (p : real) : (term122 n m p) = ((term28 m n p) = (term28 n m p)).
Proof. exact (@lem1352437 ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem1352439 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) : (term28 m n p) = (term28 n m p).
Proof. exact (EQ_MP (@lem1352438 n m p) (@lem1352435 n m p h1 h2)). Qed.
Lemma lem1352442 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1352444 (n : real) (m : real) (p : real) : (term47 n m p) = (term123 n m p).
Proof. exact (@lem1352442 ((term28 m n p) = (term28 n m p))). Qed.
Lemma lem1352447 (n : real) (m : real) (p : real) (h1 : term47 n m p) : term123 n m p.
Proof. exact (EQ_MP (@lem1352444 n m p) (@lem1351916 n m p h1)). Qed.
Lemma lem1352450 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (@lem1352447 n m p h3 (@lem1352439 n m p h1 h2)). Qed.
Lemma lem1352451 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term56.
Proof. exact (fun h0 : ~ False => @lem1352450 n m p h1 h2 h3). Qed.
Lemma lem1352453 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352454 : term56 = False.
Proof. exact (@lem1352453 False). Qed.
Lemma lem1352455 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem1352454) (@lem1352451 n m p h1 h2 h3)). Qed.
Lemma lem1352456 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem1352455 n m p h1 h2 h3) (fun h4 : False => @lem1351916 n m p h3)). Qed.
Lemma lem1352457 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem1352456 n m p h1 h2 h3) (@lem1351916 n m p h3)). Qed.
Lemma lem1352458 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem1352130 m n p h1 h2) (fun h3 : False => @lem1351910 m n p h2)). Qed.
Lemma lem1352459 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem1352458 m n p h1 h2) (@lem1351910 m n p h2)). Qed.
Lemma lem1352460 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem1351957 n m h1 h2) (fun h3 : False => @lem1351904 n m h2)). Qed.
Lemma lem1352461 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1352460 n m h1 h2) (@lem1351904 n m h2)). Qed.
Lemma lem1352462 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem1352457 n m p h1 h2 h3) (fun h4 : False => @lem1351853 n m p h3)). Qed.
Lemma lem1352463 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem1352462 n m p h1 h2 h3) (@lem1351853 n m p h3)). Qed.
Lemma lem1352464 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem1352459 m n p h1 h2) (fun h3 : False => @lem1351826 m n p h2)). Qed.
Lemma lem1352465 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem1352464 m n p h1 h2) (@lem1351826 m n p h2)). Qed.
Lemma lem1352466 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem1352461 n m h1 h2) (fun h3 : False => @lem1351799 n m h2)). Qed.
Lemma lem1352467 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1352466 n m h1 h2) (@lem1351799 n m h2)). Qed.
Lemma lem1352468 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : (term47 n m p) = False.
Proof. exact (prop_ext (fun h4 : term47 n m p => @lem1352463 n m p h1 h2 h3) (fun h4 : False => @lem1351853 n m p h3)). Qed.
Lemma lem1352469 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem1352468 n m p h1 h2 h3) (@lem1351853 n m p h3)). Qed.
Lemma lem1352470 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1352469 n m p h1 h2 h3) (fun h4 : False => @lem1351849 h1)). Qed.
Lemma lem1352471 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem1352470 n m p h1 h2 h3) (@lem1351849 h1)). Qed.
Lemma lem1352472 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem1352471 n m p h1 h2 h3) (fun h4 : False => @lem1351836 h2)). Qed.
Lemma lem1352473 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term47 n m p) : False.
Proof. exact (EQ_MP (@lem1352472 n m p h1 h2 h3) (@lem1351836 h2)). Qed.
Lemma lem1352474 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : (term46 m n p) = False.
Proof. exact (prop_ext (fun h3 : term46 m n p => @lem1352465 m n p h1 h2) (fun h3 : False => @lem1351826 m n p h2)). Qed.
Lemma lem1352475 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem1352474 m n p h1 h2) (@lem1351826 m n p h2)). Qed.
Lemma lem1352476 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1352475 m n p h1 h2) (fun h3 : False => @lem1351822 h1)). Qed.
Lemma lem1352477 (m : real) (n : real) (p : real) (h1 : term10) (h2 : term46 m n p) : False.
Proof. exact (EQ_MP (@lem1352476 m n p h1 h2) (@lem1351822 h1)). Qed.
Lemma lem1352478 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : (term45 n m) = False.
Proof. exact (prop_ext (fun h3 : term45 n m => @lem1352467 n m h1 h2) (fun h3 : False => @lem1351799 n m h2)). Qed.
Lemma lem1352479 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1352478 n m h1 h2) (@lem1351799 n m h2)). Qed.
Lemma lem1352480 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : term38 = False.
Proof. exact (prop_ext (fun h3 : term38 => @lem1352479 n m h1 h2) (fun h3 : False => @lem1351782 h1)). Qed.
Lemma lem1352481 (n : real) (m : real) (h1 : term38) (h2 : term45 n m) : False.
Proof. exact (EQ_MP (@lem1352480 n m h1 h2) (@lem1351782 h1)). Qed.
Lemma lem1352482 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term40 n m p) : False.
Proof. exact (or_elim (@lem1351770 n m p h3) (fun h0 : term46 m n p => @lem1352477 m n p h1 h0) (fun h0 : term47 n m p => @lem1352473 n m p h1 h2 h0)). Qed.
Lemma lem1352483 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (or_elim (@lem1351717 n m p h3) (fun h0 : term45 n m => @lem1352481 n m h2 h0) (fun h0 : term40 n m p => @lem1352482 n m p h1 h2 h0)). Qed.
Lemma lem1352484 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1352483 n m p h1 h2 h3) (fun h4 : False => @lem1351768 h1)). Qed.
Lemma lem1352485 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem1352484 n m p h1 h2 h3) (@lem1351768 h1)). Qed.
Lemma lem1352486 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem1352485 n m p h1 h2 h3) (fun h4 : False => @lem1351737 h2)). Qed.
Lemma lem1352487 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem1352486 n m p h1 h2 h3) (@lem1351737 h2)). Qed.
Lemma lem1352488 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1352487 n m p h1 h2 h3) (fun h4 : False => @lem1351649 h1)). Qed.
Lemma lem1352489 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem1352488 n m p h1 h2 h3) (@lem1351649 h1)). Qed.
Lemma lem1352490 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : term38 = False.
Proof. exact (prop_ext (fun h4 : term38 => @lem1352489 n m p h1 h2 h3) (fun h4 : False => @lem1351622 h2)). Qed.
Lemma lem1352491 (n : real) (m : real) (p : real) (h1 : term10) (h2 : term38) (h3 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem1352490 n m p h1 h2 h3) (@lem1351622 h2)). Qed.
Lemma lem1352492 (n : real) (m : real) (p : real) (h1 : term38) (h2 : term3 n m p) : term8.
Proof. exact (fun h0 : term10 => @lem1352491 n m p h0 h1 h2). Qed.
Lemma lem1352493 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1352494 (n : real) (m : real) (p : real) (h1 : term38) (h2 : term3 n m p) : term9.
Proof. exact (EQ_MP (@lem1352493) (@lem1352492 n m p h1 h2)). Qed.
Lemma lem1352495 (n : real) (m : real) (p : real) (h1 : term3 n m p) : term13.
Proof. exact (fun h0 : term38 => @lem1352494 n m p h0 h1). Qed.
Lemma lem1352496 (n : real) (m : real) (p : real) : term15 n m p.
Proof. exact (fun h0 : term3 n m p => @lem1352495 n m p h0). Qed.
Lemma lem1352501 (m : real) (p : real) : term19 m p.
Proof. exact (fun n : real => @lem1352496 n m p). Qed.
Lemma lem1352506 (p : real) : term23 p.
Proof. exact (fun m : real => @lem1352501 m p). Qed.
Lemma lem1352511 : term27.
Proof. exact (fun p : real => @lem1352506 p). Qed.
Lemma lem1352512 : term26.
Proof. exact (EQ_MP (@lem1351581) (@lem1352511)). Qed.
Lemma lem1352513 (p : real) : term124 p.
Proof. exact (@lem1352512 p). Qed.
Lemma lem1352514 (p : real) : (term124 p) = (term22 p).
Proof. exact (eq_refl (term124 p)). Qed.
Lemma lem1352515 (p : real) : term22 p.
Proof. exact (EQ_MP (@lem1352514 p) (@lem1352513 p)). Qed.
Lemma lem1352516 (p : real) (m : real) : term125 p m.
Proof. exact (@lem1352515 p m). Qed.
Lemma lem1352517 (m : real) (p : real) : (term125 p m) = (term18 m p).
Proof. exact (eq_refl (term125 p m)). Qed.
Lemma lem1352518 (m : real) (p : real) : term18 m p.
Proof. exact (EQ_MP (@lem1352517 m p) (@lem1352516 p m)). Qed.
Lemma lem1352519 (m : real) (p : real) (n : real) : term126 m p n.
Proof. exact (@lem1352518 m p n). Qed.
Lemma lem1352520 (n : real) (m : real) (p : real) : (term126 m p n) = (term4 n m p).
Proof. exact (eq_refl (term126 m p n)). Qed.
Lemma lem1352521 (n : real) (m : real) (p : real) : term4 n m p.
Proof. exact (EQ_MP (@lem1352520 n m p) (@lem1352519 m p n)). Qed.
Lemma lem1352523 (n : real) (m : real) (p : real) : term4 n m p.
Proof. exact (@lem1351400 n m p (@lem1352521 n m p)). Qed.
Lemma lem1352524 (n : real) (m : real) (p : real) (h1 : term3 n m p) : term12.
Proof. exact (@lem1352523 n m p (@lem1351385 n m p h1)). Qed.
Lemma lem1352525 (n : real) (m : real) (p : real) (h1 : term3 n m p) : term8.
Proof. exact (@lem1352524 n m p h1 (@lem1338238)). Qed.
Lemma lem1352526 (n : real) (m : real) (p : real) (h1 : term3 n m p) : False.
Proof. exact (@lem1352525 n m p h1 (@lem1338438)). Qed.
Lemma lem1352527 (n : real) (m : real) (p : real) (h1 : term3 n m p) : (term3 n m p) = False.
Proof. exact (prop_ext (fun h2 : term3 n m p => @lem1352526 n m p h1) (fun h2 : False => @lem1351385 n m p h1)). Qed.
Lemma lem1352528 (n : real) (m : real) (p : real) (h1 : term3 n m p) : False.
Proof. exact (EQ_MP (@lem1352527 n m p h1) (@lem1351385 n m p h1)). Qed.
Lemma lem1352529 (n : real) (m : real) (p : real) : term2 n m p.
Proof. exact (fun h0 : term3 n m p => @lem1352528 n m p h0). Qed.
Lemma lem1352530 (n : real) (m : real) (p : real) : term1 n m p.
Proof. exact (EQ_MP (@lem1351384 n m p) (@lem1352529 n m p)). Qed.
