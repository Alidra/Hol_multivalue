Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_POS_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LT_LE_spec.
Require Import SQRT_EQ_0_spec.
Require Import SQRT_POS_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem1956365 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1956366 : term1 = term2.
Proof. exact (@lem1956365 term1). Qed.
Lemma lem1956367 : term2 = term1.
Proof. exact (SYM (@lem1956366)). Qed.
Lemma lem1956368 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1956371 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1956372 : term5.
Proof. exact (fun h0 : term4 => @lem1956371 h0). Qed.
Lemma lem1956373 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1956374 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1956375 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1956373 h2 (@lem1956374 h1)). Qed.
Lemma lem1956376 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1956375 h1 h0). Qed.
Lemma lem1956377 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1956378 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1956376 h1 (@lem1956377 h2)). Qed.
Lemma lem1956379 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1956378 h0 h1). Qed.
Lemma lem1956380 : term7.
Proof. exact (fun h0 : term5 => @lem1956379 h0). Qed.
Lemma lem1956383 : term5.
Proof. exact (@lem1956380 (@lem1956372)). Qed.
Lemma lem1956407 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1956408 : term8 = term9.
Proof. exact (@lem1956407 term10). Qed.
Lemma lem1956419 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1956420 : term12 = term13.
Proof. exact (MK_COMB (@lem1956419) (@lem1956408)). Qed.
Lemma lem1956423 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1956424 : term15 = term16.
Proof. exact (MK_COMB (@lem1956423) (@lem1956420)). Qed.
Lemma lem1956427 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1956434 : term4 = term18.
Proof. exact (MK_COMB (@lem1956427) (@lem1956424)). Qed.
Lemma lem1956445 (x : real) (y : real) : ((real_lt x y) = (term19 x y)) = ((real_lt x y) = (term19 x y)).
Proof. exact (eq_refl ((real_lt x y) = (term19 x y))). Qed.
Lemma lem1956446 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1956445 x y)). Qed.
Lemma lem1956447 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956448 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1956447) (@lem1956446 x)). Qed.
Lemma lem1956449 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1956448 x)). Qed.
Lemma lem1956450 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956451 : term10 = term10.
Proof. exact (MK_COMB (@lem1956450) (@lem1956449)). Qed.
Lemma lem1956452 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1956453 : term9 = term9.
Proof. exact (MK_COMB (@lem1956452) (@lem1956451)). Qed.
Lemma lem1956458 (x : real) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1956459 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1956458 x)). Qed.
Lemma lem1956460 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956461 : term25 = term25.
Proof. exact (MK_COMB (@lem1956460) (@lem1956459)). Qed.
Lemma lem1956462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1956463 : term11 = term11.
Proof. exact (MK_COMB (@lem1956462) (@lem1956461)). Qed.
Lemma lem1956464 : term13 = term13.
Proof. exact (MK_COMB (@lem1956463) (@lem1956453)). Qed.
Lemma lem1956469 (x : real) : (((sqrt x) = term26) = (x = term26)) = (((sqrt x) = term26) = (x = term26)).
Proof. exact (eq_refl (((sqrt x) = term26) = (x = term26))). Qed.
Lemma lem1956470 : term27 = term27.
Proof. exact (fun_ext (fun x : real => @lem1956469 x)). Qed.
Lemma lem1956471 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956472 : term28 = term28.
Proof. exact (MK_COMB (@lem1956471) (@lem1956470)). Qed.
Lemma lem1956473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1956474 : term14 = term14.
Proof. exact (MK_COMB (@lem1956473) (@lem1956472)). Qed.
Lemma lem1956475 : term16 = term16.
Proof. exact (MK_COMB (@lem1956474) (@lem1956464)). Qed.
Lemma lem1956480 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1956481 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1956480 x)). Qed.
Lemma lem1956482 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956483 : term1 = term1.
Proof. exact (MK_COMB (@lem1956482) (@lem1956481)). Qed.
Lemma lem1956484 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1956485 : term3 = term3.
Proof. exact (MK_COMB (@lem1956484) (@lem1956483)). Qed.
Lemma lem1956486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1956487 : term17 = term17.
Proof. exact (MK_COMB (@lem1956486) (@lem1956485)). Qed.
Lemma lem1956488 : term18 = term18.
Proof. exact (MK_COMB (@lem1956487) (@lem1956475)). Qed.
Lemma lem1956533 : term4 = term18.
Proof. exact (TRANS (@lem1956434) (@lem1956488)). Qed.
Lemma lem1956534 : term18 = term4.
Proof. exact (SYM (@lem1956533)). Qed.
Lemma lem1956535 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1956536 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1956537 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem1956538 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1956545 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem17362 (term33 x) (term34 x)). Qed.
Lemma lem1956546 (P : real -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1956547 : term3 = term37.
Proof. exact (@lem1956546 term30). Qed.
Lemma lem1956548 (x : real) : (term38 x) = (term29 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1956549 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1956550 (x : real) : (term39 x) = (term31 x).
Proof. exact (MK_COMB (@lem1956549) (@lem1956548 x)). Qed.
Lemma lem1956551 (x : real) : (term39 x) = (term32 x).
Proof. exact (TRANS (@lem1956550 x) (@lem1956545 x)). Qed.
Lemma lem1956552 : term40 = term41.
Proof. exact (fun_ext (fun x : real => @lem1956551 x)). Qed.
Lemma lem1956553 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1956554 : term37 = term42.
Proof. exact (MK_COMB (@lem1956553) (@lem1956552)). Qed.
Lemma lem1956607 : term3 = term42.
Proof. exact (TRANS (@lem1956547) (@lem1956554)). Qed.
Lemma lem1956608 (h1 : term3) : term42.
Proof. exact (EQ_MP (@lem1956607) (@lem1956535 h1)). Qed.
Lemma lem1956623 (x : real) : (((sqrt x) = term26) = (x = term26)) = (term43 x).
Proof. exact (@lem17784 ((sqrt x) = term26) (x = term26)). Qed.
Lemma lem1956624 : term27 = term44.
Proof. exact (fun_ext (fun x : real => @lem1956623 x)). Qed.
Lemma lem1956625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956626 : term28 = term45.
Proof. exact (MK_COMB (@lem1956625) (@lem1956624)). Qed.
Lemma lem1956628 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1956629 (P : real -> Prop) (Q : real -> Prop) : (term48 P Q) = (term49 P Q).
Proof. exact (@lem1956628 real P Q). Qed.
Lemma lem1956630 : term50 = term51.
Proof. exact (@lem1956629 term52 term53). Qed.
Lemma lem1956631 (x : real) : (term54 x) = (term55 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1956632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956633 (x : real) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem1956632) (@lem1956631 x)). Qed.
Lemma lem1956634 (x : real) : (term58 x) = (term59 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1956635 (x : real) : (term60 x) = (term43 x).
Proof. exact (MK_COMB (@lem1956633 x) (@lem1956634 x)). Qed.
Lemma lem1956636 : term61 = term44.
Proof. exact (fun_ext (fun x : real => @lem1956635 x)). Qed.
Lemma lem1956637 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956638 : term50 = term45.
Proof. exact (MK_COMB (@lem1956637) (@lem1956636)). Qed.
Lemma lem1956639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1956640 : term62 = term63.
Proof. exact (MK_COMB (@lem1956639) (@lem1956638)). Qed.
Lemma lem1956641 (x : real) : (term54 x) = (term55 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1956642 : term64 = term52.
Proof. exact (fun_ext (fun x : real => @lem1956641 x)). Qed.
Lemma lem1956643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956644 : term65 = term66.
Proof. exact (MK_COMB (@lem1956643) (@lem1956642)). Qed.
Lemma lem1956645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956646 : term67 = term68.
Proof. exact (MK_COMB (@lem1956645) (@lem1956644)). Qed.
Lemma lem1956647 (x : real) : (term58 x) = (term59 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1956648 : term69 = term53.
Proof. exact (fun_ext (fun x : real => @lem1956647 x)). Qed.
Lemma lem1956649 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956650 : term70 = term71.
Proof. exact (MK_COMB (@lem1956649) (@lem1956648)). Qed.
Lemma lem1956651 : term51 = term72.
Proof. exact (MK_COMB (@lem1956646) (@lem1956650)). Qed.
Lemma lem1956652 : (term50 = term51) = (term45 = term72).
Proof. exact (MK_COMB (@lem1956640) (@lem1956651)). Qed.
Lemma lem1956751 : term45 = term72.
Proof. exact (EQ_MP (@lem1956652) (@lem1956630)). Qed.
Lemma lem1956752 : term28 = term72.
Proof. exact (TRANS (@lem1956626) (@lem1956751)). Qed.
Lemma lem1956753 (h1 : term28) : term72.
Proof. exact (EQ_MP (@lem1956752) (@lem1956536 h1)). Qed.
Lemma lem1956760 (x : real) : (term23 x) = (term73 x).
Proof. exact (@lem17265 (term74 x) (term75 x)). Qed.
Lemma lem1956761 : term24 = term76.
Proof. exact (fun_ext (fun x : real => @lem1956760 x)). Qed.
Lemma lem1956762 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956815 : term25 = term77.
Proof. exact (MK_COMB (@lem1956762) (@lem1956761)). Qed.
Lemma lem1956816 (h1 : term25) : term77.
Proof. exact (EQ_MP (@lem1956815) (@lem1956537 h1)). Qed.
Lemma lem1956824 (x : real) (y : real) : (term78 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem1956826 (x : real) (y : real) : (term79 x y) = (term79 x y).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1956827 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1956826 x y) (@lem1956824 x y)). Qed.
Lemma lem1956828 (x : real) (y : real) : (term82 x y) = (term80 x y).
Proof. exact (@lem17045 (real_le x y) (term83 x y)). Qed.
Lemma lem1956829 (x : real) (y : real) : (term82 x y) = (term81 x y).
Proof. exact (TRANS (@lem1956828 x y) (@lem1956827 x y)). Qed.
Lemma lem1956835 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1956837 (x : real) (y : real) : (term85 x y) = (term85 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1956838 (x : real) (y : real) : (term86 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem1956837 x y) (@lem1956829 x y)). Qed.
Lemma lem1956839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956840 (x : real) (y : real) : (term88 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1956839) (@lem1956838 x y)). Qed.
Lemma lem1956841 (x : real) (y : real) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1956840 x y) (@lem1956835 x y)). Qed.
Lemma lem1956842 (x : real) (y : real) : ((real_lt x y) = (term19 x y)) = (term90 x y).
Proof. exact (@lem17784 (real_lt x y) (term19 x y)). Qed.
Lemma lem1956843 (x : real) (y : real) : ((real_lt x y) = (term19 x y)) = (term91 x y).
Proof. exact (TRANS (@lem1956842 x y) (@lem1956841 x y)). Qed.
Lemma lem1956844 (x : real) : (term20 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1956843 x y)). Qed.
Lemma lem1956845 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956846 (x : real) : (term21 x) = (term93 x).
Proof. exact (MK_COMB (@lem1956845) (@lem1956844 x)). Qed.
Lemma lem1956847 : term22 = term94.
Proof. exact (fun_ext (fun x : real => @lem1956846 x)). Qed.
Lemma lem1956848 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956849 : term10 = term95.
Proof. exact (MK_COMB (@lem1956848) (@lem1956847)). Qed.
Lemma lem1956855 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1956856 (P : real -> Prop) (Q : real -> Prop) : (term48 P Q) = (term49 P Q).
Proof. exact (@lem1956855 real P Q). Qed.
Lemma lem1956857 (x : real) : (term96 x) = (term97 x).
Proof. exact (@lem1956856 (term98 x) (term99 x)). Qed.
Lemma lem1956858 (x : real) (y : real) : (term100 x y) = (term87 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1956859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956860 (x : real) (y : real) : (term101 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1956859) (@lem1956858 x y)). Qed.
Lemma lem1956861 (x : real) (y : real) : (term102 x y) = (term84 x y).
Proof. exact (eq_refl (term102 x y)). Qed.
Lemma lem1956862 (x : real) (y : real) : (term103 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1956860 x y) (@lem1956861 x y)). Qed.
Lemma lem1956863 (x : real) : (term104 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1956862 x y)). Qed.
Lemma lem1956864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956865 (x : real) : (term96 x) = (term93 x).
Proof. exact (MK_COMB (@lem1956864) (@lem1956863 x)). Qed.
Lemma lem1956866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1956867 (x : real) : (term105 x) = (term106 x).
Proof. exact (MK_COMB (@lem1956866) (@lem1956865 x)). Qed.
Lemma lem1956868 (x : real) (y : real) : (term100 x y) = (term87 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1956869 (x : real) : (term107 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1956868 x y)). Qed.
Lemma lem1956870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956871 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1956870) (@lem1956869 x)). Qed.
Lemma lem1956872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956873 (x : real) : (term110 x) = (term111 x).
Proof. exact (MK_COMB (@lem1956872) (@lem1956871 x)). Qed.
Lemma lem1956874 (x : real) (y : real) : (term102 x y) = (term84 x y).
Proof. exact (eq_refl (term102 x y)). Qed.
Lemma lem1956875 (x : real) : (term112 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1956874 x y)). Qed.
Lemma lem1956876 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956877 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1956876) (@lem1956875 x)). Qed.
Lemma lem1956878 (x : real) : (term97 x) = (term115 x).
Proof. exact (MK_COMB (@lem1956873 x) (@lem1956877 x)). Qed.
Lemma lem1956879 (x : real) : ((term96 x) = (term97 x)) = ((term93 x) = (term115 x)).
Proof. exact (MK_COMB (@lem1956867 x) (@lem1956878 x)). Qed.
Lemma lem1956880 (x : real) : (term93 x) = (term115 x).
Proof. exact (EQ_MP (@lem1956879 x) (@lem1956857 x)). Qed.
Lemma lem1956977 : term94 = term116.
Proof. exact (fun_ext (fun x : real => @lem1956880 x)). Qed.
Lemma lem1956978 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956979 : term95 = term117.
Proof. exact (MK_COMB (@lem1956978) (@lem1956977)). Qed.
Lemma lem1956981 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1956982 (P : real -> Prop) (Q : real -> Prop) : (term48 P Q) = (term49 P Q).
Proof. exact (@lem1956981 real P Q). Qed.
Lemma lem1956983 : term118 = term119.
Proof. exact (@lem1956982 term120 term121). Qed.
Lemma lem1956984 (x : real) : (term122 x) = (term109 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1956985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956986 (x : real) : (term123 x) = (term111 x).
Proof. exact (MK_COMB (@lem1956985) (@lem1956984 x)). Qed.
Lemma lem1956987 (x : real) : (term124 x) = (term114 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1956988 (x : real) : (term125 x) = (term115 x).
Proof. exact (MK_COMB (@lem1956986 x) (@lem1956987 x)). Qed.
Lemma lem1956989 : term126 = term116.
Proof. exact (fun_ext (fun x : real => @lem1956988 x)). Qed.
Lemma lem1956990 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956991 : term118 = term117.
Proof. exact (MK_COMB (@lem1956990) (@lem1956989)). Qed.
Lemma lem1956992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1956993 : term127 = term128.
Proof. exact (MK_COMB (@lem1956992) (@lem1956991)). Qed.
Lemma lem1956994 (x : real) : (term122 x) = (term109 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1956995 : term129 = term120.
Proof. exact (fun_ext (fun x : real => @lem1956994 x)). Qed.
Lemma lem1956996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1956997 : term130 = term131.
Proof. exact (MK_COMB (@lem1956996) (@lem1956995)). Qed.
Lemma lem1956998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956999 : term132 = term133.
Proof. exact (MK_COMB (@lem1956998) (@lem1956997)). Qed.
Lemma lem1957000 (x : real) : (term124 x) = (term114 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1957001 : term134 = term121.
Proof. exact (fun_ext (fun x : real => @lem1957000 x)). Qed.
Lemma lem1957002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957003 : term135 = term136.
Proof. exact (MK_COMB (@lem1957002) (@lem1957001)). Qed.
Lemma lem1957004 : term119 = term137.
Proof. exact (MK_COMB (@lem1956999) (@lem1957003)). Qed.
Lemma lem1957005 : (term118 = term119) = (term117 = term137).
Proof. exact (MK_COMB (@lem1956993) (@lem1957004)). Qed.
Lemma lem1957006 : term117 = term137.
Proof. exact (EQ_MP (@lem1957005) (@lem1956983)). Qed.
Lemma lem1957113 : term95 = term137.
Proof. exact (TRANS (@lem1956979) (@lem1957006)). Qed.
Lemma lem1957114 : term10 = term137.
Proof. exact (TRANS (@lem1956849) (@lem1957113)). Qed.
Lemma lem1957115 (h1 : term10) : term137.
Proof. exact (EQ_MP (@lem1957114) (@lem1956538 h1)). Qed.
Lemma lem1957141 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1957142 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1957141 x)). Qed.
Lemma lem1957143 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957144 : term71 = term71.
Proof. exact (MK_COMB (@lem1957143) (@lem1957142)). Qed.
Lemma lem1957169 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1957170 : term52 = term52.
Proof. exact (fun_ext (fun x : real => @lem1957169 x)). Qed.
Lemma lem1957171 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957172 : term66 = term66.
Proof. exact (MK_COMB (@lem1957171) (@lem1957170)). Qed.
Lemma lem1957173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1957174 : term68 = term68.
Proof. exact (MK_COMB (@lem1957173) (@lem1957172)). Qed.
Lemma lem1957175 : term72 = term72.
Proof. exact (MK_COMB (@lem1957174) (@lem1957144)). Qed.
Lemma lem1957176 (h1 : term28) : term72.
Proof. exact (EQ_MP (@lem1957175) (@lem1956753 h1)). Qed.
Lemma lem1957201 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1957202 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1957201 x)). Qed.
Lemma lem1957203 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957204 : term77 = term77.
Proof. exact (MK_COMB (@lem1957203) (@lem1957202)). Qed.
Lemma lem1957205 (h1 : term25) : term77.
Proof. exact (EQ_MP (@lem1957204) (@lem1956816 h1)). Qed.
Lemma lem1957230 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1957231 (x : real) : (term99 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1957230 x y)). Qed.
Lemma lem1957232 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957233 (x : real) : (term114 x) = (term114 x).
Proof. exact (MK_COMB (@lem1957232) (@lem1957231 x)). Qed.
Lemma lem1957234 : term121 = term121.
Proof. exact (fun_ext (fun x : real => @lem1957233 x)). Qed.
Lemma lem1957235 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957236 : term136 = term136.
Proof. exact (MK_COMB (@lem1957235) (@lem1957234)). Qed.
Lemma lem1957259 (x : real) (y : real) : (term87 x y) = (term87 x y).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1957260 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1957259 x y)). Qed.
Lemma lem1957261 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957262 (x : real) : (term109 x) = (term109 x).
Proof. exact (MK_COMB (@lem1957261) (@lem1957260 x)). Qed.
Lemma lem1957263 : term120 = term120.
Proof. exact (fun_ext (fun x : real => @lem1957262 x)). Qed.
Lemma lem1957264 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957265 : term131 = term131.
Proof. exact (MK_COMB (@lem1957264) (@lem1957263)). Qed.
Lemma lem1957266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1957267 : term133 = term133.
Proof. exact (MK_COMB (@lem1957266) (@lem1957265)). Qed.
Lemma lem1957268 : term137 = term137.
Proof. exact (MK_COMB (@lem1957267) (@lem1957236)). Qed.
Lemma lem1957269 (h1 : term10) : term137.
Proof. exact (EQ_MP (@lem1957268) (@lem1957115 h1)). Qed.
Lemma lem1957295 (x : real) (h1 : term32 x) : term32 x.
Proof. exact (h1). Qed.
Lemma lem1957298 (h1 : term10) : term136.
Proof. exact (proj2 (@lem1957269 h1)). Qed.
Lemma lem1957299 (h1 : term10) : term131.
Proof. exact (proj1 (@lem1957269 h1)). Qed.
Lemma lem1957300 (h1 : term28) : term71.
Proof. exact (proj2 (@lem1957176 h1)). Qed.
Lemma lem1957309 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1957310 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1957309 x)). Qed.
Lemma lem1957311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957313 : term77 = term77.
Proof. exact (MK_COMB (@lem1957311) (@lem1957310)). Qed.
Lemma lem1957314 (h1 : term25) : term77.
Proof. exact (EQ_MP (@lem1957313) (@lem1957205 h1)). Qed.
Lemma lem1957336 (x : real) (y : real) : (term87 x y) = (term87 x y).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1957337 (x : real) : (term98 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1957336 x y)). Qed.
Lemma lem1957338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957339 (x : real) : (term109 x) = (term109 x).
Proof. exact (MK_COMB (@lem1957338) (@lem1957337 x)). Qed.
Lemma lem1957340 : term120 = term120.
Proof. exact (fun_ext (fun x : real => @lem1957339 x)). Qed.
Lemma lem1957341 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957343 : term131 = term131.
Proof. exact (MK_COMB (@lem1957341) (@lem1957340)). Qed.
Lemma lem1957344 (h1 : term10) : term131.
Proof. exact (EQ_MP (@lem1957343) (@lem1957299 h1)). Qed.
Lemma lem1957362 (x : real) (y : real) : (term84 x y) = (term138 x y).
Proof. exact (@lem19490 (real_le x y) (term139 x y) (term83 x y)). Qed.
Lemma lem1957363 (x : real) : (term99 x) = (term140 x).
Proof. exact (fun_ext (fun y : real => @lem1957362 x y)). Qed.
Lemma lem1957364 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957365 (x : real) : (term114 x) = (term141 x).
Proof. exact (MK_COMB (@lem1957364) (@lem1957363 x)). Qed.
Lemma lem1957366 : term121 = term142.
Proof. exact (fun_ext (fun x : real => @lem1957365 x)). Qed.
Lemma lem1957367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957369 : term136 = term143.
Proof. exact (MK_COMB (@lem1957367) (@lem1957366)). Qed.
Lemma lem1957370 (h1 : term10) : term143.
Proof. exact (EQ_MP (@lem1957369) (@lem1957298 h1)). Qed.
Lemma lem1957391 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1957392 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1957391 x)). Qed.
Lemma lem1957393 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1957395 : term71 = term71.
Proof. exact (MK_COMB (@lem1957393) (@lem1957392)). Qed.
Lemma lem1957396 (h1 : term28) : term71.
Proof. exact (EQ_MP (@lem1957395) (@lem1957300 h1)). Qed.
Lemma lem1957397 (_27460 : real) (h1 : term25) : term144 _27460.
Proof. exact (@lem1957314 h1 _27460). Qed.
Lemma lem1957398 (_27460 : real) : (term144 _27460) = (term73 _27460).
Proof. exact (eq_refl (term144 _27460)). Qed.
Lemma lem1957400 (_27461 : real) (h1 : term10) : term122 _27461.
Proof. exact (@lem1957344 h1 _27461). Qed.
Lemma lem1957401 (_27461 : real) : (term122 _27461) = (term109 _27461).
Proof. exact (eq_refl (term122 _27461)). Qed.
Lemma lem1957402 (_27461 : real) (h1 : term10) : term109 _27461.
Proof. exact (EQ_MP (@lem1957401 _27461) (@lem1957400 _27461 h1)). Qed.
Lemma lem1957403 (_27461 : real) (_27462 : real) (h1 : term10) : term100 _27461 _27462.
Proof. exact (@lem1957402 _27461 h1 _27462). Qed.
Lemma lem1957404 (_27461 : real) (_27462 : real) : (term100 _27461 _27462) = (term87 _27461 _27462).
Proof. exact (eq_refl (term100 _27461 _27462)). Qed.
Lemma lem1957406 (_27463 : real) (h1 : term10) : term145 _27463.
Proof. exact (@lem1957370 h1 _27463). Qed.
Lemma lem1957407 (_27463 : real) : (term145 _27463) = (term141 _27463).
Proof. exact (eq_refl (term145 _27463)). Qed.
Lemma lem1957408 (_27463 : real) (h1 : term10) : term141 _27463.
Proof. exact (EQ_MP (@lem1957407 _27463) (@lem1957406 _27463 h1)). Qed.
Lemma lem1957409 (_27463 : real) (_27464 : real) (h1 : term10) : term146 _27463 _27464.
Proof. exact (@lem1957408 _27463 h1 _27464). Qed.
Lemma lem1957410 (_27463 : real) (_27464 : real) : (term146 _27463 _27464) = (term138 _27463 _27464).
Proof. exact (eq_refl (term146 _27463 _27464)). Qed.
Lemma lem1957411 (_27463 : real) (_27464 : real) (h1 : term10) : term138 _27463 _27464.
Proof. exact (EQ_MP (@lem1957410 _27463 _27464) (@lem1957409 _27463 _27464 h1)). Qed.
Lemma lem1957415 (_27466 : real) (h1 : term28) : term58 _27466.
Proof. exact (@lem1957396 h1 _27466). Qed.
Lemma lem1957416 (_27466 : real) : (term58 _27466) = (term59 _27466).
Proof. exact (eq_refl (term58 _27466)). Qed.
Lemma lem1957425 (_27460 : real) (h1 : term25) : term73 _27460.
Proof. exact (EQ_MP (@lem1957398 _27460) (@lem1957397 _27460 h1)). Qed.
Lemma lem1957429 (x : real) (h1 : term32 x) : term147 x.
Proof. exact (proj2 (@lem1957295 x h1)). Qed.
Lemma lem1957439 (_27461 : real) (_27462 : real) (h1 : term10) : term87 _27461 _27462.
Proof. exact (EQ_MP (@lem1957404 _27461 _27462) (@lem1957403 _27461 _27462 h1)). Qed.
Lemma lem1957451 (_27466 : real) (h1 : term28) : term59 _27466.
Proof. exact (EQ_MP (@lem1957416 _27466) (@lem1957415 _27466 h1)). Qed.
Lemma lem1957457 (_27463 : real) (_27464 : real) (h1 : term10) : term148 _27463 _27464.
Proof. exact (proj1 (@lem1957411 _27463 _27464 h1)). Qed.
Lemma lem1957463 (_27463 : real) (_27464 : real) (h1 : term10) : term149 _27463 _27464.
Proof. exact (proj2 (@lem1957411 _27463 _27464 h1)). Qed.
Lemma lem1957527 (x : real) (y : real) (z : real) : term150 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1957531 (x : real) (h1 : term32 x) : term33 x.
Proof. exact (proj1 (@lem1957295 x h1)). Qed.
Lemma lem1957532 (x : real) (h1 : term32 x) : term151 x.
Proof. exact (fun h0 : term152 x => @lem1957531 x h1). Qed.
Lemma lem1957534 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957535 (x : real) : (term151 x) = (term33 x).
Proof. exact (@lem1957534 (term33 x)). Qed.
Lemma lem1957536 (x : real) (h1 : term32 x) : term33 x.
Proof. exact (EQ_MP (@lem1957535 x) (@lem1957532 x h1)). Qed.
Lemma lem1957542 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1957543 (_27463 : real) (_27464 : real) : (term148 _27463 _27464) = (term154 _27463 _27464).
Proof. exact (@lem1957542 (real_le _27463 _27464) (term139 _27463 _27464)). Qed.
Lemma lem1957549 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1957550 (_27463 : real) (_27464 : real) : (term155 _27463 _27464) = (term156 _27463 _27464).
Proof. exact (MK_COMB (@lem1957549) (@lem1957543 _27463 _27464)). Qed.
Lemma lem1957556 (_27463 : real) (_27464 : real) : (term154 _27463 _27464) = (term154 _27463 _27464).
Proof. exact (eq_refl (term154 _27463 _27464)). Qed.
Lemma lem1957557 (_27463 : real) (_27464 : real) : ((term148 _27463 _27464) = (term154 _27463 _27464)) = ((term154 _27463 _27464) = (term154 _27463 _27464)).
Proof. exact (MK_COMB (@lem1957550 _27463 _27464) (@lem1957556 _27463 _27464)). Qed.
Lemma lem1957559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1957560 (x : Prop) : (x = x) = True.
Proof. exact (@lem1957559 Prop x). Qed.
Lemma lem1957561 (_27463 : real) (_27464 : real) : ((term154 _27463 _27464) = (term154 _27463 _27464)) = True.
Proof. exact (@lem1957560 (term154 _27463 _27464)). Qed.
Lemma lem1957562 (_27463 : real) (_27464 : real) : ((term148 _27463 _27464) = (term154 _27463 _27464)) = True.
Proof. exact (TRANS (@lem1957557 _27463 _27464) (@lem1957561 _27463 _27464)). Qed.
Lemma lem1957563 (_27463 : real) (_27464 : real) : True = ((term148 _27463 _27464) = (term154 _27463 _27464)).
Proof. exact (SYM (@lem1957562 _27463 _27464)). Qed.
Lemma lem1957564 (_27463 : real) (_27464 : real) : (term148 _27463 _27464) = (term154 _27463 _27464).
Proof. exact (EQ_MP (@lem1957563 _27463 _27464) (@lem0)). Qed.
Lemma lem1957565 (_27463 : real) (_27464 : real) (h1 : term10) : term154 _27463 _27464.
Proof. exact (EQ_MP (@lem1957564 _27463 _27464) (@lem1957457 _27463 _27464 h1)). Qed.
Lemma lem1957567 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1957568 (_27463 : real) (_27464 : real) : (term154 _27463 _27464) = (term158 _27463 _27464).
Proof. exact (@lem1957567 (term139 _27463 _27464) (real_le _27463 _27464)). Qed.
Lemma lem1957570 (a : Prop) : (term159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1957571 (_27463 : real) (_27464 : real) : (term160 _27463 _27464) = (real_lt _27463 _27464).
Proof. exact (@lem1957570 (real_lt _27463 _27464)). Qed.
Lemma lem1957572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957573 (_27463 : real) (_27464 : real) : (term161 _27463 _27464) = (term162 _27463 _27464).
Proof. exact (MK_COMB (@lem1957572) (@lem1957571 _27463 _27464)). Qed.
Lemma lem1957574 (_27463 : real) (_27464 : real) : (real_le _27463 _27464) = (real_le _27463 _27464).
Proof. exact (eq_refl (real_le _27463 _27464)). Qed.
Lemma lem1957575 (_27463 : real) (_27464 : real) : (term158 _27463 _27464) = (term163 _27463 _27464).
Proof. exact (MK_COMB (@lem1957573 _27463 _27464) (@lem1957574 _27463 _27464)). Qed.
Lemma lem1957576 (_27463 : real) (_27464 : real) : (term154 _27463 _27464) = (term163 _27463 _27464).
Proof. exact (TRANS (@lem1957568 _27463 _27464) (@lem1957575 _27463 _27464)). Qed.
Lemma lem1957579 (_27463 : real) (_27464 : real) (h1 : term10) : term163 _27463 _27464.
Proof. exact (EQ_MP (@lem1957576 _27463 _27464) (@lem1957565 _27463 _27464 h1)). Qed.
Lemma lem1957580 (x : real) (h1 : term10) : term164 x.
Proof. exact (@lem1957579 term26 x h1). Qed.
Lemma lem1957583 (x : real) (h1 : term10) (h2 : term32 x) : term74 x.
Proof. exact (@lem1957580 x h1 (@lem1957536 x h2)). Qed.
Lemma lem1957584 (x : real) (h1 : term10) (h2 : term32 x) : term165 x.
Proof. exact (fun h0 : term166 x => @lem1957583 x h1 h2). Qed.
Lemma lem1957586 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957587 (x : real) : (term165 x) = (term74 x).
Proof. exact (@lem1957586 (term74 x)). Qed.
Lemma lem1957588 (x : real) (h1 : term10) (h2 : term32 x) : term74 x.
Proof. exact (EQ_MP (@lem1957587 x) (@lem1957584 x h1 h2)). Qed.
Lemma lem1957594 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1957595 (_27460 : real) : (term73 _27460) = (term167 _27460).
Proof. exact (@lem1957594 (term75 _27460) (term166 _27460)). Qed.
Lemma lem1957601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1957602 (_27460 : real) : (term168 _27460) = (term169 _27460).
Proof. exact (MK_COMB (@lem1957601) (@lem1957595 _27460)). Qed.
Lemma lem1957608 (_27460 : real) : (term167 _27460) = (term167 _27460).
Proof. exact (eq_refl (term167 _27460)). Qed.
Lemma lem1957609 (_27460 : real) : ((term73 _27460) = (term167 _27460)) = ((term167 _27460) = (term167 _27460)).
Proof. exact (MK_COMB (@lem1957602 _27460) (@lem1957608 _27460)). Qed.
Lemma lem1957611 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1957612 (x : Prop) : (x = x) = True.
Proof. exact (@lem1957611 Prop x). Qed.
Lemma lem1957613 (_27460 : real) : ((term167 _27460) = (term167 _27460)) = True.
Proof. exact (@lem1957612 (term167 _27460)). Qed.
Lemma lem1957614 (_27460 : real) : ((term73 _27460) = (term167 _27460)) = True.
Proof. exact (TRANS (@lem1957609 _27460) (@lem1957613 _27460)). Qed.
Lemma lem1957615 (_27460 : real) : True = ((term73 _27460) = (term167 _27460)).
Proof. exact (SYM (@lem1957614 _27460)). Qed.
Lemma lem1957616 (_27460 : real) : (term73 _27460) = (term167 _27460).
Proof. exact (EQ_MP (@lem1957615 _27460) (@lem0)). Qed.
Lemma lem1957617 (_27460 : real) (h1 : term25) : term167 _27460.
Proof. exact (EQ_MP (@lem1957616 _27460) (@lem1957425 _27460 h1)). Qed.
Lemma lem1957619 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1957620 (_27460 : real) : (term167 _27460) = (term170 _27460).
Proof. exact (@lem1957619 (term166 _27460) (term75 _27460)). Qed.
Lemma lem1957622 (a : Prop) : (term159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1957623 (_27460 : real) : (term171 _27460) = (term74 _27460).
Proof. exact (@lem1957622 (term74 _27460)). Qed.
Lemma lem1957624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957625 (_27460 : real) : (term172 _27460) = (term173 _27460).
Proof. exact (MK_COMB (@lem1957624) (@lem1957623 _27460)). Qed.
Lemma lem1957626 (_27460 : real) : (term75 _27460) = (term75 _27460).
Proof. exact (eq_refl (term75 _27460)). Qed.
Lemma lem1957627 (_27460 : real) : (term170 _27460) = (term23 _27460).
Proof. exact (MK_COMB (@lem1957625 _27460) (@lem1957626 _27460)). Qed.
Lemma lem1957628 (_27460 : real) : (term167 _27460) = (term23 _27460).
Proof. exact (TRANS (@lem1957620 _27460) (@lem1957627 _27460)). Qed.
Lemma lem1957631 (_27460 : real) (h1 : term25) : term23 _27460.
Proof. exact (EQ_MP (@lem1957628 _27460) (@lem1957617 _27460 h1)). Qed.
Lemma lem1957632 (x : real) (h1 : term25) : term23 x.
Proof. exact (@lem1957631 x h1). Qed.
Lemma lem1957635 (x : real) (h1 : term10) (h2 : term25) (h3 : term32 x) : term75 x.
Proof. exact (@lem1957632 x h2 (@lem1957588 x h1 h3)). Qed.
Lemma lem1957636 (x : real) (h1 : term10) (h2 : term25) (h3 : term32 x) : term174 x.
Proof. exact (fun h0 : term175 x => @lem1957635 x h1 h2 h3). Qed.
Lemma lem1957638 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957639 (x : real) : (term174 x) = (term75 x).
Proof. exact (@lem1957638 (term75 x)). Qed.
Lemma lem1957640 (x : real) (h1 : term10) (h2 : term25) (h3 : term32 x) : term75 x.
Proof. exact (EQ_MP (@lem1957639 x) (@lem1957636 x h1 h2 h3)). Qed.
Lemma lem1957642 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1957643 : term26 = term26.
Proof. exact (@lem1957642 term26). Qed.
Lemma lem1957644 : term176.
Proof. exact (fun h0 : term177 => @lem1957643). Qed.
Lemma lem1957646 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957647 : term176 = (term26 = term26).
Proof. exact (@lem1957646 (term26 = term26)). Qed.
Lemma lem1957648 : term26 = term26.
Proof. exact (EQ_MP (@lem1957647) (@lem1957644)). Qed.
Lemma lem1957650 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1957651 (x : real) : term178 x.
Proof. exact (fun h0 : term179 x => @lem1957650 x). Qed.
Lemma lem1957653 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957654 (x : real) : (term178 x) = (x = x).
Proof. exact (@lem1957653 (x = x)). Qed.
Lemma lem1957655 (x : real) : x = x.
Proof. exact (EQ_MP (@lem1957654 x) (@lem1957651 x)). Qed.
Lemma lem1957657 (x : real) (h1 : term32 x) : term33 x.
Proof. exact (proj1 (@lem1957295 x h1)). Qed.
Lemma lem1957658 (x : real) (h1 : term32 x) : term151 x.
Proof. exact (fun h0 : term152 x => @lem1957657 x h1). Qed.
Lemma lem1957660 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957661 (x : real) : (term151 x) = (term33 x).
Proof. exact (@lem1957660 (term33 x)). Qed.
Lemma lem1957662 (x : real) (h1 : term32 x) : term33 x.
Proof. exact (EQ_MP (@lem1957661 x) (@lem1957658 x h1)). Qed.
Lemma lem1957668 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1957669 (_27463 : real) (_27464 : real) : (term149 _27463 _27464) = (term180 _27463 _27464).
Proof. exact (@lem1957668 (term83 _27463 _27464) (term139 _27463 _27464)). Qed.
Lemma lem1957677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1957678 (_27463 : real) (_27464 : real) : (term181 _27463 _27464) = (term182 _27463 _27464).
Proof. exact (MK_COMB (@lem1957677) (@lem1957669 _27463 _27464)). Qed.
Lemma lem1957686 (_27463 : real) (_27464 : real) : (term180 _27463 _27464) = (term180 _27463 _27464).
Proof. exact (eq_refl (term180 _27463 _27464)). Qed.
Lemma lem1957687 (_27463 : real) (_27464 : real) : ((term149 _27463 _27464) = (term180 _27463 _27464)) = ((term180 _27463 _27464) = (term180 _27463 _27464)).
Proof. exact (MK_COMB (@lem1957678 _27463 _27464) (@lem1957686 _27463 _27464)). Qed.
Lemma lem1957689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1957690 (x : Prop) : (x = x) = True.
Proof. exact (@lem1957689 Prop x). Qed.
Lemma lem1957691 (_27463 : real) (_27464 : real) : ((term180 _27463 _27464) = (term180 _27463 _27464)) = True.
Proof. exact (@lem1957690 (term180 _27463 _27464)). Qed.
Lemma lem1957692 (_27463 : real) (_27464 : real) : ((term149 _27463 _27464) = (term180 _27463 _27464)) = True.
Proof. exact (TRANS (@lem1957687 _27463 _27464) (@lem1957691 _27463 _27464)). Qed.
Lemma lem1957693 (_27463 : real) (_27464 : real) : True = ((term149 _27463 _27464) = (term180 _27463 _27464)).
Proof. exact (SYM (@lem1957692 _27463 _27464)). Qed.
Lemma lem1957694 (_27463 : real) (_27464 : real) : (term149 _27463 _27464) = (term180 _27463 _27464).
Proof. exact (EQ_MP (@lem1957693 _27463 _27464) (@lem0)). Qed.
Lemma lem1957695 (_27463 : real) (_27464 : real) (h1 : term10) : term180 _27463 _27464.
Proof. exact (EQ_MP (@lem1957694 _27463 _27464) (@lem1957463 _27463 _27464 h1)). Qed.
Lemma lem1957697 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1957698 (_27463 : real) (_27464 : real) : (term180 _27463 _27464) = (term183 _27463 _27464).
Proof. exact (@lem1957697 (term139 _27463 _27464) (term83 _27463 _27464)). Qed.
Lemma lem1957700 (a : Prop) : (term159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1957701 (_27463 : real) (_27464 : real) : (term160 _27463 _27464) = (real_lt _27463 _27464).
Proof. exact (@lem1957700 (real_lt _27463 _27464)). Qed.
Lemma lem1957702 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957703 (_27463 : real) (_27464 : real) : (term161 _27463 _27464) = (term162 _27463 _27464).
Proof. exact (MK_COMB (@lem1957702) (@lem1957701 _27463 _27464)). Qed.
Lemma lem1957704 (_27463 : real) (_27464 : real) : (term83 _27463 _27464) = (term83 _27463 _27464).
Proof. exact (eq_refl (term83 _27463 _27464)). Qed.
Lemma lem1957705 (_27463 : real) (_27464 : real) : (term183 _27463 _27464) = (term184 _27463 _27464).
Proof. exact (MK_COMB (@lem1957703 _27463 _27464) (@lem1957704 _27463 _27464)). Qed.
Lemma lem1957706 (_27463 : real) (_27464 : real) : (term180 _27463 _27464) = (term184 _27463 _27464).
Proof. exact (TRANS (@lem1957698 _27463 _27464) (@lem1957705 _27463 _27464)). Qed.
Lemma lem1957709 (_27463 : real) (_27464 : real) (h1 : term10) : term184 _27463 _27464.
Proof. exact (EQ_MP (@lem1957706 _27463 _27464) (@lem1957695 _27463 _27464 h1)). Qed.
Lemma lem1957710 (x : real) (h1 : term10) : term185 x.
Proof. exact (@lem1957709 term26 x h1). Qed.
Lemma lem1957713 (x : real) (h1 : term10) (h2 : term32 x) : term186 x.
Proof. exact (@lem1957710 x h1 (@lem1957662 x h2)). Qed.
Lemma lem1957714 (x : real) (h1 : term10) (h2 : term32 x) : term187 x.
Proof. exact (fun h0 : term26 = x => @lem1957713 x h1 h2). Qed.
Lemma lem1957716 (p : Prop) : (term188 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1957717 (x : real) : (term187 x) = (term186 x).
Proof. exact (@lem1957716 (term26 = x)). Qed.
Lemma lem1957718 (x : real) (h1 : term10) (h2 : term32 x) : term186 x.
Proof. exact (EQ_MP (@lem1957717 x) (@lem1957714 x h1 h2)). Qed.
Lemma lem1957720 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1957721 (z : real) (x : real) (y : real) : (term150 x y z) = (term189 z x y).
Proof. exact (@lem1957720 (term190 x y z) (term83 x y)). Qed.
Lemma lem1957723 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1957724 (x : real) (y : real) (z : real) : (term193 x y z) = (term194 x y z).
Proof. exact (@lem1957723 (term83 x z) (y = z)). Qed.
Lemma lem1957726 (a : Prop) : (term159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1957727 (x : real) (z : real) : (term78 x z) = (x = z).
Proof. exact (@lem1957726 (x = z)). Qed.
Lemma lem1957728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1957729 (x : real) (z : real) : (term195 x z) = (term196 x z).
Proof. exact (MK_COMB (@lem1957728) (@lem1957727 x z)). Qed.
Lemma lem1957730 (y : real) (z : real) : (term83 y z) = (term83 y z).
Proof. exact (eq_refl (term83 y z)). Qed.
Lemma lem1957731 (x : real) (y : real) (z : real) : (term194 x y z) = (term197 x y z).
Proof. exact (MK_COMB (@lem1957729 x z) (@lem1957730 y z)). Qed.
Lemma lem1957732 (x : real) (y : real) (z : real) : (term193 x y z) = (term197 x y z).
Proof. exact (TRANS (@lem1957724 x y z) (@lem1957731 x y z)). Qed.
Lemma lem1957733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957734 (x : real) (y : real) (z : real) : (term198 x y z) = (term199 x y z).
Proof. exact (MK_COMB (@lem1957733) (@lem1957732 x y z)). Qed.
Lemma lem1957735 (x : real) (y : real) : (term83 x y) = (term83 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem1957736 (z : real) (x : real) (y : real) : (term189 z x y) = (term200 z x y).
Proof. exact (MK_COMB (@lem1957734 x y z) (@lem1957735 x y)). Qed.
Lemma lem1957737 (z : real) (x : real) (y : real) : (term150 x y z) = (term200 z x y).
Proof. exact (TRANS (@lem1957721 z x y) (@lem1957736 z x y)). Qed.
Lemma lem1957739 (x : real) (h1 : term10) (h2 : term32 x) : term201 x.
Proof. exact (conj (@lem1957655 x) (@lem1957718 x h1 h2)). Qed.
Lemma lem1957741 (z : real) (x : real) (y : real) : term200 z x y.
Proof. exact (EQ_MP (@lem1957737 z x y) (@lem1957527 x y z)). Qed.
Lemma lem1957742 (x : real) : term202 x.
Proof. exact (@lem1957741 x x term26). Qed.
Lemma lem1957745 (x : real) (h1 : term10) (h2 : term32 x) : term203 x.
Proof. exact (@lem1957742 x (@lem1957739 x h1 h2)). Qed.
Lemma lem1957746 (x : real) (h1 : term10) (h2 : term32 x) : term204 x.
Proof. exact (fun h0 : x = term26 => @lem1957745 x h1 h2). Qed.
Lemma lem1957748 (p : Prop) : (term188 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1957749 (x : real) : (term204 x) = (term203 x).
Proof. exact (@lem1957748 (x = term26)). Qed.
Lemma lem1957750 (x : real) (h1 : term10) (h2 : term32 x) : term203 x.
Proof. exact (EQ_MP (@lem1957749 x) (@lem1957746 x h1 h2)). Qed.
Lemma lem1957752 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1957755 (_27466 : real) : (term59 _27466) = (term205 _27466).
Proof. exact (@lem1957752 (_27466 = term26) (term206 _27466)). Qed.
Lemma lem1957758 (_27466 : real) (h1 : term28) : term205 _27466.
Proof. exact (EQ_MP (@lem1957755 _27466) (@lem1957451 _27466 h1)). Qed.
Lemma lem1957759 (x : real) (h1 : term28) : term205 x.
Proof. exact (@lem1957758 x h1). Qed.
Lemma lem1957762 (x : real) (h1 : term10) (h2 : term28) (h3 : term32 x) : term206 x.
Proof. exact (@lem1957759 x h2 (@lem1957750 x h1 h3)). Qed.
Lemma lem1957763 (x : real) (h1 : term10) (h2 : term28) (h3 : term32 x) : term207 x.
Proof. exact (fun h0 : (sqrt x) = term26 => @lem1957762 x h1 h2 h3). Qed.
Lemma lem1957765 (p : Prop) : (term188 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1957766 (x : real) : (term207 x) = (term206 x).
Proof. exact (@lem1957765 ((sqrt x) = term26)). Qed.
Lemma lem1957767 (x : real) (h1 : term10) (h2 : term28) (h3 : term32 x) : term206 x.
Proof. exact (EQ_MP (@lem1957766 x) (@lem1957763 x h1 h2 h3)). Qed.
Lemma lem1957768 (x : real) (h1 : term10) (h2 : term28) (h3 : term32 x) : term208 x.
Proof. exact (conj (@lem1957648) (@lem1957767 x h1 h2 h3)). Qed.
Lemma lem1957770 (z : real) (x : real) (y : real) : term200 z x y.
Proof. exact (EQ_MP (@lem1957737 z x y) (@lem1957527 x y z)). Qed.
Lemma lem1957771 (x : real) : term209 x.
Proof. exact (@lem1957770 term26 term26 (sqrt x)). Qed.
Lemma lem1957774 (x : real) (h1 : term10) (h2 : term28) (h3 : term32 x) : term210 x.
Proof. exact (@lem1957771 x (@lem1957768 x h1 h2 h3)). Qed.
Lemma lem1957775 (x : real) (h1 : term10) (h2 : term28) (h3 : term32 x) : term211 x.
Proof. exact (fun h0 : term26 = (sqrt x) => @lem1957774 x h1 h2 h3). Qed.
Lemma lem1957777 (p : Prop) : (term188 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1957778 (x : real) : (term211 x) = (term210 x).
Proof. exact (@lem1957777 (term26 = (sqrt x))). Qed.
Lemma lem1957779 (x : real) (h1 : term10) (h2 : term28) (h3 : term32 x) : term210 x.
Proof. exact (EQ_MP (@lem1957778 x) (@lem1957775 x h1 h2 h3)). Qed.
Lemma lem1957781 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1957782 (_27461 : real) (_27462 : real) : (term87 _27461 _27462) = (term212 _27461 _27462).
Proof. exact (@lem1957781 (term81 _27461 _27462) (real_lt _27461 _27462)). Qed.
Lemma lem1957784 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1957785 (_27461 : real) (_27462 : real) : (term213 _27461 _27462) = (term214 _27461 _27462).
Proof. exact (@lem1957784 (term215 _27461 _27462) (_27461 = _27462)). Qed.
Lemma lem1957787 (a : Prop) : (term159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1957788 (_27461 : real) (_27462 : real) : (term216 _27461 _27462) = (real_le _27461 _27462).
Proof. exact (@lem1957787 (real_le _27461 _27462)). Qed.
Lemma lem1957789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1957790 (_27461 : real) (_27462 : real) : (term217 _27461 _27462) = (term218 _27461 _27462).
Proof. exact (MK_COMB (@lem1957789) (@lem1957788 _27461 _27462)). Qed.
Lemma lem1957791 (_27461 : real) (_27462 : real) : (term83 _27461 _27462) = (term83 _27461 _27462).
Proof. exact (eq_refl (term83 _27461 _27462)). Qed.
Lemma lem1957792 (_27461 : real) (_27462 : real) : (term214 _27461 _27462) = (term19 _27461 _27462).
Proof. exact (MK_COMB (@lem1957790 _27461 _27462) (@lem1957791 _27461 _27462)). Qed.
Lemma lem1957793 (_27461 : real) (_27462 : real) : (term213 _27461 _27462) = (term19 _27461 _27462).
Proof. exact (TRANS (@lem1957785 _27461 _27462) (@lem1957792 _27461 _27462)). Qed.
Lemma lem1957794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1957795 (_27461 : real) (_27462 : real) : (term219 _27461 _27462) = (term220 _27461 _27462).
Proof. exact (MK_COMB (@lem1957794) (@lem1957793 _27461 _27462)). Qed.
Lemma lem1957796 (_27461 : real) (_27462 : real) : (real_lt _27461 _27462) = (real_lt _27461 _27462).
Proof. exact (eq_refl (real_lt _27461 _27462)). Qed.
Lemma lem1957797 (_27461 : real) (_27462 : real) : (term212 _27461 _27462) = (term221 _27461 _27462).
Proof. exact (MK_COMB (@lem1957795 _27461 _27462) (@lem1957796 _27461 _27462)). Qed.
Lemma lem1957798 (_27461 : real) (_27462 : real) : (term87 _27461 _27462) = (term221 _27461 _27462).
Proof. exact (TRANS (@lem1957782 _27461 _27462) (@lem1957797 _27461 _27462)). Qed.
Lemma lem1957800 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : term222 x.
Proof. exact (conj (@lem1957640 x h1 h3 h4) (@lem1957779 x h1 h2 h4)). Qed.
Lemma lem1957802 (_27461 : real) (_27462 : real) (h1 : term10) : term221 _27461 _27462.
Proof. exact (EQ_MP (@lem1957798 _27461 _27462) (@lem1957439 _27461 _27462 h1)). Qed.
Lemma lem1957803 (x : real) (h1 : term10) : term223 x.
Proof. exact (@lem1957802 term26 (sqrt x) h1). Qed.
Lemma lem1957806 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : term34 x.
Proof. exact (@lem1957803 x h1 (@lem1957800 x h1 h2 h3 h4)). Qed.
Lemma lem1957807 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : term224 x.
Proof. exact (fun h0 : term147 x => @lem1957806 x h1 h2 h3 h4). Qed.
Lemma lem1957809 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957810 (x : real) : (term224 x) = (term34 x).
Proof. exact (@lem1957809 (term34 x)). Qed.
Lemma lem1957811 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : term34 x.
Proof. exact (EQ_MP (@lem1957810 x) (@lem1957807 x h1 h2 h3 h4)). Qed.
Lemma lem1957814 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1957816 (x : real) : (term147 x) = (term225 x).
Proof. exact (@lem1957814 (term34 x)). Qed.
Lemma lem1957819 (x : real) (h1 : term32 x) : term225 x.
Proof. exact (EQ_MP (@lem1957816 x) (@lem1957429 x h1)). Qed.
Lemma lem1957822 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : False.
Proof. exact (@lem1957819 x h4 (@lem1957811 x h1 h2 h3 h4)). Qed.
Lemma lem1957823 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : term226.
Proof. exact (fun h0 : ~ False => @lem1957822 x h1 h2 h3 h4). Qed.
Lemma lem1957825 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1957826 : term226 = False.
Proof. exact (@lem1957825 False). Qed.
Lemma lem1957827 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : False.
Proof. exact (EQ_MP (@lem1957826) (@lem1957823 x h1 h2 h3 h4)). Qed.
Lemma lem1957828 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : (term32 x) = False.
Proof. exact (prop_ext (fun h5 : term32 x => @lem1957827 x h1 h2 h3 h4) (fun h5 : False => @lem1957295 x h4)). Qed.
Lemma lem1957829 (x : real) (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term32 x) : False.
Proof. exact (EQ_MP (@lem1957828 x h1 h2 h3 h4) (@lem1957295 x h4)). Qed.
Lemma lem1957830 (h1 : term10) (h2 : term28) (h3 : term25) (h4 : term3) : False.
Proof. exact (ex_elim (@lem1956608 h4) (fun x : real => fun h0 : term41 x => @lem1957829 x h1 h2 h3 h0)). Qed.
Lemma lem1957831 (h1 : term28) (h2 : term25) (h3 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1957830 h0 h1 h2 h3). Qed.
Lemma lem1957832 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1957833 (h1 : term28) (h2 : term25) (h3 : term3) : term9.
Proof. exact (EQ_MP (@lem1957832) (@lem1957831 h1 h2 h3)). Qed.
Lemma lem1957834 (h1 : term28) (h2 : term3) : term13.
Proof. exact (fun h0 : term25 => @lem1957833 h1 h0 h2). Qed.
Lemma lem1957835 (h1 : term3) : term16.
Proof. exact (fun h0 : term28 => @lem1957834 h0 h1). Qed.
Lemma lem1957836 : term18.
Proof. exact (fun h0 : term3 => @lem1957835 h0). Qed.
Lemma lem1957837 : term4.
Proof. exact (EQ_MP (@lem1956534) (@lem1957836)). Qed.
Lemma lem1957839 : term4.
Proof. exact (@lem1956383 (@lem1957837)). Qed.
Lemma lem1957840 (h1 : term3) : term15.
Proof. exact (@lem1957839 (@lem1956368 h1)). Qed.
Lemma lem1957841 (h1 : term3) : term12.
Proof. exact (@lem1957840 h1 (@lem1947675)). Qed.
Lemma lem1957842 (h1 : term3) : term8.
Proof. exact (@lem1957841 h1 (@lem1945292)). Qed.
Lemma lem1957843 (h1 : term3) : False.
Proof. exact (@lem1957842 h1 (@lem1379381)). Qed.
Lemma lem1957844 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1957843 h1) (fun h2 : False => @lem1956368 h1)). Qed.
Lemma lem1957845 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1957844 h1) (@lem1956368 h1)). Qed.
Lemma lem1957846 : term2.
Proof. exact (fun h0 : term3 => @lem1957845 h0). Qed.
Lemma lem1957847 : term1.
Proof. exact (EQ_MP (@lem1956367) (@lem1957846)). Qed.
