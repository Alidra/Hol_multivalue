Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1339577_term_abbrevs.
Require Import TREAL_LE_TRANS_spec.
Require Import thm1337985_spec.
Require Import thm1337990_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Lemma lem1339442 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339443 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_le x y) = (term0 x y).
Proof. exact (@lem1339442 x y). Qed.
Lemma lem1339444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1339445 (x : prod hreal hreal) (y : prod hreal hreal) : (term1 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1339444) (@lem1339443 x y)). Qed.
Lemma lem1339447 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339448 (y : prod hreal hreal) (z : prod hreal hreal) : (treal_le y z) = (term0 y z).
Proof. exact (@lem1339447 y z). Qed.
Lemma lem1339449 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term3 x y z) = (term4 x y z).
Proof. exact (MK_COMB (@lem1339445 x y) (@lem1339448 y z)). Qed.
Lemma lem1339452 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1339453 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term5 x y z) = (term6 x y z).
Proof. exact (MK_COMB (@lem1339452) (@lem1339449 x y z)). Qed.
Lemma lem1339455 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339456 (x : prod hreal hreal) (z : prod hreal hreal) : (treal_le x z) = (term0 x z).
Proof. exact (@lem1339455 x z). Qed.
Lemma lem1339457 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term7 y x z) = (term8 y x z).
Proof. exact (MK_COMB (@lem1339453 x y z) (@lem1339456 x z)). Qed.
Lemma lem1339460 (y : prod hreal hreal) (x : prod hreal hreal) : (term9 y x) = (term10 y x).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1339457 y x z)). Qed.
Lemma lem1339461 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339462 (y : prod hreal hreal) (x : prod hreal hreal) : (term11 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1339461) (@lem1339460 y x)). Qed.
Lemma lem1339468 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339469 (y : prod hreal hreal) (x : prod hreal hreal) : (term15 y x) = (term16 y x).
Proof. exact (@lem1339468 (term17 y x)). Qed.
Lemma lem1339470 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term18 y x z) = (term8 y x z).
Proof. exact (eq_refl (term18 y x z)). Qed.
Lemma lem1339471 (y : prod hreal hreal) (x : prod hreal hreal) : (term19 y x) = (term10 y x).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1339470 y x z)). Qed.
Lemma lem1339472 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339473 (y : prod hreal hreal) (x : prod hreal hreal) : (term15 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1339472) (@lem1339471 y x)). Qed.
Lemma lem1339474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339475 (y : prod hreal hreal) (x : prod hreal hreal) : (term20 y x) = (term21 y x).
Proof. exact (MK_COMB (@lem1339474) (@lem1339473 y x)). Qed.
Lemma lem1339476 (y : prod hreal hreal) (x : prod hreal hreal) (z : real) : (term22 y x z) = (term23 y x z).
Proof. exact (eq_refl (term22 y x z)). Qed.
Lemma lem1339477 (y : prod hreal hreal) (x : prod hreal hreal) : (term24 y x) = (term17 y x).
Proof. exact (fun_ext (fun z : real => @lem1339476 y x z)). Qed.
Lemma lem1339478 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339479 (y : prod hreal hreal) (x : prod hreal hreal) : (term16 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem1339478) (@lem1339477 y x)). Qed.
Lemma lem1339480 (y : prod hreal hreal) (x : prod hreal hreal) : ((term15 y x) = (term16 y x)) = ((term12 y x) = (term25 y x)).
Proof. exact (MK_COMB (@lem1339475 y x) (@lem1339479 y x)). Qed.
Lemma lem1339481 (y : prod hreal hreal) (x : prod hreal hreal) : (term12 y x) = (term25 y x).
Proof. exact (EQ_MP (@lem1339480 y x) (@lem1339469 y x)). Qed.
Lemma lem1339492 (y : prod hreal hreal) (x : prod hreal hreal) : (term11 y x) = (term25 y x).
Proof. exact (TRANS (@lem1339462 y x) (@lem1339481 y x)). Qed.
Lemma lem1339493 (x : prod hreal hreal) : (term26 x) = (term27 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339492 y x)). Qed.
Lemma lem1339494 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339495 (x : prod hreal hreal) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1339494) (@lem1339493 x)). Qed.
Lemma lem1339501 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339502 (x : prod hreal hreal) : (term30 x) = (term31 x).
Proof. exact (@lem1339501 (term32 x)). Qed.
Lemma lem1339503 (y : prod hreal hreal) (x : prod hreal hreal) : (term33 x y) = (term25 y x).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1339504 (x : prod hreal hreal) : (term34 x) = (term27 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339503 y x)). Qed.
Lemma lem1339505 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339506 (x : prod hreal hreal) : (term30 x) = (term29 x).
Proof. exact (MK_COMB (@lem1339505) (@lem1339504 x)). Qed.
Lemma lem1339507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339508 (x : prod hreal hreal) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1339507) (@lem1339506 x)). Qed.
Lemma lem1339509 (y : real) (x : prod hreal hreal) : (term37 x y) = (term38 y x).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1339510 (x : prod hreal hreal) : (term39 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1339509 y x)). Qed.
Lemma lem1339511 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339512 (x : prod hreal hreal) : (term31 x) = (term40 x).
Proof. exact (MK_COMB (@lem1339511) (@lem1339510 x)). Qed.
Lemma lem1339513 (x : prod hreal hreal) : ((term30 x) = (term31 x)) = ((term29 x) = (term40 x)).
Proof. exact (MK_COMB (@lem1339508 x) (@lem1339512 x)). Qed.
Lemma lem1339514 (x : prod hreal hreal) : (term29 x) = (term40 x).
Proof. exact (EQ_MP (@lem1339513 x) (@lem1339502 x)). Qed.
Lemma lem1339531 (x : prod hreal hreal) : (term28 x) = (term40 x).
Proof. exact (TRANS (@lem1339495 x) (@lem1339514 x)). Qed.
Lemma lem1339532 : term41 = term42.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339531 x)). Qed.
Lemma lem1339533 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339534 : term43 = term44.
Proof. exact (MK_COMB (@lem1339533) (@lem1339532)). Qed.
Lemma lem1339540 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339541 : term45 = term46.
Proof. exact (@lem1339540 term47). Qed.
Lemma lem1339542 (x : prod hreal hreal) : (term48 x) = (term40 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1339543 : term49 = term42.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339542 x)). Qed.
Lemma lem1339544 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339545 : term45 = term44.
Proof. exact (MK_COMB (@lem1339544) (@lem1339543)). Qed.
Lemma lem1339546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339547 : term50 = term51.
Proof. exact (MK_COMB (@lem1339546) (@lem1339545)). Qed.
Lemma lem1339548 (x : real) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1339549 : term54 = term47.
Proof. exact (fun_ext (fun x : real => @lem1339548 x)). Qed.
Lemma lem1339550 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339551 : term46 = term55.
Proof. exact (MK_COMB (@lem1339550) (@lem1339549)). Qed.
Lemma lem1339552 : (term45 = term46) = (term44 = term55).
Proof. exact (MK_COMB (@lem1339547) (@lem1339551)). Qed.
Lemma lem1339553 : term44 = term55.
Proof. exact (EQ_MP (@lem1339552) (@lem1339541)). Qed.
Lemma lem1339576 : term43 = term55.
Proof. exact (TRANS (@lem1339534) (@lem1339553)). Qed.
Lemma lem1339577 : term55.
Proof. exact (EQ_MP (@lem1339576) (@lem1330544)). Qed.
