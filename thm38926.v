Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm38926_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ASSOC_spec.
Require Import ETA_AX_spec.
Require Import FUN_EQ_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20685_spec.
Require Import thm20761_spec.
Require Import thm20762_spec.
Require Import thm20780_spec.
Require Import thm20792_spec.
Require Import thm20892_spec.
Require Import thm20893_spec.
Require Import thm21021_spec.
Require Import thm21117_spec.
Require Import thm21179_spec.
Require Import thm21180_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21397_spec.
Require Import thm21487_spec.
Require Import thm21488_spec.
Require Import thm21504_spec.
Require Import thm21595_spec.
Require Import thm21596_spec.
Require Import thm735_spec.
Require Import thm736_spec.
Require Import thm793_spec.
Require Import thm794_spec.
Require Import thm9425_spec.
Lemma lem23455 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : (term0 A B t) = t.
Proof. exact (h1). Qed.
Lemma lem23456 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : t = (term0 A B t).
Proof. exact (SYM (@lem23455 A B t h1)). Qed.
Lemma lem23457 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : t = (term0 A B t).
Proof. exact (h1). Qed.
Lemma lem23458 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : (term0 A B t) = t.
Proof. exact (SYM (@lem23457 A B t h1)). Qed.
Lemma lem23459 {A B : Type'} (t : A -> B) : ((term0 A B t) = t) = (t = (term0 A B t)).
Proof. exact (prop_ext (fun h1 : (term0 A B t) = t => @lem23456 A B t h1) (fun h1 : t = (term0 A B t) => @lem23458 A B t h1)). Qed.
Lemma lem23460 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (fun_ext (fun t : A -> B => @lem23459 A B t)). Qed.
Lemma lem23461 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem23462 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem23461 A B) (@lem23460 A B)). Qed.
Lemma lem23463 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem23462 A B) (@lem9121 A B)). Qed.
Lemma lem23464 {A B : Type'} (t : A -> B) : term5 A B t.
Proof. exact (@lem23463 A B t). Qed.
Lemma lem23465 {A B : Type'} (t : A -> B) : (term5 A B t) = (t = (term0 A B t)).
Proof. exact (eq_refl (term5 A B t)). Qed.
Lemma lem23477 (t1 : Prop) : term6 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem23478 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (eq_refl (term6 t1)). Qed.
Lemma lem23479 (t1 : Prop) : term7 t1.
Proof. exact (EQ_MP (@lem23478 t1) (@lem23477 t1)). Qed.
Lemma lem23480 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (@lem23479 t1 t2). Qed.
Lemma lem23481 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (eq_refl (term8 t1 t2)). Qed.
Lemma lem23482 (t1 : Prop) (t2 : Prop) : term9 t1 t2.
Proof. exact (EQ_MP (@lem23481 t1 t2) (@lem23480 t1 t2)). Qed.
Lemma lem23483 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term10 t1 t2 t3.
Proof. exact (@lem23482 t1 t2 t3). Qed.
Lemma lem23484 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term10 t1 t2 t3) = ((term11 t1 t2 t3) = (term12 t1 t2 t3)).
Proof. exact (eq_refl (term10 t1 t2 t3)). Qed.
Lemma lem23485 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term11 t1 t2 t3) = (term12 t1 t2 t3).
Proof. exact (EQ_MP (@lem23484 t1 t2 t3) (@lem23483 t1 t2 t3)). Qed.
Lemma lem23486 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term12 t1 t2 t3) = (term11 t1 t2 t3).
Proof. exact (SYM (@lem23485 t1 t2 t3)). Qed.
Lemma lem23487 {A B : Type'} (f : A -> B) : term13 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem23488 {A B : Type'} (f : A -> B) : (term13 A B f) = (term14 A B f).
Proof. exact (eq_refl (term13 A B f)). Qed.
Lemma lem23489 {A B : Type'} (f : A -> B) : term14 A B f.
Proof. exact (EQ_MP (@lem23488 A B f) (@lem23487 A B f)). Qed.
Lemma lem23490 {A B : Type'} (f : A -> B) (g : A -> B) : term15 A B f g.
Proof. exact (@lem23489 A B f g). Qed.
Lemma lem23491 {A B : Type'} (f : A -> B) (g : A -> B) : (term15 A B f g) = ((f = g) = (term16 A B f g)).
Proof. exact (eq_refl (term15 A B f g)). Qed.
Lemma lem23513 (a : Prop) : term17 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem23514 (a : Prop) : (term17 a) = (term18 a).
Proof. exact (eq_refl (term17 a)). Qed.
Lemma lem23515 (a : Prop) : term18 a.
Proof. exact (EQ_MP (@lem23514 a) (@lem23513 a)). Qed.
Lemma lem23516 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem23517 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem23538 (b : Prop) (c : Prop) (d : Prop) : (term19 b c d) = (term19 b c d).
Proof. exact (eq_refl (term19 b c d)). Qed.
Lemma lem23539 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : (term20 b c d a) = (term21 b c d).
Proof. exact (MK_COMB (@lem23538 b c d) (@lem23516 a h1)). Qed.
Lemma lem23540 (b : Prop) (c : Prop) (d : Prop) : (term21 b c d) = (term22 b c d).
Proof. exact (eq_refl (term21 b c d)). Qed.
Lemma lem23541 (b : Prop) (c : Prop) (d : Prop) (a : Prop) : (term23 b c d a) = (term23 b c d a).
Proof. exact (eq_refl (term23 b c d a)). Qed.
Lemma lem23542 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term20 b c d a) = (term21 b c d)) = ((term20 b c d a) = (term22 b c d)).
Proof. exact (MK_COMB (@lem23541 b c d a) (@lem23540 b c d)). Qed.
Lemma lem23543 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term20 b c d a) = (term24 a b c d).
Proof. exact (eq_refl (term20 b c d a)). Qed.
Lemma lem23544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem23545 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term23 b c d a) = (term25 a b c d).
Proof. exact (MK_COMB (@lem23544) (@lem23543 a b c d)). Qed.
Lemma lem23546 (b : Prop) (c : Prop) (d : Prop) : (term22 b c d) = (term22 b c d).
Proof. exact (eq_refl (term22 b c d)). Qed.
Lemma lem23547 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term20 b c d a) = (term22 b c d)) = ((term24 a b c d) = (term22 b c d)).
Proof. exact (MK_COMB (@lem23545 a b c d) (@lem23546 b c d)). Qed.
Lemma lem23548 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term20 b c d a) = (term21 b c d)) = ((term24 a b c d) = (term22 b c d)).
Proof. exact (TRANS (@lem23542 a b c d) (@lem23547 a b c d)). Qed.
Lemma lem23549 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : (term24 a b c d) = (term22 b c d).
Proof. exact (EQ_MP (@lem23548 a b c d) (@lem23539 b c d a h1)). Qed.
Lemma lem23550 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : (term22 b c d) = (term24 a b c d).
Proof. exact (SYM (@lem23549 b c d a h1)). Qed.
Lemma lem23551 (b : Prop) (c : Prop) (d : Prop) : (term19 b c d) = (term19 b c d).
Proof. exact (eq_refl (term19 b c d)). Qed.
Lemma lem23552 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : (term20 b c d a) = (term26 b c d).
Proof. exact (MK_COMB (@lem23551 b c d) (@lem23517 a h1)). Qed.
Lemma lem23553 (b : Prop) (c : Prop) (d : Prop) : (term26 b c d) = (term27 b c d).
Proof. exact (eq_refl (term26 b c d)). Qed.
Lemma lem23554 (b : Prop) (c : Prop) (d : Prop) (a : Prop) : (term23 b c d a) = (term23 b c d a).
Proof. exact (eq_refl (term23 b c d a)). Qed.
Lemma lem23555 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term20 b c d a) = (term26 b c d)) = ((term20 b c d a) = (term27 b c d)).
Proof. exact (MK_COMB (@lem23554 b c d a) (@lem23553 b c d)). Qed.
Lemma lem23556 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term20 b c d a) = (term24 a b c d).
Proof. exact (eq_refl (term20 b c d a)). Qed.
Lemma lem23557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem23558 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term23 b c d a) = (term25 a b c d).
Proof. exact (MK_COMB (@lem23557) (@lem23556 a b c d)). Qed.
Lemma lem23559 (b : Prop) (c : Prop) (d : Prop) : (term27 b c d) = (term27 b c d).
Proof. exact (eq_refl (term27 b c d)). Qed.
Lemma lem23560 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term20 b c d a) = (term27 b c d)) = ((term24 a b c d) = (term27 b c d)).
Proof. exact (MK_COMB (@lem23558 a b c d) (@lem23559 b c d)). Qed.
Lemma lem23561 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term20 b c d a) = (term26 b c d)) = ((term24 a b c d) = (term27 b c d)).
Proof. exact (TRANS (@lem23555 a b c d) (@lem23560 a b c d)). Qed.
Lemma lem23562 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : (term24 a b c d) = (term27 b c d).
Proof. exact (EQ_MP (@lem23561 a b c d) (@lem23552 b c d a h1)). Qed.
Lemma lem23563 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : (term27 b c d) = (term24 a b c d).
Proof. exact (SYM (@lem23562 b c d a h1)). Qed.
Lemma lem23569 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem23570 (b : Prop) (c : Prop) : (term28 b c) = (b /\ c).
Proof. exact (@lem23569 (b /\ c)). Qed.
Lemma lem23573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem23574 (b : Prop) (c : Prop) : (term29 b c) = (term30 b c).
Proof. exact (MK_COMB (@lem23573) (@lem23570 b c)). Qed.
Lemma lem23578 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem23579 (d : Prop) : (True -> d) = d.
Proof. exact (@lem23578 d). Qed.
Lemma lem23580 (b : Prop) : (imp b) = (imp b).
Proof. exact (eq_refl (imp b)). Qed.
Lemma lem23581 (b : Prop) (d : Prop) : (term31 b d) = (b -> d).
Proof. exact (MK_COMB (@lem23580 b) (@lem23579 d)). Qed.
Lemma lem23584 (c : Prop) (b : Prop) (d : Prop) : (term32 c b d) = (term33 c b d).
Proof. exact (MK_COMB (@lem23574 b c) (@lem23581 b d)). Qed.
Lemma lem23587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23588 (c : Prop) (b : Prop) (d : Prop) : (term34 c b d) = (term35 c b d).
Proof. exact (MK_COMB (@lem23587) (@lem23584 c b d)). Qed.
Lemma lem23590 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem23591 (b : Prop) (c : Prop) (d : Prop) : (term36 b c d) = (term37 b c d).
Proof. exact (@lem23590 (term37 b c d)). Qed.
Lemma lem23596 (b : Prop) (c : Prop) (d : Prop) : (term22 b c d) = (term38 b c d).
Proof. exact (MK_COMB (@lem23588 c b d) (@lem23591 b c d)). Qed.
Lemma lem23599 (b : Prop) (c : Prop) (d : Prop) : (term38 b c d) = (term22 b c d).
Proof. exact (SYM (@lem23596 b c d)). Qed.
Lemma lem23600 (b : Prop) : term17 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem23601 (b : Prop) : (term17 b) = (term18 b).
Proof. exact (eq_refl (term17 b)). Qed.
Lemma lem23602 (b : Prop) : term18 b.
Proof. exact (EQ_MP (@lem23601 b) (@lem23600 b)). Qed.
Lemma lem23603 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem23604 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem23619 (c : Prop) (d : Prop) : (term39 c d) = (term39 c d).
Proof. exact (eq_refl (term39 c d)). Qed.
Lemma lem23620 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : (term40 c d b) = (term41 c d).
Proof. exact (MK_COMB (@lem23619 c d) (@lem23603 b h1)). Qed.
Lemma lem23621 (c : Prop) (d : Prop) : (term41 c d) = (term42 c d).
Proof. exact (eq_refl (term41 c d)). Qed.
Lemma lem23622 (c : Prop) (d : Prop) (b : Prop) : (term43 c d b) = (term43 c d b).
Proof. exact (eq_refl (term43 c d b)). Qed.
Lemma lem23623 (b : Prop) (c : Prop) (d : Prop) : ((term40 c d b) = (term41 c d)) = ((term40 c d b) = (term42 c d)).
Proof. exact (MK_COMB (@lem23622 c d b) (@lem23621 c d)). Qed.
Lemma lem23624 (b : Prop) (c : Prop) (d : Prop) : (term40 c d b) = (term38 b c d).
Proof. exact (eq_refl (term40 c d b)). Qed.
Lemma lem23625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem23626 (b : Prop) (c : Prop) (d : Prop) : (term43 c d b) = (term44 b c d).
Proof. exact (MK_COMB (@lem23625) (@lem23624 b c d)). Qed.
Lemma lem23627 (c : Prop) (d : Prop) : (term42 c d) = (term42 c d).
Proof. exact (eq_refl (term42 c d)). Qed.
Lemma lem23628 (b : Prop) (c : Prop) (d : Prop) : ((term40 c d b) = (term42 c d)) = ((term38 b c d) = (term42 c d)).
Proof. exact (MK_COMB (@lem23626 b c d) (@lem23627 c d)). Qed.
Lemma lem23629 (b : Prop) (c : Prop) (d : Prop) : ((term40 c d b) = (term41 c d)) = ((term38 b c d) = (term42 c d)).
Proof. exact (TRANS (@lem23623 b c d) (@lem23628 b c d)). Qed.
Lemma lem23630 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : (term38 b c d) = (term42 c d).
Proof. exact (EQ_MP (@lem23629 b c d) (@lem23620 c d b h1)). Qed.
Lemma lem23631 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : (term42 c d) = (term38 b c d).
Proof. exact (SYM (@lem23630 c d b h1)). Qed.
Lemma lem23632 (c : Prop) (d : Prop) : (term39 c d) = (term39 c d).
Proof. exact (eq_refl (term39 c d)). Qed.
Lemma lem23633 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : (term40 c d b) = (term45 c d).
Proof. exact (MK_COMB (@lem23632 c d) (@lem23604 b h1)). Qed.
Lemma lem23634 (c : Prop) (d : Prop) : (term45 c d) = (term46 c d).
Proof. exact (eq_refl (term45 c d)). Qed.
Lemma lem23635 (c : Prop) (d : Prop) (b : Prop) : (term43 c d b) = (term43 c d b).
Proof. exact (eq_refl (term43 c d b)). Qed.
Lemma lem23636 (b : Prop) (c : Prop) (d : Prop) : ((term40 c d b) = (term45 c d)) = ((term40 c d b) = (term46 c d)).
Proof. exact (MK_COMB (@lem23635 c d b) (@lem23634 c d)). Qed.
Lemma lem23637 (b : Prop) (c : Prop) (d : Prop) : (term40 c d b) = (term38 b c d).
Proof. exact (eq_refl (term40 c d b)). Qed.
Lemma lem23638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem23639 (b : Prop) (c : Prop) (d : Prop) : (term43 c d b) = (term44 b c d).
Proof. exact (MK_COMB (@lem23638) (@lem23637 b c d)). Qed.
Lemma lem23640 (c : Prop) (d : Prop) : (term46 c d) = (term46 c d).
Proof. exact (eq_refl (term46 c d)). Qed.
Lemma lem23641 (b : Prop) (c : Prop) (d : Prop) : ((term40 c d b) = (term46 c d)) = ((term38 b c d) = (term46 c d)).
Proof. exact (MK_COMB (@lem23639 b c d) (@lem23640 c d)). Qed.
Lemma lem23642 (b : Prop) (c : Prop) (d : Prop) : ((term40 c d b) = (term45 c d)) = ((term38 b c d) = (term46 c d)).
Proof. exact (TRANS (@lem23636 b c d) (@lem23641 b c d)). Qed.
Lemma lem23643 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : (term38 b c d) = (term46 c d).
Proof. exact (EQ_MP (@lem23642 b c d) (@lem23633 c d b h1)). Qed.
Lemma lem23644 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : (term46 c d) = (term38 b c d).
Proof. exact (SYM (@lem23643 c d b h1)). Qed.
Lemma lem23650 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem23651 (c : Prop) : (True /\ c) = c.
Proof. exact (@lem23650 c). Qed.
Lemma lem23652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem23653 (c : Prop) : (term47 c) = (and c).
Proof. exact (MK_COMB (@lem23652) (@lem23651 c)). Qed.
Lemma lem23655 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem23656 (d : Prop) : (True -> d) = d.
Proof. exact (@lem23655 d). Qed.
Lemma lem23657 (c : Prop) (d : Prop) : (term48 c d) = (c /\ d).
Proof. exact (MK_COMB (@lem23653 c) (@lem23656 d)). Qed.
Lemma lem23660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23661 (c : Prop) (d : Prop) : (term49 c d) = (term50 c d).
Proof. exact (MK_COMB (@lem23660) (@lem23657 c d)). Qed.
Lemma lem23663 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem23664 (c : Prop) (d : Prop) : (term28 c d) = (c /\ d).
Proof. exact (@lem23663 (c /\ d)). Qed.
Lemma lem23667 (c : Prop) (d : Prop) : (term42 c d) = (term51 c d).
Proof. exact (MK_COMB (@lem23661 c d) (@lem23664 c d)). Qed.
Lemma lem23669 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem23670 (c : Prop) (d : Prop) : (term51 c d) = True.
Proof. exact (@lem23669 (c /\ d)). Qed.
Lemma lem23671 (c : Prop) (d : Prop) : (term42 c d) = True.
Proof. exact (TRANS (@lem23667 c d) (@lem23670 c d)). Qed.
Lemma lem23672 (c : Prop) (d : Prop) : True = (term42 c d).
Proof. exact (SYM (@lem23671 c d)). Qed.
Lemma lem23673 (c : Prop) (d : Prop) : term42 c d.
Proof. exact (EQ_MP (@lem23672 c d) (@lem0)). Qed.
Lemma lem23679 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem23680 (c : Prop) : (False /\ c) = False.
Proof. exact (@lem23679 c). Qed.
Lemma lem23681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem23682 (c : Prop) : (term52 c) = (and False).
Proof. exact (MK_COMB (@lem23681) (@lem23680 c)). Qed.
Lemma lem23684 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem23685 (d : Prop) : (False -> d) = True.
Proof. exact (@lem23684 d). Qed.
Lemma lem23686 (c : Prop) (d : Prop) : (term53 c d) = (False /\ True).
Proof. exact (MK_COMB (@lem23682 c) (@lem23685 d)). Qed.
Lemma lem23688 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem23689 : (False /\ True) = False.
Proof. exact (@lem23688 True). Qed.
Lemma lem23690 (c : Prop) (d : Prop) : (term53 c d) = False.
Proof. exact (TRANS (@lem23686 c d) (@lem23689)). Qed.
Lemma lem23691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23692 (c : Prop) (d : Prop) : (term54 c d) = (imp False).
Proof. exact (MK_COMB (@lem23691) (@lem23690 c d)). Qed.
Lemma lem23694 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem23695 (c : Prop) (d : Prop) : (term55 c d) = False.
Proof. exact (@lem23694 (c /\ d)). Qed.
Lemma lem23696 (c : Prop) (d : Prop) : (term46 c d) = (False -> False).
Proof. exact (MK_COMB (@lem23692 c d) (@lem23695 c d)). Qed.
Lemma lem23698 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem23699 : (False -> False) = True.
Proof. exact (@lem23698 False). Qed.
Lemma lem23700 (c : Prop) (d : Prop) : (term46 c d) = True.
Proof. exact (TRANS (@lem23696 c d) (@lem23699)). Qed.
Lemma lem23701 (c : Prop) (d : Prop) : True = (term46 c d).
Proof. exact (SYM (@lem23700 c d)). Qed.
Lemma lem23702 (c : Prop) (d : Prop) : term46 c d.
Proof. exact (EQ_MP (@lem23701 c d) (@lem0)). Qed.
Lemma lem23703 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : term38 b c d.
Proof. exact (EQ_MP (@lem23644 c d b h1) (@lem23702 c d)). Qed.
Lemma lem23704 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : term38 b c d.
Proof. exact (EQ_MP (@lem23631 c d b h1) (@lem23673 c d)). Qed.
Lemma lem23706 (b : Prop) (c : Prop) (d : Prop) : term38 b c d.
Proof. exact (or_elim (@lem23602 b) (fun h0 : b = True => @lem23704 c d b h0) (fun h0 : b = False => @lem23703 c d b h0)). Qed.
Lemma lem23707 (b : Prop) (c : Prop) (d : Prop) : term22 b c d.
Proof. exact (EQ_MP (@lem23599 b c d) (@lem23706 b c d)). Qed.
Lemma lem23713 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem23714 (b : Prop) (c : Prop) : (term55 b c) = False.
Proof. exact (@lem23713 (b /\ c)). Qed.
Lemma lem23715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem23716 (b : Prop) (c : Prop) : (term56 b c) = (and False).
Proof. exact (MK_COMB (@lem23715) (@lem23714 b c)). Qed.
Lemma lem23720 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem23721 (d : Prop) : (False -> d) = True.
Proof. exact (@lem23720 d). Qed.
Lemma lem23722 (b : Prop) : (imp b) = (imp b).
Proof. exact (eq_refl (imp b)). Qed.
Lemma lem23723 (d : Prop) (b : Prop) : (term57 b d) = (b -> True).
Proof. exact (MK_COMB (@lem23722 b) (@lem23721 d)). Qed.
Lemma lem23725 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem23726 (b : Prop) : (b -> True) = True.
Proof. exact (@lem23725 b). Qed.
Lemma lem23727 (b : Prop) (d : Prop) : (term57 b d) = True.
Proof. exact (TRANS (@lem23723 d b) (@lem23726 b)). Qed.
Lemma lem23728 (c : Prop) (b : Prop) (d : Prop) : (term58 c b d) = (False /\ True).
Proof. exact (MK_COMB (@lem23716 b c) (@lem23727 b d)). Qed.
Lemma lem23730 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem23731 : (False /\ True) = False.
Proof. exact (@lem23730 True). Qed.
Lemma lem23732 (c : Prop) (b : Prop) (d : Prop) : (term58 c b d) = False.
Proof. exact (TRANS (@lem23728 c b d) (@lem23731)). Qed.
Lemma lem23733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23734 (c : Prop) (b : Prop) (d : Prop) : (term59 c b d) = (imp False).
Proof. exact (MK_COMB (@lem23733) (@lem23732 c b d)). Qed.
Lemma lem23736 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem23737 (b : Prop) (c : Prop) (d : Prop) : (term60 b c d) = False.
Proof. exact (@lem23736 (term37 b c d)). Qed.
Lemma lem23738 (b : Prop) (c : Prop) (d : Prop) : (term27 b c d) = (False -> False).
Proof. exact (MK_COMB (@lem23734 c b d) (@lem23737 b c d)). Qed.
Lemma lem23740 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem23741 : (False -> False) = True.
Proof. exact (@lem23740 False). Qed.
Lemma lem23742 (b : Prop) (c : Prop) (d : Prop) : (term27 b c d) = True.
Proof. exact (TRANS (@lem23738 b c d) (@lem23741)). Qed.
Lemma lem23743 (b : Prop) (c : Prop) (d : Prop) : True = (term27 b c d).
Proof. exact (SYM (@lem23742 b c d)). Qed.
Lemma lem23744 (b : Prop) (c : Prop) (d : Prop) : term27 b c d.
Proof. exact (EQ_MP (@lem23743 b c d) (@lem0)). Qed.
Lemma lem23745 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : term24 a b c d.
Proof. exact (EQ_MP (@lem23563 b c d a h1) (@lem23744 b c d)). Qed.
Lemma lem23746 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : term24 a b c d.
Proof. exact (EQ_MP (@lem23550 b c d a h1) (@lem23707 b c d)). Qed.
Lemma lem23749 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : term24 a b c d.
Proof. exact (or_elim (@lem23515 a) (fun h0 : a = True => @lem23746 b c d a h0) (fun h0 : a = False => @lem23745 b c d a h0)). Qed.
Lemma lem23750 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term24 a b c d) : term24 a b c d.
Proof. exact (h1). Qed.
Lemma lem23751 (c : Prop) (b : Prop) (a : Prop) (d : Prop) (h1 : term61 c b a d) : term61 c b a d.
Proof. exact (h1). Qed.
Lemma lem23752 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term61 c b a d) (h2 : term24 a b c d) : term62 a b c d.
Proof. exact (@lem23750 a b c d h2 (@lem23751 c b a d h1)). Qed.
Lemma lem23753 (c : Prop) (b : Prop) (a : Prop) (d : Prop) (h1 : term61 c b a d) : term63 a b c d.
Proof. exact (fun h0 : term24 a b c d => @lem23752 a b c d h1 h0). Qed.
Lemma lem23754 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term24 a b c d) : term24 a b c d.
Proof. exact (h1). Qed.
Lemma lem23755 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term61 c b a d) (h2 : term24 a b c d) : term62 a b c d.
Proof. exact (@lem23753 c b a d h1 (@lem23754 a b c d h2)). Qed.
Lemma lem23756 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (h1 : term24 a b c d) : term24 a b c d.
Proof. exact (fun h0 : term61 c b a d => @lem23755 a b c d h0 h1). Qed.
Lemma lem23757 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : term64 a b c d.
Proof. exact (fun h0 : term24 a b c d => @lem23756 a b c d h0). Qed.
Lemma lem23769 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term65 Absty Repty R dest mk) : term65 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem23770 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term66 Absty Repty R dest mk) : term66 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem23771 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term67 Repty R.
Proof. exact (h1). Qed.
Lemma lem23772 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term68 Absty Repty R dest mk) : term68 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem23773 {Repty : Type'} (R : type1402 Repty) (h1 : term69 Repty R) : term69 Repty R.
Proof. exact (h1). Qed.
Lemma lem23774 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term70 Absty Repty R dest mk) : term70 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem23775 {Repty : Type'} (R : type1402 Repty) (h1 : term71 Repty R) : term71 Repty R.
Proof. exact (h1). Qed.
Lemma lem23776 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term72 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem23777 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term73 Absty Repty mk dest.
Proof. exact (h1). Qed.
Lemma lem23778 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : term74 Absty Repty mk R.
Proof. exact (h1). Qed.
Lemma lem23780 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem23781 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term74 Absty Repty mk R) = (term76 Absty Repty mk R).
Proof. exact (@lem23780 (term74 Absty Repty mk R)). Qed.
Lemma lem23782 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term76 Absty Repty mk R) = (term74 Absty Repty mk R).
Proof. exact (SYM (@lem23781 Absty Repty mk R)). Qed.
Lemma lem23783 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term77 Absty Repty mk R) : term77 Absty Repty mk R.
Proof. exact (h1). Qed.
Lemma lem23786 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term78 Absty Repty dest mk R) : term78 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem23787 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term79 Absty Repty dest mk R.
Proof. exact (fun h0 : term78 Absty Repty dest mk R => @lem23786 Absty Repty dest mk R h0). Qed.
Lemma lem23788 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term79 Absty Repty dest mk R) : term79 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem23789 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term78 Absty Repty dest mk R) : term78 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem23790 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term78 Absty Repty dest mk R) (h2 : term79 Absty Repty dest mk R) : term78 Absty Repty dest mk R.
Proof. exact (@lem23788 Absty Repty dest mk R h2 (@lem23789 Absty Repty dest mk R h1)). Qed.
Lemma lem23791 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term78 Absty Repty dest mk R) : term80 Absty Repty dest mk R.
Proof. exact (fun h0 : term79 Absty Repty dest mk R => @lem23790 Absty Repty dest mk R h1 h0). Qed.
Lemma lem23792 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term79 Absty Repty dest mk R) : term79 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem23793 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term78 Absty Repty dest mk R) (h2 : term79 Absty Repty dest mk R) : term78 Absty Repty dest mk R.
Proof. exact (@lem23791 Absty Repty dest mk R h1 (@lem23792 Absty Repty dest mk R h2)). Qed.
Lemma lem23794 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term79 Absty Repty dest mk R) : term79 Absty Repty dest mk R.
Proof. exact (fun h0 : term78 Absty Repty dest mk R => @lem23793 Absty Repty dest mk R h0 h1). Qed.
Lemma lem23795 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term81 Absty Repty dest mk R.
Proof. exact (fun h0 : term79 Absty Repty dest mk R => @lem23794 Absty Repty dest mk R h0). Qed.
Lemma lem23798 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term79 Absty Repty dest mk R.
Proof. exact (@lem23795 Absty Repty dest mk R (@lem23787 Absty Repty dest mk R)). Qed.
Lemma lem23799 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term79 Absty Repty dest mk R.
Proof. exact (@lem23798 Absty Repty dest mk R). Qed.
Lemma lem23863 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem23864 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term76 Absty Repty mk R) = (term82 Absty Repty mk R).
Proof. exact (@lem23863 (term77 Absty Repty mk R)). Qed.
Lemma lem23866 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem23867 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term82 Absty Repty mk R) = (term74 Absty Repty mk R).
Proof. exact (@lem23866 (term74 Absty Repty mk R)). Qed.
Lemma lem23872 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term76 Absty Repty mk R) = (term74 Absty Repty mk R).
Proof. exact (TRANS (@lem23864 Absty Repty mk R) (@lem23867 Absty Repty mk R)). Qed.
Lemma lem23877 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (eq_refl (term84 Absty Repty R dest mk)). Qed.
Lemma lem23878 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term85 Absty Repty dest mk R) = (term86 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23877 Absty Repty R dest mk) (@lem23872 Absty Repty mk R)). Qed.
Lemma lem23881 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (eq_refl (term87 Absty Repty mk dest)). Qed.
Lemma lem23882 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term88 Absty Repty dest mk R) = (term89 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23881 Absty Repty mk dest) (@lem23878 Absty Repty dest mk R)). Qed.
Lemma lem23885 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (eq_refl (term90 Repty R)). Qed.
Lemma lem23886 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term91 Absty Repty dest mk R) = (term92 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23885 Repty R) (@lem23882 Absty Repty dest mk R)). Qed.
Lemma lem23889 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (eq_refl (term93 Repty R)). Qed.
Lemma lem23890 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term94 Absty Repty dest mk R) = (term95 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23889 Repty R) (@lem23886 Absty Repty dest mk R)). Qed.
Lemma lem23893 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (eq_refl (term96 Repty R)). Qed.
Lemma lem23894 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term78 Absty Repty dest mk R) = (term97 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23893 Repty R) (@lem23890 Absty Repty dest mk R)). Qed.
Lemma lem23897 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term98 Absty Repty mk R) = (term99 Absty Repty mk R).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem23894 Absty Repty dest mk R)). Qed.
Lemma lem23898 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem23899 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term100 Absty Repty mk R) = (term101 Absty Repty mk R).
Proof. exact (MK_COMB (@lem23898 Absty Repty) (@lem23897 Absty Repty mk R)). Qed.
Lemma lem23904 {Absty Repty : Type'} (R : type1402 Repty) : (term102 Absty Repty R) = (term103 Absty Repty R).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem23899 Absty Repty mk R)). Qed.
Lemma lem23905 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem23906 {Absty Repty : Type'} (R : type1402 Repty) : (term104 Absty Repty R) = (term105 Absty Repty R).
Proof. exact (MK_COMB (@lem23905 Absty Repty) (@lem23904 Absty Repty R)). Qed.
Lemma lem23911 {Absty Repty : Type'} : (term106 Absty Repty) = (term107 Absty Repty).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem23906 Absty Repty R)). Qed.
Lemma lem23912 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem23921 {Absty Repty : Type'} : (term108 Absty Repty) = (term109 Absty Repty).
Proof. exact (MK_COMB (@lem23912 Repty) (@lem23911 Absty Repty)). Qed.
Lemma lem23926 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))).
Proof. exact (eq_refl (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)))). Qed.
Lemma lem23927 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term111 Absty Repty mk x R) = (term111 Absty Repty mk x R).
Proof. exact (fun_ext (fun y : Repty => @lem23926 Absty Repty mk x R y)). Qed.
Lemma lem23928 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23929 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term112 Absty Repty mk x R) = (term112 Absty Repty mk x R).
Proof. exact (MK_COMB (@lem23928 Repty) (@lem23927 Absty Repty mk x R)). Qed.
Lemma lem23930 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term113 Absty Repty mk R) = (term113 Absty Repty mk R).
Proof. exact (fun_ext (fun x : Repty => @lem23929 Absty Repty mk x R)). Qed.
Lemma lem23931 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23932 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term74 Absty Repty mk R) = (term74 Absty Repty mk R).
Proof. exact (MK_COMB (@lem23931 Repty) (@lem23930 Absty Repty mk R)). Qed.
Lemma lem23933 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem23934 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem23935 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem23934 Repty r R x)). Qed.
Lemma lem23936 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem23937 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem23936 Repty) (@lem23935 Repty r R)). Qed.
Lemma lem23938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem23939 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term117 Repty r R) = (term117 Repty r R).
Proof. exact (MK_COMB (@lem23938) (@lem23937 Repty r R)). Qed.
Lemma lem23940 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)).
Proof. exact (MK_COMB (@lem23939 Repty r R) (@lem23933 Absty Repty dest mk r)). Qed.
Lemma lem23941 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term118 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem23940 Absty Repty R dest mk r)). Qed.
Lemma lem23942 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem23943 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term72 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem23942 Repty) (@lem23941 Absty Repty R dest mk)). Qed.
Lemma lem23944 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23945 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem23944) (@lem23943 Absty Repty R dest mk)). Qed.
Lemma lem23946 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term86 Absty Repty dest mk R) = (term86 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23945 Absty Repty R dest mk) (@lem23932 Absty Repty mk R)). Qed.
Lemma lem23947 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem23948 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem23947 Absty Repty mk dest a)). Qed.
Lemma lem23949 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem23950 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem23949 Absty) (@lem23948 Absty Repty mk dest)). Qed.
Lemma lem23951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23952 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem23951) (@lem23950 Absty Repty mk dest)). Qed.
Lemma lem23953 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term89 Absty Repty dest mk R) = (term89 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23952 Absty Repty mk dest) (@lem23946 Absty Repty dest mk R)). Qed.
Lemma lem23962 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term121 Repty y R x z) = (term121 Repty y R x z).
Proof. exact (eq_refl (term121 Repty y R x z)). Qed.
Lemma lem23963 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term122 Repty y R x) = (term122 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem23962 Repty y R x z)). Qed.
Lemma lem23964 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23965 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term123 Repty y R x) = (term123 Repty y R x).
Proof. exact (MK_COMB (@lem23964 Repty) (@lem23963 Repty y R x)). Qed.
Lemma lem23966 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term124 Repty R x) = (term124 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem23965 Repty y R x)). Qed.
Lemma lem23967 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23968 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term125 Repty R x) = (term125 Repty R x).
Proof. exact (MK_COMB (@lem23967 Repty) (@lem23966 Repty R x)). Qed.
Lemma lem23969 {Repty : Type'} (R : type1402 Repty) : (term126 Repty R) = (term126 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem23968 Repty R x)). Qed.
Lemma lem23970 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23971 {Repty : Type'} (R : type1402 Repty) : (term71 Repty R) = (term71 Repty R).
Proof. exact (MK_COMB (@lem23970 Repty) (@lem23969 Repty R)). Qed.
Lemma lem23972 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23973 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (MK_COMB (@lem23972) (@lem23971 Repty R)). Qed.
Lemma lem23974 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term92 Absty Repty dest mk R) = (term92 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23973 Repty R) (@lem23953 Absty Repty dest mk R)). Qed.
Lemma lem23979 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : ((R x y) = (R y x)) = ((R x y) = (R y x)).
Proof. exact (eq_refl ((R x y) = (R y x))). Qed.
Lemma lem23980 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term127 Repty R x) = (term127 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem23979 Repty R y x)). Qed.
Lemma lem23981 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23982 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term128 Repty R x) = (term128 Repty R x).
Proof. exact (MK_COMB (@lem23981 Repty) (@lem23980 Repty R x)). Qed.
Lemma lem23983 {Repty : Type'} (R : type1402 Repty) : (term129 Repty R) = (term129 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem23982 Repty R x)). Qed.
Lemma lem23984 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23985 {Repty : Type'} (R : type1402 Repty) : (term69 Repty R) = (term69 Repty R).
Proof. exact (MK_COMB (@lem23984 Repty) (@lem23983 Repty R)). Qed.
Lemma lem23986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23987 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (MK_COMB (@lem23986) (@lem23985 Repty R)). Qed.
Lemma lem23988 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term95 Absty Repty dest mk R) = (term95 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23987 Repty R) (@lem23974 Absty Repty dest mk R)). Qed.
Lemma lem23989 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem23990 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term130 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem23989 Repty R x)). Qed.
Lemma lem23991 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem23992 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term67 Repty R).
Proof. exact (MK_COMB (@lem23991 Repty) (@lem23990 Repty R)). Qed.
Lemma lem23993 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem23994 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (MK_COMB (@lem23993) (@lem23992 Repty R)). Qed.
Lemma lem23995 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term97 Absty Repty dest mk R) = (term97 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem23994 Repty R) (@lem23988 Absty Repty dest mk R)). Qed.
Lemma lem23996 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term99 Absty Repty mk R) = (term99 Absty Repty mk R).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem23995 Absty Repty dest mk R)). Qed.
Lemma lem23997 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem23998 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term101 Absty Repty mk R) = (term101 Absty Repty mk R).
Proof. exact (MK_COMB (@lem23997 Absty Repty) (@lem23996 Absty Repty mk R)). Qed.
Lemma lem23999 {Absty Repty : Type'} (R : type1402 Repty) : (term103 Absty Repty R) = (term103 Absty Repty R).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem23998 Absty Repty mk R)). Qed.
Lemma lem24000 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem24001 {Absty Repty : Type'} (R : type1402 Repty) : (term105 Absty Repty R) = (term105 Absty Repty R).
Proof. exact (MK_COMB (@lem24000 Absty Repty) (@lem23999 Absty Repty R)). Qed.
Lemma lem24002 {Absty Repty : Type'} : (term107 Absty Repty) = (term107 Absty Repty).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem24001 Absty Repty R)). Qed.
Lemma lem24003 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem24004 {Absty Repty : Type'} : (term109 Absty Repty) = (term109 Absty Repty).
Proof. exact (MK_COMB (@lem24003 Repty) (@lem24002 Absty Repty)). Qed.
Lemma lem24105 {Absty Repty : Type'} : (term108 Absty Repty) = (term109 Absty Repty).
Proof. exact (TRANS (@lem23921 Absty Repty) (@lem24004 Absty Repty)). Qed.
Lemma lem24106 {Absty Repty : Type'} : (term109 Absty Repty) = (term108 Absty Repty).
Proof. exact (SYM (@lem24105 Absty Repty)). Qed.
Lemma lem24111 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term72 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem24113 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem24114 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))) = (term131 Absty Repty mk x R y).
Proof. exact (@lem24113 (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)))). Qed.
Lemma lem24115 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term131 Absty Repty mk x R y) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))).
Proof. exact (SYM (@lem24114 Absty Repty mk x R y)). Qed.
Lemma lem24116 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term132 Absty Repty mk x R y) : term132 Absty Repty mk x R y.
Proof. exact (h1). Qed.
Lemma lem24514 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem24515 {Repty : Type'} (P : Repty -> Prop) : (term133 Repty P) = (term134 Repty P).
Proof. exact (@lem18394 Repty P). Qed.
Lemma lem24516 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term136 Repty r R).
Proof. exact (@lem24515 Repty (term115 Repty r R)). Qed.
Lemma lem24517 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem24518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem24520 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term138 Repty r R x) = (term139 Repty r R x).
Proof. exact (MK_COMB (@lem24518) (@lem24517 Repty r R x)). Qed.
Lemma lem24521 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term140 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem24520 Repty r R x)). Qed.
Lemma lem24522 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem24523 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term136 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem24522 Repty) (@lem24521 Repty r R)). Qed.
Lemma lem24524 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term142 Repty r R).
Proof. exact (TRANS (@lem24516 Repty r R) (@lem24523 Repty r R)). Qed.
Lemma lem24525 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem24514 Repty r R x)). Qed.
Lemma lem24526 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem24527 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem24526 Repty) (@lem24525 Repty r R)). Qed.
Lemma lem24528 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem24529 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem24530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem24531 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term144 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem24530) (@lem24524 Repty r R)). Qed.
Lemma lem24532 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term146 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24531 Repty r R) (@lem24529 Absty Repty dest mk r)). Qed.
Lemma lem24533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem24534 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term148 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem24533) (@lem24527 Repty r R)). Qed.
Lemma lem24535 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24534 Repty r R) (@lem24528 Absty Repty dest mk r)). Qed.
Lemma lem24536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem24537 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term150 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24536) (@lem24535 Absty Repty R dest mk r)). Qed.
Lemma lem24538 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term151 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24537 Absty Repty R dest mk r) (@lem24532 Absty Repty R dest mk r)). Qed.
Lemma lem24539 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term151 Absty Repty R dest mk r).
Proof. exact (@lem17784 (term116 Repty r R) ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem24540 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term152 Absty Repty R dest mk r).
Proof. exact (TRANS (@lem24539 Absty Repty R dest mk r) (@lem24538 Absty Repty R dest mk r)). Qed.
Lemma lem24541 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem24540 Absty Repty R dest mk r)). Qed.
Lemma lem24542 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem24543 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24542 Repty) (@lem24541 Absty Repty R dest mk)). Qed.
Lemma lem24545 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem24546 {Repty : Type'} (P : type686 Repty) (Q : type686 Repty) : (term157 Repty P Q) = (term158 Repty P Q).
Proof. exact (@lem24545 (Repty -> Prop) P Q). Qed.
Lemma lem24547 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk).
Proof. exact (@lem24546 Repty (term161 Absty Repty R dest mk) (term162 Absty Repty R dest mk)). Qed.
Lemma lem24548 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem24549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem24550 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term164 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24549) (@lem24548 Absty Repty R dest mk r)). Qed.
Lemma lem24551 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem24552 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term166 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24550 Absty Repty R dest mk r) (@lem24551 Absty Repty R dest mk r)). Qed.
Lemma lem24553 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term167 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem24552 Absty Repty R dest mk r)). Qed.
Lemma lem24554 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem24555 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24554 Repty) (@lem24553 Absty Repty R dest mk)). Qed.
Lemma lem24556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem24557 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term168 Absty Repty R dest mk) = (term169 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24556) (@lem24555 Absty Repty R dest mk)). Qed.
Lemma lem24558 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem24559 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term170 Absty Repty R dest mk) = (term161 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem24558 Absty Repty R dest mk r)). Qed.
Lemma lem24560 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem24561 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term171 Absty Repty R dest mk) = (term172 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24560 Repty) (@lem24559 Absty Repty R dest mk)). Qed.
Lemma lem24562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem24563 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term173 Absty Repty R dest mk) = (term174 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24562) (@lem24561 Absty Repty R dest mk)). Qed.
Lemma lem24564 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem24565 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term175 Absty Repty R dest mk) = (term162 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem24564 Absty Repty R dest mk r)). Qed.
Lemma lem24566 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem24567 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term176 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24566 Repty) (@lem24565 Absty Repty R dest mk)). Qed.
Lemma lem24568 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term160 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24563 Absty Repty R dest mk) (@lem24567 Absty Repty R dest mk)). Qed.
Lemma lem24569 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk)) = ((term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem24557 Absty Repty R dest mk) (@lem24568 Absty Repty R dest mk)). Qed.
Lemma lem24570 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem24569 Absty Repty R dest mk) (@lem24547 Absty Repty R dest mk)). Qed.
Lemma lem24676 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem24677 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem24676 Repty P Q). Qed.
Lemma lem24678 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r).
Proof. exact (@lem24677 Repty (term115 Repty r R) (term143 Absty Repty dest mk r)). Qed.
Lemma lem24679 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem24680 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term183 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem24679 Repty r R x)). Qed.
Lemma lem24681 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem24682 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term184 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem24681 Repty) (@lem24680 Repty r R)). Qed.
Lemma lem24683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem24684 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term185 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem24683) (@lem24682 Repty r R)). Qed.
Lemma lem24685 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem24686 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24684 Repty r R) (@lem24685 Absty Repty dest mk r)). Qed.
Lemma lem24687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem24688 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term186 Absty Repty R dest mk r) = (term187 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24687) (@lem24686 Absty Repty R dest mk r)). Qed.
Lemma lem24689 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem24690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem24691 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term188 Repty r R x) = (term189 Repty r R x).
Proof. exact (MK_COMB (@lem24690) (@lem24689 Repty r R x)). Qed.
Lemma lem24692 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem24693 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term190 Absty Repty R x dest mk r) = (term191 Absty Repty R x dest mk r).
Proof. exact (MK_COMB (@lem24691 Repty r R x) (@lem24692 Absty Repty dest mk r)). Qed.
Lemma lem24694 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term192 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem24693 Absty Repty R x dest mk r)). Qed.
Lemma lem24695 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem24696 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term182 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24695 Repty) (@lem24694 Absty Repty R dest mk r)). Qed.
Lemma lem24697 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r)) = ((term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r)).
Proof. exact (MK_COMB (@lem24688 Absty Repty R dest mk r) (@lem24696 Absty Repty R dest mk r)). Qed.
Lemma lem24698 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (EQ_MP (@lem24697 Absty Repty R dest mk r) (@lem24678 Absty Repty R dest mk r)). Qed.
Lemma lem24699 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term161 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem24698 Absty Repty R dest mk r)). Qed.
Lemma lem24700 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem24701 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24700 Repty) (@lem24699 Absty Repty R dest mk)). Qed.
Lemma lem24703 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem24704 {Repty : Type'} (P : type672 Repty) : (term199 Repty P) = (term200 Repty P).
Proof. exact (@lem24703 (Repty -> Prop) Repty P). Qed.
Lemma lem24705 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk).
Proof. exact (@lem24704 Repty (term203 Absty Repty R dest mk)). Qed.
Lemma lem24706 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem24707 {Repty : Type'} (x : Repty) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem24708 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) (x : Repty) : (term205 Absty Repty R dest mk r x) = (term206 Absty Repty R dest mk r x).
Proof. exact (MK_COMB (@lem24706 Absty Repty R dest mk r) (@lem24707 Repty x)). Qed.
Lemma lem24709 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term206 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term206 Absty Repty R dest mk r x)). Qed.
Lemma lem24710 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term205 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem24708 Absty Repty R dest mk r x) (@lem24709 Absty Repty R x dest mk r)). Qed.
Lemma lem24711 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term207 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem24710 Absty Repty R x dest mk r)). Qed.
Lemma lem24712 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem24713 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term208 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem24712 Repty) (@lem24711 Absty Repty R dest mk r)). Qed.
Lemma lem24714 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term209 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem24713 Absty Repty R dest mk r)). Qed.
Lemma lem24715 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem24716 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24715 Repty) (@lem24714 Absty Repty R dest mk)). Qed.
Lemma lem24717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem24718 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term210 Absty Repty R dest mk) = (term211 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24717) (@lem24716 Absty Repty R dest mk)). Qed.
Lemma lem24719 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem24720 {Repty : Type'} (x : type684 Repty) (r : Repty -> Prop) : (x r) = (x r).
Proof. exact (eq_refl (x r)). Qed.
Lemma lem24721 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : type684 Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term213 Absty Repty R dest mk x r).
Proof. exact (MK_COMB (@lem24719 Absty Repty R dest mk r) (@lem24720 Repty x r)). Qed.
Lemma lem24722 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term213 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term213 Absty Repty R dest mk x r)). Qed.
Lemma lem24723 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem24721 Absty Repty R dest mk x r) (@lem24722 Absty Repty R x dest mk r)). Qed.
Lemma lem24724 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term215 Absty Repty R dest mk x) = (term216 Absty Repty R x dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem24723 Absty Repty R x dest mk r)). Qed.
Lemma lem24725 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem24726 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term217 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem24725 Repty) (@lem24724 Absty Repty R x dest mk)). Qed.
Lemma lem24727 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term219 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem24726 Absty Repty R x dest mk)). Qed.
Lemma lem24728 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem24729 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term202 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24728 Repty) (@lem24727 Absty Repty R dest mk)). Qed.
Lemma lem24730 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk)) = ((term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem24718 Absty Repty R dest mk) (@lem24729 Absty Repty R dest mk)). Qed.
Lemma lem24731 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem24730 Absty Repty R dest mk) (@lem24705 Absty Repty R dest mk)). Qed.
Lemma lem24732 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (TRANS (@lem24701 Absty Repty R dest mk) (@lem24731 Absty Repty R dest mk)). Qed.
Lemma lem24733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem24734 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term174 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24733) (@lem24732 Absty Repty R dest mk)). Qed.
Lemma lem24735 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem24736 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24734 Absty Repty R dest mk) (@lem24735 Absty Repty R dest mk)). Qed.
Lemma lem24738 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem24739 {Repty : Type'} (P : type162 Repty) (Q : Prop) : (term226 Repty P Q) = (term227 Repty P Q).
Proof. exact (@lem24738 (type684 Repty) P Q). Qed.
Lemma lem24740 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk).
Proof. exact (@lem24739 Repty (term220 Absty Repty R dest mk) (term177 Absty Repty R dest mk)). Qed.
Lemma lem24741 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem24742 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term231 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem24741 Absty Repty R x dest mk)). Qed.
Lemma lem24743 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem24744 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term232 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24743 Repty) (@lem24742 Absty Repty R dest mk)). Qed.
Lemma lem24745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem24746 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term233 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24745) (@lem24744 Absty Repty R dest mk)). Qed.
Lemma lem24747 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem24748 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24746 Absty Repty R dest mk) (@lem24747 Absty Repty R dest mk)). Qed.
Lemma lem24749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem24750 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term234 Absty Repty R dest mk) = (term235 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24749) (@lem24748 Absty Repty R dest mk)). Qed.
Lemma lem24751 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem24752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem24753 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term236 Absty Repty R dest mk x) = (term237 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem24752) (@lem24751 Absty Repty R x dest mk)). Qed.
Lemma lem24754 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem24755 {Absty Repty : Type'} (x : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term238 Absty Repty x R dest mk) = (term239 Absty Repty x R dest mk).
Proof. exact (MK_COMB (@lem24753 Absty Repty R x dest mk) (@lem24754 Absty Repty R dest mk)). Qed.
Lemma lem24756 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term240 Absty Repty R dest mk) = (term241 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem24755 Absty Repty x R dest mk)). Qed.
Lemma lem24757 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem24758 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term229 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem24757 Repty) (@lem24756 Absty Repty R dest mk)). Qed.
Lemma lem24759 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk)) = ((term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem24750 Absty Repty R dest mk) (@lem24758 Absty Repty R dest mk)). Qed.
Lemma lem24760 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem24759 Absty Repty R dest mk) (@lem24740 Absty Repty R dest mk)). Qed.
Lemma lem24761 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem24736 Absty Repty R dest mk) (@lem24760 Absty Repty R dest mk)). Qed.
Lemma lem24762 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem24570 Absty Repty R dest mk) (@lem24761 Absty Repty R dest mk)). Qed.
Lemma lem24763 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem24543 Absty Repty R dest mk) (@lem24762 Absty Repty R dest mk)). Qed.
Lemma lem24764 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term242 Absty Repty R dest mk.
Proof. exact (EQ_MP (@lem24763 Absty Repty R dest mk) (@lem24111 Absty Repty R dest mk h1)). Qed.
Lemma lem24783 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term132 Absty Repty mk x R y) = (term243 Absty Repty mk x R y).
Proof. exact (@lem17646 ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) ((R x) = (R y))). Qed.
Lemma lem24785 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term239 Absty Repty x' R dest mk.
Proof. exact (h1). Qed.
Lemma lem24986 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term132 Absty Repty mk x R y) : term243 Absty Repty mk x R y.
Proof. exact (EQ_MP (@lem24783 Absty Repty mk x R y) (@lem24116 Absty Repty mk x R y h1)). Qed.
Lemma lem24995 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem25004 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term139 Repty r R x) = (term139 Repty r R x).
Proof. exact (eq_refl (term139 Repty r R x)). Qed.
Lemma lem25005 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term141 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem25004 Repty r R x)). Qed.
Lemma lem25006 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem25007 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term142 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem25006 Repty) (@lem25005 Repty r R)). Qed.
Lemma lem25008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem25009 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term145 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem25008) (@lem25007 Repty r R)). Qed.
Lemma lem25010 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term147 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem25009 Repty r R) (@lem24995 Absty Repty dest mk r)). Qed.
Lemma lem25011 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term162 Absty Repty R dest mk) = (term162 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem25010 Absty Repty R dest mk r)). Qed.
Lemma lem25012 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem25013 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem25012 Repty) (@lem25011 Absty Repty R dest mk)). Qed.
Lemma lem25036 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term214 Absty Repty R x' dest mk r) = (term214 Absty Repty R x' dest mk r).
Proof. exact (eq_refl (term214 Absty Repty R x' dest mk r)). Qed.
Lemma lem25037 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term216 Absty Repty R x' dest mk) = (term216 Absty Repty R x' dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem25036 Absty Repty R x' dest mk r)). Qed.
Lemma lem25038 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem25039 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term218 Absty Repty R x' dest mk) = (term218 Absty Repty R x' dest mk).
Proof. exact (MK_COMB (@lem25038 Repty) (@lem25037 Absty Repty R x' dest mk)). Qed.
Lemma lem25040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem25041 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term237 Absty Repty R x' dest mk) = (term237 Absty Repty R x' dest mk).
Proof. exact (MK_COMB (@lem25040) (@lem25039 Absty Repty R x' dest mk)). Qed.
Lemma lem25042 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term239 Absty Repty x' R dest mk) = (term239 Absty Repty x' R dest mk).
Proof. exact (MK_COMB (@lem25041 Absty Repty R x' dest mk) (@lem25013 Absty Repty R dest mk)). Qed.
Lemma lem25043 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term239 Absty Repty x' R dest mk.
Proof. exact (EQ_MP (@lem25042 Absty Repty x' R dest mk) (@lem24785 Absty Repty x' R dest mk h1)). Qed.
Lemma lem25044 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term177 Absty Repty R dest mk.
Proof. exact (proj2 (@lem25043 Absty Repty x' R dest mk h1)). Qed.
Lemma lem25048 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : term244 Absty Repty mk x R y.
Proof. exact (h1). Qed.
Lemma lem25049 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : term245 Absty Repty mk x R y.
Proof. exact (h1). Qed.
Lemma lem25107 {A : Type'} (P : A -> Prop) (Q : Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem25108 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term246 Repty P Q) = (term247 Repty P Q).
Proof. exact (@lem25107 Repty P Q). Qed.
Lemma lem25109 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term248 Absty Repty R dest mk r) = (term249 Absty Repty R dest mk r).
Proof. exact (@lem25108 Repty (term141 Repty r R) ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem25110 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term250 Repty r R x) = (term139 Repty r R x).
Proof. exact (eq_refl (term250 Repty r R x)). Qed.
Lemma lem25111 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term251 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem25110 Repty r R x)). Qed.
Lemma lem25112 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem25113 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term252 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem25112 Repty) (@lem25111 Repty r R)). Qed.
Lemma lem25114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem25115 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term253 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem25114) (@lem25113 Repty r R)). Qed.
Lemma lem25116 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem25117 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term248 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem25115 Repty r R) (@lem25116 Absty Repty dest mk r)). Qed.
Lemma lem25118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem25119 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term254 Absty Repty R dest mk r) = (term255 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem25118) (@lem25117 Absty Repty R dest mk r)). Qed.
Lemma lem25120 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term250 Repty r R x) = (term139 Repty r R x).
Proof. exact (eq_refl (term250 Repty r R x)). Qed.
Lemma lem25121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem25122 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term256 Repty r R x) = (term257 Repty r R x).
Proof. exact (MK_COMB (@lem25121) (@lem25120 Repty r R x)). Qed.
Lemma lem25123 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem25124 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term258 Absty Repty R x dest mk r) = (term259 Absty Repty R x dest mk r).
Proof. exact (MK_COMB (@lem25122 Repty r R x) (@lem25123 Absty Repty dest mk r)). Qed.
Lemma lem25125 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term260 Absty Repty R dest mk r) = (term261 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem25124 Absty Repty R x dest mk r)). Qed.
Lemma lem25126 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem25127 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term249 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem25126 Repty) (@lem25125 Absty Repty R dest mk r)). Qed.
Lemma lem25128 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term248 Absty Repty R dest mk r) = (term249 Absty Repty R dest mk r)) = ((term147 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r)).
Proof. exact (MK_COMB (@lem25119 Absty Repty R dest mk r) (@lem25127 Absty Repty R dest mk r)). Qed.
Lemma lem25129 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term147 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r).
Proof. exact (EQ_MP (@lem25128 Absty Repty R dest mk r) (@lem25109 Absty Repty R dest mk r)). Qed.
Lemma lem25130 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term162 Absty Repty R dest mk) = (term263 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem25129 Absty Repty R dest mk r)). Qed.
Lemma lem25131 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem25132 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term264 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem25131 Repty) (@lem25130 Absty Repty R dest mk)). Qed.
Lemma lem25139 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term259 Absty Repty R x dest mk r) = (term259 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term259 Absty Repty R x dest mk r)). Qed.
Lemma lem25140 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term261 Absty Repty R dest mk r) = (term261 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem25139 Absty Repty R x dest mk r)). Qed.
Lemma lem25141 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem25142 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term262 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem25141 Repty) (@lem25140 Absty Repty R dest mk r)). Qed.
Lemma lem25143 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term263 Absty Repty R dest mk) = (term263 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem25142 Absty Repty R dest mk r)). Qed.
Lemma lem25144 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem25145 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term264 Absty Repty R dest mk) = (term264 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem25144 Repty) (@lem25143 Absty Repty R dest mk)). Qed.
Lemma lem25146 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term264 Absty Repty R dest mk).
Proof. exact (TRANS (@lem25132 Absty Repty R dest mk) (@lem25145 Absty Repty R dest mk)). Qed.
Lemma lem25147 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term264 Absty Repty R dest mk.
Proof. exact (EQ_MP (@lem25146 Absty Repty R dest mk) (@lem25044 Absty Repty x' R dest mk h1)). Qed.
Lemma lem25340 {Absty Repty : Type'} (_704 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term265 Absty Repty R dest mk _704.
Proof. exact (@lem25147 Absty Repty x' R dest mk h1 _704). Qed.
Lemma lem25341 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) : (term265 Absty Repty R dest mk _704) = (term262 Absty Repty R dest mk _704).
Proof. exact (eq_refl (term265 Absty Repty R dest mk _704)). Qed.
Lemma lem25342 {Absty Repty : Type'} (_704 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term262 Absty Repty R dest mk _704.
Proof. exact (EQ_MP (@lem25341 Absty Repty R dest mk _704) (@lem25340 Absty Repty _704 x' R dest mk h1)). Qed.
Lemma lem25343 {Absty Repty : Type'} (_704 : Repty -> Prop) (_705 : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term266 Absty Repty R dest mk _704 _705.
Proof. exact (@lem25342 Absty Repty _704 x' R dest mk h1 _705). Qed.
Lemma lem25344 {Absty Repty : Type'} (R : type1402 Repty) (_705 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) : (term266 Absty Repty R dest mk _704 _705) = (term259 Absty Repty R _705 dest mk _704).
Proof. exact (eq_refl (term266 Absty Repty R dest mk _704 _705)). Qed.
Lemma lem25421 {Absty Repty : Type'} (_705 : Repty) (_704 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term259 Absty Repty R _705 dest mk _704.
Proof. exact (EQ_MP (@lem25344 Absty Repty R _705 dest mk _704) (@lem25343 Absty Repty _704 _705 x' R dest mk h1)). Qed.
Lemma lem25437 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : term267 Repty x R y.
Proof. exact (proj2 (@lem25048 Absty Repty mk x R y h1)). Qed.
Lemma lem25479 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : term268 Absty Repty x mk R y.
Proof. exact (proj1 (@lem25049 Absty Repty mk x R y h1)). Qed.
Lemma lem25509 {Absty Repty : Type'} (dest : type1413 Absty Repty) : dest = dest.
Proof. exact (eq_refl dest). Qed.
Lemma lem25510 {Absty : Type'} (_728 : Absty) (_729 : Absty) (h1 : _728 = _729) : _728 = _729.
Proof. exact (h1). Qed.
Lemma lem25511 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) (h1 : _728 = _729) : (dest _728) = (dest _729).
Proof. exact (MK_COMB (@lem25509 Absty Repty dest) (@lem25510 Absty _728 _729 h1)). Qed.
Lemma lem25512 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : term269 Absty Repty _728 dest _729.
Proof. exact (fun h0 : _728 = _729 => @lem25511 Absty Repty dest _728 _729 h0). Qed.
Lemma lem25514 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem25515 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : (term269 Absty Repty _728 dest _729) = (term271 Absty Repty _728 dest _729).
Proof. exact (@lem25514 (_728 = _729) ((dest _728) = (dest _729))). Qed.
Lemma lem25516 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : term271 Absty Repty _728 dest _729.
Proof. exact (EQ_MP (@lem25515 Absty Repty _728 dest _729) (@lem25512 Absty Repty _728 dest _729)). Qed.
Lemma lem25534 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : term272 Repty x y z.
Proof. exact (@lem21385 (Repty -> Prop) x y z). Qed.
Lemma lem25540 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : (term110 Absty Repty mk R x) = (term110 Absty Repty mk R y).
Proof. exact (proj1 (@lem25048 Absty Repty mk x R y h1)). Qed.
Lemma lem25541 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : term273 Absty Repty x mk R y.
Proof. exact (fun h0 : term268 Absty Repty x mk R y => @lem25540 Absty Repty mk x R y h1). Qed.
Lemma lem25543 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25544 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) : (term273 Absty Repty x mk R y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)).
Proof. exact (@lem25543 ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y))). Qed.
Lemma lem25545 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : (term110 Absty Repty mk R x) = (term110 Absty Repty mk R y).
Proof. exact (EQ_MP (@lem25544 Absty Repty x mk R y) (@lem25541 Absty Repty mk x R y h1)). Qed.
Lemma lem25551 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem25552 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : (term271 Absty Repty _728 dest _729) = (term275 Absty Repty dest _728 _729).
Proof. exact (@lem25551 ((dest _728) = (dest _729)) (term276 Absty _728 _729)). Qed.
Lemma lem25562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem25563 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : (term277 Absty Repty _728 dest _729) = (term278 Absty Repty dest _728 _729).
Proof. exact (MK_COMB (@lem25562) (@lem25552 Absty Repty dest _728 _729)). Qed.
Lemma lem25573 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : (term275 Absty Repty dest _728 _729) = (term275 Absty Repty dest _728 _729).
Proof. exact (eq_refl (term275 Absty Repty dest _728 _729)). Qed.
Lemma lem25574 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : ((term271 Absty Repty _728 dest _729) = (term275 Absty Repty dest _728 _729)) = ((term275 Absty Repty dest _728 _729) = (term275 Absty Repty dest _728 _729)).
Proof. exact (MK_COMB (@lem25563 Absty Repty dest _728 _729) (@lem25573 Absty Repty dest _728 _729)). Qed.
Lemma lem25576 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem25577 (x : Prop) : (x = x) = True.
Proof. exact (@lem25576 Prop x). Qed.
Lemma lem25578 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : ((term275 Absty Repty dest _728 _729) = (term275 Absty Repty dest _728 _729)) = True.
Proof. exact (@lem25577 (term275 Absty Repty dest _728 _729)). Qed.
Lemma lem25579 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : ((term271 Absty Repty _728 dest _729) = (term275 Absty Repty dest _728 _729)) = True.
Proof. exact (TRANS (@lem25574 Absty Repty dest _728 _729) (@lem25578 Absty Repty dest _728 _729)). Qed.
Lemma lem25580 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : True = ((term271 Absty Repty _728 dest _729) = (term275 Absty Repty dest _728 _729)).
Proof. exact (SYM (@lem25579 Absty Repty dest _728 _729)). Qed.
Lemma lem25581 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : (term271 Absty Repty _728 dest _729) = (term275 Absty Repty dest _728 _729).
Proof. exact (EQ_MP (@lem25580 Absty Repty dest _728 _729) (@lem0)). Qed.
Lemma lem25582 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_728 : Absty) (_729 : Absty) : term275 Absty Repty dest _728 _729.
Proof. exact (EQ_MP (@lem25581 Absty Repty dest _728 _729) (@lem25516 Absty Repty _728 dest _729)). Qed.
Lemma lem25584 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem25585 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : (term275 Absty Repty dest _728 _729) = (term280 Absty Repty _728 dest _729).
Proof. exact (@lem25584 (term276 Absty _728 _729) ((dest _728) = (dest _729))). Qed.
Lemma lem25587 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem25588 {Absty : Type'} (_728 : Absty) (_729 : Absty) : (term281 Absty _728 _729) = (_728 = _729).
Proof. exact (@lem25587 (_728 = _729)). Qed.
Lemma lem25589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem25590 {Absty : Type'} (_728 : Absty) (_729 : Absty) : (term282 Absty _728 _729) = (term283 Absty _728 _729).
Proof. exact (MK_COMB (@lem25589) (@lem25588 Absty _728 _729)). Qed.
Lemma lem25591 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : ((dest _728) = (dest _729)) = ((dest _728) = (dest _729)).
Proof. exact (eq_refl ((dest _728) = (dest _729))). Qed.
Lemma lem25592 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : (term280 Absty Repty _728 dest _729) = (term269 Absty Repty _728 dest _729).
Proof. exact (MK_COMB (@lem25590 Absty _728 _729) (@lem25591 Absty Repty _728 dest _729)). Qed.
Lemma lem25593 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : (term275 Absty Repty dest _728 _729) = (term269 Absty Repty _728 dest _729).
Proof. exact (TRANS (@lem25585 Absty Repty _728 dest _729) (@lem25592 Absty Repty _728 dest _729)). Qed.
Lemma lem25596 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : term269 Absty Repty _728 dest _729.
Proof. exact (EQ_MP (@lem25593 Absty Repty _728 dest _729) (@lem25582 Absty Repty dest _728 _729)). Qed.
Lemma lem25597 {Absty Repty : Type'} (_728 : Absty) (dest : type1413 Absty Repty) (_729 : Absty) : term269 Absty Repty _728 dest _729.
Proof. exact (@lem25596 Absty Repty _728 dest _729). Qed.
Lemma lem25598 {Absty Repty : Type'} (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) : term284 Absty Repty x dest mk R y.
Proof. exact (@lem25597 Absty Repty (term110 Absty Repty mk R x) dest (term110 Absty Repty mk R y)). Qed.
Lemma lem25601 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : (term285 Absty Repty dest mk R x) = (term285 Absty Repty dest mk R y).
Proof. exact (@lem25598 Absty Repty x dest mk R y (@lem25545 Absty Repty mk x R y h1)). Qed.
Lemma lem25602 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : term286 Absty Repty x dest mk R y.
Proof. exact (fun h0 : term287 Absty Repty x dest mk R y => @lem25601 Absty Repty dest mk x R y h1). Qed.
Lemma lem25604 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25605 {Absty Repty : Type'} (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) : (term286 Absty Repty x dest mk R y) = ((term285 Absty Repty dest mk R x) = (term285 Absty Repty dest mk R y)).
Proof. exact (@lem25604 ((term285 Absty Repty dest mk R x) = (term285 Absty Repty dest mk R y))). Qed.
Lemma lem25606 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : (term285 Absty Repty dest mk R x) = (term285 Absty Repty dest mk R y).
Proof. exact (EQ_MP (@lem25605 Absty Repty x dest mk R y) (@lem25602 Absty Repty dest mk x R y h1)). Qed.
Lemma lem25608 {Repty : Type'} (x : Repty -> Prop) : x = x.
Proof. exact (@lem21386 (Repty -> Prop) x). Qed.
Lemma lem25609 {Repty : Type'} (x : Repty -> Prop) : x = x.
Proof. exact (@lem25608 Repty x). Qed.
Lemma lem25610 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x) = (R x).
Proof. exact (@lem25609 Repty (R x)). Qed.
Lemma lem25611 {Repty : Type'} (R : type1402 Repty) (x : Repty) : term288 Repty R x.
Proof. exact (fun h0 : term289 Repty R x => @lem25610 Repty R x). Qed.
Lemma lem25613 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25614 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term288 Repty R x) = ((R x) = (R x)).
Proof. exact (@lem25613 ((R x) = (R x))). Qed.
Lemma lem25615 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x) = (R x).
Proof. exact (EQ_MP (@lem25614 Repty R x) (@lem25611 Repty R x)). Qed.
Lemma lem25621 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem25622 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : (term259 Absty Repty R _705 dest mk _704) = (term290 Absty Repty dest mk _704 R _705).
Proof. exact (@lem25621 ((term114 Absty Repty dest mk _704) = _704) (term139 Repty _704 R _705)). Qed.
Lemma lem25632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem25633 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : (term291 Absty Repty R _705 dest mk _704) = (term292 Absty Repty dest mk _704 R _705).
Proof. exact (MK_COMB (@lem25632) (@lem25622 Absty Repty dest mk _704 R _705)). Qed.
Lemma lem25643 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : (term290 Absty Repty dest mk _704 R _705) = (term290 Absty Repty dest mk _704 R _705).
Proof. exact (eq_refl (term290 Absty Repty dest mk _704 R _705)). Qed.
Lemma lem25644 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : ((term259 Absty Repty R _705 dest mk _704) = (term290 Absty Repty dest mk _704 R _705)) = ((term290 Absty Repty dest mk _704 R _705) = (term290 Absty Repty dest mk _704 R _705)).
Proof. exact (MK_COMB (@lem25633 Absty Repty dest mk _704 R _705) (@lem25643 Absty Repty dest mk _704 R _705)). Qed.
Lemma lem25646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem25647 (x : Prop) : (x = x) = True.
Proof. exact (@lem25646 Prop x). Qed.
Lemma lem25648 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : ((term290 Absty Repty dest mk _704 R _705) = (term290 Absty Repty dest mk _704 R _705)) = True.
Proof. exact (@lem25647 (term290 Absty Repty dest mk _704 R _705)). Qed.
Lemma lem25649 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : ((term259 Absty Repty R _705 dest mk _704) = (term290 Absty Repty dest mk _704 R _705)) = True.
Proof. exact (TRANS (@lem25644 Absty Repty dest mk _704 R _705) (@lem25648 Absty Repty dest mk _704 R _705)). Qed.
Lemma lem25650 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : True = ((term259 Absty Repty R _705 dest mk _704) = (term290 Absty Repty dest mk _704 R _705)).
Proof. exact (SYM (@lem25649 Absty Repty dest mk _704 R _705)). Qed.
Lemma lem25651 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : (term259 Absty Repty R _705 dest mk _704) = (term290 Absty Repty dest mk _704 R _705).
Proof. exact (EQ_MP (@lem25650 Absty Repty dest mk _704 R _705) (@lem0)). Qed.
Lemma lem25652 {Absty Repty : Type'} (_704 : Repty -> Prop) (_705 : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term290 Absty Repty dest mk _704 R _705.
Proof. exact (EQ_MP (@lem25651 Absty Repty dest mk _704 R _705) (@lem25421 Absty Repty _705 _704 x' R dest mk h1)). Qed.
Lemma lem25654 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem25655 {Absty Repty : Type'} (R : type1402 Repty) (_705 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) : (term290 Absty Repty dest mk _704 R _705) = (term293 Absty Repty R _705 dest mk _704).
Proof. exact (@lem25654 (term139 Repty _704 R _705) ((term114 Absty Repty dest mk _704) = _704)). Qed.
Lemma lem25657 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem25658 {Repty : Type'} (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : (term294 Repty _704 R _705) = (_704 = (R _705)).
Proof. exact (@lem25657 (_704 = (R _705))). Qed.
Lemma lem25659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem25660 {Repty : Type'} (_704 : Repty -> Prop) (R : type1402 Repty) (_705 : Repty) : (term295 Repty _704 R _705) = (term296 Repty _704 R _705).
Proof. exact (MK_COMB (@lem25659) (@lem25658 Repty _704 R _705)). Qed.
Lemma lem25661 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) : ((term114 Absty Repty dest mk _704) = _704) = ((term114 Absty Repty dest mk _704) = _704).
Proof. exact (eq_refl ((term114 Absty Repty dest mk _704) = _704)). Qed.
Lemma lem25662 {Absty Repty : Type'} (R : type1402 Repty) (_705 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) : (term293 Absty Repty R _705 dest mk _704) = (term297 Absty Repty R _705 dest mk _704).
Proof. exact (MK_COMB (@lem25660 Repty _704 R _705) (@lem25661 Absty Repty dest mk _704)). Qed.
Lemma lem25663 {Absty Repty : Type'} (R : type1402 Repty) (_705 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_704 : Repty -> Prop) : (term290 Absty Repty dest mk _704 R _705) = (term297 Absty Repty R _705 dest mk _704).
Proof. exact (TRANS (@lem25655 Absty Repty R _705 dest mk _704) (@lem25662 Absty Repty R _705 dest mk _704)). Qed.
Lemma lem25666 {Absty Repty : Type'} (_705 : Repty) (_704 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term297 Absty Repty R _705 dest mk _704.
Proof. exact (EQ_MP (@lem25663 Absty Repty R _705 dest mk _704) (@lem25652 Absty Repty _704 _705 x' R dest mk h1)). Qed.
Lemma lem25667 {Absty Repty : Type'} (_705 : Repty) (_704 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term297 Absty Repty R _705 dest mk _704.
Proof. exact (@lem25666 Absty Repty _705 _704 x' R dest mk h1). Qed.
Lemma lem25668 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term298 Absty Repty dest mk R x.
Proof. exact (@lem25667 Absty Repty x (R x) x' R dest mk h1). Qed.
Lemma lem25671 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (@lem25668 Absty Repty x x' R dest mk h1 (@lem25615 Repty R x)). Qed.
Lemma lem25672 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (@lem25671 Absty Repty x x' R dest mk h1). Qed.
Lemma lem25673 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term299 Absty Repty dest mk R x.
Proof. exact (fun h0 : term300 Absty Repty dest mk R x => @lem25672 Absty Repty x x' R dest mk h1). Qed.
Lemma lem25675 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25676 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term299 Absty Repty dest mk R x) = ((term285 Absty Repty dest mk R x) = (R x)).
Proof. exact (@lem25675 ((term285 Absty Repty dest mk R x) = (R x))). Qed.
Lemma lem25677 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (EQ_MP (@lem25676 Absty Repty dest mk R x) (@lem25673 Absty Repty x x' R dest mk h1)). Qed.
Lemma lem25695 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem25696 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term301 Repty x y z) = (term302 Repty y x z).
Proof. exact (@lem25695 (y = z) (term303 Repty x z)). Qed.
Lemma lem25706 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) : (term304 Repty x y) = (term304 Repty x y).
Proof. exact (eq_refl (term304 Repty x y)). Qed.
Lemma lem25707 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term272 Repty x y z) = (term305 Repty y x z).
Proof. exact (MK_COMB (@lem25706 Repty x y) (@lem25696 Repty y x z)). Qed.
Lemma lem25711 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem25712 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term305 Repty y x z) = (term306 Repty y x z).
Proof. exact (@lem25711 (y = z) (term303 Repty x y) (term303 Repty x z)). Qed.
Lemma lem25734 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term272 Repty x y z) = (term306 Repty y x z).
Proof. exact (TRANS (@lem25707 Repty y x z) (@lem25712 Repty y x z)). Qed.
Lemma lem25735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem25736 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term307 Repty x y z) = (term308 Repty y x z).
Proof. exact (MK_COMB (@lem25735) (@lem25734 Repty y x z)). Qed.
Lemma lem25758 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term306 Repty y x z) = (term306 Repty y x z).
Proof. exact (eq_refl (term306 Repty y x z)). Qed.
Lemma lem25759 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : ((term272 Repty x y z) = (term306 Repty y x z)) = ((term306 Repty y x z) = (term306 Repty y x z)).
Proof. exact (MK_COMB (@lem25736 Repty y x z) (@lem25758 Repty y x z)). Qed.
Lemma lem25761 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem25762 (x : Prop) : (x = x) = True.
Proof. exact (@lem25761 Prop x). Qed.
Lemma lem25763 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : ((term306 Repty y x z) = (term306 Repty y x z)) = True.
Proof. exact (@lem25762 (term306 Repty y x z)). Qed.
Lemma lem25764 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : ((term272 Repty x y z) = (term306 Repty y x z)) = True.
Proof. exact (TRANS (@lem25759 Repty y x z) (@lem25763 Repty y x z)). Qed.
Lemma lem25765 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : True = ((term272 Repty x y z) = (term306 Repty y x z)).
Proof. exact (SYM (@lem25764 Repty y x z)). Qed.
Lemma lem25766 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term272 Repty x y z) = (term306 Repty y x z).
Proof. exact (EQ_MP (@lem25765 Repty y x z) (@lem0)). Qed.
Lemma lem25767 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : term306 Repty y x z.
Proof. exact (EQ_MP (@lem25766 Repty y x z) (@lem25534 Repty x y z)). Qed.
Lemma lem25769 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem25770 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : (term306 Repty y x z) = (term309 Repty x y z).
Proof. exact (@lem25769 (term310 Repty y x z) (y = z)). Qed.
Lemma lem25772 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
Lemma lem25773 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term313 Repty y x z) = (term314 Repty y x z).
Proof. exact (@lem25772 (term303 Repty x y) (term303 Repty x z)). Qed.
Lemma lem25775 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem25776 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) : (term315 Repty x y) = (x = y).
Proof. exact (@lem25775 (x = y)). Qed.
Lemma lem25777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem25778 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) : (term316 Repty x y) = (term317 Repty x y).
Proof. exact (MK_COMB (@lem25777) (@lem25776 Repty x y)). Qed.
Lemma lem25780 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem25781 {Repty : Type'} (x : Repty -> Prop) (z : Repty -> Prop) : (term315 Repty x z) = (x = z).
Proof. exact (@lem25780 (x = z)). Qed.
Lemma lem25782 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term314 Repty y x z) = (term318 Repty y x z).
Proof. exact (MK_COMB (@lem25778 Repty x y) (@lem25781 Repty x z)). Qed.
Lemma lem25783 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term313 Repty y x z) = (term318 Repty y x z).
Proof. exact (TRANS (@lem25773 Repty y x z) (@lem25782 Repty y x z)). Qed.
Lemma lem25784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem25785 {Repty : Type'} (y : Repty -> Prop) (x : Repty -> Prop) (z : Repty -> Prop) : (term319 Repty y x z) = (term320 Repty y x z).
Proof. exact (MK_COMB (@lem25784) (@lem25783 Repty y x z)). Qed.
Lemma lem25786 {Repty : Type'} (y : Repty -> Prop) (z : Repty -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem25787 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : (term309 Repty x y z) = (term321 Repty x y z).
Proof. exact (MK_COMB (@lem25785 Repty y x z) (@lem25786 Repty y z)). Qed.
Lemma lem25788 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : (term306 Repty y x z) = (term321 Repty x y z).
Proof. exact (TRANS (@lem25770 Repty x y z) (@lem25787 Repty x y z)). Qed.
Lemma lem25790 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : term322 Absty Repty y dest mk R x.
Proof. exact (conj (@lem25606 Absty Repty dest mk x R y h2) (@lem25677 Absty Repty x x' R dest mk h1)). Qed.
Lemma lem25792 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : term321 Repty x y z.
Proof. exact (EQ_MP (@lem25788 Repty x y z) (@lem25767 Repty y x z)). Qed.
Lemma lem25793 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : term321 Repty x y z.
Proof. exact (@lem25792 Repty x y z). Qed.
Lemma lem25794 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (y : Repty) (R : type1402 Repty) (x : Repty) : term323 Absty Repty dest mk y R x.
Proof. exact (@lem25793 Repty (term285 Absty Repty dest mk R x) (term285 Absty Repty dest mk R y) (R x)). Qed.
Lemma lem25797 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : (term285 Absty Repty dest mk R y) = (R x).
Proof. exact (@lem25794 Absty Repty dest mk y R x (@lem25790 Absty Repty x' dest mk x R y h1 h2)). Qed.
Lemma lem25798 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : term324 Absty Repty dest mk y R x.
Proof. exact (fun h0 : term325 Absty Repty dest mk y R x => @lem25797 Absty Repty x' dest mk x R y h1 h2). Qed.
Lemma lem25800 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25801 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (y : Repty) (R : type1402 Repty) (x : Repty) : (term324 Absty Repty dest mk y R x) = ((term285 Absty Repty dest mk R y) = (R x)).
Proof. exact (@lem25800 ((term285 Absty Repty dest mk R y) = (R x))). Qed.
Lemma lem25802 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : (term285 Absty Repty dest mk R y) = (R x).
Proof. exact (EQ_MP (@lem25801 Absty Repty dest mk y R x) (@lem25798 Absty Repty x' dest mk x R y h1 h2)). Qed.
Lemma lem25804 {Repty : Type'} (x : Repty -> Prop) : x = x.
Proof. exact (@lem21386 (Repty -> Prop) x). Qed.
Lemma lem25805 {Repty : Type'} (x : Repty -> Prop) : x = x.
Proof. exact (@lem25804 Repty x). Qed.
Lemma lem25806 {Repty : Type'} (R : type1402 Repty) (y : Repty) : (R y) = (R y).
Proof. exact (@lem25805 Repty (R y)). Qed.
Lemma lem25807 {Repty : Type'} (R : type1402 Repty) (y : Repty) : term288 Repty R y.
Proof. exact (fun h0 : term289 Repty R y => @lem25806 Repty R y). Qed.
Lemma lem25809 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25810 {Repty : Type'} (R : type1402 Repty) (y : Repty) : (term288 Repty R y) = ((R y) = (R y)).
Proof. exact (@lem25809 ((R y) = (R y))). Qed.
Lemma lem25811 {Repty : Type'} (R : type1402 Repty) (y : Repty) : (R y) = (R y).
Proof. exact (EQ_MP (@lem25810 Repty R y) (@lem25807 Repty R y)). Qed.
Lemma lem25813 {Absty Repty : Type'} (_705 : Repty) (_704 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term297 Absty Repty R _705 dest mk _704.
Proof. exact (EQ_MP (@lem25663 Absty Repty R _705 dest mk _704) (@lem25652 Absty Repty _704 _705 x' R dest mk h1)). Qed.
Lemma lem25814 {Absty Repty : Type'} (_705 : Repty) (_704 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term297 Absty Repty R _705 dest mk _704.
Proof. exact (@lem25813 Absty Repty _705 _704 x' R dest mk h1). Qed.
Lemma lem25815 {Absty Repty : Type'} (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term298 Absty Repty dest mk R y.
Proof. exact (@lem25814 Absty Repty y (R y) x' R dest mk h1). Qed.
Lemma lem25818 {Absty Repty : Type'} (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R y) = (R y).
Proof. exact (@lem25815 Absty Repty y x' R dest mk h1 (@lem25811 Repty R y)). Qed.
Lemma lem25819 {Absty Repty : Type'} (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R y) = (R y).
Proof. exact (@lem25818 Absty Repty y x' R dest mk h1). Qed.
Lemma lem25820 {Absty Repty : Type'} (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term299 Absty Repty dest mk R y.
Proof. exact (fun h0 : term300 Absty Repty dest mk R y => @lem25819 Absty Repty y x' R dest mk h1). Qed.
Lemma lem25822 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25823 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) : (term299 Absty Repty dest mk R y) = ((term285 Absty Repty dest mk R y) = (R y)).
Proof. exact (@lem25822 ((term285 Absty Repty dest mk R y) = (R y))). Qed.
Lemma lem25824 {Absty Repty : Type'} (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R y) = (R y).
Proof. exact (EQ_MP (@lem25823 Absty Repty dest mk R y) (@lem25820 Absty Repty y x' R dest mk h1)). Qed.
Lemma lem25825 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : term326 Absty Repty x dest mk R y.
Proof. exact (conj (@lem25802 Absty Repty x' dest mk x R y h1 h2) (@lem25824 Absty Repty y x' R dest mk h1)). Qed.
Lemma lem25827 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : term321 Repty x y z.
Proof. exact (EQ_MP (@lem25788 Repty x y z) (@lem25767 Repty y x z)). Qed.
Lemma lem25828 {Repty : Type'} (x : Repty -> Prop) (y : Repty -> Prop) (z : Repty -> Prop) : term321 Repty x y z.
Proof. exact (@lem25827 Repty x y z). Qed.
Lemma lem25829 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : term327 Absty Repty dest mk x R y.
Proof. exact (@lem25828 Repty (term285 Absty Repty dest mk R y) (R x) (R y)). Qed.
Lemma lem25832 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : (R x) = (R y).
Proof. exact (@lem25829 Absty Repty dest mk x R y (@lem25825 Absty Repty x' dest mk x R y h1 h2)). Qed.
Lemma lem25833 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : term328 Repty x R y.
Proof. exact (fun h0 : term267 Repty x R y => @lem25832 Absty Repty x' dest mk x R y h1 h2). Qed.
Lemma lem25835 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25836 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term328 Repty x R y) = ((R x) = (R y)).
Proof. exact (@lem25835 ((R x) = (R y))). Qed.
Lemma lem25837 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : (R x) = (R y).
Proof. exact (EQ_MP (@lem25836 Repty x R y) (@lem25833 Absty Repty x' dest mk x R y h1 h2)). Qed.
Lemma lem25840 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem25842 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term267 Repty x R y) = (term329 Repty x R y).
Proof. exact (@lem25840 ((R x) = (R y))). Qed.
Lemma lem25845 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term244 Absty Repty mk x R y) : term329 Repty x R y.
Proof. exact (EQ_MP (@lem25842 Repty x R y) (@lem25437 Absty Repty mk x R y h1)). Qed.
Lemma lem25848 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : False.
Proof. exact (@lem25845 Absty Repty mk x R y h2 (@lem25837 Absty Repty x' dest mk x R y h1 h2)). Qed.
Lemma lem25849 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : term330.
Proof. exact (fun h0 : ~ False => @lem25848 Absty Repty x' dest mk x R y h1 h2). Qed.
Lemma lem25851 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25852 : term330 = False.
Proof. exact (@lem25851 False). Qed.
Lemma lem25853 {Absty Repty : Type'} (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term239 Absty Repty x' R dest mk) (h2 : term244 Absty Repty mk x R y) : False.
Proof. exact (EQ_MP (@lem25852) (@lem25849 Absty Repty x' dest mk x R y h1 h2)). Qed.
Lemma lem25889 {Absty Repty : Type'} (mk : type862 Absty Repty) : mk = mk.
Proof. exact (eq_refl mk). Qed.
Lemma lem25890 {Repty : Type'} (_742 : Repty -> Prop) (_743 : Repty -> Prop) (h1 : _742 = _743) : _742 = _743.
Proof. exact (h1). Qed.
Lemma lem25891 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) (h1 : _742 = _743) : (mk _742) = (mk _743).
Proof. exact (MK_COMB (@lem25889 Absty Repty mk) (@lem25890 Repty _742 _743 h1)). Qed.
Lemma lem25892 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : term331 Absty Repty _742 mk _743.
Proof. exact (fun h0 : _742 = _743 => @lem25891 Absty Repty mk _742 _743 h0). Qed.
Lemma lem25894 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem25895 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : (term331 Absty Repty _742 mk _743) = (term332 Absty Repty _742 mk _743).
Proof. exact (@lem25894 (_742 = _743) ((mk _742) = (mk _743))). Qed.
Lemma lem25896 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : term332 Absty Repty _742 mk _743.
Proof. exact (EQ_MP (@lem25895 Absty Repty _742 mk _743) (@lem25892 Absty Repty _742 mk _743)). Qed.
Lemma lem25912 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : (R x) = (R y).
Proof. exact (proj2 (@lem25049 Absty Repty mk x R y h1)). Qed.
Lemma lem25913 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : term328 Repty x R y.
Proof. exact (fun h0 : term267 Repty x R y => @lem25912 Absty Repty mk x R y h1). Qed.
Lemma lem25915 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25916 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term328 Repty x R y) = ((R x) = (R y)).
Proof. exact (@lem25915 ((R x) = (R y))). Qed.
Lemma lem25917 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : (R x) = (R y).
Proof. exact (EQ_MP (@lem25916 Repty x R y) (@lem25913 Absty Repty mk x R y h1)). Qed.
Lemma lem25923 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem25924 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : (term332 Absty Repty _742 mk _743) = (term333 Absty Repty mk _742 _743).
Proof. exact (@lem25923 ((mk _742) = (mk _743)) (term303 Repty _742 _743)). Qed.
Lemma lem25934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem25935 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : (term334 Absty Repty _742 mk _743) = (term335 Absty Repty mk _742 _743).
Proof. exact (MK_COMB (@lem25934) (@lem25924 Absty Repty mk _742 _743)). Qed.
Lemma lem25945 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : (term333 Absty Repty mk _742 _743) = (term333 Absty Repty mk _742 _743).
Proof. exact (eq_refl (term333 Absty Repty mk _742 _743)). Qed.
Lemma lem25946 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : ((term332 Absty Repty _742 mk _743) = (term333 Absty Repty mk _742 _743)) = ((term333 Absty Repty mk _742 _743) = (term333 Absty Repty mk _742 _743)).
Proof. exact (MK_COMB (@lem25935 Absty Repty mk _742 _743) (@lem25945 Absty Repty mk _742 _743)). Qed.
Lemma lem25948 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem25949 (x : Prop) : (x = x) = True.
Proof. exact (@lem25948 Prop x). Qed.
Lemma lem25950 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : ((term333 Absty Repty mk _742 _743) = (term333 Absty Repty mk _742 _743)) = True.
Proof. exact (@lem25949 (term333 Absty Repty mk _742 _743)). Qed.
Lemma lem25951 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : ((term332 Absty Repty _742 mk _743) = (term333 Absty Repty mk _742 _743)) = True.
Proof. exact (TRANS (@lem25946 Absty Repty mk _742 _743) (@lem25950 Absty Repty mk _742 _743)). Qed.
Lemma lem25952 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : True = ((term332 Absty Repty _742 mk _743) = (term333 Absty Repty mk _742 _743)).
Proof. exact (SYM (@lem25951 Absty Repty mk _742 _743)). Qed.
Lemma lem25953 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : (term332 Absty Repty _742 mk _743) = (term333 Absty Repty mk _742 _743).
Proof. exact (EQ_MP (@lem25952 Absty Repty mk _742 _743) (@lem0)). Qed.
Lemma lem25954 {Absty Repty : Type'} (mk : type862 Absty Repty) (_742 : Repty -> Prop) (_743 : Repty -> Prop) : term333 Absty Repty mk _742 _743.
Proof. exact (EQ_MP (@lem25953 Absty Repty mk _742 _743) (@lem25896 Absty Repty _742 mk _743)). Qed.
Lemma lem25956 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem25957 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : (term333 Absty Repty mk _742 _743) = (term336 Absty Repty _742 mk _743).
Proof. exact (@lem25956 (term303 Repty _742 _743) ((mk _742) = (mk _743))). Qed.
Lemma lem25959 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem25960 {Repty : Type'} (_742 : Repty -> Prop) (_743 : Repty -> Prop) : (term315 Repty _742 _743) = (_742 = _743).
Proof. exact (@lem25959 (_742 = _743)). Qed.
Lemma lem25961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem25962 {Repty : Type'} (_742 : Repty -> Prop) (_743 : Repty -> Prop) : (term337 Repty _742 _743) = (term338 Repty _742 _743).
Proof. exact (MK_COMB (@lem25961) (@lem25960 Repty _742 _743)). Qed.
Lemma lem25963 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : ((mk _742) = (mk _743)) = ((mk _742) = (mk _743)).
Proof. exact (eq_refl ((mk _742) = (mk _743))). Qed.
Lemma lem25964 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : (term336 Absty Repty _742 mk _743) = (term331 Absty Repty _742 mk _743).
Proof. exact (MK_COMB (@lem25962 Repty _742 _743) (@lem25963 Absty Repty _742 mk _743)). Qed.
Lemma lem25965 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : (term333 Absty Repty mk _742 _743) = (term331 Absty Repty _742 mk _743).
Proof. exact (TRANS (@lem25957 Absty Repty _742 mk _743) (@lem25964 Absty Repty _742 mk _743)). Qed.
Lemma lem25968 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : term331 Absty Repty _742 mk _743.
Proof. exact (EQ_MP (@lem25965 Absty Repty _742 mk _743) (@lem25954 Absty Repty mk _742 _743)). Qed.
Lemma lem25969 {Absty Repty : Type'} (_742 : Repty -> Prop) (mk : type862 Absty Repty) (_743 : Repty -> Prop) : term331 Absty Repty _742 mk _743.
Proof. exact (@lem25968 Absty Repty _742 mk _743). Qed.
Lemma lem25970 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) : term339 Absty Repty x mk R y.
Proof. exact (@lem25969 Absty Repty (R x) mk (R y)). Qed.
Lemma lem25973 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : (term110 Absty Repty mk R x) = (term110 Absty Repty mk R y).
Proof. exact (@lem25970 Absty Repty x mk R y (@lem25917 Absty Repty mk x R y h1)). Qed.
Lemma lem25974 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : term273 Absty Repty x mk R y.
Proof. exact (fun h0 : term268 Absty Repty x mk R y => @lem25973 Absty Repty mk x R y h1). Qed.
Lemma lem25976 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25977 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) : (term273 Absty Repty x mk R y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)).
Proof. exact (@lem25976 ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y))). Qed.
Lemma lem25978 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : (term110 Absty Repty mk R x) = (term110 Absty Repty mk R y).
Proof. exact (EQ_MP (@lem25977 Absty Repty x mk R y) (@lem25974 Absty Repty mk x R y h1)). Qed.
Lemma lem25981 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem25983 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) : (term268 Absty Repty x mk R y) = (term340 Absty Repty x mk R y).
Proof. exact (@lem25981 ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y))). Qed.
Lemma lem25986 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : term340 Absty Repty x mk R y.
Proof. exact (EQ_MP (@lem25983 Absty Repty x mk R y) (@lem25479 Absty Repty mk x R y h1)). Qed.
Lemma lem25989 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : False.
Proof. exact (@lem25986 Absty Repty mk x R y h1 (@lem25978 Absty Repty mk x R y h1)). Qed.
Lemma lem25990 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : term330.
Proof. exact (fun h0 : ~ False => @lem25989 Absty Repty mk x R y h1). Qed.
Lemma lem25992 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem25993 : term330 = False.
Proof. exact (@lem25992 False). Qed.
Lemma lem25994 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term245 Absty Repty mk x R y) : False.
Proof. exact (EQ_MP (@lem25993) (@lem25990 Absty Repty mk x R y h1)). Qed.
Lemma lem25995 {Absty Repty : Type'} (x : Repty) (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term132 Absty Repty mk x R y) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (or_elim (@lem24986 Absty Repty mk x R y h1) (fun h0 : term244 Absty Repty mk x R y => @lem25853 Absty Repty x' dest mk x R y h2 h0) (fun h0 : term245 Absty Repty mk x R y => @lem25994 Absty Repty mk x R y h0)). Qed.
Lemma lem25996 {Absty Repty : Type'} (x : Repty) (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term132 Absty Repty mk x R y) (h2 : term239 Absty Repty x' R dest mk) : (term239 Absty Repty x' R dest mk) = False.
Proof. exact (prop_ext (fun h3 : term239 Absty Repty x' R dest mk => @lem25995 Absty Repty x y x' R dest mk h1 h2) (fun h3 : False => @lem25043 Absty Repty x' R dest mk h2)). Qed.
Lemma lem25997 {Absty Repty : Type'} (x : Repty) (y : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term132 Absty Repty mk x R y) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (EQ_MP (@lem25996 Absty Repty x y x' R dest mk h1 h2) (@lem25043 Absty Repty x' R dest mk h2)). Qed.
Lemma lem25998 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term132 Absty Repty mk x R y) : False.
Proof. exact (ex_elim (@lem24764 Absty Repty R dest mk h1) (fun x' : type684 Repty => fun h0 : term241 Absty Repty R dest mk x' => @lem25997 Absty Repty x y x' R dest mk h2 h0)). Qed.
Lemma lem25999 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term132 Absty Repty mk x R y) : (term132 Absty Repty mk x R y) = False.
Proof. exact (prop_ext (fun h3 : term132 Absty Repty mk x R y => @lem25998 Absty Repty dest mk x R y h1 h2) (fun h3 : False => @lem24116 Absty Repty mk x R y h2)). Qed.
Lemma lem26000 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term132 Absty Repty mk x R y) : False.
Proof. exact (EQ_MP (@lem25999 Absty Repty dest mk x R y h1 h2) (@lem24116 Absty Repty mk x R y h2)). Qed.
Lemma lem26001 {Absty Repty : Type'} (x : Repty) (y : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term131 Absty Repty mk x R y.
Proof. exact (fun h0 : term132 Absty Repty mk x R y => @lem26000 Absty Repty dest mk x R y h1 h0). Qed.
Lemma lem26002 {Absty Repty : Type'} (x : Repty) (y : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)).
Proof. exact (EQ_MP (@lem24115 Absty Repty mk x R y) (@lem26001 Absty Repty x y R dest mk h1)). Qed.
Lemma lem26007 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term112 Absty Repty mk x R.
Proof. exact (fun y : Repty => @lem26002 Absty Repty x y R dest mk h1). Qed.
Lemma lem26012 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term74 Absty Repty mk R.
Proof. exact (fun x : Repty => @lem26007 Absty Repty x R dest mk h1). Qed.
Lemma lem26013 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term86 Absty Repty dest mk R.
Proof. exact (fun h0 : term72 Absty Repty R dest mk => @lem26012 Absty Repty R dest mk h0). Qed.
Lemma lem26014 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term89 Absty Repty dest mk R.
Proof. exact (fun h0 : term73 Absty Repty mk dest => @lem26013 Absty Repty dest mk R). Qed.
Lemma lem26015 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term92 Absty Repty dest mk R.
Proof. exact (fun h0 : term71 Repty R => @lem26014 Absty Repty dest mk R). Qed.
Lemma lem26016 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term95 Absty Repty dest mk R.
Proof. exact (fun h0 : term69 Repty R => @lem26015 Absty Repty dest mk R). Qed.
Lemma lem26017 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term97 Absty Repty dest mk R.
Proof. exact (fun h0 : term67 Repty R => @lem26016 Absty Repty dest mk R). Qed.
Lemma lem26022 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : term101 Absty Repty mk R.
Proof. exact (fun dest : type1413 Absty Repty => @lem26017 Absty Repty dest mk R). Qed.
Lemma lem26027 {Absty Repty : Type'} (R : type1402 Repty) : term105 Absty Repty R.
Proof. exact (fun mk : type862 Absty Repty => @lem26022 Absty Repty mk R). Qed.
Lemma lem26032 {Absty Repty : Type'} : term109 Absty Repty.
Proof. exact (fun R : type1402 Repty => @lem26027 Absty Repty R). Qed.
Lemma lem26033 {Absty Repty : Type'} : term108 Absty Repty.
Proof. exact (EQ_MP (@lem24106 Absty Repty) (@lem26032 Absty Repty)). Qed.
Lemma lem26034 {Absty Repty : Type'} (R : type1402 Repty) : term341 Absty Repty R.
Proof. exact (@lem26033 Absty Repty R). Qed.
Lemma lem26035 {Absty Repty : Type'} (R : type1402 Repty) : (term341 Absty Repty R) = (term104 Absty Repty R).
Proof. exact (eq_refl (term341 Absty Repty R)). Qed.
Lemma lem26036 {Absty Repty : Type'} (R : type1402 Repty) : term104 Absty Repty R.
Proof. exact (EQ_MP (@lem26035 Absty Repty R) (@lem26034 Absty Repty R)). Qed.
Lemma lem26037 {Absty Repty : Type'} (R : type1402 Repty) (mk : type862 Absty Repty) : term342 Absty Repty R mk.
Proof. exact (@lem26036 Absty Repty R mk). Qed.
Lemma lem26038 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term342 Absty Repty R mk) = (term100 Absty Repty mk R).
Proof. exact (eq_refl (term342 Absty Repty R mk)). Qed.
Lemma lem26039 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : term100 Absty Repty mk R.
Proof. exact (EQ_MP (@lem26038 Absty Repty mk R) (@lem26037 Absty Repty R mk)). Qed.
Lemma lem26040 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : term343 Absty Repty mk R dest.
Proof. exact (@lem26039 Absty Repty mk R dest). Qed.
Lemma lem26041 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term343 Absty Repty mk R dest) = (term78 Absty Repty dest mk R).
Proof. exact (eq_refl (term343 Absty Repty mk R dest)). Qed.
Lemma lem26042 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term78 Absty Repty dest mk R.
Proof. exact (EQ_MP (@lem26041 Absty Repty dest mk R) (@lem26040 Absty Repty mk R dest)). Qed.
Lemma lem26044 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term78 Absty Repty dest mk R.
Proof. exact (@lem23799 Absty Repty dest mk R (@lem26042 Absty Repty dest mk R)). Qed.
Lemma lem26045 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term94 Absty Repty dest mk R.
Proof. exact (@lem26044 Absty Repty dest mk R (@lem23771 Repty R h1)). Qed.
Lemma lem26046 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) : term91 Absty Repty dest mk R.
Proof. exact (@lem26045 Absty Repty dest mk R h2 (@lem23773 Repty R h1)). Qed.
Lemma lem26047 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) : term88 Absty Repty dest mk R.
Proof. exact (@lem26046 Absty Repty dest mk R h2 h3 (@lem23775 Repty R h1)). Qed.
Lemma lem26048 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) : term85 Absty Repty dest mk R.
Proof. exact (@lem26047 Absty Repty dest mk R h2 h3 h4 (@lem23777 Absty Repty mk dest h1)). Qed.
Lemma lem26049 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term76 Absty Repty mk R.
Proof. exact (@lem26048 Absty Repty mk dest R h1 h2 h3 h4 (@lem23776 Absty Repty R dest mk h5)). Qed.
Lemma lem26050 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term77 Absty Repty mk R) : False.
Proof. exact (@lem26049 Absty Repty R dest mk h1 h2 h3 h4 h5 (@lem23783 Absty Repty mk R h6)). Qed.
Lemma lem26051 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term77 Absty Repty mk R) : (term77 Absty Repty mk R) = False.
Proof. exact (prop_ext (fun h7 : term77 Absty Repty mk R => @lem26050 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem23783 Absty Repty mk R h6)). Qed.
Lemma lem26052 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term77 Absty Repty mk R) : False.
Proof. exact (EQ_MP (@lem26051 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (@lem23783 Absty Repty mk R h6)). Qed.
Lemma lem26053 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term76 Absty Repty mk R.
Proof. exact (fun h0 : term77 Absty Repty mk R => @lem26052 Absty Repty dest mk R h1 h2 h3 h4 h5 h0). Qed.
Lemma lem26054 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term74 Absty Repty mk R.
Proof. exact (EQ_MP (@lem23782 Absty Repty mk R) (@lem26053 Absty Repty R dest mk h1 h2 h3 h4 h5)). Qed.
Lemma lem26056 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : term24 a b c d.
Proof. exact (@lem23757 a b c d (@lem23749 a b c d)). Qed.
Lemma lem26057 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : term344 Absty Repty mk R dest.
Proof. exact (@lem26056 (term345 Absty Repty mk R) (term346 Absty Repty mk R) (term347 Absty Repty mk R) (term348 Absty Repty mk R dest)). Qed.
Lemma lem26086 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : term349 Absty Repty mk R x.
Proof. exact (@lem23778 Absty Repty mk R h1 x). Qed.
Lemma lem26087 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term349 Absty Repty mk R x) = (term112 Absty Repty mk x R).
Proof. exact (eq_refl (term349 Absty Repty mk R x)). Qed.
Lemma lem26088 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : term112 Absty Repty mk x R.
Proof. exact (EQ_MP (@lem26087 Absty Repty mk x R) (@lem26086 Absty Repty x mk R h1)). Qed.
Lemma lem26089 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : term350 Absty Repty mk x R y.
Proof. exact (@lem26088 Absty Repty x mk R h1 y). Qed.
Lemma lem26090 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term350 Absty Repty mk x R y) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))).
Proof. exact (eq_refl (term350 Absty Repty mk x R y)). Qed.
Lemma lem26110 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)).
Proof. exact (EQ_MP (@lem26090 Absty Repty mk x R y) (@lem26089 Absty Repty x y mk R h1)). Qed.
Lemma lem26111 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)).
Proof. exact (@lem26110 Absty Repty x y mk R h1). Qed.
Lemma lem26114 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term351 Repty R x y) = (term351 Repty R x y).
Proof. exact (eq_refl (term351 Repty R x y)). Qed.
Lemma lem26115 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : ((R x y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y))) = ((R x y) = ((R x) = (R y))).
Proof. exact (MK_COMB (@lem26114 Repty R x y) (@lem26111 Absty Repty x y mk R h1)). Qed.
Lemma lem26118 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : (term352 Absty Repty x mk R) = (term353 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem26115 Absty Repty x y mk R h1)). Qed.
Lemma lem26119 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26120 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : (term354 Absty Repty x mk R) = (term355 Repty x R).
Proof. exact (MK_COMB (@lem26119 Repty) (@lem26118 Absty Repty x mk R h1)). Qed.
Lemma lem26125 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : (term356 Absty Repty mk R) = (term357 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26120 Absty Repty x mk R h1)). Qed.
Lemma lem26126 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26127 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : (term345 Absty Repty mk R) = (term358 Repty R).
Proof. exact (MK_COMB (@lem26126 Repty) (@lem26125 Absty Repty mk R h1)). Qed.
Lemma lem26132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26133 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : (term359 Absty Repty mk R) = (term360 Repty R).
Proof. exact (MK_COMB (@lem26132) (@lem26127 Absty Repty mk R h1)). Qed.
Lemma lem26164 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term361 Absty Repty mk R) = (term361 Absty Repty mk R).
Proof. exact (eq_refl (term361 Absty Repty mk R)). Qed.
Lemma lem26165 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : (term362 Absty Repty mk R) = (term363 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26133 Absty Repty mk R h1) (@lem26164 Absty Repty mk R)). Qed.
Lemma lem26168 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term74 Absty Repty mk R) : (term363 Absty Repty mk R) = (term362 Absty Repty mk R).
Proof. exact (SYM (@lem26165 Absty Repty mk R h1)). Qed.
Lemma lem26186 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term16 A B f g).
Proof. exact (EQ_MP (@lem23491 A B f g) (@lem23490 A B f g)). Qed.
Lemma lem26187 {Repty : Type'} (f : Repty -> Prop) (g : Repty -> Prop) : (f = g) = (term364 Repty f g).
Proof. exact (@lem26186 Repty Prop f g). Qed.
Lemma lem26188 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : ((R x) = (R y)) = (term365 Repty x R y).
Proof. exact (@lem26187 Repty (R x) (R y)). Qed.
Lemma lem26197 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term351 Repty R x y) = (term351 Repty R x y).
Proof. exact (eq_refl (term351 Repty R x y)). Qed.
Lemma lem26198 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : ((R x y) = ((R x) = (R y))) = ((R x y) = (term365 Repty x R y)).
Proof. exact (MK_COMB (@lem26197 Repty R x y) (@lem26188 Repty x R y)). Qed.
Lemma lem26203 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term353 Repty x R) = (term366 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem26198 Repty x R y)). Qed.
Lemma lem26204 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26205 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term355 Repty x R) = (term367 Repty x R).
Proof. exact (MK_COMB (@lem26204 Repty) (@lem26203 Repty x R)). Qed.
Lemma lem26210 {Repty : Type'} (R : type1402 Repty) : (term357 Repty R) = (term368 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26205 Repty x R)). Qed.
Lemma lem26211 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26212 {Repty : Type'} (R : type1402 Repty) : (term358 Repty R) = (term369 Repty R).
Proof. exact (MK_COMB (@lem26211 Repty) (@lem26210 Repty R)). Qed.
Lemma lem26217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26218 {Repty : Type'} (R : type1402 Repty) : (term360 Repty R) = (term370 Repty R).
Proof. exact (MK_COMB (@lem26217) (@lem26212 Repty R)). Qed.
Lemma lem26253 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term361 Absty Repty mk R) = (term361 Absty Repty mk R).
Proof. exact (eq_refl (term361 Absty Repty mk R)). Qed.
Lemma lem26254 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term363 Absty Repty mk R) = (term371 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26218 Repty R) (@lem26253 Absty Repty mk R)). Qed.
Lemma lem26257 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term371 Absty Repty mk R) = (term363 Absty Repty mk R).
Proof. exact (SYM (@lem26254 Absty Repty mk R)). Qed.
Lemma lem26259 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem26260 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term371 Absty Repty mk R) = (term372 Absty Repty mk R).
Proof. exact (@lem26259 (term371 Absty Repty mk R)). Qed.
Lemma lem26261 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term372 Absty Repty mk R) = (term371 Absty Repty mk R).
Proof. exact (SYM (@lem26260 Absty Repty mk R)). Qed.
Lemma lem26262 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term373 Absty Repty mk R) : term373 Absty Repty mk R.
Proof. exact (h1). Qed.
Lemma lem26265 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term374 Absty Repty dest mk R) : term374 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem26266 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term375 Absty Repty dest mk R.
Proof. exact (fun h0 : term374 Absty Repty dest mk R => @lem26265 Absty Repty dest mk R h0). Qed.
Lemma lem26267 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term375 Absty Repty dest mk R) : term375 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem26268 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term374 Absty Repty dest mk R) : term374 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem26269 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term374 Absty Repty dest mk R) (h2 : term375 Absty Repty dest mk R) : term374 Absty Repty dest mk R.
Proof. exact (@lem26267 Absty Repty dest mk R h2 (@lem26268 Absty Repty dest mk R h1)). Qed.
Lemma lem26270 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term374 Absty Repty dest mk R) : term376 Absty Repty dest mk R.
Proof. exact (fun h0 : term375 Absty Repty dest mk R => @lem26269 Absty Repty dest mk R h1 h0). Qed.
Lemma lem26271 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term375 Absty Repty dest mk R) : term375 Absty Repty dest mk R.
Proof. exact (h1). Qed.
Lemma lem26272 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term374 Absty Repty dest mk R) (h2 : term375 Absty Repty dest mk R) : term374 Absty Repty dest mk R.
Proof. exact (@lem26270 Absty Repty dest mk R h1 (@lem26271 Absty Repty dest mk R h2)). Qed.
Lemma lem26273 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term375 Absty Repty dest mk R) : term375 Absty Repty dest mk R.
Proof. exact (fun h0 : term374 Absty Repty dest mk R => @lem26272 Absty Repty dest mk R h0 h1). Qed.
Lemma lem26274 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term377 Absty Repty dest mk R.
Proof. exact (fun h0 : term375 Absty Repty dest mk R => @lem26273 Absty Repty dest mk R h0). Qed.
Lemma lem26277 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term375 Absty Repty dest mk R.
Proof. exact (@lem26274 Absty Repty dest mk R (@lem26266 Absty Repty dest mk R)). Qed.
Lemma lem26278 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term375 Absty Repty dest mk R.
Proof. exact (@lem26277 Absty Repty dest mk R). Qed.
Lemma lem26352 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem26353 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term372 Absty Repty mk R) = (term378 Absty Repty mk R).
Proof. exact (@lem26352 (term373 Absty Repty mk R)). Qed.
Lemma lem26355 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem26356 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term378 Absty Repty mk R) = (term371 Absty Repty mk R).
Proof. exact (@lem26355 (term371 Absty Repty mk R)). Qed.
Lemma lem26359 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term372 Absty Repty mk R) = (term371 Absty Repty mk R).
Proof. exact (TRANS (@lem26353 Absty Repty mk R) (@lem26356 Absty Repty mk R)). Qed.
Lemma lem26398 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term379 Absty Repty mk R) = (term379 Absty Repty mk R).
Proof. exact (eq_refl (term379 Absty Repty mk R)). Qed.
Lemma lem26399 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term380 Absty Repty mk R) = (term381 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26398 Absty Repty mk R) (@lem26359 Absty Repty mk R)). Qed.
Lemma lem26402 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (eq_refl (term84 Absty Repty R dest mk)). Qed.
Lemma lem26403 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term382 Absty Repty dest mk R) = (term383 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26402 Absty Repty R dest mk) (@lem26399 Absty Repty mk R)). Qed.
Lemma lem26406 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (eq_refl (term87 Absty Repty mk dest)). Qed.
Lemma lem26407 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term384 Absty Repty dest mk R) = (term385 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26406 Absty Repty mk dest) (@lem26403 Absty Repty dest mk R)). Qed.
Lemma lem26410 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (eq_refl (term90 Repty R)). Qed.
Lemma lem26411 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term386 Absty Repty dest mk R) = (term387 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26410 Repty R) (@lem26407 Absty Repty dest mk R)). Qed.
Lemma lem26414 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (eq_refl (term93 Repty R)). Qed.
Lemma lem26415 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term388 Absty Repty dest mk R) = (term389 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26414 Repty R) (@lem26411 Absty Repty dest mk R)). Qed.
Lemma lem26418 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (eq_refl (term96 Repty R)). Qed.
Lemma lem26419 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term374 Absty Repty dest mk R) = (term390 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26418 Repty R) (@lem26415 Absty Repty dest mk R)). Qed.
Lemma lem26422 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term391 Absty Repty mk R) = (term392 Absty Repty mk R).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem26419 Absty Repty dest mk R)). Qed.
Lemma lem26423 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem26424 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term393 Absty Repty mk R) = (term394 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26423 Absty Repty) (@lem26422 Absty Repty mk R)). Qed.
Lemma lem26429 {Absty Repty : Type'} (R : type1402 Repty) : (term395 Absty Repty R) = (term396 Absty Repty R).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem26424 Absty Repty mk R)). Qed.
Lemma lem26430 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem26431 {Absty Repty : Type'} (R : type1402 Repty) : (term397 Absty Repty R) = (term398 Absty Repty R).
Proof. exact (MK_COMB (@lem26430 Absty Repty) (@lem26429 Absty Repty R)). Qed.
Lemma lem26436 {Absty Repty : Type'} : (term399 Absty Repty) = (term400 Absty Repty).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem26431 Absty Repty R)). Qed.
Lemma lem26437 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem26446 {Absty Repty : Type'} : (term401 Absty Repty) = (term402 Absty Repty).
Proof. exact (MK_COMB (@lem26437 Repty) (@lem26436 Absty Repty)). Qed.
Lemma lem26447 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem26448 {Absty : Type'} (P : Absty -> Prop) : (term403 Absty P) = (term403 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem26447 Absty P x)). Qed.
Lemma lem26449 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem26450 {Absty : Type'} (P : Absty -> Prop) : (term404 Absty P) = (term404 Absty P).
Proof. exact (MK_COMB (@lem26449 Absty) (@lem26448 Absty P)). Qed.
Lemma lem26451 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term405 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term405 Absty Repty P mk R x)). Qed.
Lemma lem26452 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term406 Absty Repty P mk R) = (term406 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem26451 Absty Repty P mk R x)). Qed.
Lemma lem26453 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem26454 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term407 Absty Repty P mk R) = (term407 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem26453 Repty) (@lem26452 Absty Repty P mk R)). Qed.
Lemma lem26455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem26456 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term408 Absty Repty P mk R) = (term408 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem26455) (@lem26454 Absty Repty P mk R)). Qed.
Lemma lem26457 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term407 Absty Repty P mk R) = (term404 Absty P)) = ((term407 Absty Repty P mk R) = (term404 Absty P)).
Proof. exact (MK_COMB (@lem26456 Absty Repty P mk R) (@lem26450 Absty P)). Qed.
Lemma lem26458 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term409 Absty Repty mk R) = (term409 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem26457 Absty Repty mk R P)). Qed.
Lemma lem26459 {Absty : Type'} : (@all (Absty -> Prop)) = (@all (Absty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Prop))). Qed.
Lemma lem26460 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term347 Absty Repty mk R) = (term347 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26459 Absty) (@lem26458 Absty Repty mk R)). Qed.
Lemma lem26461 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem26462 {Absty : Type'} (P : Absty -> Prop) : (term403 Absty P) = (term403 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem26461 Absty P x)). Qed.
Lemma lem26463 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem26464 {Absty : Type'} (P : Absty -> Prop) : (term410 Absty P) = (term410 Absty P).
Proof. exact (MK_COMB (@lem26463 Absty) (@lem26462 Absty P)). Qed.
Lemma lem26465 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term405 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term405 Absty Repty P mk R x)). Qed.
Lemma lem26466 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term406 Absty Repty P mk R) = (term406 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem26465 Absty Repty P mk R x)). Qed.
Lemma lem26467 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26468 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term411 Absty Repty P mk R) = (term411 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem26467 Repty) (@lem26466 Absty Repty P mk R)). Qed.
Lemma lem26469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem26470 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term412 Absty Repty P mk R) = (term412 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem26469) (@lem26468 Absty Repty P mk R)). Qed.
Lemma lem26471 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term411 Absty Repty P mk R) = (term410 Absty P)) = ((term411 Absty Repty P mk R) = (term410 Absty P)).
Proof. exact (MK_COMB (@lem26470 Absty Repty P mk R) (@lem26464 Absty P)). Qed.
Lemma lem26472 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term413 Absty Repty mk R) = (term413 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem26471 Absty Repty mk R P)). Qed.
Lemma lem26473 {Absty : Type'} : (@all (Absty -> Prop)) = (@all (Absty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Prop))). Qed.
Lemma lem26474 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term346 Absty Repty mk R) = (term346 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26473 Absty) (@lem26472 Absty Repty mk R)). Qed.
Lemma lem26475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26476 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term414 Absty Repty mk R) = (term414 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26475) (@lem26474 Absty Repty mk R)). Qed.
Lemma lem26477 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term361 Absty Repty mk R) = (term361 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26476 Absty Repty mk R) (@lem26460 Absty Repty mk R)). Qed.
Lemma lem26482 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : ((R x x') = (R y x')) = ((R x x') = (R y x')).
Proof. exact (eq_refl ((R x x') = (R y x'))). Qed.
Lemma lem26483 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term415 Repty x R y) = (term415 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem26482 Repty x R y x')). Qed.
Lemma lem26484 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26485 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term365 Repty x R y) = (term365 Repty x R y).
Proof. exact (MK_COMB (@lem26484 Repty) (@lem26483 Repty x R y)). Qed.
Lemma lem26488 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term351 Repty R x y) = (term351 Repty R x y).
Proof. exact (eq_refl (term351 Repty R x y)). Qed.
Lemma lem26489 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : ((R x y) = (term365 Repty x R y)) = ((R x y) = (term365 Repty x R y)).
Proof. exact (MK_COMB (@lem26488 Repty R x y) (@lem26485 Repty x R y)). Qed.
Lemma lem26490 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term366 Repty x R) = (term366 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem26489 Repty x R y)). Qed.
Lemma lem26491 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26492 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term367 Repty x R) = (term367 Repty x R).
Proof. exact (MK_COMB (@lem26491 Repty) (@lem26490 Repty x R)). Qed.
Lemma lem26493 {Repty : Type'} (R : type1402 Repty) : (term368 Repty R) = (term368 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26492 Repty x R)). Qed.
Lemma lem26494 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26495 {Repty : Type'} (R : type1402 Repty) : (term369 Repty R) = (term369 Repty R).
Proof. exact (MK_COMB (@lem26494 Repty) (@lem26493 Repty R)). Qed.
Lemma lem26496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26497 {Repty : Type'} (R : type1402 Repty) : (term370 Repty R) = (term370 Repty R).
Proof. exact (MK_COMB (@lem26496) (@lem26495 Repty R)). Qed.
Lemma lem26498 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term371 Absty Repty mk R) = (term371 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26497 Repty R) (@lem26477 Absty Repty mk R)). Qed.
Lemma lem26503 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))).
Proof. exact (eq_refl (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)))). Qed.
Lemma lem26504 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term111 Absty Repty mk x R) = (term111 Absty Repty mk x R).
Proof. exact (fun_ext (fun y : Repty => @lem26503 Absty Repty mk x R y)). Qed.
Lemma lem26505 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26506 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term112 Absty Repty mk x R) = (term112 Absty Repty mk x R).
Proof. exact (MK_COMB (@lem26505 Repty) (@lem26504 Absty Repty mk x R)). Qed.
Lemma lem26507 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term113 Absty Repty mk R) = (term113 Absty Repty mk R).
Proof. exact (fun_ext (fun x : Repty => @lem26506 Absty Repty mk x R)). Qed.
Lemma lem26508 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26509 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term74 Absty Repty mk R) = (term74 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26508 Repty) (@lem26507 Absty Repty mk R)). Qed.
Lemma lem26510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem26511 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term379 Absty Repty mk R) = (term379 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26510) (@lem26509 Absty Repty mk R)). Qed.
Lemma lem26512 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term381 Absty Repty mk R) = (term381 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26511 Absty Repty mk R) (@lem26498 Absty Repty mk R)). Qed.
Lemma lem26513 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem26514 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem26515 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem26514 Repty r R x)). Qed.
Lemma lem26516 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem26517 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem26516 Repty) (@lem26515 Repty r R)). Qed.
Lemma lem26518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem26519 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term117 Repty r R) = (term117 Repty r R).
Proof. exact (MK_COMB (@lem26518) (@lem26517 Repty r R)). Qed.
Lemma lem26520 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)).
Proof. exact (MK_COMB (@lem26519 Repty r R) (@lem26513 Absty Repty dest mk r)). Qed.
Lemma lem26521 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term118 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem26520 Absty Repty R dest mk r)). Qed.
Lemma lem26522 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem26523 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term72 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem26522 Repty) (@lem26521 Absty Repty R dest mk)). Qed.
Lemma lem26524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem26525 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem26524) (@lem26523 Absty Repty R dest mk)). Qed.
Lemma lem26526 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term383 Absty Repty dest mk R) = (term383 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26525 Absty Repty R dest mk) (@lem26512 Absty Repty mk R)). Qed.
Lemma lem26527 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem26528 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem26527 Absty Repty mk dest a)). Qed.
Lemma lem26529 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem26530 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem26529 Absty) (@lem26528 Absty Repty mk dest)). Qed.
Lemma lem26531 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem26532 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem26531) (@lem26530 Absty Repty mk dest)). Qed.
Lemma lem26533 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term385 Absty Repty dest mk R) = (term385 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26532 Absty Repty mk dest) (@lem26526 Absty Repty dest mk R)). Qed.
Lemma lem26542 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term121 Repty y R x z) = (term121 Repty y R x z).
Proof. exact (eq_refl (term121 Repty y R x z)). Qed.
Lemma lem26543 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term122 Repty y R x) = (term122 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem26542 Repty y R x z)). Qed.
Lemma lem26544 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26545 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term123 Repty y R x) = (term123 Repty y R x).
Proof. exact (MK_COMB (@lem26544 Repty) (@lem26543 Repty y R x)). Qed.
Lemma lem26546 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term124 Repty R x) = (term124 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem26545 Repty y R x)). Qed.
Lemma lem26547 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26548 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term125 Repty R x) = (term125 Repty R x).
Proof. exact (MK_COMB (@lem26547 Repty) (@lem26546 Repty R x)). Qed.
Lemma lem26549 {Repty : Type'} (R : type1402 Repty) : (term126 Repty R) = (term126 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26548 Repty R x)). Qed.
Lemma lem26550 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26551 {Repty : Type'} (R : type1402 Repty) : (term71 Repty R) = (term71 Repty R).
Proof. exact (MK_COMB (@lem26550 Repty) (@lem26549 Repty R)). Qed.
Lemma lem26552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem26553 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (MK_COMB (@lem26552) (@lem26551 Repty R)). Qed.
Lemma lem26554 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term387 Absty Repty dest mk R) = (term387 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26553 Repty R) (@lem26533 Absty Repty dest mk R)). Qed.
Lemma lem26559 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : ((R x y) = (R y x)) = ((R x y) = (R y x)).
Proof. exact (eq_refl ((R x y) = (R y x))). Qed.
Lemma lem26560 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term127 Repty R x) = (term127 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem26559 Repty R y x)). Qed.
Lemma lem26561 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26562 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term128 Repty R x) = (term128 Repty R x).
Proof. exact (MK_COMB (@lem26561 Repty) (@lem26560 Repty R x)). Qed.
Lemma lem26563 {Repty : Type'} (R : type1402 Repty) : (term129 Repty R) = (term129 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26562 Repty R x)). Qed.
Lemma lem26564 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26565 {Repty : Type'} (R : type1402 Repty) : (term69 Repty R) = (term69 Repty R).
Proof. exact (MK_COMB (@lem26564 Repty) (@lem26563 Repty R)). Qed.
Lemma lem26566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem26567 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (MK_COMB (@lem26566) (@lem26565 Repty R)). Qed.
Lemma lem26568 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term389 Absty Repty dest mk R) = (term389 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26567 Repty R) (@lem26554 Absty Repty dest mk R)). Qed.
Lemma lem26569 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem26570 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term130 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26569 Repty R x)). Qed.
Lemma lem26571 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26572 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term67 Repty R).
Proof. exact (MK_COMB (@lem26571 Repty) (@lem26570 Repty R)). Qed.
Lemma lem26573 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem26574 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (MK_COMB (@lem26573) (@lem26572 Repty R)). Qed.
Lemma lem26575 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term390 Absty Repty dest mk R) = (term390 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem26574 Repty R) (@lem26568 Absty Repty dest mk R)). Qed.
Lemma lem26576 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term392 Absty Repty mk R) = (term392 Absty Repty mk R).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem26575 Absty Repty dest mk R)). Qed.
Lemma lem26577 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem26578 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term394 Absty Repty mk R) = (term394 Absty Repty mk R).
Proof. exact (MK_COMB (@lem26577 Absty Repty) (@lem26576 Absty Repty mk R)). Qed.
Lemma lem26579 {Absty Repty : Type'} (R : type1402 Repty) : (term396 Absty Repty R) = (term396 Absty Repty R).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem26578 Absty Repty mk R)). Qed.
Lemma lem26580 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem26581 {Absty Repty : Type'} (R : type1402 Repty) : (term398 Absty Repty R) = (term398 Absty Repty R).
Proof. exact (MK_COMB (@lem26580 Absty Repty) (@lem26579 Absty Repty R)). Qed.
Lemma lem26582 {Absty Repty : Type'} : (term400 Absty Repty) = (term400 Absty Repty).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem26581 Absty Repty R)). Qed.
Lemma lem26583 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem26584 {Absty Repty : Type'} : (term402 Absty Repty) = (term402 Absty Repty).
Proof. exact (MK_COMB (@lem26583 Repty) (@lem26582 Absty Repty)). Qed.
Lemma lem26745 {Absty Repty : Type'} : (term401 Absty Repty) = (term402 Absty Repty).
Proof. exact (TRANS (@lem26446 Absty Repty) (@lem26584 Absty Repty)). Qed.
Lemma lem26746 {Absty Repty : Type'} : (term402 Absty Repty) = (term401 Absty Repty).
Proof. exact (SYM (@lem26745 Absty Repty)). Qed.
Lemma lem26747 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term67 Repty R.
Proof. exact (h1). Qed.
Lemma lem26748 {Repty : Type'} (R : type1402 Repty) (h1 : term69 Repty R) : term69 Repty R.
Proof. exact (h1). Qed.
Lemma lem26749 {Repty : Type'} (R : type1402 Repty) (h1 : term71 Repty R) : term71 Repty R.
Proof. exact (h1). Qed.
Lemma lem26750 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term73 Absty Repty mk dest.
Proof. exact (h1). Qed.
Lemma lem26751 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term72 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem26754 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem26755 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term371 Absty Repty mk R) = (term372 Absty Repty mk R).
Proof. exact (@lem26754 (term371 Absty Repty mk R)). Qed.
Lemma lem26756 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term372 Absty Repty mk R) = (term371 Absty Repty mk R).
Proof. exact (SYM (@lem26755 Absty Repty mk R)). Qed.
Lemma lem26757 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term373 Absty Repty mk R) : term373 Absty Repty mk R.
Proof. exact (h1). Qed.
Lemma lem26758 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem26759 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term130 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26758 Repty R x)). Qed.
Lemma lem26760 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26769 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term67 Repty R).
Proof. exact (MK_COMB (@lem26760 Repty) (@lem26759 Repty R)). Qed.
Lemma lem26770 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term67 Repty R.
Proof. exact (EQ_MP (@lem26769 Repty R) (@lem26747 Repty R h1)). Qed.
Lemma lem26785 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : ((R x y) = (R y x)) = (term416 Repty R y x).
Proof. exact (@lem17784 (R x y) (R y x)). Qed.
Lemma lem26786 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term127 Repty R x) = (term417 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem26785 Repty R y x)). Qed.
Lemma lem26787 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26788 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term128 Repty R x) = (term418 Repty R x).
Proof. exact (MK_COMB (@lem26787 Repty) (@lem26786 Repty R x)). Qed.
Lemma lem26789 {Repty : Type'} (R : type1402 Repty) : (term129 Repty R) = (term419 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26788 Repty R x)). Qed.
Lemma lem26790 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26791 {Repty : Type'} (R : type1402 Repty) : (term69 Repty R) = (term420 Repty R).
Proof. exact (MK_COMB (@lem26790 Repty) (@lem26789 Repty R)). Qed.
Lemma lem26797 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem26798 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term155 Repty P Q) = (term156 Repty P Q).
Proof. exact (@lem26797 Repty P Q). Qed.
Lemma lem26799 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term421 Repty R x) = (term422 Repty R x).
Proof. exact (@lem26798 Repty (term423 Repty R x) (term424 Repty R x)). Qed.
Lemma lem26800 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term425 Repty R x y) = (term426 Repty R y x).
Proof. exact (eq_refl (term425 Repty R x y)). Qed.
Lemma lem26801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26802 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term427 Repty R x y) = (term428 Repty R y x).
Proof. exact (MK_COMB (@lem26801) (@lem26800 Repty R y x)). Qed.
Lemma lem26803 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term429 Repty R x y) = (term430 Repty R y x).
Proof. exact (eq_refl (term429 Repty R x y)). Qed.
Lemma lem26804 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term431 Repty R x y) = (term416 Repty R y x).
Proof. exact (MK_COMB (@lem26802 Repty R y x) (@lem26803 Repty R y x)). Qed.
Lemma lem26805 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term432 Repty R x) = (term417 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem26804 Repty R y x)). Qed.
Lemma lem26806 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26807 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term421 Repty R x) = (term418 Repty R x).
Proof. exact (MK_COMB (@lem26806 Repty) (@lem26805 Repty R x)). Qed.
Lemma lem26808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem26809 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term433 Repty R x) = (term434 Repty R x).
Proof. exact (MK_COMB (@lem26808) (@lem26807 Repty R x)). Qed.
Lemma lem26810 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term425 Repty R x y) = (term426 Repty R y x).
Proof. exact (eq_refl (term425 Repty R x y)). Qed.
Lemma lem26811 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term435 Repty R x) = (term423 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem26810 Repty R y x)). Qed.
Lemma lem26812 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26813 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term436 Repty R x) = (term437 Repty R x).
Proof. exact (MK_COMB (@lem26812 Repty) (@lem26811 Repty R x)). Qed.
Lemma lem26814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26815 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term438 Repty R x) = (term439 Repty R x).
Proof. exact (MK_COMB (@lem26814) (@lem26813 Repty R x)). Qed.
Lemma lem26816 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term429 Repty R x y) = (term430 Repty R y x).
Proof. exact (eq_refl (term429 Repty R x y)). Qed.
Lemma lem26817 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term440 Repty R x) = (term424 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem26816 Repty R y x)). Qed.
Lemma lem26818 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26819 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term441 Repty R x) = (term442 Repty R x).
Proof. exact (MK_COMB (@lem26818 Repty) (@lem26817 Repty R x)). Qed.
Lemma lem26820 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term422 Repty R x) = (term443 Repty R x).
Proof. exact (MK_COMB (@lem26815 Repty R x) (@lem26819 Repty R x)). Qed.
Lemma lem26821 {Repty : Type'} (R : type1402 Repty) (x : Repty) : ((term421 Repty R x) = (term422 Repty R x)) = ((term418 Repty R x) = (term443 Repty R x)).
Proof. exact (MK_COMB (@lem26809 Repty R x) (@lem26820 Repty R x)). Qed.
Lemma lem26822 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term418 Repty R x) = (term443 Repty R x).
Proof. exact (EQ_MP (@lem26821 Repty R x) (@lem26799 Repty R x)). Qed.
Lemma lem26919 {Repty : Type'} (R : type1402 Repty) : (term419 Repty R) = (term444 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26822 Repty R x)). Qed.
Lemma lem26920 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26921 {Repty : Type'} (R : type1402 Repty) : (term420 Repty R) = (term445 Repty R).
Proof. exact (MK_COMB (@lem26920 Repty) (@lem26919 Repty R)). Qed.
Lemma lem26923 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem26924 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term155 Repty P Q) = (term156 Repty P Q).
Proof. exact (@lem26923 Repty P Q). Qed.
Lemma lem26925 {Repty : Type'} (R : type1402 Repty) : (term446 Repty R) = (term447 Repty R).
Proof. exact (@lem26924 Repty (term448 Repty R) (term449 Repty R)). Qed.
Lemma lem26926 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term450 Repty R x) = (term437 Repty R x).
Proof. exact (eq_refl (term450 Repty R x)). Qed.
Lemma lem26927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26928 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term451 Repty R x) = (term439 Repty R x).
Proof. exact (MK_COMB (@lem26927) (@lem26926 Repty R x)). Qed.
Lemma lem26929 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term452 Repty R x) = (term442 Repty R x).
Proof. exact (eq_refl (term452 Repty R x)). Qed.
Lemma lem26930 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term453 Repty R x) = (term443 Repty R x).
Proof. exact (MK_COMB (@lem26928 Repty R x) (@lem26929 Repty R x)). Qed.
Lemma lem26931 {Repty : Type'} (R : type1402 Repty) : (term454 Repty R) = (term444 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26930 Repty R x)). Qed.
Lemma lem26932 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26933 {Repty : Type'} (R : type1402 Repty) : (term446 Repty R) = (term445 Repty R).
Proof. exact (MK_COMB (@lem26932 Repty) (@lem26931 Repty R)). Qed.
Lemma lem26934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem26935 {Repty : Type'} (R : type1402 Repty) : (term455 Repty R) = (term456 Repty R).
Proof. exact (MK_COMB (@lem26934) (@lem26933 Repty R)). Qed.
Lemma lem26936 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term450 Repty R x) = (term437 Repty R x).
Proof. exact (eq_refl (term450 Repty R x)). Qed.
Lemma lem26937 {Repty : Type'} (R : type1402 Repty) : (term457 Repty R) = (term448 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26936 Repty R x)). Qed.
Lemma lem26938 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26939 {Repty : Type'} (R : type1402 Repty) : (term458 Repty R) = (term459 Repty R).
Proof. exact (MK_COMB (@lem26938 Repty) (@lem26937 Repty R)). Qed.
Lemma lem26940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem26941 {Repty : Type'} (R : type1402 Repty) : (term460 Repty R) = (term461 Repty R).
Proof. exact (MK_COMB (@lem26940) (@lem26939 Repty R)). Qed.
Lemma lem26942 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term452 Repty R x) = (term442 Repty R x).
Proof. exact (eq_refl (term452 Repty R x)). Qed.
Lemma lem26943 {Repty : Type'} (R : type1402 Repty) : (term462 Repty R) = (term449 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem26942 Repty R x)). Qed.
Lemma lem26944 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem26945 {Repty : Type'} (R : type1402 Repty) : (term463 Repty R) = (term464 Repty R).
Proof. exact (MK_COMB (@lem26944 Repty) (@lem26943 Repty R)). Qed.
Lemma lem26946 {Repty : Type'} (R : type1402 Repty) : (term447 Repty R) = (term465 Repty R).
Proof. exact (MK_COMB (@lem26941 Repty R) (@lem26945 Repty R)). Qed.
Lemma lem26947 {Repty : Type'} (R : type1402 Repty) : ((term446 Repty R) = (term447 Repty R)) = ((term445 Repty R) = (term465 Repty R)).
Proof. exact (MK_COMB (@lem26935 Repty R) (@lem26946 Repty R)). Qed.
Lemma lem26948 {Repty : Type'} (R : type1402 Repty) : (term445 Repty R) = (term465 Repty R).
Proof. exact (EQ_MP (@lem26947 Repty R) (@lem26925 Repty R)). Qed.
Lemma lem27055 {Repty : Type'} (R : type1402 Repty) : (term420 Repty R) = (term465 Repty R).
Proof. exact (TRANS (@lem26921 Repty R) (@lem26948 Repty R)). Qed.
Lemma lem27056 {Repty : Type'} (R : type1402 Repty) : (term69 Repty R) = (term465 Repty R).
Proof. exact (TRANS (@lem26791 Repty R) (@lem27055 Repty R)). Qed.
Lemma lem27057 {Repty : Type'} (R : type1402 Repty) (h1 : term69 Repty R) : term465 Repty R.
Proof. exact (EQ_MP (@lem27056 Repty R) (@lem26748 Repty R h1)). Qed.
Lemma lem27064 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (z : Repty) : (term466 Repty x R y z) = (term467 Repty x R y z).
Proof. exact (@lem17045 (R x y) (R y z)). Qed.
Lemma lem27065 {Repty : Type'} (R : type1402 Repty) (x : Repty) (z : Repty) : (R x z) = (R x z).
Proof. exact (eq_refl (R x z)). Qed.
Lemma lem27066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27067 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (z : Repty) : (term468 Repty x R y z) = (term469 Repty x R y z).
Proof. exact (MK_COMB (@lem27066) (@lem27064 Repty x R y z)). Qed.
Lemma lem27068 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term470 Repty y R x z) = (term471 Repty y R x z).
Proof. exact (MK_COMB (@lem27067 Repty x R y z) (@lem27065 Repty R x z)). Qed.
Lemma lem27069 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term121 Repty y R x z) = (term470 Repty y R x z).
Proof. exact (@lem17265 (term472 Repty x R y z) (R x z)). Qed.
Lemma lem27070 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term121 Repty y R x z) = (term471 Repty y R x z).
Proof. exact (TRANS (@lem27069 Repty y R x z) (@lem27068 Repty y R x z)). Qed.
Lemma lem27071 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term122 Repty y R x) = (term473 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem27070 Repty y R x z)). Qed.
Lemma lem27072 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem27073 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term123 Repty y R x) = (term474 Repty y R x).
Proof. exact (MK_COMB (@lem27072 Repty) (@lem27071 Repty y R x)). Qed.
Lemma lem27074 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term124 Repty R x) = (term475 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem27073 Repty y R x)). Qed.
Lemma lem27075 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem27076 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term125 Repty R x) = (term476 Repty R x).
Proof. exact (MK_COMB (@lem27075 Repty) (@lem27074 Repty R x)). Qed.
Lemma lem27077 {Repty : Type'} (R : type1402 Repty) : (term126 Repty R) = (term477 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem27076 Repty R x)). Qed.
Lemma lem27078 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem27139 {Repty : Type'} (R : type1402 Repty) : (term71 Repty R) = (term478 Repty R).
Proof. exact (MK_COMB (@lem27078 Repty) (@lem27077 Repty R)). Qed.
Lemma lem27140 {Repty : Type'} (R : type1402 Repty) (h1 : term71 Repty R) : term478 Repty R.
Proof. exact (EQ_MP (@lem27139 Repty R) (@lem26749 Repty R h1)). Qed.
Lemma lem27141 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem27142 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem27141 Absty Repty mk dest a)). Qed.
Lemma lem27143 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem27152 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem27143 Absty) (@lem27142 Absty Repty mk dest)). Qed.
Lemma lem27153 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term73 Absty Repty mk dest.
Proof. exact (EQ_MP (@lem27152 Absty Repty mk dest) (@lem26750 Absty Repty mk dest h1)). Qed.
Lemma lem27155 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem27156 {Repty : Type'} (P : Repty -> Prop) : (term133 Repty P) = (term134 Repty P).
Proof. exact (@lem18394 Repty P). Qed.
Lemma lem27157 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term136 Repty r R).
Proof. exact (@lem27156 Repty (term115 Repty r R)). Qed.
Lemma lem27158 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem27159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27161 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term138 Repty r R x) = (term139 Repty r R x).
Proof. exact (MK_COMB (@lem27159) (@lem27158 Repty r R x)). Qed.
Lemma lem27162 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term140 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem27161 Repty r R x)). Qed.
Lemma lem27163 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem27164 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term136 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem27163 Repty) (@lem27162 Repty r R)). Qed.
Lemma lem27165 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term142 Repty r R).
Proof. exact (TRANS (@lem27157 Repty r R) (@lem27164 Repty r R)). Qed.
Lemma lem27166 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem27155 Repty r R x)). Qed.
Lemma lem27167 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27168 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem27167 Repty) (@lem27166 Repty r R)). Qed.
Lemma lem27169 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem27170 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem27171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27172 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term144 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem27171) (@lem27165 Repty r R)). Qed.
Lemma lem27173 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term146 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27172 Repty r R) (@lem27170 Absty Repty dest mk r)). Qed.
Lemma lem27174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27175 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term148 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem27174) (@lem27168 Repty r R)). Qed.
Lemma lem27176 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27175 Repty r R) (@lem27169 Absty Repty dest mk r)). Qed.
Lemma lem27177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27178 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term150 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27177) (@lem27176 Absty Repty R dest mk r)). Qed.
Lemma lem27179 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term151 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27178 Absty Repty R dest mk r) (@lem27173 Absty Repty R dest mk r)). Qed.
Lemma lem27180 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term151 Absty Repty R dest mk r).
Proof. exact (@lem17784 (term116 Repty r R) ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem27181 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term152 Absty Repty R dest mk r).
Proof. exact (TRANS (@lem27180 Absty Repty R dest mk r) (@lem27179 Absty Repty R dest mk r)). Qed.
Lemma lem27182 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem27181 Absty Repty R dest mk r)). Qed.
Lemma lem27183 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem27184 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27183 Repty) (@lem27182 Absty Repty R dest mk)). Qed.
Lemma lem27186 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem27187 {Repty : Type'} (P : type686 Repty) (Q : type686 Repty) : (term157 Repty P Q) = (term158 Repty P Q).
Proof. exact (@lem27186 (Repty -> Prop) P Q). Qed.
Lemma lem27188 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk).
Proof. exact (@lem27187 Repty (term161 Absty Repty R dest mk) (term162 Absty Repty R dest mk)). Qed.
Lemma lem27189 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem27190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27191 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term164 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27190) (@lem27189 Absty Repty R dest mk r)). Qed.
Lemma lem27192 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem27193 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term166 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27191 Absty Repty R dest mk r) (@lem27192 Absty Repty R dest mk r)). Qed.
Lemma lem27194 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term167 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem27193 Absty Repty R dest mk r)). Qed.
Lemma lem27195 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem27196 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27195 Repty) (@lem27194 Absty Repty R dest mk)). Qed.
Lemma lem27197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem27198 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term168 Absty Repty R dest mk) = (term169 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27197) (@lem27196 Absty Repty R dest mk)). Qed.
Lemma lem27199 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem27200 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term170 Absty Repty R dest mk) = (term161 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem27199 Absty Repty R dest mk r)). Qed.
Lemma lem27201 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem27202 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term171 Absty Repty R dest mk) = (term172 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27201 Repty) (@lem27200 Absty Repty R dest mk)). Qed.
Lemma lem27203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27204 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term173 Absty Repty R dest mk) = (term174 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27203) (@lem27202 Absty Repty R dest mk)). Qed.
Lemma lem27205 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem27206 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term175 Absty Repty R dest mk) = (term162 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem27205 Absty Repty R dest mk r)). Qed.
Lemma lem27207 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem27208 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term176 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27207 Repty) (@lem27206 Absty Repty R dest mk)). Qed.
Lemma lem27209 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term160 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27204 Absty Repty R dest mk) (@lem27208 Absty Repty R dest mk)). Qed.
Lemma lem27210 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk)) = ((term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem27198 Absty Repty R dest mk) (@lem27209 Absty Repty R dest mk)). Qed.
Lemma lem27211 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem27210 Absty Repty R dest mk) (@lem27188 Absty Repty R dest mk)). Qed.
Lemma lem27317 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem27318 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem27317 Repty P Q). Qed.
Lemma lem27319 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r).
Proof. exact (@lem27318 Repty (term115 Repty r R) (term143 Absty Repty dest mk r)). Qed.
Lemma lem27320 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem27321 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term183 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem27320 Repty r R x)). Qed.
Lemma lem27322 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27323 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term184 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem27322 Repty) (@lem27321 Repty r R)). Qed.
Lemma lem27324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27325 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term185 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem27324) (@lem27323 Repty r R)). Qed.
Lemma lem27326 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem27327 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27325 Repty r R) (@lem27326 Absty Repty dest mk r)). Qed.
Lemma lem27328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem27329 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term186 Absty Repty R dest mk r) = (term187 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27328) (@lem27327 Absty Repty R dest mk r)). Qed.
Lemma lem27330 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem27331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27332 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term188 Repty r R x) = (term189 Repty r R x).
Proof. exact (MK_COMB (@lem27331) (@lem27330 Repty r R x)). Qed.
Lemma lem27333 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem27334 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term190 Absty Repty R x dest mk r) = (term191 Absty Repty R x dest mk r).
Proof. exact (MK_COMB (@lem27332 Repty r R x) (@lem27333 Absty Repty dest mk r)). Qed.
Lemma lem27335 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term192 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem27334 Absty Repty R x dest mk r)). Qed.
Lemma lem27336 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27337 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term182 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27336 Repty) (@lem27335 Absty Repty R dest mk r)). Qed.
Lemma lem27338 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r)) = ((term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r)).
Proof. exact (MK_COMB (@lem27329 Absty Repty R dest mk r) (@lem27337 Absty Repty R dest mk r)). Qed.
Lemma lem27339 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (EQ_MP (@lem27338 Absty Repty R dest mk r) (@lem27319 Absty Repty R dest mk r)). Qed.
Lemma lem27340 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term161 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem27339 Absty Repty R dest mk r)). Qed.
Lemma lem27341 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem27342 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27341 Repty) (@lem27340 Absty Repty R dest mk)). Qed.
Lemma lem27344 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem27345 {Repty : Type'} (P : type672 Repty) : (term199 Repty P) = (term200 Repty P).
Proof. exact (@lem27344 (Repty -> Prop) Repty P). Qed.
Lemma lem27346 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk).
Proof. exact (@lem27345 Repty (term203 Absty Repty R dest mk)). Qed.
Lemma lem27347 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem27348 {Repty : Type'} (x : Repty) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem27349 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) (x : Repty) : (term205 Absty Repty R dest mk r x) = (term206 Absty Repty R dest mk r x).
Proof. exact (MK_COMB (@lem27347 Absty Repty R dest mk r) (@lem27348 Repty x)). Qed.
Lemma lem27350 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term206 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term206 Absty Repty R dest mk r x)). Qed.
Lemma lem27351 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term205 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem27349 Absty Repty R dest mk r x) (@lem27350 Absty Repty R x dest mk r)). Qed.
Lemma lem27352 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term207 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem27351 Absty Repty R x dest mk r)). Qed.
Lemma lem27353 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27354 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term208 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem27353 Repty) (@lem27352 Absty Repty R dest mk r)). Qed.
Lemma lem27355 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term209 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem27354 Absty Repty R dest mk r)). Qed.
Lemma lem27356 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem27357 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27356 Repty) (@lem27355 Absty Repty R dest mk)). Qed.
Lemma lem27358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem27359 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term210 Absty Repty R dest mk) = (term211 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27358) (@lem27357 Absty Repty R dest mk)). Qed.
Lemma lem27360 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem27361 {Repty : Type'} (x : type684 Repty) (r : Repty -> Prop) : (x r) = (x r).
Proof. exact (eq_refl (x r)). Qed.
Lemma lem27362 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : type684 Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term213 Absty Repty R dest mk x r).
Proof. exact (MK_COMB (@lem27360 Absty Repty R dest mk r) (@lem27361 Repty x r)). Qed.
Lemma lem27363 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term213 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term213 Absty Repty R dest mk x r)). Qed.
Lemma lem27364 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem27362 Absty Repty R dest mk x r) (@lem27363 Absty Repty R x dest mk r)). Qed.
Lemma lem27365 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term215 Absty Repty R dest mk x) = (term216 Absty Repty R x dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem27364 Absty Repty R x dest mk r)). Qed.
Lemma lem27366 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem27367 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term217 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem27366 Repty) (@lem27365 Absty Repty R x dest mk)). Qed.
Lemma lem27368 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term219 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem27367 Absty Repty R x dest mk)). Qed.
Lemma lem27369 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem27370 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term202 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27369 Repty) (@lem27368 Absty Repty R dest mk)). Qed.
Lemma lem27371 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk)) = ((term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem27359 Absty Repty R dest mk) (@lem27370 Absty Repty R dest mk)). Qed.
Lemma lem27372 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem27371 Absty Repty R dest mk) (@lem27346 Absty Repty R dest mk)). Qed.
Lemma lem27373 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (TRANS (@lem27342 Absty Repty R dest mk) (@lem27372 Absty Repty R dest mk)). Qed.
Lemma lem27374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27375 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term174 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27374) (@lem27373 Absty Repty R dest mk)). Qed.
Lemma lem27376 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem27377 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27375 Absty Repty R dest mk) (@lem27376 Absty Repty R dest mk)). Qed.
Lemma lem27379 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem27380 {Repty : Type'} (P : type162 Repty) (Q : Prop) : (term226 Repty P Q) = (term227 Repty P Q).
Proof. exact (@lem27379 (type684 Repty) P Q). Qed.
Lemma lem27381 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk).
Proof. exact (@lem27380 Repty (term220 Absty Repty R dest mk) (term177 Absty Repty R dest mk)). Qed.
Lemma lem27382 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem27383 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term231 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem27382 Absty Repty R x dest mk)). Qed.
Lemma lem27384 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem27385 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term232 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27384 Repty) (@lem27383 Absty Repty R dest mk)). Qed.
Lemma lem27386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27387 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term233 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27386) (@lem27385 Absty Repty R dest mk)). Qed.
Lemma lem27388 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem27389 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27387 Absty Repty R dest mk) (@lem27388 Absty Repty R dest mk)). Qed.
Lemma lem27390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem27391 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term234 Absty Repty R dest mk) = (term235 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27390) (@lem27389 Absty Repty R dest mk)). Qed.
Lemma lem27392 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem27393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27394 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term236 Absty Repty R dest mk x) = (term237 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem27393) (@lem27392 Absty Repty R x dest mk)). Qed.
Lemma lem27395 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem27396 {Absty Repty : Type'} (x : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term238 Absty Repty x R dest mk) = (term239 Absty Repty x R dest mk).
Proof. exact (MK_COMB (@lem27394 Absty Repty R x dest mk) (@lem27395 Absty Repty R dest mk)). Qed.
Lemma lem27397 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term240 Absty Repty R dest mk) = (term241 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem27396 Absty Repty x R dest mk)). Qed.
Lemma lem27398 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem27399 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term229 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem27398 Repty) (@lem27397 Absty Repty R dest mk)). Qed.
Lemma lem27400 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk)) = ((term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem27391 Absty Repty R dest mk) (@lem27399 Absty Repty R dest mk)). Qed.
Lemma lem27401 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem27400 Absty Repty R dest mk) (@lem27381 Absty Repty R dest mk)). Qed.
Lemma lem27402 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem27377 Absty Repty R dest mk) (@lem27401 Absty Repty R dest mk)). Qed.
Lemma lem27403 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem27211 Absty Repty R dest mk) (@lem27402 Absty Repty R dest mk)). Qed.
Lemma lem27404 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem27184 Absty Repty R dest mk) (@lem27403 Absty Repty R dest mk)). Qed.
Lemma lem27405 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term242 Absty Repty R dest mk.
Proof. exact (EQ_MP (@lem27404 Absty Repty R dest mk) (@lem26751 Absty Repty R dest mk h1)). Qed.
Lemma lem27709 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term479 Repty x R y x') = (term480 Repty x R y x').
Proof. exact (@lem17930 (R x x') (R y x')). Qed.
Lemma lem27720 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : ((R x x') = (R y x')) = (term481 Repty x R y x').
Proof. exact (@lem17784 (R x x') (R y x')). Qed.
Lemma lem27721 {Repty : Type'} (P : Repty -> Prop) : (term482 Repty P) = (term483 Repty P).
Proof. exact (@lem18392 Repty P). Qed.
Lemma lem27722 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term484 Repty x R y) = (term485 Repty x R y).
Proof. exact (@lem27721 Repty (term415 Repty x R y)). Qed.
Lemma lem27723 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term486 Repty x R y x') = ((R x x') = (R y x')).
Proof. exact (eq_refl (term486 Repty x R y x')). Qed.
Lemma lem27724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27725 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term487 Repty x R y x') = (term479 Repty x R y x').
Proof. exact (MK_COMB (@lem27724) (@lem27723 Repty x R y x')). Qed.
Lemma lem27726 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term487 Repty x R y x') = (term480 Repty x R y x').
Proof. exact (TRANS (@lem27725 Repty x R y x') (@lem27709 Repty x R y x')). Qed.
Lemma lem27727 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term488 Repty x R y) = (term489 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem27726 Repty x R y x')). Qed.
Lemma lem27728 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27729 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term485 Repty x R y) = (term490 Repty x R y).
Proof. exact (MK_COMB (@lem27728 Repty) (@lem27727 Repty x R y)). Qed.
Lemma lem27730 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term484 Repty x R y) = (term490 Repty x R y).
Proof. exact (TRANS (@lem27722 Repty x R y) (@lem27729 Repty x R y)). Qed.
Lemma lem27731 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term415 Repty x R y) = (term491 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem27720 Repty x R y x')). Qed.
Lemma lem27732 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem27733 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term365 Repty x R y) = (term492 Repty x R y).
Proof. exact (MK_COMB (@lem27732 Repty) (@lem27731 Repty x R y)). Qed.
Lemma lem27735 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term493 Repty R x y) = (term493 Repty R x y).
Proof. exact (eq_refl (term493 Repty R x y)). Qed.
Lemma lem27736 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term494 Repty x R y) = (term495 Repty x R y).
Proof. exact (MK_COMB (@lem27735 Repty R x y) (@lem27733 Repty x R y)). Qed.
Lemma lem27738 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term496 Repty R x y) = (term496 Repty R x y).
Proof. exact (eq_refl (term496 Repty R x y)). Qed.
Lemma lem27739 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term497 Repty x R y) = (term498 Repty x R y).
Proof. exact (MK_COMB (@lem27738 Repty R x y) (@lem27730 Repty x R y)). Qed.
Lemma lem27740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27741 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term499 Repty x R y) = (term500 Repty x R y).
Proof. exact (MK_COMB (@lem27740) (@lem27739 Repty x R y)). Qed.
Lemma lem27742 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term501 Repty x R y) = (term502 Repty x R y).
Proof. exact (MK_COMB (@lem27741 Repty x R y) (@lem27736 Repty x R y)). Qed.
Lemma lem27743 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term503 Repty x R y) = (term501 Repty x R y).
Proof. exact (@lem17646 (R x y) (term365 Repty x R y)). Qed.
Lemma lem27744 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term503 Repty x R y) = (term502 Repty x R y).
Proof. exact (TRANS (@lem27743 Repty x R y) (@lem27742 Repty x R y)). Qed.
Lemma lem27745 {Repty : Type'} (P : Repty -> Prop) : (term482 Repty P) = (term483 Repty P).
Proof. exact (@lem18392 Repty P). Qed.
Lemma lem27746 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term504 Repty x R) = (term505 Repty x R).
Proof. exact (@lem27745 Repty (term366 Repty x R)). Qed.
Lemma lem27747 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term506 Repty x R y) = ((R x y) = (term365 Repty x R y)).
Proof. exact (eq_refl (term506 Repty x R y)). Qed.
Lemma lem27748 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27749 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term507 Repty x R y) = (term503 Repty x R y).
Proof. exact (MK_COMB (@lem27748) (@lem27747 Repty x R y)). Qed.
Lemma lem27750 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term507 Repty x R y) = (term502 Repty x R y).
Proof. exact (TRANS (@lem27749 Repty x R y) (@lem27744 Repty x R y)). Qed.
Lemma lem27751 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term508 Repty x R) = (term509 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem27750 Repty x R y)). Qed.
Lemma lem27752 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27753 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term505 Repty x R) = (term510 Repty x R).
Proof. exact (MK_COMB (@lem27752 Repty) (@lem27751 Repty x R)). Qed.
Lemma lem27754 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term504 Repty x R) = (term510 Repty x R).
Proof. exact (TRANS (@lem27746 Repty x R) (@lem27753 Repty x R)). Qed.
Lemma lem27755 {Repty : Type'} (P : Repty -> Prop) : (term482 Repty P) = (term483 Repty P).
Proof. exact (@lem18392 Repty P). Qed.
Lemma lem27756 {Repty : Type'} (R : type1402 Repty) : (term511 Repty R) = (term512 Repty R).
Proof. exact (@lem27755 Repty (term368 Repty R)). Qed.
Lemma lem27757 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term513 Repty R x) = (term367 Repty x R).
Proof. exact (eq_refl (term513 Repty R x)). Qed.
Lemma lem27758 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27759 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term514 Repty R x) = (term504 Repty x R).
Proof. exact (MK_COMB (@lem27758) (@lem27757 Repty x R)). Qed.
Lemma lem27760 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term514 Repty R x) = (term510 Repty x R).
Proof. exact (TRANS (@lem27759 Repty x R) (@lem27754 Repty x R)). Qed.
Lemma lem27761 {Repty : Type'} (R : type1402 Repty) : (term515 Repty R) = (term516 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem27760 Repty x R)). Qed.
Lemma lem27762 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27763 {Repty : Type'} (R : type1402 Repty) : (term512 Repty R) = (term517 Repty R).
Proof. exact (MK_COMB (@lem27762 Repty) (@lem27761 Repty R)). Qed.
Lemma lem27764 {Repty : Type'} (R : type1402 Repty) : (term511 Repty R) = (term517 Repty R).
Proof. exact (TRANS (@lem27756 Repty R) (@lem27763 Repty R)). Qed.
Lemma lem27766 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term405 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term405 Absty Repty P mk R x)). Qed.
Lemma lem27767 {Repty : Type'} (P : Repty -> Prop) : (term482 Repty P) = (term483 Repty P).
Proof. exact (@lem18392 Repty P). Qed.
Lemma lem27768 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term518 Absty Repty P mk R) = (term519 Absty Repty P mk R).
Proof. exact (@lem27767 Repty (term406 Absty Repty P mk R)). Qed.
Lemma lem27769 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term520 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term520 Absty Repty P mk R x)). Qed.
Lemma lem27770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27772 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term521 Absty Repty P mk R x) = (term522 Absty Repty P mk R x).
Proof. exact (MK_COMB (@lem27770) (@lem27769 Absty Repty P mk R x)). Qed.
Lemma lem27773 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term523 Absty Repty P mk R) = (term524 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem27772 Absty Repty P mk R x)). Qed.
Lemma lem27774 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27775 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term519 Absty Repty P mk R) = (term525 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27774 Repty) (@lem27773 Absty Repty P mk R)). Qed.
Lemma lem27776 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term518 Absty Repty P mk R) = (term525 Absty Repty P mk R).
Proof. exact (TRANS (@lem27768 Absty Repty P mk R) (@lem27775 Absty Repty P mk R)). Qed.
Lemma lem27777 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term406 Absty Repty P mk R) = (term406 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem27766 Absty Repty P mk R x)). Qed.
Lemma lem27778 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem27779 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term411 Absty Repty P mk R) = (term411 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27778 Repty) (@lem27777 Absty Repty P mk R)). Qed.
Lemma lem27781 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem27782 {Absty : Type'} (P : Absty -> Prop) : (term482 Absty P) = (term483 Absty P).
Proof. exact (@lem18392 Absty P). Qed.
Lemma lem27783 {Absty : Type'} (P : Absty -> Prop) : (term526 Absty P) = (term527 Absty P).
Proof. exact (@lem27782 Absty (term403 Absty P)). Qed.
Lemma lem27784 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term528 Absty P x) = (P x).
Proof. exact (eq_refl (term528 Absty P x)). Qed.
Lemma lem27785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27787 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term529 Absty P x) = (term530 Absty P x).
Proof. exact (MK_COMB (@lem27785) (@lem27784 Absty P x)). Qed.
Lemma lem27788 {Absty : Type'} (P : Absty -> Prop) : (term531 Absty P) = (term532 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem27787 Absty P x)). Qed.
Lemma lem27789 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem27790 {Absty : Type'} (P : Absty -> Prop) : (term527 Absty P) = (term483 Absty P).
Proof. exact (MK_COMB (@lem27789 Absty) (@lem27788 Absty P)). Qed.
Lemma lem27791 {Absty : Type'} (P : Absty -> Prop) : (term526 Absty P) = (term483 Absty P).
Proof. exact (TRANS (@lem27783 Absty P) (@lem27790 Absty P)). Qed.
Lemma lem27792 {Absty : Type'} (P : Absty -> Prop) : (term403 Absty P) = (term403 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem27781 Absty P x)). Qed.
Lemma lem27793 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem27794 {Absty : Type'} (P : Absty -> Prop) : (term410 Absty P) = (term410 Absty P).
Proof. exact (MK_COMB (@lem27793 Absty) (@lem27792 Absty P)). Qed.
Lemma lem27795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27796 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term533 Absty Repty P mk R) = (term534 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27795) (@lem27776 Absty Repty P mk R)). Qed.
Lemma lem27797 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term535 Absty Repty mk R P) = (term536 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27796 Absty Repty P mk R) (@lem27794 Absty P)). Qed.
Lemma lem27798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27799 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term537 Absty Repty P mk R) = (term537 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27798) (@lem27779 Absty Repty P mk R)). Qed.
Lemma lem27800 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term538 Absty Repty mk R P) = (term539 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27799 Absty Repty P mk R) (@lem27791 Absty P)). Qed.
Lemma lem27801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27802 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term540 Absty Repty mk R P) = (term541 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27801) (@lem27800 Absty Repty mk R P)). Qed.
Lemma lem27803 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term542 Absty Repty mk R P) = (term543 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27802 Absty Repty mk R P) (@lem27797 Absty Repty mk R P)). Qed.
Lemma lem27804 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term544 Absty Repty mk R P) = (term542 Absty Repty mk R P).
Proof. exact (@lem17646 (term411 Absty Repty P mk R) (term410 Absty P)). Qed.
Lemma lem27805 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term544 Absty Repty mk R P) = (term543 Absty Repty mk R P).
Proof. exact (TRANS (@lem27804 Absty Repty mk R P) (@lem27803 Absty Repty mk R P)). Qed.
Lemma lem27806 {Absty : Type'} (P : type686 Absty) : (term545 Absty P) = (term546 Absty P).
Proof. exact (@lem18392 (Absty -> Prop) P). Qed.
Lemma lem27807 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term547 Absty Repty mk R) = (term548 Absty Repty mk R).
Proof. exact (@lem27806 Absty (term413 Absty Repty mk R)). Qed.
Lemma lem27808 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term549 Absty Repty mk R P) = ((term411 Absty Repty P mk R) = (term410 Absty P)).
Proof. exact (eq_refl (term549 Absty Repty mk R P)). Qed.
Lemma lem27809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27810 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term550 Absty Repty mk R P) = (term544 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27809) (@lem27808 Absty Repty mk R P)). Qed.
Lemma lem27811 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term550 Absty Repty mk R P) = (term543 Absty Repty mk R P).
Proof. exact (TRANS (@lem27810 Absty Repty mk R P) (@lem27805 Absty Repty mk R P)). Qed.
Lemma lem27812 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term551 Absty Repty mk R) = (term552 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem27811 Absty Repty mk R P)). Qed.
Lemma lem27813 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem27814 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term548 Absty Repty mk R) = (term553 Absty Repty mk R).
Proof. exact (MK_COMB (@lem27813 Absty) (@lem27812 Absty Repty mk R)). Qed.
Lemma lem27815 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term547 Absty Repty mk R) = (term553 Absty Repty mk R).
Proof. exact (TRANS (@lem27807 Absty Repty mk R) (@lem27814 Absty Repty mk R)). Qed.
Lemma lem27817 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term405 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term405 Absty Repty P mk R x)). Qed.
Lemma lem27818 {Repty : Type'} (P : Repty -> Prop) : (term133 Repty P) = (term134 Repty P).
Proof. exact (@lem18394 Repty P). Qed.
Lemma lem27819 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term554 Absty Repty P mk R) = (term555 Absty Repty P mk R).
Proof. exact (@lem27818 Repty (term406 Absty Repty P mk R)). Qed.
Lemma lem27820 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term520 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term520 Absty Repty P mk R x)). Qed.
Lemma lem27821 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27823 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term521 Absty Repty P mk R x) = (term522 Absty Repty P mk R x).
Proof. exact (MK_COMB (@lem27821) (@lem27820 Absty Repty P mk R x)). Qed.
Lemma lem27824 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term523 Absty Repty P mk R) = (term524 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem27823 Absty Repty P mk R x)). Qed.
Lemma lem27825 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem27826 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term555 Absty Repty P mk R) = (term556 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27825 Repty) (@lem27824 Absty Repty P mk R)). Qed.
Lemma lem27827 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term554 Absty Repty P mk R) = (term556 Absty Repty P mk R).
Proof. exact (TRANS (@lem27819 Absty Repty P mk R) (@lem27826 Absty Repty P mk R)). Qed.
Lemma lem27828 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term406 Absty Repty P mk R) = (term406 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem27817 Absty Repty P mk R x)). Qed.
Lemma lem27829 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27830 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term407 Absty Repty P mk R) = (term407 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27829 Repty) (@lem27828 Absty Repty P mk R)). Qed.
Lemma lem27832 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem27833 {Absty : Type'} (P : Absty -> Prop) : (term133 Absty P) = (term134 Absty P).
Proof. exact (@lem18394 Absty P). Qed.
Lemma lem27834 {Absty : Type'} (P : Absty -> Prop) : (term557 Absty P) = (term558 Absty P).
Proof. exact (@lem27833 Absty (term403 Absty P)). Qed.
Lemma lem27835 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term528 Absty P x) = (P x).
Proof. exact (eq_refl (term528 Absty P x)). Qed.
Lemma lem27836 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27838 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term529 Absty P x) = (term530 Absty P x).
Proof. exact (MK_COMB (@lem27836) (@lem27835 Absty P x)). Qed.
Lemma lem27839 {Absty : Type'} (P : Absty -> Prop) : (term531 Absty P) = (term532 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem27838 Absty P x)). Qed.
Lemma lem27840 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem27841 {Absty : Type'} (P : Absty -> Prop) : (term558 Absty P) = (term134 Absty P).
Proof. exact (MK_COMB (@lem27840 Absty) (@lem27839 Absty P)). Qed.
Lemma lem27842 {Absty : Type'} (P : Absty -> Prop) : (term557 Absty P) = (term134 Absty P).
Proof. exact (TRANS (@lem27834 Absty P) (@lem27841 Absty P)). Qed.
Lemma lem27843 {Absty : Type'} (P : Absty -> Prop) : (term403 Absty P) = (term403 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem27832 Absty P x)). Qed.
Lemma lem27844 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem27845 {Absty : Type'} (P : Absty -> Prop) : (term404 Absty P) = (term404 Absty P).
Proof. exact (MK_COMB (@lem27844 Absty) (@lem27843 Absty P)). Qed.
Lemma lem27846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27847 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term559 Absty Repty P mk R) = (term560 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27846) (@lem27827 Absty Repty P mk R)). Qed.
Lemma lem27848 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term561 Absty Repty mk R P) = (term562 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27847 Absty Repty P mk R) (@lem27845 Absty P)). Qed.
Lemma lem27849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem27850 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term563 Absty Repty P mk R) = (term563 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem27849) (@lem27830 Absty Repty P mk R)). Qed.
Lemma lem27851 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term564 Absty Repty mk R P) = (term565 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27850 Absty Repty P mk R) (@lem27842 Absty P)). Qed.
Lemma lem27852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27853 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term566 Absty Repty mk R P) = (term567 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27852) (@lem27851 Absty Repty mk R P)). Qed.
Lemma lem27854 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term568 Absty Repty mk R P) = (term569 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27853 Absty Repty mk R P) (@lem27848 Absty Repty mk R P)). Qed.
Lemma lem27855 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term570 Absty Repty mk R P) = (term568 Absty Repty mk R P).
Proof. exact (@lem17646 (term407 Absty Repty P mk R) (term404 Absty P)). Qed.
Lemma lem27856 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term570 Absty Repty mk R P) = (term569 Absty Repty mk R P).
Proof. exact (TRANS (@lem27855 Absty Repty mk R P) (@lem27854 Absty Repty mk R P)). Qed.
Lemma lem27857 {Absty : Type'} (P : type686 Absty) : (term545 Absty P) = (term546 Absty P).
Proof. exact (@lem18392 (Absty -> Prop) P). Qed.
Lemma lem27858 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term571 Absty Repty mk R) = (term572 Absty Repty mk R).
Proof. exact (@lem27857 Absty (term409 Absty Repty mk R)). Qed.
Lemma lem27859 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term573 Absty Repty mk R P) = ((term407 Absty Repty P mk R) = (term404 Absty P)).
Proof. exact (eq_refl (term573 Absty Repty mk R P)). Qed.
Lemma lem27860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem27861 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term574 Absty Repty mk R P) = (term570 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem27860) (@lem27859 Absty Repty mk R P)). Qed.
Lemma lem27862 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term574 Absty Repty mk R P) = (term569 Absty Repty mk R P).
Proof. exact (TRANS (@lem27861 Absty Repty mk R P) (@lem27856 Absty Repty mk R P)). Qed.
Lemma lem27863 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term575 Absty Repty mk R) = (term576 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem27862 Absty Repty mk R P)). Qed.
Lemma lem27864 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem27865 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term572 Absty Repty mk R) = (term577 Absty Repty mk R).
Proof. exact (MK_COMB (@lem27864 Absty) (@lem27863 Absty Repty mk R)). Qed.
Lemma lem27866 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term571 Absty Repty mk R) = (term577 Absty Repty mk R).
Proof. exact (TRANS (@lem27858 Absty Repty mk R) (@lem27865 Absty Repty mk R)). Qed.
Lemma lem27867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27868 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term578 Absty Repty mk R) = (term579 Absty Repty mk R).
Proof. exact (MK_COMB (@lem27867) (@lem27815 Absty Repty mk R)). Qed.
Lemma lem27869 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term580 Absty Repty mk R) = (term581 Absty Repty mk R).
Proof. exact (MK_COMB (@lem27868 Absty Repty mk R) (@lem27866 Absty Repty mk R)). Qed.
Lemma lem27870 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term582 Absty Repty mk R) = (term580 Absty Repty mk R).
Proof. exact (@lem17045 (term346 Absty Repty mk R) (term347 Absty Repty mk R)). Qed.
Lemma lem27871 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term582 Absty Repty mk R) = (term581 Absty Repty mk R).
Proof. exact (TRANS (@lem27870 Absty Repty mk R) (@lem27869 Absty Repty mk R)). Qed.
Lemma lem27872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27873 {Repty : Type'} (R : type1402 Repty) : (term583 Repty R) = (term584 Repty R).
Proof. exact (MK_COMB (@lem27872) (@lem27764 Repty R)). Qed.
Lemma lem27874 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term585 Absty Repty mk R) = (term586 Absty Repty mk R).
Proof. exact (MK_COMB (@lem27873 Repty R) (@lem27871 Absty Repty mk R)). Qed.
Lemma lem27875 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term373 Absty Repty mk R) = (term585 Absty Repty mk R).
Proof. exact (@lem17045 (term369 Repty R) (term361 Absty Repty mk R)). Qed.
Lemma lem27876 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term373 Absty Repty mk R) = (term586 Absty Repty mk R).
Proof. exact (TRANS (@lem27875 Absty Repty mk R) (@lem27874 Absty Repty mk R)). Qed.
Lemma lem27882 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem27883 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term587 Repty P Q) = (term588 Repty P Q).
Proof. exact (@lem27882 Repty P Q). Qed.
Lemma lem27884 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term589 Repty x R) = (term590 Repty x R).
Proof. exact (@lem27883 Repty (term591 Repty x R) (term592 Repty x R)). Qed.
Lemma lem27885 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term593 Repty x R y) = (term498 Repty x R y).
Proof. exact (eq_refl (term593 Repty x R y)). Qed.
Lemma lem27886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27887 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term594 Repty x R y) = (term500 Repty x R y).
Proof. exact (MK_COMB (@lem27886) (@lem27885 Repty x R y)). Qed.
Lemma lem27888 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term595 Repty x R y) = (term495 Repty x R y).
Proof. exact (eq_refl (term595 Repty x R y)). Qed.
Lemma lem27889 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term596 Repty x R y) = (term502 Repty x R y).
Proof. exact (MK_COMB (@lem27887 Repty x R y) (@lem27888 Repty x R y)). Qed.
Lemma lem27890 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term597 Repty x R) = (term509 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem27889 Repty x R y)). Qed.
Lemma lem27891 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27892 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term589 Repty x R) = (term510 Repty x R).
Proof. exact (MK_COMB (@lem27891 Repty) (@lem27890 Repty x R)). Qed.
Lemma lem27893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem27894 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term598 Repty x R) = (term599 Repty x R).
Proof. exact (MK_COMB (@lem27893) (@lem27892 Repty x R)). Qed.
Lemma lem27895 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term593 Repty x R y) = (term498 Repty x R y).
Proof. exact (eq_refl (term593 Repty x R y)). Qed.
Lemma lem27896 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term600 Repty x R) = (term591 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem27895 Repty x R y)). Qed.
Lemma lem27897 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27898 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term601 Repty x R) = (term602 Repty x R).
Proof. exact (MK_COMB (@lem27897 Repty) (@lem27896 Repty x R)). Qed.
Lemma lem27899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem27900 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term603 Repty x R) = (term604 Repty x R).
Proof. exact (MK_COMB (@lem27899) (@lem27898 Repty x R)). Qed.
Lemma lem27901 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term595 Repty x R y) = (term495 Repty x R y).
Proof. exact (eq_refl (term595 Repty x R y)). Qed.
Lemma lem27902 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term605 Repty x R) = (term592 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem27901 Repty x R y)). Qed.
Lemma lem27903 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem27904 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term606 Repty x R) = (term607 Repty x R).
Proof. exact (MK_COMB (@lem27903 Repty) (@lem27902 Repty x R)). Qed.
Lemma lem27905 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term590 Repty x R) = (term608 Repty x R).
Proof. exact (MK_COMB (@lem27900 Repty x R) (@lem27904 Repty x R)). Qed.
Lemma lem27906 {Repty : Type'} (x : Repty) (R : type1402 Repty) : ((term589 Repty x R) = (term590 Repty x R)) = ((term510 Repty x R) = (term608 Repty x R)).
Proof. exact (MK_COMB (@lem27894 Repty x R) (@lem27905 Repty x R)). Qed.
Lemma lem27907 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term510 Repty x R) = (term608 Repty x R).
Proof. exact (EQ_MP (@lem27906 Repty x R) (@lem27884 Repty x R)). Qed.
Lemma lem28053 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem28054 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term155 Repty P Q) = (term156 Repty P Q).
Proof. exact (@lem28053 Repty P Q). Qed.
Lemma lem28055 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term609 Repty x R y) = (term610 Repty x R y).
Proof. exact (@lem28054 Repty (term611 Repty x R y) (term612 Repty x R y)). Qed.
Lemma lem28056 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term613 Repty x R y x') = (term614 Repty x R y x').
Proof. exact (eq_refl (term613 Repty x R y x')). Qed.
Lemma lem28057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem28058 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term615 Repty x R y x') = (term616 Repty x R y x').
Proof. exact (MK_COMB (@lem28057) (@lem28056 Repty x R y x')). Qed.
Lemma lem28059 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term617 Repty x R y x') = (term618 Repty x R y x').
Proof. exact (eq_refl (term617 Repty x R y x')). Qed.
Lemma lem28060 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term619 Repty x R y x') = (term481 Repty x R y x').
Proof. exact (MK_COMB (@lem28058 Repty x R y x') (@lem28059 Repty x R y x')). Qed.
Lemma lem28061 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term620 Repty x R y) = (term491 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem28060 Repty x R y x')). Qed.
Lemma lem28062 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem28063 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term609 Repty x R y) = (term492 Repty x R y).
Proof. exact (MK_COMB (@lem28062 Repty) (@lem28061 Repty x R y)). Qed.
Lemma lem28064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28065 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term621 Repty x R y) = (term622 Repty x R y).
Proof. exact (MK_COMB (@lem28064) (@lem28063 Repty x R y)). Qed.
Lemma lem28066 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term613 Repty x R y x') = (term614 Repty x R y x').
Proof. exact (eq_refl (term613 Repty x R y x')). Qed.
Lemma lem28067 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term623 Repty x R y) = (term611 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem28066 Repty x R y x')). Qed.
Lemma lem28068 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem28069 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term624 Repty x R y) = (term625 Repty x R y).
Proof. exact (MK_COMB (@lem28068 Repty) (@lem28067 Repty x R y)). Qed.
Lemma lem28070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem28071 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term626 Repty x R y) = (term627 Repty x R y).
Proof. exact (MK_COMB (@lem28070) (@lem28069 Repty x R y)). Qed.
Lemma lem28072 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term617 Repty x R y x') = (term618 Repty x R y x').
Proof. exact (eq_refl (term617 Repty x R y x')). Qed.
Lemma lem28073 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term628 Repty x R y) = (term612 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem28072 Repty x R y x')). Qed.
Lemma lem28074 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem28075 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term629 Repty x R y) = (term630 Repty x R y).
Proof. exact (MK_COMB (@lem28074 Repty) (@lem28073 Repty x R y)). Qed.
Lemma lem28076 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term610 Repty x R y) = (term631 Repty x R y).
Proof. exact (MK_COMB (@lem28071 Repty x R y) (@lem28075 Repty x R y)). Qed.
Lemma lem28077 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : ((term609 Repty x R y) = (term610 Repty x R y)) = ((term492 Repty x R y) = (term631 Repty x R y)).
Proof. exact (MK_COMB (@lem28065 Repty x R y) (@lem28076 Repty x R y)). Qed.
Lemma lem28078 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term492 Repty x R y) = (term631 Repty x R y).
Proof. exact (EQ_MP (@lem28077 Repty x R y) (@lem28055 Repty x R y)). Qed.
Lemma lem28175 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term493 Repty R x y) = (term493 Repty R x y).
Proof. exact (eq_refl (term493 Repty R x y)). Qed.
Lemma lem28176 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term495 Repty x R y) = (term632 Repty x R y).
Proof. exact (MK_COMB (@lem28175 Repty R x y) (@lem28078 Repty x R y)). Qed.
Lemma lem28177 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term592 Repty x R) = (term633 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem28176 Repty x R y)). Qed.
Lemma lem28178 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28179 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term607 Repty x R) = (term634 Repty x R).
Proof. exact (MK_COMB (@lem28178 Repty) (@lem28177 Repty x R)). Qed.
Lemma lem28228 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term604 Repty x R) = (term604 Repty x R).
Proof. exact (eq_refl (term604 Repty x R)). Qed.
Lemma lem28229 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term608 Repty x R) = (term635 Repty x R).
Proof. exact (MK_COMB (@lem28228 Repty x R) (@lem28179 Repty x R)). Qed.
Lemma lem28230 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term510 Repty x R) = (term635 Repty x R).
Proof. exact (TRANS (@lem27907 Repty x R) (@lem28229 Repty x R)). Qed.
Lemma lem28231 {Repty : Type'} (R : type1402 Repty) : (term516 Repty R) = (term636 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28230 Repty x R)). Qed.
Lemma lem28232 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28233 {Repty : Type'} (R : type1402 Repty) : (term517 Repty R) = (term637 Repty R).
Proof. exact (MK_COMB (@lem28232 Repty) (@lem28231 Repty R)). Qed.
Lemma lem28235 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem28236 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term587 Repty P Q) = (term588 Repty P Q).
Proof. exact (@lem28235 Repty P Q). Qed.
Lemma lem28237 {Repty : Type'} (R : type1402 Repty) : (term638 Repty R) = (term639 Repty R).
Proof. exact (@lem28236 Repty (term640 Repty R) (term641 Repty R)). Qed.
Lemma lem28238 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term642 Repty R x) = (term602 Repty x R).
Proof. exact (eq_refl (term642 Repty R x)). Qed.
Lemma lem28239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28240 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term643 Repty R x) = (term604 Repty x R).
Proof. exact (MK_COMB (@lem28239) (@lem28238 Repty x R)). Qed.
Lemma lem28241 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term644 Repty R x) = (term634 Repty x R).
Proof. exact (eq_refl (term644 Repty R x)). Qed.
Lemma lem28242 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term645 Repty R x) = (term635 Repty x R).
Proof. exact (MK_COMB (@lem28240 Repty x R) (@lem28241 Repty x R)). Qed.
Lemma lem28243 {Repty : Type'} (R : type1402 Repty) : (term646 Repty R) = (term636 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28242 Repty x R)). Qed.
Lemma lem28244 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28245 {Repty : Type'} (R : type1402 Repty) : (term638 Repty R) = (term637 Repty R).
Proof. exact (MK_COMB (@lem28244 Repty) (@lem28243 Repty R)). Qed.
Lemma lem28246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28247 {Repty : Type'} (R : type1402 Repty) : (term647 Repty R) = (term648 Repty R).
Proof. exact (MK_COMB (@lem28246) (@lem28245 Repty R)). Qed.
Lemma lem28248 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term642 Repty R x) = (term602 Repty x R).
Proof. exact (eq_refl (term642 Repty R x)). Qed.
Lemma lem28249 {Repty : Type'} (R : type1402 Repty) : (term649 Repty R) = (term640 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28248 Repty x R)). Qed.
Lemma lem28250 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28251 {Repty : Type'} (R : type1402 Repty) : (term650 Repty R) = (term651 Repty R).
Proof. exact (MK_COMB (@lem28250 Repty) (@lem28249 Repty R)). Qed.
Lemma lem28252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28253 {Repty : Type'} (R : type1402 Repty) : (term652 Repty R) = (term653 Repty R).
Proof. exact (MK_COMB (@lem28252) (@lem28251 Repty R)). Qed.
Lemma lem28254 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term644 Repty R x) = (term634 Repty x R).
Proof. exact (eq_refl (term644 Repty R x)). Qed.
Lemma lem28255 {Repty : Type'} (R : type1402 Repty) : (term654 Repty R) = (term641 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28254 Repty x R)). Qed.
Lemma lem28256 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28257 {Repty : Type'} (R : type1402 Repty) : (term655 Repty R) = (term656 Repty R).
Proof. exact (MK_COMB (@lem28256 Repty) (@lem28255 Repty R)). Qed.
Lemma lem28258 {Repty : Type'} (R : type1402 Repty) : (term639 Repty R) = (term657 Repty R).
Proof. exact (MK_COMB (@lem28253 Repty R) (@lem28257 Repty R)). Qed.
Lemma lem28259 {Repty : Type'} (R : type1402 Repty) : ((term638 Repty R) = (term639 Repty R)) = ((term637 Repty R) = (term657 Repty R)).
Proof. exact (MK_COMB (@lem28247 Repty R) (@lem28258 Repty R)). Qed.
Lemma lem28260 {Repty : Type'} (R : type1402 Repty) : (term637 Repty R) = (term657 Repty R).
Proof. exact (EQ_MP (@lem28259 Repty R) (@lem28237 Repty R)). Qed.
Lemma lem28509 {Repty : Type'} (R : type1402 Repty) : (term517 Repty R) = (term657 Repty R).
Proof. exact (TRANS (@lem28233 Repty R) (@lem28260 Repty R)). Qed.
Lemma lem28510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28511 {Repty : Type'} (R : type1402 Repty) : (term584 Repty R) = (term658 Repty R).
Proof. exact (MK_COMB (@lem28510) (@lem28509 Repty R)). Qed.
Lemma lem28513 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem28514 {Absty : Type'} (P : type686 Absty) (Q : type686 Absty) : (term659 Absty P Q) = (term660 Absty P Q).
Proof. exact (@lem28513 (Absty -> Prop) P Q). Qed.
Lemma lem28515 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term661 Absty Repty mk R) = (term662 Absty Repty mk R).
Proof. exact (@lem28514 Absty (term663 Absty Repty mk R) (term664 Absty Repty mk R)). Qed.
Lemma lem28516 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term665 Absty Repty mk R P) = (term539 Absty Repty mk R P).
Proof. exact (eq_refl (term665 Absty Repty mk R P)). Qed.
Lemma lem28517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28518 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term666 Absty Repty mk R P) = (term541 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28517) (@lem28516 Absty Repty mk R P)). Qed.
Lemma lem28519 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term667 Absty Repty mk R P) = (term536 Absty Repty mk R P).
Proof. exact (eq_refl (term667 Absty Repty mk R P)). Qed.
Lemma lem28520 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term668 Absty Repty mk R P) = (term543 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28518 Absty Repty mk R P) (@lem28519 Absty Repty mk R P)). Qed.
Lemma lem28521 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term669 Absty Repty mk R) = (term552 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28520 Absty Repty mk R P)). Qed.
Lemma lem28522 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28523 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term661 Absty Repty mk R) = (term553 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28522 Absty) (@lem28521 Absty Repty mk R)). Qed.
Lemma lem28524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28525 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term670 Absty Repty mk R) = (term671 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28524) (@lem28523 Absty Repty mk R)). Qed.
Lemma lem28526 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term665 Absty Repty mk R P) = (term539 Absty Repty mk R P).
Proof. exact (eq_refl (term665 Absty Repty mk R P)). Qed.
Lemma lem28527 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term672 Absty Repty mk R) = (term663 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28526 Absty Repty mk R P)). Qed.
Lemma lem28528 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28529 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term673 Absty Repty mk R) = (term674 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28528 Absty) (@lem28527 Absty Repty mk R)). Qed.
Lemma lem28530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28531 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term675 Absty Repty mk R) = (term676 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28530) (@lem28529 Absty Repty mk R)). Qed.
Lemma lem28532 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term667 Absty Repty mk R P) = (term536 Absty Repty mk R P).
Proof. exact (eq_refl (term667 Absty Repty mk R P)). Qed.
Lemma lem28533 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term677 Absty Repty mk R) = (term664 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28532 Absty Repty mk R P)). Qed.
Lemma lem28534 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28535 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term678 Absty Repty mk R) = (term679 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28534 Absty) (@lem28533 Absty Repty mk R)). Qed.
Lemma lem28536 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term662 Absty Repty mk R) = (term680 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28531 Absty Repty mk R) (@lem28535 Absty Repty mk R)). Qed.
Lemma lem28537 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : ((term661 Absty Repty mk R) = (term662 Absty Repty mk R)) = ((term553 Absty Repty mk R) = (term680 Absty Repty mk R)).
Proof. exact (MK_COMB (@lem28525 Absty Repty mk R) (@lem28536 Absty Repty mk R)). Qed.
Lemma lem28538 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term553 Absty Repty mk R) = (term680 Absty Repty mk R).
Proof. exact (EQ_MP (@lem28537 Absty Repty mk R) (@lem28515 Absty Repty mk R)). Qed.
Lemma lem28651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28652 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term579 Absty Repty mk R) = (term681 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28651) (@lem28538 Absty Repty mk R)). Qed.
Lemma lem28654 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term587 A P Q) = (term588 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem28655 {Absty : Type'} (P : type686 Absty) (Q : type686 Absty) : (term659 Absty P Q) = (term660 Absty P Q).
Proof. exact (@lem28654 (Absty -> Prop) P Q). Qed.
Lemma lem28656 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term682 Absty Repty mk R) = (term683 Absty Repty mk R).
Proof. exact (@lem28655 Absty (term684 Absty Repty mk R) (term685 Absty Repty mk R)). Qed.
Lemma lem28657 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term686 Absty Repty mk R P) = (term565 Absty Repty mk R P).
Proof. exact (eq_refl (term686 Absty Repty mk R P)). Qed.
Lemma lem28658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28659 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term687 Absty Repty mk R P) = (term567 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28658) (@lem28657 Absty Repty mk R P)). Qed.
Lemma lem28660 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term688 Absty Repty mk R P) = (term562 Absty Repty mk R P).
Proof. exact (eq_refl (term688 Absty Repty mk R P)). Qed.
Lemma lem28661 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term689 Absty Repty mk R P) = (term569 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28659 Absty Repty mk R P) (@lem28660 Absty Repty mk R P)). Qed.
Lemma lem28662 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term690 Absty Repty mk R) = (term576 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28661 Absty Repty mk R P)). Qed.
Lemma lem28663 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28664 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term682 Absty Repty mk R) = (term577 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28663 Absty) (@lem28662 Absty Repty mk R)). Qed.
Lemma lem28665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28666 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term691 Absty Repty mk R) = (term692 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28665) (@lem28664 Absty Repty mk R)). Qed.
Lemma lem28667 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term686 Absty Repty mk R P) = (term565 Absty Repty mk R P).
Proof. exact (eq_refl (term686 Absty Repty mk R P)). Qed.
Lemma lem28668 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term693 Absty Repty mk R) = (term684 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28667 Absty Repty mk R P)). Qed.
Lemma lem28669 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28670 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term694 Absty Repty mk R) = (term695 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28669 Absty) (@lem28668 Absty Repty mk R)). Qed.
Lemma lem28671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28672 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term696 Absty Repty mk R) = (term697 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28671) (@lem28670 Absty Repty mk R)). Qed.
Lemma lem28673 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term688 Absty Repty mk R P) = (term562 Absty Repty mk R P).
Proof. exact (eq_refl (term688 Absty Repty mk R P)). Qed.
Lemma lem28674 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term698 Absty Repty mk R) = (term685 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28673 Absty Repty mk R P)). Qed.
Lemma lem28675 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28676 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term699 Absty Repty mk R) = (term700 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28675 Absty) (@lem28674 Absty Repty mk R)). Qed.
Lemma lem28677 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term683 Absty Repty mk R) = (term701 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28672 Absty Repty mk R) (@lem28676 Absty Repty mk R)). Qed.
Lemma lem28678 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : ((term682 Absty Repty mk R) = (term683 Absty Repty mk R)) = ((term577 Absty Repty mk R) = (term701 Absty Repty mk R)).
Proof. exact (MK_COMB (@lem28666 Absty Repty mk R) (@lem28677 Absty Repty mk R)). Qed.
Lemma lem28679 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term577 Absty Repty mk R) = (term701 Absty Repty mk R).
Proof. exact (EQ_MP (@lem28678 Absty Repty mk R) (@lem28656 Absty Repty mk R)). Qed.
Lemma lem28792 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term581 Absty Repty mk R) = (term702 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28652 Absty Repty mk R) (@lem28679 Absty Repty mk R)). Qed.
Lemma lem28793 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term586 Absty Repty mk R) = (term703 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28511 Repty R) (@lem28792 Absty Repty mk R)). Qed.
Lemma lem28795 {A : Type'} (P : Prop) (Q : A -> Prop) : (term704 A P Q) = (term705 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem28796 {Repty : Type'} (P : Prop) (Q : Repty -> Prop) : (term704 Repty P Q) = (term705 Repty P Q).
Proof. exact (@lem28795 Repty P Q). Qed.
Lemma lem28797 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term706 Repty x R y) = (term707 Repty x R y).
Proof. exact (@lem28796 Repty (R x y) (term489 Repty x R y)). Qed.
Lemma lem28798 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term708 Repty x R y x') = (term480 Repty x R y x').
Proof. exact (eq_refl (term708 Repty x R y x')). Qed.
Lemma lem28799 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term709 Repty x R y) = (term489 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem28798 Repty x R y x')). Qed.
Lemma lem28800 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28801 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term710 Repty x R y) = (term490 Repty x R y).
Proof. exact (MK_COMB (@lem28800 Repty) (@lem28799 Repty x R y)). Qed.
Lemma lem28802 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term496 Repty R x y) = (term496 Repty R x y).
Proof. exact (eq_refl (term496 Repty R x y)). Qed.
Lemma lem28803 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term706 Repty x R y) = (term498 Repty x R y).
Proof. exact (MK_COMB (@lem28802 Repty R x y) (@lem28801 Repty x R y)). Qed.
Lemma lem28804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28805 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term711 Repty x R y) = (term712 Repty x R y).
Proof. exact (MK_COMB (@lem28804) (@lem28803 Repty x R y)). Qed.
Lemma lem28806 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term708 Repty x R y x') = (term480 Repty x R y x').
Proof. exact (eq_refl (term708 Repty x R y x')). Qed.
Lemma lem28807 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term496 Repty R x y) = (term496 Repty R x y).
Proof. exact (eq_refl (term496 Repty R x y)). Qed.
Lemma lem28808 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term713 Repty x R y x') = (term714 Repty x R y x').
Proof. exact (MK_COMB (@lem28807 Repty R x y) (@lem28806 Repty x R y x')). Qed.
Lemma lem28809 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term715 Repty x R y) = (term716 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem28808 Repty x R y x')). Qed.
Lemma lem28810 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28811 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term707 Repty x R y) = (term717 Repty x R y).
Proof. exact (MK_COMB (@lem28810 Repty) (@lem28809 Repty x R y)). Qed.
Lemma lem28812 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : ((term706 Repty x R y) = (term707 Repty x R y)) = ((term498 Repty x R y) = (term717 Repty x R y)).
Proof. exact (MK_COMB (@lem28805 Repty x R y) (@lem28811 Repty x R y)). Qed.
Lemma lem28813 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term498 Repty x R y) = (term717 Repty x R y).
Proof. exact (EQ_MP (@lem28812 Repty x R y) (@lem28797 Repty x R y)). Qed.
Lemma lem28814 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term591 Repty x R) = (term718 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem28813 Repty x R y)). Qed.
Lemma lem28815 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28816 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term602 Repty x R) = (term719 Repty x R).
Proof. exact (MK_COMB (@lem28815 Repty) (@lem28814 Repty x R)). Qed.
Lemma lem28817 {Repty : Type'} (R : type1402 Repty) : (term640 Repty R) = (term720 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28816 Repty x R)). Qed.
Lemma lem28818 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28819 {Repty : Type'} (R : type1402 Repty) : (term651 Repty R) = (term721 Repty R).
Proof. exact (MK_COMB (@lem28818 Repty) (@lem28817 Repty R)). Qed.
Lemma lem28820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28821 {Repty : Type'} (R : type1402 Repty) : (term653 Repty R) = (term722 Repty R).
Proof. exact (MK_COMB (@lem28820) (@lem28819 Repty R)). Qed.
Lemma lem28822 {Repty : Type'} (R : type1402 Repty) : (term656 Repty R) = (term656 Repty R).
Proof. exact (eq_refl (term656 Repty R)). Qed.
Lemma lem28823 {Repty : Type'} (R : type1402 Repty) : (term657 Repty R) = (term723 Repty R).
Proof. exact (MK_COMB (@lem28821 Repty R) (@lem28822 Repty R)). Qed.
Lemma lem28825 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term588 A P Q) = (term587 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem28826 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term588 Repty P Q) = (term587 Repty P Q).
Proof. exact (@lem28825 Repty P Q). Qed.
Lemma lem28827 {Repty : Type'} (R : type1402 Repty) : (term724 Repty R) = (term725 Repty R).
Proof. exact (@lem28826 Repty (term720 Repty R) (term641 Repty R)). Qed.
Lemma lem28828 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term726 Repty R x) = (term719 Repty x R).
Proof. exact (eq_refl (term726 Repty R x)). Qed.
Lemma lem28829 {Repty : Type'} (R : type1402 Repty) : (term727 Repty R) = (term720 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28828 Repty x R)). Qed.
Lemma lem28830 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28831 {Repty : Type'} (R : type1402 Repty) : (term728 Repty R) = (term721 Repty R).
Proof. exact (MK_COMB (@lem28830 Repty) (@lem28829 Repty R)). Qed.
Lemma lem28832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28833 {Repty : Type'} (R : type1402 Repty) : (term729 Repty R) = (term722 Repty R).
Proof. exact (MK_COMB (@lem28832) (@lem28831 Repty R)). Qed.
Lemma lem28834 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term644 Repty R x) = (term634 Repty x R).
Proof. exact (eq_refl (term644 Repty R x)). Qed.
Lemma lem28835 {Repty : Type'} (R : type1402 Repty) : (term654 Repty R) = (term641 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28834 Repty x R)). Qed.
Lemma lem28836 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28837 {Repty : Type'} (R : type1402 Repty) : (term655 Repty R) = (term656 Repty R).
Proof. exact (MK_COMB (@lem28836 Repty) (@lem28835 Repty R)). Qed.
Lemma lem28838 {Repty : Type'} (R : type1402 Repty) : (term724 Repty R) = (term723 Repty R).
Proof. exact (MK_COMB (@lem28833 Repty R) (@lem28837 Repty R)). Qed.
Lemma lem28839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28840 {Repty : Type'} (R : type1402 Repty) : (term730 Repty R) = (term731 Repty R).
Proof. exact (MK_COMB (@lem28839) (@lem28838 Repty R)). Qed.
Lemma lem28841 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term726 Repty R x) = (term719 Repty x R).
Proof. exact (eq_refl (term726 Repty R x)). Qed.
Lemma lem28842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28843 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term732 Repty R x) = (term733 Repty x R).
Proof. exact (MK_COMB (@lem28842) (@lem28841 Repty x R)). Qed.
Lemma lem28844 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term644 Repty R x) = (term634 Repty x R).
Proof. exact (eq_refl (term644 Repty R x)). Qed.
Lemma lem28845 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term734 Repty R x) = (term735 Repty x R).
Proof. exact (MK_COMB (@lem28843 Repty x R) (@lem28844 Repty x R)). Qed.
Lemma lem28846 {Repty : Type'} (R : type1402 Repty) : (term736 Repty R) = (term737 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28845 Repty x R)). Qed.
Lemma lem28847 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28848 {Repty : Type'} (R : type1402 Repty) : (term725 Repty R) = (term738 Repty R).
Proof. exact (MK_COMB (@lem28847 Repty) (@lem28846 Repty R)). Qed.
Lemma lem28849 {Repty : Type'} (R : type1402 Repty) : ((term724 Repty R) = (term725 Repty R)) = ((term723 Repty R) = (term738 Repty R)).
Proof. exact (MK_COMB (@lem28840 Repty R) (@lem28848 Repty R)). Qed.
Lemma lem28850 {Repty : Type'} (R : type1402 Repty) : (term723 Repty R) = (term738 Repty R).
Proof. exact (EQ_MP (@lem28849 Repty R) (@lem28827 Repty R)). Qed.
Lemma lem28852 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term588 A P Q) = (term587 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem28853 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term588 Repty P Q) = (term587 Repty P Q).
Proof. exact (@lem28852 Repty P Q). Qed.
Lemma lem28854 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term739 Repty x R) = (term740 Repty x R).
Proof. exact (@lem28853 Repty (term718 Repty x R) (term633 Repty x R)). Qed.
Lemma lem28855 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term741 Repty x R y) = (term717 Repty x R y).
Proof. exact (eq_refl (term741 Repty x R y)). Qed.
Lemma lem28856 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term742 Repty x R) = (term718 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem28855 Repty x R y)). Qed.
Lemma lem28857 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28858 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term743 Repty x R) = (term719 Repty x R).
Proof. exact (MK_COMB (@lem28857 Repty) (@lem28856 Repty x R)). Qed.
Lemma lem28859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28860 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term744 Repty x R) = (term733 Repty x R).
Proof. exact (MK_COMB (@lem28859) (@lem28858 Repty x R)). Qed.
Lemma lem28861 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term745 Repty x R y) = (term632 Repty x R y).
Proof. exact (eq_refl (term745 Repty x R y)). Qed.
Lemma lem28862 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term746 Repty x R) = (term633 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem28861 Repty x R y)). Qed.
Lemma lem28863 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28864 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term747 Repty x R) = (term634 Repty x R).
Proof. exact (MK_COMB (@lem28863 Repty) (@lem28862 Repty x R)). Qed.
Lemma lem28865 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term739 Repty x R) = (term735 Repty x R).
Proof. exact (MK_COMB (@lem28860 Repty x R) (@lem28864 Repty x R)). Qed.
Lemma lem28866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28867 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term748 Repty x R) = (term749 Repty x R).
Proof. exact (MK_COMB (@lem28866) (@lem28865 Repty x R)). Qed.
Lemma lem28868 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term741 Repty x R y) = (term717 Repty x R y).
Proof. exact (eq_refl (term741 Repty x R y)). Qed.
Lemma lem28869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28870 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term750 Repty x R y) = (term751 Repty x R y).
Proof. exact (MK_COMB (@lem28869) (@lem28868 Repty x R y)). Qed.
Lemma lem28871 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term745 Repty x R y) = (term632 Repty x R y).
Proof. exact (eq_refl (term745 Repty x R y)). Qed.
Lemma lem28872 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term752 Repty x R y) = (term753 Repty x R y).
Proof. exact (MK_COMB (@lem28870 Repty x R y) (@lem28871 Repty x R y)). Qed.
Lemma lem28873 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term754 Repty x R) = (term755 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem28872 Repty x R y)). Qed.
Lemma lem28874 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28875 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term740 Repty x R) = (term756 Repty x R).
Proof. exact (MK_COMB (@lem28874 Repty) (@lem28873 Repty x R)). Qed.
Lemma lem28876 {Repty : Type'} (x : Repty) (R : type1402 Repty) : ((term739 Repty x R) = (term740 Repty x R)) = ((term735 Repty x R) = (term756 Repty x R)).
Proof. exact (MK_COMB (@lem28867 Repty x R) (@lem28875 Repty x R)). Qed.
Lemma lem28877 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term735 Repty x R) = (term756 Repty x R).
Proof. exact (EQ_MP (@lem28876 Repty x R) (@lem28854 Repty x R)). Qed.
Lemma lem28879 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem28880 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem28879 Repty P Q). Qed.
Lemma lem28881 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term757 Repty x R y) = (term758 Repty x R y).
Proof. exact (@lem28880 Repty (term716 Repty x R y) (term632 Repty x R y)). Qed.
Lemma lem28882 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term759 Repty x R y x') = (term714 Repty x R y x').
Proof. exact (eq_refl (term759 Repty x R y x')). Qed.
Lemma lem28883 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term760 Repty x R y) = (term716 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem28882 Repty x R y x')). Qed.
Lemma lem28884 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28885 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term761 Repty x R y) = (term717 Repty x R y).
Proof. exact (MK_COMB (@lem28884 Repty) (@lem28883 Repty x R y)). Qed.
Lemma lem28886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28887 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term762 Repty x R y) = (term751 Repty x R y).
Proof. exact (MK_COMB (@lem28886) (@lem28885 Repty x R y)). Qed.
Lemma lem28888 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term632 Repty x R y) = (term632 Repty x R y).
Proof. exact (eq_refl (term632 Repty x R y)). Qed.
Lemma lem28889 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term757 Repty x R y) = (term753 Repty x R y).
Proof. exact (MK_COMB (@lem28887 Repty x R y) (@lem28888 Repty x R y)). Qed.
Lemma lem28890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28891 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term763 Repty x R y) = (term764 Repty x R y).
Proof. exact (MK_COMB (@lem28890) (@lem28889 Repty x R y)). Qed.
Lemma lem28892 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term759 Repty x R y x') = (term714 Repty x R y x').
Proof. exact (eq_refl (term759 Repty x R y x')). Qed.
Lemma lem28893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28894 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term765 Repty x R y x') = (term766 Repty x R y x').
Proof. exact (MK_COMB (@lem28893) (@lem28892 Repty x R y x')). Qed.
Lemma lem28895 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term632 Repty x R y) = (term632 Repty x R y).
Proof. exact (eq_refl (term632 Repty x R y)). Qed.
Lemma lem28896 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term767 Repty x' x R y) = (term768 Repty x' x R y).
Proof. exact (MK_COMB (@lem28894 Repty x R y x') (@lem28895 Repty x R y)). Qed.
Lemma lem28897 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term769 Repty x R y) = (term770 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem28896 Repty x' x R y)). Qed.
Lemma lem28898 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28899 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term758 Repty x R y) = (term771 Repty x R y).
Proof. exact (MK_COMB (@lem28898 Repty) (@lem28897 Repty x R y)). Qed.
Lemma lem28900 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : ((term757 Repty x R y) = (term758 Repty x R y)) = ((term753 Repty x R y) = (term771 Repty x R y)).
Proof. exact (MK_COMB (@lem28891 Repty x R y) (@lem28899 Repty x R y)). Qed.
Lemma lem28901 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term753 Repty x R y) = (term771 Repty x R y).
Proof. exact (EQ_MP (@lem28900 Repty x R y) (@lem28881 Repty x R y)). Qed.
Lemma lem28902 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term755 Repty x R) = (term772 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem28901 Repty x R y)). Qed.
Lemma lem28903 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28904 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term756 Repty x R) = (term773 Repty x R).
Proof. exact (MK_COMB (@lem28903 Repty) (@lem28902 Repty x R)). Qed.
Lemma lem28905 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term735 Repty x R) = (term773 Repty x R).
Proof. exact (TRANS (@lem28877 Repty x R) (@lem28904 Repty x R)). Qed.
Lemma lem28906 {Repty : Type'} (R : type1402 Repty) : (term737 Repty R) = (term774 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem28905 Repty x R)). Qed.
Lemma lem28907 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28908 {Repty : Type'} (R : type1402 Repty) : (term738 Repty R) = (term775 Repty R).
Proof. exact (MK_COMB (@lem28907 Repty) (@lem28906 Repty R)). Qed.
Lemma lem28909 {Repty : Type'} (R : type1402 Repty) : (term723 Repty R) = (term775 Repty R).
Proof. exact (TRANS (@lem28850 Repty R) (@lem28908 Repty R)). Qed.
Lemma lem28910 {Repty : Type'} (R : type1402 Repty) : (term657 Repty R) = (term775 Repty R).
Proof. exact (TRANS (@lem28823 Repty R) (@lem28909 Repty R)). Qed.
Lemma lem28911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28912 {Repty : Type'} (R : type1402 Repty) : (term658 Repty R) = (term776 Repty R).
Proof. exact (MK_COMB (@lem28911) (@lem28910 Repty R)). Qed.
Lemma lem28914 {A : Type'} (P : Prop) (Q : A -> Prop) : (term704 A P Q) = (term705 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem28915 {Absty : Type'} (P : Prop) (Q : Absty -> Prop) : (term704 Absty P Q) = (term705 Absty P Q).
Proof. exact (@lem28914 Absty P Q). Qed.
Lemma lem28916 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term777 Absty Repty mk R P) = (term778 Absty Repty mk R P).
Proof. exact (@lem28915 Absty (term411 Absty Repty P mk R) (term532 Absty P)). Qed.
Lemma lem28917 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term779 Absty P x) = (term530 Absty P x).
Proof. exact (eq_refl (term779 Absty P x)). Qed.
Lemma lem28918 {Absty : Type'} (P : Absty -> Prop) : (term780 Absty P) = (term532 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem28917 Absty P x)). Qed.
Lemma lem28919 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem28920 {Absty : Type'} (P : Absty -> Prop) : (term781 Absty P) = (term483 Absty P).
Proof. exact (MK_COMB (@lem28919 Absty) (@lem28918 Absty P)). Qed.
Lemma lem28921 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term537 Absty Repty P mk R) = (term537 Absty Repty P mk R).
Proof. exact (eq_refl (term537 Absty Repty P mk R)). Qed.
Lemma lem28922 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term777 Absty Repty mk R P) = (term539 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28921 Absty Repty P mk R) (@lem28920 Absty P)). Qed.
Lemma lem28923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28924 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term782 Absty Repty mk R P) = (term783 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28923) (@lem28922 Absty Repty mk R P)). Qed.
Lemma lem28925 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term779 Absty P x) = (term530 Absty P x).
Proof. exact (eq_refl (term779 Absty P x)). Qed.
Lemma lem28926 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term537 Absty Repty P mk R) = (term537 Absty Repty P mk R).
Proof. exact (eq_refl (term537 Absty Repty P mk R)). Qed.
Lemma lem28927 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term784 Absty Repty mk R P x) = (term785 Absty Repty mk R P x).
Proof. exact (MK_COMB (@lem28926 Absty Repty P mk R) (@lem28925 Absty P x)). Qed.
Lemma lem28928 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term786 Absty Repty mk R P) = (term787 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem28927 Absty Repty mk R P x)). Qed.
Lemma lem28929 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem28930 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term778 Absty Repty mk R P) = (term788 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28929 Absty) (@lem28928 Absty Repty mk R P)). Qed.
Lemma lem28931 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term777 Absty Repty mk R P) = (term778 Absty Repty mk R P)) = ((term539 Absty Repty mk R P) = (term788 Absty Repty mk R P)).
Proof. exact (MK_COMB (@lem28924 Absty Repty mk R P) (@lem28930 Absty Repty mk R P)). Qed.
Lemma lem28932 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term539 Absty Repty mk R P) = (term788 Absty Repty mk R P).
Proof. exact (EQ_MP (@lem28931 Absty Repty mk R P) (@lem28916 Absty Repty mk R P)). Qed.
Lemma lem28933 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term663 Absty Repty mk R) = (term789 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28932 Absty Repty mk R P)). Qed.
Lemma lem28934 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28935 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term674 Absty Repty mk R) = (term790 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28934 Absty) (@lem28933 Absty Repty mk R)). Qed.
Lemma lem28936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28937 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term676 Absty Repty mk R) = (term791 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28936) (@lem28935 Absty Repty mk R)). Qed.
Lemma lem28939 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem28940 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term224 Repty P Q) = (term225 Repty P Q).
Proof. exact (@lem28939 Repty P Q). Qed.
Lemma lem28941 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term792 Absty Repty mk R P) = (term793 Absty Repty mk R P).
Proof. exact (@lem28940 Repty (term524 Absty Repty P mk R) (term410 Absty P)). Qed.
Lemma lem28942 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term794 Absty Repty P mk R x) = (term522 Absty Repty P mk R x).
Proof. exact (eq_refl (term794 Absty Repty P mk R x)). Qed.
Lemma lem28943 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term795 Absty Repty P mk R) = (term524 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem28942 Absty Repty P mk R x)). Qed.
Lemma lem28944 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28945 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term796 Absty Repty P mk R) = (term525 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem28944 Repty) (@lem28943 Absty Repty P mk R)). Qed.
Lemma lem28946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem28947 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term797 Absty Repty P mk R) = (term534 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem28946) (@lem28945 Absty Repty P mk R)). Qed.
Lemma lem28948 {Absty : Type'} (P : Absty -> Prop) : (term410 Absty P) = (term410 Absty P).
Proof. exact (eq_refl (term410 Absty P)). Qed.
Lemma lem28949 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term792 Absty Repty mk R P) = (term536 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28947 Absty Repty P mk R) (@lem28948 Absty P)). Qed.
Lemma lem28950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28951 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term798 Absty Repty mk R P) = (term799 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28950) (@lem28949 Absty Repty mk R P)). Qed.
Lemma lem28952 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term794 Absty Repty P mk R x) = (term522 Absty Repty P mk R x).
Proof. exact (eq_refl (term794 Absty Repty P mk R x)). Qed.
Lemma lem28953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem28954 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term800 Absty Repty P mk R x) = (term801 Absty Repty P mk R x).
Proof. exact (MK_COMB (@lem28953) (@lem28952 Absty Repty P mk R x)). Qed.
Lemma lem28955 {Absty : Type'} (P : Absty -> Prop) : (term410 Absty P) = (term410 Absty P).
Proof. exact (eq_refl (term410 Absty P)). Qed.
Lemma lem28956 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term802 Absty Repty mk R x P) = (term803 Absty Repty mk R x P).
Proof. exact (MK_COMB (@lem28954 Absty Repty P mk R x) (@lem28955 Absty P)). Qed.
Lemma lem28957 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term804 Absty Repty mk R P) = (term805 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Repty => @lem28956 Absty Repty mk R x P)). Qed.
Lemma lem28958 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem28959 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term793 Absty Repty mk R P) = (term806 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28958 Repty) (@lem28957 Absty Repty mk R P)). Qed.
Lemma lem28960 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term792 Absty Repty mk R P) = (term793 Absty Repty mk R P)) = ((term536 Absty Repty mk R P) = (term806 Absty Repty mk R P)).
Proof. exact (MK_COMB (@lem28951 Absty Repty mk R P) (@lem28959 Absty Repty mk R P)). Qed.
Lemma lem28961 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term536 Absty Repty mk R P) = (term806 Absty Repty mk R P).
Proof. exact (EQ_MP (@lem28960 Absty Repty mk R P) (@lem28941 Absty Repty mk R P)). Qed.
Lemma lem28962 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term664 Absty Repty mk R) = (term807 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28961 Absty Repty mk R P)). Qed.
Lemma lem28963 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28964 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term679 Absty Repty mk R) = (term808 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28963 Absty) (@lem28962 Absty Repty mk R)). Qed.
Lemma lem28965 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term680 Absty Repty mk R) = (term809 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28937 Absty Repty mk R) (@lem28964 Absty Repty mk R)). Qed.
Lemma lem28967 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term588 A P Q) = (term587 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem28968 {Absty : Type'} (P : type686 Absty) (Q : type686 Absty) : (term660 Absty P Q) = (term659 Absty P Q).
Proof. exact (@lem28967 (Absty -> Prop) P Q). Qed.
Lemma lem28969 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term810 Absty Repty mk R) = (term811 Absty Repty mk R).
Proof. exact (@lem28968 Absty (term789 Absty Repty mk R) (term807 Absty Repty mk R)). Qed.
Lemma lem28970 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term812 Absty Repty mk R P) = (term788 Absty Repty mk R P).
Proof. exact (eq_refl (term812 Absty Repty mk R P)). Qed.
Lemma lem28971 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term813 Absty Repty mk R) = (term789 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28970 Absty Repty mk R P)). Qed.
Lemma lem28972 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28973 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term814 Absty Repty mk R) = (term790 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28972 Absty) (@lem28971 Absty Repty mk R)). Qed.
Lemma lem28974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28975 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term815 Absty Repty mk R) = (term791 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28974) (@lem28973 Absty Repty mk R)). Qed.
Lemma lem28976 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term816 Absty Repty mk R P) = (term806 Absty Repty mk R P).
Proof. exact (eq_refl (term816 Absty Repty mk R P)). Qed.
Lemma lem28977 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term817 Absty Repty mk R) = (term807 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28976 Absty Repty mk R P)). Qed.
Lemma lem28978 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28979 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term818 Absty Repty mk R) = (term808 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28978 Absty) (@lem28977 Absty Repty mk R)). Qed.
Lemma lem28980 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term810 Absty Repty mk R) = (term809 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28975 Absty Repty mk R) (@lem28979 Absty Repty mk R)). Qed.
Lemma lem28981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem28982 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term819 Absty Repty mk R) = (term820 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28981) (@lem28980 Absty Repty mk R)). Qed.
Lemma lem28983 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term812 Absty Repty mk R P) = (term788 Absty Repty mk R P).
Proof. exact (eq_refl (term812 Absty Repty mk R P)). Qed.
Lemma lem28984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem28985 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term821 Absty Repty mk R P) = (term822 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28984) (@lem28983 Absty Repty mk R P)). Qed.
Lemma lem28986 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term816 Absty Repty mk R P) = (term806 Absty Repty mk R P).
Proof. exact (eq_refl (term816 Absty Repty mk R P)). Qed.
Lemma lem28987 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term823 Absty Repty mk R P) = (term824 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem28985 Absty Repty mk R P) (@lem28986 Absty Repty mk R P)). Qed.
Lemma lem28988 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term825 Absty Repty mk R) = (term826 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem28987 Absty Repty mk R P)). Qed.
Lemma lem28989 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem28990 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term811 Absty Repty mk R) = (term827 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28989 Absty) (@lem28988 Absty Repty mk R)). Qed.
Lemma lem28991 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : ((term810 Absty Repty mk R) = (term811 Absty Repty mk R)) = ((term809 Absty Repty mk R) = (term827 Absty Repty mk R)).
Proof. exact (MK_COMB (@lem28982 Absty Repty mk R) (@lem28990 Absty Repty mk R)). Qed.
Lemma lem28992 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term809 Absty Repty mk R) = (term827 Absty Repty mk R).
Proof. exact (EQ_MP (@lem28991 Absty Repty mk R) (@lem28969 Absty Repty mk R)). Qed.
Lemma lem28996 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem28997 {Absty : Type'} (P : Absty -> Prop) (Q : Prop) : (term179 Absty P Q) = (term180 Absty P Q).
Proof. exact (@lem28996 Absty P Q). Qed.
Lemma lem28998 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term828 Absty Repty mk R P) = (term829 Absty Repty mk R P).
Proof. exact (@lem28997 Absty (term787 Absty Repty mk R P) (term806 Absty Repty mk R P)). Qed.
Lemma lem28999 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term830 Absty Repty mk R P x) = (term785 Absty Repty mk R P x).
Proof. exact (eq_refl (term830 Absty Repty mk R P x)). Qed.
Lemma lem29000 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term831 Absty Repty mk R P) = (term787 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem28999 Absty Repty mk R P x)). Qed.
Lemma lem29001 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29002 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term832 Absty Repty mk R P) = (term788 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29001 Absty) (@lem29000 Absty Repty mk R P)). Qed.
Lemma lem29003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29004 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term833 Absty Repty mk R P) = (term822 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29003) (@lem29002 Absty Repty mk R P)). Qed.
Lemma lem29005 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term806 Absty Repty mk R P) = (term806 Absty Repty mk R P).
Proof. exact (eq_refl (term806 Absty Repty mk R P)). Qed.
Lemma lem29006 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term828 Absty Repty mk R P) = (term824 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29004 Absty Repty mk R P) (@lem29005 Absty Repty mk R P)). Qed.
Lemma lem29007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29008 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term834 Absty Repty mk R P) = (term835 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29007) (@lem29006 Absty Repty mk R P)). Qed.
Lemma lem29009 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term830 Absty Repty mk R P x) = (term785 Absty Repty mk R P x).
Proof. exact (eq_refl (term830 Absty Repty mk R P x)). Qed.
Lemma lem29010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29011 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term836 Absty Repty mk R P x) = (term837 Absty Repty mk R P x).
Proof. exact (MK_COMB (@lem29010) (@lem29009 Absty Repty mk R P x)). Qed.
Lemma lem29012 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term806 Absty Repty mk R P) = (term806 Absty Repty mk R P).
Proof. exact (eq_refl (term806 Absty Repty mk R P)). Qed.
Lemma lem29013 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term838 Absty Repty x mk R P) = (term839 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29011 Absty Repty mk R P x) (@lem29012 Absty Repty mk R P)). Qed.
Lemma lem29014 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term840 Absty Repty mk R P) = (term841 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem29013 Absty Repty x mk R P)). Qed.
Lemma lem29015 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29016 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term829 Absty Repty mk R P) = (term842 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29015 Absty) (@lem29014 Absty Repty mk R P)). Qed.
Lemma lem29017 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term828 Absty Repty mk R P) = (term829 Absty Repty mk R P)) = ((term824 Absty Repty mk R P) = (term842 Absty Repty mk R P)).
Proof. exact (MK_COMB (@lem29008 Absty Repty mk R P) (@lem29016 Absty Repty mk R P)). Qed.
Lemma lem29018 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term824 Absty Repty mk R P) = (term842 Absty Repty mk R P).
Proof. exact (EQ_MP (@lem29017 Absty Repty mk R P) (@lem28998 Absty Repty mk R P)). Qed.
Lemma lem29020 {A : Type'} (P : Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem29021 {Repty : Type'} (P : Prop) (Q : Repty -> Prop) : (term843 Repty P Q) = (term844 Repty P Q).
Proof. exact (@lem29020 Repty P Q). Qed.
Lemma lem29022 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term845 Absty Repty x mk R P) = (term846 Absty Repty x mk R P).
Proof. exact (@lem29021 Repty (term785 Absty Repty mk R P x) (term805 Absty Repty mk R P)). Qed.
Lemma lem29023 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term847 Absty Repty mk R P x) = (term803 Absty Repty mk R x P).
Proof. exact (eq_refl (term847 Absty Repty mk R P x)). Qed.
Lemma lem29024 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term848 Absty Repty mk R P) = (term805 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Repty => @lem29023 Absty Repty mk R x P)). Qed.
Lemma lem29025 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29026 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term849 Absty Repty mk R P) = (term806 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29025 Repty) (@lem29024 Absty Repty mk R P)). Qed.
Lemma lem29027 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term837 Absty Repty mk R P x) = (term837 Absty Repty mk R P x).
Proof. exact (eq_refl (term837 Absty Repty mk R P x)). Qed.
Lemma lem29028 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term845 Absty Repty x mk R P) = (term839 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29027 Absty Repty mk R P x) (@lem29026 Absty Repty mk R P)). Qed.
Lemma lem29029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29030 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term850 Absty Repty x mk R P) = (term851 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29029) (@lem29028 Absty Repty x mk R P)). Qed.
Lemma lem29031 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term847 Absty Repty mk R P x) = (term803 Absty Repty mk R x P).
Proof. exact (eq_refl (term847 Absty Repty mk R P x)). Qed.
Lemma lem29032 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term837 Absty Repty mk R P x) = (term837 Absty Repty mk R P x).
Proof. exact (eq_refl (term837 Absty Repty mk R P x)). Qed.
Lemma lem29033 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x' : Repty) (P : Absty -> Prop) : (term852 Absty Repty x mk R P x') = (term853 Absty Repty x mk R x' P).
Proof. exact (MK_COMB (@lem29032 Absty Repty mk R P x) (@lem29031 Absty Repty mk R x' P)). Qed.
Lemma lem29034 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term854 Absty Repty x mk R P) = (term855 Absty Repty x mk R P).
Proof. exact (fun_ext (fun x' : Repty => @lem29033 Absty Repty x mk R x' P)). Qed.
Lemma lem29035 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29036 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term846 Absty Repty x mk R P) = (term856 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29035 Repty) (@lem29034 Absty Repty x mk R P)). Qed.
Lemma lem29037 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term845 Absty Repty x mk R P) = (term846 Absty Repty x mk R P)) = ((term839 Absty Repty x mk R P) = (term856 Absty Repty x mk R P)).
Proof. exact (MK_COMB (@lem29030 Absty Repty x mk R P) (@lem29036 Absty Repty x mk R P)). Qed.
Lemma lem29038 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term839 Absty Repty x mk R P) = (term856 Absty Repty x mk R P).
Proof. exact (EQ_MP (@lem29037 Absty Repty x mk R P) (@lem29022 Absty Repty x mk R P)). Qed.
Lemma lem29039 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term841 Absty Repty mk R P) = (term857 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem29038 Absty Repty x mk R P)). Qed.
Lemma lem29040 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29041 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term842 Absty Repty mk R P) = (term858 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29040 Absty) (@lem29039 Absty Repty mk R P)). Qed.
Lemma lem29042 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term824 Absty Repty mk R P) = (term858 Absty Repty mk R P).
Proof. exact (TRANS (@lem29018 Absty Repty mk R P) (@lem29041 Absty Repty mk R P)). Qed.
Lemma lem29043 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term826 Absty Repty mk R) = (term859 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29042 Absty Repty mk R P)). Qed.
Lemma lem29044 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29045 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term827 Absty Repty mk R) = (term860 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29044 Absty) (@lem29043 Absty Repty mk R)). Qed.
Lemma lem29046 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term809 Absty Repty mk R) = (term860 Absty Repty mk R).
Proof. exact (TRANS (@lem28992 Absty Repty mk R) (@lem29045 Absty Repty mk R)). Qed.
Lemma lem29047 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term680 Absty Repty mk R) = (term860 Absty Repty mk R).
Proof. exact (TRANS (@lem28965 Absty Repty mk R) (@lem29046 Absty Repty mk R)). Qed.
Lemma lem29048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29049 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term681 Absty Repty mk R) = (term861 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29048) (@lem29047 Absty Repty mk R)). Qed.
Lemma lem29051 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem29052 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term224 Repty P Q) = (term225 Repty P Q).
Proof. exact (@lem29051 Repty P Q). Qed.
Lemma lem29053 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term862 Absty Repty mk R P) = (term863 Absty Repty mk R P).
Proof. exact (@lem29052 Repty (term406 Absty Repty P mk R) (term134 Absty P)). Qed.
Lemma lem29054 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term520 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term520 Absty Repty P mk R x)). Qed.
Lemma lem29055 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term864 Absty Repty P mk R) = (term406 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem29054 Absty Repty P mk R x)). Qed.
Lemma lem29056 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29057 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term865 Absty Repty P mk R) = (term407 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem29056 Repty) (@lem29055 Absty Repty P mk R)). Qed.
Lemma lem29058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29059 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term866 Absty Repty P mk R) = (term563 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem29058) (@lem29057 Absty Repty P mk R)). Qed.
Lemma lem29060 {Absty : Type'} (P : Absty -> Prop) : (term134 Absty P) = (term134 Absty P).
Proof. exact (eq_refl (term134 Absty P)). Qed.
Lemma lem29061 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term862 Absty Repty mk R P) = (term565 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29059 Absty Repty P mk R) (@lem29060 Absty P)). Qed.
Lemma lem29062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29063 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term867 Absty Repty mk R P) = (term868 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29062) (@lem29061 Absty Repty mk R P)). Qed.
Lemma lem29064 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term520 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term520 Absty Repty P mk R x)). Qed.
Lemma lem29065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29066 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term869 Absty Repty P mk R x) = (term870 Absty Repty P mk R x).
Proof. exact (MK_COMB (@lem29065) (@lem29064 Absty Repty P mk R x)). Qed.
Lemma lem29067 {Absty : Type'} (P : Absty -> Prop) : (term134 Absty P) = (term134 Absty P).
Proof. exact (eq_refl (term134 Absty P)). Qed.
Lemma lem29068 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term871 Absty Repty mk R x P) = (term872 Absty Repty mk R x P).
Proof. exact (MK_COMB (@lem29066 Absty Repty P mk R x) (@lem29067 Absty P)). Qed.
Lemma lem29069 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term873 Absty Repty mk R P) = (term874 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Repty => @lem29068 Absty Repty mk R x P)). Qed.
Lemma lem29070 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29071 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term863 Absty Repty mk R P) = (term875 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29070 Repty) (@lem29069 Absty Repty mk R P)). Qed.
Lemma lem29072 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term862 Absty Repty mk R P) = (term863 Absty Repty mk R P)) = ((term565 Absty Repty mk R P) = (term875 Absty Repty mk R P)).
Proof. exact (MK_COMB (@lem29063 Absty Repty mk R P) (@lem29071 Absty Repty mk R P)). Qed.
Lemma lem29073 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term565 Absty Repty mk R P) = (term875 Absty Repty mk R P).
Proof. exact (EQ_MP (@lem29072 Absty Repty mk R P) (@lem29053 Absty Repty mk R P)). Qed.
Lemma lem29074 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term684 Absty Repty mk R) = (term876 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29073 Absty Repty mk R P)). Qed.
Lemma lem29075 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29076 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term695 Absty Repty mk R) = (term877 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29075 Absty) (@lem29074 Absty Repty mk R)). Qed.
Lemma lem29077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29078 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term697 Absty Repty mk R) = (term878 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29077) (@lem29076 Absty Repty mk R)). Qed.
Lemma lem29080 {A : Type'} (P : Prop) (Q : A -> Prop) : (term704 A P Q) = (term705 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem29081 {Absty : Type'} (P : Prop) (Q : Absty -> Prop) : (term704 Absty P Q) = (term705 Absty P Q).
Proof. exact (@lem29080 Absty P Q). Qed.
Lemma lem29082 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term562 Absty Repty mk R P) = (term879 Absty Repty mk R P).
Proof. exact (@lem29081 Absty (term556 Absty Repty P mk R) P). Qed.
Lemma lem29083 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term685 Absty Repty mk R) = (term880 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29082 Absty Repty mk R P)). Qed.
Lemma lem29084 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29085 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term700 Absty Repty mk R) = (term881 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29084 Absty) (@lem29083 Absty Repty mk R)). Qed.
Lemma lem29086 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term701 Absty Repty mk R) = (term882 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29078 Absty Repty mk R) (@lem29085 Absty Repty mk R)). Qed.
Lemma lem29088 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term588 A P Q) = (term587 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem29089 {Absty : Type'} (P : type686 Absty) (Q : type686 Absty) : (term660 Absty P Q) = (term659 Absty P Q).
Proof. exact (@lem29088 (Absty -> Prop) P Q). Qed.
Lemma lem29090 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term883 Absty Repty mk R) = (term884 Absty Repty mk R).
Proof. exact (@lem29089 Absty (term876 Absty Repty mk R) (term880 Absty Repty mk R)). Qed.
Lemma lem29091 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term885 Absty Repty mk R P) = (term875 Absty Repty mk R P).
Proof. exact (eq_refl (term885 Absty Repty mk R P)). Qed.
Lemma lem29092 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term886 Absty Repty mk R) = (term876 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29091 Absty Repty mk R P)). Qed.
Lemma lem29093 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29094 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term887 Absty Repty mk R) = (term877 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29093 Absty) (@lem29092 Absty Repty mk R)). Qed.
Lemma lem29095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29096 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term888 Absty Repty mk R) = (term878 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29095) (@lem29094 Absty Repty mk R)). Qed.
Lemma lem29097 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term889 Absty Repty mk R P) = (term879 Absty Repty mk R P).
Proof. exact (eq_refl (term889 Absty Repty mk R P)). Qed.
Lemma lem29098 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term890 Absty Repty mk R) = (term880 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29097 Absty Repty mk R P)). Qed.
Lemma lem29099 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29100 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term891 Absty Repty mk R) = (term881 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29099 Absty) (@lem29098 Absty Repty mk R)). Qed.
Lemma lem29101 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term883 Absty Repty mk R) = (term882 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29096 Absty Repty mk R) (@lem29100 Absty Repty mk R)). Qed.
Lemma lem29102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29103 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term892 Absty Repty mk R) = (term893 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29102) (@lem29101 Absty Repty mk R)). Qed.
Lemma lem29104 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term885 Absty Repty mk R P) = (term875 Absty Repty mk R P).
Proof. exact (eq_refl (term885 Absty Repty mk R P)). Qed.
Lemma lem29105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29106 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term894 Absty Repty mk R P) = (term895 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29105) (@lem29104 Absty Repty mk R P)). Qed.
Lemma lem29107 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term889 Absty Repty mk R P) = (term879 Absty Repty mk R P).
Proof. exact (eq_refl (term889 Absty Repty mk R P)). Qed.
Lemma lem29108 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term896 Absty Repty mk R P) = (term897 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29106 Absty Repty mk R P) (@lem29107 Absty Repty mk R P)). Qed.
Lemma lem29109 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term898 Absty Repty mk R) = (term899 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29108 Absty Repty mk R P)). Qed.
Lemma lem29110 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29111 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term884 Absty Repty mk R) = (term900 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29110 Absty) (@lem29109 Absty Repty mk R)). Qed.
Lemma lem29112 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : ((term883 Absty Repty mk R) = (term884 Absty Repty mk R)) = ((term882 Absty Repty mk R) = (term900 Absty Repty mk R)).
Proof. exact (MK_COMB (@lem29103 Absty Repty mk R) (@lem29111 Absty Repty mk R)). Qed.
Lemma lem29113 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term882 Absty Repty mk R) = (term900 Absty Repty mk R).
Proof. exact (EQ_MP (@lem29112 Absty Repty mk R) (@lem29090 Absty Repty mk R)). Qed.
Lemma lem29117 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem29118 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem29117 Repty P Q). Qed.
Lemma lem29119 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term901 Absty Repty mk R P) = (term902 Absty Repty mk R P).
Proof. exact (@lem29118 Repty (term874 Absty Repty mk R P) (term879 Absty Repty mk R P)). Qed.
Lemma lem29120 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term903 Absty Repty mk R P x) = (term872 Absty Repty mk R x P).
Proof. exact (eq_refl (term903 Absty Repty mk R P x)). Qed.
Lemma lem29121 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term904 Absty Repty mk R P) = (term874 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Repty => @lem29120 Absty Repty mk R x P)). Qed.
Lemma lem29122 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29123 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term905 Absty Repty mk R P) = (term875 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29122 Repty) (@lem29121 Absty Repty mk R P)). Qed.
Lemma lem29124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29125 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term906 Absty Repty mk R P) = (term895 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29124) (@lem29123 Absty Repty mk R P)). Qed.
Lemma lem29126 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term879 Absty Repty mk R P) = (term879 Absty Repty mk R P).
Proof. exact (eq_refl (term879 Absty Repty mk R P)). Qed.
Lemma lem29127 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term901 Absty Repty mk R P) = (term897 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29125 Absty Repty mk R P) (@lem29126 Absty Repty mk R P)). Qed.
Lemma lem29128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29129 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term907 Absty Repty mk R P) = (term908 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29128) (@lem29127 Absty Repty mk R P)). Qed.
Lemma lem29130 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term903 Absty Repty mk R P x) = (term872 Absty Repty mk R x P).
Proof. exact (eq_refl (term903 Absty Repty mk R P x)). Qed.
Lemma lem29131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29132 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term909 Absty Repty mk R P x) = (term910 Absty Repty mk R x P).
Proof. exact (MK_COMB (@lem29131) (@lem29130 Absty Repty mk R x P)). Qed.
Lemma lem29133 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term879 Absty Repty mk R P) = (term879 Absty Repty mk R P).
Proof. exact (eq_refl (term879 Absty Repty mk R P)). Qed.
Lemma lem29134 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term911 Absty Repty x mk R P) = (term912 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29132 Absty Repty mk R x P) (@lem29133 Absty Repty mk R P)). Qed.
Lemma lem29135 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term913 Absty Repty mk R P) = (term914 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Repty => @lem29134 Absty Repty x mk R P)). Qed.
Lemma lem29136 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29137 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term902 Absty Repty mk R P) = (term915 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29136 Repty) (@lem29135 Absty Repty mk R P)). Qed.
Lemma lem29138 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term901 Absty Repty mk R P) = (term902 Absty Repty mk R P)) = ((term897 Absty Repty mk R P) = (term915 Absty Repty mk R P)).
Proof. exact (MK_COMB (@lem29129 Absty Repty mk R P) (@lem29137 Absty Repty mk R P)). Qed.
Lemma lem29139 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term897 Absty Repty mk R P) = (term915 Absty Repty mk R P).
Proof. exact (EQ_MP (@lem29138 Absty Repty mk R P) (@lem29119 Absty Repty mk R P)). Qed.
Lemma lem29141 {A : Type'} (P : Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem29142 {Absty : Type'} (P : Prop) (Q : Absty -> Prop) : (term843 Absty P Q) = (term844 Absty P Q).
Proof. exact (@lem29141 Absty P Q). Qed.
Lemma lem29143 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term916 Absty Repty x mk R P) = (term917 Absty Repty x mk R P).
Proof. exact (@lem29142 Absty (term872 Absty Repty mk R x P) (term918 Absty Repty mk R P)). Qed.
Lemma lem29144 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term919 Absty Repty mk R P x) = (term920 Absty Repty mk R P x).
Proof. exact (eq_refl (term919 Absty Repty mk R P x)). Qed.
Lemma lem29145 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term921 Absty Repty mk R P) = (term918 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem29144 Absty Repty mk R P x)). Qed.
Lemma lem29146 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29147 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term922 Absty Repty mk R P) = (term879 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29146 Absty) (@lem29145 Absty Repty mk R P)). Qed.
Lemma lem29148 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term910 Absty Repty mk R x P) = (term910 Absty Repty mk R x P).
Proof. exact (eq_refl (term910 Absty Repty mk R x P)). Qed.
Lemma lem29149 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term916 Absty Repty x mk R P) = (term912 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29148 Absty Repty mk R x P) (@lem29147 Absty Repty mk R P)). Qed.
Lemma lem29150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29151 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term923 Absty Repty x mk R P) = (term924 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29150) (@lem29149 Absty Repty x mk R P)). Qed.
Lemma lem29152 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x : Absty) : (term919 Absty Repty mk R P x) = (term920 Absty Repty mk R P x).
Proof. exact (eq_refl (term919 Absty Repty mk R P x)). Qed.
Lemma lem29153 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (P : Absty -> Prop) : (term910 Absty Repty mk R x P) = (term910 Absty Repty mk R x P).
Proof. exact (eq_refl (term910 Absty Repty mk R x P)). Qed.
Lemma lem29154 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x' : Absty) : (term925 Absty Repty x mk R P x') = (term926 Absty Repty x mk R P x').
Proof. exact (MK_COMB (@lem29153 Absty Repty mk R x P) (@lem29152 Absty Repty mk R P x')). Qed.
Lemma lem29155 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term927 Absty Repty x mk R P) = (term928 Absty Repty x mk R P).
Proof. exact (fun_ext (fun x' : Absty => @lem29154 Absty Repty x mk R P x')). Qed.
Lemma lem29156 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29157 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term917 Absty Repty x mk R P) = (term929 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29156 Absty) (@lem29155 Absty Repty x mk R P)). Qed.
Lemma lem29158 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term916 Absty Repty x mk R P) = (term917 Absty Repty x mk R P)) = ((term912 Absty Repty x mk R P) = (term929 Absty Repty x mk R P)).
Proof. exact (MK_COMB (@lem29151 Absty Repty x mk R P) (@lem29157 Absty Repty x mk R P)). Qed.
Lemma lem29159 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term912 Absty Repty x mk R P) = (term929 Absty Repty x mk R P).
Proof. exact (EQ_MP (@lem29158 Absty Repty x mk R P) (@lem29143 Absty Repty x mk R P)). Qed.
Lemma lem29160 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term914 Absty Repty mk R P) = (term930 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Repty => @lem29159 Absty Repty x mk R P)). Qed.
Lemma lem29161 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29162 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term915 Absty Repty mk R P) = (term931 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29161 Repty) (@lem29160 Absty Repty mk R P)). Qed.
Lemma lem29163 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term897 Absty Repty mk R P) = (term931 Absty Repty mk R P).
Proof. exact (TRANS (@lem29139 Absty Repty mk R P) (@lem29162 Absty Repty mk R P)). Qed.
Lemma lem29164 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term899 Absty Repty mk R) = (term932 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29163 Absty Repty mk R P)). Qed.
Lemma lem29165 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29166 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term900 Absty Repty mk R) = (term933 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29165 Absty) (@lem29164 Absty Repty mk R)). Qed.
Lemma lem29167 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term882 Absty Repty mk R) = (term933 Absty Repty mk R).
Proof. exact (TRANS (@lem29113 Absty Repty mk R) (@lem29166 Absty Repty mk R)). Qed.
Lemma lem29168 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term701 Absty Repty mk R) = (term933 Absty Repty mk R).
Proof. exact (TRANS (@lem29086 Absty Repty mk R) (@lem29167 Absty Repty mk R)). Qed.
Lemma lem29169 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term702 Absty Repty mk R) = (term934 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29049 Absty Repty mk R) (@lem29168 Absty Repty mk R)). Qed.
Lemma lem29171 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term588 A P Q) = (term587 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem29172 {Absty : Type'} (P : type686 Absty) (Q : type686 Absty) : (term660 Absty P Q) = (term659 Absty P Q).
Proof. exact (@lem29171 (Absty -> Prop) P Q). Qed.
Lemma lem29173 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term935 Absty Repty mk R) = (term936 Absty Repty mk R).
Proof. exact (@lem29172 Absty (term859 Absty Repty mk R) (term932 Absty Repty mk R)). Qed.
Lemma lem29174 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term937 Absty Repty mk R P) = (term858 Absty Repty mk R P).
Proof. exact (eq_refl (term937 Absty Repty mk R P)). Qed.
Lemma lem29175 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term938 Absty Repty mk R) = (term859 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29174 Absty Repty mk R P)). Qed.
Lemma lem29176 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29177 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term939 Absty Repty mk R) = (term860 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29176 Absty) (@lem29175 Absty Repty mk R)). Qed.
Lemma lem29178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29179 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term940 Absty Repty mk R) = (term861 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29178) (@lem29177 Absty Repty mk R)). Qed.
Lemma lem29180 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term941 Absty Repty mk R P) = (term931 Absty Repty mk R P).
Proof. exact (eq_refl (term941 Absty Repty mk R P)). Qed.
Lemma lem29181 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term942 Absty Repty mk R) = (term932 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29180 Absty Repty mk R P)). Qed.
Lemma lem29182 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29183 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term943 Absty Repty mk R) = (term933 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29182 Absty) (@lem29181 Absty Repty mk R)). Qed.
Lemma lem29184 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term935 Absty Repty mk R) = (term934 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29179 Absty Repty mk R) (@lem29183 Absty Repty mk R)). Qed.
Lemma lem29185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29186 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term944 Absty Repty mk R) = (term945 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29185) (@lem29184 Absty Repty mk R)). Qed.
Lemma lem29187 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term937 Absty Repty mk R P) = (term858 Absty Repty mk R P).
Proof. exact (eq_refl (term937 Absty Repty mk R P)). Qed.
Lemma lem29188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29189 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term946 Absty Repty mk R P) = (term947 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29188) (@lem29187 Absty Repty mk R P)). Qed.
Lemma lem29190 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term941 Absty Repty mk R P) = (term931 Absty Repty mk R P).
Proof. exact (eq_refl (term941 Absty Repty mk R P)). Qed.
Lemma lem29191 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term948 Absty Repty mk R P) = (term949 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29189 Absty Repty mk R P) (@lem29190 Absty Repty mk R P)). Qed.
Lemma lem29192 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term950 Absty Repty mk R) = (term951 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29191 Absty Repty mk R P)). Qed.
Lemma lem29193 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29194 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term936 Absty Repty mk R) = (term952 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29193 Absty) (@lem29192 Absty Repty mk R)). Qed.
Lemma lem29195 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : ((term935 Absty Repty mk R) = (term936 Absty Repty mk R)) = ((term934 Absty Repty mk R) = (term952 Absty Repty mk R)).
Proof. exact (MK_COMB (@lem29186 Absty Repty mk R) (@lem29194 Absty Repty mk R)). Qed.
Lemma lem29196 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term934 Absty Repty mk R) = (term952 Absty Repty mk R).
Proof. exact (EQ_MP (@lem29195 Absty Repty mk R) (@lem29173 Absty Repty mk R)). Qed.
Lemma lem29200 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem29201 {Absty : Type'} (P : Absty -> Prop) (Q : Prop) : (term179 Absty P Q) = (term180 Absty P Q).
Proof. exact (@lem29200 Absty P Q). Qed.
Lemma lem29202 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term953 Absty Repty mk R P) = (term954 Absty Repty mk R P).
Proof. exact (@lem29201 Absty (term857 Absty Repty mk R P) (term931 Absty Repty mk R P)). Qed.
Lemma lem29203 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term955 Absty Repty mk R P x) = (term856 Absty Repty x mk R P).
Proof. exact (eq_refl (term955 Absty Repty mk R P x)). Qed.
Lemma lem29204 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term956 Absty Repty mk R P) = (term857 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem29203 Absty Repty x mk R P)). Qed.
Lemma lem29205 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29206 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term957 Absty Repty mk R P) = (term858 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29205 Absty) (@lem29204 Absty Repty mk R P)). Qed.
Lemma lem29207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29208 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term958 Absty Repty mk R P) = (term947 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29207) (@lem29206 Absty Repty mk R P)). Qed.
Lemma lem29209 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term931 Absty Repty mk R P) = (term931 Absty Repty mk R P).
Proof. exact (eq_refl (term931 Absty Repty mk R P)). Qed.
Lemma lem29210 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term953 Absty Repty mk R P) = (term949 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29208 Absty Repty mk R P) (@lem29209 Absty Repty mk R P)). Qed.
Lemma lem29211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29212 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term959 Absty Repty mk R P) = (term960 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29211) (@lem29210 Absty Repty mk R P)). Qed.
Lemma lem29213 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term955 Absty Repty mk R P x) = (term856 Absty Repty x mk R P).
Proof. exact (eq_refl (term955 Absty Repty mk R P x)). Qed.
Lemma lem29214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29215 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term961 Absty Repty mk R P x) = (term962 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29214) (@lem29213 Absty Repty x mk R P)). Qed.
Lemma lem29216 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term931 Absty Repty mk R P) = (term931 Absty Repty mk R P).
Proof. exact (eq_refl (term931 Absty Repty mk R P)). Qed.
Lemma lem29217 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term963 Absty Repty x mk R P) = (term964 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29215 Absty Repty x mk R P) (@lem29216 Absty Repty mk R P)). Qed.
Lemma lem29218 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term965 Absty Repty mk R P) = (term966 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem29217 Absty Repty x mk R P)). Qed.
Lemma lem29219 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29220 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term954 Absty Repty mk R P) = (term967 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29219 Absty) (@lem29218 Absty Repty mk R P)). Qed.
Lemma lem29221 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term953 Absty Repty mk R P) = (term954 Absty Repty mk R P)) = ((term949 Absty Repty mk R P) = (term967 Absty Repty mk R P)).
Proof. exact (MK_COMB (@lem29212 Absty Repty mk R P) (@lem29220 Absty Repty mk R P)). Qed.
Lemma lem29222 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term949 Absty Repty mk R P) = (term967 Absty Repty mk R P).
Proof. exact (EQ_MP (@lem29221 Absty Repty mk R P) (@lem29202 Absty Repty mk R P)). Qed.
Lemma lem29224 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term588 A P Q) = (term587 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem29225 {Repty : Type'} (P : Repty -> Prop) (Q : Repty -> Prop) : (term588 Repty P Q) = (term587 Repty P Q).
Proof. exact (@lem29224 Repty P Q). Qed.
Lemma lem29226 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term968 Absty Repty x mk R P) = (term969 Absty Repty x mk R P).
Proof. exact (@lem29225 Repty (term855 Absty Repty x mk R P) (term930 Absty Repty mk R P)). Qed.
Lemma lem29227 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x' : Repty) (P : Absty -> Prop) : (term970 Absty Repty x mk R P x') = (term853 Absty Repty x mk R x' P).
Proof. exact (eq_refl (term970 Absty Repty x mk R P x')). Qed.
Lemma lem29228 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term971 Absty Repty x mk R P) = (term855 Absty Repty x mk R P).
Proof. exact (fun_ext (fun x' : Repty => @lem29227 Absty Repty x mk R x' P)). Qed.
Lemma lem29229 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29230 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term972 Absty Repty x mk R P) = (term856 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29229 Repty) (@lem29228 Absty Repty x mk R P)). Qed.
Lemma lem29231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29232 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term973 Absty Repty x mk R P) = (term962 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29231) (@lem29230 Absty Repty x mk R P)). Qed.
Lemma lem29233 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term974 Absty Repty mk R P x) = (term929 Absty Repty x mk R P).
Proof. exact (eq_refl (term974 Absty Repty mk R P x)). Qed.
Lemma lem29234 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term975 Absty Repty mk R P) = (term930 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Repty => @lem29233 Absty Repty x mk R P)). Qed.
Lemma lem29235 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29236 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term976 Absty Repty mk R P) = (term931 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29235 Repty) (@lem29234 Absty Repty mk R P)). Qed.
Lemma lem29237 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term968 Absty Repty x mk R P) = (term964 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29232 Absty Repty x mk R P) (@lem29236 Absty Repty mk R P)). Qed.
Lemma lem29238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29239 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term977 Absty Repty x mk R P) = (term978 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29238) (@lem29237 Absty Repty x mk R P)). Qed.
Lemma lem29240 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x' : Repty) (P : Absty -> Prop) : (term970 Absty Repty x mk R P x') = (term853 Absty Repty x mk R x' P).
Proof. exact (eq_refl (term970 Absty Repty x mk R P x')). Qed.
Lemma lem29241 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29242 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x' : Repty) (P : Absty -> Prop) : (term979 Absty Repty x mk R P x') = (term980 Absty Repty x mk R x' P).
Proof. exact (MK_COMB (@lem29241) (@lem29240 Absty Repty x mk R x' P)). Qed.
Lemma lem29243 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term974 Absty Repty mk R P x) = (term929 Absty Repty x mk R P).
Proof. exact (eq_refl (term974 Absty Repty mk R P x)). Qed.
Lemma lem29244 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term981 Absty Repty x mk R P x') = (term982 Absty Repty x x' mk R P).
Proof. exact (MK_COMB (@lem29242 Absty Repty x mk R x' P) (@lem29243 Absty Repty x' mk R P)). Qed.
Lemma lem29245 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term983 Absty Repty x mk R P) = (term984 Absty Repty x mk R P).
Proof. exact (fun_ext (fun x' : Repty => @lem29244 Absty Repty x x' mk R P)). Qed.
Lemma lem29246 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29247 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term969 Absty Repty x mk R P) = (term985 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29246 Repty) (@lem29245 Absty Repty x mk R P)). Qed.
Lemma lem29248 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term968 Absty Repty x mk R P) = (term969 Absty Repty x mk R P)) = ((term964 Absty Repty x mk R P) = (term985 Absty Repty x mk R P)).
Proof. exact (MK_COMB (@lem29239 Absty Repty x mk R P) (@lem29247 Absty Repty x mk R P)). Qed.
Lemma lem29249 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term964 Absty Repty x mk R P) = (term985 Absty Repty x mk R P).
Proof. exact (EQ_MP (@lem29248 Absty Repty x mk R P) (@lem29226 Absty Repty x mk R P)). Qed.
Lemma lem29251 {A : Type'} (P : Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem29252 {Absty : Type'} (P : Prop) (Q : Absty -> Prop) : (term843 Absty P Q) = (term844 Absty P Q).
Proof. exact (@lem29251 Absty P Q). Qed.
Lemma lem29253 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term986 Absty Repty x x' mk R P) = (term987 Absty Repty x x' mk R P).
Proof. exact (@lem29252 Absty (term853 Absty Repty x mk R x' P) (term928 Absty Repty x' mk R P)). Qed.
Lemma lem29254 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x' : Absty) : (term988 Absty Repty x mk R P x') = (term926 Absty Repty x mk R P x').
Proof. exact (eq_refl (term988 Absty Repty x mk R P x')). Qed.
Lemma lem29255 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term989 Absty Repty x mk R P) = (term928 Absty Repty x mk R P).
Proof. exact (fun_ext (fun x' : Absty => @lem29254 Absty Repty x mk R P x')). Qed.
Lemma lem29256 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29257 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term990 Absty Repty x mk R P) = (term929 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29256 Absty) (@lem29255 Absty Repty x mk R P)). Qed.
Lemma lem29258 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x' : Repty) (P : Absty -> Prop) : (term980 Absty Repty x mk R x' P) = (term980 Absty Repty x mk R x' P).
Proof. exact (eq_refl (term980 Absty Repty x mk R x' P)). Qed.
Lemma lem29259 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term986 Absty Repty x x' mk R P) = (term982 Absty Repty x x' mk R P).
Proof. exact (MK_COMB (@lem29258 Absty Repty x mk R x' P) (@lem29257 Absty Repty x' mk R P)). Qed.
Lemma lem29260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29261 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term991 Absty Repty x x' mk R P) = (term992 Absty Repty x x' mk R P).
Proof. exact (MK_COMB (@lem29260) (@lem29259 Absty Repty x x' mk R P)). Qed.
Lemma lem29262 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x' : Absty) : (term988 Absty Repty x mk R P x') = (term926 Absty Repty x mk R P x').
Proof. exact (eq_refl (term988 Absty Repty x mk R P x')). Qed.
Lemma lem29263 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x' : Repty) (P : Absty -> Prop) : (term980 Absty Repty x mk R x' P) = (term980 Absty Repty x mk R x' P).
Proof. exact (eq_refl (term980 Absty Repty x mk R x' P)). Qed.
Lemma lem29264 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) : (term993 Absty Repty x x' mk R P x'') = (term994 Absty Repty x x' mk R P x'').
Proof. exact (MK_COMB (@lem29263 Absty Repty x mk R x' P) (@lem29262 Absty Repty x' mk R P x'')). Qed.
Lemma lem29265 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term995 Absty Repty x x' mk R P) = (term996 Absty Repty x x' mk R P).
Proof. exact (fun_ext (fun x'' : Absty => @lem29264 Absty Repty x x' mk R P x'')). Qed.
Lemma lem29266 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29267 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term987 Absty Repty x x' mk R P) = (term997 Absty Repty x x' mk R P).
Proof. exact (MK_COMB (@lem29266 Absty) (@lem29265 Absty Repty x x' mk R P)). Qed.
Lemma lem29268 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term986 Absty Repty x x' mk R P) = (term987 Absty Repty x x' mk R P)) = ((term982 Absty Repty x x' mk R P) = (term997 Absty Repty x x' mk R P)).
Proof. exact (MK_COMB (@lem29261 Absty Repty x x' mk R P) (@lem29267 Absty Repty x x' mk R P)). Qed.
Lemma lem29269 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term982 Absty Repty x x' mk R P) = (term997 Absty Repty x x' mk R P).
Proof. exact (EQ_MP (@lem29268 Absty Repty x x' mk R P) (@lem29253 Absty Repty x x' mk R P)). Qed.
Lemma lem29270 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term984 Absty Repty x mk R P) = (term998 Absty Repty x mk R P).
Proof. exact (fun_ext (fun x' : Repty => @lem29269 Absty Repty x x' mk R P)). Qed.
Lemma lem29271 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29272 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term985 Absty Repty x mk R P) = (term999 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29271 Repty) (@lem29270 Absty Repty x mk R P)). Qed.
Lemma lem29273 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term964 Absty Repty x mk R P) = (term999 Absty Repty x mk R P).
Proof. exact (TRANS (@lem29249 Absty Repty x mk R P) (@lem29272 Absty Repty x mk R P)). Qed.
Lemma lem29274 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term966 Absty Repty mk R P) = (term1000 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem29273 Absty Repty x mk R P)). Qed.
Lemma lem29275 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29276 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term967 Absty Repty mk R P) = (term1001 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29275 Absty) (@lem29274 Absty Repty mk R P)). Qed.
Lemma lem29277 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term949 Absty Repty mk R P) = (term1001 Absty Repty mk R P).
Proof. exact (TRANS (@lem29222 Absty Repty mk R P) (@lem29276 Absty Repty mk R P)). Qed.
Lemma lem29278 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term951 Absty Repty mk R) = (term1002 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29277 Absty Repty mk R P)). Qed.
Lemma lem29279 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29280 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term952 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29279 Absty) (@lem29278 Absty Repty mk R)). Qed.
Lemma lem29281 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term934 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (TRANS (@lem29196 Absty Repty mk R) (@lem29280 Absty Repty mk R)). Qed.
Lemma lem29282 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term702 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (TRANS (@lem29169 Absty Repty mk R) (@lem29281 Absty Repty mk R)). Qed.
Lemma lem29283 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term703 Absty Repty mk R) = (term1004 Absty Repty mk R).
Proof. exact (MK_COMB (@lem28912 Repty R) (@lem29282 Absty Repty mk R)). Qed.
Lemma lem29287 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem29288 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem29287 Repty P Q). Qed.
Lemma lem29289 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1005 Absty Repty mk R) = (term1006 Absty Repty mk R).
Proof. exact (@lem29288 Repty (term774 Repty R) (term1003 Absty Repty mk R)). Qed.
Lemma lem29290 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term1007 Repty R x) = (term773 Repty x R).
Proof. exact (eq_refl (term1007 Repty R x)). Qed.
Lemma lem29291 {Repty : Type'} (R : type1402 Repty) : (term1008 Repty R) = (term774 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem29290 Repty x R)). Qed.
Lemma lem29292 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29293 {Repty : Type'} (R : type1402 Repty) : (term1009 Repty R) = (term775 Repty R).
Proof. exact (MK_COMB (@lem29292 Repty) (@lem29291 Repty R)). Qed.
Lemma lem29294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29295 {Repty : Type'} (R : type1402 Repty) : (term1010 Repty R) = (term776 Repty R).
Proof. exact (MK_COMB (@lem29294) (@lem29293 Repty R)). Qed.
Lemma lem29296 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1003 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (eq_refl (term1003 Absty Repty mk R)). Qed.
Lemma lem29297 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1005 Absty Repty mk R) = (term1004 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29295 Repty R) (@lem29296 Absty Repty mk R)). Qed.
Lemma lem29298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29299 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1011 Absty Repty mk R) = (term1012 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29298) (@lem29297 Absty Repty mk R)). Qed.
Lemma lem29300 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term1007 Repty R x) = (term773 Repty x R).
Proof. exact (eq_refl (term1007 Repty R x)). Qed.
Lemma lem29301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29302 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term1013 Repty R x) = (term1014 Repty x R).
Proof. exact (MK_COMB (@lem29301) (@lem29300 Repty x R)). Qed.
Lemma lem29303 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1003 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (eq_refl (term1003 Absty Repty mk R)). Qed.
Lemma lem29304 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1015 Absty Repty x mk R) = (term1016 Absty Repty x mk R).
Proof. exact (MK_COMB (@lem29302 Repty x R) (@lem29303 Absty Repty mk R)). Qed.
Lemma lem29305 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1017 Absty Repty mk R) = (term1018 Absty Repty mk R).
Proof. exact (fun_ext (fun x : Repty => @lem29304 Absty Repty x mk R)). Qed.
Lemma lem29306 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29307 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1006 Absty Repty mk R) = (term1019 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29306 Repty) (@lem29305 Absty Repty mk R)). Qed.
Lemma lem29308 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : ((term1005 Absty Repty mk R) = (term1006 Absty Repty mk R)) = ((term1004 Absty Repty mk R) = (term1019 Absty Repty mk R)).
Proof. exact (MK_COMB (@lem29299 Absty Repty mk R) (@lem29307 Absty Repty mk R)). Qed.
Lemma lem29309 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1004 Absty Repty mk R) = (term1019 Absty Repty mk R).
Proof. exact (EQ_MP (@lem29308 Absty Repty mk R) (@lem29289 Absty Repty mk R)). Qed.
Lemma lem29313 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem29314 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem29313 Repty P Q). Qed.
Lemma lem29315 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1020 Absty Repty x mk R) = (term1021 Absty Repty x mk R).
Proof. exact (@lem29314 Repty (term772 Repty x R) (term1003 Absty Repty mk R)). Qed.
Lemma lem29316 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1022 Repty x R y) = (term771 Repty x R y).
Proof. exact (eq_refl (term1022 Repty x R y)). Qed.
Lemma lem29317 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term1023 Repty x R) = (term772 Repty x R).
Proof. exact (fun_ext (fun y : Repty => @lem29316 Repty x R y)). Qed.
Lemma lem29318 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29319 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term1024 Repty x R) = (term773 Repty x R).
Proof. exact (MK_COMB (@lem29318 Repty) (@lem29317 Repty x R)). Qed.
Lemma lem29320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29321 {Repty : Type'} (x : Repty) (R : type1402 Repty) : (term1025 Repty x R) = (term1014 Repty x R).
Proof. exact (MK_COMB (@lem29320) (@lem29319 Repty x R)). Qed.
Lemma lem29322 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1003 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (eq_refl (term1003 Absty Repty mk R)). Qed.
Lemma lem29323 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1020 Absty Repty x mk R) = (term1016 Absty Repty x mk R).
Proof. exact (MK_COMB (@lem29321 Repty x R) (@lem29322 Absty Repty mk R)). Qed.
Lemma lem29324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29325 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1026 Absty Repty x mk R) = (term1027 Absty Repty x mk R).
Proof. exact (MK_COMB (@lem29324) (@lem29323 Absty Repty x mk R)). Qed.
Lemma lem29326 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1022 Repty x R y) = (term771 Repty x R y).
Proof. exact (eq_refl (term1022 Repty x R y)). Qed.
Lemma lem29327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29328 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1028 Repty x R y) = (term1029 Repty x R y).
Proof. exact (MK_COMB (@lem29327) (@lem29326 Repty x R y)). Qed.
Lemma lem29329 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1003 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (eq_refl (term1003 Absty Repty mk R)). Qed.
Lemma lem29330 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1030 Absty Repty x y mk R) = (term1031 Absty Repty x y mk R).
Proof. exact (MK_COMB (@lem29328 Repty x R y) (@lem29329 Absty Repty mk R)). Qed.
Lemma lem29331 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1032 Absty Repty x mk R) = (term1033 Absty Repty x mk R).
Proof. exact (fun_ext (fun y : Repty => @lem29330 Absty Repty x y mk R)). Qed.
Lemma lem29332 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29333 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1021 Absty Repty x mk R) = (term1034 Absty Repty x mk R).
Proof. exact (MK_COMB (@lem29332 Repty) (@lem29331 Absty Repty x mk R)). Qed.
Lemma lem29334 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : ((term1020 Absty Repty x mk R) = (term1021 Absty Repty x mk R)) = ((term1016 Absty Repty x mk R) = (term1034 Absty Repty x mk R)).
Proof. exact (MK_COMB (@lem29325 Absty Repty x mk R) (@lem29333 Absty Repty x mk R)). Qed.
Lemma lem29335 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1016 Absty Repty x mk R) = (term1034 Absty Repty x mk R).
Proof. exact (EQ_MP (@lem29334 Absty Repty x mk R) (@lem29315 Absty Repty x mk R)). Qed.
Lemma lem29339 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem29340 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem29339 Repty P Q). Qed.
Lemma lem29341 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1035 Absty Repty x y mk R) = (term1036 Absty Repty x y mk R).
Proof. exact (@lem29340 Repty (term770 Repty x R y) (term1003 Absty Repty mk R)). Qed.
Lemma lem29342 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1037 Repty x R y x') = (term768 Repty x' x R y).
Proof. exact (eq_refl (term1037 Repty x R y x')). Qed.
Lemma lem29343 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1038 Repty x R y) = (term770 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem29342 Repty x' x R y)). Qed.
Lemma lem29344 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29345 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1039 Repty x R y) = (term771 Repty x R y).
Proof. exact (MK_COMB (@lem29344 Repty) (@lem29343 Repty x R y)). Qed.
Lemma lem29346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29347 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1040 Repty x R y) = (term1029 Repty x R y).
Proof. exact (MK_COMB (@lem29346) (@lem29345 Repty x R y)). Qed.
Lemma lem29348 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1003 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (eq_refl (term1003 Absty Repty mk R)). Qed.
Lemma lem29349 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1035 Absty Repty x y mk R) = (term1031 Absty Repty x y mk R).
Proof. exact (MK_COMB (@lem29347 Repty x R y) (@lem29348 Absty Repty mk R)). Qed.
Lemma lem29350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29351 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1041 Absty Repty x y mk R) = (term1042 Absty Repty x y mk R).
Proof. exact (MK_COMB (@lem29350) (@lem29349 Absty Repty x y mk R)). Qed.
Lemma lem29352 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1037 Repty x R y x') = (term768 Repty x' x R y).
Proof. exact (eq_refl (term1037 Repty x R y x')). Qed.
Lemma lem29353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29354 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1043 Repty x R y x') = (term1044 Repty x' x R y).
Proof. exact (MK_COMB (@lem29353) (@lem29352 Repty x' x R y)). Qed.
Lemma lem29355 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1003 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (eq_refl (term1003 Absty Repty mk R)). Qed.
Lemma lem29356 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1045 Absty Repty x y x' mk R) = (term1046 Absty Repty x' x y mk R).
Proof. exact (MK_COMB (@lem29354 Repty x' x R y) (@lem29355 Absty Repty mk R)). Qed.
Lemma lem29357 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1047 Absty Repty x y mk R) = (term1048 Absty Repty x y mk R).
Proof. exact (fun_ext (fun x' : Repty => @lem29356 Absty Repty x' x y mk R)). Qed.
Lemma lem29358 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29359 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1036 Absty Repty x y mk R) = (term1049 Absty Repty x y mk R).
Proof. exact (MK_COMB (@lem29358 Repty) (@lem29357 Absty Repty x y mk R)). Qed.
Lemma lem29360 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : ((term1035 Absty Repty x y mk R) = (term1036 Absty Repty x y mk R)) = ((term1031 Absty Repty x y mk R) = (term1049 Absty Repty x y mk R)).
Proof. exact (MK_COMB (@lem29351 Absty Repty x y mk R) (@lem29359 Absty Repty x y mk R)). Qed.
Lemma lem29361 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1031 Absty Repty x y mk R) = (term1049 Absty Repty x y mk R).
Proof. exact (EQ_MP (@lem29360 Absty Repty x y mk R) (@lem29341 Absty Repty x y mk R)). Qed.
Lemma lem29363 {A : Type'} (P : Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem29364 {Absty : Type'} (P : Prop) (Q : type686 Absty) : (term1050 Absty P Q) = (term1051 Absty P Q).
Proof. exact (@lem29363 (Absty -> Prop) P Q). Qed.
Lemma lem29365 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1052 Absty Repty x' x y mk R) = (term1053 Absty Repty x' x y mk R).
Proof. exact (@lem29364 Absty (term768 Repty x' x R y) (term1002 Absty Repty mk R)). Qed.
Lemma lem29366 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1054 Absty Repty mk R P) = (term1001 Absty Repty mk R P).
Proof. exact (eq_refl (term1054 Absty Repty mk R P)). Qed.
Lemma lem29367 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1055 Absty Repty mk R) = (term1002 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29366 Absty Repty mk R P)). Qed.
Lemma lem29368 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29369 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1056 Absty Repty mk R) = (term1003 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29368 Absty) (@lem29367 Absty Repty mk R)). Qed.
Lemma lem29370 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29371 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1052 Absty Repty x' x y mk R) = (term1046 Absty Repty x' x y mk R).
Proof. exact (MK_COMB (@lem29370 Repty x' x R y) (@lem29369 Absty Repty mk R)). Qed.
Lemma lem29372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29373 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1057 Absty Repty x' x y mk R) = (term1058 Absty Repty x' x y mk R).
Proof. exact (MK_COMB (@lem29372) (@lem29371 Absty Repty x' x y mk R)). Qed.
Lemma lem29374 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1054 Absty Repty mk R P) = (term1001 Absty Repty mk R P).
Proof. exact (eq_refl (term1054 Absty Repty mk R P)). Qed.
Lemma lem29375 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29376 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1059 Absty Repty x' x y mk R P) = (term1060 Absty Repty x' x y mk R P).
Proof. exact (MK_COMB (@lem29375 Repty x' x R y) (@lem29374 Absty Repty mk R P)). Qed.
Lemma lem29377 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1061 Absty Repty x' x y mk R) = (term1062 Absty Repty x' x y mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29376 Absty Repty x' x y mk R P)). Qed.
Lemma lem29378 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29379 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1053 Absty Repty x' x y mk R) = (term1063 Absty Repty x' x y mk R).
Proof. exact (MK_COMB (@lem29378 Absty) (@lem29377 Absty Repty x' x y mk R)). Qed.
Lemma lem29380 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : ((term1052 Absty Repty x' x y mk R) = (term1053 Absty Repty x' x y mk R)) = ((term1046 Absty Repty x' x y mk R) = (term1063 Absty Repty x' x y mk R)).
Proof. exact (MK_COMB (@lem29373 Absty Repty x' x y mk R) (@lem29379 Absty Repty x' x y mk R)). Qed.
Lemma lem29381 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1046 Absty Repty x' x y mk R) = (term1063 Absty Repty x' x y mk R).
Proof. exact (EQ_MP (@lem29380 Absty Repty x' x y mk R) (@lem29365 Absty Repty x' x y mk R)). Qed.
Lemma lem29383 {A : Type'} (P : Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem29384 {Absty : Type'} (P : Prop) (Q : Absty -> Prop) : (term843 Absty P Q) = (term844 Absty P Q).
Proof. exact (@lem29383 Absty P Q). Qed.
Lemma lem29385 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1064 Absty Repty x' x y mk R P) = (term1065 Absty Repty x' x y mk R P).
Proof. exact (@lem29384 Absty (term768 Repty x' x R y) (term1000 Absty Repty mk R P)). Qed.
Lemma lem29386 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1066 Absty Repty mk R P x) = (term999 Absty Repty x mk R P).
Proof. exact (eq_refl (term1066 Absty Repty mk R P x)). Qed.
Lemma lem29387 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1067 Absty Repty mk R P) = (term1000 Absty Repty mk R P).
Proof. exact (fun_ext (fun x : Absty => @lem29386 Absty Repty x mk R P)). Qed.
Lemma lem29388 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29389 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1068 Absty Repty mk R P) = (term1001 Absty Repty mk R P).
Proof. exact (MK_COMB (@lem29388 Absty) (@lem29387 Absty Repty mk R P)). Qed.
Lemma lem29390 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29391 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1064 Absty Repty x' x y mk R P) = (term1060 Absty Repty x' x y mk R P).
Proof. exact (MK_COMB (@lem29390 Repty x' x R y) (@lem29389 Absty Repty mk R P)). Qed.
Lemma lem29392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29393 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1069 Absty Repty x' x y mk R P) = (term1070 Absty Repty x' x y mk R P).
Proof. exact (MK_COMB (@lem29392) (@lem29391 Absty Repty x' x y mk R P)). Qed.
Lemma lem29394 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1066 Absty Repty mk R P x) = (term999 Absty Repty x mk R P).
Proof. exact (eq_refl (term1066 Absty Repty mk R P x)). Qed.
Lemma lem29395 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29396 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1071 Absty Repty x' x y mk R P x'') = (term1072 Absty Repty x' x y x'' mk R P).
Proof. exact (MK_COMB (@lem29395 Repty x' x R y) (@lem29394 Absty Repty x'' mk R P)). Qed.
Lemma lem29397 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1073 Absty Repty x' x y mk R P) = (term1074 Absty Repty x' x y mk R P).
Proof. exact (fun_ext (fun x'' : Absty => @lem29396 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29398 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29399 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1065 Absty Repty x' x y mk R P) = (term1075 Absty Repty x' x y mk R P).
Proof. exact (MK_COMB (@lem29398 Absty) (@lem29397 Absty Repty x' x y mk R P)). Qed.
Lemma lem29400 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term1064 Absty Repty x' x y mk R P) = (term1065 Absty Repty x' x y mk R P)) = ((term1060 Absty Repty x' x y mk R P) = (term1075 Absty Repty x' x y mk R P)).
Proof. exact (MK_COMB (@lem29393 Absty Repty x' x y mk R P) (@lem29399 Absty Repty x' x y mk R P)). Qed.
Lemma lem29401 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1060 Absty Repty x' x y mk R P) = (term1075 Absty Repty x' x y mk R P).
Proof. exact (EQ_MP (@lem29400 Absty Repty x' x y mk R P) (@lem29385 Absty Repty x' x y mk R P)). Qed.
Lemma lem29403 {A : Type'} (P : Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem29404 {Repty : Type'} (P : Prop) (Q : Repty -> Prop) : (term843 Repty P Q) = (term844 Repty P Q).
Proof. exact (@lem29403 Repty P Q). Qed.
Lemma lem29405 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1076 Absty Repty x' x y x'' mk R P) = (term1077 Absty Repty x' x y x'' mk R P).
Proof. exact (@lem29404 Repty (term768 Repty x' x R y) (term998 Absty Repty x'' mk R P)). Qed.
Lemma lem29406 {Absty Repty : Type'} (x : Absty) (x' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1078 Absty Repty x mk R P x') = (term997 Absty Repty x x' mk R P).
Proof. exact (eq_refl (term1078 Absty Repty x mk R P x')). Qed.
Lemma lem29407 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1079 Absty Repty x mk R P) = (term998 Absty Repty x mk R P).
Proof. exact (fun_ext (fun x' : Repty => @lem29406 Absty Repty x x' mk R P)). Qed.
Lemma lem29408 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29409 {Absty Repty : Type'} (x : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1080 Absty Repty x mk R P) = (term999 Absty Repty x mk R P).
Proof. exact (MK_COMB (@lem29408 Repty) (@lem29407 Absty Repty x mk R P)). Qed.
Lemma lem29410 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29411 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1076 Absty Repty x' x y x'' mk R P) = (term1072 Absty Repty x' x y x'' mk R P).
Proof. exact (MK_COMB (@lem29410 Repty x' x R y) (@lem29409 Absty Repty x'' mk R P)). Qed.
Lemma lem29412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29413 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1081 Absty Repty x' x y x'' mk R P) = (term1082 Absty Repty x' x y x'' mk R P).
Proof. exact (MK_COMB (@lem29412) (@lem29411 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29414 {Absty Repty : Type'} (x : Absty) (x'' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1078 Absty Repty x mk R P x'') = (term997 Absty Repty x x'' mk R P).
Proof. exact (eq_refl (term1078 Absty Repty x mk R P x'')). Qed.
Lemma lem29415 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29416 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1083 Absty Repty x' x y x'' mk R P x''') = (term1084 Absty Repty x' x y x'' x''' mk R P).
Proof. exact (MK_COMB (@lem29415 Repty x' x R y) (@lem29414 Absty Repty x'' x''' mk R P)). Qed.
Lemma lem29417 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1085 Absty Repty x' x y x'' mk R P) = (term1086 Absty Repty x' x y x'' mk R P).
Proof. exact (fun_ext (fun x''' : Repty => @lem29416 Absty Repty x' x y x'' x''' mk R P)). Qed.
Lemma lem29418 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29419 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1077 Absty Repty x' x y x'' mk R P) = (term1087 Absty Repty x' x y x'' mk R P).
Proof. exact (MK_COMB (@lem29418 Repty) (@lem29417 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29420 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term1076 Absty Repty x' x y x'' mk R P) = (term1077 Absty Repty x' x y x'' mk R P)) = ((term1072 Absty Repty x' x y x'' mk R P) = (term1087 Absty Repty x' x y x'' mk R P)).
Proof. exact (MK_COMB (@lem29413 Absty Repty x' x y x'' mk R P) (@lem29419 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29421 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1072 Absty Repty x' x y x'' mk R P) = (term1087 Absty Repty x' x y x'' mk R P).
Proof. exact (EQ_MP (@lem29420 Absty Repty x' x y x'' mk R P) (@lem29405 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29423 {A : Type'} (P : Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem29424 {Absty : Type'} (P : Prop) (Q : Absty -> Prop) : (term843 Absty P Q) = (term844 Absty P Q).
Proof. exact (@lem29423 Absty P Q). Qed.
Lemma lem29425 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1088 Absty Repty x' x y x'' x''' mk R P) = (term1089 Absty Repty x' x y x'' x''' mk R P).
Proof. exact (@lem29424 Absty (term768 Repty x' x R y) (term996 Absty Repty x'' x''' mk R P)). Qed.
Lemma lem29426 {Absty Repty : Type'} (x : Absty) (x'' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x' : Absty) : (term1090 Absty Repty x x'' mk R P x') = (term994 Absty Repty x x'' mk R P x').
Proof. exact (eq_refl (term1090 Absty Repty x x'' mk R P x')). Qed.
Lemma lem29427 {Absty Repty : Type'} (x : Absty) (x'' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1091 Absty Repty x x'' mk R P) = (term996 Absty Repty x x'' mk R P).
Proof. exact (fun_ext (fun x' : Absty => @lem29426 Absty Repty x x'' mk R P x')). Qed.
Lemma lem29428 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29429 {Absty Repty : Type'} (x : Absty) (x'' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1092 Absty Repty x x'' mk R P) = (term997 Absty Repty x x'' mk R P).
Proof. exact (MK_COMB (@lem29428 Absty) (@lem29427 Absty Repty x x'' mk R P)). Qed.
Lemma lem29430 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29431 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1088 Absty Repty x' x y x'' x''' mk R P) = (term1084 Absty Repty x' x y x'' x''' mk R P).
Proof. exact (MK_COMB (@lem29430 Repty x' x R y) (@lem29429 Absty Repty x'' x''' mk R P)). Qed.
Lemma lem29432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem29433 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1093 Absty Repty x' x y x'' x''' mk R P) = (term1094 Absty Repty x' x y x'' x''' mk R P).
Proof. exact (MK_COMB (@lem29432) (@lem29431 Absty Repty x' x y x'' x''' mk R P)). Qed.
Lemma lem29434 {Absty Repty : Type'} (x : Absty) (x'' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x' : Absty) : (term1090 Absty Repty x x'' mk R P x') = (term994 Absty Repty x x'' mk R P x').
Proof. exact (eq_refl (term1090 Absty Repty x x'' mk R P x')). Qed.
Lemma lem29435 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1044 Repty x' x R y).
Proof. exact (eq_refl (term1044 Repty x' x R y)). Qed.
Lemma lem29436 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) : (term1095 Absty Repty x' x y x'' x''' mk R P x'''') = (term1096 Absty Repty x' x y x'' x''' mk R P x'''').
Proof. exact (MK_COMB (@lem29435 Repty x' x R y) (@lem29434 Absty Repty x'' x''' mk R P x'''')). Qed.
Lemma lem29437 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1097 Absty Repty x' x y x'' x''' mk R P) = (term1098 Absty Repty x' x y x'' x''' mk R P).
Proof. exact (fun_ext (fun x'''' : Absty => @lem29436 Absty Repty x' x y x'' x''' mk R P x'''')). Qed.
Lemma lem29438 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29439 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1089 Absty Repty x' x y x'' x''' mk R P) = (term1099 Absty Repty x' x y x'' x''' mk R P).
Proof. exact (MK_COMB (@lem29438 Absty) (@lem29437 Absty Repty x' x y x'' x''' mk R P)). Qed.
Lemma lem29440 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : ((term1088 Absty Repty x' x y x'' x''' mk R P) = (term1089 Absty Repty x' x y x'' x''' mk R P)) = ((term1084 Absty Repty x' x y x'' x''' mk R P) = (term1099 Absty Repty x' x y x'' x''' mk R P)).
Proof. exact (MK_COMB (@lem29433 Absty Repty x' x y x'' x''' mk R P) (@lem29439 Absty Repty x' x y x'' x''' mk R P)). Qed.
Lemma lem29441 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1084 Absty Repty x' x y x'' x''' mk R P) = (term1099 Absty Repty x' x y x'' x''' mk R P).
Proof. exact (EQ_MP (@lem29440 Absty Repty x' x y x'' x''' mk R P) (@lem29425 Absty Repty x' x y x'' x''' mk R P)). Qed.
Lemma lem29442 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1086 Absty Repty x' x y x'' mk R P) = (term1100 Absty Repty x' x y x'' mk R P).
Proof. exact (fun_ext (fun x''' : Repty => @lem29441 Absty Repty x' x y x'' x''' mk R P)). Qed.
Lemma lem29443 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29444 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1087 Absty Repty x' x y x'' mk R P) = (term1101 Absty Repty x' x y x'' mk R P).
Proof. exact (MK_COMB (@lem29443 Repty) (@lem29442 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29445 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1072 Absty Repty x' x y x'' mk R P) = (term1101 Absty Repty x' x y x'' mk R P).
Proof. exact (TRANS (@lem29421 Absty Repty x' x y x'' mk R P) (@lem29444 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29446 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1074 Absty Repty x' x y mk R P) = (term1102 Absty Repty x' x y mk R P).
Proof. exact (fun_ext (fun x'' : Absty => @lem29445 Absty Repty x' x y x'' mk R P)). Qed.
Lemma lem29447 {Absty : Type'} : (@ex Absty) = (@ex Absty).
Proof. exact (eq_refl (@ex Absty)). Qed.
Lemma lem29448 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1075 Absty Repty x' x y mk R P) = (term1103 Absty Repty x' x y mk R P).
Proof. exact (MK_COMB (@lem29447 Absty) (@lem29446 Absty Repty x' x y mk R P)). Qed.
Lemma lem29449 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) : (term1060 Absty Repty x' x y mk R P) = (term1103 Absty Repty x' x y mk R P).
Proof. exact (TRANS (@lem29401 Absty Repty x' x y mk R P) (@lem29448 Absty Repty x' x y mk R P)). Qed.
Lemma lem29450 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1062 Absty Repty x' x y mk R) = (term1104 Absty Repty x' x y mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem29449 Absty Repty x' x y mk R P)). Qed.
Lemma lem29451 {Absty : Type'} : (@ex (Absty -> Prop)) = (@ex (Absty -> Prop)).
Proof. exact (eq_refl (@ex (Absty -> Prop))). Qed.
Lemma lem29452 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1063 Absty Repty x' x y mk R) = (term1105 Absty Repty x' x y mk R).
Proof. exact (MK_COMB (@lem29451 Absty) (@lem29450 Absty Repty x' x y mk R)). Qed.
Lemma lem29453 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1046 Absty Repty x' x y mk R) = (term1105 Absty Repty x' x y mk R).
Proof. exact (TRANS (@lem29381 Absty Repty x' x y mk R) (@lem29452 Absty Repty x' x y mk R)). Qed.
Lemma lem29454 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1048 Absty Repty x y mk R) = (term1106 Absty Repty x y mk R).
Proof. exact (fun_ext (fun x' : Repty => @lem29453 Absty Repty x' x y mk R)). Qed.
Lemma lem29455 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29456 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1049 Absty Repty x y mk R) = (term1107 Absty Repty x y mk R).
Proof. exact (MK_COMB (@lem29455 Repty) (@lem29454 Absty Repty x y mk R)). Qed.
Lemma lem29457 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1031 Absty Repty x y mk R) = (term1107 Absty Repty x y mk R).
Proof. exact (TRANS (@lem29361 Absty Repty x y mk R) (@lem29456 Absty Repty x y mk R)). Qed.
Lemma lem29458 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1033 Absty Repty x mk R) = (term1108 Absty Repty x mk R).
Proof. exact (fun_ext (fun y : Repty => @lem29457 Absty Repty x y mk R)). Qed.
Lemma lem29459 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29460 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1034 Absty Repty x mk R) = (term1109 Absty Repty x mk R).
Proof. exact (MK_COMB (@lem29459 Repty) (@lem29458 Absty Repty x mk R)). Qed.
Lemma lem29461 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1016 Absty Repty x mk R) = (term1109 Absty Repty x mk R).
Proof. exact (TRANS (@lem29335 Absty Repty x mk R) (@lem29460 Absty Repty x mk R)). Qed.
Lemma lem29462 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1018 Absty Repty mk R) = (term1110 Absty Repty mk R).
Proof. exact (fun_ext (fun x : Repty => @lem29461 Absty Repty x mk R)). Qed.
Lemma lem29463 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem29464 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1019 Absty Repty mk R) = (term1111 Absty Repty mk R).
Proof. exact (MK_COMB (@lem29463 Repty) (@lem29462 Absty Repty mk R)). Qed.
Lemma lem29465 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1004 Absty Repty mk R) = (term1111 Absty Repty mk R).
Proof. exact (TRANS (@lem29309 Absty Repty mk R) (@lem29464 Absty Repty mk R)). Qed.
Lemma lem29466 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term703 Absty Repty mk R) = (term1111 Absty Repty mk R).
Proof. exact (TRANS (@lem29283 Absty Repty mk R) (@lem29465 Absty Repty mk R)). Qed.
Lemma lem29467 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term586 Absty Repty mk R) = (term1111 Absty Repty mk R).
Proof. exact (TRANS (@lem28793 Absty Repty mk R) (@lem29466 Absty Repty mk R)). Qed.
Lemma lem29468 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term373 Absty Repty mk R) = (term1111 Absty Repty mk R).
Proof. exact (TRANS (@lem27876 Absty Repty mk R) (@lem29467 Absty Repty mk R)). Qed.
Lemma lem29469 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term373 Absty Repty mk R) : term1111 Absty Repty mk R.
Proof. exact (EQ_MP (@lem29468 Absty Repty mk R) (@lem26757 Absty Repty mk R h1)). Qed.
Lemma lem29470 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term1109 Absty Repty x mk R) : term1109 Absty Repty x mk R.
Proof. exact (h1). Qed.
Lemma lem29471 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term1107 Absty Repty x y mk R) : term1107 Absty Repty x y mk R.
Proof. exact (h1). Qed.
Lemma lem29472 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term1105 Absty Repty x' x y mk R) : term1105 Absty Repty x' x y mk R.
Proof. exact (h1). Qed.
Lemma lem29473 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : term1103 Absty Repty x' x y mk R P) : term1103 Absty Repty x' x y mk R P.
Proof. exact (h1). Qed.
Lemma lem29474 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : term1101 Absty Repty x' x y x'' mk R P) : term1101 Absty Repty x' x y x'' mk R P.
Proof. exact (h1). Qed.
Lemma lem29475 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : term1099 Absty Repty x' x y x'' x''' mk R P) : term1099 Absty Repty x' x y x'' x''' mk R P.
Proof. exact (h1). Qed.
Lemma lem29476 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : term1096 Absty Repty x' x y x'' x''' mk R P x''''.
Proof. exact (h1). Qed.
Lemma lem29477 {Absty Repty : Type'} (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term239 Absty Repty x''''' R dest mk.
Proof. exact (h1). Qed.
Lemma lem29484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29485 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29484 Repty Prop f x). Qed.
Lemma lem29487 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (term1112 Repty R x).
Proof. exact (@lem29485 Repty (R x) x). Qed.
Lemma lem29488 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term1113 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem29487 Repty R x)). Qed.
Lemma lem29489 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29490 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term1114 Repty R).
Proof. exact (MK_COMB (@lem29489 Repty) (@lem29488 Repty R)). Qed.
Lemma lem29491 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term1114 Repty R.
Proof. exact (EQ_MP (@lem29490 Repty R) (@lem26770 Repty R h1)). Qed.
Lemma lem29498 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29499 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29498 Repty Prop f x). Qed.
Lemma lem29501 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (R y x) = (term1115 Repty R y x).
Proof. exact (@lem29499 Repty (R y) x). Qed.
Lemma lem29502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29509 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29510 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29509 Repty Prop f x). Qed.
Lemma lem29512 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (R x y) = (term1115 Repty R x y).
Proof. exact (@lem29510 Repty (R x) y). Qed.
Lemma lem29513 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1116 Repty R x y) = (term1117 Repty R x y).
Proof. exact (MK_COMB (@lem29502) (@lem29512 Repty R x y)). Qed.
Lemma lem29514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29515 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1118 Repty R x y) = (term1119 Repty R x y).
Proof. exact (MK_COMB (@lem29514) (@lem29513 Repty R x y)). Qed.
Lemma lem29516 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term430 Repty R y x) = (term1120 Repty R y x).
Proof. exact (MK_COMB (@lem29515 Repty R x y) (@lem29501 Repty R y x)). Qed.
Lemma lem29517 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term424 Repty R x) = (term1121 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem29516 Repty R y x)). Qed.
Lemma lem29518 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29519 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term442 Repty R x) = (term1122 Repty R x).
Proof. exact (MK_COMB (@lem29518 Repty) (@lem29517 Repty R x)). Qed.
Lemma lem29520 {Repty : Type'} (R : type1402 Repty) : (term449 Repty R) = (term1123 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem29519 Repty R x)). Qed.
Lemma lem29521 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29522 {Repty : Type'} (R : type1402 Repty) : (term464 Repty R) = (term1124 Repty R).
Proof. exact (MK_COMB (@lem29521 Repty) (@lem29520 Repty R)). Qed.
Lemma lem29523 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29530 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29531 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29530 Repty Prop f x). Qed.
Lemma lem29533 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (R y x) = (term1115 Repty R y x).
Proof. exact (@lem29531 Repty (R y) x). Qed.
Lemma lem29534 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term1116 Repty R y x) = (term1117 Repty R y x).
Proof. exact (MK_COMB (@lem29523) (@lem29533 Repty R y x)). Qed.
Lemma lem29541 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29542 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29541 Repty Prop f x). Qed.
Lemma lem29544 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (R x y) = (term1115 Repty R x y).
Proof. exact (@lem29542 Repty (R x) y). Qed.
Lemma lem29545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29546 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1125 Repty R x y) = (term1126 Repty R x y).
Proof. exact (MK_COMB (@lem29545) (@lem29544 Repty R x y)). Qed.
Lemma lem29547 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term426 Repty R y x) = (term1127 Repty R y x).
Proof. exact (MK_COMB (@lem29546 Repty R x y) (@lem29534 Repty R y x)). Qed.
Lemma lem29548 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term423 Repty R x) = (term1128 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem29547 Repty R y x)). Qed.
Lemma lem29549 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29550 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term437 Repty R x) = (term1129 Repty R x).
Proof. exact (MK_COMB (@lem29549 Repty) (@lem29548 Repty R x)). Qed.
Lemma lem29551 {Repty : Type'} (R : type1402 Repty) : (term448 Repty R) = (term1130 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem29550 Repty R x)). Qed.
Lemma lem29552 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29553 {Repty : Type'} (R : type1402 Repty) : (term459 Repty R) = (term1131 Repty R).
Proof. exact (MK_COMB (@lem29552 Repty) (@lem29551 Repty R)). Qed.
Lemma lem29554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29555 {Repty : Type'} (R : type1402 Repty) : (term461 Repty R) = (term1132 Repty R).
Proof. exact (MK_COMB (@lem29554) (@lem29553 Repty R)). Qed.
Lemma lem29556 {Repty : Type'} (R : type1402 Repty) : (term465 Repty R) = (term1133 Repty R).
Proof. exact (MK_COMB (@lem29555 Repty R) (@lem29522 Repty R)). Qed.
Lemma lem29557 {Repty : Type'} (R : type1402 Repty) (h1 : term69 Repty R) : term1133 Repty R.
Proof. exact (EQ_MP (@lem29556 Repty R) (@lem27057 Repty R h1)). Qed.
Lemma lem29564 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29565 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29564 Repty Prop f x). Qed.
Lemma lem29567 {Repty : Type'} (R : type1402 Repty) (x : Repty) (z : Repty) : (R x z) = (term1115 Repty R x z).
Proof. exact (@lem29565 Repty (R x) z). Qed.
Lemma lem29568 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29575 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29576 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29575 Repty Prop f x). Qed.
Lemma lem29578 {Repty : Type'} (R : type1402 Repty) (y : Repty) (z : Repty) : (R y z) = (term1115 Repty R y z).
Proof. exact (@lem29576 Repty (R y) z). Qed.
Lemma lem29579 {Repty : Type'} (R : type1402 Repty) (y : Repty) (z : Repty) : (term1116 Repty R y z) = (term1117 Repty R y z).
Proof. exact (MK_COMB (@lem29568) (@lem29578 Repty R y z)). Qed.
Lemma lem29580 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29588 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29587 Repty Prop f x). Qed.
Lemma lem29590 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (R x y) = (term1115 Repty R x y).
Proof. exact (@lem29588 Repty (R x) y). Qed.
Lemma lem29591 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1116 Repty R x y) = (term1117 Repty R x y).
Proof. exact (MK_COMB (@lem29580) (@lem29590 Repty R x y)). Qed.
Lemma lem29592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29593 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1118 Repty R x y) = (term1119 Repty R x y).
Proof. exact (MK_COMB (@lem29592) (@lem29591 Repty R x y)). Qed.
Lemma lem29594 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (z : Repty) : (term467 Repty x R y z) = (term1134 Repty x R y z).
Proof. exact (MK_COMB (@lem29593 Repty R x y) (@lem29579 Repty R y z)). Qed.
Lemma lem29595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29596 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (z : Repty) : (term469 Repty x R y z) = (term1135 Repty x R y z).
Proof. exact (MK_COMB (@lem29595) (@lem29594 Repty x R y z)). Qed.
Lemma lem29597 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term471 Repty y R x z) = (term1136 Repty y R x z).
Proof. exact (MK_COMB (@lem29596 Repty x R y z) (@lem29567 Repty R x z)). Qed.
Lemma lem29598 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term473 Repty y R x) = (term1137 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem29597 Repty y R x z)). Qed.
Lemma lem29599 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29600 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term474 Repty y R x) = (term1138 Repty y R x).
Proof. exact (MK_COMB (@lem29599 Repty) (@lem29598 Repty y R x)). Qed.
Lemma lem29601 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term475 Repty R x) = (term1139 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem29600 Repty y R x)). Qed.
Lemma lem29602 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29603 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term476 Repty R x) = (term1140 Repty R x).
Proof. exact (MK_COMB (@lem29602 Repty) (@lem29601 Repty R x)). Qed.
Lemma lem29604 {Repty : Type'} (R : type1402 Repty) : (term477 Repty R) = (term1141 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem29603 Repty R x)). Qed.
Lemma lem29605 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29606 {Repty : Type'} (R : type1402 Repty) : (term478 Repty R) = (term1142 Repty R).
Proof. exact (MK_COMB (@lem29605 Repty) (@lem29604 Repty R)). Qed.
Lemma lem29607 {Repty : Type'} (R : type1402 Repty) (h1 : term71 Repty R) : term1142 Repty R.
Proof. exact (EQ_MP (@lem29606 Repty R) (@lem27140 Repty R h1)). Qed.
Lemma lem29616 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem29617 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem29616 Absty Repty mk dest a)). Qed.
Lemma lem29618 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem29619 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem29618 Absty) (@lem29617 Absty Repty mk dest)). Qed.
Lemma lem29620 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term73 Absty Repty mk dest.
Proof. exact (EQ_MP (@lem29619 Absty Repty mk dest) (@lem27153 Absty Repty mk dest h1)). Qed.
Lemma lem29693 {Absty : Type'} (P : Absty -> Prop) (x'''' : Absty) : (P x'''') = (P x'''').
Proof. exact (eq_refl (P x'''')). Qed.
Lemma lem29702 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term522 Absty Repty P mk R x) = (term522 Absty Repty P mk R x).
Proof. exact (eq_refl (term522 Absty Repty P mk R x)). Qed.
Lemma lem29703 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term524 Absty Repty P mk R) = (term524 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem29702 Absty Repty P mk R x)). Qed.
Lemma lem29704 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29705 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term556 Absty Repty P mk R) = (term556 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem29704 Repty) (@lem29703 Absty Repty P mk R)). Qed.
Lemma lem29706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29707 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term560 Absty Repty P mk R) = (term560 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem29706) (@lem29705 Absty Repty P mk R)). Qed.
Lemma lem29708 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) : (term920 Absty Repty mk R P x'''') = (term920 Absty Repty mk R P x'''').
Proof. exact (MK_COMB (@lem29707 Absty Repty P mk R) (@lem29693 Absty P x'''')). Qed.
Lemma lem29713 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term530 Absty P x) = (term530 Absty P x).
Proof. exact (eq_refl (term530 Absty P x)). Qed.
Lemma lem29714 {Absty : Type'} (P : Absty -> Prop) : (term532 Absty P) = (term532 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem29713 Absty P x)). Qed.
Lemma lem29715 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem29716 {Absty : Type'} (P : Absty -> Prop) : (term134 Absty P) = (term134 Absty P).
Proof. exact (MK_COMB (@lem29715 Absty) (@lem29714 Absty P)). Qed.
Lemma lem29725 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) : (term870 Absty Repty P mk R x''') = (term870 Absty Repty P mk R x''').
Proof. exact (eq_refl (term870 Absty Repty P mk R x''')). Qed.
Lemma lem29726 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) : (term872 Absty Repty mk R x''' P) = (term872 Absty Repty mk R x''' P).
Proof. exact (MK_COMB (@lem29725 Absty Repty P mk R x''') (@lem29716 Absty P)). Qed.
Lemma lem29727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29728 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) : (term910 Absty Repty mk R x''' P) = (term910 Absty Repty mk R x''' P).
Proof. exact (MK_COMB (@lem29727) (@lem29726 Absty Repty mk R x''' P)). Qed.
Lemma lem29729 {Absty Repty : Type'} (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) : (term926 Absty Repty x''' mk R P x'''') = (term926 Absty Repty x''' mk R P x'''').
Proof. exact (MK_COMB (@lem29728 Absty Repty mk R x''' P) (@lem29708 Absty Repty mk R P x'''')). Qed.
Lemma lem29732 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem29733 {Absty : Type'} (P : Absty -> Prop) : (term403 Absty P) = (term403 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem29732 Absty P x)). Qed.
Lemma lem29734 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem29735 {Absty : Type'} (P : Absty -> Prop) : (term410 Absty P) = (term410 Absty P).
Proof. exact (MK_COMB (@lem29734 Absty) (@lem29733 Absty P)). Qed.
Lemma lem29746 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) : (term801 Absty Repty P mk R x''') = (term801 Absty Repty P mk R x''').
Proof. exact (eq_refl (term801 Absty Repty P mk R x''')). Qed.
Lemma lem29747 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) : (term803 Absty Repty mk R x''' P) = (term803 Absty Repty mk R x''' P).
Proof. exact (MK_COMB (@lem29746 Absty Repty P mk R x''') (@lem29735 Absty P)). Qed.
Lemma lem29752 {Absty : Type'} (P : Absty -> Prop) (x'' : Absty) : (term530 Absty P x'') = (term530 Absty P x'').
Proof. exact (eq_refl (term530 Absty P x'')). Qed.
Lemma lem29759 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term405 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term405 Absty Repty P mk R x)). Qed.
Lemma lem29760 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term406 Absty Repty P mk R) = (term406 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem29759 Absty Repty P mk R x)). Qed.
Lemma lem29761 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29762 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term411 Absty Repty P mk R) = (term411 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem29761 Repty) (@lem29760 Absty Repty P mk R)). Qed.
Lemma lem29763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29764 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term537 Absty Repty P mk R) = (term537 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem29763) (@lem29762 Absty Repty P mk R)). Qed.
Lemma lem29765 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) : (term785 Absty Repty mk R P x'') = (term785 Absty Repty mk R P x'').
Proof. exact (MK_COMB (@lem29764 Absty Repty P mk R) (@lem29752 Absty P x'')). Qed.
Lemma lem29766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29767 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) : (term837 Absty Repty mk R P x'') = (term837 Absty Repty mk R P x'').
Proof. exact (MK_COMB (@lem29766) (@lem29765 Absty Repty mk R P x'')). Qed.
Lemma lem29768 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) : (term853 Absty Repty x'' mk R x''' P) = (term853 Absty Repty x'' mk R x''' P).
Proof. exact (MK_COMB (@lem29767 Absty Repty mk R P x'') (@lem29747 Absty Repty mk R x''' P)). Qed.
Lemma lem29769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29770 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) : (term980 Absty Repty x'' mk R x''' P) = (term980 Absty Repty x'' mk R x''' P).
Proof. exact (MK_COMB (@lem29769) (@lem29768 Absty Repty x'' mk R x''' P)). Qed.
Lemma lem29771 {Absty Repty : Type'} (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) : (term994 Absty Repty x'' x''' mk R P x'''') = (term994 Absty Repty x'' x''' mk R P x'''').
Proof. exact (MK_COMB (@lem29770 Absty Repty x'' mk R x''' P) (@lem29729 Absty Repty x''' mk R P x'''')). Qed.
Lemma lem29778 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29779 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29778 Repty Prop f x). Qed.
Lemma lem29781 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (R y x') = (term1115 Repty R y x').
Proof. exact (@lem29779 Repty (R y) x'). Qed.
Lemma lem29782 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29790 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29789 Repty Prop f x). Qed.
Lemma lem29792 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (R x x') = (term1115 Repty R x x').
Proof. exact (@lem29790 Repty (R x) x'). Qed.
Lemma lem29793 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1116 Repty R x x') = (term1117 Repty R x x').
Proof. exact (MK_COMB (@lem29782) (@lem29792 Repty R x x')). Qed.
Lemma lem29794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29795 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1118 Repty R x x') = (term1119 Repty R x x').
Proof. exact (MK_COMB (@lem29794) (@lem29793 Repty R x x')). Qed.
Lemma lem29796 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term618 Repty x R y x') = (term1143 Repty x R y x').
Proof. exact (MK_COMB (@lem29795 Repty R x x') (@lem29781 Repty R y x')). Qed.
Lemma lem29797 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term612 Repty x R y) = (term1144 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem29796 Repty x R y x')). Qed.
Lemma lem29798 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29799 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term630 Repty x R y) = (term1145 Repty x R y).
Proof. exact (MK_COMB (@lem29798 Repty) (@lem29797 Repty x R y)). Qed.
Lemma lem29800 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29808 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29807 Repty Prop f x). Qed.
Lemma lem29810 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (R y x') = (term1115 Repty R y x').
Proof. exact (@lem29808 Repty (R y) x'). Qed.
Lemma lem29811 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1116 Repty R y x') = (term1117 Repty R y x').
Proof. exact (MK_COMB (@lem29800) (@lem29810 Repty R y x')). Qed.
Lemma lem29818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29819 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29818 Repty Prop f x). Qed.
Lemma lem29821 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (R x x') = (term1115 Repty R x x').
Proof. exact (@lem29819 Repty (R x) x'). Qed.
Lemma lem29822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29823 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1125 Repty R x x') = (term1126 Repty R x x').
Proof. exact (MK_COMB (@lem29822) (@lem29821 Repty R x x')). Qed.
Lemma lem29824 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term614 Repty x R y x') = (term1146 Repty x R y x').
Proof. exact (MK_COMB (@lem29823 Repty R x x') (@lem29811 Repty R y x')). Qed.
Lemma lem29825 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term611 Repty x R y) = (term1147 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem29824 Repty x R y x')). Qed.
Lemma lem29826 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29827 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term625 Repty x R y) = (term1148 Repty x R y).
Proof. exact (MK_COMB (@lem29826 Repty) (@lem29825 Repty x R y)). Qed.
Lemma lem29828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29829 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term627 Repty x R y) = (term1149 Repty x R y).
Proof. exact (MK_COMB (@lem29828) (@lem29827 Repty x R y)). Qed.
Lemma lem29830 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term631 Repty x R y) = (term1150 Repty x R y).
Proof. exact (MK_COMB (@lem29829 Repty x R y) (@lem29799 Repty x R y)). Qed.
Lemma lem29831 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29839 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29838 Repty Prop f x). Qed.
Lemma lem29841 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (R x y) = (term1115 Repty R x y).
Proof. exact (@lem29839 Repty (R x) y). Qed.
Lemma lem29842 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1116 Repty R x y) = (term1117 Repty R x y).
Proof. exact (MK_COMB (@lem29831) (@lem29841 Repty R x y)). Qed.
Lemma lem29843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29844 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term493 Repty R x y) = (term1151 Repty R x y).
Proof. exact (MK_COMB (@lem29843) (@lem29842 Repty R x y)). Qed.
Lemma lem29845 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term632 Repty x R y) = (term1152 Repty x R y).
Proof. exact (MK_COMB (@lem29844 Repty R x y) (@lem29830 Repty x R y)). Qed.
Lemma lem29846 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29854 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29853 Repty Prop f x). Qed.
Lemma lem29856 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (R y x') = (term1115 Repty R y x').
Proof. exact (@lem29854 Repty (R y) x'). Qed.
Lemma lem29857 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1116 Repty R y x') = (term1117 Repty R y x').
Proof. exact (MK_COMB (@lem29846) (@lem29856 Repty R y x')). Qed.
Lemma lem29858 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem29865 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29866 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29865 Repty Prop f x). Qed.
Lemma lem29868 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (R x x') = (term1115 Repty R x x').
Proof. exact (@lem29866 Repty (R x) x'). Qed.
Lemma lem29869 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1116 Repty R x x') = (term1117 Repty R x x').
Proof. exact (MK_COMB (@lem29858) (@lem29868 Repty R x x')). Qed.
Lemma lem29870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29871 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1118 Repty R x x') = (term1119 Repty R x x').
Proof. exact (MK_COMB (@lem29870) (@lem29869 Repty R x x')). Qed.
Lemma lem29872 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1153 Repty x R y x') = (term1154 Repty x R y x').
Proof. exact (MK_COMB (@lem29871 Repty R x x') (@lem29857 Repty R y x')). Qed.
Lemma lem29879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29880 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29879 Repty Prop f x). Qed.
Lemma lem29882 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (R y x') = (term1115 Repty R y x').
Proof. exact (@lem29880 Repty (R y) x'). Qed.
Lemma lem29889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29890 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29889 Repty Prop f x). Qed.
Lemma lem29892 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (R x x') = (term1115 Repty R x x').
Proof. exact (@lem29890 Repty (R x) x'). Qed.
Lemma lem29893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29894 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1125 Repty R x x') = (term1126 Repty R x x').
Proof. exact (MK_COMB (@lem29893) (@lem29892 Repty R x x')). Qed.
Lemma lem29895 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1155 Repty x R y x') = (term1156 Repty x R y x').
Proof. exact (MK_COMB (@lem29894 Repty R x x') (@lem29882 Repty R y x')). Qed.
Lemma lem29896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29897 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1157 Repty x R y x') = (term1158 Repty x R y x').
Proof. exact (MK_COMB (@lem29896) (@lem29895 Repty x R y x')). Qed.
Lemma lem29898 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term480 Repty x R y x') = (term1159 Repty x R y x').
Proof. exact (MK_COMB (@lem29897 Repty x R y x') (@lem29872 Repty x R y x')). Qed.
Lemma lem29905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem29906 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem29905 Repty Prop f x). Qed.
Lemma lem29908 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (R x y) = (term1115 Repty R x y).
Proof. exact (@lem29906 Repty (R x) y). Qed.
Lemma lem29909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29910 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term496 Repty R x y) = (term1160 Repty R x y).
Proof. exact (MK_COMB (@lem29909) (@lem29908 Repty R x y)). Qed.
Lemma lem29911 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term714 Repty x R y x') = (term1161 Repty x R y x').
Proof. exact (MK_COMB (@lem29910 Repty R x y) (@lem29898 Repty x R y x')). Qed.
Lemma lem29912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29913 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term766 Repty x R y x') = (term1162 Repty x R y x').
Proof. exact (MK_COMB (@lem29912) (@lem29911 Repty x R y x')). Qed.
Lemma lem29914 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term768 Repty x' x R y) = (term1163 Repty x' x R y).
Proof. exact (MK_COMB (@lem29913 Repty x R y x') (@lem29845 Repty x R y)). Qed.
Lemma lem29915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29916 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (term1044 Repty x' x R y) = (term1164 Repty x' x R y).
Proof. exact (MK_COMB (@lem29915) (@lem29914 Repty x' x R y)). Qed.
Lemma lem29917 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) : (term1096 Absty Repty x' x y x'' x''' mk R P x'''') = (term1165 Absty Repty x' x y x'' x''' mk R P x'''').
Proof. exact (MK_COMB (@lem29916 Repty x' x R y) (@lem29771 Absty Repty x'' x''' mk R P x'''')). Qed.
Lemma lem29918 {Absty Repty : Type'} (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : term1165 Absty Repty x' x y x'' x''' mk R P x''''.
Proof. exact (EQ_MP (@lem29917 Absty Repty x' x y x'' x''' mk R P x'''') (@lem29476 Absty Repty x' x y x'' x''' mk R P x'''' h1)). Qed.
Lemma lem29927 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem29936 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term139 Repty r R x) = (term139 Repty r R x).
Proof. exact (eq_refl (term139 Repty r R x)). Qed.
Lemma lem29937 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term141 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem29936 Repty r R x)). Qed.
Lemma lem29938 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem29939 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term142 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem29938 Repty) (@lem29937 Repty r R)). Qed.
Lemma lem29940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem29941 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term145 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem29940) (@lem29939 Repty r R)). Qed.
Lemma lem29942 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term147 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem29941 Repty r R) (@lem29927 Absty Repty dest mk r)). Qed.
Lemma lem29943 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term162 Absty Repty R dest mk) = (term162 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem29942 Absty Repty R dest mk r)). Qed.
Lemma lem29944 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem29945 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem29944 Repty) (@lem29943 Absty Repty R dest mk)). Qed.
Lemma lem29968 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term214 Absty Repty R x''''' dest mk r) = (term214 Absty Repty R x''''' dest mk r).
Proof. exact (eq_refl (term214 Absty Repty R x''''' dest mk r)). Qed.
Lemma lem29969 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term216 Absty Repty R x''''' dest mk) = (term216 Absty Repty R x''''' dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem29968 Absty Repty R x''''' dest mk r)). Qed.
Lemma lem29970 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem29971 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term218 Absty Repty R x''''' dest mk) = (term218 Absty Repty R x''''' dest mk).
Proof. exact (MK_COMB (@lem29970 Repty) (@lem29969 Absty Repty R x''''' dest mk)). Qed.
Lemma lem29972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem29973 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term237 Absty Repty R x''''' dest mk) = (term237 Absty Repty R x''''' dest mk).
Proof. exact (MK_COMB (@lem29972) (@lem29971 Absty Repty R x''''' dest mk)). Qed.
Lemma lem29974 {Absty Repty : Type'} (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term239 Absty Repty x''''' R dest mk) = (term239 Absty Repty x''''' R dest mk).
Proof. exact (MK_COMB (@lem29973 Absty Repty R x''''' dest mk) (@lem29945 Absty Repty R dest mk)). Qed.
Lemma lem29975 {Absty Repty : Type'} (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term239 Absty Repty x''''' R dest mk.
Proof. exact (EQ_MP (@lem29974 Absty Repty x''''' R dest mk) (@lem29477 Absty Repty x''''' R dest mk h1)). Qed.
Lemma lem29977 {Absty Repty : Type'} (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term218 Absty Repty R x''''' dest mk.
Proof. exact (proj1 (@lem29975 Absty Repty x''''' R dest mk h1)). Qed.
Lemma lem29980 {Repty : Type'} (R : type1402 Repty) (h1 : term69 Repty R) : term1124 Repty R.
Proof. exact (proj2 (@lem29557 Repty R h1)). Qed.
Lemma lem29982 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1163 Repty x' x R y) : term1163 Repty x' x R y.
Proof. exact (h1). Qed.
Lemma lem29983 {Absty Repty : Type'} (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term994 Absty Repty x'' x''' mk R P x'''') : term994 Absty Repty x'' x''' mk R P x''''.
Proof. exact (h1). Qed.
Lemma lem29984 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1161 Repty x R y x'.
Proof. exact (h1). Qed.
Lemma lem29985 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1152 Repty x R y.
Proof. exact (h1). Qed.
Lemma lem29986 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1159 Repty x R y x'.
Proof. exact (proj2 (@lem29984 Repty x R y x' h1)). Qed.
Lemma lem29988 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1154 Repty x R y x'.
Proof. exact (proj2 (@lem29986 Repty x R y x' h1)). Qed.
Lemma lem29989 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1156 Repty x R y x'.
Proof. exact (proj1 (@lem29986 Repty x R y x' h1)). Qed.
Lemma lem29996 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1150 Repty x R y.
Proof. exact (proj2 (@lem29985 Repty x R y h1)). Qed.
Lemma lem29999 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1148 Repty x R y.
Proof. exact (proj1 (@lem29996 Repty x R y h1)). Qed.
Lemma lem30000 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term853 Absty Repty x'' mk R x''' P) : term853 Absty Repty x'' mk R x''' P.
Proof. exact (h1). Qed.
Lemma lem30001 {Absty Repty : Type'} (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term926 Absty Repty x''' mk R P x'''') : term926 Absty Repty x''' mk R P x''''.
Proof. exact (h1). Qed.
Lemma lem30002 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term785 Absty Repty mk R P x''.
Proof. exact (h1). Qed.
Lemma lem30003 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term803 Absty Repty mk R x''' P.
Proof. exact (h1). Qed.
Lemma lem30005 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term411 Absty Repty P mk R.
Proof. exact (proj1 (@lem30002 Absty Repty mk R P x'' h1)). Qed.
Lemma lem30006 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term410 Absty P.
Proof. exact (proj2 (@lem30003 Absty Repty mk R x''' P h1)). Qed.
Lemma lem30008 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term872 Absty Repty mk R x''' P.
Proof. exact (h1). Qed.
Lemma lem30009 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term920 Absty Repty mk R P x''''.
Proof. exact (h1). Qed.
Lemma lem30010 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term134 Absty P.
Proof. exact (proj2 (@lem30008 Absty Repty mk R x''' P h1)). Qed.
Lemma lem30013 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term556 Absty Repty P mk R.
Proof. exact (proj1 (@lem30009 Absty Repty mk R P x'''' h1)). Qed.
Lemma lem30179 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') : term1117 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem30183 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem30204 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term1136 Repty y R x z) = (term1136 Repty y R x z).
Proof. exact (eq_refl (term1136 Repty y R x z)). Qed.
Lemma lem30205 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term1137 Repty y R x) = (term1137 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem30204 Repty y R x z)). Qed.
Lemma lem30206 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30207 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term1138 Repty y R x) = (term1138 Repty y R x).
Proof. exact (MK_COMB (@lem30206 Repty) (@lem30205 Repty y R x)). Qed.
Lemma lem30208 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1139 Repty R x) = (term1139 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem30207 Repty y R x)). Qed.
Lemma lem30209 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30210 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1140 Repty R x) = (term1140 Repty R x).
Proof. exact (MK_COMB (@lem30209 Repty) (@lem30208 Repty R x)). Qed.
Lemma lem30211 {Repty : Type'} (R : type1402 Repty) : (term1141 Repty R) = (term1141 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem30210 Repty R x)). Qed.
Lemma lem30212 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30214 {Repty : Type'} (R : type1402 Repty) : (term1142 Repty R) = (term1142 Repty R).
Proof. exact (MK_COMB (@lem30212 Repty) (@lem30211 Repty R)). Qed.
Lemma lem30215 {Repty : Type'} (R : type1402 Repty) (h1 : term71 Repty R) : term1142 Repty R.
Proof. exact (EQ_MP (@lem30214 Repty R) (@lem29607 Repty R h1)). Qed.
Lemma lem30349 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') : term1117 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem30353 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem30374 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term1136 Repty y R x z) = (term1136 Repty y R x z).
Proof. exact (eq_refl (term1136 Repty y R x z)). Qed.
Lemma lem30375 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term1137 Repty y R x) = (term1137 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem30374 Repty y R x z)). Qed.
Lemma lem30376 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30377 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term1138 Repty y R x) = (term1138 Repty y R x).
Proof. exact (MK_COMB (@lem30376 Repty) (@lem30375 Repty y R x)). Qed.
Lemma lem30378 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1139 Repty R x) = (term1139 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem30377 Repty y R x)). Qed.
Lemma lem30379 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30380 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1140 Repty R x) = (term1140 Repty R x).
Proof. exact (MK_COMB (@lem30379 Repty) (@lem30378 Repty R x)). Qed.
Lemma lem30381 {Repty : Type'} (R : type1402 Repty) : (term1141 Repty R) = (term1141 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem30380 Repty R x)). Qed.
Lemma lem30382 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30384 {Repty : Type'} (R : type1402 Repty) : (term1142 Repty R) = (term1142 Repty R).
Proof. exact (MK_COMB (@lem30382 Repty) (@lem30381 Repty R)). Qed.
Lemma lem30385 {Repty : Type'} (R : type1402 Repty) (h1 : term71 Repty R) : term1142 Repty R.
Proof. exact (EQ_MP (@lem30384 Repty R) (@lem29607 Repty R h1)). Qed.
Lemma lem30503 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term1120 Repty R y x) = (term1120 Repty R y x).
Proof. exact (eq_refl (term1120 Repty R y x)). Qed.
Lemma lem30504 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1121 Repty R x) = (term1121 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem30503 Repty R y x)). Qed.
Lemma lem30505 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30506 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1122 Repty R x) = (term1122 Repty R x).
Proof. exact (MK_COMB (@lem30505 Repty) (@lem30504 Repty R x)). Qed.
Lemma lem30507 {Repty : Type'} (R : type1402 Repty) : (term1123 Repty R) = (term1123 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem30506 Repty R x)). Qed.
Lemma lem30508 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30510 {Repty : Type'} (R : type1402 Repty) : (term1124 Repty R) = (term1124 Repty R).
Proof. exact (MK_COMB (@lem30508 Repty) (@lem30507 Repty R)). Qed.
Lemma lem30511 {Repty : Type'} (R : type1402 Repty) (h1 : term69 Repty R) : term1124 Repty R.
Proof. exact (EQ_MP (@lem30510 Repty R) (@lem29980 Repty R h1)). Qed.
Lemma lem30519 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') : term1117 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem30523 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem30689 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') : term1117 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem30693 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem30695 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1112 Repty R x) = (term1112 Repty R x).
Proof. exact (eq_refl (term1112 Repty R x)). Qed.
Lemma lem30696 {Repty : Type'} (R : type1402 Repty) : (term1113 Repty R) = (term1113 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem30695 Repty R x)). Qed.
Lemma lem30697 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30699 {Repty : Type'} (R : type1402 Repty) : (term1114 Repty R) = (term1114 Repty R).
Proof. exact (MK_COMB (@lem30697 Repty) (@lem30696 Repty R)). Qed.
Lemma lem30700 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term1114 Repty R.
Proof. exact (EQ_MP (@lem30699 Repty R) (@lem29491 Repty R h1)). Qed.
Lemma lem30863 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1146 Repty x R y x') = (term1146 Repty x R y x').
Proof. exact (eq_refl (term1146 Repty x R y x')). Qed.
Lemma lem30864 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1147 Repty x R y) = (term1147 Repty x R y).
Proof. exact (fun_ext (fun x' : Repty => @lem30863 Repty x R y x')). Qed.
Lemma lem30865 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem30867 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) : (term1148 Repty x R y) = (term1148 Repty x R y).
Proof. exact (MK_COMB (@lem30865 Repty) (@lem30864 Repty x R y)). Qed.
Lemma lem30868 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1148 Repty x R y.
Proof. exact (EQ_MP (@lem30867 Repty x R y) (@lem29999 Repty x R y h1)). Qed.
Lemma lem30915 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem30916 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem30915 Absty Repty mk dest a)). Qed.
Lemma lem30917 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem30919 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem30917 Absty) (@lem30916 Absty Repty mk dest)). Qed.
Lemma lem30920 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term73 Absty Repty mk dest.
Proof. exact (EQ_MP (@lem30919 Absty Repty mk dest) (@lem29620 Absty Repty mk dest h1)). Qed.
Lemma lem30928 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term214 Absty Repty R x''''' dest mk r) = (term214 Absty Repty R x''''' dest mk r).
Proof. exact (eq_refl (term214 Absty Repty R x''''' dest mk r)). Qed.
Lemma lem30929 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term216 Absty Repty R x''''' dest mk) = (term216 Absty Repty R x''''' dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem30928 Absty Repty R x''''' dest mk r)). Qed.
Lemma lem30930 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem30932 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term218 Absty Repty R x''''' dest mk) = (term218 Absty Repty R x''''' dest mk).
Proof. exact (MK_COMB (@lem30930 Repty) (@lem30929 Absty Repty R x''''' dest mk)). Qed.
Lemma lem30933 {Absty Repty : Type'} (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term218 Absty Repty R x''''' dest mk.
Proof. exact (EQ_MP (@lem30932 Absty Repty R x''''' dest mk) (@lem29977 Absty Repty x''''' R dest mk h1)). Qed.
Lemma lem31041 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term405 Absty Repty P mk R x) = (term405 Absty Repty P mk R x).
Proof. exact (eq_refl (term405 Absty Repty P mk R x)). Qed.
Lemma lem31042 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term406 Absty Repty P mk R) = (term406 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem31041 Absty Repty P mk R x)). Qed.
Lemma lem31043 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem31045 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term411 Absty Repty P mk R) = (term411 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem31043 Repty) (@lem31042 Absty Repty P mk R)). Qed.
Lemma lem31046 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term411 Absty Repty P mk R.
Proof. exact (EQ_MP (@lem31045 Absty Repty P mk R) (@lem30005 Absty Repty mk R P x'' h1)). Qed.
Lemma lem31214 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem31215 {Absty : Type'} (P : Absty -> Prop) : (term403 Absty P) = (term403 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem31214 Absty P x)). Qed.
Lemma lem31216 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem31218 {Absty : Type'} (P : Absty -> Prop) : (term410 Absty P) = (term410 Absty P).
Proof. exact (MK_COMB (@lem31216 Absty) (@lem31215 Absty P)). Qed.
Lemma lem31219 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term410 Absty P.
Proof. exact (EQ_MP (@lem31218 Absty P) (@lem30006 Absty Repty mk R x''' P h1)). Qed.
Lemma lem31383 {Absty : Type'} (P : Absty -> Prop) (x : Absty) : (term530 Absty P x) = (term530 Absty P x).
Proof. exact (eq_refl (term530 Absty P x)). Qed.
Lemma lem31384 {Absty : Type'} (P : Absty -> Prop) : (term532 Absty P) = (term532 Absty P).
Proof. exact (fun_ext (fun x : Absty => @lem31383 Absty P x)). Qed.
Lemma lem31385 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem31387 {Absty : Type'} (P : Absty -> Prop) : (term134 Absty P) = (term134 Absty P).
Proof. exact (MK_COMB (@lem31385 Absty) (@lem31384 Absty P)). Qed.
Lemma lem31388 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term134 Absty P.
Proof. exact (EQ_MP (@lem31387 Absty P) (@lem30010 Absty Repty mk R x''' P h1)). Qed.
Lemma lem31422 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem31423 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem31422 Absty Repty mk dest a)). Qed.
Lemma lem31424 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem31426 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem31424 Absty) (@lem31423 Absty Repty mk dest)). Qed.
Lemma lem31427 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term73 Absty Repty mk dest.
Proof. exact (EQ_MP (@lem31426 Absty Repty mk dest) (@lem29620 Absty Repty mk dest h1)). Qed.
Lemma lem31435 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term214 Absty Repty R x''''' dest mk r) = (term214 Absty Repty R x''''' dest mk r).
Proof. exact (eq_refl (term214 Absty Repty R x''''' dest mk r)). Qed.
Lemma lem31436 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term216 Absty Repty R x''''' dest mk) = (term216 Absty Repty R x''''' dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem31435 Absty Repty R x''''' dest mk r)). Qed.
Lemma lem31437 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem31439 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term218 Absty Repty R x''''' dest mk) = (term218 Absty Repty R x''''' dest mk).
Proof. exact (MK_COMB (@lem31437 Repty) (@lem31436 Absty Repty R x''''' dest mk)). Qed.
Lemma lem31440 {Absty Repty : Type'} (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term218 Absty Repty R x''''' dest mk.
Proof. exact (EQ_MP (@lem31439 Absty Repty R x''''' dest mk) (@lem29977 Absty Repty x''''' R dest mk h1)). Qed.
Lemma lem31548 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term522 Absty Repty P mk R x) = (term522 Absty Repty P mk R x).
Proof. exact (eq_refl (term522 Absty Repty P mk R x)). Qed.
Lemma lem31549 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term524 Absty Repty P mk R) = (term524 Absty Repty P mk R).
Proof. exact (fun_ext (fun x : Repty => @lem31548 Absty Repty P mk R x)). Qed.
Lemma lem31550 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem31552 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term556 Absty Repty P mk R) = (term556 Absty Repty P mk R).
Proof. exact (MK_COMB (@lem31550 Repty) (@lem31549 Absty Repty P mk R)). Qed.
Lemma lem31553 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term556 Absty Repty P mk R.
Proof. exact (EQ_MP (@lem31552 Absty Repty P mk R) (@lem30013 Absty Repty mk R P x'''' h1)). Qed.
Lemma lem31609 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1166 Repty R _763.
Proof. exact (@lem30215 Repty R h1 _763). Qed.
Lemma lem31610 {Repty : Type'} (R : type1402 Repty) (_763 : Repty) : (term1166 Repty R _763) = (term1140 Repty R _763).
Proof. exact (eq_refl (term1166 Repty R _763)). Qed.
Lemma lem31611 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1140 Repty R _763.
Proof. exact (EQ_MP (@lem31610 Repty R _763) (@lem31609 Repty _763 R h1)). Qed.
Lemma lem31612 {Repty : Type'} (_763 : Repty) (_764 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1167 Repty R _763 _764.
Proof. exact (@lem31611 Repty _763 R h1 _764). Qed.
Lemma lem31613 {Repty : Type'} (_764 : Repty) (R : type1402 Repty) (_763 : Repty) : (term1167 Repty R _763 _764) = (term1138 Repty _764 R _763).
Proof. exact (eq_refl (term1167 Repty R _763 _764)). Qed.
Lemma lem31614 {Repty : Type'} (_764 : Repty) (_763 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1138 Repty _764 R _763.
Proof. exact (EQ_MP (@lem31613 Repty _764 R _763) (@lem31612 Repty _763 _764 R h1)). Qed.
Lemma lem31615 {Repty : Type'} (_764 : Repty) (_763 : Repty) (_765 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1168 Repty _764 R _763 _765.
Proof. exact (@lem31614 Repty _764 _763 R h1 _765). Qed.
Lemma lem31616 {Repty : Type'} (_764 : Repty) (R : type1402 Repty) (_763 : Repty) (_765 : Repty) : (term1168 Repty _764 R _763 _765) = (term1136 Repty _764 R _763 _765).
Proof. exact (eq_refl (term1168 Repty _764 R _763 _765)). Qed.
Lemma lem31617 {Repty : Type'} (_764 : Repty) (_763 : Repty) (_765 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1136 Repty _764 R _763 _765.
Proof. exact (EQ_MP (@lem31616 Repty _764 R _763 _765) (@lem31615 Repty _764 _763 _765 R h1)). Qed.
Lemma lem31657 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1166 Repty R _779.
Proof. exact (@lem30385 Repty R h1 _779). Qed.
Lemma lem31658 {Repty : Type'} (R : type1402 Repty) (_779 : Repty) : (term1166 Repty R _779) = (term1140 Repty R _779).
Proof. exact (eq_refl (term1166 Repty R _779)). Qed.
Lemma lem31659 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1140 Repty R _779.
Proof. exact (EQ_MP (@lem31658 Repty R _779) (@lem31657 Repty _779 R h1)). Qed.
Lemma lem31660 {Repty : Type'} (_779 : Repty) (_780 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1167 Repty R _779 _780.
Proof. exact (@lem31659 Repty _779 R h1 _780). Qed.
Lemma lem31661 {Repty : Type'} (_780 : Repty) (R : type1402 Repty) (_779 : Repty) : (term1167 Repty R _779 _780) = (term1138 Repty _780 R _779).
Proof. exact (eq_refl (term1167 Repty R _779 _780)). Qed.
Lemma lem31662 {Repty : Type'} (_780 : Repty) (_779 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1138 Repty _780 R _779.
Proof. exact (EQ_MP (@lem31661 Repty _780 R _779) (@lem31660 Repty _779 _780 R h1)). Qed.
Lemma lem31663 {Repty : Type'} (_780 : Repty) (_779 : Repty) (_781 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1168 Repty _780 R _779 _781.
Proof. exact (@lem31662 Repty _780 _779 R h1 _781). Qed.
Lemma lem31664 {Repty : Type'} (_780 : Repty) (R : type1402 Repty) (_779 : Repty) (_781 : Repty) : (term1168 Repty _780 R _779 _781) = (term1136 Repty _780 R _779 _781).
Proof. exact (eq_refl (term1168 Repty _780 R _779 _781)). Qed.
Lemma lem31665 {Repty : Type'} (_780 : Repty) (_779 : Repty) (_781 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1136 Repty _780 R _779 _781.
Proof. exact (EQ_MP (@lem31664 Repty _780 R _779 _781) (@lem31663 Repty _780 _779 _781 R h1)). Qed.
Lemma lem31696 {Repty : Type'} (_792 : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1169 Repty R _792.
Proof. exact (@lem30511 Repty R h1 _792). Qed.
Lemma lem31697 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) : (term1169 Repty R _792) = (term1122 Repty R _792).
Proof. exact (eq_refl (term1169 Repty R _792)). Qed.
Lemma lem31698 {Repty : Type'} (_792 : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1122 Repty R _792.
Proof. exact (EQ_MP (@lem31697 Repty R _792) (@lem31696 Repty _792 R h1)). Qed.
Lemma lem31699 {Repty : Type'} (_792 : Repty) (_793 : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1170 Repty R _792 _793.
Proof. exact (@lem31698 Repty _792 R h1 _793). Qed.
Lemma lem31700 {Repty : Type'} (R : type1402 Repty) (_793 : Repty) (_792 : Repty) : (term1170 Repty R _792 _793) = (term1120 Repty R _793 _792).
Proof. exact (eq_refl (term1170 Repty R _792 _793)). Qed.
Lemma lem31750 {Repty : Type'} (_810 : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1171 Repty R _810.
Proof. exact (@lem30700 Repty R h1 _810). Qed.
Lemma lem31751 {Repty : Type'} (R : type1402 Repty) (_810 : Repty) : (term1171 Repty R _810) = (term1112 Repty R _810).
Proof. exact (eq_refl (term1171 Repty R _810)). Qed.
Lemma lem31798 {Repty : Type'} (_826 : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1172 Repty x R y _826.
Proof. exact (@lem30868 Repty x R y h1 _826). Qed.
Lemma lem31799 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (_826 : Repty) : (term1172 Repty x R y _826) = (term1146 Repty x R y _826).
Proof. exact (eq_refl (term1172 Repty x R y _826)). Qed.
Lemma lem31816 {Absty Repty : Type'} (_832 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1173 Absty Repty mk dest _832.
Proof. exact (@lem30920 Absty Repty mk dest h1 _832). Qed.
Lemma lem31817 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (_832 : Absty) : (term1173 Absty Repty mk dest _832) = ((term119 Absty Repty mk dest _832) = _832).
Proof. exact (eq_refl (term1173 Absty Repty mk dest _832)). Qed.
Lemma lem31819 {Absty Repty : Type'} (_833 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1174 Absty Repty R x''''' dest mk _833.
Proof. exact (@lem30933 Absty Repty x''''' R dest mk h1 _833). Qed.
Lemma lem31820 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_833 : Repty -> Prop) : (term1174 Absty Repty R x''''' dest mk _833) = (term214 Absty Repty R x''''' dest mk _833).
Proof. exact (eq_refl (term1174 Absty Repty R x''''' dest mk _833)). Qed.
Lemma lem31852 {Absty Repty : Type'} (_844 : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term520 Absty Repty P mk R _844.
Proof. exact (@lem31046 Absty Repty mk R P x'' h1 _844). Qed.
Lemma lem31853 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (_844 : Repty) : (term520 Absty Repty P mk R _844) = (term405 Absty Repty P mk R _844).
Proof. exact (eq_refl (term520 Absty Repty P mk R _844)). Qed.
Lemma lem31903 {Absty Repty : Type'} (_861 : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term528 Absty P _861.
Proof. exact (@lem31219 Absty Repty mk R x''' P h1 _861). Qed.
Lemma lem31904 {Absty : Type'} (P : Absty -> Prop) (_861 : Absty) : (term528 Absty P _861) = (P _861).
Proof. exact (eq_refl (term528 Absty P _861)). Qed.
Lemma lem31954 {Absty Repty : Type'} (_878 : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term779 Absty P _878.
Proof. exact (@lem31388 Absty Repty mk R x''' P h1 _878). Qed.
Lemma lem31955 {Absty : Type'} (P : Absty -> Prop) (_878 : Absty) : (term779 Absty P _878) = (term530 Absty P _878).
Proof. exact (eq_refl (term779 Absty P _878)). Qed.
Lemma lem31969 {Absty Repty : Type'} (_883 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1173 Absty Repty mk dest _883.
Proof. exact (@lem31427 Absty Repty mk dest h1 _883). Qed.
Lemma lem31970 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (_883 : Absty) : (term1173 Absty Repty mk dest _883) = ((term119 Absty Repty mk dest _883) = _883).
Proof. exact (eq_refl (term1173 Absty Repty mk dest _883)). Qed.
Lemma lem31972 {Absty Repty : Type'} (_884 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1174 Absty Repty R x''''' dest mk _884.
Proof. exact (@lem31440 Absty Repty x''''' R dest mk h1 _884). Qed.
Lemma lem31973 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_884 : Repty -> Prop) : (term1174 Absty Repty R x''''' dest mk _884) = (term214 Absty Repty R x''''' dest mk _884).
Proof. exact (eq_refl (term1174 Absty Repty R x''''' dest mk _884)). Qed.
Lemma lem32005 {Absty Repty : Type'} (_895 : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term794 Absty Repty P mk R _895.
Proof. exact (@lem31553 Absty Repty mk R P x'''' h1 _895). Qed.
Lemma lem32006 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (_895 : Repty) : (term794 Absty Repty P mk R _895) = (term522 Absty Repty P mk R _895).
Proof. exact (eq_refl (term794 Absty Repty P mk R _895)). Qed.
Lemma lem32063 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') : term1117 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem32065 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem32078 {Repty : Type'} (_764 : Repty) (R : type1402 Repty) (_763 : Repty) (_765 : Repty) : (term1136 Repty _764 R _763 _765) = (term1175 Repty _764 R _763 _765).
Proof. exact (@lem23486 (term1117 Repty R _763 _764) (term1117 Repty R _764 _765) (term1115 Repty R _763 _765)). Qed.
Lemma lem32079 {Repty : Type'} (_764 : Repty) (_763 : Repty) (_765 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1175 Repty _764 R _763 _765.
Proof. exact (EQ_MP (@lem32078 Repty _764 R _763 _765) (@lem31617 Repty _764 _763 _765 R h1)). Qed.
Lemma lem32121 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') : term1117 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem32123 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem32136 {Repty : Type'} (_780 : Repty) (R : type1402 Repty) (_779 : Repty) (_781 : Repty) : (term1136 Repty _780 R _779 _781) = (term1175 Repty _780 R _779 _781).
Proof. exact (@lem23486 (term1117 Repty R _779 _780) (term1117 Repty R _780 _781) (term1115 Repty R _779 _781)). Qed.
Lemma lem32137 {Repty : Type'} (_780 : Repty) (_779 : Repty) (_781 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1175 Repty _780 R _779 _781.
Proof. exact (EQ_MP (@lem32136 Repty _780 R _779 _781) (@lem31665 Repty _780 _779 _781 R h1)). Qed.
Lemma lem32175 {Repty : Type'} (_793 : Repty) (_792 : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1120 Repty R _793 _792.
Proof. exact (EQ_MP (@lem31700 Repty R _793 _792) (@lem31699 Repty _792 _793 R h1)). Qed.
Lemma lem32179 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') : term1117 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem32181 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem32237 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') : term1117 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem32239 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem32293 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1117 Repty R x y.
Proof. exact (proj1 (@lem29985 Repty x R y h1)). Qed.
Lemma lem32299 {Repty : Type'} (_826 : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1146 Repty x R y _826.
Proof. exact (EQ_MP (@lem31799 Repty x R y _826) (@lem31798 Repty _826 x R y h1)). Qed.
Lemma lem32327 {Absty Repty : Type'} (_833 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term214 Absty Repty R x''''' dest mk _833.
Proof. exact (EQ_MP (@lem31820 Absty Repty R x''''' dest mk _833) (@lem31819 Absty Repty _833 x''''' R dest mk h1)). Qed.
Lemma lem32361 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term530 Absty P x''.
Proof. exact (proj2 (@lem30002 Absty Repty mk R P x'' h1)). Qed.
Lemma lem32415 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term522 Absty Repty P mk R x'''.
Proof. exact (proj1 (@lem30003 Absty Repty mk R x''' P h1)). Qed.
Lemma lem32473 {Absty Repty : Type'} (_878 : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term530 Absty P _878.
Proof. exact (EQ_MP (@lem31955 Absty P _878) (@lem31954 Absty Repty _878 mk R x''' P h1)). Qed.
Lemma lem32495 {Absty Repty : Type'} (_884 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term214 Absty Repty R x''''' dest mk _884.
Proof. exact (EQ_MP (@lem31973 Absty Repty R x''''' dest mk _884) (@lem31972 Absty Repty _884 x''''' R dest mk h1)). Qed.
Lemma lem32527 {Absty Repty : Type'} (_895 : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term522 Absty Repty P mk R _895.
Proof. exact (EQ_MP (@lem32006 Absty Repty P mk R _895) (@lem32005 Absty Repty _895 mk R P x'''' h1)). Qed.
Lemma lem32588 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem32589 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1176 Repty R x x'.
Proof. exact (fun h0 : term1117 Repty R x x' => @lem32588 Repty R x x' h1). Qed.
Lemma lem32591 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32592 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1176 Repty R x x') = (term1115 Repty R x x').
Proof. exact (@lem32591 (term1115 Repty R x x')). Qed.
Lemma lem32593 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (EQ_MP (@lem32592 Repty R x x') (@lem32589 Repty R x x' h1)). Qed.
Lemma lem32596 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem32598 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1117 Repty R x x') = (term1177 Repty R x x').
Proof. exact (@lem32596 (term1115 Repty R x x')). Qed.
Lemma lem32601 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') : term1177 Repty R x x'.
Proof. exact (EQ_MP (@lem32598 Repty R x x') (@lem32063 Repty R x x' h1)). Qed.
Lemma lem32604 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (@lem32601 Repty R x x' h1 (@lem32593 Repty R x x' h2)). Qed.
Lemma lem32605 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : term330.
Proof. exact (fun h0 : ~ False => @lem32604 Repty R x x' h1 h2). Qed.
Lemma lem32607 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32608 : term330 = False.
Proof. exact (@lem32607 False). Qed.
Lemma lem32609 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem32608) (@lem32605 Repty R x x' h1 h2)). Qed.
Lemma lem32668 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1115 Repty R x y.
Proof. exact (proj1 (@lem29984 Repty x R y x' h1)). Qed.
Lemma lem32669 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1176 Repty R x y.
Proof. exact (fun h0 : term1117 Repty R x y => @lem32668 Repty x R y x' h1). Qed.
Lemma lem32671 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32672 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1176 Repty R x y) = (term1115 Repty R x y).
Proof. exact (@lem32671 (term1115 Repty R x y)). Qed.
Lemma lem32673 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1115 Repty R x y.
Proof. exact (EQ_MP (@lem32672 Repty R x y) (@lem32669 Repty x R y x' h1)). Qed.
Lemma lem32675 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem32676 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1176 Repty R y x'.
Proof. exact (fun h0 : term1117 Repty R y x' => @lem32675 Repty R y x' h1). Qed.
Lemma lem32678 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32679 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1176 Repty R y x') = (term1115 Repty R y x').
Proof. exact (@lem32678 (term1115 Repty R y x')). Qed.
Lemma lem32680 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (EQ_MP (@lem32679 Repty R y x') (@lem32676 Repty R y x' h1)). Qed.
Lemma lem32696 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem32697 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1143 Repty _764 R _763 _765) = (term1146 Repty _763 R _764 _765).
Proof. exact (@lem32696 (term1115 Repty R _763 _765) (term1117 Repty R _764 _765)). Qed.
Lemma lem32703 {Repty : Type'} (R : type1402 Repty) (_763 : Repty) (_764 : Repty) : (term1119 Repty R _763 _764) = (term1119 Repty R _763 _764).
Proof. exact (eq_refl (term1119 Repty R _763 _764)). Qed.
Lemma lem32704 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1175 Repty _764 R _763 _765) = (term1178 Repty _763 R _764 _765).
Proof. exact (MK_COMB (@lem32703 Repty R _763 _764) (@lem32697 Repty _763 R _764 _765)). Qed.
Lemma lem32708 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem32709 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1178 Repty _763 R _764 _765) = (term1179 Repty _763 R _764 _765).
Proof. exact (@lem32708 (term1115 Repty R _763 _765) (term1117 Repty R _763 _764) (term1117 Repty R _764 _765)). Qed.
Lemma lem32725 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1175 Repty _764 R _763 _765) = (term1179 Repty _763 R _764 _765).
Proof. exact (TRANS (@lem32704 Repty _763 R _764 _765) (@lem32709 Repty _763 R _764 _765)). Qed.
Lemma lem32726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem32727 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1180 Repty _764 R _763 _765) = (term1181 Repty _763 R _764 _765).
Proof. exact (MK_COMB (@lem32726) (@lem32725 Repty _763 R _764 _765)). Qed.
Lemma lem32743 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1179 Repty _763 R _764 _765) = (term1179 Repty _763 R _764 _765).
Proof. exact (eq_refl (term1179 Repty _763 R _764 _765)). Qed.
Lemma lem32744 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : ((term1175 Repty _764 R _763 _765) = (term1179 Repty _763 R _764 _765)) = ((term1179 Repty _763 R _764 _765) = (term1179 Repty _763 R _764 _765)).
Proof. exact (MK_COMB (@lem32727 Repty _763 R _764 _765) (@lem32743 Repty _763 R _764 _765)). Qed.
Lemma lem32746 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem32747 (x : Prop) : (x = x) = True.
Proof. exact (@lem32746 Prop x). Qed.
Lemma lem32748 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : ((term1179 Repty _763 R _764 _765) = (term1179 Repty _763 R _764 _765)) = True.
Proof. exact (@lem32747 (term1179 Repty _763 R _764 _765)). Qed.
Lemma lem32749 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : ((term1175 Repty _764 R _763 _765) = (term1179 Repty _763 R _764 _765)) = True.
Proof. exact (TRANS (@lem32744 Repty _763 R _764 _765) (@lem32748 Repty _763 R _764 _765)). Qed.
Lemma lem32750 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : True = ((term1175 Repty _764 R _763 _765) = (term1179 Repty _763 R _764 _765)).
Proof. exact (SYM (@lem32749 Repty _763 R _764 _765)). Qed.
Lemma lem32751 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1175 Repty _764 R _763 _765) = (term1179 Repty _763 R _764 _765).
Proof. exact (EQ_MP (@lem32750 Repty _763 R _764 _765) (@lem0)). Qed.
Lemma lem32752 {Repty : Type'} (_763 : Repty) (_764 : Repty) (_765 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1179 Repty _763 R _764 _765.
Proof. exact (EQ_MP (@lem32751 Repty _763 R _764 _765) (@lem32079 Repty _764 _763 _765 R h1)). Qed.
Lemma lem32754 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem32755 {Repty : Type'} (_764 : Repty) (R : type1402 Repty) (_763 : Repty) (_765 : Repty) : (term1179 Repty _763 R _764 _765) = (term1182 Repty _764 R _763 _765).
Proof. exact (@lem32754 (term1134 Repty _763 R _764 _765) (term1115 Repty R _763 _765)). Qed.
Lemma lem32757 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
Lemma lem32758 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1183 Repty _763 R _764 _765) = (term1184 Repty _763 R _764 _765).
Proof. exact (@lem32757 (term1117 Repty R _763 _764) (term1117 Repty R _764 _765)). Qed.
Lemma lem32760 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem32761 {Repty : Type'} (R : type1402 Repty) (_763 : Repty) (_764 : Repty) : (term1185 Repty R _763 _764) = (term1115 Repty R _763 _764).
Proof. exact (@lem32760 (term1115 Repty R _763 _764)). Qed.
Lemma lem32762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem32763 {Repty : Type'} (R : type1402 Repty) (_763 : Repty) (_764 : Repty) : (term1186 Repty R _763 _764) = (term1160 Repty R _763 _764).
Proof. exact (MK_COMB (@lem32762) (@lem32761 Repty R _763 _764)). Qed.
Lemma lem32765 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem32766 {Repty : Type'} (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1185 Repty R _764 _765) = (term1115 Repty R _764 _765).
Proof. exact (@lem32765 (term1115 Repty R _764 _765)). Qed.
Lemma lem32767 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1184 Repty _763 R _764 _765) = (term1187 Repty _763 R _764 _765).
Proof. exact (MK_COMB (@lem32763 Repty R _763 _764) (@lem32766 Repty R _764 _765)). Qed.
Lemma lem32768 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1183 Repty _763 R _764 _765) = (term1187 Repty _763 R _764 _765).
Proof. exact (TRANS (@lem32758 Repty _763 R _764 _765) (@lem32767 Repty _763 R _764 _765)). Qed.
Lemma lem32769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem32770 {Repty : Type'} (_763 : Repty) (R : type1402 Repty) (_764 : Repty) (_765 : Repty) : (term1188 Repty _763 R _764 _765) = (term1189 Repty _763 R _764 _765).
Proof. exact (MK_COMB (@lem32769) (@lem32768 Repty _763 R _764 _765)). Qed.
Lemma lem32771 {Repty : Type'} (R : type1402 Repty) (_763 : Repty) (_765 : Repty) : (term1115 Repty R _763 _765) = (term1115 Repty R _763 _765).
Proof. exact (eq_refl (term1115 Repty R _763 _765)). Qed.
Lemma lem32772 {Repty : Type'} (_764 : Repty) (R : type1402 Repty) (_763 : Repty) (_765 : Repty) : (term1182 Repty _764 R _763 _765) = (term1190 Repty _764 R _763 _765).
Proof. exact (MK_COMB (@lem32770 Repty _763 R _764 _765) (@lem32771 Repty R _763 _765)). Qed.
Lemma lem32773 {Repty : Type'} (_764 : Repty) (R : type1402 Repty) (_763 : Repty) (_765 : Repty) : (term1179 Repty _763 R _764 _765) = (term1190 Repty _764 R _763 _765).
Proof. exact (TRANS (@lem32755 Repty _764 R _763 _765) (@lem32772 Repty _764 R _763 _765)). Qed.
Lemma lem32775 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') (h2 : term1115 Repty R y x') : term1187 Repty x R y x'.
Proof. exact (conj (@lem32673 Repty x R y x' h1) (@lem32680 Repty R y x' h2)). Qed.
Lemma lem32777 {Repty : Type'} (_764 : Repty) (_763 : Repty) (_765 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1190 Repty _764 R _763 _765.
Proof. exact (EQ_MP (@lem32773 Repty _764 R _763 _765) (@lem32752 Repty _763 _764 _765 R h1)). Qed.
Lemma lem32778 {Repty : Type'} (_764 : Repty) (_763 : Repty) (_765 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1190 Repty _764 R _763 _765.
Proof. exact (@lem32777 Repty _764 _763 _765 R h1). Qed.
Lemma lem32779 {Repty : Type'} (y : Repty) (x : Repty) (x' : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1190 Repty y R x x'.
Proof. exact (@lem32778 Repty y x x' R h1). Qed.
Lemma lem32782 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1161 Repty x R y x') (h3 : term1115 Repty R y x') : term1115 Repty R x x'.
Proof. exact (@lem32779 Repty y x x' R h1 (@lem32775 Repty x R y x' h2 h3)). Qed.
Lemma lem32783 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1161 Repty x R y x') (h3 : term1115 Repty R y x') : term1176 Repty R x x'.
Proof. exact (fun h0 : term1117 Repty R x x' => @lem32782 Repty x R y x' h1 h2 h3). Qed.
Lemma lem32785 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32786 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1176 Repty R x x') = (term1115 Repty R x x').
Proof. exact (@lem32785 (term1115 Repty R x x')). Qed.
Lemma lem32787 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1161 Repty x R y x') (h3 : term1115 Repty R y x') : term1115 Repty R x x'.
Proof. exact (EQ_MP (@lem32786 Repty R x x') (@lem32783 Repty x R y x' h1 h2 h3)). Qed.
Lemma lem32790 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem32792 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1117 Repty R x x') = (term1177 Repty R x x').
Proof. exact (@lem32790 (term1115 Repty R x x')). Qed.
Lemma lem32795 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') : term1177 Repty R x x'.
Proof. exact (EQ_MP (@lem32792 Repty R x x') (@lem32121 Repty R x x' h1)). Qed.
Lemma lem32798 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (@lem32795 Repty R x x' h2 (@lem32787 Repty x R y x' h1 h3 h4)). Qed.
Lemma lem32799 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : term330.
Proof. exact (fun h0 : ~ False => @lem32798 Repty x R y x' h1 h2 h3 h4). Qed.
Lemma lem32801 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32802 : term330 = False.
Proof. exact (@lem32801 False). Qed.
Lemma lem32803 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem32802) (@lem32799 Repty x R y x' h1 h2 h3 h4)). Qed.
Lemma lem32862 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1115 Repty R x y.
Proof. exact (proj1 (@lem29984 Repty x R y x' h1)). Qed.
Lemma lem32863 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1176 Repty R x y.
Proof. exact (fun h0 : term1117 Repty R x y => @lem32862 Repty x R y x' h1). Qed.
Lemma lem32865 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32866 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1176 Repty R x y) = (term1115 Repty R x y).
Proof. exact (@lem32865 (term1115 Repty R x y)). Qed.
Lemma lem32867 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1161 Repty x R y x') : term1115 Repty R x y.
Proof. exact (EQ_MP (@lem32866 Repty R x y) (@lem32863 Repty x R y x' h1)). Qed.
Lemma lem32873 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem32874 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : (term1120 Repty R _793 _792) = (term1127 Repty R _792 _793).
Proof. exact (@lem32873 (term1115 Repty R _793 _792) (term1117 Repty R _792 _793)). Qed.
Lemma lem32880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem32881 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : (term1191 Repty R _793 _792) = (term1192 Repty R _792 _793).
Proof. exact (MK_COMB (@lem32880) (@lem32874 Repty R _792 _793)). Qed.
Lemma lem32887 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : (term1127 Repty R _792 _793) = (term1127 Repty R _792 _793).
Proof. exact (eq_refl (term1127 Repty R _792 _793)). Qed.
Lemma lem32888 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : ((term1120 Repty R _793 _792) = (term1127 Repty R _792 _793)) = ((term1127 Repty R _792 _793) = (term1127 Repty R _792 _793)).
Proof. exact (MK_COMB (@lem32881 Repty R _792 _793) (@lem32887 Repty R _792 _793)). Qed.
Lemma lem32890 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem32891 (x : Prop) : (x = x) = True.
Proof. exact (@lem32890 Prop x). Qed.
Lemma lem32892 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : ((term1127 Repty R _792 _793) = (term1127 Repty R _792 _793)) = True.
Proof. exact (@lem32891 (term1127 Repty R _792 _793)). Qed.
Lemma lem32893 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : ((term1120 Repty R _793 _792) = (term1127 Repty R _792 _793)) = True.
Proof. exact (TRANS (@lem32888 Repty R _792 _793) (@lem32892 Repty R _792 _793)). Qed.
Lemma lem32894 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : True = ((term1120 Repty R _793 _792) = (term1127 Repty R _792 _793)).
Proof. exact (SYM (@lem32893 Repty R _792 _793)). Qed.
Lemma lem32895 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : (term1120 Repty R _793 _792) = (term1127 Repty R _792 _793).
Proof. exact (EQ_MP (@lem32894 Repty R _792 _793) (@lem0)). Qed.
Lemma lem32896 {Repty : Type'} (_792 : Repty) (_793 : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1127 Repty R _792 _793.
Proof. exact (EQ_MP (@lem32895 Repty R _792 _793) (@lem32175 Repty _793 _792 R h1)). Qed.
Lemma lem32898 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem32899 {Repty : Type'} (R : type1402 Repty) (_793 : Repty) (_792 : Repty) : (term1127 Repty R _792 _793) = (term1193 Repty R _793 _792).
Proof. exact (@lem32898 (term1117 Repty R _792 _793) (term1115 Repty R _793 _792)). Qed.
Lemma lem32901 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem32902 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : (term1185 Repty R _792 _793) = (term1115 Repty R _792 _793).
Proof. exact (@lem32901 (term1115 Repty R _792 _793)). Qed.
Lemma lem32903 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem32904 {Repty : Type'} (R : type1402 Repty) (_792 : Repty) (_793 : Repty) : (term1194 Repty R _792 _793) = (term1195 Repty R _792 _793).
Proof. exact (MK_COMB (@lem32903) (@lem32902 Repty R _792 _793)). Qed.
Lemma lem32905 {Repty : Type'} (R : type1402 Repty) (_793 : Repty) (_792 : Repty) : (term1115 Repty R _793 _792) = (term1115 Repty R _793 _792).
Proof. exact (eq_refl (term1115 Repty R _793 _792)). Qed.
Lemma lem32906 {Repty : Type'} (R : type1402 Repty) (_793 : Repty) (_792 : Repty) : (term1193 Repty R _793 _792) = (term1196 Repty R _793 _792).
Proof. exact (MK_COMB (@lem32904 Repty R _792 _793) (@lem32905 Repty R _793 _792)). Qed.
Lemma lem32907 {Repty : Type'} (R : type1402 Repty) (_793 : Repty) (_792 : Repty) : (term1127 Repty R _792 _793) = (term1196 Repty R _793 _792).
Proof. exact (TRANS (@lem32899 Repty R _793 _792) (@lem32906 Repty R _793 _792)). Qed.
Lemma lem32910 {Repty : Type'} (_793 : Repty) (_792 : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1196 Repty R _793 _792.
Proof. exact (EQ_MP (@lem32907 Repty R _793 _792) (@lem32896 Repty _792 _793 R h1)). Qed.
Lemma lem32911 {Repty : Type'} (_793 : Repty) (_792 : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1196 Repty R _793 _792.
Proof. exact (@lem32910 Repty _793 _792 R h1). Qed.
Lemma lem32912 {Repty : Type'} (y : Repty) (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1196 Repty R y x.
Proof. exact (@lem32911 Repty y x R h1). Qed.
Lemma lem32915 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term69 Repty R) (h2 : term1161 Repty x R y x') : term1115 Repty R y x.
Proof. exact (@lem32912 Repty y x R h1 (@lem32867 Repty x R y x' h2)). Qed.
Lemma lem32916 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term69 Repty R) (h2 : term1161 Repty x R y x') : term1176 Repty R y x.
Proof. exact (fun h0 : term1117 Repty R y x => @lem32915 Repty x R y x' h1 h2). Qed.
Lemma lem32918 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32919 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term1176 Repty R y x) = (term1115 Repty R y x).
Proof. exact (@lem32918 (term1115 Repty R y x)). Qed.
Lemma lem32920 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term69 Repty R) (h2 : term1161 Repty x R y x') : term1115 Repty R y x.
Proof. exact (EQ_MP (@lem32919 Repty R y x) (@lem32916 Repty x R y x' h1 h2)). Qed.
Lemma lem32922 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (h1). Qed.
Lemma lem32923 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1176 Repty R x x'.
Proof. exact (fun h0 : term1117 Repty R x x' => @lem32922 Repty R x x' h1). Qed.
Lemma lem32925 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem32926 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1176 Repty R x x') = (term1115 Repty R x x').
Proof. exact (@lem32925 (term1115 Repty R x x')). Qed.
Lemma lem32927 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1115 Repty R x x') : term1115 Repty R x x'.
Proof. exact (EQ_MP (@lem32926 Repty R x x') (@lem32923 Repty R x x' h1)). Qed.
Lemma lem32943 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem32944 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1143 Repty _780 R _779 _781) = (term1146 Repty _779 R _780 _781).
Proof. exact (@lem32943 (term1115 Repty R _779 _781) (term1117 Repty R _780 _781)). Qed.
Lemma lem32950 {Repty : Type'} (R : type1402 Repty) (_779 : Repty) (_780 : Repty) : (term1119 Repty R _779 _780) = (term1119 Repty R _779 _780).
Proof. exact (eq_refl (term1119 Repty R _779 _780)). Qed.
Lemma lem32951 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1175 Repty _780 R _779 _781) = (term1178 Repty _779 R _780 _781).
Proof. exact (MK_COMB (@lem32950 Repty R _779 _780) (@lem32944 Repty _779 R _780 _781)). Qed.
Lemma lem32955 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem32956 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1178 Repty _779 R _780 _781) = (term1179 Repty _779 R _780 _781).
Proof. exact (@lem32955 (term1115 Repty R _779 _781) (term1117 Repty R _779 _780) (term1117 Repty R _780 _781)). Qed.
Lemma lem32972 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1175 Repty _780 R _779 _781) = (term1179 Repty _779 R _780 _781).
Proof. exact (TRANS (@lem32951 Repty _779 R _780 _781) (@lem32956 Repty _779 R _780 _781)). Qed.
Lemma lem32973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem32974 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1180 Repty _780 R _779 _781) = (term1181 Repty _779 R _780 _781).
Proof. exact (MK_COMB (@lem32973) (@lem32972 Repty _779 R _780 _781)). Qed.
Lemma lem32990 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1179 Repty _779 R _780 _781) = (term1179 Repty _779 R _780 _781).
Proof. exact (eq_refl (term1179 Repty _779 R _780 _781)). Qed.
Lemma lem32991 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : ((term1175 Repty _780 R _779 _781) = (term1179 Repty _779 R _780 _781)) = ((term1179 Repty _779 R _780 _781) = (term1179 Repty _779 R _780 _781)).
Proof. exact (MK_COMB (@lem32974 Repty _779 R _780 _781) (@lem32990 Repty _779 R _780 _781)). Qed.
Lemma lem32993 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem32994 (x : Prop) : (x = x) = True.
Proof. exact (@lem32993 Prop x). Qed.
Lemma lem32995 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : ((term1179 Repty _779 R _780 _781) = (term1179 Repty _779 R _780 _781)) = True.
Proof. exact (@lem32994 (term1179 Repty _779 R _780 _781)). Qed.
Lemma lem32996 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : ((term1175 Repty _780 R _779 _781) = (term1179 Repty _779 R _780 _781)) = True.
Proof. exact (TRANS (@lem32991 Repty _779 R _780 _781) (@lem32995 Repty _779 R _780 _781)). Qed.
Lemma lem32997 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : True = ((term1175 Repty _780 R _779 _781) = (term1179 Repty _779 R _780 _781)).
Proof. exact (SYM (@lem32996 Repty _779 R _780 _781)). Qed.
Lemma lem32998 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1175 Repty _780 R _779 _781) = (term1179 Repty _779 R _780 _781).
Proof. exact (EQ_MP (@lem32997 Repty _779 R _780 _781) (@lem0)). Qed.
Lemma lem32999 {Repty : Type'} (_779 : Repty) (_780 : Repty) (_781 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1179 Repty _779 R _780 _781.
Proof. exact (EQ_MP (@lem32998 Repty _779 R _780 _781) (@lem32137 Repty _780 _779 _781 R h1)). Qed.
Lemma lem33001 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem33002 {Repty : Type'} (_780 : Repty) (R : type1402 Repty) (_779 : Repty) (_781 : Repty) : (term1179 Repty _779 R _780 _781) = (term1182 Repty _780 R _779 _781).
Proof. exact (@lem33001 (term1134 Repty _779 R _780 _781) (term1115 Repty R _779 _781)). Qed.
Lemma lem33004 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
Lemma lem33005 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1183 Repty _779 R _780 _781) = (term1184 Repty _779 R _780 _781).
Proof. exact (@lem33004 (term1117 Repty R _779 _780) (term1117 Repty R _780 _781)). Qed.
Lemma lem33007 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33008 {Repty : Type'} (R : type1402 Repty) (_779 : Repty) (_780 : Repty) : (term1185 Repty R _779 _780) = (term1115 Repty R _779 _780).
Proof. exact (@lem33007 (term1115 Repty R _779 _780)). Qed.
Lemma lem33009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem33010 {Repty : Type'} (R : type1402 Repty) (_779 : Repty) (_780 : Repty) : (term1186 Repty R _779 _780) = (term1160 Repty R _779 _780).
Proof. exact (MK_COMB (@lem33009) (@lem33008 Repty R _779 _780)). Qed.
Lemma lem33012 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33013 {Repty : Type'} (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1185 Repty R _780 _781) = (term1115 Repty R _780 _781).
Proof. exact (@lem33012 (term1115 Repty R _780 _781)). Qed.
Lemma lem33014 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1184 Repty _779 R _780 _781) = (term1187 Repty _779 R _780 _781).
Proof. exact (MK_COMB (@lem33010 Repty R _779 _780) (@lem33013 Repty R _780 _781)). Qed.
Lemma lem33015 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1183 Repty _779 R _780 _781) = (term1187 Repty _779 R _780 _781).
Proof. exact (TRANS (@lem33005 Repty _779 R _780 _781) (@lem33014 Repty _779 R _780 _781)). Qed.
Lemma lem33016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem33017 {Repty : Type'} (_779 : Repty) (R : type1402 Repty) (_780 : Repty) (_781 : Repty) : (term1188 Repty _779 R _780 _781) = (term1189 Repty _779 R _780 _781).
Proof. exact (MK_COMB (@lem33016) (@lem33015 Repty _779 R _780 _781)). Qed.
Lemma lem33018 {Repty : Type'} (R : type1402 Repty) (_779 : Repty) (_781 : Repty) : (term1115 Repty R _779 _781) = (term1115 Repty R _779 _781).
Proof. exact (eq_refl (term1115 Repty R _779 _781)). Qed.
Lemma lem33019 {Repty : Type'} (_780 : Repty) (R : type1402 Repty) (_779 : Repty) (_781 : Repty) : (term1182 Repty _780 R _779 _781) = (term1190 Repty _780 R _779 _781).
Proof. exact (MK_COMB (@lem33017 Repty _779 R _780 _781) (@lem33018 Repty R _779 _781)). Qed.
Lemma lem33020 {Repty : Type'} (_780 : Repty) (R : type1402 Repty) (_779 : Repty) (_781 : Repty) : (term1179 Repty _779 R _780 _781) = (term1190 Repty _780 R _779 _781).
Proof. exact (TRANS (@lem33002 Repty _780 R _779 _781) (@lem33019 Repty _780 R _779 _781)). Qed.
Lemma lem33022 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term69 Repty R) (h2 : term1161 Repty x R y x') (h3 : term1115 Repty R x x') : term1187 Repty y R x x'.
Proof. exact (conj (@lem32920 Repty x R y x' h1 h2) (@lem32927 Repty R x x' h3)). Qed.
Lemma lem33024 {Repty : Type'} (_780 : Repty) (_779 : Repty) (_781 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1190 Repty _780 R _779 _781.
Proof. exact (EQ_MP (@lem33020 Repty _780 R _779 _781) (@lem32999 Repty _779 _780 _781 R h1)). Qed.
Lemma lem33025 {Repty : Type'} (_780 : Repty) (_779 : Repty) (_781 : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1190 Repty _780 R _779 _781.
Proof. exact (@lem33024 Repty _780 _779 _781 R h1). Qed.
Lemma lem33026 {Repty : Type'} (x : Repty) (y : Repty) (x' : Repty) (R : type1402 Repty) (h1 : term71 Repty R) : term1190 Repty x R y x'.
Proof. exact (@lem33025 Repty x y x' R h1). Qed.
Lemma lem33029 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R x x') : term1115 Repty R y x'.
Proof. exact (@lem33026 Repty x y x' R h1 (@lem33022 Repty y R x x' h2 h3 h4)). Qed.
Lemma lem33030 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R x x') : term1176 Repty R y x'.
Proof. exact (fun h0 : term1117 Repty R y x' => @lem33029 Repty y R x x' h1 h2 h3 h4). Qed.
Lemma lem33032 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33033 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1176 Repty R y x') = (term1115 Repty R y x').
Proof. exact (@lem33032 (term1115 Repty R y x')). Qed.
Lemma lem33034 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R x x') : term1115 Repty R y x'.
Proof. exact (EQ_MP (@lem33033 Repty R y x') (@lem33030 Repty y R x x' h1 h2 h3 h4)). Qed.
Lemma lem33037 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem33039 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1117 Repty R y x') = (term1177 Repty R y x').
Proof. exact (@lem33037 (term1115 Repty R y x')). Qed.
Lemma lem33042 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') : term1177 Repty R y x'.
Proof. exact (EQ_MP (@lem33039 Repty R y x') (@lem32179 Repty R y x' h1)). Qed.
Lemma lem33045 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (@lem33042 Repty R y x' h3 (@lem33034 Repty y R x x' h1 h2 h4 h5)). Qed.
Lemma lem33046 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : term330.
Proof. exact (fun h0 : ~ False => @lem33045 Repty y R x x' h1 h2 h3 h4 h5). Qed.
Lemma lem33048 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33049 : term330 = False.
Proof. exact (@lem33048 False). Qed.
Lemma lem33050 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem33049) (@lem33046 Repty y R x x' h1 h2 h3 h4 h5)). Qed.
Lemma lem33109 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (h1). Qed.
Lemma lem33110 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1176 Repty R y x'.
Proof. exact (fun h0 : term1117 Repty R y x' => @lem33109 Repty R y x' h1). Qed.
Lemma lem33112 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33113 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1176 Repty R y x') = (term1115 Repty R y x').
Proof. exact (@lem33112 (term1115 Repty R y x')). Qed.
Lemma lem33114 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1115 Repty R y x') : term1115 Repty R y x'.
Proof. exact (EQ_MP (@lem33113 Repty R y x') (@lem33110 Repty R y x' h1)). Qed.
Lemma lem33117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem33119 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) : (term1117 Repty R y x') = (term1177 Repty R y x').
Proof. exact (@lem33117 (term1115 Repty R y x')). Qed.
Lemma lem33122 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') : term1177 Repty R y x'.
Proof. exact (EQ_MP (@lem33119 Repty R y x') (@lem32237 Repty R y x' h1)). Qed.
Lemma lem33125 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (@lem33122 Repty R y x' h1 (@lem33114 Repty R y x' h2)). Qed.
Lemma lem33126 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : term330.
Proof. exact (fun h0 : ~ False => @lem33125 Repty R y x' h1 h2). Qed.
Lemma lem33128 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33129 : term330 = False.
Proof. exact (@lem33128 False). Qed.
Lemma lem33130 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem33129) (@lem33126 Repty R y x' h1 h2)). Qed.
Lemma lem33189 {Repty : Type'} (_810 : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R _810.
Proof. exact (EQ_MP (@lem31751 Repty R _810) (@lem31750 Repty _810 R h1)). Qed.
Lemma lem33190 {Repty : Type'} (_810 : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R _810.
Proof. exact (@lem33189 Repty _810 R h1). Qed.
Lemma lem33191 {Repty : Type'} (y : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R y.
Proof. exact (@lem33190 Repty y R h1). Qed.
Lemma lem33192 {Repty : Type'} (y : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1197 Repty R y.
Proof. exact (fun h0 : term1198 Repty R y => @lem33191 Repty y R h1). Qed.
Lemma lem33194 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33195 {Repty : Type'} (R : type1402 Repty) (y : Repty) : (term1197 Repty R y) = (term1112 Repty R y).
Proof. exact (@lem33194 (term1112 Repty R y)). Qed.
Lemma lem33196 {Repty : Type'} (y : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R y.
Proof. exact (EQ_MP (@lem33195 Repty R y) (@lem33192 Repty y R h1)). Qed.
Lemma lem33198 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem33199 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (_826 : Repty) : (term1146 Repty x R y _826) = (term1199 Repty y R x _826).
Proof. exact (@lem33198 (term1117 Repty R y _826) (term1115 Repty R x _826)). Qed.
Lemma lem33201 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33202 {Repty : Type'} (R : type1402 Repty) (y : Repty) (_826 : Repty) : (term1185 Repty R y _826) = (term1115 Repty R y _826).
Proof. exact (@lem33201 (term1115 Repty R y _826)). Qed.
Lemma lem33203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem33204 {Repty : Type'} (R : type1402 Repty) (y : Repty) (_826 : Repty) : (term1194 Repty R y _826) = (term1195 Repty R y _826).
Proof. exact (MK_COMB (@lem33203) (@lem33202 Repty R y _826)). Qed.
Lemma lem33205 {Repty : Type'} (R : type1402 Repty) (x : Repty) (_826 : Repty) : (term1115 Repty R x _826) = (term1115 Repty R x _826).
Proof. exact (eq_refl (term1115 Repty R x _826)). Qed.
Lemma lem33206 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (_826 : Repty) : (term1199 Repty y R x _826) = (term1200 Repty y R x _826).
Proof. exact (MK_COMB (@lem33204 Repty R y _826) (@lem33205 Repty R x _826)). Qed.
Lemma lem33207 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (_826 : Repty) : (term1146 Repty x R y _826) = (term1200 Repty y R x _826).
Proof. exact (TRANS (@lem33199 Repty y R x _826) (@lem33206 Repty y R x _826)). Qed.
Lemma lem33210 {Repty : Type'} (_826 : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1200 Repty y R x _826.
Proof. exact (EQ_MP (@lem33207 Repty y R x _826) (@lem32299 Repty _826 x R y h1)). Qed.
Lemma lem33211 {Repty : Type'} (_826 : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1200 Repty y R x _826.
Proof. exact (@lem33210 Repty _826 x R y h1). Qed.
Lemma lem33212 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1201 Repty R x y.
Proof. exact (@lem33211 Repty y x R y h1). Qed.
Lemma lem33215 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term67 Repty R) (h2 : term1152 Repty x R y) : term1115 Repty R x y.
Proof. exact (@lem33212 Repty x R y h2 (@lem33196 Repty y R h1)). Qed.
Lemma lem33216 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term67 Repty R) (h2 : term1152 Repty x R y) : term1176 Repty R x y.
Proof. exact (fun h0 : term1117 Repty R x y => @lem33215 Repty x R y h1 h2). Qed.
Lemma lem33218 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33219 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1176 Repty R x y) = (term1115 Repty R x y).
Proof. exact (@lem33218 (term1115 Repty R x y)). Qed.
Lemma lem33220 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term67 Repty R) (h2 : term1152 Repty x R y) : term1115 Repty R x y.
Proof. exact (EQ_MP (@lem33219 Repty R x y) (@lem33216 Repty x R y h1 h2)). Qed.
Lemma lem33223 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem33225 {Repty : Type'} (R : type1402 Repty) (x : Repty) (y : Repty) : (term1117 Repty R x y) = (term1177 Repty R x y).
Proof. exact (@lem33223 (term1115 Repty R x y)). Qed.
Lemma lem33228 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term1152 Repty x R y) : term1177 Repty R x y.
Proof. exact (EQ_MP (@lem33225 Repty R x y) (@lem32293 Repty x R y h1)). Qed.
Lemma lem33231 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term67 Repty R) (h2 : term1152 Repty x R y) : False.
Proof. exact (@lem33228 Repty x R y h2 (@lem33220 Repty x R y h1 h2)). Qed.
Lemma lem33232 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term67 Repty R) (h2 : term1152 Repty x R y) : term330.
Proof. exact (fun h0 : ~ False => @lem33231 Repty x R y h1 h2). Qed.
Lemma lem33234 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33235 : term330 = False.
Proof. exact (@lem33234 False). Qed.
Lemma lem33236 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term67 Repty R) (h2 : term1152 Repty x R y) : False.
Proof. exact (EQ_MP (@lem33235) (@lem33232 Repty x R y h1 h2)). Qed.
Lemma lem33237 {Absty : Type'} (P : Absty -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem33238 {Absty : Type'} (_956 : Absty) (_957 : Absty) (h1 : _956 = _957) : _956 = _957.
Proof. exact (h1). Qed.
Lemma lem33239 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) (h1 : _956 = _957) : (P _956) = (P _957).
Proof. exact (MK_COMB (@lem33237 Absty P) (@lem33238 Absty _956 _957 h1)). Qed.
Lemma lem33241 (b : Prop) (a : Prop) : term1202 b a.
Proof. exact (or_elim (@lem21504 a) (fun h0 : a = True => @lem21596 b a h0) (fun h0 : a = False => @lem21595 b a h0)). Qed.
Lemma lem33242 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : term1203 Absty _957 P _956.
Proof. exact (@lem33241 (P _957) (P _956)). Qed.
Lemma lem33243 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) (h1 : _956 = _957) : term1204 Absty _957 P _956.
Proof. exact (@lem33242 Absty _957 P _956 (@lem33239 Absty P _956 _957 h1)). Qed.
Lemma lem33244 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : term1205 Absty _957 P _956.
Proof. exact (fun h0 : _956 = _957 => @lem33243 Absty P _956 _957 h0). Qed.
Lemma lem33246 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem33247 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : (term1205 Absty _957 P _956) = (term1206 Absty _957 P _956).
Proof. exact (@lem33246 (_956 = _957) (term1204 Absty _957 P _956)). Qed.
Lemma lem33248 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : term1206 Absty _957 P _956.
Proof. exact (EQ_MP (@lem33247 Absty _957 P _956) (@lem33244 Absty _957 P _956)). Qed.
Lemma lem33276 {Absty Repty : Type'} (dest : type1413 Absty Repty) : dest = dest.
Proof. exact (eq_refl dest). Qed.
Lemma lem33277 {Absty : Type'} (_964 : Absty) (_965 : Absty) (h1 : _964 = _965) : _964 = _965.
Proof. exact (h1). Qed.
Lemma lem33278 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) (h1 : _964 = _965) : (dest _964) = (dest _965).
Proof. exact (MK_COMB (@lem33276 Absty Repty dest) (@lem33277 Absty _964 _965 h1)). Qed.
Lemma lem33279 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : term269 Absty Repty _964 dest _965.
Proof. exact (fun h0 : _964 = _965 => @lem33278 Absty Repty dest _964 _965 h0). Qed.
Lemma lem33281 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem33282 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : (term269 Absty Repty _964 dest _965) = (term271 Absty Repty _964 dest _965).
Proof. exact (@lem33281 (_964 = _965) ((dest _964) = (dest _965))). Qed.
Lemma lem33283 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : term271 Absty Repty _964 dest _965.
Proof. exact (EQ_MP (@lem33282 Absty Repty _964 dest _965) (@lem33279 Absty Repty _964 dest _965)). Qed.
Lemma lem33284 {Absty Repty : Type'} (mk : type862 Absty Repty) : mk = mk.
Proof. exact (eq_refl mk). Qed.
Lemma lem33285 {Repty : Type'} (_966 : Repty -> Prop) (_967 : Repty -> Prop) (h1 : _966 = _967) : _966 = _967.
Proof. exact (h1). Qed.
Lemma lem33286 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) (h1 : _966 = _967) : (mk _966) = (mk _967).
Proof. exact (MK_COMB (@lem33284 Absty Repty mk) (@lem33285 Repty _966 _967 h1)). Qed.
Lemma lem33287 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : term331 Absty Repty _966 mk _967.
Proof. exact (fun h0 : _966 = _967 => @lem33286 Absty Repty mk _966 _967 h0). Qed.
Lemma lem33289 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem33290 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : (term331 Absty Repty _966 mk _967) = (term332 Absty Repty _966 mk _967).
Proof. exact (@lem33289 (_966 = _967) ((mk _966) = (mk _967))). Qed.
Lemma lem33291 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : term332 Absty Repty _966 mk _967.
Proof. exact (EQ_MP (@lem33290 Absty Repty _966 mk _967) (@lem33287 Absty Repty _966 mk _967)). Qed.
Lemma lem33305 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : term1207 Absty x y z.
Proof. exact (@lem21385 Absty x y z). Qed.
Lemma lem33307 {Absty Repty : Type'} (_832 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _832) = _832.
Proof. exact (EQ_MP (@lem31817 Absty Repty mk dest _832) (@lem31816 Absty Repty _832 mk dest h1)). Qed.
Lemma lem33308 {Absty Repty : Type'} (_832 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _832) = _832.
Proof. exact (@lem33307 Absty Repty _832 mk dest h1). Qed.
Lemma lem33309 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'') = x''.
Proof. exact (@lem33308 Absty Repty x'' mk dest h1). Qed.
Lemma lem33310 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1208 Absty Repty mk dest x''.
Proof. exact (fun h0 : term1209 Absty Repty mk dest x'' => @lem33309 Absty Repty x'' mk dest h1). Qed.
Lemma lem33312 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33313 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'' : Absty) : (term1208 Absty Repty mk dest x'') = ((term119 Absty Repty mk dest x'') = x'').
Proof. exact (@lem33312 ((term119 Absty Repty mk dest x'') = x'')). Qed.
Lemma lem33314 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'') = x''.
Proof. exact (EQ_MP (@lem33313 Absty Repty mk dest x'') (@lem33310 Absty Repty x'' mk dest h1)). Qed.
Lemma lem33320 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem33321 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : (term271 Absty Repty _964 dest _965) = (term275 Absty Repty dest _964 _965).
Proof. exact (@lem33320 ((dest _964) = (dest _965)) (term276 Absty _964 _965)). Qed.
Lemma lem33331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem33332 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : (term277 Absty Repty _964 dest _965) = (term278 Absty Repty dest _964 _965).
Proof. exact (MK_COMB (@lem33331) (@lem33321 Absty Repty dest _964 _965)). Qed.
Lemma lem33342 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : (term275 Absty Repty dest _964 _965) = (term275 Absty Repty dest _964 _965).
Proof. exact (eq_refl (term275 Absty Repty dest _964 _965)). Qed.
Lemma lem33343 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : ((term271 Absty Repty _964 dest _965) = (term275 Absty Repty dest _964 _965)) = ((term275 Absty Repty dest _964 _965) = (term275 Absty Repty dest _964 _965)).
Proof. exact (MK_COMB (@lem33332 Absty Repty dest _964 _965) (@lem33342 Absty Repty dest _964 _965)). Qed.
Lemma lem33345 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem33346 (x : Prop) : (x = x) = True.
Proof. exact (@lem33345 Prop x). Qed.
Lemma lem33347 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : ((term275 Absty Repty dest _964 _965) = (term275 Absty Repty dest _964 _965)) = True.
Proof. exact (@lem33346 (term275 Absty Repty dest _964 _965)). Qed.
Lemma lem33348 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : ((term271 Absty Repty _964 dest _965) = (term275 Absty Repty dest _964 _965)) = True.
Proof. exact (TRANS (@lem33343 Absty Repty dest _964 _965) (@lem33347 Absty Repty dest _964 _965)). Qed.
Lemma lem33349 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : True = ((term271 Absty Repty _964 dest _965) = (term275 Absty Repty dest _964 _965)).
Proof. exact (SYM (@lem33348 Absty Repty dest _964 _965)). Qed.
Lemma lem33350 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : (term271 Absty Repty _964 dest _965) = (term275 Absty Repty dest _964 _965).
Proof. exact (EQ_MP (@lem33349 Absty Repty dest _964 _965) (@lem0)). Qed.
Lemma lem33351 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_964 : Absty) (_965 : Absty) : term275 Absty Repty dest _964 _965.
Proof. exact (EQ_MP (@lem33350 Absty Repty dest _964 _965) (@lem33283 Absty Repty _964 dest _965)). Qed.
Lemma lem33353 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem33354 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : (term275 Absty Repty dest _964 _965) = (term280 Absty Repty _964 dest _965).
Proof. exact (@lem33353 (term276 Absty _964 _965) ((dest _964) = (dest _965))). Qed.
Lemma lem33356 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33357 {Absty : Type'} (_964 : Absty) (_965 : Absty) : (term281 Absty _964 _965) = (_964 = _965).
Proof. exact (@lem33356 (_964 = _965)). Qed.
Lemma lem33358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem33359 {Absty : Type'} (_964 : Absty) (_965 : Absty) : (term282 Absty _964 _965) = (term283 Absty _964 _965).
Proof. exact (MK_COMB (@lem33358) (@lem33357 Absty _964 _965)). Qed.
Lemma lem33360 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : ((dest _964) = (dest _965)) = ((dest _964) = (dest _965)).
Proof. exact (eq_refl ((dest _964) = (dest _965))). Qed.
Lemma lem33361 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : (term280 Absty Repty _964 dest _965) = (term269 Absty Repty _964 dest _965).
Proof. exact (MK_COMB (@lem33359 Absty _964 _965) (@lem33360 Absty Repty _964 dest _965)). Qed.
Lemma lem33362 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : (term275 Absty Repty dest _964 _965) = (term269 Absty Repty _964 dest _965).
Proof. exact (TRANS (@lem33354 Absty Repty _964 dest _965) (@lem33361 Absty Repty _964 dest _965)). Qed.
Lemma lem33365 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : term269 Absty Repty _964 dest _965.
Proof. exact (EQ_MP (@lem33362 Absty Repty _964 dest _965) (@lem33351 Absty Repty dest _964 _965)). Qed.
Lemma lem33366 {Absty Repty : Type'} (_964 : Absty) (dest : type1413 Absty Repty) (_965 : Absty) : term269 Absty Repty _964 dest _965.
Proof. exact (@lem33365 Absty Repty _964 dest _965). Qed.
Lemma lem33367 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'' : Absty) : term1210 Absty Repty mk dest x''.
Proof. exact (@lem33366 Absty Repty (term119 Absty Repty mk dest x'') dest x''). Qed.
Lemma lem33370 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term1211 Absty Repty mk dest x'') = (dest x'').
Proof. exact (@lem33367 Absty Repty mk dest x'' (@lem33314 Absty Repty x'' mk dest h1)). Qed.
Lemma lem33371 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term1211 Absty Repty mk dest x'') = (dest x'').
Proof. exact (@lem33370 Absty Repty x'' mk dest h1). Qed.
Lemma lem33372 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1212 Absty Repty mk dest x''.
Proof. exact (fun h0 : term1213 Absty Repty mk dest x'' => @lem33371 Absty Repty x'' mk dest h1). Qed.
Lemma lem33374 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33375 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'' : Absty) : (term1212 Absty Repty mk dest x'') = ((term1211 Absty Repty mk dest x'') = (dest x'')).
Proof. exact (@lem33374 ((term1211 Absty Repty mk dest x'') = (dest x''))). Qed.
Lemma lem33376 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term1211 Absty Repty mk dest x'') = (dest x'').
Proof. exact (EQ_MP (@lem33375 Absty Repty mk dest x'') (@lem33372 Absty Repty x'' mk dest h1)). Qed.
Lemma lem33378 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem33379 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (_833 : Repty -> Prop) : (term214 Absty Repty R x''''' dest mk _833) = (term1214 Absty Repty dest mk R x''''' _833).
Proof. exact (@lem33378 (term143 Absty Repty dest mk _833) (_833 = (term1215 Repty R x''''' _833))). Qed.
Lemma lem33381 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33382 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_833 : Repty -> Prop) : (term1216 Absty Repty dest mk _833) = ((term114 Absty Repty dest mk _833) = _833).
Proof. exact (@lem33381 ((term114 Absty Repty dest mk _833) = _833)). Qed.
Lemma lem33383 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem33384 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_833 : Repty -> Prop) : (term1217 Absty Repty dest mk _833) = (term1218 Absty Repty dest mk _833).
Proof. exact (MK_COMB (@lem33383) (@lem33382 Absty Repty dest mk _833)). Qed.
Lemma lem33385 {Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (_833 : Repty -> Prop) : (_833 = (term1215 Repty R x''''' _833)) = (_833 = (term1215 Repty R x''''' _833)).
Proof. exact (eq_refl (_833 = (term1215 Repty R x''''' _833))). Qed.
Lemma lem33386 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (_833 : Repty -> Prop) : (term1214 Absty Repty dest mk R x''''' _833) = (term1219 Absty Repty dest mk R x''''' _833).
Proof. exact (MK_COMB (@lem33384 Absty Repty dest mk _833) (@lem33385 Repty R x''''' _833)). Qed.
Lemma lem33387 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (_833 : Repty -> Prop) : (term214 Absty Repty R x''''' dest mk _833) = (term1219 Absty Repty dest mk R x''''' _833).
Proof. exact (TRANS (@lem33379 Absty Repty dest mk R x''''' _833) (@lem33386 Absty Repty dest mk R x''''' _833)). Qed.
Lemma lem33390 {Absty Repty : Type'} (_833 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1219 Absty Repty dest mk R x''''' _833.
Proof. exact (EQ_MP (@lem33387 Absty Repty dest mk R x''''' _833) (@lem32327 Absty Repty _833 x''''' R dest mk h1)). Qed.
Lemma lem33391 {Absty Repty : Type'} (_833 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1219 Absty Repty dest mk R x''''' _833.
Proof. exact (@lem33390 Absty Repty _833 x''''' R dest mk h1). Qed.
Lemma lem33392 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1220 Absty Repty mk R x''''' dest x''.
Proof. exact (@lem33391 Absty Repty (dest x'') x''''' R dest mk h1). Qed.
Lemma lem33395 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (dest x'') = (term1221 Absty Repty R x''''' dest x'').
Proof. exact (@lem33392 Absty Repty x'' x''''' R dest mk h2 (@lem33376 Absty Repty x'' mk dest h1)). Qed.
Lemma lem33396 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (dest x'') = (term1221 Absty Repty R x''''' dest x'').
Proof. exact (@lem33395 Absty Repty x'' x''''' R dest mk h1 h2). Qed.
Lemma lem33397 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1222 Absty Repty R x''''' dest x''.
Proof. exact (fun h0 : term1223 Absty Repty R x''''' dest x'' => @lem33396 Absty Repty x'' x''''' R dest mk h1 h2). Qed.
Lemma lem33399 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33400 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) : (term1222 Absty Repty R x''''' dest x'') = ((dest x'') = (term1221 Absty Repty R x''''' dest x'')).
Proof. exact (@lem33399 ((dest x'') = (term1221 Absty Repty R x''''' dest x''))). Qed.
Lemma lem33401 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (dest x'') = (term1221 Absty Repty R x''''' dest x'').
Proof. exact (EQ_MP (@lem33400 Absty Repty R x''''' dest x'') (@lem33397 Absty Repty x'' x''''' R dest mk h1 h2)). Qed.
Lemma lem33407 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem33408 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : (term332 Absty Repty _966 mk _967) = (term333 Absty Repty mk _966 _967).
Proof. exact (@lem33407 ((mk _966) = (mk _967)) (term303 Repty _966 _967)). Qed.
Lemma lem33418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem33419 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : (term334 Absty Repty _966 mk _967) = (term335 Absty Repty mk _966 _967).
Proof. exact (MK_COMB (@lem33418) (@lem33408 Absty Repty mk _966 _967)). Qed.
Lemma lem33429 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : (term333 Absty Repty mk _966 _967) = (term333 Absty Repty mk _966 _967).
Proof. exact (eq_refl (term333 Absty Repty mk _966 _967)). Qed.
Lemma lem33430 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : ((term332 Absty Repty _966 mk _967) = (term333 Absty Repty mk _966 _967)) = ((term333 Absty Repty mk _966 _967) = (term333 Absty Repty mk _966 _967)).
Proof. exact (MK_COMB (@lem33419 Absty Repty mk _966 _967) (@lem33429 Absty Repty mk _966 _967)). Qed.
Lemma lem33432 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem33433 (x : Prop) : (x = x) = True.
Proof. exact (@lem33432 Prop x). Qed.
Lemma lem33434 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : ((term333 Absty Repty mk _966 _967) = (term333 Absty Repty mk _966 _967)) = True.
Proof. exact (@lem33433 (term333 Absty Repty mk _966 _967)). Qed.
Lemma lem33435 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : ((term332 Absty Repty _966 mk _967) = (term333 Absty Repty mk _966 _967)) = True.
Proof. exact (TRANS (@lem33430 Absty Repty mk _966 _967) (@lem33434 Absty Repty mk _966 _967)). Qed.
Lemma lem33436 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : True = ((term332 Absty Repty _966 mk _967) = (term333 Absty Repty mk _966 _967)).
Proof. exact (SYM (@lem33435 Absty Repty mk _966 _967)). Qed.
Lemma lem33437 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : (term332 Absty Repty _966 mk _967) = (term333 Absty Repty mk _966 _967).
Proof. exact (EQ_MP (@lem33436 Absty Repty mk _966 _967) (@lem0)). Qed.
Lemma lem33438 {Absty Repty : Type'} (mk : type862 Absty Repty) (_966 : Repty -> Prop) (_967 : Repty -> Prop) : term333 Absty Repty mk _966 _967.
Proof. exact (EQ_MP (@lem33437 Absty Repty mk _966 _967) (@lem33291 Absty Repty _966 mk _967)). Qed.
Lemma lem33440 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem33441 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : (term333 Absty Repty mk _966 _967) = (term336 Absty Repty _966 mk _967).
Proof. exact (@lem33440 (term303 Repty _966 _967) ((mk _966) = (mk _967))). Qed.
Lemma lem33443 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33444 {Repty : Type'} (_966 : Repty -> Prop) (_967 : Repty -> Prop) : (term315 Repty _966 _967) = (_966 = _967).
Proof. exact (@lem33443 (_966 = _967)). Qed.
Lemma lem33445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem33446 {Repty : Type'} (_966 : Repty -> Prop) (_967 : Repty -> Prop) : (term337 Repty _966 _967) = (term338 Repty _966 _967).
Proof. exact (MK_COMB (@lem33445) (@lem33444 Repty _966 _967)). Qed.
Lemma lem33447 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : ((mk _966) = (mk _967)) = ((mk _966) = (mk _967)).
Proof. exact (eq_refl ((mk _966) = (mk _967))). Qed.
Lemma lem33448 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : (term336 Absty Repty _966 mk _967) = (term331 Absty Repty _966 mk _967).
Proof. exact (MK_COMB (@lem33446 Repty _966 _967) (@lem33447 Absty Repty _966 mk _967)). Qed.
Lemma lem33449 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : (term333 Absty Repty mk _966 _967) = (term331 Absty Repty _966 mk _967).
Proof. exact (TRANS (@lem33441 Absty Repty _966 mk _967) (@lem33448 Absty Repty _966 mk _967)). Qed.
Lemma lem33452 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : term331 Absty Repty _966 mk _967.
Proof. exact (EQ_MP (@lem33449 Absty Repty _966 mk _967) (@lem33438 Absty Repty mk _966 _967)). Qed.
Lemma lem33453 {Absty Repty : Type'} (_966 : Repty -> Prop) (mk : type862 Absty Repty) (_967 : Repty -> Prop) : term331 Absty Repty _966 mk _967.
Proof. exact (@lem33452 Absty Repty _966 mk _967). Qed.
Lemma lem33454 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) : term1224 Absty Repty mk R x''''' dest x''.
Proof. exact (@lem33453 Absty Repty (dest x'') mk (term1221 Absty Repty R x''''' dest x'')). Qed.
Lemma lem33457 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term119 Absty Repty mk dest x'') = (term1225 Absty Repty mk R x''''' dest x'').
Proof. exact (@lem33454 Absty Repty mk R x''''' dest x'' (@lem33401 Absty Repty x'' x''''' R dest mk h1 h2)). Qed.
Lemma lem33458 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term119 Absty Repty mk dest x'') = (term1225 Absty Repty mk R x''''' dest x'').
Proof. exact (@lem33457 Absty Repty x'' x''''' R dest mk h1 h2). Qed.
Lemma lem33459 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1226 Absty Repty mk R x''''' dest x''.
Proof. exact (fun h0 : term1227 Absty Repty mk R x''''' dest x'' => @lem33458 Absty Repty x'' x''''' R dest mk h1 h2). Qed.
Lemma lem33461 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33462 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) : (term1226 Absty Repty mk R x''''' dest x'') = ((term119 Absty Repty mk dest x'') = (term1225 Absty Repty mk R x''''' dest x'')).
Proof. exact (@lem33461 ((term119 Absty Repty mk dest x'') = (term1225 Absty Repty mk R x''''' dest x''))). Qed.
Lemma lem33463 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term119 Absty Repty mk dest x'') = (term1225 Absty Repty mk R x''''' dest x'').
Proof. exact (EQ_MP (@lem33462 Absty Repty mk R x''''' dest x'') (@lem33459 Absty Repty x'' x''''' R dest mk h1 h2)). Qed.
Lemma lem33465 {Absty Repty : Type'} (_832 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _832) = _832.
Proof. exact (EQ_MP (@lem31817 Absty Repty mk dest _832) (@lem31816 Absty Repty _832 mk dest h1)). Qed.
Lemma lem33466 {Absty Repty : Type'} (_832 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _832) = _832.
Proof. exact (@lem33465 Absty Repty _832 mk dest h1). Qed.
Lemma lem33467 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'') = x''.
Proof. exact (@lem33466 Absty Repty x'' mk dest h1). Qed.
Lemma lem33468 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1208 Absty Repty mk dest x''.
Proof. exact (fun h0 : term1209 Absty Repty mk dest x'' => @lem33467 Absty Repty x'' mk dest h1). Qed.
Lemma lem33470 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33471 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'' : Absty) : (term1208 Absty Repty mk dest x'') = ((term119 Absty Repty mk dest x'') = x'').
Proof. exact (@lem33470 ((term119 Absty Repty mk dest x'') = x'')). Qed.
Lemma lem33472 {Absty Repty : Type'} (x'' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'') = x''.
Proof. exact (EQ_MP (@lem33471 Absty Repty mk dest x'') (@lem33468 Absty Repty x'' mk dest h1)). Qed.
Lemma lem33490 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem33491 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1228 Absty x y z) = (term1229 Absty y x z).
Proof. exact (@lem33490 (y = z) (term276 Absty x z)). Qed.
Lemma lem33501 {Absty : Type'} (x : Absty) (y : Absty) : (term1230 Absty x y) = (term1230 Absty x y).
Proof. exact (eq_refl (term1230 Absty x y)). Qed.
Lemma lem33502 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1207 Absty x y z) = (term1231 Absty y x z).
Proof. exact (MK_COMB (@lem33501 Absty x y) (@lem33491 Absty y x z)). Qed.
Lemma lem33506 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem33507 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1231 Absty y x z) = (term1232 Absty y x z).
Proof. exact (@lem33506 (y = z) (term276 Absty x y) (term276 Absty x z)). Qed.
Lemma lem33529 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1207 Absty x y z) = (term1232 Absty y x z).
Proof. exact (TRANS (@lem33502 Absty y x z) (@lem33507 Absty y x z)). Qed.
Lemma lem33530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem33531 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1233 Absty x y z) = (term1234 Absty y x z).
Proof. exact (MK_COMB (@lem33530) (@lem33529 Absty y x z)). Qed.
Lemma lem33553 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1232 Absty y x z) = (term1232 Absty y x z).
Proof. exact (eq_refl (term1232 Absty y x z)). Qed.
Lemma lem33554 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : ((term1207 Absty x y z) = (term1232 Absty y x z)) = ((term1232 Absty y x z) = (term1232 Absty y x z)).
Proof. exact (MK_COMB (@lem33531 Absty y x z) (@lem33553 Absty y x z)). Qed.
Lemma lem33556 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem33557 (x : Prop) : (x = x) = True.
Proof. exact (@lem33556 Prop x). Qed.
Lemma lem33558 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : ((term1232 Absty y x z) = (term1232 Absty y x z)) = True.
Proof. exact (@lem33557 (term1232 Absty y x z)). Qed.
Lemma lem33559 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : ((term1207 Absty x y z) = (term1232 Absty y x z)) = True.
Proof. exact (TRANS (@lem33554 Absty y x z) (@lem33558 Absty y x z)). Qed.
Lemma lem33560 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : True = ((term1207 Absty x y z) = (term1232 Absty y x z)).
Proof. exact (SYM (@lem33559 Absty y x z)). Qed.
Lemma lem33561 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1207 Absty x y z) = (term1232 Absty y x z).
Proof. exact (EQ_MP (@lem33560 Absty y x z) (@lem0)). Qed.
Lemma lem33562 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : term1232 Absty y x z.
Proof. exact (EQ_MP (@lem33561 Absty y x z) (@lem33305 Absty x y z)). Qed.
Lemma lem33564 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem33565 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : (term1232 Absty y x z) = (term1235 Absty x y z).
Proof. exact (@lem33564 (term1236 Absty y x z) (y = z)). Qed.
Lemma lem33567 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
Lemma lem33568 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1237 Absty y x z) = (term1238 Absty y x z).
Proof. exact (@lem33567 (term276 Absty x y) (term276 Absty x z)). Qed.
Lemma lem33570 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33571 {Absty : Type'} (x : Absty) (y : Absty) : (term281 Absty x y) = (x = y).
Proof. exact (@lem33570 (x = y)). Qed.
Lemma lem33572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem33573 {Absty : Type'} (x : Absty) (y : Absty) : (term1239 Absty x y) = (term1240 Absty x y).
Proof. exact (MK_COMB (@lem33572) (@lem33571 Absty x y)). Qed.
Lemma lem33575 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33576 {Absty : Type'} (x : Absty) (z : Absty) : (term281 Absty x z) = (x = z).
Proof. exact (@lem33575 (x = z)). Qed.
Lemma lem33577 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1238 Absty y x z) = (term1241 Absty y x z).
Proof. exact (MK_COMB (@lem33573 Absty x y) (@lem33576 Absty x z)). Qed.
Lemma lem33578 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1237 Absty y x z) = (term1241 Absty y x z).
Proof. exact (TRANS (@lem33568 Absty y x z) (@lem33577 Absty y x z)). Qed.
Lemma lem33579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem33580 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1242 Absty y x z) = (term1243 Absty y x z).
Proof. exact (MK_COMB (@lem33579) (@lem33578 Absty y x z)). Qed.
Lemma lem33581 {Absty : Type'} (y : Absty) (z : Absty) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem33582 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : (term1235 Absty x y z) = (term1244 Absty x y z).
Proof. exact (MK_COMB (@lem33580 Absty y x z) (@lem33581 Absty y z)). Qed.
Lemma lem33583 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : (term1232 Absty y x z) = (term1244 Absty x y z).
Proof. exact (TRANS (@lem33565 Absty x y z) (@lem33582 Absty x y z)). Qed.
Lemma lem33585 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1245 Absty Repty R x''''' mk dest x''.
Proof. exact (conj (@lem33463 Absty Repty x'' x''''' R dest mk h1 h2) (@lem33472 Absty Repty x'' mk dest h1)). Qed.
Lemma lem33587 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : term1244 Absty x y z.
Proof. exact (EQ_MP (@lem33583 Absty x y z) (@lem33562 Absty y x z)). Qed.
Lemma lem33588 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : term1244 Absty x y z.
Proof. exact (@lem33587 Absty x y z). Qed.
Lemma lem33589 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) : term1246 Absty Repty mk R x''''' dest x''.
Proof. exact (@lem33588 Absty (term119 Absty Repty mk dest x'') (term1225 Absty Repty mk R x''''' dest x'') x''). Qed.
Lemma lem33592 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term1225 Absty Repty mk R x''''' dest x'') = x''.
Proof. exact (@lem33589 Absty Repty mk R x''''' dest x'' (@lem33585 Absty Repty x'' x''''' R dest mk h1 h2)). Qed.
Lemma lem33593 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term1225 Absty Repty mk R x''''' dest x'') = x''.
Proof. exact (@lem33592 Absty Repty x'' x''''' R dest mk h1 h2). Qed.
Lemma lem33594 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1247 Absty Repty mk R x''''' dest x''.
Proof. exact (fun h0 : term1248 Absty Repty mk R x''''' dest x'' => @lem33593 Absty Repty x'' x''''' R dest mk h1 h2). Qed.
Lemma lem33596 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33597 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) : (term1247 Absty Repty mk R x''''' dest x'') = ((term1225 Absty Repty mk R x''''' dest x'') = x'').
Proof. exact (@lem33596 ((term1225 Absty Repty mk R x''''' dest x'') = x'')). Qed.
Lemma lem33598 {Absty Repty : Type'} (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term1225 Absty Repty mk R x''''' dest x'') = x''.
Proof. exact (EQ_MP (@lem33597 Absty Repty mk R x''''' dest x'') (@lem33594 Absty Repty x'' x''''' R dest mk h1 h2)). Qed.
Lemma lem33600 {Absty Repty : Type'} (_844 : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term405 Absty Repty P mk R _844.
Proof. exact (EQ_MP (@lem31853 Absty Repty P mk R _844) (@lem31852 Absty Repty _844 mk R P x'' h1)). Qed.
Lemma lem33601 {Absty Repty : Type'} (_844 : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term405 Absty Repty P mk R _844.
Proof. exact (@lem33600 Absty Repty _844 mk R P x'' h1). Qed.
Lemma lem33602 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term1249 Absty Repty P mk R x''''' dest x''.
Proof. exact (@lem33601 Absty Repty (term1250 Absty Repty x''''' dest x'') mk R P x'' h1). Qed.
Lemma lem33603 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term1251 Absty Repty P mk R x''''' dest x''.
Proof. exact (fun h0 : term1252 Absty Repty P mk R x''''' dest x'' => @lem33602 Absty Repty x''''' dest mk R P x'' h1). Qed.
Lemma lem33605 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33606 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) : (term1251 Absty Repty P mk R x''''' dest x'') = (term1249 Absty Repty P mk R x''''' dest x'').
Proof. exact (@lem33605 (term1249 Absty Repty P mk R x''''' dest x'')). Qed.
Lemma lem33607 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term1249 Absty Repty P mk R x''''' dest x''.
Proof. exact (EQ_MP (@lem33606 Absty Repty P mk R x''''' dest x'') (@lem33603 Absty Repty x''''' dest mk R P x'' h1)). Qed.
Lemma lem33613 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem33614 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : (term1206 Absty _957 P _956) = (term1253 Absty _957 P _956).
Proof. exact (@lem33613 (P _957) (term276 Absty _956 _957) (term530 Absty P _956)). Qed.
Lemma lem33628 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem33629 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : (term1254 Absty _957 P _956) = (term1255 Absty P _956 _957).
Proof. exact (@lem33628 (term530 Absty P _956) (term276 Absty _956 _957)). Qed.
Lemma lem33637 {Absty : Type'} (P : Absty -> Prop) (_957 : Absty) : (term1256 Absty P _957) = (term1256 Absty P _957).
Proof. exact (eq_refl (term1256 Absty P _957)). Qed.
Lemma lem33638 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : (term1253 Absty _957 P _956) = (term1257 Absty P _956 _957).
Proof. exact (MK_COMB (@lem33637 Absty P _957) (@lem33629 Absty P _956 _957)). Qed.
Lemma lem33649 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : (term1206 Absty _957 P _956) = (term1257 Absty P _956 _957).
Proof. exact (TRANS (@lem33614 Absty _957 P _956) (@lem33638 Absty P _956 _957)). Qed.
Lemma lem33650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem33651 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : (term1258 Absty _957 P _956) = (term1259 Absty P _956 _957).
Proof. exact (MK_COMB (@lem33650) (@lem33649 Absty P _956 _957)). Qed.
Lemma lem33665 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem33666 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : (term1254 Absty _957 P _956) = (term1255 Absty P _956 _957).
Proof. exact (@lem33665 (term530 Absty P _956) (term276 Absty _956 _957)). Qed.
Lemma lem33674 {Absty : Type'} (P : Absty -> Prop) (_957 : Absty) : (term1256 Absty P _957) = (term1256 Absty P _957).
Proof. exact (eq_refl (term1256 Absty P _957)). Qed.
Lemma lem33675 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : (term1253 Absty _957 P _956) = (term1257 Absty P _956 _957).
Proof. exact (MK_COMB (@lem33674 Absty P _957) (@lem33666 Absty P _956 _957)). Qed.
Lemma lem33686 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : ((term1206 Absty _957 P _956) = (term1253 Absty _957 P _956)) = ((term1257 Absty P _956 _957) = (term1257 Absty P _956 _957)).
Proof. exact (MK_COMB (@lem33651 Absty P _956 _957) (@lem33675 Absty P _956 _957)). Qed.
Lemma lem33688 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem33689 (x : Prop) : (x = x) = True.
Proof. exact (@lem33688 Prop x). Qed.
Lemma lem33690 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) (_957 : Absty) : ((term1257 Absty P _956 _957) = (term1257 Absty P _956 _957)) = True.
Proof. exact (@lem33689 (term1257 Absty P _956 _957)). Qed.
Lemma lem33691 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : ((term1206 Absty _957 P _956) = (term1253 Absty _957 P _956)) = True.
Proof. exact (TRANS (@lem33686 Absty P _956 _957) (@lem33690 Absty P _956 _957)). Qed.
Lemma lem33692 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : True = ((term1206 Absty _957 P _956) = (term1253 Absty _957 P _956)).
Proof. exact (SYM (@lem33691 Absty _957 P _956)). Qed.
Lemma lem33693 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : (term1206 Absty _957 P _956) = (term1253 Absty _957 P _956).
Proof. exact (EQ_MP (@lem33692 Absty _957 P _956) (@lem0)). Qed.
Lemma lem33694 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : term1253 Absty _957 P _956.
Proof. exact (EQ_MP (@lem33693 Absty _957 P _956) (@lem33248 Absty _957 P _956)). Qed.
Lemma lem33696 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem33697 {Absty : Type'} (_956 : Absty) (P : Absty -> Prop) (_957 : Absty) : (term1253 Absty _957 P _956) = (term1260 Absty _956 P _957).
Proof. exact (@lem33696 (term1254 Absty _957 P _956) (P _957)). Qed.
Lemma lem33699 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
Lemma lem33700 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : (term1261 Absty _957 P _956) = (term1262 Absty _957 P _956).
Proof. exact (@lem33699 (term276 Absty _956 _957) (term530 Absty P _956)). Qed.
Lemma lem33702 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33703 {Absty : Type'} (_956 : Absty) (_957 : Absty) : (term281 Absty _956 _957) = (_956 = _957).
Proof. exact (@lem33702 (_956 = _957)). Qed.
Lemma lem33704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem33705 {Absty : Type'} (_956 : Absty) (_957 : Absty) : (term1239 Absty _956 _957) = (term1240 Absty _956 _957).
Proof. exact (MK_COMB (@lem33704) (@lem33703 Absty _956 _957)). Qed.
Lemma lem33707 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem33708 {Absty : Type'} (P : Absty -> Prop) (_956 : Absty) : (term1263 Absty P _956) = (P _956).
Proof. exact (@lem33707 (P _956)). Qed.
Lemma lem33709 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : (term1262 Absty _957 P _956) = (term1264 Absty _957 P _956).
Proof. exact (MK_COMB (@lem33705 Absty _956 _957) (@lem33708 Absty P _956)). Qed.
Lemma lem33710 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : (term1261 Absty _957 P _956) = (term1264 Absty _957 P _956).
Proof. exact (TRANS (@lem33700 Absty _957 P _956) (@lem33709 Absty _957 P _956)). Qed.
Lemma lem33711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem33712 {Absty : Type'} (_957 : Absty) (P : Absty -> Prop) (_956 : Absty) : (term1265 Absty _957 P _956) = (term1266 Absty _957 P _956).
Proof. exact (MK_COMB (@lem33711) (@lem33710 Absty _957 P _956)). Qed.
Lemma lem33713 {Absty : Type'} (P : Absty -> Prop) (_957 : Absty) : (P _957) = (P _957).
Proof. exact (eq_refl (P _957)). Qed.
Lemma lem33714 {Absty : Type'} (_956 : Absty) (P : Absty -> Prop) (_957 : Absty) : (term1260 Absty _956 P _957) = (term1267 Absty _956 P _957).
Proof. exact (MK_COMB (@lem33712 Absty _957 P _956) (@lem33713 Absty P _957)). Qed.
Lemma lem33715 {Absty : Type'} (_956 : Absty) (P : Absty -> Prop) (_957 : Absty) : (term1253 Absty _957 P _956) = (term1267 Absty _956 P _957).
Proof. exact (TRANS (@lem33697 Absty _956 P _957) (@lem33714 Absty _956 P _957)). Qed.
Lemma lem33717 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : term1268 Absty Repty P mk R x''''' dest x''.
Proof. exact (conj (@lem33598 Absty Repty x'' x''''' R dest mk h1 h3) (@lem33607 Absty Repty x''''' dest mk R P x'' h2)). Qed.
Lemma lem33719 {Absty : Type'} (_956 : Absty) (P : Absty -> Prop) (_957 : Absty) : term1267 Absty _956 P _957.
Proof. exact (EQ_MP (@lem33715 Absty _956 P _957) (@lem33694 Absty _957 P _956)). Qed.
Lemma lem33720 {Absty : Type'} (_956 : Absty) (P : Absty -> Prop) (_957 : Absty) : term1267 Absty _956 P _957.
Proof. exact (@lem33719 Absty _956 P _957). Qed.
Lemma lem33721 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (P : Absty -> Prop) (x'' : Absty) : term1269 Absty Repty mk R x''''' dest P x''.
Proof. exact (@lem33720 Absty (term1225 Absty Repty mk R x''''' dest x'') P x''). Qed.
Lemma lem33724 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : P x''.
Proof. exact (@lem33721 Absty Repty mk R x''''' dest P x'' (@lem33717 Absty Repty P x'' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem33725 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : term1270 Absty P x''.
Proof. exact (fun h0 : term530 Absty P x'' => @lem33724 Absty Repty P x'' x''''' R dest mk h1 h2 h3). Qed.
Lemma lem33727 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33728 {Absty : Type'} (P : Absty -> Prop) (x'' : Absty) : (term1270 Absty P x'') = (P x'').
Proof. exact (@lem33727 (P x'')). Qed.
Lemma lem33729 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : P x''.
Proof. exact (EQ_MP (@lem33728 Absty P x'') (@lem33725 Absty Repty P x'' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem33732 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem33734 {Absty : Type'} (P : Absty -> Prop) (x'' : Absty) : (term530 Absty P x'') = (term1271 Absty P x'').
Proof. exact (@lem33732 (P x'')). Qed.
Lemma lem33737 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'' : Absty) (h1 : term785 Absty Repty mk R P x'') : term1271 Absty P x''.
Proof. exact (EQ_MP (@lem33734 Absty P x'') (@lem32361 Absty Repty mk R P x'' h1)). Qed.
Lemma lem33740 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : False.
Proof. exact (@lem33737 Absty Repty mk R P x'' h2 (@lem33729 Absty Repty P x'' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem33741 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : term330.
Proof. exact (fun h0 : ~ False => @lem33740 Absty Repty P x'' x''''' R dest mk h1 h2 h3). Qed.
Lemma lem33743 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33744 : term330 = False.
Proof. exact (@lem33743 False). Qed.
Lemma lem33745 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : False.
Proof. exact (EQ_MP (@lem33744) (@lem33741 Absty Repty P x'' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem33816 {Absty Repty : Type'} (_861 : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : P _861.
Proof. exact (EQ_MP (@lem31904 Absty P _861) (@lem31903 Absty Repty _861 mk R x''' P h1)). Qed.
Lemma lem33817 {Absty Repty : Type'} (_861 : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : P _861.
Proof. exact (@lem33816 Absty Repty _861 mk R x''' P h1). Qed.
Lemma lem33818 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term405 Absty Repty P mk R x'''.
Proof. exact (@lem33817 Absty Repty (term110 Absty Repty mk R x''') mk R x''' P h1). Qed.
Lemma lem33819 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term1272 Absty Repty P mk R x'''.
Proof. exact (fun h0 : term522 Absty Repty P mk R x''' => @lem33818 Absty Repty mk R x''' P h1). Qed.
Lemma lem33821 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33822 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) : (term1272 Absty Repty P mk R x''') = (term405 Absty Repty P mk R x''').
Proof. exact (@lem33821 (term405 Absty Repty P mk R x''')). Qed.
Lemma lem33823 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term405 Absty Repty P mk R x'''.
Proof. exact (EQ_MP (@lem33822 Absty Repty P mk R x''') (@lem33819 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33826 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem33828 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) : (term522 Absty Repty P mk R x''') = (term1273 Absty Repty P mk R x''').
Proof. exact (@lem33826 (term405 Absty Repty P mk R x''')). Qed.
Lemma lem33831 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term1273 Absty Repty P mk R x'''.
Proof. exact (EQ_MP (@lem33828 Absty Repty P mk R x''') (@lem32415 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33834 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : False.
Proof. exact (@lem33831 Absty Repty mk R x''' P h1 (@lem33823 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33835 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : term330.
Proof. exact (fun h0 : ~ False => @lem33834 Absty Repty mk R x''' P h1). Qed.
Lemma lem33837 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33838 : term330 = False.
Proof. exact (@lem33837 False). Qed.
Lemma lem33839 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term803 Absty Repty mk R x''' P) : False.
Proof. exact (EQ_MP (@lem33838) (@lem33835 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33910 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term405 Absty Repty P mk R x'''.
Proof. exact (proj1 (@lem30008 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33911 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term1272 Absty Repty P mk R x'''.
Proof. exact (fun h0 : term522 Absty Repty P mk R x''' => @lem33910 Absty Repty mk R x''' P h1). Qed.
Lemma lem33913 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33914 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) : (term1272 Absty Repty P mk R x''') = (term405 Absty Repty P mk R x''').
Proof. exact (@lem33913 (term405 Absty Repty P mk R x''')). Qed.
Lemma lem33915 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term405 Absty Repty P mk R x'''.
Proof. exact (EQ_MP (@lem33914 Absty Repty P mk R x''') (@lem33911 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33918 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem33920 {Absty : Type'} (P : Absty -> Prop) (_878 : Absty) : (term530 Absty P _878) = (term1271 Absty P _878).
Proof. exact (@lem33918 (P _878)). Qed.
Lemma lem33923 {Absty Repty : Type'} (_878 : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term1271 Absty P _878.
Proof. exact (EQ_MP (@lem33920 Absty P _878) (@lem32473 Absty Repty _878 mk R x''' P h1)). Qed.
Lemma lem33924 {Absty Repty : Type'} (_878 : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term1271 Absty P _878.
Proof. exact (@lem33923 Absty Repty _878 mk R x''' P h1). Qed.
Lemma lem33925 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term1273 Absty Repty P mk R x'''.
Proof. exact (@lem33924 Absty Repty (term110 Absty Repty mk R x''') mk R x''' P h1). Qed.
Lemma lem33928 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : False.
Proof. exact (@lem33925 Absty Repty mk R x''' P h1 (@lem33915 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33929 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : term330.
Proof. exact (fun h0 : ~ False => @lem33928 Absty Repty mk R x''' P h1). Qed.
Lemma lem33931 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem33932 : term330 = False.
Proof. exact (@lem33931 False). Qed.
Lemma lem33933 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term872 Absty Repty mk R x''' P) : False.
Proof. exact (EQ_MP (@lem33932) (@lem33929 Absty Repty mk R x''' P h1)). Qed.
Lemma lem33934 {Absty : Type'} (P : Absty -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem33935 {Absty : Type'} (_998 : Absty) (_999 : Absty) (h1 : _998 = _999) : _998 = _999.
Proof. exact (h1). Qed.
Lemma lem33936 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) (h1 : _998 = _999) : (P _998) = (P _999).
Proof. exact (MK_COMB (@lem33934 Absty P) (@lem33935 Absty _998 _999 h1)). Qed.
Lemma lem33938 (b : Prop) (a : Prop) : term1202 b a.
Proof. exact (or_elim (@lem21504 a) (fun h0 : a = True => @lem21596 b a h0) (fun h0 : a = False => @lem21595 b a h0)). Qed.
Lemma lem33939 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : term1203 Absty _999 P _998.
Proof. exact (@lem33938 (P _999) (P _998)). Qed.
Lemma lem33940 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) (h1 : _998 = _999) : term1204 Absty _999 P _998.
Proof. exact (@lem33939 Absty _999 P _998 (@lem33936 Absty P _998 _999 h1)). Qed.
Lemma lem33941 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : term1205 Absty _999 P _998.
Proof. exact (fun h0 : _998 = _999 => @lem33940 Absty P _998 _999 h0). Qed.
Lemma lem33943 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem33944 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : (term1205 Absty _999 P _998) = (term1206 Absty _999 P _998).
Proof. exact (@lem33943 (_998 = _999) (term1204 Absty _999 P _998)). Qed.
Lemma lem33945 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : term1206 Absty _999 P _998.
Proof. exact (EQ_MP (@lem33944 Absty _999 P _998) (@lem33941 Absty _999 P _998)). Qed.
Lemma lem33973 {Absty Repty : Type'} (dest : type1413 Absty Repty) : dest = dest.
Proof. exact (eq_refl dest). Qed.
Lemma lem33974 {Absty : Type'} (_1006 : Absty) (_1007 : Absty) (h1 : _1006 = _1007) : _1006 = _1007.
Proof. exact (h1). Qed.
Lemma lem33975 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) (h1 : _1006 = _1007) : (dest _1006) = (dest _1007).
Proof. exact (MK_COMB (@lem33973 Absty Repty dest) (@lem33974 Absty _1006 _1007 h1)). Qed.
Lemma lem33976 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : term269 Absty Repty _1006 dest _1007.
Proof. exact (fun h0 : _1006 = _1007 => @lem33975 Absty Repty dest _1006 _1007 h0). Qed.
Lemma lem33978 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem33979 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : (term269 Absty Repty _1006 dest _1007) = (term271 Absty Repty _1006 dest _1007).
Proof. exact (@lem33978 (_1006 = _1007) ((dest _1006) = (dest _1007))). Qed.
Lemma lem33980 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : term271 Absty Repty _1006 dest _1007.
Proof. exact (EQ_MP (@lem33979 Absty Repty _1006 dest _1007) (@lem33976 Absty Repty _1006 dest _1007)). Qed.
Lemma lem33981 {Absty Repty : Type'} (mk : type862 Absty Repty) : mk = mk.
Proof. exact (eq_refl mk). Qed.
Lemma lem33982 {Repty : Type'} (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) (h1 : _1008 = _1009) : _1008 = _1009.
Proof. exact (h1). Qed.
Lemma lem33983 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) (h1 : _1008 = _1009) : (mk _1008) = (mk _1009).
Proof. exact (MK_COMB (@lem33981 Absty Repty mk) (@lem33982 Repty _1008 _1009 h1)). Qed.
Lemma lem33984 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : term331 Absty Repty _1008 mk _1009.
Proof. exact (fun h0 : _1008 = _1009 => @lem33983 Absty Repty mk _1008 _1009 h0). Qed.
Lemma lem33986 (a : Prop) (b : Prop) : (a -> b) = (term270 a b).
Proof. exact (or_elim (@lem21397 a) (fun h0 : a = True => @lem21488 b a h0) (fun h0 : a = False => @lem21487 b a h0)). Qed.
Lemma lem33987 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : (term331 Absty Repty _1008 mk _1009) = (term332 Absty Repty _1008 mk _1009).
Proof. exact (@lem33986 (_1008 = _1009) ((mk _1008) = (mk _1009))). Qed.
Lemma lem33988 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : term332 Absty Repty _1008 mk _1009.
Proof. exact (EQ_MP (@lem33987 Absty Repty _1008 mk _1009) (@lem33984 Absty Repty _1008 mk _1009)). Qed.
Lemma lem34002 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : term1207 Absty x y z.
Proof. exact (@lem21385 Absty x y z). Qed.
Lemma lem34004 {Absty Repty : Type'} (_883 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _883) = _883.
Proof. exact (EQ_MP (@lem31970 Absty Repty mk dest _883) (@lem31969 Absty Repty _883 mk dest h1)). Qed.
Lemma lem34005 {Absty Repty : Type'} (_883 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _883) = _883.
Proof. exact (@lem34004 Absty Repty _883 mk dest h1). Qed.
Lemma lem34006 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'''') = x''''.
Proof. exact (@lem34005 Absty Repty x'''' mk dest h1). Qed.
Lemma lem34007 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1208 Absty Repty mk dest x''''.
Proof. exact (fun h0 : term1209 Absty Repty mk dest x'''' => @lem34006 Absty Repty x'''' mk dest h1). Qed.
Lemma lem34009 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34010 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : (term1208 Absty Repty mk dest x'''') = ((term119 Absty Repty mk dest x'''') = x'''').
Proof. exact (@lem34009 ((term119 Absty Repty mk dest x'''') = x'''')). Qed.
Lemma lem34011 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'''') = x''''.
Proof. exact (EQ_MP (@lem34010 Absty Repty mk dest x'''') (@lem34007 Absty Repty x'''' mk dest h1)). Qed.
Lemma lem34013 {Absty Repty : Type'} (_883 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _883) = _883.
Proof. exact (EQ_MP (@lem31970 Absty Repty mk dest _883) (@lem31969 Absty Repty _883 mk dest h1)). Qed.
Lemma lem34014 {Absty Repty : Type'} (_883 : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest _883) = _883.
Proof. exact (@lem34013 Absty Repty _883 mk dest h1). Qed.
Lemma lem34015 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'''') = x''''.
Proof. exact (@lem34014 Absty Repty x'''' mk dest h1). Qed.
Lemma lem34016 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1208 Absty Repty mk dest x''''.
Proof. exact (fun h0 : term1209 Absty Repty mk dest x'''' => @lem34015 Absty Repty x'''' mk dest h1). Qed.
Lemma lem34018 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34019 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : (term1208 Absty Repty mk dest x'''') = ((term119 Absty Repty mk dest x'''') = x'''').
Proof. exact (@lem34018 ((term119 Absty Repty mk dest x'''') = x'''')). Qed.
Lemma lem34020 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term119 Absty Repty mk dest x'''') = x''''.
Proof. exact (EQ_MP (@lem34019 Absty Repty mk dest x'''') (@lem34016 Absty Repty x'''' mk dest h1)). Qed.
Lemma lem34026 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem34027 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : (term271 Absty Repty _1006 dest _1007) = (term275 Absty Repty dest _1006 _1007).
Proof. exact (@lem34026 ((dest _1006) = (dest _1007)) (term276 Absty _1006 _1007)). Qed.
Lemma lem34037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem34038 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : (term277 Absty Repty _1006 dest _1007) = (term278 Absty Repty dest _1006 _1007).
Proof. exact (MK_COMB (@lem34037) (@lem34027 Absty Repty dest _1006 _1007)). Qed.
Lemma lem34048 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : (term275 Absty Repty dest _1006 _1007) = (term275 Absty Repty dest _1006 _1007).
Proof. exact (eq_refl (term275 Absty Repty dest _1006 _1007)). Qed.
Lemma lem34049 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : ((term271 Absty Repty _1006 dest _1007) = (term275 Absty Repty dest _1006 _1007)) = ((term275 Absty Repty dest _1006 _1007) = (term275 Absty Repty dest _1006 _1007)).
Proof. exact (MK_COMB (@lem34038 Absty Repty dest _1006 _1007) (@lem34048 Absty Repty dest _1006 _1007)). Qed.
Lemma lem34051 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem34052 (x : Prop) : (x = x) = True.
Proof. exact (@lem34051 Prop x). Qed.
Lemma lem34053 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : ((term275 Absty Repty dest _1006 _1007) = (term275 Absty Repty dest _1006 _1007)) = True.
Proof. exact (@lem34052 (term275 Absty Repty dest _1006 _1007)). Qed.
Lemma lem34054 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : ((term271 Absty Repty _1006 dest _1007) = (term275 Absty Repty dest _1006 _1007)) = True.
Proof. exact (TRANS (@lem34049 Absty Repty dest _1006 _1007) (@lem34053 Absty Repty dest _1006 _1007)). Qed.
Lemma lem34055 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : True = ((term271 Absty Repty _1006 dest _1007) = (term275 Absty Repty dest _1006 _1007)).
Proof. exact (SYM (@lem34054 Absty Repty dest _1006 _1007)). Qed.
Lemma lem34056 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : (term271 Absty Repty _1006 dest _1007) = (term275 Absty Repty dest _1006 _1007).
Proof. exact (EQ_MP (@lem34055 Absty Repty dest _1006 _1007) (@lem0)). Qed.
Lemma lem34057 {Absty Repty : Type'} (dest : type1413 Absty Repty) (_1006 : Absty) (_1007 : Absty) : term275 Absty Repty dest _1006 _1007.
Proof. exact (EQ_MP (@lem34056 Absty Repty dest _1006 _1007) (@lem33980 Absty Repty _1006 dest _1007)). Qed.
Lemma lem34059 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem34060 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : (term275 Absty Repty dest _1006 _1007) = (term280 Absty Repty _1006 dest _1007).
Proof. exact (@lem34059 (term276 Absty _1006 _1007) ((dest _1006) = (dest _1007))). Qed.
Lemma lem34062 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem34063 {Absty : Type'} (_1006 : Absty) (_1007 : Absty) : (term281 Absty _1006 _1007) = (_1006 = _1007).
Proof. exact (@lem34062 (_1006 = _1007)). Qed.
Lemma lem34064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34065 {Absty : Type'} (_1006 : Absty) (_1007 : Absty) : (term282 Absty _1006 _1007) = (term283 Absty _1006 _1007).
Proof. exact (MK_COMB (@lem34064) (@lem34063 Absty _1006 _1007)). Qed.
Lemma lem34066 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : ((dest _1006) = (dest _1007)) = ((dest _1006) = (dest _1007)).
Proof. exact (eq_refl ((dest _1006) = (dest _1007))). Qed.
Lemma lem34067 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : (term280 Absty Repty _1006 dest _1007) = (term269 Absty Repty _1006 dest _1007).
Proof. exact (MK_COMB (@lem34065 Absty _1006 _1007) (@lem34066 Absty Repty _1006 dest _1007)). Qed.
Lemma lem34068 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : (term275 Absty Repty dest _1006 _1007) = (term269 Absty Repty _1006 dest _1007).
Proof. exact (TRANS (@lem34060 Absty Repty _1006 dest _1007) (@lem34067 Absty Repty _1006 dest _1007)). Qed.
Lemma lem34071 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : term269 Absty Repty _1006 dest _1007.
Proof. exact (EQ_MP (@lem34068 Absty Repty _1006 dest _1007) (@lem34057 Absty Repty dest _1006 _1007)). Qed.
Lemma lem34072 {Absty Repty : Type'} (_1006 : Absty) (dest : type1413 Absty Repty) (_1007 : Absty) : term269 Absty Repty _1006 dest _1007.
Proof. exact (@lem34071 Absty Repty _1006 dest _1007). Qed.
Lemma lem34073 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : term1210 Absty Repty mk dest x''''.
Proof. exact (@lem34072 Absty Repty (term119 Absty Repty mk dest x'''') dest x''''). Qed.
Lemma lem34076 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term1211 Absty Repty mk dest x'''') = (dest x'''').
Proof. exact (@lem34073 Absty Repty mk dest x'''' (@lem34020 Absty Repty x'''' mk dest h1)). Qed.
Lemma lem34077 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term1211 Absty Repty mk dest x'''') = (dest x'''').
Proof. exact (@lem34076 Absty Repty x'''' mk dest h1). Qed.
Lemma lem34078 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : term1212 Absty Repty mk dest x''''.
Proof. exact (fun h0 : term1213 Absty Repty mk dest x'''' => @lem34077 Absty Repty x'''' mk dest h1). Qed.
Lemma lem34080 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34081 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : (term1212 Absty Repty mk dest x'''') = ((term1211 Absty Repty mk dest x'''') = (dest x'''')).
Proof. exact (@lem34080 ((term1211 Absty Repty mk dest x'''') = (dest x''''))). Qed.
Lemma lem34082 {Absty Repty : Type'} (x'''' : Absty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (h1 : term73 Absty Repty mk dest) : (term1211 Absty Repty mk dest x'''') = (dest x'''').
Proof. exact (EQ_MP (@lem34081 Absty Repty mk dest x'''') (@lem34078 Absty Repty x'''' mk dest h1)). Qed.
Lemma lem34084 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem34085 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (_884 : Repty -> Prop) : (term214 Absty Repty R x''''' dest mk _884) = (term1214 Absty Repty dest mk R x''''' _884).
Proof. exact (@lem34084 (term143 Absty Repty dest mk _884) (_884 = (term1215 Repty R x''''' _884))). Qed.
Lemma lem34087 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem34088 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_884 : Repty -> Prop) : (term1216 Absty Repty dest mk _884) = ((term114 Absty Repty dest mk _884) = _884).
Proof. exact (@lem34087 ((term114 Absty Repty dest mk _884) = _884)). Qed.
Lemma lem34089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34090 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_884 : Repty -> Prop) : (term1217 Absty Repty dest mk _884) = (term1218 Absty Repty dest mk _884).
Proof. exact (MK_COMB (@lem34089) (@lem34088 Absty Repty dest mk _884)). Qed.
Lemma lem34091 {Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (_884 : Repty -> Prop) : (_884 = (term1215 Repty R x''''' _884)) = (_884 = (term1215 Repty R x''''' _884)).
Proof. exact (eq_refl (_884 = (term1215 Repty R x''''' _884))). Qed.
Lemma lem34092 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (_884 : Repty -> Prop) : (term1214 Absty Repty dest mk R x''''' _884) = (term1219 Absty Repty dest mk R x''''' _884).
Proof. exact (MK_COMB (@lem34090 Absty Repty dest mk _884) (@lem34091 Repty R x''''' _884)). Qed.
Lemma lem34093 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (_884 : Repty -> Prop) : (term214 Absty Repty R x''''' dest mk _884) = (term1219 Absty Repty dest mk R x''''' _884).
Proof. exact (TRANS (@lem34085 Absty Repty dest mk R x''''' _884) (@lem34092 Absty Repty dest mk R x''''' _884)). Qed.
Lemma lem34096 {Absty Repty : Type'} (_884 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1219 Absty Repty dest mk R x''''' _884.
Proof. exact (EQ_MP (@lem34093 Absty Repty dest mk R x''''' _884) (@lem32495 Absty Repty _884 x''''' R dest mk h1)). Qed.
Lemma lem34097 {Absty Repty : Type'} (_884 : Repty -> Prop) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1219 Absty Repty dest mk R x''''' _884.
Proof. exact (@lem34096 Absty Repty _884 x''''' R dest mk h1). Qed.
Lemma lem34098 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x''''' R dest mk) : term1220 Absty Repty mk R x''''' dest x''''.
Proof. exact (@lem34097 Absty Repty (dest x'''') x''''' R dest mk h1). Qed.
Lemma lem34101 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (dest x'''') = (term1221 Absty Repty R x''''' dest x'''').
Proof. exact (@lem34098 Absty Repty x'''' x''''' R dest mk h2 (@lem34082 Absty Repty x'''' mk dest h1)). Qed.
Lemma lem34102 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (dest x'''') = (term1221 Absty Repty R x''''' dest x'''').
Proof. exact (@lem34101 Absty Repty x'''' x''''' R dest mk h1 h2). Qed.
Lemma lem34103 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1222 Absty Repty R x''''' dest x''''.
Proof. exact (fun h0 : term1223 Absty Repty R x''''' dest x'''' => @lem34102 Absty Repty x'''' x''''' R dest mk h1 h2). Qed.
Lemma lem34105 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34106 {Absty Repty : Type'} (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : (term1222 Absty Repty R x''''' dest x'''') = ((dest x'''') = (term1221 Absty Repty R x''''' dest x'''')).
Proof. exact (@lem34105 ((dest x'''') = (term1221 Absty Repty R x''''' dest x''''))). Qed.
Lemma lem34107 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (dest x'''') = (term1221 Absty Repty R x''''' dest x'''').
Proof. exact (EQ_MP (@lem34106 Absty Repty R x''''' dest x'''') (@lem34103 Absty Repty x'''' x''''' R dest mk h1 h2)). Qed.
Lemma lem34113 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem34114 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : (term332 Absty Repty _1008 mk _1009) = (term333 Absty Repty mk _1008 _1009).
Proof. exact (@lem34113 ((mk _1008) = (mk _1009)) (term303 Repty _1008 _1009)). Qed.
Lemma lem34124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem34125 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : (term334 Absty Repty _1008 mk _1009) = (term335 Absty Repty mk _1008 _1009).
Proof. exact (MK_COMB (@lem34124) (@lem34114 Absty Repty mk _1008 _1009)). Qed.
Lemma lem34135 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : (term333 Absty Repty mk _1008 _1009) = (term333 Absty Repty mk _1008 _1009).
Proof. exact (eq_refl (term333 Absty Repty mk _1008 _1009)). Qed.
Lemma lem34136 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : ((term332 Absty Repty _1008 mk _1009) = (term333 Absty Repty mk _1008 _1009)) = ((term333 Absty Repty mk _1008 _1009) = (term333 Absty Repty mk _1008 _1009)).
Proof. exact (MK_COMB (@lem34125 Absty Repty mk _1008 _1009) (@lem34135 Absty Repty mk _1008 _1009)). Qed.
Lemma lem34138 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem34139 (x : Prop) : (x = x) = True.
Proof. exact (@lem34138 Prop x). Qed.
Lemma lem34140 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : ((term333 Absty Repty mk _1008 _1009) = (term333 Absty Repty mk _1008 _1009)) = True.
Proof. exact (@lem34139 (term333 Absty Repty mk _1008 _1009)). Qed.
Lemma lem34141 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : ((term332 Absty Repty _1008 mk _1009) = (term333 Absty Repty mk _1008 _1009)) = True.
Proof. exact (TRANS (@lem34136 Absty Repty mk _1008 _1009) (@lem34140 Absty Repty mk _1008 _1009)). Qed.
Lemma lem34142 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : True = ((term332 Absty Repty _1008 mk _1009) = (term333 Absty Repty mk _1008 _1009)).
Proof. exact (SYM (@lem34141 Absty Repty mk _1008 _1009)). Qed.
Lemma lem34143 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : (term332 Absty Repty _1008 mk _1009) = (term333 Absty Repty mk _1008 _1009).
Proof. exact (EQ_MP (@lem34142 Absty Repty mk _1008 _1009) (@lem0)). Qed.
Lemma lem34144 {Absty Repty : Type'} (mk : type862 Absty Repty) (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : term333 Absty Repty mk _1008 _1009.
Proof. exact (EQ_MP (@lem34143 Absty Repty mk _1008 _1009) (@lem33988 Absty Repty _1008 mk _1009)). Qed.
Lemma lem34146 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem34147 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : (term333 Absty Repty mk _1008 _1009) = (term336 Absty Repty _1008 mk _1009).
Proof. exact (@lem34146 (term303 Repty _1008 _1009) ((mk _1008) = (mk _1009))). Qed.
Lemma lem34149 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem34150 {Repty : Type'} (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : (term315 Repty _1008 _1009) = (_1008 = _1009).
Proof. exact (@lem34149 (_1008 = _1009)). Qed.
Lemma lem34151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34152 {Repty : Type'} (_1008 : Repty -> Prop) (_1009 : Repty -> Prop) : (term337 Repty _1008 _1009) = (term338 Repty _1008 _1009).
Proof. exact (MK_COMB (@lem34151) (@lem34150 Repty _1008 _1009)). Qed.
Lemma lem34153 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : ((mk _1008) = (mk _1009)) = ((mk _1008) = (mk _1009)).
Proof. exact (eq_refl ((mk _1008) = (mk _1009))). Qed.
Lemma lem34154 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : (term336 Absty Repty _1008 mk _1009) = (term331 Absty Repty _1008 mk _1009).
Proof. exact (MK_COMB (@lem34152 Repty _1008 _1009) (@lem34153 Absty Repty _1008 mk _1009)). Qed.
Lemma lem34155 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : (term333 Absty Repty mk _1008 _1009) = (term331 Absty Repty _1008 mk _1009).
Proof. exact (TRANS (@lem34147 Absty Repty _1008 mk _1009) (@lem34154 Absty Repty _1008 mk _1009)). Qed.
Lemma lem34158 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : term331 Absty Repty _1008 mk _1009.
Proof. exact (EQ_MP (@lem34155 Absty Repty _1008 mk _1009) (@lem34144 Absty Repty mk _1008 _1009)). Qed.
Lemma lem34159 {Absty Repty : Type'} (_1008 : Repty -> Prop) (mk : type862 Absty Repty) (_1009 : Repty -> Prop) : term331 Absty Repty _1008 mk _1009.
Proof. exact (@lem34158 Absty Repty _1008 mk _1009). Qed.
Lemma lem34160 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : term1224 Absty Repty mk R x''''' dest x''''.
Proof. exact (@lem34159 Absty Repty (dest x'''') mk (term1221 Absty Repty R x''''' dest x'''')). Qed.
Lemma lem34163 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term119 Absty Repty mk dest x'''') = (term1225 Absty Repty mk R x''''' dest x'''').
Proof. exact (@lem34160 Absty Repty mk R x''''' dest x'''' (@lem34107 Absty Repty x'''' x''''' R dest mk h1 h2)). Qed.
Lemma lem34164 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term119 Absty Repty mk dest x'''') = (term1225 Absty Repty mk R x''''' dest x'''').
Proof. exact (@lem34163 Absty Repty x'''' x''''' R dest mk h1 h2). Qed.
Lemma lem34165 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1226 Absty Repty mk R x''''' dest x''''.
Proof. exact (fun h0 : term1227 Absty Repty mk R x''''' dest x'''' => @lem34164 Absty Repty x'''' x''''' R dest mk h1 h2). Qed.
Lemma lem34167 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34168 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : (term1226 Absty Repty mk R x''''' dest x'''') = ((term119 Absty Repty mk dest x'''') = (term1225 Absty Repty mk R x''''' dest x'''')).
Proof. exact (@lem34167 ((term119 Absty Repty mk dest x'''') = (term1225 Absty Repty mk R x''''' dest x''''))). Qed.
Lemma lem34169 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : (term119 Absty Repty mk dest x'''') = (term1225 Absty Repty mk R x''''' dest x'''').
Proof. exact (EQ_MP (@lem34168 Absty Repty mk R x''''' dest x'''') (@lem34165 Absty Repty x'''' x''''' R dest mk h1 h2)). Qed.
Lemma lem34187 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem34188 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1228 Absty x y z) = (term1229 Absty y x z).
Proof. exact (@lem34187 (y = z) (term276 Absty x z)). Qed.
Lemma lem34198 {Absty : Type'} (x : Absty) (y : Absty) : (term1230 Absty x y) = (term1230 Absty x y).
Proof. exact (eq_refl (term1230 Absty x y)). Qed.
Lemma lem34199 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1207 Absty x y z) = (term1231 Absty y x z).
Proof. exact (MK_COMB (@lem34198 Absty x y) (@lem34188 Absty y x z)). Qed.
Lemma lem34203 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem34204 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1231 Absty y x z) = (term1232 Absty y x z).
Proof. exact (@lem34203 (y = z) (term276 Absty x y) (term276 Absty x z)). Qed.
Lemma lem34226 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1207 Absty x y z) = (term1232 Absty y x z).
Proof. exact (TRANS (@lem34199 Absty y x z) (@lem34204 Absty y x z)). Qed.
Lemma lem34227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem34228 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1233 Absty x y z) = (term1234 Absty y x z).
Proof. exact (MK_COMB (@lem34227) (@lem34226 Absty y x z)). Qed.
Lemma lem34250 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1232 Absty y x z) = (term1232 Absty y x z).
Proof. exact (eq_refl (term1232 Absty y x z)). Qed.
Lemma lem34251 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : ((term1207 Absty x y z) = (term1232 Absty y x z)) = ((term1232 Absty y x z) = (term1232 Absty y x z)).
Proof. exact (MK_COMB (@lem34228 Absty y x z) (@lem34250 Absty y x z)). Qed.
Lemma lem34253 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem34254 (x : Prop) : (x = x) = True.
Proof. exact (@lem34253 Prop x). Qed.
Lemma lem34255 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : ((term1232 Absty y x z) = (term1232 Absty y x z)) = True.
Proof. exact (@lem34254 (term1232 Absty y x z)). Qed.
Lemma lem34256 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : ((term1207 Absty x y z) = (term1232 Absty y x z)) = True.
Proof. exact (TRANS (@lem34251 Absty y x z) (@lem34255 Absty y x z)). Qed.
Lemma lem34257 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : True = ((term1207 Absty x y z) = (term1232 Absty y x z)).
Proof. exact (SYM (@lem34256 Absty y x z)). Qed.
Lemma lem34258 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1207 Absty x y z) = (term1232 Absty y x z).
Proof. exact (EQ_MP (@lem34257 Absty y x z) (@lem0)). Qed.
Lemma lem34259 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : term1232 Absty y x z.
Proof. exact (EQ_MP (@lem34258 Absty y x z) (@lem34002 Absty x y z)). Qed.
Lemma lem34261 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem34262 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : (term1232 Absty y x z) = (term1235 Absty x y z).
Proof. exact (@lem34261 (term1236 Absty y x z) (y = z)). Qed.
Lemma lem34264 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
Lemma lem34265 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1237 Absty y x z) = (term1238 Absty y x z).
Proof. exact (@lem34264 (term276 Absty x y) (term276 Absty x z)). Qed.
Lemma lem34267 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem34268 {Absty : Type'} (x : Absty) (y : Absty) : (term281 Absty x y) = (x = y).
Proof. exact (@lem34267 (x = y)). Qed.
Lemma lem34269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem34270 {Absty : Type'} (x : Absty) (y : Absty) : (term1239 Absty x y) = (term1240 Absty x y).
Proof. exact (MK_COMB (@lem34269) (@lem34268 Absty x y)). Qed.
Lemma lem34272 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem34273 {Absty : Type'} (x : Absty) (z : Absty) : (term281 Absty x z) = (x = z).
Proof. exact (@lem34272 (x = z)). Qed.
Lemma lem34274 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1238 Absty y x z) = (term1241 Absty y x z).
Proof. exact (MK_COMB (@lem34270 Absty x y) (@lem34273 Absty x z)). Qed.
Lemma lem34275 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1237 Absty y x z) = (term1241 Absty y x z).
Proof. exact (TRANS (@lem34265 Absty y x z) (@lem34274 Absty y x z)). Qed.
Lemma lem34276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34277 {Absty : Type'} (y : Absty) (x : Absty) (z : Absty) : (term1242 Absty y x z) = (term1243 Absty y x z).
Proof. exact (MK_COMB (@lem34276) (@lem34275 Absty y x z)). Qed.
Lemma lem34278 {Absty : Type'} (y : Absty) (z : Absty) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem34279 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : (term1235 Absty x y z) = (term1244 Absty x y z).
Proof. exact (MK_COMB (@lem34277 Absty y x z) (@lem34278 Absty y z)). Qed.
Lemma lem34280 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : (term1232 Absty y x z) = (term1244 Absty x y z).
Proof. exact (TRANS (@lem34262 Absty x y z) (@lem34279 Absty x y z)). Qed.
Lemma lem34282 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1274 Absty Repty mk R x''''' dest x''''.
Proof. exact (conj (@lem34011 Absty Repty x'''' mk dest h1) (@lem34169 Absty Repty x'''' x''''' R dest mk h1 h2)). Qed.
Lemma lem34284 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : term1244 Absty x y z.
Proof. exact (EQ_MP (@lem34280 Absty x y z) (@lem34259 Absty y x z)). Qed.
Lemma lem34285 {Absty : Type'} (x : Absty) (y : Absty) (z : Absty) : term1244 Absty x y z.
Proof. exact (@lem34284 Absty x y z). Qed.
Lemma lem34286 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : term1275 Absty Repty mk R x''''' dest x''''.
Proof. exact (@lem34285 Absty (term119 Absty Repty mk dest x'''') x'''' (term1225 Absty Repty mk R x''''' dest x'''')). Qed.
Lemma lem34289 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : x'''' = (term1225 Absty Repty mk R x''''' dest x'''').
Proof. exact (@lem34286 Absty Repty mk R x''''' dest x'''' (@lem34282 Absty Repty x'''' x''''' R dest mk h1 h2)). Qed.
Lemma lem34290 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : x'''' = (term1225 Absty Repty mk R x''''' dest x'''').
Proof. exact (@lem34289 Absty Repty x'''' x''''' R dest mk h1 h2). Qed.
Lemma lem34291 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : term1276 Absty Repty mk R x''''' dest x''''.
Proof. exact (fun h0 : term1277 Absty Repty mk R x''''' dest x'''' => @lem34290 Absty Repty x'''' x''''' R dest mk h1 h2). Qed.
Lemma lem34293 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34294 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : (term1276 Absty Repty mk R x''''' dest x'''') = (x'''' = (term1225 Absty Repty mk R x''''' dest x'''')).
Proof. exact (@lem34293 (x'''' = (term1225 Absty Repty mk R x''''' dest x''''))). Qed.
Lemma lem34295 {Absty Repty : Type'} (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) : x'''' = (term1225 Absty Repty mk R x''''' dest x'''').
Proof. exact (EQ_MP (@lem34294 Absty Repty mk R x''''' dest x'''') (@lem34291 Absty Repty x'''' x''''' R dest mk h1 h2)). Qed.
Lemma lem34297 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : P x''''.
Proof. exact (proj2 (@lem30009 Absty Repty mk R P x'''' h1)). Qed.
Lemma lem34298 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term1270 Absty P x''''.
Proof. exact (fun h0 : term530 Absty P x'''' => @lem34297 Absty Repty mk R P x'''' h1). Qed.
Lemma lem34300 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34301 {Absty : Type'} (P : Absty -> Prop) (x'''' : Absty) : (term1270 Absty P x'''') = (P x'''').
Proof. exact (@lem34300 (P x'''')). Qed.
Lemma lem34302 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : P x''''.
Proof. exact (EQ_MP (@lem34301 Absty P x'''') (@lem34298 Absty Repty mk R P x'''' h1)). Qed.
Lemma lem34308 (q : Prop) (p : Prop) (r : Prop) : (term11 p q r) = (term11 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem34309 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : (term1206 Absty _999 P _998) = (term1253 Absty _999 P _998).
Proof. exact (@lem34308 (P _999) (term276 Absty _998 _999) (term530 Absty P _998)). Qed.
Lemma lem34323 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem34324 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : (term1254 Absty _999 P _998) = (term1255 Absty P _998 _999).
Proof. exact (@lem34323 (term530 Absty P _998) (term276 Absty _998 _999)). Qed.
Lemma lem34332 {Absty : Type'} (P : Absty -> Prop) (_999 : Absty) : (term1256 Absty P _999) = (term1256 Absty P _999).
Proof. exact (eq_refl (term1256 Absty P _999)). Qed.
Lemma lem34333 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : (term1253 Absty _999 P _998) = (term1257 Absty P _998 _999).
Proof. exact (MK_COMB (@lem34332 Absty P _999) (@lem34324 Absty P _998 _999)). Qed.
Lemma lem34344 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : (term1206 Absty _999 P _998) = (term1257 Absty P _998 _999).
Proof. exact (TRANS (@lem34309 Absty _999 P _998) (@lem34333 Absty P _998 _999)). Qed.
Lemma lem34345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem34346 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : (term1258 Absty _999 P _998) = (term1259 Absty P _998 _999).
Proof. exact (MK_COMB (@lem34345) (@lem34344 Absty P _998 _999)). Qed.
Lemma lem34360 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem34361 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : (term1254 Absty _999 P _998) = (term1255 Absty P _998 _999).
Proof. exact (@lem34360 (term530 Absty P _998) (term276 Absty _998 _999)). Qed.
Lemma lem34369 {Absty : Type'} (P : Absty -> Prop) (_999 : Absty) : (term1256 Absty P _999) = (term1256 Absty P _999).
Proof. exact (eq_refl (term1256 Absty P _999)). Qed.
Lemma lem34370 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : (term1253 Absty _999 P _998) = (term1257 Absty P _998 _999).
Proof. exact (MK_COMB (@lem34369 Absty P _999) (@lem34361 Absty P _998 _999)). Qed.
Lemma lem34381 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : ((term1206 Absty _999 P _998) = (term1253 Absty _999 P _998)) = ((term1257 Absty P _998 _999) = (term1257 Absty P _998 _999)).
Proof. exact (MK_COMB (@lem34346 Absty P _998 _999) (@lem34370 Absty P _998 _999)). Qed.
Lemma lem34383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem34384 (x : Prop) : (x = x) = True.
Proof. exact (@lem34383 Prop x). Qed.
Lemma lem34385 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) (_999 : Absty) : ((term1257 Absty P _998 _999) = (term1257 Absty P _998 _999)) = True.
Proof. exact (@lem34384 (term1257 Absty P _998 _999)). Qed.
Lemma lem34386 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : ((term1206 Absty _999 P _998) = (term1253 Absty _999 P _998)) = True.
Proof. exact (TRANS (@lem34381 Absty P _998 _999) (@lem34385 Absty P _998 _999)). Qed.
Lemma lem34387 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : True = ((term1206 Absty _999 P _998) = (term1253 Absty _999 P _998)).
Proof. exact (SYM (@lem34386 Absty _999 P _998)). Qed.
Lemma lem34388 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : (term1206 Absty _999 P _998) = (term1253 Absty _999 P _998).
Proof. exact (EQ_MP (@lem34387 Absty _999 P _998) (@lem0)). Qed.
Lemma lem34389 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : term1253 Absty _999 P _998.
Proof. exact (EQ_MP (@lem34388 Absty _999 P _998) (@lem33945 Absty _999 P _998)). Qed.
Lemma lem34391 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem34392 {Absty : Type'} (_998 : Absty) (P : Absty -> Prop) (_999 : Absty) : (term1253 Absty _999 P _998) = (term1260 Absty _998 P _999).
Proof. exact (@lem34391 (term1254 Absty _999 P _998) (P _999)). Qed.
Lemma lem34394 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (or_elim (@lem20792 a) (fun h0 : a = True => @lem20893 b a h0) (fun h0 : a = False => @lem20892 b a h0)). Qed.
Lemma lem34395 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : (term1261 Absty _999 P _998) = (term1262 Absty _999 P _998).
Proof. exact (@lem34394 (term276 Absty _998 _999) (term530 Absty P _998)). Qed.
Lemma lem34397 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem34398 {Absty : Type'} (_998 : Absty) (_999 : Absty) : (term281 Absty _998 _999) = (_998 = _999).
Proof. exact (@lem34397 (_998 = _999)). Qed.
Lemma lem34399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem34400 {Absty : Type'} (_998 : Absty) (_999 : Absty) : (term1239 Absty _998 _999) = (term1240 Absty _998 _999).
Proof. exact (MK_COMB (@lem34399) (@lem34398 Absty _998 _999)). Qed.
Lemma lem34402 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem34403 {Absty : Type'} (P : Absty -> Prop) (_998 : Absty) : (term1263 Absty P _998) = (P _998).
Proof. exact (@lem34402 (P _998)). Qed.
Lemma lem34404 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : (term1262 Absty _999 P _998) = (term1264 Absty _999 P _998).
Proof. exact (MK_COMB (@lem34400 Absty _998 _999) (@lem34403 Absty P _998)). Qed.
Lemma lem34405 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : (term1261 Absty _999 P _998) = (term1264 Absty _999 P _998).
Proof. exact (TRANS (@lem34395 Absty _999 P _998) (@lem34404 Absty _999 P _998)). Qed.
Lemma lem34406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34407 {Absty : Type'} (_999 : Absty) (P : Absty -> Prop) (_998 : Absty) : (term1265 Absty _999 P _998) = (term1266 Absty _999 P _998).
Proof. exact (MK_COMB (@lem34406) (@lem34405 Absty _999 P _998)). Qed.
Lemma lem34408 {Absty : Type'} (P : Absty -> Prop) (_999 : Absty) : (P _999) = (P _999).
Proof. exact (eq_refl (P _999)). Qed.
Lemma lem34409 {Absty : Type'} (_998 : Absty) (P : Absty -> Prop) (_999 : Absty) : (term1260 Absty _998 P _999) = (term1267 Absty _998 P _999).
Proof. exact (MK_COMB (@lem34407 Absty _999 P _998) (@lem34408 Absty P _999)). Qed.
Lemma lem34410 {Absty : Type'} (_998 : Absty) (P : Absty -> Prop) (_999 : Absty) : (term1253 Absty _999 P _998) = (term1267 Absty _998 P _999).
Proof. exact (TRANS (@lem34392 Absty _998 P _999) (@lem34409 Absty _998 P _999)). Qed.
Lemma lem34412 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : term1278 Absty Repty mk R x''''' dest P x''''.
Proof. exact (conj (@lem34295 Absty Repty x'''' x''''' R dest mk h1 h3) (@lem34302 Absty Repty mk R P x'''' h2)). Qed.
Lemma lem34414 {Absty : Type'} (_998 : Absty) (P : Absty -> Prop) (_999 : Absty) : term1267 Absty _998 P _999.
Proof. exact (EQ_MP (@lem34410 Absty _998 P _999) (@lem34389 Absty _999 P _998)). Qed.
Lemma lem34415 {Absty : Type'} (_998 : Absty) (P : Absty -> Prop) (_999 : Absty) : term1267 Absty _998 P _999.
Proof. exact (@lem34414 Absty _998 P _999). Qed.
Lemma lem34416 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : term1279 Absty Repty P mk R x''''' dest x''''.
Proof. exact (@lem34415 Absty x'''' P (term1225 Absty Repty mk R x''''' dest x'''')). Qed.
Lemma lem34419 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : term1249 Absty Repty P mk R x''''' dest x''''.
Proof. exact (@lem34416 Absty Repty P mk R x''''' dest x'''' (@lem34412 Absty Repty P x'''' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem34420 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : term1251 Absty Repty P mk R x''''' dest x''''.
Proof. exact (fun h0 : term1252 Absty Repty P mk R x''''' dest x'''' => @lem34419 Absty Repty P x'''' x''''' R dest mk h1 h2 h3). Qed.
Lemma lem34422 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34423 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'''' : Absty) : (term1251 Absty Repty P mk R x''''' dest x'''') = (term1249 Absty Repty P mk R x''''' dest x'''').
Proof. exact (@lem34422 (term1249 Absty Repty P mk R x''''' dest x'''')). Qed.
Lemma lem34424 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : term1249 Absty Repty P mk R x''''' dest x''''.
Proof. exact (EQ_MP (@lem34423 Absty Repty P mk R x''''' dest x'''') (@lem34420 Absty Repty P x'''' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem34427 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem34429 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (_895 : Repty) : (term522 Absty Repty P mk R _895) = (term1273 Absty Repty P mk R _895).
Proof. exact (@lem34427 (term405 Absty Repty P mk R _895)). Qed.
Lemma lem34432 {Absty Repty : Type'} (_895 : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term1273 Absty Repty P mk R _895.
Proof. exact (EQ_MP (@lem34429 Absty Repty P mk R _895) (@lem32527 Absty Repty _895 mk R P x'''' h1)). Qed.
Lemma lem34433 {Absty Repty : Type'} (_895 : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term1273 Absty Repty P mk R _895.
Proof. exact (@lem34432 Absty Repty _895 mk R P x'''' h1). Qed.
Lemma lem34434 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term920 Absty Repty mk R P x'''') : term1280 Absty Repty P mk R x''''' dest x''''.
Proof. exact (@lem34433 Absty Repty (term1250 Absty Repty x''''' dest x'''') mk R P x'''' h1). Qed.
Lemma lem34437 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : False.
Proof. exact (@lem34434 Absty Repty x''''' dest mk R P x'''' h2 (@lem34424 Absty Repty P x'''' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem34438 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : term330.
Proof. exact (fun h0 : ~ False => @lem34437 Absty Repty P x'''' x''''' R dest mk h1 h2 h3). Qed.
Lemma lem34440 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem34441 : term330 = False.
Proof. exact (@lem34440 False). Qed.
Lemma lem34442 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : False.
Proof. exact (EQ_MP (@lem34441) (@lem34438 Absty Repty P x'''' x''''' R dest mk h1 h2 h3)). Qed.
Lemma lem34443 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : (term1115 Repty R y x') = False.
Proof. exact (prop_ext (fun h3 : term1115 Repty R y x' => @lem33130 Repty R y x' h1 h2) (fun h3 : False => @lem32239 Repty R y x' h2)). Qed.
Lemma lem34444 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34443 Repty R y x' h1 h2) (@lem32239 Repty R y x' h2)). Qed.
Lemma lem34445 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : (term1117 Repty R y x') = False.
Proof. exact (prop_ext (fun h3 : term1117 Repty R y x' => @lem34444 Repty R y x' h1 h2) (fun h3 : False => @lem32237 Repty R y x' h1)). Qed.
Lemma lem34446 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34445 Repty R y x' h1 h2) (@lem32237 Repty R y x' h1)). Qed.
Lemma lem34447 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : (term1115 Repty R x x') = False.
Proof. exact (prop_ext (fun h6 : term1115 Repty R x x' => @lem33050 Repty y R x x' h1 h2 h3 h4 h5) (fun h6 : False => @lem32181 Repty R x x' h5)). Qed.
Lemma lem34448 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34447 Repty y R x x' h1 h2 h3 h4 h5) (@lem32181 Repty R x x' h5)). Qed.
Lemma lem34449 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : (term1117 Repty R y x') = False.
Proof. exact (prop_ext (fun h6 : term1117 Repty R y x' => @lem34448 Repty y R x x' h1 h2 h3 h4 h5) (fun h6 : False => @lem32179 Repty R y x' h3)). Qed.
Lemma lem34450 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34449 Repty y R x x' h1 h2 h3 h4 h5) (@lem32179 Repty R y x' h3)). Qed.
Lemma lem34451 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : (term1115 Repty R y x') = False.
Proof. exact (prop_ext (fun h5 : term1115 Repty R y x' => @lem32803 Repty x R y x' h1 h2 h3 h4) (fun h5 : False => @lem32123 Repty R y x' h4)). Qed.
Lemma lem34452 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34451 Repty x R y x' h1 h2 h3 h4) (@lem32123 Repty R y x' h4)). Qed.
Lemma lem34453 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : (term1117 Repty R x x') = False.
Proof. exact (prop_ext (fun h5 : term1117 Repty R x x' => @lem34452 Repty x R y x' h1 h2 h3 h4) (fun h5 : False => @lem32121 Repty R x x' h2)). Qed.
Lemma lem34454 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34453 Repty x R y x' h1 h2 h3 h4) (@lem32121 Repty R x x' h2)). Qed.
Lemma lem34455 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : (term1115 Repty R x x') = False.
Proof. exact (prop_ext (fun h3 : term1115 Repty R x x' => @lem32609 Repty R x x' h1 h2) (fun h3 : False => @lem32065 Repty R x x' h2)). Qed.
Lemma lem34456 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34455 Repty R x x' h1 h2) (@lem32065 Repty R x x' h2)). Qed.
Lemma lem34457 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : (term1117 Repty R x x') = False.
Proof. exact (prop_ext (fun h3 : term1117 Repty R x x' => @lem34456 Repty R x x' h1 h2) (fun h3 : False => @lem32063 Repty R x x' h1)). Qed.
Lemma lem34458 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34457 Repty R x x' h1 h2) (@lem32063 Repty R x x' h1)). Qed.
Lemma lem34459 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : (term1115 Repty R y x') = False.
Proof. exact (prop_ext (fun h3 : term1115 Repty R y x' => @lem34446 Repty R y x' h1 h2) (fun h3 : False => @lem30693 Repty R y x' h2)). Qed.
Lemma lem34460 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34459 Repty R y x' h1 h2) (@lem30693 Repty R y x' h2)). Qed.
Lemma lem34461 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : (term1117 Repty R y x') = False.
Proof. exact (prop_ext (fun h3 : term1117 Repty R y x' => @lem34460 Repty R y x' h1 h2) (fun h3 : False => @lem30689 Repty R y x' h1)). Qed.
Lemma lem34462 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34461 Repty R y x' h1 h2) (@lem30689 Repty R y x' h1)). Qed.
Lemma lem34463 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : (term1115 Repty R x x') = False.
Proof. exact (prop_ext (fun h6 : term1115 Repty R x x' => @lem34450 Repty y R x x' h1 h2 h3 h4 h5) (fun h6 : False => @lem30523 Repty R x x' h5)). Qed.
Lemma lem34464 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34463 Repty y R x x' h1 h2 h3 h4 h5) (@lem30523 Repty R x x' h5)). Qed.
Lemma lem34465 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : (term1117 Repty R y x') = False.
Proof. exact (prop_ext (fun h6 : term1117 Repty R y x' => @lem34464 Repty y R x x' h1 h2 h3 h4 h5) (fun h6 : False => @lem30519 Repty R y x' h3)). Qed.
Lemma lem34466 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34465 Repty y R x x' h1 h2 h3 h4 h5) (@lem30519 Repty R y x' h3)). Qed.
Lemma lem34467 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : (term1115 Repty R y x') = False.
Proof. exact (prop_ext (fun h5 : term1115 Repty R y x' => @lem34454 Repty x R y x' h1 h2 h3 h4) (fun h5 : False => @lem30353 Repty R y x' h4)). Qed.
Lemma lem34468 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34467 Repty x R y x' h1 h2 h3 h4) (@lem30353 Repty R y x' h4)). Qed.
Lemma lem34469 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : (term1117 Repty R x x') = False.
Proof. exact (prop_ext (fun h5 : term1117 Repty R x x' => @lem34468 Repty x R y x' h1 h2 h3 h4) (fun h5 : False => @lem30349 Repty R x x' h2)). Qed.
Lemma lem34470 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34469 Repty x R y x' h1 h2 h3 h4) (@lem30349 Repty R x x' h2)). Qed.
Lemma lem34471 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : (term1115 Repty R x x') = False.
Proof. exact (prop_ext (fun h3 : term1115 Repty R x x' => @lem34458 Repty R x x' h1 h2) (fun h3 : False => @lem30183 Repty R x x' h2)). Qed.
Lemma lem34472 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34471 Repty R x x' h1 h2) (@lem30183 Repty R x x' h2)). Qed.
Lemma lem34473 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : (term1117 Repty R x x') = False.
Proof. exact (prop_ext (fun h3 : term1117 Repty R x x' => @lem34472 Repty R x x' h1 h2) (fun h3 : False => @lem30179 Repty R x x' h1)). Qed.
Lemma lem34474 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34473 Repty R x x' h1 h2) (@lem30179 Repty R x x' h1)). Qed.
Lemma lem34475 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : (term73 Absty Repty mk dest) = False.
Proof. exact (prop_ext (fun h4 : term73 Absty Repty mk dest => @lem34442 Absty Repty P x'''' x''''' R dest mk h1 h2 h3) (fun h4 : False => @lem31427 Absty Repty mk dest h1)). Qed.
Lemma lem34476 {Absty Repty : Type'} (P : Absty -> Prop) (x'''' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term920 Absty Repty mk R P x'''') (h3 : term239 Absty Repty x''''' R dest mk) : False.
Proof. exact (EQ_MP (@lem34475 Absty Repty P x'''' x''''' R dest mk h1 h2 h3) (@lem31427 Absty Repty mk dest h1)). Qed.
Lemma lem34477 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : (term73 Absty Repty mk dest) = False.
Proof. exact (prop_ext (fun h4 : term73 Absty Repty mk dest => @lem33745 Absty Repty P x'' x''''' R dest mk h1 h2 h3) (fun h4 : False => @lem30920 Absty Repty mk dest h1)). Qed.
Lemma lem34478 {Absty Repty : Type'} (P : Absty -> Prop) (x'' : Absty) (x''''' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term785 Absty Repty mk R P x'') (h3 : term239 Absty Repty x''''' R dest mk) : False.
Proof. exact (EQ_MP (@lem34477 Absty Repty P x'' x''''' R dest mk h1 h2 h3) (@lem30920 Absty Repty mk dest h1)). Qed.
Lemma lem34479 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : (term1115 Repty R y x') = False.
Proof. exact (prop_ext (fun h3 : term1115 Repty R y x' => @lem34462 Repty R y x' h1 h2) (fun h3 : False => @lem30693 Repty R y x' h2)). Qed.
Lemma lem34480 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34479 Repty R y x' h1 h2) (@lem30693 Repty R y x' h2)). Qed.
Lemma lem34481 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : (term1117 Repty R y x') = False.
Proof. exact (prop_ext (fun h3 : term1117 Repty R y x' => @lem34480 Repty R y x' h1 h2) (fun h3 : False => @lem30689 Repty R y x' h1)). Qed.
Lemma lem34482 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term1117 Repty R y x') (h2 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34481 Repty R y x' h1 h2) (@lem30689 Repty R y x' h1)). Qed.
Lemma lem34483 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : (term1115 Repty R x x') = False.
Proof. exact (prop_ext (fun h6 : term1115 Repty R x x' => @lem34466 Repty y R x x' h1 h2 h3 h4 h5) (fun h6 : False => @lem30523 Repty R x x' h5)). Qed.
Lemma lem34484 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34483 Repty y R x x' h1 h2 h3 h4 h5) (@lem30523 Repty R x x' h5)). Qed.
Lemma lem34485 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : (term1117 Repty R y x') = False.
Proof. exact (prop_ext (fun h6 : term1117 Repty R y x' => @lem34484 Repty y R x x' h1 h2 h3 h4 h5) (fun h6 : False => @lem30519 Repty R y x' h3)). Qed.
Lemma lem34486 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') (h5 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34485 Repty y R x x' h1 h2 h3 h4 h5) (@lem30519 Repty R y x' h3)). Qed.
Lemma lem34487 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : (term1115 Repty R y x') = False.
Proof. exact (prop_ext (fun h5 : term1115 Repty R y x' => @lem34470 Repty x R y x' h1 h2 h3 h4) (fun h5 : False => @lem30353 Repty R y x' h4)). Qed.
Lemma lem34488 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34487 Repty x R y x' h1 h2 h3 h4) (@lem30353 Repty R y x' h4)). Qed.
Lemma lem34489 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : (term1117 Repty R x x') = False.
Proof. exact (prop_ext (fun h5 : term1117 Repty R x x' => @lem34488 Repty x R y x' h1 h2 h3 h4) (fun h5 : False => @lem30349 Repty R x x' h2)). Qed.
Lemma lem34490 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') (h4 : term1115 Repty R y x') : False.
Proof. exact (EQ_MP (@lem34489 Repty x R y x' h1 h2 h3 h4) (@lem30349 Repty R x x' h2)). Qed.
Lemma lem34491 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : (term1115 Repty R x x') = False.
Proof. exact (prop_ext (fun h3 : term1115 Repty R x x' => @lem34474 Repty R x x' h1 h2) (fun h3 : False => @lem30183 Repty R x x' h2)). Qed.
Lemma lem34492 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34491 Repty R x x' h1 h2) (@lem30183 Repty R x x' h2)). Qed.
Lemma lem34493 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : (term1117 Repty R x x') = False.
Proof. exact (prop_ext (fun h3 : term1117 Repty R x x' => @lem34492 Repty R x x' h1 h2) (fun h3 : False => @lem30179 Repty R x x' h1)). Qed.
Lemma lem34494 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) (h1 : term1117 Repty R x x') (h2 : term1115 Repty R x x') : False.
Proof. exact (EQ_MP (@lem34493 Repty R x x' h1 h2) (@lem30179 Repty R x x' h1)). Qed.
Lemma lem34495 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) (h3 : term926 Absty Repty x''' mk R P x'''') : False.
Proof. exact (or_elim (@lem30001 Absty Repty x''' mk R P x'''' h3) (fun h0 : term872 Absty Repty mk R x''' P => @lem33933 Absty Repty mk R x''' P h0) (fun h0 : term920 Absty Repty mk R P x'''' => @lem34476 Absty Repty P x'''' x''''' R dest mk h1 h0 h2)). Qed.
Lemma lem34496 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (x''' : Repty) (P : Absty -> Prop) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) (h3 : term853 Absty Repty x'' mk R x''' P) : False.
Proof. exact (or_elim (@lem30000 Absty Repty x'' mk R x''' P h3) (fun h0 : term785 Absty Repty mk R P x'' => @lem34478 Absty Repty P x'' x''''' R dest mk h1 h0 h2) (fun h0 : term803 Absty Repty mk R x''' P => @lem33839 Absty Repty mk R x''' P h0)). Qed.
Lemma lem34497 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term239 Absty Repty x''''' R dest mk) (h3 : term994 Absty Repty x'' x''' mk R P x'''') : False.
Proof. exact (or_elim (@lem29983 Absty Repty x'' x''' mk R P x'''' h3) (fun h0 : term853 Absty Repty x'' mk R x''' P => @lem34496 Absty Repty x''''' dest x'' mk R x''' P h1 h2 h0) (fun h0 : term926 Absty Repty x''' mk R P x'''' => @lem34495 Absty Repty x''''' dest x''' mk R P x'''' h1 h2 h0)). Qed.
Lemma lem34498 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1117 Repty R y x') (h4 : term1161 Repty x R y x') : False.
Proof. exact (or_elim (@lem29989 Repty x R y x' h4) (fun h0 : term1115 Repty R x x' => @lem34486 Repty y R x x' h1 h2 h3 h4 h0) (fun h0 : term1115 Repty R y x' => @lem34482 Repty R y x' h3 h0)). Qed.
Lemma lem34499 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term1117 Repty R x x') (h3 : term1161 Repty x R y x') : False.
Proof. exact (or_elim (@lem29989 Repty x R y x' h3) (fun h0 : term1115 Repty R x x' => @lem34494 Repty R x x' h2 h0) (fun h0 : term1115 Repty R y x' => @lem34490 Repty x R y x' h1 h2 h3 h0)). Qed.
Lemma lem34500 {Repty : Type'} (x : Repty) (R : type1402 Repty) (y : Repty) (x' : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term1161 Repty x R y x') : False.
Proof. exact (or_elim (@lem29988 Repty x R y x' h3) (fun h0 : term1117 Repty R x x' => @lem34499 Repty x R y x' h1 h0 h3) (fun h0 : term1117 Repty R y x' => @lem34498 Repty x R y x' h1 h2 h0 h3)). Qed.
Lemma lem34501 {Repty : Type'} (x' : Repty) (x : Repty) (R : type1402 Repty) (y : Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) (h4 : term1163 Repty x' x R y) : False.
Proof. exact (or_elim (@lem29982 Repty x' x R y h4) (fun h0 : term1161 Repty x R y x' => @lem34500 Repty x R y x' h1 h2 h0) (fun h0 : term1152 Repty x R y => @lem33236 Repty x R y h3 h0)). Qed.
Lemma lem34502 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term239 Absty Repty x''''' R dest mk) (h6 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : False.
Proof. exact (or_elim (@lem29918 Absty Repty x' x y x'' x''' mk R P x'''' h6) (fun h0 : term1163 Repty x' x R y => @lem34501 Repty x' x R y h2 h3 h4 h0) (fun h0 : term994 Absty Repty x'' x''' mk R P x'''' => @lem34497 Absty Repty x''''' dest x'' x''' mk R P x'''' h1 h5 h0)). Qed.
Lemma lem34503 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term239 Absty Repty x''''' R dest mk) (h6 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : (term239 Absty Repty x''''' R dest mk) = False.
Proof. exact (prop_ext (fun h7 : term239 Absty Repty x''''' R dest mk => @lem34502 Absty Repty x''''' dest x' x y x'' x''' mk R P x'''' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem29975 Absty Repty x''''' R dest mk h5)). Qed.
Lemma lem34504 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term239 Absty Repty x''''' R dest mk) (h6 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : False.
Proof. exact (EQ_MP (@lem34503 Absty Repty x''''' dest x' x y x'' x''' mk R P x'''' h1 h2 h3 h4 h5 h6) (@lem29975 Absty Repty x''''' R dest mk h5)). Qed.
Lemma lem34505 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term239 Absty Repty x''''' R dest mk) (h6 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : (term73 Absty Repty mk dest) = False.
Proof. exact (prop_ext (fun h7 : term73 Absty Repty mk dest => @lem34504 Absty Repty x''''' dest x' x y x'' x''' mk R P x'''' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem29620 Absty Repty mk dest h1)). Qed.
Lemma lem34506 {Absty Repty : Type'} (x''''' : type684 Repty) (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term239 Absty Repty x''''' R dest mk) (h6 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : False.
Proof. exact (EQ_MP (@lem34505 Absty Repty x''''' dest x' x y x'' x''' mk R P x'''' h1 h2 h3 h4 h5 h6) (@lem29620 Absty Repty mk dest h1)). Qed.
Lemma lem34507 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (x'''' : Absty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term1096 Absty Repty x' x y x'' x''' mk R P x'''') : False.
Proof. exact (ex_elim (@lem27405 Absty Repty R dest mk h5) (fun x''''' : type684 Repty => fun h0 : term241 Absty Repty R dest mk x''''' => @lem34506 Absty Repty x''''' dest x' x y x'' x''' mk R P x'''' h1 h2 h3 h4 h0 h6)). Qed.
Lemma lem34508 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (x''' : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term1099 Absty Repty x' x y x'' x''' mk R P) : False.
Proof. exact (ex_elim (@lem29475 Absty Repty x' x y x'' x''' mk R P h6) (fun x'''' : Absty => fun h0 : term1098 Absty Repty x' x y x'' x''' mk R P x'''' => @lem34507 Absty Repty dest x' x y x'' x''' mk R P x'''' h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem34509 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (x'' : Absty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term1101 Absty Repty x' x y x'' mk R P) : False.
Proof. exact (ex_elim (@lem29474 Absty Repty x' x y x'' mk R P h6) (fun x''' : Repty => fun h0 : term1100 Absty Repty x' x y x'' mk R P x''' => @lem34508 Absty Repty dest x' x y x'' x''' mk R P h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem34510 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term1103 Absty Repty x' x y mk R P) : False.
Proof. exact (ex_elim (@lem29473 Absty Repty x' x y mk R P h6) (fun x'' : Absty => fun h0 : term1102 Absty Repty x' x y mk R P x'' => @lem34509 Absty Repty dest x' x y x'' mk R P h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem34511 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x' : Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term1105 Absty Repty x' x y mk R) : False.
Proof. exact (ex_elim (@lem29472 Absty Repty x' x y mk R h6) (fun P : Absty -> Prop => fun h0 : term1104 Absty Repty x' x y mk R P => @lem34510 Absty Repty dest x' x y mk R P h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem34512 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term1107 Absty Repty x y mk R) : False.
Proof. exact (ex_elim (@lem29471 Absty Repty x y mk R h6) (fun x' : Repty => fun h0 : term1106 Absty Repty x y mk R x' => @lem34511 Absty Repty dest x' x y mk R h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem34513 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term1109 Absty Repty x mk R) : False.
Proof. exact (ex_elim (@lem29470 Absty Repty x mk R h6) (fun y : Repty => fun h0 : term1108 Absty Repty x mk R y => @lem34512 Absty Repty dest x y mk R h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem34514 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term373 Absty Repty mk R) : False.
Proof. exact (ex_elim (@lem29469 Absty Repty mk R h6) (fun x : Repty => fun h0 : term1110 Absty Repty mk R x => @lem34513 Absty Repty dest x mk R h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem34515 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term373 Absty Repty mk R) : (term73 Absty Repty mk dest) = False.
Proof. exact (prop_ext (fun h7 : term73 Absty Repty mk dest => @lem34514 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem27153 Absty Repty mk dest h1)). Qed.
Lemma lem34516 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term373 Absty Repty mk R) : False.
Proof. exact (EQ_MP (@lem34515 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (@lem27153 Absty Repty mk dest h1)). Qed.
Lemma lem34517 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term373 Absty Repty mk R) : (term67 Repty R) = False.
Proof. exact (prop_ext (fun h7 : term67 Repty R => @lem34516 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem26770 Repty R h4)). Qed.
Lemma lem34518 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term373 Absty Repty mk R) : False.
Proof. exact (EQ_MP (@lem34517 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (@lem26770 Repty R h4)). Qed.
Lemma lem34519 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term373 Absty Repty mk R) : (term373 Absty Repty mk R) = False.
Proof. exact (prop_ext (fun h7 : term373 Absty Repty mk R => @lem34518 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem26757 Absty Repty mk R h6)). Qed.
Lemma lem34520 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) (h6 : term373 Absty Repty mk R) : False.
Proof. exact (EQ_MP (@lem34519 Absty Repty dest mk R h1 h2 h3 h4 h5 h6) (@lem26757 Absty Repty mk R h6)). Qed.
Lemma lem34521 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term372 Absty Repty mk R.
Proof. exact (fun h0 : term373 Absty Repty mk R => @lem34520 Absty Repty dest mk R h1 h2 h3 h4 h5 h0). Qed.
Lemma lem34522 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term371 Absty Repty mk R.
Proof. exact (EQ_MP (@lem26756 Absty Repty mk R) (@lem34521 Absty Repty R dest mk h1 h2 h3 h4 h5)). Qed.
Lemma lem34523 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term381 Absty Repty mk R.
Proof. exact (fun h0 : term74 Absty Repty mk R => @lem34522 Absty Repty R dest mk h1 h2 h3 h4 h5). Qed.
Lemma lem34524 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) : term383 Absty Repty dest mk R.
Proof. exact (fun h0 : term72 Absty Repty R dest mk => @lem34523 Absty Repty R dest mk h1 h2 h3 h4 h0). Qed.
Lemma lem34525 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) : term385 Absty Repty dest mk R.
Proof. exact (fun h0 : term73 Absty Repty mk dest => @lem34524 Absty Repty mk dest R h0 h1 h2 h3). Qed.
Lemma lem34526 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) : term387 Absty Repty dest mk R.
Proof. exact (fun h0 : term71 Repty R => @lem34525 Absty Repty dest mk R h0 h1 h2). Qed.
Lemma lem34527 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term389 Absty Repty dest mk R.
Proof. exact (fun h0 : term69 Repty R => @lem34526 Absty Repty dest mk R h0 h1). Qed.
Lemma lem34528 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term390 Absty Repty dest mk R.
Proof. exact (fun h0 : term67 Repty R => @lem34527 Absty Repty dest mk R h0). Qed.
Lemma lem34533 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : term394 Absty Repty mk R.
Proof. exact (fun dest : type1413 Absty Repty => @lem34528 Absty Repty dest mk R). Qed.
Lemma lem34538 {Absty Repty : Type'} (R : type1402 Repty) : term398 Absty Repty R.
Proof. exact (fun mk : type862 Absty Repty => @lem34533 Absty Repty mk R). Qed.
Lemma lem34543 {Absty Repty : Type'} : term402 Absty Repty.
Proof. exact (fun R : type1402 Repty => @lem34538 Absty Repty R). Qed.
Lemma lem34544 {Absty Repty : Type'} : term401 Absty Repty.
Proof. exact (EQ_MP (@lem26746 Absty Repty) (@lem34543 Absty Repty)). Qed.
Lemma lem34545 {Absty Repty : Type'} (R : type1402 Repty) : term1281 Absty Repty R.
Proof. exact (@lem34544 Absty Repty R). Qed.
Lemma lem34546 {Absty Repty : Type'} (R : type1402 Repty) : (term1281 Absty Repty R) = (term397 Absty Repty R).
Proof. exact (eq_refl (term1281 Absty Repty R)). Qed.
Lemma lem34547 {Absty Repty : Type'} (R : type1402 Repty) : term397 Absty Repty R.
Proof. exact (EQ_MP (@lem34546 Absty Repty R) (@lem34545 Absty Repty R)). Qed.
Lemma lem34548 {Absty Repty : Type'} (R : type1402 Repty) (mk : type862 Absty Repty) : term1282 Absty Repty R mk.
Proof. exact (@lem34547 Absty Repty R mk). Qed.
Lemma lem34549 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1282 Absty Repty R mk) = (term393 Absty Repty mk R).
Proof. exact (eq_refl (term1282 Absty Repty R mk)). Qed.
Lemma lem34550 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : term393 Absty Repty mk R.
Proof. exact (EQ_MP (@lem34549 Absty Repty mk R) (@lem34548 Absty Repty R mk)). Qed.
Lemma lem34551 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : term1283 Absty Repty mk R dest.
Proof. exact (@lem34550 Absty Repty mk R dest). Qed.
Lemma lem34552 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1283 Absty Repty mk R dest) = (term374 Absty Repty dest mk R).
Proof. exact (eq_refl (term1283 Absty Repty mk R dest)). Qed.
Lemma lem34553 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term374 Absty Repty dest mk R.
Proof. exact (EQ_MP (@lem34552 Absty Repty dest mk R) (@lem34551 Absty Repty mk R dest)). Qed.
Lemma lem34555 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : term374 Absty Repty dest mk R.
Proof. exact (@lem26278 Absty Repty dest mk R (@lem34553 Absty Repty dest mk R)). Qed.
Lemma lem34556 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term388 Absty Repty dest mk R.
Proof. exact (@lem34555 Absty Repty dest mk R (@lem23771 Repty R h1)). Qed.
Lemma lem34557 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) : term386 Absty Repty dest mk R.
Proof. exact (@lem34556 Absty Repty dest mk R h2 (@lem23773 Repty R h1)). Qed.
Lemma lem34558 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) : term384 Absty Repty dest mk R.
Proof. exact (@lem34557 Absty Repty dest mk R h2 h3 (@lem23775 Repty R h1)). Qed.
Lemma lem34559 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) : term382 Absty Repty dest mk R.
Proof. exact (@lem34558 Absty Repty dest mk R h2 h3 h4 (@lem23777 Absty Repty mk dest h1)). Qed.
Lemma lem34560 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term380 Absty Repty mk R.
Proof. exact (@lem34559 Absty Repty mk dest R h1 h2 h3 h4 (@lem23776 Absty Repty R dest mk h5)). Qed.
Lemma lem34561 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term372 Absty Repty mk R.
Proof. exact (@lem34560 Absty Repty R dest mk h1 h2 h4 h5 h6 (@lem23778 Absty Repty mk R h3)). Qed.
Lemma lem34562 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term373 Absty Repty mk R) : False.
Proof. exact (@lem34561 Absty Repty R dest mk h1 h2 h3 h4 h5 h6 (@lem26262 Absty Repty mk R h7)). Qed.
Lemma lem34563 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term373 Absty Repty mk R) : (term373 Absty Repty mk R) = False.
Proof. exact (prop_ext (fun h8 : term373 Absty Repty mk R => @lem34562 Absty Repty dest mk R h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem26262 Absty Repty mk R h7)). Qed.
Lemma lem34564 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term373 Absty Repty mk R) : False.
Proof. exact (EQ_MP (@lem34563 Absty Repty dest mk R h1 h2 h3 h4 h5 h6 h7) (@lem26262 Absty Repty mk R h7)). Qed.
Lemma lem34565 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term372 Absty Repty mk R.
Proof. exact (fun h0 : term373 Absty Repty mk R => @lem34564 Absty Repty dest mk R h1 h2 h3 h4 h5 h6 h0). Qed.
Lemma lem34566 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term371 Absty Repty mk R.
Proof. exact (EQ_MP (@lem26261 Absty Repty mk R) (@lem34565 Absty Repty R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem34567 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term363 Absty Repty mk R.
Proof. exact (EQ_MP (@lem26257 Absty Repty mk R) (@lem34566 Absty Repty R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem34568 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term362 Absty Repty mk R.
Proof. exact (EQ_MP (@lem26168 Absty Repty mk R h3) (@lem34567 Absty Repty R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem34569 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : term346 Absty Repty mk R.
Proof. exact (h1). Qed.
Lemma lem34571 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : (term411 Absty Repty P mk R) = (term410 Absty P)) : (term411 Absty Repty P mk R) = (term410 Absty P).
Proof. exact (h1). Qed.
Lemma lem34572 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (P : Absty -> Prop) (h1 : (term411 Absty Repty P mk R) = (term410 Absty P)) : (term410 Absty P) = (term411 Absty Repty P mk R).
Proof. exact (SYM (@lem34571 Absty Repty mk R P h1)). Qed.
Lemma lem34573 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : (term410 Absty P) = (term411 Absty Repty P mk R)) : (term410 Absty P) = (term411 Absty Repty P mk R).
Proof. exact (h1). Qed.
Lemma lem34574 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : (term410 Absty P) = (term411 Absty Repty P mk R)) : (term411 Absty Repty P mk R) = (term410 Absty P).
Proof. exact (SYM (@lem34573 Absty Repty P mk R h1)). Qed.
Lemma lem34575 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : ((term411 Absty Repty P mk R) = (term410 Absty P)) = ((term410 Absty P) = (term411 Absty Repty P mk R)).
Proof. exact (prop_ext (fun h1 : (term411 Absty Repty P mk R) = (term410 Absty P) => @lem34572 Absty Repty mk R P h1) (fun h1 : (term410 Absty P) = (term411 Absty Repty P mk R) => @lem34574 Absty Repty P mk R h1)). Qed.
Lemma lem34576 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term413 Absty Repty mk R) = (term1284 Absty Repty mk R).
Proof. exact (fun_ext (fun P : Absty -> Prop => @lem34575 Absty Repty P mk R)). Qed.
Lemma lem34577 {Absty : Type'} : (@all (Absty -> Prop)) = (@all (Absty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Prop))). Qed.
Lemma lem34578 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term346 Absty Repty mk R) = (term1285 Absty Repty mk R).
Proof. exact (MK_COMB (@lem34577 Absty) (@lem34576 Absty Repty mk R)). Qed.
Lemma lem34579 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : term1285 Absty Repty mk R.
Proof. exact (EQ_MP (@lem34578 Absty Repty mk R) (@lem34569 Absty Repty mk R h1)). Qed.
Lemma lem34580 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : term1286 Absty Repty mk R P.
Proof. exact (@lem34579 Absty Repty mk R h1 P). Qed.
Lemma lem34581 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1286 Absty Repty mk R P) = ((term410 Absty P) = (term411 Absty Repty P mk R)).
Proof. exact (eq_refl (term1286 Absty Repty mk R P)). Qed.
Lemma lem34610 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : (term410 Absty P) = (term411 Absty Repty P mk R).
Proof. exact (EQ_MP (@lem34581 Absty Repty P mk R) (@lem34580 Absty Repty P mk R h1)). Qed.
Lemma lem34611 {Absty Repty : Type'} (P : Absty -> Prop) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : (term410 Absty P) = (term411 Absty Repty P mk R).
Proof. exact (@lem34610 Absty Repty P mk R h1). Qed.
Lemma lem34612 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : (term1287 Absty Repty mk R dest) = (term1288 Absty Repty dest mk R).
Proof. exact (@lem34611 Absty Repty (term1289 Absty Repty mk R dest) mk R h1). Qed.
Lemma lem34613 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (x : Absty) : (term1290 Absty Repty mk R dest x) = ((term1291 Absty Repty mk R dest x) = x).
Proof. exact (eq_refl (term1290 Absty Repty mk R dest x)). Qed.
Lemma lem34614 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : (term1292 Absty Repty mk R dest) = (term1289 Absty Repty mk R dest).
Proof. exact (fun_ext (fun x : Absty => @lem34613 Absty Repty mk R dest x)). Qed.
Lemma lem34615 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem34616 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : (term1287 Absty Repty mk R dest) = (term348 Absty Repty mk R dest).
Proof. exact (MK_COMB (@lem34615 Absty) (@lem34614 Absty Repty mk R dest)). Qed.
Lemma lem34617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem34618 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) : (term1293 Absty Repty mk R dest) = (term1294 Absty Repty mk R dest).
Proof. exact (MK_COMB (@lem34617) (@lem34616 Absty Repty mk R dest)). Qed.
Lemma lem34619 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1295 Absty Repty dest mk R x) = ((term1296 Absty Repty dest mk R x) = (term110 Absty Repty mk R x)).
Proof. exact (eq_refl (term1295 Absty Repty dest mk R x)). Qed.
Lemma lem34620 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1297 Absty Repty dest mk R) = (term1298 Absty Repty dest mk R).
Proof. exact (fun_ext (fun x : Repty => @lem34619 Absty Repty dest mk R x)). Qed.
Lemma lem34621 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34622 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : (term1288 Absty Repty dest mk R) = (term1299 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem34621 Repty) (@lem34620 Absty Repty dest mk R)). Qed.
Lemma lem34623 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) : ((term1287 Absty Repty mk R dest) = (term1288 Absty Repty dest mk R)) = ((term348 Absty Repty mk R dest) = (term1299 Absty Repty dest mk R)).
Proof. exact (MK_COMB (@lem34618 Absty Repty mk R dest) (@lem34622 Absty Repty dest mk R)). Qed.
Lemma lem34624 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : (term348 Absty Repty mk R dest) = (term1299 Absty Repty dest mk R).
Proof. exact (EQ_MP (@lem34623 Absty Repty dest mk R) (@lem34612 Absty Repty dest mk R h1)). Qed.
Lemma lem34635 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term1300 Absty Repty mk R) = (term1300 Absty Repty mk R).
Proof. exact (eq_refl (term1300 Absty Repty mk R)). Qed.
Lemma lem34636 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : (term1301 Absty Repty mk R dest) = (term1302 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem34635 Absty Repty mk R) (@lem34624 Absty Repty dest mk R h1)). Qed.
Lemma lem34639 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term346 Absty Repty mk R) : (term1302 Absty Repty dest mk R) = (term1301 Absty Repty mk R dest).
Proof. exact (SYM (@lem34636 Absty Repty dest mk R h1)). Qed.
Lemma lem34640 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : term345 Absty Repty mk R.
Proof. exact (h1). Qed.
Lemma lem34643 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) (h1 : (R x y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y))) : (R x y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)).
Proof. exact (h1). Qed.
Lemma lem34644 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (y : Repty) (h1 : (R x y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y))) : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y).
Proof. exact (SYM (@lem34643 Absty Repty x mk R y h1)). Qed.
Lemma lem34645 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (y : Repty) (h1 : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y)) : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y).
Proof. exact (h1). Qed.
Lemma lem34646 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (y : Repty) (h1 : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y)) : (R x y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)).
Proof. exact (SYM (@lem34645 Absty Repty mk R x y h1)). Qed.
Lemma lem34647 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (y : Repty) : ((R x y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y))) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y)).
Proof. exact (prop_ext (fun h1 : (R x y) = ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) => @lem34644 Absty Repty x mk R y h1) (fun h1 : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y) => @lem34646 Absty Repty mk R x y h1)). Qed.
Lemma lem34648 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term352 Absty Repty x mk R) = (term1303 Absty Repty mk R x).
Proof. exact (fun_ext (fun y : Repty => @lem34647 Absty Repty mk R x y)). Qed.
Lemma lem34649 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34650 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term354 Absty Repty x mk R) = (term1304 Absty Repty mk R x).
Proof. exact (MK_COMB (@lem34649 Repty) (@lem34648 Absty Repty mk R x)). Qed.
Lemma lem34651 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term356 Absty Repty mk R) = (term1305 Absty Repty mk R).
Proof. exact (fun_ext (fun x : Repty => @lem34650 Absty Repty mk R x)). Qed.
Lemma lem34652 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34653 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term345 Absty Repty mk R) = (term1306 Absty Repty mk R).
Proof. exact (MK_COMB (@lem34652 Repty) (@lem34651 Absty Repty mk R)). Qed.
Lemma lem34654 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : term1306 Absty Repty mk R.
Proof. exact (EQ_MP (@lem34653 Absty Repty mk R) (@lem34640 Absty Repty mk R h1)). Qed.
Lemma lem34655 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : term1307 Absty Repty mk R x.
Proof. exact (@lem34654 Absty Repty mk R h1 x). Qed.
Lemma lem34656 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1307 Absty Repty mk R x) = (term1304 Absty Repty mk R x).
Proof. exact (eq_refl (term1307 Absty Repty mk R x)). Qed.
Lemma lem34657 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : term1304 Absty Repty mk R x.
Proof. exact (EQ_MP (@lem34656 Absty Repty mk R x) (@lem34655 Absty Repty x mk R h1)). Qed.
Lemma lem34658 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : term1308 Absty Repty mk R x y.
Proof. exact (@lem34657 Absty Repty x mk R h1 y). Qed.
Lemma lem34659 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (y : Repty) : (term1308 Absty Repty mk R x y) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y)).
Proof. exact (eq_refl (term1308 Absty Repty mk R x y)). Qed.
Lemma lem34666 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y).
Proof. exact (EQ_MP (@lem34659 Absty Repty mk R x y) (@lem34658 Absty Repty x y mk R h1)). Qed.
Lemma lem34667 {Absty Repty : Type'} (x : Repty) (y : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : ((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = (R x y).
Proof. exact (@lem34666 Absty Repty x y mk R h1). Qed.
Lemma lem34668 {Absty Repty : Type'} (dest : type1413 Absty Repty) (x : Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : ((term1296 Absty Repty dest mk R x) = (term110 Absty Repty mk R x)) = (term1309 Absty Repty dest mk R x).
Proof. exact (@lem34667 Absty Repty (term1310 Absty Repty dest mk R x) x mk R h1). Qed.
Lemma lem34669 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : (term1298 Absty Repty dest mk R) = (term1311 Absty Repty dest mk R).
Proof. exact (fun_ext (fun x : Repty => @lem34668 Absty Repty dest x mk R h1)). Qed.
Lemma lem34670 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34671 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : (term1299 Absty Repty dest mk R) = (term1312 Absty Repty dest mk R).
Proof. exact (MK_COMB (@lem34670 Repty) (@lem34669 Absty Repty dest mk R h1)). Qed.
Lemma lem34676 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (h1 : term345 Absty Repty mk R) : (term1312 Absty Repty dest mk R) = (term1299 Absty Repty dest mk R).
Proof. exact (SYM (@lem34671 Absty Repty dest mk R h1)). Qed.
Lemma lem34677 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : (term285 Absty Repty dest mk R x) = (R x)) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (h1). Qed.
Lemma lem34678 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1313 Repty R x) = (term1313 Repty R x).
Proof. exact (eq_refl (term1313 Repty R x)). Qed.
Lemma lem34679 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : (term285 Absty Repty dest mk R x) = (R x)) : (term1314 Absty Repty dest mk R x) = (term1315 Repty R x).
Proof. exact (MK_COMB (@lem34678 Repty R x) (@lem34677 Absty Repty dest mk R x h1)). Qed.
Lemma lem34680 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1315 Repty R x) = (term1316 Repty R x).
Proof. exact (eq_refl (term1315 Repty R x)). Qed.
Lemma lem34681 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1317 Absty Repty dest mk R x) = (term1317 Absty Repty dest mk R x).
Proof. exact (eq_refl (term1317 Absty Repty dest mk R x)). Qed.
Lemma lem34682 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : ((term1314 Absty Repty dest mk R x) = (term1315 Repty R x)) = ((term1314 Absty Repty dest mk R x) = (term1316 Repty R x)).
Proof. exact (MK_COMB (@lem34681 Absty Repty dest mk R x) (@lem34680 Repty R x)). Qed.
Lemma lem34683 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1314 Absty Repty dest mk R x) = (term1309 Absty Repty dest mk R x).
Proof. exact (eq_refl (term1314 Absty Repty dest mk R x)). Qed.
Lemma lem34684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem34685 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1317 Absty Repty dest mk R x) = (term1318 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34684) (@lem34683 Absty Repty dest mk R x)). Qed.
Lemma lem34686 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1316 Repty R x) = (term1316 Repty R x).
Proof. exact (eq_refl (term1316 Repty R x)). Qed.
Lemma lem34687 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : ((term1314 Absty Repty dest mk R x) = (term1316 Repty R x)) = ((term1309 Absty Repty dest mk R x) = (term1316 Repty R x)).
Proof. exact (MK_COMB (@lem34685 Absty Repty dest mk R x) (@lem34686 Repty R x)). Qed.
Lemma lem34688 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : ((term1314 Absty Repty dest mk R x) = (term1315 Repty R x)) = ((term1309 Absty Repty dest mk R x) = (term1316 Repty R x)).
Proof. exact (TRANS (@lem34682 Absty Repty dest mk R x) (@lem34687 Absty Repty dest mk R x)). Qed.
Lemma lem34689 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : (term285 Absty Repty dest mk R x) = (R x)) : (term1309 Absty Repty dest mk R x) = (term1316 Repty R x).
Proof. exact (EQ_MP (@lem34688 Absty Repty dest mk R x) (@lem34679 Absty Repty dest mk R x h1)). Qed.
Lemma lem34690 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : (term285 Absty Repty dest mk R x) = (R x)) : (term1316 Repty R x) = (term1309 Absty Repty dest mk R x).
Proof. exact (SYM (@lem34689 Absty Repty dest mk R x h1)). Qed.
Lemma lem34692 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem34693 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : ((term285 Absty Repty dest mk R x) = (R x)) = (term1319 Absty Repty dest mk R x).
Proof. exact (@lem34692 ((term285 Absty Repty dest mk R x) = (R x))). Qed.
Lemma lem34694 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1319 Absty Repty dest mk R x) = ((term285 Absty Repty dest mk R x) = (R x)).
Proof. exact (SYM (@lem34693 Absty Repty dest mk R x)). Qed.
Lemma lem34695 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term300 Absty Repty dest mk R x) : term300 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem34698 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1320 Absty Repty dest mk R x) : term1320 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem34699 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1321 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1320 Absty Repty dest mk R x => @lem34698 Absty Repty dest mk R x h0). Qed.
Lemma lem34700 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1321 Absty Repty dest mk R x) : term1321 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem34701 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1320 Absty Repty dest mk R x) : term1320 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem34702 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1320 Absty Repty dest mk R x) (h2 : term1321 Absty Repty dest mk R x) : term1320 Absty Repty dest mk R x.
Proof. exact (@lem34700 Absty Repty dest mk R x h2 (@lem34701 Absty Repty dest mk R x h1)). Qed.
Lemma lem34703 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1320 Absty Repty dest mk R x) : term1322 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1321 Absty Repty dest mk R x => @lem34702 Absty Repty dest mk R x h1 h0). Qed.
Lemma lem34704 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1321 Absty Repty dest mk R x) : term1321 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem34705 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1320 Absty Repty dest mk R x) (h2 : term1321 Absty Repty dest mk R x) : term1320 Absty Repty dest mk R x.
Proof. exact (@lem34703 Absty Repty dest mk R x h1 (@lem34704 Absty Repty dest mk R x h2)). Qed.
Lemma lem34706 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1321 Absty Repty dest mk R x) : term1321 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1320 Absty Repty dest mk R x => @lem34705 Absty Repty dest mk R x h0 h1). Qed.
Lemma lem34707 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1323 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1321 Absty Repty dest mk R x => @lem34706 Absty Repty dest mk R x h0). Qed.
Lemma lem34710 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1321 Absty Repty dest mk R x.
Proof. exact (@lem34707 Absty Repty dest mk R x (@lem34699 Absty Repty dest mk R x)). Qed.
Lemma lem34711 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1321 Absty Repty dest mk R x.
Proof. exact (@lem34710 Absty Repty dest mk R x). Qed.
Lemma lem34789 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem34790 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1319 Absty Repty dest mk R x) = (term1324 Absty Repty dest mk R x).
Proof. exact (@lem34789 (term300 Absty Repty dest mk R x)). Qed.
Lemma lem34792 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem34793 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1324 Absty Repty dest mk R x) = ((term285 Absty Repty dest mk R x) = (R x)).
Proof. exact (@lem34792 ((term285 Absty Repty dest mk R x) = (R x))). Qed.
Lemma lem34794 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1319 Absty Repty dest mk R x) = ((term285 Absty Repty dest mk R x) = (R x)).
Proof. exact (TRANS (@lem34790 Absty Repty dest mk R x) (@lem34793 Absty Repty dest mk R x)). Qed.
Lemma lem34795 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term379 Absty Repty mk R) = (term379 Absty Repty mk R).
Proof. exact (eq_refl (term379 Absty Repty mk R)). Qed.
Lemma lem34796 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1325 Absty Repty dest mk R x) = (term1326 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34795 Absty Repty mk R) (@lem34794 Absty Repty dest mk R x)). Qed.
Lemma lem34799 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (eq_refl (term84 Absty Repty R dest mk)). Qed.
Lemma lem34800 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1327 Absty Repty dest mk R x) = (term1328 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34799 Absty Repty R dest mk) (@lem34796 Absty Repty dest mk R x)). Qed.
Lemma lem34803 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (eq_refl (term87 Absty Repty mk dest)). Qed.
Lemma lem34804 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1329 Absty Repty dest mk R x) = (term1330 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34803 Absty Repty mk dest) (@lem34800 Absty Repty dest mk R x)). Qed.
Lemma lem34807 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (eq_refl (term90 Repty R)). Qed.
Lemma lem34808 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1331 Absty Repty dest mk R x) = (term1332 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34807 Repty R) (@lem34804 Absty Repty dest mk R x)). Qed.
Lemma lem34811 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (eq_refl (term93 Repty R)). Qed.
Lemma lem34812 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1333 Absty Repty dest mk R x) = (term1334 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34811 Repty R) (@lem34808 Absty Repty dest mk R x)). Qed.
Lemma lem34815 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (eq_refl (term96 Repty R)). Qed.
Lemma lem34816 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1320 Absty Repty dest mk R x) = (term1335 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34815 Repty R) (@lem34812 Absty Repty dest mk R x)). Qed.
Lemma lem34819 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1336 Absty Repty mk R x) = (term1337 Absty Repty mk R x).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem34816 Absty Repty dest mk R x)). Qed.
Lemma lem34820 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem34821 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1338 Absty Repty mk R x) = (term1339 Absty Repty mk R x).
Proof. exact (MK_COMB (@lem34820 Absty Repty) (@lem34819 Absty Repty mk R x)). Qed.
Lemma lem34826 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1340 Absty Repty R x) = (term1341 Absty Repty R x).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem34821 Absty Repty mk R x)). Qed.
Lemma lem34827 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem34828 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1342 Absty Repty R x) = (term1343 Absty Repty R x).
Proof. exact (MK_COMB (@lem34827 Absty Repty) (@lem34826 Absty Repty R x)). Qed.
Lemma lem34833 {Absty Repty : Type'} (x : Repty) : (term1344 Absty Repty x) = (term1345 Absty Repty x).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem34828 Absty Repty R x)). Qed.
Lemma lem34834 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem34835 {Absty Repty : Type'} (x : Repty) : (term1346 Absty Repty x) = (term1347 Absty Repty x).
Proof. exact (MK_COMB (@lem34834 Repty) (@lem34833 Absty Repty x)). Qed.
Lemma lem34840 {Absty Repty : Type'} : (term1348 Absty Repty) = (term1349 Absty Repty).
Proof. exact (fun_ext (fun x : Repty => @lem34835 Absty Repty x)). Qed.
Lemma lem34841 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34850 {Absty Repty : Type'} : (term1350 Absty Repty) = (term1351 Absty Repty).
Proof. exact (MK_COMB (@lem34841 Repty) (@lem34840 Absty Repty)). Qed.
Lemma lem34851 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : ((term285 Absty Repty dest mk R x) = (R x)) = ((term285 Absty Repty dest mk R x) = (R x)).
Proof. exact (eq_refl ((term285 Absty Repty dest mk R x) = (R x))). Qed.
Lemma lem34856 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))).
Proof. exact (eq_refl (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)))). Qed.
Lemma lem34857 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term111 Absty Repty mk x R) = (term111 Absty Repty mk x R).
Proof. exact (fun_ext (fun y : Repty => @lem34856 Absty Repty mk x R y)). Qed.
Lemma lem34858 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34859 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term112 Absty Repty mk x R) = (term112 Absty Repty mk x R).
Proof. exact (MK_COMB (@lem34858 Repty) (@lem34857 Absty Repty mk x R)). Qed.
Lemma lem34860 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term113 Absty Repty mk R) = (term113 Absty Repty mk R).
Proof. exact (fun_ext (fun x : Repty => @lem34859 Absty Repty mk x R)). Qed.
Lemma lem34861 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34862 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term74 Absty Repty mk R) = (term74 Absty Repty mk R).
Proof. exact (MK_COMB (@lem34861 Repty) (@lem34860 Absty Repty mk R)). Qed.
Lemma lem34863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34864 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term379 Absty Repty mk R) = (term379 Absty Repty mk R).
Proof. exact (MK_COMB (@lem34863) (@lem34862 Absty Repty mk R)). Qed.
Lemma lem34865 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1326 Absty Repty dest mk R x) = (term1326 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34864 Absty Repty mk R) (@lem34851 Absty Repty dest mk R x)). Qed.
Lemma lem34866 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem34867 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem34868 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem34867 Repty r R x)). Qed.
Lemma lem34869 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem34870 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem34869 Repty) (@lem34868 Repty r R)). Qed.
Lemma lem34871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem34872 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term117 Repty r R) = (term117 Repty r R).
Proof. exact (MK_COMB (@lem34871) (@lem34870 Repty r R)). Qed.
Lemma lem34873 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)).
Proof. exact (MK_COMB (@lem34872 Repty r R) (@lem34866 Absty Repty dest mk r)). Qed.
Lemma lem34874 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term118 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem34873 Absty Repty R dest mk r)). Qed.
Lemma lem34875 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem34876 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term72 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem34875 Repty) (@lem34874 Absty Repty R dest mk)). Qed.
Lemma lem34877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34878 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem34877) (@lem34876 Absty Repty R dest mk)). Qed.
Lemma lem34879 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1328 Absty Repty dest mk R x) = (term1328 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34878 Absty Repty R dest mk) (@lem34865 Absty Repty dest mk R x)). Qed.
Lemma lem34880 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem34881 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem34880 Absty Repty mk dest a)). Qed.
Lemma lem34882 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem34883 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem34882 Absty) (@lem34881 Absty Repty mk dest)). Qed.
Lemma lem34884 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34885 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem34884) (@lem34883 Absty Repty mk dest)). Qed.
Lemma lem34886 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1330 Absty Repty dest mk R x) = (term1330 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34885 Absty Repty mk dest) (@lem34879 Absty Repty dest mk R x)). Qed.
Lemma lem34895 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term121 Repty y R x z) = (term121 Repty y R x z).
Proof. exact (eq_refl (term121 Repty y R x z)). Qed.
Lemma lem34896 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term122 Repty y R x) = (term122 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem34895 Repty y R x z)). Qed.
Lemma lem34897 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34898 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term123 Repty y R x) = (term123 Repty y R x).
Proof. exact (MK_COMB (@lem34897 Repty) (@lem34896 Repty y R x)). Qed.
Lemma lem34899 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term124 Repty R x) = (term124 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem34898 Repty y R x)). Qed.
Lemma lem34900 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34901 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term125 Repty R x) = (term125 Repty R x).
Proof. exact (MK_COMB (@lem34900 Repty) (@lem34899 Repty R x)). Qed.
Lemma lem34902 {Repty : Type'} (R : type1402 Repty) : (term126 Repty R) = (term126 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem34901 Repty R x)). Qed.
Lemma lem34903 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34904 {Repty : Type'} (R : type1402 Repty) : (term71 Repty R) = (term71 Repty R).
Proof. exact (MK_COMB (@lem34903 Repty) (@lem34902 Repty R)). Qed.
Lemma lem34905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34906 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (MK_COMB (@lem34905) (@lem34904 Repty R)). Qed.
Lemma lem34907 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1332 Absty Repty dest mk R x) = (term1332 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34906 Repty R) (@lem34886 Absty Repty dest mk R x)). Qed.
Lemma lem34912 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : ((R x y) = (R y x)) = ((R x y) = (R y x)).
Proof. exact (eq_refl ((R x y) = (R y x))). Qed.
Lemma lem34913 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term127 Repty R x) = (term127 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem34912 Repty R y x)). Qed.
Lemma lem34914 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34915 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term128 Repty R x) = (term128 Repty R x).
Proof. exact (MK_COMB (@lem34914 Repty) (@lem34913 Repty R x)). Qed.
Lemma lem34916 {Repty : Type'} (R : type1402 Repty) : (term129 Repty R) = (term129 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem34915 Repty R x)). Qed.
Lemma lem34917 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34918 {Repty : Type'} (R : type1402 Repty) : (term69 Repty R) = (term69 Repty R).
Proof. exact (MK_COMB (@lem34917 Repty) (@lem34916 Repty R)). Qed.
Lemma lem34919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34920 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (MK_COMB (@lem34919) (@lem34918 Repty R)). Qed.
Lemma lem34921 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1334 Absty Repty dest mk R x) = (term1334 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34920 Repty R) (@lem34907 Absty Repty dest mk R x)). Qed.
Lemma lem34922 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem34923 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term130 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem34922 Repty R x)). Qed.
Lemma lem34924 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34925 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term67 Repty R).
Proof. exact (MK_COMB (@lem34924 Repty) (@lem34923 Repty R)). Qed.
Lemma lem34926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem34927 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (MK_COMB (@lem34926) (@lem34925 Repty R)). Qed.
Lemma lem34928 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1335 Absty Repty dest mk R x) = (term1335 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem34927 Repty R) (@lem34921 Absty Repty dest mk R x)). Qed.
Lemma lem34929 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1337 Absty Repty mk R x) = (term1337 Absty Repty mk R x).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem34928 Absty Repty dest mk R x)). Qed.
Lemma lem34930 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem34931 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1339 Absty Repty mk R x) = (term1339 Absty Repty mk R x).
Proof. exact (MK_COMB (@lem34930 Absty Repty) (@lem34929 Absty Repty mk R x)). Qed.
Lemma lem34932 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1341 Absty Repty R x) = (term1341 Absty Repty R x).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem34931 Absty Repty mk R x)). Qed.
Lemma lem34933 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem34934 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1343 Absty Repty R x) = (term1343 Absty Repty R x).
Proof. exact (MK_COMB (@lem34933 Absty Repty) (@lem34932 Absty Repty R x)). Qed.
Lemma lem34935 {Absty Repty : Type'} (x : Repty) : (term1345 Absty Repty x) = (term1345 Absty Repty x).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem34934 Absty Repty R x)). Qed.
Lemma lem34936 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem34937 {Absty Repty : Type'} (x : Repty) : (term1347 Absty Repty x) = (term1347 Absty Repty x).
Proof. exact (MK_COMB (@lem34936 Repty) (@lem34935 Absty Repty x)). Qed.
Lemma lem34938 {Absty Repty : Type'} : (term1349 Absty Repty) = (term1349 Absty Repty).
Proof. exact (fun_ext (fun x : Repty => @lem34937 Absty Repty x)). Qed.
Lemma lem34939 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem34940 {Absty Repty : Type'} : (term1351 Absty Repty) = (term1351 Absty Repty).
Proof. exact (MK_COMB (@lem34939 Repty) (@lem34938 Absty Repty)). Qed.
Lemma lem35049 {Absty Repty : Type'} : (term1350 Absty Repty) = (term1351 Absty Repty).
Proof. exact (TRANS (@lem34850 Absty Repty) (@lem34940 Absty Repty)). Qed.
Lemma lem35050 {Absty Repty : Type'} : (term1351 Absty Repty) = (term1350 Absty Repty).
Proof. exact (SYM (@lem35049 Absty Repty)). Qed.
Lemma lem35055 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term72 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem35058 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem35059 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : ((term285 Absty Repty dest mk R x) = (R x)) = (term1319 Absty Repty dest mk R x).
Proof. exact (@lem35058 ((term285 Absty Repty dest mk R x) = (R x))). Qed.
Lemma lem35060 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1319 Absty Repty dest mk R x) = ((term285 Absty Repty dest mk R x) = (R x)).
Proof. exact (SYM (@lem35059 Absty Repty dest mk R x)). Qed.
Lemma lem35061 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term300 Absty Repty dest mk R x) : term300 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem35459 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem35460 {Repty : Type'} (P : Repty -> Prop) : (term133 Repty P) = (term134 Repty P).
Proof. exact (@lem18394 Repty P). Qed.
Lemma lem35461 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term136 Repty r R).
Proof. exact (@lem35460 Repty (term115 Repty r R)). Qed.
Lemma lem35462 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem35463 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem35465 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term138 Repty r R x) = (term139 Repty r R x).
Proof. exact (MK_COMB (@lem35463) (@lem35462 Repty r R x)). Qed.
Lemma lem35466 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term140 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem35465 Repty r R x)). Qed.
Lemma lem35467 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem35468 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term136 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem35467 Repty) (@lem35466 Repty r R)). Qed.
Lemma lem35469 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term142 Repty r R).
Proof. exact (TRANS (@lem35461 Repty r R) (@lem35468 Repty r R)). Qed.
Lemma lem35470 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem35459 Repty r R x)). Qed.
Lemma lem35471 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem35472 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem35471 Repty) (@lem35470 Repty r R)). Qed.
Lemma lem35473 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem35474 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem35475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem35476 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term144 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem35475) (@lem35469 Repty r R)). Qed.
Lemma lem35477 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term146 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35476 Repty r R) (@lem35474 Absty Repty dest mk r)). Qed.
Lemma lem35478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem35479 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term148 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem35478) (@lem35472 Repty r R)). Qed.
Lemma lem35480 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35479 Repty r R) (@lem35473 Absty Repty dest mk r)). Qed.
Lemma lem35481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem35482 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term150 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35481) (@lem35480 Absty Repty R dest mk r)). Qed.
Lemma lem35483 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term151 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35482 Absty Repty R dest mk r) (@lem35477 Absty Repty R dest mk r)). Qed.
Lemma lem35484 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term151 Absty Repty R dest mk r).
Proof. exact (@lem17784 (term116 Repty r R) ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem35485 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term152 Absty Repty R dest mk r).
Proof. exact (TRANS (@lem35484 Absty Repty R dest mk r) (@lem35483 Absty Repty R dest mk r)). Qed.
Lemma lem35486 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem35485 Absty Repty R dest mk r)). Qed.
Lemma lem35487 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem35488 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35487 Repty) (@lem35486 Absty Repty R dest mk)). Qed.
Lemma lem35490 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem35491 {Repty : Type'} (P : type686 Repty) (Q : type686 Repty) : (term157 Repty P Q) = (term158 Repty P Q).
Proof. exact (@lem35490 (Repty -> Prop) P Q). Qed.
Lemma lem35492 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk).
Proof. exact (@lem35491 Repty (term161 Absty Repty R dest mk) (term162 Absty Repty R dest mk)). Qed.
Lemma lem35493 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem35494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem35495 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term164 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35494) (@lem35493 Absty Repty R dest mk r)). Qed.
Lemma lem35496 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem35497 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term166 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35495 Absty Repty R dest mk r) (@lem35496 Absty Repty R dest mk r)). Qed.
Lemma lem35498 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term167 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem35497 Absty Repty R dest mk r)). Qed.
Lemma lem35499 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem35500 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35499 Repty) (@lem35498 Absty Repty R dest mk)). Qed.
Lemma lem35501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem35502 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term168 Absty Repty R dest mk) = (term169 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35501) (@lem35500 Absty Repty R dest mk)). Qed.
Lemma lem35503 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem35504 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term170 Absty Repty R dest mk) = (term161 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem35503 Absty Repty R dest mk r)). Qed.
Lemma lem35505 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem35506 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term171 Absty Repty R dest mk) = (term172 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35505 Repty) (@lem35504 Absty Repty R dest mk)). Qed.
Lemma lem35507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem35508 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term173 Absty Repty R dest mk) = (term174 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35507) (@lem35506 Absty Repty R dest mk)). Qed.
Lemma lem35509 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem35510 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term175 Absty Repty R dest mk) = (term162 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem35509 Absty Repty R dest mk r)). Qed.
Lemma lem35511 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem35512 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term176 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35511 Repty) (@lem35510 Absty Repty R dest mk)). Qed.
Lemma lem35513 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term160 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35508 Absty Repty R dest mk) (@lem35512 Absty Repty R dest mk)). Qed.
Lemma lem35514 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk)) = ((term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem35502 Absty Repty R dest mk) (@lem35513 Absty Repty R dest mk)). Qed.
Lemma lem35515 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem35514 Absty Repty R dest mk) (@lem35492 Absty Repty R dest mk)). Qed.
Lemma lem35621 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem35622 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem35621 Repty P Q). Qed.
Lemma lem35623 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r).
Proof. exact (@lem35622 Repty (term115 Repty r R) (term143 Absty Repty dest mk r)). Qed.
Lemma lem35624 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem35625 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term183 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem35624 Repty r R x)). Qed.
Lemma lem35626 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem35627 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term184 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem35626 Repty) (@lem35625 Repty r R)). Qed.
Lemma lem35628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem35629 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term185 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem35628) (@lem35627 Repty r R)). Qed.
Lemma lem35630 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem35631 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35629 Repty r R) (@lem35630 Absty Repty dest mk r)). Qed.
Lemma lem35632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem35633 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term186 Absty Repty R dest mk r) = (term187 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35632) (@lem35631 Absty Repty R dest mk r)). Qed.
Lemma lem35634 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem35635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem35636 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term188 Repty r R x) = (term189 Repty r R x).
Proof. exact (MK_COMB (@lem35635) (@lem35634 Repty r R x)). Qed.
Lemma lem35637 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem35638 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term190 Absty Repty R x dest mk r) = (term191 Absty Repty R x dest mk r).
Proof. exact (MK_COMB (@lem35636 Repty r R x) (@lem35637 Absty Repty dest mk r)). Qed.
Lemma lem35639 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term192 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem35638 Absty Repty R x dest mk r)). Qed.
Lemma lem35640 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem35641 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term182 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35640 Repty) (@lem35639 Absty Repty R dest mk r)). Qed.
Lemma lem35642 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r)) = ((term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r)).
Proof. exact (MK_COMB (@lem35633 Absty Repty R dest mk r) (@lem35641 Absty Repty R dest mk r)). Qed.
Lemma lem35643 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (EQ_MP (@lem35642 Absty Repty R dest mk r) (@lem35623 Absty Repty R dest mk r)). Qed.
Lemma lem35644 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term161 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem35643 Absty Repty R dest mk r)). Qed.
Lemma lem35645 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem35646 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35645 Repty) (@lem35644 Absty Repty R dest mk)). Qed.
Lemma lem35648 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem35649 {Repty : Type'} (P : type672 Repty) : (term199 Repty P) = (term200 Repty P).
Proof. exact (@lem35648 (Repty -> Prop) Repty P). Qed.
Lemma lem35650 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk).
Proof. exact (@lem35649 Repty (term203 Absty Repty R dest mk)). Qed.
Lemma lem35651 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem35652 {Repty : Type'} (x : Repty) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem35653 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) (x : Repty) : (term205 Absty Repty R dest mk r x) = (term206 Absty Repty R dest mk r x).
Proof. exact (MK_COMB (@lem35651 Absty Repty R dest mk r) (@lem35652 Repty x)). Qed.
Lemma lem35654 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term206 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term206 Absty Repty R dest mk r x)). Qed.
Lemma lem35655 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term205 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem35653 Absty Repty R dest mk r x) (@lem35654 Absty Repty R x dest mk r)). Qed.
Lemma lem35656 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term207 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem35655 Absty Repty R x dest mk r)). Qed.
Lemma lem35657 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem35658 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term208 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem35657 Repty) (@lem35656 Absty Repty R dest mk r)). Qed.
Lemma lem35659 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term209 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem35658 Absty Repty R dest mk r)). Qed.
Lemma lem35660 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem35661 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35660 Repty) (@lem35659 Absty Repty R dest mk)). Qed.
Lemma lem35662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem35663 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term210 Absty Repty R dest mk) = (term211 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35662) (@lem35661 Absty Repty R dest mk)). Qed.
Lemma lem35664 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem35665 {Repty : Type'} (x : type684 Repty) (r : Repty -> Prop) : (x r) = (x r).
Proof. exact (eq_refl (x r)). Qed.
Lemma lem35666 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : type684 Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term213 Absty Repty R dest mk x r).
Proof. exact (MK_COMB (@lem35664 Absty Repty R dest mk r) (@lem35665 Repty x r)). Qed.
Lemma lem35667 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term213 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term213 Absty Repty R dest mk x r)). Qed.
Lemma lem35668 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem35666 Absty Repty R dest mk x r) (@lem35667 Absty Repty R x dest mk r)). Qed.
Lemma lem35669 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term215 Absty Repty R dest mk x) = (term216 Absty Repty R x dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem35668 Absty Repty R x dest mk r)). Qed.
Lemma lem35670 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem35671 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term217 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem35670 Repty) (@lem35669 Absty Repty R x dest mk)). Qed.
Lemma lem35672 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term219 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem35671 Absty Repty R x dest mk)). Qed.
Lemma lem35673 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem35674 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term202 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35673 Repty) (@lem35672 Absty Repty R dest mk)). Qed.
Lemma lem35675 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk)) = ((term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem35663 Absty Repty R dest mk) (@lem35674 Absty Repty R dest mk)). Qed.
Lemma lem35676 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem35675 Absty Repty R dest mk) (@lem35650 Absty Repty R dest mk)). Qed.
Lemma lem35677 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (TRANS (@lem35646 Absty Repty R dest mk) (@lem35676 Absty Repty R dest mk)). Qed.
Lemma lem35678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem35679 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term174 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35678) (@lem35677 Absty Repty R dest mk)). Qed.
Lemma lem35680 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem35681 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35679 Absty Repty R dest mk) (@lem35680 Absty Repty R dest mk)). Qed.
Lemma lem35683 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem35684 {Repty : Type'} (P : type162 Repty) (Q : Prop) : (term226 Repty P Q) = (term227 Repty P Q).
Proof. exact (@lem35683 (type684 Repty) P Q). Qed.
Lemma lem35685 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk).
Proof. exact (@lem35684 Repty (term220 Absty Repty R dest mk) (term177 Absty Repty R dest mk)). Qed.
Lemma lem35686 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem35687 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term231 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem35686 Absty Repty R x dest mk)). Qed.
Lemma lem35688 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem35689 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term232 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35688 Repty) (@lem35687 Absty Repty R dest mk)). Qed.
Lemma lem35690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem35691 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term233 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35690) (@lem35689 Absty Repty R dest mk)). Qed.
Lemma lem35692 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem35693 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35691 Absty Repty R dest mk) (@lem35692 Absty Repty R dest mk)). Qed.
Lemma lem35694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem35695 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term234 Absty Repty R dest mk) = (term235 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35694) (@lem35693 Absty Repty R dest mk)). Qed.
Lemma lem35696 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem35697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem35698 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term236 Absty Repty R dest mk x) = (term237 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem35697) (@lem35696 Absty Repty R x dest mk)). Qed.
Lemma lem35699 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem35700 {Absty Repty : Type'} (x : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term238 Absty Repty x R dest mk) = (term239 Absty Repty x R dest mk).
Proof. exact (MK_COMB (@lem35698 Absty Repty R x dest mk) (@lem35699 Absty Repty R dest mk)). Qed.
Lemma lem35701 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term240 Absty Repty R dest mk) = (term241 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem35700 Absty Repty x R dest mk)). Qed.
Lemma lem35702 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem35703 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term229 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem35702 Repty) (@lem35701 Absty Repty R dest mk)). Qed.
Lemma lem35704 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk)) = ((term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem35695 Absty Repty R dest mk) (@lem35703 Absty Repty R dest mk)). Qed.
Lemma lem35705 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem35704 Absty Repty R dest mk) (@lem35685 Absty Repty R dest mk)). Qed.
Lemma lem35706 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem35681 Absty Repty R dest mk) (@lem35705 Absty Repty R dest mk)). Qed.
Lemma lem35707 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem35515 Absty Repty R dest mk) (@lem35706 Absty Repty R dest mk)). Qed.
Lemma lem35708 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem35488 Absty Repty R dest mk) (@lem35707 Absty Repty R dest mk)). Qed.
Lemma lem35709 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term242 Absty Repty R dest mk.
Proof. exact (EQ_MP (@lem35708 Absty Repty R dest mk) (@lem35055 Absty Repty R dest mk h1)). Qed.
Lemma lem36002 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term300 Absty Repty dest mk R x) : term300 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36003 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term239 Absty Repty x' R dest mk.
Proof. exact (h1). Qed.
Lemma lem36232 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term300 Absty Repty dest mk R x) : term300 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36241 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem36250 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term139 Repty r R x) = (term139 Repty r R x).
Proof. exact (eq_refl (term139 Repty r R x)). Qed.
Lemma lem36251 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term141 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem36250 Repty r R x)). Qed.
Lemma lem36252 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem36253 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term142 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem36252 Repty) (@lem36251 Repty r R)). Qed.
Lemma lem36254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem36255 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term145 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem36254) (@lem36253 Repty r R)). Qed.
Lemma lem36256 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term147 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem36255 Repty r R) (@lem36241 Absty Repty dest mk r)). Qed.
Lemma lem36257 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term162 Absty Repty R dest mk) = (term162 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem36256 Absty Repty R dest mk r)). Qed.
Lemma lem36258 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem36259 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem36258 Repty) (@lem36257 Absty Repty R dest mk)). Qed.
Lemma lem36282 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term214 Absty Repty R x' dest mk r) = (term214 Absty Repty R x' dest mk r).
Proof. exact (eq_refl (term214 Absty Repty R x' dest mk r)). Qed.
Lemma lem36283 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term216 Absty Repty R x' dest mk) = (term216 Absty Repty R x' dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem36282 Absty Repty R x' dest mk r)). Qed.
Lemma lem36284 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem36285 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term218 Absty Repty R x' dest mk) = (term218 Absty Repty R x' dest mk).
Proof. exact (MK_COMB (@lem36284 Repty) (@lem36283 Absty Repty R x' dest mk)). Qed.
Lemma lem36286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem36287 {Absty Repty : Type'} (R : type1402 Repty) (x' : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term237 Absty Repty R x' dest mk) = (term237 Absty Repty R x' dest mk).
Proof. exact (MK_COMB (@lem36286) (@lem36285 Absty Repty R x' dest mk)). Qed.
Lemma lem36288 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term239 Absty Repty x' R dest mk) = (term239 Absty Repty x' R dest mk).
Proof. exact (MK_COMB (@lem36287 Absty Repty R x' dest mk) (@lem36259 Absty Repty R dest mk)). Qed.
Lemma lem36289 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term239 Absty Repty x' R dest mk.
Proof. exact (EQ_MP (@lem36288 Absty Repty x' R dest mk) (@lem36003 Absty Repty x' R dest mk h1)). Qed.
Lemma lem36290 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term177 Absty Repty R dest mk.
Proof. exact (proj2 (@lem36289 Absty Repty x' R dest mk h1)). Qed.
Lemma lem36338 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term300 Absty Repty dest mk R x) : term300 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36353 {A : Type'} (P : A -> Prop) (Q : Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem36354 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term246 Repty P Q) = (term247 Repty P Q).
Proof. exact (@lem36353 Repty P Q). Qed.
Lemma lem36355 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term248 Absty Repty R dest mk r) = (term249 Absty Repty R dest mk r).
Proof. exact (@lem36354 Repty (term141 Repty r R) ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem36356 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term250 Repty r R x) = (term139 Repty r R x).
Proof. exact (eq_refl (term250 Repty r R x)). Qed.
Lemma lem36357 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term251 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem36356 Repty r R x)). Qed.
Lemma lem36358 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem36359 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term252 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem36358 Repty) (@lem36357 Repty r R)). Qed.
Lemma lem36360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem36361 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term253 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem36360) (@lem36359 Repty r R)). Qed.
Lemma lem36362 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem36363 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term248 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem36361 Repty r R) (@lem36362 Absty Repty dest mk r)). Qed.
Lemma lem36364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem36365 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term254 Absty Repty R dest mk r) = (term255 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem36364) (@lem36363 Absty Repty R dest mk r)). Qed.
Lemma lem36366 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term250 Repty r R x) = (term139 Repty r R x).
Proof. exact (eq_refl (term250 Repty r R x)). Qed.
Lemma lem36367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem36368 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term256 Repty r R x) = (term257 Repty r R x).
Proof. exact (MK_COMB (@lem36367) (@lem36366 Repty r R x)). Qed.
Lemma lem36369 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem36370 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term258 Absty Repty R x dest mk r) = (term259 Absty Repty R x dest mk r).
Proof. exact (MK_COMB (@lem36368 Repty r R x) (@lem36369 Absty Repty dest mk r)). Qed.
Lemma lem36371 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term260 Absty Repty R dest mk r) = (term261 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem36370 Absty Repty R x dest mk r)). Qed.
Lemma lem36372 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem36373 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term249 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem36372 Repty) (@lem36371 Absty Repty R dest mk r)). Qed.
Lemma lem36374 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term248 Absty Repty R dest mk r) = (term249 Absty Repty R dest mk r)) = ((term147 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r)).
Proof. exact (MK_COMB (@lem36365 Absty Repty R dest mk r) (@lem36373 Absty Repty R dest mk r)). Qed.
Lemma lem36375 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term147 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r).
Proof. exact (EQ_MP (@lem36374 Absty Repty R dest mk r) (@lem36355 Absty Repty R dest mk r)). Qed.
Lemma lem36376 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term162 Absty Repty R dest mk) = (term263 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem36375 Absty Repty R dest mk r)). Qed.
Lemma lem36377 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem36378 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term264 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem36377 Repty) (@lem36376 Absty Repty R dest mk)). Qed.
Lemma lem36385 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term259 Absty Repty R x dest mk r) = (term259 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term259 Absty Repty R x dest mk r)). Qed.
Lemma lem36386 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term261 Absty Repty R dest mk r) = (term261 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem36385 Absty Repty R x dest mk r)). Qed.
Lemma lem36387 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem36388 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term262 Absty Repty R dest mk r) = (term262 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem36387 Repty) (@lem36386 Absty Repty R dest mk r)). Qed.
Lemma lem36389 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term263 Absty Repty R dest mk) = (term263 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem36388 Absty Repty R dest mk r)). Qed.
Lemma lem36390 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem36391 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term264 Absty Repty R dest mk) = (term264 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem36390 Repty) (@lem36389 Absty Repty R dest mk)). Qed.
Lemma lem36392 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term264 Absty Repty R dest mk).
Proof. exact (TRANS (@lem36378 Absty Repty R dest mk) (@lem36391 Absty Repty R dest mk)). Qed.
Lemma lem36393 {Absty Repty : Type'} (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term264 Absty Repty R dest mk.
Proof. exact (EQ_MP (@lem36392 Absty Repty R dest mk) (@lem36290 Absty Repty x' R dest mk h1)). Qed.
Lemma lem36476 {Absty Repty : Type'} (_1020 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term265 Absty Repty R dest mk _1020.
Proof. exact (@lem36393 Absty Repty x' R dest mk h1 _1020). Qed.
Lemma lem36477 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) : (term265 Absty Repty R dest mk _1020) = (term262 Absty Repty R dest mk _1020).
Proof. exact (eq_refl (term265 Absty Repty R dest mk _1020)). Qed.
Lemma lem36478 {Absty Repty : Type'} (_1020 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term262 Absty Repty R dest mk _1020.
Proof. exact (EQ_MP (@lem36477 Absty Repty R dest mk _1020) (@lem36476 Absty Repty _1020 x' R dest mk h1)). Qed.
Lemma lem36479 {Absty Repty : Type'} (_1020 : Repty -> Prop) (_1021 : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term266 Absty Repty R dest mk _1020 _1021.
Proof. exact (@lem36478 Absty Repty _1020 x' R dest mk h1 _1021). Qed.
Lemma lem36480 {Absty Repty : Type'} (R : type1402 Repty) (_1021 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) : (term266 Absty Repty R dest mk _1020 _1021) = (term259 Absty Repty R _1021 dest mk _1020).
Proof. exact (eq_refl (term266 Absty Repty R dest mk _1020 _1021)). Qed.
Lemma lem36523 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term300 Absty Repty dest mk R x) : term300 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36535 {Absty Repty : Type'} (_1021 : Repty) (_1020 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term259 Absty Repty R _1021 dest mk _1020.
Proof. exact (EQ_MP (@lem36480 Absty Repty R _1021 dest mk _1020) (@lem36479 Absty Repty _1020 _1021 x' R dest mk h1)). Qed.
Lemma lem36618 {Repty : Type'} (x : Repty -> Prop) : x = x.
Proof. exact (@lem21386 (Repty -> Prop) x). Qed.
Lemma lem36619 {Repty : Type'} (x : Repty -> Prop) : x = x.
Proof. exact (@lem36618 Repty x). Qed.
Lemma lem36620 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x) = (R x).
Proof. exact (@lem36619 Repty (R x)). Qed.
Lemma lem36621 {Repty : Type'} (R : type1402 Repty) (x : Repty) : term288 Repty R x.
Proof. exact (fun h0 : term289 Repty R x => @lem36620 Repty R x). Qed.
Lemma lem36623 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem36624 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term288 Repty R x) = ((R x) = (R x)).
Proof. exact (@lem36623 ((R x) = (R x))). Qed.
Lemma lem36625 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x) = (R x).
Proof. exact (EQ_MP (@lem36624 Repty R x) (@lem36621 Repty R x)). Qed.
Lemma lem36631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem36632 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : (term259 Absty Repty R _1021 dest mk _1020) = (term290 Absty Repty dest mk _1020 R _1021).
Proof. exact (@lem36631 ((term114 Absty Repty dest mk _1020) = _1020) (term139 Repty _1020 R _1021)). Qed.
Lemma lem36642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem36643 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : (term291 Absty Repty R _1021 dest mk _1020) = (term292 Absty Repty dest mk _1020 R _1021).
Proof. exact (MK_COMB (@lem36642) (@lem36632 Absty Repty dest mk _1020 R _1021)). Qed.
Lemma lem36653 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : (term290 Absty Repty dest mk _1020 R _1021) = (term290 Absty Repty dest mk _1020 R _1021).
Proof. exact (eq_refl (term290 Absty Repty dest mk _1020 R _1021)). Qed.
Lemma lem36654 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : ((term259 Absty Repty R _1021 dest mk _1020) = (term290 Absty Repty dest mk _1020 R _1021)) = ((term290 Absty Repty dest mk _1020 R _1021) = (term290 Absty Repty dest mk _1020 R _1021)).
Proof. exact (MK_COMB (@lem36643 Absty Repty dest mk _1020 R _1021) (@lem36653 Absty Repty dest mk _1020 R _1021)). Qed.
Lemma lem36656 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem36657 (x : Prop) : (x = x) = True.
Proof. exact (@lem36656 Prop x). Qed.
Lemma lem36658 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : ((term290 Absty Repty dest mk _1020 R _1021) = (term290 Absty Repty dest mk _1020 R _1021)) = True.
Proof. exact (@lem36657 (term290 Absty Repty dest mk _1020 R _1021)). Qed.
Lemma lem36659 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : ((term259 Absty Repty R _1021 dest mk _1020) = (term290 Absty Repty dest mk _1020 R _1021)) = True.
Proof. exact (TRANS (@lem36654 Absty Repty dest mk _1020 R _1021) (@lem36658 Absty Repty dest mk _1020 R _1021)). Qed.
Lemma lem36660 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : True = ((term259 Absty Repty R _1021 dest mk _1020) = (term290 Absty Repty dest mk _1020 R _1021)).
Proof. exact (SYM (@lem36659 Absty Repty dest mk _1020 R _1021)). Qed.
Lemma lem36661 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : (term259 Absty Repty R _1021 dest mk _1020) = (term290 Absty Repty dest mk _1020 R _1021).
Proof. exact (EQ_MP (@lem36660 Absty Repty dest mk _1020 R _1021) (@lem0)). Qed.
Lemma lem36662 {Absty Repty : Type'} (_1020 : Repty -> Prop) (_1021 : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term290 Absty Repty dest mk _1020 R _1021.
Proof. exact (EQ_MP (@lem36661 Absty Repty dest mk _1020 R _1021) (@lem36535 Absty Repty _1021 _1020 x' R dest mk h1)). Qed.
Lemma lem36664 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (or_elim (@lem20685 a) (fun h0 : a = True => @lem20762 b a h0) (fun h0 : a = False => @lem20761 b a h0)). Qed.
Lemma lem36665 {Absty Repty : Type'} (R : type1402 Repty) (_1021 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) : (term290 Absty Repty dest mk _1020 R _1021) = (term293 Absty Repty R _1021 dest mk _1020).
Proof. exact (@lem36664 (term139 Repty _1020 R _1021) ((term114 Absty Repty dest mk _1020) = _1020)). Qed.
Lemma lem36667 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem36668 {Repty : Type'} (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : (term294 Repty _1020 R _1021) = (_1020 = (R _1021)).
Proof. exact (@lem36667 (_1020 = (R _1021))). Qed.
Lemma lem36669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem36670 {Repty : Type'} (_1020 : Repty -> Prop) (R : type1402 Repty) (_1021 : Repty) : (term295 Repty _1020 R _1021) = (term296 Repty _1020 R _1021).
Proof. exact (MK_COMB (@lem36669) (@lem36668 Repty _1020 R _1021)). Qed.
Lemma lem36671 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) : ((term114 Absty Repty dest mk _1020) = _1020) = ((term114 Absty Repty dest mk _1020) = _1020).
Proof. exact (eq_refl ((term114 Absty Repty dest mk _1020) = _1020)). Qed.
Lemma lem36672 {Absty Repty : Type'} (R : type1402 Repty) (_1021 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) : (term293 Absty Repty R _1021 dest mk _1020) = (term297 Absty Repty R _1021 dest mk _1020).
Proof. exact (MK_COMB (@lem36670 Repty _1020 R _1021) (@lem36671 Absty Repty dest mk _1020)). Qed.
Lemma lem36673 {Absty Repty : Type'} (R : type1402 Repty) (_1021 : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (_1020 : Repty -> Prop) : (term290 Absty Repty dest mk _1020 R _1021) = (term297 Absty Repty R _1021 dest mk _1020).
Proof. exact (TRANS (@lem36665 Absty Repty R _1021 dest mk _1020) (@lem36672 Absty Repty R _1021 dest mk _1020)). Qed.
Lemma lem36676 {Absty Repty : Type'} (_1021 : Repty) (_1020 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term297 Absty Repty R _1021 dest mk _1020.
Proof. exact (EQ_MP (@lem36673 Absty Repty R _1021 dest mk _1020) (@lem36662 Absty Repty _1020 _1021 x' R dest mk h1)). Qed.
Lemma lem36677 {Absty Repty : Type'} (_1021 : Repty) (_1020 : Repty -> Prop) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term297 Absty Repty R _1021 dest mk _1020.
Proof. exact (@lem36676 Absty Repty _1021 _1020 x' R dest mk h1). Qed.
Lemma lem36678 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term298 Absty Repty dest mk R x.
Proof. exact (@lem36677 Absty Repty x (R x) x' R dest mk h1). Qed.
Lemma lem36681 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (@lem36678 Absty Repty x x' R dest mk h1 (@lem36625 Repty R x)). Qed.
Lemma lem36682 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (@lem36681 Absty Repty x x' R dest mk h1). Qed.
Lemma lem36683 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : term299 Absty Repty dest mk R x.
Proof. exact (fun h0 : term300 Absty Repty dest mk R x => @lem36682 Absty Repty x x' R dest mk h1). Qed.
Lemma lem36685 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem36686 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term299 Absty Repty dest mk R x) = ((term285 Absty Repty dest mk R x) = (R x)).
Proof. exact (@lem36685 ((term285 Absty Repty dest mk R x) = (R x))). Qed.
Lemma lem36687 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term239 Absty Repty x' R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (EQ_MP (@lem36686 Absty Repty dest mk R x) (@lem36683 Absty Repty x x' R dest mk h1)). Qed.
Lemma lem36690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem36692 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term300 Absty Repty dest mk R x) = (term1352 Absty Repty dest mk R x).
Proof. exact (@lem36690 ((term285 Absty Repty dest mk R x) = (R x))). Qed.
Lemma lem36695 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term300 Absty Repty dest mk R x) : term1352 Absty Repty dest mk R x.
Proof. exact (EQ_MP (@lem36692 Absty Repty dest mk R x) (@lem36523 Absty Repty dest mk R x h1)). Qed.
Lemma lem36698 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (@lem36695 Absty Repty dest mk R x h1 (@lem36687 Absty Repty x x' R dest mk h2)). Qed.
Lemma lem36699 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : term330.
Proof. exact (fun h0 : ~ False => @lem36698 Absty Repty x x' R dest mk h1 h2). Qed.
Lemma lem36701 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem36702 : term330 = False.
Proof. exact (@lem36701 False). Qed.
Lemma lem36703 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (EQ_MP (@lem36702) (@lem36699 Absty Repty x x' R dest mk h1 h2)). Qed.
Lemma lem36704 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : (term300 Absty Repty dest mk R x) = False.
Proof. exact (prop_ext (fun h3 : term300 Absty Repty dest mk R x => @lem36703 Absty Repty x x' R dest mk h1 h2) (fun h3 : False => @lem36523 Absty Repty dest mk R x h1)). Qed.
Lemma lem36705 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (EQ_MP (@lem36704 Absty Repty x x' R dest mk h1 h2) (@lem36523 Absty Repty dest mk R x h1)). Qed.
Lemma lem36706 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : (term300 Absty Repty dest mk R x) = False.
Proof. exact (prop_ext (fun h3 : term300 Absty Repty dest mk R x => @lem36705 Absty Repty x x' R dest mk h1 h2) (fun h3 : False => @lem36338 Absty Repty dest mk R x h1)). Qed.
Lemma lem36707 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (EQ_MP (@lem36706 Absty Repty x x' R dest mk h1 h2) (@lem36338 Absty Repty dest mk R x h1)). Qed.
Lemma lem36708 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : (term300 Absty Repty dest mk R x) = False.
Proof. exact (prop_ext (fun h3 : term300 Absty Repty dest mk R x => @lem36707 Absty Repty x x' R dest mk h1 h2) (fun h3 : False => @lem36338 Absty Repty dest mk R x h1)). Qed.
Lemma lem36709 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (EQ_MP (@lem36708 Absty Repty x x' R dest mk h1 h2) (@lem36338 Absty Repty dest mk R x h1)). Qed.
Lemma lem36710 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : (term239 Absty Repty x' R dest mk) = False.
Proof. exact (prop_ext (fun h3 : term239 Absty Repty x' R dest mk => @lem36709 Absty Repty x x' R dest mk h1 h2) (fun h3 : False => @lem36289 Absty Repty x' R dest mk h2)). Qed.
Lemma lem36711 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (EQ_MP (@lem36710 Absty Repty x x' R dest mk h1 h2) (@lem36289 Absty Repty x' R dest mk h2)). Qed.
Lemma lem36712 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : (term300 Absty Repty dest mk R x) = False.
Proof. exact (prop_ext (fun h3 : term300 Absty Repty dest mk R x => @lem36711 Absty Repty x x' R dest mk h1 h2) (fun h3 : False => @lem36232 Absty Repty dest mk R x h1)). Qed.
Lemma lem36713 {Absty Repty : Type'} (x : Repty) (x' : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term300 Absty Repty dest mk R x) (h2 : term239 Absty Repty x' R dest mk) : False.
Proof. exact (EQ_MP (@lem36712 Absty Repty x x' R dest mk h1 h2) (@lem36232 Absty Repty dest mk R x h1)). Qed.
Lemma lem36714 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term300 Absty Repty dest mk R x) : False.
Proof. exact (ex_elim (@lem35709 Absty Repty R dest mk h1) (fun x' : type684 Repty => fun h0 : term241 Absty Repty R dest mk x' => @lem36713 Absty Repty x x' R dest mk h2 h0)). Qed.
Lemma lem36715 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term300 Absty Repty dest mk R x) : (term300 Absty Repty dest mk R x) = False.
Proof. exact (prop_ext (fun h3 : term300 Absty Repty dest mk R x => @lem36714 Absty Repty dest mk R x h1 h2) (fun h3 : False => @lem36002 Absty Repty dest mk R x h2)). Qed.
Lemma lem36716 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term300 Absty Repty dest mk R x) : False.
Proof. exact (EQ_MP (@lem36715 Absty Repty dest mk R x h1 h2) (@lem36002 Absty Repty dest mk R x h2)). Qed.
Lemma lem36717 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term300 Absty Repty dest mk R x) : (term300 Absty Repty dest mk R x) = False.
Proof. exact (prop_ext (fun h3 : term300 Absty Repty dest mk R x => @lem36716 Absty Repty dest mk R x h1 h2) (fun h3 : False => @lem35061 Absty Repty dest mk R x h2)). Qed.
Lemma lem36718 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term72 Absty Repty R dest mk) (h2 : term300 Absty Repty dest mk R x) : False.
Proof. exact (EQ_MP (@lem36717 Absty Repty dest mk R x h1 h2) (@lem35061 Absty Repty dest mk R x h2)). Qed.
Lemma lem36719 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term1319 Absty Repty dest mk R x.
Proof. exact (fun h0 : term300 Absty Repty dest mk R x => @lem36718 Absty Repty dest mk R x h1 h0). Qed.
Lemma lem36720 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (EQ_MP (@lem35060 Absty Repty dest mk R x) (@lem36719 Absty Repty x R dest mk h1)). Qed.
Lemma lem36721 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term1326 Absty Repty dest mk R x.
Proof. exact (fun h0 : term74 Absty Repty mk R => @lem36720 Absty Repty x R dest mk h1). Qed.
Lemma lem36722 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1328 Absty Repty dest mk R x.
Proof. exact (fun h0 : term72 Absty Repty R dest mk => @lem36721 Absty Repty x R dest mk h0). Qed.
Lemma lem36723 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1330 Absty Repty dest mk R x.
Proof. exact (fun h0 : term73 Absty Repty mk dest => @lem36722 Absty Repty dest mk R x). Qed.
Lemma lem36724 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1332 Absty Repty dest mk R x.
Proof. exact (fun h0 : term71 Repty R => @lem36723 Absty Repty dest mk R x). Qed.
Lemma lem36725 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1334 Absty Repty dest mk R x.
Proof. exact (fun h0 : term69 Repty R => @lem36724 Absty Repty dest mk R x). Qed.
Lemma lem36726 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1335 Absty Repty dest mk R x.
Proof. exact (fun h0 : term67 Repty R => @lem36725 Absty Repty dest mk R x). Qed.
Lemma lem36731 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1339 Absty Repty mk R x.
Proof. exact (fun dest : type1413 Absty Repty => @lem36726 Absty Repty dest mk R x). Qed.
Lemma lem36736 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : term1343 Absty Repty R x.
Proof. exact (fun mk : type862 Absty Repty => @lem36731 Absty Repty mk R x). Qed.
Lemma lem36741 {Absty Repty : Type'} (x : Repty) : term1347 Absty Repty x.
Proof. exact (fun R : type1402 Repty => @lem36736 Absty Repty R x). Qed.
Lemma lem36746 {Absty Repty : Type'} : term1351 Absty Repty.
Proof. exact (fun x : Repty => @lem36741 Absty Repty x). Qed.
Lemma lem36747 {Absty Repty : Type'} : term1350 Absty Repty.
Proof. exact (EQ_MP (@lem35050 Absty Repty) (@lem36746 Absty Repty)). Qed.
Lemma lem36748 {Absty Repty : Type'} (x : Repty) : term1353 Absty Repty x.
Proof. exact (@lem36747 Absty Repty x). Qed.
Lemma lem36749 {Absty Repty : Type'} (x : Repty) : (term1353 Absty Repty x) = (term1346 Absty Repty x).
Proof. exact (eq_refl (term1353 Absty Repty x)). Qed.
Lemma lem36750 {Absty Repty : Type'} (x : Repty) : term1346 Absty Repty x.
Proof. exact (EQ_MP (@lem36749 Absty Repty x) (@lem36748 Absty Repty x)). Qed.
Lemma lem36751 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) : term1354 Absty Repty x R.
Proof. exact (@lem36750 Absty Repty x R). Qed.
Lemma lem36752 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1354 Absty Repty x R) = (term1342 Absty Repty R x).
Proof. exact (eq_refl (term1354 Absty Repty x R)). Qed.
Lemma lem36753 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : term1342 Absty Repty R x.
Proof. exact (EQ_MP (@lem36752 Absty Repty R x) (@lem36751 Absty Repty x R)). Qed.
Lemma lem36754 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (mk : type862 Absty Repty) : term1355 Absty Repty R x mk.
Proof. exact (@lem36753 Absty Repty R x mk). Qed.
Lemma lem36755 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1355 Absty Repty R x mk) = (term1338 Absty Repty mk R x).
Proof. exact (eq_refl (term1355 Absty Repty R x mk)). Qed.
Lemma lem36756 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1338 Absty Repty mk R x.
Proof. exact (EQ_MP (@lem36755 Absty Repty mk R x) (@lem36754 Absty Repty R x mk)). Qed.
Lemma lem36757 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) : term1356 Absty Repty mk R x dest.
Proof. exact (@lem36756 Absty Repty mk R x dest). Qed.
Lemma lem36758 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1356 Absty Repty mk R x dest) = (term1320 Absty Repty dest mk R x).
Proof. exact (eq_refl (term1356 Absty Repty mk R x dest)). Qed.
Lemma lem36759 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1320 Absty Repty dest mk R x.
Proof. exact (EQ_MP (@lem36758 Absty Repty dest mk R x) (@lem36757 Absty Repty mk R x dest)). Qed.
Lemma lem36761 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1320 Absty Repty dest mk R x.
Proof. exact (@lem34711 Absty Repty dest mk R x (@lem36759 Absty Repty dest mk R x)). Qed.
Lemma lem36762 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1333 Absty Repty dest mk R x.
Proof. exact (@lem36761 Absty Repty dest mk R x (@lem23771 Repty R h1)). Qed.
Lemma lem36763 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) : term1331 Absty Repty dest mk R x.
Proof. exact (@lem36762 Absty Repty dest mk x R h2 (@lem23773 Repty R h1)). Qed.
Lemma lem36764 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) : term1329 Absty Repty dest mk R x.
Proof. exact (@lem36763 Absty Repty dest mk x R h2 h3 (@lem23775 Repty R h1)). Qed.
Lemma lem36765 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) : term1327 Absty Repty dest mk R x.
Proof. exact (@lem36764 Absty Repty dest mk x R h2 h3 h4 (@lem23777 Absty Repty mk dest h1)). Qed.
Lemma lem36766 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term1325 Absty Repty dest mk R x.
Proof. exact (@lem36765 Absty Repty x mk dest R h1 h2 h3 h4 (@lem23776 Absty Repty R dest mk h5)). Qed.
Lemma lem36767 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1319 Absty Repty dest mk R x.
Proof. exact (@lem36766 Absty Repty x R dest mk h1 h2 h4 h5 h6 (@lem23778 Absty Repty mk R h3)). Qed.
Lemma lem36768 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term300 Absty Repty dest mk R x) : False.
Proof. exact (@lem36767 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6 (@lem34695 Absty Repty dest mk R x h7)). Qed.
Lemma lem36769 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term300 Absty Repty dest mk R x) : (term300 Absty Repty dest mk R x) = False.
Proof. exact (prop_ext (fun h8 : term300 Absty Repty dest mk R x => @lem36768 Absty Repty dest mk R x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem34695 Absty Repty dest mk R x h7)). Qed.
Lemma lem36770 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term300 Absty Repty dest mk R x) : False.
Proof. exact (EQ_MP (@lem36769 Absty Repty dest mk R x h1 h2 h3 h4 h5 h6 h7) (@lem34695 Absty Repty dest mk R x h7)). Qed.
Lemma lem36771 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1319 Absty Repty dest mk R x.
Proof. exact (fun h0 : term300 Absty Repty dest mk R x => @lem36770 Absty Repty dest mk R x h1 h2 h3 h4 h5 h6 h0). Qed.
Lemma lem36772 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : (term285 Absty Repty dest mk R x) = (R x).
Proof. exact (EQ_MP (@lem34694 Absty Repty dest mk R x) (@lem36771 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem36774 {A B : Type'} (t : A -> B) : t = (term0 A B t).
Proof. exact (EQ_MP (@lem23465 A B t) (@lem23464 A B t)). Qed.
Lemma lem36775 {Repty : Type'} (t : Repty -> Prop) : t = (term403 Repty t).
Proof. exact (@lem36774 Repty Prop t). Qed.
Lemma lem36776 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x) = (term1357 Repty R x).
Proof. exact (@lem36775 Repty (R x)). Qed.
Lemma lem36777 {Repty : Type'} : (@ε Repty) = (@ε Repty).
Proof. exact (eq_refl (@ε Repty)). Qed.
Lemma lem36778 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1358 Repty R x) = (term1359 Repty R x).
Proof. exact (MK_COMB (@lem36777 Repty) (@lem36776 Repty R x)). Qed.
Lemma lem36779 {Repty : Type'} (R : type1402 Repty) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem36780 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1360 Repty R x) = (term1361 Repty R x).
Proof. exact (MK_COMB (@lem36779 Repty R) (@lem36778 Repty R x)). Qed.
Lemma lem36781 {Repty : Type'} (x : Repty) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem36782 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1316 Repty R x) = (term1362 Repty R x).
Proof. exact (MK_COMB (@lem36780 Repty R x) (@lem36781 Repty x)). Qed.
Lemma lem36783 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1362 Repty R x) = (term1316 Repty R x).
Proof. exact (SYM (@lem36782 Repty R x)). Qed.
Lemma lem36807 {Repty : Type'} (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1363 Repty R x.
Proof. exact (@lem23773 Repty R h1 x). Qed.
Lemma lem36808 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1363 Repty R x) = (term128 Repty R x).
Proof. exact (eq_refl (term1363 Repty R x)). Qed.
Lemma lem36809 {Repty : Type'} (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term128 Repty R x.
Proof. exact (EQ_MP (@lem36808 Repty R x) (@lem36807 Repty x R h1)). Qed.
Lemma lem36810 {Repty : Type'} (x : Repty) (y : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : term1364 Repty R x y.
Proof. exact (@lem36809 Repty x R h1 y). Qed.
Lemma lem36811 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : (term1364 Repty R x y) = ((R x y) = (R y x)).
Proof. exact (eq_refl (term1364 Repty R x y)). Qed.
Lemma lem36814 {Repty : Type'} (y : Repty) (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : (R x y) = (R y x).
Proof. exact (EQ_MP (@lem36811 Repty R y x) (@lem36810 Repty x y R h1)). Qed.
Lemma lem36815 {Repty : Type'} (y : Repty) (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : (R x y) = (R y x).
Proof. exact (@lem36814 Repty y x R h1). Qed.
Lemma lem36816 {Repty : Type'} (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : (term1362 Repty R x) = (term1365 Repty R x).
Proof. exact (@lem36815 Repty x (term1359 Repty R x) R h1). Qed.
Lemma lem36817 {Repty : Type'} (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) : (term1365 Repty R x) = (term1362 Repty R x).
Proof. exact (SYM (@lem36816 Repty x R h1)). Qed.
Lemma lem36818 {Repty : Type'} (P : Repty -> Prop) : (term1366 Repty P) = (ex P).
Proof. exact (@lem9425 Repty P). Qed.
Lemma lem36819 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1367 Repty R x) = (term1368 Repty R x).
Proof. exact (@lem36818 Repty (term1357 Repty R x)). Qed.
Lemma lem36820 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1367 Repty R x) = (term1365 Repty R x).
Proof. exact (eq_refl (term1367 Repty R x)). Qed.
Lemma lem36821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem36822 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1369 Repty R x) = (term1370 Repty R x).
Proof. exact (MK_COMB (@lem36821) (@lem36820 Repty R x)). Qed.
Lemma lem36823 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1368 Repty R x) = (term1368 Repty R x).
Proof. exact (eq_refl (term1368 Repty R x)). Qed.
Lemma lem36824 {Repty : Type'} (R : type1402 Repty) (x : Repty) : ((term1367 Repty R x) = (term1368 Repty R x)) = ((term1365 Repty R x) = (term1368 Repty R x)).
Proof. exact (MK_COMB (@lem36822 Repty R x) (@lem36823 Repty R x)). Qed.
Lemma lem36825 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1365 Repty R x) = (term1368 Repty R x).
Proof. exact (EQ_MP (@lem36824 Repty R x) (@lem36819 Repty R x)). Qed.
Lemma lem36826 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1368 Repty R x) = (term1365 Repty R x).
Proof. exact (SYM (@lem36825 Repty R x)). Qed.
Lemma lem36828 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem36829 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1368 Repty R x) = (term1371 Repty R x).
Proof. exact (@lem36828 (term1368 Repty R x)). Qed.
Lemma lem36830 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1371 Repty R x) = (term1368 Repty R x).
Proof. exact (SYM (@lem36829 Repty R x)). Qed.
Lemma lem36831 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1372 Repty R x.
Proof. exact (h1). Qed.
Lemma lem36834 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1373 Absty Repty dest mk R x) : term1373 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36835 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1374 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1373 Absty Repty dest mk R x => @lem36834 Absty Repty dest mk R x h0). Qed.
Lemma lem36836 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1374 Absty Repty dest mk R x) : term1374 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36837 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1373 Absty Repty dest mk R x) : term1373 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36838 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1373 Absty Repty dest mk R x) (h2 : term1374 Absty Repty dest mk R x) : term1373 Absty Repty dest mk R x.
Proof. exact (@lem36836 Absty Repty dest mk R x h2 (@lem36837 Absty Repty dest mk R x h1)). Qed.
Lemma lem36839 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1373 Absty Repty dest mk R x) : term1375 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1374 Absty Repty dest mk R x => @lem36838 Absty Repty dest mk R x h1 h0). Qed.
Lemma lem36840 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1374 Absty Repty dest mk R x) : term1374 Absty Repty dest mk R x.
Proof. exact (h1). Qed.
Lemma lem36841 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1373 Absty Repty dest mk R x) (h2 : term1374 Absty Repty dest mk R x) : term1373 Absty Repty dest mk R x.
Proof. exact (@lem36839 Absty Repty dest mk R x h1 (@lem36840 Absty Repty dest mk R x h2)). Qed.
Lemma lem36842 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term1374 Absty Repty dest mk R x) : term1374 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1373 Absty Repty dest mk R x => @lem36841 Absty Repty dest mk R x h0 h1). Qed.
Lemma lem36843 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1376 Absty Repty dest mk R x.
Proof. exact (fun h0 : term1374 Absty Repty dest mk R x => @lem36842 Absty Repty dest mk R x h0). Qed.
Lemma lem36846 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1374 Absty Repty dest mk R x.
Proof. exact (@lem36843 Absty Repty dest mk R x (@lem36835 Absty Repty dest mk R x)). Qed.
Lemma lem36847 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1374 Absty Repty dest mk R x.
Proof. exact (@lem36846 Absty Repty dest mk R x). Qed.
Lemma lem36925 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem36926 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1371 Repty R x) = (term1377 Repty R x).
Proof. exact (@lem36925 (term1372 Repty R x)). Qed.
Lemma lem36928 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem36929 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1377 Repty R x) = (term1368 Repty R x).
Proof. exact (@lem36928 (term1368 Repty R x)). Qed.
Lemma lem36934 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1371 Repty R x) = (term1368 Repty R x).
Proof. exact (TRANS (@lem36926 Repty R x) (@lem36929 Repty R x)). Qed.
Lemma lem36935 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term379 Absty Repty mk R) = (term379 Absty Repty mk R).
Proof. exact (eq_refl (term379 Absty Repty mk R)). Qed.
Lemma lem36936 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1378 Absty Repty mk R x) = (term1379 Absty Repty mk R x).
Proof. exact (MK_COMB (@lem36935 Absty Repty mk R) (@lem36934 Repty R x)). Qed.
Lemma lem36939 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (eq_refl (term84 Absty Repty R dest mk)). Qed.
Lemma lem36940 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1380 Absty Repty dest mk R x) = (term1381 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem36939 Absty Repty R dest mk) (@lem36936 Absty Repty mk R x)). Qed.
Lemma lem36943 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (eq_refl (term87 Absty Repty mk dest)). Qed.
Lemma lem36944 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1382 Absty Repty dest mk R x) = (term1383 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem36943 Absty Repty mk dest) (@lem36940 Absty Repty dest mk R x)). Qed.
Lemma lem36947 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (eq_refl (term90 Repty R)). Qed.
Lemma lem36948 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1384 Absty Repty dest mk R x) = (term1385 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem36947 Repty R) (@lem36944 Absty Repty dest mk R x)). Qed.
Lemma lem36951 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (eq_refl (term93 Repty R)). Qed.
Lemma lem36952 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1386 Absty Repty dest mk R x) = (term1387 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem36951 Repty R) (@lem36948 Absty Repty dest mk R x)). Qed.
Lemma lem36955 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (eq_refl (term96 Repty R)). Qed.
Lemma lem36956 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1373 Absty Repty dest mk R x) = (term1388 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem36955 Repty R) (@lem36952 Absty Repty dest mk R x)). Qed.
Lemma lem36959 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1389 Absty Repty mk R x) = (term1390 Absty Repty mk R x).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem36956 Absty Repty dest mk R x)). Qed.
Lemma lem36960 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem36961 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1391 Absty Repty mk R x) = (term1392 Absty Repty mk R x).
Proof. exact (MK_COMB (@lem36960 Absty Repty) (@lem36959 Absty Repty mk R x)). Qed.
Lemma lem36966 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1393 Absty Repty R x) = (term1394 Absty Repty R x).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem36961 Absty Repty mk R x)). Qed.
Lemma lem36967 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem36968 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1395 Absty Repty R x) = (term1396 Absty Repty R x).
Proof. exact (MK_COMB (@lem36967 Absty Repty) (@lem36966 Absty Repty R x)). Qed.
Lemma lem36973 {Absty Repty : Type'} (x : Repty) : (term1397 Absty Repty x) = (term1398 Absty Repty x).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem36968 Absty Repty R x)). Qed.
Lemma lem36974 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem36975 {Absty Repty : Type'} (x : Repty) : (term1399 Absty Repty x) = (term1400 Absty Repty x).
Proof. exact (MK_COMB (@lem36974 Repty) (@lem36973 Absty Repty x)). Qed.
Lemma lem36980 {Absty Repty : Type'} : (term1401 Absty Repty) = (term1402 Absty Repty).
Proof. exact (fun_ext (fun x : Repty => @lem36975 Absty Repty x)). Qed.
Lemma lem36981 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem36990 {Absty Repty : Type'} : (term1403 Absty Repty) = (term1404 Absty Repty).
Proof. exact (MK_COMB (@lem36981 Repty) (@lem36980 Absty Repty)). Qed.
Lemma lem36991 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (R x x') = (R x x').
Proof. exact (eq_refl (R x x')). Qed.
Lemma lem36992 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1357 Repty R x) = (term1357 Repty R x).
Proof. exact (fun_ext (fun x' : Repty => @lem36991 Repty R x x')). Qed.
Lemma lem36993 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem36994 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1368 Repty R x) = (term1368 Repty R x).
Proof. exact (MK_COMB (@lem36993 Repty) (@lem36992 Repty R x)). Qed.
Lemma lem36999 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (y : Repty) : (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))) = (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y))).
Proof. exact (eq_refl (((term110 Absty Repty mk R x) = (term110 Absty Repty mk R y)) = ((R x) = (R y)))). Qed.
Lemma lem37000 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term111 Absty Repty mk x R) = (term111 Absty Repty mk x R).
Proof. exact (fun_ext (fun y : Repty => @lem36999 Absty Repty mk x R y)). Qed.
Lemma lem37001 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37002 {Absty Repty : Type'} (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) : (term112 Absty Repty mk x R) = (term112 Absty Repty mk x R).
Proof. exact (MK_COMB (@lem37001 Repty) (@lem37000 Absty Repty mk x R)). Qed.
Lemma lem37003 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term113 Absty Repty mk R) = (term113 Absty Repty mk R).
Proof. exact (fun_ext (fun x : Repty => @lem37002 Absty Repty mk x R)). Qed.
Lemma lem37004 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37005 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term74 Absty Repty mk R) = (term74 Absty Repty mk R).
Proof. exact (MK_COMB (@lem37004 Repty) (@lem37003 Absty Repty mk R)). Qed.
Lemma lem37006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem37007 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) : (term379 Absty Repty mk R) = (term379 Absty Repty mk R).
Proof. exact (MK_COMB (@lem37006) (@lem37005 Absty Repty mk R)). Qed.
Lemma lem37008 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1379 Absty Repty mk R x) = (term1379 Absty Repty mk R x).
Proof. exact (MK_COMB (@lem37007 Absty Repty mk R) (@lem36994 Repty R x)). Qed.
Lemma lem37009 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem37010 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem37011 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem37010 Repty r R x)). Qed.
Lemma lem37012 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem37013 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem37012 Repty) (@lem37011 Repty r R)). Qed.
Lemma lem37014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem37015 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term117 Repty r R) = (term117 Repty r R).
Proof. exact (MK_COMB (@lem37014) (@lem37013 Repty r R)). Qed.
Lemma lem37016 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)).
Proof. exact (MK_COMB (@lem37015 Repty r R) (@lem37009 Absty Repty dest mk r)). Qed.
Lemma lem37017 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term118 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37016 Absty Repty R dest mk r)). Qed.
Lemma lem37018 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37019 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term72 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37018 Repty) (@lem37017 Absty Repty R dest mk)). Qed.
Lemma lem37020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem37021 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term84 Absty Repty R dest mk) = (term84 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37020) (@lem37019 Absty Repty R dest mk)). Qed.
Lemma lem37022 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1381 Absty Repty dest mk R x) = (term1381 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem37021 Absty Repty R dest mk) (@lem37008 Absty Repty mk R x)). Qed.
Lemma lem37023 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (a : Absty) : ((term119 Absty Repty mk dest a) = a) = ((term119 Absty Repty mk dest a) = a).
Proof. exact (eq_refl ((term119 Absty Repty mk dest a) = a)). Qed.
Lemma lem37024 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term120 Absty Repty mk dest) = (term120 Absty Repty mk dest).
Proof. exact (fun_ext (fun a : Absty => @lem37023 Absty Repty mk dest a)). Qed.
Lemma lem37025 {Absty : Type'} : (@all Absty) = (@all Absty).
Proof. exact (eq_refl (@all Absty)). Qed.
Lemma lem37026 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term73 Absty Repty mk dest) = (term73 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem37025 Absty) (@lem37024 Absty Repty mk dest)). Qed.
Lemma lem37027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem37028 {Absty Repty : Type'} (mk : type862 Absty Repty) (dest : type1413 Absty Repty) : (term87 Absty Repty mk dest) = (term87 Absty Repty mk dest).
Proof. exact (MK_COMB (@lem37027) (@lem37026 Absty Repty mk dest)). Qed.
Lemma lem37029 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1383 Absty Repty dest mk R x) = (term1383 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem37028 Absty Repty mk dest) (@lem37022 Absty Repty dest mk R x)). Qed.
Lemma lem37038 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) (z : Repty) : (term121 Repty y R x z) = (term121 Repty y R x z).
Proof. exact (eq_refl (term121 Repty y R x z)). Qed.
Lemma lem37039 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term122 Repty y R x) = (term122 Repty y R x).
Proof. exact (fun_ext (fun z : Repty => @lem37038 Repty y R x z)). Qed.
Lemma lem37040 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37041 {Repty : Type'} (y : Repty) (R : type1402 Repty) (x : Repty) : (term123 Repty y R x) = (term123 Repty y R x).
Proof. exact (MK_COMB (@lem37040 Repty) (@lem37039 Repty y R x)). Qed.
Lemma lem37042 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term124 Repty R x) = (term124 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem37041 Repty y R x)). Qed.
Lemma lem37043 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37044 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term125 Repty R x) = (term125 Repty R x).
Proof. exact (MK_COMB (@lem37043 Repty) (@lem37042 Repty R x)). Qed.
Lemma lem37045 {Repty : Type'} (R : type1402 Repty) : (term126 Repty R) = (term126 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem37044 Repty R x)). Qed.
Lemma lem37046 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37047 {Repty : Type'} (R : type1402 Repty) : (term71 Repty R) = (term71 Repty R).
Proof. exact (MK_COMB (@lem37046 Repty) (@lem37045 Repty R)). Qed.
Lemma lem37048 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem37049 {Repty : Type'} (R : type1402 Repty) : (term90 Repty R) = (term90 Repty R).
Proof. exact (MK_COMB (@lem37048) (@lem37047 Repty R)). Qed.
Lemma lem37050 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1385 Absty Repty dest mk R x) = (term1385 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem37049 Repty R) (@lem37029 Absty Repty dest mk R x)). Qed.
Lemma lem37055 {Repty : Type'} (R : type1402 Repty) (y : Repty) (x : Repty) : ((R x y) = (R y x)) = ((R x y) = (R y x)).
Proof. exact (eq_refl ((R x y) = (R y x))). Qed.
Lemma lem37056 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term127 Repty R x) = (term127 Repty R x).
Proof. exact (fun_ext (fun y : Repty => @lem37055 Repty R y x)). Qed.
Lemma lem37057 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37058 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term128 Repty R x) = (term128 Repty R x).
Proof. exact (MK_COMB (@lem37057 Repty) (@lem37056 Repty R x)). Qed.
Lemma lem37059 {Repty : Type'} (R : type1402 Repty) : (term129 Repty R) = (term129 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem37058 Repty R x)). Qed.
Lemma lem37060 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37061 {Repty : Type'} (R : type1402 Repty) : (term69 Repty R) = (term69 Repty R).
Proof. exact (MK_COMB (@lem37060 Repty) (@lem37059 Repty R)). Qed.
Lemma lem37062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem37063 {Repty : Type'} (R : type1402 Repty) : (term93 Repty R) = (term93 Repty R).
Proof. exact (MK_COMB (@lem37062) (@lem37061 Repty R)). Qed.
Lemma lem37064 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1387 Absty Repty dest mk R x) = (term1387 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem37063 Repty R) (@lem37050 Absty Repty dest mk R x)). Qed.
Lemma lem37065 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem37066 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term130 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem37065 Repty R x)). Qed.
Lemma lem37067 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37068 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term67 Repty R).
Proof. exact (MK_COMB (@lem37067 Repty) (@lem37066 Repty R)). Qed.
Lemma lem37069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem37070 {Repty : Type'} (R : type1402 Repty) : (term96 Repty R) = (term96 Repty R).
Proof. exact (MK_COMB (@lem37069) (@lem37068 Repty R)). Qed.
Lemma lem37071 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1388 Absty Repty dest mk R x) = (term1388 Absty Repty dest mk R x).
Proof. exact (MK_COMB (@lem37070 Repty R) (@lem37064 Absty Repty dest mk R x)). Qed.
Lemma lem37072 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1390 Absty Repty mk R x) = (term1390 Absty Repty mk R x).
Proof. exact (fun_ext (fun dest : type1413 Absty Repty => @lem37071 Absty Repty dest mk R x)). Qed.
Lemma lem37073 {Absty Repty : Type'} : (@all (Absty -> Repty -> Prop)) = (@all (Absty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Absty -> Repty -> Prop))). Qed.
Lemma lem37074 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1392 Absty Repty mk R x) = (term1392 Absty Repty mk R x).
Proof. exact (MK_COMB (@lem37073 Absty Repty) (@lem37072 Absty Repty mk R x)). Qed.
Lemma lem37075 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1394 Absty Repty R x) = (term1394 Absty Repty R x).
Proof. exact (fun_ext (fun mk : type862 Absty Repty => @lem37074 Absty Repty mk R x)). Qed.
Lemma lem37076 {Absty Repty : Type'} : (@all ((Repty -> Prop) -> Absty)) = (@all ((Repty -> Prop) -> Absty)).
Proof. exact (eq_refl (@all ((Repty -> Prop) -> Absty))). Qed.
Lemma lem37077 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1396 Absty Repty R x) = (term1396 Absty Repty R x).
Proof. exact (MK_COMB (@lem37076 Absty Repty) (@lem37075 Absty Repty R x)). Qed.
Lemma lem37078 {Absty Repty : Type'} (x : Repty) : (term1398 Absty Repty x) = (term1398 Absty Repty x).
Proof. exact (fun_ext (fun R : type1402 Repty => @lem37077 Absty Repty R x)). Qed.
Lemma lem37079 {Repty : Type'} : (@all (Repty -> Repty -> Prop)) = (@all (Repty -> Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Repty -> Prop))). Qed.
Lemma lem37080 {Absty Repty : Type'} (x : Repty) : (term1400 Absty Repty x) = (term1400 Absty Repty x).
Proof. exact (MK_COMB (@lem37079 Repty) (@lem37078 Absty Repty x)). Qed.
Lemma lem37081 {Absty Repty : Type'} : (term1402 Absty Repty) = (term1402 Absty Repty).
Proof. exact (fun_ext (fun x : Repty => @lem37080 Absty Repty x)). Qed.
Lemma lem37082 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37083 {Absty Repty : Type'} : (term1404 Absty Repty) = (term1404 Absty Repty).
Proof. exact (MK_COMB (@lem37082 Repty) (@lem37081 Absty Repty)). Qed.
Lemma lem37198 {Absty Repty : Type'} : (term1403 Absty Repty) = (term1404 Absty Repty).
Proof. exact (TRANS (@lem36990 Absty Repty) (@lem37083 Absty Repty)). Qed.
Lemma lem37199 {Absty Repty : Type'} : (term1404 Absty Repty) = (term1403 Absty Repty).
Proof. exact (SYM (@lem37198 Absty Repty)). Qed.
Lemma lem37200 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term67 Repty R.
Proof. exact (h1). Qed.
Lemma lem37204 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term72 Absty Repty R dest mk.
Proof. exact (h1). Qed.
Lemma lem37207 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem37208 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1368 Repty R x) = (term1371 Repty R x).
Proof. exact (@lem37207 (term1368 Repty R x)). Qed.
Lemma lem37209 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1371 Repty R x) = (term1368 Repty R x).
Proof. exact (SYM (@lem37208 Repty R x)). Qed.
Lemma lem37210 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1372 Repty R x.
Proof. exact (h1). Qed.
Lemma lem37211 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (R x x).
Proof. exact (eq_refl (R x x)). Qed.
Lemma lem37212 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term130 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem37211 Repty R x)). Qed.
Lemma lem37213 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37222 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term67 Repty R).
Proof. exact (MK_COMB (@lem37213 Repty) (@lem37212 Repty R)). Qed.
Lemma lem37223 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term67 Repty R.
Proof. exact (EQ_MP (@lem37222 Repty R) (@lem37200 Repty R h1)). Qed.
Lemma lem37608 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (r = (R x)) = (r = (R x)).
Proof. exact (eq_refl (r = (R x))). Qed.
Lemma lem37609 {Repty : Type'} (P : Repty -> Prop) : (term133 Repty P) = (term134 Repty P).
Proof. exact (@lem18394 Repty P). Qed.
Lemma lem37610 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term136 Repty r R).
Proof. exact (@lem37609 Repty (term115 Repty r R)). Qed.
Lemma lem37611 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem37612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem37614 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term138 Repty r R x) = (term139 Repty r R x).
Proof. exact (MK_COMB (@lem37612) (@lem37611 Repty r R x)). Qed.
Lemma lem37615 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term140 Repty r R) = (term141 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem37614 Repty r R x)). Qed.
Lemma lem37616 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem37617 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term136 Repty r R) = (term142 Repty r R).
Proof. exact (MK_COMB (@lem37616 Repty) (@lem37615 Repty r R)). Qed.
Lemma lem37618 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term135 Repty r R) = (term142 Repty r R).
Proof. exact (TRANS (@lem37610 Repty r R) (@lem37617 Repty r R)). Qed.
Lemma lem37619 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term115 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem37608 Repty r R x)). Qed.
Lemma lem37620 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem37621 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term116 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem37620 Repty) (@lem37619 Repty r R)). Qed.
Lemma lem37622 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem37623 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term114 Absty Repty dest mk r) = r) = ((term114 Absty Repty dest mk r) = r).
Proof. exact (eq_refl ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem37624 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem37625 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term144 Repty r R) = (term145 Repty r R).
Proof. exact (MK_COMB (@lem37624) (@lem37618 Repty r R)). Qed.
Lemma lem37626 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term146 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37625 Repty r R) (@lem37623 Absty Repty dest mk r)). Qed.
Lemma lem37627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem37628 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term148 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem37627) (@lem37621 Repty r R)). Qed.
Lemma lem37629 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37628 Repty r R) (@lem37622 Absty Repty dest mk r)). Qed.
Lemma lem37630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem37631 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term150 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37630) (@lem37629 Absty Repty R dest mk r)). Qed.
Lemma lem37632 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term151 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37631 Absty Repty R dest mk r) (@lem37626 Absty Repty R dest mk r)). Qed.
Lemma lem37633 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term151 Absty Repty R dest mk r).
Proof. exact (@lem17784 (term116 Repty r R) ((term114 Absty Repty dest mk r) = r)). Qed.
Lemma lem37634 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term116 Repty r R) = ((term114 Absty Repty dest mk r) = r)) = (term152 Absty Repty R dest mk r).
Proof. exact (TRANS (@lem37633 Absty Repty R dest mk r) (@lem37632 Absty Repty R dest mk r)). Qed.
Lemma lem37635 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term118 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37634 Absty Repty R dest mk r)). Qed.
Lemma lem37636 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37637 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37636 Repty) (@lem37635 Absty Repty R dest mk)). Qed.
Lemma lem37639 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem37640 {Repty : Type'} (P : type686 Repty) (Q : type686 Repty) : (term157 Repty P Q) = (term158 Repty P Q).
Proof. exact (@lem37639 (Repty -> Prop) P Q). Qed.
Lemma lem37641 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk).
Proof. exact (@lem37640 Repty (term161 Absty Repty R dest mk) (term162 Absty Repty R dest mk)). Qed.
Lemma lem37642 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem37643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem37644 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term164 Absty Repty R dest mk r) = (term150 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37643) (@lem37642 Absty Repty R dest mk r)). Qed.
Lemma lem37645 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem37646 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term166 Absty Repty R dest mk r) = (term152 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37644 Absty Repty R dest mk r) (@lem37645 Absty Repty R dest mk r)). Qed.
Lemma lem37647 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term167 Absty Repty R dest mk) = (term153 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37646 Absty Repty R dest mk r)). Qed.
Lemma lem37648 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37649 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term159 Absty Repty R dest mk) = (term154 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37648 Repty) (@lem37647 Absty Repty R dest mk)). Qed.
Lemma lem37650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem37651 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term168 Absty Repty R dest mk) = (term169 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37650) (@lem37649 Absty Repty R dest mk)). Qed.
Lemma lem37652 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term163 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (eq_refl (term163 Absty Repty R dest mk r)). Qed.
Lemma lem37653 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term170 Absty Repty R dest mk) = (term161 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37652 Absty Repty R dest mk r)). Qed.
Lemma lem37654 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37655 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term171 Absty Repty R dest mk) = (term172 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37654 Repty) (@lem37653 Absty Repty R dest mk)). Qed.
Lemma lem37656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem37657 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term173 Absty Repty R dest mk) = (term174 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37656) (@lem37655 Absty Repty R dest mk)). Qed.
Lemma lem37658 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term165 Absty Repty R dest mk r) = (term147 Absty Repty R dest mk r).
Proof. exact (eq_refl (term165 Absty Repty R dest mk r)). Qed.
Lemma lem37659 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term175 Absty Repty R dest mk) = (term162 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37658 Absty Repty R dest mk r)). Qed.
Lemma lem37660 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37661 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term176 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37660 Repty) (@lem37659 Absty Repty R dest mk)). Qed.
Lemma lem37662 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term160 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37657 Absty Repty R dest mk) (@lem37661 Absty Repty R dest mk)). Qed.
Lemma lem37663 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term159 Absty Repty R dest mk) = (term160 Absty Repty R dest mk)) = ((term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem37651 Absty Repty R dest mk) (@lem37662 Absty Repty R dest mk)). Qed.
Lemma lem37664 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term178 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem37663 Absty Repty R dest mk) (@lem37641 Absty Repty R dest mk)). Qed.
Lemma lem37770 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem37771 {Repty : Type'} (P : Repty -> Prop) (Q : Prop) : (term179 Repty P Q) = (term180 Repty P Q).
Proof. exact (@lem37770 Repty P Q). Qed.
Lemma lem37772 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r).
Proof. exact (@lem37771 Repty (term115 Repty r R) (term143 Absty Repty dest mk r)). Qed.
Lemma lem37773 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem37774 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term183 Repty r R) = (term115 Repty r R).
Proof. exact (fun_ext (fun x : Repty => @lem37773 Repty r R x)). Qed.
Lemma lem37775 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem37776 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term184 Repty r R) = (term116 Repty r R).
Proof. exact (MK_COMB (@lem37775 Repty) (@lem37774 Repty r R)). Qed.
Lemma lem37777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem37778 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) : (term185 Repty r R) = (term148 Repty r R).
Proof. exact (MK_COMB (@lem37777) (@lem37776 Repty r R)). Qed.
Lemma lem37779 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem37780 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term181 Absty Repty R dest mk r) = (term149 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37778 Repty r R) (@lem37779 Absty Repty dest mk r)). Qed.
Lemma lem37781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem37782 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term186 Absty Repty R dest mk r) = (term187 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37781) (@lem37780 Absty Repty R dest mk r)). Qed.
Lemma lem37783 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term137 Repty r R x) = (r = (R x)).
Proof. exact (eq_refl (term137 Repty r R x)). Qed.
Lemma lem37784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem37785 {Repty : Type'} (r : Repty -> Prop) (R : type1402 Repty) (x : Repty) : (term188 Repty r R x) = (term189 Repty r R x).
Proof. exact (MK_COMB (@lem37784) (@lem37783 Repty r R x)). Qed.
Lemma lem37786 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term143 Absty Repty dest mk r) = (term143 Absty Repty dest mk r).
Proof. exact (eq_refl (term143 Absty Repty dest mk r)). Qed.
Lemma lem37787 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term190 Absty Repty R x dest mk r) = (term191 Absty Repty R x dest mk r).
Proof. exact (MK_COMB (@lem37785 Repty r R x) (@lem37786 Absty Repty dest mk r)). Qed.
Lemma lem37788 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term192 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem37787 Absty Repty R x dest mk r)). Qed.
Lemma lem37789 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem37790 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term182 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37789 Repty) (@lem37788 Absty Repty R dest mk r)). Qed.
Lemma lem37791 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : ((term181 Absty Repty R dest mk r) = (term182 Absty Repty R dest mk r)) = ((term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r)).
Proof. exact (MK_COMB (@lem37782 Absty Repty R dest mk r) (@lem37790 Absty Repty R dest mk r)). Qed.
Lemma lem37792 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term149 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (EQ_MP (@lem37791 Absty Repty R dest mk r) (@lem37772 Absty Repty R dest mk r)). Qed.
Lemma lem37793 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term161 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37792 Absty Repty R dest mk r)). Qed.
Lemma lem37794 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37795 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37794 Repty) (@lem37793 Absty Repty R dest mk)). Qed.
Lemma lem37797 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem37798 {Repty : Type'} (P : type672 Repty) : (term199 Repty P) = (term200 Repty P).
Proof. exact (@lem37797 (Repty -> Prop) Repty P). Qed.
Lemma lem37799 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk).
Proof. exact (@lem37798 Repty (term203 Absty Repty R dest mk)). Qed.
Lemma lem37800 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem37801 {Repty : Type'} (x : Repty) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem37802 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) (x : Repty) : (term205 Absty Repty R dest mk r x) = (term206 Absty Repty R dest mk r x).
Proof. exact (MK_COMB (@lem37800 Absty Repty R dest mk r) (@lem37801 Repty x)). Qed.
Lemma lem37803 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term206 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term206 Absty Repty R dest mk r x)). Qed.
Lemma lem37804 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term205 Absty Repty R dest mk r x) = (term191 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem37802 Absty Repty R dest mk r x) (@lem37803 Absty Repty R x dest mk r)). Qed.
Lemma lem37805 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term207 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (fun_ext (fun x : Repty => @lem37804 Absty Repty R x dest mk r)). Qed.
Lemma lem37806 {Repty : Type'} : (@ex Repty) = (@ex Repty).
Proof. exact (eq_refl (@ex Repty)). Qed.
Lemma lem37807 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term208 Absty Repty R dest mk r) = (term194 Absty Repty R dest mk r).
Proof. exact (MK_COMB (@lem37806 Repty) (@lem37805 Absty Repty R dest mk r)). Qed.
Lemma lem37808 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term209 Absty Repty R dest mk) = (term195 Absty Repty R dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37807 Absty Repty R dest mk r)). Qed.
Lemma lem37809 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37810 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term201 Absty Repty R dest mk) = (term196 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37809 Repty) (@lem37808 Absty Repty R dest mk)). Qed.
Lemma lem37811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem37812 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term210 Absty Repty R dest mk) = (term211 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37811) (@lem37810 Absty Repty R dest mk)). Qed.
Lemma lem37813 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term204 Absty Repty R dest mk r) = (term193 Absty Repty R dest mk r).
Proof. exact (eq_refl (term204 Absty Repty R dest mk r)). Qed.
Lemma lem37814 {Repty : Type'} (x : type684 Repty) (r : Repty -> Prop) : (x r) = (x r).
Proof. exact (eq_refl (x r)). Qed.
Lemma lem37815 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : type684 Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term213 Absty Repty R dest mk x r).
Proof. exact (MK_COMB (@lem37813 Absty Repty R dest mk r) (@lem37814 Repty x r)). Qed.
Lemma lem37816 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term213 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (eq_refl (term213 Absty Repty R dest mk x r)). Qed.
Lemma lem37817 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (r : Repty -> Prop) : (term212 Absty Repty R dest mk x r) = (term214 Absty Repty R x dest mk r).
Proof. exact (TRANS (@lem37815 Absty Repty R dest mk x r) (@lem37816 Absty Repty R x dest mk r)). Qed.
Lemma lem37818 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term215 Absty Repty R dest mk x) = (term216 Absty Repty R x dest mk).
Proof. exact (fun_ext (fun r : Repty -> Prop => @lem37817 Absty Repty R x dest mk r)). Qed.
Lemma lem37819 {Repty : Type'} : (@all (Repty -> Prop)) = (@all (Repty -> Prop)).
Proof. exact (eq_refl (@all (Repty -> Prop))). Qed.
Lemma lem37820 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term217 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem37819 Repty) (@lem37818 Absty Repty R x dest mk)). Qed.
Lemma lem37821 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term219 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem37820 Absty Repty R x dest mk)). Qed.
Lemma lem37822 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem37823 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term202 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37822 Repty) (@lem37821 Absty Repty R dest mk)). Qed.
Lemma lem37824 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term201 Absty Repty R dest mk) = (term202 Absty Repty R dest mk)) = ((term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem37812 Absty Repty R dest mk) (@lem37823 Absty Repty R dest mk)). Qed.
Lemma lem37825 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term196 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem37824 Absty Repty R dest mk) (@lem37799 Absty Repty R dest mk)). Qed.
Lemma lem37826 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term172 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (TRANS (@lem37795 Absty Repty R dest mk) (@lem37825 Absty Repty R dest mk)). Qed.
Lemma lem37827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem37828 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term174 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37827) (@lem37826 Absty Repty R dest mk)). Qed.
Lemma lem37829 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem37830 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37828 Absty Repty R dest mk) (@lem37829 Absty Repty R dest mk)). Qed.
Lemma lem37832 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem37833 {Repty : Type'} (P : type162 Repty) (Q : Prop) : (term226 Repty P Q) = (term227 Repty P Q).
Proof. exact (@lem37832 (type684 Repty) P Q). Qed.
Lemma lem37834 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk).
Proof. exact (@lem37833 Repty (term220 Absty Repty R dest mk) (term177 Absty Repty R dest mk)). Qed.
Lemma lem37835 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem37836 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term231 Absty Repty R dest mk) = (term220 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem37835 Absty Repty R x dest mk)). Qed.
Lemma lem37837 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem37838 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term232 Absty Repty R dest mk) = (term221 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37837 Repty) (@lem37836 Absty Repty R dest mk)). Qed.
Lemma lem37839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem37840 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term233 Absty Repty R dest mk) = (term222 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37839) (@lem37838 Absty Repty R dest mk)). Qed.
Lemma lem37841 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem37842 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term228 Absty Repty R dest mk) = (term223 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37840 Absty Repty R dest mk) (@lem37841 Absty Repty R dest mk)). Qed.
Lemma lem37843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem37844 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term234 Absty Repty R dest mk) = (term235 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37843) (@lem37842 Absty Repty R dest mk)). Qed.
Lemma lem37845 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term230 Absty Repty R dest mk x) = (term218 Absty Repty R x dest mk).
Proof. exact (eq_refl (term230 Absty Repty R dest mk x)). Qed.
Lemma lem37846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem37847 {Absty Repty : Type'} (R : type1402 Repty) (x : type684 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term236 Absty Repty R dest mk x) = (term237 Absty Repty R x dest mk).
Proof. exact (MK_COMB (@lem37846) (@lem37845 Absty Repty R x dest mk)). Qed.
Lemma lem37848 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term177 Absty Repty R dest mk) = (term177 Absty Repty R dest mk).
Proof. exact (eq_refl (term177 Absty Repty R dest mk)). Qed.
Lemma lem37849 {Absty Repty : Type'} (x : type684 Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term238 Absty Repty x R dest mk) = (term239 Absty Repty x R dest mk).
Proof. exact (MK_COMB (@lem37847 Absty Repty R x dest mk) (@lem37848 Absty Repty R dest mk)). Qed.
Lemma lem37850 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term240 Absty Repty R dest mk) = (term241 Absty Repty R dest mk).
Proof. exact (fun_ext (fun x : type684 Repty => @lem37849 Absty Repty x R dest mk)). Qed.
Lemma lem37851 {Repty : Type'} : (@ex ((Repty -> Prop) -> Repty)) = (@ex ((Repty -> Prop) -> Repty)).
Proof. exact (eq_refl (@ex ((Repty -> Prop) -> Repty))). Qed.
Lemma lem37852 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term229 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (MK_COMB (@lem37851 Repty) (@lem37850 Absty Repty R dest mk)). Qed.
Lemma lem37853 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : ((term228 Absty Repty R dest mk) = (term229 Absty Repty R dest mk)) = ((term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk)).
Proof. exact (MK_COMB (@lem37844 Absty Repty R dest mk) (@lem37852 Absty Repty R dest mk)). Qed.
Lemma lem37854 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term223 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (EQ_MP (@lem37853 Absty Repty R dest mk) (@lem37834 Absty Repty R dest mk)). Qed.
Lemma lem37855 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term178 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem37830 Absty Repty R dest mk) (@lem37854 Absty Repty R dest mk)). Qed.
Lemma lem37856 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term154 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem37664 Absty Repty R dest mk) (@lem37855 Absty Repty R dest mk)). Qed.
Lemma lem37857 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) : (term72 Absty Repty R dest mk) = (term242 Absty Repty R dest mk).
Proof. exact (TRANS (@lem37637 Absty Repty R dest mk) (@lem37856 Absty Repty R dest mk)). Qed.
Lemma lem37858 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term72 Absty Repty R dest mk) : term242 Absty Repty R dest mk.
Proof. exact (EQ_MP (@lem37857 Absty Repty R dest mk) (@lem37204 Absty Repty R dest mk h1)). Qed.
Lemma lem38147 {Repty : Type'} (P : Repty -> Prop) : (term133 Repty P) = (term134 Repty P).
Proof. exact (@lem18394 Repty P). Qed.
Lemma lem38148 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1372 Repty R x) = (term1405 Repty R x).
Proof. exact (@lem38147 Repty (term1357 Repty R x)). Qed.
Lemma lem38149 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1406 Repty R x x') = (R x x').
Proof. exact (eq_refl (term1406 Repty R x x')). Qed.
Lemma lem38150 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem38152 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1407 Repty R x x') = (term1116 Repty R x x').
Proof. exact (MK_COMB (@lem38150) (@lem38149 Repty R x x')). Qed.
Lemma lem38153 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1408 Repty R x) = (term1409 Repty R x).
Proof. exact (fun_ext (fun x' : Repty => @lem38152 Repty R x x')). Qed.
Lemma lem38154 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem38155 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1405 Repty R x) = (term1410 Repty R x).
Proof. exact (MK_COMB (@lem38154 Repty) (@lem38153 Repty R x)). Qed.
Lemma lem38164 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1372 Repty R x) = (term1410 Repty R x).
Proof. exact (TRANS (@lem38148 Repty R x) (@lem38155 Repty R x)). Qed.
Lemma lem38165 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1410 Repty R x.
Proof. exact (EQ_MP (@lem38164 Repty R x) (@lem37210 Repty R x h1)). Qed.
Lemma lem38173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem38174 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem38173 Repty Prop f x). Qed.
Lemma lem38176 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (R x x) = (term1112 Repty R x).
Proof. exact (@lem38174 Repty (R x) x). Qed.
Lemma lem38177 {Repty : Type'} (R : type1402 Repty) : (term130 Repty R) = (term1113 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem38176 Repty R x)). Qed.
Lemma lem38178 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem38179 {Repty : Type'} (R : type1402 Repty) : (term67 Repty R) = (term1114 Repty R).
Proof. exact (MK_COMB (@lem38178 Repty) (@lem38177 Repty R)). Qed.
Lemma lem38180 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term1114 Repty R.
Proof. exact (EQ_MP (@lem38179 Repty R) (@lem37223 Repty R h1)). Qed.
Lemma lem38380 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem38387 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem38388 {Repty : Type'} (f : Repty -> Prop) (x : Repty) : (f x) = (@I (Repty -> Prop) f x).
Proof. exact (@lem38387 Repty Prop f x). Qed.
Lemma lem38390 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (R x x') = (term1115 Repty R x x').
Proof. exact (@lem38388 Repty (R x) x'). Qed.
Lemma lem38391 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1116 Repty R x x') = (term1117 Repty R x x').
Proof. exact (MK_COMB (@lem38380) (@lem38390 Repty R x x')). Qed.
Lemma lem38392 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1409 Repty R x) = (term1411 Repty R x).
Proof. exact (fun_ext (fun x' : Repty => @lem38391 Repty R x x')). Qed.
Lemma lem38393 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem38394 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1410 Repty R x) = (term1412 Repty R x).
Proof. exact (MK_COMB (@lem38393 Repty) (@lem38392 Repty R x)). Qed.
Lemma lem38395 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1412 Repty R x.
Proof. exact (EQ_MP (@lem38394 Repty R x) (@lem38165 Repty R x h1)). Qed.
Lemma lem38460 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1112 Repty R x) = (term1112 Repty R x).
Proof. exact (eq_refl (term1112 Repty R x)). Qed.
Lemma lem38461 {Repty : Type'} (R : type1402 Repty) : (term1113 Repty R) = (term1113 Repty R).
Proof. exact (fun_ext (fun x : Repty => @lem38460 Repty R x)). Qed.
Lemma lem38462 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem38464 {Repty : Type'} (R : type1402 Repty) : (term1114 Repty R) = (term1114 Repty R).
Proof. exact (MK_COMB (@lem38462 Repty) (@lem38461 Repty R)). Qed.
Lemma lem38465 {Repty : Type'} (R : type1402 Repty) (h1 : term67 Repty R) : term1114 Repty R.
Proof. exact (EQ_MP (@lem38464 Repty R) (@lem38180 Repty R h1)). Qed.
Lemma lem38499 {Repty : Type'} (R : type1402 Repty) (x : Repty) (x' : Repty) : (term1117 Repty R x x') = (term1117 Repty R x x').
Proof. exact (eq_refl (term1117 Repty R x x')). Qed.
Lemma lem38500 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1411 Repty R x) = (term1411 Repty R x).
Proof. exact (fun_ext (fun x' : Repty => @lem38499 Repty R x x')). Qed.
Lemma lem38501 {Repty : Type'} : (@all Repty) = (@all Repty).
Proof. exact (eq_refl (@all Repty)). Qed.
Lemma lem38503 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1412 Repty R x) = (term1412 Repty R x).
Proof. exact (MK_COMB (@lem38501 Repty) (@lem38500 Repty R x)). Qed.
Lemma lem38504 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1412 Repty R x.
Proof. exact (EQ_MP (@lem38503 Repty R x) (@lem38395 Repty R x h1)). Qed.
Lemma lem38624 {Repty : Type'} (_1042 : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1171 Repty R _1042.
Proof. exact (@lem38465 Repty R h1 _1042). Qed.
Lemma lem38625 {Repty : Type'} (R : type1402 Repty) (_1042 : Repty) : (term1171 Repty R _1042) = (term1112 Repty R _1042).
Proof. exact (eq_refl (term1171 Repty R _1042)). Qed.
Lemma lem38639 {Repty : Type'} (_1047 : Repty) (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1413 Repty R x _1047.
Proof. exact (@lem38504 Repty R x h1 _1047). Qed.
Lemma lem38640 {Repty : Type'} (R : type1402 Repty) (x : Repty) (_1047 : Repty) : (term1413 Repty R x _1047) = (term1117 Repty R x _1047).
Proof. exact (eq_refl (term1413 Repty R x _1047)). Qed.
Lemma lem38692 {Repty : Type'} (_1047 : Repty) (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1117 Repty R x _1047.
Proof. exact (EQ_MP (@lem38640 Repty R x _1047) (@lem38639 Repty _1047 R x h1)). Qed.
Lemma lem38787 {Repty : Type'} (_1042 : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R _1042.
Proof. exact (EQ_MP (@lem38625 Repty R _1042) (@lem38624 Repty _1042 R h1)). Qed.
Lemma lem38788 {Repty : Type'} (_1042 : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R _1042.
Proof. exact (@lem38787 Repty _1042 R h1). Qed.
Lemma lem38789 {Repty : Type'} (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R x.
Proof. exact (@lem38788 Repty x R h1). Qed.
Lemma lem38790 {Repty : Type'} (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1197 Repty R x.
Proof. exact (fun h0 : term1198 Repty R x => @lem38789 Repty x R h1). Qed.
Lemma lem38792 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem38793 {Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1197 Repty R x) = (term1112 Repty R x).
Proof. exact (@lem38792 (term1112 Repty R x)). Qed.
Lemma lem38794 {Repty : Type'} (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1112 Repty R x.
Proof. exact (EQ_MP (@lem38793 Repty R x) (@lem38790 Repty x R h1)). Qed.
Lemma lem38797 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem38799 {Repty : Type'} (R : type1402 Repty) (x : Repty) (_1047 : Repty) : (term1117 Repty R x _1047) = (term1177 Repty R x _1047).
Proof. exact (@lem38797 (term1115 Repty R x _1047)). Qed.
Lemma lem38802 {Repty : Type'} (_1047 : Repty) (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1177 Repty R x _1047.
Proof. exact (EQ_MP (@lem38799 Repty R x _1047) (@lem38692 Repty _1047 R x h1)). Qed.
Lemma lem38803 {Repty : Type'} (_1047 : Repty) (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1177 Repty R x _1047.
Proof. exact (@lem38802 Repty _1047 R x h1). Qed.
Lemma lem38804 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term1372 Repty R x) : term1414 Repty R x.
Proof. exact (@lem38803 Repty x R x h1). Qed.
Lemma lem38807 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term1372 Repty R x) : False.
Proof. exact (@lem38804 Repty R x h2 (@lem38794 Repty x R h1)). Qed.
Lemma lem38808 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term1372 Repty R x) : term330.
Proof. exact (fun h0 : ~ False => @lem38807 Repty R x h1 h2). Qed.
Lemma lem38810 (p : Prop) : (term274 p) = p.
Proof. exact (or_elim (@lem21117 p) (fun h0 : p = True => @lem21180 p h0) (fun h0 : p = False => @lem21179 p h0)). Qed.
Lemma lem38811 : term330 = False.
Proof. exact (@lem38810 False). Qed.
Lemma lem38812 {Repty : Type'} (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term1372 Repty R x) : False.
Proof. exact (EQ_MP (@lem38811) (@lem38808 Repty R x h1 h2)). Qed.
Lemma lem38813 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) (h3 : term1372 Repty R x) : False.
Proof. exact (ex_elim (@lem37858 Absty Repty R dest mk h2) (fun x' : type684 Repty => fun h0 : term241 Absty Repty R dest mk x' => @lem38812 Repty R x h1 h3)). Qed.
Lemma lem38814 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) (h3 : term1372 Repty R x) : (term67 Repty R) = False.
Proof. exact (prop_ext (fun h4 : term67 Repty R => @lem38813 Absty Repty dest mk R x h1 h2 h3) (fun h4 : False => @lem37223 Repty R h1)). Qed.
Lemma lem38815 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) (h3 : term1372 Repty R x) : False.
Proof. exact (EQ_MP (@lem38814 Absty Repty dest mk R x h1 h2 h3) (@lem37223 Repty R h1)). Qed.
Lemma lem38816 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) (h3 : term1372 Repty R x) : (term1372 Repty R x) = False.
Proof. exact (prop_ext (fun h4 : term1372 Repty R x => @lem38815 Absty Repty dest mk R x h1 h2 h3) (fun h4 : False => @lem37210 Repty R x h3)). Qed.
Lemma lem38817 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) (h3 : term1372 Repty R x) : False.
Proof. exact (EQ_MP (@lem38816 Absty Repty dest mk R x h1 h2 h3) (@lem37210 Repty R x h3)). Qed.
Lemma lem38818 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) : term1371 Repty R x.
Proof. exact (fun h0 : term1372 Repty R x => @lem38817 Absty Repty dest mk R x h1 h2 h0). Qed.
Lemma lem38819 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) : term1368 Repty R x.
Proof. exact (EQ_MP (@lem37209 Repty R x) (@lem38818 Absty Repty x R dest mk h1 h2)). Qed.
Lemma lem38820 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term72 Absty Repty R dest mk) : term1379 Absty Repty mk R x.
Proof. exact (fun h0 : term74 Absty Repty mk R => @lem38819 Absty Repty x R dest mk h1 h2). Qed.
Lemma lem38821 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1381 Absty Repty dest mk R x.
Proof. exact (fun h0 : term72 Absty Repty R dest mk => @lem38820 Absty Repty x R dest mk h1 h0). Qed.
Lemma lem38822 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1383 Absty Repty dest mk R x.
Proof. exact (fun h0 : term73 Absty Repty mk dest => @lem38821 Absty Repty dest mk x R h1). Qed.
Lemma lem38823 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1385 Absty Repty dest mk R x.
Proof. exact (fun h0 : term71 Repty R => @lem38822 Absty Repty dest mk x R h1). Qed.
Lemma lem38824 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1387 Absty Repty dest mk R x.
Proof. exact (fun h0 : term69 Repty R => @lem38823 Absty Repty dest mk x R h1). Qed.
Lemma lem38825 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1388 Absty Repty dest mk R x.
Proof. exact (fun h0 : term67 Repty R => @lem38824 Absty Repty dest mk x R h0). Qed.
Lemma lem38830 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1392 Absty Repty mk R x.
Proof. exact (fun dest : type1413 Absty Repty => @lem38825 Absty Repty dest mk R x). Qed.
Lemma lem38835 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : term1396 Absty Repty R x.
Proof. exact (fun mk : type862 Absty Repty => @lem38830 Absty Repty mk R x). Qed.
Lemma lem38840 {Absty Repty : Type'} (x : Repty) : term1400 Absty Repty x.
Proof. exact (fun R : type1402 Repty => @lem38835 Absty Repty R x). Qed.
Lemma lem38845 {Absty Repty : Type'} : term1404 Absty Repty.
Proof. exact (fun x : Repty => @lem38840 Absty Repty x). Qed.
Lemma lem38846 {Absty Repty : Type'} : term1403 Absty Repty.
Proof. exact (EQ_MP (@lem37199 Absty Repty) (@lem38845 Absty Repty)). Qed.
Lemma lem38847 {Absty Repty : Type'} (x : Repty) : term1415 Absty Repty x.
Proof. exact (@lem38846 Absty Repty x). Qed.
Lemma lem38848 {Absty Repty : Type'} (x : Repty) : (term1415 Absty Repty x) = (term1399 Absty Repty x).
Proof. exact (eq_refl (term1415 Absty Repty x)). Qed.
Lemma lem38849 {Absty Repty : Type'} (x : Repty) : term1399 Absty Repty x.
Proof. exact (EQ_MP (@lem38848 Absty Repty x) (@lem38847 Absty Repty x)). Qed.
Lemma lem38850 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) : term1416 Absty Repty x R.
Proof. exact (@lem38849 Absty Repty x R). Qed.
Lemma lem38851 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : (term1416 Absty Repty x R) = (term1395 Absty Repty R x).
Proof. exact (eq_refl (term1416 Absty Repty x R)). Qed.
Lemma lem38852 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) : term1395 Absty Repty R x.
Proof. exact (EQ_MP (@lem38851 Absty Repty R x) (@lem38850 Absty Repty x R)). Qed.
Lemma lem38853 {Absty Repty : Type'} (R : type1402 Repty) (x : Repty) (mk : type862 Absty Repty) : term1417 Absty Repty R x mk.
Proof. exact (@lem38852 Absty Repty R x mk). Qed.
Lemma lem38854 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1417 Absty Repty R x mk) = (term1391 Absty Repty mk R x).
Proof. exact (eq_refl (term1417 Absty Repty R x mk)). Qed.
Lemma lem38855 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1391 Absty Repty mk R x.
Proof. exact (EQ_MP (@lem38854 Absty Repty mk R x) (@lem38853 Absty Repty R x mk)). Qed.
Lemma lem38856 {Absty Repty : Type'} (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (dest : type1413 Absty Repty) : term1418 Absty Repty mk R x dest.
Proof. exact (@lem38855 Absty Repty mk R x dest). Qed.
Lemma lem38857 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : (term1418 Absty Repty mk R x dest) = (term1373 Absty Repty dest mk R x).
Proof. exact (eq_refl (term1418 Absty Repty mk R x dest)). Qed.
Lemma lem38858 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1373 Absty Repty dest mk R x.
Proof. exact (EQ_MP (@lem38857 Absty Repty dest mk R x) (@lem38856 Absty Repty mk R x dest)). Qed.
Lemma lem38860 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) : term1373 Absty Repty dest mk R x.
Proof. exact (@lem36847 Absty Repty dest mk R x (@lem38858 Absty Repty dest mk R x)). Qed.
Lemma lem38861 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term67 Repty R) : term1386 Absty Repty dest mk R x.
Proof. exact (@lem38860 Absty Repty dest mk R x (@lem23771 Repty R h1)). Qed.
Lemma lem38862 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) : term1384 Absty Repty dest mk R x.
Proof. exact (@lem38861 Absty Repty dest mk x R h2 (@lem23773 Repty R h1)). Qed.
Lemma lem38863 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (x : Repty) (R : type1402 Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) : term1382 Absty Repty dest mk R x.
Proof. exact (@lem38862 Absty Repty dest mk x R h2 h3 (@lem23775 Repty R h1)). Qed.
Lemma lem38864 {Absty Repty : Type'} (x : Repty) (mk : type862 Absty Repty) (dest : type1413 Absty Repty) (R : type1402 Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) : term1380 Absty Repty dest mk R x.
Proof. exact (@lem38863 Absty Repty dest mk x R h2 h3 h4 (@lem23777 Absty Repty mk dest h1)). Qed.
Lemma lem38865 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term1378 Absty Repty mk R x.
Proof. exact (@lem38864 Absty Repty x mk dest R h1 h2 h3 h4 (@lem23776 Absty Repty R dest mk h5)). Qed.
Lemma lem38866 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1371 Repty R x.
Proof. exact (@lem38865 Absty Repty x R dest mk h1 h2 h4 h5 h6 (@lem23778 Absty Repty mk R h3)). Qed.
Lemma lem38867 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term1372 Repty R x) : False.
Proof. exact (@lem38866 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6 (@lem36831 Repty R x h7)). Qed.
Lemma lem38868 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term1372 Repty R x) : (term1372 Repty R x) = False.
Proof. exact (prop_ext (fun h8 : term1372 Repty R x => @lem38867 Absty Repty dest mk R x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem36831 Repty R x h7)). Qed.
Lemma lem38869 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : term1372 Repty R x) : False.
Proof. exact (EQ_MP (@lem38868 Absty Repty dest mk R x h1 h2 h3 h4 h5 h6 h7) (@lem36831 Repty R x h7)). Qed.
Lemma lem38870 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1371 Repty R x.
Proof. exact (fun h0 : term1372 Repty R x => @lem38869 Absty Repty dest mk R x h1 h2 h3 h4 h5 h6 h0). Qed.
Lemma lem38871 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1368 Repty R x.
Proof. exact (EQ_MP (@lem36830 Repty R x) (@lem38870 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38872 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1365 Repty R x.
Proof. exact (EQ_MP (@lem36826 Repty R x) (@lem38871 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38873 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1362 Repty R x.
Proof. exact (EQ_MP (@lem36817 Repty x R h4) (@lem38872 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38874 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1316 Repty R x.
Proof. exact (EQ_MP (@lem36783 Repty R x) (@lem38873 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38875 {Absty Repty : Type'} (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (R : type1402 Repty) (x : Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) (h7 : (term285 Absty Repty dest mk R x) = (R x)) : term1309 Absty Repty dest mk R x.
Proof. exact (EQ_MP (@lem34690 Absty Repty dest mk R x h7) (@lem38874 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38876 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : ((term285 Absty Repty dest mk R x) = (R x)) = (term1309 Absty Repty dest mk R x).
Proof. exact (prop_ext (fun h7 : (term285 Absty Repty dest mk R x) = (R x) => @lem38875 Absty Repty dest mk R x h1 h2 h3 h4 h5 h6 h7) (fun h7 : term1309 Absty Repty dest mk R x => @lem36772 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38877 {Absty Repty : Type'} (x : Repty) (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1309 Absty Repty dest mk R x.
Proof. exact (EQ_MP (@lem38876 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6) (@lem36772 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38882 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1312 Absty Repty dest mk R.
Proof. exact (fun x : Repty => @lem38877 Absty Repty x R dest mk h1 h2 h3 h4 h5 h6). Qed.
Lemma lem38883 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term345 Absty Repty mk R) (h5 : term69 Repty R) (h6 : term67 Repty R) (h7 : term72 Absty Repty R dest mk) : term1299 Absty Repty dest mk R.
Proof. exact (EQ_MP (@lem34676 Absty Repty dest mk R h4) (@lem38882 Absty Repty R dest mk h1 h2 h3 h5 h6 h7)). Qed.
Lemma lem38884 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1302 Absty Repty dest mk R.
Proof. exact (fun h0 : term345 Absty Repty mk R => @lem38883 Absty Repty R dest mk h1 h2 h3 h0 h4 h5 h6). Qed.
Lemma lem38885 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term346 Absty Repty mk R) (h7 : term72 Absty Repty R dest mk) : term1301 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem34639 Absty Repty dest mk R h6) (@lem38884 Absty Repty R dest mk h1 h2 h3 h4 h5 h7)). Qed.
Lemma lem38886 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1419 Absty Repty mk R dest.
Proof. exact (fun h0 : term346 Absty Repty mk R => @lem38885 Absty Repty R dest mk h1 h2 h3 h4 h5 h0 h6). Qed.
Lemma lem38887 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1420 Absty Repty mk R dest.
Proof. exact (conj (@lem34568 Absty Repty R dest mk h1 h2 h3 h4 h5 h6) (@lem38886 Absty Repty R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38888 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (@lem26057 Absty Repty mk R dest (@lem38887 Absty Repty R dest mk h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem38889 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : (term74 Absty Repty mk R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h7 : term74 Absty Repty mk R => @lem38888 Absty Repty R dest mk h1 h2 h3 h4 h5 h6) (fun h7 : term1421 Absty Repty mk R dest => @lem23778 Absty Repty mk R h3)). Qed.
Lemma lem38890 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term74 Absty Repty mk R) (h4 : term69 Repty R) (h5 : term67 Repty R) (h6 : term72 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38889 Absty Repty R dest mk h1 h2 h3 h4 h5 h6) (@lem23778 Absty Repty mk R h3)). Qed.
Lemma lem38891 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : (term74 Absty Repty mk R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h6 : term74 Absty Repty mk R => @lem38890 Absty Repty R dest mk h1 h2 h6 h3 h4 h5) (fun h6 : term1421 Absty Repty mk R dest => @lem26054 Absty Repty R dest mk h1 h2 h3 h4 h5)). Qed.
Lemma lem38892 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38891 Absty Repty R dest mk h1 h2 h3 h4 h5) (@lem26054 Absty Repty R dest mk h1 h2 h3 h4 h5)). Qed.
Lemma lem38893 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term65 Absty Repty R dest mk) : term66 Absty Repty R dest mk.
Proof. exact (proj2 (@lem23769 Absty Repty R dest mk h1)). Qed.
Lemma lem38894 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term65 Absty Repty R dest mk) : term67 Repty R.
Proof. exact (proj1 (@lem23769 Absty Repty R dest mk h1)). Qed.
Lemma lem38895 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term66 Absty Repty R dest mk) : term68 Absty Repty R dest mk.
Proof. exact (proj2 (@lem23770 Absty Repty R dest mk h1)). Qed.
Lemma lem38896 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term66 Absty Repty R dest mk) : term69 Repty R.
Proof. exact (proj1 (@lem23770 Absty Repty R dest mk h1)). Qed.
Lemma lem38897 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term68 Absty Repty R dest mk) : term70 Absty Repty R dest mk.
Proof. exact (proj2 (@lem23772 Absty Repty R dest mk h1)). Qed.
Lemma lem38898 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term68 Absty Repty R dest mk) : term71 Repty R.
Proof. exact (proj1 (@lem23772 Absty Repty R dest mk h1)). Qed.
Lemma lem38899 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term70 Absty Repty R dest mk) : term72 Absty Repty R dest mk.
Proof. exact (proj2 (@lem23774 Absty Repty R dest mk h1)). Qed.
Lemma lem38900 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term70 Absty Repty R dest mk) : term73 Absty Repty mk dest.
Proof. exact (proj1 (@lem23774 Absty Repty R dest mk h1)). Qed.
Lemma lem38901 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : (term72 Absty Repty R dest mk) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h6 : term72 Absty Repty R dest mk => @lem38892 Absty Repty R dest mk h1 h2 h3 h4 h5) (fun h6 : term1421 Absty Repty mk R dest => @lem23776 Absty Repty R dest mk h5)). Qed.
Lemma lem38902 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38901 Absty Repty R dest mk h1 h2 h3 h4 h5) (@lem23776 Absty Repty R dest mk h5)). Qed.
Lemma lem38903 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : (term73 Absty Repty mk dest) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h6 : term73 Absty Repty mk dest => @lem38902 Absty Repty R dest mk h1 h2 h3 h4 h5) (fun h6 : term1421 Absty Repty mk R dest => @lem23777 Absty Repty mk dest h1)). Qed.
Lemma lem38904 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term72 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38903 Absty Repty R dest mk h1 h2 h3 h4 h5) (@lem23777 Absty Repty mk dest h1)). Qed.
Lemma lem38905 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term70 Absty Repty R dest mk) : (term72 Absty Repty R dest mk) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h6 : term72 Absty Repty R dest mk => @lem38904 Absty Repty R dest mk h1 h2 h3 h4 h6) (fun h6 : term1421 Absty Repty mk R dest => @lem38899 Absty Repty R dest mk h5)). Qed.
Lemma lem38906 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term73 Absty Repty mk dest) (h2 : term71 Repty R) (h3 : term69 Repty R) (h4 : term67 Repty R) (h5 : term70 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38905 Absty Repty R dest mk h1 h2 h3 h4 h5) (@lem38899 Absty Repty R dest mk h5)). Qed.
Lemma lem38907 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) (h4 : term70 Absty Repty R dest mk) : (term73 Absty Repty mk dest) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h5 : term73 Absty Repty mk dest => @lem38906 Absty Repty R dest mk h5 h1 h2 h3 h4) (fun h5 : term1421 Absty Repty mk R dest => @lem38900 Absty Repty R dest mk h4)). Qed.
Lemma lem38908 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) (h4 : term70 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38907 Absty Repty R dest mk h1 h2 h3 h4) (@lem38900 Absty Repty R dest mk h4)). Qed.
Lemma lem38909 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) (h4 : term70 Absty Repty R dest mk) : (term71 Repty R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h5 : term71 Repty R => @lem38908 Absty Repty R dest mk h1 h2 h3 h4) (fun h5 : term1421 Absty Repty mk R dest => @lem23775 Repty R h1)). Qed.
Lemma lem38910 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) (h4 : term70 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38909 Absty Repty R dest mk h1 h2 h3 h4) (@lem23775 Repty R h1)). Qed.
Lemma lem38911 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) (h4 : term68 Absty Repty R dest mk) : (term70 Absty Repty R dest mk) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h5 : term70 Absty Repty R dest mk => @lem38910 Absty Repty R dest mk h1 h2 h3 h5) (fun h5 : term1421 Absty Repty mk R dest => @lem38897 Absty Repty R dest mk h4)). Qed.
Lemma lem38912 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term71 Repty R) (h2 : term69 Repty R) (h3 : term67 Repty R) (h4 : term68 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38911 Absty Repty R dest mk h1 h2 h3 h4) (@lem38897 Absty Repty R dest mk h4)). Qed.
Lemma lem38913 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) (h3 : term68 Absty Repty R dest mk) : (term71 Repty R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h4 : term71 Repty R => @lem38912 Absty Repty R dest mk h4 h1 h2 h3) (fun h4 : term1421 Absty Repty mk R dest => @lem38898 Absty Repty R dest mk h3)). Qed.
Lemma lem38914 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) (h3 : term68 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38913 Absty Repty R dest mk h1 h2 h3) (@lem38898 Absty Repty R dest mk h3)). Qed.
Lemma lem38915 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) (h3 : term68 Absty Repty R dest mk) : (term69 Repty R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h4 : term69 Repty R => @lem38914 Absty Repty R dest mk h1 h2 h3) (fun h4 : term1421 Absty Repty mk R dest => @lem23773 Repty R h1)). Qed.
Lemma lem38916 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) (h3 : term68 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38915 Absty Repty R dest mk h1 h2 h3) (@lem23773 Repty R h1)). Qed.
Lemma lem38917 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) (h3 : term66 Absty Repty R dest mk) : (term68 Absty Repty R dest mk) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h4 : term68 Absty Repty R dest mk => @lem38916 Absty Repty R dest mk h1 h2 h4) (fun h4 : term1421 Absty Repty mk R dest => @lem38895 Absty Repty R dest mk h3)). Qed.
Lemma lem38918 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term69 Repty R) (h2 : term67 Repty R) (h3 : term66 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38917 Absty Repty R dest mk h1 h2 h3) (@lem38895 Absty Repty R dest mk h3)). Qed.
Lemma lem38919 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term66 Absty Repty R dest mk) : (term69 Repty R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h3 : term69 Repty R => @lem38918 Absty Repty R dest mk h3 h1 h2) (fun h3 : term1421 Absty Repty mk R dest => @lem38896 Absty Repty R dest mk h2)). Qed.
Lemma lem38920 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term66 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38919 Absty Repty R dest mk h1 h2) (@lem38896 Absty Repty R dest mk h2)). Qed.
Lemma lem38921 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term66 Absty Repty R dest mk) : (term67 Repty R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h3 : term67 Repty R => @lem38920 Absty Repty R dest mk h1 h2) (fun h3 : term1421 Absty Repty mk R dest => @lem23771 Repty R h1)). Qed.
Lemma lem38922 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term66 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38921 Absty Repty R dest mk h1 h2) (@lem23771 Repty R h1)). Qed.
Lemma lem38923 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term65 Absty Repty R dest mk) : (term66 Absty Repty R dest mk) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h3 : term66 Absty Repty R dest mk => @lem38922 Absty Repty R dest mk h1 h3) (fun h3 : term1421 Absty Repty mk R dest => @lem38893 Absty Repty R dest mk h2)). Qed.
Lemma lem38924 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term67 Repty R) (h2 : term65 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38923 Absty Repty R dest mk h1 h2) (@lem38893 Absty Repty R dest mk h2)). Qed.
Lemma lem38925 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term65 Absty Repty R dest mk) : (term67 Repty R) = (term1421 Absty Repty mk R dest).
Proof. exact (prop_ext (fun h2 : term67 Repty R => @lem38924 Absty Repty R dest mk h2 h1) (fun h2 : term1421 Absty Repty mk R dest => @lem38894 Absty Repty R dest mk h1)). Qed.
Lemma lem38926 {Absty Repty : Type'} (R : type1402 Repty) (dest : type1413 Absty Repty) (mk : type862 Absty Repty) (h1 : term65 Absty Repty R dest mk) : term1421 Absty Repty mk R dest.
Proof. exact (EQ_MP (@lem38925 Absty Repty R dest mk h1) (@lem38894 Absty Repty R dest mk h1)). Qed.
