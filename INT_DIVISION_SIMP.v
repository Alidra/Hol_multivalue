Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIVISION_SIMP_term_abbrevs.
Require Import MONO_FORALL_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1482981_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17362_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982729_spec.
Require Import thm1982733_spec.
Require Import thm1982747_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2387577_spec.
Require Import thm4211_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2389436 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem2389437 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem2389438 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem2389436 A P Q h2 (@lem2389437 A P Q h1)). Qed.
Lemma lem2389439 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem2389438 A P Q h1 h0). Qed.
Lemma lem2389440 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem2389441 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem2389439 A P Q h1 (@lem2389440 A P Q h2)). Qed.
Lemma lem2389442 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem2389441 A P Q h0 h1). Qed.
Lemma lem2389443 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem2389442 A P Q h0). Qed.
Lemma lem2389446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem2389443 A P Q (@lem7363 A P Q)). Qed.
Lemma lem2389447 (P : int -> Prop) (Q : int -> Prop) : term5 P Q.
Proof. exact (@lem2389446 int P Q). Qed.
Lemma lem2389448 : term6.
Proof. exact (@lem2389447 term7 term8). Qed.
Lemma lem2389449 (m : int) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem2389450 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2389451 (m : int) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem2389450) (@lem2389449 m)). Qed.
Lemma lem2389452 (m : int) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem2389453 (m : int) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem2389451 m) (@lem2389452 m)). Qed.
Lemma lem2389454 : term17 = term18.
Proof. exact (fun_ext (fun m : int => @lem2389453 m)). Qed.
Lemma lem2389455 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2389456 : term19 = term20.
Proof. exact (MK_COMB (@lem2389455) (@lem2389454)). Qed.
Lemma lem2389457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2389458 : term21 = term22.
Proof. exact (MK_COMB (@lem2389457) (@lem2389456)). Qed.
Lemma lem2389459 (m : int) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem2389460 : term23 = term7.
Proof. exact (fun_ext (fun m : int => @lem2389459 m)). Qed.
Lemma lem2389461 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2389462 : term24 = term25.
Proof. exact (MK_COMB (@lem2389461) (@lem2389460)). Qed.
Lemma lem2389463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2389464 : term26 = term27.
Proof. exact (MK_COMB (@lem2389463) (@lem2389462)). Qed.
Lemma lem2389465 (m : int) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem2389466 : term28 = term8.
Proof. exact (fun_ext (fun m : int => @lem2389465 m)). Qed.
Lemma lem2389467 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2389468 : term29 = term30.
Proof. exact (MK_COMB (@lem2389467) (@lem2389466)). Qed.
Lemma lem2389469 : term31 = term32.
Proof. exact (MK_COMB (@lem2389464) (@lem2389468)). Qed.
Lemma lem2389470 : term6 = term33.
Proof. exact (MK_COMB (@lem2389458) (@lem2389469)). Qed.
Lemma lem2389471 : term33.
Proof. exact (EQ_MP (@lem2389470) (@lem2389448)). Qed.
Lemma lem2389473 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem2389443 A P Q (@lem7363 A P Q)). Qed.
Lemma lem2389474 (P : int -> Prop) (Q : int -> Prop) : term5 P Q.
Proof. exact (@lem2389473 int P Q). Qed.
Lemma lem2389475 (m : int) : term34 m.
Proof. exact (@lem2389474 (term35 m) (term36 m)). Qed.
Lemma lem2389476 (m : int) (n : int) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem2389477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2389478 (m : int) (n : int) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2389477) (@lem2389476 m n)). Qed.
Lemma lem2389479 (n : int) (m : int) : (term41 m n) = ((term42 m n) = m).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem2389480 (n : int) (m : int) : (term43 m n) = (term44 n m).
Proof. exact (MK_COMB (@lem2389478 m n) (@lem2389479 n m)). Qed.
Lemma lem2389481 (m : int) : (term45 m) = (term46 m).
Proof. exact (fun_ext (fun n : int => @lem2389480 n m)). Qed.
Lemma lem2389482 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2389483 (m : int) : (term47 m) = (term48 m).
Proof. exact (MK_COMB (@lem2389482) (@lem2389481 m)). Qed.
Lemma lem2389484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2389485 (m : int) : (term49 m) = (term50 m).
Proof. exact (MK_COMB (@lem2389484) (@lem2389483 m)). Qed.
Lemma lem2389486 (m : int) (n : int) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem2389487 (m : int) : (term51 m) = (term35 m).
Proof. exact (fun_ext (fun n : int => @lem2389486 m n)). Qed.
Lemma lem2389488 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2389489 (m : int) : (term52 m) = (term10 m).
Proof. exact (MK_COMB (@lem2389488) (@lem2389487 m)). Qed.
Lemma lem2389490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2389491 (m : int) : (term53 m) = (term12 m).
Proof. exact (MK_COMB (@lem2389490) (@lem2389489 m)). Qed.
Lemma lem2389492 (n : int) (m : int) : (term41 m n) = ((term42 m n) = m).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem2389493 (m : int) : (term54 m) = (term36 m).
Proof. exact (fun_ext (fun n : int => @lem2389492 n m)). Qed.
Lemma lem2389494 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2389495 (m : int) : (term55 m) = (term14 m).
Proof. exact (MK_COMB (@lem2389494) (@lem2389493 m)). Qed.
Lemma lem2389496 (m : int) : (term56 m) = (term16 m).
Proof. exact (MK_COMB (@lem2389491 m) (@lem2389495 m)). Qed.
Lemma lem2389497 (m : int) : (term34 m) = (term57 m).
Proof. exact (MK_COMB (@lem2389485 m) (@lem2389496 m)). Qed.
Lemma lem2389498 (m : int) : term57 m.
Proof. exact (EQ_MP (@lem2389497 m) (@lem2389475 m)). Qed.
Lemma lem2389501 (_474 : Prop) (_475 : Prop) (_476 : Prop -> Prop) (_477 : Prop) : (term58 _476 _475 _474 _477) = (term59 _474 _475 _476 _477).
Proof. exact (@lem13473 Prop _474 _475 _476 _477). Qed.
Lemma lem2389502 (_474 : Prop) (_475 : Prop) (n : int) (m : int) (_477 : Prop) : (term60 n m _475 _474 _477) = (term61 _474 _475 n m _477).
Proof. exact (@lem2389501 _474 _475 (term62 n m) _477). Qed.
Lemma lem2389503 (m : int) (n : int) : (term63 m n) = (term64 m n).
Proof. exact (@lem2389502 (term65 n m) (n = term66) n m (term67 m n)). Qed.
Lemma lem2389504 (n : int) (m : int) : (term68 m n) = (term69 n m).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem2389505 (n : int) : (term70 n) = (term70 n).
Proof. exact (eq_refl (term70 n)). Qed.
Lemma lem2389506 (n : int) (m : int) : (term71 m n) = (term72 n m).
Proof. exact (MK_COMB (@lem2389505 n) (@lem2389504 n m)). Qed.
Lemma lem2389507 (n : int) (m : int) : (term73 n m) = (term74 n m).
Proof. exact (eq_refl (term73 n m)). Qed.
Lemma lem2389508 (n : int) : (term75 n) = (term75 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem2389509 (n : int) (m : int) : (term76 n m) = (term77 n m).
Proof. exact (MK_COMB (@lem2389508 n) (@lem2389507 n m)). Qed.
Lemma lem2389510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2389511 (n : int) (m : int) : (term78 n m) = (term79 n m).
Proof. exact (MK_COMB (@lem2389510) (@lem2389509 n m)). Qed.
Lemma lem2389512 (n : int) (m : int) : (term64 m n) = (term80 n m).
Proof. exact (MK_COMB (@lem2389511 n m) (@lem2389506 n m)). Qed.
Lemma lem2389513 (n : int) (m : int) : (term63 m n) = (term44 n m).
Proof. exact (eq_refl (term63 m n)). Qed.
Lemma lem2389514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2389515 (n : int) (m : int) : (term81 m n) = (term82 n m).
Proof. exact (MK_COMB (@lem2389514) (@lem2389513 n m)). Qed.
Lemma lem2389516 (n : int) (m : int) : ((term63 m n) = (term64 m n)) = ((term44 n m) = (term80 n m)).
Proof. exact (MK_COMB (@lem2389515 n m) (@lem2389512 n m)). Qed.
Lemma lem2389517 (n : int) (m : int) : (term44 n m) = (term80 n m).
Proof. exact (EQ_MP (@lem2389516 n m) (@lem2389503 m n)). Qed.
Lemma lem2389518 (n : int) (m : int) : (term80 n m) = (term44 n m).
Proof. exact (SYM (@lem2389517 n m)). Qed.
Lemma lem2389519 (n : int) (h1 : n = term66) : n = term66.
Proof. exact (h1). Qed.
Lemma lem2389556 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term83 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2389557 (p : Prop) (q : Prop) (p' : Prop) : term84 p q p'.
Proof. exact (fun q' : Prop => @lem2389556 p q p' q'). Qed.
Lemma lem2389558 (p : Prop) (q : Prop) : term85 p q.
Proof. exact (fun p' : Prop => @lem2389557 p q p'). Qed.
Lemma lem2389559 (n : int) (m : int) : term86 n m.
Proof. exact (@lem2389558 (term65 n m) ((term42 m n) = m)). Qed.
Lemma lem2389560 (n : int) (m : int) (p' : Prop) : term87 n m p'.
Proof. exact (@lem2389559 n m p'). Qed.
Lemma lem2389561 (n : int) (m : int) (p' : Prop) : (term87 n m p') = (term88 n m p').
Proof. exact (eq_refl (term87 n m p')). Qed.
Lemma lem2389562 (n : int) (m : int) (p' : Prop) : term88 n m p'.
Proof. exact (EQ_MP (@lem2389561 n m p') (@lem2389560 n m p')). Qed.
Lemma lem2389563 (n : int) (m : int) (p' : Prop) (q' : Prop) : term89 n m p' q'.
Proof. exact (@lem2389562 n m p' q'). Qed.
Lemma lem2389564 (n : int) (m : int) (p' : Prop) (q' : Prop) : (term89 n m p' q') = (term90 n m p' q').
Proof. exact (eq_refl (term89 n m p' q')). Qed.
Lemma lem2389565 (n : int) (m : int) (p' : Prop) (q' : Prop) : term90 n m p' q'.
Proof. exact (EQ_MP (@lem2389564 n m p' q') (@lem2389563 n m p' q')). Qed.
Lemma lem2389571 (n : int) (h1 : n = term66) : n = term66.
Proof. exact (h1). Qed.
Lemma lem2389572 (m : int) : (div m) = (div m).
Proof. exact (eq_refl (div m)). Qed.
Lemma lem2389573 (m : int) (n : int) (h1 : n = term66) : (div m n) = (term91 m).
Proof. exact (MK_COMB (@lem2389572 m) (@lem2389571 n h1)). Qed.
Lemma lem2389574 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2389575 (m : int) (n : int) (h1 : n = term66) : (term92 m n) = (term93 m).
Proof. exact (MK_COMB (@lem2389574) (@lem2389573 m n h1)). Qed.
Lemma lem2389576 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2389577 (m : int) (n : int) (h1 : n = term66) : ((div m n) = term66) = ((term91 m) = term66).
Proof. exact (MK_COMB (@lem2389575 m n h1) (@lem2389576)). Qed.
Lemma lem2389580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2389581 (m : int) (n : int) (h1 : n = term66) : (term94 m n) = (term95 m).
Proof. exact (MK_COMB (@lem2389580) (@lem2389577 m n h1)). Qed.
Lemma lem2389587 (n : int) (h1 : n = term66) : n = term66.
Proof. exact (h1). Qed.
Lemma lem2389588 (m : int) : (rem m) = (rem m).
Proof. exact (eq_refl (rem m)). Qed.
Lemma lem2389589 (m : int) (n : int) (h1 : n = term66) : (rem m n) = (term96 m).
Proof. exact (MK_COMB (@lem2389588 m) (@lem2389587 n h1)). Qed.
Lemma lem2389590 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2389591 (m : int) (n : int) (h1 : n = term66) : (term97 m n) = (term98 m).
Proof. exact (MK_COMB (@lem2389590) (@lem2389589 m n h1)). Qed.
Lemma lem2389592 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2389593 (m : int) (n : int) (h1 : n = term66) : ((rem m n) = m) = ((term96 m) = m).
Proof. exact (MK_COMB (@lem2389591 m n h1) (@lem2389592 m)). Qed.
Lemma lem2389596 (m : int) (n : int) (h1 : n = term66) : (term65 n m) = (term99 m).
Proof. exact (MK_COMB (@lem2389581 m n h1) (@lem2389593 m n h1)). Qed.
Lemma lem2389603 (n : int) (m : int) (q' : Prop) : term100 n m q'.
Proof. exact (@lem2389565 n m (term99 m) q'). Qed.
Lemma lem2389604 (m : int) (q' : Prop) (n : int) (h1 : n = term66) : term101 n m q'.
Proof. exact (@lem2389603 n m q' (@lem2389596 m n h1)). Qed.
Lemma lem2389605 (m : int) (h1 : term99 m) : term99 m.
Proof. exact (h1). Qed.
Lemma lem2389611 (n : int) (h1 : n = term66) : n = term66.
Proof. exact (h1). Qed.
Lemma lem2389612 (m : int) : (div m) = (div m).
Proof. exact (eq_refl (div m)). Qed.
Lemma lem2389613 (m : int) (n : int) (h1 : n = term66) : (div m n) = (term91 m).
Proof. exact (MK_COMB (@lem2389612 m) (@lem2389611 n h1)). Qed.
Lemma lem2389615 (m : int) (h1 : term99 m) : (term91 m) = term66.
Proof. exact (proj1 (@lem2389605 m h1)). Qed.
Lemma lem2389616 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : (div m n) = term66.
Proof. exact (TRANS (@lem2389613 m n h2) (@lem2389615 m h1)). Qed.
Lemma lem2389617 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2389618 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : (term102 m n) = term103.
Proof. exact (MK_COMB (@lem2389617) (@lem2389616 m n h1 h2)). Qed.
Lemma lem2389620 (n : int) (h1 : n = term66) : n = term66.
Proof. exact (h1). Qed.
Lemma lem2389621 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : (term104 m n) = term105.
Proof. exact (MK_COMB (@lem2389618 m n h1 h2) (@lem2389620 n h2)). Qed.
Lemma lem2389622 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2389623 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : (term106 m n) = term107.
Proof. exact (MK_COMB (@lem2389622) (@lem2389621 m n h1 h2)). Qed.
Lemma lem2389625 (n : int) (h1 : n = term66) : n = term66.
Proof. exact (h1). Qed.
Lemma lem2389626 (m : int) : (rem m) = (rem m).
Proof. exact (eq_refl (rem m)). Qed.
Lemma lem2389627 (m : int) (n : int) (h1 : n = term66) : (rem m n) = (term96 m).
Proof. exact (MK_COMB (@lem2389626 m) (@lem2389625 n h1)). Qed.
Lemma lem2389629 (m : int) (h1 : term99 m) : (term96 m) = m.
Proof. exact (proj2 (@lem2389605 m h1)). Qed.
Lemma lem2389630 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : (rem m n) = m.
Proof. exact (TRANS (@lem2389627 m n h2) (@lem2389629 m h1)). Qed.
Lemma lem2389631 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : (term42 m n) = (term108 m).
Proof. exact (MK_COMB (@lem2389623 m n h1 h2) (@lem2389630 m n h1 h2)). Qed.
Lemma lem2389632 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2389633 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : (term109 m n) = (term110 m).
Proof. exact (MK_COMB (@lem2389632) (@lem2389631 m n h1 h2)). Qed.
Lemma lem2389634 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2389635 (m : int) (n : int) (h1 : term99 m) (h2 : n = term66) : ((term42 m n) = m) = ((term108 m) = m).
Proof. exact (MK_COMB (@lem2389633 m n h1 h2) (@lem2389634 m)). Qed.
Lemma lem2389638 (m : int) (n : int) (h1 : n = term66) : term111 n m.
Proof. exact (fun h0 : term99 m => @lem2389635 m n h0 h1). Qed.
Lemma lem2389639 (m : int) (n : int) (h1 : n = term66) : term112 n m.
Proof. exact (@lem2389604 m ((term108 m) = m) n h1). Qed.
Lemma lem2389640 (m : int) (n : int) (h1 : n = term66) : (term74 n m) = (term113 m).
Proof. exact (@lem2389639 m n h1 (@lem2389638 m n h1)). Qed.
Lemma lem2389680 (m : int) (n : int) (h1 : n = term66) : (term113 m) = (term74 n m).
Proof. exact (SYM (@lem2389640 m n h1)). Qed.
Lemma lem2389749 (m : int) : (term114 m) = (term113 m).
Proof. exact (@lem2318604 (term113 m)). Qed.
Lemma lem2389782 (m : int) : (term115 m) = (term116 m).
Proof. exact (@lem17362 (term99 m) ((term108 m) = m)). Qed.
Lemma lem2389785 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2389786 (m : int) : ((term91 m) = term66) = ((term117 m) = term118).
Proof. exact (@lem2389785 (term91 m) term66). Qed.
Lemma lem2389790 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2389791 : term118 = term120.
Proof. exact (@lem2389790 (NUMERAL 0)). Qed.
Lemma lem2389792 (m : int) : (term121 m) = (term121 m).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem2389793 (m : int) : ((term117 m) = term118) = ((term117 m) = term120).
Proof. exact (MK_COMB (@lem2389792 m) (@lem2389791)). Qed.
Lemma lem2389795 (m : int) : ((term91 m) = term66) = ((term117 m) = term120).
Proof. exact (TRANS (@lem2389786 m) (@lem2389793 m)). Qed.
Lemma lem2389798 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2389802 (m : int) : ((term96 m) = m) = ((term122 m) = (real_of_int m)).
Proof. exact (@lem2389798 (term96 m) m). Qed.
Lemma lem2389803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2389804 (m : int) : (term95 m) = (term123 m).
Proof. exact (MK_COMB (@lem2389803) (@lem2389795 m)). Qed.
Lemma lem2389805 (m : int) : (term99 m) = (term124 m).
Proof. exact (MK_COMB (@lem2389804 m) (@lem2389802 m)). Qed.
Lemma lem2389807 (y : int) (x : int) : (term125 x y) = (term126 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2389808 (m : int) : (term127 m) = (term128 m).
Proof. exact (@lem2389807 m (term108 m)). Qed.
Lemma lem2389810 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2389811 (m : int) : (term130 m) = (term131 m).
Proof. exact (@lem2389810 (term132 m) m). Qed.
Lemma lem2389813 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2389814 (m : int) : (term135 m) = (term136 m).
Proof. exact (@lem2389813 (term108 m) term137). Qed.
Lemma lem2389816 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2389817 (m : int) : (term138 m) = (term139 m).
Proof. exact (@lem2389816 term105 m). Qed.
Lemma lem2389819 (x : int) (y : int) : (term140 x y) = (term141 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2389820 : term142 = term143.
Proof. exact (@lem2389819 term66 term66). Qed.
Lemma lem2389822 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2389823 : term118 = term120.
Proof. exact (@lem2389822 (NUMERAL 0)). Qed.
Lemma lem2389824 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2389825 : term144 = term145.
Proof. exact (MK_COMB (@lem2389824) (@lem2389823)). Qed.
Lemma lem2389827 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2389828 : term118 = term120.
Proof. exact (@lem2389827 (NUMERAL 0)). Qed.
Lemma lem2389829 : term143 = term146.
Proof. exact (MK_COMB (@lem2389825) (@lem2389828)). Qed.
Lemma lem2389830 : term142 = term146.
Proof. exact (TRANS (@lem2389820) (@lem2389829)). Qed.
Lemma lem2389831 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2389832 : term147 = term148.
Proof. exact (MK_COMB (@lem2389831) (@lem2389830)). Qed.
Lemma lem2389833 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2389834 (m : int) : (term139 m) = (term149 m).
Proof. exact (MK_COMB (@lem2389832) (@lem2389833 m)). Qed.
Lemma lem2389835 (m : int) : (term138 m) = (term149 m).
Proof. exact (TRANS (@lem2389817 m) (@lem2389834 m)). Qed.
Lemma lem2389836 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2389837 (m : int) : (term150 m) = (term151 m).
Proof. exact (MK_COMB (@lem2389836) (@lem2389835 m)). Qed.
Lemma lem2389839 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2389840 : term152 = term153.
Proof. exact (@lem2389839 term154). Qed.
Lemma lem2389841 (m : int) : (term136 m) = (term155 m).
Proof. exact (MK_COMB (@lem2389837 m) (@lem2389840)). Qed.
Lemma lem2389842 (m : int) : (term135 m) = (term155 m).
Proof. exact (TRANS (@lem2389814 m) (@lem2389841 m)). Qed.
Lemma lem2389843 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2389844 (m : int) : (term156 m) = (term157 m).
Proof. exact (MK_COMB (@lem2389843) (@lem2389842 m)). Qed.
Lemma lem2389845 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2389846 (m : int) : (term131 m) = (term158 m).
Proof. exact (MK_COMB (@lem2389844 m) (@lem2389845 m)). Qed.
Lemma lem2389847 (m : int) : (term130 m) = (term158 m).
Proof. exact (TRANS (@lem2389811 m) (@lem2389846 m)). Qed.
Lemma lem2389848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2389849 (m : int) : (term159 m) = (term160 m).
Proof. exact (MK_COMB (@lem2389848) (@lem2389847 m)). Qed.
Lemma lem2389851 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2389852 (m : int) : (term161 m) = (term162 m).
Proof. exact (@lem2389851 (term163 m) (term108 m)). Qed.
Lemma lem2389854 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2389855 (m : int) : (term164 m) = (term165 m).
Proof. exact (@lem2389854 m term137). Qed.
Lemma lem2389857 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2389858 : term152 = term153.
Proof. exact (@lem2389857 term154). Qed.
Lemma lem2389859 (m : int) : (term166 m) = (term166 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem2389860 (m : int) : (term165 m) = (term167 m).
Proof. exact (MK_COMB (@lem2389859 m) (@lem2389858)). Qed.
Lemma lem2389861 (m : int) : (term164 m) = (term167 m).
Proof. exact (TRANS (@lem2389855 m) (@lem2389860 m)). Qed.
Lemma lem2389862 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2389863 (m : int) : (term168 m) = (term169 m).
Proof. exact (MK_COMB (@lem2389862) (@lem2389861 m)). Qed.
Lemma lem2389865 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2389866 (m : int) : (term138 m) = (term139 m).
Proof. exact (@lem2389865 term105 m). Qed.
Lemma lem2389868 (x : int) (y : int) : (term140 x y) = (term141 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2389869 : term142 = term143.
Proof. exact (@lem2389868 term66 term66). Qed.
Lemma lem2389871 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2389872 : term118 = term120.
Proof. exact (@lem2389871 (NUMERAL 0)). Qed.
Lemma lem2389873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2389874 : term144 = term145.
Proof. exact (MK_COMB (@lem2389873) (@lem2389872)). Qed.
Lemma lem2389876 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2389877 : term118 = term120.
Proof. exact (@lem2389876 (NUMERAL 0)). Qed.
Lemma lem2389878 : term143 = term146.
Proof. exact (MK_COMB (@lem2389874) (@lem2389877)). Qed.
Lemma lem2389879 : term142 = term146.
Proof. exact (TRANS (@lem2389869) (@lem2389878)). Qed.
Lemma lem2389880 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2389881 : term147 = term148.
Proof. exact (MK_COMB (@lem2389880) (@lem2389879)). Qed.
Lemma lem2389882 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2389883 (m : int) : (term139 m) = (term149 m).
Proof. exact (MK_COMB (@lem2389881) (@lem2389882 m)). Qed.
Lemma lem2389884 (m : int) : (term138 m) = (term149 m).
Proof. exact (TRANS (@lem2389866 m) (@lem2389883 m)). Qed.
Lemma lem2389885 (m : int) : (term162 m) = (term170 m).
Proof. exact (MK_COMB (@lem2389863 m) (@lem2389884 m)). Qed.
Lemma lem2389886 (m : int) : (term161 m) = (term170 m).
Proof. exact (TRANS (@lem2389852 m) (@lem2389885 m)). Qed.
Lemma lem2389887 (m : int) : (term128 m) = (term171 m).
Proof. exact (MK_COMB (@lem2389849 m) (@lem2389886 m)). Qed.
Lemma lem2389888 (m : int) : (term127 m) = (term171 m).
Proof. exact (TRANS (@lem2389808 m) (@lem2389887 m)). Qed.
Lemma lem2389889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2389890 (m : int) : (term172 m) = (term173 m).
Proof. exact (MK_COMB (@lem2389889) (@lem2389805 m)). Qed.
Lemma lem2389891 (m : int) : (term116 m) = (term174 m).
Proof. exact (MK_COMB (@lem2389890 m) (@lem2389888 m)). Qed.
Lemma lem2389892 (m : int) : (term115 m) = (term174 m).
Proof. exact (TRANS (@lem2389782 m) (@lem2389891 m)). Qed.
Lemma lem2389896 (t : Prop) : (term175 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2389932 (m : int) : (term176 m) = (term174 m).
Proof. exact (@lem2389896 (term174 m)). Qed.
Lemma lem2389933 (m : int) : ((term117 m) = term120) = ((term177 m) = term120).
Proof. exact (@lem1988293 (term117 m) term120). Qed.
Lemma lem2389939 (m : int) : (term177 m) = (term178 m).
Proof. exact (@lem1982792 (term117 m) term120). Qed.
Lemma lem2389941 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2389942 : term120 = term180.
Proof. exact (@lem2389941 (NUMERAL 0)). Qed.
Lemma lem2389944 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2389945 : term183 = term184.
Proof. exact (@lem2389944 term154). Qed.
Lemma lem2389946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2389947 : term185 = term186.
Proof. exact (MK_COMB (@lem2389946) (@lem2389945)). Qed.
Lemma lem2389948 : term187 = term188.
Proof. exact (MK_COMB (@lem2389947) (@lem2389942)). Qed.
Lemma lem2389949 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2389951 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2389952 : term192 = term193.
Proof. exact (@lem2389951 term154 term154). Qed.
Lemma lem2389953 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2389954 : term195 = term154.
Proof. exact (EQ_MP (@lem2389953) (@lem940073)). Qed.
Lemma lem2389955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2389956 : term193 = term153.
Proof. exact (MK_COMB (@lem2389955) (@lem2389954)). Qed.
Lemma lem2389957 : term192 = term153.
Proof. exact (TRANS (@lem2389952) (@lem2389956)). Qed.
Lemma lem2389959 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2389960 : term187 = term120.
Proof. exact (@lem2389959 term154). Qed.
Lemma lem2389961 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2389962 : term197 = term198.
Proof. exact (MK_COMB (@lem2389961) (@lem2389960)). Qed.
Lemma lem2389963 : term189 = term180.
Proof. exact (MK_COMB (@lem2389962) (@lem2389957)). Qed.
Lemma lem2389964 : term188 = term180.
Proof. exact (TRANS (@lem2389949) (@lem2389963)). Qed.
Lemma lem2389965 : term187 = term180.
Proof. exact (TRANS (@lem2389948) (@lem2389964)). Qed.
Lemma lem2389967 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2389968 : term180 = term120.
Proof. exact (@lem2389967 term120). Qed.
Lemma lem2389969 : term187 = term120.
Proof. exact (TRANS (@lem2389965) (@lem2389968)). Qed.
Lemma lem2389970 (m : int) : (term200 m) = (term200 m).
Proof. exact (eq_refl (term200 m)). Qed.
Lemma lem2389971 (m : int) : (term178 m) = (term201 m).
Proof. exact (MK_COMB (@lem2389970 m) (@lem2389969)). Qed.
Lemma lem2389972 (m : int) : (term201 m) = (term117 m).
Proof. exact (@lem1982723 (term117 m)). Qed.
Lemma lem2389973 (m : int) : (term178 m) = (term117 m).
Proof. exact (TRANS (@lem2389971 m) (@lem2389972 m)). Qed.
Lemma lem2389975 (m : int) : (term177 m) = (term117 m).
Proof. exact (TRANS (@lem2389939 m) (@lem2389973 m)). Qed.
Lemma lem2389976 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2389977 (m : int) : (term202 m) = (term121 m).
Proof. exact (MK_COMB (@lem2389976) (@lem2389975 m)). Qed.
Lemma lem2389978 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2389979 (m : int) : ((term177 m) = term120) = ((term117 m) = term120).
Proof. exact (MK_COMB (@lem2389977 m) (@lem2389978)). Qed.
Lemma lem2389980 (m : int) : ((term117 m) = term120) = ((term117 m) = term120).
Proof. exact (TRANS (@lem2389933 m) (@lem2389979 m)). Qed.
Lemma lem2389981 (m : int) : ((term122 m) = (real_of_int m)) = ((term203 m) = term120).
Proof. exact (@lem1988293 (term122 m) (real_of_int m)). Qed.
Lemma lem2389987 (m : int) : (term203 m) = (term204 m).
Proof. exact (@lem1982792 (term122 m) (real_of_int m)). Qed.
Lemma lem2389992 (m : int) : (term204 m) = (term205 m).
Proof. exact (@lem1982761 (term206 m) (term122 m)). Qed.
Lemma lem2389994 (m : int) : (term203 m) = (term205 m).
Proof. exact (TRANS (@lem2389987 m) (@lem2389992 m)). Qed.
Lemma lem2389995 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2389996 (m : int) : (term207 m) = (term208 m).
Proof. exact (MK_COMB (@lem2389995) (@lem2389994 m)). Qed.
Lemma lem2389997 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2389998 (m : int) : ((term203 m) = term120) = ((term205 m) = term120).
Proof. exact (MK_COMB (@lem2389996 m) (@lem2389997)). Qed.
Lemma lem2389999 (m : int) : ((term122 m) = (real_of_int m)) = ((term205 m) = term120).
Proof. exact (TRANS (@lem2389981 m) (@lem2389998 m)). Qed.
Lemma lem2390000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390001 (m : int) : (term123 m) = (term123 m).
Proof. exact (MK_COMB (@lem2390000) (@lem2389980 m)). Qed.
Lemma lem2390002 (m : int) : (term124 m) = (term209 m).
Proof. exact (MK_COMB (@lem2390001 m) (@lem2389999 m)). Qed.
Lemma lem2390003 (m : int) : (term158 m) = (term210 m).
Proof. exact (@lem1988287 (real_of_int m) (term155 m)). Qed.
Lemma lem2390004 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2390005 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2390012 : term146 = term120.
Proof. exact (@lem1982729 term120). Qed.
Lemma lem2390013 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390014 : term148 = term211.
Proof. exact (MK_COMB (@lem2390013) (@lem2390012)). Qed.
Lemma lem2390015 (m : int) : (term149 m) = (term212 m).
Proof. exact (MK_COMB (@lem2390014) (@lem2390005 m)). Qed.
Lemma lem2390016 (m : int) : (term212 m) = (real_of_int m).
Proof. exact (@lem1982721 (real_of_int m)). Qed.
Lemma lem2390017 (m : int) : (term149 m) = (real_of_int m).
Proof. exact (TRANS (@lem2390015 m) (@lem2390016 m)). Qed.
Lemma lem2390018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390019 (m : int) : (term151 m) = (term166 m).
Proof. exact (MK_COMB (@lem2390018) (@lem2390017 m)). Qed.
Lemma lem2390022 (m : int) : (term155 m) = (term167 m).
Proof. exact (MK_COMB (@lem2390019 m) (@lem2390004)). Qed.
Lemma lem2390025 (m : int) : (term213 m) = (term213 m).
Proof. exact (eq_refl (term213 m)). Qed.
Lemma lem2390026 (m : int) : (term214 m) = (term215 m).
Proof. exact (MK_COMB (@lem2390025 m) (@lem2390022 m)). Qed.
Lemma lem2390027 (m : int) : (term215 m) = (term216 m).
Proof. exact (@lem1982792 (real_of_int m) (term167 m)). Qed.
Lemma lem2390028 (m : int) : (term217 m) = (term218 m).
Proof. exact (@lem1982781 (real_of_int m) term183 term153). Qed.
Lemma lem2390030 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390031 : term153 = term219.
Proof. exact (@lem2390030 term154). Qed.
Lemma lem2390033 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390034 : term183 = term184.
Proof. exact (@lem2390033 term154). Qed.
Lemma lem2390035 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390036 : term185 = term186.
Proof. exact (MK_COMB (@lem2390035) (@lem2390034)). Qed.
Lemma lem2390037 : term220 = term221.
Proof. exact (MK_COMB (@lem2390036) (@lem2390031)). Qed.
Lemma lem2390038 : term221 = term222.
Proof. exact (@lem1981613 term183 term153 term153 term153). Qed.
Lemma lem2390040 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390041 : term192 = term193.
Proof. exact (@lem2390040 term154 term154). Qed.
Lemma lem2390042 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390043 : term195 = term154.
Proof. exact (EQ_MP (@lem2390042) (@lem940073)). Qed.
Lemma lem2390044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390045 : term193 = term153.
Proof. exact (MK_COMB (@lem2390044) (@lem2390043)). Qed.
Lemma lem2390046 : term192 = term153.
Proof. exact (TRANS (@lem2390041) (@lem2390045)). Qed.
Lemma lem2390048 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2390049 : term220 = term225.
Proof. exact (@lem2390048 term154 term154). Qed.
Lemma lem2390050 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390051 : term195 = term154.
Proof. exact (EQ_MP (@lem2390050) (@lem940073)). Qed.
Lemma lem2390052 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390053 : term193 = term153.
Proof. exact (MK_COMB (@lem2390052) (@lem2390051)). Qed.
Lemma lem2390054 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2390055 : term225 = term183.
Proof. exact (MK_COMB (@lem2390054) (@lem2390053)). Qed.
Lemma lem2390056 : term220 = term183.
Proof. exact (TRANS (@lem2390049) (@lem2390055)). Qed.
Lemma lem2390057 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2390058 : term226 = term227.
Proof. exact (MK_COMB (@lem2390057) (@lem2390056)). Qed.
Lemma lem2390059 : term222 = term184.
Proof. exact (MK_COMB (@lem2390058) (@lem2390046)). Qed.
Lemma lem2390060 : term221 = term184.
Proof. exact (TRANS (@lem2390038) (@lem2390059)). Qed.
Lemma lem2390061 : term220 = term184.
Proof. exact (TRANS (@lem2390037) (@lem2390060)). Qed.
Lemma lem2390063 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2390064 : term184 = term183.
Proof. exact (@lem2390063 term183). Qed.
Lemma lem2390065 : term220 = term183.
Proof. exact (TRANS (@lem2390061) (@lem2390064)). Qed.
Lemma lem2390068 (m : int) : (term228 m) = (term228 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem2390069 (m : int) : (term218 m) = (term229 m).
Proof. exact (MK_COMB (@lem2390068 m) (@lem2390065)). Qed.
Lemma lem2390070 (m : int) : (term217 m) = (term229 m).
Proof. exact (TRANS (@lem2390028 m) (@lem2390069 m)). Qed.
Lemma lem2390071 (m : int) : (term166 m) = (term166 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem2390072 (m : int) : (term216 m) = (term230 m).
Proof. exact (MK_COMB (@lem2390071 m) (@lem2390070 m)). Qed.
Lemma lem2390073 (m : int) : (term230 m) = (term231 m).
Proof. exact (@lem1982763 (real_of_int m) (term206 m) term183). Qed.
Lemma lem2390074 (m : int) : (term232 m) = (term233 m).
Proof. exact (@lem1982715 term183 (real_of_int m)). Qed.
Lemma lem2390076 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390077 : term153 = term219.
Proof. exact (@lem2390076 term154). Qed.
Lemma lem2390079 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390080 : term183 = term184.
Proof. exact (@lem2390079 term154). Qed.
Lemma lem2390081 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390082 : term234 = term235.
Proof. exact (MK_COMB (@lem2390081) (@lem2390080)). Qed.
Lemma lem2390083 : term236 = term237.
Proof. exact (MK_COMB (@lem2390082) (@lem2390077)). Qed.
Lemma lem2390084 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2390086 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390087 : term240 = term241.
Proof. exact (@lem2390086 (NUMERAL 0) term154). Qed.
Lemma lem2390088 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390089 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390090 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390089 h1) (fun h1 : term241 = True => @lem2390088)). Qed.
Lemma lem2390091 : term241 = True.
Proof. exact (EQ_MP (@lem2390090) (@lem2390088)). Qed.
Lemma lem2390092 : term240 = True.
Proof. exact (TRANS (@lem2390087) (@lem2390091)). Qed.
Lemma lem2390093 : True = term240.
Proof. exact (SYM (@lem2390092)). Qed.
Lemma lem2390094 : term240.
Proof. exact (EQ_MP (@lem2390093) (@lem0)). Qed.
Lemma lem2390095 : term243.
Proof. exact (@lem2390084 (@lem2390094)). Qed.
Lemma lem2390097 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390098 : term240 = term241.
Proof. exact (@lem2390097 (NUMERAL 0) term154). Qed.
Lemma lem2390099 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390100 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390101 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390100 h1) (fun h1 : term241 = True => @lem2390099)). Qed.
Lemma lem2390102 : term241 = True.
Proof. exact (EQ_MP (@lem2390101) (@lem2390099)). Qed.
Lemma lem2390103 : term240 = True.
Proof. exact (TRANS (@lem2390098) (@lem2390102)). Qed.
Lemma lem2390104 : True = term240.
Proof. exact (SYM (@lem2390103)). Qed.
Lemma lem2390105 : term240.
Proof. exact (EQ_MP (@lem2390104) (@lem0)). Qed.
Lemma lem2390106 : term244.
Proof. exact (@lem2390095 (@lem2390105)). Qed.
Lemma lem2390108 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390109 : term240 = term241.
Proof. exact (@lem2390108 (NUMERAL 0) term154). Qed.
Lemma lem2390110 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390111 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390112 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390111 h1) (fun h1 : term241 = True => @lem2390110)). Qed.
Lemma lem2390113 : term241 = True.
Proof. exact (EQ_MP (@lem2390112) (@lem2390110)). Qed.
Lemma lem2390114 : term240 = True.
Proof. exact (TRANS (@lem2390109) (@lem2390113)). Qed.
Lemma lem2390115 : True = term240.
Proof. exact (SYM (@lem2390114)). Qed.
Lemma lem2390116 : term240.
Proof. exact (EQ_MP (@lem2390115) (@lem0)). Qed.
Lemma lem2390117 : term245.
Proof. exact (@lem2390106 (@lem2390116)). Qed.
Lemma lem2390119 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390120 : term192 = term193.
Proof. exact (@lem2390119 term154 term154). Qed.
Lemma lem2390121 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390122 : term195 = term154.
Proof. exact (EQ_MP (@lem2390121) (@lem940073)). Qed.
Lemma lem2390123 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390124 : term193 = term153.
Proof. exact (MK_COMB (@lem2390123) (@lem2390122)). Qed.
Lemma lem2390125 : term192 = term153.
Proof. exact (TRANS (@lem2390120) (@lem2390124)). Qed.
Lemma lem2390127 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2390128 : term220 = term225.
Proof. exact (@lem2390127 term154 term154). Qed.
Lemma lem2390129 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390130 : term195 = term154.
Proof. exact (EQ_MP (@lem2390129) (@lem940073)). Qed.
Lemma lem2390131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390132 : term193 = term153.
Proof. exact (MK_COMB (@lem2390131) (@lem2390130)). Qed.
Lemma lem2390133 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2390134 : term225 = term183.
Proof. exact (MK_COMB (@lem2390133) (@lem2390132)). Qed.
Lemma lem2390135 : term220 = term183.
Proof. exact (TRANS (@lem2390128) (@lem2390134)). Qed.
Lemma lem2390136 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390137 : term246 = term234.
Proof. exact (MK_COMB (@lem2390136) (@lem2390135)). Qed.
Lemma lem2390138 : term247 = term236.
Proof. exact (MK_COMB (@lem2390137) (@lem2390125)). Qed.
Lemma lem2390140 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2390141 : term236 = term120.
Proof. exact (@lem2390140 term154). Qed.
Lemma lem2390142 : term247 = term120.
Proof. exact (TRANS (@lem2390138) (@lem2390141)). Qed.
Lemma lem2390143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390144 : term249 = term145.
Proof. exact (MK_COMB (@lem2390143) (@lem2390142)). Qed.
Lemma lem2390145 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2390146 : term250 = term251.
Proof. exact (MK_COMB (@lem2390144) (@lem2390145)). Qed.
Lemma lem2390148 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2390149 : term251 = term120.
Proof. exact (@lem2390148 term154). Qed.
Lemma lem2390150 : term250 = term120.
Proof. exact (TRANS (@lem2390146) (@lem2390149)). Qed.
Lemma lem2390152 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390153 : term192 = term193.
Proof. exact (@lem2390152 term154 term154). Qed.
Lemma lem2390154 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390155 : term195 = term154.
Proof. exact (EQ_MP (@lem2390154) (@lem940073)). Qed.
Lemma lem2390156 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390157 : term193 = term153.
Proof. exact (MK_COMB (@lem2390156) (@lem2390155)). Qed.
Lemma lem2390158 : term192 = term153.
Proof. exact (TRANS (@lem2390153) (@lem2390157)). Qed.
Lemma lem2390159 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2390160 : term253 = term251.
Proof. exact (MK_COMB (@lem2390159) (@lem2390158)). Qed.
Lemma lem2390162 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2390163 : term251 = term120.
Proof. exact (@lem2390162 term154). Qed.
Lemma lem2390164 : term253 = term120.
Proof. exact (TRANS (@lem2390160) (@lem2390163)). Qed.
Lemma lem2390165 : term120 = term253.
Proof. exact (SYM (@lem2390164)). Qed.
Lemma lem2390166 : term250 = term253.
Proof. exact (TRANS (@lem2390150) (@lem2390165)). Qed.
Lemma lem2390167 : term237 = term180.
Proof. exact (@lem2390117 (@lem2390166)). Qed.
Lemma lem2390168 : term236 = term180.
Proof. exact (TRANS (@lem2390083) (@lem2390167)). Qed.
Lemma lem2390170 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2390171 : term180 = term120.
Proof. exact (@lem2390170 term120). Qed.
Lemma lem2390172 : term236 = term120.
Proof. exact (TRANS (@lem2390168) (@lem2390171)). Qed.
Lemma lem2390173 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390174 : term254 = term145.
Proof. exact (MK_COMB (@lem2390173) (@lem2390172)). Qed.
Lemma lem2390175 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2390176 (m : int) : (term233 m) = (term255 m).
Proof. exact (MK_COMB (@lem2390174) (@lem2390175 m)). Qed.
Lemma lem2390177 (m : int) : (term232 m) = (term255 m).
Proof. exact (TRANS (@lem2390074 m) (@lem2390176 m)). Qed.
Lemma lem2390178 (m : int) : (term255 m) = term120.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2390179 (m : int) : (term232 m) = term120.
Proof. exact (TRANS (@lem2390177 m) (@lem2390178 m)). Qed.
Lemma lem2390180 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390181 (m : int) : (term256 m) = term211.
Proof. exact (MK_COMB (@lem2390180) (@lem2390179 m)). Qed.
Lemma lem2390182 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2390183 (m : int) : (term231 m) = term257.
Proof. exact (MK_COMB (@lem2390181 m) (@lem2390182)). Qed.
Lemma lem2390184 (m : int) : (term230 m) = term257.
Proof. exact (TRANS (@lem2390073 m) (@lem2390183 m)). Qed.
Lemma lem2390185 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2390186 (m : int) : (term230 m) = term183.
Proof. exact (TRANS (@lem2390184 m) (@lem2390185)). Qed.
Lemma lem2390187 (m : int) : (term216 m) = term183.
Proof. exact (TRANS (@lem2390072 m) (@lem2390186 m)). Qed.
Lemma lem2390188 (m : int) : (term215 m) = term183.
Proof. exact (TRANS (@lem2390027 m) (@lem2390187 m)). Qed.
Lemma lem2390189 (m : int) : (term214 m) = term183.
Proof. exact (TRANS (@lem2390026 m) (@lem2390188 m)). Qed.
Lemma lem2390190 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2390191 (m : int) : (term258 m) = term259.
Proof. exact (MK_COMB (@lem2390190) (@lem2390189 m)). Qed.
Lemma lem2390192 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2390193 (m : int) : (term210 m) = term260.
Proof. exact (MK_COMB (@lem2390191 m) (@lem2390192)). Qed.
Lemma lem2390194 (m : int) : (term158 m) = term260.
Proof. exact (TRANS (@lem2390003 m) (@lem2390193 m)). Qed.
Lemma lem2390195 (m : int) : (term170 m) = (term261 m).
Proof. exact (@lem1988287 (term149 m) (term167 m)). Qed.
Lemma lem2390202 (m : int) : (term167 m) = (term167 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem2390203 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2390210 : term146 = term120.
Proof. exact (@lem1982729 term120). Qed.
Lemma lem2390211 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390212 : term148 = term211.
Proof. exact (MK_COMB (@lem2390211) (@lem2390210)). Qed.
Lemma lem2390213 (m : int) : (term149 m) = (term212 m).
Proof. exact (MK_COMB (@lem2390212) (@lem2390203 m)). Qed.
Lemma lem2390214 (m : int) : (term212 m) = (real_of_int m).
Proof. exact (@lem1982721 (real_of_int m)). Qed.
Lemma lem2390215 (m : int) : (term149 m) = (real_of_int m).
Proof. exact (TRANS (@lem2390213 m) (@lem2390214 m)). Qed.
Lemma lem2390216 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2390217 (m : int) : (term262 m) = (term213 m).
Proof. exact (MK_COMB (@lem2390216) (@lem2390215 m)). Qed.
Lemma lem2390218 (m : int) : (term263 m) = (term215 m).
Proof. exact (MK_COMB (@lem2390217 m) (@lem2390202 m)). Qed.
Lemma lem2390219 (m : int) : (term215 m) = (term216 m).
Proof. exact (@lem1982792 (real_of_int m) (term167 m)). Qed.
Lemma lem2390220 (m : int) : (term217 m) = (term218 m).
Proof. exact (@lem1982781 (real_of_int m) term183 term153). Qed.
Lemma lem2390222 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390223 : term153 = term219.
Proof. exact (@lem2390222 term154). Qed.
Lemma lem2390225 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390226 : term183 = term184.
Proof. exact (@lem2390225 term154). Qed.
Lemma lem2390227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390228 : term185 = term186.
Proof. exact (MK_COMB (@lem2390227) (@lem2390226)). Qed.
Lemma lem2390229 : term220 = term221.
Proof. exact (MK_COMB (@lem2390228) (@lem2390223)). Qed.
Lemma lem2390230 : term221 = term222.
Proof. exact (@lem1981613 term183 term153 term153 term153). Qed.
Lemma lem2390232 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390233 : term192 = term193.
Proof. exact (@lem2390232 term154 term154). Qed.
Lemma lem2390234 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390235 : term195 = term154.
Proof. exact (EQ_MP (@lem2390234) (@lem940073)). Qed.
Lemma lem2390236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390237 : term193 = term153.
Proof. exact (MK_COMB (@lem2390236) (@lem2390235)). Qed.
Lemma lem2390238 : term192 = term153.
Proof. exact (TRANS (@lem2390233) (@lem2390237)). Qed.
Lemma lem2390240 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2390241 : term220 = term225.
Proof. exact (@lem2390240 term154 term154). Qed.
Lemma lem2390242 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390243 : term195 = term154.
Proof. exact (EQ_MP (@lem2390242) (@lem940073)). Qed.
Lemma lem2390244 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390245 : term193 = term153.
Proof. exact (MK_COMB (@lem2390244) (@lem2390243)). Qed.
Lemma lem2390246 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2390247 : term225 = term183.
Proof. exact (MK_COMB (@lem2390246) (@lem2390245)). Qed.
Lemma lem2390248 : term220 = term183.
Proof. exact (TRANS (@lem2390241) (@lem2390247)). Qed.
Lemma lem2390249 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2390250 : term226 = term227.
Proof. exact (MK_COMB (@lem2390249) (@lem2390248)). Qed.
Lemma lem2390251 : term222 = term184.
Proof. exact (MK_COMB (@lem2390250) (@lem2390238)). Qed.
Lemma lem2390252 : term221 = term184.
Proof. exact (TRANS (@lem2390230) (@lem2390251)). Qed.
Lemma lem2390253 : term220 = term184.
Proof. exact (TRANS (@lem2390229) (@lem2390252)). Qed.
Lemma lem2390255 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2390256 : term184 = term183.
Proof. exact (@lem2390255 term183). Qed.
Lemma lem2390257 : term220 = term183.
Proof. exact (TRANS (@lem2390253) (@lem2390256)). Qed.
Lemma lem2390260 (m : int) : (term228 m) = (term228 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem2390261 (m : int) : (term218 m) = (term229 m).
Proof. exact (MK_COMB (@lem2390260 m) (@lem2390257)). Qed.
Lemma lem2390262 (m : int) : (term217 m) = (term229 m).
Proof. exact (TRANS (@lem2390220 m) (@lem2390261 m)). Qed.
Lemma lem2390263 (m : int) : (term166 m) = (term166 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem2390264 (m : int) : (term216 m) = (term230 m).
Proof. exact (MK_COMB (@lem2390263 m) (@lem2390262 m)). Qed.
Lemma lem2390265 (m : int) : (term230 m) = (term231 m).
Proof. exact (@lem1982763 (real_of_int m) (term206 m) term183). Qed.
Lemma lem2390266 (m : int) : (term232 m) = (term233 m).
Proof. exact (@lem1982715 term183 (real_of_int m)). Qed.
Lemma lem2390268 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390269 : term153 = term219.
Proof. exact (@lem2390268 term154). Qed.
Lemma lem2390271 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390272 : term183 = term184.
Proof. exact (@lem2390271 term154). Qed.
Lemma lem2390273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390274 : term234 = term235.
Proof. exact (MK_COMB (@lem2390273) (@lem2390272)). Qed.
Lemma lem2390275 : term236 = term237.
Proof. exact (MK_COMB (@lem2390274) (@lem2390269)). Qed.
Lemma lem2390276 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2390278 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390279 : term240 = term241.
Proof. exact (@lem2390278 (NUMERAL 0) term154). Qed.
Lemma lem2390280 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390281 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390282 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390281 h1) (fun h1 : term241 = True => @lem2390280)). Qed.
Lemma lem2390283 : term241 = True.
Proof. exact (EQ_MP (@lem2390282) (@lem2390280)). Qed.
Lemma lem2390284 : term240 = True.
Proof. exact (TRANS (@lem2390279) (@lem2390283)). Qed.
Lemma lem2390285 : True = term240.
Proof. exact (SYM (@lem2390284)). Qed.
Lemma lem2390286 : term240.
Proof. exact (EQ_MP (@lem2390285) (@lem0)). Qed.
Lemma lem2390287 : term243.
Proof. exact (@lem2390276 (@lem2390286)). Qed.
Lemma lem2390289 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390290 : term240 = term241.
Proof. exact (@lem2390289 (NUMERAL 0) term154). Qed.
Lemma lem2390291 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390292 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390293 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390292 h1) (fun h1 : term241 = True => @lem2390291)). Qed.
Lemma lem2390294 : term241 = True.
Proof. exact (EQ_MP (@lem2390293) (@lem2390291)). Qed.
Lemma lem2390295 : term240 = True.
Proof. exact (TRANS (@lem2390290) (@lem2390294)). Qed.
Lemma lem2390296 : True = term240.
Proof. exact (SYM (@lem2390295)). Qed.
Lemma lem2390297 : term240.
Proof. exact (EQ_MP (@lem2390296) (@lem0)). Qed.
Lemma lem2390298 : term244.
Proof. exact (@lem2390287 (@lem2390297)). Qed.
Lemma lem2390300 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390301 : term240 = term241.
Proof. exact (@lem2390300 (NUMERAL 0) term154). Qed.
Lemma lem2390302 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390303 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390304 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390303 h1) (fun h1 : term241 = True => @lem2390302)). Qed.
Lemma lem2390305 : term241 = True.
Proof. exact (EQ_MP (@lem2390304) (@lem2390302)). Qed.
Lemma lem2390306 : term240 = True.
Proof. exact (TRANS (@lem2390301) (@lem2390305)). Qed.
Lemma lem2390307 : True = term240.
Proof. exact (SYM (@lem2390306)). Qed.
Lemma lem2390308 : term240.
Proof. exact (EQ_MP (@lem2390307) (@lem0)). Qed.
Lemma lem2390309 : term245.
Proof. exact (@lem2390298 (@lem2390308)). Qed.
Lemma lem2390311 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390312 : term192 = term193.
Proof. exact (@lem2390311 term154 term154). Qed.
Lemma lem2390313 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390314 : term195 = term154.
Proof. exact (EQ_MP (@lem2390313) (@lem940073)). Qed.
Lemma lem2390315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390316 : term193 = term153.
Proof. exact (MK_COMB (@lem2390315) (@lem2390314)). Qed.
Lemma lem2390317 : term192 = term153.
Proof. exact (TRANS (@lem2390312) (@lem2390316)). Qed.
Lemma lem2390319 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2390320 : term220 = term225.
Proof. exact (@lem2390319 term154 term154). Qed.
Lemma lem2390321 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390322 : term195 = term154.
Proof. exact (EQ_MP (@lem2390321) (@lem940073)). Qed.
Lemma lem2390323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390324 : term193 = term153.
Proof. exact (MK_COMB (@lem2390323) (@lem2390322)). Qed.
Lemma lem2390325 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2390326 : term225 = term183.
Proof. exact (MK_COMB (@lem2390325) (@lem2390324)). Qed.
Lemma lem2390327 : term220 = term183.
Proof. exact (TRANS (@lem2390320) (@lem2390326)). Qed.
Lemma lem2390328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390329 : term246 = term234.
Proof. exact (MK_COMB (@lem2390328) (@lem2390327)). Qed.
Lemma lem2390330 : term247 = term236.
Proof. exact (MK_COMB (@lem2390329) (@lem2390317)). Qed.
Lemma lem2390332 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2390333 : term236 = term120.
Proof. exact (@lem2390332 term154). Qed.
Lemma lem2390334 : term247 = term120.
Proof. exact (TRANS (@lem2390330) (@lem2390333)). Qed.
Lemma lem2390335 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390336 : term249 = term145.
Proof. exact (MK_COMB (@lem2390335) (@lem2390334)). Qed.
Lemma lem2390337 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2390338 : term250 = term251.
Proof. exact (MK_COMB (@lem2390336) (@lem2390337)). Qed.
Lemma lem2390340 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2390341 : term251 = term120.
Proof. exact (@lem2390340 term154). Qed.
Lemma lem2390342 : term250 = term120.
Proof. exact (TRANS (@lem2390338) (@lem2390341)). Qed.
Lemma lem2390344 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390345 : term192 = term193.
Proof. exact (@lem2390344 term154 term154). Qed.
Lemma lem2390346 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390347 : term195 = term154.
Proof. exact (EQ_MP (@lem2390346) (@lem940073)). Qed.
Lemma lem2390348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390349 : term193 = term153.
Proof. exact (MK_COMB (@lem2390348) (@lem2390347)). Qed.
Lemma lem2390350 : term192 = term153.
Proof. exact (TRANS (@lem2390345) (@lem2390349)). Qed.
Lemma lem2390351 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2390352 : term253 = term251.
Proof. exact (MK_COMB (@lem2390351) (@lem2390350)). Qed.
Lemma lem2390354 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2390355 : term251 = term120.
Proof. exact (@lem2390354 term154). Qed.
Lemma lem2390356 : term253 = term120.
Proof. exact (TRANS (@lem2390352) (@lem2390355)). Qed.
Lemma lem2390357 : term120 = term253.
Proof. exact (SYM (@lem2390356)). Qed.
Lemma lem2390358 : term250 = term253.
Proof. exact (TRANS (@lem2390342) (@lem2390357)). Qed.
Lemma lem2390359 : term237 = term180.
Proof. exact (@lem2390309 (@lem2390358)). Qed.
Lemma lem2390360 : term236 = term180.
Proof. exact (TRANS (@lem2390275) (@lem2390359)). Qed.
Lemma lem2390362 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2390363 : term180 = term120.
Proof. exact (@lem2390362 term120). Qed.
Lemma lem2390364 : term236 = term120.
Proof. exact (TRANS (@lem2390360) (@lem2390363)). Qed.
Lemma lem2390365 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390366 : term254 = term145.
Proof. exact (MK_COMB (@lem2390365) (@lem2390364)). Qed.
Lemma lem2390367 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2390368 (m : int) : (term233 m) = (term255 m).
Proof. exact (MK_COMB (@lem2390366) (@lem2390367 m)). Qed.
Lemma lem2390369 (m : int) : (term232 m) = (term255 m).
Proof. exact (TRANS (@lem2390266 m) (@lem2390368 m)). Qed.
Lemma lem2390370 (m : int) : (term255 m) = term120.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2390371 (m : int) : (term232 m) = term120.
Proof. exact (TRANS (@lem2390369 m) (@lem2390370 m)). Qed.
Lemma lem2390372 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390373 (m : int) : (term256 m) = term211.
Proof. exact (MK_COMB (@lem2390372) (@lem2390371 m)). Qed.
Lemma lem2390374 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2390375 (m : int) : (term231 m) = term257.
Proof. exact (MK_COMB (@lem2390373 m) (@lem2390374)). Qed.
Lemma lem2390376 (m : int) : (term230 m) = term257.
Proof. exact (TRANS (@lem2390265 m) (@lem2390375 m)). Qed.
Lemma lem2390377 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2390378 (m : int) : (term230 m) = term183.
Proof. exact (TRANS (@lem2390376 m) (@lem2390377)). Qed.
Lemma lem2390379 (m : int) : (term216 m) = term183.
Proof. exact (TRANS (@lem2390264 m) (@lem2390378 m)). Qed.
Lemma lem2390380 (m : int) : (term215 m) = term183.
Proof. exact (TRANS (@lem2390219 m) (@lem2390379 m)). Qed.
Lemma lem2390381 (m : int) : (term263 m) = term183.
Proof. exact (TRANS (@lem2390218 m) (@lem2390380 m)). Qed.
Lemma lem2390382 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2390383 (m : int) : (term264 m) = term259.
Proof. exact (MK_COMB (@lem2390382) (@lem2390381 m)). Qed.
Lemma lem2390384 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2390385 (m : int) : (term261 m) = term260.
Proof. exact (MK_COMB (@lem2390383 m) (@lem2390384)). Qed.
Lemma lem2390386 (m : int) : (term170 m) = term260.
Proof. exact (TRANS (@lem2390195 m) (@lem2390385 m)). Qed.
Lemma lem2390387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2390388 (m : int) : (term160 m) = term265.
Proof. exact (MK_COMB (@lem2390387) (@lem2390194 m)). Qed.
Lemma lem2390389 (m : int) : (term171 m) = term266.
Proof. exact (MK_COMB (@lem2390388 m) (@lem2390386 m)). Qed.
Lemma lem2390390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390391 (m : int) : (term173 m) = (term267 m).
Proof. exact (MK_COMB (@lem2390390) (@lem2390002 m)). Qed.
Lemma lem2390392 (m : int) : (term174 m) = (term268 m).
Proof. exact (MK_COMB (@lem2390391 m) (@lem2390389 m)). Qed.
Lemma lem2390399 (m : int) : (term176 m) = (term268 m).
Proof. exact (TRANS (@lem2389932 m) (@lem2390392 m)). Qed.
Lemma lem2390422 (m : int) : (term268 m) = (term269 m).
Proof. exact (@lem19158 term260 (term209 m) term260). Qed.
Lemma lem2390423 (m : int) : (term176 m) = (term269 m).
Proof. exact (TRANS (@lem2390399 m) (@lem2390422 m)). Qed.
Lemma lem2390433 (m : int) (h1 : term269 m) : term269 m.
Proof. exact (h1). Qed.
Lemma lem2390434 (m : int) (h1 : term270 m) : term270 m.
Proof. exact (h1). Qed.
Lemma lem2390435 (m : int) (h1 : term270 m) : term260.
Proof. exact (proj2 (@lem2390434 m h1)). Qed.
Lemma lem2390440 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2390441 : term260 = term271.
Proof. exact (@lem2390440 term120 term183). Qed.
Lemma lem2390443 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390444 : term183 = term184.
Proof. exact (@lem2390443 term154). Qed.
Lemma lem2390446 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390447 : term120 = term180.
Proof. exact (@lem2390446 (NUMERAL 0)). Qed.
Lemma lem2390448 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390449 : term272 = term273.
Proof. exact (MK_COMB (@lem2390448) (@lem2390447)). Qed.
Lemma lem2390450 : term271 = term274.
Proof. exact (MK_COMB (@lem2390449) (@lem2390444)). Qed.
Lemma lem2390451 : term275.
Proof. exact (@lem1980026 term120 term153 term183 term153). Qed.
Lemma lem2390453 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390454 : term240 = term241.
Proof. exact (@lem2390453 (NUMERAL 0) term154). Qed.
Lemma lem2390455 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390456 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390457 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390456 h1) (fun h1 : term241 = True => @lem2390455)). Qed.
Lemma lem2390458 : term241 = True.
Proof. exact (EQ_MP (@lem2390457) (@lem2390455)). Qed.
Lemma lem2390459 : term240 = True.
Proof. exact (TRANS (@lem2390454) (@lem2390458)). Qed.
Lemma lem2390460 : True = term240.
Proof. exact (SYM (@lem2390459)). Qed.
Lemma lem2390461 : term240.
Proof. exact (EQ_MP (@lem2390460) (@lem0)). Qed.
Lemma lem2390462 : term276.
Proof. exact (@lem2390451 (@lem2390461)). Qed.
Lemma lem2390464 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390465 : term240 = term241.
Proof. exact (@lem2390464 (NUMERAL 0) term154). Qed.
Lemma lem2390466 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390467 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390468 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390467 h1) (fun h1 : term241 = True => @lem2390466)). Qed.
Lemma lem2390469 : term241 = True.
Proof. exact (EQ_MP (@lem2390468) (@lem2390466)). Qed.
Lemma lem2390470 : term240 = True.
Proof. exact (TRANS (@lem2390465) (@lem2390469)). Qed.
Lemma lem2390471 : True = term240.
Proof. exact (SYM (@lem2390470)). Qed.
Lemma lem2390472 : term240.
Proof. exact (EQ_MP (@lem2390471) (@lem0)). Qed.
Lemma lem2390473 : term274 = term277.
Proof. exact (@lem2390462 (@lem2390472)). Qed.
Lemma lem2390475 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2390476 : term220 = term225.
Proof. exact (@lem2390475 term154 term154). Qed.
Lemma lem2390477 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390478 : term195 = term154.
Proof. exact (EQ_MP (@lem2390477) (@lem940073)). Qed.
Lemma lem2390479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390480 : term193 = term153.
Proof. exact (MK_COMB (@lem2390479) (@lem2390478)). Qed.
Lemma lem2390481 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2390482 : term225 = term183.
Proof. exact (MK_COMB (@lem2390481) (@lem2390480)). Qed.
Lemma lem2390483 : term220 = term183.
Proof. exact (TRANS (@lem2390476) (@lem2390482)). Qed.
Lemma lem2390485 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2390486 : term251 = term120.
Proof. exact (@lem2390485 term154). Qed.
Lemma lem2390487 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390488 : term278 = term272.
Proof. exact (MK_COMB (@lem2390487) (@lem2390486)). Qed.
Lemma lem2390489 : term277 = term271.
Proof. exact (MK_COMB (@lem2390488) (@lem2390483)). Qed.
Lemma lem2390491 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2390492 : term271 = term281.
Proof. exact (@lem2390491 (NUMERAL 0) term154). Qed.
Lemma lem2390493 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390494 (h1 : term242 = (BIT1 0)) : (term154 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2390495 : (term242 = (BIT1 0)) = ((term154 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390494 h1) (fun h1 : (term154 = (NUMERAL 0)) = False => @lem2390493)). Qed.
Lemma lem2390496 : (term154 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2390495) (@lem2390493)). Qed.
Lemma lem2390497 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2390498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390499 : term282 = (and True).
Proof. exact (MK_COMB (@lem2390498) (@lem2390497)). Qed.
Lemma lem2390500 : term281 = (True /\ False).
Proof. exact (MK_COMB (@lem2390499) (@lem2390496)). Qed.
Lemma lem2390502 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2390503 : term281 = False.
Proof. exact (TRANS (@lem2390500) (@lem2390502)). Qed.
Lemma lem2390504 : term271 = False.
Proof. exact (TRANS (@lem2390492) (@lem2390503)). Qed.
Lemma lem2390505 : term277 = False.
Proof. exact (TRANS (@lem2390489) (@lem2390504)). Qed.
Lemma lem2390506 : term274 = False.
Proof. exact (TRANS (@lem2390473) (@lem2390505)). Qed.
Lemma lem2390507 : term271 = False.
Proof. exact (TRANS (@lem2390450) (@lem2390506)). Qed.
Lemma lem2390508 : term260 = False.
Proof. exact (TRANS (@lem2390441) (@lem2390507)). Qed.
Lemma lem2390509 (m : int) (h1 : term270 m) : False.
Proof. exact (EQ_MP (@lem2390508) (@lem2390435 m h1)). Qed.
Lemma lem2390510 (m : int) (h1 : term270 m) : term270 m.
Proof. exact (h1). Qed.
Lemma lem2390511 (m : int) (h1 : term270 m) : term260.
Proof. exact (proj2 (@lem2390510 m h1)). Qed.
Lemma lem2390516 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2390517 : term260 = term271.
Proof. exact (@lem2390516 term120 term183). Qed.
Lemma lem2390519 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390520 : term183 = term184.
Proof. exact (@lem2390519 term154). Qed.
Lemma lem2390522 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390523 : term120 = term180.
Proof. exact (@lem2390522 (NUMERAL 0)). Qed.
Lemma lem2390524 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390525 : term272 = term273.
Proof. exact (MK_COMB (@lem2390524) (@lem2390523)). Qed.
Lemma lem2390526 : term271 = term274.
Proof. exact (MK_COMB (@lem2390525) (@lem2390520)). Qed.
Lemma lem2390527 : term275.
Proof. exact (@lem1980026 term120 term153 term183 term153). Qed.
Lemma lem2390529 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390530 : term240 = term241.
Proof. exact (@lem2390529 (NUMERAL 0) term154). Qed.
Lemma lem2390531 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390532 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390533 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390532 h1) (fun h1 : term241 = True => @lem2390531)). Qed.
Lemma lem2390534 : term241 = True.
Proof. exact (EQ_MP (@lem2390533) (@lem2390531)). Qed.
Lemma lem2390535 : term240 = True.
Proof. exact (TRANS (@lem2390530) (@lem2390534)). Qed.
Lemma lem2390536 : True = term240.
Proof. exact (SYM (@lem2390535)). Qed.
Lemma lem2390537 : term240.
Proof. exact (EQ_MP (@lem2390536) (@lem0)). Qed.
Lemma lem2390538 : term276.
Proof. exact (@lem2390527 (@lem2390537)). Qed.
Lemma lem2390540 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2390541 : term240 = term241.
Proof. exact (@lem2390540 (NUMERAL 0) term154). Qed.
Lemma lem2390542 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390543 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2390544 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390543 h1) (fun h1 : term241 = True => @lem2390542)). Qed.
Lemma lem2390545 : term241 = True.
Proof. exact (EQ_MP (@lem2390544) (@lem2390542)). Qed.
Lemma lem2390546 : term240 = True.
Proof. exact (TRANS (@lem2390541) (@lem2390545)). Qed.
Lemma lem2390547 : True = term240.
Proof. exact (SYM (@lem2390546)). Qed.
Lemma lem2390548 : term240.
Proof. exact (EQ_MP (@lem2390547) (@lem0)). Qed.
Lemma lem2390549 : term274 = term277.
Proof. exact (@lem2390538 (@lem2390548)). Qed.
Lemma lem2390551 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2390552 : term220 = term225.
Proof. exact (@lem2390551 term154 term154). Qed.
Lemma lem2390553 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390554 : term195 = term154.
Proof. exact (EQ_MP (@lem2390553) (@lem940073)). Qed.
Lemma lem2390555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390556 : term193 = term153.
Proof. exact (MK_COMB (@lem2390555) (@lem2390554)). Qed.
Lemma lem2390557 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2390558 : term225 = term183.
Proof. exact (MK_COMB (@lem2390557) (@lem2390556)). Qed.
Lemma lem2390559 : term220 = term183.
Proof. exact (TRANS (@lem2390552) (@lem2390558)). Qed.
Lemma lem2390561 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2390562 : term251 = term120.
Proof. exact (@lem2390561 term154). Qed.
Lemma lem2390563 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390564 : term278 = term272.
Proof. exact (MK_COMB (@lem2390563) (@lem2390562)). Qed.
Lemma lem2390565 : term277 = term271.
Proof. exact (MK_COMB (@lem2390564) (@lem2390559)). Qed.
Lemma lem2390567 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2390568 : term271 = term281.
Proof. exact (@lem2390567 (NUMERAL 0) term154). Qed.
Lemma lem2390569 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2390570 (h1 : term242 = (BIT1 0)) : (term154 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2390571 : (term242 = (BIT1 0)) = ((term154 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2390570 h1) (fun h1 : (term154 = (NUMERAL 0)) = False => @lem2390569)). Qed.
Lemma lem2390572 : (term154 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2390571) (@lem2390569)). Qed.
Lemma lem2390573 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2390574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390575 : term282 = (and True).
Proof. exact (MK_COMB (@lem2390574) (@lem2390573)). Qed.
Lemma lem2390576 : term281 = (True /\ False).
Proof. exact (MK_COMB (@lem2390575) (@lem2390572)). Qed.
Lemma lem2390578 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2390579 : term281 = False.
Proof. exact (TRANS (@lem2390576) (@lem2390578)). Qed.
Lemma lem2390580 : term271 = False.
Proof. exact (TRANS (@lem2390568) (@lem2390579)). Qed.
Lemma lem2390581 : term277 = False.
Proof. exact (TRANS (@lem2390565) (@lem2390580)). Qed.
Lemma lem2390582 : term274 = False.
Proof. exact (TRANS (@lem2390549) (@lem2390581)). Qed.
Lemma lem2390583 : term271 = False.
Proof. exact (TRANS (@lem2390526) (@lem2390582)). Qed.
Lemma lem2390584 : term260 = False.
Proof. exact (TRANS (@lem2390517) (@lem2390583)). Qed.
Lemma lem2390585 (m : int) (h1 : term270 m) : False.
Proof. exact (EQ_MP (@lem2390584) (@lem2390511 m h1)). Qed.
Lemma lem2390586 (m : int) (h1 : term269 m) : False.
Proof. exact (or_elim (@lem2390433 m h1) (fun h0 : term270 m => @lem2390509 m h0) (fun h0 : term270 m => @lem2390585 m h0)). Qed.
Lemma lem2390588 (m : int) (h1 : term269 m) : term269 m.
Proof. exact (h1). Qed.
Lemma lem2390589 (m : int) (h1 : term269 m) : (term269 m) = False.
Proof. exact (prop_ext (fun h2 : term269 m => @lem2390586 m h1) (fun h2 : False => @lem2390588 m h1)). Qed.
Lemma lem2390590 (m : int) (h1 : term269 m) : False.
Proof. exact (EQ_MP (@lem2390589 m h1) (@lem2390588 m h1)). Qed.
Lemma lem2390591 (m : int) (h1 : term176 m) : term176 m.
Proof. exact (h1). Qed.
Lemma lem2390592 (m : int) (h1 : term176 m) : term269 m.
Proof. exact (EQ_MP (@lem2390423 m) (@lem2390591 m h1)). Qed.
Lemma lem2390593 (m : int) (h1 : term176 m) : (term269 m) = False.
Proof. exact (prop_ext (fun h2 : term269 m => @lem2390590 m h2) (fun h2 : False => @lem2390592 m h1)). Qed.
Lemma lem2390594 (m : int) (h1 : term176 m) : False.
Proof. exact (EQ_MP (@lem2390593 m h1) (@lem2390592 m h1)). Qed.
Lemma lem2390595 (m : int) : term283 m.
Proof. exact (fun h0 : term176 m => @lem2390594 m h0). Qed.
Lemma lem2390596 (m : int) : term284 m.
Proof. exact (@lem1386578 (term285 m)). Qed.
Lemma lem2390599 (m : int) : term285 m.
Proof. exact (@lem2390596 m (@lem2390595 m)). Qed.
Lemma lem2390600 (m : int) : (term174 m) = (term115 m).
Proof. exact (SYM (@lem2389892 m)). Qed.
Lemma lem2390601 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2390602 (m : int) : (term285 m) = (term114 m).
Proof. exact (MK_COMB (@lem2390601) (@lem2390600 m)). Qed.
Lemma lem2390603 (m : int) : term114 m.
Proof. exact (EQ_MP (@lem2390602 m) (@lem2390599 m)). Qed.
Lemma lem2390604 (m : int) : term113 m.
Proof. exact (EQ_MP (@lem2389749 m) (@lem2390603 m)). Qed.
Lemma lem2390605 (n : int) (m : int) : (term286 n m) = (term69 n m).
Proof. exact (@lem2318604 (term69 n m)). Qed.
Lemma lem2390648 (n : int) (m : int) : (term287 n m) = (term288 n m).
Proof. exact (@lem17362 (term67 m n) ((term42 m n) = m)). Qed.
Lemma lem2390651 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2390652 (m : int) (n : int) : (term289 m n) = (term290 m n).
Proof. exact (@lem2390651 term66 (rem m n)). Qed.
Lemma lem2390654 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2390655 : term118 = term120.
Proof. exact (@lem2390654 (NUMERAL 0)). Qed.
Lemma lem2390656 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390657 : term291 = term272.
Proof. exact (MK_COMB (@lem2390656) (@lem2390655)). Qed.
Lemma lem2390658 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2390659 (m : int) (n : int) : (term290 m n) = (term293 m n).
Proof. exact (MK_COMB (@lem2390657) (@lem2390658 m n)). Qed.
Lemma lem2390661 (m : int) (n : int) : (term289 m n) = (term293 m n).
Proof. exact (TRANS (@lem2390652 m n) (@lem2390659 m n)). Qed.
Lemma lem2390663 (x : int) (y : int) : (int_lt x y) = (term294 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2390664 (m : int) (n : int) : (term295 m n) = (term296 m n).
Proof. exact (@lem2390663 (rem m n) (int_abs n)). Qed.
Lemma lem2390666 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2390667 (m : int) (n : int) : (term296 m n) = (term297 m n).
Proof. exact (@lem2390666 (term298 m n) (int_abs n)). Qed.
Lemma lem2390669 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2390670 (m : int) (n : int) : (term299 m n) = (term300 m n).
Proof. exact (@lem2390669 (rem m n) term137). Qed.
Lemma lem2390672 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2390673 : term152 = term153.
Proof. exact (@lem2390672 term154). Qed.
Lemma lem2390674 (m : int) (n : int) : (term301 m n) = (term301 m n).
Proof. exact (eq_refl (term301 m n)). Qed.
Lemma lem2390675 (m : int) (n : int) : (term300 m n) = (term302 m n).
Proof. exact (MK_COMB (@lem2390674 m n) (@lem2390673)). Qed.
Lemma lem2390676 (m : int) (n : int) : (term299 m n) = (term302 m n).
Proof. exact (TRANS (@lem2390670 m n) (@lem2390675 m n)). Qed.
Lemma lem2390677 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390678 (m : int) (n : int) : (term303 m n) = (term304 m n).
Proof. exact (MK_COMB (@lem2390677) (@lem2390676 m n)). Qed.
Lemma lem2390680 (x : int) : (term305 x) = (term306 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2390681 (n : int) : (term305 n) = (term306 n).
Proof. exact (@lem2390680 n). Qed.
Lemma lem2390682 (m : int) (n : int) : (term297 m n) = (term307 m n).
Proof. exact (MK_COMB (@lem2390678 m n) (@lem2390681 n)). Qed.
Lemma lem2390683 (m : int) (n : int) : (term296 m n) = (term307 m n).
Proof. exact (TRANS (@lem2390667 m n) (@lem2390682 m n)). Qed.
Lemma lem2390684 (m : int) (n : int) : (term295 m n) = (term307 m n).
Proof. exact (TRANS (@lem2390664 m n) (@lem2390683 m n)). Qed.
Lemma lem2390687 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2390688 (m : int) (n : int) : (m = (term42 m n)) = ((real_of_int m) = (term308 m n)).
Proof. exact (@lem2390687 m (term42 m n)). Qed.
Lemma lem2390692 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2390693 (m : int) (n : int) : (term308 m n) = (term309 m n).
Proof. exact (@lem2390692 (term104 m n) (rem m n)). Qed.
Lemma lem2390695 (x : int) (y : int) : (term140 x y) = (term141 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2390696 (m : int) (n : int) : (term310 m n) = (term311 m n).
Proof. exact (@lem2390695 (div m n) n). Qed.
Lemma lem2390697 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390698 (m : int) (n : int) : (term312 m n) = (term313 m n).
Proof. exact (MK_COMB (@lem2390697) (@lem2390696 m n)). Qed.
Lemma lem2390699 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2390700 (m : int) (n : int) : (term309 m n) = (term314 m n).
Proof. exact (MK_COMB (@lem2390698 m n) (@lem2390699 m n)). Qed.
Lemma lem2390701 (m : int) (n : int) : (term308 m n) = (term314 m n).
Proof. exact (TRANS (@lem2390693 m n) (@lem2390700 m n)). Qed.
Lemma lem2390702 (m : int) : (term315 m) = (term315 m).
Proof. exact (eq_refl (term315 m)). Qed.
Lemma lem2390703 (m : int) (n : int) : ((real_of_int m) = (term308 m n)) = ((real_of_int m) = (term314 m n)).
Proof. exact (MK_COMB (@lem2390702 m) (@lem2390701 m n)). Qed.
Lemma lem2390705 (m : int) (n : int) : (m = (term42 m n)) = ((real_of_int m) = (term314 m n)).
Proof. exact (TRANS (@lem2390688 m n) (@lem2390703 m n)). Qed.
Lemma lem2390706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390707 (m : int) (n : int) : (term316 m n) = (term317 m n).
Proof. exact (MK_COMB (@lem2390706) (@lem2390684 m n)). Qed.
Lemma lem2390708 (m : int) (n : int) : (term318 m n) = (term319 m n).
Proof. exact (MK_COMB (@lem2390707 m n) (@lem2390705 m n)). Qed.
Lemma lem2390709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390710 (m : int) (n : int) : (term320 m n) = (term321 m n).
Proof. exact (MK_COMB (@lem2390709) (@lem2390661 m n)). Qed.
Lemma lem2390711 (m : int) (n : int) : (term67 m n) = (term322 m n).
Proof. exact (MK_COMB (@lem2390710 m n) (@lem2390708 m n)). Qed.
Lemma lem2390713 (y : int) (x : int) : (term125 x y) = (term126 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2390714 (m : int) (n : int) : (term323 n m) = (term324 m n).
Proof. exact (@lem2390713 m (term42 m n)). Qed.
Lemma lem2390716 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2390717 (n : int) (m : int) : (term325 n m) = (term326 n m).
Proof. exact (@lem2390716 (term327 m n) m). Qed.
Lemma lem2390719 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2390720 (m : int) (n : int) : (term328 m n) = (term329 m n).
Proof. exact (@lem2390719 (term42 m n) term137). Qed.
Lemma lem2390722 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2390723 (m : int) (n : int) : (term308 m n) = (term309 m n).
Proof. exact (@lem2390722 (term104 m n) (rem m n)). Qed.
Lemma lem2390725 (x : int) (y : int) : (term140 x y) = (term141 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2390726 (m : int) (n : int) : (term310 m n) = (term311 m n).
Proof. exact (@lem2390725 (div m n) n). Qed.
Lemma lem2390727 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390728 (m : int) (n : int) : (term312 m n) = (term313 m n).
Proof. exact (MK_COMB (@lem2390727) (@lem2390726 m n)). Qed.
Lemma lem2390729 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2390730 (m : int) (n : int) : (term309 m n) = (term314 m n).
Proof. exact (MK_COMB (@lem2390728 m n) (@lem2390729 m n)). Qed.
Lemma lem2390731 (m : int) (n : int) : (term308 m n) = (term314 m n).
Proof. exact (TRANS (@lem2390723 m n) (@lem2390730 m n)). Qed.
Lemma lem2390732 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390733 (m : int) (n : int) : (term330 m n) = (term331 m n).
Proof. exact (MK_COMB (@lem2390732) (@lem2390731 m n)). Qed.
Lemma lem2390735 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2390736 : term152 = term153.
Proof. exact (@lem2390735 term154). Qed.
Lemma lem2390737 (m : int) (n : int) : (term329 m n) = (term332 m n).
Proof. exact (MK_COMB (@lem2390733 m n) (@lem2390736)). Qed.
Lemma lem2390738 (m : int) (n : int) : (term328 m n) = (term332 m n).
Proof. exact (TRANS (@lem2390720 m n) (@lem2390737 m n)). Qed.
Lemma lem2390739 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390740 (m : int) (n : int) : (term333 m n) = (term334 m n).
Proof. exact (MK_COMB (@lem2390739) (@lem2390738 m n)). Qed.
Lemma lem2390741 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2390742 (n : int) (m : int) : (term326 n m) = (term335 n m).
Proof. exact (MK_COMB (@lem2390740 m n) (@lem2390741 m)). Qed.
Lemma lem2390743 (n : int) (m : int) : (term325 n m) = (term335 n m).
Proof. exact (TRANS (@lem2390717 n m) (@lem2390742 n m)). Qed.
Lemma lem2390744 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2390745 (n : int) (m : int) : (term336 n m) = (term337 n m).
Proof. exact (MK_COMB (@lem2390744) (@lem2390743 n m)). Qed.
Lemma lem2390747 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2390748 (m : int) (n : int) : (term338 m n) = (term339 m n).
Proof. exact (@lem2390747 (term163 m) (term42 m n)). Qed.
Lemma lem2390750 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2390751 (m : int) : (term164 m) = (term165 m).
Proof. exact (@lem2390750 m term137). Qed.
Lemma lem2390753 (n : nat) : (term119 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2390754 : term152 = term153.
Proof. exact (@lem2390753 term154). Qed.
Lemma lem2390755 (m : int) : (term166 m) = (term166 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem2390756 (m : int) : (term165 m) = (term167 m).
Proof. exact (MK_COMB (@lem2390755 m) (@lem2390754)). Qed.
Lemma lem2390757 (m : int) : (term164 m) = (term167 m).
Proof. exact (TRANS (@lem2390751 m) (@lem2390756 m)). Qed.
Lemma lem2390758 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2390759 (m : int) : (term168 m) = (term169 m).
Proof. exact (MK_COMB (@lem2390758) (@lem2390757 m)). Qed.
Lemma lem2390761 (x : int) (y : int) : (term133 x y) = (term134 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2390762 (m : int) (n : int) : (term308 m n) = (term309 m n).
Proof. exact (@lem2390761 (term104 m n) (rem m n)). Qed.
Lemma lem2390764 (x : int) (y : int) : (term140 x y) = (term141 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2390765 (m : int) (n : int) : (term310 m n) = (term311 m n).
Proof. exact (@lem2390764 (div m n) n). Qed.
Lemma lem2390766 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390767 (m : int) (n : int) : (term312 m n) = (term313 m n).
Proof. exact (MK_COMB (@lem2390766) (@lem2390765 m n)). Qed.
Lemma lem2390768 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2390769 (m : int) (n : int) : (term309 m n) = (term314 m n).
Proof. exact (MK_COMB (@lem2390767 m n) (@lem2390768 m n)). Qed.
Lemma lem2390770 (m : int) (n : int) : (term308 m n) = (term314 m n).
Proof. exact (TRANS (@lem2390762 m n) (@lem2390769 m n)). Qed.
Lemma lem2390771 (m : int) (n : int) : (term339 m n) = (term340 m n).
Proof. exact (MK_COMB (@lem2390759 m) (@lem2390770 m n)). Qed.
Lemma lem2390772 (m : int) (n : int) : (term338 m n) = (term340 m n).
Proof. exact (TRANS (@lem2390748 m n) (@lem2390771 m n)). Qed.
Lemma lem2390773 (m : int) (n : int) : (term324 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem2390745 n m) (@lem2390772 m n)). Qed.
Lemma lem2390774 (m : int) (n : int) : (term323 n m) = (term341 m n).
Proof. exact (TRANS (@lem2390714 m n) (@lem2390773 m n)). Qed.
Lemma lem2390775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390776 (m : int) (n : int) : (term342 m n) = (term343 m n).
Proof. exact (MK_COMB (@lem2390775) (@lem2390711 m n)). Qed.
Lemma lem2390777 (m : int) (n : int) : (term288 n m) = (term344 m n).
Proof. exact (MK_COMB (@lem2390776 m n) (@lem2390774 m n)). Qed.
Lemma lem2390778 (m : int) (n : int) : (term287 n m) = (term344 m n).
Proof. exact (TRANS (@lem2390648 n m) (@lem2390777 m n)). Qed.
Lemma lem2390782 (t : Prop) : (term175 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2390828 (m : int) (n : int) : (term345 m n) = (term344 m n).
Proof. exact (@lem2390782 (term344 m n)). Qed.
Lemma lem2390829 (m : int) (n : int) : (term293 m n) = (term346 m n).
Proof. exact (@lem1988287 (term292 m n) term120). Qed.
Lemma lem2390835 (m : int) (n : int) : (term347 m n) = (term348 m n).
Proof. exact (@lem1982792 (term292 m n) term120). Qed.
Lemma lem2390837 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390838 : term120 = term180.
Proof. exact (@lem2390837 (NUMERAL 0)). Qed.
Lemma lem2390840 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390841 : term183 = term184.
Proof. exact (@lem2390840 term154). Qed.
Lemma lem2390842 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390843 : term185 = term186.
Proof. exact (MK_COMB (@lem2390842) (@lem2390841)). Qed.
Lemma lem2390844 : term187 = term188.
Proof. exact (MK_COMB (@lem2390843) (@lem2390838)). Qed.
Lemma lem2390845 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2390847 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390848 : term192 = term193.
Proof. exact (@lem2390847 term154 term154). Qed.
Lemma lem2390849 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390850 : term195 = term154.
Proof. exact (EQ_MP (@lem2390849) (@lem940073)). Qed.
Lemma lem2390851 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390852 : term193 = term153.
Proof. exact (MK_COMB (@lem2390851) (@lem2390850)). Qed.
Lemma lem2390853 : term192 = term153.
Proof. exact (TRANS (@lem2390848) (@lem2390852)). Qed.
Lemma lem2390855 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2390856 : term187 = term120.
Proof. exact (@lem2390855 term154). Qed.
Lemma lem2390857 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2390858 : term197 = term198.
Proof. exact (MK_COMB (@lem2390857) (@lem2390856)). Qed.
Lemma lem2390859 : term189 = term180.
Proof. exact (MK_COMB (@lem2390858) (@lem2390853)). Qed.
Lemma lem2390860 : term188 = term180.
Proof. exact (TRANS (@lem2390845) (@lem2390859)). Qed.
Lemma lem2390861 : term187 = term180.
Proof. exact (TRANS (@lem2390844) (@lem2390860)). Qed.
Lemma lem2390863 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2390864 : term180 = term120.
Proof. exact (@lem2390863 term120). Qed.
Lemma lem2390865 : term187 = term120.
Proof. exact (TRANS (@lem2390861) (@lem2390864)). Qed.
Lemma lem2390866 (m : int) (n : int) : (term301 m n) = (term301 m n).
Proof. exact (eq_refl (term301 m n)). Qed.
Lemma lem2390867 (m : int) (n : int) : (term348 m n) = (term349 m n).
Proof. exact (MK_COMB (@lem2390866 m n) (@lem2390865)). Qed.
Lemma lem2390868 (m : int) (n : int) : (term349 m n) = (term292 m n).
Proof. exact (@lem1982723 (term292 m n)). Qed.
Lemma lem2390869 (m : int) (n : int) : (term348 m n) = (term292 m n).
Proof. exact (TRANS (@lem2390867 m n) (@lem2390868 m n)). Qed.
Lemma lem2390871 (m : int) (n : int) : (term347 m n) = (term292 m n).
Proof. exact (TRANS (@lem2390835 m n) (@lem2390869 m n)). Qed.
Lemma lem2390872 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2390873 (m : int) (n : int) : (term350 m n) = (term351 m n).
Proof. exact (MK_COMB (@lem2390872) (@lem2390871 m n)). Qed.
Lemma lem2390874 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2390875 (m : int) (n : int) : (term346 m n) = (term352 m n).
Proof. exact (MK_COMB (@lem2390873 m n) (@lem2390874)). Qed.
Lemma lem2390876 (m : int) (n : int) : (term293 m n) = (term352 m n).
Proof. exact (TRANS (@lem2390829 m n) (@lem2390875 m n)). Qed.
Lemma lem2390877 (m : int) (n : int) : (term307 m n) = (term353 m n).
Proof. exact (@lem1988287 (term306 n) (term302 m n)). Qed.
Lemma lem2390891 (m : int) (n : int) : (term354 m n) = (term355 m n).
Proof. exact (@lem1982792 (term306 n) (term302 m n)). Qed.
Lemma lem2390892 (m : int) (n : int) : (term356 m n) = (term357 m n).
Proof. exact (@lem1982781 (term292 m n) term183 term153). Qed.
Lemma lem2390894 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2390895 : term153 = term219.
Proof. exact (@lem2390894 term154). Qed.
Lemma lem2390897 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2390898 : term183 = term184.
Proof. exact (@lem2390897 term154). Qed.
Lemma lem2390899 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2390900 : term185 = term186.
Proof. exact (MK_COMB (@lem2390899) (@lem2390898)). Qed.
Lemma lem2390901 : term220 = term221.
Proof. exact (MK_COMB (@lem2390900) (@lem2390895)). Qed.
Lemma lem2390902 : term221 = term222.
Proof. exact (@lem1981613 term183 term153 term153 term153). Qed.
Lemma lem2390904 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2390905 : term192 = term193.
Proof. exact (@lem2390904 term154 term154). Qed.
Lemma lem2390906 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390907 : term195 = term154.
Proof. exact (EQ_MP (@lem2390906) (@lem940073)). Qed.
Lemma lem2390908 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390909 : term193 = term153.
Proof. exact (MK_COMB (@lem2390908) (@lem2390907)). Qed.
Lemma lem2390910 : term192 = term153.
Proof. exact (TRANS (@lem2390905) (@lem2390909)). Qed.
Lemma lem2390912 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2390913 : term220 = term225.
Proof. exact (@lem2390912 term154 term154). Qed.
Lemma lem2390914 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2390915 : term195 = term154.
Proof. exact (EQ_MP (@lem2390914) (@lem940073)). Qed.
Lemma lem2390916 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2390917 : term193 = term153.
Proof. exact (MK_COMB (@lem2390916) (@lem2390915)). Qed.
Lemma lem2390918 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2390919 : term225 = term183.
Proof. exact (MK_COMB (@lem2390918) (@lem2390917)). Qed.
Lemma lem2390920 : term220 = term183.
Proof. exact (TRANS (@lem2390913) (@lem2390919)). Qed.
Lemma lem2390921 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2390922 : term226 = term227.
Proof. exact (MK_COMB (@lem2390921) (@lem2390920)). Qed.
Lemma lem2390923 : term222 = term184.
Proof. exact (MK_COMB (@lem2390922) (@lem2390910)). Qed.
Lemma lem2390924 : term221 = term184.
Proof. exact (TRANS (@lem2390902) (@lem2390923)). Qed.
Lemma lem2390925 : term220 = term184.
Proof. exact (TRANS (@lem2390901) (@lem2390924)). Qed.
Lemma lem2390927 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2390928 : term184 = term183.
Proof. exact (@lem2390927 term183). Qed.
Lemma lem2390929 : term220 = term183.
Proof. exact (TRANS (@lem2390925) (@lem2390928)). Qed.
Lemma lem2390932 (m : int) (n : int) : (term358 m n) = (term358 m n).
Proof. exact (eq_refl (term358 m n)). Qed.
Lemma lem2390933 (m : int) (n : int) : (term357 m n) = (term359 m n).
Proof. exact (MK_COMB (@lem2390932 m n) (@lem2390929)). Qed.
Lemma lem2390934 (m : int) (n : int) : (term356 m n) = (term359 m n).
Proof. exact (TRANS (@lem2390892 m n) (@lem2390933 m n)). Qed.
Lemma lem2390935 (n : int) : (term360 n) = (term360 n).
Proof. exact (eq_refl (term360 n)). Qed.
Lemma lem2390938 (m : int) (n : int) : (term355 m n) = (term361 m n).
Proof. exact (MK_COMB (@lem2390935 n) (@lem2390934 m n)). Qed.
Lemma lem2390940 (m : int) (n : int) : (term354 m n) = (term361 m n).
Proof. exact (TRANS (@lem2390891 m n) (@lem2390938 m n)). Qed.
Lemma lem2390941 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2390942 (m : int) (n : int) : (term362 m n) = (term363 m n).
Proof. exact (MK_COMB (@lem2390941) (@lem2390940 m n)). Qed.
Lemma lem2390943 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2390944 (m : int) (n : int) : (term353 m n) = (term364 m n).
Proof. exact (MK_COMB (@lem2390942 m n) (@lem2390943)). Qed.
Lemma lem2390945 (m : int) (n : int) : (term307 m n) = (term364 m n).
Proof. exact (TRANS (@lem2390877 m n) (@lem2390944 m n)). Qed.
Lemma lem2390946 (m : int) (n : int) : ((real_of_int m) = (term314 m n)) = ((term365 m n) = term120).
Proof. exact (@lem1988293 (real_of_int m) (term314 m n)). Qed.
Lemma lem2390947 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2390954 (m : int) (n : int) : (term311 m n) = (term366 m n).
Proof. exact (@lem1982747 (real_of_int n) (term367 m n)). Qed.
Lemma lem2390955 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2390956 (m : int) (n : int) : (term313 m n) = (term368 m n).
Proof. exact (MK_COMB (@lem2390955) (@lem2390954 m n)). Qed.
Lemma lem2390959 (m : int) (n : int) : (term314 m n) = (term369 m n).
Proof. exact (MK_COMB (@lem2390956 m n) (@lem2390947 m n)). Qed.
Lemma lem2390962 (m : int) : (term213 m) = (term213 m).
Proof. exact (eq_refl (term213 m)). Qed.
Lemma lem2390963 (m : int) (n : int) : (term365 m n) = (term370 m n).
Proof. exact (MK_COMB (@lem2390962 m) (@lem2390959 m n)). Qed.
Lemma lem2390964 (m : int) (n : int) : (term370 m n) = (term371 m n).
Proof. exact (@lem1982792 (real_of_int m) (term369 m n)). Qed.
Lemma lem2390971 (m : int) (n : int) : (term372 m n) = (term373 m n).
Proof. exact (@lem1982781 (term366 m n) term183 (term292 m n)). Qed.
Lemma lem2390972 (m : int) : (term166 m) = (term166 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem2390973 (m : int) (n : int) : (term371 m n) = (term374 m n).
Proof. exact (MK_COMB (@lem2390972 m) (@lem2390971 m n)). Qed.
Lemma lem2390978 (m : int) (n : int) : (term374 m n) = (term375 m n).
Proof. exact (@lem1982757 (term376 m n) (real_of_int m) (term377 m n)). Qed.
Lemma lem2390979 (m : int) (n : int) : (term371 m n) = (term375 m n).
Proof. exact (TRANS (@lem2390973 m n) (@lem2390978 m n)). Qed.
Lemma lem2390980 (m : int) (n : int) : (term370 m n) = (term375 m n).
Proof. exact (TRANS (@lem2390964 m n) (@lem2390979 m n)). Qed.
Lemma lem2390981 (m : int) (n : int) : (term365 m n) = (term375 m n).
Proof. exact (TRANS (@lem2390963 m n) (@lem2390980 m n)). Qed.
Lemma lem2390982 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2390983 (m : int) (n : int) : (term378 m n) = (term379 m n).
Proof. exact (MK_COMB (@lem2390982) (@lem2390981 m n)). Qed.
Lemma lem2390984 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2390985 (m : int) (n : int) : ((term365 m n) = term120) = ((term375 m n) = term120).
Proof. exact (MK_COMB (@lem2390983 m n) (@lem2390984)). Qed.
Lemma lem2390986 (m : int) (n : int) : ((real_of_int m) = (term314 m n)) = ((term375 m n) = term120).
Proof. exact (TRANS (@lem2390946 m n) (@lem2390985 m n)). Qed.
Lemma lem2390987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390988 (m : int) (n : int) : (term317 m n) = (term380 m n).
Proof. exact (MK_COMB (@lem2390987) (@lem2390945 m n)). Qed.
Lemma lem2390989 (m : int) (n : int) : (term319 m n) = (term381 m n).
Proof. exact (MK_COMB (@lem2390988 m n) (@lem2390986 m n)). Qed.
Lemma lem2390990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2390991 (m : int) (n : int) : (term321 m n) = (term382 m n).
Proof. exact (MK_COMB (@lem2390990) (@lem2390876 m n)). Qed.
Lemma lem2390992 (m : int) (n : int) : (term322 m n) = (term383 m n).
Proof. exact (MK_COMB (@lem2390991 m n) (@lem2390989 m n)). Qed.
Lemma lem2390993 (m : int) (n : int) : (term335 n m) = (term384 m n).
Proof. exact (@lem1988287 (real_of_int m) (term332 m n)). Qed.
Lemma lem2390994 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2390995 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2391002 (m : int) (n : int) : (term311 m n) = (term366 m n).
Proof. exact (@lem1982747 (real_of_int n) (term367 m n)). Qed.
Lemma lem2391003 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2391004 (m : int) (n : int) : (term313 m n) = (term368 m n).
Proof. exact (MK_COMB (@lem2391003) (@lem2391002 m n)). Qed.
Lemma lem2391007 (m : int) (n : int) : (term314 m n) = (term369 m n).
Proof. exact (MK_COMB (@lem2391004 m n) (@lem2390995 m n)). Qed.
Lemma lem2391008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2391009 (m : int) (n : int) : (term331 m n) = (term385 m n).
Proof. exact (MK_COMB (@lem2391008) (@lem2391007 m n)). Qed.
Lemma lem2391010 (m : int) (n : int) : (term332 m n) = (term386 m n).
Proof. exact (MK_COMB (@lem2391009 m n) (@lem2390994)). Qed.
Lemma lem2391015 (m : int) (n : int) : (term386 m n) = (term387 m n).
Proof. exact (@lem1982755 (term366 m n) (term292 m n) term153). Qed.
Lemma lem2391016 (m : int) (n : int) : (term332 m n) = (term387 m n).
Proof. exact (TRANS (@lem2391010 m n) (@lem2391015 m n)). Qed.
Lemma lem2391019 (m : int) : (term213 m) = (term213 m).
Proof. exact (eq_refl (term213 m)). Qed.
Lemma lem2391020 (m : int) (n : int) : (term388 m n) = (term389 m n).
Proof. exact (MK_COMB (@lem2391019 m) (@lem2391016 m n)). Qed.
Lemma lem2391021 (m : int) (n : int) : (term389 m n) = (term390 m n).
Proof. exact (@lem1982792 (real_of_int m) (term387 m n)). Qed.
Lemma lem2391022 (m : int) (n : int) : (term391 m n) = (term392 m n).
Proof. exact (@lem1982781 (term366 m n) term183 (term302 m n)). Qed.
Lemma lem2391023 (m : int) (n : int) : (term356 m n) = (term357 m n).
Proof. exact (@lem1982781 (term292 m n) term183 term153). Qed.
Lemma lem2391025 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391026 : term153 = term219.
Proof. exact (@lem2391025 term154). Qed.
Lemma lem2391028 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391029 : term183 = term184.
Proof. exact (@lem2391028 term154). Qed.
Lemma lem2391030 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391031 : term185 = term186.
Proof. exact (MK_COMB (@lem2391030) (@lem2391029)). Qed.
Lemma lem2391032 : term220 = term221.
Proof. exact (MK_COMB (@lem2391031) (@lem2391026)). Qed.
Lemma lem2391033 : term221 = term222.
Proof. exact (@lem1981613 term183 term153 term153 term153). Qed.
Lemma lem2391035 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391036 : term192 = term193.
Proof. exact (@lem2391035 term154 term154). Qed.
Lemma lem2391037 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391038 : term195 = term154.
Proof. exact (EQ_MP (@lem2391037) (@lem940073)). Qed.
Lemma lem2391039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391040 : term193 = term153.
Proof. exact (MK_COMB (@lem2391039) (@lem2391038)). Qed.
Lemma lem2391041 : term192 = term153.
Proof. exact (TRANS (@lem2391036) (@lem2391040)). Qed.
Lemma lem2391043 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2391044 : term220 = term225.
Proof. exact (@lem2391043 term154 term154). Qed.
Lemma lem2391045 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391046 : term195 = term154.
Proof. exact (EQ_MP (@lem2391045) (@lem940073)). Qed.
Lemma lem2391047 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391048 : term193 = term153.
Proof. exact (MK_COMB (@lem2391047) (@lem2391046)). Qed.
Lemma lem2391049 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2391050 : term225 = term183.
Proof. exact (MK_COMB (@lem2391049) (@lem2391048)). Qed.
Lemma lem2391051 : term220 = term183.
Proof. exact (TRANS (@lem2391044) (@lem2391050)). Qed.
Lemma lem2391052 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391053 : term226 = term227.
Proof. exact (MK_COMB (@lem2391052) (@lem2391051)). Qed.
Lemma lem2391054 : term222 = term184.
Proof. exact (MK_COMB (@lem2391053) (@lem2391041)). Qed.
Lemma lem2391055 : term221 = term184.
Proof. exact (TRANS (@lem2391033) (@lem2391054)). Qed.
Lemma lem2391056 : term220 = term184.
Proof. exact (TRANS (@lem2391032) (@lem2391055)). Qed.
Lemma lem2391058 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391059 : term184 = term183.
Proof. exact (@lem2391058 term183). Qed.
Lemma lem2391060 : term220 = term183.
Proof. exact (TRANS (@lem2391056) (@lem2391059)). Qed.
Lemma lem2391063 (m : int) (n : int) : (term358 m n) = (term358 m n).
Proof. exact (eq_refl (term358 m n)). Qed.
Lemma lem2391064 (m : int) (n : int) : (term357 m n) = (term359 m n).
Proof. exact (MK_COMB (@lem2391063 m n) (@lem2391060)). Qed.
Lemma lem2391065 (m : int) (n : int) : (term356 m n) = (term359 m n).
Proof. exact (TRANS (@lem2391023 m n) (@lem2391064 m n)). Qed.
Lemma lem2391068 (m : int) (n : int) : (term393 m n) = (term393 m n).
Proof. exact (eq_refl (term393 m n)). Qed.
Lemma lem2391069 (m : int) (n : int) : (term392 m n) = (term394 m n).
Proof. exact (MK_COMB (@lem2391068 m n) (@lem2391065 m n)). Qed.
Lemma lem2391070 (m : int) (n : int) : (term391 m n) = (term394 m n).
Proof. exact (TRANS (@lem2391022 m n) (@lem2391069 m n)). Qed.
Lemma lem2391071 (m : int) : (term166 m) = (term166 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem2391072 (m : int) (n : int) : (term390 m n) = (term395 m n).
Proof. exact (MK_COMB (@lem2391071 m) (@lem2391070 m n)). Qed.
Lemma lem2391077 (m : int) (n : int) : (term395 m n) = (term396 m n).
Proof. exact (@lem1982757 (term376 m n) (real_of_int m) (term359 m n)). Qed.
Lemma lem2391078 (m : int) (n : int) : (term390 m n) = (term396 m n).
Proof. exact (TRANS (@lem2391072 m n) (@lem2391077 m n)). Qed.
Lemma lem2391079 (m : int) (n : int) : (term389 m n) = (term396 m n).
Proof. exact (TRANS (@lem2391021 m n) (@lem2391078 m n)). Qed.
Lemma lem2391080 (m : int) (n : int) : (term388 m n) = (term396 m n).
Proof. exact (TRANS (@lem2391020 m n) (@lem2391079 m n)). Qed.
Lemma lem2391081 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391082 (m : int) (n : int) : (term397 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem2391081) (@lem2391080 m n)). Qed.
Lemma lem2391083 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391084 (m : int) (n : int) : (term384 m n) = (term399 m n).
Proof. exact (MK_COMB (@lem2391082 m n) (@lem2391083)). Qed.
Lemma lem2391085 (m : int) (n : int) : (term335 n m) = (term399 m n).
Proof. exact (TRANS (@lem2390993 m n) (@lem2391084 m n)). Qed.
Lemma lem2391086 (n : int) (m : int) : (term340 m n) = (term400 n m).
Proof. exact (@lem1988287 (term314 m n) (term167 m)). Qed.
Lemma lem2391093 (m : int) : (term167 m) = (term167 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem2391094 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2391101 (m : int) (n : int) : (term311 m n) = (term366 m n).
Proof. exact (@lem1982747 (real_of_int n) (term367 m n)). Qed.
Lemma lem2391102 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2391103 (m : int) (n : int) : (term313 m n) = (term368 m n).
Proof. exact (MK_COMB (@lem2391102) (@lem2391101 m n)). Qed.
Lemma lem2391106 (m : int) (n : int) : (term314 m n) = (term369 m n).
Proof. exact (MK_COMB (@lem2391103 m n) (@lem2391094 m n)). Qed.
Lemma lem2391107 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2391108 (m : int) (n : int) : (term401 m n) = (term402 m n).
Proof. exact (MK_COMB (@lem2391107) (@lem2391106 m n)). Qed.
Lemma lem2391109 (n : int) (m : int) : (term403 n m) = (term404 n m).
Proof. exact (MK_COMB (@lem2391108 m n) (@lem2391093 m)). Qed.
Lemma lem2391110 (n : int) (m : int) : (term404 n m) = (term405 n m).
Proof. exact (@lem1982792 (term369 m n) (term167 m)). Qed.
Lemma lem2391111 (m : int) : (term217 m) = (term218 m).
Proof. exact (@lem1982781 (real_of_int m) term183 term153). Qed.
Lemma lem2391113 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391114 : term153 = term219.
Proof. exact (@lem2391113 term154). Qed.
Lemma lem2391116 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391117 : term183 = term184.
Proof. exact (@lem2391116 term154). Qed.
Lemma lem2391118 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391119 : term185 = term186.
Proof. exact (MK_COMB (@lem2391118) (@lem2391117)). Qed.
Lemma lem2391120 : term220 = term221.
Proof. exact (MK_COMB (@lem2391119) (@lem2391114)). Qed.
Lemma lem2391121 : term221 = term222.
Proof. exact (@lem1981613 term183 term153 term153 term153). Qed.
Lemma lem2391123 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391124 : term192 = term193.
Proof. exact (@lem2391123 term154 term154). Qed.
Lemma lem2391125 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391126 : term195 = term154.
Proof. exact (EQ_MP (@lem2391125) (@lem940073)). Qed.
Lemma lem2391127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391128 : term193 = term153.
Proof. exact (MK_COMB (@lem2391127) (@lem2391126)). Qed.
Lemma lem2391129 : term192 = term153.
Proof. exact (TRANS (@lem2391124) (@lem2391128)). Qed.
Lemma lem2391131 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2391132 : term220 = term225.
Proof. exact (@lem2391131 term154 term154). Qed.
Lemma lem2391133 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391134 : term195 = term154.
Proof. exact (EQ_MP (@lem2391133) (@lem940073)). Qed.
Lemma lem2391135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391136 : term193 = term153.
Proof. exact (MK_COMB (@lem2391135) (@lem2391134)). Qed.
Lemma lem2391137 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2391138 : term225 = term183.
Proof. exact (MK_COMB (@lem2391137) (@lem2391136)). Qed.
Lemma lem2391139 : term220 = term183.
Proof. exact (TRANS (@lem2391132) (@lem2391138)). Qed.
Lemma lem2391140 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391141 : term226 = term227.
Proof. exact (MK_COMB (@lem2391140) (@lem2391139)). Qed.
Lemma lem2391142 : term222 = term184.
Proof. exact (MK_COMB (@lem2391141) (@lem2391129)). Qed.
Lemma lem2391143 : term221 = term184.
Proof. exact (TRANS (@lem2391121) (@lem2391142)). Qed.
Lemma lem2391144 : term220 = term184.
Proof. exact (TRANS (@lem2391120) (@lem2391143)). Qed.
Lemma lem2391146 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391147 : term184 = term183.
Proof. exact (@lem2391146 term183). Qed.
Lemma lem2391148 : term220 = term183.
Proof. exact (TRANS (@lem2391144) (@lem2391147)). Qed.
Lemma lem2391151 (m : int) : (term228 m) = (term228 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem2391152 (m : int) : (term218 m) = (term229 m).
Proof. exact (MK_COMB (@lem2391151 m) (@lem2391148)). Qed.
Lemma lem2391153 (m : int) : (term217 m) = (term229 m).
Proof. exact (TRANS (@lem2391111 m) (@lem2391152 m)). Qed.
Lemma lem2391154 (m : int) (n : int) : (term385 m n) = (term385 m n).
Proof. exact (eq_refl (term385 m n)). Qed.
Lemma lem2391155 (n : int) (m : int) : (term405 n m) = (term406 n m).
Proof. exact (MK_COMB (@lem2391154 m n) (@lem2391153 m)). Qed.
Lemma lem2391156 (n : int) (m : int) : (term406 n m) = (term407 n m).
Proof. exact (@lem1982755 (term366 m n) (term292 m n) (term229 m)). Qed.
Lemma lem2391161 (m : int) (n : int) : (term408 n m) = (term409 m n).
Proof. exact (@lem1982757 (term206 m) (term292 m n) term183). Qed.
Lemma lem2391162 (m : int) (n : int) : (term368 m n) = (term368 m n).
Proof. exact (eq_refl (term368 m n)). Qed.
Lemma lem2391163 (m : int) (n : int) : (term407 n m) = (term410 m n).
Proof. exact (MK_COMB (@lem2391162 m n) (@lem2391161 m n)). Qed.
Lemma lem2391164 (m : int) (n : int) : (term406 n m) = (term410 m n).
Proof. exact (TRANS (@lem2391156 n m) (@lem2391163 m n)). Qed.
Lemma lem2391165 (m : int) (n : int) : (term405 n m) = (term410 m n).
Proof. exact (TRANS (@lem2391155 n m) (@lem2391164 m n)). Qed.
Lemma lem2391166 (m : int) (n : int) : (term404 n m) = (term410 m n).
Proof. exact (TRANS (@lem2391110 n m) (@lem2391165 m n)). Qed.
Lemma lem2391167 (m : int) (n : int) : (term403 n m) = (term410 m n).
Proof. exact (TRANS (@lem2391109 n m) (@lem2391166 m n)). Qed.
Lemma lem2391168 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391169 (m : int) (n : int) : (term411 n m) = (term412 m n).
Proof. exact (MK_COMB (@lem2391168) (@lem2391167 m n)). Qed.
Lemma lem2391170 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391171 (m : int) (n : int) : (term400 n m) = (term413 m n).
Proof. exact (MK_COMB (@lem2391169 m n) (@lem2391170)). Qed.
Lemma lem2391172 (m : int) (n : int) : (term340 m n) = (term413 m n).
Proof. exact (TRANS (@lem2391086 n m) (@lem2391171 m n)). Qed.
Lemma lem2391173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2391174 (m : int) (n : int) : (term337 n m) = (term414 m n).
Proof. exact (MK_COMB (@lem2391173) (@lem2391085 m n)). Qed.
Lemma lem2391175 (m : int) (n : int) : (term341 m n) = (term415 m n).
Proof. exact (MK_COMB (@lem2391174 m n) (@lem2391172 m n)). Qed.
Lemma lem2391176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391177 (m : int) (n : int) : (term343 m n) = (term416 m n).
Proof. exact (MK_COMB (@lem2391176) (@lem2390992 m n)). Qed.
Lemma lem2391178 (m : int) (n : int) : (term344 m n) = (term417 m n).
Proof. exact (MK_COMB (@lem2391177 m n) (@lem2391175 m n)). Qed.
Lemma lem2391185 (m : int) (n : int) : (term345 m n) = (term417 m n).
Proof. exact (TRANS (@lem2390828 m n) (@lem2391178 m n)). Qed.
Lemma lem2391214 (m : int) (n : int) : (term417 m n) = (term418 m n).
Proof. exact (@lem19158 (term399 m n) (term383 m n) (term413 m n)). Qed.
Lemma lem2391215 (m : int) (n : int) : (term345 m n) = (term418 m n).
Proof. exact (TRANS (@lem2391185 m n) (@lem2391214 m n)). Qed.
Lemma lem2391217 (m : int) (n : int) : (term419 m n) = (term420 m n).
Proof. exact (eq_refl (term419 m n)). Qed.
Lemma lem2391218 (m : int) (n : int) : (term420 m n) = (term419 m n).
Proof. exact (SYM (@lem2391217 m n)). Qed.
Lemma lem2391219 (m : int) (n : int) : (term419 m n) = (term421 m n).
Proof. exact (@lem1482981 (term422 m n) (real_of_int n)). Qed.
Lemma lem2391220 (m : int) (n : int) : (term420 m n) = (term421 m n).
Proof. exact (TRANS (@lem2391218 m n) (@lem2391219 m n)). Qed.
Lemma lem2391221 (m : int) (n : int) : (term423 m n) = (term424 m n).
Proof. exact (eq_refl (term423 m n)). Qed.
Lemma lem2391222 (n : int) : (term425 n) = (term425 n).
Proof. exact (eq_refl (term425 n)). Qed.
Lemma lem2391223 (m : int) (n : int) : (term426 m n) = (term427 m n).
Proof. exact (MK_COMB (@lem2391222 n) (@lem2391221 m n)). Qed.
Lemma lem2391224 (m : int) (n : int) : (term428 m n) = (term429 m n).
Proof. exact (eq_refl (term428 m n)). Qed.
Lemma lem2391225 (n : int) : (term430 n) = (term430 n).
Proof. exact (eq_refl (term430 n)). Qed.
Lemma lem2391226 (m : int) (n : int) : (term431 m n) = (term432 m n).
Proof. exact (MK_COMB (@lem2391225 n) (@lem2391224 m n)). Qed.
Lemma lem2391227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2391228 (m : int) (n : int) : (term433 m n) = (term434 m n).
Proof. exact (MK_COMB (@lem2391227) (@lem2391226 m n)). Qed.
Lemma lem2391229 (m : int) (n : int) : (term421 m n) = (term435 m n).
Proof. exact (MK_COMB (@lem2391228 m n) (@lem2391223 m n)). Qed.
Lemma lem2391230 (m : int) (n : int) : (term436 m n) = (term436 m n).
Proof. exact (eq_refl (term436 m n)). Qed.
Lemma lem2391231 (m : int) (n : int) : ((term420 m n) = (term421 m n)) = ((term420 m n) = (term435 m n)).
Proof. exact (MK_COMB (@lem2391230 m n) (@lem2391229 m n)). Qed.
Lemma lem2391232 (m : int) (n : int) : (term420 m n) = (term435 m n).
Proof. exact (EQ_MP (@lem2391231 m n) (@lem2391220 m n)). Qed.
Lemma lem2391233 (n : int) : (term437 n) = (term438 n).
Proof. exact (@lem1988291 (real_of_int n) term120). Qed.
Lemma lem2391239 (n : int) : (term439 n) = (term440 n).
Proof. exact (@lem1982792 (real_of_int n) term120). Qed.
Lemma lem2391241 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391242 : term120 = term180.
Proof. exact (@lem2391241 (NUMERAL 0)). Qed.
Lemma lem2391244 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391245 : term183 = term184.
Proof. exact (@lem2391244 term154). Qed.
Lemma lem2391246 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391247 : term185 = term186.
Proof. exact (MK_COMB (@lem2391246) (@lem2391245)). Qed.
Lemma lem2391248 : term187 = term188.
Proof. exact (MK_COMB (@lem2391247) (@lem2391242)). Qed.
Lemma lem2391249 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2391251 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391252 : term192 = term193.
Proof. exact (@lem2391251 term154 term154). Qed.
Lemma lem2391253 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391254 : term195 = term154.
Proof. exact (EQ_MP (@lem2391253) (@lem940073)). Qed.
Lemma lem2391255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391256 : term193 = term153.
Proof. exact (MK_COMB (@lem2391255) (@lem2391254)). Qed.
Lemma lem2391257 : term192 = term153.
Proof. exact (TRANS (@lem2391252) (@lem2391256)). Qed.
Lemma lem2391259 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2391260 : term187 = term120.
Proof. exact (@lem2391259 term154). Qed.
Lemma lem2391261 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391262 : term197 = term198.
Proof. exact (MK_COMB (@lem2391261) (@lem2391260)). Qed.
Lemma lem2391263 : term189 = term180.
Proof. exact (MK_COMB (@lem2391262) (@lem2391257)). Qed.
Lemma lem2391264 : term188 = term180.
Proof. exact (TRANS (@lem2391249) (@lem2391263)). Qed.
Lemma lem2391265 : term187 = term180.
Proof. exact (TRANS (@lem2391248) (@lem2391264)). Qed.
Lemma lem2391267 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391268 : term180 = term120.
Proof. exact (@lem2391267 term120). Qed.
Lemma lem2391269 : term187 = term120.
Proof. exact (TRANS (@lem2391265) (@lem2391268)). Qed.
Lemma lem2391270 (n : int) : (term166 n) = (term166 n).
Proof. exact (eq_refl (term166 n)). Qed.
Lemma lem2391271 (n : int) : (term440 n) = (term441 n).
Proof. exact (MK_COMB (@lem2391270 n) (@lem2391269)). Qed.
Lemma lem2391272 (n : int) : (term441 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2391273 (n : int) : (term440 n) = (real_of_int n).
Proof. exact (TRANS (@lem2391271 n) (@lem2391272 n)). Qed.
Lemma lem2391275 (n : int) : (term439 n) = (real_of_int n).
Proof. exact (TRANS (@lem2391239 n) (@lem2391273 n)). Qed.
Lemma lem2391276 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391277 (n : int) : (term442 n) = (term443 n).
Proof. exact (MK_COMB (@lem2391276) (@lem2391275 n)). Qed.
Lemma lem2391278 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391279 (n : int) : (term438 n) = (term437 n).
Proof. exact (MK_COMB (@lem2391277 n) (@lem2391278)). Qed.
Lemma lem2391280 (n : int) : (term437 n) = (term437 n).
Proof. exact (TRANS (@lem2391233 n) (@lem2391279 n)). Qed.
Lemma lem2391281 (m : int) (n : int) : (term352 m n) = (term346 m n).
Proof. exact (@lem1988291 (term292 m n) term120). Qed.
Lemma lem2391287 (m : int) (n : int) : (term347 m n) = (term348 m n).
Proof. exact (@lem1982792 (term292 m n) term120). Qed.
Lemma lem2391289 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391290 : term120 = term180.
Proof. exact (@lem2391289 (NUMERAL 0)). Qed.
Lemma lem2391292 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391293 : term183 = term184.
Proof. exact (@lem2391292 term154). Qed.
Lemma lem2391294 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391295 : term185 = term186.
Proof. exact (MK_COMB (@lem2391294) (@lem2391293)). Qed.
Lemma lem2391296 : term187 = term188.
Proof. exact (MK_COMB (@lem2391295) (@lem2391290)). Qed.
Lemma lem2391297 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2391299 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391300 : term192 = term193.
Proof. exact (@lem2391299 term154 term154). Qed.
Lemma lem2391301 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391302 : term195 = term154.
Proof. exact (EQ_MP (@lem2391301) (@lem940073)). Qed.
Lemma lem2391303 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391304 : term193 = term153.
Proof. exact (MK_COMB (@lem2391303) (@lem2391302)). Qed.
Lemma lem2391305 : term192 = term153.
Proof. exact (TRANS (@lem2391300) (@lem2391304)). Qed.
Lemma lem2391307 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2391308 : term187 = term120.
Proof. exact (@lem2391307 term154). Qed.
Lemma lem2391309 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391310 : term197 = term198.
Proof. exact (MK_COMB (@lem2391309) (@lem2391308)). Qed.
Lemma lem2391311 : term189 = term180.
Proof. exact (MK_COMB (@lem2391310) (@lem2391305)). Qed.
Lemma lem2391312 : term188 = term180.
Proof. exact (TRANS (@lem2391297) (@lem2391311)). Qed.
Lemma lem2391313 : term187 = term180.
Proof. exact (TRANS (@lem2391296) (@lem2391312)). Qed.
Lemma lem2391315 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391316 : term180 = term120.
Proof. exact (@lem2391315 term120). Qed.
Lemma lem2391317 : term187 = term120.
Proof. exact (TRANS (@lem2391313) (@lem2391316)). Qed.
Lemma lem2391318 (m : int) (n : int) : (term301 m n) = (term301 m n).
Proof. exact (eq_refl (term301 m n)). Qed.
Lemma lem2391319 (m : int) (n : int) : (term348 m n) = (term349 m n).
Proof. exact (MK_COMB (@lem2391318 m n) (@lem2391317)). Qed.
Lemma lem2391320 (m : int) (n : int) : (term349 m n) = (term292 m n).
Proof. exact (@lem1982723 (term292 m n)). Qed.
Lemma lem2391321 (m : int) (n : int) : (term348 m n) = (term292 m n).
Proof. exact (TRANS (@lem2391319 m n) (@lem2391320 m n)). Qed.
Lemma lem2391323 (m : int) (n : int) : (term347 m n) = (term292 m n).
Proof. exact (TRANS (@lem2391287 m n) (@lem2391321 m n)). Qed.
Lemma lem2391324 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391325 (m : int) (n : int) : (term350 m n) = (term351 m n).
Proof. exact (MK_COMB (@lem2391324) (@lem2391323 m n)). Qed.
Lemma lem2391326 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391327 (m : int) (n : int) : (term346 m n) = (term352 m n).
Proof. exact (MK_COMB (@lem2391325 m n) (@lem2391326)). Qed.
Lemma lem2391328 (m : int) (n : int) : (term352 m n) = (term352 m n).
Proof. exact (TRANS (@lem2391281 m n) (@lem2391327 m n)). Qed.
Lemma lem2391329 (m : int) (n : int) : (term444 m n) = (term445 m n).
Proof. exact (@lem1988291 (term446 m n) term120). Qed.
Lemma lem2391353 (m : int) (n : int) : (term447 m n) = (term448 m n).
Proof. exact (@lem1982792 (term446 m n) term120). Qed.
Lemma lem2391355 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391356 : term120 = term180.
Proof. exact (@lem2391355 (NUMERAL 0)). Qed.
Lemma lem2391358 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391359 : term183 = term184.
Proof. exact (@lem2391358 term154). Qed.
Lemma lem2391360 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391361 : term185 = term186.
Proof. exact (MK_COMB (@lem2391360) (@lem2391359)). Qed.
Lemma lem2391362 : term187 = term188.
Proof. exact (MK_COMB (@lem2391361) (@lem2391356)). Qed.
Lemma lem2391363 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2391365 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391366 : term192 = term193.
Proof. exact (@lem2391365 term154 term154). Qed.
Lemma lem2391367 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391368 : term195 = term154.
Proof. exact (EQ_MP (@lem2391367) (@lem940073)). Qed.
Lemma lem2391369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391370 : term193 = term153.
Proof. exact (MK_COMB (@lem2391369) (@lem2391368)). Qed.
Lemma lem2391371 : term192 = term153.
Proof. exact (TRANS (@lem2391366) (@lem2391370)). Qed.
Lemma lem2391373 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2391374 : term187 = term120.
Proof. exact (@lem2391373 term154). Qed.
Lemma lem2391375 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391376 : term197 = term198.
Proof. exact (MK_COMB (@lem2391375) (@lem2391374)). Qed.
Lemma lem2391377 : term189 = term180.
Proof. exact (MK_COMB (@lem2391376) (@lem2391371)). Qed.
Lemma lem2391378 : term188 = term180.
Proof. exact (TRANS (@lem2391363) (@lem2391377)). Qed.
Lemma lem2391379 : term187 = term180.
Proof. exact (TRANS (@lem2391362) (@lem2391378)). Qed.
Lemma lem2391381 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391382 : term180 = term120.
Proof. exact (@lem2391381 term120). Qed.
Lemma lem2391383 : term187 = term120.
Proof. exact (TRANS (@lem2391379) (@lem2391382)). Qed.
Lemma lem2391384 (m : int) (n : int) : (term449 m n) = (term449 m n).
Proof. exact (eq_refl (term449 m n)). Qed.
Lemma lem2391385 (m : int) (n : int) : (term448 m n) = (term450 m n).
Proof. exact (MK_COMB (@lem2391384 m n) (@lem2391383)). Qed.
Lemma lem2391386 (m : int) (n : int) : (term450 m n) = (term446 m n).
Proof. exact (@lem1982723 (term446 m n)). Qed.
Lemma lem2391387 (m : int) (n : int) : (term448 m n) = (term446 m n).
Proof. exact (TRANS (@lem2391385 m n) (@lem2391386 m n)). Qed.
Lemma lem2391389 (m : int) (n : int) : (term447 m n) = (term446 m n).
Proof. exact (TRANS (@lem2391353 m n) (@lem2391387 m n)). Qed.
Lemma lem2391390 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391391 (m : int) (n : int) : (term451 m n) = (term452 m n).
Proof. exact (MK_COMB (@lem2391390) (@lem2391389 m n)). Qed.
Lemma lem2391392 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391393 (m : int) (n : int) : (term445 m n) = (term444 m n).
Proof. exact (MK_COMB (@lem2391391 m n) (@lem2391392)). Qed.
Lemma lem2391394 (m : int) (n : int) : (term444 m n) = (term444 m n).
Proof. exact (TRANS (@lem2391329 m n) (@lem2391393 m n)). Qed.
Lemma lem2391395 (m : int) (n : int) : ((term375 m n) = term120) = ((term453 m n) = term120).
Proof. exact (@lem1988293 (term375 m n) term120). Qed.
Lemma lem2391431 (m : int) (n : int) : (term453 m n) = (term454 m n).
Proof. exact (@lem1982792 (term375 m n) term120). Qed.
Lemma lem2391433 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391434 : term120 = term180.
Proof. exact (@lem2391433 (NUMERAL 0)). Qed.
Lemma lem2391436 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391437 : term183 = term184.
Proof. exact (@lem2391436 term154). Qed.
Lemma lem2391438 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391439 : term185 = term186.
Proof. exact (MK_COMB (@lem2391438) (@lem2391437)). Qed.
Lemma lem2391440 : term187 = term188.
Proof. exact (MK_COMB (@lem2391439) (@lem2391434)). Qed.
Lemma lem2391441 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2391443 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391444 : term192 = term193.
Proof. exact (@lem2391443 term154 term154). Qed.
Lemma lem2391445 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391446 : term195 = term154.
Proof. exact (EQ_MP (@lem2391445) (@lem940073)). Qed.
Lemma lem2391447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391448 : term193 = term153.
Proof. exact (MK_COMB (@lem2391447) (@lem2391446)). Qed.
Lemma lem2391449 : term192 = term153.
Proof. exact (TRANS (@lem2391444) (@lem2391448)). Qed.
Lemma lem2391451 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2391452 : term187 = term120.
Proof. exact (@lem2391451 term154). Qed.
Lemma lem2391453 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391454 : term197 = term198.
Proof. exact (MK_COMB (@lem2391453) (@lem2391452)). Qed.
Lemma lem2391455 : term189 = term180.
Proof. exact (MK_COMB (@lem2391454) (@lem2391449)). Qed.
Lemma lem2391456 : term188 = term180.
Proof. exact (TRANS (@lem2391441) (@lem2391455)). Qed.
Lemma lem2391457 : term187 = term180.
Proof. exact (TRANS (@lem2391440) (@lem2391456)). Qed.
Lemma lem2391459 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391460 : term180 = term120.
Proof. exact (@lem2391459 term120). Qed.
Lemma lem2391461 : term187 = term120.
Proof. exact (TRANS (@lem2391457) (@lem2391460)). Qed.
Lemma lem2391462 (m : int) (n : int) : (term455 m n) = (term455 m n).
Proof. exact (eq_refl (term455 m n)). Qed.
Lemma lem2391463 (m : int) (n : int) : (term454 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem2391462 m n) (@lem2391461)). Qed.
Lemma lem2391464 (m : int) (n : int) : (term456 m n) = (term375 m n).
Proof. exact (@lem1982723 (term375 m n)). Qed.
Lemma lem2391465 (m : int) (n : int) : (term454 m n) = (term375 m n).
Proof. exact (TRANS (@lem2391463 m n) (@lem2391464 m n)). Qed.
Lemma lem2391467 (m : int) (n : int) : (term453 m n) = (term375 m n).
Proof. exact (TRANS (@lem2391431 m n) (@lem2391465 m n)). Qed.
Lemma lem2391468 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2391469 (m : int) (n : int) : (term457 m n) = (term379 m n).
Proof. exact (MK_COMB (@lem2391468) (@lem2391467 m n)). Qed.
Lemma lem2391470 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391471 (m : int) (n : int) : ((term453 m n) = term120) = ((term375 m n) = term120).
Proof. exact (MK_COMB (@lem2391469 m n) (@lem2391470)). Qed.
Lemma lem2391472 (m : int) (n : int) : ((term375 m n) = term120) = ((term375 m n) = term120).
Proof. exact (TRANS (@lem2391395 m n) (@lem2391471 m n)). Qed.
Lemma lem2391473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391474 (m : int) (n : int) : (term458 m n) = (term458 m n).
Proof. exact (MK_COMB (@lem2391473) (@lem2391394 m n)). Qed.
Lemma lem2391475 (m : int) (n : int) : (term459 m n) = (term459 m n).
Proof. exact (MK_COMB (@lem2391474 m n) (@lem2391472 m n)). Qed.
Lemma lem2391476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391477 (m : int) (n : int) : (term382 m n) = (term382 m n).
Proof. exact (MK_COMB (@lem2391476) (@lem2391328 m n)). Qed.
Lemma lem2391478 (m : int) (n : int) : (term460 m n) = (term460 m n).
Proof. exact (MK_COMB (@lem2391477 m n) (@lem2391475 m n)). Qed.
Lemma lem2391479 (m : int) (n : int) : (term399 m n) = (term461 m n).
Proof. exact (@lem1988291 (term396 m n) term120). Qed.
Lemma lem2391521 (m : int) (n : int) : (term462 m n) = (term463 m n).
Proof. exact (@lem1982792 (term396 m n) term120). Qed.
Lemma lem2391523 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391524 : term120 = term180.
Proof. exact (@lem2391523 (NUMERAL 0)). Qed.
Lemma lem2391526 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391527 : term183 = term184.
Proof. exact (@lem2391526 term154). Qed.
Lemma lem2391528 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391529 : term185 = term186.
Proof. exact (MK_COMB (@lem2391528) (@lem2391527)). Qed.
Lemma lem2391530 : term187 = term188.
Proof. exact (MK_COMB (@lem2391529) (@lem2391524)). Qed.
Lemma lem2391531 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2391533 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391534 : term192 = term193.
Proof. exact (@lem2391533 term154 term154). Qed.
Lemma lem2391535 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391536 : term195 = term154.
Proof. exact (EQ_MP (@lem2391535) (@lem940073)). Qed.
Lemma lem2391537 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391538 : term193 = term153.
Proof. exact (MK_COMB (@lem2391537) (@lem2391536)). Qed.
Lemma lem2391539 : term192 = term153.
Proof. exact (TRANS (@lem2391534) (@lem2391538)). Qed.
Lemma lem2391541 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2391542 : term187 = term120.
Proof. exact (@lem2391541 term154). Qed.
Lemma lem2391543 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391544 : term197 = term198.
Proof. exact (MK_COMB (@lem2391543) (@lem2391542)). Qed.
Lemma lem2391545 : term189 = term180.
Proof. exact (MK_COMB (@lem2391544) (@lem2391539)). Qed.
Lemma lem2391546 : term188 = term180.
Proof. exact (TRANS (@lem2391531) (@lem2391545)). Qed.
Lemma lem2391547 : term187 = term180.
Proof. exact (TRANS (@lem2391530) (@lem2391546)). Qed.
Lemma lem2391549 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391550 : term180 = term120.
Proof. exact (@lem2391549 term120). Qed.
Lemma lem2391551 : term187 = term120.
Proof. exact (TRANS (@lem2391547) (@lem2391550)). Qed.
Lemma lem2391552 (m : int) (n : int) : (term464 m n) = (term464 m n).
Proof. exact (eq_refl (term464 m n)). Qed.
Lemma lem2391553 (m : int) (n : int) : (term463 m n) = (term465 m n).
Proof. exact (MK_COMB (@lem2391552 m n) (@lem2391551)). Qed.
Lemma lem2391554 (m : int) (n : int) : (term465 m n) = (term396 m n).
Proof. exact (@lem1982723 (term396 m n)). Qed.
Lemma lem2391555 (m : int) (n : int) : (term463 m n) = (term396 m n).
Proof. exact (TRANS (@lem2391553 m n) (@lem2391554 m n)). Qed.
Lemma lem2391557 (m : int) (n : int) : (term462 m n) = (term396 m n).
Proof. exact (TRANS (@lem2391521 m n) (@lem2391555 m n)). Qed.
Lemma lem2391558 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391559 (m : int) (n : int) : (term466 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem2391558) (@lem2391557 m n)). Qed.
Lemma lem2391560 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391561 (m : int) (n : int) : (term461 m n) = (term399 m n).
Proof. exact (MK_COMB (@lem2391559 m n) (@lem2391560)). Qed.
Lemma lem2391562 (m : int) (n : int) : (term399 m n) = (term399 m n).
Proof. exact (TRANS (@lem2391479 m n) (@lem2391561 m n)). Qed.
Lemma lem2391563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391564 (m : int) (n : int) : (term467 m n) = (term467 m n).
Proof. exact (MK_COMB (@lem2391563) (@lem2391478 m n)). Qed.
Lemma lem2391565 (m : int) (n : int) : (term429 m n) = (term429 m n).
Proof. exact (MK_COMB (@lem2391564 m n) (@lem2391562 m n)). Qed.
Lemma lem2391566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391567 (n : int) : (term430 n) = (term430 n).
Proof. exact (MK_COMB (@lem2391566) (@lem2391280 n)). Qed.
Lemma lem2391568 (m : int) (n : int) : (term432 m n) = (term432 m n).
Proof. exact (MK_COMB (@lem2391567 n) (@lem2391565 m n)). Qed.
Lemma lem2391569 (n : int) : (term468 n) = (term469 n).
Proof. exact (@lem1988289 term120 (real_of_int n)). Qed.
Lemma lem2391575 (n : int) : (term470 n) = (term471 n).
Proof. exact (@lem1982792 term120 (real_of_int n)). Qed.
Lemma lem2391580 (n : int) : (term471 n) = (term206 n).
Proof. exact (@lem1982721 (term206 n)). Qed.
Lemma lem2391582 (n : int) : (term470 n) = (term206 n).
Proof. exact (TRANS (@lem2391575 n) (@lem2391580 n)). Qed.
Lemma lem2391583 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2391584 (n : int) : (term472 n) = (term473 n).
Proof. exact (MK_COMB (@lem2391583) (@lem2391582 n)). Qed.
Lemma lem2391585 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391586 (n : int) : (term469 n) = (term474 n).
Proof. exact (MK_COMB (@lem2391584 n) (@lem2391585)). Qed.
Lemma lem2391587 (n : int) : (term468 n) = (term474 n).
Proof. exact (TRANS (@lem2391569 n) (@lem2391586 n)). Qed.
Lemma lem2391588 (m : int) (n : int) : (term475 m n) = (term476 m n).
Proof. exact (@lem1988291 (term477 m n) term120). Qed.
Lemma lem2391589 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391602 (m : int) (n : int) : (term359 m n) = (term359 m n).
Proof. exact (eq_refl (term359 m n)). Qed.
Lemma lem2391609 (n : int) : (term478 n) = (term206 n).
Proof. exact (@lem1982785 (real_of_int n)). Qed.
Lemma lem2391610 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2391611 (n : int) : (term479 n) = (term228 n).
Proof. exact (MK_COMB (@lem2391610) (@lem2391609 n)). Qed.
Lemma lem2391614 (m : int) (n : int) : (term477 m n) = (term480 m n).
Proof. exact (MK_COMB (@lem2391611 n) (@lem2391602 m n)). Qed.
Lemma lem2391615 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2391616 (m : int) (n : int) : (term481 m n) = (term482 m n).
Proof. exact (MK_COMB (@lem2391615) (@lem2391614 m n)). Qed.
Lemma lem2391617 (m : int) (n : int) : (term483 m n) = (term484 m n).
Proof. exact (MK_COMB (@lem2391616 m n) (@lem2391589)). Qed.
Lemma lem2391618 (m : int) (n : int) : (term484 m n) = (term485 m n).
Proof. exact (@lem1982792 (term480 m n) term120). Qed.
Lemma lem2391620 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391621 : term120 = term180.
Proof. exact (@lem2391620 (NUMERAL 0)). Qed.
Lemma lem2391623 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391624 : term183 = term184.
Proof. exact (@lem2391623 term154). Qed.
Lemma lem2391625 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391626 : term185 = term186.
Proof. exact (MK_COMB (@lem2391625) (@lem2391624)). Qed.
Lemma lem2391627 : term187 = term188.
Proof. exact (MK_COMB (@lem2391626) (@lem2391621)). Qed.
Lemma lem2391628 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2391630 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391631 : term192 = term193.
Proof. exact (@lem2391630 term154 term154). Qed.
Lemma lem2391632 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391633 : term195 = term154.
Proof. exact (EQ_MP (@lem2391632) (@lem940073)). Qed.
Lemma lem2391634 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391635 : term193 = term153.
Proof. exact (MK_COMB (@lem2391634) (@lem2391633)). Qed.
Lemma lem2391636 : term192 = term153.
Proof. exact (TRANS (@lem2391631) (@lem2391635)). Qed.
Lemma lem2391638 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2391639 : term187 = term120.
Proof. exact (@lem2391638 term154). Qed.
Lemma lem2391640 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391641 : term197 = term198.
Proof. exact (MK_COMB (@lem2391640) (@lem2391639)). Qed.
Lemma lem2391642 : term189 = term180.
Proof. exact (MK_COMB (@lem2391641) (@lem2391636)). Qed.
Lemma lem2391643 : term188 = term180.
Proof. exact (TRANS (@lem2391628) (@lem2391642)). Qed.
Lemma lem2391644 : term187 = term180.
Proof. exact (TRANS (@lem2391627) (@lem2391643)). Qed.
Lemma lem2391646 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391647 : term180 = term120.
Proof. exact (@lem2391646 term120). Qed.
Lemma lem2391648 : term187 = term120.
Proof. exact (TRANS (@lem2391644) (@lem2391647)). Qed.
Lemma lem2391649 (m : int) (n : int) : (term486 m n) = (term486 m n).
Proof. exact (eq_refl (term486 m n)). Qed.
Lemma lem2391650 (m : int) (n : int) : (term485 m n) = (term487 m n).
Proof. exact (MK_COMB (@lem2391649 m n) (@lem2391648)). Qed.
Lemma lem2391651 (m : int) (n : int) : (term487 m n) = (term480 m n).
Proof. exact (@lem1982723 (term480 m n)). Qed.
Lemma lem2391652 (m : int) (n : int) : (term485 m n) = (term480 m n).
Proof. exact (TRANS (@lem2391650 m n) (@lem2391651 m n)). Qed.
Lemma lem2391653 (m : int) (n : int) : (term484 m n) = (term480 m n).
Proof. exact (TRANS (@lem2391618 m n) (@lem2391652 m n)). Qed.
Lemma lem2391654 (m : int) (n : int) : (term483 m n) = (term480 m n).
Proof. exact (TRANS (@lem2391617 m n) (@lem2391653 m n)). Qed.
Lemma lem2391655 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391656 (m : int) (n : int) : (term488 m n) = (term489 m n).
Proof. exact (MK_COMB (@lem2391655) (@lem2391654 m n)). Qed.
Lemma lem2391657 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391658 (m : int) (n : int) : (term476 m n) = (term490 m n).
Proof. exact (MK_COMB (@lem2391656 m n) (@lem2391657)). Qed.
Lemma lem2391659 (m : int) (n : int) : (term475 m n) = (term490 m n).
Proof. exact (TRANS (@lem2391588 m n) (@lem2391658 m n)). Qed.
Lemma lem2391660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391661 (m : int) (n : int) : (term491 m n) = (term492 m n).
Proof. exact (MK_COMB (@lem2391660) (@lem2391659 m n)). Qed.
Lemma lem2391662 (m : int) (n : int) : (term493 m n) = (term494 m n).
Proof. exact (MK_COMB (@lem2391661 m n) (@lem2391472 m n)). Qed.
Lemma lem2391663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391664 (m : int) (n : int) : (term382 m n) = (term382 m n).
Proof. exact (MK_COMB (@lem2391663) (@lem2391328 m n)). Qed.
Lemma lem2391665 (m : int) (n : int) : (term495 m n) = (term496 m n).
Proof. exact (MK_COMB (@lem2391664 m n) (@lem2391662 m n)). Qed.
Lemma lem2391666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391667 (m : int) (n : int) : (term497 m n) = (term498 m n).
Proof. exact (MK_COMB (@lem2391666) (@lem2391665 m n)). Qed.
Lemma lem2391668 (m : int) (n : int) : (term424 m n) = (term499 m n).
Proof. exact (MK_COMB (@lem2391667 m n) (@lem2391562 m n)). Qed.
Lemma lem2391669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391670 (n : int) : (term425 n) = (term500 n).
Proof. exact (MK_COMB (@lem2391669) (@lem2391587 n)). Qed.
Lemma lem2391671 (m : int) (n : int) : (term427 m n) = (term501 m n).
Proof. exact (MK_COMB (@lem2391670 n) (@lem2391668 m n)). Qed.
Lemma lem2391672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2391673 (m : int) (n : int) : (term434 m n) = (term434 m n).
Proof. exact (MK_COMB (@lem2391672) (@lem2391568 m n)). Qed.
Lemma lem2391674 (m : int) (n : int) : (term435 m n) = (term502 m n).
Proof. exact (MK_COMB (@lem2391673 m n) (@lem2391671 m n)). Qed.
Lemma lem2391686 (m : int) (n : int) : (term420 m n) = (term502 m n).
Proof. exact (TRANS (@lem2391232 m n) (@lem2391674 m n)). Qed.
Lemma lem2391688 (m : int) (n : int) : (term503 m n) = (term504 m n).
Proof. exact (eq_refl (term503 m n)). Qed.
Lemma lem2391689 (m : int) (n : int) : (term504 m n) = (term503 m n).
Proof. exact (SYM (@lem2391688 m n)). Qed.
Lemma lem2391690 (m : int) (n : int) : (term503 m n) = (term505 m n).
Proof. exact (@lem1482981 (term506 m n) (real_of_int n)). Qed.
Lemma lem2391691 (m : int) (n : int) : (term504 m n) = (term505 m n).
Proof. exact (TRANS (@lem2391689 m n) (@lem2391690 m n)). Qed.
Lemma lem2391692 (m : int) (n : int) : (term507 m n) = (term508 m n).
Proof. exact (eq_refl (term507 m n)). Qed.
Lemma lem2391693 (n : int) : (term425 n) = (term425 n).
Proof. exact (eq_refl (term425 n)). Qed.
Lemma lem2391694 (m : int) (n : int) : (term509 m n) = (term510 m n).
Proof. exact (MK_COMB (@lem2391693 n) (@lem2391692 m n)). Qed.
Lemma lem2391695 (m : int) (n : int) : (term511 m n) = (term512 m n).
Proof. exact (eq_refl (term511 m n)). Qed.
Lemma lem2391696 (n : int) : (term430 n) = (term430 n).
Proof. exact (eq_refl (term430 n)). Qed.
Lemma lem2391697 (m : int) (n : int) : (term513 m n) = (term514 m n).
Proof. exact (MK_COMB (@lem2391696 n) (@lem2391695 m n)). Qed.
Lemma lem2391698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2391699 (m : int) (n : int) : (term515 m n) = (term516 m n).
Proof. exact (MK_COMB (@lem2391698) (@lem2391697 m n)). Qed.
Lemma lem2391700 (m : int) (n : int) : (term505 m n) = (term517 m n).
Proof. exact (MK_COMB (@lem2391699 m n) (@lem2391694 m n)). Qed.
Lemma lem2391701 (m : int) (n : int) : (term518 m n) = (term518 m n).
Proof. exact (eq_refl (term518 m n)). Qed.
Lemma lem2391702 (m : int) (n : int) : ((term504 m n) = (term505 m n)) = ((term504 m n) = (term517 m n)).
Proof. exact (MK_COMB (@lem2391701 m n) (@lem2391700 m n)). Qed.
Lemma lem2391703 (m : int) (n : int) : (term504 m n) = (term517 m n).
Proof. exact (EQ_MP (@lem2391702 m n) (@lem2391691 m n)). Qed.
Lemma lem2391704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391705 (m : int) (n : int) : (term458 m n) = (term458 m n).
Proof. exact (MK_COMB (@lem2391704) (@lem2391394 m n)). Qed.
Lemma lem2391706 (m : int) (n : int) : (term459 m n) = (term459 m n).
Proof. exact (MK_COMB (@lem2391705 m n) (@lem2391472 m n)). Qed.
Lemma lem2391707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391708 (m : int) (n : int) : (term382 m n) = (term382 m n).
Proof. exact (MK_COMB (@lem2391707) (@lem2391328 m n)). Qed.
Lemma lem2391709 (m : int) (n : int) : (term460 m n) = (term460 m n).
Proof. exact (MK_COMB (@lem2391708 m n) (@lem2391706 m n)). Qed.
Lemma lem2391710 (m : int) (n : int) : (term413 m n) = (term519 m n).
Proof. exact (@lem1988291 (term410 m n) term120). Qed.
Lemma lem2391746 (m : int) (n : int) : (term520 m n) = (term521 m n).
Proof. exact (@lem1982792 (term410 m n) term120). Qed.
Lemma lem2391748 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391749 : term120 = term180.
Proof. exact (@lem2391748 (NUMERAL 0)). Qed.
Lemma lem2391751 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391752 : term183 = term184.
Proof. exact (@lem2391751 term154). Qed.
Lemma lem2391753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391754 : term185 = term186.
Proof. exact (MK_COMB (@lem2391753) (@lem2391752)). Qed.
Lemma lem2391755 : term187 = term188.
Proof. exact (MK_COMB (@lem2391754) (@lem2391749)). Qed.
Lemma lem2391756 : term188 = term189.
Proof. exact (@lem1981613 term183 term120 term153 term153). Qed.
Lemma lem2391758 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391759 : term192 = term193.
Proof. exact (@lem2391758 term154 term154). Qed.
Lemma lem2391760 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391761 : term195 = term154.
Proof. exact (EQ_MP (@lem2391760) (@lem940073)). Qed.
Lemma lem2391762 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391763 : term193 = term153.
Proof. exact (MK_COMB (@lem2391762) (@lem2391761)). Qed.
Lemma lem2391764 : term192 = term153.
Proof. exact (TRANS (@lem2391759) (@lem2391763)). Qed.
Lemma lem2391766 (x : nat) : (term196 x) = term120.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2391767 : term187 = term120.
Proof. exact (@lem2391766 term154). Qed.
Lemma lem2391768 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391769 : term197 = term198.
Proof. exact (MK_COMB (@lem2391768) (@lem2391767)). Qed.
Lemma lem2391770 : term189 = term180.
Proof. exact (MK_COMB (@lem2391769) (@lem2391764)). Qed.
Lemma lem2391771 : term188 = term180.
Proof. exact (TRANS (@lem2391756) (@lem2391770)). Qed.
Lemma lem2391772 : term187 = term180.
Proof. exact (TRANS (@lem2391755) (@lem2391771)). Qed.
Lemma lem2391774 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391775 : term180 = term120.
Proof. exact (@lem2391774 term120). Qed.
Lemma lem2391776 : term187 = term120.
Proof. exact (TRANS (@lem2391772) (@lem2391775)). Qed.
Lemma lem2391777 (m : int) (n : int) : (term522 m n) = (term522 m n).
Proof. exact (eq_refl (term522 m n)). Qed.
Lemma lem2391778 (m : int) (n : int) : (term521 m n) = (term523 m n).
Proof. exact (MK_COMB (@lem2391777 m n) (@lem2391776)). Qed.
Lemma lem2391779 (m : int) (n : int) : (term523 m n) = (term410 m n).
Proof. exact (@lem1982723 (term410 m n)). Qed.
Lemma lem2391780 (m : int) (n : int) : (term521 m n) = (term410 m n).
Proof. exact (TRANS (@lem2391778 m n) (@lem2391779 m n)). Qed.
Lemma lem2391782 (m : int) (n : int) : (term520 m n) = (term410 m n).
Proof. exact (TRANS (@lem2391746 m n) (@lem2391780 m n)). Qed.
Lemma lem2391783 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391784 (m : int) (n : int) : (term524 m n) = (term412 m n).
Proof. exact (MK_COMB (@lem2391783) (@lem2391782 m n)). Qed.
Lemma lem2391785 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391786 (m : int) (n : int) : (term519 m n) = (term413 m n).
Proof. exact (MK_COMB (@lem2391784 m n) (@lem2391785)). Qed.
Lemma lem2391787 (m : int) (n : int) : (term413 m n) = (term413 m n).
Proof. exact (TRANS (@lem2391710 m n) (@lem2391786 m n)). Qed.
Lemma lem2391788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391789 (m : int) (n : int) : (term467 m n) = (term467 m n).
Proof. exact (MK_COMB (@lem2391788) (@lem2391709 m n)). Qed.
Lemma lem2391790 (m : int) (n : int) : (term512 m n) = (term512 m n).
Proof. exact (MK_COMB (@lem2391789 m n) (@lem2391787 m n)). Qed.
Lemma lem2391791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391792 (n : int) : (term430 n) = (term430 n).
Proof. exact (MK_COMB (@lem2391791) (@lem2391280 n)). Qed.
Lemma lem2391793 (m : int) (n : int) : (term514 m n) = (term514 m n).
Proof. exact (MK_COMB (@lem2391792 n) (@lem2391790 m n)). Qed.
Lemma lem2391794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391795 (m : int) (n : int) : (term491 m n) = (term492 m n).
Proof. exact (MK_COMB (@lem2391794) (@lem2391659 m n)). Qed.
Lemma lem2391796 (m : int) (n : int) : (term493 m n) = (term494 m n).
Proof. exact (MK_COMB (@lem2391795 m n) (@lem2391472 m n)). Qed.
Lemma lem2391797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391798 (m : int) (n : int) : (term382 m n) = (term382 m n).
Proof. exact (MK_COMB (@lem2391797) (@lem2391328 m n)). Qed.
Lemma lem2391799 (m : int) (n : int) : (term495 m n) = (term496 m n).
Proof. exact (MK_COMB (@lem2391798 m n) (@lem2391796 m n)). Qed.
Lemma lem2391800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391801 (m : int) (n : int) : (term497 m n) = (term498 m n).
Proof. exact (MK_COMB (@lem2391800) (@lem2391799 m n)). Qed.
Lemma lem2391802 (m : int) (n : int) : (term508 m n) = (term525 m n).
Proof. exact (MK_COMB (@lem2391801 m n) (@lem2391787 m n)). Qed.
Lemma lem2391803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2391804 (n : int) : (term425 n) = (term500 n).
Proof. exact (MK_COMB (@lem2391803) (@lem2391587 n)). Qed.
Lemma lem2391805 (m : int) (n : int) : (term510 m n) = (term526 m n).
Proof. exact (MK_COMB (@lem2391804 n) (@lem2391802 m n)). Qed.
Lemma lem2391806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2391807 (m : int) (n : int) : (term516 m n) = (term516 m n).
Proof. exact (MK_COMB (@lem2391806) (@lem2391793 m n)). Qed.
Lemma lem2391808 (m : int) (n : int) : (term517 m n) = (term527 m n).
Proof. exact (MK_COMB (@lem2391807 m n) (@lem2391805 m n)). Qed.
Lemma lem2391820 (m : int) (n : int) : (term504 m n) = (term527 m n).
Proof. exact (TRANS (@lem2391703 m n) (@lem2391808 m n)). Qed.
Lemma lem2391821 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2391822 (m : int) (n : int) : (term528 m n) = (term529 m n).
Proof. exact (MK_COMB (@lem2391821) (@lem2391686 m n)). Qed.
Lemma lem2391823 (m : int) (n : int) : (term418 m n) = (term530 m n).
Proof. exact (MK_COMB (@lem2391822 m n) (@lem2391820 m n)). Qed.
Lemma lem2391824 (m : int) (n : int) (h1 : term530 m n) : term530 m n.
Proof. exact (h1). Qed.
Lemma lem2391825 (m : int) (n : int) (h1 : term502 m n) : term502 m n.
Proof. exact (h1). Qed.
Lemma lem2391826 (m : int) (n : int) (h1 : term432 m n) : term432 m n.
Proof. exact (h1). Qed.
Lemma lem2391827 (m : int) (n : int) (h1 : term432 m n) : term429 m n.
Proof. exact (proj2 (@lem2391826 m n h1)). Qed.
Lemma lem2391829 (m : int) (n : int) (h1 : term432 m n) : term399 m n.
Proof. exact (proj2 (@lem2391827 m n h1)). Qed.
Lemma lem2391830 (m : int) (n : int) (h1 : term432 m n) : term460 m n.
Proof. exact (proj1 (@lem2391827 m n h1)). Qed.
Lemma lem2391831 (m : int) (n : int) (h1 : term432 m n) : term459 m n.
Proof. exact (proj2 (@lem2391830 m n h1)). Qed.
Lemma lem2391833 (m : int) (n : int) (h1 : term432 m n) : (term375 m n) = term120.
Proof. exact (proj2 (@lem2391831 m n h1)). Qed.
Lemma lem2391836 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2391837 : term531 = term240.
Proof. exact (@lem2391836 term120 term153). Qed.
Lemma lem2391839 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391840 : term153 = term219.
Proof. exact (@lem2391839 term154). Qed.
Lemma lem2391842 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2391843 : term120 = term180.
Proof. exact (@lem2391842 (NUMERAL 0)). Qed.
Lemma lem2391844 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2391845 : term532 = term533.
Proof. exact (MK_COMB (@lem2391844) (@lem2391843)). Qed.
Lemma lem2391846 : term240 = term534.
Proof. exact (MK_COMB (@lem2391845) (@lem2391840)). Qed.
Lemma lem2391847 : term535.
Proof. exact (@lem1980255 term120 term153 term153 term153). Qed.
Lemma lem2391849 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2391850 : term240 = term241.
Proof. exact (@lem2391849 (NUMERAL 0) term154). Qed.
Lemma lem2391851 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2391852 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2391853 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2391852 h1) (fun h1 : term241 = True => @lem2391851)). Qed.
Lemma lem2391854 : term241 = True.
Proof. exact (EQ_MP (@lem2391853) (@lem2391851)). Qed.
Lemma lem2391855 : term240 = True.
Proof. exact (TRANS (@lem2391850) (@lem2391854)). Qed.
Lemma lem2391856 : True = term240.
Proof. exact (SYM (@lem2391855)). Qed.
Lemma lem2391857 : term240.
Proof. exact (EQ_MP (@lem2391856) (@lem0)). Qed.
Lemma lem2391858 : term536.
Proof. exact (@lem2391847 (@lem2391857)). Qed.
Lemma lem2391860 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2391861 : term240 = term241.
Proof. exact (@lem2391860 (NUMERAL 0) term154). Qed.
Lemma lem2391862 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2391863 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2391864 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2391863 h1) (fun h1 : term241 = True => @lem2391862)). Qed.
Lemma lem2391865 : term241 = True.
Proof. exact (EQ_MP (@lem2391864) (@lem2391862)). Qed.
Lemma lem2391866 : term240 = True.
Proof. exact (TRANS (@lem2391861) (@lem2391865)). Qed.
Lemma lem2391867 : True = term240.
Proof. exact (SYM (@lem2391866)). Qed.
Lemma lem2391868 : term240.
Proof. exact (EQ_MP (@lem2391867) (@lem0)). Qed.
Lemma lem2391869 : term534 = term537.
Proof. exact (@lem2391858 (@lem2391868)). Qed.
Lemma lem2391871 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391872 : term192 = term193.
Proof. exact (@lem2391871 term154 term154). Qed.
Lemma lem2391873 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391874 : term195 = term154.
Proof. exact (EQ_MP (@lem2391873) (@lem940073)). Qed.
Lemma lem2391875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391876 : term193 = term153.
Proof. exact (MK_COMB (@lem2391875) (@lem2391874)). Qed.
Lemma lem2391877 : term192 = term153.
Proof. exact (TRANS (@lem2391872) (@lem2391876)). Qed.
Lemma lem2391879 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2391880 : term251 = term120.
Proof. exact (@lem2391879 term154). Qed.
Lemma lem2391881 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2391882 : term538 = term532.
Proof. exact (MK_COMB (@lem2391881) (@lem2391880)). Qed.
Lemma lem2391883 : term537 = term240.
Proof. exact (MK_COMB (@lem2391882) (@lem2391877)). Qed.
Lemma lem2391885 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2391886 : term240 = term241.
Proof. exact (@lem2391885 (NUMERAL 0) term154). Qed.
Lemma lem2391887 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2391888 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2391889 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2391888 h1) (fun h1 : term241 = True => @lem2391887)). Qed.
Lemma lem2391890 : term241 = True.
Proof. exact (EQ_MP (@lem2391889) (@lem2391887)). Qed.
Lemma lem2391891 : term240 = True.
Proof. exact (TRANS (@lem2391886) (@lem2391890)). Qed.
Lemma lem2391892 : term537 = True.
Proof. exact (TRANS (@lem2391883) (@lem2391891)). Qed.
Lemma lem2391893 : term534 = True.
Proof. exact (TRANS (@lem2391869) (@lem2391892)). Qed.
Lemma lem2391894 : term240 = True.
Proof. exact (TRANS (@lem2391846) (@lem2391893)). Qed.
Lemma lem2391895 : term531 = True.
Proof. exact (TRANS (@lem2391837) (@lem2391894)). Qed.
Lemma lem2391896 : True = term531.
Proof. exact (SYM (@lem2391895)). Qed.
Lemma lem2391897 : term531.
Proof. exact (EQ_MP (@lem2391896) (@lem0)). Qed.
Lemma lem2391898 (m : int) (n : int) (h1 : term432 m n) : term539 m n.
Proof. exact (conj (@lem2391897) (@lem2391829 m n h1)). Qed.
Lemma lem2391900 (x : real) (y : real) : term540 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2391901 (m : int) (n : int) : term541 m n.
Proof. exact (@lem2391900 term153 (term396 m n)). Qed.
Lemma lem2391902 (m : int) (n : int) (h1 : term432 m n) : term542 m n.
Proof. exact (@lem2391901 m n (@lem2391898 m n h1)). Qed.
Lemma lem2391903 (m : int) (n : int) : (term543 m n) = (term396 m n).
Proof. exact (@lem1982733 (term396 m n)). Qed.
Lemma lem2391904 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2391905 (m : int) (n : int) : (term544 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem2391904) (@lem2391903 m n)). Qed.
Lemma lem2391906 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2391907 (m : int) (n : int) : (term542 m n) = (term399 m n).
Proof. exact (MK_COMB (@lem2391905 m n) (@lem2391906)). Qed.
Lemma lem2391908 (m : int) (n : int) (h1 : term432 m n) : term399 m n.
Proof. exact (EQ_MP (@lem2391907 m n) (@lem2391902 m n h1)). Qed.
Lemma lem2391910 (y : real) : term545 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2391911 (m : int) (n : int) : term546 m n.
Proof. exact (@lem2391910 (term375 m n)). Qed.
Lemma lem2391912 (m : int) (n : int) (h1 : term432 m n) : term547 m n.
Proof. exact (@lem2391911 m n (@lem2391833 m n h1)). Qed.
Lemma lem2391913 (m : int) (n : int) (h1 : term432 m n) : term548 m n.
Proof. exact (@lem2391912 m n h1 term183). Qed.
Lemma lem2391914 (m : int) (n : int) : (term548 m n) = ((term549 m n) = term120).
Proof. exact (eq_refl (term548 m n)). Qed.
Lemma lem2391915 (m : int) (n : int) (h1 : term432 m n) : (term549 m n) = term120.
Proof. exact (EQ_MP (@lem2391914 m n) (@lem2391913 m n h1)). Qed.
Lemma lem2391916 (m : int) (n : int) : (term549 m n) = (term550 m n).
Proof. exact (@lem1982781 (term376 m n) term183 (term551 m n)). Qed.
Lemma lem2391917 (m : int) (n : int) : (term552 m n) = (term553 m n).
Proof. exact (@lem1982781 (real_of_int m) term183 (term377 m n)). Qed.
Lemma lem2391918 (m : int) (n : int) : (term554 m n) = (term555 m n).
Proof. exact (@lem1982749 term183 term183 (term292 m n)). Qed.
Lemma lem2391920 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391921 : term183 = term184.
Proof. exact (@lem2391920 term154). Qed.
Lemma lem2391923 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391924 : term183 = term184.
Proof. exact (@lem2391923 term154). Qed.
Lemma lem2391925 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391926 : term185 = term186.
Proof. exact (MK_COMB (@lem2391925) (@lem2391924)). Qed.
Lemma lem2391927 : term556 = term557.
Proof. exact (MK_COMB (@lem2391926) (@lem2391921)). Qed.
Lemma lem2391928 : term557 = term558.
Proof. exact (@lem1981613 term183 term183 term153 term153). Qed.
Lemma lem2391930 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391931 : term192 = term193.
Proof. exact (@lem2391930 term154 term154). Qed.
Lemma lem2391932 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391933 : term195 = term154.
Proof. exact (EQ_MP (@lem2391932) (@lem940073)). Qed.
Lemma lem2391934 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391935 : term193 = term153.
Proof. exact (MK_COMB (@lem2391934) (@lem2391933)). Qed.
Lemma lem2391936 : term192 = term153.
Proof. exact (TRANS (@lem2391931) (@lem2391935)). Qed.
Lemma lem2391938 (m : nat) (n : nat) : (term559 m n) = (term191 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2391939 : term556 = term193.
Proof. exact (@lem2391938 term154 term154). Qed.
Lemma lem2391940 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391941 : term195 = term154.
Proof. exact (EQ_MP (@lem2391940) (@lem940073)). Qed.
Lemma lem2391942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391943 : term193 = term153.
Proof. exact (MK_COMB (@lem2391942) (@lem2391941)). Qed.
Lemma lem2391944 : term556 = term153.
Proof. exact (TRANS (@lem2391939) (@lem2391943)). Qed.
Lemma lem2391945 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391946 : term560 = term561.
Proof. exact (MK_COMB (@lem2391945) (@lem2391944)). Qed.
Lemma lem2391947 : term558 = term219.
Proof. exact (MK_COMB (@lem2391946) (@lem2391936)). Qed.
Lemma lem2391948 : term557 = term219.
Proof. exact (TRANS (@lem2391928) (@lem2391947)). Qed.
Lemma lem2391949 : term556 = term219.
Proof. exact (TRANS (@lem2391927) (@lem2391948)). Qed.
Lemma lem2391951 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2391952 : term219 = term153.
Proof. exact (@lem2391951 term153). Qed.
Lemma lem2391953 : term556 = term153.
Proof. exact (TRANS (@lem2391949) (@lem2391952)). Qed.
Lemma lem2391954 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391955 : term562 = term563.
Proof. exact (MK_COMB (@lem2391954) (@lem2391953)). Qed.
Lemma lem2391956 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2391957 (m : int) (n : int) : (term555 m n) = (term564 m n).
Proof. exact (MK_COMB (@lem2391955) (@lem2391956 m n)). Qed.
Lemma lem2391958 (m : int) (n : int) : (term554 m n) = (term564 m n).
Proof. exact (TRANS (@lem2391918 m n) (@lem2391957 m n)). Qed.
Lemma lem2391959 (m : int) (n : int) : (term564 m n) = (term292 m n).
Proof. exact (@lem1982709 (term292 m n)). Qed.
Lemma lem2391960 (m : int) (n : int) : (term554 m n) = (term292 m n).
Proof. exact (TRANS (@lem2391958 m n) (@lem2391959 m n)). Qed.
Lemma lem2391963 (m : int) : (term228 m) = (term228 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem2391964 (m : int) (n : int) : (term553 m n) = (term565 m n).
Proof. exact (MK_COMB (@lem2391963 m) (@lem2391960 m n)). Qed.
Lemma lem2391965 (m : int) (n : int) : (term552 m n) = (term565 m n).
Proof. exact (TRANS (@lem2391917 m n) (@lem2391964 m n)). Qed.
Lemma lem2391966 (m : int) (n : int) : (term566 m n) = (term567 m n).
Proof. exact (@lem1982749 term183 term183 (term366 m n)). Qed.
Lemma lem2391968 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391969 : term183 = term184.
Proof. exact (@lem2391968 term154). Qed.
Lemma lem2391971 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2391972 : term183 = term184.
Proof. exact (@lem2391971 term154). Qed.
Lemma lem2391973 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2391974 : term185 = term186.
Proof. exact (MK_COMB (@lem2391973) (@lem2391972)). Qed.
Lemma lem2391975 : term556 = term557.
Proof. exact (MK_COMB (@lem2391974) (@lem2391969)). Qed.
Lemma lem2391976 : term557 = term558.
Proof. exact (@lem1981613 term183 term183 term153 term153). Qed.
Lemma lem2391978 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2391979 : term192 = term193.
Proof. exact (@lem2391978 term154 term154). Qed.
Lemma lem2391980 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391981 : term195 = term154.
Proof. exact (EQ_MP (@lem2391980) (@lem940073)). Qed.
Lemma lem2391982 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391983 : term193 = term153.
Proof. exact (MK_COMB (@lem2391982) (@lem2391981)). Qed.
Lemma lem2391984 : term192 = term153.
Proof. exact (TRANS (@lem2391979) (@lem2391983)). Qed.
Lemma lem2391986 (m : nat) (n : nat) : (term559 m n) = (term191 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2391987 : term556 = term193.
Proof. exact (@lem2391986 term154 term154). Qed.
Lemma lem2391988 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2391989 : term195 = term154.
Proof. exact (EQ_MP (@lem2391988) (@lem940073)). Qed.
Lemma lem2391990 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2391991 : term193 = term153.
Proof. exact (MK_COMB (@lem2391990) (@lem2391989)). Qed.
Lemma lem2391992 : term556 = term153.
Proof. exact (TRANS (@lem2391987) (@lem2391991)). Qed.
Lemma lem2391993 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2391994 : term560 = term561.
Proof. exact (MK_COMB (@lem2391993) (@lem2391992)). Qed.
Lemma lem2391995 : term558 = term219.
Proof. exact (MK_COMB (@lem2391994) (@lem2391984)). Qed.
Lemma lem2391996 : term557 = term219.
Proof. exact (TRANS (@lem2391976) (@lem2391995)). Qed.
Lemma lem2391997 : term556 = term219.
Proof. exact (TRANS (@lem2391975) (@lem2391996)). Qed.
Lemma lem2391999 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2392000 : term219 = term153.
Proof. exact (@lem2391999 term153). Qed.
Lemma lem2392001 : term556 = term153.
Proof. exact (TRANS (@lem2391997) (@lem2392000)). Qed.
Lemma lem2392002 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392003 : term562 = term563.
Proof. exact (MK_COMB (@lem2392002) (@lem2392001)). Qed.
Lemma lem2392004 (m : int) (n : int) : (term366 m n) = (term366 m n).
Proof. exact (eq_refl (term366 m n)). Qed.
Lemma lem2392005 (m : int) (n : int) : (term567 m n) = (term568 m n).
Proof. exact (MK_COMB (@lem2392003) (@lem2392004 m n)). Qed.
Lemma lem2392006 (m : int) (n : int) : (term566 m n) = (term568 m n).
Proof. exact (TRANS (@lem2391966 m n) (@lem2392005 m n)). Qed.
Lemma lem2392007 (m : int) (n : int) : (term568 m n) = (term366 m n).
Proof. exact (@lem1982709 (term366 m n)). Qed.
Lemma lem2392008 (m : int) (n : int) : (term566 m n) = (term366 m n).
Proof. exact (TRANS (@lem2392006 m n) (@lem2392007 m n)). Qed.
Lemma lem2392009 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392010 (m : int) (n : int) : (term569 m n) = (term368 m n).
Proof. exact (MK_COMB (@lem2392009) (@lem2392008 m n)). Qed.
Lemma lem2392011 (m : int) (n : int) : (term550 m n) = (term570 m n).
Proof. exact (MK_COMB (@lem2392010 m n) (@lem2391965 m n)). Qed.
Lemma lem2392012 (m : int) (n : int) : (term549 m n) = (term570 m n).
Proof. exact (TRANS (@lem2391916 m n) (@lem2392011 m n)). Qed.
Lemma lem2392013 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2392014 (m : int) (n : int) : (term571 m n) = (term572 m n).
Proof. exact (MK_COMB (@lem2392013) (@lem2392012 m n)). Qed.
Lemma lem2392015 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2392016 (m : int) (n : int) : ((term549 m n) = term120) = ((term570 m n) = term120).
Proof. exact (MK_COMB (@lem2392014 m n) (@lem2392015)). Qed.
Lemma lem2392017 (m : int) (n : int) (h1 : term432 m n) : (term570 m n) = term120.
Proof. exact (EQ_MP (@lem2392016 m n) (@lem2391915 m n h1)). Qed.
Lemma lem2392018 (m : int) (n : int) (h1 : term432 m n) : term573 m n.
Proof. exact (conj (@lem2392017 m n h1) (@lem2391908 m n h1)). Qed.
Lemma lem2392020 (x : real) (y : real) : term574 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2392021 (m : int) (n : int) : term575 m n.
Proof. exact (@lem2392020 (term570 m n) (term396 m n)). Qed.
Lemma lem2392022 (m : int) (n : int) (h1 : term432 m n) : term576 m n.
Proof. exact (@lem2392021 m n (@lem2392018 m n h1)). Qed.
Lemma lem2392023 (m : int) (n : int) : (term577 m n) = (term578 m n).
Proof. exact (@lem1982753 (term366 m n) (term376 m n) (term565 m n) (term579 m n)). Qed.
Lemma lem2392024 (m : int) (n : int) : (term580 m n) = (term581 m n).
Proof. exact (@lem1982715 term183 (term366 m n)). Qed.
Lemma lem2392026 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392027 : term153 = term219.
Proof. exact (@lem2392026 term154). Qed.
Lemma lem2392029 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392030 : term183 = term184.
Proof. exact (@lem2392029 term154). Qed.
Lemma lem2392031 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392032 : term234 = term235.
Proof. exact (MK_COMB (@lem2392031) (@lem2392030)). Qed.
Lemma lem2392033 : term236 = term237.
Proof. exact (MK_COMB (@lem2392032) (@lem2392027)). Qed.
Lemma lem2392034 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2392036 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392037 : term240 = term241.
Proof. exact (@lem2392036 (NUMERAL 0) term154). Qed.
Lemma lem2392038 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392039 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392040 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392039 h1) (fun h1 : term241 = True => @lem2392038)). Qed.
Lemma lem2392041 : term241 = True.
Proof. exact (EQ_MP (@lem2392040) (@lem2392038)). Qed.
Lemma lem2392042 : term240 = True.
Proof. exact (TRANS (@lem2392037) (@lem2392041)). Qed.
Lemma lem2392043 : True = term240.
Proof. exact (SYM (@lem2392042)). Qed.
Lemma lem2392044 : term240.
Proof. exact (EQ_MP (@lem2392043) (@lem0)). Qed.
Lemma lem2392045 : term243.
Proof. exact (@lem2392034 (@lem2392044)). Qed.
Lemma lem2392047 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392048 : term240 = term241.
Proof. exact (@lem2392047 (NUMERAL 0) term154). Qed.
Lemma lem2392049 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392050 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392051 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392050 h1) (fun h1 : term241 = True => @lem2392049)). Qed.
Lemma lem2392052 : term241 = True.
Proof. exact (EQ_MP (@lem2392051) (@lem2392049)). Qed.
Lemma lem2392053 : term240 = True.
Proof. exact (TRANS (@lem2392048) (@lem2392052)). Qed.
Lemma lem2392054 : True = term240.
Proof. exact (SYM (@lem2392053)). Qed.
Lemma lem2392055 : term240.
Proof. exact (EQ_MP (@lem2392054) (@lem0)). Qed.
Lemma lem2392056 : term244.
Proof. exact (@lem2392045 (@lem2392055)). Qed.
Lemma lem2392058 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392059 : term240 = term241.
Proof. exact (@lem2392058 (NUMERAL 0) term154). Qed.
Lemma lem2392060 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392061 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392062 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392061 h1) (fun h1 : term241 = True => @lem2392060)). Qed.
Lemma lem2392063 : term241 = True.
Proof. exact (EQ_MP (@lem2392062) (@lem2392060)). Qed.
Lemma lem2392064 : term240 = True.
Proof. exact (TRANS (@lem2392059) (@lem2392063)). Qed.
Lemma lem2392065 : True = term240.
Proof. exact (SYM (@lem2392064)). Qed.
Lemma lem2392066 : term240.
Proof. exact (EQ_MP (@lem2392065) (@lem0)). Qed.
Lemma lem2392067 : term245.
Proof. exact (@lem2392056 (@lem2392066)). Qed.
Lemma lem2392069 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392070 : term192 = term193.
Proof. exact (@lem2392069 term154 term154). Qed.
Lemma lem2392071 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392072 : term195 = term154.
Proof. exact (EQ_MP (@lem2392071) (@lem940073)). Qed.
Lemma lem2392073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392074 : term193 = term153.
Proof. exact (MK_COMB (@lem2392073) (@lem2392072)). Qed.
Lemma lem2392075 : term192 = term153.
Proof. exact (TRANS (@lem2392070) (@lem2392074)). Qed.
Lemma lem2392077 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2392078 : term220 = term225.
Proof. exact (@lem2392077 term154 term154). Qed.
Lemma lem2392079 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392080 : term195 = term154.
Proof. exact (EQ_MP (@lem2392079) (@lem940073)). Qed.
Lemma lem2392081 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392082 : term193 = term153.
Proof. exact (MK_COMB (@lem2392081) (@lem2392080)). Qed.
Lemma lem2392083 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2392084 : term225 = term183.
Proof. exact (MK_COMB (@lem2392083) (@lem2392082)). Qed.
Lemma lem2392085 : term220 = term183.
Proof. exact (TRANS (@lem2392078) (@lem2392084)). Qed.
Lemma lem2392086 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392087 : term246 = term234.
Proof. exact (MK_COMB (@lem2392086) (@lem2392085)). Qed.
Lemma lem2392088 : term247 = term236.
Proof. exact (MK_COMB (@lem2392087) (@lem2392075)). Qed.
Lemma lem2392090 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2392091 : term236 = term120.
Proof. exact (@lem2392090 term154). Qed.
Lemma lem2392092 : term247 = term120.
Proof. exact (TRANS (@lem2392088) (@lem2392091)). Qed.
Lemma lem2392093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392094 : term249 = term145.
Proof. exact (MK_COMB (@lem2392093) (@lem2392092)). Qed.
Lemma lem2392095 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2392096 : term250 = term251.
Proof. exact (MK_COMB (@lem2392094) (@lem2392095)). Qed.
Lemma lem2392098 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392099 : term251 = term120.
Proof. exact (@lem2392098 term154). Qed.
Lemma lem2392100 : term250 = term120.
Proof. exact (TRANS (@lem2392096) (@lem2392099)). Qed.
Lemma lem2392102 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392103 : term192 = term193.
Proof. exact (@lem2392102 term154 term154). Qed.
Lemma lem2392104 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392105 : term195 = term154.
Proof. exact (EQ_MP (@lem2392104) (@lem940073)). Qed.
Lemma lem2392106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392107 : term193 = term153.
Proof. exact (MK_COMB (@lem2392106) (@lem2392105)). Qed.
Lemma lem2392108 : term192 = term153.
Proof. exact (TRANS (@lem2392103) (@lem2392107)). Qed.
Lemma lem2392109 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2392110 : term253 = term251.
Proof. exact (MK_COMB (@lem2392109) (@lem2392108)). Qed.
Lemma lem2392112 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392113 : term251 = term120.
Proof. exact (@lem2392112 term154). Qed.
Lemma lem2392114 : term253 = term120.
Proof. exact (TRANS (@lem2392110) (@lem2392113)). Qed.
Lemma lem2392115 : term120 = term253.
Proof. exact (SYM (@lem2392114)). Qed.
Lemma lem2392116 : term250 = term253.
Proof. exact (TRANS (@lem2392100) (@lem2392115)). Qed.
Lemma lem2392117 : term237 = term180.
Proof. exact (@lem2392067 (@lem2392116)). Qed.
Lemma lem2392118 : term236 = term180.
Proof. exact (TRANS (@lem2392033) (@lem2392117)). Qed.
Lemma lem2392120 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2392121 : term180 = term120.
Proof. exact (@lem2392120 term120). Qed.
Lemma lem2392122 : term236 = term120.
Proof. exact (TRANS (@lem2392118) (@lem2392121)). Qed.
Lemma lem2392123 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392124 : term254 = term145.
Proof. exact (MK_COMB (@lem2392123) (@lem2392122)). Qed.
Lemma lem2392125 (m : int) (n : int) : (term366 m n) = (term366 m n).
Proof. exact (eq_refl (term366 m n)). Qed.
Lemma lem2392126 (m : int) (n : int) : (term581 m n) = (term582 m n).
Proof. exact (MK_COMB (@lem2392124) (@lem2392125 m n)). Qed.
Lemma lem2392127 (m : int) (n : int) : (term580 m n) = (term582 m n).
Proof. exact (TRANS (@lem2392024 m n) (@lem2392126 m n)). Qed.
Lemma lem2392128 (m : int) (n : int) : (term582 m n) = term120.
Proof. exact (@lem1982719 (term366 m n)). Qed.
Lemma lem2392129 (m : int) (n : int) : (term580 m n) = term120.
Proof. exact (TRANS (@lem2392127 m n) (@lem2392128 m n)). Qed.
Lemma lem2392130 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392131 (m : int) (n : int) : (term583 m n) = term211.
Proof. exact (MK_COMB (@lem2392130) (@lem2392129 m n)). Qed.
Lemma lem2392132 (m : int) (n : int) : (term584 m n) = (term585 m n).
Proof. exact (@lem1982753 (term206 m) (real_of_int m) (term292 m n) (term359 m n)). Qed.
Lemma lem2392133 (m : int) : (term586 m) = (term233 m).
Proof. exact (@lem1982713 term183 (real_of_int m)). Qed.
Lemma lem2392135 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392136 : term153 = term219.
Proof. exact (@lem2392135 term154). Qed.
Lemma lem2392138 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392139 : term183 = term184.
Proof. exact (@lem2392138 term154). Qed.
Lemma lem2392140 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392141 : term234 = term235.
Proof. exact (MK_COMB (@lem2392140) (@lem2392139)). Qed.
Lemma lem2392142 : term236 = term237.
Proof. exact (MK_COMB (@lem2392141) (@lem2392136)). Qed.
Lemma lem2392143 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2392145 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392146 : term240 = term241.
Proof. exact (@lem2392145 (NUMERAL 0) term154). Qed.
Lemma lem2392147 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392148 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392149 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392148 h1) (fun h1 : term241 = True => @lem2392147)). Qed.
Lemma lem2392150 : term241 = True.
Proof. exact (EQ_MP (@lem2392149) (@lem2392147)). Qed.
Lemma lem2392151 : term240 = True.
Proof. exact (TRANS (@lem2392146) (@lem2392150)). Qed.
Lemma lem2392152 : True = term240.
Proof. exact (SYM (@lem2392151)). Qed.
Lemma lem2392153 : term240.
Proof. exact (EQ_MP (@lem2392152) (@lem0)). Qed.
Lemma lem2392154 : term243.
Proof. exact (@lem2392143 (@lem2392153)). Qed.
Lemma lem2392156 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392157 : term240 = term241.
Proof. exact (@lem2392156 (NUMERAL 0) term154). Qed.
Lemma lem2392158 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392159 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392160 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392159 h1) (fun h1 : term241 = True => @lem2392158)). Qed.
Lemma lem2392161 : term241 = True.
Proof. exact (EQ_MP (@lem2392160) (@lem2392158)). Qed.
Lemma lem2392162 : term240 = True.
Proof. exact (TRANS (@lem2392157) (@lem2392161)). Qed.
Lemma lem2392163 : True = term240.
Proof. exact (SYM (@lem2392162)). Qed.
Lemma lem2392164 : term240.
Proof. exact (EQ_MP (@lem2392163) (@lem0)). Qed.
Lemma lem2392165 : term244.
Proof. exact (@lem2392154 (@lem2392164)). Qed.
Lemma lem2392167 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392168 : term240 = term241.
Proof. exact (@lem2392167 (NUMERAL 0) term154). Qed.
Lemma lem2392169 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392170 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392171 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392170 h1) (fun h1 : term241 = True => @lem2392169)). Qed.
Lemma lem2392172 : term241 = True.
Proof. exact (EQ_MP (@lem2392171) (@lem2392169)). Qed.
Lemma lem2392173 : term240 = True.
Proof. exact (TRANS (@lem2392168) (@lem2392172)). Qed.
Lemma lem2392174 : True = term240.
Proof. exact (SYM (@lem2392173)). Qed.
Lemma lem2392175 : term240.
Proof. exact (EQ_MP (@lem2392174) (@lem0)). Qed.
Lemma lem2392176 : term245.
Proof. exact (@lem2392165 (@lem2392175)). Qed.
Lemma lem2392178 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392179 : term192 = term193.
Proof. exact (@lem2392178 term154 term154). Qed.
Lemma lem2392180 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392181 : term195 = term154.
Proof. exact (EQ_MP (@lem2392180) (@lem940073)). Qed.
Lemma lem2392182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392183 : term193 = term153.
Proof. exact (MK_COMB (@lem2392182) (@lem2392181)). Qed.
Lemma lem2392184 : term192 = term153.
Proof. exact (TRANS (@lem2392179) (@lem2392183)). Qed.
Lemma lem2392186 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2392187 : term220 = term225.
Proof. exact (@lem2392186 term154 term154). Qed.
Lemma lem2392188 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392189 : term195 = term154.
Proof. exact (EQ_MP (@lem2392188) (@lem940073)). Qed.
Lemma lem2392190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392191 : term193 = term153.
Proof. exact (MK_COMB (@lem2392190) (@lem2392189)). Qed.
Lemma lem2392192 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2392193 : term225 = term183.
Proof. exact (MK_COMB (@lem2392192) (@lem2392191)). Qed.
Lemma lem2392194 : term220 = term183.
Proof. exact (TRANS (@lem2392187) (@lem2392193)). Qed.
Lemma lem2392195 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392196 : term246 = term234.
Proof. exact (MK_COMB (@lem2392195) (@lem2392194)). Qed.
Lemma lem2392197 : term247 = term236.
Proof. exact (MK_COMB (@lem2392196) (@lem2392184)). Qed.
Lemma lem2392199 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2392200 : term236 = term120.
Proof. exact (@lem2392199 term154). Qed.
Lemma lem2392201 : term247 = term120.
Proof. exact (TRANS (@lem2392197) (@lem2392200)). Qed.
Lemma lem2392202 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392203 : term249 = term145.
Proof. exact (MK_COMB (@lem2392202) (@lem2392201)). Qed.
Lemma lem2392204 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2392205 : term250 = term251.
Proof. exact (MK_COMB (@lem2392203) (@lem2392204)). Qed.
Lemma lem2392207 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392208 : term251 = term120.
Proof. exact (@lem2392207 term154). Qed.
Lemma lem2392209 : term250 = term120.
Proof. exact (TRANS (@lem2392205) (@lem2392208)). Qed.
Lemma lem2392211 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392212 : term192 = term193.
Proof. exact (@lem2392211 term154 term154). Qed.
Lemma lem2392213 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392214 : term195 = term154.
Proof. exact (EQ_MP (@lem2392213) (@lem940073)). Qed.
Lemma lem2392215 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392216 : term193 = term153.
Proof. exact (MK_COMB (@lem2392215) (@lem2392214)). Qed.
Lemma lem2392217 : term192 = term153.
Proof. exact (TRANS (@lem2392212) (@lem2392216)). Qed.
Lemma lem2392218 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2392219 : term253 = term251.
Proof. exact (MK_COMB (@lem2392218) (@lem2392217)). Qed.
Lemma lem2392221 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392222 : term251 = term120.
Proof. exact (@lem2392221 term154). Qed.
Lemma lem2392223 : term253 = term120.
Proof. exact (TRANS (@lem2392219) (@lem2392222)). Qed.
Lemma lem2392224 : term120 = term253.
Proof. exact (SYM (@lem2392223)). Qed.
Lemma lem2392225 : term250 = term253.
Proof. exact (TRANS (@lem2392209) (@lem2392224)). Qed.
Lemma lem2392226 : term237 = term180.
Proof. exact (@lem2392176 (@lem2392225)). Qed.
Lemma lem2392227 : term236 = term180.
Proof. exact (TRANS (@lem2392142) (@lem2392226)). Qed.
Lemma lem2392229 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2392230 : term180 = term120.
Proof. exact (@lem2392229 term120). Qed.
Lemma lem2392231 : term236 = term120.
Proof. exact (TRANS (@lem2392227) (@lem2392230)). Qed.
Lemma lem2392232 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392233 : term254 = term145.
Proof. exact (MK_COMB (@lem2392232) (@lem2392231)). Qed.
Lemma lem2392234 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2392235 (m : int) : (term233 m) = (term255 m).
Proof. exact (MK_COMB (@lem2392233) (@lem2392234 m)). Qed.
Lemma lem2392236 (m : int) : (term586 m) = (term255 m).
Proof. exact (TRANS (@lem2392133 m) (@lem2392235 m)). Qed.
Lemma lem2392237 (m : int) : (term255 m) = term120.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2392238 (m : int) : (term586 m) = term120.
Proof. exact (TRANS (@lem2392236 m) (@lem2392237 m)). Qed.
Lemma lem2392239 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392240 (m : int) : (term587 m) = term211.
Proof. exact (MK_COMB (@lem2392239) (@lem2392238 m)). Qed.
Lemma lem2392241 (m : int) (n : int) : (term588 m n) = (term589 m n).
Proof. exact (@lem1982763 (term292 m n) (term377 m n) term183). Qed.
Lemma lem2392242 (m : int) (n : int) : (term590 m n) = (term591 m n).
Proof. exact (@lem1982715 term183 (term292 m n)). Qed.
Lemma lem2392244 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392245 : term153 = term219.
Proof. exact (@lem2392244 term154). Qed.
Lemma lem2392247 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392248 : term183 = term184.
Proof. exact (@lem2392247 term154). Qed.
Lemma lem2392249 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392250 : term234 = term235.
Proof. exact (MK_COMB (@lem2392249) (@lem2392248)). Qed.
Lemma lem2392251 : term236 = term237.
Proof. exact (MK_COMB (@lem2392250) (@lem2392245)). Qed.
Lemma lem2392252 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2392254 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392255 : term240 = term241.
Proof. exact (@lem2392254 (NUMERAL 0) term154). Qed.
Lemma lem2392256 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392257 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392258 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392257 h1) (fun h1 : term241 = True => @lem2392256)). Qed.
Lemma lem2392259 : term241 = True.
Proof. exact (EQ_MP (@lem2392258) (@lem2392256)). Qed.
Lemma lem2392260 : term240 = True.
Proof. exact (TRANS (@lem2392255) (@lem2392259)). Qed.
Lemma lem2392261 : True = term240.
Proof. exact (SYM (@lem2392260)). Qed.
Lemma lem2392262 : term240.
Proof. exact (EQ_MP (@lem2392261) (@lem0)). Qed.
Lemma lem2392263 : term243.
Proof. exact (@lem2392252 (@lem2392262)). Qed.
Lemma lem2392265 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392266 : term240 = term241.
Proof. exact (@lem2392265 (NUMERAL 0) term154). Qed.
Lemma lem2392267 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392268 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392269 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392268 h1) (fun h1 : term241 = True => @lem2392267)). Qed.
Lemma lem2392270 : term241 = True.
Proof. exact (EQ_MP (@lem2392269) (@lem2392267)). Qed.
Lemma lem2392271 : term240 = True.
Proof. exact (TRANS (@lem2392266) (@lem2392270)). Qed.
Lemma lem2392272 : True = term240.
Proof. exact (SYM (@lem2392271)). Qed.
Lemma lem2392273 : term240.
Proof. exact (EQ_MP (@lem2392272) (@lem0)). Qed.
Lemma lem2392274 : term244.
Proof. exact (@lem2392263 (@lem2392273)). Qed.
Lemma lem2392276 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392277 : term240 = term241.
Proof. exact (@lem2392276 (NUMERAL 0) term154). Qed.
Lemma lem2392278 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392279 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392280 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392279 h1) (fun h1 : term241 = True => @lem2392278)). Qed.
Lemma lem2392281 : term241 = True.
Proof. exact (EQ_MP (@lem2392280) (@lem2392278)). Qed.
Lemma lem2392282 : term240 = True.
Proof. exact (TRANS (@lem2392277) (@lem2392281)). Qed.
Lemma lem2392283 : True = term240.
Proof. exact (SYM (@lem2392282)). Qed.
Lemma lem2392284 : term240.
Proof. exact (EQ_MP (@lem2392283) (@lem0)). Qed.
Lemma lem2392285 : term245.
Proof. exact (@lem2392274 (@lem2392284)). Qed.
Lemma lem2392287 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392288 : term192 = term193.
Proof. exact (@lem2392287 term154 term154). Qed.
Lemma lem2392289 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392290 : term195 = term154.
Proof. exact (EQ_MP (@lem2392289) (@lem940073)). Qed.
Lemma lem2392291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392292 : term193 = term153.
Proof. exact (MK_COMB (@lem2392291) (@lem2392290)). Qed.
Lemma lem2392293 : term192 = term153.
Proof. exact (TRANS (@lem2392288) (@lem2392292)). Qed.
Lemma lem2392295 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2392296 : term220 = term225.
Proof. exact (@lem2392295 term154 term154). Qed.
Lemma lem2392297 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392298 : term195 = term154.
Proof. exact (EQ_MP (@lem2392297) (@lem940073)). Qed.
Lemma lem2392299 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392300 : term193 = term153.
Proof. exact (MK_COMB (@lem2392299) (@lem2392298)). Qed.
Lemma lem2392301 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2392302 : term225 = term183.
Proof. exact (MK_COMB (@lem2392301) (@lem2392300)). Qed.
Lemma lem2392303 : term220 = term183.
Proof. exact (TRANS (@lem2392296) (@lem2392302)). Qed.
Lemma lem2392304 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392305 : term246 = term234.
Proof. exact (MK_COMB (@lem2392304) (@lem2392303)). Qed.
Lemma lem2392306 : term247 = term236.
Proof. exact (MK_COMB (@lem2392305) (@lem2392293)). Qed.
Lemma lem2392308 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2392309 : term236 = term120.
Proof. exact (@lem2392308 term154). Qed.
Lemma lem2392310 : term247 = term120.
Proof. exact (TRANS (@lem2392306) (@lem2392309)). Qed.
Lemma lem2392311 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392312 : term249 = term145.
Proof. exact (MK_COMB (@lem2392311) (@lem2392310)). Qed.
Lemma lem2392313 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2392314 : term250 = term251.
Proof. exact (MK_COMB (@lem2392312) (@lem2392313)). Qed.
Lemma lem2392316 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392317 : term251 = term120.
Proof. exact (@lem2392316 term154). Qed.
Lemma lem2392318 : term250 = term120.
Proof. exact (TRANS (@lem2392314) (@lem2392317)). Qed.
Lemma lem2392320 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392321 : term192 = term193.
Proof. exact (@lem2392320 term154 term154). Qed.
Lemma lem2392322 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392323 : term195 = term154.
Proof. exact (EQ_MP (@lem2392322) (@lem940073)). Qed.
Lemma lem2392324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392325 : term193 = term153.
Proof. exact (MK_COMB (@lem2392324) (@lem2392323)). Qed.
Lemma lem2392326 : term192 = term153.
Proof. exact (TRANS (@lem2392321) (@lem2392325)). Qed.
Lemma lem2392327 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2392328 : term253 = term251.
Proof. exact (MK_COMB (@lem2392327) (@lem2392326)). Qed.
Lemma lem2392330 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392331 : term251 = term120.
Proof. exact (@lem2392330 term154). Qed.
Lemma lem2392332 : term253 = term120.
Proof. exact (TRANS (@lem2392328) (@lem2392331)). Qed.
Lemma lem2392333 : term120 = term253.
Proof. exact (SYM (@lem2392332)). Qed.
Lemma lem2392334 : term250 = term253.
Proof. exact (TRANS (@lem2392318) (@lem2392333)). Qed.
Lemma lem2392335 : term237 = term180.
Proof. exact (@lem2392285 (@lem2392334)). Qed.
Lemma lem2392336 : term236 = term180.
Proof. exact (TRANS (@lem2392251) (@lem2392335)). Qed.
Lemma lem2392338 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2392339 : term180 = term120.
Proof. exact (@lem2392338 term120). Qed.
Lemma lem2392340 : term236 = term120.
Proof. exact (TRANS (@lem2392336) (@lem2392339)). Qed.
Lemma lem2392341 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392342 : term254 = term145.
Proof. exact (MK_COMB (@lem2392341) (@lem2392340)). Qed.
Lemma lem2392343 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2392344 (m : int) (n : int) : (term591 m n) = (term592 m n).
Proof. exact (MK_COMB (@lem2392342) (@lem2392343 m n)). Qed.
Lemma lem2392345 (m : int) (n : int) : (term590 m n) = (term592 m n).
Proof. exact (TRANS (@lem2392242 m n) (@lem2392344 m n)). Qed.
Lemma lem2392346 (m : int) (n : int) : (term592 m n) = term120.
Proof. exact (@lem1982719 (term292 m n)). Qed.
Lemma lem2392347 (m : int) (n : int) : (term590 m n) = term120.
Proof. exact (TRANS (@lem2392345 m n) (@lem2392346 m n)). Qed.
Lemma lem2392348 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392349 (m : int) (n : int) : (term593 m n) = term211.
Proof. exact (MK_COMB (@lem2392348) (@lem2392347 m n)). Qed.
Lemma lem2392350 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2392351 (m : int) (n : int) : (term589 m n) = term257.
Proof. exact (MK_COMB (@lem2392349 m n) (@lem2392350)). Qed.
Lemma lem2392352 (m : int) (n : int) : (term588 m n) = term257.
Proof. exact (TRANS (@lem2392241 m n) (@lem2392351 m n)). Qed.
Lemma lem2392353 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2392354 (m : int) (n : int) : (term588 m n) = term183.
Proof. exact (TRANS (@lem2392352 m n) (@lem2392353)). Qed.
Lemma lem2392355 (m : int) (n : int) : (term585 m n) = term257.
Proof. exact (MK_COMB (@lem2392240 m) (@lem2392354 m n)). Qed.
Lemma lem2392356 (m : int) (n : int) : (term584 m n) = term257.
Proof. exact (TRANS (@lem2392132 m n) (@lem2392355 m n)). Qed.
Lemma lem2392357 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2392358 (m : int) (n : int) : (term584 m n) = term183.
Proof. exact (TRANS (@lem2392356 m n) (@lem2392357)). Qed.
Lemma lem2392359 (m : int) (n : int) : (term578 m n) = term257.
Proof. exact (MK_COMB (@lem2392131 m n) (@lem2392358 m n)). Qed.
Lemma lem2392360 (m : int) (n : int) : (term577 m n) = term257.
Proof. exact (TRANS (@lem2392023 m n) (@lem2392359 m n)). Qed.
Lemma lem2392361 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2392362 (m : int) (n : int) : (term577 m n) = term183.
Proof. exact (TRANS (@lem2392360 m n) (@lem2392361)). Qed.
Lemma lem2392363 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2392364 (m : int) (n : int) : (term594 m n) = term259.
Proof. exact (MK_COMB (@lem2392363) (@lem2392362 m n)). Qed.
Lemma lem2392365 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2392366 (m : int) (n : int) : (term576 m n) = term260.
Proof. exact (MK_COMB (@lem2392364 m n) (@lem2392365)). Qed.
Lemma lem2392367 (m : int) (n : int) (h1 : term432 m n) : term260.
Proof. exact (EQ_MP (@lem2392366 m n) (@lem2392022 m n h1)). Qed.
Lemma lem2392369 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2392370 : term260 = term271.
Proof. exact (@lem2392369 term120 term183). Qed.
Lemma lem2392372 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392373 : term183 = term184.
Proof. exact (@lem2392372 term154). Qed.
Lemma lem2392375 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392376 : term120 = term180.
Proof. exact (@lem2392375 (NUMERAL 0)). Qed.
Lemma lem2392377 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2392378 : term272 = term273.
Proof. exact (MK_COMB (@lem2392377) (@lem2392376)). Qed.
Lemma lem2392379 : term271 = term274.
Proof. exact (MK_COMB (@lem2392378) (@lem2392373)). Qed.
Lemma lem2392380 : term275.
Proof. exact (@lem1980026 term120 term153 term183 term153). Qed.
Lemma lem2392382 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392383 : term240 = term241.
Proof. exact (@lem2392382 (NUMERAL 0) term154). Qed.
Lemma lem2392384 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392385 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392386 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392385 h1) (fun h1 : term241 = True => @lem2392384)). Qed.
Lemma lem2392387 : term241 = True.
Proof. exact (EQ_MP (@lem2392386) (@lem2392384)). Qed.
Lemma lem2392388 : term240 = True.
Proof. exact (TRANS (@lem2392383) (@lem2392387)). Qed.
Lemma lem2392389 : True = term240.
Proof. exact (SYM (@lem2392388)). Qed.
Lemma lem2392390 : term240.
Proof. exact (EQ_MP (@lem2392389) (@lem0)). Qed.
Lemma lem2392391 : term276.
Proof. exact (@lem2392380 (@lem2392390)). Qed.
Lemma lem2392393 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392394 : term240 = term241.
Proof. exact (@lem2392393 (NUMERAL 0) term154). Qed.
Lemma lem2392395 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392396 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392397 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392396 h1) (fun h1 : term241 = True => @lem2392395)). Qed.
Lemma lem2392398 : term241 = True.
Proof. exact (EQ_MP (@lem2392397) (@lem2392395)). Qed.
Lemma lem2392399 : term240 = True.
Proof. exact (TRANS (@lem2392394) (@lem2392398)). Qed.
Lemma lem2392400 : True = term240.
Proof. exact (SYM (@lem2392399)). Qed.
Lemma lem2392401 : term240.
Proof. exact (EQ_MP (@lem2392400) (@lem0)). Qed.
Lemma lem2392402 : term274 = term277.
Proof. exact (@lem2392391 (@lem2392401)). Qed.
Lemma lem2392404 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2392405 : term220 = term225.
Proof. exact (@lem2392404 term154 term154). Qed.
Lemma lem2392406 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392407 : term195 = term154.
Proof. exact (EQ_MP (@lem2392406) (@lem940073)). Qed.
Lemma lem2392408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392409 : term193 = term153.
Proof. exact (MK_COMB (@lem2392408) (@lem2392407)). Qed.
Lemma lem2392410 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2392411 : term225 = term183.
Proof. exact (MK_COMB (@lem2392410) (@lem2392409)). Qed.
Lemma lem2392412 : term220 = term183.
Proof. exact (TRANS (@lem2392405) (@lem2392411)). Qed.
Lemma lem2392414 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392415 : term251 = term120.
Proof. exact (@lem2392414 term154). Qed.
Lemma lem2392416 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2392417 : term278 = term272.
Proof. exact (MK_COMB (@lem2392416) (@lem2392415)). Qed.
Lemma lem2392418 : term277 = term271.
Proof. exact (MK_COMB (@lem2392417) (@lem2392412)). Qed.
Lemma lem2392420 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2392421 : term271 = term281.
Proof. exact (@lem2392420 (NUMERAL 0) term154). Qed.
Lemma lem2392422 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392423 (h1 : term242 = (BIT1 0)) : (term154 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2392424 : (term242 = (BIT1 0)) = ((term154 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392423 h1) (fun h1 : (term154 = (NUMERAL 0)) = False => @lem2392422)). Qed.
Lemma lem2392425 : (term154 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2392424) (@lem2392422)). Qed.
Lemma lem2392426 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2392427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2392428 : term282 = (and True).
Proof. exact (MK_COMB (@lem2392427) (@lem2392426)). Qed.
Lemma lem2392429 : term281 = (True /\ False).
Proof. exact (MK_COMB (@lem2392428) (@lem2392425)). Qed.
Lemma lem2392431 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2392432 : term281 = False.
Proof. exact (TRANS (@lem2392429) (@lem2392431)). Qed.
Lemma lem2392433 : term271 = False.
Proof. exact (TRANS (@lem2392421) (@lem2392432)). Qed.
Lemma lem2392434 : term277 = False.
Proof. exact (TRANS (@lem2392418) (@lem2392433)). Qed.
Lemma lem2392435 : term274 = False.
Proof. exact (TRANS (@lem2392402) (@lem2392434)). Qed.
Lemma lem2392436 : term271 = False.
Proof. exact (TRANS (@lem2392379) (@lem2392435)). Qed.
Lemma lem2392437 : term260 = False.
Proof. exact (TRANS (@lem2392370) (@lem2392436)). Qed.
Lemma lem2392438 (m : int) (n : int) (h1 : term432 m n) : False.
Proof. exact (EQ_MP (@lem2392437) (@lem2392367 m n h1)). Qed.
Lemma lem2392439 (m : int) (n : int) (h1 : term501 m n) : term501 m n.
Proof. exact (h1). Qed.
Lemma lem2392440 (m : int) (n : int) (h1 : term501 m n) : term499 m n.
Proof. exact (proj2 (@lem2392439 m n h1)). Qed.
Lemma lem2392442 (m : int) (n : int) (h1 : term501 m n) : term399 m n.
Proof. exact (proj2 (@lem2392440 m n h1)). Qed.
Lemma lem2392443 (m : int) (n : int) (h1 : term501 m n) : term496 m n.
Proof. exact (proj1 (@lem2392440 m n h1)). Qed.
Lemma lem2392444 (m : int) (n : int) (h1 : term501 m n) : term494 m n.
Proof. exact (proj2 (@lem2392443 m n h1)). Qed.
Lemma lem2392446 (m : int) (n : int) (h1 : term501 m n) : (term375 m n) = term120.
Proof. exact (proj2 (@lem2392444 m n h1)). Qed.
Lemma lem2392449 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2392450 : term531 = term240.
Proof. exact (@lem2392449 term120 term153). Qed.
Lemma lem2392452 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392453 : term153 = term219.
Proof. exact (@lem2392452 term154). Qed.
Lemma lem2392455 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392456 : term120 = term180.
Proof. exact (@lem2392455 (NUMERAL 0)). Qed.
Lemma lem2392457 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2392458 : term532 = term533.
Proof. exact (MK_COMB (@lem2392457) (@lem2392456)). Qed.
Lemma lem2392459 : term240 = term534.
Proof. exact (MK_COMB (@lem2392458) (@lem2392453)). Qed.
Lemma lem2392460 : term535.
Proof. exact (@lem1980255 term120 term153 term153 term153). Qed.
Lemma lem2392462 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392463 : term240 = term241.
Proof. exact (@lem2392462 (NUMERAL 0) term154). Qed.
Lemma lem2392464 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392465 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392466 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392465 h1) (fun h1 : term241 = True => @lem2392464)). Qed.
Lemma lem2392467 : term241 = True.
Proof. exact (EQ_MP (@lem2392466) (@lem2392464)). Qed.
Lemma lem2392468 : term240 = True.
Proof. exact (TRANS (@lem2392463) (@lem2392467)). Qed.
Lemma lem2392469 : True = term240.
Proof. exact (SYM (@lem2392468)). Qed.
Lemma lem2392470 : term240.
Proof. exact (EQ_MP (@lem2392469) (@lem0)). Qed.
Lemma lem2392471 : term536.
Proof. exact (@lem2392460 (@lem2392470)). Qed.
Lemma lem2392473 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392474 : term240 = term241.
Proof. exact (@lem2392473 (NUMERAL 0) term154). Qed.
Lemma lem2392475 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392476 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392477 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392476 h1) (fun h1 : term241 = True => @lem2392475)). Qed.
Lemma lem2392478 : term241 = True.
Proof. exact (EQ_MP (@lem2392477) (@lem2392475)). Qed.
Lemma lem2392479 : term240 = True.
Proof. exact (TRANS (@lem2392474) (@lem2392478)). Qed.
Lemma lem2392480 : True = term240.
Proof. exact (SYM (@lem2392479)). Qed.
Lemma lem2392481 : term240.
Proof. exact (EQ_MP (@lem2392480) (@lem0)). Qed.
Lemma lem2392482 : term534 = term537.
Proof. exact (@lem2392471 (@lem2392481)). Qed.
Lemma lem2392484 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392485 : term192 = term193.
Proof. exact (@lem2392484 term154 term154). Qed.
Lemma lem2392486 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392487 : term195 = term154.
Proof. exact (EQ_MP (@lem2392486) (@lem940073)). Qed.
Lemma lem2392488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392489 : term193 = term153.
Proof. exact (MK_COMB (@lem2392488) (@lem2392487)). Qed.
Lemma lem2392490 : term192 = term153.
Proof. exact (TRANS (@lem2392485) (@lem2392489)). Qed.
Lemma lem2392492 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392493 : term251 = term120.
Proof. exact (@lem2392492 term154). Qed.
Lemma lem2392494 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2392495 : term538 = term532.
Proof. exact (MK_COMB (@lem2392494) (@lem2392493)). Qed.
Lemma lem2392496 : term537 = term240.
Proof. exact (MK_COMB (@lem2392495) (@lem2392490)). Qed.
Lemma lem2392498 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392499 : term240 = term241.
Proof. exact (@lem2392498 (NUMERAL 0) term154). Qed.
Lemma lem2392500 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392501 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392502 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392501 h1) (fun h1 : term241 = True => @lem2392500)). Qed.
Lemma lem2392503 : term241 = True.
Proof. exact (EQ_MP (@lem2392502) (@lem2392500)). Qed.
Lemma lem2392504 : term240 = True.
Proof. exact (TRANS (@lem2392499) (@lem2392503)). Qed.
Lemma lem2392505 : term537 = True.
Proof. exact (TRANS (@lem2392496) (@lem2392504)). Qed.
Lemma lem2392506 : term534 = True.
Proof. exact (TRANS (@lem2392482) (@lem2392505)). Qed.
Lemma lem2392507 : term240 = True.
Proof. exact (TRANS (@lem2392459) (@lem2392506)). Qed.
Lemma lem2392508 : term531 = True.
Proof. exact (TRANS (@lem2392450) (@lem2392507)). Qed.
Lemma lem2392509 : True = term531.
Proof. exact (SYM (@lem2392508)). Qed.
Lemma lem2392510 : term531.
Proof. exact (EQ_MP (@lem2392509) (@lem0)). Qed.
Lemma lem2392511 (m : int) (n : int) (h1 : term501 m n) : term539 m n.
Proof. exact (conj (@lem2392510) (@lem2392442 m n h1)). Qed.
Lemma lem2392513 (x : real) (y : real) : term540 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2392514 (m : int) (n : int) : term541 m n.
Proof. exact (@lem2392513 term153 (term396 m n)). Qed.
Lemma lem2392515 (m : int) (n : int) (h1 : term501 m n) : term542 m n.
Proof. exact (@lem2392514 m n (@lem2392511 m n h1)). Qed.
Lemma lem2392516 (m : int) (n : int) : (term543 m n) = (term396 m n).
Proof. exact (@lem1982733 (term396 m n)). Qed.
Lemma lem2392517 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2392518 (m : int) (n : int) : (term544 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem2392517) (@lem2392516 m n)). Qed.
Lemma lem2392519 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2392520 (m : int) (n : int) : (term542 m n) = (term399 m n).
Proof. exact (MK_COMB (@lem2392518 m n) (@lem2392519)). Qed.
Lemma lem2392521 (m : int) (n : int) (h1 : term501 m n) : term399 m n.
Proof. exact (EQ_MP (@lem2392520 m n) (@lem2392515 m n h1)). Qed.
Lemma lem2392523 (y : real) : term545 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2392524 (m : int) (n : int) : term546 m n.
Proof. exact (@lem2392523 (term375 m n)). Qed.
Lemma lem2392525 (m : int) (n : int) (h1 : term501 m n) : term547 m n.
Proof. exact (@lem2392524 m n (@lem2392446 m n h1)). Qed.
Lemma lem2392526 (m : int) (n : int) (h1 : term501 m n) : term548 m n.
Proof. exact (@lem2392525 m n h1 term183). Qed.
Lemma lem2392527 (m : int) (n : int) : (term548 m n) = ((term549 m n) = term120).
Proof. exact (eq_refl (term548 m n)). Qed.
Lemma lem2392528 (m : int) (n : int) (h1 : term501 m n) : (term549 m n) = term120.
Proof. exact (EQ_MP (@lem2392527 m n) (@lem2392526 m n h1)). Qed.
Lemma lem2392529 (m : int) (n : int) : (term549 m n) = (term550 m n).
Proof. exact (@lem1982781 (term376 m n) term183 (term551 m n)). Qed.
Lemma lem2392530 (m : int) (n : int) : (term552 m n) = (term553 m n).
Proof. exact (@lem1982781 (real_of_int m) term183 (term377 m n)). Qed.
Lemma lem2392531 (m : int) (n : int) : (term554 m n) = (term555 m n).
Proof. exact (@lem1982749 term183 term183 (term292 m n)). Qed.
Lemma lem2392533 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392534 : term183 = term184.
Proof. exact (@lem2392533 term154). Qed.
Lemma lem2392536 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392537 : term183 = term184.
Proof. exact (@lem2392536 term154). Qed.
Lemma lem2392538 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392539 : term185 = term186.
Proof. exact (MK_COMB (@lem2392538) (@lem2392537)). Qed.
Lemma lem2392540 : term556 = term557.
Proof. exact (MK_COMB (@lem2392539) (@lem2392534)). Qed.
Lemma lem2392541 : term557 = term558.
Proof. exact (@lem1981613 term183 term183 term153 term153). Qed.
Lemma lem2392543 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392544 : term192 = term193.
Proof. exact (@lem2392543 term154 term154). Qed.
Lemma lem2392545 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392546 : term195 = term154.
Proof. exact (EQ_MP (@lem2392545) (@lem940073)). Qed.
Lemma lem2392547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392548 : term193 = term153.
Proof. exact (MK_COMB (@lem2392547) (@lem2392546)). Qed.
Lemma lem2392549 : term192 = term153.
Proof. exact (TRANS (@lem2392544) (@lem2392548)). Qed.
Lemma lem2392551 (m : nat) (n : nat) : (term559 m n) = (term191 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2392552 : term556 = term193.
Proof. exact (@lem2392551 term154 term154). Qed.
Lemma lem2392553 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392554 : term195 = term154.
Proof. exact (EQ_MP (@lem2392553) (@lem940073)). Qed.
Lemma lem2392555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392556 : term193 = term153.
Proof. exact (MK_COMB (@lem2392555) (@lem2392554)). Qed.
Lemma lem2392557 : term556 = term153.
Proof. exact (TRANS (@lem2392552) (@lem2392556)). Qed.
Lemma lem2392558 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2392559 : term560 = term561.
Proof. exact (MK_COMB (@lem2392558) (@lem2392557)). Qed.
Lemma lem2392560 : term558 = term219.
Proof. exact (MK_COMB (@lem2392559) (@lem2392549)). Qed.
Lemma lem2392561 : term557 = term219.
Proof. exact (TRANS (@lem2392541) (@lem2392560)). Qed.
Lemma lem2392562 : term556 = term219.
Proof. exact (TRANS (@lem2392540) (@lem2392561)). Qed.
Lemma lem2392564 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2392565 : term219 = term153.
Proof. exact (@lem2392564 term153). Qed.
Lemma lem2392566 : term556 = term153.
Proof. exact (TRANS (@lem2392562) (@lem2392565)). Qed.
Lemma lem2392567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392568 : term562 = term563.
Proof. exact (MK_COMB (@lem2392567) (@lem2392566)). Qed.
Lemma lem2392569 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2392570 (m : int) (n : int) : (term555 m n) = (term564 m n).
Proof. exact (MK_COMB (@lem2392568) (@lem2392569 m n)). Qed.
Lemma lem2392571 (m : int) (n : int) : (term554 m n) = (term564 m n).
Proof. exact (TRANS (@lem2392531 m n) (@lem2392570 m n)). Qed.
Lemma lem2392572 (m : int) (n : int) : (term564 m n) = (term292 m n).
Proof. exact (@lem1982709 (term292 m n)). Qed.
Lemma lem2392573 (m : int) (n : int) : (term554 m n) = (term292 m n).
Proof. exact (TRANS (@lem2392571 m n) (@lem2392572 m n)). Qed.
Lemma lem2392576 (m : int) : (term228 m) = (term228 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem2392577 (m : int) (n : int) : (term553 m n) = (term565 m n).
Proof. exact (MK_COMB (@lem2392576 m) (@lem2392573 m n)). Qed.
Lemma lem2392578 (m : int) (n : int) : (term552 m n) = (term565 m n).
Proof. exact (TRANS (@lem2392530 m n) (@lem2392577 m n)). Qed.
Lemma lem2392579 (m : int) (n : int) : (term566 m n) = (term567 m n).
Proof. exact (@lem1982749 term183 term183 (term366 m n)). Qed.
Lemma lem2392581 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392582 : term183 = term184.
Proof. exact (@lem2392581 term154). Qed.
Lemma lem2392584 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392585 : term183 = term184.
Proof. exact (@lem2392584 term154). Qed.
Lemma lem2392586 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392587 : term185 = term186.
Proof. exact (MK_COMB (@lem2392586) (@lem2392585)). Qed.
Lemma lem2392588 : term556 = term557.
Proof. exact (MK_COMB (@lem2392587) (@lem2392582)). Qed.
Lemma lem2392589 : term557 = term558.
Proof. exact (@lem1981613 term183 term183 term153 term153). Qed.
Lemma lem2392591 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392592 : term192 = term193.
Proof. exact (@lem2392591 term154 term154). Qed.
Lemma lem2392593 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392594 : term195 = term154.
Proof. exact (EQ_MP (@lem2392593) (@lem940073)). Qed.
Lemma lem2392595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392596 : term193 = term153.
Proof. exact (MK_COMB (@lem2392595) (@lem2392594)). Qed.
Lemma lem2392597 : term192 = term153.
Proof. exact (TRANS (@lem2392592) (@lem2392596)). Qed.
Lemma lem2392599 (m : nat) (n : nat) : (term559 m n) = (term191 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2392600 : term556 = term193.
Proof. exact (@lem2392599 term154 term154). Qed.
Lemma lem2392601 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392602 : term195 = term154.
Proof. exact (EQ_MP (@lem2392601) (@lem940073)). Qed.
Lemma lem2392603 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392604 : term193 = term153.
Proof. exact (MK_COMB (@lem2392603) (@lem2392602)). Qed.
Lemma lem2392605 : term556 = term153.
Proof. exact (TRANS (@lem2392600) (@lem2392604)). Qed.
Lemma lem2392606 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2392607 : term560 = term561.
Proof. exact (MK_COMB (@lem2392606) (@lem2392605)). Qed.
Lemma lem2392608 : term558 = term219.
Proof. exact (MK_COMB (@lem2392607) (@lem2392597)). Qed.
Lemma lem2392609 : term557 = term219.
Proof. exact (TRANS (@lem2392589) (@lem2392608)). Qed.
Lemma lem2392610 : term556 = term219.
Proof. exact (TRANS (@lem2392588) (@lem2392609)). Qed.
Lemma lem2392612 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2392613 : term219 = term153.
Proof. exact (@lem2392612 term153). Qed.
Lemma lem2392614 : term556 = term153.
Proof. exact (TRANS (@lem2392610) (@lem2392613)). Qed.
Lemma lem2392615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392616 : term562 = term563.
Proof. exact (MK_COMB (@lem2392615) (@lem2392614)). Qed.
Lemma lem2392617 (m : int) (n : int) : (term366 m n) = (term366 m n).
Proof. exact (eq_refl (term366 m n)). Qed.
Lemma lem2392618 (m : int) (n : int) : (term567 m n) = (term568 m n).
Proof. exact (MK_COMB (@lem2392616) (@lem2392617 m n)). Qed.
Lemma lem2392619 (m : int) (n : int) : (term566 m n) = (term568 m n).
Proof. exact (TRANS (@lem2392579 m n) (@lem2392618 m n)). Qed.
Lemma lem2392620 (m : int) (n : int) : (term568 m n) = (term366 m n).
Proof. exact (@lem1982709 (term366 m n)). Qed.
Lemma lem2392621 (m : int) (n : int) : (term566 m n) = (term366 m n).
Proof. exact (TRANS (@lem2392619 m n) (@lem2392620 m n)). Qed.
Lemma lem2392622 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392623 (m : int) (n : int) : (term569 m n) = (term368 m n).
Proof. exact (MK_COMB (@lem2392622) (@lem2392621 m n)). Qed.
Lemma lem2392624 (m : int) (n : int) : (term550 m n) = (term570 m n).
Proof. exact (MK_COMB (@lem2392623 m n) (@lem2392578 m n)). Qed.
Lemma lem2392625 (m : int) (n : int) : (term549 m n) = (term570 m n).
Proof. exact (TRANS (@lem2392529 m n) (@lem2392624 m n)). Qed.
Lemma lem2392626 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2392627 (m : int) (n : int) : (term571 m n) = (term572 m n).
Proof. exact (MK_COMB (@lem2392626) (@lem2392625 m n)). Qed.
Lemma lem2392628 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2392629 (m : int) (n : int) : ((term549 m n) = term120) = ((term570 m n) = term120).
Proof. exact (MK_COMB (@lem2392627 m n) (@lem2392628)). Qed.
Lemma lem2392630 (m : int) (n : int) (h1 : term501 m n) : (term570 m n) = term120.
Proof. exact (EQ_MP (@lem2392629 m n) (@lem2392528 m n h1)). Qed.
Lemma lem2392631 (m : int) (n : int) (h1 : term501 m n) : term573 m n.
Proof. exact (conj (@lem2392630 m n h1) (@lem2392521 m n h1)). Qed.
Lemma lem2392633 (x : real) (y : real) : term574 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2392634 (m : int) (n : int) : term575 m n.
Proof. exact (@lem2392633 (term570 m n) (term396 m n)). Qed.
Lemma lem2392635 (m : int) (n : int) (h1 : term501 m n) : term576 m n.
Proof. exact (@lem2392634 m n (@lem2392631 m n h1)). Qed.
Lemma lem2392636 (m : int) (n : int) : (term577 m n) = (term578 m n).
Proof. exact (@lem1982753 (term366 m n) (term376 m n) (term565 m n) (term579 m n)). Qed.
Lemma lem2392637 (m : int) (n : int) : (term580 m n) = (term581 m n).
Proof. exact (@lem1982715 term183 (term366 m n)). Qed.
Lemma lem2392639 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392640 : term153 = term219.
Proof. exact (@lem2392639 term154). Qed.
Lemma lem2392642 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392643 : term183 = term184.
Proof. exact (@lem2392642 term154). Qed.
Lemma lem2392644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392645 : term234 = term235.
Proof. exact (MK_COMB (@lem2392644) (@lem2392643)). Qed.
Lemma lem2392646 : term236 = term237.
Proof. exact (MK_COMB (@lem2392645) (@lem2392640)). Qed.
Lemma lem2392647 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2392649 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392650 : term240 = term241.
Proof. exact (@lem2392649 (NUMERAL 0) term154). Qed.
Lemma lem2392651 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392652 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392653 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392652 h1) (fun h1 : term241 = True => @lem2392651)). Qed.
Lemma lem2392654 : term241 = True.
Proof. exact (EQ_MP (@lem2392653) (@lem2392651)). Qed.
Lemma lem2392655 : term240 = True.
Proof. exact (TRANS (@lem2392650) (@lem2392654)). Qed.
Lemma lem2392656 : True = term240.
Proof. exact (SYM (@lem2392655)). Qed.
Lemma lem2392657 : term240.
Proof. exact (EQ_MP (@lem2392656) (@lem0)). Qed.
Lemma lem2392658 : term243.
Proof. exact (@lem2392647 (@lem2392657)). Qed.
Lemma lem2392660 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392661 : term240 = term241.
Proof. exact (@lem2392660 (NUMERAL 0) term154). Qed.
Lemma lem2392662 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392663 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392664 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392663 h1) (fun h1 : term241 = True => @lem2392662)). Qed.
Lemma lem2392665 : term241 = True.
Proof. exact (EQ_MP (@lem2392664) (@lem2392662)). Qed.
Lemma lem2392666 : term240 = True.
Proof. exact (TRANS (@lem2392661) (@lem2392665)). Qed.
Lemma lem2392667 : True = term240.
Proof. exact (SYM (@lem2392666)). Qed.
Lemma lem2392668 : term240.
Proof. exact (EQ_MP (@lem2392667) (@lem0)). Qed.
Lemma lem2392669 : term244.
Proof. exact (@lem2392658 (@lem2392668)). Qed.
Lemma lem2392671 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392672 : term240 = term241.
Proof. exact (@lem2392671 (NUMERAL 0) term154). Qed.
Lemma lem2392673 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392674 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392675 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392674 h1) (fun h1 : term241 = True => @lem2392673)). Qed.
Lemma lem2392676 : term241 = True.
Proof. exact (EQ_MP (@lem2392675) (@lem2392673)). Qed.
Lemma lem2392677 : term240 = True.
Proof. exact (TRANS (@lem2392672) (@lem2392676)). Qed.
Lemma lem2392678 : True = term240.
Proof. exact (SYM (@lem2392677)). Qed.
Lemma lem2392679 : term240.
Proof. exact (EQ_MP (@lem2392678) (@lem0)). Qed.
Lemma lem2392680 : term245.
Proof. exact (@lem2392669 (@lem2392679)). Qed.
Lemma lem2392682 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392683 : term192 = term193.
Proof. exact (@lem2392682 term154 term154). Qed.
Lemma lem2392684 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392685 : term195 = term154.
Proof. exact (EQ_MP (@lem2392684) (@lem940073)). Qed.
Lemma lem2392686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392687 : term193 = term153.
Proof. exact (MK_COMB (@lem2392686) (@lem2392685)). Qed.
Lemma lem2392688 : term192 = term153.
Proof. exact (TRANS (@lem2392683) (@lem2392687)). Qed.
Lemma lem2392690 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2392691 : term220 = term225.
Proof. exact (@lem2392690 term154 term154). Qed.
Lemma lem2392692 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392693 : term195 = term154.
Proof. exact (EQ_MP (@lem2392692) (@lem940073)). Qed.
Lemma lem2392694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392695 : term193 = term153.
Proof. exact (MK_COMB (@lem2392694) (@lem2392693)). Qed.
Lemma lem2392696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2392697 : term225 = term183.
Proof. exact (MK_COMB (@lem2392696) (@lem2392695)). Qed.
Lemma lem2392698 : term220 = term183.
Proof. exact (TRANS (@lem2392691) (@lem2392697)). Qed.
Lemma lem2392699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392700 : term246 = term234.
Proof. exact (MK_COMB (@lem2392699) (@lem2392698)). Qed.
Lemma lem2392701 : term247 = term236.
Proof. exact (MK_COMB (@lem2392700) (@lem2392688)). Qed.
Lemma lem2392703 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2392704 : term236 = term120.
Proof. exact (@lem2392703 term154). Qed.
Lemma lem2392705 : term247 = term120.
Proof. exact (TRANS (@lem2392701) (@lem2392704)). Qed.
Lemma lem2392706 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392707 : term249 = term145.
Proof. exact (MK_COMB (@lem2392706) (@lem2392705)). Qed.
Lemma lem2392708 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2392709 : term250 = term251.
Proof. exact (MK_COMB (@lem2392707) (@lem2392708)). Qed.
Lemma lem2392711 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392712 : term251 = term120.
Proof. exact (@lem2392711 term154). Qed.
Lemma lem2392713 : term250 = term120.
Proof. exact (TRANS (@lem2392709) (@lem2392712)). Qed.
Lemma lem2392715 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392716 : term192 = term193.
Proof. exact (@lem2392715 term154 term154). Qed.
Lemma lem2392717 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392718 : term195 = term154.
Proof. exact (EQ_MP (@lem2392717) (@lem940073)). Qed.
Lemma lem2392719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392720 : term193 = term153.
Proof. exact (MK_COMB (@lem2392719) (@lem2392718)). Qed.
Lemma lem2392721 : term192 = term153.
Proof. exact (TRANS (@lem2392716) (@lem2392720)). Qed.
Lemma lem2392722 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2392723 : term253 = term251.
Proof. exact (MK_COMB (@lem2392722) (@lem2392721)). Qed.
Lemma lem2392725 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392726 : term251 = term120.
Proof. exact (@lem2392725 term154). Qed.
Lemma lem2392727 : term253 = term120.
Proof. exact (TRANS (@lem2392723) (@lem2392726)). Qed.
Lemma lem2392728 : term120 = term253.
Proof. exact (SYM (@lem2392727)). Qed.
Lemma lem2392729 : term250 = term253.
Proof. exact (TRANS (@lem2392713) (@lem2392728)). Qed.
Lemma lem2392730 : term237 = term180.
Proof. exact (@lem2392680 (@lem2392729)). Qed.
Lemma lem2392731 : term236 = term180.
Proof. exact (TRANS (@lem2392646) (@lem2392730)). Qed.
Lemma lem2392733 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2392734 : term180 = term120.
Proof. exact (@lem2392733 term120). Qed.
Lemma lem2392735 : term236 = term120.
Proof. exact (TRANS (@lem2392731) (@lem2392734)). Qed.
Lemma lem2392736 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392737 : term254 = term145.
Proof. exact (MK_COMB (@lem2392736) (@lem2392735)). Qed.
Lemma lem2392738 (m : int) (n : int) : (term366 m n) = (term366 m n).
Proof. exact (eq_refl (term366 m n)). Qed.
Lemma lem2392739 (m : int) (n : int) : (term581 m n) = (term582 m n).
Proof. exact (MK_COMB (@lem2392737) (@lem2392738 m n)). Qed.
Lemma lem2392740 (m : int) (n : int) : (term580 m n) = (term582 m n).
Proof. exact (TRANS (@lem2392637 m n) (@lem2392739 m n)). Qed.
Lemma lem2392741 (m : int) (n : int) : (term582 m n) = term120.
Proof. exact (@lem1982719 (term366 m n)). Qed.
Lemma lem2392742 (m : int) (n : int) : (term580 m n) = term120.
Proof. exact (TRANS (@lem2392740 m n) (@lem2392741 m n)). Qed.
Lemma lem2392743 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392744 (m : int) (n : int) : (term583 m n) = term211.
Proof. exact (MK_COMB (@lem2392743) (@lem2392742 m n)). Qed.
Lemma lem2392745 (m : int) (n : int) : (term584 m n) = (term585 m n).
Proof. exact (@lem1982753 (term206 m) (real_of_int m) (term292 m n) (term359 m n)). Qed.
Lemma lem2392746 (m : int) : (term586 m) = (term233 m).
Proof. exact (@lem1982713 term183 (real_of_int m)). Qed.
Lemma lem2392748 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392749 : term153 = term219.
Proof. exact (@lem2392748 term154). Qed.
Lemma lem2392751 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392752 : term183 = term184.
Proof. exact (@lem2392751 term154). Qed.
Lemma lem2392753 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392754 : term234 = term235.
Proof. exact (MK_COMB (@lem2392753) (@lem2392752)). Qed.
Lemma lem2392755 : term236 = term237.
Proof. exact (MK_COMB (@lem2392754) (@lem2392749)). Qed.
Lemma lem2392756 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2392758 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392759 : term240 = term241.
Proof. exact (@lem2392758 (NUMERAL 0) term154). Qed.
Lemma lem2392760 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392761 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392762 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392761 h1) (fun h1 : term241 = True => @lem2392760)). Qed.
Lemma lem2392763 : term241 = True.
Proof. exact (EQ_MP (@lem2392762) (@lem2392760)). Qed.
Lemma lem2392764 : term240 = True.
Proof. exact (TRANS (@lem2392759) (@lem2392763)). Qed.
Lemma lem2392765 : True = term240.
Proof. exact (SYM (@lem2392764)). Qed.
Lemma lem2392766 : term240.
Proof. exact (EQ_MP (@lem2392765) (@lem0)). Qed.
Lemma lem2392767 : term243.
Proof. exact (@lem2392756 (@lem2392766)). Qed.
Lemma lem2392769 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392770 : term240 = term241.
Proof. exact (@lem2392769 (NUMERAL 0) term154). Qed.
Lemma lem2392771 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392772 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392773 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392772 h1) (fun h1 : term241 = True => @lem2392771)). Qed.
Lemma lem2392774 : term241 = True.
Proof. exact (EQ_MP (@lem2392773) (@lem2392771)). Qed.
Lemma lem2392775 : term240 = True.
Proof. exact (TRANS (@lem2392770) (@lem2392774)). Qed.
Lemma lem2392776 : True = term240.
Proof. exact (SYM (@lem2392775)). Qed.
Lemma lem2392777 : term240.
Proof. exact (EQ_MP (@lem2392776) (@lem0)). Qed.
Lemma lem2392778 : term244.
Proof. exact (@lem2392767 (@lem2392777)). Qed.
Lemma lem2392780 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392781 : term240 = term241.
Proof. exact (@lem2392780 (NUMERAL 0) term154). Qed.
Lemma lem2392782 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392783 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392784 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392783 h1) (fun h1 : term241 = True => @lem2392782)). Qed.
Lemma lem2392785 : term241 = True.
Proof. exact (EQ_MP (@lem2392784) (@lem2392782)). Qed.
Lemma lem2392786 : term240 = True.
Proof. exact (TRANS (@lem2392781) (@lem2392785)). Qed.
Lemma lem2392787 : True = term240.
Proof. exact (SYM (@lem2392786)). Qed.
Lemma lem2392788 : term240.
Proof. exact (EQ_MP (@lem2392787) (@lem0)). Qed.
Lemma lem2392789 : term245.
Proof. exact (@lem2392778 (@lem2392788)). Qed.
Lemma lem2392791 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392792 : term192 = term193.
Proof. exact (@lem2392791 term154 term154). Qed.
Lemma lem2392793 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392794 : term195 = term154.
Proof. exact (EQ_MP (@lem2392793) (@lem940073)). Qed.
Lemma lem2392795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392796 : term193 = term153.
Proof. exact (MK_COMB (@lem2392795) (@lem2392794)). Qed.
Lemma lem2392797 : term192 = term153.
Proof. exact (TRANS (@lem2392792) (@lem2392796)). Qed.
Lemma lem2392799 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2392800 : term220 = term225.
Proof. exact (@lem2392799 term154 term154). Qed.
Lemma lem2392801 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392802 : term195 = term154.
Proof. exact (EQ_MP (@lem2392801) (@lem940073)). Qed.
Lemma lem2392803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392804 : term193 = term153.
Proof. exact (MK_COMB (@lem2392803) (@lem2392802)). Qed.
Lemma lem2392805 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2392806 : term225 = term183.
Proof. exact (MK_COMB (@lem2392805) (@lem2392804)). Qed.
Lemma lem2392807 : term220 = term183.
Proof. exact (TRANS (@lem2392800) (@lem2392806)). Qed.
Lemma lem2392808 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392809 : term246 = term234.
Proof. exact (MK_COMB (@lem2392808) (@lem2392807)). Qed.
Lemma lem2392810 : term247 = term236.
Proof. exact (MK_COMB (@lem2392809) (@lem2392797)). Qed.
Lemma lem2392812 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2392813 : term236 = term120.
Proof. exact (@lem2392812 term154). Qed.
Lemma lem2392814 : term247 = term120.
Proof. exact (TRANS (@lem2392810) (@lem2392813)). Qed.
Lemma lem2392815 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392816 : term249 = term145.
Proof. exact (MK_COMB (@lem2392815) (@lem2392814)). Qed.
Lemma lem2392817 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2392818 : term250 = term251.
Proof. exact (MK_COMB (@lem2392816) (@lem2392817)). Qed.
Lemma lem2392820 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392821 : term251 = term120.
Proof. exact (@lem2392820 term154). Qed.
Lemma lem2392822 : term250 = term120.
Proof. exact (TRANS (@lem2392818) (@lem2392821)). Qed.
Lemma lem2392824 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392825 : term192 = term193.
Proof. exact (@lem2392824 term154 term154). Qed.
Lemma lem2392826 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392827 : term195 = term154.
Proof. exact (EQ_MP (@lem2392826) (@lem940073)). Qed.
Lemma lem2392828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392829 : term193 = term153.
Proof. exact (MK_COMB (@lem2392828) (@lem2392827)). Qed.
Lemma lem2392830 : term192 = term153.
Proof. exact (TRANS (@lem2392825) (@lem2392829)). Qed.
Lemma lem2392831 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2392832 : term253 = term251.
Proof. exact (MK_COMB (@lem2392831) (@lem2392830)). Qed.
Lemma lem2392834 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392835 : term251 = term120.
Proof. exact (@lem2392834 term154). Qed.
Lemma lem2392836 : term253 = term120.
Proof. exact (TRANS (@lem2392832) (@lem2392835)). Qed.
Lemma lem2392837 : term120 = term253.
Proof. exact (SYM (@lem2392836)). Qed.
Lemma lem2392838 : term250 = term253.
Proof. exact (TRANS (@lem2392822) (@lem2392837)). Qed.
Lemma lem2392839 : term237 = term180.
Proof. exact (@lem2392789 (@lem2392838)). Qed.
Lemma lem2392840 : term236 = term180.
Proof. exact (TRANS (@lem2392755) (@lem2392839)). Qed.
Lemma lem2392842 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2392843 : term180 = term120.
Proof. exact (@lem2392842 term120). Qed.
Lemma lem2392844 : term236 = term120.
Proof. exact (TRANS (@lem2392840) (@lem2392843)). Qed.
Lemma lem2392845 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392846 : term254 = term145.
Proof. exact (MK_COMB (@lem2392845) (@lem2392844)). Qed.
Lemma lem2392847 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2392848 (m : int) : (term233 m) = (term255 m).
Proof. exact (MK_COMB (@lem2392846) (@lem2392847 m)). Qed.
Lemma lem2392849 (m : int) : (term586 m) = (term255 m).
Proof. exact (TRANS (@lem2392746 m) (@lem2392848 m)). Qed.
Lemma lem2392850 (m : int) : (term255 m) = term120.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2392851 (m : int) : (term586 m) = term120.
Proof. exact (TRANS (@lem2392849 m) (@lem2392850 m)). Qed.
Lemma lem2392852 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392853 (m : int) : (term587 m) = term211.
Proof. exact (MK_COMB (@lem2392852) (@lem2392851 m)). Qed.
Lemma lem2392854 (m : int) (n : int) : (term588 m n) = (term589 m n).
Proof. exact (@lem1982763 (term292 m n) (term377 m n) term183). Qed.
Lemma lem2392855 (m : int) (n : int) : (term590 m n) = (term591 m n).
Proof. exact (@lem1982715 term183 (term292 m n)). Qed.
Lemma lem2392857 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392858 : term153 = term219.
Proof. exact (@lem2392857 term154). Qed.
Lemma lem2392860 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392861 : term183 = term184.
Proof. exact (@lem2392860 term154). Qed.
Lemma lem2392862 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392863 : term234 = term235.
Proof. exact (MK_COMB (@lem2392862) (@lem2392861)). Qed.
Lemma lem2392864 : term236 = term237.
Proof. exact (MK_COMB (@lem2392863) (@lem2392858)). Qed.
Lemma lem2392865 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2392867 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392868 : term240 = term241.
Proof. exact (@lem2392867 (NUMERAL 0) term154). Qed.
Lemma lem2392869 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392870 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392871 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392870 h1) (fun h1 : term241 = True => @lem2392869)). Qed.
Lemma lem2392872 : term241 = True.
Proof. exact (EQ_MP (@lem2392871) (@lem2392869)). Qed.
Lemma lem2392873 : term240 = True.
Proof. exact (TRANS (@lem2392868) (@lem2392872)). Qed.
Lemma lem2392874 : True = term240.
Proof. exact (SYM (@lem2392873)). Qed.
Lemma lem2392875 : term240.
Proof. exact (EQ_MP (@lem2392874) (@lem0)). Qed.
Lemma lem2392876 : term243.
Proof. exact (@lem2392865 (@lem2392875)). Qed.
Lemma lem2392878 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392879 : term240 = term241.
Proof. exact (@lem2392878 (NUMERAL 0) term154). Qed.
Lemma lem2392880 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392881 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392882 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392881 h1) (fun h1 : term241 = True => @lem2392880)). Qed.
Lemma lem2392883 : term241 = True.
Proof. exact (EQ_MP (@lem2392882) (@lem2392880)). Qed.
Lemma lem2392884 : term240 = True.
Proof. exact (TRANS (@lem2392879) (@lem2392883)). Qed.
Lemma lem2392885 : True = term240.
Proof. exact (SYM (@lem2392884)). Qed.
Lemma lem2392886 : term240.
Proof. exact (EQ_MP (@lem2392885) (@lem0)). Qed.
Lemma lem2392887 : term244.
Proof. exact (@lem2392876 (@lem2392886)). Qed.
Lemma lem2392889 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392890 : term240 = term241.
Proof. exact (@lem2392889 (NUMERAL 0) term154). Qed.
Lemma lem2392891 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392892 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392893 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392892 h1) (fun h1 : term241 = True => @lem2392891)). Qed.
Lemma lem2392894 : term241 = True.
Proof. exact (EQ_MP (@lem2392893) (@lem2392891)). Qed.
Lemma lem2392895 : term240 = True.
Proof. exact (TRANS (@lem2392890) (@lem2392894)). Qed.
Lemma lem2392896 : True = term240.
Proof. exact (SYM (@lem2392895)). Qed.
Lemma lem2392897 : term240.
Proof. exact (EQ_MP (@lem2392896) (@lem0)). Qed.
Lemma lem2392898 : term245.
Proof. exact (@lem2392887 (@lem2392897)). Qed.
Lemma lem2392900 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392901 : term192 = term193.
Proof. exact (@lem2392900 term154 term154). Qed.
Lemma lem2392902 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392903 : term195 = term154.
Proof. exact (EQ_MP (@lem2392902) (@lem940073)). Qed.
Lemma lem2392904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392905 : term193 = term153.
Proof. exact (MK_COMB (@lem2392904) (@lem2392903)). Qed.
Lemma lem2392906 : term192 = term153.
Proof. exact (TRANS (@lem2392901) (@lem2392905)). Qed.
Lemma lem2392908 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2392909 : term220 = term225.
Proof. exact (@lem2392908 term154 term154). Qed.
Lemma lem2392910 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392911 : term195 = term154.
Proof. exact (EQ_MP (@lem2392910) (@lem940073)). Qed.
Lemma lem2392912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392913 : term193 = term153.
Proof. exact (MK_COMB (@lem2392912) (@lem2392911)). Qed.
Lemma lem2392914 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2392915 : term225 = term183.
Proof. exact (MK_COMB (@lem2392914) (@lem2392913)). Qed.
Lemma lem2392916 : term220 = term183.
Proof. exact (TRANS (@lem2392909) (@lem2392915)). Qed.
Lemma lem2392917 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392918 : term246 = term234.
Proof. exact (MK_COMB (@lem2392917) (@lem2392916)). Qed.
Lemma lem2392919 : term247 = term236.
Proof. exact (MK_COMB (@lem2392918) (@lem2392906)). Qed.
Lemma lem2392921 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2392922 : term236 = term120.
Proof. exact (@lem2392921 term154). Qed.
Lemma lem2392923 : term247 = term120.
Proof. exact (TRANS (@lem2392919) (@lem2392922)). Qed.
Lemma lem2392924 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392925 : term249 = term145.
Proof. exact (MK_COMB (@lem2392924) (@lem2392923)). Qed.
Lemma lem2392926 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2392927 : term250 = term251.
Proof. exact (MK_COMB (@lem2392925) (@lem2392926)). Qed.
Lemma lem2392929 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392930 : term251 = term120.
Proof. exact (@lem2392929 term154). Qed.
Lemma lem2392931 : term250 = term120.
Proof. exact (TRANS (@lem2392927) (@lem2392930)). Qed.
Lemma lem2392933 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2392934 : term192 = term193.
Proof. exact (@lem2392933 term154 term154). Qed.
Lemma lem2392935 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2392936 : term195 = term154.
Proof. exact (EQ_MP (@lem2392935) (@lem940073)). Qed.
Lemma lem2392937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2392938 : term193 = term153.
Proof. exact (MK_COMB (@lem2392937) (@lem2392936)). Qed.
Lemma lem2392939 : term192 = term153.
Proof. exact (TRANS (@lem2392934) (@lem2392938)). Qed.
Lemma lem2392940 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2392941 : term253 = term251.
Proof. exact (MK_COMB (@lem2392940) (@lem2392939)). Qed.
Lemma lem2392943 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2392944 : term251 = term120.
Proof. exact (@lem2392943 term154). Qed.
Lemma lem2392945 : term253 = term120.
Proof. exact (TRANS (@lem2392941) (@lem2392944)). Qed.
Lemma lem2392946 : term120 = term253.
Proof. exact (SYM (@lem2392945)). Qed.
Lemma lem2392947 : term250 = term253.
Proof. exact (TRANS (@lem2392931) (@lem2392946)). Qed.
Lemma lem2392948 : term237 = term180.
Proof. exact (@lem2392898 (@lem2392947)). Qed.
Lemma lem2392949 : term236 = term180.
Proof. exact (TRANS (@lem2392864) (@lem2392948)). Qed.
Lemma lem2392951 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2392952 : term180 = term120.
Proof. exact (@lem2392951 term120). Qed.
Lemma lem2392953 : term236 = term120.
Proof. exact (TRANS (@lem2392949) (@lem2392952)). Qed.
Lemma lem2392954 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2392955 : term254 = term145.
Proof. exact (MK_COMB (@lem2392954) (@lem2392953)). Qed.
Lemma lem2392956 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2392957 (m : int) (n : int) : (term591 m n) = (term592 m n).
Proof. exact (MK_COMB (@lem2392955) (@lem2392956 m n)). Qed.
Lemma lem2392958 (m : int) (n : int) : (term590 m n) = (term592 m n).
Proof. exact (TRANS (@lem2392855 m n) (@lem2392957 m n)). Qed.
Lemma lem2392959 (m : int) (n : int) : (term592 m n) = term120.
Proof. exact (@lem1982719 (term292 m n)). Qed.
Lemma lem2392960 (m : int) (n : int) : (term590 m n) = term120.
Proof. exact (TRANS (@lem2392958 m n) (@lem2392959 m n)). Qed.
Lemma lem2392961 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2392962 (m : int) (n : int) : (term593 m n) = term211.
Proof. exact (MK_COMB (@lem2392961) (@lem2392960 m n)). Qed.
Lemma lem2392963 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2392964 (m : int) (n : int) : (term589 m n) = term257.
Proof. exact (MK_COMB (@lem2392962 m n) (@lem2392963)). Qed.
Lemma lem2392965 (m : int) (n : int) : (term588 m n) = term257.
Proof. exact (TRANS (@lem2392854 m n) (@lem2392964 m n)). Qed.
Lemma lem2392966 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2392967 (m : int) (n : int) : (term588 m n) = term183.
Proof. exact (TRANS (@lem2392965 m n) (@lem2392966)). Qed.
Lemma lem2392968 (m : int) (n : int) : (term585 m n) = term257.
Proof. exact (MK_COMB (@lem2392853 m) (@lem2392967 m n)). Qed.
Lemma lem2392969 (m : int) (n : int) : (term584 m n) = term257.
Proof. exact (TRANS (@lem2392745 m n) (@lem2392968 m n)). Qed.
Lemma lem2392970 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2392971 (m : int) (n : int) : (term584 m n) = term183.
Proof. exact (TRANS (@lem2392969 m n) (@lem2392970)). Qed.
Lemma lem2392972 (m : int) (n : int) : (term578 m n) = term257.
Proof. exact (MK_COMB (@lem2392744 m n) (@lem2392971 m n)). Qed.
Lemma lem2392973 (m : int) (n : int) : (term577 m n) = term257.
Proof. exact (TRANS (@lem2392636 m n) (@lem2392972 m n)). Qed.
Lemma lem2392974 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2392975 (m : int) (n : int) : (term577 m n) = term183.
Proof. exact (TRANS (@lem2392973 m n) (@lem2392974)). Qed.
Lemma lem2392976 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2392977 (m : int) (n : int) : (term594 m n) = term259.
Proof. exact (MK_COMB (@lem2392976) (@lem2392975 m n)). Qed.
Lemma lem2392978 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2392979 (m : int) (n : int) : (term576 m n) = term260.
Proof. exact (MK_COMB (@lem2392977 m n) (@lem2392978)). Qed.
Lemma lem2392980 (m : int) (n : int) (h1 : term501 m n) : term260.
Proof. exact (EQ_MP (@lem2392979 m n) (@lem2392635 m n h1)). Qed.
Lemma lem2392982 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2392983 : term260 = term271.
Proof. exact (@lem2392982 term120 term183). Qed.
Lemma lem2392985 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2392986 : term183 = term184.
Proof. exact (@lem2392985 term154). Qed.
Lemma lem2392988 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2392989 : term120 = term180.
Proof. exact (@lem2392988 (NUMERAL 0)). Qed.
Lemma lem2392990 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2392991 : term272 = term273.
Proof. exact (MK_COMB (@lem2392990) (@lem2392989)). Qed.
Lemma lem2392992 : term271 = term274.
Proof. exact (MK_COMB (@lem2392991) (@lem2392986)). Qed.
Lemma lem2392993 : term275.
Proof. exact (@lem1980026 term120 term153 term183 term153). Qed.
Lemma lem2392995 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2392996 : term240 = term241.
Proof. exact (@lem2392995 (NUMERAL 0) term154). Qed.
Lemma lem2392997 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2392998 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2392999 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2392998 h1) (fun h1 : term241 = True => @lem2392997)). Qed.
Lemma lem2393000 : term241 = True.
Proof. exact (EQ_MP (@lem2392999) (@lem2392997)). Qed.
Lemma lem2393001 : term240 = True.
Proof. exact (TRANS (@lem2392996) (@lem2393000)). Qed.
Lemma lem2393002 : True = term240.
Proof. exact (SYM (@lem2393001)). Qed.
Lemma lem2393003 : term240.
Proof. exact (EQ_MP (@lem2393002) (@lem0)). Qed.
Lemma lem2393004 : term276.
Proof. exact (@lem2392993 (@lem2393003)). Qed.
Lemma lem2393006 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393007 : term240 = term241.
Proof. exact (@lem2393006 (NUMERAL 0) term154). Qed.
Lemma lem2393008 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393009 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393010 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393009 h1) (fun h1 : term241 = True => @lem2393008)). Qed.
Lemma lem2393011 : term241 = True.
Proof. exact (EQ_MP (@lem2393010) (@lem2393008)). Qed.
Lemma lem2393012 : term240 = True.
Proof. exact (TRANS (@lem2393007) (@lem2393011)). Qed.
Lemma lem2393013 : True = term240.
Proof. exact (SYM (@lem2393012)). Qed.
Lemma lem2393014 : term240.
Proof. exact (EQ_MP (@lem2393013) (@lem0)). Qed.
Lemma lem2393015 : term274 = term277.
Proof. exact (@lem2393004 (@lem2393014)). Qed.
Lemma lem2393017 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393018 : term220 = term225.
Proof. exact (@lem2393017 term154 term154). Qed.
Lemma lem2393019 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393020 : term195 = term154.
Proof. exact (EQ_MP (@lem2393019) (@lem940073)). Qed.
Lemma lem2393021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393022 : term193 = term153.
Proof. exact (MK_COMB (@lem2393021) (@lem2393020)). Qed.
Lemma lem2393023 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393024 : term225 = term183.
Proof. exact (MK_COMB (@lem2393023) (@lem2393022)). Qed.
Lemma lem2393025 : term220 = term183.
Proof. exact (TRANS (@lem2393018) (@lem2393024)). Qed.
Lemma lem2393027 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393028 : term251 = term120.
Proof. exact (@lem2393027 term154). Qed.
Lemma lem2393029 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2393030 : term278 = term272.
Proof. exact (MK_COMB (@lem2393029) (@lem2393028)). Qed.
Lemma lem2393031 : term277 = term271.
Proof. exact (MK_COMB (@lem2393030) (@lem2393025)). Qed.
Lemma lem2393033 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2393034 : term271 = term281.
Proof. exact (@lem2393033 (NUMERAL 0) term154). Qed.
Lemma lem2393035 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393036 (h1 : term242 = (BIT1 0)) : (term154 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2393037 : (term242 = (BIT1 0)) = ((term154 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393036 h1) (fun h1 : (term154 = (NUMERAL 0)) = False => @lem2393035)). Qed.
Lemma lem2393038 : (term154 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2393037) (@lem2393035)). Qed.
Lemma lem2393039 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2393040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2393041 : term282 = (and True).
Proof. exact (MK_COMB (@lem2393040) (@lem2393039)). Qed.
Lemma lem2393042 : term281 = (True /\ False).
Proof. exact (MK_COMB (@lem2393041) (@lem2393038)). Qed.
Lemma lem2393044 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2393045 : term281 = False.
Proof. exact (TRANS (@lem2393042) (@lem2393044)). Qed.
Lemma lem2393046 : term271 = False.
Proof. exact (TRANS (@lem2393034) (@lem2393045)). Qed.
Lemma lem2393047 : term277 = False.
Proof. exact (TRANS (@lem2393031) (@lem2393046)). Qed.
Lemma lem2393048 : term274 = False.
Proof. exact (TRANS (@lem2393015) (@lem2393047)). Qed.
Lemma lem2393049 : term271 = False.
Proof. exact (TRANS (@lem2392992) (@lem2393048)). Qed.
Lemma lem2393050 : term260 = False.
Proof. exact (TRANS (@lem2392983) (@lem2393049)). Qed.
Lemma lem2393051 (m : int) (n : int) (h1 : term501 m n) : False.
Proof. exact (EQ_MP (@lem2393050) (@lem2392980 m n h1)). Qed.
Lemma lem2393052 (m : int) (n : int) (h1 : term502 m n) : False.
Proof. exact (or_elim (@lem2391825 m n h1) (fun h0 : term432 m n => @lem2392438 m n h0) (fun h0 : term501 m n => @lem2393051 m n h0)). Qed.
Lemma lem2393053 (m : int) (n : int) (h1 : term527 m n) : term527 m n.
Proof. exact (h1). Qed.
Lemma lem2393054 (m : int) (n : int) (h1 : term514 m n) : term514 m n.
Proof. exact (h1). Qed.
Lemma lem2393055 (m : int) (n : int) (h1 : term514 m n) : term512 m n.
Proof. exact (proj2 (@lem2393054 m n h1)). Qed.
Lemma lem2393057 (m : int) (n : int) (h1 : term514 m n) : term413 m n.
Proof. exact (proj2 (@lem2393055 m n h1)). Qed.
Lemma lem2393058 (m : int) (n : int) (h1 : term514 m n) : term460 m n.
Proof. exact (proj1 (@lem2393055 m n h1)). Qed.
Lemma lem2393059 (m : int) (n : int) (h1 : term514 m n) : term459 m n.
Proof. exact (proj2 (@lem2393058 m n h1)). Qed.
Lemma lem2393061 (m : int) (n : int) (h1 : term514 m n) : (term375 m n) = term120.
Proof. exact (proj2 (@lem2393059 m n h1)). Qed.
Lemma lem2393064 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2393065 : term531 = term240.
Proof. exact (@lem2393064 term120 term153). Qed.
Lemma lem2393067 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393068 : term153 = term219.
Proof. exact (@lem2393067 term154). Qed.
Lemma lem2393070 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393071 : term120 = term180.
Proof. exact (@lem2393070 (NUMERAL 0)). Qed.
Lemma lem2393072 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2393073 : term532 = term533.
Proof. exact (MK_COMB (@lem2393072) (@lem2393071)). Qed.
Lemma lem2393074 : term240 = term534.
Proof. exact (MK_COMB (@lem2393073) (@lem2393068)). Qed.
Lemma lem2393075 : term535.
Proof. exact (@lem1980255 term120 term153 term153 term153). Qed.
Lemma lem2393077 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393078 : term240 = term241.
Proof. exact (@lem2393077 (NUMERAL 0) term154). Qed.
Lemma lem2393079 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393080 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393081 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393080 h1) (fun h1 : term241 = True => @lem2393079)). Qed.
Lemma lem2393082 : term241 = True.
Proof. exact (EQ_MP (@lem2393081) (@lem2393079)). Qed.
Lemma lem2393083 : term240 = True.
Proof. exact (TRANS (@lem2393078) (@lem2393082)). Qed.
Lemma lem2393084 : True = term240.
Proof. exact (SYM (@lem2393083)). Qed.
Lemma lem2393085 : term240.
Proof. exact (EQ_MP (@lem2393084) (@lem0)). Qed.
Lemma lem2393086 : term536.
Proof. exact (@lem2393075 (@lem2393085)). Qed.
Lemma lem2393088 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393089 : term240 = term241.
Proof. exact (@lem2393088 (NUMERAL 0) term154). Qed.
Lemma lem2393090 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393091 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393092 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393091 h1) (fun h1 : term241 = True => @lem2393090)). Qed.
Lemma lem2393093 : term241 = True.
Proof. exact (EQ_MP (@lem2393092) (@lem2393090)). Qed.
Lemma lem2393094 : term240 = True.
Proof. exact (TRANS (@lem2393089) (@lem2393093)). Qed.
Lemma lem2393095 : True = term240.
Proof. exact (SYM (@lem2393094)). Qed.
Lemma lem2393096 : term240.
Proof. exact (EQ_MP (@lem2393095) (@lem0)). Qed.
Lemma lem2393097 : term534 = term537.
Proof. exact (@lem2393086 (@lem2393096)). Qed.
Lemma lem2393099 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393100 : term192 = term193.
Proof. exact (@lem2393099 term154 term154). Qed.
Lemma lem2393101 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393102 : term195 = term154.
Proof. exact (EQ_MP (@lem2393101) (@lem940073)). Qed.
Lemma lem2393103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393104 : term193 = term153.
Proof. exact (MK_COMB (@lem2393103) (@lem2393102)). Qed.
Lemma lem2393105 : term192 = term153.
Proof. exact (TRANS (@lem2393100) (@lem2393104)). Qed.
Lemma lem2393107 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393108 : term251 = term120.
Proof. exact (@lem2393107 term154). Qed.
Lemma lem2393109 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2393110 : term538 = term532.
Proof. exact (MK_COMB (@lem2393109) (@lem2393108)). Qed.
Lemma lem2393111 : term537 = term240.
Proof. exact (MK_COMB (@lem2393110) (@lem2393105)). Qed.
Lemma lem2393113 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393114 : term240 = term241.
Proof. exact (@lem2393113 (NUMERAL 0) term154). Qed.
Lemma lem2393115 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393116 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393117 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393116 h1) (fun h1 : term241 = True => @lem2393115)). Qed.
Lemma lem2393118 : term241 = True.
Proof. exact (EQ_MP (@lem2393117) (@lem2393115)). Qed.
Lemma lem2393119 : term240 = True.
Proof. exact (TRANS (@lem2393114) (@lem2393118)). Qed.
Lemma lem2393120 : term537 = True.
Proof. exact (TRANS (@lem2393111) (@lem2393119)). Qed.
Lemma lem2393121 : term534 = True.
Proof. exact (TRANS (@lem2393097) (@lem2393120)). Qed.
Lemma lem2393122 : term240 = True.
Proof. exact (TRANS (@lem2393074) (@lem2393121)). Qed.
Lemma lem2393123 : term531 = True.
Proof. exact (TRANS (@lem2393065) (@lem2393122)). Qed.
Lemma lem2393124 : True = term531.
Proof. exact (SYM (@lem2393123)). Qed.
Lemma lem2393125 : term531.
Proof. exact (EQ_MP (@lem2393124) (@lem0)). Qed.
Lemma lem2393126 (m : int) (n : int) (h1 : term514 m n) : term595 m n.
Proof. exact (conj (@lem2393125) (@lem2393057 m n h1)). Qed.
Lemma lem2393128 (x : real) (y : real) : term540 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2393129 (m : int) (n : int) : term596 m n.
Proof. exact (@lem2393128 term153 (term410 m n)). Qed.
Lemma lem2393130 (m : int) (n : int) (h1 : term514 m n) : term597 m n.
Proof. exact (@lem2393129 m n (@lem2393126 m n h1)). Qed.
Lemma lem2393131 (m : int) (n : int) : (term598 m n) = (term410 m n).
Proof. exact (@lem1982733 (term410 m n)). Qed.
Lemma lem2393132 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2393133 (m : int) (n : int) : (term599 m n) = (term412 m n).
Proof. exact (MK_COMB (@lem2393132) (@lem2393131 m n)). Qed.
Lemma lem2393134 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2393135 (m : int) (n : int) : (term597 m n) = (term413 m n).
Proof. exact (MK_COMB (@lem2393133 m n) (@lem2393134)). Qed.
Lemma lem2393136 (m : int) (n : int) (h1 : term514 m n) : term413 m n.
Proof. exact (EQ_MP (@lem2393135 m n) (@lem2393130 m n h1)). Qed.
Lemma lem2393138 (y : real) : term545 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2393139 (m : int) (n : int) : term546 m n.
Proof. exact (@lem2393138 (term375 m n)). Qed.
Lemma lem2393140 (m : int) (n : int) (h1 : term514 m n) : term547 m n.
Proof. exact (@lem2393139 m n (@lem2393061 m n h1)). Qed.
Lemma lem2393141 (m : int) (n : int) (h1 : term514 m n) : term600 m n.
Proof. exact (@lem2393140 m n h1 term153). Qed.
Lemma lem2393142 (m : int) (n : int) : (term600 m n) = ((term601 m n) = term120).
Proof. exact (eq_refl (term600 m n)). Qed.
Lemma lem2393143 (m : int) (n : int) (h1 : term514 m n) : (term601 m n) = term120.
Proof. exact (EQ_MP (@lem2393142 m n) (@lem2393141 m n h1)). Qed.
Lemma lem2393144 (m : int) (n : int) : (term601 m n) = (term375 m n).
Proof. exact (@lem1982733 (term375 m n)). Qed.
Lemma lem2393145 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2393146 (m : int) (n : int) : (term602 m n) = (term379 m n).
Proof. exact (MK_COMB (@lem2393145) (@lem2393144 m n)). Qed.
Lemma lem2393147 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2393148 (m : int) (n : int) : ((term601 m n) = term120) = ((term375 m n) = term120).
Proof. exact (MK_COMB (@lem2393146 m n) (@lem2393147)). Qed.
Lemma lem2393149 (m : int) (n : int) (h1 : term514 m n) : (term375 m n) = term120.
Proof. exact (EQ_MP (@lem2393148 m n) (@lem2393143 m n h1)). Qed.
Lemma lem2393150 (m : int) (n : int) (h1 : term514 m n) : term603 m n.
Proof. exact (conj (@lem2393149 m n h1) (@lem2393136 m n h1)). Qed.
Lemma lem2393152 (x : real) (y : real) : term574 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2393153 (m : int) (n : int) : term604 m n.
Proof. exact (@lem2393152 (term375 m n) (term410 m n)). Qed.
Lemma lem2393154 (m : int) (n : int) (h1 : term514 m n) : term605 m n.
Proof. exact (@lem2393153 m n (@lem2393150 m n h1)). Qed.
Lemma lem2393155 (m : int) (n : int) : (term606 m n) = (term607 m n).
Proof. exact (@lem1982753 (term376 m n) (term366 m n) (term551 m n) (term409 m n)). Qed.
Lemma lem2393156 (m : int) (n : int) : (term608 m n) = (term581 m n).
Proof. exact (@lem1982713 term183 (term366 m n)). Qed.
Lemma lem2393158 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393159 : term153 = term219.
Proof. exact (@lem2393158 term154). Qed.
Lemma lem2393161 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2393162 : term183 = term184.
Proof. exact (@lem2393161 term154). Qed.
Lemma lem2393163 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393164 : term234 = term235.
Proof. exact (MK_COMB (@lem2393163) (@lem2393162)). Qed.
Lemma lem2393165 : term236 = term237.
Proof. exact (MK_COMB (@lem2393164) (@lem2393159)). Qed.
Lemma lem2393166 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2393168 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393169 : term240 = term241.
Proof. exact (@lem2393168 (NUMERAL 0) term154). Qed.
Lemma lem2393170 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393171 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393172 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393171 h1) (fun h1 : term241 = True => @lem2393170)). Qed.
Lemma lem2393173 : term241 = True.
Proof. exact (EQ_MP (@lem2393172) (@lem2393170)). Qed.
Lemma lem2393174 : term240 = True.
Proof. exact (TRANS (@lem2393169) (@lem2393173)). Qed.
Lemma lem2393175 : True = term240.
Proof. exact (SYM (@lem2393174)). Qed.
Lemma lem2393176 : term240.
Proof. exact (EQ_MP (@lem2393175) (@lem0)). Qed.
Lemma lem2393177 : term243.
Proof. exact (@lem2393166 (@lem2393176)). Qed.
Lemma lem2393179 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393180 : term240 = term241.
Proof. exact (@lem2393179 (NUMERAL 0) term154). Qed.
Lemma lem2393181 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393182 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393183 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393182 h1) (fun h1 : term241 = True => @lem2393181)). Qed.
Lemma lem2393184 : term241 = True.
Proof. exact (EQ_MP (@lem2393183) (@lem2393181)). Qed.
Lemma lem2393185 : term240 = True.
Proof. exact (TRANS (@lem2393180) (@lem2393184)). Qed.
Lemma lem2393186 : True = term240.
Proof. exact (SYM (@lem2393185)). Qed.
Lemma lem2393187 : term240.
Proof. exact (EQ_MP (@lem2393186) (@lem0)). Qed.
Lemma lem2393188 : term244.
Proof. exact (@lem2393177 (@lem2393187)). Qed.
Lemma lem2393190 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393191 : term240 = term241.
Proof. exact (@lem2393190 (NUMERAL 0) term154). Qed.
Lemma lem2393192 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393193 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393194 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393193 h1) (fun h1 : term241 = True => @lem2393192)). Qed.
Lemma lem2393195 : term241 = True.
Proof. exact (EQ_MP (@lem2393194) (@lem2393192)). Qed.
Lemma lem2393196 : term240 = True.
Proof. exact (TRANS (@lem2393191) (@lem2393195)). Qed.
Lemma lem2393197 : True = term240.
Proof. exact (SYM (@lem2393196)). Qed.
Lemma lem2393198 : term240.
Proof. exact (EQ_MP (@lem2393197) (@lem0)). Qed.
Lemma lem2393199 : term245.
Proof. exact (@lem2393188 (@lem2393198)). Qed.
Lemma lem2393201 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393202 : term192 = term193.
Proof. exact (@lem2393201 term154 term154). Qed.
Lemma lem2393203 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393204 : term195 = term154.
Proof. exact (EQ_MP (@lem2393203) (@lem940073)). Qed.
Lemma lem2393205 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393206 : term193 = term153.
Proof. exact (MK_COMB (@lem2393205) (@lem2393204)). Qed.
Lemma lem2393207 : term192 = term153.
Proof. exact (TRANS (@lem2393202) (@lem2393206)). Qed.
Lemma lem2393209 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393210 : term220 = term225.
Proof. exact (@lem2393209 term154 term154). Qed.
Lemma lem2393211 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393212 : term195 = term154.
Proof. exact (EQ_MP (@lem2393211) (@lem940073)). Qed.
Lemma lem2393213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393214 : term193 = term153.
Proof. exact (MK_COMB (@lem2393213) (@lem2393212)). Qed.
Lemma lem2393215 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393216 : term225 = term183.
Proof. exact (MK_COMB (@lem2393215) (@lem2393214)). Qed.
Lemma lem2393217 : term220 = term183.
Proof. exact (TRANS (@lem2393210) (@lem2393216)). Qed.
Lemma lem2393218 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393219 : term246 = term234.
Proof. exact (MK_COMB (@lem2393218) (@lem2393217)). Qed.
Lemma lem2393220 : term247 = term236.
Proof. exact (MK_COMB (@lem2393219) (@lem2393207)). Qed.
Lemma lem2393222 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2393223 : term236 = term120.
Proof. exact (@lem2393222 term154). Qed.
Lemma lem2393224 : term247 = term120.
Proof. exact (TRANS (@lem2393220) (@lem2393223)). Qed.
Lemma lem2393225 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393226 : term249 = term145.
Proof. exact (MK_COMB (@lem2393225) (@lem2393224)). Qed.
Lemma lem2393227 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2393228 : term250 = term251.
Proof. exact (MK_COMB (@lem2393226) (@lem2393227)). Qed.
Lemma lem2393230 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393231 : term251 = term120.
Proof. exact (@lem2393230 term154). Qed.
Lemma lem2393232 : term250 = term120.
Proof. exact (TRANS (@lem2393228) (@lem2393231)). Qed.
Lemma lem2393234 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393235 : term192 = term193.
Proof. exact (@lem2393234 term154 term154). Qed.
Lemma lem2393236 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393237 : term195 = term154.
Proof. exact (EQ_MP (@lem2393236) (@lem940073)). Qed.
Lemma lem2393238 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393239 : term193 = term153.
Proof. exact (MK_COMB (@lem2393238) (@lem2393237)). Qed.
Lemma lem2393240 : term192 = term153.
Proof. exact (TRANS (@lem2393235) (@lem2393239)). Qed.
Lemma lem2393241 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2393242 : term253 = term251.
Proof. exact (MK_COMB (@lem2393241) (@lem2393240)). Qed.
Lemma lem2393244 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393245 : term251 = term120.
Proof. exact (@lem2393244 term154). Qed.
Lemma lem2393246 : term253 = term120.
Proof. exact (TRANS (@lem2393242) (@lem2393245)). Qed.
Lemma lem2393247 : term120 = term253.
Proof. exact (SYM (@lem2393246)). Qed.
Lemma lem2393248 : term250 = term253.
Proof. exact (TRANS (@lem2393232) (@lem2393247)). Qed.
Lemma lem2393249 : term237 = term180.
Proof. exact (@lem2393199 (@lem2393248)). Qed.
Lemma lem2393250 : term236 = term180.
Proof. exact (TRANS (@lem2393165) (@lem2393249)). Qed.
Lemma lem2393252 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2393253 : term180 = term120.
Proof. exact (@lem2393252 term120). Qed.
Lemma lem2393254 : term236 = term120.
Proof. exact (TRANS (@lem2393250) (@lem2393253)). Qed.
Lemma lem2393255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393256 : term254 = term145.
Proof. exact (MK_COMB (@lem2393255) (@lem2393254)). Qed.
Lemma lem2393257 (m : int) (n : int) : (term366 m n) = (term366 m n).
Proof. exact (eq_refl (term366 m n)). Qed.
Lemma lem2393258 (m : int) (n : int) : (term581 m n) = (term582 m n).
Proof. exact (MK_COMB (@lem2393256) (@lem2393257 m n)). Qed.
Lemma lem2393259 (m : int) (n : int) : (term608 m n) = (term582 m n).
Proof. exact (TRANS (@lem2393156 m n) (@lem2393258 m n)). Qed.
Lemma lem2393260 (m : int) (n : int) : (term582 m n) = term120.
Proof. exact (@lem1982719 (term366 m n)). Qed.
Lemma lem2393261 (m : int) (n : int) : (term608 m n) = term120.
Proof. exact (TRANS (@lem2393259 m n) (@lem2393260 m n)). Qed.
Lemma lem2393262 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393263 (m : int) (n : int) : (term609 m n) = term211.
Proof. exact (MK_COMB (@lem2393262) (@lem2393261 m n)). Qed.
Lemma lem2393264 (m : int) (n : int) : (term610 m n) = (term611 m n).
Proof. exact (@lem1982753 (real_of_int m) (term206 m) (term377 m n) (term612 m n)). Qed.
Lemma lem2393265 (m : int) : (term232 m) = (term233 m).
Proof. exact (@lem1982715 term183 (real_of_int m)). Qed.
Lemma lem2393267 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393268 : term153 = term219.
Proof. exact (@lem2393267 term154). Qed.
Lemma lem2393270 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2393271 : term183 = term184.
Proof. exact (@lem2393270 term154). Qed.
Lemma lem2393272 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393273 : term234 = term235.
Proof. exact (MK_COMB (@lem2393272) (@lem2393271)). Qed.
Lemma lem2393274 : term236 = term237.
Proof. exact (MK_COMB (@lem2393273) (@lem2393268)). Qed.
Lemma lem2393275 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2393277 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393278 : term240 = term241.
Proof. exact (@lem2393277 (NUMERAL 0) term154). Qed.
Lemma lem2393279 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393280 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393281 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393280 h1) (fun h1 : term241 = True => @lem2393279)). Qed.
Lemma lem2393282 : term241 = True.
Proof. exact (EQ_MP (@lem2393281) (@lem2393279)). Qed.
Lemma lem2393283 : term240 = True.
Proof. exact (TRANS (@lem2393278) (@lem2393282)). Qed.
Lemma lem2393284 : True = term240.
Proof. exact (SYM (@lem2393283)). Qed.
Lemma lem2393285 : term240.
Proof. exact (EQ_MP (@lem2393284) (@lem0)). Qed.
Lemma lem2393286 : term243.
Proof. exact (@lem2393275 (@lem2393285)). Qed.
Lemma lem2393288 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393289 : term240 = term241.
Proof. exact (@lem2393288 (NUMERAL 0) term154). Qed.
Lemma lem2393290 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393291 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393292 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393291 h1) (fun h1 : term241 = True => @lem2393290)). Qed.
Lemma lem2393293 : term241 = True.
Proof. exact (EQ_MP (@lem2393292) (@lem2393290)). Qed.
Lemma lem2393294 : term240 = True.
Proof. exact (TRANS (@lem2393289) (@lem2393293)). Qed.
Lemma lem2393295 : True = term240.
Proof. exact (SYM (@lem2393294)). Qed.
Lemma lem2393296 : term240.
Proof. exact (EQ_MP (@lem2393295) (@lem0)). Qed.
Lemma lem2393297 : term244.
Proof. exact (@lem2393286 (@lem2393296)). Qed.
Lemma lem2393299 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393300 : term240 = term241.
Proof. exact (@lem2393299 (NUMERAL 0) term154). Qed.
Lemma lem2393301 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393302 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393303 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393302 h1) (fun h1 : term241 = True => @lem2393301)). Qed.
Lemma lem2393304 : term241 = True.
Proof. exact (EQ_MP (@lem2393303) (@lem2393301)). Qed.
Lemma lem2393305 : term240 = True.
Proof. exact (TRANS (@lem2393300) (@lem2393304)). Qed.
Lemma lem2393306 : True = term240.
Proof. exact (SYM (@lem2393305)). Qed.
Lemma lem2393307 : term240.
Proof. exact (EQ_MP (@lem2393306) (@lem0)). Qed.
Lemma lem2393308 : term245.
Proof. exact (@lem2393297 (@lem2393307)). Qed.
Lemma lem2393310 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393311 : term192 = term193.
Proof. exact (@lem2393310 term154 term154). Qed.
Lemma lem2393312 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393313 : term195 = term154.
Proof. exact (EQ_MP (@lem2393312) (@lem940073)). Qed.
Lemma lem2393314 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393315 : term193 = term153.
Proof. exact (MK_COMB (@lem2393314) (@lem2393313)). Qed.
Lemma lem2393316 : term192 = term153.
Proof. exact (TRANS (@lem2393311) (@lem2393315)). Qed.
Lemma lem2393318 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393319 : term220 = term225.
Proof. exact (@lem2393318 term154 term154). Qed.
Lemma lem2393320 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393321 : term195 = term154.
Proof. exact (EQ_MP (@lem2393320) (@lem940073)). Qed.
Lemma lem2393322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393323 : term193 = term153.
Proof. exact (MK_COMB (@lem2393322) (@lem2393321)). Qed.
Lemma lem2393324 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393325 : term225 = term183.
Proof. exact (MK_COMB (@lem2393324) (@lem2393323)). Qed.
Lemma lem2393326 : term220 = term183.
Proof. exact (TRANS (@lem2393319) (@lem2393325)). Qed.
Lemma lem2393327 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393328 : term246 = term234.
Proof. exact (MK_COMB (@lem2393327) (@lem2393326)). Qed.
Lemma lem2393329 : term247 = term236.
Proof. exact (MK_COMB (@lem2393328) (@lem2393316)). Qed.
Lemma lem2393331 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2393332 : term236 = term120.
Proof. exact (@lem2393331 term154). Qed.
Lemma lem2393333 : term247 = term120.
Proof. exact (TRANS (@lem2393329) (@lem2393332)). Qed.
Lemma lem2393334 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393335 : term249 = term145.
Proof. exact (MK_COMB (@lem2393334) (@lem2393333)). Qed.
Lemma lem2393336 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2393337 : term250 = term251.
Proof. exact (MK_COMB (@lem2393335) (@lem2393336)). Qed.
Lemma lem2393339 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393340 : term251 = term120.
Proof. exact (@lem2393339 term154). Qed.
Lemma lem2393341 : term250 = term120.
Proof. exact (TRANS (@lem2393337) (@lem2393340)). Qed.
Lemma lem2393343 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393344 : term192 = term193.
Proof. exact (@lem2393343 term154 term154). Qed.
Lemma lem2393345 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393346 : term195 = term154.
Proof. exact (EQ_MP (@lem2393345) (@lem940073)). Qed.
Lemma lem2393347 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393348 : term193 = term153.
Proof. exact (MK_COMB (@lem2393347) (@lem2393346)). Qed.
Lemma lem2393349 : term192 = term153.
Proof. exact (TRANS (@lem2393344) (@lem2393348)). Qed.
Lemma lem2393350 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2393351 : term253 = term251.
Proof. exact (MK_COMB (@lem2393350) (@lem2393349)). Qed.
Lemma lem2393353 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393354 : term251 = term120.
Proof. exact (@lem2393353 term154). Qed.
Lemma lem2393355 : term253 = term120.
Proof. exact (TRANS (@lem2393351) (@lem2393354)). Qed.
Lemma lem2393356 : term120 = term253.
Proof. exact (SYM (@lem2393355)). Qed.
Lemma lem2393357 : term250 = term253.
Proof. exact (TRANS (@lem2393341) (@lem2393356)). Qed.
Lemma lem2393358 : term237 = term180.
Proof. exact (@lem2393308 (@lem2393357)). Qed.
Lemma lem2393359 : term236 = term180.
Proof. exact (TRANS (@lem2393274) (@lem2393358)). Qed.
Lemma lem2393361 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2393362 : term180 = term120.
Proof. exact (@lem2393361 term120). Qed.
Lemma lem2393363 : term236 = term120.
Proof. exact (TRANS (@lem2393359) (@lem2393362)). Qed.
Lemma lem2393364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393365 : term254 = term145.
Proof. exact (MK_COMB (@lem2393364) (@lem2393363)). Qed.
Lemma lem2393366 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2393367 (m : int) : (term233 m) = (term255 m).
Proof. exact (MK_COMB (@lem2393365) (@lem2393366 m)). Qed.
Lemma lem2393368 (m : int) : (term232 m) = (term255 m).
Proof. exact (TRANS (@lem2393265 m) (@lem2393367 m)). Qed.
Lemma lem2393369 (m : int) : (term255 m) = term120.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2393370 (m : int) : (term232 m) = term120.
Proof. exact (TRANS (@lem2393368 m) (@lem2393369 m)). Qed.
Lemma lem2393371 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393372 (m : int) : (term256 m) = term211.
Proof. exact (MK_COMB (@lem2393371) (@lem2393370 m)). Qed.
Lemma lem2393373 (m : int) (n : int) : (term613 m n) = (term614 m n).
Proof. exact (@lem1982763 (term377 m n) (term292 m n) term183). Qed.
Lemma lem2393374 (m : int) (n : int) : (term615 m n) = (term591 m n).
Proof. exact (@lem1982713 term183 (term292 m n)). Qed.
Lemma lem2393376 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393377 : term153 = term219.
Proof. exact (@lem2393376 term154). Qed.
Lemma lem2393379 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2393380 : term183 = term184.
Proof. exact (@lem2393379 term154). Qed.
Lemma lem2393381 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393382 : term234 = term235.
Proof. exact (MK_COMB (@lem2393381) (@lem2393380)). Qed.
Lemma lem2393383 : term236 = term237.
Proof. exact (MK_COMB (@lem2393382) (@lem2393377)). Qed.
Lemma lem2393384 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2393386 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393387 : term240 = term241.
Proof. exact (@lem2393386 (NUMERAL 0) term154). Qed.
Lemma lem2393388 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393389 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393390 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393389 h1) (fun h1 : term241 = True => @lem2393388)). Qed.
Lemma lem2393391 : term241 = True.
Proof. exact (EQ_MP (@lem2393390) (@lem2393388)). Qed.
Lemma lem2393392 : term240 = True.
Proof. exact (TRANS (@lem2393387) (@lem2393391)). Qed.
Lemma lem2393393 : True = term240.
Proof. exact (SYM (@lem2393392)). Qed.
Lemma lem2393394 : term240.
Proof. exact (EQ_MP (@lem2393393) (@lem0)). Qed.
Lemma lem2393395 : term243.
Proof. exact (@lem2393384 (@lem2393394)). Qed.
Lemma lem2393397 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393398 : term240 = term241.
Proof. exact (@lem2393397 (NUMERAL 0) term154). Qed.
Lemma lem2393399 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393400 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393401 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393400 h1) (fun h1 : term241 = True => @lem2393399)). Qed.
Lemma lem2393402 : term241 = True.
Proof. exact (EQ_MP (@lem2393401) (@lem2393399)). Qed.
Lemma lem2393403 : term240 = True.
Proof. exact (TRANS (@lem2393398) (@lem2393402)). Qed.
Lemma lem2393404 : True = term240.
Proof. exact (SYM (@lem2393403)). Qed.
Lemma lem2393405 : term240.
Proof. exact (EQ_MP (@lem2393404) (@lem0)). Qed.
Lemma lem2393406 : term244.
Proof. exact (@lem2393395 (@lem2393405)). Qed.
Lemma lem2393408 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393409 : term240 = term241.
Proof. exact (@lem2393408 (NUMERAL 0) term154). Qed.
Lemma lem2393410 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393411 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393412 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393411 h1) (fun h1 : term241 = True => @lem2393410)). Qed.
Lemma lem2393413 : term241 = True.
Proof. exact (EQ_MP (@lem2393412) (@lem2393410)). Qed.
Lemma lem2393414 : term240 = True.
Proof. exact (TRANS (@lem2393409) (@lem2393413)). Qed.
Lemma lem2393415 : True = term240.
Proof. exact (SYM (@lem2393414)). Qed.
Lemma lem2393416 : term240.
Proof. exact (EQ_MP (@lem2393415) (@lem0)). Qed.
Lemma lem2393417 : term245.
Proof. exact (@lem2393406 (@lem2393416)). Qed.
Lemma lem2393419 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393420 : term192 = term193.
Proof. exact (@lem2393419 term154 term154). Qed.
Lemma lem2393421 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393422 : term195 = term154.
Proof. exact (EQ_MP (@lem2393421) (@lem940073)). Qed.
Lemma lem2393423 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393424 : term193 = term153.
Proof. exact (MK_COMB (@lem2393423) (@lem2393422)). Qed.
Lemma lem2393425 : term192 = term153.
Proof. exact (TRANS (@lem2393420) (@lem2393424)). Qed.
Lemma lem2393427 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393428 : term220 = term225.
Proof. exact (@lem2393427 term154 term154). Qed.
Lemma lem2393429 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393430 : term195 = term154.
Proof. exact (EQ_MP (@lem2393429) (@lem940073)). Qed.
Lemma lem2393431 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393432 : term193 = term153.
Proof. exact (MK_COMB (@lem2393431) (@lem2393430)). Qed.
Lemma lem2393433 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393434 : term225 = term183.
Proof. exact (MK_COMB (@lem2393433) (@lem2393432)). Qed.
Lemma lem2393435 : term220 = term183.
Proof. exact (TRANS (@lem2393428) (@lem2393434)). Qed.
Lemma lem2393436 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393437 : term246 = term234.
Proof. exact (MK_COMB (@lem2393436) (@lem2393435)). Qed.
Lemma lem2393438 : term247 = term236.
Proof. exact (MK_COMB (@lem2393437) (@lem2393425)). Qed.
Lemma lem2393440 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2393441 : term236 = term120.
Proof. exact (@lem2393440 term154). Qed.
Lemma lem2393442 : term247 = term120.
Proof. exact (TRANS (@lem2393438) (@lem2393441)). Qed.
Lemma lem2393443 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393444 : term249 = term145.
Proof. exact (MK_COMB (@lem2393443) (@lem2393442)). Qed.
Lemma lem2393445 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2393446 : term250 = term251.
Proof. exact (MK_COMB (@lem2393444) (@lem2393445)). Qed.
Lemma lem2393448 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393449 : term251 = term120.
Proof. exact (@lem2393448 term154). Qed.
Lemma lem2393450 : term250 = term120.
Proof. exact (TRANS (@lem2393446) (@lem2393449)). Qed.
Lemma lem2393452 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393453 : term192 = term193.
Proof. exact (@lem2393452 term154 term154). Qed.
Lemma lem2393454 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393455 : term195 = term154.
Proof. exact (EQ_MP (@lem2393454) (@lem940073)). Qed.
Lemma lem2393456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393457 : term193 = term153.
Proof. exact (MK_COMB (@lem2393456) (@lem2393455)). Qed.
Lemma lem2393458 : term192 = term153.
Proof. exact (TRANS (@lem2393453) (@lem2393457)). Qed.
Lemma lem2393459 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2393460 : term253 = term251.
Proof. exact (MK_COMB (@lem2393459) (@lem2393458)). Qed.
Lemma lem2393462 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393463 : term251 = term120.
Proof. exact (@lem2393462 term154). Qed.
Lemma lem2393464 : term253 = term120.
Proof. exact (TRANS (@lem2393460) (@lem2393463)). Qed.
Lemma lem2393465 : term120 = term253.
Proof. exact (SYM (@lem2393464)). Qed.
Lemma lem2393466 : term250 = term253.
Proof. exact (TRANS (@lem2393450) (@lem2393465)). Qed.
Lemma lem2393467 : term237 = term180.
Proof. exact (@lem2393417 (@lem2393466)). Qed.
Lemma lem2393468 : term236 = term180.
Proof. exact (TRANS (@lem2393383) (@lem2393467)). Qed.
Lemma lem2393470 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2393471 : term180 = term120.
Proof. exact (@lem2393470 term120). Qed.
Lemma lem2393472 : term236 = term120.
Proof. exact (TRANS (@lem2393468) (@lem2393471)). Qed.
Lemma lem2393473 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393474 : term254 = term145.
Proof. exact (MK_COMB (@lem2393473) (@lem2393472)). Qed.
Lemma lem2393475 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2393476 (m : int) (n : int) : (term591 m n) = (term592 m n).
Proof. exact (MK_COMB (@lem2393474) (@lem2393475 m n)). Qed.
Lemma lem2393477 (m : int) (n : int) : (term615 m n) = (term592 m n).
Proof. exact (TRANS (@lem2393374 m n) (@lem2393476 m n)). Qed.
Lemma lem2393478 (m : int) (n : int) : (term592 m n) = term120.
Proof. exact (@lem1982719 (term292 m n)). Qed.
Lemma lem2393479 (m : int) (n : int) : (term615 m n) = term120.
Proof. exact (TRANS (@lem2393477 m n) (@lem2393478 m n)). Qed.
Lemma lem2393480 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393481 (m : int) (n : int) : (term616 m n) = term211.
Proof. exact (MK_COMB (@lem2393480) (@lem2393479 m n)). Qed.
Lemma lem2393482 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2393483 (m : int) (n : int) : (term614 m n) = term257.
Proof. exact (MK_COMB (@lem2393481 m n) (@lem2393482)). Qed.
Lemma lem2393484 (m : int) (n : int) : (term613 m n) = term257.
Proof. exact (TRANS (@lem2393373 m n) (@lem2393483 m n)). Qed.
Lemma lem2393485 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2393486 (m : int) (n : int) : (term613 m n) = term183.
Proof. exact (TRANS (@lem2393484 m n) (@lem2393485)). Qed.
Lemma lem2393487 (m : int) (n : int) : (term611 m n) = term257.
Proof. exact (MK_COMB (@lem2393372 m) (@lem2393486 m n)). Qed.
Lemma lem2393488 (m : int) (n : int) : (term610 m n) = term257.
Proof. exact (TRANS (@lem2393264 m n) (@lem2393487 m n)). Qed.
Lemma lem2393489 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2393490 (m : int) (n : int) : (term610 m n) = term183.
Proof. exact (TRANS (@lem2393488 m n) (@lem2393489)). Qed.
Lemma lem2393491 (m : int) (n : int) : (term607 m n) = term257.
Proof. exact (MK_COMB (@lem2393263 m n) (@lem2393490 m n)). Qed.
Lemma lem2393492 (m : int) (n : int) : (term606 m n) = term257.
Proof. exact (TRANS (@lem2393155 m n) (@lem2393491 m n)). Qed.
Lemma lem2393493 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2393494 (m : int) (n : int) : (term606 m n) = term183.
Proof. exact (TRANS (@lem2393492 m n) (@lem2393493)). Qed.
Lemma lem2393495 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2393496 (m : int) (n : int) : (term617 m n) = term259.
Proof. exact (MK_COMB (@lem2393495) (@lem2393494 m n)). Qed.
Lemma lem2393497 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2393498 (m : int) (n : int) : (term605 m n) = term260.
Proof. exact (MK_COMB (@lem2393496 m n) (@lem2393497)). Qed.
Lemma lem2393499 (m : int) (n : int) (h1 : term514 m n) : term260.
Proof. exact (EQ_MP (@lem2393498 m n) (@lem2393154 m n h1)). Qed.
Lemma lem2393501 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2393502 : term260 = term271.
Proof. exact (@lem2393501 term120 term183). Qed.
Lemma lem2393504 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2393505 : term183 = term184.
Proof. exact (@lem2393504 term154). Qed.
Lemma lem2393507 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393508 : term120 = term180.
Proof. exact (@lem2393507 (NUMERAL 0)). Qed.
Lemma lem2393509 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2393510 : term272 = term273.
Proof. exact (MK_COMB (@lem2393509) (@lem2393508)). Qed.
Lemma lem2393511 : term271 = term274.
Proof. exact (MK_COMB (@lem2393510) (@lem2393505)). Qed.
Lemma lem2393512 : term275.
Proof. exact (@lem1980026 term120 term153 term183 term153). Qed.
Lemma lem2393514 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393515 : term240 = term241.
Proof. exact (@lem2393514 (NUMERAL 0) term154). Qed.
Lemma lem2393516 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393517 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393518 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393517 h1) (fun h1 : term241 = True => @lem2393516)). Qed.
Lemma lem2393519 : term241 = True.
Proof. exact (EQ_MP (@lem2393518) (@lem2393516)). Qed.
Lemma lem2393520 : term240 = True.
Proof. exact (TRANS (@lem2393515) (@lem2393519)). Qed.
Lemma lem2393521 : True = term240.
Proof. exact (SYM (@lem2393520)). Qed.
Lemma lem2393522 : term240.
Proof. exact (EQ_MP (@lem2393521) (@lem0)). Qed.
Lemma lem2393523 : term276.
Proof. exact (@lem2393512 (@lem2393522)). Qed.
Lemma lem2393525 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393526 : term240 = term241.
Proof. exact (@lem2393525 (NUMERAL 0) term154). Qed.
Lemma lem2393527 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393528 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393529 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393528 h1) (fun h1 : term241 = True => @lem2393527)). Qed.
Lemma lem2393530 : term241 = True.
Proof. exact (EQ_MP (@lem2393529) (@lem2393527)). Qed.
Lemma lem2393531 : term240 = True.
Proof. exact (TRANS (@lem2393526) (@lem2393530)). Qed.
Lemma lem2393532 : True = term240.
Proof. exact (SYM (@lem2393531)). Qed.
Lemma lem2393533 : term240.
Proof. exact (EQ_MP (@lem2393532) (@lem0)). Qed.
Lemma lem2393534 : term274 = term277.
Proof. exact (@lem2393523 (@lem2393533)). Qed.
Lemma lem2393536 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393537 : term220 = term225.
Proof. exact (@lem2393536 term154 term154). Qed.
Lemma lem2393538 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393539 : term195 = term154.
Proof. exact (EQ_MP (@lem2393538) (@lem940073)). Qed.
Lemma lem2393540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393541 : term193 = term153.
Proof. exact (MK_COMB (@lem2393540) (@lem2393539)). Qed.
Lemma lem2393542 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393543 : term225 = term183.
Proof. exact (MK_COMB (@lem2393542) (@lem2393541)). Qed.
Lemma lem2393544 : term220 = term183.
Proof. exact (TRANS (@lem2393537) (@lem2393543)). Qed.
Lemma lem2393546 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393547 : term251 = term120.
Proof. exact (@lem2393546 term154). Qed.
Lemma lem2393548 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2393549 : term278 = term272.
Proof. exact (MK_COMB (@lem2393548) (@lem2393547)). Qed.
Lemma lem2393550 : term277 = term271.
Proof. exact (MK_COMB (@lem2393549) (@lem2393544)). Qed.
Lemma lem2393552 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2393553 : term271 = term281.
Proof. exact (@lem2393552 (NUMERAL 0) term154). Qed.
Lemma lem2393554 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393555 (h1 : term242 = (BIT1 0)) : (term154 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2393556 : (term242 = (BIT1 0)) = ((term154 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393555 h1) (fun h1 : (term154 = (NUMERAL 0)) = False => @lem2393554)). Qed.
Lemma lem2393557 : (term154 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2393556) (@lem2393554)). Qed.
Lemma lem2393558 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2393559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2393560 : term282 = (and True).
Proof. exact (MK_COMB (@lem2393559) (@lem2393558)). Qed.
Lemma lem2393561 : term281 = (True /\ False).
Proof. exact (MK_COMB (@lem2393560) (@lem2393557)). Qed.
Lemma lem2393563 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2393564 : term281 = False.
Proof. exact (TRANS (@lem2393561) (@lem2393563)). Qed.
Lemma lem2393565 : term271 = False.
Proof. exact (TRANS (@lem2393553) (@lem2393564)). Qed.
Lemma lem2393566 : term277 = False.
Proof. exact (TRANS (@lem2393550) (@lem2393565)). Qed.
Lemma lem2393567 : term274 = False.
Proof. exact (TRANS (@lem2393534) (@lem2393566)). Qed.
Lemma lem2393568 : term271 = False.
Proof. exact (TRANS (@lem2393511) (@lem2393567)). Qed.
Lemma lem2393569 : term260 = False.
Proof. exact (TRANS (@lem2393502) (@lem2393568)). Qed.
Lemma lem2393570 (m : int) (n : int) (h1 : term514 m n) : False.
Proof. exact (EQ_MP (@lem2393569) (@lem2393499 m n h1)). Qed.
Lemma lem2393571 (m : int) (n : int) (h1 : term526 m n) : term526 m n.
Proof. exact (h1). Qed.
Lemma lem2393572 (m : int) (n : int) (h1 : term526 m n) : term525 m n.
Proof. exact (proj2 (@lem2393571 m n h1)). Qed.
Lemma lem2393574 (m : int) (n : int) (h1 : term526 m n) : term413 m n.
Proof. exact (proj2 (@lem2393572 m n h1)). Qed.
Lemma lem2393575 (m : int) (n : int) (h1 : term526 m n) : term496 m n.
Proof. exact (proj1 (@lem2393572 m n h1)). Qed.
Lemma lem2393576 (m : int) (n : int) (h1 : term526 m n) : term494 m n.
Proof. exact (proj2 (@lem2393575 m n h1)). Qed.
Lemma lem2393578 (m : int) (n : int) (h1 : term526 m n) : (term375 m n) = term120.
Proof. exact (proj2 (@lem2393576 m n h1)). Qed.
Lemma lem2393581 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2393582 : term531 = term240.
Proof. exact (@lem2393581 term120 term153). Qed.
Lemma lem2393584 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393585 : term153 = term219.
Proof. exact (@lem2393584 term154). Qed.
Lemma lem2393587 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393588 : term120 = term180.
Proof. exact (@lem2393587 (NUMERAL 0)). Qed.
Lemma lem2393589 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2393590 : term532 = term533.
Proof. exact (MK_COMB (@lem2393589) (@lem2393588)). Qed.
Lemma lem2393591 : term240 = term534.
Proof. exact (MK_COMB (@lem2393590) (@lem2393585)). Qed.
Lemma lem2393592 : term535.
Proof. exact (@lem1980255 term120 term153 term153 term153). Qed.
Lemma lem2393594 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393595 : term240 = term241.
Proof. exact (@lem2393594 (NUMERAL 0) term154). Qed.
Lemma lem2393596 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393597 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393598 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393597 h1) (fun h1 : term241 = True => @lem2393596)). Qed.
Lemma lem2393599 : term241 = True.
Proof. exact (EQ_MP (@lem2393598) (@lem2393596)). Qed.
Lemma lem2393600 : term240 = True.
Proof. exact (TRANS (@lem2393595) (@lem2393599)). Qed.
Lemma lem2393601 : True = term240.
Proof. exact (SYM (@lem2393600)). Qed.
Lemma lem2393602 : term240.
Proof. exact (EQ_MP (@lem2393601) (@lem0)). Qed.
Lemma lem2393603 : term536.
Proof. exact (@lem2393592 (@lem2393602)). Qed.
Lemma lem2393605 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393606 : term240 = term241.
Proof. exact (@lem2393605 (NUMERAL 0) term154). Qed.
Lemma lem2393607 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393608 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393609 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393608 h1) (fun h1 : term241 = True => @lem2393607)). Qed.
Lemma lem2393610 : term241 = True.
Proof. exact (EQ_MP (@lem2393609) (@lem2393607)). Qed.
Lemma lem2393611 : term240 = True.
Proof. exact (TRANS (@lem2393606) (@lem2393610)). Qed.
Lemma lem2393612 : True = term240.
Proof. exact (SYM (@lem2393611)). Qed.
Lemma lem2393613 : term240.
Proof. exact (EQ_MP (@lem2393612) (@lem0)). Qed.
Lemma lem2393614 : term534 = term537.
Proof. exact (@lem2393603 (@lem2393613)). Qed.
Lemma lem2393616 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393617 : term192 = term193.
Proof. exact (@lem2393616 term154 term154). Qed.
Lemma lem2393618 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393619 : term195 = term154.
Proof. exact (EQ_MP (@lem2393618) (@lem940073)). Qed.
Lemma lem2393620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393621 : term193 = term153.
Proof. exact (MK_COMB (@lem2393620) (@lem2393619)). Qed.
Lemma lem2393622 : term192 = term153.
Proof. exact (TRANS (@lem2393617) (@lem2393621)). Qed.
Lemma lem2393624 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393625 : term251 = term120.
Proof. exact (@lem2393624 term154). Qed.
Lemma lem2393626 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2393627 : term538 = term532.
Proof. exact (MK_COMB (@lem2393626) (@lem2393625)). Qed.
Lemma lem2393628 : term537 = term240.
Proof. exact (MK_COMB (@lem2393627) (@lem2393622)). Qed.
Lemma lem2393630 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393631 : term240 = term241.
Proof. exact (@lem2393630 (NUMERAL 0) term154). Qed.
Lemma lem2393632 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393633 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393634 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393633 h1) (fun h1 : term241 = True => @lem2393632)). Qed.
Lemma lem2393635 : term241 = True.
Proof. exact (EQ_MP (@lem2393634) (@lem2393632)). Qed.
Lemma lem2393636 : term240 = True.
Proof. exact (TRANS (@lem2393631) (@lem2393635)). Qed.
Lemma lem2393637 : term537 = True.
Proof. exact (TRANS (@lem2393628) (@lem2393636)). Qed.
Lemma lem2393638 : term534 = True.
Proof. exact (TRANS (@lem2393614) (@lem2393637)). Qed.
Lemma lem2393639 : term240 = True.
Proof. exact (TRANS (@lem2393591) (@lem2393638)). Qed.
Lemma lem2393640 : term531 = True.
Proof. exact (TRANS (@lem2393582) (@lem2393639)). Qed.
Lemma lem2393641 : True = term531.
Proof. exact (SYM (@lem2393640)). Qed.
Lemma lem2393642 : term531.
Proof. exact (EQ_MP (@lem2393641) (@lem0)). Qed.
Lemma lem2393643 (m : int) (n : int) (h1 : term526 m n) : term595 m n.
Proof. exact (conj (@lem2393642) (@lem2393574 m n h1)). Qed.
Lemma lem2393645 (x : real) (y : real) : term540 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2393646 (m : int) (n : int) : term596 m n.
Proof. exact (@lem2393645 term153 (term410 m n)). Qed.
Lemma lem2393647 (m : int) (n : int) (h1 : term526 m n) : term597 m n.
Proof. exact (@lem2393646 m n (@lem2393643 m n h1)). Qed.
Lemma lem2393648 (m : int) (n : int) : (term598 m n) = (term410 m n).
Proof. exact (@lem1982733 (term410 m n)). Qed.
Lemma lem2393649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2393650 (m : int) (n : int) : (term599 m n) = (term412 m n).
Proof. exact (MK_COMB (@lem2393649) (@lem2393648 m n)). Qed.
Lemma lem2393651 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2393652 (m : int) (n : int) : (term597 m n) = (term413 m n).
Proof. exact (MK_COMB (@lem2393650 m n) (@lem2393651)). Qed.
Lemma lem2393653 (m : int) (n : int) (h1 : term526 m n) : term413 m n.
Proof. exact (EQ_MP (@lem2393652 m n) (@lem2393647 m n h1)). Qed.
Lemma lem2393655 (y : real) : term545 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2393656 (m : int) (n : int) : term546 m n.
Proof. exact (@lem2393655 (term375 m n)). Qed.
Lemma lem2393657 (m : int) (n : int) (h1 : term526 m n) : term547 m n.
Proof. exact (@lem2393656 m n (@lem2393578 m n h1)). Qed.
Lemma lem2393658 (m : int) (n : int) (h1 : term526 m n) : term600 m n.
Proof. exact (@lem2393657 m n h1 term153). Qed.
Lemma lem2393659 (m : int) (n : int) : (term600 m n) = ((term601 m n) = term120).
Proof. exact (eq_refl (term600 m n)). Qed.
Lemma lem2393660 (m : int) (n : int) (h1 : term526 m n) : (term601 m n) = term120.
Proof. exact (EQ_MP (@lem2393659 m n) (@lem2393658 m n h1)). Qed.
Lemma lem2393661 (m : int) (n : int) : (term601 m n) = (term375 m n).
Proof. exact (@lem1982733 (term375 m n)). Qed.
Lemma lem2393662 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2393663 (m : int) (n : int) : (term602 m n) = (term379 m n).
Proof. exact (MK_COMB (@lem2393662) (@lem2393661 m n)). Qed.
Lemma lem2393664 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2393665 (m : int) (n : int) : ((term601 m n) = term120) = ((term375 m n) = term120).
Proof. exact (MK_COMB (@lem2393663 m n) (@lem2393664)). Qed.
Lemma lem2393666 (m : int) (n : int) (h1 : term526 m n) : (term375 m n) = term120.
Proof. exact (EQ_MP (@lem2393665 m n) (@lem2393660 m n h1)). Qed.
Lemma lem2393667 (m : int) (n : int) (h1 : term526 m n) : term603 m n.
Proof. exact (conj (@lem2393666 m n h1) (@lem2393653 m n h1)). Qed.
Lemma lem2393669 (x : real) (y : real) : term574 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2393670 (m : int) (n : int) : term604 m n.
Proof. exact (@lem2393669 (term375 m n) (term410 m n)). Qed.
Lemma lem2393671 (m : int) (n : int) (h1 : term526 m n) : term605 m n.
Proof. exact (@lem2393670 m n (@lem2393667 m n h1)). Qed.
Lemma lem2393672 (m : int) (n : int) : (term606 m n) = (term607 m n).
Proof. exact (@lem1982753 (term376 m n) (term366 m n) (term551 m n) (term409 m n)). Qed.
Lemma lem2393673 (m : int) (n : int) : (term608 m n) = (term581 m n).
Proof. exact (@lem1982713 term183 (term366 m n)). Qed.
Lemma lem2393675 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393676 : term153 = term219.
Proof. exact (@lem2393675 term154). Qed.
Lemma lem2393678 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2393679 : term183 = term184.
Proof. exact (@lem2393678 term154). Qed.
Lemma lem2393680 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393681 : term234 = term235.
Proof. exact (MK_COMB (@lem2393680) (@lem2393679)). Qed.
Lemma lem2393682 : term236 = term237.
Proof. exact (MK_COMB (@lem2393681) (@lem2393676)). Qed.
Lemma lem2393683 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2393685 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393686 : term240 = term241.
Proof. exact (@lem2393685 (NUMERAL 0) term154). Qed.
Lemma lem2393687 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393688 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393689 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393688 h1) (fun h1 : term241 = True => @lem2393687)). Qed.
Lemma lem2393690 : term241 = True.
Proof. exact (EQ_MP (@lem2393689) (@lem2393687)). Qed.
Lemma lem2393691 : term240 = True.
Proof. exact (TRANS (@lem2393686) (@lem2393690)). Qed.
Lemma lem2393692 : True = term240.
Proof. exact (SYM (@lem2393691)). Qed.
Lemma lem2393693 : term240.
Proof. exact (EQ_MP (@lem2393692) (@lem0)). Qed.
Lemma lem2393694 : term243.
Proof. exact (@lem2393683 (@lem2393693)). Qed.
Lemma lem2393696 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393697 : term240 = term241.
Proof. exact (@lem2393696 (NUMERAL 0) term154). Qed.
Lemma lem2393698 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393699 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393700 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393699 h1) (fun h1 : term241 = True => @lem2393698)). Qed.
Lemma lem2393701 : term241 = True.
Proof. exact (EQ_MP (@lem2393700) (@lem2393698)). Qed.
Lemma lem2393702 : term240 = True.
Proof. exact (TRANS (@lem2393697) (@lem2393701)). Qed.
Lemma lem2393703 : True = term240.
Proof. exact (SYM (@lem2393702)). Qed.
Lemma lem2393704 : term240.
Proof. exact (EQ_MP (@lem2393703) (@lem0)). Qed.
Lemma lem2393705 : term244.
Proof. exact (@lem2393694 (@lem2393704)). Qed.
Lemma lem2393707 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393708 : term240 = term241.
Proof. exact (@lem2393707 (NUMERAL 0) term154). Qed.
Lemma lem2393709 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393710 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393711 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393710 h1) (fun h1 : term241 = True => @lem2393709)). Qed.
Lemma lem2393712 : term241 = True.
Proof. exact (EQ_MP (@lem2393711) (@lem2393709)). Qed.
Lemma lem2393713 : term240 = True.
Proof. exact (TRANS (@lem2393708) (@lem2393712)). Qed.
Lemma lem2393714 : True = term240.
Proof. exact (SYM (@lem2393713)). Qed.
Lemma lem2393715 : term240.
Proof. exact (EQ_MP (@lem2393714) (@lem0)). Qed.
Lemma lem2393716 : term245.
Proof. exact (@lem2393705 (@lem2393715)). Qed.
Lemma lem2393718 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393719 : term192 = term193.
Proof. exact (@lem2393718 term154 term154). Qed.
Lemma lem2393720 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393721 : term195 = term154.
Proof. exact (EQ_MP (@lem2393720) (@lem940073)). Qed.
Lemma lem2393722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393723 : term193 = term153.
Proof. exact (MK_COMB (@lem2393722) (@lem2393721)). Qed.
Lemma lem2393724 : term192 = term153.
Proof. exact (TRANS (@lem2393719) (@lem2393723)). Qed.
Lemma lem2393726 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393727 : term220 = term225.
Proof. exact (@lem2393726 term154 term154). Qed.
Lemma lem2393728 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393729 : term195 = term154.
Proof. exact (EQ_MP (@lem2393728) (@lem940073)). Qed.
Lemma lem2393730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393731 : term193 = term153.
Proof. exact (MK_COMB (@lem2393730) (@lem2393729)). Qed.
Lemma lem2393732 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393733 : term225 = term183.
Proof. exact (MK_COMB (@lem2393732) (@lem2393731)). Qed.
Lemma lem2393734 : term220 = term183.
Proof. exact (TRANS (@lem2393727) (@lem2393733)). Qed.
Lemma lem2393735 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393736 : term246 = term234.
Proof. exact (MK_COMB (@lem2393735) (@lem2393734)). Qed.
Lemma lem2393737 : term247 = term236.
Proof. exact (MK_COMB (@lem2393736) (@lem2393724)). Qed.
Lemma lem2393739 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2393740 : term236 = term120.
Proof. exact (@lem2393739 term154). Qed.
Lemma lem2393741 : term247 = term120.
Proof. exact (TRANS (@lem2393737) (@lem2393740)). Qed.
Lemma lem2393742 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393743 : term249 = term145.
Proof. exact (MK_COMB (@lem2393742) (@lem2393741)). Qed.
Lemma lem2393744 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2393745 : term250 = term251.
Proof. exact (MK_COMB (@lem2393743) (@lem2393744)). Qed.
Lemma lem2393747 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393748 : term251 = term120.
Proof. exact (@lem2393747 term154). Qed.
Lemma lem2393749 : term250 = term120.
Proof. exact (TRANS (@lem2393745) (@lem2393748)). Qed.
Lemma lem2393751 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393752 : term192 = term193.
Proof. exact (@lem2393751 term154 term154). Qed.
Lemma lem2393753 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393754 : term195 = term154.
Proof. exact (EQ_MP (@lem2393753) (@lem940073)). Qed.
Lemma lem2393755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393756 : term193 = term153.
Proof. exact (MK_COMB (@lem2393755) (@lem2393754)). Qed.
Lemma lem2393757 : term192 = term153.
Proof. exact (TRANS (@lem2393752) (@lem2393756)). Qed.
Lemma lem2393758 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2393759 : term253 = term251.
Proof. exact (MK_COMB (@lem2393758) (@lem2393757)). Qed.
Lemma lem2393761 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393762 : term251 = term120.
Proof. exact (@lem2393761 term154). Qed.
Lemma lem2393763 : term253 = term120.
Proof. exact (TRANS (@lem2393759) (@lem2393762)). Qed.
Lemma lem2393764 : term120 = term253.
Proof. exact (SYM (@lem2393763)). Qed.
Lemma lem2393765 : term250 = term253.
Proof. exact (TRANS (@lem2393749) (@lem2393764)). Qed.
Lemma lem2393766 : term237 = term180.
Proof. exact (@lem2393716 (@lem2393765)). Qed.
Lemma lem2393767 : term236 = term180.
Proof. exact (TRANS (@lem2393682) (@lem2393766)). Qed.
Lemma lem2393769 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2393770 : term180 = term120.
Proof. exact (@lem2393769 term120). Qed.
Lemma lem2393771 : term236 = term120.
Proof. exact (TRANS (@lem2393767) (@lem2393770)). Qed.
Lemma lem2393772 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393773 : term254 = term145.
Proof. exact (MK_COMB (@lem2393772) (@lem2393771)). Qed.
Lemma lem2393774 (m : int) (n : int) : (term366 m n) = (term366 m n).
Proof. exact (eq_refl (term366 m n)). Qed.
Lemma lem2393775 (m : int) (n : int) : (term581 m n) = (term582 m n).
Proof. exact (MK_COMB (@lem2393773) (@lem2393774 m n)). Qed.
Lemma lem2393776 (m : int) (n : int) : (term608 m n) = (term582 m n).
Proof. exact (TRANS (@lem2393673 m n) (@lem2393775 m n)). Qed.
Lemma lem2393777 (m : int) (n : int) : (term582 m n) = term120.
Proof. exact (@lem1982719 (term366 m n)). Qed.
Lemma lem2393778 (m : int) (n : int) : (term608 m n) = term120.
Proof. exact (TRANS (@lem2393776 m n) (@lem2393777 m n)). Qed.
Lemma lem2393779 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393780 (m : int) (n : int) : (term609 m n) = term211.
Proof. exact (MK_COMB (@lem2393779) (@lem2393778 m n)). Qed.
Lemma lem2393781 (m : int) (n : int) : (term610 m n) = (term611 m n).
Proof. exact (@lem1982753 (real_of_int m) (term206 m) (term377 m n) (term612 m n)). Qed.
Lemma lem2393782 (m : int) : (term232 m) = (term233 m).
Proof. exact (@lem1982715 term183 (real_of_int m)). Qed.
Lemma lem2393784 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393785 : term153 = term219.
Proof. exact (@lem2393784 term154). Qed.
Lemma lem2393787 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2393788 : term183 = term184.
Proof. exact (@lem2393787 term154). Qed.
Lemma lem2393789 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393790 : term234 = term235.
Proof. exact (MK_COMB (@lem2393789) (@lem2393788)). Qed.
Lemma lem2393791 : term236 = term237.
Proof. exact (MK_COMB (@lem2393790) (@lem2393785)). Qed.
Lemma lem2393792 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2393794 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393795 : term240 = term241.
Proof. exact (@lem2393794 (NUMERAL 0) term154). Qed.
Lemma lem2393796 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393797 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393798 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393797 h1) (fun h1 : term241 = True => @lem2393796)). Qed.
Lemma lem2393799 : term241 = True.
Proof. exact (EQ_MP (@lem2393798) (@lem2393796)). Qed.
Lemma lem2393800 : term240 = True.
Proof. exact (TRANS (@lem2393795) (@lem2393799)). Qed.
Lemma lem2393801 : True = term240.
Proof. exact (SYM (@lem2393800)). Qed.
Lemma lem2393802 : term240.
Proof. exact (EQ_MP (@lem2393801) (@lem0)). Qed.
Lemma lem2393803 : term243.
Proof. exact (@lem2393792 (@lem2393802)). Qed.
Lemma lem2393805 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393806 : term240 = term241.
Proof. exact (@lem2393805 (NUMERAL 0) term154). Qed.
Lemma lem2393807 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393808 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393809 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393808 h1) (fun h1 : term241 = True => @lem2393807)). Qed.
Lemma lem2393810 : term241 = True.
Proof. exact (EQ_MP (@lem2393809) (@lem2393807)). Qed.
Lemma lem2393811 : term240 = True.
Proof. exact (TRANS (@lem2393806) (@lem2393810)). Qed.
Lemma lem2393812 : True = term240.
Proof. exact (SYM (@lem2393811)). Qed.
Lemma lem2393813 : term240.
Proof. exact (EQ_MP (@lem2393812) (@lem0)). Qed.
Lemma lem2393814 : term244.
Proof. exact (@lem2393803 (@lem2393813)). Qed.
Lemma lem2393816 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393817 : term240 = term241.
Proof. exact (@lem2393816 (NUMERAL 0) term154). Qed.
Lemma lem2393818 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393819 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393820 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393819 h1) (fun h1 : term241 = True => @lem2393818)). Qed.
Lemma lem2393821 : term241 = True.
Proof. exact (EQ_MP (@lem2393820) (@lem2393818)). Qed.
Lemma lem2393822 : term240 = True.
Proof. exact (TRANS (@lem2393817) (@lem2393821)). Qed.
Lemma lem2393823 : True = term240.
Proof. exact (SYM (@lem2393822)). Qed.
Lemma lem2393824 : term240.
Proof. exact (EQ_MP (@lem2393823) (@lem0)). Qed.
Lemma lem2393825 : term245.
Proof. exact (@lem2393814 (@lem2393824)). Qed.
Lemma lem2393827 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393828 : term192 = term193.
Proof. exact (@lem2393827 term154 term154). Qed.
Lemma lem2393829 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393830 : term195 = term154.
Proof. exact (EQ_MP (@lem2393829) (@lem940073)). Qed.
Lemma lem2393831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393832 : term193 = term153.
Proof. exact (MK_COMB (@lem2393831) (@lem2393830)). Qed.
Lemma lem2393833 : term192 = term153.
Proof. exact (TRANS (@lem2393828) (@lem2393832)). Qed.
Lemma lem2393835 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393836 : term220 = term225.
Proof. exact (@lem2393835 term154 term154). Qed.
Lemma lem2393837 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393838 : term195 = term154.
Proof. exact (EQ_MP (@lem2393837) (@lem940073)). Qed.
Lemma lem2393839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393840 : term193 = term153.
Proof. exact (MK_COMB (@lem2393839) (@lem2393838)). Qed.
Lemma lem2393841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393842 : term225 = term183.
Proof. exact (MK_COMB (@lem2393841) (@lem2393840)). Qed.
Lemma lem2393843 : term220 = term183.
Proof. exact (TRANS (@lem2393836) (@lem2393842)). Qed.
Lemma lem2393844 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393845 : term246 = term234.
Proof. exact (MK_COMB (@lem2393844) (@lem2393843)). Qed.
Lemma lem2393846 : term247 = term236.
Proof. exact (MK_COMB (@lem2393845) (@lem2393833)). Qed.
Lemma lem2393848 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2393849 : term236 = term120.
Proof. exact (@lem2393848 term154). Qed.
Lemma lem2393850 : term247 = term120.
Proof. exact (TRANS (@lem2393846) (@lem2393849)). Qed.
Lemma lem2393851 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393852 : term249 = term145.
Proof. exact (MK_COMB (@lem2393851) (@lem2393850)). Qed.
Lemma lem2393853 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2393854 : term250 = term251.
Proof. exact (MK_COMB (@lem2393852) (@lem2393853)). Qed.
Lemma lem2393856 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393857 : term251 = term120.
Proof. exact (@lem2393856 term154). Qed.
Lemma lem2393858 : term250 = term120.
Proof. exact (TRANS (@lem2393854) (@lem2393857)). Qed.
Lemma lem2393860 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393861 : term192 = term193.
Proof. exact (@lem2393860 term154 term154). Qed.
Lemma lem2393862 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393863 : term195 = term154.
Proof. exact (EQ_MP (@lem2393862) (@lem940073)). Qed.
Lemma lem2393864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393865 : term193 = term153.
Proof. exact (MK_COMB (@lem2393864) (@lem2393863)). Qed.
Lemma lem2393866 : term192 = term153.
Proof. exact (TRANS (@lem2393861) (@lem2393865)). Qed.
Lemma lem2393867 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2393868 : term253 = term251.
Proof. exact (MK_COMB (@lem2393867) (@lem2393866)). Qed.
Lemma lem2393870 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393871 : term251 = term120.
Proof. exact (@lem2393870 term154). Qed.
Lemma lem2393872 : term253 = term120.
Proof. exact (TRANS (@lem2393868) (@lem2393871)). Qed.
Lemma lem2393873 : term120 = term253.
Proof. exact (SYM (@lem2393872)). Qed.
Lemma lem2393874 : term250 = term253.
Proof. exact (TRANS (@lem2393858) (@lem2393873)). Qed.
Lemma lem2393875 : term237 = term180.
Proof. exact (@lem2393825 (@lem2393874)). Qed.
Lemma lem2393876 : term236 = term180.
Proof. exact (TRANS (@lem2393791) (@lem2393875)). Qed.
Lemma lem2393878 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2393879 : term180 = term120.
Proof. exact (@lem2393878 term120). Qed.
Lemma lem2393880 : term236 = term120.
Proof. exact (TRANS (@lem2393876) (@lem2393879)). Qed.
Lemma lem2393881 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393882 : term254 = term145.
Proof. exact (MK_COMB (@lem2393881) (@lem2393880)). Qed.
Lemma lem2393883 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2393884 (m : int) : (term233 m) = (term255 m).
Proof. exact (MK_COMB (@lem2393882) (@lem2393883 m)). Qed.
Lemma lem2393885 (m : int) : (term232 m) = (term255 m).
Proof. exact (TRANS (@lem2393782 m) (@lem2393884 m)). Qed.
Lemma lem2393886 (m : int) : (term255 m) = term120.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2393887 (m : int) : (term232 m) = term120.
Proof. exact (TRANS (@lem2393885 m) (@lem2393886 m)). Qed.
Lemma lem2393888 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393889 (m : int) : (term256 m) = term211.
Proof. exact (MK_COMB (@lem2393888) (@lem2393887 m)). Qed.
Lemma lem2393890 (m : int) (n : int) : (term613 m n) = (term614 m n).
Proof. exact (@lem1982763 (term377 m n) (term292 m n) term183). Qed.
Lemma lem2393891 (m : int) (n : int) : (term615 m n) = (term591 m n).
Proof. exact (@lem1982713 term183 (term292 m n)). Qed.
Lemma lem2393893 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2393894 : term153 = term219.
Proof. exact (@lem2393893 term154). Qed.
Lemma lem2393896 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2393897 : term183 = term184.
Proof. exact (@lem2393896 term154). Qed.
Lemma lem2393898 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393899 : term234 = term235.
Proof. exact (MK_COMB (@lem2393898) (@lem2393897)). Qed.
Lemma lem2393900 : term236 = term237.
Proof. exact (MK_COMB (@lem2393899) (@lem2393894)). Qed.
Lemma lem2393901 : term238.
Proof. exact (@lem1981473 term183 term153 term153 term153 term120 term153). Qed.
Lemma lem2393903 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393904 : term240 = term241.
Proof. exact (@lem2393903 (NUMERAL 0) term154). Qed.
Lemma lem2393905 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393906 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393907 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393906 h1) (fun h1 : term241 = True => @lem2393905)). Qed.
Lemma lem2393908 : term241 = True.
Proof. exact (EQ_MP (@lem2393907) (@lem2393905)). Qed.
Lemma lem2393909 : term240 = True.
Proof. exact (TRANS (@lem2393904) (@lem2393908)). Qed.
Lemma lem2393910 : True = term240.
Proof. exact (SYM (@lem2393909)). Qed.
Lemma lem2393911 : term240.
Proof. exact (EQ_MP (@lem2393910) (@lem0)). Qed.
Lemma lem2393912 : term243.
Proof. exact (@lem2393901 (@lem2393911)). Qed.
Lemma lem2393914 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393915 : term240 = term241.
Proof. exact (@lem2393914 (NUMERAL 0) term154). Qed.
Lemma lem2393916 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393917 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393918 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393917 h1) (fun h1 : term241 = True => @lem2393916)). Qed.
Lemma lem2393919 : term241 = True.
Proof. exact (EQ_MP (@lem2393918) (@lem2393916)). Qed.
Lemma lem2393920 : term240 = True.
Proof. exact (TRANS (@lem2393915) (@lem2393919)). Qed.
Lemma lem2393921 : True = term240.
Proof. exact (SYM (@lem2393920)). Qed.
Lemma lem2393922 : term240.
Proof. exact (EQ_MP (@lem2393921) (@lem0)). Qed.
Lemma lem2393923 : term244.
Proof. exact (@lem2393912 (@lem2393922)). Qed.
Lemma lem2393925 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2393926 : term240 = term241.
Proof. exact (@lem2393925 (NUMERAL 0) term154). Qed.
Lemma lem2393927 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2393928 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2393929 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2393928 h1) (fun h1 : term241 = True => @lem2393927)). Qed.
Lemma lem2393930 : term241 = True.
Proof. exact (EQ_MP (@lem2393929) (@lem2393927)). Qed.
Lemma lem2393931 : term240 = True.
Proof. exact (TRANS (@lem2393926) (@lem2393930)). Qed.
Lemma lem2393932 : True = term240.
Proof. exact (SYM (@lem2393931)). Qed.
Lemma lem2393933 : term240.
Proof. exact (EQ_MP (@lem2393932) (@lem0)). Qed.
Lemma lem2393934 : term245.
Proof. exact (@lem2393923 (@lem2393933)). Qed.
Lemma lem2393936 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393937 : term192 = term193.
Proof. exact (@lem2393936 term154 term154). Qed.
Lemma lem2393938 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393939 : term195 = term154.
Proof. exact (EQ_MP (@lem2393938) (@lem940073)). Qed.
Lemma lem2393940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393941 : term193 = term153.
Proof. exact (MK_COMB (@lem2393940) (@lem2393939)). Qed.
Lemma lem2393942 : term192 = term153.
Proof. exact (TRANS (@lem2393937) (@lem2393941)). Qed.
Lemma lem2393944 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2393945 : term220 = term225.
Proof. exact (@lem2393944 term154 term154). Qed.
Lemma lem2393946 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393947 : term195 = term154.
Proof. exact (EQ_MP (@lem2393946) (@lem940073)). Qed.
Lemma lem2393948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393949 : term193 = term153.
Proof. exact (MK_COMB (@lem2393948) (@lem2393947)). Qed.
Lemma lem2393950 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2393951 : term225 = term183.
Proof. exact (MK_COMB (@lem2393950) (@lem2393949)). Qed.
Lemma lem2393952 : term220 = term183.
Proof. exact (TRANS (@lem2393945) (@lem2393951)). Qed.
Lemma lem2393953 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393954 : term246 = term234.
Proof. exact (MK_COMB (@lem2393953) (@lem2393952)). Qed.
Lemma lem2393955 : term247 = term236.
Proof. exact (MK_COMB (@lem2393954) (@lem2393942)). Qed.
Lemma lem2393957 (m : nat) : (term248 m) = term120.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2393958 : term236 = term120.
Proof. exact (@lem2393957 term154). Qed.
Lemma lem2393959 : term247 = term120.
Proof. exact (TRANS (@lem2393955) (@lem2393958)). Qed.
Lemma lem2393960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393961 : term249 = term145.
Proof. exact (MK_COMB (@lem2393960) (@lem2393959)). Qed.
Lemma lem2393962 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem2393963 : term250 = term251.
Proof. exact (MK_COMB (@lem2393961) (@lem2393962)). Qed.
Lemma lem2393965 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393966 : term251 = term120.
Proof. exact (@lem2393965 term154). Qed.
Lemma lem2393967 : term250 = term120.
Proof. exact (TRANS (@lem2393963) (@lem2393966)). Qed.
Lemma lem2393969 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2393970 : term192 = term193.
Proof. exact (@lem2393969 term154 term154). Qed.
Lemma lem2393971 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2393972 : term195 = term154.
Proof. exact (EQ_MP (@lem2393971) (@lem940073)). Qed.
Lemma lem2393973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2393974 : term193 = term153.
Proof. exact (MK_COMB (@lem2393973) (@lem2393972)). Qed.
Lemma lem2393975 : term192 = term153.
Proof. exact (TRANS (@lem2393970) (@lem2393974)). Qed.
Lemma lem2393976 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem2393977 : term253 = term251.
Proof. exact (MK_COMB (@lem2393976) (@lem2393975)). Qed.
Lemma lem2393979 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2393980 : term251 = term120.
Proof. exact (@lem2393979 term154). Qed.
Lemma lem2393981 : term253 = term120.
Proof. exact (TRANS (@lem2393977) (@lem2393980)). Qed.
Lemma lem2393982 : term120 = term253.
Proof. exact (SYM (@lem2393981)). Qed.
Lemma lem2393983 : term250 = term253.
Proof. exact (TRANS (@lem2393967) (@lem2393982)). Qed.
Lemma lem2393984 : term237 = term180.
Proof. exact (@lem2393934 (@lem2393983)). Qed.
Lemma lem2393985 : term236 = term180.
Proof. exact (TRANS (@lem2393900) (@lem2393984)). Qed.
Lemma lem2393987 (x : real) : (term199 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2393988 : term180 = term120.
Proof. exact (@lem2393987 term120). Qed.
Lemma lem2393989 : term236 = term120.
Proof. exact (TRANS (@lem2393985) (@lem2393988)). Qed.
Lemma lem2393990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2393991 : term254 = term145.
Proof. exact (MK_COMB (@lem2393990) (@lem2393989)). Qed.
Lemma lem2393992 (m : int) (n : int) : (term292 m n) = (term292 m n).
Proof. exact (eq_refl (term292 m n)). Qed.
Lemma lem2393993 (m : int) (n : int) : (term591 m n) = (term592 m n).
Proof. exact (MK_COMB (@lem2393991) (@lem2393992 m n)). Qed.
Lemma lem2393994 (m : int) (n : int) : (term615 m n) = (term592 m n).
Proof. exact (TRANS (@lem2393891 m n) (@lem2393993 m n)). Qed.
Lemma lem2393995 (m : int) (n : int) : (term592 m n) = term120.
Proof. exact (@lem1982719 (term292 m n)). Qed.
Lemma lem2393996 (m : int) (n : int) : (term615 m n) = term120.
Proof. exact (TRANS (@lem2393994 m n) (@lem2393995 m n)). Qed.
Lemma lem2393997 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2393998 (m : int) (n : int) : (term616 m n) = term211.
Proof. exact (MK_COMB (@lem2393997) (@lem2393996 m n)). Qed.
Lemma lem2393999 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2394000 (m : int) (n : int) : (term614 m n) = term257.
Proof. exact (MK_COMB (@lem2393998 m n) (@lem2393999)). Qed.
Lemma lem2394001 (m : int) (n : int) : (term613 m n) = term257.
Proof. exact (TRANS (@lem2393890 m n) (@lem2394000 m n)). Qed.
Lemma lem2394002 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2394003 (m : int) (n : int) : (term613 m n) = term183.
Proof. exact (TRANS (@lem2394001 m n) (@lem2394002)). Qed.
Lemma lem2394004 (m : int) (n : int) : (term611 m n) = term257.
Proof. exact (MK_COMB (@lem2393889 m) (@lem2394003 m n)). Qed.
Lemma lem2394005 (m : int) (n : int) : (term610 m n) = term257.
Proof. exact (TRANS (@lem2393781 m n) (@lem2394004 m n)). Qed.
Lemma lem2394006 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2394007 (m : int) (n : int) : (term610 m n) = term183.
Proof. exact (TRANS (@lem2394005 m n) (@lem2394006)). Qed.
Lemma lem2394008 (m : int) (n : int) : (term607 m n) = term257.
Proof. exact (MK_COMB (@lem2393780 m n) (@lem2394007 m n)). Qed.
Lemma lem2394009 (m : int) (n : int) : (term606 m n) = term257.
Proof. exact (TRANS (@lem2393672 m n) (@lem2394008 m n)). Qed.
Lemma lem2394010 : term257 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2394011 (m : int) (n : int) : (term606 m n) = term183.
Proof. exact (TRANS (@lem2394009 m n) (@lem2394010)). Qed.
Lemma lem2394012 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2394013 (m : int) (n : int) : (term617 m n) = term259.
Proof. exact (MK_COMB (@lem2394012) (@lem2394011 m n)). Qed.
Lemma lem2394014 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem2394015 (m : int) (n : int) : (term605 m n) = term260.
Proof. exact (MK_COMB (@lem2394013 m n) (@lem2394014)). Qed.
Lemma lem2394016 (m : int) (n : int) (h1 : term526 m n) : term260.
Proof. exact (EQ_MP (@lem2394015 m n) (@lem2393671 m n h1)). Qed.
Lemma lem2394018 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2394019 : term260 = term271.
Proof. exact (@lem2394018 term120 term183). Qed.
Lemma lem2394021 (x : nat) : (term181 x) = (term182 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2394022 : term183 = term184.
Proof. exact (@lem2394021 term154). Qed.
Lemma lem2394024 (x : nat) : (real_of_num x) = (term179 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2394025 : term120 = term180.
Proof. exact (@lem2394024 (NUMERAL 0)). Qed.
Lemma lem2394026 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2394027 : term272 = term273.
Proof. exact (MK_COMB (@lem2394026) (@lem2394025)). Qed.
Lemma lem2394028 : term271 = term274.
Proof. exact (MK_COMB (@lem2394027) (@lem2394022)). Qed.
Lemma lem2394029 : term275.
Proof. exact (@lem1980026 term120 term153 term183 term153). Qed.
Lemma lem2394031 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2394032 : term240 = term241.
Proof. exact (@lem2394031 (NUMERAL 0) term154). Qed.
Lemma lem2394033 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2394034 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2394035 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2394034 h1) (fun h1 : term241 = True => @lem2394033)). Qed.
Lemma lem2394036 : term241 = True.
Proof. exact (EQ_MP (@lem2394035) (@lem2394033)). Qed.
Lemma lem2394037 : term240 = True.
Proof. exact (TRANS (@lem2394032) (@lem2394036)). Qed.
Lemma lem2394038 : True = term240.
Proof. exact (SYM (@lem2394037)). Qed.
Lemma lem2394039 : term240.
Proof. exact (EQ_MP (@lem2394038) (@lem0)). Qed.
Lemma lem2394040 : term276.
Proof. exact (@lem2394029 (@lem2394039)). Qed.
Lemma lem2394042 (m : nat) (n : nat) : (term239 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2394043 : term240 = term241.
Proof. exact (@lem2394042 (NUMERAL 0) term154). Qed.
Lemma lem2394044 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2394045 (h1 : term242 = (BIT1 0)) : term241 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2394046 : (term242 = (BIT1 0)) = (term241 = True).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2394045 h1) (fun h1 : term241 = True => @lem2394044)). Qed.
Lemma lem2394047 : term241 = True.
Proof. exact (EQ_MP (@lem2394046) (@lem2394044)). Qed.
Lemma lem2394048 : term240 = True.
Proof. exact (TRANS (@lem2394043) (@lem2394047)). Qed.
Lemma lem2394049 : True = term240.
Proof. exact (SYM (@lem2394048)). Qed.
Lemma lem2394050 : term240.
Proof. exact (EQ_MP (@lem2394049) (@lem0)). Qed.
Lemma lem2394051 : term274 = term277.
Proof. exact (@lem2394040 (@lem2394050)). Qed.
Lemma lem2394053 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2394054 : term220 = term225.
Proof. exact (@lem2394053 term154 term154). Qed.
Lemma lem2394055 : (term194 = (BIT1 0)) = (term195 = term154).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2394056 : term195 = term154.
Proof. exact (EQ_MP (@lem2394055) (@lem940073)). Qed.
Lemma lem2394057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2394058 : term193 = term153.
Proof. exact (MK_COMB (@lem2394057) (@lem2394056)). Qed.
Lemma lem2394059 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2394060 : term225 = term183.
Proof. exact (MK_COMB (@lem2394059) (@lem2394058)). Qed.
Lemma lem2394061 : term220 = term183.
Proof. exact (TRANS (@lem2394054) (@lem2394060)). Qed.
Lemma lem2394063 (x : nat) : (term252 x) = term120.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2394064 : term251 = term120.
Proof. exact (@lem2394063 term154). Qed.
Lemma lem2394065 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2394066 : term278 = term272.
Proof. exact (MK_COMB (@lem2394065) (@lem2394064)). Qed.
Lemma lem2394067 : term277 = term271.
Proof. exact (MK_COMB (@lem2394066) (@lem2394061)). Qed.
Lemma lem2394069 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2394070 : term271 = term281.
Proof. exact (@lem2394069 (NUMERAL 0) term154). Qed.
Lemma lem2394071 : term242 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2394072 (h1 : term242 = (BIT1 0)) : (term154 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2394073 : (term242 = (BIT1 0)) = ((term154 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term242 = (BIT1 0) => @lem2394072 h1) (fun h1 : (term154 = (NUMERAL 0)) = False => @lem2394071)). Qed.
Lemma lem2394074 : (term154 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2394073) (@lem2394071)). Qed.
Lemma lem2394075 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2394076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2394077 : term282 = (and True).
Proof. exact (MK_COMB (@lem2394076) (@lem2394075)). Qed.
Lemma lem2394078 : term281 = (True /\ False).
Proof. exact (MK_COMB (@lem2394077) (@lem2394074)). Qed.
Lemma lem2394080 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2394081 : term281 = False.
Proof. exact (TRANS (@lem2394078) (@lem2394080)). Qed.
Lemma lem2394082 : term271 = False.
Proof. exact (TRANS (@lem2394070) (@lem2394081)). Qed.
Lemma lem2394083 : term277 = False.
Proof. exact (TRANS (@lem2394067) (@lem2394082)). Qed.
Lemma lem2394084 : term274 = False.
Proof. exact (TRANS (@lem2394051) (@lem2394083)). Qed.
Lemma lem2394085 : term271 = False.
Proof. exact (TRANS (@lem2394028) (@lem2394084)). Qed.
Lemma lem2394086 : term260 = False.
Proof. exact (TRANS (@lem2394019) (@lem2394085)). Qed.
Lemma lem2394087 (m : int) (n : int) (h1 : term526 m n) : False.
Proof. exact (EQ_MP (@lem2394086) (@lem2394016 m n h1)). Qed.
Lemma lem2394088 (m : int) (n : int) (h1 : term527 m n) : False.
Proof. exact (or_elim (@lem2393053 m n h1) (fun h0 : term514 m n => @lem2393570 m n h0) (fun h0 : term526 m n => @lem2394087 m n h0)). Qed.
Lemma lem2394089 (m : int) (n : int) (h1 : term530 m n) : False.
Proof. exact (or_elim (@lem2391824 m n h1) (fun h0 : term502 m n => @lem2393052 m n h0) (fun h0 : term527 m n => @lem2394088 m n h0)). Qed.
Lemma lem2394090 (m : int) (n : int) (h1 : term418 m n) : term418 m n.
Proof. exact (h1). Qed.
Lemma lem2394091 (m : int) (n : int) (h1 : term418 m n) : term530 m n.
Proof. exact (EQ_MP (@lem2391823 m n) (@lem2394090 m n h1)). Qed.
Lemma lem2394092 (m : int) (n : int) (h1 : term418 m n) : (term530 m n) = False.
Proof. exact (prop_ext (fun h2 : term530 m n => @lem2394089 m n h2) (fun h2 : False => @lem2394091 m n h1)). Qed.
Lemma lem2394093 (m : int) (n : int) (h1 : term418 m n) : False.
Proof. exact (EQ_MP (@lem2394092 m n h1) (@lem2394091 m n h1)). Qed.
Lemma lem2394094 (m : int) (n : int) (h1 : term345 m n) : term345 m n.
Proof. exact (h1). Qed.
Lemma lem2394095 (m : int) (n : int) (h1 : term345 m n) : term418 m n.
Proof. exact (EQ_MP (@lem2391215 m n) (@lem2394094 m n h1)). Qed.
Lemma lem2394096 (m : int) (n : int) (h1 : term345 m n) : (term418 m n) = False.
Proof. exact (prop_ext (fun h2 : term418 m n => @lem2394093 m n h2) (fun h2 : False => @lem2394095 m n h1)). Qed.
Lemma lem2394097 (m : int) (n : int) (h1 : term345 m n) : False.
Proof. exact (EQ_MP (@lem2394096 m n h1) (@lem2394095 m n h1)). Qed.
Lemma lem2394098 (m : int) (n : int) : term618 m n.
Proof. exact (fun h0 : term345 m n => @lem2394097 m n h0). Qed.
Lemma lem2394099 (m : int) (n : int) : term619 m n.
Proof. exact (@lem1386578 (term620 m n)). Qed.
Lemma lem2394102 (m : int) (n : int) : term620 m n.
Proof. exact (@lem2394099 m n (@lem2394098 m n)). Qed.
Lemma lem2394103 (n : int) (m : int) : (term344 m n) = (term287 n m).
Proof. exact (SYM (@lem2390778 m n)). Qed.
Lemma lem2394104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2394105 (n : int) (m : int) : (term620 m n) = (term286 n m).
Proof. exact (MK_COMB (@lem2394104) (@lem2394103 n m)). Qed.
Lemma lem2394106 (n : int) (m : int) : term286 n m.
Proof. exact (EQ_MP (@lem2394105 n m) (@lem2394102 m n)). Qed.
Lemma lem2394110 (n : int) (m : int) : term69 n m.
Proof. exact (EQ_MP (@lem2390605 n m) (@lem2394106 n m)). Qed.
Lemma lem2394111 (n : int) (m : int) : term72 n m.
Proof. exact (fun h0 : term621 n => @lem2394110 n m). Qed.
Lemma lem2394112 (m : int) (n : int) (h1 : n = term66) : term74 n m.
Proof. exact (EQ_MP (@lem2389680 m n h1) (@lem2390604 m)). Qed.
Lemma lem2394113 (m : int) (n : int) (h1 : n = term66) : (n = term66) = (term74 n m).
Proof. exact (prop_ext (fun h2 : n = term66 => @lem2394112 m n h1) (fun h2 : term74 n m => @lem2389519 n h1)). Qed.
Lemma lem2394114 (m : int) (n : int) (h1 : n = term66) : term74 n m.
Proof. exact (EQ_MP (@lem2394113 m n h1) (@lem2389519 n h1)). Qed.
Lemma lem2394115 (n : int) (m : int) : term77 n m.
Proof. exact (fun h0 : n = term66 => @lem2394114 m n h0). Qed.
Lemma lem2394116 (n : int) (m : int) : term80 n m.
Proof. exact (conj (@lem2394115 n m) (@lem2394111 n m)). Qed.
Lemma lem2394117 (n : int) (m : int) : term44 n m.
Proof. exact (EQ_MP (@lem2389518 n m) (@lem2394116 n m)). Qed.
Lemma lem2394122 (m : int) : term48 m.
Proof. exact (fun n : int => @lem2394117 n m). Qed.
Lemma lem2394123 (m : int) : term16 m.
Proof. exact (@lem2389498 m (@lem2394122 m)). Qed.
Lemma lem2394128 : term20.
Proof. exact (fun m : int => @lem2394123 m). Qed.
Lemma lem2394129 : term32.
Proof. exact (@lem2389471 (@lem2394128)). Qed.
Lemma lem2394130 : term30.
Proof. exact (@lem2394129 (@lem2387577)). Qed.
