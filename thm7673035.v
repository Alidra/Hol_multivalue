Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7673035_term_abbrevs.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1011992_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
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
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem7670353 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7670354 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7670355 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7670354 m) (@lem7670353 m)). Qed.
Lemma lem7670356 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7670355 m n). Qed.
Lemma lem7670357 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7670358 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7670357 m n) (@lem7670356 m n)). Qed.
Lemma lem7670359 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7670358 m n p). Qed.
Lemma lem7670360 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7670363 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7670360 m p n) (@lem7670359 m n p)). Qed.
Lemma lem7670364 {A B : Type'} : (term7 A B) = (term8 A B).
Proof. exact (@lem7670363 term9 term9 (term10 A B)). Qed.
Lemma lem7670367 {A B : Type'} : (term8 A B) = (term7 A B).
Proof. exact (SYM (@lem7670364 A B)). Qed.
Lemma lem7670368 : term11 = True.
Proof. exact (@lem1011992 (BIT1 0)). Qed.
Lemma lem7670369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670370 : term12 = (and True).
Proof. exact (MK_COMB (@lem7670369) (@lem7670368)). Qed.
Lemma lem7670371 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (eq_refl (term13 A B)). Qed.
Lemma lem7670372 {A B : Type'} : (term8 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem7670370) (@lem7670371 A B)). Qed.
Lemma lem7670374 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7670375 {A B : Type'} : (term14 A B) = (term13 A B).
Proof. exact (@lem7670374 (term13 A B)). Qed.
Lemma lem7670376 {A B : Type'} : (term8 A B) = (term13 A B).
Proof. exact (TRANS (@lem7670372 A B) (@lem7670375 A B)). Qed.
Lemma lem7670380 {A B : Type'} (h1 : (term15 A B) = False) : (term15 A B) = False.
Proof. exact (h1). Qed.
Lemma lem7670381 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7670382 {A B : Type'} (h1 : (term15 A B) = False) : (term16 A B) = (@COND nat False).
Proof. exact (MK_COMB (@lem7670381) (@lem7670380 A B h1)). Qed.
Lemma lem7670383 {A B : Type'} : (term17 A B) = (term17 A B).
Proof. exact (eq_refl (term17 A B)). Qed.
Lemma lem7670384 {A B : Type'} (h1 : (term15 A B) = False) : (term18 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem7670382 A B h1) (@lem7670383 A B)). Qed.
Lemma lem7670385 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7670386 {A B : Type'} (h1 : (term15 A B) = False) : (term10 A B) = (term20 A B).
Proof. exact (MK_COMB (@lem7670384 A B h1) (@lem7670385)). Qed.
Lemma lem7670388 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7670389 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7670388 nat t1 t2). Qed.
Lemma lem7670390 {A B : Type'} : (term20 A B) = term9.
Proof. exact (@lem7670389 (term17 A B) term9). Qed.
Lemma lem7670391 {A B : Type'} (h1 : (term15 A B) = False) : (term10 A B) = term9.
Proof. exact (TRANS (@lem7670386 A B h1) (@lem7670390 A B)). Qed.
Lemma lem7670392 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7670393 {A B : Type'} (h1 : (term15 A B) = False) : (term13 A B) = term11.
Proof. exact (MK_COMB (@lem7670392) (@lem7670391 A B h1)). Qed.
Lemma lem7670394 {A B : Type'} : term22 A B.
Proof. exact (fun h0 : (term15 A B) = False => @lem7670393 A B h0). Qed.
Lemma lem7670396 {A B : Type'} (h1 : (term15 A B) = True) : (term15 A B) = True.
Proof. exact (h1). Qed.
Lemma lem7670397 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7670398 {A B : Type'} (h1 : (term15 A B) = True) : (term16 A B) = (@COND nat True).
Proof. exact (MK_COMB (@lem7670397) (@lem7670396 A B h1)). Qed.
Lemma lem7670399 {A B : Type'} : (term17 A B) = (term17 A B).
Proof. exact (eq_refl (term17 A B)). Qed.
Lemma lem7670400 {A B : Type'} (h1 : (term15 A B) = True) : (term18 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem7670398 A B h1) (@lem7670399 A B)). Qed.
Lemma lem7670401 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7670402 {A B : Type'} (h1 : (term15 A B) = True) : (term10 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem7670400 A B h1) (@lem7670401)). Qed.
Lemma lem7670404 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7670405 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7670404 nat t2 t1). Qed.
Lemma lem7670406 {A B : Type'} : (term24 A B) = (term17 A B).
Proof. exact (@lem7670405 term9 (term17 A B)). Qed.
Lemma lem7670407 {A B : Type'} (h1 : (term15 A B) = True) : (term10 A B) = (term17 A B).
Proof. exact (TRANS (@lem7670402 A B h1) (@lem7670406 A B)). Qed.
Lemma lem7670408 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7670409 {A B : Type'} (h1 : (term15 A B) = True) : (term13 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem7670408) (@lem7670407 A B h1)). Qed.
Lemma lem7670410 {A B : Type'} : term26 A B.
Proof. exact (fun h0 : (term15 A B) = True => @lem7670409 A B h0). Qed.
Lemma lem7670411 {A B : Type'} : term27 A B.
Proof. exact (conj (@lem7670394 A B) (@lem7670410 A B)). Qed.
Lemma lem7670413 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term28 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7670414 {A B : Type'} : term29 A B.
Proof. exact (@lem7670413 (term13 A B) (term25 A B) (term15 A B) term11). Qed.
Lemma lem7670447 {A B : Type'} : (term13 A B) = (term30 A B).
Proof. exact (@lem7670414 A B (@lem7670411 A B)). Qed.
Lemma lem7670462 {A B : Type'} : (term8 A B) = (term30 A B).
Proof. exact (TRANS (@lem7670376 A B) (@lem7670447 A B)). Qed.
Lemma lem7670463 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (@lem1032781 (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B)) (term33 A B)). Qed.
Lemma lem7670464 {A B : Type'} (d : nat) : (term34 A B d) = (term35 A B d).
Proof. exact (eq_refl (term34 A B d)). Qed.
Lemma lem7670465 {A B : Type'} (d : nat) : (term36 A B d) = (term36 A B d).
Proof. exact (eq_refl (term36 A B d)). Qed.
Lemma lem7670466 {A B : Type'} (d : nat) : (term37 A B d) = (term38 A B d).
Proof. exact (MK_COMB (@lem7670465 A B d) (@lem7670464 A B d)). Qed.
Lemma lem7670467 {A B : Type'} : (term39 A B) = (term40 A B).
Proof. exact (fun_ext (fun d : nat => @lem7670466 A B d)). Qed.
Lemma lem7670468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7670469 {A B : Type'} : (term32 A B) = (term41 A B).
Proof. exact (MK_COMB (@lem7670468) (@lem7670467 A B)). Qed.
Lemma lem7670470 {A B : Type'} : (term31 A B) = (term30 A B).
Proof. exact (eq_refl (term31 A B)). Qed.
Lemma lem7670471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7670472 {A B : Type'} : (term42 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem7670471) (@lem7670470 A B)). Qed.
Lemma lem7670473 {A B : Type'} : ((term31 A B) = (term32 A B)) = ((term30 A B) = (term41 A B)).
Proof. exact (MK_COMB (@lem7670472 A B) (@lem7670469 A B)). Qed.
Lemma lem7670474 {A B : Type'} : (term30 A B) = (term41 A B).
Proof. exact (EQ_MP (@lem7670473 A B) (@lem7670463 A B)). Qed.
Lemma lem7670475 {A B : Type'} (d : nat) : (term38 A B d) = (term38 A B d).
Proof. exact (eq_refl (term38 A B d)). Qed.
Lemma lem7670476 {A B : Type'} : (term40 A B) = (term40 A B).
Proof. exact (fun_ext (fun d : nat => @lem7670475 A B d)). Qed.
Lemma lem7670477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7670478 {A B : Type'} : (term41 A B) = (term41 A B).
Proof. exact (MK_COMB (@lem7670477) (@lem7670476 A B)). Qed.
Lemma lem7670479 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (eq_refl (term43 A B)). Qed.
Lemma lem7670480 {A B : Type'} : ((term30 A B) = (term41 A B)) = ((term30 A B) = (term41 A B)).
Proof. exact (MK_COMB (@lem7670479 A B) (@lem7670478 A B)). Qed.
Lemma lem7670481 {A B : Type'} : (term30 A B) = (term41 A B).
Proof. exact (EQ_MP (@lem7670480 A B) (@lem7670474 A B)). Qed.
Lemma lem7670482 {A B : Type'} : (term8 A B) = (term41 A B).
Proof. exact (TRANS (@lem7670462 A B) (@lem7670481 A B)). Qed.
Lemma lem7670493 : term11 = True.
Proof. exact (@lem1011992 (BIT1 0)). Qed.
Lemma lem7670494 {A B : Type'} : (term44 A B) = (term44 A B).
Proof. exact (eq_refl (term44 A B)). Qed.
Lemma lem7670495 {A B : Type'} : (term45 A B) = (term46 A B).
Proof. exact (MK_COMB (@lem7670494 A B) (@lem7670493)). Qed.
Lemma lem7670497 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7670498 {A B : Type'} : (term46 A B) = True.
Proof. exact (@lem7670497 (term15 A B)). Qed.
Lemma lem7670499 {A B : Type'} : (term45 A B) = True.
Proof. exact (TRANS (@lem7670495 A B) (@lem7670498 A B)). Qed.
Lemma lem7670500 {A B : Type'} (d : nat) : (term47 A B d) = (term47 A B d).
Proof. exact (eq_refl (term47 A B d)). Qed.
Lemma lem7670501 {A B : Type'} (d : nat) : (term35 A B d) = (term48 A B d).
Proof. exact (MK_COMB (@lem7670500 A B d) (@lem7670499 A B)). Qed.
Lemma lem7670503 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7670504 {A B : Type'} (d : nat) : (term48 A B d) = (term49 A B d).
Proof. exact (@lem7670503 (term49 A B d)). Qed.
Lemma lem7670507 {A B : Type'} (d : nat) : (term35 A B d) = (term49 A B d).
Proof. exact (TRANS (@lem7670501 A B d) (@lem7670504 A B d)). Qed.
Lemma lem7670508 {A B : Type'} (d : nat) : (term36 A B d) = (term36 A B d).
Proof. exact (eq_refl (term36 A B d)). Qed.
Lemma lem7670509 {A B : Type'} (d : nat) : (term38 A B d) = (term50 A B d).
Proof. exact (MK_COMB (@lem7670508 A B d) (@lem7670507 A B d)). Qed.
Lemma lem7670512 {A B : Type'} : (term40 A B) = (term51 A B).
Proof. exact (fun_ext (fun d : nat => @lem7670509 A B d)). Qed.
Lemma lem7670513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7670514 {A B : Type'} : (term41 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem7670513) (@lem7670512 A B)). Qed.
Lemma lem7670523 {A B : Type'} : (term8 A B) = (term52 A B).
Proof. exact (TRANS (@lem7670482 A B) (@lem7670514 A B)). Qed.
Lemma lem7670538 {A B : Type'} (d : nat) : (term49 A B d) = (term49 A B d).
Proof. exact (eq_refl (term49 A B d)). Qed.
Lemma lem7670555 {A B : Type'} (d : nat) : (term53 A B d) = (term53 A B d).
Proof. exact (eq_refl (term53 A B d)). Qed.
Lemma lem7670562 {B : Type'} (d : nat) : (term54 B d) = (term55 B d).
Proof. exact (@lem1032098 d (@dimindex B (@UNIV B))). Qed.
Lemma lem7670565 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (eq_refl (term56 A)). Qed.
Lemma lem7670566 {A B : Type'} (d : nat) : ((@dimindex A (@UNIV A)) = (term54 B d)) = ((@dimindex A (@UNIV A)) = (term55 B d)).
Proof. exact (MK_COMB (@lem7670565 A) (@lem7670562 B d)). Qed.
Lemma lem7670567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7670568 {A B : Type'} (d : nat) : (term57 A B d) = (term58 A B d).
Proof. exact (MK_COMB (@lem7670567) (@lem7670566 A B d)). Qed.
Lemma lem7670569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670570 {A B : Type'} (d : nat) : (term59 A B d) = (term60 A B d).
Proof. exact (MK_COMB (@lem7670569) (@lem7670568 A B d)). Qed.
Lemma lem7670571 {A B : Type'} (d : nat) : (term61 A B d) = (term62 A B d).
Proof. exact (MK_COMB (@lem7670570 A B d) (@lem7670555 A B d)). Qed.
Lemma lem7670572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7670573 {A B : Type'} (d : nat) : (term36 A B d) = (term63 A B d).
Proof. exact (MK_COMB (@lem7670572) (@lem7670571 A B d)). Qed.
Lemma lem7670574 {A B : Type'} (d : nat) : (term50 A B d) = (term64 A B d).
Proof. exact (MK_COMB (@lem7670573 A B d) (@lem7670538 A B d)). Qed.
Lemma lem7670575 {A B : Type'} : (term51 A B) = (term65 A B).
Proof. exact (fun_ext (fun d : nat => @lem7670574 A B d)). Qed.
Lemma lem7670576 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7670577 {A B : Type'} : (term52 A B) = (term66 A B).
Proof. exact (MK_COMB (@lem7670576) (@lem7670575 A B)). Qed.
Lemma lem7670580 {A B : Type'} : (term8 A B) = (term66 A B).
Proof. exact (TRANS (@lem7670523 A B) (@lem7670577 A B)). Qed.
Lemma lem7670582 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7670583 {A B : Type'} (d : nat) : ((@dimindex A (@UNIV A)) = (term55 B d)) = ((term67 A) = (term68 B d)).
Proof. exact (@lem7670582 (@dimindex A (@UNIV A)) (term55 B d)). Qed.
Lemma lem7670587 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7670588 {B : Type'} (d : nat) : (term68 B d) = (term71 B d).
Proof. exact (@lem7670587 d (@dimindex B (@UNIV B))). Qed.
Lemma lem7670589 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (eq_refl (term72 A)). Qed.
Lemma lem7670590 {A B : Type'} (d : nat) : ((term67 A) = (term68 B d)) = ((term67 A) = (term71 B d)).
Proof. exact (MK_COMB (@lem7670589 A) (@lem7670588 B d)). Qed.
Lemma lem7670591 {A B : Type'} (d : nat) : ((@dimindex A (@UNIV A)) = (term55 B d)) = ((term67 A) = (term71 B d)).
Proof. exact (TRANS (@lem7670583 A B d) (@lem7670590 A B d)). Qed.
Lemma lem7670592 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7670593 {A B : Type'} (d : nat) : (term58 A B d) = (term73 A B d).
Proof. exact (MK_COMB (@lem7670592) (@lem7670591 A B d)). Qed.
Lemma lem7670594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670595 {A B : Type'} (d : nat) : (term60 A B d) = (term74 A B d).
Proof. exact (MK_COMB (@lem7670594) (@lem7670593 A B d)). Qed.
Lemma lem7670597 (m : nat) (n : nat) : (Peano.lt m n) = (term75 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7670598 {A B : Type'} : (term76 A B) = (term77 A B).
Proof. exact (@lem7670597 (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))). Qed.
Lemma lem7670599 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7670600 {A B : Type'} : (term78 A B) = (term79 A B).
Proof. exact (MK_COMB (@lem7670599) (@lem7670598 A B)). Qed.
Lemma lem7670601 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7670602 {A B : Type'} : (term80 A B) = (term81 A B).
Proof. exact (MK_COMB (@lem7670601) (@lem7670600 A B)). Qed.
Lemma lem7670604 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7670605 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term82).
Proof. exact (@lem7670604 d (NUMERAL 0)). Qed.
Lemma lem7670608 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7670609 (d : nat) : (term83 d) = (term84 d).
Proof. exact (MK_COMB (@lem7670608) (@lem7670605 d)). Qed.
Lemma lem7670610 {A B : Type'} (d : nat) : (term53 A B d) = (term85 A B d).
Proof. exact (MK_COMB (@lem7670602 A B) (@lem7670609 d)). Qed.
Lemma lem7670611 {A B : Type'} (d : nat) : (term62 A B d) = (term86 A B d).
Proof. exact (MK_COMB (@lem7670595 A B d) (@lem7670610 A B d)). Qed.
Lemma lem7670612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7670613 {A B : Type'} (d : nat) : (term63 A B d) = (term87 A B d).
Proof. exact (MK_COMB (@lem7670612) (@lem7670611 A B d)). Qed.
Lemma lem7670615 (m : nat) (n : nat) : (Peano.lt m n) = (term75 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7670616 {A B : Type'} : (term15 A B) = (term88 A B).
Proof. exact (@lem7670615 (@dimindex B (@UNIV B)) (@dimindex A (@UNIV A))). Qed.
Lemma lem7670617 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7670618 {A B : Type'} : (term89 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem7670617) (@lem7670616 A B)). Qed.
Lemma lem7670619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7670620 {A B : Type'} : (term91 A B) = (term92 A B).
Proof. exact (MK_COMB (@lem7670619) (@lem7670618 A B)). Qed.
Lemma lem7670622 (m : nat) (n : nat) : (Peano.le m n) = (term93 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7670623 (d : nat) : (term94 d) = (term95 d).
Proof. exact (@lem7670622 term9 d). Qed.
Lemma lem7670624 {A B : Type'} (d : nat) : (term49 A B d) = (term96 A B d).
Proof. exact (MK_COMB (@lem7670620 A B) (@lem7670623 d)). Qed.
Lemma lem7670625 {A B : Type'} (d : nat) : (term64 A B d) = (term97 A B d).
Proof. exact (MK_COMB (@lem7670613 A B d) (@lem7670624 A B d)). Qed.
Lemma lem7670626 {A B : Type'} : (term65 A B) = (term98 A B).
Proof. exact (fun_ext (fun d : nat => @lem7670625 A B d)). Qed.
Lemma lem7670627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7670628 {A B : Type'} : (term66 A B) = (term99 A B).
Proof. exact (MK_COMB (@lem7670627) (@lem7670626 A B)). Qed.
Lemma lem7670629 {A B : Type'} : (term8 A B) = (term99 A B).
Proof. exact (TRANS (@lem7670580 A B) (@lem7670628 A B)). Qed.
Lemma lem7670630 (d : nat) : term100 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem7670631 (d : nat) : (term100 d) = (term101 d).
Proof. exact (eq_refl (term100 d)). Qed.
Lemma lem7670632 (d : nat) : term101 d.
Proof. exact (EQ_MP (@lem7670631 d) (@lem7670630 d)). Qed.
Lemma lem7670633 {A : Type'} : term102 A.
Proof. exact (@lem2307535 (@dimindex A (@UNIV A))). Qed.
Lemma lem7670634 {A : Type'} : (term102 A) = (term103 A).
Proof. exact (eq_refl (term102 A)). Qed.
Lemma lem7670635 {A : Type'} : term103 A.
Proof. exact (EQ_MP (@lem7670634 A) (@lem7670633 A)). Qed.
Lemma lem7670636 {B : Type'} : term102 B.
Proof. exact (@lem2307535 (@dimindex B (@UNIV B))). Qed.
Lemma lem7670637 {B : Type'} : (term102 B) = (term103 B).
Proof. exact (eq_refl (term102 B)). Qed.
Lemma lem7670638 {B : Type'} : term103 B.
Proof. exact (EQ_MP (@lem7670637 B) (@lem7670636 B)). Qed.
Lemma lem7670639 (_98799 : int) (_98798 : int) (_98797 : int) : (term104 _98799 _98798 _98797) = (term105 _98799 _98798 _98797).
Proof. exact (@lem2318604 (term105 _98799 _98798 _98797)). Qed.
Lemma lem7670664 (_98798 : int) (_98797 : int) (_98799 : int) : (term106 _98798 _98797 _98799) = (_98798 = (int_add _98797 _98799)).
Proof. exact (@lem16933 (_98798 = (int_add _98797 _98799))). Qed.
Lemma lem7670667 (_98798 : int) (_98799 : int) : (term107 _98798 _98799) = (int_lt _98798 _98799).
Proof. exact (@lem16933 (int_lt _98798 _98799)). Qed.
Lemma lem7670670 (_98797 : int) : (term108 _98797) = (_98797 = term82).
Proof. exact (@lem16933 (_98797 = term82)). Qed.
Lemma lem7670671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670672 (_98798 : int) (_98799 : int) : (term109 _98798 _98799) = (term110 _98798 _98799).
Proof. exact (MK_COMB (@lem7670671) (@lem7670667 _98798 _98799)). Qed.
Lemma lem7670673 (_98798 : int) (_98799 : int) (_98797 : int) : (term111 _98798 _98799 _98797) = (term112 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7670672 _98798 _98799) (@lem7670670 _98797)). Qed.
Lemma lem7670674 (_98798 : int) (_98799 : int) (_98797 : int) : (term113 _98798 _98799 _98797) = (term111 _98798 _98799 _98797).
Proof. exact (@lem17160 (term114 _98798 _98799) (term115 _98797)). Qed.
Lemma lem7670675 (_98798 : int) (_98799 : int) (_98797 : int) : (term113 _98798 _98799 _98797) = (term112 _98798 _98799 _98797).
Proof. exact (TRANS (@lem7670674 _98798 _98799 _98797) (@lem7670673 _98798 _98799 _98797)). Qed.
Lemma lem7670676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7670677 (_98798 : int) (_98797 : int) (_98799 : int) : (term116 _98798 _98797 _98799) = (term117 _98798 _98797 _98799).
Proof. exact (MK_COMB (@lem7670676) (@lem7670664 _98798 _98797 _98799)). Qed.
Lemma lem7670678 (_98798 : int) (_98799 : int) (_98797 : int) : (term118 _98798 _98799 _98797) = (term119 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7670677 _98798 _98797 _98799) (@lem7670675 _98798 _98799 _98797)). Qed.
Lemma lem7670679 (_98798 : int) (_98799 : int) (_98797 : int) : (term120 _98798 _98799 _98797) = (term118 _98798 _98799 _98797).
Proof. exact (@lem17045 (term121 _98798 _98797 _98799) (term122 _98798 _98799 _98797)). Qed.
Lemma lem7670680 (_98798 : int) (_98799 : int) (_98797 : int) : (term120 _98798 _98799 _98797) = (term119 _98798 _98799 _98797).
Proof. exact (TRANS (@lem7670679 _98798 _98799 _98797) (@lem7670678 _98798 _98799 _98797)). Qed.
Lemma lem7670683 (_98799 : int) (_98798 : int) : (term107 _98799 _98798) = (int_lt _98799 _98798).
Proof. exact (@lem16933 (int_lt _98799 _98798)). Qed.
Lemma lem7670684 (_98797 : int) : (term123 _98797) = (term123 _98797).
Proof. exact (eq_refl (term123 _98797)). Qed.
Lemma lem7670685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670686 (_98799 : int) (_98798 : int) : (term109 _98799 _98798) = (term110 _98799 _98798).
Proof. exact (MK_COMB (@lem7670685) (@lem7670683 _98799 _98798)). Qed.
Lemma lem7670687 (_98799 : int) (_98798 : int) (_98797 : int) : (term124 _98799 _98798 _98797) = (term125 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670686 _98799 _98798) (@lem7670684 _98797)). Qed.
Lemma lem7670688 (_98799 : int) (_98798 : int) (_98797 : int) : (term126 _98799 _98798 _98797) = (term124 _98799 _98798 _98797).
Proof. exact (@lem17160 (term114 _98799 _98798) (term127 _98797)). Qed.
Lemma lem7670689 (_98799 : int) (_98798 : int) (_98797 : int) : (term126 _98799 _98798 _98797) = (term125 _98799 _98798 _98797).
Proof. exact (TRANS (@lem7670688 _98799 _98798 _98797) (@lem7670687 _98799 _98798 _98797)). Qed.
Lemma lem7670690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670691 (_98798 : int) (_98799 : int) (_98797 : int) : (term128 _98798 _98799 _98797) = (term129 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7670690) (@lem7670680 _98798 _98799 _98797)). Qed.
Lemma lem7670692 (_98799 : int) (_98798 : int) (_98797 : int) : (term130 _98799 _98798 _98797) = (term131 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670691 _98798 _98799 _98797) (@lem7670689 _98799 _98798 _98797)). Qed.
Lemma lem7670693 (_98799 : int) (_98798 : int) (_98797 : int) : (term132 _98799 _98798 _98797) = (term130 _98799 _98798 _98797).
Proof. exact (@lem17160 (term133 _98798 _98799 _98797) (term134 _98799 _98798 _98797)). Qed.
Lemma lem7670694 (_98799 : int) (_98798 : int) (_98797 : int) : (term132 _98799 _98798 _98797) = (term131 _98799 _98798 _98797).
Proof. exact (TRANS (@lem7670693 _98799 _98798 _98797) (@lem7670692 _98799 _98798 _98797)). Qed.
Lemma lem7670696 (_98799 : int) : (term135 _98799) = (term135 _98799).
Proof. exact (eq_refl (term135 _98799)). Qed.
Lemma lem7670697 (_98799 : int) (_98798 : int) (_98797 : int) : (term136 _98799 _98798 _98797) = (term137 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670696 _98799) (@lem7670694 _98799 _98798 _98797)). Qed.
Lemma lem7670698 (_98799 : int) (_98798 : int) (_98797 : int) : (term138 _98799 _98798 _98797) = (term136 _98799 _98798 _98797).
Proof. exact (@lem17362 (term139 _98799) (term140 _98799 _98798 _98797)). Qed.
Lemma lem7670699 (_98799 : int) (_98798 : int) (_98797 : int) : (term138 _98799 _98798 _98797) = (term137 _98799 _98798 _98797).
Proof. exact (TRANS (@lem7670698 _98799 _98798 _98797) (@lem7670697 _98799 _98798 _98797)). Qed.
Lemma lem7670701 (_98798 : int) : (term135 _98798) = (term135 _98798).
Proof. exact (eq_refl (term135 _98798)). Qed.
Lemma lem7670702 (_98799 : int) (_98798 : int) (_98797 : int) : (term141 _98799 _98798 _98797) = (term142 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670701 _98798) (@lem7670699 _98799 _98798 _98797)). Qed.
Lemma lem7670703 (_98799 : int) (_98798 : int) (_98797 : int) : (term143 _98799 _98798 _98797) = (term141 _98799 _98798 _98797).
Proof. exact (@lem17362 (term139 _98798) (term144 _98799 _98798 _98797)). Qed.
Lemma lem7670704 (_98799 : int) (_98798 : int) (_98797 : int) : (term143 _98799 _98798 _98797) = (term142 _98799 _98798 _98797).
Proof. exact (TRANS (@lem7670703 _98799 _98798 _98797) (@lem7670702 _98799 _98798 _98797)). Qed.
Lemma lem7670706 (_98797 : int) : (term135 _98797) = (term135 _98797).
Proof. exact (eq_refl (term135 _98797)). Qed.
Lemma lem7670707 (_98799 : int) (_98798 : int) (_98797 : int) : (term145 _98799 _98798 _98797) = (term146 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670706 _98797) (@lem7670704 _98799 _98798 _98797)). Qed.
Lemma lem7670708 (_98799 : int) (_98798 : int) (_98797 : int) : (term147 _98799 _98798 _98797) = (term145 _98799 _98798 _98797).
Proof. exact (@lem17362 (term139 _98797) (term148 _98799 _98798 _98797)). Qed.
Lemma lem7670742 (_98799 : int) (_98798 : int) (_98797 : int) : (term147 _98799 _98798 _98797) = (term146 _98799 _98798 _98797).
Proof. exact (TRANS (@lem7670708 _98799 _98798 _98797) (@lem7670707 _98799 _98798 _98797)). Qed.
Lemma lem7670745 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7670746 (_98797 : int) : (term139 _98797) = (term150 _98797).
Proof. exact (@lem7670745 term82 _98797). Qed.
Lemma lem7670748 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670749 : term152 = term153.
Proof. exact (@lem7670748 (NUMERAL 0)). Qed.
Lemma lem7670750 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670751 : term154 = term155.
Proof. exact (MK_COMB (@lem7670750) (@lem7670749)). Qed.
Lemma lem7670752 (_98797 : int) : (real_of_int _98797) = (real_of_int _98797).
Proof. exact (eq_refl (real_of_int _98797)). Qed.
Lemma lem7670753 (_98797 : int) : (term150 _98797) = (term156 _98797).
Proof. exact (MK_COMB (@lem7670751) (@lem7670752 _98797)). Qed.
Lemma lem7670755 (_98797 : int) : (term139 _98797) = (term156 _98797).
Proof. exact (TRANS (@lem7670746 _98797) (@lem7670753 _98797)). Qed.
Lemma lem7670758 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7670759 (_98798 : int) : (term139 _98798) = (term150 _98798).
Proof. exact (@lem7670758 term82 _98798). Qed.
Lemma lem7670761 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670762 : term152 = term153.
Proof. exact (@lem7670761 (NUMERAL 0)). Qed.
Lemma lem7670763 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670764 : term154 = term155.
Proof. exact (MK_COMB (@lem7670763) (@lem7670762)). Qed.
Lemma lem7670765 (_98798 : int) : (real_of_int _98798) = (real_of_int _98798).
Proof. exact (eq_refl (real_of_int _98798)). Qed.
Lemma lem7670766 (_98798 : int) : (term150 _98798) = (term156 _98798).
Proof. exact (MK_COMB (@lem7670764) (@lem7670765 _98798)). Qed.
Lemma lem7670768 (_98798 : int) : (term139 _98798) = (term156 _98798).
Proof. exact (TRANS (@lem7670759 _98798) (@lem7670766 _98798)). Qed.
Lemma lem7670771 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7670772 (_98799 : int) : (term139 _98799) = (term150 _98799).
Proof. exact (@lem7670771 term82 _98799). Qed.
Lemma lem7670774 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670775 : term152 = term153.
Proof. exact (@lem7670774 (NUMERAL 0)). Qed.
Lemma lem7670776 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670777 : term154 = term155.
Proof. exact (MK_COMB (@lem7670776) (@lem7670775)). Qed.
Lemma lem7670778 (_98799 : int) : (real_of_int _98799) = (real_of_int _98799).
Proof. exact (eq_refl (real_of_int _98799)). Qed.
Lemma lem7670779 (_98799 : int) : (term150 _98799) = (term156 _98799).
Proof. exact (MK_COMB (@lem7670777) (@lem7670778 _98799)). Qed.
Lemma lem7670781 (_98799 : int) : (term139 _98799) = (term156 _98799).
Proof. exact (TRANS (@lem7670772 _98799) (@lem7670779 _98799)). Qed.
Lemma lem7670784 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7670785 (_98798 : int) (_98797 : int) (_98799 : int) : (_98798 = (int_add _98797 _98799)) = ((real_of_int _98798) = (term157 _98797 _98799)).
Proof. exact (@lem7670784 _98798 (int_add _98797 _98799)). Qed.
Lemma lem7670789 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7670790 (_98797 : int) (_98799 : int) : (term157 _98797 _98799) = (term158 _98797 _98799).
Proof. exact (@lem7670789 _98797 _98799). Qed.
Lemma lem7670791 (_98798 : int) : (term159 _98798) = (term159 _98798).
Proof. exact (eq_refl (term159 _98798)). Qed.
Lemma lem7670792 (_98798 : int) (_98797 : int) (_98799 : int) : ((real_of_int _98798) = (term157 _98797 _98799)) = ((real_of_int _98798) = (term158 _98797 _98799)).
Proof. exact (MK_COMB (@lem7670791 _98798) (@lem7670790 _98797 _98799)). Qed.
Lemma lem7670794 (_98798 : int) (_98797 : int) (_98799 : int) : (_98798 = (int_add _98797 _98799)) = ((real_of_int _98798) = (term158 _98797 _98799)).
Proof. exact (TRANS (@lem7670785 _98798 _98797 _98799) (@lem7670792 _98798 _98797 _98799)). Qed.
Lemma lem7670796 (x : int) (y : int) : (int_lt x y) = (term160 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem7670797 (_98798 : int) (_98799 : int) : (int_lt _98798 _98799) = (term160 _98798 _98799).
Proof. exact (@lem7670796 _98798 _98799). Qed.
Lemma lem7670799 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7670800 (_98798 : int) (_98799 : int) : (term160 _98798 _98799) = (term161 _98798 _98799).
Proof. exact (@lem7670799 (term162 _98798) _98799). Qed.
Lemma lem7670802 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7670803 (_98798 : int) : (term163 _98798) = (term164 _98798).
Proof. exact (@lem7670802 _98798 term165). Qed.
Lemma lem7670805 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670806 : term166 = term167.
Proof. exact (@lem7670805 term9). Qed.
Lemma lem7670807 (_98798 : int) : (term168 _98798) = (term168 _98798).
Proof. exact (eq_refl (term168 _98798)). Qed.
Lemma lem7670808 (_98798 : int) : (term164 _98798) = (term169 _98798).
Proof. exact (MK_COMB (@lem7670807 _98798) (@lem7670806)). Qed.
Lemma lem7670809 (_98798 : int) : (term163 _98798) = (term169 _98798).
Proof. exact (TRANS (@lem7670803 _98798) (@lem7670808 _98798)). Qed.
Lemma lem7670810 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670811 (_98798 : int) : (term170 _98798) = (term171 _98798).
Proof. exact (MK_COMB (@lem7670810) (@lem7670809 _98798)). Qed.
Lemma lem7670812 (_98799 : int) : (real_of_int _98799) = (real_of_int _98799).
Proof. exact (eq_refl (real_of_int _98799)). Qed.
Lemma lem7670813 (_98798 : int) (_98799 : int) : (term161 _98798 _98799) = (term172 _98798 _98799).
Proof. exact (MK_COMB (@lem7670811 _98798) (@lem7670812 _98799)). Qed.
Lemma lem7670814 (_98798 : int) (_98799 : int) : (term160 _98798 _98799) = (term172 _98798 _98799).
Proof. exact (TRANS (@lem7670800 _98798 _98799) (@lem7670813 _98798 _98799)). Qed.
Lemma lem7670815 (_98798 : int) (_98799 : int) : (int_lt _98798 _98799) = (term172 _98798 _98799).
Proof. exact (TRANS (@lem7670797 _98798 _98799) (@lem7670814 _98798 _98799)). Qed.
Lemma lem7670818 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7670819 (_98797 : int) : (_98797 = term82) = ((real_of_int _98797) = term152).
Proof. exact (@lem7670818 _98797 term82). Qed.
Lemma lem7670823 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670824 : term152 = term153.
Proof. exact (@lem7670823 (NUMERAL 0)). Qed.
Lemma lem7670825 (_98797 : int) : (term159 _98797) = (term159 _98797).
Proof. exact (eq_refl (term159 _98797)). Qed.
Lemma lem7670826 (_98797 : int) : ((real_of_int _98797) = term152) = ((real_of_int _98797) = term153).
Proof. exact (MK_COMB (@lem7670825 _98797) (@lem7670824)). Qed.
Lemma lem7670828 (_98797 : int) : (_98797 = term82) = ((real_of_int _98797) = term153).
Proof. exact (TRANS (@lem7670819 _98797) (@lem7670826 _98797)). Qed.
Lemma lem7670829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670830 (_98798 : int) (_98799 : int) : (term110 _98798 _98799) = (term173 _98798 _98799).
Proof. exact (MK_COMB (@lem7670829) (@lem7670815 _98798 _98799)). Qed.
Lemma lem7670831 (_98798 : int) (_98799 : int) (_98797 : int) : (term112 _98798 _98799 _98797) = (term174 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7670830 _98798 _98799) (@lem7670828 _98797)). Qed.
Lemma lem7670832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7670833 (_98798 : int) (_98797 : int) (_98799 : int) : (term117 _98798 _98797 _98799) = (term175 _98798 _98797 _98799).
Proof. exact (MK_COMB (@lem7670832) (@lem7670794 _98798 _98797 _98799)). Qed.
Lemma lem7670834 (_98798 : int) (_98799 : int) (_98797 : int) : (term119 _98798 _98799 _98797) = (term176 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7670833 _98798 _98797 _98799) (@lem7670831 _98798 _98799 _98797)). Qed.
Lemma lem7670836 (x : int) (y : int) : (int_lt x y) = (term160 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem7670837 (_98799 : int) (_98798 : int) : (int_lt _98799 _98798) = (term160 _98799 _98798).
Proof. exact (@lem7670836 _98799 _98798). Qed.
Lemma lem7670839 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7670840 (_98799 : int) (_98798 : int) : (term160 _98799 _98798) = (term161 _98799 _98798).
Proof. exact (@lem7670839 (term162 _98799) _98798). Qed.
Lemma lem7670842 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7670843 (_98799 : int) : (term163 _98799) = (term164 _98799).
Proof. exact (@lem7670842 _98799 term165). Qed.
Lemma lem7670845 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670846 : term166 = term167.
Proof. exact (@lem7670845 term9). Qed.
Lemma lem7670847 (_98799 : int) : (term168 _98799) = (term168 _98799).
Proof. exact (eq_refl (term168 _98799)). Qed.
Lemma lem7670848 (_98799 : int) : (term164 _98799) = (term169 _98799).
Proof. exact (MK_COMB (@lem7670847 _98799) (@lem7670846)). Qed.
Lemma lem7670849 (_98799 : int) : (term163 _98799) = (term169 _98799).
Proof. exact (TRANS (@lem7670843 _98799) (@lem7670848 _98799)). Qed.
Lemma lem7670850 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670851 (_98799 : int) : (term170 _98799) = (term171 _98799).
Proof. exact (MK_COMB (@lem7670850) (@lem7670849 _98799)). Qed.
Lemma lem7670852 (_98798 : int) : (real_of_int _98798) = (real_of_int _98798).
Proof. exact (eq_refl (real_of_int _98798)). Qed.
Lemma lem7670853 (_98799 : int) (_98798 : int) : (term161 _98799 _98798) = (term172 _98799 _98798).
Proof. exact (MK_COMB (@lem7670851 _98799) (@lem7670852 _98798)). Qed.
Lemma lem7670854 (_98799 : int) (_98798 : int) : (term160 _98799 _98798) = (term172 _98799 _98798).
Proof. exact (TRANS (@lem7670840 _98799 _98798) (@lem7670853 _98799 _98798)). Qed.
Lemma lem7670855 (_98799 : int) (_98798 : int) : (int_lt _98799 _98798) = (term172 _98799 _98798).
Proof. exact (TRANS (@lem7670837 _98799 _98798) (@lem7670854 _98799 _98798)). Qed.
Lemma lem7670857 (y : int) (x : int) : (term177 x y) = (term160 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7670858 (_98797 : int) : (term123 _98797) = (term178 _98797).
Proof. exact (@lem7670857 _98797 term165). Qed.
Lemma lem7670860 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7670861 (_98797 : int) : (term178 _98797) = (term179 _98797).
Proof. exact (@lem7670860 (term162 _98797) term165). Qed.
Lemma lem7670863 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7670864 (_98797 : int) : (term163 _98797) = (term164 _98797).
Proof. exact (@lem7670863 _98797 term165). Qed.
Lemma lem7670866 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670867 : term166 = term167.
Proof. exact (@lem7670866 term9). Qed.
Lemma lem7670868 (_98797 : int) : (term168 _98797) = (term168 _98797).
Proof. exact (eq_refl (term168 _98797)). Qed.
Lemma lem7670869 (_98797 : int) : (term164 _98797) = (term169 _98797).
Proof. exact (MK_COMB (@lem7670868 _98797) (@lem7670867)). Qed.
Lemma lem7670870 (_98797 : int) : (term163 _98797) = (term169 _98797).
Proof. exact (TRANS (@lem7670864 _98797) (@lem7670869 _98797)). Qed.
Lemma lem7670871 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7670872 (_98797 : int) : (term170 _98797) = (term171 _98797).
Proof. exact (MK_COMB (@lem7670871) (@lem7670870 _98797)). Qed.
Lemma lem7670874 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7670875 : term166 = term167.
Proof. exact (@lem7670874 term9). Qed.
Lemma lem7670876 (_98797 : int) : (term179 _98797) = (term180 _98797).
Proof. exact (MK_COMB (@lem7670872 _98797) (@lem7670875)). Qed.
Lemma lem7670877 (_98797 : int) : (term178 _98797) = (term180 _98797).
Proof. exact (TRANS (@lem7670861 _98797) (@lem7670876 _98797)). Qed.
Lemma lem7670878 (_98797 : int) : (term123 _98797) = (term180 _98797).
Proof. exact (TRANS (@lem7670858 _98797) (@lem7670877 _98797)). Qed.
Lemma lem7670879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670880 (_98799 : int) (_98798 : int) : (term110 _98799 _98798) = (term173 _98799 _98798).
Proof. exact (MK_COMB (@lem7670879) (@lem7670855 _98799 _98798)). Qed.
Lemma lem7670881 (_98799 : int) (_98798 : int) (_98797 : int) : (term125 _98799 _98798 _98797) = (term181 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670880 _98799 _98798) (@lem7670878 _98797)). Qed.
Lemma lem7670882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670883 (_98798 : int) (_98799 : int) (_98797 : int) : (term129 _98798 _98799 _98797) = (term182 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7670882) (@lem7670834 _98798 _98799 _98797)). Qed.
Lemma lem7670884 (_98799 : int) (_98798 : int) (_98797 : int) : (term131 _98799 _98798 _98797) = (term183 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670883 _98798 _98799 _98797) (@lem7670881 _98799 _98798 _98797)). Qed.
Lemma lem7670885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670886 (_98799 : int) : (term135 _98799) = (term184 _98799).
Proof. exact (MK_COMB (@lem7670885) (@lem7670781 _98799)). Qed.
Lemma lem7670887 (_98799 : int) (_98798 : int) (_98797 : int) : (term137 _98799 _98798 _98797) = (term185 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670886 _98799) (@lem7670884 _98799 _98798 _98797)). Qed.
Lemma lem7670888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670889 (_98798 : int) : (term135 _98798) = (term184 _98798).
Proof. exact (MK_COMB (@lem7670888) (@lem7670768 _98798)). Qed.
Lemma lem7670890 (_98799 : int) (_98798 : int) (_98797 : int) : (term142 _98799 _98798 _98797) = (term186 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670889 _98798) (@lem7670887 _98799 _98798 _98797)). Qed.
Lemma lem7670891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7670892 (_98797 : int) : (term135 _98797) = (term184 _98797).
Proof. exact (MK_COMB (@lem7670891) (@lem7670755 _98797)). Qed.
Lemma lem7670893 (_98799 : int) (_98798 : int) (_98797 : int) : (term146 _98799 _98798 _98797) = (term187 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7670892 _98797) (@lem7670890 _98799 _98798 _98797)). Qed.
Lemma lem7670894 (_98799 : int) (_98798 : int) (_98797 : int) : (term147 _98799 _98798 _98797) = (term187 _98799 _98798 _98797).
Proof. exact (TRANS (@lem7670742 _98799 _98798 _98797) (@lem7670893 _98799 _98798 _98797)). Qed.
Lemma lem7670898 (t : Prop) : (term188 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7670974 (_98799 : int) (_98798 : int) (_98797 : int) : (term189 _98799 _98798 _98797) = (term187 _98799 _98798 _98797).
Proof. exact (@lem7670898 (term187 _98799 _98798 _98797)). Qed.
Lemma lem7670975 (_98797 : int) : (term156 _98797) = (term190 _98797).
Proof. exact (@lem1988287 (real_of_int _98797) term153). Qed.
Lemma lem7670981 (_98797 : int) : (term191 _98797) = (term192 _98797).
Proof. exact (@lem1982792 (real_of_int _98797) term153). Qed.
Lemma lem7670983 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7670984 : term153 = term194.
Proof. exact (@lem7670983 (NUMERAL 0)). Qed.
Lemma lem7670986 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7670987 : term197 = term198.
Proof. exact (@lem7670986 term9). Qed.
Lemma lem7670988 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7670989 : term199 = term200.
Proof. exact (MK_COMB (@lem7670988) (@lem7670987)). Qed.
Lemma lem7670990 : term201 = term202.
Proof. exact (MK_COMB (@lem7670989) (@lem7670984)). Qed.
Lemma lem7670991 : term202 = term203.
Proof. exact (@lem1981613 term197 term153 term167 term167). Qed.
Lemma lem7670993 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7670994 : term206 = term207.
Proof. exact (@lem7670993 term9 term9). Qed.
Lemma lem7670995 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7670996 : term209 = term9.
Proof. exact (EQ_MP (@lem7670995) (@lem940073)). Qed.
Lemma lem7670997 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7670998 : term207 = term167.
Proof. exact (MK_COMB (@lem7670997) (@lem7670996)). Qed.
Lemma lem7670999 : term206 = term167.
Proof. exact (TRANS (@lem7670994) (@lem7670998)). Qed.
Lemma lem7671001 (x : nat) : (term210 x) = term153.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7671002 : term201 = term153.
Proof. exact (@lem7671001 term9). Qed.
Lemma lem7671003 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671004 : term211 = term212.
Proof. exact (MK_COMB (@lem7671003) (@lem7671002)). Qed.
Lemma lem7671005 : term203 = term194.
Proof. exact (MK_COMB (@lem7671004) (@lem7670999)). Qed.
Lemma lem7671006 : term202 = term194.
Proof. exact (TRANS (@lem7670991) (@lem7671005)). Qed.
Lemma lem7671007 : term201 = term194.
Proof. exact (TRANS (@lem7670990) (@lem7671006)). Qed.
Lemma lem7671009 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671010 : term194 = term153.
Proof. exact (@lem7671009 term153). Qed.
Lemma lem7671011 : term201 = term153.
Proof. exact (TRANS (@lem7671007) (@lem7671010)). Qed.
Lemma lem7671012 (_98797 : int) : (term168 _98797) = (term168 _98797).
Proof. exact (eq_refl (term168 _98797)). Qed.
Lemma lem7671013 (_98797 : int) : (term192 _98797) = (term214 _98797).
Proof. exact (MK_COMB (@lem7671012 _98797) (@lem7671011)). Qed.
Lemma lem7671014 (_98797 : int) : (term214 _98797) = (real_of_int _98797).
Proof. exact (@lem1982723 (real_of_int _98797)). Qed.
Lemma lem7671015 (_98797 : int) : (term192 _98797) = (real_of_int _98797).
Proof. exact (TRANS (@lem7671013 _98797) (@lem7671014 _98797)). Qed.
Lemma lem7671017 (_98797 : int) : (term191 _98797) = (real_of_int _98797).
Proof. exact (TRANS (@lem7670981 _98797) (@lem7671015 _98797)). Qed.
Lemma lem7671018 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7671019 (_98797 : int) : (term215 _98797) = (term216 _98797).
Proof. exact (MK_COMB (@lem7671018) (@lem7671017 _98797)). Qed.
Lemma lem7671020 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671021 (_98797 : int) : (term190 _98797) = (term217 _98797).
Proof. exact (MK_COMB (@lem7671019 _98797) (@lem7671020)). Qed.
Lemma lem7671022 (_98797 : int) : (term156 _98797) = (term217 _98797).
Proof. exact (TRANS (@lem7670975 _98797) (@lem7671021 _98797)). Qed.
Lemma lem7671023 (_98798 : int) : (term156 _98798) = (term190 _98798).
Proof. exact (@lem1988287 (real_of_int _98798) term153). Qed.
Lemma lem7671029 (_98798 : int) : (term191 _98798) = (term192 _98798).
Proof. exact (@lem1982792 (real_of_int _98798) term153). Qed.
Lemma lem7671031 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671032 : term153 = term194.
Proof. exact (@lem7671031 (NUMERAL 0)). Qed.
Lemma lem7671034 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671035 : term197 = term198.
Proof. exact (@lem7671034 term9). Qed.
Lemma lem7671036 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671037 : term199 = term200.
Proof. exact (MK_COMB (@lem7671036) (@lem7671035)). Qed.
Lemma lem7671038 : term201 = term202.
Proof. exact (MK_COMB (@lem7671037) (@lem7671032)). Qed.
Lemma lem7671039 : term202 = term203.
Proof. exact (@lem1981613 term197 term153 term167 term167). Qed.
Lemma lem7671041 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671042 : term206 = term207.
Proof. exact (@lem7671041 term9 term9). Qed.
Lemma lem7671043 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671044 : term209 = term9.
Proof. exact (EQ_MP (@lem7671043) (@lem940073)). Qed.
Lemma lem7671045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671046 : term207 = term167.
Proof. exact (MK_COMB (@lem7671045) (@lem7671044)). Qed.
Lemma lem7671047 : term206 = term167.
Proof. exact (TRANS (@lem7671042) (@lem7671046)). Qed.
Lemma lem7671049 (x : nat) : (term210 x) = term153.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7671050 : term201 = term153.
Proof. exact (@lem7671049 term9). Qed.
Lemma lem7671051 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671052 : term211 = term212.
Proof. exact (MK_COMB (@lem7671051) (@lem7671050)). Qed.
Lemma lem7671053 : term203 = term194.
Proof. exact (MK_COMB (@lem7671052) (@lem7671047)). Qed.
Lemma lem7671054 : term202 = term194.
Proof. exact (TRANS (@lem7671039) (@lem7671053)). Qed.
Lemma lem7671055 : term201 = term194.
Proof. exact (TRANS (@lem7671038) (@lem7671054)). Qed.
Lemma lem7671057 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671058 : term194 = term153.
Proof. exact (@lem7671057 term153). Qed.
Lemma lem7671059 : term201 = term153.
Proof. exact (TRANS (@lem7671055) (@lem7671058)). Qed.
Lemma lem7671060 (_98798 : int) : (term168 _98798) = (term168 _98798).
Proof. exact (eq_refl (term168 _98798)). Qed.
Lemma lem7671061 (_98798 : int) : (term192 _98798) = (term214 _98798).
Proof. exact (MK_COMB (@lem7671060 _98798) (@lem7671059)). Qed.
Lemma lem7671062 (_98798 : int) : (term214 _98798) = (real_of_int _98798).
Proof. exact (@lem1982723 (real_of_int _98798)). Qed.
Lemma lem7671063 (_98798 : int) : (term192 _98798) = (real_of_int _98798).
Proof. exact (TRANS (@lem7671061 _98798) (@lem7671062 _98798)). Qed.
Lemma lem7671065 (_98798 : int) : (term191 _98798) = (real_of_int _98798).
Proof. exact (TRANS (@lem7671029 _98798) (@lem7671063 _98798)). Qed.
Lemma lem7671066 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7671067 (_98798 : int) : (term215 _98798) = (term216 _98798).
Proof. exact (MK_COMB (@lem7671066) (@lem7671065 _98798)). Qed.
Lemma lem7671068 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671069 (_98798 : int) : (term190 _98798) = (term217 _98798).
Proof. exact (MK_COMB (@lem7671067 _98798) (@lem7671068)). Qed.
Lemma lem7671070 (_98798 : int) : (term156 _98798) = (term217 _98798).
Proof. exact (TRANS (@lem7671023 _98798) (@lem7671069 _98798)). Qed.
Lemma lem7671071 (_98799 : int) : (term156 _98799) = (term190 _98799).
Proof. exact (@lem1988287 (real_of_int _98799) term153). Qed.
Lemma lem7671077 (_98799 : int) : (term191 _98799) = (term192 _98799).
Proof. exact (@lem1982792 (real_of_int _98799) term153). Qed.
Lemma lem7671079 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671080 : term153 = term194.
Proof. exact (@lem7671079 (NUMERAL 0)). Qed.
Lemma lem7671082 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671083 : term197 = term198.
Proof. exact (@lem7671082 term9). Qed.
Lemma lem7671084 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671085 : term199 = term200.
Proof. exact (MK_COMB (@lem7671084) (@lem7671083)). Qed.
Lemma lem7671086 : term201 = term202.
Proof. exact (MK_COMB (@lem7671085) (@lem7671080)). Qed.
Lemma lem7671087 : term202 = term203.
Proof. exact (@lem1981613 term197 term153 term167 term167). Qed.
Lemma lem7671089 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671090 : term206 = term207.
Proof. exact (@lem7671089 term9 term9). Qed.
Lemma lem7671091 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671092 : term209 = term9.
Proof. exact (EQ_MP (@lem7671091) (@lem940073)). Qed.
Lemma lem7671093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671094 : term207 = term167.
Proof. exact (MK_COMB (@lem7671093) (@lem7671092)). Qed.
Lemma lem7671095 : term206 = term167.
Proof. exact (TRANS (@lem7671090) (@lem7671094)). Qed.
Lemma lem7671097 (x : nat) : (term210 x) = term153.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7671098 : term201 = term153.
Proof. exact (@lem7671097 term9). Qed.
Lemma lem7671099 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671100 : term211 = term212.
Proof. exact (MK_COMB (@lem7671099) (@lem7671098)). Qed.
Lemma lem7671101 : term203 = term194.
Proof. exact (MK_COMB (@lem7671100) (@lem7671095)). Qed.
Lemma lem7671102 : term202 = term194.
Proof. exact (TRANS (@lem7671087) (@lem7671101)). Qed.
Lemma lem7671103 : term201 = term194.
Proof. exact (TRANS (@lem7671086) (@lem7671102)). Qed.
Lemma lem7671105 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671106 : term194 = term153.
Proof. exact (@lem7671105 term153). Qed.
Lemma lem7671107 : term201 = term153.
Proof. exact (TRANS (@lem7671103) (@lem7671106)). Qed.
Lemma lem7671108 (_98799 : int) : (term168 _98799) = (term168 _98799).
Proof. exact (eq_refl (term168 _98799)). Qed.
Lemma lem7671109 (_98799 : int) : (term192 _98799) = (term214 _98799).
Proof. exact (MK_COMB (@lem7671108 _98799) (@lem7671107)). Qed.
Lemma lem7671110 (_98799 : int) : (term214 _98799) = (real_of_int _98799).
Proof. exact (@lem1982723 (real_of_int _98799)). Qed.
Lemma lem7671111 (_98799 : int) : (term192 _98799) = (real_of_int _98799).
Proof. exact (TRANS (@lem7671109 _98799) (@lem7671110 _98799)). Qed.
Lemma lem7671113 (_98799 : int) : (term191 _98799) = (real_of_int _98799).
Proof. exact (TRANS (@lem7671077 _98799) (@lem7671111 _98799)). Qed.
Lemma lem7671114 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7671115 (_98799 : int) : (term215 _98799) = (term216 _98799).
Proof. exact (MK_COMB (@lem7671114) (@lem7671113 _98799)). Qed.
Lemma lem7671116 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671117 (_98799 : int) : (term190 _98799) = (term217 _98799).
Proof. exact (MK_COMB (@lem7671115 _98799) (@lem7671116)). Qed.
Lemma lem7671118 (_98799 : int) : (term156 _98799) = (term217 _98799).
Proof. exact (TRANS (@lem7671071 _98799) (@lem7671117 _98799)). Qed.
Lemma lem7671119 (_98798 : int) (_98797 : int) (_98799 : int) : ((real_of_int _98798) = (term158 _98797 _98799)) = ((term218 _98798 _98797 _98799) = term153).
Proof. exact (@lem1988293 (real_of_int _98798) (term158 _98797 _98799)). Qed.
Lemma lem7671131 (_98798 : int) (_98797 : int) (_98799 : int) : (term218 _98798 _98797 _98799) = (term219 _98798 _98797 _98799).
Proof. exact (@lem1982792 (real_of_int _98798) (term158 _98797 _98799)). Qed.
Lemma lem7671138 (_98797 : int) (_98799 : int) : (term220 _98797 _98799) = (term221 _98797 _98799).
Proof. exact (@lem1982781 (real_of_int _98797) term197 (real_of_int _98799)). Qed.
Lemma lem7671139 (_98798 : int) : (term168 _98798) = (term168 _98798).
Proof. exact (eq_refl (term168 _98798)). Qed.
Lemma lem7671140 (_98798 : int) (_98797 : int) (_98799 : int) : (term219 _98798 _98797 _98799) = (term222 _98798 _98797 _98799).
Proof. exact (MK_COMB (@lem7671139 _98798) (@lem7671138 _98797 _98799)). Qed.
Lemma lem7671145 (_98797 : int) (_98798 : int) (_98799 : int) : (term222 _98798 _98797 _98799) = (term223 _98797 _98798 _98799).
Proof. exact (@lem1982757 (term224 _98797) (real_of_int _98798) (term224 _98799)). Qed.
Lemma lem7671146 (_98797 : int) (_98798 : int) (_98799 : int) : (term219 _98798 _98797 _98799) = (term223 _98797 _98798 _98799).
Proof. exact (TRANS (@lem7671140 _98798 _98797 _98799) (@lem7671145 _98797 _98798 _98799)). Qed.
Lemma lem7671148 (_98797 : int) (_98798 : int) (_98799 : int) : (term218 _98798 _98797 _98799) = (term223 _98797 _98798 _98799).
Proof. exact (TRANS (@lem7671131 _98798 _98797 _98799) (@lem7671146 _98797 _98798 _98799)). Qed.
Lemma lem7671149 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7671150 (_98797 : int) (_98798 : int) (_98799 : int) : (term225 _98798 _98797 _98799) = (term226 _98797 _98798 _98799).
Proof. exact (MK_COMB (@lem7671149) (@lem7671148 _98797 _98798 _98799)). Qed.
Lemma lem7671151 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671152 (_98797 : int) (_98798 : int) (_98799 : int) : ((term218 _98798 _98797 _98799) = term153) = ((term223 _98797 _98798 _98799) = term153).
Proof. exact (MK_COMB (@lem7671150 _98797 _98798 _98799) (@lem7671151)). Qed.
Lemma lem7671153 (_98797 : int) (_98798 : int) (_98799 : int) : ((real_of_int _98798) = (term158 _98797 _98799)) = ((term223 _98797 _98798 _98799) = term153).
Proof. exact (TRANS (@lem7671119 _98798 _98797 _98799) (@lem7671152 _98797 _98798 _98799)). Qed.
Lemma lem7671154 (_98799 : int) (_98798 : int) : (term172 _98798 _98799) = (term227 _98799 _98798).
Proof. exact (@lem1988287 (real_of_int _98799) (term169 _98798)). Qed.
Lemma lem7671166 (_98799 : int) (_98798 : int) : (term228 _98799 _98798) = (term229 _98799 _98798).
Proof. exact (@lem1982792 (real_of_int _98799) (term169 _98798)). Qed.
Lemma lem7671167 (_98798 : int) : (term230 _98798) = (term231 _98798).
Proof. exact (@lem1982781 (real_of_int _98798) term197 term167). Qed.
Lemma lem7671169 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671170 : term167 = term232.
Proof. exact (@lem7671169 term9). Qed.
Lemma lem7671172 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671173 : term197 = term198.
Proof. exact (@lem7671172 term9). Qed.
Lemma lem7671174 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671175 : term199 = term200.
Proof. exact (MK_COMB (@lem7671174) (@lem7671173)). Qed.
Lemma lem7671176 : term233 = term234.
Proof. exact (MK_COMB (@lem7671175) (@lem7671170)). Qed.
Lemma lem7671177 : term234 = term235.
Proof. exact (@lem1981613 term197 term167 term167 term167). Qed.
Lemma lem7671179 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671180 : term206 = term207.
Proof. exact (@lem7671179 term9 term9). Qed.
Lemma lem7671181 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671182 : term209 = term9.
Proof. exact (EQ_MP (@lem7671181) (@lem940073)). Qed.
Lemma lem7671183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671184 : term207 = term167.
Proof. exact (MK_COMB (@lem7671183) (@lem7671182)). Qed.
Lemma lem7671185 : term206 = term167.
Proof. exact (TRANS (@lem7671180) (@lem7671184)). Qed.
Lemma lem7671187 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7671188 : term233 = term238.
Proof. exact (@lem7671187 term9 term9). Qed.
Lemma lem7671189 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671190 : term209 = term9.
Proof. exact (EQ_MP (@lem7671189) (@lem940073)). Qed.
Lemma lem7671191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671192 : term207 = term167.
Proof. exact (MK_COMB (@lem7671191) (@lem7671190)). Qed.
Lemma lem7671193 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7671194 : term238 = term197.
Proof. exact (MK_COMB (@lem7671193) (@lem7671192)). Qed.
Lemma lem7671195 : term233 = term197.
Proof. exact (TRANS (@lem7671188) (@lem7671194)). Qed.
Lemma lem7671196 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671197 : term239 = term240.
Proof. exact (MK_COMB (@lem7671196) (@lem7671195)). Qed.
Lemma lem7671198 : term235 = term198.
Proof. exact (MK_COMB (@lem7671197) (@lem7671185)). Qed.
Lemma lem7671199 : term234 = term198.
Proof. exact (TRANS (@lem7671177) (@lem7671198)). Qed.
Lemma lem7671200 : term233 = term198.
Proof. exact (TRANS (@lem7671176) (@lem7671199)). Qed.
Lemma lem7671202 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671203 : term198 = term197.
Proof. exact (@lem7671202 term197). Qed.
Lemma lem7671204 : term233 = term197.
Proof. exact (TRANS (@lem7671200) (@lem7671203)). Qed.
Lemma lem7671207 (_98798 : int) : (term241 _98798) = (term241 _98798).
Proof. exact (eq_refl (term241 _98798)). Qed.
Lemma lem7671208 (_98798 : int) : (term231 _98798) = (term242 _98798).
Proof. exact (MK_COMB (@lem7671207 _98798) (@lem7671204)). Qed.
Lemma lem7671209 (_98798 : int) : (term230 _98798) = (term242 _98798).
Proof. exact (TRANS (@lem7671167 _98798) (@lem7671208 _98798)). Qed.
Lemma lem7671210 (_98799 : int) : (term168 _98799) = (term168 _98799).
Proof. exact (eq_refl (term168 _98799)). Qed.
Lemma lem7671211 (_98799 : int) (_98798 : int) : (term229 _98799 _98798) = (term243 _98799 _98798).
Proof. exact (MK_COMB (@lem7671210 _98799) (@lem7671209 _98798)). Qed.
Lemma lem7671216 (_98798 : int) (_98799 : int) : (term243 _98799 _98798) = (term244 _98798 _98799).
Proof. exact (@lem1982757 (term224 _98798) (real_of_int _98799) term197). Qed.
Lemma lem7671217 (_98798 : int) (_98799 : int) : (term229 _98799 _98798) = (term244 _98798 _98799).
Proof. exact (TRANS (@lem7671211 _98799 _98798) (@lem7671216 _98798 _98799)). Qed.
Lemma lem7671219 (_98798 : int) (_98799 : int) : (term228 _98799 _98798) = (term244 _98798 _98799).
Proof. exact (TRANS (@lem7671166 _98799 _98798) (@lem7671217 _98798 _98799)). Qed.
Lemma lem7671220 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7671221 (_98798 : int) (_98799 : int) : (term245 _98799 _98798) = (term246 _98798 _98799).
Proof. exact (MK_COMB (@lem7671220) (@lem7671219 _98798 _98799)). Qed.
Lemma lem7671222 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671223 (_98798 : int) (_98799 : int) : (term227 _98799 _98798) = (term247 _98798 _98799).
Proof. exact (MK_COMB (@lem7671221 _98798 _98799) (@lem7671222)). Qed.
Lemma lem7671224 (_98798 : int) (_98799 : int) : (term172 _98798 _98799) = (term247 _98798 _98799).
Proof. exact (TRANS (@lem7671154 _98799 _98798) (@lem7671223 _98798 _98799)). Qed.
Lemma lem7671225 (_98797 : int) : ((real_of_int _98797) = term153) = ((term191 _98797) = term153).
Proof. exact (@lem1988293 (real_of_int _98797) term153). Qed.
Lemma lem7671231 (_98797 : int) : (term191 _98797) = (term192 _98797).
Proof. exact (@lem1982792 (real_of_int _98797) term153). Qed.
Lemma lem7671233 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671234 : term153 = term194.
Proof. exact (@lem7671233 (NUMERAL 0)). Qed.
Lemma lem7671236 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671237 : term197 = term198.
Proof. exact (@lem7671236 term9). Qed.
Lemma lem7671238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671239 : term199 = term200.
Proof. exact (MK_COMB (@lem7671238) (@lem7671237)). Qed.
Lemma lem7671240 : term201 = term202.
Proof. exact (MK_COMB (@lem7671239) (@lem7671234)). Qed.
Lemma lem7671241 : term202 = term203.
Proof. exact (@lem1981613 term197 term153 term167 term167). Qed.
Lemma lem7671243 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671244 : term206 = term207.
Proof. exact (@lem7671243 term9 term9). Qed.
Lemma lem7671245 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671246 : term209 = term9.
Proof. exact (EQ_MP (@lem7671245) (@lem940073)). Qed.
Lemma lem7671247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671248 : term207 = term167.
Proof. exact (MK_COMB (@lem7671247) (@lem7671246)). Qed.
Lemma lem7671249 : term206 = term167.
Proof. exact (TRANS (@lem7671244) (@lem7671248)). Qed.
Lemma lem7671251 (x : nat) : (term210 x) = term153.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7671252 : term201 = term153.
Proof. exact (@lem7671251 term9). Qed.
Lemma lem7671253 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671254 : term211 = term212.
Proof. exact (MK_COMB (@lem7671253) (@lem7671252)). Qed.
Lemma lem7671255 : term203 = term194.
Proof. exact (MK_COMB (@lem7671254) (@lem7671249)). Qed.
Lemma lem7671256 : term202 = term194.
Proof. exact (TRANS (@lem7671241) (@lem7671255)). Qed.
Lemma lem7671257 : term201 = term194.
Proof. exact (TRANS (@lem7671240) (@lem7671256)). Qed.
Lemma lem7671259 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671260 : term194 = term153.
Proof. exact (@lem7671259 term153). Qed.
Lemma lem7671261 : term201 = term153.
Proof. exact (TRANS (@lem7671257) (@lem7671260)). Qed.
Lemma lem7671262 (_98797 : int) : (term168 _98797) = (term168 _98797).
Proof. exact (eq_refl (term168 _98797)). Qed.
Lemma lem7671263 (_98797 : int) : (term192 _98797) = (term214 _98797).
Proof. exact (MK_COMB (@lem7671262 _98797) (@lem7671261)). Qed.
Lemma lem7671264 (_98797 : int) : (term214 _98797) = (real_of_int _98797).
Proof. exact (@lem1982723 (real_of_int _98797)). Qed.
Lemma lem7671265 (_98797 : int) : (term192 _98797) = (real_of_int _98797).
Proof. exact (TRANS (@lem7671263 _98797) (@lem7671264 _98797)). Qed.
Lemma lem7671267 (_98797 : int) : (term191 _98797) = (real_of_int _98797).
Proof. exact (TRANS (@lem7671231 _98797) (@lem7671265 _98797)). Qed.
Lemma lem7671268 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7671269 (_98797 : int) : (term248 _98797) = (term159 _98797).
Proof. exact (MK_COMB (@lem7671268) (@lem7671267 _98797)). Qed.
Lemma lem7671270 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671271 (_98797 : int) : ((term191 _98797) = term153) = ((real_of_int _98797) = term153).
Proof. exact (MK_COMB (@lem7671269 _98797) (@lem7671270)). Qed.
Lemma lem7671272 (_98797 : int) : ((real_of_int _98797) = term153) = ((real_of_int _98797) = term153).
Proof. exact (TRANS (@lem7671225 _98797) (@lem7671271 _98797)). Qed.
Lemma lem7671273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7671274 (_98798 : int) (_98799 : int) : (term173 _98798 _98799) = (term249 _98798 _98799).
Proof. exact (MK_COMB (@lem7671273) (@lem7671224 _98798 _98799)). Qed.
Lemma lem7671275 (_98798 : int) (_98799 : int) (_98797 : int) : (term174 _98798 _98799 _98797) = (term250 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671274 _98798 _98799) (@lem7671272 _98797)). Qed.
Lemma lem7671276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7671277 (_98797 : int) (_98798 : int) (_98799 : int) : (term175 _98798 _98797 _98799) = (term251 _98797 _98798 _98799).
Proof. exact (MK_COMB (@lem7671276) (@lem7671153 _98797 _98798 _98799)). Qed.
Lemma lem7671278 (_98798 : int) (_98799 : int) (_98797 : int) : (term176 _98798 _98799 _98797) = (term252 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671277 _98797 _98798 _98799) (@lem7671275 _98798 _98799 _98797)). Qed.
Lemma lem7671279 (_98798 : int) (_98799 : int) : (term172 _98799 _98798) = (term227 _98798 _98799).
Proof. exact (@lem1988287 (real_of_int _98798) (term169 _98799)). Qed.
Lemma lem7671291 (_98798 : int) (_98799 : int) : (term228 _98798 _98799) = (term229 _98798 _98799).
Proof. exact (@lem1982792 (real_of_int _98798) (term169 _98799)). Qed.
Lemma lem7671292 (_98799 : int) : (term230 _98799) = (term231 _98799).
Proof. exact (@lem1982781 (real_of_int _98799) term197 term167). Qed.
Lemma lem7671294 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671295 : term167 = term232.
Proof. exact (@lem7671294 term9). Qed.
Lemma lem7671297 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671298 : term197 = term198.
Proof. exact (@lem7671297 term9). Qed.
Lemma lem7671299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671300 : term199 = term200.
Proof. exact (MK_COMB (@lem7671299) (@lem7671298)). Qed.
Lemma lem7671301 : term233 = term234.
Proof. exact (MK_COMB (@lem7671300) (@lem7671295)). Qed.
Lemma lem7671302 : term234 = term235.
Proof. exact (@lem1981613 term197 term167 term167 term167). Qed.
Lemma lem7671304 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671305 : term206 = term207.
Proof. exact (@lem7671304 term9 term9). Qed.
Lemma lem7671306 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671307 : term209 = term9.
Proof. exact (EQ_MP (@lem7671306) (@lem940073)). Qed.
Lemma lem7671308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671309 : term207 = term167.
Proof. exact (MK_COMB (@lem7671308) (@lem7671307)). Qed.
Lemma lem7671310 : term206 = term167.
Proof. exact (TRANS (@lem7671305) (@lem7671309)). Qed.
Lemma lem7671312 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7671313 : term233 = term238.
Proof. exact (@lem7671312 term9 term9). Qed.
Lemma lem7671314 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671315 : term209 = term9.
Proof. exact (EQ_MP (@lem7671314) (@lem940073)). Qed.
Lemma lem7671316 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671317 : term207 = term167.
Proof. exact (MK_COMB (@lem7671316) (@lem7671315)). Qed.
Lemma lem7671318 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7671319 : term238 = term197.
Proof. exact (MK_COMB (@lem7671318) (@lem7671317)). Qed.
Lemma lem7671320 : term233 = term197.
Proof. exact (TRANS (@lem7671313) (@lem7671319)). Qed.
Lemma lem7671321 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671322 : term239 = term240.
Proof. exact (MK_COMB (@lem7671321) (@lem7671320)). Qed.
Lemma lem7671323 : term235 = term198.
Proof. exact (MK_COMB (@lem7671322) (@lem7671310)). Qed.
Lemma lem7671324 : term234 = term198.
Proof. exact (TRANS (@lem7671302) (@lem7671323)). Qed.
Lemma lem7671325 : term233 = term198.
Proof. exact (TRANS (@lem7671301) (@lem7671324)). Qed.
Lemma lem7671327 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671328 : term198 = term197.
Proof. exact (@lem7671327 term197). Qed.
Lemma lem7671329 : term233 = term197.
Proof. exact (TRANS (@lem7671325) (@lem7671328)). Qed.
Lemma lem7671332 (_98799 : int) : (term241 _98799) = (term241 _98799).
Proof. exact (eq_refl (term241 _98799)). Qed.
Lemma lem7671333 (_98799 : int) : (term231 _98799) = (term242 _98799).
Proof. exact (MK_COMB (@lem7671332 _98799) (@lem7671329)). Qed.
Lemma lem7671334 (_98799 : int) : (term230 _98799) = (term242 _98799).
Proof. exact (TRANS (@lem7671292 _98799) (@lem7671333 _98799)). Qed.
Lemma lem7671335 (_98798 : int) : (term168 _98798) = (term168 _98798).
Proof. exact (eq_refl (term168 _98798)). Qed.
Lemma lem7671338 (_98798 : int) (_98799 : int) : (term229 _98798 _98799) = (term243 _98798 _98799).
Proof. exact (MK_COMB (@lem7671335 _98798) (@lem7671334 _98799)). Qed.
Lemma lem7671340 (_98798 : int) (_98799 : int) : (term228 _98798 _98799) = (term243 _98798 _98799).
Proof. exact (TRANS (@lem7671291 _98798 _98799) (@lem7671338 _98798 _98799)). Qed.
Lemma lem7671341 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7671342 (_98798 : int) (_98799 : int) : (term245 _98798 _98799) = (term253 _98798 _98799).
Proof. exact (MK_COMB (@lem7671341) (@lem7671340 _98798 _98799)). Qed.
Lemma lem7671343 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671344 (_98798 : int) (_98799 : int) : (term227 _98798 _98799) = (term254 _98798 _98799).
Proof. exact (MK_COMB (@lem7671342 _98798 _98799) (@lem7671343)). Qed.
Lemma lem7671345 (_98798 : int) (_98799 : int) : (term172 _98799 _98798) = (term254 _98798 _98799).
Proof. exact (TRANS (@lem7671279 _98798 _98799) (@lem7671344 _98798 _98799)). Qed.
Lemma lem7671346 (_98797 : int) : (term180 _98797) = (term255 _98797).
Proof. exact (@lem1988287 term167 (term169 _98797)). Qed.
Lemma lem7671358 (_98797 : int) : (term256 _98797) = (term257 _98797).
Proof. exact (@lem1982792 term167 (term169 _98797)). Qed.
Lemma lem7671359 (_98797 : int) : (term230 _98797) = (term231 _98797).
Proof. exact (@lem1982781 (real_of_int _98797) term197 term167). Qed.
Lemma lem7671361 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671362 : term167 = term232.
Proof. exact (@lem7671361 term9). Qed.
Lemma lem7671364 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671365 : term197 = term198.
Proof. exact (@lem7671364 term9). Qed.
Lemma lem7671366 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671367 : term199 = term200.
Proof. exact (MK_COMB (@lem7671366) (@lem7671365)). Qed.
Lemma lem7671368 : term233 = term234.
Proof. exact (MK_COMB (@lem7671367) (@lem7671362)). Qed.
Lemma lem7671369 : term234 = term235.
Proof. exact (@lem1981613 term197 term167 term167 term167). Qed.
Lemma lem7671371 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671372 : term206 = term207.
Proof. exact (@lem7671371 term9 term9). Qed.
Lemma lem7671373 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671374 : term209 = term9.
Proof. exact (EQ_MP (@lem7671373) (@lem940073)). Qed.
Lemma lem7671375 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671376 : term207 = term167.
Proof. exact (MK_COMB (@lem7671375) (@lem7671374)). Qed.
Lemma lem7671377 : term206 = term167.
Proof. exact (TRANS (@lem7671372) (@lem7671376)). Qed.
Lemma lem7671379 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7671380 : term233 = term238.
Proof. exact (@lem7671379 term9 term9). Qed.
Lemma lem7671381 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671382 : term209 = term9.
Proof. exact (EQ_MP (@lem7671381) (@lem940073)). Qed.
Lemma lem7671383 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671384 : term207 = term167.
Proof. exact (MK_COMB (@lem7671383) (@lem7671382)). Qed.
Lemma lem7671385 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7671386 : term238 = term197.
Proof. exact (MK_COMB (@lem7671385) (@lem7671384)). Qed.
Lemma lem7671387 : term233 = term197.
Proof. exact (TRANS (@lem7671380) (@lem7671386)). Qed.
Lemma lem7671388 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671389 : term239 = term240.
Proof. exact (MK_COMB (@lem7671388) (@lem7671387)). Qed.
Lemma lem7671390 : term235 = term198.
Proof. exact (MK_COMB (@lem7671389) (@lem7671377)). Qed.
Lemma lem7671391 : term234 = term198.
Proof. exact (TRANS (@lem7671369) (@lem7671390)). Qed.
Lemma lem7671392 : term233 = term198.
Proof. exact (TRANS (@lem7671368) (@lem7671391)). Qed.
Lemma lem7671394 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671395 : term198 = term197.
Proof. exact (@lem7671394 term197). Qed.
Lemma lem7671396 : term233 = term197.
Proof. exact (TRANS (@lem7671392) (@lem7671395)). Qed.
Lemma lem7671399 (_98797 : int) : (term241 _98797) = (term241 _98797).
Proof. exact (eq_refl (term241 _98797)). Qed.
Lemma lem7671400 (_98797 : int) : (term231 _98797) = (term242 _98797).
Proof. exact (MK_COMB (@lem7671399 _98797) (@lem7671396)). Qed.
Lemma lem7671401 (_98797 : int) : (term230 _98797) = (term242 _98797).
Proof. exact (TRANS (@lem7671359 _98797) (@lem7671400 _98797)). Qed.
Lemma lem7671402 : term258 = term258.
Proof. exact (eq_refl term258). Qed.
Lemma lem7671403 (_98797 : int) : (term257 _98797) = (term259 _98797).
Proof. exact (MK_COMB (@lem7671402) (@lem7671401 _98797)). Qed.
Lemma lem7671404 (_98797 : int) : (term259 _98797) = (term260 _98797).
Proof. exact (@lem1982757 (term224 _98797) term167 term197). Qed.
Lemma lem7671406 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671407 : term197 = term198.
Proof. exact (@lem7671406 term9). Qed.
Lemma lem7671409 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671410 : term167 = term232.
Proof. exact (@lem7671409 term9). Qed.
Lemma lem7671411 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671412 : term258 = term261.
Proof. exact (MK_COMB (@lem7671411) (@lem7671410)). Qed.
Lemma lem7671413 : term262 = term263.
Proof. exact (MK_COMB (@lem7671412) (@lem7671407)). Qed.
Lemma lem7671414 : term264.
Proof. exact (@lem1981473 term167 term167 term197 term167 term153 term167). Qed.
Lemma lem7671416 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671417 : term266 = term267.
Proof. exact (@lem7671416 (NUMERAL 0) term9). Qed.
Lemma lem7671418 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671419 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671420 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671419 h1) (fun h1 : term267 = True => @lem7671418)). Qed.
Lemma lem7671421 : term267 = True.
Proof. exact (EQ_MP (@lem7671420) (@lem7671418)). Qed.
Lemma lem7671422 : term266 = True.
Proof. exact (TRANS (@lem7671417) (@lem7671421)). Qed.
Lemma lem7671423 : True = term266.
Proof. exact (SYM (@lem7671422)). Qed.
Lemma lem7671424 : term266.
Proof. exact (EQ_MP (@lem7671423) (@lem0)). Qed.
Lemma lem7671425 : term269.
Proof. exact (@lem7671414 (@lem7671424)). Qed.
Lemma lem7671427 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671428 : term266 = term267.
Proof. exact (@lem7671427 (NUMERAL 0) term9). Qed.
Lemma lem7671429 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671430 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671431 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671430 h1) (fun h1 : term267 = True => @lem7671429)). Qed.
Lemma lem7671432 : term267 = True.
Proof. exact (EQ_MP (@lem7671431) (@lem7671429)). Qed.
Lemma lem7671433 : term266 = True.
Proof. exact (TRANS (@lem7671428) (@lem7671432)). Qed.
Lemma lem7671434 : True = term266.
Proof. exact (SYM (@lem7671433)). Qed.
Lemma lem7671435 : term266.
Proof. exact (EQ_MP (@lem7671434) (@lem0)). Qed.
Lemma lem7671436 : term270.
Proof. exact (@lem7671425 (@lem7671435)). Qed.
Lemma lem7671438 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671439 : term266 = term267.
Proof. exact (@lem7671438 (NUMERAL 0) term9). Qed.
Lemma lem7671440 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671441 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671442 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671441 h1) (fun h1 : term267 = True => @lem7671440)). Qed.
Lemma lem7671443 : term267 = True.
Proof. exact (EQ_MP (@lem7671442) (@lem7671440)). Qed.
Lemma lem7671444 : term266 = True.
Proof. exact (TRANS (@lem7671439) (@lem7671443)). Qed.
Lemma lem7671445 : True = term266.
Proof. exact (SYM (@lem7671444)). Qed.
Lemma lem7671446 : term266.
Proof. exact (EQ_MP (@lem7671445) (@lem0)). Qed.
Lemma lem7671447 : term271.
Proof. exact (@lem7671436 (@lem7671446)). Qed.
Lemma lem7671449 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7671450 : term233 = term238.
Proof. exact (@lem7671449 term9 term9). Qed.
Lemma lem7671451 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671452 : term209 = term9.
Proof. exact (EQ_MP (@lem7671451) (@lem940073)). Qed.
Lemma lem7671453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671454 : term207 = term167.
Proof. exact (MK_COMB (@lem7671453) (@lem7671452)). Qed.
Lemma lem7671455 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7671456 : term238 = term197.
Proof. exact (MK_COMB (@lem7671455) (@lem7671454)). Qed.
Lemma lem7671457 : term233 = term197.
Proof. exact (TRANS (@lem7671450) (@lem7671456)). Qed.
Lemma lem7671459 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671460 : term206 = term207.
Proof. exact (@lem7671459 term9 term9). Qed.
Lemma lem7671461 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671462 : term209 = term9.
Proof. exact (EQ_MP (@lem7671461) (@lem940073)). Qed.
Lemma lem7671463 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671464 : term207 = term167.
Proof. exact (MK_COMB (@lem7671463) (@lem7671462)). Qed.
Lemma lem7671465 : term206 = term167.
Proof. exact (TRANS (@lem7671460) (@lem7671464)). Qed.
Lemma lem7671466 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671467 : term272 = term258.
Proof. exact (MK_COMB (@lem7671466) (@lem7671465)). Qed.
Lemma lem7671468 : term273 = term262.
Proof. exact (MK_COMB (@lem7671467) (@lem7671457)). Qed.
Lemma lem7671470 (m : nat) : (term274 m) = term153.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7671471 : term262 = term153.
Proof. exact (@lem7671470 term9). Qed.
Lemma lem7671472 : term273 = term153.
Proof. exact (TRANS (@lem7671468) (@lem7671471)). Qed.
Lemma lem7671473 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671474 : term275 = term276.
Proof. exact (MK_COMB (@lem7671473) (@lem7671472)). Qed.
Lemma lem7671475 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem7671476 : term277 = term278.
Proof. exact (MK_COMB (@lem7671474) (@lem7671475)). Qed.
Lemma lem7671478 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7671479 : term278 = term153.
Proof. exact (@lem7671478 term9). Qed.
Lemma lem7671480 : term277 = term153.
Proof. exact (TRANS (@lem7671476) (@lem7671479)). Qed.
Lemma lem7671482 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671483 : term206 = term207.
Proof. exact (@lem7671482 term9 term9). Qed.
Lemma lem7671484 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671485 : term209 = term9.
Proof. exact (EQ_MP (@lem7671484) (@lem940073)). Qed.
Lemma lem7671486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671487 : term207 = term167.
Proof. exact (MK_COMB (@lem7671486) (@lem7671485)). Qed.
Lemma lem7671488 : term206 = term167.
Proof. exact (TRANS (@lem7671483) (@lem7671487)). Qed.
Lemma lem7671489 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem7671490 : term280 = term278.
Proof. exact (MK_COMB (@lem7671489) (@lem7671488)). Qed.
Lemma lem7671492 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7671493 : term278 = term153.
Proof. exact (@lem7671492 term9). Qed.
Lemma lem7671494 : term280 = term153.
Proof. exact (TRANS (@lem7671490) (@lem7671493)). Qed.
Lemma lem7671495 : term153 = term280.
Proof. exact (SYM (@lem7671494)). Qed.
Lemma lem7671496 : term277 = term280.
Proof. exact (TRANS (@lem7671480) (@lem7671495)). Qed.
Lemma lem7671497 : term263 = term194.
Proof. exact (@lem7671447 (@lem7671496)). Qed.
Lemma lem7671498 : term262 = term194.
Proof. exact (TRANS (@lem7671413) (@lem7671497)). Qed.
Lemma lem7671500 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7671501 : term194 = term153.
Proof. exact (@lem7671500 term153). Qed.
Lemma lem7671502 : term262 = term153.
Proof. exact (TRANS (@lem7671498) (@lem7671501)). Qed.
Lemma lem7671503 (_98797 : int) : (term241 _98797) = (term241 _98797).
Proof. exact (eq_refl (term241 _98797)). Qed.
Lemma lem7671504 (_98797 : int) : (term260 _98797) = (term281 _98797).
Proof. exact (MK_COMB (@lem7671503 _98797) (@lem7671502)). Qed.
Lemma lem7671505 (_98797 : int) : (term259 _98797) = (term281 _98797).
Proof. exact (TRANS (@lem7671404 _98797) (@lem7671504 _98797)). Qed.
Lemma lem7671506 (_98797 : int) : (term281 _98797) = (term224 _98797).
Proof. exact (@lem1982723 (term224 _98797)). Qed.
Lemma lem7671507 (_98797 : int) : (term259 _98797) = (term224 _98797).
Proof. exact (TRANS (@lem7671505 _98797) (@lem7671506 _98797)). Qed.
Lemma lem7671508 (_98797 : int) : (term257 _98797) = (term224 _98797).
Proof. exact (TRANS (@lem7671403 _98797) (@lem7671507 _98797)). Qed.
Lemma lem7671510 (_98797 : int) : (term256 _98797) = (term224 _98797).
Proof. exact (TRANS (@lem7671358 _98797) (@lem7671508 _98797)). Qed.
Lemma lem7671511 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7671512 (_98797 : int) : (term282 _98797) = (term283 _98797).
Proof. exact (MK_COMB (@lem7671511) (@lem7671510 _98797)). Qed.
Lemma lem7671513 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671514 (_98797 : int) : (term255 _98797) = (term284 _98797).
Proof. exact (MK_COMB (@lem7671512 _98797) (@lem7671513)). Qed.
Lemma lem7671515 (_98797 : int) : (term180 _98797) = (term284 _98797).
Proof. exact (TRANS (@lem7671346 _98797) (@lem7671514 _98797)). Qed.
Lemma lem7671516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7671517 (_98798 : int) (_98799 : int) : (term173 _98799 _98798) = (term285 _98798 _98799).
Proof. exact (MK_COMB (@lem7671516) (@lem7671345 _98798 _98799)). Qed.
Lemma lem7671518 (_98798 : int) (_98799 : int) (_98797 : int) : (term181 _98799 _98798 _98797) = (term286 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671517 _98798 _98799) (@lem7671515 _98797)). Qed.
Lemma lem7671519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7671520 (_98798 : int) (_98799 : int) (_98797 : int) : (term182 _98798 _98799 _98797) = (term287 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671519) (@lem7671278 _98798 _98799 _98797)). Qed.
Lemma lem7671521 (_98798 : int) (_98799 : int) (_98797 : int) : (term183 _98799 _98798 _98797) = (term288 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671520 _98798 _98799 _98797) (@lem7671518 _98798 _98799 _98797)). Qed.
Lemma lem7671522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7671523 (_98799 : int) : (term184 _98799) = (term289 _98799).
Proof. exact (MK_COMB (@lem7671522) (@lem7671118 _98799)). Qed.
Lemma lem7671524 (_98798 : int) (_98799 : int) (_98797 : int) : (term185 _98799 _98798 _98797) = (term290 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671523 _98799) (@lem7671521 _98798 _98799 _98797)). Qed.
Lemma lem7671525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7671526 (_98798 : int) : (term184 _98798) = (term289 _98798).
Proof. exact (MK_COMB (@lem7671525) (@lem7671070 _98798)). Qed.
Lemma lem7671527 (_98798 : int) (_98799 : int) (_98797 : int) : (term186 _98799 _98798 _98797) = (term291 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671526 _98798) (@lem7671524 _98798 _98799 _98797)). Qed.
Lemma lem7671528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7671529 (_98797 : int) : (term184 _98797) = (term289 _98797).
Proof. exact (MK_COMB (@lem7671528) (@lem7671022 _98797)). Qed.
Lemma lem7671530 (_98798 : int) (_98799 : int) (_98797 : int) : (term187 _98799 _98798 _98797) = (term292 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671529 _98797) (@lem7671527 _98798 _98799 _98797)). Qed.
Lemma lem7671537 (_98798 : int) (_98799 : int) (_98797 : int) : (term189 _98799 _98798 _98797) = (term292 _98798 _98799 _98797).
Proof. exact (TRANS (@lem7670974 _98799 _98798 _98797) (@lem7671530 _98798 _98799 _98797)). Qed.
Lemma lem7671566 (_98798 : int) (_98799 : int) (_98797 : int) : (term288 _98798 _98799 _98797) = (term293 _98798 _98799 _98797).
Proof. exact (@lem19367 ((term223 _98797 _98798 _98799) = term153) (term250 _98798 _98799 _98797) (term286 _98798 _98799 _98797)). Qed.
Lemma lem7671569 (_98799 : int) : (term289 _98799) = (term289 _98799).
Proof. exact (eq_refl (term289 _98799)). Qed.
Lemma lem7671570 (_98798 : int) (_98799 : int) (_98797 : int) : (term290 _98798 _98799 _98797) = (term294 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671569 _98799) (@lem7671566 _98798 _98799 _98797)). Qed.
Lemma lem7671577 (_98798 : int) (_98799 : int) (_98797 : int) : (term294 _98798 _98799 _98797) = (term295 _98798 _98799 _98797).
Proof. exact (@lem19158 (term296 _98798 _98799 _98797) (term217 _98799) (term297 _98798 _98799 _98797)). Qed.
Lemma lem7671578 (_98798 : int) (_98799 : int) (_98797 : int) : (term290 _98798 _98799 _98797) = (term295 _98798 _98799 _98797).
Proof. exact (TRANS (@lem7671570 _98798 _98799 _98797) (@lem7671577 _98798 _98799 _98797)). Qed.
Lemma lem7671581 (_98798 : int) : (term289 _98798) = (term289 _98798).
Proof. exact (eq_refl (term289 _98798)). Qed.
Lemma lem7671582 (_98798 : int) (_98799 : int) (_98797 : int) : (term291 _98798 _98799 _98797) = (term298 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671581 _98798) (@lem7671578 _98798 _98799 _98797)). Qed.
Lemma lem7671589 (_98798 : int) (_98799 : int) (_98797 : int) : (term298 _98798 _98799 _98797) = (term299 _98798 _98799 _98797).
Proof. exact (@lem19158 (term300 _98798 _98799 _98797) (term217 _98798) (term301 _98798 _98799 _98797)). Qed.
Lemma lem7671590 (_98798 : int) (_98799 : int) (_98797 : int) : (term291 _98798 _98799 _98797) = (term299 _98798 _98799 _98797).
Proof. exact (TRANS (@lem7671582 _98798 _98799 _98797) (@lem7671589 _98798 _98799 _98797)). Qed.
Lemma lem7671593 (_98797 : int) : (term289 _98797) = (term289 _98797).
Proof. exact (eq_refl (term289 _98797)). Qed.
Lemma lem7671594 (_98798 : int) (_98799 : int) (_98797 : int) : (term292 _98798 _98799 _98797) = (term302 _98798 _98799 _98797).
Proof. exact (MK_COMB (@lem7671593 _98797) (@lem7671590 _98798 _98799 _98797)). Qed.
Lemma lem7671601 (_98798 : int) (_98799 : int) (_98797 : int) : (term302 _98798 _98799 _98797) = (term303 _98798 _98799 _98797).
Proof. exact (@lem19158 (term304 _98798 _98799 _98797) (term217 _98797) (term305 _98798 _98799 _98797)). Qed.
Lemma lem7671602 (_98798 : int) (_98799 : int) (_98797 : int) : (term292 _98798 _98799 _98797) = (term303 _98798 _98799 _98797).
Proof. exact (TRANS (@lem7671594 _98798 _98799 _98797) (@lem7671601 _98798 _98799 _98797)). Qed.
Lemma lem7671603 (_98798 : int) (_98799 : int) (_98797 : int) : (term189 _98799 _98798 _98797) = (term303 _98798 _98799 _98797).
Proof. exact (TRANS (@lem7671537 _98798 _98799 _98797) (@lem7671602 _98798 _98799 _98797)). Qed.
Lemma lem7671613 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term303 _98798 _98799 _98797) : term303 _98798 _98799 _98797.
Proof. exact (h1). Qed.
Lemma lem7671614 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term306 _98798 _98799 _98797.
Proof. exact (h1). Qed.
Lemma lem7671615 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term304 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7671614 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671617 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term300 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7671615 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671619 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term296 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7671617 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671621 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term286 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7671619 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671622 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : (term223 _98797 _98798 _98799) = term153.
Proof. exact (proj1 (@lem7671619 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671623 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term284 _98797.
Proof. exact (proj2 (@lem7671621 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671624 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term254 _98798 _98799.
Proof. exact (proj1 (@lem7671621 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671626 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7671627 : term307 = term266.
Proof. exact (@lem7671626 term153 term167). Qed.
Lemma lem7671629 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671630 : term167 = term232.
Proof. exact (@lem7671629 term9). Qed.
Lemma lem7671632 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671633 : term153 = term194.
Proof. exact (@lem7671632 (NUMERAL 0)). Qed.
Lemma lem7671634 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7671635 : term308 = term309.
Proof. exact (MK_COMB (@lem7671634) (@lem7671633)). Qed.
Lemma lem7671636 : term266 = term310.
Proof. exact (MK_COMB (@lem7671635) (@lem7671630)). Qed.
Lemma lem7671637 : term311.
Proof. exact (@lem1980255 term153 term167 term167 term167). Qed.
Lemma lem7671639 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671640 : term266 = term267.
Proof. exact (@lem7671639 (NUMERAL 0) term9). Qed.
Lemma lem7671641 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671642 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671643 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671642 h1) (fun h1 : term267 = True => @lem7671641)). Qed.
Lemma lem7671644 : term267 = True.
Proof. exact (EQ_MP (@lem7671643) (@lem7671641)). Qed.
Lemma lem7671645 : term266 = True.
Proof. exact (TRANS (@lem7671640) (@lem7671644)). Qed.
Lemma lem7671646 : True = term266.
Proof. exact (SYM (@lem7671645)). Qed.
Lemma lem7671647 : term266.
Proof. exact (EQ_MP (@lem7671646) (@lem0)). Qed.
Lemma lem7671648 : term312.
Proof. exact (@lem7671637 (@lem7671647)). Qed.
Lemma lem7671650 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671651 : term266 = term267.
Proof. exact (@lem7671650 (NUMERAL 0) term9). Qed.
Lemma lem7671652 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671653 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671654 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671653 h1) (fun h1 : term267 = True => @lem7671652)). Qed.
Lemma lem7671655 : term267 = True.
Proof. exact (EQ_MP (@lem7671654) (@lem7671652)). Qed.
Lemma lem7671656 : term266 = True.
Proof. exact (TRANS (@lem7671651) (@lem7671655)). Qed.
Lemma lem7671657 : True = term266.
Proof. exact (SYM (@lem7671656)). Qed.
Lemma lem7671658 : term266.
Proof. exact (EQ_MP (@lem7671657) (@lem0)). Qed.
Lemma lem7671659 : term310 = term313.
Proof. exact (@lem7671648 (@lem7671658)). Qed.
Lemma lem7671661 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671662 : term206 = term207.
Proof. exact (@lem7671661 term9 term9). Qed.
Lemma lem7671663 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671664 : term209 = term9.
Proof. exact (EQ_MP (@lem7671663) (@lem940073)). Qed.
Lemma lem7671665 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671666 : term207 = term167.
Proof. exact (MK_COMB (@lem7671665) (@lem7671664)). Qed.
Lemma lem7671667 : term206 = term167.
Proof. exact (TRANS (@lem7671662) (@lem7671666)). Qed.
Lemma lem7671669 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7671670 : term278 = term153.
Proof. exact (@lem7671669 term9). Qed.
Lemma lem7671671 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7671672 : term314 = term308.
Proof. exact (MK_COMB (@lem7671671) (@lem7671670)). Qed.
Lemma lem7671673 : term313 = term266.
Proof. exact (MK_COMB (@lem7671672) (@lem7671667)). Qed.
Lemma lem7671675 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671676 : term266 = term267.
Proof. exact (@lem7671675 (NUMERAL 0) term9). Qed.
Lemma lem7671677 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671678 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671679 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671678 h1) (fun h1 : term267 = True => @lem7671677)). Qed.
Lemma lem7671680 : term267 = True.
Proof. exact (EQ_MP (@lem7671679) (@lem7671677)). Qed.
Lemma lem7671681 : term266 = True.
Proof. exact (TRANS (@lem7671676) (@lem7671680)). Qed.
Lemma lem7671682 : term313 = True.
Proof. exact (TRANS (@lem7671673) (@lem7671681)). Qed.
Lemma lem7671683 : term310 = True.
Proof. exact (TRANS (@lem7671659) (@lem7671682)). Qed.
Lemma lem7671684 : term266 = True.
Proof. exact (TRANS (@lem7671636) (@lem7671683)). Qed.
Lemma lem7671685 : term307 = True.
Proof. exact (TRANS (@lem7671627) (@lem7671684)). Qed.
Lemma lem7671686 : True = term307.
Proof. exact (SYM (@lem7671685)). Qed.
Lemma lem7671687 : term307.
Proof. exact (EQ_MP (@lem7671686) (@lem0)). Qed.
Lemma lem7671688 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term315 _98798 _98799.
Proof. exact (conj (@lem7671687) (@lem7671624 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671690 (x : real) (y : real) : term316 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7671691 (_98798 : int) (_98799 : int) : term317 _98798 _98799.
Proof. exact (@lem7671690 term167 (term243 _98798 _98799)). Qed.
Lemma lem7671692 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term318 _98798 _98799.
Proof. exact (@lem7671691 _98798 _98799 (@lem7671688 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671693 (_98798 : int) (_98799 : int) : (term319 _98798 _98799) = (term243 _98798 _98799).
Proof. exact (@lem1982733 (term243 _98798 _98799)). Qed.
Lemma lem7671694 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7671695 (_98798 : int) (_98799 : int) : (term320 _98798 _98799) = (term253 _98798 _98799).
Proof. exact (MK_COMB (@lem7671694) (@lem7671693 _98798 _98799)). Qed.
Lemma lem7671696 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671697 (_98798 : int) (_98799 : int) : (term318 _98798 _98799) = (term254 _98798 _98799).
Proof. exact (MK_COMB (@lem7671695 _98798 _98799) (@lem7671696)). Qed.
Lemma lem7671698 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term254 _98798 _98799.
Proof. exact (EQ_MP (@lem7671697 _98798 _98799) (@lem7671692 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671700 (y : real) : term321 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7671701 (_98797 : int) (_98798 : int) (_98799 : int) : term322 _98797 _98798 _98799.
Proof. exact (@lem7671700 (term223 _98797 _98798 _98799)). Qed.
Lemma lem7671702 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term323 _98797 _98798 _98799.
Proof. exact (@lem7671701 _98797 _98798 _98799 (@lem7671622 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671703 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term324 _98797 _98798 _98799.
Proof. exact (@lem7671702 _98798 _98799 _98797 h1 term197). Qed.
Lemma lem7671704 (_98797 : int) (_98798 : int) (_98799 : int) : (term324 _98797 _98798 _98799) = ((term325 _98797 _98798 _98799) = term153).
Proof. exact (eq_refl (term324 _98797 _98798 _98799)). Qed.
Lemma lem7671705 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : (term325 _98797 _98798 _98799) = term153.
Proof. exact (EQ_MP (@lem7671704 _98797 _98798 _98799) (@lem7671703 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671706 (_98797 : int) (_98798 : int) (_98799 : int) : (term325 _98797 _98798 _98799) = (term326 _98797 _98798 _98799).
Proof. exact (@lem1982781 (term224 _98797) term197 (term327 _98798 _98799)). Qed.
Lemma lem7671707 (_98798 : int) (_98799 : int) : (term328 _98798 _98799) = (term329 _98798 _98799).
Proof. exact (@lem1982781 (real_of_int _98798) term197 (term224 _98799)). Qed.
Lemma lem7671708 (_98799 : int) : (term330 _98799) = (term331 _98799).
Proof. exact (@lem1982749 term197 term197 (real_of_int _98799)). Qed.
Lemma lem7671710 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671711 : term197 = term198.
Proof. exact (@lem7671710 term9). Qed.
Lemma lem7671713 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671714 : term197 = term198.
Proof. exact (@lem7671713 term9). Qed.
Lemma lem7671715 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671716 : term199 = term200.
Proof. exact (MK_COMB (@lem7671715) (@lem7671714)). Qed.
Lemma lem7671717 : term332 = term333.
Proof. exact (MK_COMB (@lem7671716) (@lem7671711)). Qed.
Lemma lem7671718 : term333 = term334.
Proof. exact (@lem1981613 term197 term197 term167 term167). Qed.
Lemma lem7671720 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671721 : term206 = term207.
Proof. exact (@lem7671720 term9 term9). Qed.
Lemma lem7671722 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671723 : term209 = term9.
Proof. exact (EQ_MP (@lem7671722) (@lem940073)). Qed.
Lemma lem7671724 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671725 : term207 = term167.
Proof. exact (MK_COMB (@lem7671724) (@lem7671723)). Qed.
Lemma lem7671726 : term206 = term167.
Proof. exact (TRANS (@lem7671721) (@lem7671725)). Qed.
Lemma lem7671728 (m : nat) (n : nat) : (term335 m n) = (term205 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7671729 : term332 = term207.
Proof. exact (@lem7671728 term9 term9). Qed.
Lemma lem7671730 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671731 : term209 = term9.
Proof. exact (EQ_MP (@lem7671730) (@lem940073)). Qed.
Lemma lem7671732 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671733 : term207 = term167.
Proof. exact (MK_COMB (@lem7671732) (@lem7671731)). Qed.
Lemma lem7671734 : term332 = term167.
Proof. exact (TRANS (@lem7671729) (@lem7671733)). Qed.
Lemma lem7671735 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671736 : term336 = term337.
Proof. exact (MK_COMB (@lem7671735) (@lem7671734)). Qed.
Lemma lem7671737 : term334 = term232.
Proof. exact (MK_COMB (@lem7671736) (@lem7671726)). Qed.
Lemma lem7671738 : term333 = term232.
Proof. exact (TRANS (@lem7671718) (@lem7671737)). Qed.
Lemma lem7671739 : term332 = term232.
Proof. exact (TRANS (@lem7671717) (@lem7671738)). Qed.
Lemma lem7671741 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671742 : term232 = term167.
Proof. exact (@lem7671741 term167). Qed.
Lemma lem7671743 : term332 = term167.
Proof. exact (TRANS (@lem7671739) (@lem7671742)). Qed.
Lemma lem7671744 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671745 : term338 = term339.
Proof. exact (MK_COMB (@lem7671744) (@lem7671743)). Qed.
Lemma lem7671746 (_98799 : int) : (real_of_int _98799) = (real_of_int _98799).
Proof. exact (eq_refl (real_of_int _98799)). Qed.
Lemma lem7671747 (_98799 : int) : (term331 _98799) = (term340 _98799).
Proof. exact (MK_COMB (@lem7671745) (@lem7671746 _98799)). Qed.
Lemma lem7671748 (_98799 : int) : (term330 _98799) = (term340 _98799).
Proof. exact (TRANS (@lem7671708 _98799) (@lem7671747 _98799)). Qed.
Lemma lem7671749 (_98799 : int) : (term340 _98799) = (real_of_int _98799).
Proof. exact (@lem1982709 (real_of_int _98799)). Qed.
Lemma lem7671750 (_98799 : int) : (term330 _98799) = (real_of_int _98799).
Proof. exact (TRANS (@lem7671748 _98799) (@lem7671749 _98799)). Qed.
Lemma lem7671753 (_98798 : int) : (term241 _98798) = (term241 _98798).
Proof. exact (eq_refl (term241 _98798)). Qed.
Lemma lem7671754 (_98798 : int) (_98799 : int) : (term329 _98798 _98799) = (term341 _98798 _98799).
Proof. exact (MK_COMB (@lem7671753 _98798) (@lem7671750 _98799)). Qed.
Lemma lem7671755 (_98798 : int) (_98799 : int) : (term328 _98798 _98799) = (term341 _98798 _98799).
Proof. exact (TRANS (@lem7671707 _98798 _98799) (@lem7671754 _98798 _98799)). Qed.
Lemma lem7671756 (_98797 : int) : (term330 _98797) = (term331 _98797).
Proof. exact (@lem1982749 term197 term197 (real_of_int _98797)). Qed.
Lemma lem7671758 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671759 : term197 = term198.
Proof. exact (@lem7671758 term9). Qed.
Lemma lem7671761 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671762 : term197 = term198.
Proof. exact (@lem7671761 term9). Qed.
Lemma lem7671763 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671764 : term199 = term200.
Proof. exact (MK_COMB (@lem7671763) (@lem7671762)). Qed.
Lemma lem7671765 : term332 = term333.
Proof. exact (MK_COMB (@lem7671764) (@lem7671759)). Qed.
Lemma lem7671766 : term333 = term334.
Proof. exact (@lem1981613 term197 term197 term167 term167). Qed.
Lemma lem7671768 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671769 : term206 = term207.
Proof. exact (@lem7671768 term9 term9). Qed.
Lemma lem7671770 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671771 : term209 = term9.
Proof. exact (EQ_MP (@lem7671770) (@lem940073)). Qed.
Lemma lem7671772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671773 : term207 = term167.
Proof. exact (MK_COMB (@lem7671772) (@lem7671771)). Qed.
Lemma lem7671774 : term206 = term167.
Proof. exact (TRANS (@lem7671769) (@lem7671773)). Qed.
Lemma lem7671776 (m : nat) (n : nat) : (term335 m n) = (term205 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7671777 : term332 = term207.
Proof. exact (@lem7671776 term9 term9). Qed.
Lemma lem7671778 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671779 : term209 = term9.
Proof. exact (EQ_MP (@lem7671778) (@lem940073)). Qed.
Lemma lem7671780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671781 : term207 = term167.
Proof. exact (MK_COMB (@lem7671780) (@lem7671779)). Qed.
Lemma lem7671782 : term332 = term167.
Proof. exact (TRANS (@lem7671777) (@lem7671781)). Qed.
Lemma lem7671783 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7671784 : term336 = term337.
Proof. exact (MK_COMB (@lem7671783) (@lem7671782)). Qed.
Lemma lem7671785 : term334 = term232.
Proof. exact (MK_COMB (@lem7671784) (@lem7671774)). Qed.
Lemma lem7671786 : term333 = term232.
Proof. exact (TRANS (@lem7671766) (@lem7671785)). Qed.
Lemma lem7671787 : term332 = term232.
Proof. exact (TRANS (@lem7671765) (@lem7671786)). Qed.
Lemma lem7671789 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7671790 : term232 = term167.
Proof. exact (@lem7671789 term167). Qed.
Lemma lem7671791 : term332 = term167.
Proof. exact (TRANS (@lem7671787) (@lem7671790)). Qed.
Lemma lem7671792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671793 : term338 = term339.
Proof. exact (MK_COMB (@lem7671792) (@lem7671791)). Qed.
Lemma lem7671794 (_98797 : int) : (real_of_int _98797) = (real_of_int _98797).
Proof. exact (eq_refl (real_of_int _98797)). Qed.
Lemma lem7671795 (_98797 : int) : (term331 _98797) = (term340 _98797).
Proof. exact (MK_COMB (@lem7671793) (@lem7671794 _98797)). Qed.
Lemma lem7671796 (_98797 : int) : (term330 _98797) = (term340 _98797).
Proof. exact (TRANS (@lem7671756 _98797) (@lem7671795 _98797)). Qed.
Lemma lem7671797 (_98797 : int) : (term340 _98797) = (real_of_int _98797).
Proof. exact (@lem1982709 (real_of_int _98797)). Qed.
Lemma lem7671798 (_98797 : int) : (term330 _98797) = (real_of_int _98797).
Proof. exact (TRANS (@lem7671796 _98797) (@lem7671797 _98797)). Qed.
Lemma lem7671799 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671800 (_98797 : int) : (term342 _98797) = (term168 _98797).
Proof. exact (MK_COMB (@lem7671799) (@lem7671798 _98797)). Qed.
Lemma lem7671801 (_98797 : int) (_98798 : int) (_98799 : int) : (term326 _98797 _98798 _98799) = (term343 _98797 _98798 _98799).
Proof. exact (MK_COMB (@lem7671800 _98797) (@lem7671755 _98798 _98799)). Qed.
Lemma lem7671802 (_98797 : int) (_98798 : int) (_98799 : int) : (term325 _98797 _98798 _98799) = (term343 _98797 _98798 _98799).
Proof. exact (TRANS (@lem7671706 _98797 _98798 _98799) (@lem7671801 _98797 _98798 _98799)). Qed.
Lemma lem7671803 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7671804 (_98797 : int) (_98798 : int) (_98799 : int) : (term344 _98797 _98798 _98799) = (term345 _98797 _98798 _98799).
Proof. exact (MK_COMB (@lem7671803) (@lem7671802 _98797 _98798 _98799)). Qed.
Lemma lem7671805 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7671806 (_98797 : int) (_98798 : int) (_98799 : int) : ((term325 _98797 _98798 _98799) = term153) = ((term343 _98797 _98798 _98799) = term153).
Proof. exact (MK_COMB (@lem7671804 _98797 _98798 _98799) (@lem7671805)). Qed.
Lemma lem7671807 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : (term343 _98797 _98798 _98799) = term153.
Proof. exact (EQ_MP (@lem7671806 _98797 _98798 _98799) (@lem7671705 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671808 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term346 _98797 _98798 _98799.
Proof. exact (conj (@lem7671807 _98798 _98799 _98797 h1) (@lem7671698 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671810 (x : real) (y : real) : term347 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7671811 (_98797 : int) (_98798 : int) (_98799 : int) : term348 _98797 _98798 _98799.
Proof. exact (@lem7671810 (term343 _98797 _98798 _98799) (term243 _98798 _98799)). Qed.
Lemma lem7671812 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term349 _98797 _98798 _98799.
Proof. exact (@lem7671811 _98797 _98798 _98799 (@lem7671808 _98798 _98799 _98797 h1)). Qed.
Lemma lem7671813 (_98797 : int) (_98798 : int) (_98799 : int) : (term350 _98797 _98798 _98799) = (term351 _98797 _98798 _98799).
Proof. exact (@lem1982755 (real_of_int _98797) (term341 _98798 _98799) (term243 _98798 _98799)). Qed.
Lemma lem7671814 (_98798 : int) (_98799 : int) : (term352 _98798 _98799) = (term353 _98798 _98799).
Proof. exact (@lem1982753 (term224 _98798) (real_of_int _98798) (real_of_int _98799) (term242 _98799)). Qed.
Lemma lem7671815 (_98798 : int) : (term354 _98798) = (term355 _98798).
Proof. exact (@lem1982713 term197 (real_of_int _98798)). Qed.
Lemma lem7671817 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671818 : term167 = term232.
Proof. exact (@lem7671817 term9). Qed.
Lemma lem7671820 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671821 : term197 = term198.
Proof. exact (@lem7671820 term9). Qed.
Lemma lem7671822 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671823 : term356 = term357.
Proof. exact (MK_COMB (@lem7671822) (@lem7671821)). Qed.
Lemma lem7671824 : term358 = term359.
Proof. exact (MK_COMB (@lem7671823) (@lem7671818)). Qed.
Lemma lem7671825 : term360.
Proof. exact (@lem1981473 term197 term167 term167 term167 term153 term167). Qed.
Lemma lem7671827 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671828 : term266 = term267.
Proof. exact (@lem7671827 (NUMERAL 0) term9). Qed.
Lemma lem7671829 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671830 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671831 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671830 h1) (fun h1 : term267 = True => @lem7671829)). Qed.
Lemma lem7671832 : term267 = True.
Proof. exact (EQ_MP (@lem7671831) (@lem7671829)). Qed.
Lemma lem7671833 : term266 = True.
Proof. exact (TRANS (@lem7671828) (@lem7671832)). Qed.
Lemma lem7671834 : True = term266.
Proof. exact (SYM (@lem7671833)). Qed.
Lemma lem7671835 : term266.
Proof. exact (EQ_MP (@lem7671834) (@lem0)). Qed.
Lemma lem7671836 : term361.
Proof. exact (@lem7671825 (@lem7671835)). Qed.
Lemma lem7671838 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671839 : term266 = term267.
Proof. exact (@lem7671838 (NUMERAL 0) term9). Qed.
Lemma lem7671840 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671841 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671842 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671841 h1) (fun h1 : term267 = True => @lem7671840)). Qed.
Lemma lem7671843 : term267 = True.
Proof. exact (EQ_MP (@lem7671842) (@lem7671840)). Qed.
Lemma lem7671844 : term266 = True.
Proof. exact (TRANS (@lem7671839) (@lem7671843)). Qed.
Lemma lem7671845 : True = term266.
Proof. exact (SYM (@lem7671844)). Qed.
Lemma lem7671846 : term266.
Proof. exact (EQ_MP (@lem7671845) (@lem0)). Qed.
Lemma lem7671847 : term362.
Proof. exact (@lem7671836 (@lem7671846)). Qed.
Lemma lem7671849 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671850 : term266 = term267.
Proof. exact (@lem7671849 (NUMERAL 0) term9). Qed.
Lemma lem7671851 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671852 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671853 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671852 h1) (fun h1 : term267 = True => @lem7671851)). Qed.
Lemma lem7671854 : term267 = True.
Proof. exact (EQ_MP (@lem7671853) (@lem7671851)). Qed.
Lemma lem7671855 : term266 = True.
Proof. exact (TRANS (@lem7671850) (@lem7671854)). Qed.
Lemma lem7671856 : True = term266.
Proof. exact (SYM (@lem7671855)). Qed.
Lemma lem7671857 : term266.
Proof. exact (EQ_MP (@lem7671856) (@lem0)). Qed.
Lemma lem7671858 : term363.
Proof. exact (@lem7671847 (@lem7671857)). Qed.
Lemma lem7671860 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671861 : term206 = term207.
Proof. exact (@lem7671860 term9 term9). Qed.
Lemma lem7671862 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671863 : term209 = term9.
Proof. exact (EQ_MP (@lem7671862) (@lem940073)). Qed.
Lemma lem7671864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671865 : term207 = term167.
Proof. exact (MK_COMB (@lem7671864) (@lem7671863)). Qed.
Lemma lem7671866 : term206 = term167.
Proof. exact (TRANS (@lem7671861) (@lem7671865)). Qed.
Lemma lem7671868 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7671869 : term233 = term238.
Proof. exact (@lem7671868 term9 term9). Qed.
Lemma lem7671870 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671871 : term209 = term9.
Proof. exact (EQ_MP (@lem7671870) (@lem940073)). Qed.
Lemma lem7671872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671873 : term207 = term167.
Proof. exact (MK_COMB (@lem7671872) (@lem7671871)). Qed.
Lemma lem7671874 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7671875 : term238 = term197.
Proof. exact (MK_COMB (@lem7671874) (@lem7671873)). Qed.
Lemma lem7671876 : term233 = term197.
Proof. exact (TRANS (@lem7671869) (@lem7671875)). Qed.
Lemma lem7671877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671878 : term364 = term356.
Proof. exact (MK_COMB (@lem7671877) (@lem7671876)). Qed.
Lemma lem7671879 : term365 = term358.
Proof. exact (MK_COMB (@lem7671878) (@lem7671866)). Qed.
Lemma lem7671881 (m : nat) : (term366 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7671882 : term358 = term153.
Proof. exact (@lem7671881 term9). Qed.
Lemma lem7671883 : term365 = term153.
Proof. exact (TRANS (@lem7671879) (@lem7671882)). Qed.
Lemma lem7671884 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671885 : term367 = term276.
Proof. exact (MK_COMB (@lem7671884) (@lem7671883)). Qed.
Lemma lem7671886 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem7671887 : term368 = term278.
Proof. exact (MK_COMB (@lem7671885) (@lem7671886)). Qed.
Lemma lem7671889 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7671890 : term278 = term153.
Proof. exact (@lem7671889 term9). Qed.
Lemma lem7671891 : term368 = term153.
Proof. exact (TRANS (@lem7671887) (@lem7671890)). Qed.
Lemma lem7671893 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671894 : term206 = term207.
Proof. exact (@lem7671893 term9 term9). Qed.
Lemma lem7671895 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671896 : term209 = term9.
Proof. exact (EQ_MP (@lem7671895) (@lem940073)). Qed.
Lemma lem7671897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671898 : term207 = term167.
Proof. exact (MK_COMB (@lem7671897) (@lem7671896)). Qed.
Lemma lem7671899 : term206 = term167.
Proof. exact (TRANS (@lem7671894) (@lem7671898)). Qed.
Lemma lem7671900 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem7671901 : term280 = term278.
Proof. exact (MK_COMB (@lem7671900) (@lem7671899)). Qed.
Lemma lem7671903 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7671904 : term278 = term153.
Proof. exact (@lem7671903 term9). Qed.
Lemma lem7671905 : term280 = term153.
Proof. exact (TRANS (@lem7671901) (@lem7671904)). Qed.
Lemma lem7671906 : term153 = term280.
Proof. exact (SYM (@lem7671905)). Qed.
Lemma lem7671907 : term368 = term280.
Proof. exact (TRANS (@lem7671891) (@lem7671906)). Qed.
Lemma lem7671908 : term359 = term194.
Proof. exact (@lem7671858 (@lem7671907)). Qed.
Lemma lem7671909 : term358 = term194.
Proof. exact (TRANS (@lem7671824) (@lem7671908)). Qed.
Lemma lem7671911 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7671912 : term194 = term153.
Proof. exact (@lem7671911 term153). Qed.
Lemma lem7671913 : term358 = term153.
Proof. exact (TRANS (@lem7671909) (@lem7671912)). Qed.
Lemma lem7671914 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671915 : term369 = term276.
Proof. exact (MK_COMB (@lem7671914) (@lem7671913)). Qed.
Lemma lem7671916 (_98798 : int) : (real_of_int _98798) = (real_of_int _98798).
Proof. exact (eq_refl (real_of_int _98798)). Qed.
Lemma lem7671917 (_98798 : int) : (term355 _98798) = (term370 _98798).
Proof. exact (MK_COMB (@lem7671915) (@lem7671916 _98798)). Qed.
Lemma lem7671918 (_98798 : int) : (term354 _98798) = (term370 _98798).
Proof. exact (TRANS (@lem7671815 _98798) (@lem7671917 _98798)). Qed.
Lemma lem7671919 (_98798 : int) : (term370 _98798) = term153.
Proof. exact (@lem1982719 (real_of_int _98798)). Qed.
Lemma lem7671920 (_98798 : int) : (term354 _98798) = term153.
Proof. exact (TRANS (@lem7671918 _98798) (@lem7671919 _98798)). Qed.
Lemma lem7671921 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671922 (_98798 : int) : (term371 _98798) = term372.
Proof. exact (MK_COMB (@lem7671921) (@lem7671920 _98798)). Qed.
Lemma lem7671923 (_98799 : int) : (term373 _98799) = (term374 _98799).
Proof. exact (@lem1982763 (real_of_int _98799) (term224 _98799) term197). Qed.
Lemma lem7671924 (_98799 : int) : (term375 _98799) = (term355 _98799).
Proof. exact (@lem1982715 term197 (real_of_int _98799)). Qed.
Lemma lem7671926 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7671927 : term167 = term232.
Proof. exact (@lem7671926 term9). Qed.
Lemma lem7671929 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7671930 : term197 = term198.
Proof. exact (@lem7671929 term9). Qed.
Lemma lem7671931 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671932 : term356 = term357.
Proof. exact (MK_COMB (@lem7671931) (@lem7671930)). Qed.
Lemma lem7671933 : term358 = term359.
Proof. exact (MK_COMB (@lem7671932) (@lem7671927)). Qed.
Lemma lem7671934 : term360.
Proof. exact (@lem1981473 term197 term167 term167 term167 term153 term167). Qed.
Lemma lem7671936 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671937 : term266 = term267.
Proof. exact (@lem7671936 (NUMERAL 0) term9). Qed.
Lemma lem7671938 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671939 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671940 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671939 h1) (fun h1 : term267 = True => @lem7671938)). Qed.
Lemma lem7671941 : term267 = True.
Proof. exact (EQ_MP (@lem7671940) (@lem7671938)). Qed.
Lemma lem7671942 : term266 = True.
Proof. exact (TRANS (@lem7671937) (@lem7671941)). Qed.
Lemma lem7671943 : True = term266.
Proof. exact (SYM (@lem7671942)). Qed.
Lemma lem7671944 : term266.
Proof. exact (EQ_MP (@lem7671943) (@lem0)). Qed.
Lemma lem7671945 : term361.
Proof. exact (@lem7671934 (@lem7671944)). Qed.
Lemma lem7671947 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671948 : term266 = term267.
Proof. exact (@lem7671947 (NUMERAL 0) term9). Qed.
Lemma lem7671949 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671950 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671951 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671950 h1) (fun h1 : term267 = True => @lem7671949)). Qed.
Lemma lem7671952 : term267 = True.
Proof. exact (EQ_MP (@lem7671951) (@lem7671949)). Qed.
Lemma lem7671953 : term266 = True.
Proof. exact (TRANS (@lem7671948) (@lem7671952)). Qed.
Lemma lem7671954 : True = term266.
Proof. exact (SYM (@lem7671953)). Qed.
Lemma lem7671955 : term266.
Proof. exact (EQ_MP (@lem7671954) (@lem0)). Qed.
Lemma lem7671956 : term362.
Proof. exact (@lem7671945 (@lem7671955)). Qed.
Lemma lem7671958 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7671959 : term266 = term267.
Proof. exact (@lem7671958 (NUMERAL 0) term9). Qed.
Lemma lem7671960 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7671961 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7671962 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7671961 h1) (fun h1 : term267 = True => @lem7671960)). Qed.
Lemma lem7671963 : term267 = True.
Proof. exact (EQ_MP (@lem7671962) (@lem7671960)). Qed.
Lemma lem7671964 : term266 = True.
Proof. exact (TRANS (@lem7671959) (@lem7671963)). Qed.
Lemma lem7671965 : True = term266.
Proof. exact (SYM (@lem7671964)). Qed.
Lemma lem7671966 : term266.
Proof. exact (EQ_MP (@lem7671965) (@lem0)). Qed.
Lemma lem7671967 : term363.
Proof. exact (@lem7671956 (@lem7671966)). Qed.
Lemma lem7671969 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7671970 : term206 = term207.
Proof. exact (@lem7671969 term9 term9). Qed.
Lemma lem7671971 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671972 : term209 = term9.
Proof. exact (EQ_MP (@lem7671971) (@lem940073)). Qed.
Lemma lem7671973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671974 : term207 = term167.
Proof. exact (MK_COMB (@lem7671973) (@lem7671972)). Qed.
Lemma lem7671975 : term206 = term167.
Proof. exact (TRANS (@lem7671970) (@lem7671974)). Qed.
Lemma lem7671977 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7671978 : term233 = term238.
Proof. exact (@lem7671977 term9 term9). Qed.
Lemma lem7671979 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7671980 : term209 = term9.
Proof. exact (EQ_MP (@lem7671979) (@lem940073)). Qed.
Lemma lem7671981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7671982 : term207 = term167.
Proof. exact (MK_COMB (@lem7671981) (@lem7671980)). Qed.
Lemma lem7671983 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7671984 : term238 = term197.
Proof. exact (MK_COMB (@lem7671983) (@lem7671982)). Qed.
Lemma lem7671985 : term233 = term197.
Proof. exact (TRANS (@lem7671978) (@lem7671984)). Qed.
Lemma lem7671986 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7671987 : term364 = term356.
Proof. exact (MK_COMB (@lem7671986) (@lem7671985)). Qed.
Lemma lem7671988 : term365 = term358.
Proof. exact (MK_COMB (@lem7671987) (@lem7671975)). Qed.
Lemma lem7671990 (m : nat) : (term366 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7671991 : term358 = term153.
Proof. exact (@lem7671990 term9). Qed.
Lemma lem7671992 : term365 = term153.
Proof. exact (TRANS (@lem7671988) (@lem7671991)). Qed.
Lemma lem7671993 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7671994 : term367 = term276.
Proof. exact (MK_COMB (@lem7671993) (@lem7671992)). Qed.
Lemma lem7671995 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem7671996 : term368 = term278.
Proof. exact (MK_COMB (@lem7671994) (@lem7671995)). Qed.
Lemma lem7671998 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7671999 : term278 = term153.
Proof. exact (@lem7671998 term9). Qed.
Lemma lem7672000 : term368 = term153.
Proof. exact (TRANS (@lem7671996) (@lem7671999)). Qed.
Lemma lem7672002 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672003 : term206 = term207.
Proof. exact (@lem7672002 term9 term9). Qed.
Lemma lem7672004 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672005 : term209 = term9.
Proof. exact (EQ_MP (@lem7672004) (@lem940073)). Qed.
Lemma lem7672006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672007 : term207 = term167.
Proof. exact (MK_COMB (@lem7672006) (@lem7672005)). Qed.
Lemma lem7672008 : term206 = term167.
Proof. exact (TRANS (@lem7672003) (@lem7672007)). Qed.
Lemma lem7672009 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem7672010 : term280 = term278.
Proof. exact (MK_COMB (@lem7672009) (@lem7672008)). Qed.
Lemma lem7672012 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672013 : term278 = term153.
Proof. exact (@lem7672012 term9). Qed.
Lemma lem7672014 : term280 = term153.
Proof. exact (TRANS (@lem7672010) (@lem7672013)). Qed.
Lemma lem7672015 : term153 = term280.
Proof. exact (SYM (@lem7672014)). Qed.
Lemma lem7672016 : term368 = term280.
Proof. exact (TRANS (@lem7672000) (@lem7672015)). Qed.
Lemma lem7672017 : term359 = term194.
Proof. exact (@lem7671967 (@lem7672016)). Qed.
Lemma lem7672018 : term358 = term194.
Proof. exact (TRANS (@lem7671933) (@lem7672017)). Qed.
Lemma lem7672020 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7672021 : term194 = term153.
Proof. exact (@lem7672020 term153). Qed.
Lemma lem7672022 : term358 = term153.
Proof. exact (TRANS (@lem7672018) (@lem7672021)). Qed.
Lemma lem7672023 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672024 : term369 = term276.
Proof. exact (MK_COMB (@lem7672023) (@lem7672022)). Qed.
Lemma lem7672025 (_98799 : int) : (real_of_int _98799) = (real_of_int _98799).
Proof. exact (eq_refl (real_of_int _98799)). Qed.
Lemma lem7672026 (_98799 : int) : (term355 _98799) = (term370 _98799).
Proof. exact (MK_COMB (@lem7672024) (@lem7672025 _98799)). Qed.
Lemma lem7672027 (_98799 : int) : (term375 _98799) = (term370 _98799).
Proof. exact (TRANS (@lem7671924 _98799) (@lem7672026 _98799)). Qed.
Lemma lem7672028 (_98799 : int) : (term370 _98799) = term153.
Proof. exact (@lem1982719 (real_of_int _98799)). Qed.
Lemma lem7672029 (_98799 : int) : (term375 _98799) = term153.
Proof. exact (TRANS (@lem7672027 _98799) (@lem7672028 _98799)). Qed.
Lemma lem7672030 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672031 (_98799 : int) : (term376 _98799) = term372.
Proof. exact (MK_COMB (@lem7672030) (@lem7672029 _98799)). Qed.
Lemma lem7672032 : term197 = term197.
Proof. exact (eq_refl term197). Qed.
Lemma lem7672033 (_98799 : int) : (term374 _98799) = term377.
Proof. exact (MK_COMB (@lem7672031 _98799) (@lem7672032)). Qed.
Lemma lem7672034 (_98799 : int) : (term373 _98799) = term377.
Proof. exact (TRANS (@lem7671923 _98799) (@lem7672033 _98799)). Qed.
Lemma lem7672035 : term377 = term197.
Proof. exact (@lem1982721 term197). Qed.
Lemma lem7672036 (_98799 : int) : (term373 _98799) = term197.
Proof. exact (TRANS (@lem7672034 _98799) (@lem7672035)). Qed.
Lemma lem7672037 (_98798 : int) (_98799 : int) : (term353 _98798 _98799) = term377.
Proof. exact (MK_COMB (@lem7671922 _98798) (@lem7672036 _98799)). Qed.
Lemma lem7672038 (_98798 : int) (_98799 : int) : (term352 _98798 _98799) = term377.
Proof. exact (TRANS (@lem7671814 _98798 _98799) (@lem7672037 _98798 _98799)). Qed.
Lemma lem7672039 : term377 = term197.
Proof. exact (@lem1982721 term197). Qed.
Lemma lem7672040 (_98798 : int) (_98799 : int) : (term352 _98798 _98799) = term197.
Proof. exact (TRANS (@lem7672038 _98798 _98799) (@lem7672039)). Qed.
Lemma lem7672041 (_98797 : int) : (term168 _98797) = (term168 _98797).
Proof. exact (eq_refl (term168 _98797)). Qed.
Lemma lem7672042 (_98798 : int) (_98799 : int) (_98797 : int) : (term351 _98797 _98798 _98799) = (term378 _98797).
Proof. exact (MK_COMB (@lem7672041 _98797) (@lem7672040 _98798 _98799)). Qed.
Lemma lem7672043 (_98798 : int) (_98799 : int) (_98797 : int) : (term350 _98797 _98798 _98799) = (term378 _98797).
Proof. exact (TRANS (@lem7671813 _98797 _98798 _98799) (@lem7672042 _98798 _98799 _98797)). Qed.
Lemma lem7672044 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7672045 (_98798 : int) (_98799 : int) (_98797 : int) : (term379 _98797 _98798 _98799) = (term380 _98797).
Proof. exact (MK_COMB (@lem7672044) (@lem7672043 _98798 _98799 _98797)). Qed.
Lemma lem7672046 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7672047 (_98798 : int) (_98799 : int) (_98797 : int) : (term349 _98797 _98798 _98799) = (term381 _98797).
Proof. exact (MK_COMB (@lem7672045 _98798 _98799 _98797) (@lem7672046)). Qed.
Lemma lem7672048 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term381 _98797.
Proof. exact (EQ_MP (@lem7672047 _98798 _98799 _98797) (@lem7671812 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672050 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7672051 : term307 = term266.
Proof. exact (@lem7672050 term153 term167). Qed.
Lemma lem7672053 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672054 : term167 = term232.
Proof. exact (@lem7672053 term9). Qed.
Lemma lem7672056 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672057 : term153 = term194.
Proof. exact (@lem7672056 (NUMERAL 0)). Qed.
Lemma lem7672058 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672059 : term308 = term309.
Proof. exact (MK_COMB (@lem7672058) (@lem7672057)). Qed.
Lemma lem7672060 : term266 = term310.
Proof. exact (MK_COMB (@lem7672059) (@lem7672054)). Qed.
Lemma lem7672061 : term311.
Proof. exact (@lem1980255 term153 term167 term167 term167). Qed.
Lemma lem7672063 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672064 : term266 = term267.
Proof. exact (@lem7672063 (NUMERAL 0) term9). Qed.
Lemma lem7672065 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672066 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672067 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672066 h1) (fun h1 : term267 = True => @lem7672065)). Qed.
Lemma lem7672068 : term267 = True.
Proof. exact (EQ_MP (@lem7672067) (@lem7672065)). Qed.
Lemma lem7672069 : term266 = True.
Proof. exact (TRANS (@lem7672064) (@lem7672068)). Qed.
Lemma lem7672070 : True = term266.
Proof. exact (SYM (@lem7672069)). Qed.
Lemma lem7672071 : term266.
Proof. exact (EQ_MP (@lem7672070) (@lem0)). Qed.
Lemma lem7672072 : term312.
Proof. exact (@lem7672061 (@lem7672071)). Qed.
Lemma lem7672074 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672075 : term266 = term267.
Proof. exact (@lem7672074 (NUMERAL 0) term9). Qed.
Lemma lem7672076 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672077 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672078 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672077 h1) (fun h1 : term267 = True => @lem7672076)). Qed.
Lemma lem7672079 : term267 = True.
Proof. exact (EQ_MP (@lem7672078) (@lem7672076)). Qed.
Lemma lem7672080 : term266 = True.
Proof. exact (TRANS (@lem7672075) (@lem7672079)). Qed.
Lemma lem7672081 : True = term266.
Proof. exact (SYM (@lem7672080)). Qed.
Lemma lem7672082 : term266.
Proof. exact (EQ_MP (@lem7672081) (@lem0)). Qed.
Lemma lem7672083 : term310 = term313.
Proof. exact (@lem7672072 (@lem7672082)). Qed.
Lemma lem7672085 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672086 : term206 = term207.
Proof. exact (@lem7672085 term9 term9). Qed.
Lemma lem7672087 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672088 : term209 = term9.
Proof. exact (EQ_MP (@lem7672087) (@lem940073)). Qed.
Lemma lem7672089 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672090 : term207 = term167.
Proof. exact (MK_COMB (@lem7672089) (@lem7672088)). Qed.
Lemma lem7672091 : term206 = term167.
Proof. exact (TRANS (@lem7672086) (@lem7672090)). Qed.
Lemma lem7672093 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672094 : term278 = term153.
Proof. exact (@lem7672093 term9). Qed.
Lemma lem7672095 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672096 : term314 = term308.
Proof. exact (MK_COMB (@lem7672095) (@lem7672094)). Qed.
Lemma lem7672097 : term313 = term266.
Proof. exact (MK_COMB (@lem7672096) (@lem7672091)). Qed.
Lemma lem7672099 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672100 : term266 = term267.
Proof. exact (@lem7672099 (NUMERAL 0) term9). Qed.
Lemma lem7672101 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672102 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672103 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672102 h1) (fun h1 : term267 = True => @lem7672101)). Qed.
Lemma lem7672104 : term267 = True.
Proof. exact (EQ_MP (@lem7672103) (@lem7672101)). Qed.
Lemma lem7672105 : term266 = True.
Proof. exact (TRANS (@lem7672100) (@lem7672104)). Qed.
Lemma lem7672106 : term313 = True.
Proof. exact (TRANS (@lem7672097) (@lem7672105)). Qed.
Lemma lem7672107 : term310 = True.
Proof. exact (TRANS (@lem7672083) (@lem7672106)). Qed.
Lemma lem7672108 : term266 = True.
Proof. exact (TRANS (@lem7672060) (@lem7672107)). Qed.
Lemma lem7672109 : term307 = True.
Proof. exact (TRANS (@lem7672051) (@lem7672108)). Qed.
Lemma lem7672110 : True = term307.
Proof. exact (SYM (@lem7672109)). Qed.
Lemma lem7672111 : term307.
Proof. exact (EQ_MP (@lem7672110) (@lem0)). Qed.
Lemma lem7672112 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term382 _98797.
Proof. exact (conj (@lem7672111) (@lem7672048 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672114 (x : real) (y : real) : term316 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7672115 (_98797 : int) : term383 _98797.
Proof. exact (@lem7672114 term167 (term378 _98797)). Qed.
Lemma lem7672116 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term384 _98797.
Proof. exact (@lem7672115 _98797 (@lem7672112 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672117 (_98797 : int) : (term385 _98797) = (term378 _98797).
Proof. exact (@lem1982733 (term378 _98797)). Qed.
Lemma lem7672118 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7672119 (_98797 : int) : (term386 _98797) = (term380 _98797).
Proof. exact (MK_COMB (@lem7672118) (@lem7672117 _98797)). Qed.
Lemma lem7672120 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7672121 (_98797 : int) : (term384 _98797) = (term381 _98797).
Proof. exact (MK_COMB (@lem7672119 _98797) (@lem7672120)). Qed.
Lemma lem7672122 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term381 _98797.
Proof. exact (EQ_MP (@lem7672121 _98797) (@lem7672116 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672124 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7672125 : term307 = term266.
Proof. exact (@lem7672124 term153 term167). Qed.
Lemma lem7672127 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672128 : term167 = term232.
Proof. exact (@lem7672127 term9). Qed.
Lemma lem7672130 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672131 : term153 = term194.
Proof. exact (@lem7672130 (NUMERAL 0)). Qed.
Lemma lem7672132 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672133 : term308 = term309.
Proof. exact (MK_COMB (@lem7672132) (@lem7672131)). Qed.
Lemma lem7672134 : term266 = term310.
Proof. exact (MK_COMB (@lem7672133) (@lem7672128)). Qed.
Lemma lem7672135 : term311.
Proof. exact (@lem1980255 term153 term167 term167 term167). Qed.
Lemma lem7672137 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672138 : term266 = term267.
Proof. exact (@lem7672137 (NUMERAL 0) term9). Qed.
Lemma lem7672139 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672140 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672141 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672140 h1) (fun h1 : term267 = True => @lem7672139)). Qed.
Lemma lem7672142 : term267 = True.
Proof. exact (EQ_MP (@lem7672141) (@lem7672139)). Qed.
Lemma lem7672143 : term266 = True.
Proof. exact (TRANS (@lem7672138) (@lem7672142)). Qed.
Lemma lem7672144 : True = term266.
Proof. exact (SYM (@lem7672143)). Qed.
Lemma lem7672145 : term266.
Proof. exact (EQ_MP (@lem7672144) (@lem0)). Qed.
Lemma lem7672146 : term312.
Proof. exact (@lem7672135 (@lem7672145)). Qed.
Lemma lem7672148 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672149 : term266 = term267.
Proof. exact (@lem7672148 (NUMERAL 0) term9). Qed.
Lemma lem7672150 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672151 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672152 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672151 h1) (fun h1 : term267 = True => @lem7672150)). Qed.
Lemma lem7672153 : term267 = True.
Proof. exact (EQ_MP (@lem7672152) (@lem7672150)). Qed.
Lemma lem7672154 : term266 = True.
Proof. exact (TRANS (@lem7672149) (@lem7672153)). Qed.
Lemma lem7672155 : True = term266.
Proof. exact (SYM (@lem7672154)). Qed.
Lemma lem7672156 : term266.
Proof. exact (EQ_MP (@lem7672155) (@lem0)). Qed.
Lemma lem7672157 : term310 = term313.
Proof. exact (@lem7672146 (@lem7672156)). Qed.
Lemma lem7672159 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672160 : term206 = term207.
Proof. exact (@lem7672159 term9 term9). Qed.
Lemma lem7672161 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672162 : term209 = term9.
Proof. exact (EQ_MP (@lem7672161) (@lem940073)). Qed.
Lemma lem7672163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672164 : term207 = term167.
Proof. exact (MK_COMB (@lem7672163) (@lem7672162)). Qed.
Lemma lem7672165 : term206 = term167.
Proof. exact (TRANS (@lem7672160) (@lem7672164)). Qed.
Lemma lem7672167 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672168 : term278 = term153.
Proof. exact (@lem7672167 term9). Qed.
Lemma lem7672169 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672170 : term314 = term308.
Proof. exact (MK_COMB (@lem7672169) (@lem7672168)). Qed.
Lemma lem7672171 : term313 = term266.
Proof. exact (MK_COMB (@lem7672170) (@lem7672165)). Qed.
Lemma lem7672173 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672174 : term266 = term267.
Proof. exact (@lem7672173 (NUMERAL 0) term9). Qed.
Lemma lem7672175 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672176 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672177 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672176 h1) (fun h1 : term267 = True => @lem7672175)). Qed.
Lemma lem7672178 : term267 = True.
Proof. exact (EQ_MP (@lem7672177) (@lem7672175)). Qed.
Lemma lem7672179 : term266 = True.
Proof. exact (TRANS (@lem7672174) (@lem7672178)). Qed.
Lemma lem7672180 : term313 = True.
Proof. exact (TRANS (@lem7672171) (@lem7672179)). Qed.
Lemma lem7672181 : term310 = True.
Proof. exact (TRANS (@lem7672157) (@lem7672180)). Qed.
Lemma lem7672182 : term266 = True.
Proof. exact (TRANS (@lem7672134) (@lem7672181)). Qed.
Lemma lem7672183 : term307 = True.
Proof. exact (TRANS (@lem7672125) (@lem7672182)). Qed.
Lemma lem7672184 : True = term307.
Proof. exact (SYM (@lem7672183)). Qed.
Lemma lem7672185 : term307.
Proof. exact (EQ_MP (@lem7672184) (@lem0)). Qed.
Lemma lem7672186 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term387 _98797.
Proof. exact (conj (@lem7672185) (@lem7671623 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672188 (x : real) (y : real) : term316 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7672189 (_98797 : int) : term388 _98797.
Proof. exact (@lem7672188 term167 (term224 _98797)). Qed.
Lemma lem7672190 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term389 _98797.
Proof. exact (@lem7672189 _98797 (@lem7672186 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672191 (_98797 : int) : (term390 _98797) = (term224 _98797).
Proof. exact (@lem1982733 (term224 _98797)). Qed.
Lemma lem7672192 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7672193 (_98797 : int) : (term391 _98797) = (term283 _98797).
Proof. exact (MK_COMB (@lem7672192) (@lem7672191 _98797)). Qed.
Lemma lem7672194 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7672195 (_98797 : int) : (term389 _98797) = (term284 _98797).
Proof. exact (MK_COMB (@lem7672193 _98797) (@lem7672194)). Qed.
Lemma lem7672196 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term284 _98797.
Proof. exact (EQ_MP (@lem7672195 _98797) (@lem7672190 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672197 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term392 _98797.
Proof. exact (conj (@lem7672196 _98798 _98799 _98797 h1) (@lem7672122 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672199 (x : real) (y : real) : term393 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7672200 (_98797 : int) : term394 _98797.
Proof. exact (@lem7672199 (term224 _98797) (term378 _98797)). Qed.
Lemma lem7672201 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term395 _98797.
Proof. exact (@lem7672200 _98797 (@lem7672197 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672202 (_98797 : int) : (term396 _98797) = (term397 _98797).
Proof. exact (@lem1982763 (term224 _98797) (real_of_int _98797) term197). Qed.
Lemma lem7672203 (_98797 : int) : (term354 _98797) = (term355 _98797).
Proof. exact (@lem1982713 term197 (real_of_int _98797)). Qed.
Lemma lem7672205 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672206 : term167 = term232.
Proof. exact (@lem7672205 term9). Qed.
Lemma lem7672208 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7672209 : term197 = term198.
Proof. exact (@lem7672208 term9). Qed.
Lemma lem7672210 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672211 : term356 = term357.
Proof. exact (MK_COMB (@lem7672210) (@lem7672209)). Qed.
Lemma lem7672212 : term358 = term359.
Proof. exact (MK_COMB (@lem7672211) (@lem7672206)). Qed.
Lemma lem7672213 : term360.
Proof. exact (@lem1981473 term197 term167 term167 term167 term153 term167). Qed.
Lemma lem7672215 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672216 : term266 = term267.
Proof. exact (@lem7672215 (NUMERAL 0) term9). Qed.
Lemma lem7672217 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672218 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672219 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672218 h1) (fun h1 : term267 = True => @lem7672217)). Qed.
Lemma lem7672220 : term267 = True.
Proof. exact (EQ_MP (@lem7672219) (@lem7672217)). Qed.
Lemma lem7672221 : term266 = True.
Proof. exact (TRANS (@lem7672216) (@lem7672220)). Qed.
Lemma lem7672222 : True = term266.
Proof. exact (SYM (@lem7672221)). Qed.
Lemma lem7672223 : term266.
Proof. exact (EQ_MP (@lem7672222) (@lem0)). Qed.
Lemma lem7672224 : term361.
Proof. exact (@lem7672213 (@lem7672223)). Qed.
Lemma lem7672226 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672227 : term266 = term267.
Proof. exact (@lem7672226 (NUMERAL 0) term9). Qed.
Lemma lem7672228 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672229 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672230 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672229 h1) (fun h1 : term267 = True => @lem7672228)). Qed.
Lemma lem7672231 : term267 = True.
Proof. exact (EQ_MP (@lem7672230) (@lem7672228)). Qed.
Lemma lem7672232 : term266 = True.
Proof. exact (TRANS (@lem7672227) (@lem7672231)). Qed.
Lemma lem7672233 : True = term266.
Proof. exact (SYM (@lem7672232)). Qed.
Lemma lem7672234 : term266.
Proof. exact (EQ_MP (@lem7672233) (@lem0)). Qed.
Lemma lem7672235 : term362.
Proof. exact (@lem7672224 (@lem7672234)). Qed.
Lemma lem7672237 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672238 : term266 = term267.
Proof. exact (@lem7672237 (NUMERAL 0) term9). Qed.
Lemma lem7672239 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672240 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672241 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672240 h1) (fun h1 : term267 = True => @lem7672239)). Qed.
Lemma lem7672242 : term267 = True.
Proof. exact (EQ_MP (@lem7672241) (@lem7672239)). Qed.
Lemma lem7672243 : term266 = True.
Proof. exact (TRANS (@lem7672238) (@lem7672242)). Qed.
Lemma lem7672244 : True = term266.
Proof. exact (SYM (@lem7672243)). Qed.
Lemma lem7672245 : term266.
Proof. exact (EQ_MP (@lem7672244) (@lem0)). Qed.
Lemma lem7672246 : term363.
Proof. exact (@lem7672235 (@lem7672245)). Qed.
Lemma lem7672248 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672249 : term206 = term207.
Proof. exact (@lem7672248 term9 term9). Qed.
Lemma lem7672250 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672251 : term209 = term9.
Proof. exact (EQ_MP (@lem7672250) (@lem940073)). Qed.
Lemma lem7672252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672253 : term207 = term167.
Proof. exact (MK_COMB (@lem7672252) (@lem7672251)). Qed.
Lemma lem7672254 : term206 = term167.
Proof. exact (TRANS (@lem7672249) (@lem7672253)). Qed.
Lemma lem7672256 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672257 : term233 = term238.
Proof. exact (@lem7672256 term9 term9). Qed.
Lemma lem7672258 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672259 : term209 = term9.
Proof. exact (EQ_MP (@lem7672258) (@lem940073)). Qed.
Lemma lem7672260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672261 : term207 = term167.
Proof. exact (MK_COMB (@lem7672260) (@lem7672259)). Qed.
Lemma lem7672262 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672263 : term238 = term197.
Proof. exact (MK_COMB (@lem7672262) (@lem7672261)). Qed.
Lemma lem7672264 : term233 = term197.
Proof. exact (TRANS (@lem7672257) (@lem7672263)). Qed.
Lemma lem7672265 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672266 : term364 = term356.
Proof. exact (MK_COMB (@lem7672265) (@lem7672264)). Qed.
Lemma lem7672267 : term365 = term358.
Proof. exact (MK_COMB (@lem7672266) (@lem7672254)). Qed.
Lemma lem7672269 (m : nat) : (term366 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7672270 : term358 = term153.
Proof. exact (@lem7672269 term9). Qed.
Lemma lem7672271 : term365 = term153.
Proof. exact (TRANS (@lem7672267) (@lem7672270)). Qed.
Lemma lem7672272 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672273 : term367 = term276.
Proof. exact (MK_COMB (@lem7672272) (@lem7672271)). Qed.
Lemma lem7672274 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem7672275 : term368 = term278.
Proof. exact (MK_COMB (@lem7672273) (@lem7672274)). Qed.
Lemma lem7672277 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672278 : term278 = term153.
Proof. exact (@lem7672277 term9). Qed.
Lemma lem7672279 : term368 = term153.
Proof. exact (TRANS (@lem7672275) (@lem7672278)). Qed.
Lemma lem7672281 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672282 : term206 = term207.
Proof. exact (@lem7672281 term9 term9). Qed.
Lemma lem7672283 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672284 : term209 = term9.
Proof. exact (EQ_MP (@lem7672283) (@lem940073)). Qed.
Lemma lem7672285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672286 : term207 = term167.
Proof. exact (MK_COMB (@lem7672285) (@lem7672284)). Qed.
Lemma lem7672287 : term206 = term167.
Proof. exact (TRANS (@lem7672282) (@lem7672286)). Qed.
Lemma lem7672288 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem7672289 : term280 = term278.
Proof. exact (MK_COMB (@lem7672288) (@lem7672287)). Qed.
Lemma lem7672291 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672292 : term278 = term153.
Proof. exact (@lem7672291 term9). Qed.
Lemma lem7672293 : term280 = term153.
Proof. exact (TRANS (@lem7672289) (@lem7672292)). Qed.
Lemma lem7672294 : term153 = term280.
Proof. exact (SYM (@lem7672293)). Qed.
Lemma lem7672295 : term368 = term280.
Proof. exact (TRANS (@lem7672279) (@lem7672294)). Qed.
Lemma lem7672296 : term359 = term194.
Proof. exact (@lem7672246 (@lem7672295)). Qed.
Lemma lem7672297 : term358 = term194.
Proof. exact (TRANS (@lem7672212) (@lem7672296)). Qed.
Lemma lem7672299 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7672300 : term194 = term153.
Proof. exact (@lem7672299 term153). Qed.
Lemma lem7672301 : term358 = term153.
Proof. exact (TRANS (@lem7672297) (@lem7672300)). Qed.
Lemma lem7672302 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672303 : term369 = term276.
Proof. exact (MK_COMB (@lem7672302) (@lem7672301)). Qed.
Lemma lem7672304 (_98797 : int) : (real_of_int _98797) = (real_of_int _98797).
Proof. exact (eq_refl (real_of_int _98797)). Qed.
Lemma lem7672305 (_98797 : int) : (term355 _98797) = (term370 _98797).
Proof. exact (MK_COMB (@lem7672303) (@lem7672304 _98797)). Qed.
Lemma lem7672306 (_98797 : int) : (term354 _98797) = (term370 _98797).
Proof. exact (TRANS (@lem7672203 _98797) (@lem7672305 _98797)). Qed.
Lemma lem7672307 (_98797 : int) : (term370 _98797) = term153.
Proof. exact (@lem1982719 (real_of_int _98797)). Qed.
Lemma lem7672308 (_98797 : int) : (term354 _98797) = term153.
Proof. exact (TRANS (@lem7672306 _98797) (@lem7672307 _98797)). Qed.
Lemma lem7672309 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672310 (_98797 : int) : (term371 _98797) = term372.
Proof. exact (MK_COMB (@lem7672309) (@lem7672308 _98797)). Qed.
Lemma lem7672311 : term197 = term197.
Proof. exact (eq_refl term197). Qed.
Lemma lem7672312 (_98797 : int) : (term397 _98797) = term377.
Proof. exact (MK_COMB (@lem7672310 _98797) (@lem7672311)). Qed.
Lemma lem7672313 (_98797 : int) : (term396 _98797) = term377.
Proof. exact (TRANS (@lem7672202 _98797) (@lem7672312 _98797)). Qed.
Lemma lem7672314 : term377 = term197.
Proof. exact (@lem1982721 term197). Qed.
Lemma lem7672315 (_98797 : int) : (term396 _98797) = term197.
Proof. exact (TRANS (@lem7672313 _98797) (@lem7672314)). Qed.
Lemma lem7672316 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7672317 (_98797 : int) : (term398 _98797) = term399.
Proof. exact (MK_COMB (@lem7672316) (@lem7672315 _98797)). Qed.
Lemma lem7672318 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7672319 (_98797 : int) : (term395 _98797) = term400.
Proof. exact (MK_COMB (@lem7672317 _98797) (@lem7672318)). Qed.
Lemma lem7672320 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : term400.
Proof. exact (EQ_MP (@lem7672319 _98797) (@lem7672201 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672322 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7672323 : term400 = term401.
Proof. exact (@lem7672322 term153 term197). Qed.
Lemma lem7672325 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7672326 : term197 = term198.
Proof. exact (@lem7672325 term9). Qed.
Lemma lem7672328 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672329 : term153 = term194.
Proof. exact (@lem7672328 (NUMERAL 0)). Qed.
Lemma lem7672330 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7672331 : term155 = term402.
Proof. exact (MK_COMB (@lem7672330) (@lem7672329)). Qed.
Lemma lem7672332 : term401 = term403.
Proof. exact (MK_COMB (@lem7672331) (@lem7672326)). Qed.
Lemma lem7672333 : term404.
Proof. exact (@lem1980026 term153 term167 term197 term167). Qed.
Lemma lem7672335 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672336 : term266 = term267.
Proof. exact (@lem7672335 (NUMERAL 0) term9). Qed.
Lemma lem7672337 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672338 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672339 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672338 h1) (fun h1 : term267 = True => @lem7672337)). Qed.
Lemma lem7672340 : term267 = True.
Proof. exact (EQ_MP (@lem7672339) (@lem7672337)). Qed.
Lemma lem7672341 : term266 = True.
Proof. exact (TRANS (@lem7672336) (@lem7672340)). Qed.
Lemma lem7672342 : True = term266.
Proof. exact (SYM (@lem7672341)). Qed.
Lemma lem7672343 : term266.
Proof. exact (EQ_MP (@lem7672342) (@lem0)). Qed.
Lemma lem7672344 : term405.
Proof. exact (@lem7672333 (@lem7672343)). Qed.
Lemma lem7672346 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672347 : term266 = term267.
Proof. exact (@lem7672346 (NUMERAL 0) term9). Qed.
Lemma lem7672348 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672349 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672350 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672349 h1) (fun h1 : term267 = True => @lem7672348)). Qed.
Lemma lem7672351 : term267 = True.
Proof. exact (EQ_MP (@lem7672350) (@lem7672348)). Qed.
Lemma lem7672352 : term266 = True.
Proof. exact (TRANS (@lem7672347) (@lem7672351)). Qed.
Lemma lem7672353 : True = term266.
Proof. exact (SYM (@lem7672352)). Qed.
Lemma lem7672354 : term266.
Proof. exact (EQ_MP (@lem7672353) (@lem0)). Qed.
Lemma lem7672355 : term403 = term406.
Proof. exact (@lem7672344 (@lem7672354)). Qed.
Lemma lem7672357 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672358 : term233 = term238.
Proof. exact (@lem7672357 term9 term9). Qed.
Lemma lem7672359 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672360 : term209 = term9.
Proof. exact (EQ_MP (@lem7672359) (@lem940073)). Qed.
Lemma lem7672361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672362 : term207 = term167.
Proof. exact (MK_COMB (@lem7672361) (@lem7672360)). Qed.
Lemma lem7672363 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672364 : term238 = term197.
Proof. exact (MK_COMB (@lem7672363) (@lem7672362)). Qed.
Lemma lem7672365 : term233 = term197.
Proof. exact (TRANS (@lem7672358) (@lem7672364)). Qed.
Lemma lem7672367 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672368 : term278 = term153.
Proof. exact (@lem7672367 term9). Qed.
Lemma lem7672369 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7672370 : term407 = term155.
Proof. exact (MK_COMB (@lem7672369) (@lem7672368)). Qed.
Lemma lem7672371 : term406 = term401.
Proof. exact (MK_COMB (@lem7672370) (@lem7672365)). Qed.
Lemma lem7672373 (m : nat) (n : nat) : (term408 m n) = (term409 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7672374 : term401 = term410.
Proof. exact (@lem7672373 (NUMERAL 0) term9). Qed.
Lemma lem7672375 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672376 (h1 : term268 = (BIT1 0)) : (term9 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7672377 : (term268 = (BIT1 0)) = ((term9 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672376 h1) (fun h1 : (term9 = (NUMERAL 0)) = False => @lem7672375)). Qed.
Lemma lem7672378 : (term9 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7672377) (@lem7672375)). Qed.
Lemma lem7672379 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7672380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7672381 : term411 = (and True).
Proof. exact (MK_COMB (@lem7672380) (@lem7672379)). Qed.
Lemma lem7672382 : term410 = (True /\ False).
Proof. exact (MK_COMB (@lem7672381) (@lem7672378)). Qed.
Lemma lem7672384 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7672385 : term410 = False.
Proof. exact (TRANS (@lem7672382) (@lem7672384)). Qed.
Lemma lem7672386 : term401 = False.
Proof. exact (TRANS (@lem7672374) (@lem7672385)). Qed.
Lemma lem7672387 : term406 = False.
Proof. exact (TRANS (@lem7672371) (@lem7672386)). Qed.
Lemma lem7672388 : term403 = False.
Proof. exact (TRANS (@lem7672355) (@lem7672387)). Qed.
Lemma lem7672389 : term401 = False.
Proof. exact (TRANS (@lem7672332) (@lem7672388)). Qed.
Lemma lem7672390 : term400 = False.
Proof. exact (TRANS (@lem7672323) (@lem7672389)). Qed.
Lemma lem7672391 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term306 _98798 _98799 _98797) : False.
Proof. exact (EQ_MP (@lem7672390) (@lem7672320 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672392 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term412 _98798 _98799 _98797.
Proof. exact (h1). Qed.
Lemma lem7672393 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term305 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7672392 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672395 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term301 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7672393 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672397 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term297 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7672395 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672399 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term286 _98798 _98799 _98797.
Proof. exact (proj2 (@lem7672397 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672400 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term250 _98798 _98799 _98797.
Proof. exact (proj1 (@lem7672397 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672402 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term247 _98798 _98799.
Proof. exact (proj1 (@lem7672400 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672404 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term254 _98798 _98799.
Proof. exact (proj1 (@lem7672399 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672406 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7672407 : term307 = term266.
Proof. exact (@lem7672406 term153 term167). Qed.
Lemma lem7672409 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672410 : term167 = term232.
Proof. exact (@lem7672409 term9). Qed.
Lemma lem7672412 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672413 : term153 = term194.
Proof. exact (@lem7672412 (NUMERAL 0)). Qed.
Lemma lem7672414 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672415 : term308 = term309.
Proof. exact (MK_COMB (@lem7672414) (@lem7672413)). Qed.
Lemma lem7672416 : term266 = term310.
Proof. exact (MK_COMB (@lem7672415) (@lem7672410)). Qed.
Lemma lem7672417 : term311.
Proof. exact (@lem1980255 term153 term167 term167 term167). Qed.
Lemma lem7672419 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672420 : term266 = term267.
Proof. exact (@lem7672419 (NUMERAL 0) term9). Qed.
Lemma lem7672421 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672422 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672423 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672422 h1) (fun h1 : term267 = True => @lem7672421)). Qed.
Lemma lem7672424 : term267 = True.
Proof. exact (EQ_MP (@lem7672423) (@lem7672421)). Qed.
Lemma lem7672425 : term266 = True.
Proof. exact (TRANS (@lem7672420) (@lem7672424)). Qed.
Lemma lem7672426 : True = term266.
Proof. exact (SYM (@lem7672425)). Qed.
Lemma lem7672427 : term266.
Proof. exact (EQ_MP (@lem7672426) (@lem0)). Qed.
Lemma lem7672428 : term312.
Proof. exact (@lem7672417 (@lem7672427)). Qed.
Lemma lem7672430 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672431 : term266 = term267.
Proof. exact (@lem7672430 (NUMERAL 0) term9). Qed.
Lemma lem7672432 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672433 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672434 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672433 h1) (fun h1 : term267 = True => @lem7672432)). Qed.
Lemma lem7672435 : term267 = True.
Proof. exact (EQ_MP (@lem7672434) (@lem7672432)). Qed.
Lemma lem7672436 : term266 = True.
Proof. exact (TRANS (@lem7672431) (@lem7672435)). Qed.
Lemma lem7672437 : True = term266.
Proof. exact (SYM (@lem7672436)). Qed.
Lemma lem7672438 : term266.
Proof. exact (EQ_MP (@lem7672437) (@lem0)). Qed.
Lemma lem7672439 : term310 = term313.
Proof. exact (@lem7672428 (@lem7672438)). Qed.
Lemma lem7672441 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672442 : term206 = term207.
Proof. exact (@lem7672441 term9 term9). Qed.
Lemma lem7672443 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672444 : term209 = term9.
Proof. exact (EQ_MP (@lem7672443) (@lem940073)). Qed.
Lemma lem7672445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672446 : term207 = term167.
Proof. exact (MK_COMB (@lem7672445) (@lem7672444)). Qed.
Lemma lem7672447 : term206 = term167.
Proof. exact (TRANS (@lem7672442) (@lem7672446)). Qed.
Lemma lem7672449 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672450 : term278 = term153.
Proof. exact (@lem7672449 term9). Qed.
Lemma lem7672451 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672452 : term314 = term308.
Proof. exact (MK_COMB (@lem7672451) (@lem7672450)). Qed.
Lemma lem7672453 : term313 = term266.
Proof. exact (MK_COMB (@lem7672452) (@lem7672447)). Qed.
Lemma lem7672455 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672456 : term266 = term267.
Proof. exact (@lem7672455 (NUMERAL 0) term9). Qed.
Lemma lem7672457 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672458 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672459 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672458 h1) (fun h1 : term267 = True => @lem7672457)). Qed.
Lemma lem7672460 : term267 = True.
Proof. exact (EQ_MP (@lem7672459) (@lem7672457)). Qed.
Lemma lem7672461 : term266 = True.
Proof. exact (TRANS (@lem7672456) (@lem7672460)). Qed.
Lemma lem7672462 : term313 = True.
Proof. exact (TRANS (@lem7672453) (@lem7672461)). Qed.
Lemma lem7672463 : term310 = True.
Proof. exact (TRANS (@lem7672439) (@lem7672462)). Qed.
Lemma lem7672464 : term266 = True.
Proof. exact (TRANS (@lem7672416) (@lem7672463)). Qed.
Lemma lem7672465 : term307 = True.
Proof. exact (TRANS (@lem7672407) (@lem7672464)). Qed.
Lemma lem7672466 : True = term307.
Proof. exact (SYM (@lem7672465)). Qed.
Lemma lem7672467 : term307.
Proof. exact (EQ_MP (@lem7672466) (@lem0)). Qed.
Lemma lem7672468 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term315 _98798 _98799.
Proof. exact (conj (@lem7672467) (@lem7672404 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672470 (x : real) (y : real) : term316 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7672471 (_98798 : int) (_98799 : int) : term317 _98798 _98799.
Proof. exact (@lem7672470 term167 (term243 _98798 _98799)). Qed.
Lemma lem7672472 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term318 _98798 _98799.
Proof. exact (@lem7672471 _98798 _98799 (@lem7672468 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672473 (_98798 : int) (_98799 : int) : (term319 _98798 _98799) = (term243 _98798 _98799).
Proof. exact (@lem1982733 (term243 _98798 _98799)). Qed.
Lemma lem7672474 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7672475 (_98798 : int) (_98799 : int) : (term320 _98798 _98799) = (term253 _98798 _98799).
Proof. exact (MK_COMB (@lem7672474) (@lem7672473 _98798 _98799)). Qed.
Lemma lem7672476 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7672477 (_98798 : int) (_98799 : int) : (term318 _98798 _98799) = (term254 _98798 _98799).
Proof. exact (MK_COMB (@lem7672475 _98798 _98799) (@lem7672476)). Qed.
Lemma lem7672478 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term254 _98798 _98799.
Proof. exact (EQ_MP (@lem7672477 _98798 _98799) (@lem7672472 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672480 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7672481 : term307 = term266.
Proof. exact (@lem7672480 term153 term167). Qed.
Lemma lem7672483 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672484 : term167 = term232.
Proof. exact (@lem7672483 term9). Qed.
Lemma lem7672486 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672487 : term153 = term194.
Proof. exact (@lem7672486 (NUMERAL 0)). Qed.
Lemma lem7672488 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672489 : term308 = term309.
Proof. exact (MK_COMB (@lem7672488) (@lem7672487)). Qed.
Lemma lem7672490 : term266 = term310.
Proof. exact (MK_COMB (@lem7672489) (@lem7672484)). Qed.
Lemma lem7672491 : term311.
Proof. exact (@lem1980255 term153 term167 term167 term167). Qed.
Lemma lem7672493 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672494 : term266 = term267.
Proof. exact (@lem7672493 (NUMERAL 0) term9). Qed.
Lemma lem7672495 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672496 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672497 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672496 h1) (fun h1 : term267 = True => @lem7672495)). Qed.
Lemma lem7672498 : term267 = True.
Proof. exact (EQ_MP (@lem7672497) (@lem7672495)). Qed.
Lemma lem7672499 : term266 = True.
Proof. exact (TRANS (@lem7672494) (@lem7672498)). Qed.
Lemma lem7672500 : True = term266.
Proof. exact (SYM (@lem7672499)). Qed.
Lemma lem7672501 : term266.
Proof. exact (EQ_MP (@lem7672500) (@lem0)). Qed.
Lemma lem7672502 : term312.
Proof. exact (@lem7672491 (@lem7672501)). Qed.
Lemma lem7672504 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672505 : term266 = term267.
Proof. exact (@lem7672504 (NUMERAL 0) term9). Qed.
Lemma lem7672506 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672507 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672508 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672507 h1) (fun h1 : term267 = True => @lem7672506)). Qed.
Lemma lem7672509 : term267 = True.
Proof. exact (EQ_MP (@lem7672508) (@lem7672506)). Qed.
Lemma lem7672510 : term266 = True.
Proof. exact (TRANS (@lem7672505) (@lem7672509)). Qed.
Lemma lem7672511 : True = term266.
Proof. exact (SYM (@lem7672510)). Qed.
Lemma lem7672512 : term266.
Proof. exact (EQ_MP (@lem7672511) (@lem0)). Qed.
Lemma lem7672513 : term310 = term313.
Proof. exact (@lem7672502 (@lem7672512)). Qed.
Lemma lem7672515 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672516 : term206 = term207.
Proof. exact (@lem7672515 term9 term9). Qed.
Lemma lem7672517 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672518 : term209 = term9.
Proof. exact (EQ_MP (@lem7672517) (@lem940073)). Qed.
Lemma lem7672519 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672520 : term207 = term167.
Proof. exact (MK_COMB (@lem7672519) (@lem7672518)). Qed.
Lemma lem7672521 : term206 = term167.
Proof. exact (TRANS (@lem7672516) (@lem7672520)). Qed.
Lemma lem7672523 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672524 : term278 = term153.
Proof. exact (@lem7672523 term9). Qed.
Lemma lem7672525 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7672526 : term314 = term308.
Proof. exact (MK_COMB (@lem7672525) (@lem7672524)). Qed.
Lemma lem7672527 : term313 = term266.
Proof. exact (MK_COMB (@lem7672526) (@lem7672521)). Qed.
Lemma lem7672529 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672530 : term266 = term267.
Proof. exact (@lem7672529 (NUMERAL 0) term9). Qed.
Lemma lem7672531 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672532 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672533 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672532 h1) (fun h1 : term267 = True => @lem7672531)). Qed.
Lemma lem7672534 : term267 = True.
Proof. exact (EQ_MP (@lem7672533) (@lem7672531)). Qed.
Lemma lem7672535 : term266 = True.
Proof. exact (TRANS (@lem7672530) (@lem7672534)). Qed.
Lemma lem7672536 : term313 = True.
Proof. exact (TRANS (@lem7672527) (@lem7672535)). Qed.
Lemma lem7672537 : term310 = True.
Proof. exact (TRANS (@lem7672513) (@lem7672536)). Qed.
Lemma lem7672538 : term266 = True.
Proof. exact (TRANS (@lem7672490) (@lem7672537)). Qed.
Lemma lem7672539 : term307 = True.
Proof. exact (TRANS (@lem7672481) (@lem7672538)). Qed.
Lemma lem7672540 : True = term307.
Proof. exact (SYM (@lem7672539)). Qed.
Lemma lem7672541 : term307.
Proof. exact (EQ_MP (@lem7672540) (@lem0)). Qed.
Lemma lem7672542 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term413 _98798 _98799.
Proof. exact (conj (@lem7672541) (@lem7672402 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672544 (x : real) (y : real) : term316 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7672545 (_98798 : int) (_98799 : int) : term414 _98798 _98799.
Proof. exact (@lem7672544 term167 (term244 _98798 _98799)). Qed.
Lemma lem7672546 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term415 _98798 _98799.
Proof. exact (@lem7672545 _98798 _98799 (@lem7672542 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672547 (_98798 : int) (_98799 : int) : (term416 _98798 _98799) = (term244 _98798 _98799).
Proof. exact (@lem1982733 (term244 _98798 _98799)). Qed.
Lemma lem7672548 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7672549 (_98798 : int) (_98799 : int) : (term417 _98798 _98799) = (term246 _98798 _98799).
Proof. exact (MK_COMB (@lem7672548) (@lem7672547 _98798 _98799)). Qed.
Lemma lem7672550 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7672551 (_98798 : int) (_98799 : int) : (term415 _98798 _98799) = (term247 _98798 _98799).
Proof. exact (MK_COMB (@lem7672549 _98798 _98799) (@lem7672550)). Qed.
Lemma lem7672552 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term247 _98798 _98799.
Proof. exact (EQ_MP (@lem7672551 _98798 _98799) (@lem7672546 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672553 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term418 _98798 _98799.
Proof. exact (conj (@lem7672552 _98798 _98799 _98797 h1) (@lem7672478 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672555 (x : real) (y : real) : term393 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7672556 (_98798 : int) (_98799 : int) : term419 _98798 _98799.
Proof. exact (@lem7672555 (term244 _98798 _98799) (term243 _98798 _98799)). Qed.
Lemma lem7672557 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term420 _98798 _98799.
Proof. exact (@lem7672556 _98798 _98799 (@lem7672553 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672558 (_98798 : int) (_98799 : int) : (term421 _98798 _98799) = (term422 _98798 _98799).
Proof. exact (@lem1982753 (term224 _98798) (real_of_int _98798) (term378 _98799) (term242 _98799)). Qed.
Lemma lem7672559 (_98798 : int) : (term354 _98798) = (term355 _98798).
Proof. exact (@lem1982713 term197 (real_of_int _98798)). Qed.
Lemma lem7672561 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672562 : term167 = term232.
Proof. exact (@lem7672561 term9). Qed.
Lemma lem7672564 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7672565 : term197 = term198.
Proof. exact (@lem7672564 term9). Qed.
Lemma lem7672566 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672567 : term356 = term357.
Proof. exact (MK_COMB (@lem7672566) (@lem7672565)). Qed.
Lemma lem7672568 : term358 = term359.
Proof. exact (MK_COMB (@lem7672567) (@lem7672562)). Qed.
Lemma lem7672569 : term360.
Proof. exact (@lem1981473 term197 term167 term167 term167 term153 term167). Qed.
Lemma lem7672571 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672572 : term266 = term267.
Proof. exact (@lem7672571 (NUMERAL 0) term9). Qed.
Lemma lem7672573 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672574 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672575 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672574 h1) (fun h1 : term267 = True => @lem7672573)). Qed.
Lemma lem7672576 : term267 = True.
Proof. exact (EQ_MP (@lem7672575) (@lem7672573)). Qed.
Lemma lem7672577 : term266 = True.
Proof. exact (TRANS (@lem7672572) (@lem7672576)). Qed.
Lemma lem7672578 : True = term266.
Proof. exact (SYM (@lem7672577)). Qed.
Lemma lem7672579 : term266.
Proof. exact (EQ_MP (@lem7672578) (@lem0)). Qed.
Lemma lem7672580 : term361.
Proof. exact (@lem7672569 (@lem7672579)). Qed.
Lemma lem7672582 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672583 : term266 = term267.
Proof. exact (@lem7672582 (NUMERAL 0) term9). Qed.
Lemma lem7672584 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672585 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672586 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672585 h1) (fun h1 : term267 = True => @lem7672584)). Qed.
Lemma lem7672587 : term267 = True.
Proof. exact (EQ_MP (@lem7672586) (@lem7672584)). Qed.
Lemma lem7672588 : term266 = True.
Proof. exact (TRANS (@lem7672583) (@lem7672587)). Qed.
Lemma lem7672589 : True = term266.
Proof. exact (SYM (@lem7672588)). Qed.
Lemma lem7672590 : term266.
Proof. exact (EQ_MP (@lem7672589) (@lem0)). Qed.
Lemma lem7672591 : term362.
Proof. exact (@lem7672580 (@lem7672590)). Qed.
Lemma lem7672593 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672594 : term266 = term267.
Proof. exact (@lem7672593 (NUMERAL 0) term9). Qed.
Lemma lem7672595 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672596 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672597 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672596 h1) (fun h1 : term267 = True => @lem7672595)). Qed.
Lemma lem7672598 : term267 = True.
Proof. exact (EQ_MP (@lem7672597) (@lem7672595)). Qed.
Lemma lem7672599 : term266 = True.
Proof. exact (TRANS (@lem7672594) (@lem7672598)). Qed.
Lemma lem7672600 : True = term266.
Proof. exact (SYM (@lem7672599)). Qed.
Lemma lem7672601 : term266.
Proof. exact (EQ_MP (@lem7672600) (@lem0)). Qed.
Lemma lem7672602 : term363.
Proof. exact (@lem7672591 (@lem7672601)). Qed.
Lemma lem7672604 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672605 : term206 = term207.
Proof. exact (@lem7672604 term9 term9). Qed.
Lemma lem7672606 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672607 : term209 = term9.
Proof. exact (EQ_MP (@lem7672606) (@lem940073)). Qed.
Lemma lem7672608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672609 : term207 = term167.
Proof. exact (MK_COMB (@lem7672608) (@lem7672607)). Qed.
Lemma lem7672610 : term206 = term167.
Proof. exact (TRANS (@lem7672605) (@lem7672609)). Qed.
Lemma lem7672612 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672613 : term233 = term238.
Proof. exact (@lem7672612 term9 term9). Qed.
Lemma lem7672614 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672615 : term209 = term9.
Proof. exact (EQ_MP (@lem7672614) (@lem940073)). Qed.
Lemma lem7672616 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672617 : term207 = term167.
Proof. exact (MK_COMB (@lem7672616) (@lem7672615)). Qed.
Lemma lem7672618 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672619 : term238 = term197.
Proof. exact (MK_COMB (@lem7672618) (@lem7672617)). Qed.
Lemma lem7672620 : term233 = term197.
Proof. exact (TRANS (@lem7672613) (@lem7672619)). Qed.
Lemma lem7672621 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672622 : term364 = term356.
Proof. exact (MK_COMB (@lem7672621) (@lem7672620)). Qed.
Lemma lem7672623 : term365 = term358.
Proof. exact (MK_COMB (@lem7672622) (@lem7672610)). Qed.
Lemma lem7672625 (m : nat) : (term366 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7672626 : term358 = term153.
Proof. exact (@lem7672625 term9). Qed.
Lemma lem7672627 : term365 = term153.
Proof. exact (TRANS (@lem7672623) (@lem7672626)). Qed.
Lemma lem7672628 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672629 : term367 = term276.
Proof. exact (MK_COMB (@lem7672628) (@lem7672627)). Qed.
Lemma lem7672630 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem7672631 : term368 = term278.
Proof. exact (MK_COMB (@lem7672629) (@lem7672630)). Qed.
Lemma lem7672633 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672634 : term278 = term153.
Proof. exact (@lem7672633 term9). Qed.
Lemma lem7672635 : term368 = term153.
Proof. exact (TRANS (@lem7672631) (@lem7672634)). Qed.
Lemma lem7672637 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672638 : term206 = term207.
Proof. exact (@lem7672637 term9 term9). Qed.
Lemma lem7672639 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672640 : term209 = term9.
Proof. exact (EQ_MP (@lem7672639) (@lem940073)). Qed.
Lemma lem7672641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672642 : term207 = term167.
Proof. exact (MK_COMB (@lem7672641) (@lem7672640)). Qed.
Lemma lem7672643 : term206 = term167.
Proof. exact (TRANS (@lem7672638) (@lem7672642)). Qed.
Lemma lem7672644 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem7672645 : term280 = term278.
Proof. exact (MK_COMB (@lem7672644) (@lem7672643)). Qed.
Lemma lem7672647 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672648 : term278 = term153.
Proof. exact (@lem7672647 term9). Qed.
Lemma lem7672649 : term280 = term153.
Proof. exact (TRANS (@lem7672645) (@lem7672648)). Qed.
Lemma lem7672650 : term153 = term280.
Proof. exact (SYM (@lem7672649)). Qed.
Lemma lem7672651 : term368 = term280.
Proof. exact (TRANS (@lem7672635) (@lem7672650)). Qed.
Lemma lem7672652 : term359 = term194.
Proof. exact (@lem7672602 (@lem7672651)). Qed.
Lemma lem7672653 : term358 = term194.
Proof. exact (TRANS (@lem7672568) (@lem7672652)). Qed.
Lemma lem7672655 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7672656 : term194 = term153.
Proof. exact (@lem7672655 term153). Qed.
Lemma lem7672657 : term358 = term153.
Proof. exact (TRANS (@lem7672653) (@lem7672656)). Qed.
Lemma lem7672658 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672659 : term369 = term276.
Proof. exact (MK_COMB (@lem7672658) (@lem7672657)). Qed.
Lemma lem7672660 (_98798 : int) : (real_of_int _98798) = (real_of_int _98798).
Proof. exact (eq_refl (real_of_int _98798)). Qed.
Lemma lem7672661 (_98798 : int) : (term355 _98798) = (term370 _98798).
Proof. exact (MK_COMB (@lem7672659) (@lem7672660 _98798)). Qed.
Lemma lem7672662 (_98798 : int) : (term354 _98798) = (term370 _98798).
Proof. exact (TRANS (@lem7672559 _98798) (@lem7672661 _98798)). Qed.
Lemma lem7672663 (_98798 : int) : (term370 _98798) = term153.
Proof. exact (@lem1982719 (real_of_int _98798)). Qed.
Lemma lem7672664 (_98798 : int) : (term354 _98798) = term153.
Proof. exact (TRANS (@lem7672662 _98798) (@lem7672663 _98798)). Qed.
Lemma lem7672665 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672666 (_98798 : int) : (term371 _98798) = term372.
Proof. exact (MK_COMB (@lem7672665) (@lem7672664 _98798)). Qed.
Lemma lem7672667 (_98799 : int) : (term423 _98799) = (term424 _98799).
Proof. exact (@lem1982753 (real_of_int _98799) (term224 _98799) term197 term197). Qed.
Lemma lem7672668 (_98799 : int) : (term375 _98799) = (term355 _98799).
Proof. exact (@lem1982715 term197 (real_of_int _98799)). Qed.
Lemma lem7672670 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672671 : term167 = term232.
Proof. exact (@lem7672670 term9). Qed.
Lemma lem7672673 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7672674 : term197 = term198.
Proof. exact (@lem7672673 term9). Qed.
Lemma lem7672675 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672676 : term356 = term357.
Proof. exact (MK_COMB (@lem7672675) (@lem7672674)). Qed.
Lemma lem7672677 : term358 = term359.
Proof. exact (MK_COMB (@lem7672676) (@lem7672671)). Qed.
Lemma lem7672678 : term360.
Proof. exact (@lem1981473 term197 term167 term167 term167 term153 term167). Qed.
Lemma lem7672680 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672681 : term266 = term267.
Proof. exact (@lem7672680 (NUMERAL 0) term9). Qed.
Lemma lem7672682 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672683 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672684 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672683 h1) (fun h1 : term267 = True => @lem7672682)). Qed.
Lemma lem7672685 : term267 = True.
Proof. exact (EQ_MP (@lem7672684) (@lem7672682)). Qed.
Lemma lem7672686 : term266 = True.
Proof. exact (TRANS (@lem7672681) (@lem7672685)). Qed.
Lemma lem7672687 : True = term266.
Proof. exact (SYM (@lem7672686)). Qed.
Lemma lem7672688 : term266.
Proof. exact (EQ_MP (@lem7672687) (@lem0)). Qed.
Lemma lem7672689 : term361.
Proof. exact (@lem7672678 (@lem7672688)). Qed.
Lemma lem7672691 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672692 : term266 = term267.
Proof. exact (@lem7672691 (NUMERAL 0) term9). Qed.
Lemma lem7672693 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672694 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672695 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672694 h1) (fun h1 : term267 = True => @lem7672693)). Qed.
Lemma lem7672696 : term267 = True.
Proof. exact (EQ_MP (@lem7672695) (@lem7672693)). Qed.
Lemma lem7672697 : term266 = True.
Proof. exact (TRANS (@lem7672692) (@lem7672696)). Qed.
Lemma lem7672698 : True = term266.
Proof. exact (SYM (@lem7672697)). Qed.
Lemma lem7672699 : term266.
Proof. exact (EQ_MP (@lem7672698) (@lem0)). Qed.
Lemma lem7672700 : term362.
Proof. exact (@lem7672689 (@lem7672699)). Qed.
Lemma lem7672702 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672703 : term266 = term267.
Proof. exact (@lem7672702 (NUMERAL 0) term9). Qed.
Lemma lem7672704 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672705 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672706 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672705 h1) (fun h1 : term267 = True => @lem7672704)). Qed.
Lemma lem7672707 : term267 = True.
Proof. exact (EQ_MP (@lem7672706) (@lem7672704)). Qed.
Lemma lem7672708 : term266 = True.
Proof. exact (TRANS (@lem7672703) (@lem7672707)). Qed.
Lemma lem7672709 : True = term266.
Proof. exact (SYM (@lem7672708)). Qed.
Lemma lem7672710 : term266.
Proof. exact (EQ_MP (@lem7672709) (@lem0)). Qed.
Lemma lem7672711 : term363.
Proof. exact (@lem7672700 (@lem7672710)). Qed.
Lemma lem7672713 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672714 : term206 = term207.
Proof. exact (@lem7672713 term9 term9). Qed.
Lemma lem7672715 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672716 : term209 = term9.
Proof. exact (EQ_MP (@lem7672715) (@lem940073)). Qed.
Lemma lem7672717 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672718 : term207 = term167.
Proof. exact (MK_COMB (@lem7672717) (@lem7672716)). Qed.
Lemma lem7672719 : term206 = term167.
Proof. exact (TRANS (@lem7672714) (@lem7672718)). Qed.
Lemma lem7672721 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672722 : term233 = term238.
Proof. exact (@lem7672721 term9 term9). Qed.
Lemma lem7672723 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672724 : term209 = term9.
Proof. exact (EQ_MP (@lem7672723) (@lem940073)). Qed.
Lemma lem7672725 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672726 : term207 = term167.
Proof. exact (MK_COMB (@lem7672725) (@lem7672724)). Qed.
Lemma lem7672727 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672728 : term238 = term197.
Proof. exact (MK_COMB (@lem7672727) (@lem7672726)). Qed.
Lemma lem7672729 : term233 = term197.
Proof. exact (TRANS (@lem7672722) (@lem7672728)). Qed.
Lemma lem7672730 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672731 : term364 = term356.
Proof. exact (MK_COMB (@lem7672730) (@lem7672729)). Qed.
Lemma lem7672732 : term365 = term358.
Proof. exact (MK_COMB (@lem7672731) (@lem7672719)). Qed.
Lemma lem7672734 (m : nat) : (term366 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7672735 : term358 = term153.
Proof. exact (@lem7672734 term9). Qed.
Lemma lem7672736 : term365 = term153.
Proof. exact (TRANS (@lem7672732) (@lem7672735)). Qed.
Lemma lem7672737 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672738 : term367 = term276.
Proof. exact (MK_COMB (@lem7672737) (@lem7672736)). Qed.
Lemma lem7672739 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem7672740 : term368 = term278.
Proof. exact (MK_COMB (@lem7672738) (@lem7672739)). Qed.
Lemma lem7672742 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672743 : term278 = term153.
Proof. exact (@lem7672742 term9). Qed.
Lemma lem7672744 : term368 = term153.
Proof. exact (TRANS (@lem7672740) (@lem7672743)). Qed.
Lemma lem7672746 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672747 : term206 = term207.
Proof. exact (@lem7672746 term9 term9). Qed.
Lemma lem7672748 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672749 : term209 = term9.
Proof. exact (EQ_MP (@lem7672748) (@lem940073)). Qed.
Lemma lem7672750 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672751 : term207 = term167.
Proof. exact (MK_COMB (@lem7672750) (@lem7672749)). Qed.
Lemma lem7672752 : term206 = term167.
Proof. exact (TRANS (@lem7672747) (@lem7672751)). Qed.
Lemma lem7672753 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem7672754 : term280 = term278.
Proof. exact (MK_COMB (@lem7672753) (@lem7672752)). Qed.
Lemma lem7672756 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672757 : term278 = term153.
Proof. exact (@lem7672756 term9). Qed.
Lemma lem7672758 : term280 = term153.
Proof. exact (TRANS (@lem7672754) (@lem7672757)). Qed.
Lemma lem7672759 : term153 = term280.
Proof. exact (SYM (@lem7672758)). Qed.
Lemma lem7672760 : term368 = term280.
Proof. exact (TRANS (@lem7672744) (@lem7672759)). Qed.
Lemma lem7672761 : term359 = term194.
Proof. exact (@lem7672711 (@lem7672760)). Qed.
Lemma lem7672762 : term358 = term194.
Proof. exact (TRANS (@lem7672677) (@lem7672761)). Qed.
Lemma lem7672764 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7672765 : term194 = term153.
Proof. exact (@lem7672764 term153). Qed.
Lemma lem7672766 : term358 = term153.
Proof. exact (TRANS (@lem7672762) (@lem7672765)). Qed.
Lemma lem7672767 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672768 : term369 = term276.
Proof. exact (MK_COMB (@lem7672767) (@lem7672766)). Qed.
Lemma lem7672769 (_98799 : int) : (real_of_int _98799) = (real_of_int _98799).
Proof. exact (eq_refl (real_of_int _98799)). Qed.
Lemma lem7672770 (_98799 : int) : (term355 _98799) = (term370 _98799).
Proof. exact (MK_COMB (@lem7672768) (@lem7672769 _98799)). Qed.
Lemma lem7672771 (_98799 : int) : (term375 _98799) = (term370 _98799).
Proof. exact (TRANS (@lem7672668 _98799) (@lem7672770 _98799)). Qed.
Lemma lem7672772 (_98799 : int) : (term370 _98799) = term153.
Proof. exact (@lem1982719 (real_of_int _98799)). Qed.
Lemma lem7672773 (_98799 : int) : (term375 _98799) = term153.
Proof. exact (TRANS (@lem7672771 _98799) (@lem7672772 _98799)). Qed.
Lemma lem7672774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672775 (_98799 : int) : (term376 _98799) = term372.
Proof. exact (MK_COMB (@lem7672774) (@lem7672773 _98799)). Qed.
Lemma lem7672777 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7672778 : term197 = term198.
Proof. exact (@lem7672777 term9). Qed.
Lemma lem7672780 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7672781 : term197 = term198.
Proof. exact (@lem7672780 term9). Qed.
Lemma lem7672782 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672783 : term356 = term357.
Proof. exact (MK_COMB (@lem7672782) (@lem7672781)). Qed.
Lemma lem7672784 : term425 = term426.
Proof. exact (MK_COMB (@lem7672783) (@lem7672778)). Qed.
Lemma lem7672785 : term427.
Proof. exact (@lem1981473 term197 term167 term197 term167 term428 term167). Qed.
Lemma lem7672787 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672788 : term266 = term267.
Proof. exact (@lem7672787 (NUMERAL 0) term9). Qed.
Lemma lem7672789 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672790 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672791 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672790 h1) (fun h1 : term267 = True => @lem7672789)). Qed.
Lemma lem7672792 : term267 = True.
Proof. exact (EQ_MP (@lem7672791) (@lem7672789)). Qed.
Lemma lem7672793 : term266 = True.
Proof. exact (TRANS (@lem7672788) (@lem7672792)). Qed.
Lemma lem7672794 : True = term266.
Proof. exact (SYM (@lem7672793)). Qed.
Lemma lem7672795 : term266.
Proof. exact (EQ_MP (@lem7672794) (@lem0)). Qed.
Lemma lem7672796 : term429.
Proof. exact (@lem7672785 (@lem7672795)). Qed.
Lemma lem7672798 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672799 : term266 = term267.
Proof. exact (@lem7672798 (NUMERAL 0) term9). Qed.
Lemma lem7672800 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672801 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672802 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672801 h1) (fun h1 : term267 = True => @lem7672800)). Qed.
Lemma lem7672803 : term267 = True.
Proof. exact (EQ_MP (@lem7672802) (@lem7672800)). Qed.
Lemma lem7672804 : term266 = True.
Proof. exact (TRANS (@lem7672799) (@lem7672803)). Qed.
Lemma lem7672805 : True = term266.
Proof. exact (SYM (@lem7672804)). Qed.
Lemma lem7672806 : term266.
Proof. exact (EQ_MP (@lem7672805) (@lem0)). Qed.
Lemma lem7672807 : term430.
Proof. exact (@lem7672796 (@lem7672806)). Qed.
Lemma lem7672809 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672810 : term266 = term267.
Proof. exact (@lem7672809 (NUMERAL 0) term9). Qed.
Lemma lem7672811 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672812 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672813 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672812 h1) (fun h1 : term267 = True => @lem7672811)). Qed.
Lemma lem7672814 : term267 = True.
Proof. exact (EQ_MP (@lem7672813) (@lem7672811)). Qed.
Lemma lem7672815 : term266 = True.
Proof. exact (TRANS (@lem7672810) (@lem7672814)). Qed.
Lemma lem7672816 : True = term266.
Proof. exact (SYM (@lem7672815)). Qed.
Lemma lem7672817 : term266.
Proof. exact (EQ_MP (@lem7672816) (@lem0)). Qed.
Lemma lem7672818 : term431.
Proof. exact (@lem7672807 (@lem7672817)). Qed.
Lemma lem7672820 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672821 : term233 = term238.
Proof. exact (@lem7672820 term9 term9). Qed.
Lemma lem7672822 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672823 : term209 = term9.
Proof. exact (EQ_MP (@lem7672822) (@lem940073)). Qed.
Lemma lem7672824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672825 : term207 = term167.
Proof. exact (MK_COMB (@lem7672824) (@lem7672823)). Qed.
Lemma lem7672826 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672827 : term238 = term197.
Proof. exact (MK_COMB (@lem7672826) (@lem7672825)). Qed.
Lemma lem7672828 : term233 = term197.
Proof. exact (TRANS (@lem7672821) (@lem7672827)). Qed.
Lemma lem7672830 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672831 : term233 = term238.
Proof. exact (@lem7672830 term9 term9). Qed.
Lemma lem7672832 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672833 : term209 = term9.
Proof. exact (EQ_MP (@lem7672832) (@lem940073)). Qed.
Lemma lem7672834 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672835 : term207 = term167.
Proof. exact (MK_COMB (@lem7672834) (@lem7672833)). Qed.
Lemma lem7672836 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672837 : term238 = term197.
Proof. exact (MK_COMB (@lem7672836) (@lem7672835)). Qed.
Lemma lem7672838 : term233 = term197.
Proof. exact (TRANS (@lem7672831) (@lem7672837)). Qed.
Lemma lem7672839 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7672840 : term364 = term356.
Proof. exact (MK_COMB (@lem7672839) (@lem7672838)). Qed.
Lemma lem7672841 : term432 = term425.
Proof. exact (MK_COMB (@lem7672840) (@lem7672828)). Qed.
Lemma lem7672842 : term425 = term433.
Proof. exact (@lem1367763 term9 term9). Qed.
Lemma lem7672843 : term434 = term435.
Proof. exact (@lem706885). Qed.
Lemma lem7672844 : (term434 = term435) = (term436 = term437).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term435). Qed.
Lemma lem7672845 : term436 = term437.
Proof. exact (EQ_MP (@lem7672844) (@lem7672843)). Qed.
Lemma lem7672846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672847 : term438 = term439.
Proof. exact (MK_COMB (@lem7672846) (@lem7672845)). Qed.
Lemma lem7672848 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672849 : term433 = term428.
Proof. exact (MK_COMB (@lem7672848) (@lem7672847)). Qed.
Lemma lem7672850 : term425 = term428.
Proof. exact (TRANS (@lem7672842) (@lem7672849)). Qed.
Lemma lem7672851 : term432 = term428.
Proof. exact (TRANS (@lem7672841) (@lem7672850)). Qed.
Lemma lem7672852 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7672853 : term440 = term441.
Proof. exact (MK_COMB (@lem7672852) (@lem7672851)). Qed.
Lemma lem7672854 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem7672855 : term442 = term443.
Proof. exact (MK_COMB (@lem7672853) (@lem7672854)). Qed.
Lemma lem7672857 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672858 : term443 = term444.
Proof. exact (@lem7672857 term437 term9). Qed.
Lemma lem7672859 : term445 = term435.
Proof. exact (@lem996237 term435). Qed.
Lemma lem7672860 : (term445 = term435) = (term446 = term437).
Proof. exact (@lem1007663 term435 (BIT1 0) term435). Qed.
Lemma lem7672861 : term446 = term437.
Proof. exact (EQ_MP (@lem7672860) (@lem7672859)). Qed.
Lemma lem7672862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672863 : term447 = term439.
Proof. exact (MK_COMB (@lem7672862) (@lem7672861)). Qed.
Lemma lem7672864 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672865 : term444 = term428.
Proof. exact (MK_COMB (@lem7672864) (@lem7672863)). Qed.
Lemma lem7672866 : term443 = term428.
Proof. exact (TRANS (@lem7672858) (@lem7672865)). Qed.
Lemma lem7672867 : term442 = term428.
Proof. exact (TRANS (@lem7672855) (@lem7672866)). Qed.
Lemma lem7672869 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7672870 : term206 = term207.
Proof. exact (@lem7672869 term9 term9). Qed.
Lemma lem7672871 : (term208 = (BIT1 0)) = (term209 = term9).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7672872 : term209 = term9.
Proof. exact (EQ_MP (@lem7672871) (@lem940073)). Qed.
Lemma lem7672873 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672874 : term207 = term167.
Proof. exact (MK_COMB (@lem7672873) (@lem7672872)). Qed.
Lemma lem7672875 : term206 = term167.
Proof. exact (TRANS (@lem7672870) (@lem7672874)). Qed.
Lemma lem7672876 : term441 = term441.
Proof. exact (eq_refl term441). Qed.
Lemma lem7672877 : term448 = term443.
Proof. exact (MK_COMB (@lem7672876) (@lem7672875)). Qed.
Lemma lem7672879 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672880 : term443 = term444.
Proof. exact (@lem7672879 term437 term9). Qed.
Lemma lem7672881 : term445 = term435.
Proof. exact (@lem996237 term435). Qed.
Lemma lem7672882 : (term445 = term435) = (term446 = term437).
Proof. exact (@lem1007663 term435 (BIT1 0) term435). Qed.
Lemma lem7672883 : term446 = term437.
Proof. exact (EQ_MP (@lem7672882) (@lem7672881)). Qed.
Lemma lem7672884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672885 : term447 = term439.
Proof. exact (MK_COMB (@lem7672884) (@lem7672883)). Qed.
Lemma lem7672886 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672887 : term444 = term428.
Proof. exact (MK_COMB (@lem7672886) (@lem7672885)). Qed.
Lemma lem7672888 : term443 = term428.
Proof. exact (TRANS (@lem7672880) (@lem7672887)). Qed.
Lemma lem7672889 : term448 = term428.
Proof. exact (TRANS (@lem7672877) (@lem7672888)). Qed.
Lemma lem7672890 : term428 = term448.
Proof. exact (SYM (@lem7672889)). Qed.
Lemma lem7672891 : term442 = term448.
Proof. exact (TRANS (@lem7672867) (@lem7672890)). Qed.
Lemma lem7672892 : term426 = term449.
Proof. exact (@lem7672818 (@lem7672891)). Qed.
Lemma lem7672893 : term425 = term449.
Proof. exact (TRANS (@lem7672784) (@lem7672892)). Qed.
Lemma lem7672895 (x : real) : (term213 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7672896 : term449 = term428.
Proof. exact (@lem7672895 term428). Qed.
Lemma lem7672897 : term425 = term428.
Proof. exact (TRANS (@lem7672893) (@lem7672896)). Qed.
Lemma lem7672898 (_98799 : int) : (term424 _98799) = term450.
Proof. exact (MK_COMB (@lem7672775 _98799) (@lem7672897)). Qed.
Lemma lem7672899 (_98799 : int) : (term423 _98799) = term450.
Proof. exact (TRANS (@lem7672667 _98799) (@lem7672898 _98799)). Qed.
Lemma lem7672900 : term450 = term428.
Proof. exact (@lem1982721 term428). Qed.
Lemma lem7672901 (_98799 : int) : (term423 _98799) = term428.
Proof. exact (TRANS (@lem7672899 _98799) (@lem7672900)). Qed.
Lemma lem7672902 (_98798 : int) (_98799 : int) : (term422 _98798 _98799) = term450.
Proof. exact (MK_COMB (@lem7672666 _98798) (@lem7672901 _98799)). Qed.
Lemma lem7672903 (_98798 : int) (_98799 : int) : (term421 _98798 _98799) = term450.
Proof. exact (TRANS (@lem7672558 _98798 _98799) (@lem7672902 _98798 _98799)). Qed.
Lemma lem7672904 : term450 = term428.
Proof. exact (@lem1982721 term428). Qed.
Lemma lem7672905 (_98798 : int) (_98799 : int) : (term421 _98798 _98799) = term428.
Proof. exact (TRANS (@lem7672903 _98798 _98799) (@lem7672904)). Qed.
Lemma lem7672906 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7672907 (_98798 : int) (_98799 : int) : (term451 _98798 _98799) = term452.
Proof. exact (MK_COMB (@lem7672906) (@lem7672905 _98798 _98799)). Qed.
Lemma lem7672908 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7672909 (_98798 : int) (_98799 : int) : (term420 _98798 _98799) = term453.
Proof. exact (MK_COMB (@lem7672907 _98798 _98799) (@lem7672908)). Qed.
Lemma lem7672910 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : term453.
Proof. exact (EQ_MP (@lem7672909 _98798 _98799) (@lem7672557 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672912 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7672913 : term453 = term454.
Proof. exact (@lem7672912 term153 term428). Qed.
Lemma lem7672915 (x : nat) : (term195 x) = (term196 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7672916 : term428 = term449.
Proof. exact (@lem7672915 term437). Qed.
Lemma lem7672918 (x : nat) : (real_of_num x) = (term193 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7672919 : term153 = term194.
Proof. exact (@lem7672918 (NUMERAL 0)). Qed.
Lemma lem7672920 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7672921 : term155 = term402.
Proof. exact (MK_COMB (@lem7672920) (@lem7672919)). Qed.
Lemma lem7672922 : term454 = term455.
Proof. exact (MK_COMB (@lem7672921) (@lem7672916)). Qed.
Lemma lem7672923 : term456.
Proof. exact (@lem1980026 term153 term167 term428 term167). Qed.
Lemma lem7672925 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672926 : term266 = term267.
Proof. exact (@lem7672925 (NUMERAL 0) term9). Qed.
Lemma lem7672927 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672928 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672929 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672928 h1) (fun h1 : term267 = True => @lem7672927)). Qed.
Lemma lem7672930 : term267 = True.
Proof. exact (EQ_MP (@lem7672929) (@lem7672927)). Qed.
Lemma lem7672931 : term266 = True.
Proof. exact (TRANS (@lem7672926) (@lem7672930)). Qed.
Lemma lem7672932 : True = term266.
Proof. exact (SYM (@lem7672931)). Qed.
Lemma lem7672933 : term266.
Proof. exact (EQ_MP (@lem7672932) (@lem0)). Qed.
Lemma lem7672934 : term457.
Proof. exact (@lem7672923 (@lem7672933)). Qed.
Lemma lem7672936 (m : nat) (n : nat) : (term265 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7672937 : term266 = term267.
Proof. exact (@lem7672936 (NUMERAL 0) term9). Qed.
Lemma lem7672938 : term268 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7672939 (h1 : term268 = (BIT1 0)) : term267 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7672940 : (term268 = (BIT1 0)) = (term267 = True).
Proof. exact (prop_ext (fun h1 : term268 = (BIT1 0) => @lem7672939 h1) (fun h1 : term267 = True => @lem7672938)). Qed.
Lemma lem7672941 : term267 = True.
Proof. exact (EQ_MP (@lem7672940) (@lem7672938)). Qed.
Lemma lem7672942 : term266 = True.
Proof. exact (TRANS (@lem7672937) (@lem7672941)). Qed.
Lemma lem7672943 : True = term266.
Proof. exact (SYM (@lem7672942)). Qed.
Lemma lem7672944 : term266.
Proof. exact (EQ_MP (@lem7672943) (@lem0)). Qed.
Lemma lem7672945 : term455 = term458.
Proof. exact (@lem7672934 (@lem7672944)). Qed.
Lemma lem7672947 (m : nat) (n : nat) : (term236 m n) = (term237 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7672948 : term443 = term444.
Proof. exact (@lem7672947 term437 term9). Qed.
Lemma lem7672949 : term445 = term435.
Proof. exact (@lem996237 term435). Qed.
Lemma lem7672950 : (term445 = term435) = (term446 = term437).
Proof. exact (@lem1007663 term435 (BIT1 0) term435). Qed.
Lemma lem7672951 : term446 = term437.
Proof. exact (EQ_MP (@lem7672950) (@lem7672949)). Qed.
Lemma lem7672952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7672953 : term447 = term439.
Proof. exact (MK_COMB (@lem7672952) (@lem7672951)). Qed.
Lemma lem7672954 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7672955 : term444 = term428.
Proof. exact (MK_COMB (@lem7672954) (@lem7672953)). Qed.
Lemma lem7672956 : term443 = term428.
Proof. exact (TRANS (@lem7672948) (@lem7672955)). Qed.
Lemma lem7672958 (x : nat) : (term279 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7672959 : term278 = term153.
Proof. exact (@lem7672958 term9). Qed.
Lemma lem7672960 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7672961 : term407 = term155.
Proof. exact (MK_COMB (@lem7672960) (@lem7672959)). Qed.
Lemma lem7672962 : term458 = term454.
Proof. exact (MK_COMB (@lem7672961) (@lem7672956)). Qed.
Lemma lem7672964 (m : nat) (n : nat) : (term408 m n) = (term409 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7672965 : term454 = term459.
Proof. exact (@lem7672964 (NUMERAL 0) term437). Qed.
Lemma lem7672966 : term460 = term435.
Proof. exact (@lem912803). Qed.
Lemma lem7672967 (h1 : term460 = term435) : (term437 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term435 h1). Qed.
Lemma lem7672968 : (term460 = term435) = ((term437 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term460 = term435 => @lem7672967 h1) (fun h1 : (term437 = (NUMERAL 0)) = False => @lem7672966)). Qed.
Lemma lem7672969 : (term437 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7672968) (@lem7672966)). Qed.
Lemma lem7672970 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7672971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7672972 : term411 = (and True).
Proof. exact (MK_COMB (@lem7672971) (@lem7672970)). Qed.
Lemma lem7672973 : term459 = (True /\ False).
Proof. exact (MK_COMB (@lem7672972) (@lem7672969)). Qed.
Lemma lem7672975 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7672976 : term459 = False.
Proof. exact (TRANS (@lem7672973) (@lem7672975)). Qed.
Lemma lem7672977 : term454 = False.
Proof. exact (TRANS (@lem7672965) (@lem7672976)). Qed.
Lemma lem7672978 : term458 = False.
Proof. exact (TRANS (@lem7672962) (@lem7672977)). Qed.
Lemma lem7672979 : term455 = False.
Proof. exact (TRANS (@lem7672945) (@lem7672978)). Qed.
Lemma lem7672980 : term454 = False.
Proof. exact (TRANS (@lem7672922) (@lem7672979)). Qed.
Lemma lem7672981 : term453 = False.
Proof. exact (TRANS (@lem7672913) (@lem7672980)). Qed.
Lemma lem7672982 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term412 _98798 _98799 _98797) : False.
Proof. exact (EQ_MP (@lem7672981) (@lem7672910 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672983 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term303 _98798 _98799 _98797) : False.
Proof. exact (or_elim (@lem7671613 _98798 _98799 _98797 h1) (fun h0 : term306 _98798 _98799 _98797 => @lem7672391 _98798 _98799 _98797 h0) (fun h0 : term412 _98798 _98799 _98797 => @lem7672982 _98798 _98799 _98797 h0)). Qed.
Lemma lem7672985 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term303 _98798 _98799 _98797) : term303 _98798 _98799 _98797.
Proof. exact (h1). Qed.
Lemma lem7672986 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term303 _98798 _98799 _98797) : (term303 _98798 _98799 _98797) = False.
Proof. exact (prop_ext (fun h2 : term303 _98798 _98799 _98797 => @lem7672983 _98798 _98799 _98797 h1) (fun h2 : False => @lem7672985 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672987 (_98798 : int) (_98799 : int) (_98797 : int) (h1 : term303 _98798 _98799 _98797) : False.
Proof. exact (EQ_MP (@lem7672986 _98798 _98799 _98797 h1) (@lem7672985 _98798 _98799 _98797 h1)). Qed.
Lemma lem7672988 (_98799 : int) (_98798 : int) (_98797 : int) (h1 : term189 _98799 _98798 _98797) : term189 _98799 _98798 _98797.
Proof. exact (h1). Qed.
Lemma lem7672989 (_98799 : int) (_98798 : int) (_98797 : int) (h1 : term189 _98799 _98798 _98797) : term303 _98798 _98799 _98797.
Proof. exact (EQ_MP (@lem7671603 _98798 _98799 _98797) (@lem7672988 _98799 _98798 _98797 h1)). Qed.
Lemma lem7672990 (_98799 : int) (_98798 : int) (_98797 : int) (h1 : term189 _98799 _98798 _98797) : (term303 _98798 _98799 _98797) = False.
Proof. exact (prop_ext (fun h2 : term303 _98798 _98799 _98797 => @lem7672987 _98798 _98799 _98797 h2) (fun h2 : False => @lem7672989 _98799 _98798 _98797 h1)). Qed.
Lemma lem7672991 (_98799 : int) (_98798 : int) (_98797 : int) (h1 : term189 _98799 _98798 _98797) : False.
Proof. exact (EQ_MP (@lem7672990 _98799 _98798 _98797 h1) (@lem7672989 _98799 _98798 _98797 h1)). Qed.
Lemma lem7672992 (_98799 : int) (_98798 : int) (_98797 : int) : term461 _98799 _98798 _98797.
Proof. exact (fun h0 : term189 _98799 _98798 _98797 => @lem7672991 _98799 _98798 _98797 h0). Qed.
Lemma lem7672993 (_98799 : int) (_98798 : int) (_98797 : int) : term462 _98799 _98798 _98797.
Proof. exact (@lem1386578 (term463 _98799 _98798 _98797)). Qed.
Lemma lem7672996 (_98799 : int) (_98798 : int) (_98797 : int) : term463 _98799 _98798 _98797.
Proof. exact (@lem7672993 _98799 _98798 _98797 (@lem7672992 _98799 _98798 _98797)). Qed.
Lemma lem7672997 (_98799 : int) (_98798 : int) (_98797 : int) : (term187 _98799 _98798 _98797) = (term147 _98799 _98798 _98797).
Proof. exact (SYM (@lem7670894 _98799 _98798 _98797)). Qed.
Lemma lem7672998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7672999 (_98799 : int) (_98798 : int) (_98797 : int) : (term463 _98799 _98798 _98797) = (term104 _98799 _98798 _98797).
Proof. exact (MK_COMB (@lem7672998) (@lem7672997 _98799 _98798 _98797)). Qed.
Lemma lem7673000 (_98799 : int) (_98798 : int) (_98797 : int) : term104 _98799 _98798 _98797.
Proof. exact (EQ_MP (@lem7672999 _98799 _98798 _98797) (@lem7672996 _98799 _98798 _98797)). Qed.
Lemma lem7673001 (_98799 : int) (_98798 : int) (_98797 : int) : term105 _98799 _98798 _98797.
Proof. exact (EQ_MP (@lem7670639 _98799 _98798 _98797) (@lem7673000 _98799 _98798 _98797)). Qed.
Lemma lem7673002 {A B : Type'} (d : nat) : term464 A B d.
Proof. exact (@lem7673001 (term67 B) (term67 A) (int_of_num d)). Qed.
Lemma lem7673003 {A B : Type'} (d : nat) : term465 A B d.
Proof. exact (@lem7673002 A B d (@lem7670632 d)). Qed.
Lemma lem7673004 {A B : Type'} (d : nat) : term466 A B d.
Proof. exact (@lem7673003 A B d (@lem7670635 A)). Qed.
Lemma lem7673005 {A B : Type'} (d : nat) : term97 A B d.
Proof. exact (@lem7673004 A B d (@lem7670638 B)). Qed.
Lemma lem7673006 {A B : Type'} : term99 A B.
Proof. exact (fun d : nat => @lem7673005 A B d). Qed.
Lemma lem7673007 {A B : Type'} : (term99 A B) = (term8 A B).
Proof. exact (SYM (@lem7670629 A B)). Qed.
Lemma lem7673008 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem7673007 A B) (@lem7673006 A B)). Qed.
Lemma lem7673009 {A B : Type'} : (term8 A B) = ((term8 A B) = True).
Proof. exact (@lem7 (term8 A B)). Qed.
Lemma lem7673010 {A B : Type'} : (term8 A B) = True.
Proof. exact (EQ_MP (@lem7673009 A B) (@lem7673008 A B)). Qed.
Lemma lem7673011 {A B : Type'} : True = (term8 A B).
Proof. exact (SYM (@lem7673010 A B)). Qed.
Lemma lem7673012 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem7673011 A B) (@lem0)). Qed.
Lemma lem7673013 {A B : Type'} : term7 A B.
Proof. exact (EQ_MP (@lem7670367 A B) (@lem7673012 A B)). Qed.
Lemma lem7673014 {A B : Type'} : term467 A B.
Proof. exact (ex_intro (term468 A B) term9 (@lem7673013 A B)). Qed.
Lemma lem7673016 {A : Type'} : (@ex A) = (term469 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem7673017 : (@ex nat) = term470.
Proof. exact (@lem7673016 nat). Qed.
Lemma lem7673018 {A B : Type'} : (term468 A B) = (term468 A B).
Proof. exact (eq_refl (term468 A B)). Qed.
Lemma lem7673019 {A B : Type'} : (term467 A B) = (term471 A B).
Proof. exact (MK_COMB (@lem7673017) (@lem7673018 A B)). Qed.
Lemma lem7673020 {A B : Type'} : (term471 A B) = (term472 A B).
Proof. exact (eq_refl (term471 A B)). Qed.
Lemma lem7673021 {A B : Type'} : (term467 A B) = (term472 A B).
Proof. exact (TRANS (@lem7673019 A B) (@lem7673020 A B)). Qed.
Lemma lem7673022 {A B : Type'} : term472 A B.
Proof. exact (EQ_MP (@lem7673021 A B) (@lem7673014 A B)). Qed.
Lemma lem7673023 {A B : Type'} (a : finite_diff A B) : (term473 A B a) = a.
Proof. exact (@axiom_33 A B a). Qed.
Lemma lem7673024 {A B : Type'} (r : nat) : (term474 A B r) = ((term475 A B r) = r).
Proof. exact (@axiom_34 A B r). Qed.
Lemma lem7673027 {A B : Type'} (r : nat) : (term474 A B r) = (term476 A B r).
Proof. exact (eq_refl (term474 A B r)). Qed.
Lemma lem7673028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673029 {A B : Type'} (r : nat) : (term477 A B r) = (term478 A B r).
Proof. exact (MK_COMB (@lem7673028) (@lem7673027 A B r)). Qed.
Lemma lem7673030 {A B : Type'} (r : nat) : ((term475 A B r) = r) = ((term475 A B r) = r).
Proof. exact (eq_refl ((term475 A B r) = r)). Qed.
Lemma lem7673031 {A B : Type'} (r : nat) : ((term474 A B r) = ((term475 A B r) = r)) = ((term476 A B r) = ((term475 A B r) = r)).
Proof. exact (MK_COMB (@lem7673029 A B r) (@lem7673030 A B r)). Qed.
Lemma lem7673032 {A B : Type'} (r : nat) : (term476 A B r) = ((term475 A B r) = r).
Proof. exact (EQ_MP (@lem7673031 A B r) (@lem7673024 A B r)). Qed.
Lemma lem7673033 {A B : Type'} : term479 A B.
Proof. exact (fun r : nat => @lem7673032 A B r). Qed.
Lemma lem7673034 {A B : Type'} : term480 A B.
Proof. exact (fun a : finite_diff A B => @lem7673023 A B a). Qed.
Lemma lem7673035 {A B : Type'} : term481 A B.
Proof. exact (conj (@lem7673034 A B) (@lem7673033 A B)). Qed.
