Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_LE_ADD_LCANCEL_term_abbrevs.
Require Import HREAL_EQ_ADD_LCANCEL_spec.
Require Import HREAL_LE_EXISTS_DEF_spec.
Require Import thm0_spec.
Require Import thm1320203_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1321463 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1321464 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1321463 x y z h1)). Qed.
Lemma lem1321465 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1321466 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1321465 x y z h1)). Qed.
Lemma lem1321467 (x : hreal) (y : hreal) (z : hreal) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1321464 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1321466 x y z h1)). Qed.
Lemma lem1321468 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1321467 x y z)). Qed.
Lemma lem1321469 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321470 (x : hreal) (y : hreal) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1321469) (@lem1321468 x y)). Qed.
Lemma lem1321471 (x : hreal) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : hreal => @lem1321470 x y)). Qed.
Lemma lem1321472 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321473 (x : hreal) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1321472) (@lem1321471 x)). Qed.
Lemma lem1321474 : term10 = term11.
Proof. exact (fun_ext (fun x : hreal => @lem1321473 x)). Qed.
Lemma lem1321475 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321476 : term12 = term13.
Proof. exact (MK_COMB (@lem1321475) (@lem1321474)). Qed.
Lemma lem1321477 : term13.
Proof. exact (EQ_MP (@lem1321476) (@lem1320203)). Qed.
Lemma lem1321478 (m : hreal) : term14 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1321479 (m : hreal) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1321480 (m : hreal) : term15 m.
Proof. exact (EQ_MP (@lem1321479 m) (@lem1321478 m)). Qed.
Lemma lem1321481 (m : hreal) (n : hreal) : term16 m n.
Proof. exact (@lem1321480 m n). Qed.
Lemma lem1321482 (m : hreal) (n : hreal) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1321483 (m : hreal) (n : hreal) : term17 m n.
Proof. exact (EQ_MP (@lem1321482 m n) (@lem1321481 m n)). Qed.
Lemma lem1321484 (m : hreal) (n : hreal) (p : hreal) : term18 m n p.
Proof. exact (@lem1321483 m n p). Qed.
Lemma lem1321485 (m : hreal) (n : hreal) (p : hreal) : (term18 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem1321487 (x : hreal) : term19 x.
Proof. exact (@lem1321477 x). Qed.
Lemma lem1321488 (x : hreal) : (term19 x) = (term9 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1321489 (x : hreal) : term9 x.
Proof. exact (EQ_MP (@lem1321488 x) (@lem1321487 x)). Qed.
Lemma lem1321490 (x : hreal) (y : hreal) : term20 x y.
Proof. exact (@lem1321489 x y). Qed.
Lemma lem1321491 (x : hreal) (y : hreal) : (term20 x y) = (term5 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1321492 (x : hreal) (y : hreal) : term5 x y.
Proof. exact (EQ_MP (@lem1321491 x y) (@lem1321490 x y)). Qed.
Lemma lem1321493 (x : hreal) (y : hreal) (z : hreal) : term21 x y z.
Proof. exact (@lem1321492 x y z). Qed.
Lemma lem1321494 (x : hreal) (y : hreal) (z : hreal) : (term21 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term21 x y z)). Qed.
Lemma lem1321496 (m : hreal) : term22 m.
Proof. exact (@lem1321284 m). Qed.
Lemma lem1321497 (m : hreal) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem1321498 (m : hreal) : term23 m.
Proof. exact (EQ_MP (@lem1321497 m) (@lem1321496 m)). Qed.
Lemma lem1321499 (m : hreal) (n : hreal) : term24 m n.
Proof. exact (@lem1321498 m n). Qed.
Lemma lem1321500 (n : hreal) (m : hreal) : (term24 m n) = ((hreal_le m n) = (term25 n m)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1321517 (n : hreal) (m : hreal) : (hreal_le m n) = (term25 n m).
Proof. exact (EQ_MP (@lem1321500 n m) (@lem1321499 m n)). Qed.
Lemma lem1321518 (p : hreal) (m : hreal) (n : hreal) : (term26 n m p) = (term27 p m n).
Proof. exact (@lem1321517 (hreal_add m p) (hreal_add m n)). Qed.
Lemma lem1321528 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1321494 x y z) (@lem1321493 x y z)). Qed.
Lemma lem1321529 (m : hreal) (n : hreal) (d : hreal) : (term1 m n d) = (term0 m n d).
Proof. exact (@lem1321528 m n d). Qed.
Lemma lem1321530 (m : hreal) (p : hreal) : (term28 m p) = (term28 m p).
Proof. exact (eq_refl (term28 m p)). Qed.
Lemma lem1321531 (p : hreal) (m : hreal) (n : hreal) (d : hreal) : ((hreal_add m p) = (term1 m n d)) = ((hreal_add m p) = (term0 m n d)).
Proof. exact (MK_COMB (@lem1321530 m p) (@lem1321529 m n d)). Qed.
Lemma lem1321533 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1321485 m n p) (@lem1321484 m n p)). Qed.
Lemma lem1321534 (m : hreal) (p : hreal) (n : hreal) (d : hreal) : ((hreal_add m p) = (term0 m n d)) = (p = (hreal_add n d)).
Proof. exact (@lem1321533 m p (hreal_add n d)). Qed.
Lemma lem1321537 (m : hreal) (p : hreal) (n : hreal) (d : hreal) : ((hreal_add m p) = (term1 m n d)) = (p = (hreal_add n d)).
Proof. exact (TRANS (@lem1321531 p m n d) (@lem1321534 m p n d)). Qed.
Lemma lem1321538 (m : hreal) (p : hreal) (n : hreal) : (term29 p m n) = (term30 p n).
Proof. exact (fun_ext (fun d : hreal => @lem1321537 m p n d)). Qed.
Lemma lem1321539 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1321540 (m : hreal) (p : hreal) (n : hreal) : (term27 p m n) = (term25 p n).
Proof. exact (MK_COMB (@lem1321539) (@lem1321538 m p n)). Qed.
Lemma lem1321545 (m : hreal) (p : hreal) (n : hreal) : (term26 n m p) = (term25 p n).
Proof. exact (TRANS (@lem1321518 p m n) (@lem1321540 m p n)). Qed.
Lemma lem1321546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321547 (m : hreal) (p : hreal) (n : hreal) : (term31 n m p) = (term32 p n).
Proof. exact (MK_COMB (@lem1321546) (@lem1321545 m p n)). Qed.
Lemma lem1321549 (n : hreal) (m : hreal) : (hreal_le m n) = (term25 n m).
Proof. exact (EQ_MP (@lem1321500 n m) (@lem1321499 m n)). Qed.
Lemma lem1321550 (p : hreal) (n : hreal) : (hreal_le n p) = (term25 p n).
Proof. exact (@lem1321549 p n). Qed.
Lemma lem1321557 (m : hreal) (p : hreal) (n : hreal) : ((term26 n m p) = (hreal_le n p)) = ((term25 p n) = (term25 p n)).
Proof. exact (MK_COMB (@lem1321547 m p n) (@lem1321550 p n)). Qed.
Lemma lem1321559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1321560 (x : Prop) : (x = x) = True.
Proof. exact (@lem1321559 Prop x). Qed.
Lemma lem1321561 (p : hreal) (n : hreal) : ((term25 p n) = (term25 p n)) = True.
Proof. exact (@lem1321560 (term25 p n)). Qed.
Lemma lem1321562 (m : hreal) (n : hreal) (p : hreal) : ((term26 n m p) = (hreal_le n p)) = True.
Proof. exact (TRANS (@lem1321557 m p n) (@lem1321561 p n)). Qed.
Lemma lem1321563 (m : hreal) (n : hreal) : (term33 m n) = term34.
Proof. exact (fun_ext (fun p : hreal => @lem1321562 m n p)). Qed.
Lemma lem1321564 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321565 (m : hreal) (n : hreal) : (term35 m n) = term36.
Proof. exact (MK_COMB (@lem1321564) (@lem1321563 m n)). Qed.
Lemma lem1321567 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1321568 (t : Prop) : (term38 t) = t.
Proof. exact (@lem1321567 hreal t). Qed.
Lemma lem1321569 : term36 = True.
Proof. exact (@lem1321568 True). Qed.
Lemma lem1321570 (m : hreal) (n : hreal) : (term35 m n) = True.
Proof. exact (TRANS (@lem1321565 m n) (@lem1321569)). Qed.
Lemma lem1321571 (m : hreal) : (term39 m) = term34.
Proof. exact (fun_ext (fun n : hreal => @lem1321570 m n)). Qed.
Lemma lem1321572 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321573 (m : hreal) : (term40 m) = term36.
Proof. exact (MK_COMB (@lem1321572) (@lem1321571 m)). Qed.
Lemma lem1321575 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1321576 (t : Prop) : (term38 t) = t.
Proof. exact (@lem1321575 hreal t). Qed.
Lemma lem1321577 : term36 = True.
Proof. exact (@lem1321576 True). Qed.
Lemma lem1321578 (m : hreal) : (term40 m) = True.
Proof. exact (TRANS (@lem1321573 m) (@lem1321577)). Qed.
Lemma lem1321579 : term41 = term34.
Proof. exact (fun_ext (fun m : hreal => @lem1321578 m)). Qed.
Lemma lem1321580 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321581 : term42 = term36.
Proof. exact (MK_COMB (@lem1321580) (@lem1321579)). Qed.
Lemma lem1321583 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1321584 (t : Prop) : (term38 t) = t.
Proof. exact (@lem1321583 hreal t). Qed.
Lemma lem1321585 : term36 = True.
Proof. exact (@lem1321584 True). Qed.
Lemma lem1321586 : term42 = True.
Proof. exact (TRANS (@lem1321581) (@lem1321585)). Qed.
Lemma lem1321587 : True = term42.
Proof. exact (SYM (@lem1321586)). Qed.
Lemma lem1321588 : term42.
Proof. exact (EQ_MP (@lem1321587) (@lem0)). Qed.
