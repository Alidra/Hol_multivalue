Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337622_term_abbrevs.
Require Import TREAL_EQ_REFL_spec.
Require Import TREAL_EQ_TRANS_spec.
Require Import TREAL_NEG_WELLDEF_spec.
Require Import thm1337493_spec.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1337538 : real_neg = term0.
Proof. exact (@real_neg_def). Qed.
Lemma lem1337539 (x1 : real) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem1337540 (x1 : real) : (real_neg x1) = (term1 x1).
Proof. exact (MK_COMB (@lem1337538) (@lem1337539 x1)). Qed.
Lemma lem1337541 (x1 : real) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1337542 (x1 : real) : (term3 x1) = (term3 x1).
Proof. exact (eq_refl (term3 x1)). Qed.
Lemma lem1337543 (x1 : real) : ((real_neg x1) = (term1 x1)) = ((real_neg x1) = (term2 x1)).
Proof. exact (MK_COMB (@lem1337542 x1) (@lem1337541 x1)). Qed.
Lemma lem1337544 (x1 : real) : (real_neg x1) = (term2 x1).
Proof. exact (EQ_MP (@lem1337543 x1) (@lem1337540 x1)). Qed.
Lemma lem1337545 (x : prod hreal hreal) : (term4 x) = ((term5 x) = (treal_eq x)).
Proof. exact (@lem1337493 (treal_eq x)). Qed.
Lemma lem1337546 (x : prod hreal hreal) : (treal_eq x) = (treal_eq x).
Proof. exact (eq_refl (treal_eq x)). Qed.
Lemma lem1337547 (x : prod hreal hreal) : term4 x.
Proof. exact (ex_intro (term6 x) x (@lem1337546 x)). Qed.
Lemma lem1337548 (x : prod hreal hreal) : (term5 x) = (treal_eq x).
Proof. exact (EQ_MP (@lem1337545 x) (@lem1337547 x)). Qed.
Lemma lem1337549 (x1 : prod hreal hreal) : (term7 x1) = (term8 x1).
Proof. exact (@lem1337544 (term9 x1)). Qed.
Lemma lem1337550 (x1 : prod hreal hreal) : (term5 x1) = (treal_eq x1).
Proof. exact (@lem1337548 x1). Qed.
Lemma lem1337551 (x1 : prod hreal hreal) : (term10 x1) = (term10 x1).
Proof. exact (eq_refl (term10 x1)). Qed.
Lemma lem1337552 (x1 : prod hreal hreal) : (term11 x1) = (term12 x1).
Proof. exact (MK_COMB (@lem1337551 x1) (@lem1337550 x1)). Qed.
Lemma lem1337553 (x1 : prod hreal hreal) : (term12 x1) = ((term7 x1) = (term13 x1)).
Proof. exact (eq_refl (term12 x1)). Qed.
Lemma lem1337554 (x1 : prod hreal hreal) : (term14 x1) = (term14 x1).
Proof. exact (eq_refl (term14 x1)). Qed.
Lemma lem1337555 (x1 : prod hreal hreal) : ((term11 x1) = (term12 x1)) = ((term11 x1) = ((term7 x1) = (term13 x1))).
Proof. exact (MK_COMB (@lem1337554 x1) (@lem1337553 x1)). Qed.
Lemma lem1337556 (x1 : prod hreal hreal) : (term11 x1) = ((term7 x1) = (term8 x1)).
Proof. exact (eq_refl (term11 x1)). Qed.
Lemma lem1337557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337558 (x1 : prod hreal hreal) : (term14 x1) = (term15 x1).
Proof. exact (MK_COMB (@lem1337557) (@lem1337556 x1)). Qed.
Lemma lem1337559 (x1 : prod hreal hreal) : ((term7 x1) = (term13 x1)) = ((term7 x1) = (term13 x1)).
Proof. exact (eq_refl ((term7 x1) = (term13 x1))). Qed.
Lemma lem1337560 (x1 : prod hreal hreal) : ((term11 x1) = ((term7 x1) = (term13 x1))) = (((term7 x1) = (term8 x1)) = ((term7 x1) = (term13 x1))).
Proof. exact (MK_COMB (@lem1337558 x1) (@lem1337559 x1)). Qed.
Lemma lem1337561 (x1 : prod hreal hreal) : ((term11 x1) = (term12 x1)) = (((term7 x1) = (term8 x1)) = ((term7 x1) = (term13 x1))).
Proof. exact (TRANS (@lem1337555 x1) (@lem1337560 x1)). Qed.
Lemma lem1337562 (x1 : prod hreal hreal) : ((term7 x1) = (term8 x1)) = ((term7 x1) = (term13 x1)).
Proof. exact (EQ_MP (@lem1337561 x1) (@lem1337552 x1)). Qed.
Lemma lem1337563 (x1 : prod hreal hreal) : (term7 x1) = (term13 x1).
Proof. exact (EQ_MP (@lem1337562 x1) (@lem1337549 x1)). Qed.
Lemma lem1337564 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : term16 u x1 x1'.
Proof. exact (h1). Qed.
Lemma lem1337565 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : treal_eq x1 x1'.
Proof. exact (proj2 (@lem1337564 u x1 x1' h1)). Qed.
Lemma lem1337566 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : term17 x1' u.
Proof. exact (proj1 (@lem1337564 u x1 x1' h1)). Qed.
Lemma lem1337567 (x1 : prod hreal hreal) : term18 x1.
Proof. exact (@lem1332887 x1). Qed.
Lemma lem1337568 (x1 : prod hreal hreal) : (term18 x1) = (term19 x1).
Proof. exact (eq_refl (term18 x1)). Qed.
Lemma lem1337569 (x1 : prod hreal hreal) : term19 x1.
Proof. exact (EQ_MP (@lem1337568 x1) (@lem1337567 x1)). Qed.
Lemma lem1337570 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term20 x1 x2.
Proof. exact (@lem1337569 x1 x2). Qed.
Lemma lem1337571 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term20 x1 x2) = (term21 x1 x2).
Proof. exact (eq_refl (term20 x1 x2)). Qed.
Lemma lem1337574 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term21 x1 x2.
Proof. exact (EQ_MP (@lem1337571 x1 x2) (@lem1337570 x1 x2)). Qed.
Lemma lem1337575 (x1 : prod hreal hreal) (x1' : prod hreal hreal) : term21 x1 x1'.
Proof. exact (@lem1337574 x1 x1'). Qed.
Lemma lem1337576 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : term22 x1 x1'.
Proof. exact (@lem1337575 x1 x1' (@lem1337565 u x1 x1' h1)). Qed.
Lemma lem1337577 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : term23 x1 x1' u.
Proof. exact (conj (@lem1337576 u x1 x1' h1) (@lem1337566 u x1 x1' h1)). Qed.
Lemma lem1337578 (x : prod hreal hreal) : term24 x.
Proof. exact (@lem1326778 x). Qed.
Lemma lem1337579 (x : prod hreal hreal) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1337580 (x : prod hreal hreal) : term25 x.
Proof. exact (EQ_MP (@lem1337579 x) (@lem1337578 x)). Qed.
Lemma lem1337581 (x : prod hreal hreal) (y : prod hreal hreal) : term26 x y.
Proof. exact (@lem1337580 x y). Qed.
Lemma lem1337582 (y : prod hreal hreal) (x : prod hreal hreal) : (term26 x y) = (term27 y x).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1337583 (y : prod hreal hreal) (x : prod hreal hreal) : term27 y x.
Proof. exact (EQ_MP (@lem1337582 y x) (@lem1337581 x y)). Qed.
Lemma lem1337584 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term28 y x z.
Proof. exact (@lem1337583 y x z). Qed.
Lemma lem1337585 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term28 y x z) = (term29 y x z).
Proof. exact (eq_refl (term28 y x z)). Qed.
Lemma lem1337588 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term29 y x z.
Proof. exact (EQ_MP (@lem1337585 y x z) (@lem1337584 y x z)). Qed.
Lemma lem1337589 (x1' : prod hreal hreal) (x1 : prod hreal hreal) (u : prod hreal hreal) : term30 x1' x1 u.
Proof. exact (@lem1337588 (treal_neg x1') (treal_neg x1) u). Qed.
Lemma lem1337590 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : term17 x1 u.
Proof. exact (@lem1337589 x1' x1 u (@lem1337577 u x1 x1' h1)). Qed.
Lemma lem1337591 (u : prod hreal hreal) (x1 : prod hreal hreal) (h1 : term31 u x1) : term31 u x1.
Proof. exact (h1). Qed.
Lemma lem1337592 (u : prod hreal hreal) (x1 : prod hreal hreal) (h1 : term31 u x1) : term17 x1 u.
Proof. exact (ex_elim (@lem1337591 u x1 h1) (fun x1' : prod hreal hreal => fun h0 : term32 u x1 x1' => @lem1337590 u x1 x1' h0)). Qed.
Lemma lem1337593 (x1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term17 x1 u) : term17 x1 u.
Proof. exact (h1). Qed.
Lemma lem1337594 (x1 : prod hreal hreal) : term33 x1.
Proof. exact (@lem1326193 x1). Qed.
Lemma lem1337595 (x1 : prod hreal hreal) : (term33 x1) = (treal_eq x1 x1).
Proof. exact (eq_refl (term33 x1)). Qed.
Lemma lem1337596 (x1 : prod hreal hreal) : treal_eq x1 x1.
Proof. exact (EQ_MP (@lem1337595 x1) (@lem1337594 x1)). Qed.
Lemma lem1337597 (x1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term17 x1 u) : term34 u x1.
Proof. exact (conj (@lem1337593 x1 u h1) (@lem1337596 x1)). Qed.
Lemma lem1337598 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : term16 u x1 x1'.
Proof. exact (h1). Qed.
Lemma lem1337599 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (h1 : term16 u x1 x1') : term31 u x1.
Proof. exact (ex_intro (term32 u x1) x1' (@lem1337598 u x1 x1' h1)). Qed.
Lemma lem1337602 (x1' : prod hreal hreal) (u : prod hreal hreal) (x1 : prod hreal hreal) : term35 x1' u x1.
Proof. exact (fun h0 : term16 u x1 x1' => @lem1337599 u x1 x1' h0). Qed.
Lemma lem1337603 (u : prod hreal hreal) (x1 : prod hreal hreal) : term36 u x1.
Proof. exact (@lem1337602 x1 u x1). Qed.
Lemma lem1337604 (x1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term17 x1 u) : term31 u x1.
Proof. exact (@lem1337603 u x1 (@lem1337597 x1 u h1)). Qed.
Lemma lem1337605 (u : prod hreal hreal) (x1 : prod hreal hreal) : term37 u x1.
Proof. exact (fun h0 : term17 x1 u => @lem1337604 x1 u h0). Qed.
Lemma lem1337606 (x1 : prod hreal hreal) (u : prod hreal hreal) : term38 x1 u.
Proof. exact (fun h0 : term31 u x1 => @lem1337592 u x1 h0). Qed.
Lemma lem1337607 (u : prod hreal hreal) (x1 : prod hreal hreal) : term39 u x1.
Proof. exact (conj (@lem1337606 x1 u) (@lem1337605 u x1)). Qed.
Lemma lem1337608 (x1 : prod hreal hreal) (u : prod hreal hreal) : (term39 u x1) = ((term31 u x1) = (term17 x1 u)).
Proof. exact (@lem32 (term31 u x1) (term17 x1 u)). Qed.
Lemma lem1337609 (x1 : prod hreal hreal) (u : prod hreal hreal) : (term31 u x1) = (term17 x1 u).
Proof. exact (EQ_MP (@lem1337608 x1 u) (@lem1337607 u x1)). Qed.
Lemma lem1337610 (x1 : prod hreal hreal) : (term40 x1) = (term41 x1).
Proof. exact (fun_ext (fun u : prod hreal hreal => @lem1337609 x1 u)). Qed.
Lemma lem1337611 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337612 (x1 : prod hreal hreal) : (term13 x1) = (term42 x1).
Proof. exact (MK_COMB (@lem1337611) (@lem1337610 x1)). Qed.
Lemma lem1337613 (x1 : prod hreal hreal) : (term7 x1) = (term42 x1).
Proof. exact (TRANS (@lem1337563 x1) (@lem1337612 x1)). Qed.
Lemma lem1337614 (t : type1233) : (term43 t) = t.
Proof. exact (@lem9127 (prod hreal hreal) Prop t). Qed.
Lemma lem1337617 (x1 : prod hreal hreal) : (term41 x1) = (term44 x1).
Proof. exact (@lem1337614 (term44 x1)). Qed.
Lemma lem1337618 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337619 (x1 : prod hreal hreal) : (term42 x1) = (term45 x1).
Proof. exact (MK_COMB (@lem1337618) (@lem1337617 x1)). Qed.
Lemma lem1337620 (x1 : prod hreal hreal) : (term46 x1) = (term46 x1).
Proof. exact (eq_refl (term46 x1)). Qed.
Lemma lem1337621 (x1 : prod hreal hreal) : ((term7 x1) = (term42 x1)) = ((term7 x1) = (term45 x1)).
Proof. exact (MK_COMB (@lem1337620 x1) (@lem1337619 x1)). Qed.
Lemma lem1337622 (x1 : prod hreal hreal) : (term7 x1) = (term45 x1).
Proof. exact (EQ_MP (@lem1337621 x1) (@lem1337613 x1)). Qed.
