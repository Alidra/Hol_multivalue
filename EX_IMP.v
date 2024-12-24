Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EX_IMP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1101587_spec.
Require Import thm1101588_spec.
Require Import thm1101596_spec.
Require Import thm1101597_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm21386_spec.
Lemma lem1133442 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1133443 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1133444 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1133443 t1) (@lem1133442 t1)). Qed.
Lemma lem1133445 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1133444 t1 t2). Qed.
Lemma lem1133446 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1133447 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1133446 t1 t2) (@lem1133445 t1 t2)). Qed.
Lemma lem1133448 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1133447 t1 t2 t3). Qed.
Lemma lem1133449 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1133450 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1133449 t1 t2 t3) (@lem1133448 t1 t2 t3)). Qed.
Lemma lem1133451 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1133450 t1 t2 t3)). Qed.
Lemma lem1133457 {A : Type'} (P : type1143 A) : term7 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1133458 {_26750 : Type'} (P : type1143 _26750) : term7 _26750 P.
Proof. exact (@lem1133457 _26750 P). Qed.
Lemma lem1133459 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : term8 _26750 P Q.
Proof. exact (@lem1133458 _26750 (term9 _26750 P Q)). Qed.
Lemma lem1133460 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term10 _26750 P Q) = (term11 _26750 P Q).
Proof. exact (eq_refl (term10 _26750 P Q)). Qed.
Lemma lem1133461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133462 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term12 _26750 P Q) = (term13 _26750 P Q).
Proof. exact (MK_COMB (@lem1133461) (@lem1133460 _26750 P Q)). Qed.
Lemma lem1133463 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term14 _26750 P Q t) = (term15 _26750 P Q t).
Proof. exact (eq_refl (term14 _26750 P Q t)). Qed.
Lemma lem1133464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133465 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term16 _26750 P Q t) = (term17 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133464) (@lem1133463 _26750 P Q t)). Qed.
Lemma lem1133466 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (h : _26750) (t : list _26750) : (term18 _26750 P Q h t) = (term19 _26750 P Q h t).
Proof. exact (eq_refl (term18 _26750 P Q h t)). Qed.
Lemma lem1133467 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (h : _26750) (t : list _26750) : (term20 _26750 P Q h t) = (term21 _26750 P Q h t).
Proof. exact (MK_COMB (@lem1133465 _26750 P Q t) (@lem1133466 _26750 P Q h t)). Qed.
Lemma lem1133468 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (h : _26750) : (term22 _26750 P Q h) = (term23 _26750 P Q h).
Proof. exact (fun_ext (fun t : list _26750 => @lem1133467 _26750 P Q h t)). Qed.
Lemma lem1133469 {_26750 : Type'} : (@all (list _26750)) = (@all (list _26750)).
Proof. exact (eq_refl (@all (list _26750))). Qed.
Lemma lem1133470 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (h : _26750) : (term24 _26750 P Q h) = (term25 _26750 P Q h).
Proof. exact (MK_COMB (@lem1133469 _26750) (@lem1133468 _26750 P Q h)). Qed.
Lemma lem1133471 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term26 _26750 P Q) = (term27 _26750 P Q).
Proof. exact (fun_ext (fun h : _26750 => @lem1133470 _26750 P Q h)). Qed.
Lemma lem1133472 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1133473 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term28 _26750 P Q) = (term29 _26750 P Q).
Proof. exact (MK_COMB (@lem1133472 _26750) (@lem1133471 _26750 P Q)). Qed.
Lemma lem1133474 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term30 _26750 P Q) = (term31 _26750 P Q).
Proof. exact (MK_COMB (@lem1133462 _26750 P Q) (@lem1133473 _26750 P Q)). Qed.
Lemma lem1133475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133476 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term32 _26750 P Q) = (term33 _26750 P Q).
Proof. exact (MK_COMB (@lem1133475) (@lem1133474 _26750 P Q)). Qed.
Lemma lem1133477 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (l : list _26750) : (term14 _26750 P Q l) = (term15 _26750 P Q l).
Proof. exact (eq_refl (term14 _26750 P Q l)). Qed.
Lemma lem1133478 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term34 _26750 P Q) = (term9 _26750 P Q).
Proof. exact (fun_ext (fun l : list _26750 => @lem1133477 _26750 P Q l)). Qed.
Lemma lem1133479 {_26750 : Type'} : (@all (list _26750)) = (@all (list _26750)).
Proof. exact (eq_refl (@all (list _26750))). Qed.
Lemma lem1133480 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term35 _26750 P Q) = (term36 _26750 P Q).
Proof. exact (MK_COMB (@lem1133479 _26750) (@lem1133478 _26750 P Q)). Qed.
Lemma lem1133481 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term8 _26750 P Q) = (term37 _26750 P Q).
Proof. exact (MK_COMB (@lem1133476 _26750 P Q) (@lem1133480 _26750 P Q)). Qed.
Lemma lem1133482 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : term37 _26750 P Q.
Proof. exact (EQ_MP (@lem1133481 _26750 P Q) (@lem1133459 _26750 P Q)). Qed.
Lemma lem1133483 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term15 _26750 P Q t.
Proof. exact (h1). Qed.
Lemma lem1133497 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1133498 {_26750 : Type'} (x : _26750) : (@List.In _26750 x (@nil _26750)) = False.
Proof. exact (@lem1133497 _26750 x). Qed.
Lemma lem1133499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133500 {_26750 : Type'} (x : _26750) : (term38 _26750 x) = (and False).
Proof. exact (MK_COMB (@lem1133499) (@lem1133498 _26750 x)). Qed.
Lemma lem1133501 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1133502 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term39 _26750 P x) = (term40 _26750 P x).
Proof. exact (MK_COMB (@lem1133500 _26750 x) (@lem1133501 _26750 P x)). Qed.
Lemma lem1133504 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1133505 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term40 _26750 P x) = False.
Proof. exact (@lem1133504 (P x)). Qed.
Lemma lem1133506 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term39 _26750 P x) = False.
Proof. exact (TRANS (@lem1133502 _26750 P x) (@lem1133505 _26750 P x)). Qed.
Lemma lem1133507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133508 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term41 _26750 P x) = (imp False).
Proof. exact (MK_COMB (@lem1133507) (@lem1133506 _26750 P x)). Qed.
Lemma lem1133509 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (Q x) = (Q x).
Proof. exact (eq_refl (Q x)). Qed.
Lemma lem1133510 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term42 _26750 P Q x) = (term43 _26750 Q x).
Proof. exact (MK_COMB (@lem1133508 _26750 P x) (@lem1133509 _26750 Q x)). Qed.
Lemma lem1133512 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1133513 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (term43 _26750 Q x) = True.
Proof. exact (@lem1133512 (Q x)). Qed.
Lemma lem1133514 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term42 _26750 P Q x) = True.
Proof. exact (TRANS (@lem1133510 _26750 P Q x) (@lem1133513 _26750 Q x)). Qed.
Lemma lem1133515 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term44 _26750 P Q) = (term45 _26750).
Proof. exact (fun_ext (fun x : _26750 => @lem1133514 _26750 P Q x)). Qed.
Lemma lem1133516 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1133517 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term46 _26750 P Q) = (term47 _26750).
Proof. exact (MK_COMB (@lem1133516 _26750) (@lem1133515 _26750 P Q)). Qed.
Lemma lem1133519 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1133520 {_26750 : Type'} (t : Prop) : (term48 _26750 t) = t.
Proof. exact (@lem1133519 _26750 t). Qed.
Lemma lem1133521 {_26750 : Type'} : (term47 _26750) = True.
Proof. exact (@lem1133520 _26750 True). Qed.
Lemma lem1133522 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term46 _26750 P Q) = True.
Proof. exact (TRANS (@lem1133517 _26750 P Q) (@lem1133521 _26750)). Qed.
Lemma lem1133523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133524 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term49 _26750 P Q) = (and True).
Proof. exact (MK_COMB (@lem1133523) (@lem1133522 _26750 P Q)). Qed.
Lemma lem1133526 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1133527 {_26750 : Type'} (P : _26750 -> Prop) : (@EX _26750 P (@nil _26750)) = False.
Proof. exact (@lem1133526 _26750 P). Qed.
Lemma lem1133528 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) : (term50 _26750 Q P) = (True /\ False).
Proof. exact (MK_COMB (@lem1133524 _26750 P Q) (@lem1133527 _26750 P)). Qed.
Lemma lem1133530 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1133531 : (True /\ False) = False.
Proof. exact (@lem1133530 False). Qed.
Lemma lem1133532 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) : (term50 _26750 Q P) = False.
Proof. exact (TRANS (@lem1133528 _26750 Q P) (@lem1133531)). Qed.
Lemma lem1133533 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133534 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) : (term51 _26750 Q P) = (imp False).
Proof. exact (MK_COMB (@lem1133533) (@lem1133532 _26750 Q P)). Qed.
Lemma lem1133536 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1133537 {_26750 : Type'} (P : _26750 -> Prop) : (@EX _26750 P (@nil _26750)) = False.
Proof. exact (@lem1133536 _26750 P). Qed.
Lemma lem1133538 {_26750 : Type'} (Q : _26750 -> Prop) : (@EX _26750 Q (@nil _26750)) = False.
Proof. exact (@lem1133537 _26750 Q). Qed.
Lemma lem1133539 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term11 _26750 P Q) = (False -> False).
Proof. exact (MK_COMB (@lem1133534 _26750 Q P) (@lem1133538 _26750 Q)). Qed.
Lemma lem1133541 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1133542 : (False -> False) = True.
Proof. exact (@lem1133541 False). Qed.
Lemma lem1133543 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term11 _26750 P Q) = True.
Proof. exact (TRANS (@lem1133539 _26750 P Q) (@lem1133542)). Qed.
Lemma lem1133544 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : True = (term11 _26750 P Q).
Proof. exact (SYM (@lem1133543 _26750 P Q)). Qed.
Lemma lem1133545 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : term11 _26750 P Q.
Proof. exact (EQ_MP (@lem1133544 _26750 P Q) (@lem0)). Qed.
Lemma lem1133559 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term52 _25376 x h t) = (term53 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1133560 {_26750 : Type'} (h : _26750) (x : _26750) (t : list _26750) : (term52 _26750 x h t) = (term53 _26750 h x t).
Proof. exact (@lem1133559 _26750 h x t). Qed.
Lemma lem1133565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133566 {_26750 : Type'} (h : _26750) (x : _26750) (t : list _26750) : (term54 _26750 x h t) = (term55 _26750 h x t).
Proof. exact (MK_COMB (@lem1133565) (@lem1133560 _26750 h x t)). Qed.
Lemma lem1133567 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1133568 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term56 _26750 h t P x) = (term57 _26750 h t P x).
Proof. exact (MK_COMB (@lem1133566 _26750 h x t) (@lem1133567 _26750 P x)). Qed.
Lemma lem1133571 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133572 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term58 _26750 h t P x) = (term59 _26750 h t P x).
Proof. exact (MK_COMB (@lem1133571) (@lem1133568 _26750 h t P x)). Qed.
Lemma lem1133573 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (Q x) = (Q x).
Proof. exact (eq_refl (Q x)). Qed.
Lemma lem1133574 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term60 _26750 h t P Q x) = (term61 _26750 h t P Q x).
Proof. exact (MK_COMB (@lem1133572 _26750 h t P x) (@lem1133573 _26750 Q x)). Qed.
Lemma lem1133577 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term62 _26750 h t P Q) = (term63 _26750 h t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1133574 _26750 h t P Q x)). Qed.
Lemma lem1133578 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1133579 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term64 _26750 h t P Q) = (term65 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1133578 _26750) (@lem1133577 _26750 h t P Q)). Qed.
Lemma lem1133584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133585 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term66 _26750 h t P Q) = (term67 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1133584) (@lem1133579 _26750 h t P Q)). Qed.
Lemma lem1133587 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term68 _25328 P h t) = (term69 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1133588 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term68 _26750 P h t) = (term69 _26750 h P t).
Proof. exact (@lem1133587 _26750 h P t). Qed.
Lemma lem1133591 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term70 _26750 Q P h t) = (term71 _26750 Q h P t).
Proof. exact (MK_COMB (@lem1133585 _26750 h t P Q) (@lem1133588 _26750 h P t)). Qed.
Lemma lem1133594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133595 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term72 _26750 Q P h t) = (term73 _26750 Q h P t).
Proof. exact (MK_COMB (@lem1133594) (@lem1133591 _26750 Q h P t)). Qed.
Lemma lem1133597 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term68 _25328 P h t) = (term69 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1133598 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term68 _26750 P h t) = (term69 _26750 h P t).
Proof. exact (@lem1133597 _26750 h P t). Qed.
Lemma lem1133599 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term68 _26750 Q h t) = (term69 _26750 h Q t).
Proof. exact (@lem1133598 _26750 h Q t). Qed.
Lemma lem1133602 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term19 _26750 P Q h t) = (term74 _26750 P h Q t).
Proof. exact (MK_COMB (@lem1133595 _26750 Q h P t) (@lem1133599 _26750 h Q t)). Qed.
Lemma lem1133605 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (h : _26750) (t : list _26750) : (term74 _26750 P h Q t) = (term19 _26750 P Q h t).
Proof. exact (SYM (@lem1133602 _26750 P h Q t)). Qed.
Lemma lem1133607 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1133608 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term74 _26750 P h Q t) = (term76 _26750 P h Q t).
Proof. exact (@lem1133607 (term74 _26750 P h Q t)). Qed.
Lemma lem1133609 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term76 _26750 P h Q t) = (term74 _26750 P h Q t).
Proof. exact (SYM (@lem1133608 _26750 P h Q t)). Qed.
Lemma lem1133610 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term77 _26750 P h Q t) : term77 _26750 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1133613 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term78 _26750 P h Q t) : term78 _26750 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1133614 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term79 _26750 P h Q t.
Proof. exact (fun h0 : term78 _26750 P h Q t => @lem1133613 _26750 P h Q t h0). Qed.
Lemma lem1133615 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term79 _26750 P h Q t) : term79 _26750 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1133616 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term78 _26750 P h Q t) : term78 _26750 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1133617 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term78 _26750 P h Q t) (h2 : term79 _26750 P h Q t) : term78 _26750 P h Q t.
Proof. exact (@lem1133615 _26750 P h Q t h2 (@lem1133616 _26750 P h Q t h1)). Qed.
Lemma lem1133618 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term78 _26750 P h Q t) : term80 _26750 P h Q t.
Proof. exact (fun h0 : term79 _26750 P h Q t => @lem1133617 _26750 P h Q t h1 h0). Qed.
Lemma lem1133619 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term79 _26750 P h Q t) : term79 _26750 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1133620 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term78 _26750 P h Q t) (h2 : term79 _26750 P h Q t) : term78 _26750 P h Q t.
Proof. exact (@lem1133618 _26750 P h Q t h1 (@lem1133619 _26750 P h Q t h2)). Qed.
Lemma lem1133621 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term79 _26750 P h Q t) : term79 _26750 P h Q t.
Proof. exact (fun h0 : term78 _26750 P h Q t => @lem1133620 _26750 P h Q t h0 h1). Qed.
Lemma lem1133622 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term81 _26750 P h Q t.
Proof. exact (fun h0 : term79 _26750 P h Q t => @lem1133621 _26750 P h Q t h0). Qed.
Lemma lem1133625 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term79 _26750 P h Q t.
Proof. exact (@lem1133622 _26750 P h Q t (@lem1133614 _26750 P h Q t)). Qed.
Lemma lem1133626 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term79 _26750 P h Q t.
Proof. exact (@lem1133625 _26750 P h Q t). Qed.
Lemma lem1133658 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1133659 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term76 _26750 P h Q t) = (term82 _26750 P h Q t).
Proof. exact (@lem1133658 (term77 _26750 P h Q t)). Qed.
Lemma lem1133661 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1133662 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term82 _26750 P h Q t) = (term74 _26750 P h Q t).
Proof. exact (@lem1133661 (term74 _26750 P h Q t)). Qed.
Lemma lem1133665 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term76 _26750 P h Q t) = (term74 _26750 P h Q t).
Proof. exact (TRANS (@lem1133659 _26750 P h Q t) (@lem1133662 _26750 P h Q t)). Qed.
Lemma lem1133682 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term17 _26750 P Q t) = (term17 _26750 P Q t).
Proof. exact (eq_refl (term17 _26750 P Q t)). Qed.
Lemma lem1133683 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term78 _26750 P h Q t) = (term84 _26750 P h Q t).
Proof. exact (MK_COMB (@lem1133682 _26750 P Q t) (@lem1133665 _26750 P h Q t)). Qed.
Lemma lem1133686 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term85 _26750 h Q t) = (term86 _26750 h Q t).
Proof. exact (fun_ext (fun P : _26750 -> Prop => @lem1133683 _26750 P h Q t)). Qed.
Lemma lem1133687 {_26750 : Type'} : (@all (_26750 -> Prop)) = (@all (_26750 -> Prop)).
Proof. exact (eq_refl (@all (_26750 -> Prop))). Qed.
Lemma lem1133688 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term87 _26750 h Q t) = (term88 _26750 h Q t).
Proof. exact (MK_COMB (@lem1133687 _26750) (@lem1133686 _26750 h Q t)). Qed.
Lemma lem1133693 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term89 _26750 Q t) = (term90 _26750 Q t).
Proof. exact (fun_ext (fun h : _26750 => @lem1133688 _26750 h Q t)). Qed.
Lemma lem1133694 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1133695 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term91 _26750 Q t) = (term92 _26750 Q t).
Proof. exact (MK_COMB (@lem1133694 _26750) (@lem1133693 _26750 Q t)). Qed.
Lemma lem1133700 {_26750 : Type'} (t : list _26750) : (term93 _26750 t) = (term94 _26750 t).
Proof. exact (fun_ext (fun Q : _26750 -> Prop => @lem1133695 _26750 Q t)). Qed.
Lemma lem1133701 {_26750 : Type'} : (@all (_26750 -> Prop)) = (@all (_26750 -> Prop)).
Proof. exact (eq_refl (@all (_26750 -> Prop))). Qed.
Lemma lem1133702 {_26750 : Type'} (t : list _26750) : (term95 _26750 t) = (term96 _26750 t).
Proof. exact (MK_COMB (@lem1133701 _26750) (@lem1133700 _26750 t)). Qed.
Lemma lem1133707 {_26750 : Type'} : (term97 _26750) = (term98 _26750).
Proof. exact (fun_ext (fun t : list _26750 => @lem1133702 _26750 t)). Qed.
Lemma lem1133708 {_26750 : Type'} : (@all (list _26750)) = (@all (list _26750)).
Proof. exact (eq_refl (@all (list _26750))). Qed.
Lemma lem1133717 {_26750 : Type'} : (term99 _26750) = (term100 _26750).
Proof. exact (MK_COMB (@lem1133708 _26750) (@lem1133707 _26750)). Qed.
Lemma lem1133722 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term69 _26750 h Q t) = (term69 _26750 h Q t).
Proof. exact (eq_refl (term69 _26750 h Q t)). Qed.
Lemma lem1133727 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term69 _26750 h P t) = (term69 _26750 h P t).
Proof. exact (eq_refl (term69 _26750 h P t)). Qed.
Lemma lem1133740 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term61 _26750 h t P Q x) = (term61 _26750 h t P Q x).
Proof. exact (eq_refl (term61 _26750 h t P Q x)). Qed.
Lemma lem1133741 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term63 _26750 h t P Q) = (term63 _26750 h t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1133740 _26750 h t P Q x)). Qed.
Lemma lem1133742 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1133743 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term65 _26750 h t P Q) = (term65 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1133742 _26750) (@lem1133741 _26750 h t P Q)). Qed.
Lemma lem1133744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133745 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term67 _26750 h t P Q) = (term67 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1133744) (@lem1133743 _26750 h t P Q)). Qed.
Lemma lem1133746 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term71 _26750 Q h P t) = (term71 _26750 Q h P t).
Proof. exact (MK_COMB (@lem1133745 _26750 h t P Q) (@lem1133727 _26750 h P t)). Qed.
Lemma lem1133747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133748 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term73 _26750 Q h P t) = (term73 _26750 Q h P t).
Proof. exact (MK_COMB (@lem1133747) (@lem1133746 _26750 Q h P t)). Qed.
Lemma lem1133749 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term74 _26750 P h Q t) = (term74 _26750 P h Q t).
Proof. exact (MK_COMB (@lem1133748 _26750 Q h P t) (@lem1133722 _26750 h Q t)). Qed.
Lemma lem1133750 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (@EX _26750 Q t) = (@EX _26750 Q t).
Proof. exact (eq_refl (@EX _26750 Q t)). Qed.
Lemma lem1133751 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (@EX _26750 P t) = (@EX _26750 P t).
Proof. exact (eq_refl (@EX _26750 P t)). Qed.
Lemma lem1133760 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term101 _26750 t P Q x) = (term101 _26750 t P Q x).
Proof. exact (eq_refl (term101 _26750 t P Q x)). Qed.
Lemma lem1133761 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term102 _26750 t P Q) = (term102 _26750 t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1133760 _26750 t P Q x)). Qed.
Lemma lem1133762 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1133763 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term103 _26750 t P Q) = (term103 _26750 t P Q).
Proof. exact (MK_COMB (@lem1133762 _26750) (@lem1133761 _26750 t P Q)). Qed.
Lemma lem1133764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133765 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term104 _26750 t P Q) = (term104 _26750 t P Q).
Proof. exact (MK_COMB (@lem1133764) (@lem1133763 _26750 t P Q)). Qed.
Lemma lem1133766 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term105 _26750 Q P t) = (term105 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133765 _26750 t P Q) (@lem1133751 _26750 P t)). Qed.
Lemma lem1133767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133768 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term106 _26750 Q P t) = (term106 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133767) (@lem1133766 _26750 Q P t)). Qed.
Lemma lem1133769 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term15 _26750 P Q t) = (term15 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133768 _26750 Q P t) (@lem1133750 _26750 Q t)). Qed.
Lemma lem1133770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133771 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term17 _26750 P Q t) = (term17 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133770) (@lem1133769 _26750 P Q t)). Qed.
Lemma lem1133772 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term84 _26750 P h Q t) = (term84 _26750 P h Q t).
Proof. exact (MK_COMB (@lem1133771 _26750 P Q t) (@lem1133749 _26750 P h Q t)). Qed.
Lemma lem1133773 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term86 _26750 h Q t) = (term86 _26750 h Q t).
Proof. exact (fun_ext (fun P : _26750 -> Prop => @lem1133772 _26750 P h Q t)). Qed.
Lemma lem1133774 {_26750 : Type'} : (@all (_26750 -> Prop)) = (@all (_26750 -> Prop)).
Proof. exact (eq_refl (@all (_26750 -> Prop))). Qed.
Lemma lem1133775 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term88 _26750 h Q t) = (term88 _26750 h Q t).
Proof. exact (MK_COMB (@lem1133774 _26750) (@lem1133773 _26750 h Q t)). Qed.
Lemma lem1133776 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term90 _26750 Q t) = (term90 _26750 Q t).
Proof. exact (fun_ext (fun h : _26750 => @lem1133775 _26750 h Q t)). Qed.
Lemma lem1133777 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1133778 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term92 _26750 Q t) = (term92 _26750 Q t).
Proof. exact (MK_COMB (@lem1133777 _26750) (@lem1133776 _26750 Q t)). Qed.
Lemma lem1133779 {_26750 : Type'} (t : list _26750) : (term94 _26750 t) = (term94 _26750 t).
Proof. exact (fun_ext (fun Q : _26750 -> Prop => @lem1133778 _26750 Q t)). Qed.
Lemma lem1133780 {_26750 : Type'} : (@all (_26750 -> Prop)) = (@all (_26750 -> Prop)).
Proof. exact (eq_refl (@all (_26750 -> Prop))). Qed.
Lemma lem1133781 {_26750 : Type'} (t : list _26750) : (term96 _26750 t) = (term96 _26750 t).
Proof. exact (MK_COMB (@lem1133780 _26750) (@lem1133779 _26750 t)). Qed.
Lemma lem1133782 {_26750 : Type'} : (term98 _26750) = (term98 _26750).
Proof. exact (fun_ext (fun t : list _26750 => @lem1133781 _26750 t)). Qed.
Lemma lem1133783 {_26750 : Type'} : (@all (list _26750)) = (@all (list _26750)).
Proof. exact (eq_refl (@all (list _26750))). Qed.
Lemma lem1133784 {_26750 : Type'} : (term100 _26750) = (term100 _26750).
Proof. exact (MK_COMB (@lem1133783 _26750) (@lem1133782 _26750)). Qed.
Lemma lem1133847 {_26750 : Type'} : (term99 _26750) = (term100 _26750).
Proof. exact (TRANS (@lem1133717 _26750) (@lem1133784 _26750)). Qed.
Lemma lem1133848 {_26750 : Type'} : (term100 _26750) = (term99 _26750).
Proof. exact (SYM (@lem1133847 _26750)). Qed.
Lemma lem1133849 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term15 _26750 P Q t.
Proof. exact (h1). Qed.
Lemma lem1133850 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term71 _26750 Q h P t.
Proof. exact (h1). Qed.
Lemma lem1133852 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1133853 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term69 _26750 h Q t) = (term107 _26750 h Q t).
Proof. exact (@lem1133852 (term69 _26750 h Q t)). Qed.
Lemma lem1133854 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term107 _26750 h Q t) = (term69 _26750 h Q t).
Proof. exact (SYM (@lem1133853 _26750 h Q t)). Qed.
Lemma lem1133855 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term108 _26750 h Q t.
Proof. exact (h1). Qed.
Lemma lem1133866 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term109 _26750 t P Q x) = (term110 _26750 t P Q x).
Proof. exact (@lem17362 (term111 _26750 t P x) (Q x)). Qed.
Lemma lem1133867 {_26750 : Type'} (P : _26750 -> Prop) : (term112 _26750 P) = (term113 _26750 P).
Proof. exact (@lem18392 _26750 P). Qed.
Lemma lem1133868 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term114 _26750 t P Q) = (term115 _26750 t P Q).
Proof. exact (@lem1133867 _26750 (term102 _26750 t P Q)). Qed.
Lemma lem1133869 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term116 _26750 t P Q x) = (term101 _26750 t P Q x).
Proof. exact (eq_refl (term116 _26750 t P Q x)). Qed.
Lemma lem1133870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1133871 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term117 _26750 t P Q x) = (term109 _26750 t P Q x).
Proof. exact (MK_COMB (@lem1133870) (@lem1133869 _26750 t P Q x)). Qed.
Lemma lem1133872 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term117 _26750 t P Q x) = (term110 _26750 t P Q x).
Proof. exact (TRANS (@lem1133871 _26750 t P Q x) (@lem1133866 _26750 t P Q x)). Qed.
Lemma lem1133873 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term118 _26750 t P Q) = (term119 _26750 t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1133872 _26750 t P Q x)). Qed.
Lemma lem1133874 {_26750 : Type'} : (@ex _26750) = (@ex _26750).
Proof. exact (eq_refl (@ex _26750)). Qed.
Lemma lem1133875 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term115 _26750 t P Q) = (term120 _26750 t P Q).
Proof. exact (MK_COMB (@lem1133874 _26750) (@lem1133873 _26750 t P Q)). Qed.
Lemma lem1133876 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term114 _26750 t P Q) = (term120 _26750 t P Q).
Proof. exact (TRANS (@lem1133868 _26750 t P Q) (@lem1133875 _26750 t P Q)). Qed.
Lemma lem1133877 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (term121 _26750 P t) = (term121 _26750 P t).
Proof. exact (eq_refl (term121 _26750 P t)). Qed.
Lemma lem1133878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1133879 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term122 _26750 t P Q) = (term123 _26750 t P Q).
Proof. exact (MK_COMB (@lem1133878) (@lem1133876 _26750 t P Q)). Qed.
Lemma lem1133880 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term124 _26750 Q P t) = (term125 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133879 _26750 t P Q) (@lem1133877 _26750 P t)). Qed.
Lemma lem1133881 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term126 _26750 Q P t) = (term124 _26750 Q P t).
Proof. exact (@lem17045 (term103 _26750 t P Q) (@EX _26750 P t)). Qed.
Lemma lem1133882 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term126 _26750 Q P t) = (term125 _26750 Q P t).
Proof. exact (TRANS (@lem1133881 _26750 Q P t) (@lem1133880 _26750 Q P t)). Qed.
Lemma lem1133883 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (@EX _26750 Q t) = (@EX _26750 Q t).
Proof. exact (eq_refl (@EX _26750 Q t)). Qed.
Lemma lem1133884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1133885 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term127 _26750 Q P t) = (term128 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133884) (@lem1133882 _26750 Q P t)). Qed.
Lemma lem1133886 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term129 _26750 P Q t) = (term130 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133885 _26750 Q P t) (@lem1133883 _26750 Q t)). Qed.
Lemma lem1133887 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term15 _26750 P Q t) = (term129 _26750 P Q t).
Proof. exact (@lem17265 (term105 _26750 Q P t) (@EX _26750 Q t)). Qed.
Lemma lem1133888 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term15 _26750 P Q t) = (term130 _26750 P Q t).
Proof. exact (TRANS (@lem1133887 _26750 P Q t) (@lem1133886 _26750 P Q t)). Qed.
Lemma lem1133939 {A : Type'} (P : A -> Prop) (Q : Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1133940 {_26750 : Type'} (P : _26750 -> Prop) (Q : Prop) : (term131 _26750 P Q) = (term132 _26750 P Q).
Proof. exact (@lem1133939 _26750 P Q). Qed.
Lemma lem1133941 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term133 _26750 Q P t) = (term134 _26750 Q P t).
Proof. exact (@lem1133940 _26750 (term119 _26750 t P Q) (term121 _26750 P t)). Qed.
Lemma lem1133942 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term135 _26750 t P Q x) = (term110 _26750 t P Q x).
Proof. exact (eq_refl (term135 _26750 t P Q x)). Qed.
Lemma lem1133943 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term136 _26750 t P Q) = (term119 _26750 t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1133942 _26750 t P Q x)). Qed.
Lemma lem1133944 {_26750 : Type'} : (@ex _26750) = (@ex _26750).
Proof. exact (eq_refl (@ex _26750)). Qed.
Lemma lem1133945 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term137 _26750 t P Q) = (term120 _26750 t P Q).
Proof. exact (MK_COMB (@lem1133944 _26750) (@lem1133943 _26750 t P Q)). Qed.
Lemma lem1133946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1133947 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term138 _26750 t P Q) = (term123 _26750 t P Q).
Proof. exact (MK_COMB (@lem1133946) (@lem1133945 _26750 t P Q)). Qed.
Lemma lem1133948 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (term121 _26750 P t) = (term121 _26750 P t).
Proof. exact (eq_refl (term121 _26750 P t)). Qed.
Lemma lem1133949 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term133 _26750 Q P t) = (term125 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133947 _26750 t P Q) (@lem1133948 _26750 P t)). Qed.
Lemma lem1133950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1133951 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term139 _26750 Q P t) = (term140 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133950) (@lem1133949 _26750 Q P t)). Qed.
Lemma lem1133952 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term135 _26750 t P Q x) = (term110 _26750 t P Q x).
Proof. exact (eq_refl (term135 _26750 t P Q x)). Qed.
Lemma lem1133953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1133954 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term141 _26750 t P Q x) = (term142 _26750 t P Q x).
Proof. exact (MK_COMB (@lem1133953) (@lem1133952 _26750 t P Q x)). Qed.
Lemma lem1133955 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (term121 _26750 P t) = (term121 _26750 P t).
Proof. exact (eq_refl (term121 _26750 P t)). Qed.
Lemma lem1133956 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) : (term143 _26750 Q x P t) = (term144 _26750 Q x P t).
Proof. exact (MK_COMB (@lem1133954 _26750 t P Q x) (@lem1133955 _26750 P t)). Qed.
Lemma lem1133957 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term145 _26750 Q P t) = (term146 _26750 Q P t).
Proof. exact (fun_ext (fun x : _26750 => @lem1133956 _26750 Q x P t)). Qed.
Lemma lem1133958 {_26750 : Type'} : (@ex _26750) = (@ex _26750).
Proof. exact (eq_refl (@ex _26750)). Qed.
Lemma lem1133959 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term134 _26750 Q P t) = (term147 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133958 _26750) (@lem1133957 _26750 Q P t)). Qed.
Lemma lem1133960 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : ((term133 _26750 Q P t) = (term134 _26750 Q P t)) = ((term125 _26750 Q P t) = (term147 _26750 Q P t)).
Proof. exact (MK_COMB (@lem1133951 _26750 Q P t) (@lem1133959 _26750 Q P t)). Qed.
Lemma lem1133961 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term125 _26750 Q P t) = (term147 _26750 Q P t).
Proof. exact (EQ_MP (@lem1133960 _26750 Q P t) (@lem1133941 _26750 Q P t)). Qed.
Lemma lem1133962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1133963 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term128 _26750 Q P t) = (term148 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133962) (@lem1133961 _26750 Q P t)). Qed.
Lemma lem1133964 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (@EX _26750 Q t) = (@EX _26750 Q t).
Proof. exact (eq_refl (@EX _26750 Q t)). Qed.
Lemma lem1133965 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term130 _26750 P Q t) = (term149 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133963 _26750 Q P t) (@lem1133964 _26750 Q t)). Qed.
Lemma lem1133967 {A : Type'} (P : A -> Prop) (Q : Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1133968 {_26750 : Type'} (P : _26750 -> Prop) (Q : Prop) : (term131 _26750 P Q) = (term132 _26750 P Q).
Proof. exact (@lem1133967 _26750 P Q). Qed.
Lemma lem1133969 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term150 _26750 P Q t) = (term151 _26750 P Q t).
Proof. exact (@lem1133968 _26750 (term146 _26750 Q P t) (@EX _26750 Q t)). Qed.
Lemma lem1133970 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) : (term152 _26750 Q P t x) = (term144 _26750 Q x P t).
Proof. exact (eq_refl (term152 _26750 Q P t x)). Qed.
Lemma lem1133971 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term153 _26750 Q P t) = (term146 _26750 Q P t).
Proof. exact (fun_ext (fun x : _26750 => @lem1133970 _26750 Q x P t)). Qed.
Lemma lem1133972 {_26750 : Type'} : (@ex _26750) = (@ex _26750).
Proof. exact (eq_refl (@ex _26750)). Qed.
Lemma lem1133973 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term154 _26750 Q P t) = (term147 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133972 _26750) (@lem1133971 _26750 Q P t)). Qed.
Lemma lem1133974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1133975 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (t : list _26750) : (term155 _26750 Q P t) = (term148 _26750 Q P t).
Proof. exact (MK_COMB (@lem1133974) (@lem1133973 _26750 Q P t)). Qed.
Lemma lem1133976 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (@EX _26750 Q t) = (@EX _26750 Q t).
Proof. exact (eq_refl (@EX _26750 Q t)). Qed.
Lemma lem1133977 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term150 _26750 P Q t) = (term149 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133975 _26750 Q P t) (@lem1133976 _26750 Q t)). Qed.
Lemma lem1133978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1133979 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term156 _26750 P Q t) = (term157 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133978) (@lem1133977 _26750 P Q t)). Qed.
Lemma lem1133980 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) : (term152 _26750 Q P t x) = (term144 _26750 Q x P t).
Proof. exact (eq_refl (term152 _26750 Q P t x)). Qed.
Lemma lem1133981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1133982 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) : (term158 _26750 Q P t x) = (term159 _26750 Q x P t).
Proof. exact (MK_COMB (@lem1133981) (@lem1133980 _26750 Q x P t)). Qed.
Lemma lem1133983 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (@EX _26750 Q t) = (@EX _26750 Q t).
Proof. exact (eq_refl (@EX _26750 Q t)). Qed.
Lemma lem1133984 {_26750 : Type'} (x : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term160 _26750 P x Q t) = (term161 _26750 x P Q t).
Proof. exact (MK_COMB (@lem1133982 _26750 Q x P t) (@lem1133983 _26750 Q t)). Qed.
Lemma lem1133985 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term162 _26750 P Q t) = (term163 _26750 P Q t).
Proof. exact (fun_ext (fun x : _26750 => @lem1133984 _26750 x P Q t)). Qed.
Lemma lem1133986 {_26750 : Type'} : (@ex _26750) = (@ex _26750).
Proof. exact (eq_refl (@ex _26750)). Qed.
Lemma lem1133987 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term151 _26750 P Q t) = (term164 _26750 P Q t).
Proof. exact (MK_COMB (@lem1133986 _26750) (@lem1133985 _26750 P Q t)). Qed.
Lemma lem1133988 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : ((term150 _26750 P Q t) = (term151 _26750 P Q t)) = ((term149 _26750 P Q t) = (term164 _26750 P Q t)).
Proof. exact (MK_COMB (@lem1133979 _26750 P Q t) (@lem1133987 _26750 P Q t)). Qed.
Lemma lem1133989 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term149 _26750 P Q t) = (term164 _26750 P Q t).
Proof. exact (EQ_MP (@lem1133988 _26750 P Q t) (@lem1133969 _26750 P Q t)). Qed.
Lemma lem1133991 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term130 _26750 P Q t) = (term164 _26750 P Q t).
Proof. exact (TRANS (@lem1133965 _26750 P Q t) (@lem1133989 _26750 P Q t)). Qed.
Lemma lem1133992 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term15 _26750 P Q t) = (term164 _26750 P Q t).
Proof. exact (TRANS (@lem1133888 _26750 P Q t) (@lem1133991 _26750 P Q t)). Qed.
Lemma lem1133993 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term164 _26750 P Q t.
Proof. exact (EQ_MP (@lem1133992 _26750 P Q t) (@lem1133849 _26750 P Q t h1)). Qed.
Lemma lem1134000 {_26750 : Type'} (h : _26750) (x : _26750) (t : list _26750) : (term165 _26750 h x t) = (term166 _26750 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _26750 x t)). Qed.
Lemma lem1134001 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term167 _26750 P x) = (term167 _26750 P x).
Proof. exact (eq_refl (term167 _26750 P x)). Qed.
Lemma lem1134002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134003 {_26750 : Type'} (h : _26750) (x : _26750) (t : list _26750) : (term168 _26750 h x t) = (term169 _26750 h x t).
Proof. exact (MK_COMB (@lem1134002) (@lem1134000 _26750 h x t)). Qed.
Lemma lem1134004 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term170 _26750 h t P x) = (term171 _26750 h t P x).
Proof. exact (MK_COMB (@lem1134003 _26750 h x t) (@lem1134001 _26750 P x)). Qed.
Lemma lem1134005 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term172 _26750 h t P x) = (term170 _26750 h t P x).
Proof. exact (@lem17045 (term53 _26750 h x t) (P x)). Qed.
Lemma lem1134006 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term172 _26750 h t P x) = (term171 _26750 h t P x).
Proof. exact (TRANS (@lem1134005 _26750 h t P x) (@lem1134004 _26750 h t P x)). Qed.
Lemma lem1134007 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (Q x) = (Q x).
Proof. exact (eq_refl (Q x)). Qed.
Lemma lem1134008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134009 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term173 _26750 h t P x) = (term174 _26750 h t P x).
Proof. exact (MK_COMB (@lem1134008) (@lem1134006 _26750 h t P x)). Qed.
Lemma lem1134010 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term175 _26750 h t P Q x) = (term176 _26750 h t P Q x).
Proof. exact (MK_COMB (@lem1134009 _26750 h t P x) (@lem1134007 _26750 Q x)). Qed.
Lemma lem1134011 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term61 _26750 h t P Q x) = (term175 _26750 h t P Q x).
Proof. exact (@lem17265 (term57 _26750 h t P x) (Q x)). Qed.
Lemma lem1134012 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term61 _26750 h t P Q x) = (term176 _26750 h t P Q x).
Proof. exact (TRANS (@lem1134011 _26750 h t P Q x) (@lem1134010 _26750 h t P Q x)). Qed.
Lemma lem1134013 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term63 _26750 h t P Q) = (term177 _26750 h t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1134012 _26750 h t P Q x)). Qed.
Lemma lem1134014 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1134015 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term65 _26750 h t P Q) = (term178 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1134014 _26750) (@lem1134013 _26750 h t P Q)). Qed.
Lemma lem1134020 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term69 _26750 h P t) = (term69 _26750 h P t).
Proof. exact (eq_refl (term69 _26750 h P t)). Qed.
Lemma lem1134021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1134022 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term67 _26750 h t P Q) = (term179 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1134021) (@lem1134015 _26750 h t P Q)). Qed.
Lemma lem1134059 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term71 _26750 Q h P t) = (term180 _26750 Q h P t).
Proof. exact (MK_COMB (@lem1134022 _26750 h t P Q) (@lem1134020 _26750 h P t)). Qed.
Lemma lem1134060 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term180 _26750 Q h P t.
Proof. exact (EQ_MP (@lem1134059 _26750 Q h P t) (@lem1133850 _26750 Q h P t h1)). Qed.
Lemma lem1134071 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term108 _26750 h Q t) = (term181 _26750 h Q t).
Proof. exact (@lem17160 (Q h) (@EX _26750 Q t)). Qed.
Lemma lem1134072 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term181 _26750 h Q t.
Proof. exact (EQ_MP (@lem1134071 _26750 h Q t) (@lem1133855 _26750 h Q t h1)). Qed.
Lemma lem1134073 {_26750 : Type'} (x : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term161 _26750 x P Q t) : term161 _26750 x P Q t.
Proof. exact (h1). Qed.
Lemma lem1134078 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (@EX _26750 P t) = (@EX _26750 P t).
Proof. exact (eq_refl (@EX _26750 P t)). Qed.
Lemma lem1134083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1134084 {_26750 : Type'} (f : _26750 -> Prop) (x : _26750) : (f x) = (@I (_26750 -> Prop) f x).
Proof. exact (@lem1134083 _26750 Prop f x). Qed.
Lemma lem1134086 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) : (P h) = (@I (_26750 -> Prop) P h).
Proof. exact (@lem1134084 _26750 P h). Qed.
Lemma lem1134087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134088 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) : (term182 _26750 P h) = (term183 _26750 P h).
Proof. exact (MK_COMB (@lem1134087) (@lem1134086 _26750 P h)). Qed.
Lemma lem1134089 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term69 _26750 h P t) = (term184 _26750 h P t).
Proof. exact (MK_COMB (@lem1134088 _26750 P h) (@lem1134078 _26750 P t)). Qed.
Lemma lem1134094 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1134095 {_26750 : Type'} (f : _26750 -> Prop) (x : _26750) : (f x) = (@I (_26750 -> Prop) f x).
Proof. exact (@lem1134094 _26750 Prop f x). Qed.
Lemma lem1134097 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (Q x) = (@I (_26750 -> Prop) Q x).
Proof. exact (@lem1134095 _26750 Q x). Qed.
Lemma lem1134098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1134103 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1134104 {_26750 : Type'} (f : _26750 -> Prop) (x : _26750) : (f x) = (@I (_26750 -> Prop) f x).
Proof. exact (@lem1134103 _26750 Prop f x). Qed.
Lemma lem1134106 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (P x) = (@I (_26750 -> Prop) P x).
Proof. exact (@lem1134104 _26750 P x). Qed.
Lemma lem1134107 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term167 _26750 P x) = (term185 _26750 P x).
Proof. exact (MK_COMB (@lem1134098) (@lem1134106 _26750 P x)). Qed.
Lemma lem1134126 {_26750 : Type'} (h : _26750) (x : _26750) (t : list _26750) : (term169 _26750 h x t) = (term169 _26750 h x t).
Proof. exact (eq_refl (term169 _26750 h x t)). Qed.
Lemma lem1134127 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term171 _26750 h t P x) = (term186 _26750 h t P x).
Proof. exact (MK_COMB (@lem1134126 _26750 h x t) (@lem1134107 _26750 P x)). Qed.
Lemma lem1134128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134129 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term174 _26750 h t P x) = (term187 _26750 h t P x).
Proof. exact (MK_COMB (@lem1134128) (@lem1134127 _26750 h t P x)). Qed.
Lemma lem1134130 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term176 _26750 h t P Q x) = (term188 _26750 h t P Q x).
Proof. exact (MK_COMB (@lem1134129 _26750 h t P x) (@lem1134097 _26750 Q x)). Qed.
Lemma lem1134131 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term177 _26750 h t P Q) = (term189 _26750 h t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1134130 _26750 h t P Q x)). Qed.
Lemma lem1134132 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1134133 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term178 _26750 h t P Q) = (term190 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1134132 _26750) (@lem1134131 _26750 h t P Q)). Qed.
Lemma lem1134134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1134135 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term179 _26750 h t P Q) = (term191 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1134134) (@lem1134133 _26750 h t P Q)). Qed.
Lemma lem1134136 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) : (term180 _26750 Q h P t) = (term192 _26750 Q h P t).
Proof. exact (MK_COMB (@lem1134135 _26750 h t P Q) (@lem1134089 _26750 h P t)). Qed.
Lemma lem1134137 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term192 _26750 Q h P t.
Proof. exact (EQ_MP (@lem1134136 _26750 Q h P t) (@lem1134060 _26750 Q h P t h1)). Qed.
Lemma lem1134144 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term121 _26750 Q t) = (term121 _26750 Q t).
Proof. exact (eq_refl (term121 _26750 Q t)). Qed.
Lemma lem1134145 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1134150 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1134151 {_26750 : Type'} (f : _26750 -> Prop) (x : _26750) : (f x) = (@I (_26750 -> Prop) f x).
Proof. exact (@lem1134150 _26750 Prop f x). Qed.
Lemma lem1134153 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) : (Q h) = (@I (_26750 -> Prop) Q h).
Proof. exact (@lem1134151 _26750 Q h). Qed.
Lemma lem1134154 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) : (term167 _26750 Q h) = (term185 _26750 Q h).
Proof. exact (MK_COMB (@lem1134145) (@lem1134153 _26750 Q h)). Qed.
Lemma lem1134155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1134156 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) : (term193 _26750 Q h) = (term194 _26750 Q h).
Proof. exact (MK_COMB (@lem1134155) (@lem1134154 _26750 Q h)). Qed.
Lemma lem1134157 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term181 _26750 h Q t) = (term195 _26750 h Q t).
Proof. exact (MK_COMB (@lem1134156 _26750 Q h) (@lem1134144 _26750 Q t)). Qed.
Lemma lem1134158 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term195 _26750 h Q t.
Proof. exact (EQ_MP (@lem1134157 _26750 h Q t) (@lem1134072 _26750 h Q t h1)). Qed.
Lemma lem1134163 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (@EX _26750 Q t) = (@EX _26750 Q t).
Proof. exact (eq_refl (@EX _26750 Q t)). Qed.
Lemma lem1134170 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (term121 _26750 P t) = (term121 _26750 P t).
Proof. exact (eq_refl (term121 _26750 P t)). Qed.
Lemma lem1134171 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1134176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1134177 {_26750 : Type'} (f : _26750 -> Prop) (x : _26750) : (f x) = (@I (_26750 -> Prop) f x).
Proof. exact (@lem1134176 _26750 Prop f x). Qed.
Lemma lem1134179 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (Q x) = (@I (_26750 -> Prop) Q x).
Proof. exact (@lem1134177 _26750 Q x). Qed.
Lemma lem1134180 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (term167 _26750 Q x) = (term185 _26750 Q x).
Proof. exact (MK_COMB (@lem1134171) (@lem1134179 _26750 Q x)). Qed.
Lemma lem1134185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1134186 {_26750 : Type'} (f : _26750 -> Prop) (x : _26750) : (f x) = (@I (_26750 -> Prop) f x).
Proof. exact (@lem1134185 _26750 Prop f x). Qed.
Lemma lem1134188 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (P x) = (@I (_26750 -> Prop) P x).
Proof. exact (@lem1134186 _26750 P x). Qed.
Lemma lem1134195 {_26750 : Type'} (x : _26750) (t : list _26750) : (term196 _26750 x t) = (term196 _26750 x t).
Proof. exact (eq_refl (term196 _26750 x t)). Qed.
Lemma lem1134196 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term111 _26750 t P x) = (term197 _26750 t P x).
Proof. exact (MK_COMB (@lem1134195 _26750 x t) (@lem1134188 _26750 P x)). Qed.
Lemma lem1134197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1134198 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term198 _26750 t P x) = (term199 _26750 t P x).
Proof. exact (MK_COMB (@lem1134197) (@lem1134196 _26750 t P x)). Qed.
Lemma lem1134199 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term110 _26750 t P Q x) = (term200 _26750 t P Q x).
Proof. exact (MK_COMB (@lem1134198 _26750 t P x) (@lem1134180 _26750 Q x)). Qed.
Lemma lem1134200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134201 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term142 _26750 t P Q x) = (term201 _26750 t P Q x).
Proof. exact (MK_COMB (@lem1134200) (@lem1134199 _26750 t P Q x)). Qed.
Lemma lem1134202 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) : (term144 _26750 Q x P t) = (term202 _26750 Q x P t).
Proof. exact (MK_COMB (@lem1134201 _26750 t P Q x) (@lem1134170 _26750 P t)). Qed.
Lemma lem1134203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134204 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) : (term159 _26750 Q x P t) = (term203 _26750 Q x P t).
Proof. exact (MK_COMB (@lem1134203) (@lem1134202 _26750 Q x P t)). Qed.
Lemma lem1134205 {_26750 : Type'} (x : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) : (term161 _26750 x P Q t) = (term204 _26750 x P Q t).
Proof. exact (MK_COMB (@lem1134204 _26750 Q x P t) (@lem1134163 _26750 Q t)). Qed.
Lemma lem1134206 {_26750 : Type'} (x : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term161 _26750 x P Q t) : term204 _26750 x P Q t.
Proof. exact (EQ_MP (@lem1134205 _26750 x P Q t) (@lem1134073 _26750 x P Q t h1)). Qed.
Lemma lem1134209 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term184 _26750 h P t.
Proof. exact (proj2 (@lem1134137 _26750 Q h P t h1)). Qed.
Lemma lem1134210 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term190 _26750 h t P Q.
Proof. exact (proj1 (@lem1134137 _26750 Q h P t h1)). Qed.
Lemma lem1134213 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term202 _26750 Q x P t) : term202 _26750 Q x P t.
Proof. exact (h1). Qed.
Lemma lem1134215 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term200 _26750 t P Q x.
Proof. exact (h1). Qed.
Lemma lem1134218 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term197 _26750 t P x.
Proof. exact (proj1 (@lem1134215 _26750 t P Q x h1)). Qed.
Lemma lem1134221 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term202 _26750 Q x P t) : term202 _26750 Q x P t.
Proof. exact (h1). Qed.
Lemma lem1134223 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term200 _26750 t P Q x.
Proof. exact (h1). Qed.
Lemma lem1134226 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term197 _26750 t P x.
Proof. exact (proj1 (@lem1134223 _26750 t P Q x h1)). Qed.
Lemma lem1134238 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (@I (_26750 -> Prop) Q x) = (@I (_26750 -> Prop) Q x).
Proof. exact (eq_refl (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134255 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term186 _26750 h t P x) = (term205 _26750 h t P x).
Proof. exact (@lem19699 (term206 _26750 x h) (term207 _26750 x t) (term185 _26750 P x)). Qed.
Lemma lem1134256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134257 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term187 _26750 h t P x) = (term208 _26750 h t P x).
Proof. exact (MK_COMB (@lem1134256) (@lem1134255 _26750 h t P x)). Qed.
Lemma lem1134258 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term188 _26750 h t P Q x) = (term209 _26750 h t P Q x).
Proof. exact (MK_COMB (@lem1134257 _26750 h t P x) (@lem1134238 _26750 Q x)). Qed.
Lemma lem1134265 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term209 _26750 h t P Q x) = (term210 _26750 h t P Q x).
Proof. exact (@lem19699 (term211 _26750 h P x) (term212 _26750 t P x) (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134266 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term188 _26750 h t P Q x) = (term210 _26750 h t P Q x).
Proof. exact (TRANS (@lem1134258 _26750 h t P Q x) (@lem1134265 _26750 h t P Q x)). Qed.
Lemma lem1134267 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term189 _26750 h t P Q) = (term213 _26750 h t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1134266 _26750 h t P Q x)). Qed.
Lemma lem1134268 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1134270 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term190 _26750 h t P Q) = (term214 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1134268 _26750) (@lem1134267 _26750 h t P Q)). Qed.
Lemma lem1134271 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term214 _26750 h t P Q.
Proof. exact (EQ_MP (@lem1134270 _26750 h t P Q) (@lem1134210 _26750 Q h P t h1)). Qed.
Lemma lem1134297 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (@I (_26750 -> Prop) Q x) = (@I (_26750 -> Prop) Q x).
Proof. exact (eq_refl (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134314 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term186 _26750 h t P x) = (term205 _26750 h t P x).
Proof. exact (@lem19699 (term206 _26750 x h) (term207 _26750 x t) (term185 _26750 P x)). Qed.
Lemma lem1134315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134316 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term187 _26750 h t P x) = (term208 _26750 h t P x).
Proof. exact (MK_COMB (@lem1134315) (@lem1134314 _26750 h t P x)). Qed.
Lemma lem1134317 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term188 _26750 h t P Q x) = (term209 _26750 h t P Q x).
Proof. exact (MK_COMB (@lem1134316 _26750 h t P x) (@lem1134297 _26750 Q x)). Qed.
Lemma lem1134324 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term209 _26750 h t P Q x) = (term210 _26750 h t P Q x).
Proof. exact (@lem19699 (term211 _26750 h P x) (term212 _26750 t P x) (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134325 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term188 _26750 h t P Q x) = (term210 _26750 h t P Q x).
Proof. exact (TRANS (@lem1134317 _26750 h t P Q x) (@lem1134324 _26750 h t P Q x)). Qed.
Lemma lem1134326 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term189 _26750 h t P Q) = (term213 _26750 h t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1134325 _26750 h t P Q x)). Qed.
Lemma lem1134327 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1134329 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term190 _26750 h t P Q) = (term214 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1134327 _26750) (@lem1134326 _26750 h t P Q)). Qed.
Lemma lem1134330 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term214 _26750 h t P Q.
Proof. exact (EQ_MP (@lem1134329 _26750 h t P Q) (@lem1134210 _26750 Q h P t h1)). Qed.
Lemma lem1134334 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (h1 : @I (_26750 -> Prop) P h) : @I (_26750 -> Prop) P h.
Proof. exact (h1). Qed.
Lemma lem1134389 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (h1). Qed.
Lemma lem1134399 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (@I (_26750 -> Prop) Q x) = (@I (_26750 -> Prop) Q x).
Proof. exact (eq_refl (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134416 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term186 _26750 h t P x) = (term205 _26750 h t P x).
Proof. exact (@lem19699 (term206 _26750 x h) (term207 _26750 x t) (term185 _26750 P x)). Qed.
Lemma lem1134417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1134418 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (x : _26750) : (term187 _26750 h t P x) = (term208 _26750 h t P x).
Proof. exact (MK_COMB (@lem1134417) (@lem1134416 _26750 h t P x)). Qed.
Lemma lem1134419 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term188 _26750 h t P Q x) = (term209 _26750 h t P Q x).
Proof. exact (MK_COMB (@lem1134418 _26750 h t P x) (@lem1134399 _26750 Q x)). Qed.
Lemma lem1134426 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term209 _26750 h t P Q x) = (term210 _26750 h t P Q x).
Proof. exact (@lem19699 (term211 _26750 h P x) (term212 _26750 t P x) (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134427 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) : (term188 _26750 h t P Q x) = (term210 _26750 h t P Q x).
Proof. exact (TRANS (@lem1134419 _26750 h t P Q x) (@lem1134426 _26750 h t P Q x)). Qed.
Lemma lem1134428 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term189 _26750 h t P Q) = (term213 _26750 h t P Q).
Proof. exact (fun_ext (fun x : _26750 => @lem1134427 _26750 h t P Q x)). Qed.
Lemma lem1134429 {_26750 : Type'} : (@all _26750) = (@all _26750).
Proof. exact (eq_refl (@all _26750)). Qed.
Lemma lem1134431 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) : (term190 _26750 h t P Q) = (term214 _26750 h t P Q).
Proof. exact (MK_COMB (@lem1134429 _26750) (@lem1134428 _26750 h t P Q)). Qed.
Lemma lem1134432 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term214 _26750 h t P Q.
Proof. exact (EQ_MP (@lem1134431 _26750 h t P Q) (@lem1134210 _26750 Q h P t h1)). Qed.
Lemma lem1134495 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 P t) : @EX _26750 P t.
Proof. exact (h1). Qed.
Lemma lem1134499 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) : term121 _26750 P t.
Proof. exact (h1). Qed.
Lemma lem1134550 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (h1). Qed.
Lemma lem1134551 {_26750 : Type'} (_18661 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term215 _26750 h t P Q _18661.
Proof. exact (@lem1134271 _26750 Q h P t h1 _18661). Qed.
Lemma lem1134552 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18661 : _26750) : (term215 _26750 h t P Q _18661) = (term210 _26750 h t P Q _18661).
Proof. exact (eq_refl (term215 _26750 h t P Q _18661)). Qed.
Lemma lem1134553 {_26750 : Type'} (_18661 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term210 _26750 h t P Q _18661.
Proof. exact (EQ_MP (@lem1134552 _26750 h t P Q _18661) (@lem1134551 _26750 _18661 Q h P t h1)). Qed.
Lemma lem1134554 {_26750 : Type'} (_18662 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term215 _26750 h t P Q _18662.
Proof. exact (@lem1134330 _26750 Q h P t h1 _18662). Qed.
Lemma lem1134555 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18662 : _26750) : (term215 _26750 h t P Q _18662) = (term210 _26750 h t P Q _18662).
Proof. exact (eq_refl (term215 _26750 h t P Q _18662)). Qed.
Lemma lem1134556 {_26750 : Type'} (_18662 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term210 _26750 h t P Q _18662.
Proof. exact (EQ_MP (@lem1134555 _26750 h t P Q _18662) (@lem1134554 _26750 _18662 Q h P t h1)). Qed.
Lemma lem1134560 {_26750 : Type'} (_18664 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term215 _26750 h t P Q _18664.
Proof. exact (@lem1134432 _26750 Q h P t h1 _18664). Qed.
Lemma lem1134561 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18664 : _26750) : (term215 _26750 h t P Q _18664) = (term210 _26750 h t P Q _18664).
Proof. exact (eq_refl (term215 _26750 h t P Q _18664)). Qed.
Lemma lem1134562 {_26750 : Type'} (_18664 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term210 _26750 h t P Q _18664.
Proof. exact (EQ_MP (@lem1134561 _26750 h t P Q _18664) (@lem1134560 _26750 _18664 Q h P t h1)). Qed.
Lemma lem1134569 {_26750 : Type'} (_18661 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term216 _26750 t P Q _18661.
Proof. exact (proj2 (@lem1134553 _26750 _18661 Q h P t h1)). Qed.
Lemma lem1134572 {_26750 : Type'} (_18662 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term217 _26750 h P Q _18662.
Proof. exact (proj1 (@lem1134556 _26750 _18662 Q h P t h1)). Qed.
Lemma lem1134575 {_26750 : Type'} (_18664 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term216 _26750 t P Q _18664.
Proof. exact (proj2 (@lem1134562 _26750 _18664 Q h P t h1)). Qed.
Lemma lem1134588 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term185 _26750 Q x.
Proof. exact (proj2 (@lem1134215 _26750 t P Q x h1)). Qed.
Lemma lem1134615 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18661 : _26750) : (term216 _26750 t P Q _18661) = (term218 _26750 t P Q _18661).
Proof. exact (@lem1133451 (term207 _26750 _18661 t) (term185 _26750 P _18661) (@I (_26750 -> Prop) Q _18661)). Qed.
Lemma lem1134616 {_26750 : Type'} (_18661 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term218 _26750 t P Q _18661.
Proof. exact (EQ_MP (@lem1134615 _26750 t P Q _18661) (@lem1134569 _26750 _18661 Q h P t h1)). Qed.
Lemma lem1134618 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term185 _26750 Q h.
Proof. exact (proj1 (@lem1134158 _26750 h Q t h1)). Qed.
Lemma lem1134622 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (h1 : @I (_26750 -> Prop) P h) : @I (_26750 -> Prop) P h.
Proof. exact (h1). Qed.
Lemma lem1134635 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18662 : _26750) : (term217 _26750 h P Q _18662) = (term219 _26750 h P Q _18662).
Proof. exact (@lem1133451 (term206 _26750 _18662 h) (term185 _26750 P _18662) (@I (_26750 -> Prop) Q _18662)). Qed.
Lemma lem1134636 {_26750 : Type'} (_18662 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term219 _26750 h P Q _18662.
Proof. exact (EQ_MP (@lem1134635 _26750 h P Q _18662) (@lem1134572 _26750 _18662 Q h P t h1)). Qed.
Lemma lem1134652 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term121 _26750 Q t.
Proof. exact (proj2 (@lem1134158 _26750 h Q t h1)). Qed.
Lemma lem1134656 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (h1). Qed.
Lemma lem1134688 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term185 _26750 Q x.
Proof. exact (proj2 (@lem1134223 _26750 t P Q x h1)). Qed.
Lemma lem1134715 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18664 : _26750) : (term216 _26750 t P Q _18664) = (term218 _26750 t P Q _18664).
Proof. exact (@lem1133451 (term207 _26750 _18664 t) (term185 _26750 P _18664) (@I (_26750 -> Prop) Q _18664)). Qed.
Lemma lem1134716 {_26750 : Type'} (_18664 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term218 _26750 t P Q _18664.
Proof. exact (EQ_MP (@lem1134715 _26750 t P Q _18664) (@lem1134575 _26750 _18664 Q h P t h1)). Qed.
Lemma lem1134722 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 P t) : @EX _26750 P t.
Proof. exact (h1). Qed.
Lemma lem1134724 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) : term121 _26750 P t.
Proof. exact (h1). Qed.
Lemma lem1134752 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term121 _26750 Q t.
Proof. exact (proj2 (@lem1134158 _26750 h Q t h1)). Qed.
Lemma lem1134756 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (h1). Qed.
Lemma lem1134845 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @List.In _26750 x t.
Proof. exact (proj1 (@lem1134218 _26750 t P Q x h1)). Qed.
Lemma lem1134846 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term220 _26750 x t.
Proof. exact (fun h0 : term207 _26750 x t => @lem1134845 _26750 t P Q x h1). Qed.
Lemma lem1134848 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1134849 {_26750 : Type'} (x : _26750) (t : list _26750) : (term220 _26750 x t) = (@List.In _26750 x t).
Proof. exact (@lem1134848 (@List.In _26750 x t)). Qed.
Lemma lem1134850 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @List.In _26750 x t.
Proof. exact (EQ_MP (@lem1134849 _26750 x t) (@lem1134846 _26750 t P Q x h1)). Qed.
Lemma lem1134852 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @I (_26750 -> Prop) P x.
Proof. exact (proj2 (@lem1134218 _26750 t P Q x h1)). Qed.
Lemma lem1134853 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term222 _26750 P x.
Proof. exact (fun h0 : term185 _26750 P x => @lem1134852 _26750 t P Q x h1). Qed.
Lemma lem1134855 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1134856 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term222 _26750 P x) = (@I (_26750 -> Prop) P x).
Proof. exact (@lem1134855 (@I (_26750 -> Prop) P x)). Qed.
Lemma lem1134857 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @I (_26750 -> Prop) P x.
Proof. exact (EQ_MP (@lem1134856 _26750 P x) (@lem1134853 _26750 t P Q x h1)). Qed.
Lemma lem1134863 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1134864 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (Q : _26750 -> Prop) (_18661 : _26750) : (term218 _26750 t P Q _18661) = (term223 _26750 P t Q _18661).
Proof. exact (@lem1134863 (term185 _26750 P _18661) (term207 _26750 _18661 t) (@I (_26750 -> Prop) Q _18661)). Qed.
Lemma lem1134878 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1134879 {_26750 : Type'} (Q : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term224 _26750 t Q _18661) = (term225 _26750 Q _18661 t).
Proof. exact (@lem1134878 (@I (_26750 -> Prop) Q _18661) (term207 _26750 _18661 t)). Qed.
Lemma lem1134885 {_26750 : Type'} (P : _26750 -> Prop) (_18661 : _26750) : (term226 _26750 P _18661) = (term226 _26750 P _18661).
Proof. exact (eq_refl (term226 _26750 P _18661)). Qed.
Lemma lem1134886 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term223 _26750 P t Q _18661) = (term227 _26750 P Q _18661 t).
Proof. exact (MK_COMB (@lem1134885 _26750 P _18661) (@lem1134879 _26750 Q _18661 t)). Qed.
Lemma lem1134890 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1134891 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term227 _26750 P Q _18661 t) = (term228 _26750 Q P _18661 t).
Proof. exact (@lem1134890 (@I (_26750 -> Prop) Q _18661) (term185 _26750 P _18661) (term207 _26750 _18661 t)). Qed.
Lemma lem1134907 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term223 _26750 P t Q _18661) = (term228 _26750 Q P _18661 t).
Proof. exact (TRANS (@lem1134886 _26750 P Q _18661 t) (@lem1134891 _26750 Q P _18661 t)). Qed.
Lemma lem1134908 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term218 _26750 t P Q _18661) = (term228 _26750 Q P _18661 t).
Proof. exact (TRANS (@lem1134864 _26750 P t Q _18661) (@lem1134907 _26750 Q P _18661 t)). Qed.
Lemma lem1134909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1134910 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term229 _26750 t P Q _18661) = (term230 _26750 Q P _18661 t).
Proof. exact (MK_COMB (@lem1134909) (@lem1134908 _26750 Q P _18661 t)). Qed.
Lemma lem1134924 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1134925 {_26750 : Type'} (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term212 _26750 t P _18661) = (term231 _26750 P _18661 t).
Proof. exact (@lem1134924 (term185 _26750 P _18661) (term207 _26750 _18661 t)). Qed.
Lemma lem1134931 {_26750 : Type'} (Q : _26750 -> Prop) (_18661 : _26750) : (term183 _26750 Q _18661) = (term183 _26750 Q _18661).
Proof. exact (eq_refl (term183 _26750 Q _18661)). Qed.
Lemma lem1134932 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : (term232 _26750 Q t P _18661) = (term228 _26750 Q P _18661 t).
Proof. exact (MK_COMB (@lem1134931 _26750 Q _18661) (@lem1134925 _26750 P _18661 t)). Qed.
Lemma lem1134943 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : ((term218 _26750 t P Q _18661) = (term232 _26750 Q t P _18661)) = ((term228 _26750 Q P _18661 t) = (term228 _26750 Q P _18661 t)).
Proof. exact (MK_COMB (@lem1134910 _26750 Q P _18661 t) (@lem1134932 _26750 Q P _18661 t)). Qed.
Lemma lem1134945 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1134946 (x : Prop) : (x = x) = True.
Proof. exact (@lem1134945 Prop x). Qed.
Lemma lem1134947 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18661 : _26750) (t : list _26750) : ((term228 _26750 Q P _18661 t) = (term228 _26750 Q P _18661 t)) = True.
Proof. exact (@lem1134946 (term228 _26750 Q P _18661 t)). Qed.
Lemma lem1134948 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (_18661 : _26750) : ((term218 _26750 t P Q _18661) = (term232 _26750 Q t P _18661)) = True.
Proof. exact (TRANS (@lem1134943 _26750 Q P _18661 t) (@lem1134947 _26750 Q P _18661 t)). Qed.
Lemma lem1134949 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (_18661 : _26750) : True = ((term218 _26750 t P Q _18661) = (term232 _26750 Q t P _18661)).
Proof. exact (SYM (@lem1134948 _26750 Q t P _18661)). Qed.
Lemma lem1134950 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (_18661 : _26750) : (term218 _26750 t P Q _18661) = (term232 _26750 Q t P _18661).
Proof. exact (EQ_MP (@lem1134949 _26750 Q t P _18661) (@lem0)). Qed.
Lemma lem1134951 {_26750 : Type'} (_18661 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term232 _26750 Q t P _18661.
Proof. exact (EQ_MP (@lem1134950 _26750 Q t P _18661) (@lem1134616 _26750 _18661 Q h P t h1)). Qed.
Lemma lem1134953 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1134954 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18661 : _26750) : (term232 _26750 Q t P _18661) = (term234 _26750 t P Q _18661).
Proof. exact (@lem1134953 (term212 _26750 t P _18661) (@I (_26750 -> Prop) Q _18661)). Qed.
Lemma lem1134956 (a : Prop) (b : Prop) : (term235 a b) = (term236 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1134957 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18661 : _26750) : (term237 _26750 t P _18661) = (term238 _26750 t P _18661).
Proof. exact (@lem1134956 (term207 _26750 _18661 t) (term185 _26750 P _18661)). Qed.
Lemma lem1134959 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1134960 {_26750 : Type'} (_18661 : _26750) (t : list _26750) : (term239 _26750 _18661 t) = (@List.In _26750 _18661 t).
Proof. exact (@lem1134959 (@List.In _26750 _18661 t)). Qed.
Lemma lem1134961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1134962 {_26750 : Type'} (_18661 : _26750) (t : list _26750) : (term240 _26750 _18661 t) = (term196 _26750 _18661 t).
Proof. exact (MK_COMB (@lem1134961) (@lem1134960 _26750 _18661 t)). Qed.
Lemma lem1134964 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1134965 {_26750 : Type'} (P : _26750 -> Prop) (_18661 : _26750) : (term241 _26750 P _18661) = (@I (_26750 -> Prop) P _18661).
Proof. exact (@lem1134964 (@I (_26750 -> Prop) P _18661)). Qed.
Lemma lem1134966 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18661 : _26750) : (term238 _26750 t P _18661) = (term197 _26750 t P _18661).
Proof. exact (MK_COMB (@lem1134962 _26750 _18661 t) (@lem1134965 _26750 P _18661)). Qed.
Lemma lem1134967 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18661 : _26750) : (term237 _26750 t P _18661) = (term197 _26750 t P _18661).
Proof. exact (TRANS (@lem1134957 _26750 t P _18661) (@lem1134966 _26750 t P _18661)). Qed.
Lemma lem1134968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1134969 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18661 : _26750) : (term242 _26750 t P _18661) = (term243 _26750 t P _18661).
Proof. exact (MK_COMB (@lem1134968) (@lem1134967 _26750 t P _18661)). Qed.
Lemma lem1134970 {_26750 : Type'} (Q : _26750 -> Prop) (_18661 : _26750) : (@I (_26750 -> Prop) Q _18661) = (@I (_26750 -> Prop) Q _18661).
Proof. exact (eq_refl (@I (_26750 -> Prop) Q _18661)). Qed.
Lemma lem1134971 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18661 : _26750) : (term234 _26750 t P Q _18661) = (term244 _26750 t P Q _18661).
Proof. exact (MK_COMB (@lem1134969 _26750 t P _18661) (@lem1134970 _26750 Q _18661)). Qed.
Lemma lem1134972 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18661 : _26750) : (term232 _26750 Q t P _18661) = (term244 _26750 t P Q _18661).
Proof. exact (TRANS (@lem1134954 _26750 t P Q _18661) (@lem1134971 _26750 t P Q _18661)). Qed.
Lemma lem1134974 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term197 _26750 t P x.
Proof. exact (conj (@lem1134850 _26750 t P Q x h1) (@lem1134857 _26750 t P Q x h1)). Qed.
Lemma lem1134976 {_26750 : Type'} (_18661 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term244 _26750 t P Q _18661.
Proof. exact (EQ_MP (@lem1134972 _26750 t P Q _18661) (@lem1134951 _26750 _18661 Q h P t h1)). Qed.
Lemma lem1134977 {_26750 : Type'} (_18661 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term244 _26750 t P Q _18661.
Proof. exact (@lem1134976 _26750 _18661 Q h P t h1). Qed.
Lemma lem1134978 {_26750 : Type'} (x : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term244 _26750 t P Q x.
Proof. exact (@lem1134977 _26750 x Q h P t h1). Qed.
Lemma lem1134981 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : @I (_26750 -> Prop) Q x.
Proof. exact (@lem1134978 _26750 x Q h P t h1 (@lem1134974 _26750 t P Q x h2)). Qed.
Lemma lem1134982 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : term222 _26750 Q x.
Proof. exact (fun h0 : term185 _26750 Q x => @lem1134981 _26750 h t P Q x h1 h2). Qed.
Lemma lem1134984 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1134985 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (term222 _26750 Q x) = (@I (_26750 -> Prop) Q x).
Proof. exact (@lem1134984 (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134986 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : @I (_26750 -> Prop) Q x.
Proof. exact (EQ_MP (@lem1134985 _26750 Q x) (@lem1134982 _26750 h t P Q x h1 h2)). Qed.
Lemma lem1134989 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1134991 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (term185 _26750 Q x) = (term245 _26750 Q x).
Proof. exact (@lem1134989 (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1134994 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term245 _26750 Q x.
Proof. exact (EQ_MP (@lem1134991 _26750 Q x) (@lem1134588 _26750 t P Q x h1)). Qed.
Lemma lem1134997 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : False.
Proof. exact (@lem1134994 _26750 t P Q x h2 (@lem1134986 _26750 h t P Q x h1 h2)). Qed.
Lemma lem1134998 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : term246.
Proof. exact (fun h0 : ~ False => @lem1134997 _26750 h t P Q x h1 h2). Qed.
Lemma lem1135000 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135001 : term246 = False.
Proof. exact (@lem1135000 False). Qed.
Lemma lem1135002 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : False.
Proof. exact (EQ_MP (@lem1135001) (@lem1134998 _26750 h t P Q x h1 h2)). Qed.
Lemma lem1135067 {_26750 : Type'} (x : _26750) : x = x.
Proof. exact (@lem21386 _26750 x). Qed.
Lemma lem1135068 {_26750 : Type'} (x : _26750) : x = x.
Proof. exact (@lem1135067 _26750 x). Qed.
Lemma lem1135069 {_26750 : Type'} (h : _26750) : h = h.
Proof. exact (@lem1135068 _26750 h). Qed.
Lemma lem1135070 {_26750 : Type'} (h : _26750) : term247 _26750 h.
Proof. exact (fun h0 : term248 _26750 h => @lem1135069 _26750 h). Qed.
Lemma lem1135072 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135073 {_26750 : Type'} (h : _26750) : (term247 _26750 h) = (h = h).
Proof. exact (@lem1135072 (h = h)). Qed.
Lemma lem1135074 {_26750 : Type'} (h : _26750) : h = h.
Proof. exact (EQ_MP (@lem1135073 _26750 h) (@lem1135070 _26750 h)). Qed.
Lemma lem1135076 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (h1 : @I (_26750 -> Prop) P h) : @I (_26750 -> Prop) P h.
Proof. exact (h1). Qed.
Lemma lem1135077 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (h1 : @I (_26750 -> Prop) P h) : term222 _26750 P h.
Proof. exact (fun h0 : term185 _26750 P h => @lem1135076 _26750 P h h1). Qed.
Lemma lem1135079 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135080 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) : (term222 _26750 P h) = (@I (_26750 -> Prop) P h).
Proof. exact (@lem1135079 (@I (_26750 -> Prop) P h)). Qed.
Lemma lem1135081 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (h1 : @I (_26750 -> Prop) P h) : @I (_26750 -> Prop) P h.
Proof. exact (EQ_MP (@lem1135080 _26750 P h) (@lem1135077 _26750 P h h1)). Qed.
Lemma lem1135099 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1135100 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18662 : _26750) : (term249 _26750 P Q _18662) = (term250 _26750 Q P _18662).
Proof. exact (@lem1135099 (@I (_26750 -> Prop) Q _18662) (term185 _26750 P _18662)). Qed.
Lemma lem1135106 {_26750 : Type'} (_18662 : _26750) (h : _26750) : (term251 _26750 _18662 h) = (term251 _26750 _18662 h).
Proof. exact (eq_refl (term251 _26750 _18662 h)). Qed.
Lemma lem1135107 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18662 : _26750) : (term219 _26750 h P Q _18662) = (term252 _26750 h Q P _18662).
Proof. exact (MK_COMB (@lem1135106 _26750 _18662 h) (@lem1135100 _26750 Q P _18662)). Qed.
Lemma lem1135111 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1135112 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term252 _26750 h Q P _18662) = (term253 _26750 Q h P _18662).
Proof. exact (@lem1135111 (@I (_26750 -> Prop) Q _18662) (term206 _26750 _18662 h) (term185 _26750 P _18662)). Qed.
Lemma lem1135130 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term219 _26750 h P Q _18662) = (term253 _26750 Q h P _18662).
Proof. exact (TRANS (@lem1135107 _26750 h Q P _18662) (@lem1135112 _26750 Q h P _18662)). Qed.
Lemma lem1135131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1135132 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term254 _26750 h P Q _18662) = (term255 _26750 Q h P _18662).
Proof. exact (MK_COMB (@lem1135131) (@lem1135130 _26750 Q h P _18662)). Qed.
Lemma lem1135150 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term253 _26750 Q h P _18662) = (term253 _26750 Q h P _18662).
Proof. exact (eq_refl (term253 _26750 Q h P _18662)). Qed.
Lemma lem1135151 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : ((term219 _26750 h P Q _18662) = (term253 _26750 Q h P _18662)) = ((term253 _26750 Q h P _18662) = (term253 _26750 Q h P _18662)).
Proof. exact (MK_COMB (@lem1135132 _26750 Q h P _18662) (@lem1135150 _26750 Q h P _18662)). Qed.
Lemma lem1135153 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1135154 (x : Prop) : (x = x) = True.
Proof. exact (@lem1135153 Prop x). Qed.
Lemma lem1135155 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : ((term253 _26750 Q h P _18662) = (term253 _26750 Q h P _18662)) = True.
Proof. exact (@lem1135154 (term253 _26750 Q h P _18662)). Qed.
Lemma lem1135156 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : ((term219 _26750 h P Q _18662) = (term253 _26750 Q h P _18662)) = True.
Proof. exact (TRANS (@lem1135151 _26750 Q h P _18662) (@lem1135155 _26750 Q h P _18662)). Qed.
Lemma lem1135157 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : True = ((term219 _26750 h P Q _18662) = (term253 _26750 Q h P _18662)).
Proof. exact (SYM (@lem1135156 _26750 Q h P _18662)). Qed.
Lemma lem1135158 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term219 _26750 h P Q _18662) = (term253 _26750 Q h P _18662).
Proof. exact (EQ_MP (@lem1135157 _26750 Q h P _18662) (@lem0)). Qed.
Lemma lem1135159 {_26750 : Type'} (_18662 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term253 _26750 Q h P _18662.
Proof. exact (EQ_MP (@lem1135158 _26750 Q h P _18662) (@lem1134636 _26750 _18662 Q h P t h1)). Qed.
Lemma lem1135161 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1135162 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18662 : _26750) : (term253 _26750 Q h P _18662) = (term256 _26750 h P Q _18662).
Proof. exact (@lem1135161 (term211 _26750 h P _18662) (@I (_26750 -> Prop) Q _18662)). Qed.
Lemma lem1135164 (a : Prop) (b : Prop) : (term235 a b) = (term236 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1135165 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term257 _26750 h P _18662) = (term258 _26750 h P _18662).
Proof. exact (@lem1135164 (term206 _26750 _18662 h) (term185 _26750 P _18662)). Qed.
Lemma lem1135167 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1135168 {_26750 : Type'} (_18662 : _26750) (h : _26750) : (term259 _26750 _18662 h) = (_18662 = h).
Proof. exact (@lem1135167 (_18662 = h)). Qed.
Lemma lem1135169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1135170 {_26750 : Type'} (_18662 : _26750) (h : _26750) : (term260 _26750 _18662 h) = (term261 _26750 _18662 h).
Proof. exact (MK_COMB (@lem1135169) (@lem1135168 _26750 _18662 h)). Qed.
Lemma lem1135172 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1135173 {_26750 : Type'} (P : _26750 -> Prop) (_18662 : _26750) : (term241 _26750 P _18662) = (@I (_26750 -> Prop) P _18662).
Proof. exact (@lem1135172 (@I (_26750 -> Prop) P _18662)). Qed.
Lemma lem1135174 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term258 _26750 h P _18662) = (term262 _26750 h P _18662).
Proof. exact (MK_COMB (@lem1135170 _26750 _18662 h) (@lem1135173 _26750 P _18662)). Qed.
Lemma lem1135175 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term257 _26750 h P _18662) = (term262 _26750 h P _18662).
Proof. exact (TRANS (@lem1135165 _26750 h P _18662) (@lem1135174 _26750 h P _18662)). Qed.
Lemma lem1135176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1135177 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (_18662 : _26750) : (term263 _26750 h P _18662) = (term264 _26750 h P _18662).
Proof. exact (MK_COMB (@lem1135176) (@lem1135175 _26750 h P _18662)). Qed.
Lemma lem1135178 {_26750 : Type'} (Q : _26750 -> Prop) (_18662 : _26750) : (@I (_26750 -> Prop) Q _18662) = (@I (_26750 -> Prop) Q _18662).
Proof. exact (eq_refl (@I (_26750 -> Prop) Q _18662)). Qed.
Lemma lem1135179 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18662 : _26750) : (term256 _26750 h P Q _18662) = (term265 _26750 h P Q _18662).
Proof. exact (MK_COMB (@lem1135177 _26750 h P _18662) (@lem1135178 _26750 Q _18662)). Qed.
Lemma lem1135180 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18662 : _26750) : (term253 _26750 Q h P _18662) = (term265 _26750 h P Q _18662).
Proof. exact (TRANS (@lem1135162 _26750 h P Q _18662) (@lem1135179 _26750 h P Q _18662)). Qed.
Lemma lem1135182 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (h1 : @I (_26750 -> Prop) P h) : term266 _26750 P h.
Proof. exact (conj (@lem1135074 _26750 h) (@lem1135081 _26750 P h h1)). Qed.
Lemma lem1135184 {_26750 : Type'} (_18662 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term265 _26750 h P Q _18662.
Proof. exact (EQ_MP (@lem1135180 _26750 h P Q _18662) (@lem1135159 _26750 _18662 Q h P t h1)). Qed.
Lemma lem1135185 {_26750 : Type'} (_18662 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term265 _26750 h P Q _18662.
Proof. exact (@lem1135184 _26750 _18662 Q h P t h1). Qed.
Lemma lem1135186 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term267 _26750 P Q h.
Proof. exact (@lem1135185 _26750 h Q h P t h1). Qed.
Lemma lem1135189 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term71 _26750 Q h P t) (h2 : @I (_26750 -> Prop) P h) : @I (_26750 -> Prop) Q h.
Proof. exact (@lem1135186 _26750 Q h P t h1 (@lem1135182 _26750 P h h2)). Qed.
Lemma lem1135190 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term71 _26750 Q h P t) (h2 : @I (_26750 -> Prop) P h) : term222 _26750 Q h.
Proof. exact (fun h0 : term185 _26750 Q h => @lem1135189 _26750 Q t P h h1 h2). Qed.
Lemma lem1135192 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135193 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) : (term222 _26750 Q h) = (@I (_26750 -> Prop) Q h).
Proof. exact (@lem1135192 (@I (_26750 -> Prop) Q h)). Qed.
Lemma lem1135194 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term71 _26750 Q h P t) (h2 : @I (_26750 -> Prop) P h) : @I (_26750 -> Prop) Q h.
Proof. exact (EQ_MP (@lem1135193 _26750 Q h) (@lem1135190 _26750 Q t P h h1 h2)). Qed.
Lemma lem1135197 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1135199 {_26750 : Type'} (Q : _26750 -> Prop) (h : _26750) : (term185 _26750 Q h) = (term245 _26750 Q h).
Proof. exact (@lem1135197 (@I (_26750 -> Prop) Q h)). Qed.
Lemma lem1135202 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term245 _26750 Q h.
Proof. exact (EQ_MP (@lem1135199 _26750 Q h) (@lem1134618 _26750 h Q t h1)). Qed.
Lemma lem1135205 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : False.
Proof. exact (@lem1135202 _26750 h Q t h1 (@lem1135194 _26750 Q t P h h2 h3)). Qed.
Lemma lem1135206 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : term246.
Proof. exact (fun h0 : ~ False => @lem1135205 _26750 Q t P h h1 h2 h3). Qed.
Lemma lem1135208 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135209 : term246 = False.
Proof. exact (@lem1135208 False). Qed.
Lemma lem1135210 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1135209) (@lem1135206 _26750 Q t P h h1 h2 h3)). Qed.
Lemma lem1135275 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (h1). Qed.
Lemma lem1135276 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : term268 _26750 Q t.
Proof. exact (fun h0 : term121 _26750 Q t => @lem1135275 _26750 Q t h1). Qed.
Lemma lem1135278 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135279 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term268 _26750 Q t) = (@EX _26750 Q t).
Proof. exact (@lem1135278 (@EX _26750 Q t)). Qed.
Lemma lem1135280 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (EQ_MP (@lem1135279 _26750 Q t) (@lem1135276 _26750 Q t h1)). Qed.
Lemma lem1135283 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1135285 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term121 _26750 Q t) = (term269 _26750 Q t).
Proof. exact (@lem1135283 (@EX _26750 Q t)). Qed.
Lemma lem1135288 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term269 _26750 Q t.
Proof. exact (EQ_MP (@lem1135285 _26750 Q t) (@lem1134652 _26750 h Q t h1)). Qed.
Lemma lem1135291 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (@lem1135288 _26750 h Q t h1 (@lem1135280 _26750 Q t h2)). Qed.
Lemma lem1135292 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : term246.
Proof. exact (fun h0 : ~ False => @lem1135291 _26750 h Q t h1 h2). Qed.
Lemma lem1135294 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135295 : term246 = False.
Proof. exact (@lem1135294 False). Qed.
Lemma lem1135296 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135295) (@lem1135292 _26750 h Q t h1 h2)). Qed.
Lemma lem1135361 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @List.In _26750 x t.
Proof. exact (proj1 (@lem1134226 _26750 t P Q x h1)). Qed.
Lemma lem1135362 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term220 _26750 x t.
Proof. exact (fun h0 : term207 _26750 x t => @lem1135361 _26750 t P Q x h1). Qed.
Lemma lem1135364 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135365 {_26750 : Type'} (x : _26750) (t : list _26750) : (term220 _26750 x t) = (@List.In _26750 x t).
Proof. exact (@lem1135364 (@List.In _26750 x t)). Qed.
Lemma lem1135366 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @List.In _26750 x t.
Proof. exact (EQ_MP (@lem1135365 _26750 x t) (@lem1135362 _26750 t P Q x h1)). Qed.
Lemma lem1135368 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @I (_26750 -> Prop) P x.
Proof. exact (proj2 (@lem1134226 _26750 t P Q x h1)). Qed.
Lemma lem1135369 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term222 _26750 P x.
Proof. exact (fun h0 : term185 _26750 P x => @lem1135368 _26750 t P Q x h1). Qed.
Lemma lem1135371 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135372 {_26750 : Type'} (P : _26750 -> Prop) (x : _26750) : (term222 _26750 P x) = (@I (_26750 -> Prop) P x).
Proof. exact (@lem1135371 (@I (_26750 -> Prop) P x)). Qed.
Lemma lem1135373 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : @I (_26750 -> Prop) P x.
Proof. exact (EQ_MP (@lem1135372 _26750 P x) (@lem1135369 _26750 t P Q x h1)). Qed.
Lemma lem1135379 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1135380 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (Q : _26750 -> Prop) (_18664 : _26750) : (term218 _26750 t P Q _18664) = (term223 _26750 P t Q _18664).
Proof. exact (@lem1135379 (term185 _26750 P _18664) (term207 _26750 _18664 t) (@I (_26750 -> Prop) Q _18664)). Qed.
Lemma lem1135394 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1135395 {_26750 : Type'} (Q : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term224 _26750 t Q _18664) = (term225 _26750 Q _18664 t).
Proof. exact (@lem1135394 (@I (_26750 -> Prop) Q _18664) (term207 _26750 _18664 t)). Qed.
Lemma lem1135401 {_26750 : Type'} (P : _26750 -> Prop) (_18664 : _26750) : (term226 _26750 P _18664) = (term226 _26750 P _18664).
Proof. exact (eq_refl (term226 _26750 P _18664)). Qed.
Lemma lem1135402 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term223 _26750 P t Q _18664) = (term227 _26750 P Q _18664 t).
Proof. exact (MK_COMB (@lem1135401 _26750 P _18664) (@lem1135395 _26750 Q _18664 t)). Qed.
Lemma lem1135406 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1135407 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term227 _26750 P Q _18664 t) = (term228 _26750 Q P _18664 t).
Proof. exact (@lem1135406 (@I (_26750 -> Prop) Q _18664) (term185 _26750 P _18664) (term207 _26750 _18664 t)). Qed.
Lemma lem1135423 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term223 _26750 P t Q _18664) = (term228 _26750 Q P _18664 t).
Proof. exact (TRANS (@lem1135402 _26750 P Q _18664 t) (@lem1135407 _26750 Q P _18664 t)). Qed.
Lemma lem1135424 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term218 _26750 t P Q _18664) = (term228 _26750 Q P _18664 t).
Proof. exact (TRANS (@lem1135380 _26750 P t Q _18664) (@lem1135423 _26750 Q P _18664 t)). Qed.
Lemma lem1135425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1135426 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term229 _26750 t P Q _18664) = (term230 _26750 Q P _18664 t).
Proof. exact (MK_COMB (@lem1135425) (@lem1135424 _26750 Q P _18664 t)). Qed.
Lemma lem1135440 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1135441 {_26750 : Type'} (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term212 _26750 t P _18664) = (term231 _26750 P _18664 t).
Proof. exact (@lem1135440 (term185 _26750 P _18664) (term207 _26750 _18664 t)). Qed.
Lemma lem1135447 {_26750 : Type'} (Q : _26750 -> Prop) (_18664 : _26750) : (term183 _26750 Q _18664) = (term183 _26750 Q _18664).
Proof. exact (eq_refl (term183 _26750 Q _18664)). Qed.
Lemma lem1135448 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : (term232 _26750 Q t P _18664) = (term228 _26750 Q P _18664 t).
Proof. exact (MK_COMB (@lem1135447 _26750 Q _18664) (@lem1135441 _26750 P _18664 t)). Qed.
Lemma lem1135459 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : ((term218 _26750 t P Q _18664) = (term232 _26750 Q t P _18664)) = ((term228 _26750 Q P _18664 t) = (term228 _26750 Q P _18664 t)).
Proof. exact (MK_COMB (@lem1135426 _26750 Q P _18664 t) (@lem1135448 _26750 Q P _18664 t)). Qed.
Lemma lem1135461 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1135462 (x : Prop) : (x = x) = True.
Proof. exact (@lem1135461 Prop x). Qed.
Lemma lem1135463 {_26750 : Type'} (Q : _26750 -> Prop) (P : _26750 -> Prop) (_18664 : _26750) (t : list _26750) : ((term228 _26750 Q P _18664 t) = (term228 _26750 Q P _18664 t)) = True.
Proof. exact (@lem1135462 (term228 _26750 Q P _18664 t)). Qed.
Lemma lem1135464 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (_18664 : _26750) : ((term218 _26750 t P Q _18664) = (term232 _26750 Q t P _18664)) = True.
Proof. exact (TRANS (@lem1135459 _26750 Q P _18664 t) (@lem1135463 _26750 Q P _18664 t)). Qed.
Lemma lem1135465 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (_18664 : _26750) : True = ((term218 _26750 t P Q _18664) = (term232 _26750 Q t P _18664)).
Proof. exact (SYM (@lem1135464 _26750 Q t P _18664)). Qed.
Lemma lem1135466 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (_18664 : _26750) : (term218 _26750 t P Q _18664) = (term232 _26750 Q t P _18664).
Proof. exact (EQ_MP (@lem1135465 _26750 Q t P _18664) (@lem0)). Qed.
Lemma lem1135467 {_26750 : Type'} (_18664 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term232 _26750 Q t P _18664.
Proof. exact (EQ_MP (@lem1135466 _26750 Q t P _18664) (@lem1134716 _26750 _18664 Q h P t h1)). Qed.
Lemma lem1135469 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1135470 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18664 : _26750) : (term232 _26750 Q t P _18664) = (term234 _26750 t P Q _18664).
Proof. exact (@lem1135469 (term212 _26750 t P _18664) (@I (_26750 -> Prop) Q _18664)). Qed.
Lemma lem1135472 (a : Prop) (b : Prop) : (term235 a b) = (term236 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1135473 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18664 : _26750) : (term237 _26750 t P _18664) = (term238 _26750 t P _18664).
Proof. exact (@lem1135472 (term207 _26750 _18664 t) (term185 _26750 P _18664)). Qed.
Lemma lem1135475 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1135476 {_26750 : Type'} (_18664 : _26750) (t : list _26750) : (term239 _26750 _18664 t) = (@List.In _26750 _18664 t).
Proof. exact (@lem1135475 (@List.In _26750 _18664 t)). Qed.
Lemma lem1135477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1135478 {_26750 : Type'} (_18664 : _26750) (t : list _26750) : (term240 _26750 _18664 t) = (term196 _26750 _18664 t).
Proof. exact (MK_COMB (@lem1135477) (@lem1135476 _26750 _18664 t)). Qed.
Lemma lem1135480 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1135481 {_26750 : Type'} (P : _26750 -> Prop) (_18664 : _26750) : (term241 _26750 P _18664) = (@I (_26750 -> Prop) P _18664).
Proof. exact (@lem1135480 (@I (_26750 -> Prop) P _18664)). Qed.
Lemma lem1135482 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18664 : _26750) : (term238 _26750 t P _18664) = (term197 _26750 t P _18664).
Proof. exact (MK_COMB (@lem1135478 _26750 _18664 t) (@lem1135481 _26750 P _18664)). Qed.
Lemma lem1135483 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18664 : _26750) : (term237 _26750 t P _18664) = (term197 _26750 t P _18664).
Proof. exact (TRANS (@lem1135473 _26750 t P _18664) (@lem1135482 _26750 t P _18664)). Qed.
Lemma lem1135484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1135485 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (_18664 : _26750) : (term242 _26750 t P _18664) = (term243 _26750 t P _18664).
Proof. exact (MK_COMB (@lem1135484) (@lem1135483 _26750 t P _18664)). Qed.
Lemma lem1135486 {_26750 : Type'} (Q : _26750 -> Prop) (_18664 : _26750) : (@I (_26750 -> Prop) Q _18664) = (@I (_26750 -> Prop) Q _18664).
Proof. exact (eq_refl (@I (_26750 -> Prop) Q _18664)). Qed.
Lemma lem1135487 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18664 : _26750) : (term234 _26750 t P Q _18664) = (term244 _26750 t P Q _18664).
Proof. exact (MK_COMB (@lem1135485 _26750 t P _18664) (@lem1135486 _26750 Q _18664)). Qed.
Lemma lem1135488 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (_18664 : _26750) : (term232 _26750 Q t P _18664) = (term244 _26750 t P Q _18664).
Proof. exact (TRANS (@lem1135470 _26750 t P Q _18664) (@lem1135487 _26750 t P Q _18664)). Qed.
Lemma lem1135490 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term197 _26750 t P x.
Proof. exact (conj (@lem1135366 _26750 t P Q x h1) (@lem1135373 _26750 t P Q x h1)). Qed.
Lemma lem1135492 {_26750 : Type'} (_18664 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term244 _26750 t P Q _18664.
Proof. exact (EQ_MP (@lem1135488 _26750 t P Q _18664) (@lem1135467 _26750 _18664 Q h P t h1)). Qed.
Lemma lem1135493 {_26750 : Type'} (_18664 : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term244 _26750 t P Q _18664.
Proof. exact (@lem1135492 _26750 _18664 Q h P t h1). Qed.
Lemma lem1135494 {_26750 : Type'} (x : _26750) (Q : _26750 -> Prop) (h : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) : term244 _26750 t P Q x.
Proof. exact (@lem1135493 _26750 x Q h P t h1). Qed.
Lemma lem1135497 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : @I (_26750 -> Prop) Q x.
Proof. exact (@lem1135494 _26750 x Q h P t h1 (@lem1135490 _26750 t P Q x h2)). Qed.
Lemma lem1135498 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : term222 _26750 Q x.
Proof. exact (fun h0 : term185 _26750 Q x => @lem1135497 _26750 h t P Q x h1 h2). Qed.
Lemma lem1135500 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135501 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (term222 _26750 Q x) = (@I (_26750 -> Prop) Q x).
Proof. exact (@lem1135500 (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1135502 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : @I (_26750 -> Prop) Q x.
Proof. exact (EQ_MP (@lem1135501 _26750 Q x) (@lem1135498 _26750 h t P Q x h1 h2)). Qed.
Lemma lem1135505 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1135507 {_26750 : Type'} (Q : _26750 -> Prop) (x : _26750) : (term185 _26750 Q x) = (term245 _26750 Q x).
Proof. exact (@lem1135505 (@I (_26750 -> Prop) Q x)). Qed.
Lemma lem1135510 {_26750 : Type'} (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term200 _26750 t P Q x) : term245 _26750 Q x.
Proof. exact (EQ_MP (@lem1135507 _26750 Q x) (@lem1134688 _26750 t P Q x h1)). Qed.
Lemma lem1135513 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : False.
Proof. exact (@lem1135510 _26750 t P Q x h2 (@lem1135502 _26750 h t P Q x h1 h2)). Qed.
Lemma lem1135514 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : term246.
Proof. exact (fun h0 : ~ False => @lem1135513 _26750 h t P Q x h1 h2). Qed.
Lemma lem1135516 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135517 : term246 = False.
Proof. exact (@lem1135516 False). Qed.
Lemma lem1135518 {_26750 : Type'} (h : _26750) (t : list _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (x : _26750) (h1 : term71 _26750 Q h P t) (h2 : term200 _26750 t P Q x) : False.
Proof. exact (EQ_MP (@lem1135517) (@lem1135514 _26750 h t P Q x h1 h2)). Qed.
Lemma lem1135583 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 P t) : @EX _26750 P t.
Proof. exact (h1). Qed.
Lemma lem1135584 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 P t) : term268 _26750 P t.
Proof. exact (fun h0 : term121 _26750 P t => @lem1135583 _26750 P t h1). Qed.
Lemma lem1135586 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135587 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (term268 _26750 P t) = (@EX _26750 P t).
Proof. exact (@lem1135586 (@EX _26750 P t)). Qed.
Lemma lem1135588 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 P t) : @EX _26750 P t.
Proof. exact (EQ_MP (@lem1135587 _26750 P t) (@lem1135584 _26750 P t h1)). Qed.
Lemma lem1135591 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1135593 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) : (term121 _26750 P t) = (term269 _26750 P t).
Proof. exact (@lem1135591 (@EX _26750 P t)). Qed.
Lemma lem1135596 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) : term269 _26750 P t.
Proof. exact (EQ_MP (@lem1135593 _26750 P t) (@lem1134724 _26750 P t h1)). Qed.
Lemma lem1135599 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (@lem1135596 _26750 P t h1 (@lem1135588 _26750 P t h2)). Qed.
Lemma lem1135600 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : term246.
Proof. exact (fun h0 : ~ False => @lem1135599 _26750 P t h1 h2). Qed.
Lemma lem1135602 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135603 : term246 = False.
Proof. exact (@lem1135602 False). Qed.
Lemma lem1135604 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (EQ_MP (@lem1135603) (@lem1135600 _26750 P t h1 h2)). Qed.
Lemma lem1135669 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (h1). Qed.
Lemma lem1135670 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : term268 _26750 Q t.
Proof. exact (fun h0 : term121 _26750 Q t => @lem1135669 _26750 Q t h1). Qed.
Lemma lem1135672 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135673 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term268 _26750 Q t) = (@EX _26750 Q t).
Proof. exact (@lem1135672 (@EX _26750 Q t)). Qed.
Lemma lem1135674 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h1 : @EX _26750 Q t) : @EX _26750 Q t.
Proof. exact (EQ_MP (@lem1135673 _26750 Q t) (@lem1135670 _26750 Q t h1)). Qed.
Lemma lem1135677 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1135679 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term121 _26750 Q t) = (term269 _26750 Q t).
Proof. exact (@lem1135677 (@EX _26750 Q t)). Qed.
Lemma lem1135682 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) : term269 _26750 Q t.
Proof. exact (EQ_MP (@lem1135679 _26750 Q t) (@lem1134752 _26750 h Q t h1)). Qed.
Lemma lem1135685 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (@lem1135682 _26750 h Q t h1 (@lem1135674 _26750 Q t h2)). Qed.
Lemma lem1135686 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : term246.
Proof. exact (fun h0 : ~ False => @lem1135685 _26750 h Q t h1 h2). Qed.
Lemma lem1135688 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1135689 : term246 = False.
Proof. exact (@lem1135688 False). Qed.
Lemma lem1135690 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135689) (@lem1135686 _26750 h Q t h1 h2)). Qed.
Lemma lem1135691 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : (@EX _26750 Q t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 Q t => @lem1135690 _26750 h Q t h1 h2) (fun h3 : False => @lem1134756 _26750 Q t h2)). Qed.
Lemma lem1135692 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135691 _26750 h Q t h1 h2) (@lem1134756 _26750 Q t h2)). Qed.
Lemma lem1135693 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : (term121 _26750 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26750 P t => @lem1135604 _26750 P t h1 h2) (fun h3 : False => @lem1134724 _26750 P t h1)). Qed.
Lemma lem1135694 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (EQ_MP (@lem1135693 _26750 P t h1 h2) (@lem1134724 _26750 P t h1)). Qed.
Lemma lem1135695 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : (@EX _26750 P t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 P t => @lem1135694 _26750 P t h1 h2) (fun h3 : False => @lem1134722 _26750 P t h2)). Qed.
Lemma lem1135696 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (EQ_MP (@lem1135695 _26750 P t h1 h2) (@lem1134722 _26750 P t h2)). Qed.
Lemma lem1135697 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : (@EX _26750 Q t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 Q t => @lem1135296 _26750 h Q t h1 h2) (fun h3 : False => @lem1134656 _26750 Q t h2)). Qed.
Lemma lem1135698 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135697 _26750 h Q t h1 h2) (@lem1134656 _26750 Q t h2)). Qed.
Lemma lem1135699 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : (@I (_26750 -> Prop) P h) = False.
Proof. exact (prop_ext (fun h4 : @I (_26750 -> Prop) P h => @lem1135210 _26750 Q t P h h1 h2 h3) (fun h4 : False => @lem1134622 _26750 P h h3)). Qed.
Lemma lem1135700 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1135699 _26750 Q t P h h1 h2 h3) (@lem1134622 _26750 P h h3)). Qed.
Lemma lem1135701 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : (@EX _26750 Q t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 Q t => @lem1135692 _26750 h Q t h1 h2) (fun h3 : False => @lem1134550 _26750 Q t h2)). Qed.
Lemma lem1135702 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135701 _26750 h Q t h1 h2) (@lem1134550 _26750 Q t h2)). Qed.
Lemma lem1135703 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : (term121 _26750 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26750 P t => @lem1135696 _26750 P t h1 h2) (fun h3 : False => @lem1134499 _26750 P t h1)). Qed.
Lemma lem1135704 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (EQ_MP (@lem1135703 _26750 P t h1 h2) (@lem1134499 _26750 P t h1)). Qed.
Lemma lem1135705 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : (@EX _26750 P t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 P t => @lem1135704 _26750 P t h1 h2) (fun h3 : False => @lem1134495 _26750 P t h2)). Qed.
Lemma lem1135706 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (EQ_MP (@lem1135705 _26750 P t h1 h2) (@lem1134495 _26750 P t h2)). Qed.
Lemma lem1135707 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : (@EX _26750 Q t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 Q t => @lem1135698 _26750 h Q t h1 h2) (fun h3 : False => @lem1134389 _26750 Q t h2)). Qed.
Lemma lem1135708 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135707 _26750 h Q t h1 h2) (@lem1134389 _26750 Q t h2)). Qed.
Lemma lem1135709 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : (@I (_26750 -> Prop) P h) = False.
Proof. exact (prop_ext (fun h4 : @I (_26750 -> Prop) P h => @lem1135700 _26750 Q t P h h1 h2 h3) (fun h4 : False => @lem1134334 _26750 P h h3)). Qed.
Lemma lem1135710 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1135709 _26750 Q t P h h1 h2 h3) (@lem1134334 _26750 P h h3)). Qed.
Lemma lem1135711 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : (@EX _26750 Q t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 Q t => @lem1135702 _26750 h Q t h1 h2) (fun h3 : False => @lem1134550 _26750 Q t h2)). Qed.
Lemma lem1135712 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135711 _26750 h Q t h1 h2) (@lem1134550 _26750 Q t h2)). Qed.
Lemma lem1135713 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : (term121 _26750 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26750 P t => @lem1135706 _26750 P t h1 h2) (fun h3 : False => @lem1134499 _26750 P t h1)). Qed.
Lemma lem1135714 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (EQ_MP (@lem1135713 _26750 P t h1 h2) (@lem1134499 _26750 P t h1)). Qed.
Lemma lem1135715 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : (@EX _26750 P t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 P t => @lem1135714 _26750 P t h1 h2) (fun h3 : False => @lem1134495 _26750 P t h2)). Qed.
Lemma lem1135716 {_26750 : Type'} (P : _26750 -> Prop) (t : list _26750) (h1 : term121 _26750 P t) (h2 : @EX _26750 P t) : False.
Proof. exact (EQ_MP (@lem1135715 _26750 P t h1 h2) (@lem1134495 _26750 P t h2)). Qed.
Lemma lem1135717 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : (@EX _26750 Q t) = False.
Proof. exact (prop_ext (fun h3 : @EX _26750 Q t => @lem1135708 _26750 h Q t h1 h2) (fun h3 : False => @lem1134389 _26750 Q t h2)). Qed.
Lemma lem1135718 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : @EX _26750 Q t) : False.
Proof. exact (EQ_MP (@lem1135717 _26750 h Q t h1 h2) (@lem1134389 _26750 Q t h2)). Qed.
Lemma lem1135719 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : (@I (_26750 -> Prop) P h) = False.
Proof. exact (prop_ext (fun h4 : @I (_26750 -> Prop) P h => @lem1135710 _26750 Q t P h h1 h2 h3) (fun h4 : False => @lem1134334 _26750 P h h3)). Qed.
Lemma lem1135720 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) (h : _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1135719 _26750 Q t P h h1 h2 h3) (@lem1134334 _26750 P h h3)). Qed.
Lemma lem1135721 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) (h2 : @EX _26750 P t) (h3 : term202 _26750 Q x P t) : False.
Proof. exact (or_elim (@lem1134221 _26750 Q x P t h3) (fun h0 : term200 _26750 t P Q x => @lem1135518 _26750 h t P Q x h1 h0) (fun h0 : term121 _26750 P t => @lem1135716 _26750 P t h0 h2)). Qed.
Lemma lem1135722 {_26750 : Type'} (h : _26750) (x : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @EX _26750 P t) (h4 : term161 _26750 x P Q t) : False.
Proof. exact (or_elim (@lem1134206 _26750 x P Q t h4) (fun h0 : term202 _26750 Q x P t => @lem1135721 _26750 h Q x P t h2 h3 h0) (fun h0 : @EX _26750 Q t => @lem1135712 _26750 h Q t h1 h0)). Qed.
Lemma lem1135723 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (x : _26750) (P : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) (h4 : term202 _26750 Q x P t) : False.
Proof. exact (or_elim (@lem1134213 _26750 Q x P t h4) (fun h0 : term200 _26750 t P Q x => @lem1135002 _26750 h t P Q x h2 h0) (fun h0 : term121 _26750 P t => @lem1135720 _26750 Q t P h h1 h2 h3)). Qed.
Lemma lem1135724 {_26750 : Type'} (h : _26750) (x : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : @I (_26750 -> Prop) P h) (h4 : term161 _26750 x P Q t) : False.
Proof. exact (or_elim (@lem1134206 _26750 x P Q t h4) (fun h0 : term202 _26750 Q x P t => @lem1135723 _26750 h Q x P t h1 h2 h3 h0) (fun h0 : @EX _26750 Q t => @lem1135718 _26750 h Q t h1 h0)). Qed.
Lemma lem1135725 {_26750 : Type'} (h : _26750) (x : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : term161 _26750 x P Q t) : False.
Proof. exact (or_elim (@lem1134209 _26750 Q h P t h2) (fun h0 : @I (_26750 -> Prop) P h => @lem1135724 _26750 h x P Q t h1 h2 h0 h3) (fun h0 : @EX _26750 P t => @lem1135722 _26750 h x P Q t h1 h2 h0 h3)). Qed.
Lemma lem1135726 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : term15 _26750 P Q t) : False.
Proof. exact (ex_elim (@lem1133993 _26750 P Q t h3) (fun x : _26750 => fun h0 : term163 _26750 P Q t x => @lem1135725 _26750 h x P Q t h1 h2 h0)). Qed.
Lemma lem1135727 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : term15 _26750 P Q t) : (term108 _26750 h Q t) = False.
Proof. exact (prop_ext (fun h4 : term108 _26750 h Q t => @lem1135726 _26750 h P Q t h1 h2 h3) (fun h4 : False => @lem1133855 _26750 h Q t h1)). Qed.
Lemma lem1135728 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term108 _26750 h Q t) (h2 : term71 _26750 Q h P t) (h3 : term15 _26750 P Q t) : False.
Proof. exact (EQ_MP (@lem1135727 _26750 h P Q t h1 h2 h3) (@lem1133855 _26750 h Q t h1)). Qed.
Lemma lem1135729 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) (h2 : term15 _26750 P Q t) : term107 _26750 h Q t.
Proof. exact (fun h0 : term108 _26750 h Q t => @lem1135728 _26750 h P Q t h0 h1 h2). Qed.
Lemma lem1135730 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term71 _26750 Q h P t) (h2 : term15 _26750 P Q t) : term69 _26750 h Q t.
Proof. exact (EQ_MP (@lem1133854 _26750 h Q t) (@lem1135729 _26750 h P Q t h1 h2)). Qed.
Lemma lem1135731 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term74 _26750 P h Q t.
Proof. exact (fun h0 : term71 _26750 Q h P t => @lem1135730 _26750 h P Q t h0 h1). Qed.
Lemma lem1135732 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term84 _26750 P h Q t.
Proof. exact (fun h0 : term15 _26750 P Q t => @lem1135731 _26750 h P Q t h0). Qed.
Lemma lem1135737 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term88 _26750 h Q t.
Proof. exact (fun P : _26750 -> Prop => @lem1135732 _26750 P h Q t). Qed.
Lemma lem1135742 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : term92 _26750 Q t.
Proof. exact (fun h : _26750 => @lem1135737 _26750 h Q t). Qed.
Lemma lem1135747 {_26750 : Type'} (t : list _26750) : term96 _26750 t.
Proof. exact (fun Q : _26750 -> Prop => @lem1135742 _26750 Q t). Qed.
Lemma lem1135752 {_26750 : Type'} : term100 _26750.
Proof. exact (fun t : list _26750 => @lem1135747 _26750 t). Qed.
Lemma lem1135753 {_26750 : Type'} : term99 _26750.
Proof. exact (EQ_MP (@lem1133848 _26750) (@lem1135752 _26750)). Qed.
Lemma lem1135754 {_26750 : Type'} (t : list _26750) : term270 _26750 t.
Proof. exact (@lem1135753 _26750 t). Qed.
Lemma lem1135755 {_26750 : Type'} (t : list _26750) : (term270 _26750 t) = (term95 _26750 t).
Proof. exact (eq_refl (term270 _26750 t)). Qed.
Lemma lem1135756 {_26750 : Type'} (t : list _26750) : term95 _26750 t.
Proof. exact (EQ_MP (@lem1135755 _26750 t) (@lem1135754 _26750 t)). Qed.
Lemma lem1135757 {_26750 : Type'} (t : list _26750) (Q : _26750 -> Prop) : term271 _26750 t Q.
Proof. exact (@lem1135756 _26750 t Q). Qed.
Lemma lem1135758 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : (term271 _26750 t Q) = (term91 _26750 Q t).
Proof. exact (eq_refl (term271 _26750 t Q)). Qed.
Lemma lem1135759 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) : term91 _26750 Q t.
Proof. exact (EQ_MP (@lem1135758 _26750 Q t) (@lem1135757 _26750 t Q)). Qed.
Lemma lem1135760 {_26750 : Type'} (Q : _26750 -> Prop) (t : list _26750) (h : _26750) : term272 _26750 Q t h.
Proof. exact (@lem1135759 _26750 Q t h). Qed.
Lemma lem1135761 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term272 _26750 Q t h) = (term87 _26750 h Q t).
Proof. exact (eq_refl (term272 _26750 Q t h)). Qed.
Lemma lem1135762 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term87 _26750 h Q t.
Proof. exact (EQ_MP (@lem1135761 _26750 h Q t) (@lem1135760 _26750 Q t h)). Qed.
Lemma lem1135763 {_26750 : Type'} (h : _26750) (Q : _26750 -> Prop) (t : list _26750) (P : _26750 -> Prop) : term273 _26750 h Q t P.
Proof. exact (@lem1135762 _26750 h Q t P). Qed.
Lemma lem1135764 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : (term273 _26750 h Q t P) = (term78 _26750 P h Q t).
Proof. exact (eq_refl (term273 _26750 h Q t P)). Qed.
Lemma lem1135765 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term78 _26750 P h Q t.
Proof. exact (EQ_MP (@lem1135764 _26750 P h Q t) (@lem1135763 _26750 h Q t P)). Qed.
Lemma lem1135767 {_26750 : Type'} (P : _26750 -> Prop) (h : _26750) (Q : _26750 -> Prop) (t : list _26750) : term78 _26750 P h Q t.
Proof. exact (@lem1133626 _26750 P h Q t (@lem1135765 _26750 P h Q t)). Qed.
Lemma lem1135768 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term76 _26750 P h Q t.
Proof. exact (@lem1135767 _26750 P h Q t (@lem1133483 _26750 P Q t h1)). Qed.
Lemma lem1135769 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term77 _26750 P h Q t) (h2 : term15 _26750 P Q t) : False.
Proof. exact (@lem1135768 _26750 h P Q t h2 (@lem1133610 _26750 P h Q t h1)). Qed.
Lemma lem1135770 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term77 _26750 P h Q t) (h2 : term15 _26750 P Q t) : (term77 _26750 P h Q t) = False.
Proof. exact (prop_ext (fun h3 : term77 _26750 P h Q t => @lem1135769 _26750 h P Q t h1 h2) (fun h3 : False => @lem1133610 _26750 P h Q t h1)). Qed.
Lemma lem1135771 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term77 _26750 P h Q t) (h2 : term15 _26750 P Q t) : False.
Proof. exact (EQ_MP (@lem1135770 _26750 h P Q t h1 h2) (@lem1133610 _26750 P h Q t h1)). Qed.
Lemma lem1135772 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term76 _26750 P h Q t.
Proof. exact (fun h0 : term77 _26750 P h Q t => @lem1135771 _26750 h P Q t h0 h1). Qed.
Lemma lem1135773 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term74 _26750 P h Q t.
Proof. exact (EQ_MP (@lem1133609 _26750 P h Q t) (@lem1135772 _26750 h P Q t h1)). Qed.
Lemma lem1135774 {_26750 : Type'} (h : _26750) (P : _26750 -> Prop) (Q : _26750 -> Prop) (t : list _26750) (h1 : term15 _26750 P Q t) : term19 _26750 P Q h t.
Proof. exact (EQ_MP (@lem1133605 _26750 P Q h t) (@lem1135773 _26750 h P Q t h1)). Qed.
Lemma lem1135775 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (h : _26750) (t : list _26750) : term21 _26750 P Q h t.
Proof. exact (fun h0 : term15 _26750 P Q t => @lem1135774 _26750 h P Q t h0). Qed.
Lemma lem1135780 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) (h : _26750) : term25 _26750 P Q h.
Proof. exact (fun t : list _26750 => @lem1135775 _26750 P Q h t). Qed.
Lemma lem1135785 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : term29 _26750 P Q.
Proof. exact (fun h : _26750 => @lem1135780 _26750 P Q h). Qed.
Lemma lem1135786 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : term31 _26750 P Q.
Proof. exact (conj (@lem1133545 _26750 P Q) (@lem1135785 _26750 P Q)). Qed.
Lemma lem1135787 {_26750 : Type'} (P : _26750 -> Prop) (Q : _26750 -> Prop) : term36 _26750 P Q.
Proof. exact (@lem1133482 _26750 P Q (@lem1135786 _26750 P Q)). Qed.
Lemma lem1135792 {_26750 : Type'} (P : _26750 -> Prop) : term274 _26750 P.
Proof. exact (fun Q : _26750 -> Prop => @lem1135787 _26750 P Q). Qed.
Lemma lem1135797 {_26750 : Type'} : term275 _26750.
Proof. exact (fun P : _26750 -> Prop => @lem1135792 _26750 P). Qed.
