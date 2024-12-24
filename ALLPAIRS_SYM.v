Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALLPAIRS_SYM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1109872_spec.
Require Import thm1109873_spec.
Require Import thm1109884_spec.
Require Import thm1109885_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm7_spec.
Lemma lem1164520 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1164521 {_27460 : Type'} (P : type1143 _27460) : term0 _27460 P.
Proof. exact (@lem1164520 _27460 P). Qed.
Lemma lem1164522 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term1 _27459 _27460 P.
Proof. exact (@lem1164521 _27460 (term2 _27459 _27460 P)). Qed.
Lemma lem1164523 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term3 _27459 _27460 P) = (term4 _27459 _27460 P).
Proof. exact (eq_refl (term3 _27459 _27460 P)). Qed.
Lemma lem1164524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164525 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term5 _27459 _27460 P) = (term6 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164524) (@lem1164523 _27459 _27460 P)). Qed.
Lemma lem1164526 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (term7 _27459 _27460 P t) = (term8 _27459 _27460 P t).
Proof. exact (eq_refl (term7 _27459 _27460 P t)). Qed.
Lemma lem1164527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164528 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (term9 _27459 _27460 P t) = (term10 _27459 _27460 P t).
Proof. exact (MK_COMB (@lem1164527) (@lem1164526 _27459 _27460 P t)). Qed.
Lemma lem1164529 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term11 _27459 _27460 P h t) = (term12 _27459 _27460 P h t).
Proof. exact (eq_refl (term11 _27459 _27460 P h t)). Qed.
Lemma lem1164530 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term13 _27459 _27460 P h t) = (term14 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164528 _27459 _27460 P t) (@lem1164529 _27459 _27460 P h t)). Qed.
Lemma lem1164531 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term15 _27459 _27460 P h) = (term16 _27459 _27460 P h).
Proof. exact (fun_ext (fun t : list _27460 => @lem1164530 _27459 _27460 P h t)). Qed.
Lemma lem1164532 {_27460 : Type'} : (@all (list _27460)) = (@all (list _27460)).
Proof. exact (eq_refl (@all (list _27460))). Qed.
Lemma lem1164533 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term17 _27459 _27460 P h) = (term18 _27459 _27460 P h).
Proof. exact (MK_COMB (@lem1164532 _27460) (@lem1164531 _27459 _27460 P h)). Qed.
Lemma lem1164534 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term19 _27459 _27460 P) = (term20 _27459 _27460 P).
Proof. exact (fun_ext (fun h : _27460 => @lem1164533 _27459 _27460 P h)). Qed.
Lemma lem1164535 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1164536 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term21 _27459 _27460 P) = (term22 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164535 _27460) (@lem1164534 _27459 _27460 P)). Qed.
Lemma lem1164537 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term23 _27459 _27460 P) = (term24 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164525 _27459 _27460 P) (@lem1164536 _27459 _27460 P)). Qed.
Lemma lem1164538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164539 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term25 _27459 _27460 P) = (term26 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164538) (@lem1164537 _27459 _27460 P)). Qed.
Lemma lem1164540 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (l : list _27460) : (term7 _27459 _27460 P l) = (term8 _27459 _27460 P l).
Proof. exact (eq_refl (term7 _27459 _27460 P l)). Qed.
Lemma lem1164541 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term27 _27459 _27460 P) = (term2 _27459 _27460 P).
Proof. exact (fun_ext (fun l : list _27460 => @lem1164540 _27459 _27460 P l)). Qed.
Lemma lem1164542 {_27460 : Type'} : (@all (list _27460)) = (@all (list _27460)).
Proof. exact (eq_refl (@all (list _27460))). Qed.
Lemma lem1164543 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term28 _27459 _27460 P) = (term29 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164542 _27460) (@lem1164541 _27459 _27460 P)). Qed.
Lemma lem1164544 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term1 _27459 _27460 P) = (term30 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164539 _27459 _27460 P) (@lem1164543 _27459 _27460 P)). Qed.
Lemma lem1164545 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term30 _27459 _27460 P.
Proof. exact (EQ_MP (@lem1164544 _27459 _27460 P) (@lem1164522 _27459 _27460 P)). Qed.
Lemma lem1164546 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term8 _27459 _27460 P t.
Proof. exact (h1). Qed.
Lemma lem1164554 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True.
Proof. exact (EQ_MP (@lem1109873 _25786 _25787 f l) (@lem1109872 _25786 _25787 f l)). Qed.
Lemma lem1164555 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (l : list _27459) : (@ALLPAIRS _27459 _27460 f (@nil _27460) l) = True.
Proof. exact (@lem1164554 _27459 _27460 f l). Qed.
Lemma lem1164556 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) : (@ALLPAIRS _27459 _27460 P (@nil _27460) m) = True.
Proof. exact (@lem1164555 _27459 _27460 P m). Qed.
Lemma lem1164557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164558 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) : (term31 _27459 _27460 P m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1164557) (@lem1164556 _27459 _27460 P m)). Qed.
Lemma lem1164559 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) : (term32 _27459 _27460 P m) = (term32 _27459 _27460 P m).
Proof. exact (eq_refl (term32 _27459 _27460 P m)). Qed.
Lemma lem1164560 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) : ((@ALLPAIRS _27459 _27460 P (@nil _27460) m) = (term32 _27459 _27460 P m)) = (True = (term32 _27459 _27460 P m)).
Proof. exact (MK_COMB (@lem1164558 _27459 _27460 P m) (@lem1164559 _27459 _27460 P m)). Qed.
Lemma lem1164562 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1164563 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) : (True = (term32 _27459 _27460 P m)) = (term32 _27459 _27460 P m).
Proof. exact (@lem1164562 (term32 _27459 _27460 P m)). Qed.
Lemma lem1164564 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) : ((@ALLPAIRS _27459 _27460 P (@nil _27460) m) = (term32 _27459 _27460 P m)) = (term32 _27459 _27460 P m).
Proof. exact (TRANS (@lem1164560 _27459 _27460 P m) (@lem1164563 _27459 _27460 P m)). Qed.
Lemma lem1164565 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term33 _27459 _27460 P) = (term34 _27459 _27460 P).
Proof. exact (fun_ext (fun m : list _27459 => @lem1164564 _27459 _27460 P m)). Qed.
Lemma lem1164566 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1164567 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term4 _27459 _27460 P) = (term35 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164566 _27459) (@lem1164565 _27459 _27460 P)). Qed.
Lemma lem1164572 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term35 _27459 _27460 P) = (term4 _27459 _27460 P).
Proof. exact (SYM (@lem1164567 _27459 _27460 P)). Qed.
Lemma lem1164580 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term36 _25786 _25787 f h t l) = (term37 _25786 _25787 h f t l).
Proof. exact (EQ_MP (@lem1109885 _25786 _25787 h f t l) (@lem1109884 _25786 _25787 h f t l)). Qed.
Lemma lem1164581 {_27459 _27460 : Type'} (h : _27460) (f : type1470 _27459 _27460) (t : list _27460) (l : list _27459) : (term36 _27459 _27460 f h t l) = (term37 _27459 _27460 h f t l).
Proof. exact (@lem1164580 _27459 _27460 h f t l). Qed.
Lemma lem1164582 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term36 _27459 _27460 P h t m) = (term37 _27459 _27460 h P t m).
Proof. exact (@lem1164581 _27459 _27460 h P t m). Qed.
Lemma lem1164585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164586 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term38 _27459 _27460 P h t m) = (term39 _27459 _27460 h P t m).
Proof. exact (MK_COMB (@lem1164585) (@lem1164582 _27459 _27460 h P t m)). Qed.
Lemma lem1164587 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (h : _27460) (t : list _27460) : (term40 _27459 _27460 P m h t) = (term40 _27459 _27460 P m h t).
Proof. exact (eq_refl (term40 _27459 _27460 P m h t)). Qed.
Lemma lem1164588 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (h : _27460) (t : list _27460) : ((term36 _27459 _27460 P h t m) = (term40 _27459 _27460 P m h t)) = ((term37 _27459 _27460 h P t m) = (term40 _27459 _27460 P m h t)).
Proof. exact (MK_COMB (@lem1164586 _27459 _27460 h P t m) (@lem1164587 _27459 _27460 P m h t)). Qed.
Lemma lem1164591 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term41 _27459 _27460 P h t) = (term42 _27459 _27460 P h t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1164588 _27459 _27460 P m h t)). Qed.
Lemma lem1164592 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1164593 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term12 _27459 _27460 P h t) = (term43 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164592 _27459) (@lem1164591 _27459 _27460 P h t)). Qed.
Lemma lem1164598 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term43 _27459 _27460 P h t) = (term12 _27459 _27460 P h t).
Proof. exact (SYM (@lem1164593 _27459 _27460 P h t)). Qed.
Lemma lem1164600 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1164601 {_27459 : Type'} (P : type1143 _27459) : term0 _27459 P.
Proof. exact (@lem1164600 _27459 P). Qed.
Lemma lem1164602 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term44 _27459 _27460 P.
Proof. exact (@lem1164601 _27459 (term34 _27459 _27460 P)). Qed.
Lemma lem1164603 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term45 _27459 _27460 P) = (term46 _27459 _27460 P).
Proof. exact (eq_refl (term45 _27459 _27460 P)). Qed.
Lemma lem1164604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164605 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term47 _27459 _27460 P) = (term48 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164604) (@lem1164603 _27459 _27460 P)). Qed.
Lemma lem1164606 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) : (term49 _27459 _27460 P t) = (term32 _27459 _27460 P t).
Proof. exact (eq_refl (term49 _27459 _27460 P t)). Qed.
Lemma lem1164607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164608 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) : (term50 _27459 _27460 P t) = (term51 _27459 _27460 P t).
Proof. exact (MK_COMB (@lem1164607) (@lem1164606 _27459 _27460 P t)). Qed.
Lemma lem1164609 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) (t : list _27459) : (term52 _27459 _27460 P h t) = (term53 _27459 _27460 P h t).
Proof. exact (eq_refl (term52 _27459 _27460 P h t)). Qed.
Lemma lem1164610 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) (t : list _27459) : (term54 _27459 _27460 P h t) = (term55 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164608 _27459 _27460 P t) (@lem1164609 _27459 _27460 P h t)). Qed.
Lemma lem1164611 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) : (term56 _27459 _27460 P h) = (term57 _27459 _27460 P h).
Proof. exact (fun_ext (fun t : list _27459 => @lem1164610 _27459 _27460 P h t)). Qed.
Lemma lem1164612 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1164613 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) : (term58 _27459 _27460 P h) = (term59 _27459 _27460 P h).
Proof. exact (MK_COMB (@lem1164612 _27459) (@lem1164611 _27459 _27460 P h)). Qed.
Lemma lem1164614 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term60 _27459 _27460 P) = (term61 _27459 _27460 P).
Proof. exact (fun_ext (fun h : _27459 => @lem1164613 _27459 _27460 P h)). Qed.
Lemma lem1164615 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1164616 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term62 _27459 _27460 P) = (term63 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164615 _27459) (@lem1164614 _27459 _27460 P)). Qed.
Lemma lem1164617 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term64 _27459 _27460 P) = (term65 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164605 _27459 _27460 P) (@lem1164616 _27459 _27460 P)). Qed.
Lemma lem1164618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164619 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term66 _27459 _27460 P) = (term67 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164618) (@lem1164617 _27459 _27460 P)). Qed.
Lemma lem1164620 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) : (term49 _27459 _27460 P m) = (term32 _27459 _27460 P m).
Proof. exact (eq_refl (term49 _27459 _27460 P m)). Qed.
Lemma lem1164621 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term68 _27459 _27460 P) = (term34 _27459 _27460 P).
Proof. exact (fun_ext (fun m : list _27459 => @lem1164620 _27459 _27460 P m)). Qed.
Lemma lem1164622 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1164623 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term69 _27459 _27460 P) = (term35 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164622 _27459) (@lem1164621 _27459 _27460 P)). Qed.
Lemma lem1164624 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term44 _27459 _27460 P) = (term70 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164619 _27459 _27460 P) (@lem1164623 _27459 _27460 P)). Qed.
Lemma lem1164625 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term70 _27459 _27460 P.
Proof. exact (EQ_MP (@lem1164624 _27459 _27460 P) (@lem1164602 _27459 _27460 P)). Qed.
Lemma lem1164626 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : term32 _27459 _27460 P t.
Proof. exact (h1). Qed.
Lemma lem1164628 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1164629 {_27459 : Type'} (P : type1143 _27459) : term0 _27459 P.
Proof. exact (@lem1164628 _27459 P). Qed.
Lemma lem1164630 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : term71 _27459 _27460 P h t.
Proof. exact (@lem1164629 _27459 (term42 _27459 _27460 P h t)). Qed.
Lemma lem1164631 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term72 _27459 _27460 P h t) = ((term73 _27459 _27460 h P t) = (term74 _27459 _27460 P h t)).
Proof. exact (eq_refl (term72 _27459 _27460 P h t)). Qed.
Lemma lem1164632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164633 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term75 _27459 _27460 P h t) = (term76 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164632) (@lem1164631 _27459 _27460 P h t)). Qed.
Lemma lem1164634 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) (h : _27460) (t' : list _27460) : (term77 _27459 _27460 P h t' t) = ((term37 _27459 _27460 h P t' t) = (term40 _27459 _27460 P t h t')).
Proof. exact (eq_refl (term77 _27459 _27460 P h t' t)). Qed.
Lemma lem1164635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164636 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) (h : _27460) (t' : list _27460) : (term78 _27459 _27460 P h t' t) = (term79 _27459 _27460 P t h t').
Proof. exact (MK_COMB (@lem1164635) (@lem1164634 _27459 _27460 P t h t')). Qed.
Lemma lem1164637 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) (t : list _27459) (h' : _27460) (t' : list _27460) : (term80 _27459 _27460 P h' t' h t) = ((term81 _27459 _27460 h' P t' h t) = (term82 _27459 _27460 P h t h' t')).
Proof. exact (eq_refl (term80 _27459 _27460 P h' t' h t)). Qed.
Lemma lem1164638 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) (t : list _27459) (h' : _27460) (t' : list _27460) : (term83 _27459 _27460 P h' t' h t) = (term84 _27459 _27460 P h t h' t').
Proof. exact (MK_COMB (@lem1164636 _27459 _27460 P t h' t') (@lem1164637 _27459 _27460 P h t h' t')). Qed.
Lemma lem1164639 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) (h' : _27460) (t : list _27460) : (term85 _27459 _27460 P h' t h) = (term86 _27459 _27460 P h h' t).
Proof. exact (fun_ext (fun t' : list _27459 => @lem1164638 _27459 _27460 P h t' h' t)). Qed.
Lemma lem1164640 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1164641 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) (h' : _27460) (t : list _27460) : (term87 _27459 _27460 P h' t h) = (term88 _27459 _27460 P h h' t).
Proof. exact (MK_COMB (@lem1164640 _27459) (@lem1164639 _27459 _27460 P h h' t)). Qed.
Lemma lem1164642 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term89 _27459 _27460 P h t) = (term90 _27459 _27460 P h t).
Proof. exact (fun_ext (fun h' : _27459 => @lem1164641 _27459 _27460 P h' h t)). Qed.
Lemma lem1164643 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1164644 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term91 _27459 _27460 P h t) = (term92 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164643 _27459) (@lem1164642 _27459 _27460 P h t)). Qed.
Lemma lem1164645 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term93 _27459 _27460 P h t) = (term94 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164633 _27459 _27460 P h t) (@lem1164644 _27459 _27460 P h t)). Qed.
Lemma lem1164646 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164647 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term95 _27459 _27460 P h t) = (term96 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164646) (@lem1164645 _27459 _27460 P h t)). Qed.
Lemma lem1164648 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (h : _27460) (t : list _27460) : (term77 _27459 _27460 P h t m) = ((term37 _27459 _27460 h P t m) = (term40 _27459 _27460 P m h t)).
Proof. exact (eq_refl (term77 _27459 _27460 P h t m)). Qed.
Lemma lem1164649 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term97 _27459 _27460 P h t) = (term42 _27459 _27460 P h t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1164648 _27459 _27460 P m h t)). Qed.
Lemma lem1164650 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1164651 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term98 _27459 _27460 P h t) = (term43 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164650 _27459) (@lem1164649 _27459 _27460 P h t)). Qed.
Lemma lem1164652 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term71 _27459 _27460 P h t) = (term99 _27459 _27460 P h t).
Proof. exact (MK_COMB (@lem1164647 _27459 _27460 P h t) (@lem1164651 _27459 _27460 P h t)). Qed.
Lemma lem1164653 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : term99 _27459 _27460 P h t.
Proof. exact (EQ_MP (@lem1164652 _27459 _27460 P h t) (@lem1164630 _27459 _27460 P h t)). Qed.
Lemma lem1164654 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t).
Proof. exact (h1). Qed.
Lemma lem1164660 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True.
Proof. exact (EQ_MP (@lem1109873 _25786 _25787 f l) (@lem1109872 _25786 _25787 f l)). Qed.
Lemma lem1164661 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (l : list _27460) : (@ALLPAIRS _27460 _27459 f (@nil _27459) l) = True.
Proof. exact (@lem1164660 _27460 _27459 f l). Qed.
Lemma lem1164662 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term46 _27459 _27460 P) = True.
Proof. exact (@lem1164661 _27459 _27460 (term100 _27459 _27460 P) (@nil _27460)). Qed.
Lemma lem1164663 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : True = (term46 _27459 _27460 P).
Proof. exact (SYM (@lem1164662 _27459 _27460 P)). Qed.
Lemma lem1164664 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term46 _27459 _27460 P.
Proof. exact (EQ_MP (@lem1164663 _27459 _27460 P) (@lem0)). Qed.
Lemma lem1164669 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) : (term32 _27459 _27460 P t) = ((term32 _27459 _27460 P t) = True).
Proof. exact (@lem7 (term32 _27459 _27460 P t)). Qed.
Lemma lem1164672 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term36 _25786 _25787 f h t l) = (term37 _25786 _25787 h f t l).
Proof. exact (EQ_MP (@lem1109885 _25786 _25787 h f t l) (@lem1109884 _25786 _25787 h f t l)). Qed.
Lemma lem1164673 {_27459 _27460 : Type'} (h : _27459) (f : type1413 _27459 _27460) (t : list _27459) (l : list _27460) : (term101 _27459 _27460 f h t l) = (term102 _27459 _27460 h f t l).
Proof. exact (@lem1164672 _27460 _27459 h f t l). Qed.
Lemma lem1164674 {_27459 _27460 : Type'} (h : _27459) (P : type1470 _27459 _27460) (t : list _27459) : (term53 _27459 _27460 P h t) = (term103 _27459 _27460 h P t).
Proof. exact (@lem1164673 _27459 _27460 h (term100 _27459 _27460 P) t (@nil _27460)). Qed.
Lemma lem1164678 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1164679 {_27460 : Type'} (P : _27460 -> Prop) : (@List.Forall _27460 P (@nil _27460)) = True.
Proof. exact (@lem1164678 _27460 P). Qed.
Lemma lem1164680 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) : (term104 _27459 _27460 P h) = True.
Proof. exact (@lem1164679 _27460 (term105 _27459 _27460 P h)). Qed.
Lemma lem1164681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164682 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) : (term106 _27459 _27460 P h) = (and True).
Proof. exact (MK_COMB (@lem1164681) (@lem1164680 _27459 _27460 P h)). Qed.
Lemma lem1164684 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : (term32 _27459 _27460 P t) = True.
Proof. exact (EQ_MP (@lem1164669 _27459 _27460 P t) (@lem1164626 _27459 _27460 P t h1)). Qed.
Lemma lem1164685 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : (term32 _27459 _27460 P t) = True.
Proof. exact (@lem1164684 _27459 _27460 P t h1). Qed.
Lemma lem1164686 {_27459 _27460 : Type'} (h : _27459) (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : (term103 _27459 _27460 h P t) = (True /\ True).
Proof. exact (MK_COMB (@lem1164682 _27459 _27460 P h) (@lem1164685 _27459 _27460 P t h1)). Qed.
Lemma lem1164688 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1164689 : (True /\ True) = True.
Proof. exact (@lem1164688 True). Qed.
Lemma lem1164690 {_27459 _27460 : Type'} (h : _27459) (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : (term103 _27459 _27460 h P t) = True.
Proof. exact (TRANS (@lem1164686 _27459 _27460 h P t h1) (@lem1164689)). Qed.
Lemma lem1164691 {_27459 _27460 : Type'} (h : _27459) (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : (term53 _27459 _27460 P h t) = True.
Proof. exact (TRANS (@lem1164674 _27459 _27460 h P t) (@lem1164690 _27459 _27460 h P t h1)). Qed.
Lemma lem1164692 {_27459 _27460 : Type'} (h : _27459) (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : True = (term53 _27459 _27460 P h t).
Proof. exact (SYM (@lem1164691 _27459 _27460 h P t h1)). Qed.
Lemma lem1164693 {_27459 _27460 : Type'} (h : _27459) (P : type1470 _27459 _27460) (t : list _27459) (h1 : term32 _27459 _27460 P t) : term53 _27459 _27460 P h t.
Proof. exact (EQ_MP (@lem1164692 _27459 _27460 h P t h1) (@lem0)). Qed.
Lemma lem1164698 {_27459 _27460 : Type'} (m : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term107 _27459 _27460 P t m.
Proof. exact (@lem1164546 _27459 _27460 P t h1 m). Qed.
Lemma lem1164699 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term107 _27459 _27460 P t m) = ((@ALLPAIRS _27459 _27460 P t m) = (term108 _27459 _27460 P m t)).
Proof. exact (eq_refl (term107 _27459 _27460 P t m)). Qed.
Lemma lem1164706 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1164707 {_27459 : Type'} (P : _27459 -> Prop) : (@List.Forall _27459 P (@nil _27459)) = True.
Proof. exact (@lem1164706 _27459 P). Qed.
Lemma lem1164708 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term109 _27459 _27460 P h) = True.
Proof. exact (@lem1164707 _27459 (P h)). Qed.
Lemma lem1164709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164710 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term110 _27459 _27460 P h) = (and True).
Proof. exact (MK_COMB (@lem1164709) (@lem1164708 _27459 _27460 P h)). Qed.
Lemma lem1164712 {_27459 _27460 : Type'} (m : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (@ALLPAIRS _27459 _27460 P t m) = (term108 _27459 _27460 P m t).
Proof. exact (EQ_MP (@lem1164699 _27459 _27460 P m t) (@lem1164698 _27459 _27460 m P t h1)). Qed.
Lemma lem1164713 {_27459 _27460 : Type'} (m : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (@ALLPAIRS _27459 _27460 P t m) = (term108 _27459 _27460 P m t).
Proof. exact (@lem1164712 _27459 _27460 m P t h1). Qed.
Lemma lem1164714 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (@ALLPAIRS _27459 _27460 P t (@nil _27459)) = (term111 _27459 _27460 P t).
Proof. exact (@lem1164713 _27459 _27460 (@nil _27459) P t h1). Qed.
Lemma lem1164716 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True.
Proof. exact (EQ_MP (@lem1109873 _25786 _25787 f l) (@lem1109872 _25786 _25787 f l)). Qed.
Lemma lem1164717 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (l : list _27460) : (@ALLPAIRS _27460 _27459 f (@nil _27459) l) = True.
Proof. exact (@lem1164716 _27460 _27459 f l). Qed.
Lemma lem1164718 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (term111 _27459 _27460 P t) = True.
Proof. exact (@lem1164717 _27459 _27460 (term100 _27459 _27460 P) t). Qed.
Lemma lem1164719 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (@ALLPAIRS _27459 _27460 P t (@nil _27459)) = True.
Proof. exact (TRANS (@lem1164714 _27459 _27460 P t h1) (@lem1164718 _27459 _27460 P t)). Qed.
Lemma lem1164720 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term73 _27459 _27460 h P t) = (True /\ True).
Proof. exact (MK_COMB (@lem1164710 _27459 _27460 P h) (@lem1164719 _27459 _27460 P t h1)). Qed.
Lemma lem1164722 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1164723 : (True /\ True) = True.
Proof. exact (@lem1164722 True). Qed.
Lemma lem1164724 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term73 _27459 _27460 h P t) = True.
Proof. exact (TRANS (@lem1164720 _27459 _27460 h P t h1) (@lem1164723)). Qed.
Lemma lem1164725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164726 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term112 _27459 _27460 h P t) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1164725) (@lem1164724 _27459 _27460 h P t h1)). Qed.
Lemma lem1164728 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True.
Proof. exact (EQ_MP (@lem1109873 _25786 _25787 f l) (@lem1109872 _25786 _25787 f l)). Qed.
Lemma lem1164729 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (l : list _27460) : (@ALLPAIRS _27460 _27459 f (@nil _27459) l) = True.
Proof. exact (@lem1164728 _27460 _27459 f l). Qed.
Lemma lem1164730 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : (term74 _27459 _27460 P h t) = True.
Proof. exact (@lem1164729 _27459 _27460 (term100 _27459 _27460 P) (@cons _27460 h t)). Qed.
Lemma lem1164731 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : ((term73 _27459 _27460 h P t) = (term74 _27459 _27460 P h t)) = (True = True).
Proof. exact (MK_COMB (@lem1164726 _27459 _27460 h P t h1) (@lem1164730 _27459 _27460 P h t)). Qed.
Lemma lem1164733 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1164734 : (True = True) = True.
Proof. exact (@lem1164733 True). Qed.
Lemma lem1164735 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : ((term73 _27459 _27460 h P t) = (term74 _27459 _27460 P h t)) = True.
Proof. exact (TRANS (@lem1164731 _27459 _27460 h P t h1) (@lem1164734)). Qed.
Lemma lem1164736 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : True = ((term73 _27459 _27460 h P t) = (term74 _27459 _27460 P h t)).
Proof. exact (SYM (@lem1164735 _27459 _27460 h P t h1)). Qed.
Lemma lem1164737 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term73 _27459 _27460 h P t) = (term74 _27459 _27460 P h t).
Proof. exact (EQ_MP (@lem1164736 _27459 _27460 h P t h1) (@lem0)). Qed.
Lemma lem1164742 {_27459 _27460 : Type'} (m : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term107 _27459 _27460 P t m.
Proof. exact (@lem1164546 _27459 _27460 P t h1 m). Qed.
Lemma lem1164743 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term107 _27459 _27460 P t m) = ((@ALLPAIRS _27459 _27460 P t m) = (term108 _27459 _27460 P m t)).
Proof. exact (eq_refl (term107 _27459 _27460 P t m)). Qed.
Lemma lem1164750 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term113 _25307 P h t) = (term114 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1164751 {_27459 : Type'} (h : _27459) (P : _27459 -> Prop) (t : list _27459) : (term113 _27459 P h t) = (term114 _27459 h P t).
Proof. exact (@lem1164750 _27459 h P t). Qed.
Lemma lem1164752 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term115 _27459 _27460 P h h' t') = (term116 _27459 _27460 h' P h t').
Proof. exact (@lem1164751 _27459 h' (P h) t'). Qed.
Lemma lem1164755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164756 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term117 _27459 _27460 P h h' t') = (term118 _27459 _27460 h' P h t').
Proof. exact (MK_COMB (@lem1164755) (@lem1164752 _27459 _27460 h' P h t')). Qed.
Lemma lem1164758 {_27459 _27460 : Type'} (m : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (@ALLPAIRS _27459 _27460 P t m) = (term108 _27459 _27460 P m t).
Proof. exact (EQ_MP (@lem1164743 _27459 _27460 P m t) (@lem1164742 _27459 _27460 m P t h1)). Qed.
Lemma lem1164759 {_27459 _27460 : Type'} (m : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (@ALLPAIRS _27459 _27460 P t m) = (term108 _27459 _27460 P m t).
Proof. exact (@lem1164758 _27459 _27460 m P t h1). Qed.
Lemma lem1164760 {_27459 _27460 : Type'} (h' : _27459) (t' : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term119 _27459 _27460 P t h' t') = (term120 _27459 _27460 P h' t' t).
Proof. exact (@lem1164759 _27459 _27460 (@cons _27459 h' t') P t h1). Qed.
Lemma lem1164762 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term36 _25786 _25787 f h t l) = (term37 _25786 _25787 h f t l).
Proof. exact (EQ_MP (@lem1109885 _25786 _25787 h f t l) (@lem1109884 _25786 _25787 h f t l)). Qed.
Lemma lem1164763 {_27459 _27460 : Type'} (h : _27459) (f : type1413 _27459 _27460) (t : list _27459) (l : list _27460) : (term101 _27459 _27460 f h t l) = (term102 _27459 _27460 h f t l).
Proof. exact (@lem1164762 _27460 _27459 h f t l). Qed.
Lemma lem1164764 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term120 _27459 _27460 P h' t' t) = (term121 _27459 _27460 h' P t' t).
Proof. exact (@lem1164763 _27459 _27460 h' (term100 _27459 _27460 P) t' t). Qed.
Lemma lem1164767 {_27459 _27460 : Type'} (h' : _27459) (t' : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term119 _27459 _27460 P t h' t') = (term121 _27459 _27460 h' P t' t).
Proof. exact (TRANS (@lem1164760 _27459 _27460 h' t' P t h1) (@lem1164764 _27459 _27460 h' P t' t)). Qed.
Lemma lem1164769 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1164770 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (y : _27459) : (term123 _27459 _27460 f y) = (f y).
Proof. exact (@lem1164769 _27459 (_27460 -> Prop) f y). Qed.
Lemma lem1164771 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term124 _27459 _27460 P h') = (term105 _27459 _27460 P h').
Proof. exact (@lem1164770 _27459 _27460 (term100 _27459 _27460 P) h'). Qed.
Lemma lem1164772 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1164773 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term126 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1164772 _27459 _27460 P x)). Qed.
Lemma lem1164774 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1164775 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term124 _27459 _27460 P h') = (term105 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164773 _27459 _27460 P) (@lem1164774 _27459 h')). Qed.
Lemma lem1164776 {_27460 : Type'} : (@eq (_27460 -> Prop)) = (@eq (_27460 -> Prop)).
Proof. exact (eq_refl (@eq (_27460 -> Prop))). Qed.
Lemma lem1164777 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term127 _27459 _27460 P h') = (term128 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164776 _27460) (@lem1164775 _27459 _27460 P h')). Qed.
Lemma lem1164778 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term105 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (eq_refl (term105 _27459 _27460 P h')). Qed.
Lemma lem1164779 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : ((term124 _27459 _27460 P h') = (term105 _27459 _27460 P h')) = ((term105 _27459 _27460 P h') = (term125 _27459 _27460 P h')).
Proof. exact (MK_COMB (@lem1164777 _27459 _27460 P h') (@lem1164778 _27459 _27460 P h')). Qed.
Lemma lem1164780 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term105 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (EQ_MP (@lem1164779 _27459 _27460 P h') (@lem1164771 _27459 _27460 P h')). Qed.
Lemma lem1164781 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1164782 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term129 _27459 _27460 P h') = (term130 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164781 _27460) (@lem1164780 _27459 _27460 P h')). Qed.
Lemma lem1164783 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1164784 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term131 _27459 _27460 P h' t) = (term132 _27459 _27460 P h' t).
Proof. exact (MK_COMB (@lem1164782 _27459 _27460 P h') (@lem1164783 _27460 t)). Qed.
Lemma lem1164785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164786 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term133 _27459 _27460 P h' t) = (term134 _27459 _27460 P h' t).
Proof. exact (MK_COMB (@lem1164785) (@lem1164784 _27459 _27460 P h' t)). Qed.
Lemma lem1164787 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term108 _27459 _27460 P t' t) = (term108 _27459 _27460 P t' t).
Proof. exact (eq_refl (term108 _27459 _27460 P t' t)). Qed.
Lemma lem1164788 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term121 _27459 _27460 h' P t' t) = (term135 _27459 _27460 h' P t' t).
Proof. exact (MK_COMB (@lem1164786 _27459 _27460 P h' t) (@lem1164787 _27459 _27460 P t' t)). Qed.
Lemma lem1164791 {_27459 _27460 : Type'} (h' : _27459) (t' : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term119 _27459 _27460 P t h' t') = (term135 _27459 _27460 h' P t' t).
Proof. exact (TRANS (@lem1164767 _27459 _27460 h' t' P t h1) (@lem1164788 _27459 _27460 h' P t' t)). Qed.
Lemma lem1164792 {_27459 _27460 : Type'} (h : _27460) (h' : _27459) (t' : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term81 _27459 _27460 h P t h' t') = (term136 _27459 _27460 h h' P t' t).
Proof. exact (MK_COMB (@lem1164756 _27459 _27460 h' P h t') (@lem1164791 _27459 _27460 h' t' P t h1)). Qed.
Lemma lem1164795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164796 {_27459 _27460 : Type'} (h : _27460) (h' : _27459) (t' : list _27459) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : (term137 _27459 _27460 h P t h' t') = (term138 _27459 _27460 h h' P t' t).
Proof. exact (MK_COMB (@lem1164795) (@lem1164792 _27459 _27460 h h' t' P t h1)). Qed.
Lemma lem1164798 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term36 _25786 _25787 f h t l) = (term37 _25786 _25787 h f t l).
Proof. exact (EQ_MP (@lem1109885 _25786 _25787 h f t l) (@lem1109884 _25786 _25787 h f t l)). Qed.
Lemma lem1164799 {_27459 _27460 : Type'} (h : _27459) (f : type1413 _27459 _27460) (t : list _27459) (l : list _27460) : (term101 _27459 _27460 f h t l) = (term102 _27459 _27460 h f t l).
Proof. exact (@lem1164798 _27460 _27459 h f t l). Qed.
Lemma lem1164800 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term82 _27459 _27460 P h' t' h t) = (term139 _27459 _27460 h' P t' h t).
Proof. exact (@lem1164799 _27459 _27460 h' (term100 _27459 _27460 P) t' (@cons _27460 h t)). Qed.
Lemma lem1164804 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term113 _25307 P h t) = (term114 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1164805 {_27460 : Type'} (h : _27460) (P : _27460 -> Prop) (t : list _27460) : (term113 _27460 P h t) = (term114 _27460 h P t).
Proof. exact (@lem1164804 _27460 h P t). Qed.
Lemma lem1164806 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term140 _27459 _27460 P h' h t) = (term141 _27459 _27460 h P h' t).
Proof. exact (@lem1164805 _27460 h (term105 _27459 _27460 P h') t). Qed.
Lemma lem1164810 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1164811 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (y : _27459) : (term123 _27459 _27460 f y) = (f y).
Proof. exact (@lem1164810 _27459 (_27460 -> Prop) f y). Qed.
Lemma lem1164812 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term124 _27459 _27460 P h') = (term105 _27459 _27460 P h').
Proof. exact (@lem1164811 _27459 _27460 (term100 _27459 _27460 P) h'). Qed.
Lemma lem1164813 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1164814 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term126 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1164813 _27459 _27460 P x)). Qed.
Lemma lem1164815 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1164816 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term124 _27459 _27460 P h') = (term105 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164814 _27459 _27460 P) (@lem1164815 _27459 h')). Qed.
Lemma lem1164817 {_27460 : Type'} : (@eq (_27460 -> Prop)) = (@eq (_27460 -> Prop)).
Proof. exact (eq_refl (@eq (_27460 -> Prop))). Qed.
Lemma lem1164818 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term127 _27459 _27460 P h') = (term128 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164817 _27460) (@lem1164816 _27459 _27460 P h')). Qed.
Lemma lem1164819 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term105 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (eq_refl (term105 _27459 _27460 P h')). Qed.
Lemma lem1164820 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : ((term124 _27459 _27460 P h') = (term105 _27459 _27460 P h')) = ((term105 _27459 _27460 P h') = (term125 _27459 _27460 P h')).
Proof. exact (MK_COMB (@lem1164818 _27459 _27460 P h') (@lem1164819 _27459 _27460 P h')). Qed.
Lemma lem1164821 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term105 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (EQ_MP (@lem1164820 _27459 _27460 P h') (@lem1164812 _27459 _27460 P h')). Qed.
Lemma lem1164822 {_27460 : Type'} (h : _27460) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1164823 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (h : _27460) : (term142 _27459 _27460 P h' h) = (term143 _27459 _27460 P h' h).
Proof. exact (MK_COMB (@lem1164821 _27459 _27460 P h') (@lem1164822 _27460 h)). Qed.
Lemma lem1164825 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1164826 {_27460 : Type'} (f : _27460 -> Prop) (y : _27460) : (term144 _27460 f y) = (f y).
Proof. exact (@lem1164825 _27460 Prop f y). Qed.
Lemma lem1164827 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (h : _27460) : (term145 _27459 _27460 P h' h) = (term143 _27459 _27460 P h' h).
Proof. exact (@lem1164826 _27460 (term125 _27459 _27460 P h') h). Qed.
Lemma lem1164828 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (y : _27460) (h' : _27459) : (term143 _27459 _27460 P h' y) = (P y h').
Proof. exact (eq_refl (term143 _27459 _27460 P h' y)). Qed.
Lemma lem1164829 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term146 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (fun_ext (fun y : _27460 => @lem1164828 _27459 _27460 P y h')). Qed.
Lemma lem1164830 {_27460 : Type'} (h : _27460) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1164831 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (h : _27460) : (term145 _27459 _27460 P h' h) = (term143 _27459 _27460 P h' h).
Proof. exact (MK_COMB (@lem1164829 _27459 _27460 P h') (@lem1164830 _27460 h)). Qed.
Lemma lem1164832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164833 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (h : _27460) : (term147 _27459 _27460 P h' h) = (term148 _27459 _27460 P h' h).
Proof. exact (MK_COMB (@lem1164832) (@lem1164831 _27459 _27460 P h' h)). Qed.
Lemma lem1164834 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term143 _27459 _27460 P h' h) = (P h h').
Proof. exact (eq_refl (term143 _27459 _27460 P h' h)). Qed.
Lemma lem1164835 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : ((term145 _27459 _27460 P h' h) = (term143 _27459 _27460 P h' h)) = ((term143 _27459 _27460 P h' h) = (P h h')).
Proof. exact (MK_COMB (@lem1164833 _27459 _27460 P h' h) (@lem1164834 _27459 _27460 P h h')). Qed.
Lemma lem1164836 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term143 _27459 _27460 P h' h) = (P h h').
Proof. exact (EQ_MP (@lem1164835 _27459 _27460 P h h') (@lem1164827 _27459 _27460 P h' h)). Qed.
Lemma lem1164837 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term142 _27459 _27460 P h' h) = (P h h').
Proof. exact (TRANS (@lem1164823 _27459 _27460 P h' h) (@lem1164836 _27459 _27460 P h h')). Qed.
Lemma lem1164838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164839 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term149 _27459 _27460 P h' h) = (term150 _27459 _27460 P h h').
Proof. exact (MK_COMB (@lem1164838) (@lem1164837 _27459 _27460 P h h')). Qed.
Lemma lem1164841 {A B : Type'} (f : A -> B) (y : A) : (term122 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1164842 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (y : _27459) : (term123 _27459 _27460 f y) = (f y).
Proof. exact (@lem1164841 _27459 (_27460 -> Prop) f y). Qed.
Lemma lem1164843 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term124 _27459 _27460 P h') = (term105 _27459 _27460 P h').
Proof. exact (@lem1164842 _27459 _27460 (term100 _27459 _27460 P) h'). Qed.
Lemma lem1164844 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1164845 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term126 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1164844 _27459 _27460 P x)). Qed.
Lemma lem1164846 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1164847 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term124 _27459 _27460 P h') = (term105 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164845 _27459 _27460 P) (@lem1164846 _27459 h')). Qed.
Lemma lem1164848 {_27460 : Type'} : (@eq (_27460 -> Prop)) = (@eq (_27460 -> Prop)).
Proof. exact (eq_refl (@eq (_27460 -> Prop))). Qed.
Lemma lem1164849 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term127 _27459 _27460 P h') = (term128 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164848 _27460) (@lem1164847 _27459 _27460 P h')). Qed.
Lemma lem1164850 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term105 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (eq_refl (term105 _27459 _27460 P h')). Qed.
Lemma lem1164851 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : ((term124 _27459 _27460 P h') = (term105 _27459 _27460 P h')) = ((term105 _27459 _27460 P h') = (term125 _27459 _27460 P h')).
Proof. exact (MK_COMB (@lem1164849 _27459 _27460 P h') (@lem1164850 _27459 _27460 P h')). Qed.
Lemma lem1164852 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term105 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (EQ_MP (@lem1164851 _27459 _27460 P h') (@lem1164843 _27459 _27460 P h')). Qed.
Lemma lem1164853 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1164854 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term129 _27459 _27460 P h') = (term130 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1164853 _27460) (@lem1164852 _27459 _27460 P h')). Qed.
Lemma lem1164855 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1164856 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term131 _27459 _27460 P h' t) = (term132 _27459 _27460 P h' t).
Proof. exact (MK_COMB (@lem1164854 _27459 _27460 P h') (@lem1164855 _27460 t)). Qed.
Lemma lem1164857 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term141 _27459 _27460 h P h' t) = (term151 _27459 _27460 h P h' t).
Proof. exact (MK_COMB (@lem1164839 _27459 _27460 P h h') (@lem1164856 _27459 _27460 P h' t)). Qed.
Lemma lem1164860 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term140 _27459 _27460 P h' h t) = (term151 _27459 _27460 h P h' t).
Proof. exact (TRANS (@lem1164806 _27459 _27460 h P h' t) (@lem1164857 _27459 _27460 h P h' t)). Qed.
Lemma lem1164861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164862 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term152 _27459 _27460 P h' h t) = (term153 _27459 _27460 h P h' t).
Proof. exact (MK_COMB (@lem1164861) (@lem1164860 _27459 _27460 h P h' t)). Qed.
Lemma lem1164863 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term40 _27459 _27460 P t' h t) = (term40 _27459 _27460 P t' h t).
Proof. exact (eq_refl (term40 _27459 _27460 P t' h t)). Qed.
Lemma lem1164864 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term139 _27459 _27460 h' P t' h t) = (term154 _27459 _27460 h' P t' h t).
Proof. exact (MK_COMB (@lem1164862 _27459 _27460 h P h' t) (@lem1164863 _27459 _27460 P t' h t)). Qed.
Lemma lem1164867 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term82 _27459 _27460 P h' t' h t) = (term154 _27459 _27460 h' P t' h t).
Proof. exact (TRANS (@lem1164800 _27459 _27460 h' P t' h t) (@lem1164864 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164868 {_27459 _27460 : Type'} (h' : _27459) (t' : list _27459) (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : ((term81 _27459 _27460 h P t h' t') = (term82 _27459 _27460 P h' t' h t)) = ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t)).
Proof. exact (MK_COMB (@lem1164796 _27459 _27460 h h' t' P t h1) (@lem1164867 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164871 {_27459 _27460 : Type'} (h' : _27459) (t' : list _27459) (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t)) = ((term81 _27459 _27460 h P t h' t') = (term82 _27459 _27460 P h' t' h t)).
Proof. exact (SYM (@lem1164868 _27459 _27460 h' t' h P t h1)). Qed.
Lemma lem1164873 (p : Prop) : p = (term155 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1164874 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t)) = (term156 _27459 _27460 h' P t' h t).
Proof. exact (@lem1164873 ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t))). Qed.
Lemma lem1164875 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term156 _27459 _27460 h' P t' h t) = ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t)).
Proof. exact (SYM (@lem1164874 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164876 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term157 _27459 _27460 h' P t' h t) : term157 _27459 _27460 h' P t' h t.
Proof. exact (h1). Qed.
Lemma lem1164879 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term158 _27459 _27460 h' P t' h t) : term158 _27459 _27460 h' P t' h t.
Proof. exact (h1). Qed.
Lemma lem1164880 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term159 _27459 _27460 h' P t' h t.
Proof. exact (fun h0 : term158 _27459 _27460 h' P t' h t => @lem1164879 _27459 _27460 h' P t' h t h0). Qed.
Lemma lem1164881 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term159 _27459 _27460 h' P t' h t) : term159 _27459 _27460 h' P t' h t.
Proof. exact (h1). Qed.
Lemma lem1164882 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term158 _27459 _27460 h' P t' h t) : term158 _27459 _27460 h' P t' h t.
Proof. exact (h1). Qed.
Lemma lem1164883 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term158 _27459 _27460 h' P t' h t) (h2 : term159 _27459 _27460 h' P t' h t) : term158 _27459 _27460 h' P t' h t.
Proof. exact (@lem1164881 _27459 _27460 h' P t' h t h2 (@lem1164882 _27459 _27460 h' P t' h t h1)). Qed.
Lemma lem1164884 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term158 _27459 _27460 h' P t' h t) : term160 _27459 _27460 h' P t' h t.
Proof. exact (fun h0 : term159 _27459 _27460 h' P t' h t => @lem1164883 _27459 _27460 h' P t' h t h1 h0). Qed.
Lemma lem1164885 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term159 _27459 _27460 h' P t' h t) : term159 _27459 _27460 h' P t' h t.
Proof. exact (h1). Qed.
Lemma lem1164886 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term158 _27459 _27460 h' P t' h t) (h2 : term159 _27459 _27460 h' P t' h t) : term158 _27459 _27460 h' P t' h t.
Proof. exact (@lem1164884 _27459 _27460 h' P t' h t h1 (@lem1164885 _27459 _27460 h' P t' h t h2)). Qed.
Lemma lem1164887 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term159 _27459 _27460 h' P t' h t) : term159 _27459 _27460 h' P t' h t.
Proof. exact (fun h0 : term158 _27459 _27460 h' P t' h t => @lem1164886 _27459 _27460 h' P t' h t h0 h1). Qed.
Lemma lem1164888 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term161 _27459 _27460 h' P t' h t.
Proof. exact (fun h0 : term159 _27459 _27460 h' P t' h t => @lem1164887 _27459 _27460 h' P t' h t h0). Qed.
Lemma lem1164891 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term159 _27459 _27460 h' P t' h t.
Proof. exact (@lem1164888 _27459 _27460 h' P t' h t (@lem1164880 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164892 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term159 _27459 _27460 h' P t' h t.
Proof. exact (@lem1164891 _27459 _27460 h' P t' h t). Qed.
Lemma lem1164924 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1164925 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term156 _27459 _27460 h' P t' h t) = (term162 _27459 _27460 h' P t' h t).
Proof. exact (@lem1164924 (term157 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164927 (t : Prop) : (term163 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1164928 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term162 _27459 _27460 h' P t' h t) = ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t)).
Proof. exact (@lem1164927 ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t))). Qed.
Lemma lem1164929 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term156 _27459 _27460 h' P t' h t) = ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t)).
Proof. exact (TRANS (@lem1164925 _27459 _27460 h' P t' h t) (@lem1164928 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164940 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term79 _27459 _27460 P t' h t) = (term79 _27459 _27460 P t' h t).
Proof. exact (eq_refl (term79 _27459 _27460 P t' h t)). Qed.
Lemma lem1164941 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term164 _27459 _27460 h' P t' h t) = (term165 _27459 _27460 h' P t' h t).
Proof. exact (MK_COMB (@lem1164940 _27459 _27460 P t' h t) (@lem1164929 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164944 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (term10 _27459 _27460 P t) = (term10 _27459 _27460 P t).
Proof. exact (eq_refl (term10 _27459 _27460 P t)). Qed.
Lemma lem1164945 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term158 _27459 _27460 h' P t' h t) = (term166 _27459 _27460 h' P t' h t).
Proof. exact (MK_COMB (@lem1164944 _27459 _27460 P t) (@lem1164941 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164948 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term167 _27459 _27460 P t' h t) = (term168 _27459 _27460 P t' h t).
Proof. exact (fun_ext (fun h' : _27459 => @lem1164945 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1164949 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1164950 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term169 _27459 _27460 P t' h t) = (term170 _27459 _27460 P t' h t).
Proof. exact (MK_COMB (@lem1164949 _27459) (@lem1164948 _27459 _27460 P t' h t)). Qed.
Lemma lem1164955 {_27459 _27460 : Type'} (t' : list _27459) (h : _27460) (t : list _27460) : (term171 _27459 _27460 t' h t) = (term172 _27459 _27460 t' h t).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1164950 _27459 _27460 P t' h t)). Qed.
Lemma lem1164956 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1164957 {_27459 _27460 : Type'} (t' : list _27459) (h : _27460) (t : list _27460) : (term173 _27459 _27460 t' h t) = (term174 _27459 _27460 t' h t).
Proof. exact (MK_COMB (@lem1164956 _27459 _27460) (@lem1164955 _27459 _27460 t' h t)). Qed.
Lemma lem1164962 {_27459 _27460 : Type'} (h : _27460) (t : list _27460) : (term175 _27459 _27460 h t) = (term176 _27459 _27460 h t).
Proof. exact (fun_ext (fun t' : list _27459 => @lem1164957 _27459 _27460 t' h t)). Qed.
Lemma lem1164963 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1164964 {_27459 _27460 : Type'} (h : _27460) (t : list _27460) : (term177 _27459 _27460 h t) = (term178 _27459 _27460 h t).
Proof. exact (MK_COMB (@lem1164963 _27459) (@lem1164962 _27459 _27460 h t)). Qed.
Lemma lem1164969 {_27459 _27460 : Type'} (t : list _27460) : (term179 _27459 _27460 t) = (term180 _27459 _27460 t).
Proof. exact (fun_ext (fun h : _27460 => @lem1164964 _27459 _27460 h t)). Qed.
Lemma lem1164970 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1164971 {_27459 _27460 : Type'} (t : list _27460) : (term181 _27459 _27460 t) = (term182 _27459 _27460 t).
Proof. exact (MK_COMB (@lem1164970 _27460) (@lem1164969 _27459 _27460 t)). Qed.
Lemma lem1164976 {_27459 _27460 : Type'} : (term183 _27459 _27460) = (term184 _27459 _27460).
Proof. exact (fun_ext (fun t : list _27460 => @lem1164971 _27459 _27460 t)). Qed.
Lemma lem1164977 {_27460 : Type'} : (@all (list _27460)) = (@all (list _27460)).
Proof. exact (eq_refl (@all (list _27460))). Qed.
Lemma lem1164984 {_27459 _27460 : Type'} : (term185 _27459 _27460) = (term186 _27459 _27460).
Proof. exact (MK_COMB (@lem1164977 _27460) (@lem1164976 _27459 _27460)). Qed.
Lemma lem1164985 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : _19608 = (term187 _27459 _27460).
Proof. exact (h1). Qed.
Lemma lem1164986 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1164987 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (_19608 P) = (term188 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1164985 _27459 _27460 _19608 h1) (@lem1164986 _27459 _27460 P)). Qed.
Lemma lem1164988 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term188 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (eq_refl (term188 _27459 _27460 P)). Qed.
Lemma lem1164989 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term189 _27459 _27460 _19608 P) = (term189 _27459 _27460 _19608 P).
Proof. exact (eq_refl (term189 _27459 _27460 _19608 P)). Qed.
Lemma lem1164990 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19608 P) = (term188 _27459 _27460 P)) = ((_19608 P) = (term100 _27459 _27460 P)).
Proof. exact (MK_COMB (@lem1164989 _27459 _27460 _19608 P) (@lem1164988 _27459 _27460 P)). Qed.
Lemma lem1164991 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (_19608 P) = (term100 _27459 _27460 P).
Proof. exact (EQ_MP (@lem1164990 _27459 _27460 _19608 P) (@lem1164987 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1164997 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (@cons _27460 h t).
Proof. exact (eq_refl (@cons _27460 h t)). Qed.
Lemma lem1164998 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1165000 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (SYM (@lem1164991 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165001 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (@lem1165000 _27459 _27460 P _19608 h1). Qed.
Lemma lem1165002 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1165003 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term190 _27459 _27460 P) = (term191 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1165002 _27459 _27460) (@lem1165001 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165004 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term192 _27459 _27460 P t') = (term193 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1165003 _27459 _27460 P _19608 h1) (@lem1164998 _27459 t')). Qed.
Lemma lem1165005 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term40 _27459 _27460 P t' h t) = (term194 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165004 _27459 _27460 P t' _19608 h1) (@lem1164997 _27460 h t)). Qed.
Lemma lem1165006 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1165011 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (y : _27460) (h' : _27459) : (P y h') = (P y h').
Proof. exact (eq_refl (P y h')). Qed.
Lemma lem1165012 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term125 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (fun_ext (fun y : _27460 => @lem1165011 _27459 _27460 P y h')). Qed.
Lemma lem1165013 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1165014 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term130 _27459 _27460 P h') = (term130 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1165013 _27460) (@lem1165012 _27459 _27460 P h')). Qed.
Lemma lem1165015 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term132 _27459 _27460 P h' t) = (term132 _27459 _27460 P h' t).
Proof. exact (MK_COMB (@lem1165014 _27459 _27460 P h') (@lem1165006 _27460 t)). Qed.
Lemma lem1165022 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term150 _27459 _27460 P h h') = (term150 _27459 _27460 P h h').
Proof. exact (eq_refl (term150 _27459 _27460 P h h')). Qed.
Lemma lem1165023 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term151 _27459 _27460 h P h' t) = (term151 _27459 _27460 h P h' t).
Proof. exact (MK_COMB (@lem1165022 _27459 _27460 P h h') (@lem1165015 _27459 _27460 P h' t)). Qed.
Lemma lem1165024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1165025 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term153 _27459 _27460 h P h' t) = (term153 _27459 _27460 h P h' t).
Proof. exact (MK_COMB (@lem1165024) (@lem1165023 _27459 _27460 h P h' t)). Qed.
Lemma lem1165026 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term154 _27459 _27460 h' P t' h t) = (term195 _27459 _27460 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165025 _27459 _27460 h P h' t) (@lem1165005 _27459 _27460 P t' h t _19608 h1)). Qed.
Lemma lem1165027 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1165028 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1165030 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (SYM (@lem1164991 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165031 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (@lem1165030 _27459 _27460 P _19608 h1). Qed.
Lemma lem1165032 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1165033 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term190 _27459 _27460 P) = (term191 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1165032 _27459 _27460) (@lem1165031 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165034 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term192 _27459 _27460 P t') = (term193 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1165033 _27459 _27460 P _19608 h1) (@lem1165028 _27459 t')). Qed.
Lemma lem1165035 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term108 _27459 _27460 P t' t) = (term196 _27459 _27460 _19608 P t' t).
Proof. exact (MK_COMB (@lem1165034 _27459 _27460 P t' _19608 h1) (@lem1165027 _27460 t)). Qed.
Lemma lem1165036 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1165041 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (y : _27460) (h' : _27459) : (P y h') = (P y h').
Proof. exact (eq_refl (P y h')). Qed.
Lemma lem1165042 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term125 _27459 _27460 P h') = (term125 _27459 _27460 P h').
Proof. exact (fun_ext (fun y : _27460 => @lem1165041 _27459 _27460 P y h')). Qed.
Lemma lem1165043 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1165044 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) : (term130 _27459 _27460 P h') = (term130 _27459 _27460 P h').
Proof. exact (MK_COMB (@lem1165043 _27460) (@lem1165042 _27459 _27460 P h')). Qed.
Lemma lem1165045 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term132 _27459 _27460 P h' t) = (term132 _27459 _27460 P h' t).
Proof. exact (MK_COMB (@lem1165044 _27459 _27460 P h') (@lem1165036 _27460 t)). Qed.
Lemma lem1165046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1165047 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term134 _27459 _27460 P h' t) = (term134 _27459 _27460 P h' t).
Proof. exact (MK_COMB (@lem1165046) (@lem1165045 _27459 _27460 P h' t)). Qed.
Lemma lem1165048 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term135 _27459 _27460 h' P t' t) = (term197 _27459 _27460 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1165047 _27459 _27460 P h' t) (@lem1165035 _27459 _27460 P t' t _19608 h1)). Qed.
Lemma lem1165065 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term118 _27459 _27460 h' P h t') = (term118 _27459 _27460 h' P h t').
Proof. exact (eq_refl (term118 _27459 _27460 h' P h t')). Qed.
Lemma lem1165066 {_27459 _27460 : Type'} (h : _27460) (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term136 _27459 _27460 h h' P t' t) = (term198 _27459 _27460 h h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1165065 _27459 _27460 h' P h t') (@lem1165048 _27459 _27460 h' P t' t _19608 h1)). Qed.
Lemma lem1165067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1165068 {_27459 _27460 : Type'} (h : _27460) (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term138 _27459 _27460 h h' P t' t) = (term199 _27459 _27460 h h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1165067) (@lem1165066 _27459 _27460 h h' P t' t _19608 h1)). Qed.
Lemma lem1165069 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : ((term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t)) = ((term198 _27459 _27460 h h' _19608 P t' t) = (term195 _27459 _27460 h' _19608 P t' h t)).
Proof. exact (MK_COMB (@lem1165068 _27459 _27460 h h' P t' t _19608 h1) (@lem1165026 _27459 _27460 h' P t' h t _19608 h1)). Qed.
Lemma lem1165074 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (@cons _27460 h t).
Proof. exact (eq_refl (@cons _27460 h t)). Qed.
Lemma lem1165075 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1165077 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (SYM (@lem1164991 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165078 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (@lem1165077 _27459 _27460 P _19608 h1). Qed.
Lemma lem1165079 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1165080 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term190 _27459 _27460 P) = (term191 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1165079 _27459 _27460) (@lem1165078 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165081 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term192 _27459 _27460 P t') = (term193 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1165080 _27459 _27460 P _19608 h1) (@lem1165075 _27459 t')). Qed.
Lemma lem1165082 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term40 _27459 _27460 P t' h t) = (term194 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165081 _27459 _27460 P t' _19608 h1) (@lem1165074 _27460 h t)). Qed.
Lemma lem1165101 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term39 _27459 _27460 h P t t') = (term39 _27459 _27460 h P t t').
Proof. exact (eq_refl (term39 _27459 _27460 h P t t')). Qed.
Lemma lem1165102 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : ((term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) = ((term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)).
Proof. exact (MK_COMB (@lem1165101 _27459 _27460 h P t t') (@lem1165082 _27459 _27460 P t' h t _19608 h1)). Qed.
Lemma lem1165103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165104 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term79 _27459 _27460 P t' h t) = (term200 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165103) (@lem1165102 _27459 _27460 P t' h t _19608 h1)). Qed.
Lemma lem1165105 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term165 _27459 _27460 h' P t' h t) = (term201 _27459 _27460 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165104 _27459 _27460 P t' h t _19608 h1) (@lem1165069 _27459 _27460 h' P t' h t _19608 h1)). Qed.
Lemma lem1165106 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1165107 {_27459 : Type'} (m : list _27459) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1165109 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (SYM (@lem1164991 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165110 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term100 _27459 _27460 P) = (_19608 P).
Proof. exact (@lem1165109 _27459 _27460 P _19608 h1). Qed.
Lemma lem1165111 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1165112 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term190 _27459 _27460 P) = (term191 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1165111 _27459 _27460) (@lem1165110 _27459 _27460 P _19608 h1)). Qed.
Lemma lem1165113 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term192 _27459 _27460 P m) = (term193 _27459 _27460 _19608 P m).
Proof. exact (MK_COMB (@lem1165112 _27459 _27460 P _19608 h1) (@lem1165107 _27459 m)). Qed.
Lemma lem1165114 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term108 _27459 _27460 P m t) = (term196 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1165113 _27459 _27460 P m _19608 h1) (@lem1165106 _27460 t)). Qed.
Lemma lem1165123 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term202 _27459 _27460 P t m) = (term202 _27459 _27460 P t m).
Proof. exact (eq_refl (term202 _27459 _27460 P t m)). Qed.
Lemma lem1165124 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : ((@ALLPAIRS _27459 _27460 P t m) = (term108 _27459 _27460 P m t)) = ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t)).
Proof. exact (MK_COMB (@lem1165123 _27459 _27460 P t m) (@lem1165114 _27459 _27460 P m t _19608 h1)). Qed.
Lemma lem1165125 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term203 _27459 _27460 P t) = (term204 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1165124 _27459 _27460 P m t _19608 h1)). Qed.
Lemma lem1165126 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1165127 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term8 _27459 _27460 P t) = (term205 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1165126 _27459) (@lem1165125 _27459 _27460 P t _19608 h1)). Qed.
Lemma lem1165128 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165129 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term10 _27459 _27460 P t) = (term206 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1165128) (@lem1165127 _27459 _27460 P t _19608 h1)). Qed.
Lemma lem1165130 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term166 _27459 _27460 h' P t' h t) = (term207 _27459 _27460 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165129 _27459 _27460 P t _19608 h1) (@lem1165105 _27459 _27460 h' P t' h t _19608 h1)). Qed.
Lemma lem1165131 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term168 _27459 _27460 P t' h t) = (term208 _27459 _27460 _19608 P t' h t).
Proof. exact (fun_ext (fun h' : _27459 => @lem1165130 _27459 _27460 h' P t' h t _19608 h1)). Qed.
Lemma lem1165132 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165133 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term170 _27459 _27460 P t' h t) = (term209 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165132 _27459) (@lem1165131 _27459 _27460 P t' h t _19608 h1)). Qed.
Lemma lem1165134 {_27459 _27460 : Type'} (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term172 _27459 _27460 t' h t) = (term210 _27459 _27460 _19608 t' h t).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165133 _27459 _27460 P t' h t _19608 h1)). Qed.
Lemma lem1165135 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165136 {_27459 _27460 : Type'} (t' : list _27459) (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term174 _27459 _27460 t' h t) = (term211 _27459 _27460 _19608 t' h t).
Proof. exact (MK_COMB (@lem1165135 _27459 _27460) (@lem1165134 _27459 _27460 t' h t _19608 h1)). Qed.
Lemma lem1165137 {_27459 _27460 : Type'} (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term176 _27459 _27460 h t) = (term212 _27459 _27460 _19608 h t).
Proof. exact (fun_ext (fun t' : list _27459 => @lem1165136 _27459 _27460 t' h t _19608 h1)). Qed.
Lemma lem1165138 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1165139 {_27459 _27460 : Type'} (h : _27460) (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term178 _27459 _27460 h t) = (term213 _27459 _27460 _19608 h t).
Proof. exact (MK_COMB (@lem1165138 _27459) (@lem1165137 _27459 _27460 h t _19608 h1)). Qed.
Lemma lem1165140 {_27459 _27460 : Type'} (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term180 _27459 _27460 t) = (term214 _27459 _27460 _19608 t).
Proof. exact (fun_ext (fun h : _27460 => @lem1165139 _27459 _27460 h t _19608 h1)). Qed.
Lemma lem1165141 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1165142 {_27459 _27460 : Type'} (t : list _27460) (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term182 _27459 _27460 t) = (term215 _27459 _27460 _19608 t).
Proof. exact (MK_COMB (@lem1165141 _27460) (@lem1165140 _27459 _27460 t _19608 h1)). Qed.
Lemma lem1165143 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term184 _27459 _27460) = (term216 _27459 _27460 _19608).
Proof. exact (fun_ext (fun t : list _27460 => @lem1165142 _27459 _27460 t _19608 h1)). Qed.
Lemma lem1165144 {_27460 : Type'} : (@all (list _27460)) = (@all (list _27460)).
Proof. exact (eq_refl (@all (list _27460))). Qed.
Lemma lem1165145 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (h1 : _19608 = (term187 _27459 _27460)) : (term186 _27459 _27460) = (term217 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165144 _27460) (@lem1165143 _27459 _27460 _19608 h1)). Qed.
Lemma lem1165146 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : term218 _27459 _27460 _19608.
Proof. exact (fun h0 : _19608 = (term187 _27459 _27460) => @lem1165145 _27459 _27460 _19608 h0). Qed.
Lemma lem1165147 {_27459 _27460 : Type'} : term219 _27459 _27460.
Proof. exact (fun _19608 : type738 _27459 _27460 => @lem1165146 _27459 _27460 _19608). Qed.
Lemma lem1165149 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term220 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1165150 {_27459 _27460 : Type'} (P : Prop) (c : type738 _27459 _27460) (Q : type188 _27459 _27460) : term221 _27459 _27460 P c Q.
Proof. exact (@lem1165149 (type738 _27459 _27460) P c Q). Qed.
Lemma lem1165151 {_27459 _27460 : Type'} : term222 _27459 _27460.
Proof. exact (@lem1165150 _27459 _27460 (term186 _27459 _27460) (term187 _27459 _27460) (term223 _27459 _27460)). Qed.
Lemma lem1165152 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term224 _27459 _27460 _19608) = (term217 _27459 _27460 _19608).
Proof. exact (eq_refl (term224 _27459 _27460 _19608)). Qed.
Lemma lem1165153 {_27459 _27460 : Type'} : (term225 _27459 _27460) = (term225 _27459 _27460).
Proof. exact (eq_refl (term225 _27459 _27460)). Qed.
Lemma lem1165154 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : ((term186 _27459 _27460) = (term224 _27459 _27460 _19608)) = ((term186 _27459 _27460) = (term217 _27459 _27460 _19608)).
Proof. exact (MK_COMB (@lem1165153 _27459 _27460) (@lem1165152 _27459 _27460 _19608)). Qed.
Lemma lem1165155 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term226 _27459 _27460 _19608) = (term226 _27459 _27460 _19608).
Proof. exact (eq_refl (term226 _27459 _27460 _19608)). Qed.
Lemma lem1165156 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term227 _27459 _27460 _19608) = (term218 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165155 _27459 _27460 _19608) (@lem1165154 _27459 _27460 _19608)). Qed.
Lemma lem1165157 {_27459 _27460 : Type'} : (term228 _27459 _27460) = (term229 _27459 _27460).
Proof. exact (fun_ext (fun _19608 : type738 _27459 _27460 => @lem1165156 _27459 _27460 _19608)). Qed.
Lemma lem1165158 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165159 {_27459 _27460 : Type'} : (term230 _27459 _27460) = (term219 _27459 _27460).
Proof. exact (MK_COMB (@lem1165158 _27459 _27460) (@lem1165157 _27459 _27460)). Qed.
Lemma lem1165160 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165161 {_27459 _27460 : Type'} : (term231 _27459 _27460) = (term232 _27459 _27460).
Proof. exact (MK_COMB (@lem1165160) (@lem1165159 _27459 _27460)). Qed.
Lemma lem1165162 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term224 _27459 _27460 _19608) = (term217 _27459 _27460 _19608).
Proof. exact (eq_refl (term224 _27459 _27460 _19608)). Qed.
Lemma lem1165163 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term226 _27459 _27460 _19608) = (term226 _27459 _27460 _19608).
Proof. exact (eq_refl (term226 _27459 _27460 _19608)). Qed.
Lemma lem1165164 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term233 _27459 _27460 _19608) = (term234 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165163 _27459 _27460 _19608) (@lem1165162 _27459 _27460 _19608)). Qed.
Lemma lem1165165 {_27459 _27460 : Type'} : (term235 _27459 _27460) = (term236 _27459 _27460).
Proof. exact (fun_ext (fun _19608 : type738 _27459 _27460 => @lem1165164 _27459 _27460 _19608)). Qed.
Lemma lem1165166 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165167 {_27459 _27460 : Type'} : (term237 _27459 _27460) = (term238 _27459 _27460).
Proof. exact (MK_COMB (@lem1165166 _27459 _27460) (@lem1165165 _27459 _27460)). Qed.
Lemma lem1165168 {_27459 _27460 : Type'} : (term225 _27459 _27460) = (term225 _27459 _27460).
Proof. exact (eq_refl (term225 _27459 _27460)). Qed.
Lemma lem1165169 {_27459 _27460 : Type'} : ((term186 _27459 _27460) = (term237 _27459 _27460)) = ((term186 _27459 _27460) = (term238 _27459 _27460)).
Proof. exact (MK_COMB (@lem1165168 _27459 _27460) (@lem1165167 _27459 _27460)). Qed.
Lemma lem1165170 {_27459 _27460 : Type'} : (term222 _27459 _27460) = (term239 _27459 _27460).
Proof. exact (MK_COMB (@lem1165161 _27459 _27460) (@lem1165169 _27459 _27460)). Qed.
Lemma lem1165171 {_27459 _27460 : Type'} : term239 _27459 _27460.
Proof. exact (EQ_MP (@lem1165170 _27459 _27460) (@lem1165151 _27459 _27460)). Qed.
Lemma lem1165172 {_27459 _27460 : Type'} : (term186 _27459 _27460) = (term238 _27459 _27460).
Proof. exact (@lem1165171 _27459 _27460 (@lem1165147 _27459 _27460)). Qed.
Lemma lem1165174 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term240 _3571 _3575 t)) = (term241 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1165175 {_27459 _27460 : Type'} (s : type738 _27459 _27460) (t : type738 _27459 _27460) : (s = (term242 _27459 _27460 t)) = (term243 _27459 _27460 s t).
Proof. exact (@lem1165174 (type1413 _27459 _27460) (type1470 _27459 _27460) s t). Qed.
Lemma lem1165176 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (_19608 = (term244 _27459 _27460)) = (term245 _27459 _27460 _19608).
Proof. exact (@lem1165175 _27459 _27460 _19608 (term187 _27459 _27460)). Qed.
Lemma lem1165177 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term188 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (eq_refl (term188 _27459 _27460 P)). Qed.
Lemma lem1165178 {_27459 _27460 : Type'} : (term244 _27459 _27460) = (term187 _27459 _27460).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165177 _27459 _27460 P)). Qed.
Lemma lem1165179 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (@eq ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608) = (@eq ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608).
Proof. exact (eq_refl (@eq ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608)). Qed.
Lemma lem1165180 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (_19608 = (term244 _27459 _27460)) = (_19608 = (term187 _27459 _27460)).
Proof. exact (MK_COMB (@lem1165179 _27459 _27460 _19608) (@lem1165178 _27459 _27460)). Qed.
Lemma lem1165181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1165182 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term246 _27459 _27460 _19608) = (term247 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165181) (@lem1165180 _27459 _27460 _19608)). Qed.
Lemma lem1165183 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term188 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (eq_refl (term188 _27459 _27460 P)). Qed.
Lemma lem1165184 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term189 _27459 _27460 _19608 P) = (term189 _27459 _27460 _19608 P).
Proof. exact (eq_refl (term189 _27459 _27460 _19608 P)). Qed.
Lemma lem1165185 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19608 P) = (term188 _27459 _27460 P)) = ((_19608 P) = (term100 _27459 _27460 P)).
Proof. exact (MK_COMB (@lem1165184 _27459 _27460 _19608 P) (@lem1165183 _27459 _27460 P)). Qed.
Lemma lem1165186 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term248 _27459 _27460 _19608) = (term249 _27459 _27460 _19608).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165185 _27459 _27460 _19608 P)). Qed.
Lemma lem1165187 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165188 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term245 _27459 _27460 _19608) = (term250 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165187 _27459 _27460) (@lem1165186 _27459 _27460 _19608)). Qed.
Lemma lem1165189 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : ((_19608 = (term244 _27459 _27460)) = (term245 _27459 _27460 _19608)) = ((_19608 = (term187 _27459 _27460)) = (term250 _27459 _27460 _19608)).
Proof. exact (MK_COMB (@lem1165182 _27459 _27460 _19608) (@lem1165188 _27459 _27460 _19608)). Qed.
Lemma lem1165190 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (_19608 = (term187 _27459 _27460)) = (term250 _27459 _27460 _19608).
Proof. exact (EQ_MP (@lem1165189 _27459 _27460 _19608) (@lem1165176 _27459 _27460 _19608)). Qed.
Lemma lem1165192 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term240 _3571 _3575 t)) = (term241 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1165193 {_27459 _27460 : Type'} (s : type1413 _27459 _27460) (t : type1413 _27459 _27460) : (s = (term251 _27459 _27460 t)) = (term252 _27459 _27460 s t).
Proof. exact (@lem1165192 (_27460 -> Prop) _27459 s t). Qed.
Lemma lem1165194 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19608 P) = (term126 _27459 _27460 P)) = (term253 _27459 _27460 _19608 P).
Proof. exact (@lem1165193 _27459 _27460 (_19608 P) (term100 _27459 _27460 P)). Qed.
Lemma lem1165195 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1165196 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term126 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165195 _27459 _27460 P x)). Qed.
Lemma lem1165197 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term189 _27459 _27460 _19608 P) = (term189 _27459 _27460 _19608 P).
Proof. exact (eq_refl (term189 _27459 _27460 _19608 P)). Qed.
Lemma lem1165198 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19608 P) = (term126 _27459 _27460 P)) = ((_19608 P) = (term100 _27459 _27460 P)).
Proof. exact (MK_COMB (@lem1165197 _27459 _27460 _19608 P) (@lem1165196 _27459 _27460 P)). Qed.
Lemma lem1165199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1165200 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term254 _27459 _27460 _19608 P) = (term255 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1165199) (@lem1165198 _27459 _27460 _19608 P)). Qed.
Lemma lem1165201 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1165202 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term256 _27459 _27460 _19608 P x) = (term256 _27459 _27460 _19608 P x).
Proof. exact (eq_refl (term256 _27459 _27460 _19608 P x)). Qed.
Lemma lem1165203 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19608 P x) = (term105 _27459 _27460 P x)) = ((_19608 P x) = (term125 _27459 _27460 P x)).
Proof. exact (MK_COMB (@lem1165202 _27459 _27460 _19608 P x) (@lem1165201 _27459 _27460 P x)). Qed.
Lemma lem1165204 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term257 _27459 _27460 _19608 P) = (term258 _27459 _27460 _19608 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165203 _27459 _27460 _19608 P x)). Qed.
Lemma lem1165205 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165206 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term253 _27459 _27460 _19608 P) = (term259 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1165205 _27459) (@lem1165204 _27459 _27460 _19608 P)). Qed.
Lemma lem1165207 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (((_19608 P) = (term126 _27459 _27460 P)) = (term253 _27459 _27460 _19608 P)) = (((_19608 P) = (term100 _27459 _27460 P)) = (term259 _27459 _27460 _19608 P)).
Proof. exact (MK_COMB (@lem1165200 _27459 _27460 _19608 P) (@lem1165206 _27459 _27460 _19608 P)). Qed.
Lemma lem1165208 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19608 P) = (term100 _27459 _27460 P)) = (term259 _27459 _27460 _19608 P).
Proof. exact (EQ_MP (@lem1165207 _27459 _27460 _19608 P) (@lem1165194 _27459 _27460 _19608 P)). Qed.
Lemma lem1165209 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19608 P x) = (term125 _27459 _27460 P x)) = ((_19608 P x) = (term125 _27459 _27460 P x)).
Proof. exact (eq_refl ((_19608 P x) = (term125 _27459 _27460 P x))). Qed.
Lemma lem1165210 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term258 _27459 _27460 _19608 P) = (term258 _27459 _27460 _19608 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165209 _27459 _27460 _19608 P x)). Qed.
Lemma lem1165211 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165212 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term259 _27459 _27460 _19608 P) = (term259 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1165211 _27459) (@lem1165210 _27459 _27460 _19608 P)). Qed.
Lemma lem1165213 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19608 P) = (term100 _27459 _27460 P)) = (term259 _27459 _27460 _19608 P).
Proof. exact (TRANS (@lem1165208 _27459 _27460 _19608 P) (@lem1165212 _27459 _27460 _19608 P)). Qed.
Lemma lem1165214 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term249 _27459 _27460 _19608) = (term260 _27459 _27460 _19608).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165213 _27459 _27460 _19608 P)). Qed.
Lemma lem1165215 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165216 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term250 _27459 _27460 _19608) = (term261 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165215 _27459 _27460) (@lem1165214 _27459 _27460 _19608)). Qed.
Lemma lem1165217 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (_19608 = (term187 _27459 _27460)) = (term261 _27459 _27460 _19608).
Proof. exact (TRANS (@lem1165190 _27459 _27460 _19608) (@lem1165216 _27459 _27460 _19608)). Qed.
Lemma lem1165218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165219 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term226 _27459 _27460 _19608) = (term262 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165218) (@lem1165217 _27459 _27460 _19608)). Qed.
Lemma lem1165220 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term217 _27459 _27460 _19608) = (term217 _27459 _27460 _19608).
Proof. exact (eq_refl (term217 _27459 _27460 _19608)). Qed.
Lemma lem1165221 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) : (term234 _27459 _27460 _19608) = (term263 _27459 _27460 _19608).
Proof. exact (MK_COMB (@lem1165219 _27459 _27460 _19608) (@lem1165220 _27459 _27460 _19608)). Qed.
Lemma lem1165222 {_27459 _27460 : Type'} : (term236 _27459 _27460) = (term264 _27459 _27460).
Proof. exact (fun_ext (fun _19608 : type738 _27459 _27460 => @lem1165221 _27459 _27460 _19608)). Qed.
Lemma lem1165223 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165224 {_27459 _27460 : Type'} : (term238 _27459 _27460) = (term265 _27459 _27460).
Proof. exact (MK_COMB (@lem1165223 _27459 _27460) (@lem1165222 _27459 _27460)). Qed.
Lemma lem1165225 {_27459 _27460 : Type'} : (term225 _27459 _27460) = (term225 _27459 _27460).
Proof. exact (eq_refl (term225 _27459 _27460)). Qed.
Lemma lem1165226 {_27459 _27460 : Type'} : ((term186 _27459 _27460) = (term238 _27459 _27460)) = ((term186 _27459 _27460) = (term265 _27459 _27460)).
Proof. exact (MK_COMB (@lem1165225 _27459 _27460) (@lem1165224 _27459 _27460)). Qed.
Lemma lem1165227 {_27459 _27460 : Type'} : (term186 _27459 _27460) = (term265 _27459 _27460).
Proof. exact (EQ_MP (@lem1165226 _27459 _27460) (@lem1165172 _27459 _27460)). Qed.
Lemma lem1165228 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : _19609 = (term187 _27459 _27460).
Proof. exact (h1). Qed.
Lemma lem1165229 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1165230 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (_19609 P) = (term188 _27459 _27460 P).
Proof. exact (MK_COMB (@lem1165228 _27459 _27460 _19609 h1) (@lem1165229 _27459 _27460 P)). Qed.
Lemma lem1165231 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term188 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (eq_refl (term188 _27459 _27460 P)). Qed.
Lemma lem1165232 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term189 _27459 _27460 _19609 P) = (term189 _27459 _27460 _19609 P).
Proof. exact (eq_refl (term189 _27459 _27460 _19609 P)). Qed.
Lemma lem1165233 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19609 P) = (term188 _27459 _27460 P)) = ((_19609 P) = (term100 _27459 _27460 P)).
Proof. exact (MK_COMB (@lem1165232 _27459 _27460 _19609 P) (@lem1165231 _27459 _27460 P)). Qed.
Lemma lem1165234 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (_19609 P) = (term100 _27459 _27460 P).
Proof. exact (EQ_MP (@lem1165233 _27459 _27460 _19609 P) (@lem1165230 _27459 _27460 P _19609 h1)). Qed.
Lemma lem1165235 {_27459 : Type'} (x : _27459) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1165236 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (_19609 P x) = (term105 _27459 _27460 P x).
Proof. exact (MK_COMB (@lem1165234 _27459 _27460 P _19609 h1) (@lem1165235 _27459 x)). Qed.
Lemma lem1165237 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1165238 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term256 _27459 _27460 _19609 P x) = (term256 _27459 _27460 _19609 P x).
Proof. exact (eq_refl (term256 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165239 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19609 P x) = (term105 _27459 _27460 P x)) = ((_19609 P x) = (term125 _27459 _27460 P x)).
Proof. exact (MK_COMB (@lem1165238 _27459 _27460 _19609 P x) (@lem1165237 _27459 _27460 P x)). Qed.
Lemma lem1165240 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (_19609 P x) = (term125 _27459 _27460 P x).
Proof. exact (EQ_MP (@lem1165239 _27459 _27460 _19609 P x) (@lem1165236 _27459 _27460 P x _19609 h1)). Qed.
Lemma lem1165254 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term194 _27459 _27460 _19608 P t' h t).
Proof. exact (eq_refl (term194 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1165255 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1165257 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P x) = (_19609 P x).
Proof. exact (SYM (@lem1165240 _27459 _27460 P x _19609 h1)). Qed.
Lemma lem1165258 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P x) = (_19609 P x).
Proof. exact (@lem1165257 _27459 _27460 P x _19609 h1). Qed.
Lemma lem1165259 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P h') = (_19609 P h').
Proof. exact (@lem1165258 _27459 _27460 P h' _19609 h1). Qed.
Lemma lem1165260 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1165261 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term130 _27459 _27460 P h') = (term266 _27459 _27460 _19609 P h').
Proof. exact (MK_COMB (@lem1165260 _27460) (@lem1165259 _27459 _27460 P h' _19609 h1)). Qed.
Lemma lem1165262 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term132 _27459 _27460 P h' t) = (term267 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1165261 _27459 _27460 P h' _19609 h1) (@lem1165255 _27460 t)). Qed.
Lemma lem1165269 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term150 _27459 _27460 P h h') = (term150 _27459 _27460 P h h').
Proof. exact (eq_refl (term150 _27459 _27460 P h h')). Qed.
Lemma lem1165270 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term151 _27459 _27460 h P h' t) = (term268 _27459 _27460 h _19609 P h' t).
Proof. exact (MK_COMB (@lem1165269 _27459 _27460 P h h') (@lem1165262 _27459 _27460 P h' t _19609 h1)). Qed.
Lemma lem1165271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1165272 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term153 _27459 _27460 h P h' t) = (term269 _27459 _27460 h _19609 P h' t).
Proof. exact (MK_COMB (@lem1165271) (@lem1165270 _27459 _27460 h P h' t _19609 h1)). Qed.
Lemma lem1165273 {_27459 _27460 : Type'} (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term195 _27459 _27460 h' _19608 P t' h t) = (term270 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165272 _27459 _27460 h P h' t _19609 h1) (@lem1165254 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1165282 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P t' t) = (term196 _27459 _27460 _19608 P t' t).
Proof. exact (eq_refl (term196 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1165283 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1165285 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P x) = (_19609 P x).
Proof. exact (SYM (@lem1165240 _27459 _27460 P x _19609 h1)). Qed.
Lemma lem1165286 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P x) = (_19609 P x).
Proof. exact (@lem1165285 _27459 _27460 P x _19609 h1). Qed.
Lemma lem1165287 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P h') = (_19609 P h').
Proof. exact (@lem1165286 _27459 _27460 P h' _19609 h1). Qed.
Lemma lem1165288 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1165289 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term130 _27459 _27460 P h') = (term266 _27459 _27460 _19609 P h').
Proof. exact (MK_COMB (@lem1165288 _27460) (@lem1165287 _27459 _27460 P h' _19609 h1)). Qed.
Lemma lem1165290 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term132 _27459 _27460 P h' t) = (term267 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1165289 _27459 _27460 P h' _19609 h1) (@lem1165283 _27460 t)). Qed.
Lemma lem1165291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1165292 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term134 _27459 _27460 P h' t) = (term271 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1165291) (@lem1165290 _27459 _27460 P h' t _19609 h1)). Qed.
Lemma lem1165293 {_27459 _27460 : Type'} (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term197 _27459 _27460 h' _19608 P t' t) = (term272 _27459 _27460 _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1165292 _27459 _27460 P h' t _19609 h1) (@lem1165282 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1165310 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term118 _27459 _27460 h' P h t') = (term118 _27459 _27460 h' P h t').
Proof. exact (eq_refl (term118 _27459 _27460 h' P h t')). Qed.
Lemma lem1165311 {_27459 _27460 : Type'} (h : _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term198 _27459 _27460 h h' _19608 P t' t) = (term273 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1165310 _27459 _27460 h' P h t') (@lem1165293 _27459 _27460 h' _19608 P t' t _19609 h1)). Qed.
Lemma lem1165312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1165313 {_27459 _27460 : Type'} (h : _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term199 _27459 _27460 h h' _19608 P t' t) = (term274 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1165312) (@lem1165311 _27459 _27460 h h' _19608 P t' t _19609 h1)). Qed.
Lemma lem1165314 {_27459 _27460 : Type'} (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : ((term198 _27459 _27460 h h' _19608 P t' t) = (term195 _27459 _27460 h' _19608 P t' h t)) = ((term273 _27459 _27460 h _19609 h' _19608 P t' t) = (term270 _27459 _27460 _19609 h' _19608 P t' h t)).
Proof. exact (MK_COMB (@lem1165313 _27459 _27460 h h' _19608 P t' t _19609 h1) (@lem1165273 _27459 _27460 h' _19608 P t' h t _19609 h1)). Qed.
Lemma lem1165349 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term200 _27459 _27460 _19608 P t' h t) = (term200 _27459 _27460 _19608 P t' h t).
Proof. exact (eq_refl (term200 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1165350 {_27459 _27460 : Type'} (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term201 _27459 _27460 h' _19608 P t' h t) = (term275 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165349 _27459 _27460 _19608 P t' h t) (@lem1165314 _27459 _27460 h' _19608 P t' h t _19609 h1)). Qed.
Lemma lem1165369 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t)) = ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t)).
Proof. exact (eq_refl ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t))). Qed.
Lemma lem1165370 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term204 _27459 _27460 _19608 P t) = (term204 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1165369 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1165371 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1165372 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term205 _27459 _27460 _19608 P t) = (term205 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1165371 _27459) (@lem1165370 _27459 _27460 _19608 P t)). Qed.
Lemma lem1165373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165374 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term206 _27459 _27460 _19608 P t) = (term206 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1165373) (@lem1165372 _27459 _27460 _19608 P t)). Qed.
Lemma lem1165375 {_27459 _27460 : Type'} (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term207 _27459 _27460 h' _19608 P t' h t) = (term276 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165374 _27459 _27460 _19608 P t) (@lem1165350 _27459 _27460 h' _19608 P t' h t _19609 h1)). Qed.
Lemma lem1165376 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term208 _27459 _27460 _19608 P t' h t) = (term277 _27459 _27460 _19609 _19608 P t' h t).
Proof. exact (fun_ext (fun h' : _27459 => @lem1165375 _27459 _27460 h' _19608 P t' h t _19609 h1)). Qed.
Lemma lem1165377 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165378 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term209 _27459 _27460 _19608 P t' h t) = (term278 _27459 _27460 _19609 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165377 _27459) (@lem1165376 _27459 _27460 _19608 P t' h t _19609 h1)). Qed.
Lemma lem1165379 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term210 _27459 _27460 _19608 t' h t) = (term279 _27459 _27460 _19609 _19608 t' h t).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165378 _27459 _27460 _19608 P t' h t _19609 h1)). Qed.
Lemma lem1165380 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165381 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term211 _27459 _27460 _19608 t' h t) = (term280 _27459 _27460 _19609 _19608 t' h t).
Proof. exact (MK_COMB (@lem1165380 _27459 _27460) (@lem1165379 _27459 _27460 _19608 t' h t _19609 h1)). Qed.
Lemma lem1165382 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term212 _27459 _27460 _19608 h t) = (term281 _27459 _27460 _19609 _19608 h t).
Proof. exact (fun_ext (fun t' : list _27459 => @lem1165381 _27459 _27460 _19608 t' h t _19609 h1)). Qed.
Lemma lem1165383 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1165384 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (h : _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term213 _27459 _27460 _19608 h t) = (term282 _27459 _27460 _19609 _19608 h t).
Proof. exact (MK_COMB (@lem1165383 _27459) (@lem1165382 _27459 _27460 _19608 h t _19609 h1)). Qed.
Lemma lem1165385 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term214 _27459 _27460 _19608 t) = (term283 _27459 _27460 _19609 _19608 t).
Proof. exact (fun_ext (fun h : _27460 => @lem1165384 _27459 _27460 _19608 h t _19609 h1)). Qed.
Lemma lem1165386 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1165387 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (t : list _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term215 _27459 _27460 _19608 t) = (term284 _27459 _27460 _19609 _19608 t).
Proof. exact (MK_COMB (@lem1165386 _27460) (@lem1165385 _27459 _27460 _19608 t _19609 h1)). Qed.
Lemma lem1165388 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term216 _27459 _27460 _19608) = (term285 _27459 _27460 _19609 _19608).
Proof. exact (fun_ext (fun t : list _27460 => @lem1165387 _27459 _27460 _19608 t _19609 h1)). Qed.
Lemma lem1165389 {_27460 : Type'} : (@all (list _27460)) = (@all (list _27460)).
Proof. exact (eq_refl (@all (list _27460))). Qed.
Lemma lem1165390 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term217 _27459 _27460 _19608) = (term286 _27459 _27460 _19609 _19608).
Proof. exact (MK_COMB (@lem1165389 _27460) (@lem1165388 _27459 _27460 _19608 _19609 h1)). Qed.
Lemma lem1165392 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P x) = (_19609 P x).
Proof. exact (SYM (@lem1165240 _27459 _27460 P x _19609 h1)). Qed.
Lemma lem1165393 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term125 _27459 _27460 P x) = (_19609 P x).
Proof. exact (@lem1165392 _27459 _27460 P x _19609 h1). Qed.
Lemma lem1165400 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term256 _27459 _27460 _19608 P x) = (term256 _27459 _27460 _19608 P x).
Proof. exact (eq_refl (term256 _27459 _27460 _19608 P x)). Qed.
Lemma lem1165401 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : ((_19608 P x) = (term125 _27459 _27460 P x)) = ((_19608 P x) = (_19609 P x)).
Proof. exact (MK_COMB (@lem1165400 _27459 _27460 _19608 P x) (@lem1165393 _27459 _27460 P x _19609 h1)). Qed.
Lemma lem1165402 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term258 _27459 _27460 _19608 P) = (term287 _27459 _27460 _19608 _19609 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165401 _27459 _27460 _19608 P x _19609 h1)). Qed.
Lemma lem1165403 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165404 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term259 _27459 _27460 _19608 P) = (term288 _27459 _27460 _19608 _19609 P).
Proof. exact (MK_COMB (@lem1165403 _27459) (@lem1165402 _27459 _27460 _19608 P _19609 h1)). Qed.
Lemma lem1165405 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term260 _27459 _27460 _19608) = (term289 _27459 _27460 _19608 _19609).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165404 _27459 _27460 _19608 P _19609 h1)). Qed.
Lemma lem1165406 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165407 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term261 _27459 _27460 _19608) = (term290 _27459 _27460 _19608 _19609).
Proof. exact (MK_COMB (@lem1165406 _27459 _27460) (@lem1165405 _27459 _27460 _19608 _19609 h1)). Qed.
Lemma lem1165408 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165409 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term262 _27459 _27460 _19608) = (term291 _27459 _27460 _19608 _19609).
Proof. exact (MK_COMB (@lem1165408) (@lem1165407 _27459 _27460 _19608 _19609 h1)). Qed.
Lemma lem1165410 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term263 _27459 _27460 _19608) = (term292 _27459 _27460 _19609 _19608).
Proof. exact (MK_COMB (@lem1165409 _27459 _27460 _19608 _19609 h1) (@lem1165390 _27459 _27460 _19608 _19609 h1)). Qed.
Lemma lem1165411 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term264 _27459 _27460) = (term293 _27459 _27460 _19609).
Proof. exact (fun_ext (fun _19608 : type738 _27459 _27460 => @lem1165410 _27459 _27460 _19608 _19609 h1)). Qed.
Lemma lem1165412 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165413 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h1 : _19609 = (term187 _27459 _27460)) : (term265 _27459 _27460) = (term294 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165412 _27459 _27460) (@lem1165411 _27459 _27460 _19609 h1)). Qed.
Lemma lem1165414 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : term295 _27459 _27460 _19609.
Proof. exact (fun h0 : _19609 = (term187 _27459 _27460) => @lem1165413 _27459 _27460 _19609 h0). Qed.
Lemma lem1165415 {_27459 _27460 : Type'} : term296 _27459 _27460.
Proof. exact (fun _19609 : type738 _27459 _27460 => @lem1165414 _27459 _27460 _19609). Qed.
Lemma lem1165417 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term220 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1165418 {_27459 _27460 : Type'} (P : Prop) (c : type738 _27459 _27460) (Q : type188 _27459 _27460) : term221 _27459 _27460 P c Q.
Proof. exact (@lem1165417 (type738 _27459 _27460) P c Q). Qed.
Lemma lem1165419 {_27459 _27460 : Type'} : term297 _27459 _27460.
Proof. exact (@lem1165418 _27459 _27460 (term265 _27459 _27460) (term187 _27459 _27460) (term298 _27459 _27460)). Qed.
Lemma lem1165420 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term299 _27459 _27460 _19609) = (term294 _27459 _27460 _19609).
Proof. exact (eq_refl (term299 _27459 _27460 _19609)). Qed.
Lemma lem1165421 {_27459 _27460 : Type'} : (term300 _27459 _27460) = (term300 _27459 _27460).
Proof. exact (eq_refl (term300 _27459 _27460)). Qed.
Lemma lem1165422 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : ((term265 _27459 _27460) = (term299 _27459 _27460 _19609)) = ((term265 _27459 _27460) = (term294 _27459 _27460 _19609)).
Proof. exact (MK_COMB (@lem1165421 _27459 _27460) (@lem1165420 _27459 _27460 _19609)). Qed.
Lemma lem1165423 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term226 _27459 _27460 _19609) = (term226 _27459 _27460 _19609).
Proof. exact (eq_refl (term226 _27459 _27460 _19609)). Qed.
Lemma lem1165424 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term301 _27459 _27460 _19609) = (term295 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165423 _27459 _27460 _19609) (@lem1165422 _27459 _27460 _19609)). Qed.
Lemma lem1165425 {_27459 _27460 : Type'} : (term302 _27459 _27460) = (term303 _27459 _27460).
Proof. exact (fun_ext (fun _19609 : type738 _27459 _27460 => @lem1165424 _27459 _27460 _19609)). Qed.
Lemma lem1165426 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165427 {_27459 _27460 : Type'} : (term304 _27459 _27460) = (term296 _27459 _27460).
Proof. exact (MK_COMB (@lem1165426 _27459 _27460) (@lem1165425 _27459 _27460)). Qed.
Lemma lem1165428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165429 {_27459 _27460 : Type'} : (term305 _27459 _27460) = (term306 _27459 _27460).
Proof. exact (MK_COMB (@lem1165428) (@lem1165427 _27459 _27460)). Qed.
Lemma lem1165430 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term299 _27459 _27460 _19609) = (term294 _27459 _27460 _19609).
Proof. exact (eq_refl (term299 _27459 _27460 _19609)). Qed.
Lemma lem1165431 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term226 _27459 _27460 _19609) = (term226 _27459 _27460 _19609).
Proof. exact (eq_refl (term226 _27459 _27460 _19609)). Qed.
Lemma lem1165432 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term307 _27459 _27460 _19609) = (term308 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165431 _27459 _27460 _19609) (@lem1165430 _27459 _27460 _19609)). Qed.
Lemma lem1165433 {_27459 _27460 : Type'} : (term309 _27459 _27460) = (term310 _27459 _27460).
Proof. exact (fun_ext (fun _19609 : type738 _27459 _27460 => @lem1165432 _27459 _27460 _19609)). Qed.
Lemma lem1165434 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165435 {_27459 _27460 : Type'} : (term311 _27459 _27460) = (term312 _27459 _27460).
Proof. exact (MK_COMB (@lem1165434 _27459 _27460) (@lem1165433 _27459 _27460)). Qed.
Lemma lem1165436 {_27459 _27460 : Type'} : (term300 _27459 _27460) = (term300 _27459 _27460).
Proof. exact (eq_refl (term300 _27459 _27460)). Qed.
Lemma lem1165437 {_27459 _27460 : Type'} : ((term265 _27459 _27460) = (term311 _27459 _27460)) = ((term265 _27459 _27460) = (term312 _27459 _27460)).
Proof. exact (MK_COMB (@lem1165436 _27459 _27460) (@lem1165435 _27459 _27460)). Qed.
Lemma lem1165438 {_27459 _27460 : Type'} : (term297 _27459 _27460) = (term313 _27459 _27460).
Proof. exact (MK_COMB (@lem1165429 _27459 _27460) (@lem1165437 _27459 _27460)). Qed.
Lemma lem1165439 {_27459 _27460 : Type'} : term313 _27459 _27460.
Proof. exact (EQ_MP (@lem1165438 _27459 _27460) (@lem1165419 _27459 _27460)). Qed.
Lemma lem1165440 {_27459 _27460 : Type'} : (term265 _27459 _27460) = (term312 _27459 _27460).
Proof. exact (@lem1165439 _27459 _27460 (@lem1165415 _27459 _27460)). Qed.
Lemma lem1165442 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term240 _3571 _3575 t)) = (term241 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1165443 {_27459 _27460 : Type'} (s : type738 _27459 _27460) (t : type738 _27459 _27460) : (s = (term242 _27459 _27460 t)) = (term243 _27459 _27460 s t).
Proof. exact (@lem1165442 (type1413 _27459 _27460) (type1470 _27459 _27460) s t). Qed.
Lemma lem1165444 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (_19609 = (term244 _27459 _27460)) = (term245 _27459 _27460 _19609).
Proof. exact (@lem1165443 _27459 _27460 _19609 (term187 _27459 _27460)). Qed.
Lemma lem1165445 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term188 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (eq_refl (term188 _27459 _27460 P)). Qed.
Lemma lem1165446 {_27459 _27460 : Type'} : (term244 _27459 _27460) = (term187 _27459 _27460).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165445 _27459 _27460 P)). Qed.
Lemma lem1165447 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (@eq ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609) = (@eq ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609).
Proof. exact (eq_refl (@eq ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609)). Qed.
Lemma lem1165448 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (_19609 = (term244 _27459 _27460)) = (_19609 = (term187 _27459 _27460)).
Proof. exact (MK_COMB (@lem1165447 _27459 _27460 _19609) (@lem1165446 _27459 _27460)). Qed.
Lemma lem1165449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1165450 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term246 _27459 _27460 _19609) = (term247 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165449) (@lem1165448 _27459 _27460 _19609)). Qed.
Lemma lem1165451 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term188 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (eq_refl (term188 _27459 _27460 P)). Qed.
Lemma lem1165452 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term189 _27459 _27460 _19609 P) = (term189 _27459 _27460 _19609 P).
Proof. exact (eq_refl (term189 _27459 _27460 _19609 P)). Qed.
Lemma lem1165453 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19609 P) = (term188 _27459 _27460 P)) = ((_19609 P) = (term100 _27459 _27460 P)).
Proof. exact (MK_COMB (@lem1165452 _27459 _27460 _19609 P) (@lem1165451 _27459 _27460 P)). Qed.
Lemma lem1165454 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term248 _27459 _27460 _19609) = (term249 _27459 _27460 _19609).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165453 _27459 _27460 _19609 P)). Qed.
Lemma lem1165455 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165456 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term245 _27459 _27460 _19609) = (term250 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165455 _27459 _27460) (@lem1165454 _27459 _27460 _19609)). Qed.
Lemma lem1165457 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : ((_19609 = (term244 _27459 _27460)) = (term245 _27459 _27460 _19609)) = ((_19609 = (term187 _27459 _27460)) = (term250 _27459 _27460 _19609)).
Proof. exact (MK_COMB (@lem1165450 _27459 _27460 _19609) (@lem1165456 _27459 _27460 _19609)). Qed.
Lemma lem1165458 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (_19609 = (term187 _27459 _27460)) = (term250 _27459 _27460 _19609).
Proof. exact (EQ_MP (@lem1165457 _27459 _27460 _19609) (@lem1165444 _27459 _27460 _19609)). Qed.
Lemma lem1165460 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term240 _3571 _3575 t)) = (term241 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1165461 {_27459 _27460 : Type'} (s : type1413 _27459 _27460) (t : type1413 _27459 _27460) : (s = (term251 _27459 _27460 t)) = (term252 _27459 _27460 s t).
Proof. exact (@lem1165460 (_27460 -> Prop) _27459 s t). Qed.
Lemma lem1165462 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19609 P) = (term126 _27459 _27460 P)) = (term253 _27459 _27460 _19609 P).
Proof. exact (@lem1165461 _27459 _27460 (_19609 P) (term100 _27459 _27460 P)). Qed.
Lemma lem1165463 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1165464 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (term126 _27459 _27460 P) = (term100 _27459 _27460 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165463 _27459 _27460 P x)). Qed.
Lemma lem1165465 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term189 _27459 _27460 _19609 P) = (term189 _27459 _27460 _19609 P).
Proof. exact (eq_refl (term189 _27459 _27460 _19609 P)). Qed.
Lemma lem1165466 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19609 P) = (term126 _27459 _27460 P)) = ((_19609 P) = (term100 _27459 _27460 P)).
Proof. exact (MK_COMB (@lem1165465 _27459 _27460 _19609 P) (@lem1165464 _27459 _27460 P)). Qed.
Lemma lem1165467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1165468 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term254 _27459 _27460 _19609 P) = (term255 _27459 _27460 _19609 P).
Proof. exact (MK_COMB (@lem1165467) (@lem1165466 _27459 _27460 _19609 P)). Qed.
Lemma lem1165469 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term105 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (eq_refl (term105 _27459 _27460 P x)). Qed.
Lemma lem1165470 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term256 _27459 _27460 _19609 P x) = (term256 _27459 _27460 _19609 P x).
Proof. exact (eq_refl (term256 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165471 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19609 P x) = (term105 _27459 _27460 P x)) = ((_19609 P x) = (term125 _27459 _27460 P x)).
Proof. exact (MK_COMB (@lem1165470 _27459 _27460 _19609 P x) (@lem1165469 _27459 _27460 P x)). Qed.
Lemma lem1165472 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term257 _27459 _27460 _19609 P) = (term258 _27459 _27460 _19609 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165471 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165473 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165474 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term253 _27459 _27460 _19609 P) = (term259 _27459 _27460 _19609 P).
Proof. exact (MK_COMB (@lem1165473 _27459) (@lem1165472 _27459 _27460 _19609 P)). Qed.
Lemma lem1165475 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (((_19609 P) = (term126 _27459 _27460 P)) = (term253 _27459 _27460 _19609 P)) = (((_19609 P) = (term100 _27459 _27460 P)) = (term259 _27459 _27460 _19609 P)).
Proof. exact (MK_COMB (@lem1165468 _27459 _27460 _19609 P) (@lem1165474 _27459 _27460 _19609 P)). Qed.
Lemma lem1165476 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19609 P) = (term100 _27459 _27460 P)) = (term259 _27459 _27460 _19609 P).
Proof. exact (EQ_MP (@lem1165475 _27459 _27460 _19609 P) (@lem1165462 _27459 _27460 _19609 P)). Qed.
Lemma lem1165478 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term240 _3571 _3575 t)) = (term241 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1165479 {_27460 : Type'} (s : _27460 -> Prop) (t : _27460 -> Prop) : (s = (term314 _27460 t)) = (term315 _27460 s t).
Proof. exact (@lem1165478 Prop _27460 s t). Qed.
Lemma lem1165480 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19609 P x) = (term146 _27459 _27460 P x)) = (term316 _27459 _27460 _19609 P x).
Proof. exact (@lem1165479 _27460 (_19609 P x) (term125 _27459 _27460 P x)). Qed.
Lemma lem1165481 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (y : _27460) (x : _27459) : (term143 _27459 _27460 P x y) = (P y x).
Proof. exact (eq_refl (term143 _27459 _27460 P x y)). Qed.
Lemma lem1165482 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (x : _27459) : (term146 _27459 _27460 P x) = (term125 _27459 _27460 P x).
Proof. exact (fun_ext (fun y : _27460 => @lem1165481 _27459 _27460 P y x)). Qed.
Lemma lem1165483 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term256 _27459 _27460 _19609 P x) = (term256 _27459 _27460 _19609 P x).
Proof. exact (eq_refl (term256 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165484 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19609 P x) = (term146 _27459 _27460 P x)) = ((_19609 P x) = (term125 _27459 _27460 P x)).
Proof. exact (MK_COMB (@lem1165483 _27459 _27460 _19609 P x) (@lem1165482 _27459 _27460 P x)). Qed.
Lemma lem1165485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1165486 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term317 _27459 _27460 _19609 P x) = (term318 _27459 _27460 _19609 P x).
Proof. exact (MK_COMB (@lem1165485) (@lem1165484 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165487 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (y : _27460) (x : _27459) : (term143 _27459 _27460 P x y) = (P y x).
Proof. exact (eq_refl (term143 _27459 _27460 P x y)). Qed.
Lemma lem1165488 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) (y : _27460) : (term319 _27459 _27460 _19609 P x y) = (term319 _27459 _27460 _19609 P x y).
Proof. exact (eq_refl (term319 _27459 _27460 _19609 P x y)). Qed.
Lemma lem1165489 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (y : _27460) (x : _27459) : ((_19609 P x y) = (term143 _27459 _27460 P x y)) = ((_19609 P x y) = (P y x)).
Proof. exact (MK_COMB (@lem1165488 _27459 _27460 _19609 P x y) (@lem1165487 _27459 _27460 P y x)). Qed.
Lemma lem1165490 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term320 _27459 _27460 _19609 P x) = (term321 _27459 _27460 _19609 P x).
Proof. exact (fun_ext (fun y : _27460 => @lem1165489 _27459 _27460 _19609 P y x)). Qed.
Lemma lem1165491 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1165492 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term316 _27459 _27460 _19609 P x) = (term322 _27459 _27460 _19609 P x).
Proof. exact (MK_COMB (@lem1165491 _27460) (@lem1165490 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165493 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (((_19609 P x) = (term146 _27459 _27460 P x)) = (term316 _27459 _27460 _19609 P x)) = (((_19609 P x) = (term125 _27459 _27460 P x)) = (term322 _27459 _27460 _19609 P x)).
Proof. exact (MK_COMB (@lem1165486 _27459 _27460 _19609 P x) (@lem1165492 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165494 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19609 P x) = (term125 _27459 _27460 P x)) = (term322 _27459 _27460 _19609 P x).
Proof. exact (EQ_MP (@lem1165493 _27459 _27460 _19609 P x) (@lem1165480 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165495 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (y : _27460) (x : _27459) : ((_19609 P x y) = (P y x)) = ((_19609 P x y) = (P y x)).
Proof. exact (eq_refl ((_19609 P x y) = (P y x))). Qed.
Lemma lem1165496 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term321 _27459 _27460 _19609 P x) = (term321 _27459 _27460 _19609 P x).
Proof. exact (fun_ext (fun y : _27460 => @lem1165495 _27459 _27460 _19609 P y x)). Qed.
Lemma lem1165497 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1165498 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term322 _27459 _27460 _19609 P x) = (term322 _27459 _27460 _19609 P x).
Proof. exact (MK_COMB (@lem1165497 _27460) (@lem1165496 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165499 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19609 P x) = (term125 _27459 _27460 P x)) = (term322 _27459 _27460 _19609 P x).
Proof. exact (TRANS (@lem1165494 _27459 _27460 _19609 P x) (@lem1165498 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165500 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term258 _27459 _27460 _19609 P) = (term323 _27459 _27460 _19609 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165499 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165501 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165502 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term259 _27459 _27460 _19609 P) = (term324 _27459 _27460 _19609 P).
Proof. exact (MK_COMB (@lem1165501 _27459) (@lem1165500 _27459 _27460 _19609 P)). Qed.
Lemma lem1165503 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : ((_19609 P) = (term100 _27459 _27460 P)) = (term324 _27459 _27460 _19609 P).
Proof. exact (TRANS (@lem1165476 _27459 _27460 _19609 P) (@lem1165502 _27459 _27460 _19609 P)). Qed.
Lemma lem1165504 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term249 _27459 _27460 _19609) = (term325 _27459 _27460 _19609).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165503 _27459 _27460 _19609 P)). Qed.
Lemma lem1165505 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165506 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term250 _27459 _27460 _19609) = (term326 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165505 _27459 _27460) (@lem1165504 _27459 _27460 _19609)). Qed.
Lemma lem1165507 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (_19609 = (term187 _27459 _27460)) = (term326 _27459 _27460 _19609).
Proof. exact (TRANS (@lem1165458 _27459 _27460 _19609) (@lem1165506 _27459 _27460 _19609)). Qed.
Lemma lem1165508 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165509 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term226 _27459 _27460 _19609) = (term327 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165508) (@lem1165507 _27459 _27460 _19609)). Qed.
Lemma lem1165510 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term294 _27459 _27460 _19609) = (term294 _27459 _27460 _19609).
Proof. exact (eq_refl (term294 _27459 _27460 _19609)). Qed.
Lemma lem1165511 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term308 _27459 _27460 _19609) = (term328 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165509 _27459 _27460 _19609) (@lem1165510 _27459 _27460 _19609)). Qed.
Lemma lem1165512 {_27459 _27460 : Type'} : (term310 _27459 _27460) = (term329 _27459 _27460).
Proof. exact (fun_ext (fun _19609 : type738 _27459 _27460 => @lem1165511 _27459 _27460 _19609)). Qed.
Lemma lem1165513 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165514 {_27459 _27460 : Type'} : (term312 _27459 _27460) = (term330 _27459 _27460).
Proof. exact (MK_COMB (@lem1165513 _27459 _27460) (@lem1165512 _27459 _27460)). Qed.
Lemma lem1165515 {_27459 _27460 : Type'} : (term300 _27459 _27460) = (term300 _27459 _27460).
Proof. exact (eq_refl (term300 _27459 _27460)). Qed.
Lemma lem1165516 {_27459 _27460 : Type'} : ((term265 _27459 _27460) = (term312 _27459 _27460)) = ((term265 _27459 _27460) = (term330 _27459 _27460)).
Proof. exact (MK_COMB (@lem1165515 _27459 _27460) (@lem1165514 _27459 _27460)). Qed.
Lemma lem1165519 {_27459 _27460 : Type'} : (term265 _27459 _27460) = (term330 _27459 _27460).
Proof. exact (EQ_MP (@lem1165516 _27459 _27460) (@lem1165440 _27459 _27460)). Qed.
Lemma lem1165520 {_27459 _27460 : Type'} : (term186 _27459 _27460) = (term330 _27459 _27460).
Proof. exact (TRANS (@lem1165227 _27459 _27460) (@lem1165519 _27459 _27460)). Qed.
Lemma lem1165521 {_27459 _27460 : Type'} : (term185 _27459 _27460) = (term330 _27459 _27460).
Proof. exact (TRANS (@lem1164984 _27459 _27460) (@lem1165520 _27459 _27460)). Qed.
Lemma lem1165558 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term275 _27459 _27460 _19609 h' _19608 P t' h t) = (term275 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (eq_refl (term275 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1165563 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t)) = ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t)).
Proof. exact (eq_refl ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t))). Qed.
Lemma lem1165564 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term204 _27459 _27460 _19608 P t) = (term204 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1165563 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1165565 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1165566 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term205 _27459 _27460 _19608 P t) = (term205 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1165565 _27459) (@lem1165564 _27459 _27460 _19608 P t)). Qed.
Lemma lem1165567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165568 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term206 _27459 _27460 _19608 P t) = (term206 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1165567) (@lem1165566 _27459 _27460 _19608 P t)). Qed.
Lemma lem1165569 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term276 _27459 _27460 _19609 h' _19608 P t' h t) = (term276 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165568 _27459 _27460 _19608 P t) (@lem1165558 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1165570 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term277 _27459 _27460 _19609 _19608 P t' h t) = (term277 _27459 _27460 _19609 _19608 P t' h t).
Proof. exact (fun_ext (fun h' : _27459 => @lem1165569 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1165571 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165572 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term278 _27459 _27460 _19609 _19608 P t' h t) = (term278 _27459 _27460 _19609 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1165571 _27459) (@lem1165570 _27459 _27460 _19609 _19608 P t' h t)). Qed.
Lemma lem1165573 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term279 _27459 _27460 _19609 _19608 t' h t) = (term279 _27459 _27460 _19609 _19608 t' h t).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165572 _27459 _27460 _19609 _19608 P t' h t)). Qed.
Lemma lem1165574 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165575 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term280 _27459 _27460 _19609 _19608 t' h t) = (term280 _27459 _27460 _19609 _19608 t' h t).
Proof. exact (MK_COMB (@lem1165574 _27459 _27460) (@lem1165573 _27459 _27460 _19609 _19608 t' h t)). Qed.
Lemma lem1165576 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (h : _27460) (t : list _27460) : (term281 _27459 _27460 _19609 _19608 h t) = (term281 _27459 _27460 _19609 _19608 h t).
Proof. exact (fun_ext (fun t' : list _27459 => @lem1165575 _27459 _27460 _19609 _19608 t' h t)). Qed.
Lemma lem1165577 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1165578 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (h : _27460) (t : list _27460) : (term282 _27459 _27460 _19609 _19608 h t) = (term282 _27459 _27460 _19609 _19608 h t).
Proof. exact (MK_COMB (@lem1165577 _27459) (@lem1165576 _27459 _27460 _19609 _19608 h t)). Qed.
Lemma lem1165579 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (t : list _27460) : (term283 _27459 _27460 _19609 _19608 t) = (term283 _27459 _27460 _19609 _19608 t).
Proof. exact (fun_ext (fun h : _27460 => @lem1165578 _27459 _27460 _19609 _19608 h t)). Qed.
Lemma lem1165580 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1165581 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (t : list _27460) : (term284 _27459 _27460 _19609 _19608 t) = (term284 _27459 _27460 _19609 _19608 t).
Proof. exact (MK_COMB (@lem1165580 _27460) (@lem1165579 _27459 _27460 _19609 _19608 t)). Qed.
Lemma lem1165582 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) : (term285 _27459 _27460 _19609 _19608) = (term285 _27459 _27460 _19609 _19608).
Proof. exact (fun_ext (fun t : list _27460 => @lem1165581 _27459 _27460 _19609 _19608 t)). Qed.
Lemma lem1165583 {_27460 : Type'} : (@all (list _27460)) = (@all (list _27460)).
Proof. exact (eq_refl (@all (list _27460))). Qed.
Lemma lem1165584 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) : (term286 _27459 _27460 _19609 _19608) = (term286 _27459 _27460 _19609 _19608).
Proof. exact (MK_COMB (@lem1165583 _27460) (@lem1165582 _27459 _27460 _19609 _19608)). Qed.
Lemma lem1165585 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : ((_19608 P x) = (_19609 P x)) = ((_19608 P x) = (_19609 P x)).
Proof. exact (eq_refl ((_19608 P x) = (_19609 P x))). Qed.
Lemma lem1165586 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term287 _27459 _27460 _19608 _19609 P) = (term287 _27459 _27460 _19608 _19609 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165585 _27459 _27460 _19608 _19609 P x)). Qed.
Lemma lem1165587 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165588 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term288 _27459 _27460 _19608 _19609 P) = (term288 _27459 _27460 _19608 _19609 P).
Proof. exact (MK_COMB (@lem1165587 _27459) (@lem1165586 _27459 _27460 _19608 _19609 P)). Qed.
Lemma lem1165589 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) : (term289 _27459 _27460 _19608 _19609) = (term289 _27459 _27460 _19608 _19609).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165588 _27459 _27460 _19608 _19609 P)). Qed.
Lemma lem1165590 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165591 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) : (term290 _27459 _27460 _19608 _19609) = (term290 _27459 _27460 _19608 _19609).
Proof. exact (MK_COMB (@lem1165590 _27459 _27460) (@lem1165589 _27459 _27460 _19608 _19609)). Qed.
Lemma lem1165592 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165593 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (_19609 : type738 _27459 _27460) : (term291 _27459 _27460 _19608 _19609) = (term291 _27459 _27460 _19608 _19609).
Proof. exact (MK_COMB (@lem1165592) (@lem1165591 _27459 _27460 _19608 _19609)). Qed.
Lemma lem1165594 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) : (term292 _27459 _27460 _19609 _19608) = (term292 _27459 _27460 _19609 _19608).
Proof. exact (MK_COMB (@lem1165593 _27459 _27460 _19608 _19609) (@lem1165584 _27459 _27460 _19609 _19608)). Qed.
Lemma lem1165595 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term293 _27459 _27460 _19609) = (term293 _27459 _27460 _19609).
Proof. exact (fun_ext (fun _19608 : type738 _27459 _27460 => @lem1165594 _27459 _27460 _19609 _19608)). Qed.
Lemma lem1165596 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165597 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term294 _27459 _27460 _19609) = (term294 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165596 _27459 _27460) (@lem1165595 _27459 _27460 _19609)). Qed.
Lemma lem1165602 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (y : _27460) (x : _27459) : ((_19609 P x y) = (P y x)) = ((_19609 P x y) = (P y x)).
Proof. exact (eq_refl ((_19609 P x y) = (P y x))). Qed.
Lemma lem1165603 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term321 _27459 _27460 _19609 P x) = (term321 _27459 _27460 _19609 P x).
Proof. exact (fun_ext (fun y : _27460 => @lem1165602 _27459 _27460 _19609 P y x)). Qed.
Lemma lem1165604 {_27460 : Type'} : (@all _27460) = (@all _27460).
Proof. exact (eq_refl (@all _27460)). Qed.
Lemma lem1165605 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (x : _27459) : (term322 _27459 _27460 _19609 P x) = (term322 _27459 _27460 _19609 P x).
Proof. exact (MK_COMB (@lem1165604 _27460) (@lem1165603 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165606 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term323 _27459 _27460 _19609 P) = (term323 _27459 _27460 _19609 P).
Proof. exact (fun_ext (fun x : _27459 => @lem1165605 _27459 _27460 _19609 P x)). Qed.
Lemma lem1165607 {_27459 : Type'} : (@all _27459) = (@all _27459).
Proof. exact (eq_refl (@all _27459)). Qed.
Lemma lem1165608 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term324 _27459 _27460 _19609 P) = (term324 _27459 _27460 _19609 P).
Proof. exact (MK_COMB (@lem1165607 _27459) (@lem1165606 _27459 _27460 _19609 P)). Qed.
Lemma lem1165609 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term325 _27459 _27460 _19609) = (term325 _27459 _27460 _19609).
Proof. exact (fun_ext (fun P : type1470 _27459 _27460 => @lem1165608 _27459 _27460 _19609 P)). Qed.
Lemma lem1165610 {_27459 _27460 : Type'} : (@all (_27460 -> _27459 -> Prop)) = (@all (_27460 -> _27459 -> Prop)).
Proof. exact (eq_refl (@all (_27460 -> _27459 -> Prop))). Qed.
Lemma lem1165611 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term326 _27459 _27460 _19609) = (term326 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165610 _27459 _27460) (@lem1165609 _27459 _27460 _19609)). Qed.
Lemma lem1165612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1165613 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term327 _27459 _27460 _19609) = (term327 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165612) (@lem1165611 _27459 _27460 _19609)). Qed.
Lemma lem1165614 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : (term328 _27459 _27460 _19609) = (term328 _27459 _27460 _19609).
Proof. exact (MK_COMB (@lem1165613 _27459 _27460 _19609) (@lem1165597 _27459 _27460 _19609)). Qed.
Lemma lem1165615 {_27459 _27460 : Type'} : (term329 _27459 _27460) = (term329 _27459 _27460).
Proof. exact (fun_ext (fun _19609 : type738 _27459 _27460 => @lem1165614 _27459 _27460 _19609)). Qed.
Lemma lem1165616 {_27459 _27460 : Type'} : (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)) = (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop)).
Proof. exact (eq_refl (@all ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop))). Qed.
Lemma lem1165617 {_27459 _27460 : Type'} : (term330 _27459 _27460) = (term330 _27459 _27460).
Proof. exact (MK_COMB (@lem1165616 _27459 _27460) (@lem1165615 _27459 _27460)). Qed.
Lemma lem1165718 {_27459 _27460 : Type'} : (term185 _27459 _27460) = (term330 _27459 _27460).
Proof. exact (TRANS (@lem1165521 _27459 _27460) (@lem1165617 _27459 _27460)). Qed.
Lemma lem1165719 {_27459 _27460 : Type'} : (term330 _27459 _27460) = (term185 _27459 _27460).
Proof. exact (SYM (@lem1165718 _27459 _27460)). Qed.
Lemma lem1165722 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term205 _27459 _27460 _19608 P t.
Proof. exact (h1). Qed.
Lemma lem1165723 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t).
Proof. exact (h1). Qed.
Lemma lem1165725 (p : Prop) : p = (term155 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1165726 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : ((term273 _27459 _27460 h _19609 h' _19608 P t' t) = (term270 _27459 _27460 _19609 h' _19608 P t' h t)) = (term331 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (@lem1165725 ((term273 _27459 _27460 h _19609 h' _19608 P t' t) = (term270 _27459 _27460 _19609 h' _19608 P t' h t))). Qed.
Lemma lem1165727 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term331 _27459 _27460 _19609 h' _19608 P t' h t) = ((term273 _27459 _27460 h _19609 h' _19608 P t' t) = (term270 _27459 _27460 _19609 h' _19608 P t' h t)).
Proof. exact (SYM (@lem1165726 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1165728 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term332 _27459 _27460 _19609 h' _19608 P t' h t) : term332 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1166200 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : ((@ALLPAIRS _27459 _27460 P t m) = (term196 _27459 _27460 _19608 P m t)) = (term333 _27459 _27460 _19608 P m t).
Proof. exact (@lem17784 (@ALLPAIRS _27459 _27460 P t m) (term196 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166201 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term204 _27459 _27460 _19608 P t) = (term334 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1166200 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166202 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1166203 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term205 _27459 _27460 _19608 P t) = (term335 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166202 _27459) (@lem1166201 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166205 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1166206 {_27459 : Type'} (P : type1143 _27459) (Q : type1143 _27459) : (term338 _27459 P Q) = (term339 _27459 P Q).
Proof. exact (@lem1166205 (list _27459) P Q). Qed.
Lemma lem1166207 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term340 _27459 _27460 _19608 P t) = (term341 _27459 _27460 _19608 P t).
Proof. exact (@lem1166206 _27459 (term342 _27459 _27460 _19608 P t) (term343 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166208 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term344 _27459 _27460 _19608 P t m) = (term345 _27459 _27460 _19608 P m t).
Proof. exact (eq_refl (term344 _27459 _27460 _19608 P t m)). Qed.
Lemma lem1166209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166210 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term346 _27459 _27460 _19608 P t m) = (term347 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166209) (@lem1166208 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166211 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term348 _27459 _27460 _19608 P t m) = (term349 _27459 _27460 _19608 P m t).
Proof. exact (eq_refl (term348 _27459 _27460 _19608 P t m)). Qed.
Lemma lem1166212 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term350 _27459 _27460 _19608 P t m) = (term333 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166210 _27459 _27460 _19608 P m t) (@lem1166211 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166213 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term351 _27459 _27460 _19608 P t) = (term334 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1166212 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166214 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1166215 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term340 _27459 _27460 _19608 P t) = (term335 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166214 _27459) (@lem1166213 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1166217 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term352 _27459 _27460 _19608 P t) = (term353 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166216) (@lem1166215 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166218 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term344 _27459 _27460 _19608 P t m) = (term345 _27459 _27460 _19608 P m t).
Proof. exact (eq_refl (term344 _27459 _27460 _19608 P t m)). Qed.
Lemma lem1166219 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term354 _27459 _27460 _19608 P t) = (term342 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1166218 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166220 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1166221 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term355 _27459 _27460 _19608 P t) = (term356 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166220 _27459) (@lem1166219 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166223 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term357 _27459 _27460 _19608 P t) = (term358 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166222) (@lem1166221 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166224 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term348 _27459 _27460 _19608 P t m) = (term349 _27459 _27460 _19608 P m t).
Proof. exact (eq_refl (term348 _27459 _27460 _19608 P t m)). Qed.
Lemma lem1166225 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term359 _27459 _27460 _19608 P t) = (term343 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1166224 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166226 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1166227 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term360 _27459 _27460 _19608 P t) = (term361 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166226 _27459) (@lem1166225 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166228 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term341 _27459 _27460 _19608 P t) = (term362 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166223 _27459 _27460 _19608 P t) (@lem1166227 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166229 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : ((term340 _27459 _27460 _19608 P t) = (term341 _27459 _27460 _19608 P t)) = ((term335 _27459 _27460 _19608 P t) = (term362 _27459 _27460 _19608 P t)).
Proof. exact (MK_COMB (@lem1166217 _27459 _27460 _19608 P t) (@lem1166228 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166328 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term335 _27459 _27460 _19608 P t) = (term362 _27459 _27460 _19608 P t).
Proof. exact (EQ_MP (@lem1166229 _27459 _27460 _19608 P t) (@lem1166207 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166329 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term205 _27459 _27460 _19608 P t) = (term362 _27459 _27460 _19608 P t).
Proof. exact (TRANS (@lem1166203 _27459 _27460 _19608 P t) (@lem1166328 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166330 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term362 _27459 _27460 _19608 P t.
Proof. exact (EQ_MP (@lem1166329 _27459 _27460 _19608 P t) (@lem1165722 _27459 _27460 _19608 P t h1)). Qed.
Lemma lem1166339 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term363 _27459 _27460 h P t t') = (term364 _27459 _27460 h P t t').
Proof. exact (@lem17045 (term365 _27459 _27460 P h t') (@ALLPAIRS _27459 _27460 P t t')). Qed.
Lemma lem1166343 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term366 _27459 _27460 _19608 P t' h t) = (term366 _27459 _27460 _19608 P t' h t).
Proof. exact (eq_refl (term366 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166346 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term367 _27459 _27460 h P t t') = (term368 _27459 _27460 h P t t').
Proof. exact (MK_COMB (@lem1166345) (@lem1166339 _27459 _27460 h P t t')). Qed.
Lemma lem1166347 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term369 _27459 _27460 _19608 P t' h t) = (term370 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166346 _27459 _27460 h P t t') (@lem1166343 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166352 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term371 _27459 _27460 _19608 P t' h t) = (term371 _27459 _27460 _19608 P t' h t).
Proof. exact (eq_refl (term371 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166353 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term372 _27459 _27460 _19608 P t' h t) = (term373 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166352 _27459 _27460 _19608 P t' h t) (@lem1166347 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166354 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : ((term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) = (term372 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem17500 (term37 _27459 _27460 h P t t') (term194 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166359 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : ((term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) = (term373 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1166354 _27459 _27460 _19608 P t' h t) (@lem1166353 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166360 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : term373 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1166359 _27459 _27460 _19608 P t' h t) (@lem1165723 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1166369 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term374 _27459 _27460 h' P h t') = (term375 _27459 _27460 h' P h t').
Proof. exact (@lem17045 (P h h') (term365 _27459 _27460 P h t')). Qed.
Lemma lem1166381 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term376 _27459 _27460 _19609 h' _19608 P t' t) = (term377 _27459 _27460 _19609 h' _19608 P t' t).
Proof. exact (@lem17045 (term267 _27459 _27460 _19609 P h' t) (term196 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1166385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1166386 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term378 _27459 _27460 h' P h t') = (term379 _27459 _27460 h' P h t').
Proof. exact (MK_COMB (@lem1166385) (@lem1166369 _27459 _27460 h' P h t')). Qed.
Lemma lem1166387 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term380 _27459 _27460 h _19609 h' _19608 P t' t) = (term381 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1166386 _27459 _27460 h' P h t') (@lem1166381 _27459 _27460 _19609 h' _19608 P t' t)). Qed.
Lemma lem1166388 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term382 _27459 _27460 h _19609 h' _19608 P t' t) = (term380 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (@lem17045 (term116 _27459 _27460 h' P h t') (term272 _27459 _27460 _19609 h' _19608 P t' t)). Qed.
Lemma lem1166389 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term382 _27459 _27460 h _19609 h' _19608 P t' t) = (term381 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (TRANS (@lem1166388 _27459 _27460 h _19609 h' _19608 P t' t) (@lem1166387 _27459 _27460 h _19609 h' _19608 P t' t)). Qed.
Lemma lem1166401 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term383 _27459 _27460 h _19609 P h' t) = (term384 _27459 _27460 h _19609 P h' t).
Proof. exact (@lem17045 (P h h') (term267 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1166405 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term366 _27459 _27460 _19608 P t' h t) = (term366 _27459 _27460 _19608 P t' h t).
Proof. exact (eq_refl (term366 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1166408 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term385 _27459 _27460 h _19609 P h' t) = (term386 _27459 _27460 h _19609 P h' t).
Proof. exact (MK_COMB (@lem1166407) (@lem1166401 _27459 _27460 h _19609 P h' t)). Qed.
Lemma lem1166409 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term387 _27459 _27460 _19609 h' _19608 P t' h t) = (term388 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166408 _27459 _27460 h _19609 P h' t) (@lem1166405 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166410 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term389 _27459 _27460 _19609 h' _19608 P t' h t) = (term387 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (@lem17045 (term268 _27459 _27460 h _19609 P h' t) (term194 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166411 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term389 _27459 _27460 _19609 h' _19608 P t' h t) = (term388 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (TRANS (@lem1166410 _27459 _27460 _19609 h' _19608 P t' h t) (@lem1166409 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166414 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term270 _27459 _27460 _19609 h' _19608 P t' h t) = (term270 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (eq_refl (term270 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166416 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term390 _27459 _27460 h _19609 h' _19608 P t' t) = (term391 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1166415) (@lem1166389 _27459 _27460 h _19609 h' _19608 P t' t)). Qed.
Lemma lem1166417 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term392 _27459 _27460 _19609 h' _19608 P t' h t) = (term393 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166416 _27459 _27460 h _19609 h' _19608 P t' t) (@lem1166414 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166419 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term394 _27459 _27460 h _19609 h' _19608 P t' t) = (term394 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (eq_refl (term394 _27459 _27460 h _19609 h' _19608 P t' t)). Qed.
Lemma lem1166420 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term395 _27459 _27460 _19609 h' _19608 P t' h t) = (term396 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166419 _27459 _27460 h _19609 h' _19608 P t' t) (@lem1166411 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1166422 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term397 _27459 _27460 _19609 h' _19608 P t' h t) = (term398 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166421) (@lem1166420 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166423 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term399 _27459 _27460 _19609 h' _19608 P t' h t) = (term400 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166422 _27459 _27460 _19609 h' _19608 P t' h t) (@lem1166417 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166424 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term332 _27459 _27460 _19609 h' _19608 P t' h t) = (term399 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (@lem17646 (term273 _27459 _27460 h _19609 h' _19608 P t' t) (term270 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166429 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term332 _27459 _27460 _19609 h' _19608 P t' h t) = (term400 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (TRANS (@lem1166424 _27459 _27460 _19609 h' _19608 P t' h t) (@lem1166423 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1166430 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term332 _27459 _27460 _19609 h' _19608 P t' h t) : term400 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (EQ_MP (@lem1166429 _27459 _27460 _19609 h' _19608 P t' h t) (@lem1165728 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1166593 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1166598 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166599 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1166598 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1166601 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1166599 _27459 _27460 _19608 P). Qed.
Lemma lem1166602 {_27459 : Type'} (m : list _27459) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1166603 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166604 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1166593 _27459 _27460) (@lem1166601 _27459 _27460 _19608 P)). Qed.
Lemma lem1166605 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term193 _27459 _27460 _19608 P m) = (term402 _27459 _27460 _19608 P m).
Proof. exact (MK_COMB (@lem1166604 _27459 _27460 _19608 P) (@lem1166602 _27459 m)). Qed.
Lemma lem1166606 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P m t) = (term403 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166605 _27459 _27460 _19608 P m) (@lem1166603 _27460 t)). Qed.
Lemma lem1166608 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166609 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166608 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1166610 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1166609 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1166611 {_27459 : Type'} (m : list _27459) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1166612 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term402 _27459 _27460 _19608 P m) = (term405 _27459 _27460 _19608 P m).
Proof. exact (MK_COMB (@lem1166610 _27459 _27460 _19608 P) (@lem1166611 _27459 m)). Qed.
Lemma lem1166614 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166615 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166614 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1166616 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term405 _27459 _27460 _19608 P m) = (term406 _27459 _27460 _19608 P m).
Proof. exact (@lem1166615 _27459 _27460 (term404 _27459 _27460 _19608 P) m). Qed.
Lemma lem1166617 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term402 _27459 _27460 _19608 P m) = (term406 _27459 _27460 _19608 P m).
Proof. exact (TRANS (@lem1166612 _27459 _27460 _19608 P m) (@lem1166616 _27459 _27460 _19608 P m)). Qed.
Lemma lem1166618 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166619 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P m t) = (term407 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166617 _27459 _27460 _19608 P m) (@lem1166618 _27460 t)). Qed.
Lemma lem1166621 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166622 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1166621 (list _27460) Prop f x). Qed.
Lemma lem1166623 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term407 _27459 _27460 _19608 P m t) = (term408 _27459 _27460 _19608 P m t).
Proof. exact (@lem1166622 _27460 (term406 _27459 _27460 _19608 P m) t). Qed.
Lemma lem1166624 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P m t) = (term408 _27459 _27460 _19608 P m t).
Proof. exact (TRANS (@lem1166619 _27459 _27460 _19608 P m t) (@lem1166623 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166625 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P m t) = (term408 _27459 _27460 _19608 P m t).
Proof. exact (TRANS (@lem1166606 _27459 _27460 _19608 P m t) (@lem1166624 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166626 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1166635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166636 {_27459 _27460 : Type'} (f : type736 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166635 (type1470 _27459 _27460) (type1149 _27459 _27460) f x). Qed.
Lemma lem1166637 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (@ALLPAIRS _27459 _27460 P) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P).
Proof. exact (@lem1166636 _27459 _27460 (@ALLPAIRS _27459 _27460) P). Qed.
Lemma lem1166638 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166639 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t).
Proof. exact (MK_COMB (@lem1166637 _27459 _27460 P) (@lem1166638 _27460 t)). Qed.
Lemma lem1166641 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166642 {_27459 _27460 : Type'} (f : type1149 _27459 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166641 (list _27460) (type1143 _27459) f x). Qed.
Lemma lem1166643 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t) = (term409 _27459 _27460 P t).
Proof. exact (@lem1166642 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P) t). Qed.
Lemma lem1166644 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (term409 _27459 _27460 P t).
Proof. exact (TRANS (@lem1166639 _27459 _27460 P t) (@lem1166643 _27459 _27460 P t)). Qed.
Lemma lem1166645 {_27459 : Type'} (m : list _27459) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1166646 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (@ALLPAIRS _27459 _27460 P t m) = (term410 _27459 _27460 P t m).
Proof. exact (MK_COMB (@lem1166644 _27459 _27460 P t) (@lem1166645 _27459 m)). Qed.
Lemma lem1166648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166649 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1166648 (list _27459) Prop f x). Qed.
Lemma lem1166650 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term410 _27459 _27460 P t m) = (term411 _27459 _27460 P t m).
Proof. exact (@lem1166649 _27459 (term409 _27459 _27460 P t) m). Qed.
Lemma lem1166652 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (@ALLPAIRS _27459 _27460 P t m) = (term411 _27459 _27460 P t m).
Proof. exact (TRANS (@lem1166646 _27459 _27460 P t m) (@lem1166650 _27459 _27460 P t m)). Qed.
Lemma lem1166653 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term412 _27459 _27460 P t m) = (term413 _27459 _27460 P t m).
Proof. exact (MK_COMB (@lem1166626) (@lem1166652 _27459 _27460 P t m)). Qed.
Lemma lem1166654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1166655 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term414 _27459 _27460 P t m) = (term415 _27459 _27460 P t m).
Proof. exact (MK_COMB (@lem1166654) (@lem1166653 _27459 _27460 P t m)). Qed.
Lemma lem1166656 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term349 _27459 _27460 _19608 P m t) = (term416 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166655 _27459 _27460 P t m) (@lem1166625 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166657 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term343 _27459 _27460 _19608 P t) = (term417 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1166656 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166658 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1166659 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term361 _27459 _27460 _19608 P t) = (term418 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166658 _27459) (@lem1166657 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166660 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1166661 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1166666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166667 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1166666 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1166669 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1166667 _27459 _27460 _19608 P). Qed.
Lemma lem1166670 {_27459 : Type'} (m : list _27459) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1166671 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166672 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1166661 _27459 _27460) (@lem1166669 _27459 _27460 _19608 P)). Qed.
Lemma lem1166673 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term193 _27459 _27460 _19608 P m) = (term402 _27459 _27460 _19608 P m).
Proof. exact (MK_COMB (@lem1166672 _27459 _27460 _19608 P) (@lem1166670 _27459 m)). Qed.
Lemma lem1166674 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P m t) = (term403 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166673 _27459 _27460 _19608 P m) (@lem1166671 _27460 t)). Qed.
Lemma lem1166676 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166677 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166676 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1166678 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1166677 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1166679 {_27459 : Type'} (m : list _27459) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1166680 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term402 _27459 _27460 _19608 P m) = (term405 _27459 _27460 _19608 P m).
Proof. exact (MK_COMB (@lem1166678 _27459 _27460 _19608 P) (@lem1166679 _27459 m)). Qed.
Lemma lem1166682 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166683 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166682 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1166684 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term405 _27459 _27460 _19608 P m) = (term406 _27459 _27460 _19608 P m).
Proof. exact (@lem1166683 _27459 _27460 (term404 _27459 _27460 _19608 P) m). Qed.
Lemma lem1166685 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) : (term402 _27459 _27460 _19608 P m) = (term406 _27459 _27460 _19608 P m).
Proof. exact (TRANS (@lem1166680 _27459 _27460 _19608 P m) (@lem1166684 _27459 _27460 _19608 P m)). Qed.
Lemma lem1166686 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166687 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P m t) = (term407 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166685 _27459 _27460 _19608 P m) (@lem1166686 _27460 t)). Qed.
Lemma lem1166689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166690 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1166689 (list _27460) Prop f x). Qed.
Lemma lem1166691 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term407 _27459 _27460 _19608 P m t) = (term408 _27459 _27460 _19608 P m t).
Proof. exact (@lem1166690 _27460 (term406 _27459 _27460 _19608 P m) t). Qed.
Lemma lem1166692 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P m t) = (term408 _27459 _27460 _19608 P m t).
Proof. exact (TRANS (@lem1166687 _27459 _27460 _19608 P m t) (@lem1166691 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166693 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P m t) = (term408 _27459 _27460 _19608 P m t).
Proof. exact (TRANS (@lem1166674 _27459 _27460 _19608 P m t) (@lem1166692 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166694 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term419 _27459 _27460 _19608 P m t) = (term420 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166660) (@lem1166693 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166703 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166704 {_27459 _27460 : Type'} (f : type736 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166703 (type1470 _27459 _27460) (type1149 _27459 _27460) f x). Qed.
Lemma lem1166705 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (@ALLPAIRS _27459 _27460 P) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P).
Proof. exact (@lem1166704 _27459 _27460 (@ALLPAIRS _27459 _27460) P). Qed.
Lemma lem1166706 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166707 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t).
Proof. exact (MK_COMB (@lem1166705 _27459 _27460 P) (@lem1166706 _27460 t)). Qed.
Lemma lem1166709 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166710 {_27459 _27460 : Type'} (f : type1149 _27459 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166709 (list _27460) (type1143 _27459) f x). Qed.
Lemma lem1166711 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t) = (term409 _27459 _27460 P t).
Proof. exact (@lem1166710 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P) t). Qed.
Lemma lem1166712 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (term409 _27459 _27460 P t).
Proof. exact (TRANS (@lem1166707 _27459 _27460 P t) (@lem1166711 _27459 _27460 P t)). Qed.
Lemma lem1166713 {_27459 : Type'} (m : list _27459) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1166714 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (@ALLPAIRS _27459 _27460 P t m) = (term410 _27459 _27460 P t m).
Proof. exact (MK_COMB (@lem1166712 _27459 _27460 P t) (@lem1166713 _27459 m)). Qed.
Lemma lem1166716 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166717 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1166716 (list _27459) Prop f x). Qed.
Lemma lem1166718 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term410 _27459 _27460 P t m) = (term411 _27459 _27460 P t m).
Proof. exact (@lem1166717 _27459 (term409 _27459 _27460 P t) m). Qed.
Lemma lem1166720 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (@ALLPAIRS _27459 _27460 P t m) = (term411 _27459 _27460 P t m).
Proof. exact (TRANS (@lem1166714 _27459 _27460 P t m) (@lem1166718 _27459 _27460 P t m)). Qed.
Lemma lem1166721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1166722 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (m : list _27459) : (term421 _27459 _27460 P t m) = (term422 _27459 _27460 P t m).
Proof. exact (MK_COMB (@lem1166721) (@lem1166720 _27459 _27460 P t m)). Qed.
Lemma lem1166723 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term345 _27459 _27460 _19608 P m t) = (term423 _27459 _27460 _19608 P m t).
Proof. exact (MK_COMB (@lem1166722 _27459 _27460 P t m) (@lem1166694 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166724 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term342 _27459 _27460 _19608 P t) = (term424 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1166723 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1166725 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1166726 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term356 _27459 _27460 _19608 P t) = (term425 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166725 _27459) (@lem1166724 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166728 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term358 _27459 _27460 _19608 P t) = (term426 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166727) (@lem1166726 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166729 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term362 _27459 _27460 _19608 P t) = (term427 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1166728 _27459 _27460 _19608 P t) (@lem1166659 _27459 _27460 _19608 P t)). Qed.
Lemma lem1166730 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term427 _27459 _27460 _19608 P t.
Proof. exact (EQ_MP (@lem1166729 _27459 _27460 _19608 P t) (@lem1166330 _27459 _27460 _19608 P t h1)). Qed.
Lemma lem1166731 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1166732 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1166737 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166738 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1166737 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1166740 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1166738 _27459 _27460 _19608 P). Qed.
Lemma lem1166741 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166748 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166749 {_27460 : Type'} (f : type1397 _27460) (x : _27460) : (f x) = (@I (_27460 -> (list _27460) -> list _27460) f x).
Proof. exact (@lem1166748 _27460 (type1138 _27460) f x). Qed.
Lemma lem1166750 {_27460 : Type'} (h : _27460) : (@cons _27460 h) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h).
Proof. exact (@lem1166749 _27460 (@cons _27460) h). Qed.
Lemma lem1166751 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166752 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t).
Proof. exact (MK_COMB (@lem1166750 _27460 h) (@lem1166751 _27460 t)). Qed.
Lemma lem1166754 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166755 {_27460 : Type'} (f : type1138 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> list _27460) f x).
Proof. exact (@lem1166754 (list _27460) (list _27460) f x). Qed.
Lemma lem1166756 {_27460 : Type'} (h : _27460) (t : list _27460) : (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t) = (term428 _27460 h t).
Proof. exact (@lem1166755 _27460 (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h) t). Qed.
Lemma lem1166758 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (term428 _27460 h t).
Proof. exact (TRANS (@lem1166752 _27460 h t) (@lem1166756 _27460 h t)). Qed.
Lemma lem1166759 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1166732 _27459 _27460) (@lem1166740 _27459 _27460 _19608 P)). Qed.
Lemma lem1166760 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term193 _27459 _27460 _19608 P t') = (term402 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1166759 _27459 _27460 _19608 P) (@lem1166741 _27459 t')). Qed.
Lemma lem1166761 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term429 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166760 _27459 _27460 _19608 P t') (@lem1166758 _27460 h t)). Qed.
Lemma lem1166763 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166764 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166763 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1166765 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1166764 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1166766 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166767 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term405 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1166765 _27459 _27460 _19608 P) (@lem1166766 _27459 t')). Qed.
Lemma lem1166769 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166770 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166769 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1166771 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term405 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (@lem1166770 _27459 _27460 (term404 _27459 _27460 _19608 P) t'). Qed.
Lemma lem1166772 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (TRANS (@lem1166767 _27459 _27460 _19608 P t') (@lem1166771 _27459 _27460 _19608 P t')). Qed.
Lemma lem1166773 {_27460 : Type'} (h : _27460) (t : list _27460) : (term428 _27460 h t) = (term428 _27460 h t).
Proof. exact (eq_refl (term428 _27460 h t)). Qed.
Lemma lem1166774 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term430 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166772 _27459 _27460 _19608 P t') (@lem1166773 _27460 h t)). Qed.
Lemma lem1166776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166777 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1166776 (list _27460) Prop f x). Qed.
Lemma lem1166778 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term430 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1166777 _27460 (term406 _27459 _27460 _19608 P t') (term428 _27460 h t)). Qed.
Lemma lem1166779 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1166774 _27459 _27460 _19608 P t' h t) (@lem1166778 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166780 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1166761 _27459 _27460 _19608 P t' h t) (@lem1166779 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166781 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term366 _27459 _27460 _19608 P t' h t) = (term432 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166731) (@lem1166780 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166782 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1166791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166792 {_27459 _27460 : Type'} (f : type736 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166791 (type1470 _27459 _27460) (type1149 _27459 _27460) f x). Qed.
Lemma lem1166793 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (@ALLPAIRS _27459 _27460 P) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P).
Proof. exact (@lem1166792 _27459 _27460 (@ALLPAIRS _27459 _27460) P). Qed.
Lemma lem1166794 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166795 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t).
Proof. exact (MK_COMB (@lem1166793 _27459 _27460 P) (@lem1166794 _27460 t)). Qed.
Lemma lem1166797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166798 {_27459 _27460 : Type'} (f : type1149 _27459 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166797 (list _27460) (type1143 _27459) f x). Qed.
Lemma lem1166799 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t) = (term409 _27459 _27460 P t).
Proof. exact (@lem1166798 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P) t). Qed.
Lemma lem1166800 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (term409 _27459 _27460 P t).
Proof. exact (TRANS (@lem1166795 _27459 _27460 P t) (@lem1166799 _27459 _27460 P t)). Qed.
Lemma lem1166801 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166802 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (@ALLPAIRS _27459 _27460 P t t') = (term410 _27459 _27460 P t t').
Proof. exact (MK_COMB (@lem1166800 _27459 _27460 P t) (@lem1166801 _27459 t')). Qed.
Lemma lem1166804 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166805 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1166804 (list _27459) Prop f x). Qed.
Lemma lem1166806 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term410 _27459 _27460 P t t') = (term411 _27459 _27460 P t t').
Proof. exact (@lem1166805 _27459 (term409 _27459 _27460 P t) t'). Qed.
Lemma lem1166808 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (@ALLPAIRS _27459 _27460 P t t') = (term411 _27459 _27460 P t t').
Proof. exact (TRANS (@lem1166802 _27459 _27460 P t t') (@lem1166806 _27459 _27460 P t t')). Qed.
Lemma lem1166809 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term412 _27459 _27460 P t t') = (term413 _27459 _27460 P t t').
Proof. exact (MK_COMB (@lem1166782) (@lem1166808 _27459 _27460 P t t')). Qed.
Lemma lem1166810 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1166811 {_27459 : Type'} : (@List.Forall _27459) = (@List.Forall _27459).
Proof. exact (eq_refl (@List.Forall _27459)). Qed.
Lemma lem1166816 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166817 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1166816 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1166819 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1166817 _27459 _27460 P h). Qed.
Lemma lem1166820 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166821 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term433 _27459 _27460 P h) = (term434 _27459 _27460 P h).
Proof. exact (MK_COMB (@lem1166811 _27459) (@lem1166819 _27459 _27460 P h)). Qed.
Lemma lem1166822 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term435 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1166821 _27459 _27460 P h) (@lem1166820 _27459 t')). Qed.
Lemma lem1166824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166825 {_27459 : Type'} (f : type663 _27459) (x : _27459 -> Prop) : (f x) = (@I ((_27459 -> Prop) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166824 (_27459 -> Prop) (type1143 _27459) f x). Qed.
Lemma lem1166826 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term434 _27459 _27460 P h) = (term436 _27459 _27460 P h).
Proof. exact (@lem1166825 _27459 (@List.Forall _27459) (@I (_27460 -> _27459 -> Prop) P h)). Qed.
Lemma lem1166827 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166828 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term437 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1166826 _27459 _27460 P h) (@lem1166827 _27459 t')). Qed.
Lemma lem1166830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166831 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1166830 (list _27459) Prop f x). Qed.
Lemma lem1166832 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term437 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1166831 _27459 (term436 _27459 _27460 P h) t'). Qed.
Lemma lem1166833 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1166828 _27459 _27460 P h t') (@lem1166832 _27459 _27460 P h t')). Qed.
Lemma lem1166834 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1166822 _27459 _27460 P h t') (@lem1166833 _27459 _27460 P h t')). Qed.
Lemma lem1166835 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term439 _27459 _27460 P h t') = (term440 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1166810) (@lem1166834 _27459 _27460 P h t')). Qed.
Lemma lem1166836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1166837 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term441 _27459 _27460 P h t') = (term442 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1166836) (@lem1166835 _27459 _27460 P h t')). Qed.
Lemma lem1166838 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term364 _27459 _27460 h P t t') = (term443 _27459 _27460 h P t t').
Proof. exact (MK_COMB (@lem1166837 _27459 _27460 P h t') (@lem1166809 _27459 _27460 P t t')). Qed.
Lemma lem1166839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166840 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term368 _27459 _27460 h P t t') = (term444 _27459 _27460 h P t t').
Proof. exact (MK_COMB (@lem1166839) (@lem1166838 _27459 _27460 h P t t')). Qed.
Lemma lem1166841 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term370 _27459 _27460 _19608 P t' h t) = (term445 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166840 _27459 _27460 h P t t') (@lem1166781 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166842 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1166847 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166848 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1166847 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1166850 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1166848 _27459 _27460 _19608 P). Qed.
Lemma lem1166851 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166859 {_27460 : Type'} (f : type1397 _27460) (x : _27460) : (f x) = (@I (_27460 -> (list _27460) -> list _27460) f x).
Proof. exact (@lem1166858 _27460 (type1138 _27460) f x). Qed.
Lemma lem1166860 {_27460 : Type'} (h : _27460) : (@cons _27460 h) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h).
Proof. exact (@lem1166859 _27460 (@cons _27460) h). Qed.
Lemma lem1166861 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166862 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t).
Proof. exact (MK_COMB (@lem1166860 _27460 h) (@lem1166861 _27460 t)). Qed.
Lemma lem1166864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166865 {_27460 : Type'} (f : type1138 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> list _27460) f x).
Proof. exact (@lem1166864 (list _27460) (list _27460) f x). Qed.
Lemma lem1166866 {_27460 : Type'} (h : _27460) (t : list _27460) : (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t) = (term428 _27460 h t).
Proof. exact (@lem1166865 _27460 (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h) t). Qed.
Lemma lem1166868 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (term428 _27460 h t).
Proof. exact (TRANS (@lem1166862 _27460 h t) (@lem1166866 _27460 h t)). Qed.
Lemma lem1166869 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1166842 _27459 _27460) (@lem1166850 _27459 _27460 _19608 P)). Qed.
Lemma lem1166870 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term193 _27459 _27460 _19608 P t') = (term402 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1166869 _27459 _27460 _19608 P) (@lem1166851 _27459 t')). Qed.
Lemma lem1166871 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term429 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166870 _27459 _27460 _19608 P t') (@lem1166868 _27460 h t)). Qed.
Lemma lem1166873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166874 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166873 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1166875 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1166874 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1166876 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166877 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term405 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1166875 _27459 _27460 _19608 P) (@lem1166876 _27459 t')). Qed.
Lemma lem1166879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166880 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166879 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1166881 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term405 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (@lem1166880 _27459 _27460 (term404 _27459 _27460 _19608 P) t'). Qed.
Lemma lem1166882 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (TRANS (@lem1166877 _27459 _27460 _19608 P t') (@lem1166881 _27459 _27460 _19608 P t')). Qed.
Lemma lem1166883 {_27460 : Type'} (h : _27460) (t : list _27460) : (term428 _27460 h t) = (term428 _27460 h t).
Proof. exact (eq_refl (term428 _27460 h t)). Qed.
Lemma lem1166884 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term430 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166882 _27459 _27460 _19608 P t') (@lem1166883 _27460 h t)). Qed.
Lemma lem1166886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166887 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1166886 (list _27460) Prop f x). Qed.
Lemma lem1166888 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term430 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1166887 _27460 (term406 _27459 _27460 _19608 P t') (term428 _27460 h t)). Qed.
Lemma lem1166889 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1166884 _27459 _27460 _19608 P t' h t) (@lem1166888 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166890 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1166871 _27459 _27460 _19608 P t' h t) (@lem1166889 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166899 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166900 {_27459 _27460 : Type'} (f : type736 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166899 (type1470 _27459 _27460) (type1149 _27459 _27460) f x). Qed.
Lemma lem1166901 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : (@ALLPAIRS _27459 _27460 P) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P).
Proof. exact (@lem1166900 _27459 _27460 (@ALLPAIRS _27459 _27460) P). Qed.
Lemma lem1166902 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166903 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t).
Proof. exact (MK_COMB (@lem1166901 _27459 _27460 P) (@lem1166902 _27460 t)). Qed.
Lemma lem1166905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166906 {_27459 _27460 : Type'} (f : type1149 _27459 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166905 (list _27460) (type1143 _27459) f x). Qed.
Lemma lem1166907 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P t) = (term409 _27459 _27460 P t).
Proof. exact (@lem1166906 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> (list _27460) -> (list _27459) -> Prop) (@ALLPAIRS _27459 _27460) P) t). Qed.
Lemma lem1166908 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) : (@ALLPAIRS _27459 _27460 P t) = (term409 _27459 _27460 P t).
Proof. exact (TRANS (@lem1166903 _27459 _27460 P t) (@lem1166907 _27459 _27460 P t)). Qed.
Lemma lem1166909 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166910 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (@ALLPAIRS _27459 _27460 P t t') = (term410 _27459 _27460 P t t').
Proof. exact (MK_COMB (@lem1166908 _27459 _27460 P t) (@lem1166909 _27459 t')). Qed.
Lemma lem1166912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166913 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1166912 (list _27459) Prop f x). Qed.
Lemma lem1166914 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term410 _27459 _27460 P t t') = (term411 _27459 _27460 P t t').
Proof. exact (@lem1166913 _27459 (term409 _27459 _27460 P t) t'). Qed.
Lemma lem1166916 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (@ALLPAIRS _27459 _27460 P t t') = (term411 _27459 _27460 P t t').
Proof. exact (TRANS (@lem1166910 _27459 _27460 P t t') (@lem1166914 _27459 _27460 P t t')). Qed.
Lemma lem1166917 {_27459 : Type'} : (@List.Forall _27459) = (@List.Forall _27459).
Proof. exact (eq_refl (@List.Forall _27459)). Qed.
Lemma lem1166922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166923 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1166922 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1166925 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1166923 _27459 _27460 P h). Qed.
Lemma lem1166926 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166927 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term433 _27459 _27460 P h) = (term434 _27459 _27460 P h).
Proof. exact (MK_COMB (@lem1166917 _27459) (@lem1166925 _27459 _27460 P h)). Qed.
Lemma lem1166928 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term435 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1166927 _27459 _27460 P h) (@lem1166926 _27459 t')). Qed.
Lemma lem1166930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166931 {_27459 : Type'} (f : type663 _27459) (x : _27459 -> Prop) : (f x) = (@I ((_27459 -> Prop) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1166930 (_27459 -> Prop) (type1143 _27459) f x). Qed.
Lemma lem1166932 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term434 _27459 _27460 P h) = (term436 _27459 _27460 P h).
Proof. exact (@lem1166931 _27459 (@List.Forall _27459) (@I (_27460 -> _27459 -> Prop) P h)). Qed.
Lemma lem1166933 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166934 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term437 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1166932 _27459 _27460 P h) (@lem1166933 _27459 t')). Qed.
Lemma lem1166936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166937 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1166936 (list _27459) Prop f x). Qed.
Lemma lem1166938 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term437 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1166937 _27459 (term436 _27459 _27460 P h) t'). Qed.
Lemma lem1166939 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1166934 _27459 _27460 P h t') (@lem1166938 _27459 _27460 P h t')). Qed.
Lemma lem1166940 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1166928 _27459 _27460 P h t') (@lem1166939 _27459 _27460 P h t')). Qed.
Lemma lem1166941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166942 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term446 _27459 _27460 P h t') = (term447 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1166941) (@lem1166940 _27459 _27460 P h t')). Qed.
Lemma lem1166943 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term37 _27459 _27460 h P t t') = (term448 _27459 _27460 h P t t').
Proof. exact (MK_COMB (@lem1166942 _27459 _27460 P h t') (@lem1166916 _27459 _27460 P t t')). Qed.
Lemma lem1166944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1166945 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term449 _27459 _27460 h P t t') = (term450 _27459 _27460 h P t t').
Proof. exact (MK_COMB (@lem1166944) (@lem1166943 _27459 _27460 h P t t')). Qed.
Lemma lem1166946 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term451 _27459 _27460 _19608 P t' h t) = (term452 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166945 _27459 _27460 h P t t') (@lem1166890 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1166948 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term371 _27459 _27460 _19608 P t' h t) = (term453 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166947) (@lem1166946 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166949 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term373 _27459 _27460 _19608 P t' h t) = (term454 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166948 _27459 _27460 _19608 P t' h t) (@lem1166841 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166950 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : term454 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1166949 _27459 _27460 _19608 P t' h t) (@lem1166360 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1166951 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1166956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166957 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1166956 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1166959 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1166957 _27459 _27460 _19608 P). Qed.
Lemma lem1166960 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166968 {_27460 : Type'} (f : type1397 _27460) (x : _27460) : (f x) = (@I (_27460 -> (list _27460) -> list _27460) f x).
Proof. exact (@lem1166967 _27460 (type1138 _27460) f x). Qed.
Lemma lem1166969 {_27460 : Type'} (h : _27460) : (@cons _27460 h) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h).
Proof. exact (@lem1166968 _27460 (@cons _27460) h). Qed.
Lemma lem1166970 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1166971 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t).
Proof. exact (MK_COMB (@lem1166969 _27460 h) (@lem1166970 _27460 t)). Qed.
Lemma lem1166973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166974 {_27460 : Type'} (f : type1138 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> list _27460) f x).
Proof. exact (@lem1166973 (list _27460) (list _27460) f x). Qed.
Lemma lem1166975 {_27460 : Type'} (h : _27460) (t : list _27460) : (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t) = (term428 _27460 h t).
Proof. exact (@lem1166974 _27460 (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h) t). Qed.
Lemma lem1166977 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (term428 _27460 h t).
Proof. exact (TRANS (@lem1166971 _27460 h t) (@lem1166975 _27460 h t)). Qed.
Lemma lem1166978 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1166951 _27459 _27460) (@lem1166959 _27459 _27460 _19608 P)). Qed.
Lemma lem1166979 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term193 _27459 _27460 _19608 P t') = (term402 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1166978 _27459 _27460 _19608 P) (@lem1166960 _27459 t')). Qed.
Lemma lem1166980 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term429 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166979 _27459 _27460 _19608 P t') (@lem1166977 _27460 h t)). Qed.
Lemma lem1166982 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166983 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166982 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1166984 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1166983 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1166985 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1166986 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term405 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1166984 _27459 _27460 _19608 P) (@lem1166985 _27459 t')). Qed.
Lemma lem1166988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166989 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1166988 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1166990 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term405 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (@lem1166989 _27459 _27460 (term404 _27459 _27460 _19608 P) t'). Qed.
Lemma lem1166991 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (TRANS (@lem1166986 _27459 _27460 _19608 P t') (@lem1166990 _27459 _27460 _19608 P t')). Qed.
Lemma lem1166992 {_27460 : Type'} (h : _27460) (t : list _27460) : (term428 _27460 h t) = (term428 _27460 h t).
Proof. exact (eq_refl (term428 _27460 h t)). Qed.
Lemma lem1166993 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term430 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1166991 _27459 _27460 _19608 P t') (@lem1166992 _27460 h t)). Qed.
Lemma lem1166995 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1166996 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1166995 (list _27460) Prop f x). Qed.
Lemma lem1166997 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term430 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1166996 _27460 (term406 _27459 _27460 _19608 P t') (term428 _27460 h t)). Qed.
Lemma lem1166998 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1166993 _27459 _27460 _19608 P t' h t) (@lem1166997 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1166999 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1166980 _27459 _27460 _19608 P t' h t) (@lem1166998 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1167000 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1167007 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167008 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167007 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1167009 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19609 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P).
Proof. exact (@lem1167008 _27459 _27460 _19609 P). Qed.
Lemma lem1167010 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167011 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h').
Proof. exact (MK_COMB (@lem1167009 _27459 _27460 _19609 P) (@lem1167010 _27459 h')). Qed.
Lemma lem1167013 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167014 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (x : _27459) : (f x) = (@I (_27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167013 _27459 (_27460 -> Prop) f x). Qed.
Lemma lem1167015 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (@lem1167014 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P) h'). Qed.
Lemma lem1167017 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (TRANS (@lem1167011 _27459 _27460 _19609 P h') (@lem1167015 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167018 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167019 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term266 _27459 _27460 _19609 P h') = (term456 _27459 _27460 _19609 P h').
Proof. exact (MK_COMB (@lem1167000 _27460) (@lem1167017 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167020 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term457 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167019 _27459 _27460 _19609 P h') (@lem1167018 _27460 t)). Qed.
Lemma lem1167022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167023 {_27460 : Type'} (f : type663 _27460) (x : _27460 -> Prop) : (f x) = (@I ((_27460 -> Prop) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167022 (_27460 -> Prop) (type1143 _27460) f x). Qed.
Lemma lem1167024 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term456 _27459 _27460 _19609 P h') = (term458 _27459 _27460 _19609 P h').
Proof. exact (@lem1167023 _27460 (@List.Forall _27460) (term455 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167025 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167026 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term459 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167024 _27459 _27460 _19609 P h') (@lem1167025 _27460 t)). Qed.
Lemma lem1167028 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167029 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1167028 (list _27460) Prop f x). Qed.
Lemma lem1167030 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term459 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1167029 _27460 (term458 _27459 _27460 _19609 P h') t). Qed.
Lemma lem1167031 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167026 _27459 _27460 _19609 P h' t) (@lem1167030 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167032 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167020 _27459 _27460 _19609 P h' t) (@lem1167031 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167040 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1167039 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1167041 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1167040 _27459 _27460 P h). Qed.
Lemma lem1167042 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167043 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (@I (_27460 -> _27459 -> Prop) P h h').
Proof. exact (MK_COMB (@lem1167041 _27459 _27460 P h) (@lem1167042 _27459 h')). Qed.
Lemma lem1167045 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167046 {_27459 : Type'} (f : _27459 -> Prop) (x : _27459) : (f x) = (@I (_27459 -> Prop) f x).
Proof. exact (@lem1167045 _27459 Prop f x). Qed.
Lemma lem1167047 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (@I (_27460 -> _27459 -> Prop) P h h') = (term461 _27459 _27460 P h h').
Proof. exact (@lem1167046 _27459 (@I (_27460 -> _27459 -> Prop) P h) h'). Qed.
Lemma lem1167049 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (term461 _27459 _27460 P h h').
Proof. exact (TRANS (@lem1167043 _27459 _27460 P h h') (@lem1167047 _27459 _27460 P h h')). Qed.
Lemma lem1167050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1167051 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term150 _27459 _27460 P h h') = (term462 _27459 _27460 P h h').
Proof. exact (MK_COMB (@lem1167050) (@lem1167049 _27459 _27460 P h h')). Qed.
Lemma lem1167052 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term268 _27459 _27460 h _19609 P h' t) = (term463 _27459 _27460 h _19609 P h' t).
Proof. exact (MK_COMB (@lem1167051 _27459 _27460 P h h') (@lem1167032 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1167054 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term269 _27459 _27460 h _19609 P h' t) = (term464 _27459 _27460 h _19609 P h' t).
Proof. exact (MK_COMB (@lem1167053) (@lem1167052 _27459 _27460 h _19609 P h' t)). Qed.
Lemma lem1167055 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term270 _27459 _27460 _19609 h' _19608 P t' h t) = (term465 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167054 _27459 _27460 h _19609 P h' t) (@lem1166999 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1167056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1167057 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1167062 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167063 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167062 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1167065 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1167063 _27459 _27460 _19608 P). Qed.
Lemma lem1167066 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167067 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167068 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1167057 _27459 _27460) (@lem1167065 _27459 _27460 _19608 P)). Qed.
Lemma lem1167069 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term193 _27459 _27460 _19608 P t') = (term402 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1167068 _27459 _27460 _19608 P) (@lem1167066 _27459 t')). Qed.
Lemma lem1167070 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P t' t) = (term403 _27459 _27460 _19608 P t' t).
Proof. exact (MK_COMB (@lem1167069 _27459 _27460 _19608 P t') (@lem1167067 _27460 t)). Qed.
Lemma lem1167072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167073 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167072 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1167074 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1167073 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1167075 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167076 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term405 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1167074 _27459 _27460 _19608 P) (@lem1167075 _27459 t')). Qed.
Lemma lem1167078 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167079 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167078 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1167080 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term405 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (@lem1167079 _27459 _27460 (term404 _27459 _27460 _19608 P) t'). Qed.
Lemma lem1167081 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (TRANS (@lem1167076 _27459 _27460 _19608 P t') (@lem1167080 _27459 _27460 _19608 P t')). Qed.
Lemma lem1167082 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167083 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P t' t) = (term407 _27459 _27460 _19608 P t' t).
Proof. exact (MK_COMB (@lem1167081 _27459 _27460 _19608 P t') (@lem1167082 _27460 t)). Qed.
Lemma lem1167085 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167086 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1167085 (list _27460) Prop f x). Qed.
Lemma lem1167087 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term407 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (@lem1167086 _27460 (term406 _27459 _27460 _19608 P t') t). Qed.
Lemma lem1167088 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (TRANS (@lem1167083 _27459 _27460 _19608 P t' t) (@lem1167087 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1167089 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (TRANS (@lem1167070 _27459 _27460 _19608 P t' t) (@lem1167088 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1167090 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term419 _27459 _27460 _19608 P t' t) = (term420 _27459 _27460 _19608 P t' t).
Proof. exact (MK_COMB (@lem1167056) (@lem1167089 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1167091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1167092 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1167099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167100 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167099 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1167101 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19609 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P).
Proof. exact (@lem1167100 _27459 _27460 _19609 P). Qed.
Lemma lem1167102 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167103 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h').
Proof. exact (MK_COMB (@lem1167101 _27459 _27460 _19609 P) (@lem1167102 _27459 h')). Qed.
Lemma lem1167105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167106 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (x : _27459) : (f x) = (@I (_27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167105 _27459 (_27460 -> Prop) f x). Qed.
Lemma lem1167107 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (@lem1167106 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P) h'). Qed.
Lemma lem1167109 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (TRANS (@lem1167103 _27459 _27460 _19609 P h') (@lem1167107 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167110 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167111 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term266 _27459 _27460 _19609 P h') = (term456 _27459 _27460 _19609 P h').
Proof. exact (MK_COMB (@lem1167092 _27460) (@lem1167109 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167112 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term457 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167111 _27459 _27460 _19609 P h') (@lem1167110 _27460 t)). Qed.
Lemma lem1167114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167115 {_27460 : Type'} (f : type663 _27460) (x : _27460 -> Prop) : (f x) = (@I ((_27460 -> Prop) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167114 (_27460 -> Prop) (type1143 _27460) f x). Qed.
Lemma lem1167116 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term456 _27459 _27460 _19609 P h') = (term458 _27459 _27460 _19609 P h').
Proof. exact (@lem1167115 _27460 (@List.Forall _27460) (term455 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167117 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167118 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term459 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167116 _27459 _27460 _19609 P h') (@lem1167117 _27460 t)). Qed.
Lemma lem1167120 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167121 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1167120 (list _27460) Prop f x). Qed.
Lemma lem1167122 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term459 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1167121 _27460 (term458 _27459 _27460 _19609 P h') t). Qed.
Lemma lem1167123 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167118 _27459 _27460 _19609 P h' t) (@lem1167122 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167124 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167112 _27459 _27460 _19609 P h' t) (@lem1167123 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167125 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term466 _27459 _27460 _19609 P h' t) = (term467 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167091) (@lem1167124 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1167127 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term468 _27459 _27460 _19609 P h' t) = (term469 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167126) (@lem1167125 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167128 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term377 _27459 _27460 _19609 h' _19608 P t' t) = (term470 _27459 _27460 _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1167127 _27459 _27460 _19609 P h' t) (@lem1167090 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1167129 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1167130 {_27459 : Type'} : (@List.Forall _27459) = (@List.Forall _27459).
Proof. exact (eq_refl (@List.Forall _27459)). Qed.
Lemma lem1167135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167136 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1167135 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1167138 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1167136 _27459 _27460 P h). Qed.
Lemma lem1167139 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167140 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term433 _27459 _27460 P h) = (term434 _27459 _27460 P h).
Proof. exact (MK_COMB (@lem1167130 _27459) (@lem1167138 _27459 _27460 P h)). Qed.
Lemma lem1167141 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term435 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1167140 _27459 _27460 P h) (@lem1167139 _27459 t')). Qed.
Lemma lem1167143 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167144 {_27459 : Type'} (f : type663 _27459) (x : _27459 -> Prop) : (f x) = (@I ((_27459 -> Prop) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1167143 (_27459 -> Prop) (type1143 _27459) f x). Qed.
Lemma lem1167145 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term434 _27459 _27460 P h) = (term436 _27459 _27460 P h).
Proof. exact (@lem1167144 _27459 (@List.Forall _27459) (@I (_27460 -> _27459 -> Prop) P h)). Qed.
Lemma lem1167146 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167147 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term437 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1167145 _27459 _27460 P h) (@lem1167146 _27459 t')). Qed.
Lemma lem1167149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167150 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1167149 (list _27459) Prop f x). Qed.
Lemma lem1167151 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term437 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1167150 _27459 (term436 _27459 _27460 P h) t'). Qed.
Lemma lem1167152 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1167147 _27459 _27460 P h t') (@lem1167151 _27459 _27460 P h t')). Qed.
Lemma lem1167153 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1167141 _27459 _27460 P h t') (@lem1167152 _27459 _27460 P h t')). Qed.
Lemma lem1167154 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term439 _27459 _27460 P h t') = (term440 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1167129) (@lem1167153 _27459 _27460 P h t')). Qed.
Lemma lem1167155 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1167162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167163 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1167162 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1167164 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1167163 _27459 _27460 P h). Qed.
Lemma lem1167165 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167166 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (@I (_27460 -> _27459 -> Prop) P h h').
Proof. exact (MK_COMB (@lem1167164 _27459 _27460 P h) (@lem1167165 _27459 h')). Qed.
Lemma lem1167168 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167169 {_27459 : Type'} (f : _27459 -> Prop) (x : _27459) : (f x) = (@I (_27459 -> Prop) f x).
Proof. exact (@lem1167168 _27459 Prop f x). Qed.
Lemma lem1167170 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (@I (_27460 -> _27459 -> Prop) P h h') = (term461 _27459 _27460 P h h').
Proof. exact (@lem1167169 _27459 (@I (_27460 -> _27459 -> Prop) P h) h'). Qed.
Lemma lem1167172 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (term461 _27459 _27460 P h h').
Proof. exact (TRANS (@lem1167166 _27459 _27460 P h h') (@lem1167170 _27459 _27460 P h h')). Qed.
Lemma lem1167173 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term471 _27459 _27460 P h h') = (term472 _27459 _27460 P h h').
Proof. exact (MK_COMB (@lem1167155) (@lem1167172 _27459 _27460 P h h')). Qed.
Lemma lem1167174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1167175 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term473 _27459 _27460 P h h') = (term474 _27459 _27460 P h h').
Proof. exact (MK_COMB (@lem1167174) (@lem1167173 _27459 _27460 P h h')). Qed.
Lemma lem1167176 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term375 _27459 _27460 h' P h t') = (term475 _27459 _27460 h' P h t').
Proof. exact (MK_COMB (@lem1167175 _27459 _27460 P h h') (@lem1167154 _27459 _27460 P h t')). Qed.
Lemma lem1167177 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1167178 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term379 _27459 _27460 h' P h t') = (term476 _27459 _27460 h' P h t').
Proof. exact (MK_COMB (@lem1167177) (@lem1167176 _27459 _27460 h' P h t')). Qed.
Lemma lem1167179 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term381 _27459 _27460 h _19609 h' _19608 P t' t) = (term477 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1167178 _27459 _27460 h' P h t') (@lem1167128 _27459 _27460 _19609 h' _19608 P t' t)). Qed.
Lemma lem1167180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1167181 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term391 _27459 _27460 h _19609 h' _19608 P t' t) = (term478 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1167180) (@lem1167179 _27459 _27460 h _19609 h' _19608 P t' t)). Qed.
Lemma lem1167182 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term393 _27459 _27460 _19609 h' _19608 P t' h t) = (term479 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167181 _27459 _27460 h _19609 h' _19608 P t' t) (@lem1167055 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1167183 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1167184 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1167189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167190 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167189 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1167192 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1167190 _27459 _27460 _19608 P). Qed.
Lemma lem1167193 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167200 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167201 {_27460 : Type'} (f : type1397 _27460) (x : _27460) : (f x) = (@I (_27460 -> (list _27460) -> list _27460) f x).
Proof. exact (@lem1167200 _27460 (type1138 _27460) f x). Qed.
Lemma lem1167202 {_27460 : Type'} (h : _27460) : (@cons _27460 h) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h).
Proof. exact (@lem1167201 _27460 (@cons _27460) h). Qed.
Lemma lem1167203 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167204 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t).
Proof. exact (MK_COMB (@lem1167202 _27460 h) (@lem1167203 _27460 t)). Qed.
Lemma lem1167206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167207 {_27460 : Type'} (f : type1138 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> list _27460) f x).
Proof. exact (@lem1167206 (list _27460) (list _27460) f x). Qed.
Lemma lem1167208 {_27460 : Type'} (h : _27460) (t : list _27460) : (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h t) = (term428 _27460 h t).
Proof. exact (@lem1167207 _27460 (@I (_27460 -> (list _27460) -> list _27460) (@cons _27460) h) t). Qed.
Lemma lem1167210 {_27460 : Type'} (h : _27460) (t : list _27460) : (@cons _27460 h t) = (term428 _27460 h t).
Proof. exact (TRANS (@lem1167204 _27460 h t) (@lem1167208 _27460 h t)). Qed.
Lemma lem1167211 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1167184 _27459 _27460) (@lem1167192 _27459 _27460 _19608 P)). Qed.
Lemma lem1167212 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term193 _27459 _27460 _19608 P t') = (term402 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1167211 _27459 _27460 _19608 P) (@lem1167193 _27459 t')). Qed.
Lemma lem1167213 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term429 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167212 _27459 _27460 _19608 P t') (@lem1167210 _27460 h t)). Qed.
Lemma lem1167215 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167216 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167215 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1167217 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1167216 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1167218 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167219 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term405 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1167217 _27459 _27460 _19608 P) (@lem1167218 _27459 t')). Qed.
Lemma lem1167221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167222 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167221 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1167223 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term405 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (@lem1167222 _27459 _27460 (term404 _27459 _27460 _19608 P) t'). Qed.
Lemma lem1167224 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (TRANS (@lem1167219 _27459 _27460 _19608 P t') (@lem1167223 _27459 _27460 _19608 P t')). Qed.
Lemma lem1167225 {_27460 : Type'} (h : _27460) (t : list _27460) : (term428 _27460 h t) = (term428 _27460 h t).
Proof. exact (eq_refl (term428 _27460 h t)). Qed.
Lemma lem1167226 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term430 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167224 _27459 _27460 _19608 P t') (@lem1167225 _27460 h t)). Qed.
Lemma lem1167228 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167229 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1167228 (list _27460) Prop f x). Qed.
Lemma lem1167230 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term430 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1167229 _27460 (term406 _27459 _27460 _19608 P t') (term428 _27460 h t)). Qed.
Lemma lem1167231 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term429 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1167226 _27459 _27460 _19608 P t' h t) (@lem1167230 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1167232 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term194 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (TRANS (@lem1167213 _27459 _27460 _19608 P t' h t) (@lem1167231 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1167233 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term366 _27459 _27460 _19608 P t' h t) = (term432 _27459 _27460 _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167183) (@lem1167232 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1167234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1167235 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1167242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167243 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167242 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1167244 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19609 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P).
Proof. exact (@lem1167243 _27459 _27460 _19609 P). Qed.
Lemma lem1167245 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167246 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h').
Proof. exact (MK_COMB (@lem1167244 _27459 _27460 _19609 P) (@lem1167245 _27459 h')). Qed.
Lemma lem1167248 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167249 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (x : _27459) : (f x) = (@I (_27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167248 _27459 (_27460 -> Prop) f x). Qed.
Lemma lem1167250 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (@lem1167249 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P) h'). Qed.
Lemma lem1167252 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (TRANS (@lem1167246 _27459 _27460 _19609 P h') (@lem1167250 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167253 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167254 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term266 _27459 _27460 _19609 P h') = (term456 _27459 _27460 _19609 P h').
Proof. exact (MK_COMB (@lem1167235 _27460) (@lem1167252 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167255 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term457 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167254 _27459 _27460 _19609 P h') (@lem1167253 _27460 t)). Qed.
Lemma lem1167257 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167258 {_27460 : Type'} (f : type663 _27460) (x : _27460 -> Prop) : (f x) = (@I ((_27460 -> Prop) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167257 (_27460 -> Prop) (type1143 _27460) f x). Qed.
Lemma lem1167259 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term456 _27459 _27460 _19609 P h') = (term458 _27459 _27460 _19609 P h').
Proof. exact (@lem1167258 _27460 (@List.Forall _27460) (term455 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167260 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167261 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term459 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167259 _27459 _27460 _19609 P h') (@lem1167260 _27460 t)). Qed.
Lemma lem1167263 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167264 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1167263 (list _27460) Prop f x). Qed.
Lemma lem1167265 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term459 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1167264 _27460 (term458 _27459 _27460 _19609 P h') t). Qed.
Lemma lem1167266 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167261 _27459 _27460 _19609 P h' t) (@lem1167265 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167267 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167255 _27459 _27460 _19609 P h' t) (@lem1167266 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167268 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term466 _27459 _27460 _19609 P h' t) = (term467 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167234) (@lem1167267 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167269 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1167276 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167277 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1167276 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1167278 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1167277 _27459 _27460 P h). Qed.
Lemma lem1167279 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167280 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (@I (_27460 -> _27459 -> Prop) P h h').
Proof. exact (MK_COMB (@lem1167278 _27459 _27460 P h) (@lem1167279 _27459 h')). Qed.
Lemma lem1167282 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167283 {_27459 : Type'} (f : _27459 -> Prop) (x : _27459) : (f x) = (@I (_27459 -> Prop) f x).
Proof. exact (@lem1167282 _27459 Prop f x). Qed.
Lemma lem1167284 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (@I (_27460 -> _27459 -> Prop) P h h') = (term461 _27459 _27460 P h h').
Proof. exact (@lem1167283 _27459 (@I (_27460 -> _27459 -> Prop) P h) h'). Qed.
Lemma lem1167286 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (term461 _27459 _27460 P h h').
Proof. exact (TRANS (@lem1167280 _27459 _27460 P h h') (@lem1167284 _27459 _27460 P h h')). Qed.
Lemma lem1167287 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term471 _27459 _27460 P h h') = (term472 _27459 _27460 P h h').
Proof. exact (MK_COMB (@lem1167269) (@lem1167286 _27459 _27460 P h h')). Qed.
Lemma lem1167288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1167289 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term473 _27459 _27460 P h h') = (term474 _27459 _27460 P h h').
Proof. exact (MK_COMB (@lem1167288) (@lem1167287 _27459 _27460 P h h')). Qed.
Lemma lem1167290 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term384 _27459 _27460 h _19609 P h' t) = (term480 _27459 _27460 h _19609 P h' t).
Proof. exact (MK_COMB (@lem1167289 _27459 _27460 P h h') (@lem1167268 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1167292 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term386 _27459 _27460 h _19609 P h' t) = (term481 _27459 _27460 h _19609 P h' t).
Proof. exact (MK_COMB (@lem1167291) (@lem1167290 _27459 _27460 h _19609 P h' t)). Qed.
Lemma lem1167293 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term388 _27459 _27460 _19609 h' _19608 P t' h t) = (term482 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167292 _27459 _27460 h _19609 P h' t) (@lem1167233 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1167294 {_27459 _27460 : Type'} : (@ALLPAIRS _27460 _27459) = (@ALLPAIRS _27460 _27459).
Proof. exact (eq_refl (@ALLPAIRS _27460 _27459)). Qed.
Lemma lem1167299 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167300 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167299 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1167302 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19608 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P).
Proof. exact (@lem1167300 _27459 _27460 _19608 P). Qed.
Lemma lem1167303 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167304 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167305 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term191 _27459 _27460 _19608 P) = (term401 _27459 _27460 _19608 P).
Proof. exact (MK_COMB (@lem1167294 _27459 _27460) (@lem1167302 _27459 _27460 _19608 P)). Qed.
Lemma lem1167306 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term193 _27459 _27460 _19608 P t') = (term402 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1167305 _27459 _27460 _19608 P) (@lem1167303 _27459 t')). Qed.
Lemma lem1167307 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P t' t) = (term403 _27459 _27460 _19608 P t' t).
Proof. exact (MK_COMB (@lem1167306 _27459 _27460 _19608 P t') (@lem1167304 _27460 t)). Qed.
Lemma lem1167309 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167310 {_27459 _27460 : Type'} (f : type462 _27459 _27460) (x : type1413 _27459 _27460) : (f x) = (@I ((_27459 -> _27460 -> Prop) -> (list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167309 (type1413 _27459 _27460) (type1135 _27459 _27460) f x). Qed.
Lemma lem1167311 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (term401 _27459 _27460 _19608 P) = (term404 _27459 _27460 _19608 P).
Proof. exact (@lem1167310 _27459 _27460 (@ALLPAIRS _27460 _27459) (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19608 P)). Qed.
Lemma lem1167312 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167313 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term405 _27459 _27460 _19608 P t').
Proof. exact (MK_COMB (@lem1167311 _27459 _27460 _19608 P) (@lem1167312 _27459 t')). Qed.
Lemma lem1167315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167316 {_27459 _27460 : Type'} (f : type1135 _27459 _27460) (x : list _27459) : (f x) = (@I ((list _27459) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167315 (list _27459) (type1143 _27460) f x). Qed.
Lemma lem1167317 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term405 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (@lem1167316 _27459 _27460 (term404 _27459 _27460 _19608 P) t'). Qed.
Lemma lem1167318 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) : (term402 _27459 _27460 _19608 P t') = (term406 _27459 _27460 _19608 P t').
Proof. exact (TRANS (@lem1167313 _27459 _27460 _19608 P t') (@lem1167317 _27459 _27460 _19608 P t')). Qed.
Lemma lem1167319 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167320 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P t' t) = (term407 _27459 _27460 _19608 P t' t).
Proof. exact (MK_COMB (@lem1167318 _27459 _27460 _19608 P t') (@lem1167319 _27460 t)). Qed.
Lemma lem1167322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167323 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1167322 (list _27460) Prop f x). Qed.
Lemma lem1167324 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term407 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (@lem1167323 _27460 (term406 _27459 _27460 _19608 P t') t). Qed.
Lemma lem1167325 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term403 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (TRANS (@lem1167320 _27459 _27460 _19608 P t' t) (@lem1167324 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1167326 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term196 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (TRANS (@lem1167307 _27459 _27460 _19608 P t' t) (@lem1167325 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1167327 {_27460 : Type'} : (@List.Forall _27460) = (@List.Forall _27460).
Proof. exact (eq_refl (@List.Forall _27460)). Qed.
Lemma lem1167334 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167335 {_27459 _27460 : Type'} (f : type738 _27459 _27460) (x : type1470 _27459 _27460) : (f x) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167334 (type1470 _27459 _27460) (type1413 _27459 _27460) f x). Qed.
Lemma lem1167336 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) : (_19609 P) = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P).
Proof. exact (@lem1167335 _27459 _27460 _19609 P). Qed.
Lemma lem1167337 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167338 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h').
Proof. exact (MK_COMB (@lem1167336 _27459 _27460 _19609 P) (@lem1167337 _27459 h')). Qed.
Lemma lem1167340 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167341 {_27459 _27460 : Type'} (f : type1413 _27459 _27460) (x : _27459) : (f x) = (@I (_27459 -> _27460 -> Prop) f x).
Proof. exact (@lem1167340 _27459 (_27460 -> Prop) f x). Qed.
Lemma lem1167342 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (@lem1167341 _27459 _27460 (@I ((_27460 -> _27459 -> Prop) -> _27459 -> _27460 -> Prop) _19609 P) h'). Qed.
Lemma lem1167344 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (_19609 P h') = (term455 _27459 _27460 _19609 P h').
Proof. exact (TRANS (@lem1167338 _27459 _27460 _19609 P h') (@lem1167342 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167345 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167346 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term266 _27459 _27460 _19609 P h') = (term456 _27459 _27460 _19609 P h').
Proof. exact (MK_COMB (@lem1167327 _27460) (@lem1167344 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167347 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term457 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167346 _27459 _27460 _19609 P h') (@lem1167345 _27460 t)). Qed.
Lemma lem1167349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167350 {_27460 : Type'} (f : type663 _27460) (x : _27460 -> Prop) : (f x) = (@I ((_27460 -> Prop) -> (list _27460) -> Prop) f x).
Proof. exact (@lem1167349 (_27460 -> Prop) (type1143 _27460) f x). Qed.
Lemma lem1167351 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) : (term456 _27459 _27460 _19609 P h') = (term458 _27459 _27460 _19609 P h').
Proof. exact (@lem1167350 _27460 (@List.Forall _27460) (term455 _27459 _27460 _19609 P h')). Qed.
Lemma lem1167352 {_27460 : Type'} (t : list _27460) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1167353 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term459 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167351 _27459 _27460 _19609 P h') (@lem1167352 _27460 t)). Qed.
Lemma lem1167355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167356 {_27460 : Type'} (f : type1143 _27460) (x : list _27460) : (f x) = (@I ((list _27460) -> Prop) f x).
Proof. exact (@lem1167355 (list _27460) Prop f x). Qed.
Lemma lem1167357 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term459 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1167356 _27460 (term458 _27459 _27460 _19609 P h') t). Qed.
Lemma lem1167358 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term457 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167353 _27459 _27460 _19609 P h' t) (@lem1167357 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167359 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term267 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (TRANS (@lem1167347 _27459 _27460 _19609 P h' t) (@lem1167358 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1167361 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term271 _27459 _27460 _19609 P h' t) = (term483 _27459 _27460 _19609 P h' t).
Proof. exact (MK_COMB (@lem1167360) (@lem1167359 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1167362 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term272 _27459 _27460 _19609 h' _19608 P t' t) = (term484 _27459 _27460 _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1167361 _27459 _27460 _19609 P h' t) (@lem1167326 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1167363 {_27459 : Type'} : (@List.Forall _27459) = (@List.Forall _27459).
Proof. exact (eq_refl (@List.Forall _27459)). Qed.
Lemma lem1167368 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167369 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1167368 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1167371 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1167369 _27459 _27460 P h). Qed.
Lemma lem1167372 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167373 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term433 _27459 _27460 P h) = (term434 _27459 _27460 P h).
Proof. exact (MK_COMB (@lem1167363 _27459) (@lem1167371 _27459 _27460 P h)). Qed.
Lemma lem1167374 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term435 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1167373 _27459 _27460 P h) (@lem1167372 _27459 t')). Qed.
Lemma lem1167376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167377 {_27459 : Type'} (f : type663 _27459) (x : _27459 -> Prop) : (f x) = (@I ((_27459 -> Prop) -> (list _27459) -> Prop) f x).
Proof. exact (@lem1167376 (_27459 -> Prop) (type1143 _27459) f x). Qed.
Lemma lem1167378 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (term434 _27459 _27460 P h) = (term436 _27459 _27460 P h).
Proof. exact (@lem1167377 _27459 (@List.Forall _27459) (@I (_27460 -> _27459 -> Prop) P h)). Qed.
Lemma lem1167379 {_27459 : Type'} (t' : list _27459) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1167380 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term437 _27459 _27460 P h t').
Proof. exact (MK_COMB (@lem1167378 _27459 _27460 P h) (@lem1167379 _27459 t')). Qed.
Lemma lem1167382 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167383 {_27459 : Type'} (f : type1143 _27459) (x : list _27459) : (f x) = (@I ((list _27459) -> Prop) f x).
Proof. exact (@lem1167382 (list _27459) Prop f x). Qed.
Lemma lem1167384 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term437 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1167383 _27459 (term436 _27459 _27460 P h) t'). Qed.
Lemma lem1167385 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term435 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1167380 _27459 _27460 P h t') (@lem1167384 _27459 _27460 P h t')). Qed.
Lemma lem1167386 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term365 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (TRANS (@lem1167374 _27459 _27460 P h t') (@lem1167385 _27459 _27460 P h t')). Qed.
Lemma lem1167393 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167394 {_27459 _27460 : Type'} (f : type1470 _27459 _27460) (x : _27460) : (f x) = (@I (_27460 -> _27459 -> Prop) f x).
Proof. exact (@lem1167393 _27460 (_27459 -> Prop) f x). Qed.
Lemma lem1167395 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : (P h) = (@I (_27460 -> _27459 -> Prop) P h).
Proof. exact (@lem1167394 _27459 _27460 P h). Qed.
Lemma lem1167396 {_27459 : Type'} (h' : _27459) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1167397 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (@I (_27460 -> _27459 -> Prop) P h h').
Proof. exact (MK_COMB (@lem1167395 _27459 _27460 P h) (@lem1167396 _27459 h')). Qed.
Lemma lem1167399 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1167400 {_27459 : Type'} (f : _27459 -> Prop) (x : _27459) : (f x) = (@I (_27459 -> Prop) f x).
Proof. exact (@lem1167399 _27459 Prop f x). Qed.
Lemma lem1167401 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (@I (_27460 -> _27459 -> Prop) P h h') = (term461 _27459 _27460 P h h').
Proof. exact (@lem1167400 _27459 (@I (_27460 -> _27459 -> Prop) P h) h'). Qed.
Lemma lem1167403 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (P h h') = (term461 _27459 _27460 P h h').
Proof. exact (TRANS (@lem1167397 _27459 _27460 P h h') (@lem1167401 _27459 _27460 P h h')). Qed.
Lemma lem1167404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1167405 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term150 _27459 _27460 P h h') = (term462 _27459 _27460 P h h').
Proof. exact (MK_COMB (@lem1167404) (@lem1167403 _27459 _27460 P h h')). Qed.
Lemma lem1167406 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term116 _27459 _27460 h' P h t') = (term485 _27459 _27460 h' P h t').
Proof. exact (MK_COMB (@lem1167405 _27459 _27460 P h h') (@lem1167386 _27459 _27460 P h t')). Qed.
Lemma lem1167407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1167408 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term118 _27459 _27460 h' P h t') = (term486 _27459 _27460 h' P h t').
Proof. exact (MK_COMB (@lem1167407) (@lem1167406 _27459 _27460 h' P h t')). Qed.
Lemma lem1167409 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term273 _27459 _27460 h _19609 h' _19608 P t' t) = (term487 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1167408 _27459 _27460 h' P h t') (@lem1167362 _27459 _27460 _19609 h' _19608 P t' t)). Qed.
Lemma lem1167410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1167411 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term394 _27459 _27460 h _19609 h' _19608 P t' t) = (term488 _27459 _27460 h _19609 h' _19608 P t' t).
Proof. exact (MK_COMB (@lem1167410) (@lem1167409 _27459 _27460 h _19609 h' _19608 P t' t)). Qed.
Lemma lem1167412 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term396 _27459 _27460 _19609 h' _19608 P t' h t) = (term489 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167411 _27459 _27460 h _19609 h' _19608 P t' t) (@lem1167293 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1167413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1167414 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term398 _27459 _27460 _19609 h' _19608 P t' h t) = (term490 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167413) (@lem1167412 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1167415 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term400 _27459 _27460 _19609 h' _19608 P t' h t) = (term491 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (MK_COMB (@lem1167414 _27459 _27460 _19609 h' _19608 P t' h t) (@lem1167182 _27459 _27460 _19609 h' _19608 P t' h t)). Qed.
Lemma lem1167416 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term332 _27459 _27460 _19609 h' _19608 P t' h t) : term491 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (EQ_MP (@lem1167415 _27459 _27460 _19609 h' _19608 P t' h t) (@lem1166430 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167417 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term418 _27459 _27460 _19608 P t.
Proof. exact (proj2 (@lem1166730 _27459 _27460 _19608 P t h1)). Qed.
Lemma lem1167418 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term425 _27459 _27460 _19608 P t.
Proof. exact (proj1 (@lem1166730 _27459 _27460 _19608 P t h1)). Qed.
Lemma lem1167421 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term489 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167422 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term479 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167423 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term482 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (proj2 (@lem1167421 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167424 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term487 _27459 _27460 h _19609 h' _19608 P t' t.
Proof. exact (proj1 (@lem1167421 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167425 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term484 _27459 _27460 _19609 h' _19608 P t' t.
Proof. exact (proj2 (@lem1167424 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167426 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term485 _27459 _27460 h' P h t'.
Proof. exact (proj1 (@lem1167424 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167431 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term480 _27459 _27460 h _19609 P h' t) : term480 _27459 _27460 h _19609 P h' t.
Proof. exact (h1). Qed.
Lemma lem1167436 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term445 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167442 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term443 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167436 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167446 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term445 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167452 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term443 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167446 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167455 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term452 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167456 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term445 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167462 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term443 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167456 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167465 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term465 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (proj2 (@lem1167422 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167466 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term477 _27459 _27460 h _19609 h' _19608 P t' t.
Proof. exact (proj1 (@lem1167422 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167468 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term463 _27459 _27460 h _19609 P h' t.
Proof. exact (proj1 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1167471 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term475 _27459 _27460 h' P h t') : term475 _27459 _27460 h' P h t'.
Proof. exact (h1). Qed.
Lemma lem1167472 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (h1 : term470 _27459 _27460 _19609 h' _19608 P t' t) : term470 _27459 _27460 _19609 h' _19608 P t' t.
Proof. exact (h1). Qed.
Lemma lem1167476 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term445 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167482 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term443 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167476 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167485 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term452 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167486 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term445 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167488 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term448 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167485 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167492 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term443 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167486 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167498 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term445 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167504 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term443 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167498 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167507 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term452 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167508 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term445 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1167510 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term448 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167507 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167514 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term443 _27459 _27460 h P t t'.
Proof. exact (proj1 (@lem1167508 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1167610 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term472 _27459 _27460 P h h'.
Proof. exact (h1). Qed.
Lemma lem1167724 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1167818 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term472 _27459 _27460 P h h'.
Proof. exact (h1). Qed.
Lemma lem1167920 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term467 _27459 _27460 _19609 P h' t.
Proof. exact (h1). Qed.
Lemma lem1168034 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1168128 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term467 _27459 _27460 _19609 P h' t.
Proof. exact (h1). Qed.
Lemma lem1168230 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1168344 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1168362 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term423 _27459 _27460 _19608 P m t) = (term423 _27459 _27460 _19608 P m t).
Proof. exact (eq_refl (term423 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1168363 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term424 _27459 _27460 _19608 P t) = (term424 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1168362 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1168364 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1168366 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term425 _27459 _27460 _19608 P t) = (term425 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1168364 _27459) (@lem1168363 _27459 _27460 _19608 P t)). Qed.
Lemma lem1168367 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term425 _27459 _27460 _19608 P t.
Proof. exact (EQ_MP (@lem1168366 _27459 _27460 _19608 P t) (@lem1167418 _27459 _27460 _19608 P t h1)). Qed.
Lemma lem1168446 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) (h1 : term413 _27459 _27460 P t t') : term413 _27459 _27460 P t t'.
Proof. exact (h1). Qed.
Lemma lem1168536 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term472 _27459 _27460 P h h'.
Proof. exact (h1). Qed.
Lemma lem1168834 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1169132 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term467 _27459 _27460 _19609 P h' t.
Proof. exact (h1). Qed.
Lemma lem1169371 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (m : list _27459) (t : list _27460) : (term416 _27459 _27460 _19608 P m t) = (term416 _27459 _27460 _19608 P m t).
Proof. exact (eq_refl (term416 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1169372 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term417 _27459 _27460 _19608 P t) = (term417 _27459 _27460 _19608 P t).
Proof. exact (fun_ext (fun m : list _27459 => @lem1169371 _27459 _27460 _19608 P m t)). Qed.
Lemma lem1169373 {_27459 : Type'} : (@all (list _27459)) = (@all (list _27459)).
Proof. exact (eq_refl (@all (list _27459))). Qed.
Lemma lem1169375 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) : (term418 _27459 _27460 _19608 P t) = (term418 _27459 _27460 _19608 P t).
Proof. exact (MK_COMB (@lem1169373 _27459) (@lem1169372 _27459 _27460 _19608 P t)). Qed.
Lemma lem1169376 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term418 _27459 _27460 _19608 P t.
Proof. exact (EQ_MP (@lem1169375 _27459 _27460 _19608 P t) (@lem1167417 _27459 _27460 _19608 P t h1)). Qed.
Lemma lem1169430 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (h1 : term420 _27459 _27460 _19608 P t' t) : term420 _27459 _27460 _19608 P t' t.
Proof. exact (h1). Qed.
Lemma lem1169885 {_27459 _27460 : Type'} (_19692 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term492 _27459 _27460 _19608 P t _19692.
Proof. exact (@lem1168367 _27459 _27460 _19608 P t h1 _19692). Qed.
Lemma lem1169886 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19692 : list _27459) (t : list _27460) : (term492 _27459 _27460 _19608 P t _19692) = (term423 _27459 _27460 _19608 P _19692 t).
Proof. exact (eq_refl (term492 _27459 _27460 _19608 P t _19692)). Qed.
Lemma lem1170188 {_27459 _27460 : Type'} (_19793 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term493 _27459 _27460 _19608 P t _19793.
Proof. exact (@lem1169376 _27459 _27460 _19608 P t h1 _19793). Qed.
Lemma lem1170189 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19793 : list _27459) (t : list _27460) : (term493 _27459 _27460 _19608 P t _19793) = (term416 _27459 _27460 _19608 P _19793 t).
Proof. exact (eq_refl (term493 _27459 _27460 _19608 P t _19793)). Qed.
Lemma lem1170304 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term472 _27459 _27460 P h h'.
Proof. exact (h1). Qed.
Lemma lem1170350 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1170386 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term472 _27459 _27460 P h h'.
Proof. exact (h1). Qed.
Lemma lem1170426 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term467 _27459 _27460 _19609 P h' t.
Proof. exact (h1). Qed.
Lemma lem1170472 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1170508 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term467 _27459 _27460 _19609 P h' t.
Proof. exact (h1). Qed.
Lemma lem1170548 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (h1). Qed.
Lemma lem1170594 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1170602 {_27459 _27460 : Type'} (_19692 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term423 _27459 _27460 _19608 P _19692 t.
Proof. exact (EQ_MP (@lem1169886 _27459 _27460 _19608 P _19692 t) (@lem1169885 _27459 _27460 _19692 _19608 P t h1)). Qed.
Lemma lem1170634 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) (h1 : term413 _27459 _27460 P t t') : term413 _27459 _27460 P t t'.
Proof. exact (h1). Qed.
Lemma lem1170668 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term472 _27459 _27460 P h h'.
Proof. exact (h1). Qed.
Lemma lem1170710 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167476 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1170748 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167476 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1170784 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term440 _27459 _27460 P h t'.
Proof. exact (h1). Qed.
Lemma lem1170826 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167486 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1170864 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167486 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1170900 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term467 _27459 _27460 _19609 P h' t.
Proof. exact (h1). Qed.
Lemma lem1170942 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167498 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1170980 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167498 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1170996 {_27459 _27460 : Type'} (_19793 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term416 _27459 _27460 _19608 P _19793 t.
Proof. exact (EQ_MP (@lem1170189 _27459 _27460 _19608 P _19793 t) (@lem1170188 _27459 _27460 _19793 _19608 P t h1)). Qed.
Lemma lem1171016 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (h1 : term420 _27459 _27460 _19608 P t' t) : term420 _27459 _27460 _19608 P t' t.
Proof. exact (h1). Qed.
Lemma lem1171058 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167508 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1171096 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term432 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167508 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1171379 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term461 _27459 _27460 P h h'.
Proof. exact (proj1 (@lem1167426 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1171380 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term494 _27459 _27460 P h h'.
Proof. exact (fun h0 : term472 _27459 _27460 P h h' => @lem1171379 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1171382 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1171383 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term494 _27459 _27460 P h h') = (term461 _27459 _27460 P h h').
Proof. exact (@lem1171382 (term461 _27459 _27460 P h h')). Qed.
Lemma lem1171384 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term461 _27459 _27460 P h h'.
Proof. exact (EQ_MP (@lem1171383 _27459 _27460 P h h') (@lem1171380 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1171387 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1171389 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term472 _27459 _27460 P h h') = (term496 _27459 _27460 P h h').
Proof. exact (@lem1171387 (term461 _27459 _27460 P h h')). Qed.
Lemma lem1171392 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term496 _27459 _27460 P h h'.
Proof. exact (EQ_MP (@lem1171389 _27459 _27460 P h h') (@lem1170304 _27459 _27460 P h h' h1)). Qed.
Lemma lem1171395 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1171392 _27459 _27460 P h h' h1 (@lem1171384 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1171396 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1171395 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1171398 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1171399 : term497 = False.
Proof. exact (@lem1171398 False). Qed.
Lemma lem1171400 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1171399) (@lem1171396 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1171681 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (proj2 (@lem1167426 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1171682 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term498 _27459 _27460 P h t'.
Proof. exact (fun h0 : term440 _27459 _27460 P h t' => @lem1171681 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1171684 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1171685 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term498 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1171684 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1171686 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1171685 _27459 _27460 P h t') (@lem1171682 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1171689 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1171691 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term440 _27459 _27460 P h t') = (term499 _27459 _27460 P h t').
Proof. exact (@lem1171689 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1171694 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term499 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1171691 _27459 _27460 P h t') (@lem1170350 _27459 _27460 P h t' h1)). Qed.
Lemma lem1171697 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1171694 _27459 _27460 P h t' h1 (@lem1171686 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1171698 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1171697 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1171700 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1171701 : term497 = False.
Proof. exact (@lem1171700 False). Qed.
Lemma lem1171702 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1171701) (@lem1171698 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1171983 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term461 _27459 _27460 P h h'.
Proof. exact (proj1 (@lem1167426 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1171984 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term494 _27459 _27460 P h h'.
Proof. exact (fun h0 : term472 _27459 _27460 P h h' => @lem1171983 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1171986 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1171987 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term494 _27459 _27460 P h h') = (term461 _27459 _27460 P h h').
Proof. exact (@lem1171986 (term461 _27459 _27460 P h h')). Qed.
Lemma lem1171988 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term461 _27459 _27460 P h h'.
Proof. exact (EQ_MP (@lem1171987 _27459 _27460 P h h') (@lem1171984 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1171991 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1171993 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term472 _27459 _27460 P h h') = (term496 _27459 _27460 P h h').
Proof. exact (@lem1171991 (term461 _27459 _27460 P h h')). Qed.
Lemma lem1171996 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term496 _27459 _27460 P h h'.
Proof. exact (EQ_MP (@lem1171993 _27459 _27460 P h h') (@lem1170386 _27459 _27460 P h h' h1)). Qed.
Lemma lem1171999 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1171996 _27459 _27460 P h h' h1 (@lem1171988 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1172000 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1171999 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1172002 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1172003 : term497 = False.
Proof. exact (@lem1172002 False). Qed.
Lemma lem1172004 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1172003) (@lem1172000 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1172285 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term460 _27459 _27460 _19609 P h' t.
Proof. exact (proj1 (@lem1167425 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1172286 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term500 _27459 _27460 _19609 P h' t.
Proof. exact (fun h0 : term467 _27459 _27460 _19609 P h' t => @lem1172285 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1172288 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1172289 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term500 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1172288 (term460 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1172290 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term460 _27459 _27460 _19609 P h' t.
Proof. exact (EQ_MP (@lem1172289 _27459 _27460 _19609 P h' t) (@lem1172286 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1172293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1172295 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term467 _27459 _27460 _19609 P h' t) = (term501 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1172293 (term460 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1172298 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term501 _27459 _27460 _19609 P h' t.
Proof. exact (EQ_MP (@lem1172295 _27459 _27460 _19609 P h' t) (@lem1170426 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1172301 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1172298 _27459 _27460 _19609 P h' t h1 (@lem1172290 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1172302 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1172301 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1172304 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1172305 : term497 = False.
Proof. exact (@lem1172304 False). Qed.
Lemma lem1172306 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1172305) (@lem1172302 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1172587 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (proj2 (@lem1167426 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1172588 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term498 _27459 _27460 P h t'.
Proof. exact (fun h0 : term440 _27459 _27460 P h t' => @lem1172587 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1172590 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1172591 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term498 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1172590 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1172592 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1172591 _27459 _27460 P h t') (@lem1172588 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1172595 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1172597 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term440 _27459 _27460 P h t') = (term499 _27459 _27460 P h t').
Proof. exact (@lem1172595 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1172600 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term499 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1172597 _27459 _27460 P h t') (@lem1170472 _27459 _27460 P h t' h1)). Qed.
Lemma lem1172603 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1172600 _27459 _27460 P h t' h1 (@lem1172592 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1172604 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1172603 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1172606 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1172607 : term497 = False.
Proof. exact (@lem1172606 False). Qed.
Lemma lem1172608 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1172607) (@lem1172604 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1172889 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term460 _27459 _27460 _19609 P h' t.
Proof. exact (proj1 (@lem1167425 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1172890 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term500 _27459 _27460 _19609 P h' t.
Proof. exact (fun h0 : term467 _27459 _27460 _19609 P h' t => @lem1172889 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1172892 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1172893 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term500 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1172892 (term460 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1172894 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term460 _27459 _27460 _19609 P h' t.
Proof. exact (EQ_MP (@lem1172893 _27459 _27460 _19609 P h' t) (@lem1172890 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1172897 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1172899 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term467 _27459 _27460 _19609 P h' t) = (term501 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1172897 (term460 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1172902 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term501 _27459 _27460 _19609 P h' t.
Proof. exact (EQ_MP (@lem1172899 _27459 _27460 _19609 P h' t) (@lem1170508 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1172905 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1172902 _27459 _27460 _19609 P h' t h1 (@lem1172894 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1172906 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1172905 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1172908 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1172909 : term497 = False.
Proof. exact (@lem1172908 False). Qed.
Lemma lem1172910 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1172909) (@lem1172906 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1173191 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167455 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1173192 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1173191 _27459 _27460 _19608 P t' h t h1). Qed.
Lemma lem1173194 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1173195 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1173194 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1173196 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1173195 _27459 _27460 _19608 P t' h t) (@lem1173192 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1173199 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1173201 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1173199 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1173204 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1173201 _27459 _27460 _19608 P t' h t) (@lem1170548 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1173207 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (@lem1173204 _27459 _27460 _19608 P t' h t h1 (@lem1173196 _27459 _27460 _19608 P t' h t h2)). Qed.
Lemma lem1173208 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1173207 _27459 _27460 _19608 P t' h t h1 h2). Qed.
Lemma lem1173210 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1173211 : term497 = False.
Proof. exact (@lem1173210 False). Qed.
Lemma lem1173212 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1173211) (@lem1173208 _27459 _27460 _19608 P t' h t h1 h2)). Qed.
Lemma lem1173493 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (proj2 (@lem1167426 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1173494 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term498 _27459 _27460 P h t'.
Proof. exact (fun h0 : term440 _27459 _27460 P h t' => @lem1173493 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1173496 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1173497 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term498 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1173496 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1173498 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1173497 _27459 _27460 P h t') (@lem1173494 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1173501 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1173503 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term440 _27459 _27460 P h t') = (term499 _27459 _27460 P h t').
Proof. exact (@lem1173501 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1173506 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term499 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1173503 _27459 _27460 P h t') (@lem1170594 _27459 _27460 P h t' h1)). Qed.
Lemma lem1173509 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1173506 _27459 _27460 P h t' h1 (@lem1173498 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1173510 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1173509 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1173512 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1173513 : term497 = False.
Proof. exact (@lem1173512 False). Qed.
Lemma lem1173514 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1173513) (@lem1173510 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1173795 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term408 _27459 _27460 _19608 P t' t.
Proof. exact (proj2 (@lem1167425 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1173796 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term504 _27459 _27460 _19608 P t' t.
Proof. exact (fun h0 : term420 _27459 _27460 _19608 P t' t => @lem1173795 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1173798 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1173799 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term504 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (@lem1173798 (term408 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1173800 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term408 _27459 _27460 _19608 P t' t.
Proof. exact (EQ_MP (@lem1173799 _27459 _27460 _19608 P t' t) (@lem1173796 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1173802 (b : Prop) (a : Prop) : (a \/ b) = (term505 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1173803 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19692 : list _27459) : (term423 _27459 _27460 _19608 P _19692 t) = (term506 _27459 _27460 _19608 P t _19692).
Proof. exact (@lem1173802 (term420 _27459 _27460 _19608 P _19692 t) (term411 _27459 _27460 P t _19692)). Qed.
Lemma lem1173805 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1173806 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19692 : list _27459) (t : list _27460) : (term507 _27459 _27460 _19608 P _19692 t) = (term408 _27459 _27460 _19608 P _19692 t).
Proof. exact (@lem1173805 (term408 _27459 _27460 _19608 P _19692 t)). Qed.
Lemma lem1173807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1173808 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19692 : list _27459) (t : list _27460) : (term508 _27459 _27460 _19608 P _19692 t) = (term509 _27459 _27460 _19608 P _19692 t).
Proof. exact (MK_COMB (@lem1173807) (@lem1173806 _27459 _27460 _19608 P _19692 t)). Qed.
Lemma lem1173809 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (_19692 : list _27459) : (term411 _27459 _27460 P t _19692) = (term411 _27459 _27460 P t _19692).
Proof. exact (eq_refl (term411 _27459 _27460 P t _19692)). Qed.
Lemma lem1173810 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19692 : list _27459) : (term506 _27459 _27460 _19608 P t _19692) = (term510 _27459 _27460 _19608 P t _19692).
Proof. exact (MK_COMB (@lem1173808 _27459 _27460 _19608 P _19692 t) (@lem1173809 _27459 _27460 P t _19692)). Qed.
Lemma lem1173811 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19692 : list _27459) : (term423 _27459 _27460 _19608 P _19692 t) = (term510 _27459 _27460 _19608 P t _19692).
Proof. exact (TRANS (@lem1173803 _27459 _27460 _19608 P t _19692) (@lem1173810 _27459 _27460 _19608 P t _19692)). Qed.
Lemma lem1173814 {_27459 _27460 : Type'} (_19692 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term510 _27459 _27460 _19608 P t _19692.
Proof. exact (EQ_MP (@lem1173811 _27459 _27460 _19608 P t _19692) (@lem1170602 _27459 _27460 _19692 _19608 P t h1)). Qed.
Lemma lem1173815 {_27459 _27460 : Type'} (_19692 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term510 _27459 _27460 _19608 P t _19692.
Proof. exact (@lem1173814 _27459 _27460 _19692 _19608 P t h1). Qed.
Lemma lem1173816 {_27459 _27460 : Type'} (t' : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term510 _27459 _27460 _19608 P t t'.
Proof. exact (@lem1173815 _27459 _27460 t' _19608 P t h1). Qed.
Lemma lem1173819 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term411 _27459 _27460 P t t'.
Proof. exact (@lem1173816 _27459 _27460 t' _19608 P t h1 (@lem1173800 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1173820 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term511 _27459 _27460 P t t'.
Proof. exact (fun h0 : term413 _27459 _27460 P t t' => @lem1173819 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1173822 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1173823 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term511 _27459 _27460 P t t') = (term411 _27459 _27460 P t t').
Proof. exact (@lem1173822 (term411 _27459 _27460 P t t')). Qed.
Lemma lem1173824 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term411 _27459 _27460 P t t'.
Proof. exact (EQ_MP (@lem1173823 _27459 _27460 P t t') (@lem1173820 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1173827 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1173829 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term413 _27459 _27460 P t t') = (term512 _27459 _27460 P t t').
Proof. exact (@lem1173827 (term411 _27459 _27460 P t t')). Qed.
Lemma lem1173832 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) (h1 : term413 _27459 _27460 P t t') : term512 _27459 _27460 P t t'.
Proof. exact (EQ_MP (@lem1173829 _27459 _27460 P t t') (@lem1170634 _27459 _27460 P t t' h1)). Qed.
Lemma lem1173835 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1173832 _27459 _27460 P t t' h2 (@lem1173824 _27459 _27460 _19609 h' _19608 P t' h t h1 h3)). Qed.
Lemma lem1173836 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1173835 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3). Qed.
Lemma lem1173838 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1173839 : term497 = False.
Proof. exact (@lem1173838 False). Qed.
Lemma lem1173840 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1173839) (@lem1173836 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3)). Qed.
Lemma lem1174121 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term461 _27459 _27460 P h h'.
Proof. exact (proj1 (@lem1167468 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1174122 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term494 _27459 _27460 P h h'.
Proof. exact (fun h0 : term472 _27459 _27460 P h h' => @lem1174121 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1174124 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1174125 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term494 _27459 _27460 P h h') = (term461 _27459 _27460 P h h').
Proof. exact (@lem1174124 (term461 _27459 _27460 P h h')). Qed.
Lemma lem1174126 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term461 _27459 _27460 P h h'.
Proof. exact (EQ_MP (@lem1174125 _27459 _27460 P h h') (@lem1174122 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1174129 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1174131 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) : (term472 _27459 _27460 P h h') = (term496 _27459 _27460 P h h').
Proof. exact (@lem1174129 (term461 _27459 _27460 P h h')). Qed.
Lemma lem1174134 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (h' : _27459) (h1 : term472 _27459 _27460 P h h') : term496 _27459 _27460 P h h'.
Proof. exact (EQ_MP (@lem1174131 _27459 _27460 P h h') (@lem1170668 _27459 _27460 P h h' h1)). Qed.
Lemma lem1174137 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1174134 _27459 _27460 P h h' h1 (@lem1174126 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1174138 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1174137 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1174140 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1174141 : term497 = False.
Proof. exact (@lem1174140 False). Qed.
Lemma lem1174142 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1174141) (@lem1174138 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1174423 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1174424 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1174423 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1174426 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1174427 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1174426 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1174428 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1174427 _27459 _27460 _19608 P t' h t) (@lem1174424 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1174431 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1174433 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1174431 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1174436 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1174433 _27459 _27460 _19608 P t' h t) (@lem1170710 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1174439 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1174436 _27459 _27460 _19608 P t' h t h1 (@lem1174428 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1174440 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1174439 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1174442 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1174443 : term497 = False.
Proof. exact (@lem1174442 False). Qed.
Lemma lem1174444 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1174443) (@lem1174440 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1174708 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1174709 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1174708 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1174711 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1174712 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1174711 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1174713 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1174712 _27459 _27460 _19608 P t' h t) (@lem1174709 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1174716 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1174718 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1174716 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1174721 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1174718 _27459 _27460 _19608 P t' h t) (@lem1170748 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1174724 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1174721 _27459 _27460 _19608 P t' h t h1 (@lem1174713 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1174725 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1174724 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1174727 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1174728 : term497 = False.
Proof. exact (@lem1174727 False). Qed.
Lemma lem1174729 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1174728) (@lem1174725 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1175010 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (proj1 (@lem1167488 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1175011 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term498 _27459 _27460 P h t'.
Proof. exact (fun h0 : term440 _27459 _27460 P h t' => @lem1175010 _27459 _27460 _19608 P t' h t h1). Qed.
Lemma lem1175013 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175014 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term498 _27459 _27460 P h t') = (term438 _27459 _27460 P h t').
Proof. exact (@lem1175013 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1175015 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term438 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1175014 _27459 _27460 P h t') (@lem1175011 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1175018 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1175020 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) : (term440 _27459 _27460 P h t') = (term499 _27459 _27460 P h t').
Proof. exact (@lem1175018 (term438 _27459 _27460 P h t')). Qed.
Lemma lem1175023 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term440 _27459 _27460 P h t') : term499 _27459 _27460 P h t'.
Proof. exact (EQ_MP (@lem1175020 _27459 _27460 P h t') (@lem1170784 _27459 _27460 P h t' h1)). Qed.
Lemma lem1175026 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (@lem1175023 _27459 _27460 P h t' h1 (@lem1175015 _27459 _27460 _19608 P t' h t h2)). Qed.
Lemma lem1175027 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1175026 _27459 _27460 _19608 P t' h t h1 h2). Qed.
Lemma lem1175029 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175030 : term497 = False.
Proof. exact (@lem1175029 False). Qed.
Lemma lem1175031 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1175030) (@lem1175027 _27459 _27460 _19608 P t' h t h1 h2)). Qed.
Lemma lem1175312 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1175313 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1175312 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1175315 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175316 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1175315 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1175317 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1175316 _27459 _27460 _19608 P t' h t) (@lem1175313 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1175320 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1175322 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1175320 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1175325 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1175322 _27459 _27460 _19608 P t' h t) (@lem1170826 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1175328 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1175325 _27459 _27460 _19608 P t' h t h1 (@lem1175317 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1175329 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1175328 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1175331 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175332 : term497 = False.
Proof. exact (@lem1175331 False). Qed.
Lemma lem1175333 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1175332) (@lem1175329 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1175614 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1175615 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1175614 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1175617 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175618 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1175617 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1175619 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1175618 _27459 _27460 _19608 P t' h t) (@lem1175615 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1175622 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1175624 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1175622 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1175627 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1175624 _27459 _27460 _19608 P t' h t) (@lem1170864 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1175630 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1175627 _27459 _27460 _19608 P t' h t h1 (@lem1175619 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1175631 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1175630 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1175633 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175634 : term497 = False.
Proof. exact (@lem1175633 False). Qed.
Lemma lem1175635 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1175634) (@lem1175631 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1175916 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term460 _27459 _27460 _19609 P h' t.
Proof. exact (proj2 (@lem1167468 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1175917 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term500 _27459 _27460 _19609 P h' t.
Proof. exact (fun h0 : term467 _27459 _27460 _19609 P h' t => @lem1175916 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1175919 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175920 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term500 _27459 _27460 _19609 P h' t) = (term460 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1175919 (term460 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1175921 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term460 _27459 _27460 _19609 P h' t.
Proof. exact (EQ_MP (@lem1175920 _27459 _27460 _19609 P h' t) (@lem1175917 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1175924 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1175926 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) : (term467 _27459 _27460 _19609 P h' t) = (term501 _27459 _27460 _19609 P h' t).
Proof. exact (@lem1175924 (term460 _27459 _27460 _19609 P h' t)). Qed.
Lemma lem1175929 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) : term501 _27459 _27460 _19609 P h' t.
Proof. exact (EQ_MP (@lem1175926 _27459 _27460 _19609 P h' t) (@lem1170900 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1175932 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1175929 _27459 _27460 _19609 P h' t h1 (@lem1175921 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1175933 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1175932 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1175935 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1175936 : term497 = False.
Proof. exact (@lem1175935 False). Qed.
Lemma lem1175937 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1175936) (@lem1175933 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1176218 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1176219 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1176218 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1176221 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1176222 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1176221 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1176223 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1176222 _27459 _27460 _19608 P t' h t) (@lem1176219 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1176226 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1176228 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1176226 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1176231 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1176228 _27459 _27460 _19608 P t' h t) (@lem1170942 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1176234 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1176231 _27459 _27460 _19608 P t' h t h1 (@lem1176223 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1176235 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1176234 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1176237 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1176238 : term497 = False.
Proof. exact (@lem1176237 False). Qed.
Lemma lem1176239 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1176238) (@lem1176235 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1176503 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1176504 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1176503 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1176506 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1176507 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1176506 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1176508 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1176507 _27459 _27460 _19608 P t' h t) (@lem1176504 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1176511 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1176513 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1176511 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1176516 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1176513 _27459 _27460 _19608 P t' h t) (@lem1170980 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1176519 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1176516 _27459 _27460 _19608 P t' h t h1 (@lem1176508 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1176520 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1176519 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1176522 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1176523 : term497 = False.
Proof. exact (@lem1176522 False). Qed.
Lemma lem1176524 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1176523) (@lem1176520 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1176805 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term411 _27459 _27460 P t t'.
Proof. exact (proj2 (@lem1167510 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1176806 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term511 _27459 _27460 P t t'.
Proof. exact (fun h0 : term413 _27459 _27460 P t t' => @lem1176805 _27459 _27460 _19608 P t' h t h1). Qed.
Lemma lem1176808 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1176809 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (t' : list _27459) : (term511 _27459 _27460 P t t') = (term411 _27459 _27460 P t t').
Proof. exact (@lem1176808 (term411 _27459 _27460 P t t')). Qed.
Lemma lem1176810 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term452 _27459 _27460 _19608 P t' h t) : term411 _27459 _27460 P t t'.
Proof. exact (EQ_MP (@lem1176809 _27459 _27460 P t t') (@lem1176806 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1176816 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1176817 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : (term416 _27459 _27460 _19608 P _19793 t) = (term513 _27459 _27460 _19608 P t _19793).
Proof. exact (@lem1176816 (term408 _27459 _27460 _19608 P _19793 t) (term413 _27459 _27460 P t _19793)). Qed.
Lemma lem1176823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1176824 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : (term514 _27459 _27460 _19608 P _19793 t) = (term515 _27459 _27460 _19608 P t _19793).
Proof. exact (MK_COMB (@lem1176823) (@lem1176817 _27459 _27460 _19608 P t _19793)). Qed.
Lemma lem1176830 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : (term513 _27459 _27460 _19608 P t _19793) = (term513 _27459 _27460 _19608 P t _19793).
Proof. exact (eq_refl (term513 _27459 _27460 _19608 P t _19793)). Qed.
Lemma lem1176831 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : ((term416 _27459 _27460 _19608 P _19793 t) = (term513 _27459 _27460 _19608 P t _19793)) = ((term513 _27459 _27460 _19608 P t _19793) = (term513 _27459 _27460 _19608 P t _19793)).
Proof. exact (MK_COMB (@lem1176824 _27459 _27460 _19608 P t _19793) (@lem1176830 _27459 _27460 _19608 P t _19793)). Qed.
Lemma lem1176833 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1176834 (x : Prop) : (x = x) = True.
Proof. exact (@lem1176833 Prop x). Qed.
Lemma lem1176835 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : ((term513 _27459 _27460 _19608 P t _19793) = (term513 _27459 _27460 _19608 P t _19793)) = True.
Proof. exact (@lem1176834 (term513 _27459 _27460 _19608 P t _19793)). Qed.
Lemma lem1176836 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : ((term416 _27459 _27460 _19608 P _19793 t) = (term513 _27459 _27460 _19608 P t _19793)) = True.
Proof. exact (TRANS (@lem1176831 _27459 _27460 _19608 P t _19793) (@lem1176835 _27459 _27460 _19608 P t _19793)). Qed.
Lemma lem1176837 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : True = ((term416 _27459 _27460 _19608 P _19793 t) = (term513 _27459 _27460 _19608 P t _19793)).
Proof. exact (SYM (@lem1176836 _27459 _27460 _19608 P t _19793)). Qed.
Lemma lem1176838 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : (term416 _27459 _27460 _19608 P _19793 t) = (term513 _27459 _27460 _19608 P t _19793).
Proof. exact (EQ_MP (@lem1176837 _27459 _27460 _19608 P t _19793) (@lem0)). Qed.
Lemma lem1176839 {_27459 _27460 : Type'} (_19793 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term513 _27459 _27460 _19608 P t _19793.
Proof. exact (EQ_MP (@lem1176838 _27459 _27460 _19608 P t _19793) (@lem1170996 _27459 _27460 _19793 _19608 P t h1)). Qed.
Lemma lem1176841 (b : Prop) (a : Prop) : (a \/ b) = (term505 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1176842 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19793 : list _27459) (t : list _27460) : (term513 _27459 _27460 _19608 P t _19793) = (term516 _27459 _27460 _19608 P _19793 t).
Proof. exact (@lem1176841 (term413 _27459 _27460 P t _19793) (term408 _27459 _27460 _19608 P _19793 t)). Qed.
Lemma lem1176844 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1176845 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : (term517 _27459 _27460 P t _19793) = (term411 _27459 _27460 P t _19793).
Proof. exact (@lem1176844 (term411 _27459 _27460 P t _19793)). Qed.
Lemma lem1176846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1176847 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t : list _27460) (_19793 : list _27459) : (term518 _27459 _27460 P t _19793) = (term519 _27459 _27460 P t _19793).
Proof. exact (MK_COMB (@lem1176846) (@lem1176845 _27459 _27460 P t _19793)). Qed.
Lemma lem1176848 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19793 : list _27459) (t : list _27460) : (term408 _27459 _27460 _19608 P _19793 t) = (term408 _27459 _27460 _19608 P _19793 t).
Proof. exact (eq_refl (term408 _27459 _27460 _19608 P _19793 t)). Qed.
Lemma lem1176849 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19793 : list _27459) (t : list _27460) : (term516 _27459 _27460 _19608 P _19793 t) = (term520 _27459 _27460 _19608 P _19793 t).
Proof. exact (MK_COMB (@lem1176847 _27459 _27460 P t _19793) (@lem1176848 _27459 _27460 _19608 P _19793 t)). Qed.
Lemma lem1176850 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (_19793 : list _27459) (t : list _27460) : (term513 _27459 _27460 _19608 P t _19793) = (term520 _27459 _27460 _19608 P _19793 t).
Proof. exact (TRANS (@lem1176842 _27459 _27460 _19608 P _19793 t) (@lem1176849 _27459 _27460 _19608 P _19793 t)). Qed.
Lemma lem1176853 {_27459 _27460 : Type'} (_19793 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term520 _27459 _27460 _19608 P _19793 t.
Proof. exact (EQ_MP (@lem1176850 _27459 _27460 _19608 P _19793 t) (@lem1176839 _27459 _27460 _19793 _19608 P t h1)). Qed.
Lemma lem1176854 {_27459 _27460 : Type'} (_19793 : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term520 _27459 _27460 _19608 P _19793 t.
Proof. exact (@lem1176853 _27459 _27460 _19793 _19608 P t h1). Qed.
Lemma lem1176855 {_27459 _27460 : Type'} (t' : list _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term520 _27459 _27460 _19608 P t' t.
Proof. exact (@lem1176854 _27459 _27460 t' _19608 P t h1). Qed.
Lemma lem1176858 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term452 _27459 _27460 _19608 P t' h t) : term408 _27459 _27460 _19608 P t' t.
Proof. exact (@lem1176855 _27459 _27460 t' _19608 P t h1 (@lem1176810 _27459 _27460 _19608 P t' h t h2)). Qed.
Lemma lem1176859 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term452 _27459 _27460 _19608 P t' h t) : term504 _27459 _27460 _19608 P t' t.
Proof. exact (fun h0 : term420 _27459 _27460 _19608 P t' t => @lem1176858 _27459 _27460 _19608 P t' h t h1 h2). Qed.
Lemma lem1176861 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1176862 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term504 _27459 _27460 _19608 P t' t) = (term408 _27459 _27460 _19608 P t' t).
Proof. exact (@lem1176861 (term408 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1176863 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term452 _27459 _27460 _19608 P t' h t) : term408 _27459 _27460 _19608 P t' t.
Proof. exact (EQ_MP (@lem1176862 _27459 _27460 _19608 P t' t) (@lem1176859 _27459 _27460 _19608 P t' h t h1 h2)). Qed.
Lemma lem1176866 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1176868 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) : (term420 _27459 _27460 _19608 P t' t) = (term521 _27459 _27460 _19608 P t' t).
Proof. exact (@lem1176866 (term408 _27459 _27460 _19608 P t' t)). Qed.
Lemma lem1176871 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (h1 : term420 _27459 _27460 _19608 P t' t) : term521 _27459 _27460 _19608 P t' t.
Proof. exact (EQ_MP (@lem1176868 _27459 _27460 _19608 P t' t) (@lem1171016 _27459 _27460 _19608 P t' t h1)). Qed.
Lemma lem1176874 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (@lem1176871 _27459 _27460 _19608 P t' t h2 (@lem1176863 _27459 _27460 _19608 P t' h t h1 h3)). Qed.
Lemma lem1176875 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1176874 _27459 _27460 _19608 P t' h t h1 h2 h3). Qed.
Lemma lem1176877 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1176878 : term497 = False.
Proof. exact (@lem1176877 False). Qed.
Lemma lem1176879 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1176878) (@lem1176875 _27459 _27460 _19608 P t' h t h1 h2 h3)). Qed.
Lemma lem1177160 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1177161 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1177160 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1177163 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1177164 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1177163 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1177165 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1177164 _27459 _27460 _19608 P t' h t) (@lem1177161 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1177168 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1177170 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1177168 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1177173 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1177170 _27459 _27460 _19608 P t' h t) (@lem1171058 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177176 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1177173 _27459 _27460 _19608 P t' h t h1 (@lem1177165 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1177177 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1177176 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1177179 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1177180 : term497 = False.
Proof. exact (@lem1177179 False). Qed.
Lemma lem1177181 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177180) (@lem1177177 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177445 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (proj2 (@lem1167465 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1177446 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term502 _27459 _27460 _19608 P t' h t.
Proof. exact (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1177445 _27459 _27460 _19609 h' _19608 P t' h t h1). Qed.
Lemma lem1177448 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1177449 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term502 _27459 _27460 _19608 P t' h t) = (term431 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1177448 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1177450 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term431 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1177449 _27459 _27460 _19608 P t' h t) (@lem1177446 _27459 _27460 _19609 h' _19608 P t' h t h1)). Qed.
Lemma lem1177453 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1177455 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term432 _27459 _27460 _19608 P t' h t) = (term503 _27459 _27460 _19608 P t' h t).
Proof. exact (@lem1177453 (term431 _27459 _27460 _19608 P t' h t)). Qed.
Lemma lem1177458 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) : term503 _27459 _27460 _19608 P t' h t.
Proof. exact (EQ_MP (@lem1177455 _27459 _27460 _19608 P t' h t) (@lem1171096 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177461 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (@lem1177458 _27459 _27460 _19608 P t' h t h1 (@lem1177450 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1177462 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : term497.
Proof. exact (fun h0 : ~ False => @lem1177461 _27459 _27460 _19609 h' _19608 P t' h t h1 h2). Qed.
Lemma lem1177464 (p : Prop) : (term495 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1177465 : term497 = False.
Proof. exact (@lem1177464 False). Qed.
Lemma lem1177466 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177465) (@lem1177462 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177467 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : (term420 _27459 _27460 _19608 P t' t) = False.
Proof. exact (prop_ext (fun h4 : term420 _27459 _27460 _19608 P t' t => @lem1176879 _27459 _27460 _19608 P t' h t h1 h2 h3) (fun h4 : False => @lem1171016 _27459 _27460 _19608 P t' t h2)). Qed.
Lemma lem1177468 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177467 _27459 _27460 _19608 P t' h t h1 h2 h3) (@lem1171016 _27459 _27460 _19608 P t' t h2)). Qed.
Lemma lem1177469 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1175937 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170900 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177470 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177469 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170900 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177471 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1175031 _27459 _27460 _19608 P t' h t h1 h2) (fun h3 : False => @lem1170784 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177472 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177471 _27459 _27460 _19608 P t' h t h1 h2) (@lem1170784 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177473 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1174142 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170668 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177474 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177473 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170668 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177475 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term413 _27459 _27460 P t t') = False.
Proof. exact (prop_ext (fun h4 : term413 _27459 _27460 P t t' => @lem1173840 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (fun h4 : False => @lem1170634 _27459 _27460 P t t' h2)). Qed.
Lemma lem1177476 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177475 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (@lem1170634 _27459 _27460 P t t' h2)). Qed.
Lemma lem1177477 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1173514 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170594 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177478 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177477 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170594 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177479 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : (term432 _27459 _27460 _19608 P t' h t) = False.
Proof. exact (prop_ext (fun h3 : term432 _27459 _27460 _19608 P t' h t => @lem1173212 _27459 _27460 _19608 P t' h t h1 h2) (fun h3 : False => @lem1170548 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177480 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177479 _27459 _27460 _19608 P t' h t h1 h2) (@lem1170548 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177481 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1172910 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170508 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177482 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177481 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170508 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177483 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1172608 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170472 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177484 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177483 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170472 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177485 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1172306 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170426 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177486 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177485 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170426 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177487 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1172004 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170386 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177488 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177487 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170386 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177489 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1171702 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170350 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177490 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177489 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170350 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177491 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1171400 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1170304 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177492 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177491 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1170304 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177493 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : (term420 _27459 _27460 _19608 P t' t) = False.
Proof. exact (prop_ext (fun h4 : term420 _27459 _27460 _19608 P t' t => @lem1177468 _27459 _27460 _19608 P t' h t h1 h2 h3) (fun h4 : False => @lem1169430 _27459 _27460 _19608 P t' t h2)). Qed.
Lemma lem1177494 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177493 _27459 _27460 _19608 P t' h t h1 h2 h3) (@lem1169430 _27459 _27460 _19608 P t' t h2)). Qed.
Lemma lem1177495 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1177470 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1169132 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177496 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177495 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1169132 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177497 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177472 _27459 _27460 _19608 P t' h t h1 h2) (fun h3 : False => @lem1168834 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177498 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177497 _27459 _27460 _19608 P t' h t h1 h2) (@lem1168834 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177499 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1177474 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168536 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177500 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177499 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168536 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177501 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term413 _27459 _27460 P t t') = False.
Proof. exact (prop_ext (fun h4 : term413 _27459 _27460 P t t' => @lem1177476 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (fun h4 : False => @lem1168446 _27459 _27460 P t t' h2)). Qed.
Lemma lem1177502 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177501 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (@lem1168446 _27459 _27460 P t t' h2)). Qed.
Lemma lem1177503 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177478 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168344 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177504 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177503 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168344 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177505 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : (term432 _27459 _27460 _19608 P t' h t) = False.
Proof. exact (prop_ext (fun h3 : term432 _27459 _27460 _19608 P t' h t => @lem1177480 _27459 _27460 _19608 P t' h t h1 h2) (fun h3 : False => @lem1168230 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177506 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177505 _27459 _27460 _19608 P t' h t h1 h2) (@lem1168230 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177507 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1177482 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168128 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177508 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177507 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168128 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177509 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177484 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168034 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177510 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177509 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168034 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177511 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1177486 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167920 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177512 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177511 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167920 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177513 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1177488 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167818 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177514 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177513 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167818 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177515 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177490 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167724 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177516 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177515 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167724 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177517 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1177492 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167610 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177518 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177517 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167610 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177519 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : (term420 _27459 _27460 _19608 P t' t) = False.
Proof. exact (prop_ext (fun h4 : term420 _27459 _27460 _19608 P t' t => @lem1177494 _27459 _27460 _19608 P t' h t h1 h2 h3) (fun h4 : False => @lem1169430 _27459 _27460 _19608 P t' t h2)). Qed.
Lemma lem1177520 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177519 _27459 _27460 _19608 P t' h t h1 h2 h3) (@lem1169430 _27459 _27460 _19608 P t' t h2)). Qed.
Lemma lem1177521 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1177496 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1169132 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177522 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177521 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1169132 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177523 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177498 _27459 _27460 _19608 P t' h t h1 h2) (fun h3 : False => @lem1168834 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177524 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177523 _27459 _27460 _19608 P t' h t h1 h2) (@lem1168834 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177525 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1177500 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168536 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177526 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177525 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168536 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177527 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term413 _27459 _27460 P t t') = False.
Proof. exact (prop_ext (fun h4 : term413 _27459 _27460 P t t' => @lem1177502 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (fun h4 : False => @lem1168446 _27459 _27460 P t t' h2)). Qed.
Lemma lem1177528 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term413 _27459 _27460 P t t') (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177527 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (@lem1168446 _27459 _27460 P t t' h2)). Qed.
Lemma lem1177529 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177504 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168344 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177530 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177529 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168344 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177531 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : (term432 _27459 _27460 _19608 P t' h t) = False.
Proof. exact (prop_ext (fun h3 : term432 _27459 _27460 _19608 P t' h t => @lem1177506 _27459 _27460 _19608 P t' h t h1 h2) (fun h3 : False => @lem1168230 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177532 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term432 _27459 _27460 _19608 P t' h t) (h2 : term452 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177531 _27459 _27460 _19608 P t' h t h1 h2) (@lem1168230 _27459 _27460 _19608 P t' h t h1)). Qed.
Lemma lem1177533 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1177508 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168128 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177534 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177533 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168128 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177535 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177510 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1168034 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177536 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177535 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1168034 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177537 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term467 _27459 _27460 _19609 P h' t) = False.
Proof. exact (prop_ext (fun h3 : term467 _27459 _27460 _19609 P h' t => @lem1177512 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167920 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177538 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177537 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167920 _27459 _27460 _19609 P h' t h1)). Qed.
Lemma lem1177539 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1177514 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167818 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177540 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177539 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167818 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177541 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term440 _27459 _27460 P h t') = False.
Proof. exact (prop_ext (fun h3 : term440 _27459 _27460 P h t' => @lem1177516 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167724 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177542 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177541 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167724 _27459 _27460 P h t' h1)). Qed.
Lemma lem1177543 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : (term472 _27459 _27460 P h h') = False.
Proof. exact (prop_ext (fun h3 : term472 _27459 _27460 P h h' => @lem1177518 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h3 : False => @lem1167610 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177544 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (EQ_MP (@lem1177543 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (@lem1167610 _27459 _27460 P h h' h1)). Qed.
Lemma lem1177545 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (or_elim (@lem1167514 _27459 _27460 _19608 P t' h t h1) (fun h0 : term440 _27459 _27460 P h t' => @lem1177181 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term413 _27459 _27460 P t t' => @lem1177466 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177546 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term420 _27459 _27460 _19608 P t' t) (h3 : term479 _27459 _27460 _19609 h' _19608 P t' h t) (h4 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1166950 _27459 _27460 _19608 P t' h t h4) (fun h0 : term452 _27459 _27460 _19608 P t' h t => @lem1177520 _27459 _27460 _19608 P t' h t h1 h2 h0) (fun h0 : term445 _27459 _27460 _19608 P t' h t => @lem1177545 _27459 _27460 _19609 h' _19608 P t' h t h0 h3)). Qed.
Lemma lem1177547 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (or_elim (@lem1167504 _27459 _27460 _19608 P t' h t h1) (fun h0 : term440 _27459 _27460 P h t' => @lem1176239 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term413 _27459 _27460 P t t' => @lem1176524 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177548 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1166950 _27459 _27460 _19608 P t' h t h3) (fun h0 : term452 _27459 _27460 _19608 P t' h t => @lem1177522 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term445 _27459 _27460 _19608 P t' h t => @lem1177547 _27459 _27460 _19609 h' _19608 P t' h t h0 h2)). Qed.
Lemma lem1177549 {_27459 _27460 : Type'} (h : _27460) (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) (h4 : term470 _27459 _27460 _19609 h' _19608 P t' t) : False.
Proof. exact (or_elim (@lem1167472 _27459 _27460 _19609 h' _19608 P t' t h4) (fun h0 : term467 _27459 _27460 _19609 P h' t => @lem1177548 _27459 _27460 _19609 h' _19608 P t' h t h0 h2 h3) (fun h0 : term420 _27459 _27460 _19608 P t' t => @lem1177546 _27459 _27460 _19609 h' _19608 P t' h t h1 h0 h2 h3)). Qed.
Lemma lem1177550 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (or_elim (@lem1167492 _27459 _27460 _19608 P t' h t h1) (fun h0 : term440 _27459 _27460 P h t' => @lem1175333 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term413 _27459 _27460 P t t' => @lem1175635 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177551 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term440 _27459 _27460 P h t') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1166950 _27459 _27460 _19608 P t' h t h3) (fun h0 : term452 _27459 _27460 _19608 P t' h t => @lem1177524 _27459 _27460 _19608 P t' h t h1 h0) (fun h0 : term445 _27459 _27460 _19608 P t' h t => @lem1177550 _27459 _27460 _19609 h' _19608 P t' h t h0 h2)). Qed.
Lemma lem1177552 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term445 _27459 _27460 _19608 P t' h t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) : False.
Proof. exact (or_elim (@lem1167482 _27459 _27460 _19608 P t' h t h1) (fun h0 : term440 _27459 _27460 P h t' => @lem1174444 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term413 _27459 _27460 P t t' => @lem1174729 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177553 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1166950 _27459 _27460 _19608 P t' h t h3) (fun h0 : term452 _27459 _27460 _19608 P t' h t => @lem1177526 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term445 _27459 _27460 _19608 P t' h t => @lem1177552 _27459 _27460 _19609 h' _19608 P t' h t h0 h2)). Qed.
Lemma lem1177554 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (t : list _27460) (h' : _27459) (P : type1470 _27459 _27460) (h : _27460) (t' : list _27459) (h1 : term479 _27459 _27460 _19609 h' _19608 P t' h t) (h2 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) (h3 : term475 _27459 _27460 h' P h t') : False.
Proof. exact (or_elim (@lem1167471 _27459 _27460 h' P h t' h3) (fun h0 : term472 _27459 _27460 P h h' => @lem1177553 _27459 _27460 _19609 h' _19608 P t' h t h0 h1 h2) (fun h0 : term440 _27459 _27460 P h t' => @lem1177551 _27459 _27460 _19609 h' _19608 P t' h t h0 h1 h2)). Qed.
Lemma lem1177555 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term479 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1167466 _27459 _27460 _19609 h' _19608 P t' h t h2) (fun h0 : term475 _27459 _27460 h' P h t' => @lem1177554 _27459 _27460 _19609 _19608 t h' P h t' h2 h3 h0) (fun h0 : term470 _27459 _27460 _19609 h' _19608 P t' t => @lem1177549 _27459 _27460 h _19609 h' _19608 P t' t h1 h2 h3 h0)). Qed.
Lemma lem1177556 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : term445 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (or_elim (@lem1167462 _27459 _27460 _19608 P t' h t h3) (fun h0 : term440 _27459 _27460 P h t' => @lem1177530 _27459 _27460 _19609 h' _19608 P t' h t h0 h2) (fun h0 : term413 _27459 _27460 P t t' => @lem1177528 _27459 _27460 _19609 h' _19608 P t' h t h1 h0 h2)). Qed.
Lemma lem1177557 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term432 _27459 _27460 _19608 P t' h t) (h3 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h4 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1166950 _27459 _27460 _19608 P t' h t h4) (fun h0 : term452 _27459 _27460 _19608 P t' h t => @lem1177532 _27459 _27460 _19608 P t' h t h2 h0) (fun h0 : term445 _27459 _27460 _19608 P t' h t => @lem1177556 _27459 _27460 _19609 h' _19608 P t' h t h1 h3 h0)). Qed.
Lemma lem1177558 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : term445 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (or_elim (@lem1167452 _27459 _27460 _19608 P t' h t h3) (fun h0 : term440 _27459 _27460 P h t' => @lem1177536 _27459 _27460 _19609 h' _19608 P t' h t h0 h2) (fun h0 : term413 _27459 _27460 P t t' => @lem1177534 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177559 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term467 _27459 _27460 _19609 P h' t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1166950 _27459 _27460 _19608 P t' h t h3) (fun h0 : term452 _27459 _27460 _19608 P t' h t => @lem1177538 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term445 _27459 _27460 _19608 P t' h t => @lem1177558 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h0)). Qed.
Lemma lem1177560 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : term445 _27459 _27460 _19608 P t' h t) : False.
Proof. exact (or_elim (@lem1167442 _27459 _27460 _19608 P t' h t h3) (fun h0 : term440 _27459 _27460 P h t' => @lem1177542 _27459 _27460 _19609 h' _19608 P t' h t h0 h2) (fun h0 : term413 _27459 _27460 P t t' => @lem1177540 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177561 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term472 _27459 _27460 P h h') (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1166950 _27459 _27460 _19608 P t' h t h3) (fun h0 : term452 _27459 _27460 _19608 P t' h t => @lem1177544 _27459 _27460 _19609 h' _19608 P t' h t h1 h2) (fun h0 : term445 _27459 _27460 _19608 P t' h t => @lem1177560 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h0)). Qed.
Lemma lem1177562 {_27459 _27460 : Type'} (_19608 : type738 _27459 _27460) (t' : list _27459) (h : _27460) (_19609 : type738 _27459 _27460) (P : type1470 _27459 _27460) (h' : _27459) (t : list _27460) (h1 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h2 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) (h3 : term480 _27459 _27460 h _19609 P h' t) : False.
Proof. exact (or_elim (@lem1167431 _27459 _27460 h _19609 P h' t h3) (fun h0 : term472 _27459 _27460 P h h' => @lem1177561 _27459 _27460 _19609 h' _19608 P t' h t h0 h1 h2) (fun h0 : term467 _27459 _27460 _19609 P h' t => @lem1177559 _27459 _27460 _19609 h' _19608 P t' h t h0 h1 h2)). Qed.
Lemma lem1177563 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term489 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1167423 _27459 _27460 _19609 h' _19608 P t' h t h2) (fun h0 : term480 _27459 _27460 h _19609 P h' t => @lem1177562 _27459 _27460 _19608 t' h _19609 P h' t h2 h3 h0) (fun h0 : term432 _27459 _27460 _19608 P t' h t => @lem1177557 _27459 _27460 _19609 h' _19608 P t' h t h1 h0 h2 h3)). Qed.
Lemma lem1177564 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term332 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (or_elim (@lem1167416 _27459 _27460 _19609 h' _19608 P t' h t h2) (fun h0 : term489 _27459 _27460 _19609 h' _19608 P t' h t => @lem1177563 _27459 _27460 _19609 h' _19608 P t' h t h1 h0 h3) (fun h0 : term479 _27459 _27460 _19609 h' _19608 P t' h t => @lem1177555 _27459 _27460 _19609 h' _19608 P t' h t h1 h0 h3)). Qed.
Lemma lem1177565 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term332 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : (term332 _27459 _27460 _19609 h' _19608 P t' h t) = False.
Proof. exact (prop_ext (fun h4 : term332 _27459 _27460 _19609 h' _19608 P t' h t => @lem1177564 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (fun h4 : False => @lem1165728 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1177566 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : term332 _27459 _27460 _19609 h' _19608 P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : False.
Proof. exact (EQ_MP (@lem1177565 _27459 _27460 _19609 h' _19608 P t' h t h1 h2 h3) (@lem1165728 _27459 _27460 _19609 h' _19608 P t' h t h2)). Qed.
Lemma lem1177567 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : term331 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (fun h0 : term332 _27459 _27460 _19609 h' _19608 P t' h t => @lem1177566 _27459 _27460 _19609 h' _19608 P t' h t h1 h0 h2). Qed.
Lemma lem1177568 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) (h2 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t)) : (term273 _27459 _27460 h _19609 h' _19608 P t' t) = (term270 _27459 _27460 _19609 h' _19608 P t' h t).
Proof. exact (EQ_MP (@lem1165727 _27459 _27460 _19609 h' _19608 P t' h t) (@lem1177567 _27459 _27460 _19609 h' _19608 P t' h t h1 h2)). Qed.
Lemma lem1177569 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (t' : list _27459) (h : _27460) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term205 _27459 _27460 _19608 P t) : term275 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (fun h0 : (term37 _27459 _27460 h P t t') = (term194 _27459 _27460 _19608 P t' h t) => @lem1177568 _27459 _27460 _19609 h' _19608 P t' h t h1 h0). Qed.
Lemma lem1177570 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (h' : _27459) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term276 _27459 _27460 _19609 h' _19608 P t' h t.
Proof. exact (fun h0 : term205 _27459 _27460 _19608 P t => @lem1177569 _27459 _27460 _19609 h' t' h _19608 P t h0). Qed.
Lemma lem1177575 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term278 _27459 _27460 _19609 _19608 P t' h t.
Proof. exact (fun h' : _27459 => @lem1177570 _27459 _27460 _19609 h' _19608 P t' h t). Qed.
Lemma lem1177580 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term280 _27459 _27460 _19609 _19608 t' h t.
Proof. exact (fun P : type1470 _27459 _27460 => @lem1177575 _27459 _27460 _19609 _19608 P t' h t). Qed.
Lemma lem1177585 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (h : _27460) (t : list _27460) : term282 _27459 _27460 _19609 _19608 h t.
Proof. exact (fun t' : list _27459 => @lem1177580 _27459 _27460 _19609 _19608 t' h t). Qed.
Lemma lem1177590 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) (t : list _27460) : term284 _27459 _27460 _19609 _19608 t.
Proof. exact (fun h : _27460 => @lem1177585 _27459 _27460 _19609 _19608 h t). Qed.
Lemma lem1177595 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) : term286 _27459 _27460 _19609 _19608.
Proof. exact (fun t : list _27460 => @lem1177590 _27459 _27460 _19609 _19608 t). Qed.
Lemma lem1177596 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) (_19608 : type738 _27459 _27460) : term292 _27459 _27460 _19609 _19608.
Proof. exact (fun h0 : term290 _27459 _27460 _19608 _19609 => @lem1177595 _27459 _27460 _19609 _19608). Qed.
Lemma lem1177601 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : term294 _27459 _27460 _19609.
Proof. exact (fun _19608 : type738 _27459 _27460 => @lem1177596 _27459 _27460 _19609 _19608). Qed.
Lemma lem1177602 {_27459 _27460 : Type'} (_19609 : type738 _27459 _27460) : term328 _27459 _27460 _19609.
Proof. exact (fun h0 : term326 _27459 _27460 _19609 => @lem1177601 _27459 _27460 _19609). Qed.
Lemma lem1177607 {_27459 _27460 : Type'} : term330 _27459 _27460.
Proof. exact (fun _19609 : type738 _27459 _27460 => @lem1177602 _27459 _27460 _19609). Qed.
Lemma lem1177608 {_27459 _27460 : Type'} : term185 _27459 _27460.
Proof. exact (EQ_MP (@lem1165719 _27459 _27460) (@lem1177607 _27459 _27460)). Qed.
Lemma lem1177609 {_27459 _27460 : Type'} (t : list _27460) : term522 _27459 _27460 t.
Proof. exact (@lem1177608 _27459 _27460 t). Qed.
Lemma lem1177610 {_27459 _27460 : Type'} (t : list _27460) : (term522 _27459 _27460 t) = (term181 _27459 _27460 t).
Proof. exact (eq_refl (term522 _27459 _27460 t)). Qed.
Lemma lem1177611 {_27459 _27460 : Type'} (t : list _27460) : term181 _27459 _27460 t.
Proof. exact (EQ_MP (@lem1177610 _27459 _27460 t) (@lem1177609 _27459 _27460 t)). Qed.
Lemma lem1177612 {_27459 _27460 : Type'} (t : list _27460) (h : _27460) : term523 _27459 _27460 t h.
Proof. exact (@lem1177611 _27459 _27460 t h). Qed.
Lemma lem1177613 {_27459 _27460 : Type'} (h : _27460) (t : list _27460) : (term523 _27459 _27460 t h) = (term177 _27459 _27460 h t).
Proof. exact (eq_refl (term523 _27459 _27460 t h)). Qed.
Lemma lem1177614 {_27459 _27460 : Type'} (h : _27460) (t : list _27460) : term177 _27459 _27460 h t.
Proof. exact (EQ_MP (@lem1177613 _27459 _27460 h t) (@lem1177612 _27459 _27460 t h)). Qed.
Lemma lem1177615 {_27459 _27460 : Type'} (h : _27460) (t : list _27460) (t' : list _27459) : term524 _27459 _27460 h t t'.
Proof. exact (@lem1177614 _27459 _27460 h t t'). Qed.
Lemma lem1177616 {_27459 _27460 : Type'} (t' : list _27459) (h : _27460) (t : list _27460) : (term524 _27459 _27460 h t t') = (term173 _27459 _27460 t' h t).
Proof. exact (eq_refl (term524 _27459 _27460 h t t')). Qed.
Lemma lem1177617 {_27459 _27460 : Type'} (t' : list _27459) (h : _27460) (t : list _27460) : term173 _27459 _27460 t' h t.
Proof. exact (EQ_MP (@lem1177616 _27459 _27460 t' h t) (@lem1177615 _27459 _27460 h t t')). Qed.
Lemma lem1177618 {_27459 _27460 : Type'} (t' : list _27459) (h : _27460) (t : list _27460) (P : type1470 _27459 _27460) : term525 _27459 _27460 t' h t P.
Proof. exact (@lem1177617 _27459 _27460 t' h t P). Qed.
Lemma lem1177619 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term525 _27459 _27460 t' h t P) = (term169 _27459 _27460 P t' h t).
Proof. exact (eq_refl (term525 _27459 _27460 t' h t P)). Qed.
Lemma lem1177620 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term169 _27459 _27460 P t' h t.
Proof. exact (EQ_MP (@lem1177619 _27459 _27460 P t' h t) (@lem1177618 _27459 _27460 t' h t P)). Qed.
Lemma lem1177621 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h' : _27459) : term526 _27459 _27460 P t' h t h'.
Proof. exact (@lem1177620 _27459 _27460 P t' h t h'). Qed.
Lemma lem1177622 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : (term526 _27459 _27460 P t' h t h') = (term158 _27459 _27460 h' P t' h t).
Proof. exact (eq_refl (term526 _27459 _27460 P t' h t h')). Qed.
Lemma lem1177623 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term158 _27459 _27460 h' P t' h t.
Proof. exact (EQ_MP (@lem1177622 _27459 _27460 h' P t' h t) (@lem1177621 _27459 _27460 P t' h t h')). Qed.
Lemma lem1177625 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) : term158 _27459 _27460 h' P t' h t.
Proof. exact (@lem1164892 _27459 _27460 h' P t' h t (@lem1177623 _27459 _27460 h' P t' h t)). Qed.
Lemma lem1177626 {_27459 _27460 : Type'} (h' : _27459) (t' : list _27459) (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term164 _27459 _27460 h' P t' h t.
Proof. exact (@lem1177625 _27459 _27460 h' P t' h t (@lem1164546 _27459 _27460 P t h1)). Qed.
Lemma lem1177627 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) (h2 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : term156 _27459 _27460 h' P t' h t.
Proof. exact (@lem1177626 _27459 _27460 h' t' h P t h1 (@lem1164654 _27459 _27460 P t' h t h2)). Qed.
Lemma lem1177628 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) (h2 : term157 _27459 _27460 h' P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : False.
Proof. exact (@lem1177627 _27459 _27460 h' P t' h t h1 h3 (@lem1164876 _27459 _27460 h' P t' h t h2)). Qed.
Lemma lem1177629 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) (h2 : term157 _27459 _27460 h' P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : (term157 _27459 _27460 h' P t' h t) = False.
Proof. exact (prop_ext (fun h4 : term157 _27459 _27460 h' P t' h t => @lem1177628 _27459 _27460 h' P t' h t h1 h2 h3) (fun h4 : False => @lem1164876 _27459 _27460 h' P t' h t h2)). Qed.
Lemma lem1177630 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) (h2 : term157 _27459 _27460 h' P t' h t) (h3 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : False.
Proof. exact (EQ_MP (@lem1177629 _27459 _27460 h' P t' h t h1 h2 h3) (@lem1164876 _27459 _27460 h' P t' h t h2)). Qed.
Lemma lem1177631 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) (h2 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : term156 _27459 _27460 h' P t' h t.
Proof. exact (fun h0 : term157 _27459 _27460 h' P t' h t => @lem1177630 _27459 _27460 h' P t' h t h1 h0 h2). Qed.
Lemma lem1177632 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) (h2 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : (term136 _27459 _27460 h h' P t' t) = (term154 _27459 _27460 h' P t' h t).
Proof. exact (EQ_MP (@lem1164875 _27459 _27460 h' P t' h t) (@lem1177631 _27459 _27460 h' P t' h t h1 h2)). Qed.
Lemma lem1177633 {_27459 _27460 : Type'} (h' : _27459) (P : type1470 _27459 _27460) (t' : list _27459) (h : _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) (h2 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t)) : (term81 _27459 _27460 h P t h' t') = (term82 _27459 _27460 P h' t' h t).
Proof. exact (EQ_MP (@lem1164871 _27459 _27460 h' t' h P t h1) (@lem1177632 _27459 _27460 h' P t' h t h1 h2)). Qed.
Lemma lem1177634 {_27459 _27460 : Type'} (h' : _27459) (t' : list _27459) (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term84 _27459 _27460 P h' t' h t.
Proof. exact (fun h0 : (term37 _27459 _27460 h P t t') = (term40 _27459 _27460 P t' h t) => @lem1177633 _27459 _27460 h' P t' h t h1 h0). Qed.
Lemma lem1177639 {_27459 _27460 : Type'} (h' : _27459) (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term88 _27459 _27460 P h' h t.
Proof. exact (fun t' : list _27459 => @lem1177634 _27459 _27460 h' t' h P t h1). Qed.
Lemma lem1177644 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term92 _27459 _27460 P h t.
Proof. exact (fun h' : _27459 => @lem1177639 _27459 _27460 h' h P t h1). Qed.
Lemma lem1177645 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term94 _27459 _27460 P h t.
Proof. exact (conj (@lem1164737 _27459 _27460 h P t h1) (@lem1177644 _27459 _27460 h P t h1)). Qed.
Lemma lem1177646 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term43 _27459 _27460 P h t.
Proof. exact (@lem1164653 _27459 _27460 P h t (@lem1177645 _27459 _27460 h P t h1)). Qed.
Lemma lem1177647 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) (t : list _27459) : term55 _27459 _27460 P h t.
Proof. exact (fun h0 : term32 _27459 _27460 P t => @lem1164693 _27459 _27460 h P t h0). Qed.
Lemma lem1177652 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27459) : term59 _27459 _27460 P h.
Proof. exact (fun t : list _27459 => @lem1177647 _27459 _27460 P h t). Qed.
Lemma lem1177657 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term63 _27459 _27460 P.
Proof. exact (fun h : _27459 => @lem1177652 _27459 _27460 P h). Qed.
Lemma lem1177658 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term65 _27459 _27460 P.
Proof. exact (conj (@lem1164664 _27459 _27460 P) (@lem1177657 _27459 _27460 P)). Qed.
Lemma lem1177659 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term35 _27459 _27460 P.
Proof. exact (@lem1164625 _27459 _27460 P (@lem1177658 _27459 _27460 P)). Qed.
Lemma lem1177660 {_27459 _27460 : Type'} (h : _27460) (P : type1470 _27459 _27460) (t : list _27460) (h1 : term8 _27459 _27460 P t) : term12 _27459 _27460 P h t.
Proof. exact (EQ_MP (@lem1164598 _27459 _27460 P h t) (@lem1177646 _27459 _27460 h P t h1)). Qed.
Lemma lem1177661 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term4 _27459 _27460 P.
Proof. exact (EQ_MP (@lem1164572 _27459 _27460 P) (@lem1177659 _27459 _27460 P)). Qed.
Lemma lem1177662 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) (t : list _27460) : term14 _27459 _27460 P h t.
Proof. exact (fun h0 : term8 _27459 _27460 P t => @lem1177660 _27459 _27460 h P t h0). Qed.
Lemma lem1177667 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) (h : _27460) : term18 _27459 _27460 P h.
Proof. exact (fun t : list _27460 => @lem1177662 _27459 _27460 P h t). Qed.
Lemma lem1177672 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term22 _27459 _27460 P.
Proof. exact (fun h : _27460 => @lem1177667 _27459 _27460 P h). Qed.
Lemma lem1177673 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term24 _27459 _27460 P.
Proof. exact (conj (@lem1177661 _27459 _27460 P) (@lem1177672 _27459 _27460 P)). Qed.
Lemma lem1177674 {_27459 _27460 : Type'} (P : type1470 _27459 _27460) : term29 _27459 _27460 P.
Proof. exact (@lem1164545 _27459 _27460 P (@lem1177673 _27459 _27460 P)). Qed.
Lemma lem1177679 {_27459 _27460 : Type'} : term527 _27459 _27460.
Proof. exact (fun P : type1470 _27459 _27460 => @lem1177674 _27459 _27460 P). Qed.
