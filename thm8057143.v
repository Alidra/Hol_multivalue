Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8057143_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm8049069_spec.
Require Import thm8049070_spec.
Require Import thm8049087_spec.
Require Import thm8050658_spec.
Require Import thm8050938_spec.
Lemma lem8055482 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8055483 {_143061 _143062 : Type'} (s : type56 _143061 _143062) (t : type56 _143061 _143062) : (s = t) = (term1 _143061 _143062 s t).
Proof. exact (@lem8055482 (type24 _143061 _143062) s t). Qed.
Lemma lem8055484 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (f = (@EMPTY ((cart _143061 _143062) -> Prop))) = (term2 _143061 _143062 f).
Proof. exact (@lem8055483 _143061 _143062 f (@EMPTY ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055493 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055494 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term3 _143061 _143062 f) = (term4 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055493) (@lem8055484 _143061 _143062 f)). Qed.
Lemma lem8055511 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term5 _143061 _143062 _143063 t) = (term5 _143061 _143062 _143063 t).
Proof. exact (eq_refl (term5 _143061 _143062 _143063 t)). Qed.
Lemma lem8055512 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term6 _143061 _143062 _143063 f t) = (term7 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8055494 _143061 _143062 f) (@lem8055511 _143061 _143062 _143063 t)). Qed.
Lemma lem8055515 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term7 _143061 _143062 _143063 f t) = (term6 _143061 _143062 _143063 f t).
Proof. exact (SYM (@lem8055512 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055525 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055526 {_143061 _143062 : Type'} (P : type56 _143061 _143062) (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x P) = (P x).
Proof. exact (@lem8055525 (type24 _143061 _143062) P x). Qed.
Lemma lem8055527 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x f) = (f x).
Proof. exact (@lem8055526 _143061 _143062 f x). Qed.
Lemma lem8055528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055529 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (term8 _143061 _143062 x f) = (term9 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8055528) (@lem8055527 _143061 _143062 f x)). Qed.
Lemma lem8055531 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8055532 {_143061 _143062 : Type'} (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x (@EMPTY ((cart _143061 _143062) -> Prop))) = False.
Proof. exact (@lem8055531 (type24 _143061 _143062) x). Qed.
Lemma lem8055533 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : ((@IN ((cart _143061 _143062) -> Prop) x f) = (@IN ((cart _143061 _143062) -> Prop) x (@EMPTY ((cart _143061 _143062) -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem8055529 _143061 _143062 f x) (@lem8055532 _143061 _143062 x)). Qed.
Lemma lem8055535 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8055536 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : ((f x) = False) = (term10 _143061 _143062 f x).
Proof. exact (@lem8055535 (f x)). Qed.
Lemma lem8055537 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : ((@IN ((cart _143061 _143062) -> Prop) x f) = (@IN ((cart _143061 _143062) -> Prop) x (@EMPTY ((cart _143061 _143062) -> Prop)))) = (term10 _143061 _143062 f x).
Proof. exact (TRANS (@lem8055533 _143061 _143062 f x) (@lem8055536 _143061 _143062 f x)). Qed.
Lemma lem8055538 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term11 _143061 _143062 f) = (term12 _143061 _143062 f).
Proof. exact (fun_ext (fun x : type24 _143061 _143062 => @lem8055537 _143061 _143062 f x)). Qed.
Lemma lem8055539 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055540 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term2 _143061 _143062 f) = (term13 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055539 _143061 _143062) (@lem8055538 _143061 _143062 f)). Qed.
Lemma lem8055545 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055546 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term4 _143061 _143062 f) = (term14 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055545) (@lem8055540 _143061 _143062 f)). Qed.
Lemma lem8055560 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8055561 {_143061 _143062 : Type'} (s : type56 _143061 _143062) (x : cart _143061 _143062) : (term17 _143061 _143062 x s) = (term18 _143061 _143062 s x).
Proof. exact (@lem8055560 (cart _143061 _143062) s x). Qed.
Lemma lem8055562 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (term19 _143061 _143062 x) = (term20 _143061 _143062 x).
Proof. exact (@lem8055561 _143061 _143062 (@EMPTY ((cart _143061 _143062) -> Prop)) x). Qed.
Lemma lem8055570 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8055571 {_143061 _143062 : Type'} (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x (@EMPTY ((cart _143061 _143062) -> Prop))) = False.
Proof. exact (@lem8055570 (type24 _143061 _143062) x). Qed.
Lemma lem8055572 {_143061 _143062 : Type'} (t : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) t (@EMPTY ((cart _143061 _143062) -> Prop))) = False.
Proof. exact (@lem8055571 _143061 _143062 t). Qed.
Lemma lem8055573 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055574 {_143061 _143062 : Type'} (t : type24 _143061 _143062) : (term21 _143061 _143062 t) = (imp False).
Proof. exact (MK_COMB (@lem8055573) (@lem8055572 _143061 _143062 t)). Qed.
Lemma lem8055576 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055577 {_143061 _143062 : Type'} (P : type24 _143061 _143062) (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x P) = (P x).
Proof. exact (@lem8055576 (cart _143061 _143062) P x). Qed.
Lemma lem8055578 {_143061 _143062 : Type'} (t : type24 _143061 _143062) (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x t) = (t x).
Proof. exact (@lem8055577 _143061 _143062 t x). Qed.
Lemma lem8055579 {_143061 _143062 : Type'} (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term22 _143061 _143062 x t) = (term23 _143061 _143062 t x).
Proof. exact (MK_COMB (@lem8055574 _143061 _143062 t) (@lem8055578 _143061 _143062 t x)). Qed.
Lemma lem8055581 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8055582 {_143061 _143062 : Type'} (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term23 _143061 _143062 t x) = True.
Proof. exact (@lem8055581 (t x)). Qed.
Lemma lem8055583 {_143061 _143062 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143062) : (term22 _143061 _143062 x t) = True.
Proof. exact (TRANS (@lem8055579 _143061 _143062 t x) (@lem8055582 _143061 _143062 t x)). Qed.
Lemma lem8055584 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (term24 _143061 _143062 x) = (term25 _143061 _143062).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8055583 _143061 _143062 x t)). Qed.
Lemma lem8055585 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055586 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (term20 _143061 _143062 x) = (term26 _143061 _143062).
Proof. exact (MK_COMB (@lem8055585 _143061 _143062) (@lem8055584 _143061 _143062 x)). Qed.
Lemma lem8055588 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8055589 {_143061 _143062 : Type'} (t : Prop) : (term28 _143061 _143062 t) = t.
Proof. exact (@lem8055588 (type24 _143061 _143062) t). Qed.
Lemma lem8055590 {_143061 _143062 : Type'} : (term26 _143061 _143062) = True.
Proof. exact (@lem8055589 _143061 _143062 True). Qed.
Lemma lem8055591 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (term20 _143061 _143062 x) = True.
Proof. exact (TRANS (@lem8055586 _143061 _143062 x) (@lem8055590 _143061 _143062)). Qed.
Lemma lem8055592 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (term19 _143061 _143062 x) = True.
Proof. exact (TRANS (@lem8055562 _143061 _143062 x) (@lem8055591 _143061 _143062 x)). Qed.
Lemma lem8055593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8055594 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (term29 _143061 _143062 x) = (and True).
Proof. exact (MK_COMB (@lem8055593) (@lem8055592 _143061 _143062 x)). Qed.
Lemma lem8055596 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055597 {_143061 _143063 : Type'} (P : type24 _143061 _143063) (x : cart _143061 _143063) : (@IN (cart _143061 _143063) x P) = (P x).
Proof. exact (@lem8055596 (cart _143061 _143063) P x). Qed.
Lemma lem8055598 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (@IN (cart _143061 _143063) y t) = (t y).
Proof. exact (@lem8055597 _143061 _143063 t y). Qed.
Lemma lem8055599 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term30 _143061 _143062 _143063 x y t) = (term31 _143061 _143063 t y).
Proof. exact (MK_COMB (@lem8055594 _143061 _143062 x) (@lem8055598 _143061 _143063 t y)). Qed.
Lemma lem8055601 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8055602 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term31 _143061 _143063 t y) = (t y).
Proof. exact (@lem8055601 (t y)). Qed.
Lemma lem8055603 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term30 _143061 _143062 _143063 x y t) = (t y).
Proof. exact (TRANS (@lem8055599 _143061 _143062 _143063 x t y) (@lem8055602 _143061 _143063 t y)). Qed.
Lemma lem8055604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055605 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term32 _143061 _143062 _143063 x y t) = (term33 _143061 _143063 t y).
Proof. exact (MK_COMB (@lem8055604) (@lem8055603 _143061 _143062 _143063 x t y)). Qed.
Lemma lem8055609 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem8055610 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x (@UNIV (cart _143061 _143062))) = True.
Proof. exact (@lem8055609 (cart _143061 _143062) x). Qed.
Lemma lem8055611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8055612 {_143061 _143062 : Type'} (x : cart _143061 _143062) : (term34 _143061 _143062 x) = (and True).
Proof. exact (MK_COMB (@lem8055611) (@lem8055610 _143061 _143062 x)). Qed.
Lemma lem8055614 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055615 {_143061 _143063 : Type'} (P : type24 _143061 _143063) (x : cart _143061 _143063) : (@IN (cart _143061 _143063) x P) = (P x).
Proof. exact (@lem8055614 (cart _143061 _143063) P x). Qed.
Lemma lem8055616 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (@IN (cart _143061 _143063) y t) = (t y).
Proof. exact (@lem8055615 _143061 _143063 t y). Qed.
Lemma lem8055617 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term35 _143061 _143062 _143063 x y t) = (term31 _143061 _143063 t y).
Proof. exact (MK_COMB (@lem8055612 _143061 _143062 x) (@lem8055616 _143061 _143063 t y)). Qed.
Lemma lem8055619 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8055620 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term31 _143061 _143063 t y) = (t y).
Proof. exact (@lem8055619 (t y)). Qed.
Lemma lem8055621 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term35 _143061 _143062 _143063 x y t) = (t y).
Proof. exact (TRANS (@lem8055617 _143061 _143062 _143063 x t y) (@lem8055620 _143061 _143063 t y)). Qed.
Lemma lem8055622 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term30 _143061 _143062 _143063 x y t) = (term35 _143061 _143062 _143063 x y t)) = ((t y) = (t y)).
Proof. exact (MK_COMB (@lem8055605 _143061 _143062 _143063 x t y) (@lem8055621 _143061 _143062 _143063 x t y)). Qed.
Lemma lem8055624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8055625 (x : Prop) : (x = x) = True.
Proof. exact (@lem8055624 Prop x). Qed.
Lemma lem8055626 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((t y) = (t y)) = True.
Proof. exact (@lem8055625 (t y)). Qed.
Lemma lem8055627 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : ((term30 _143061 _143062 _143063 x y t) = (term35 _143061 _143062 _143063 x y t)) = True.
Proof. exact (TRANS (@lem8055622 _143061 _143062 _143063 x t y) (@lem8055626 _143061 _143063 t y)). Qed.
Lemma lem8055628 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term36 _143061 _143062 _143063 x t) = (term37 _143061 _143063).
Proof. exact (fun_ext (fun y : cart _143061 _143063 => @lem8055627 _143061 _143062 _143063 x y t)). Qed.
Lemma lem8055629 {_143061 _143063 : Type'} : (@all (cart _143061 _143063)) = (@all (cart _143061 _143063)).
Proof. exact (eq_refl (@all (cart _143061 _143063))). Qed.
Lemma lem8055630 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term38 _143061 _143062 _143063 x t) = (term39 _143061 _143063).
Proof. exact (MK_COMB (@lem8055629 _143061 _143063) (@lem8055628 _143061 _143062 _143063 x t)). Qed.
Lemma lem8055632 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8055633 {_143061 _143063 : Type'} (t : Prop) : (term40 _143061 _143063 t) = t.
Proof. exact (@lem8055632 (cart _143061 _143063) t). Qed.
Lemma lem8055634 {_143061 _143063 : Type'} : (term39 _143061 _143063) = True.
Proof. exact (@lem8055633 _143061 _143063 True). Qed.
Lemma lem8055635 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term38 _143061 _143062 _143063 x t) = True.
Proof. exact (TRANS (@lem8055630 _143061 _143062 _143063 x t) (@lem8055634 _143061 _143063)). Qed.
Lemma lem8055636 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term41 _143061 _143062 _143063 t) = (term37 _143061 _143062).
Proof. exact (fun_ext (fun x : cart _143061 _143062 => @lem8055635 _143061 _143062 _143063 x t)). Qed.
Lemma lem8055637 {_143061 _143062 : Type'} : (@all (cart _143061 _143062)) = (@all (cart _143061 _143062)).
Proof. exact (eq_refl (@all (cart _143061 _143062))). Qed.
Lemma lem8055638 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term5 _143061 _143062 _143063 t) = (term39 _143061 _143062).
Proof. exact (MK_COMB (@lem8055637 _143061 _143062) (@lem8055636 _143061 _143062 _143063 t)). Qed.
Lemma lem8055640 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8055641 {_143061 _143062 : Type'} (t : Prop) : (term40 _143061 _143062 t) = t.
Proof. exact (@lem8055640 (cart _143061 _143062) t). Qed.
Lemma lem8055642 {_143061 _143062 : Type'} : (term39 _143061 _143062) = True.
Proof. exact (@lem8055641 _143061 _143062 True). Qed.
Lemma lem8055643 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term5 _143061 _143062 _143063 t) = True.
Proof. exact (TRANS (@lem8055638 _143061 _143062 _143063 t) (@lem8055642 _143061 _143062)). Qed.
Lemma lem8055644 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) : (term7 _143061 _143062 _143063 f t) = (term42 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055546 _143061 _143062 f) (@lem8055643 _143061 _143062 _143063 t)). Qed.
Lemma lem8055646 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8055647 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term42 _143061 _143062 f) = True.
Proof. exact (@lem8055646 (term13 _143061 _143062 f)). Qed.
Lemma lem8055648 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term7 _143061 _143062 _143063 f t) = True.
Proof. exact (TRANS (@lem8055644 _143061 _143062 _143063 t f) (@lem8055647 _143061 _143062 f)). Qed.
Lemma lem8055649 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : True = (term7 _143061 _143062 _143063 f t).
Proof. exact (SYM (@lem8055648 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055650 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term7 _143061 _143062 _143063 f t.
Proof. exact (EQ_MP (@lem8055649 _143061 _143062 _143063 f t) (@lem0)). Qed.
Lemma lem8055651 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term6 _143061 _143062 _143063 f t.
Proof. exact (EQ_MP (@lem8055515 _143061 _143062 _143063 f t) (@lem8055650 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055652 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : term5 _143061 _143062 _143063 t.
Proof. exact (@lem8055651 _143061 _143062 _143063 f t (@lem8049070 _143061 _143062 f h1)). Qed.
Lemma lem8055668 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8055669 {_143061 _143062 : Type'} (s : type56 _143061 _143062) (t : type56 _143061 _143062) : (s = t) = (term1 _143061 _143062 s t).
Proof. exact (@lem8055668 (type24 _143061 _143062) s t). Qed.
Lemma lem8055670 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (f = (@EMPTY ((cart _143061 _143062) -> Prop))) = (term2 _143061 _143062 f).
Proof. exact (@lem8055669 _143061 _143062 f (@EMPTY ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055679 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8055680 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term43 _143061 _143062 f) = (term44 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055679) (@lem8055670 _143061 _143062 f)). Qed.
Lemma lem8055681 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055682 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term45 _143061 _143062 f) = (term46 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055681) (@lem8055680 _143061 _143062 f)). Qed.
Lemma lem8055705 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term47 _143061 _143062 _143063 f t) = (term47 _143061 _143062 _143063 f t).
Proof. exact (eq_refl (term47 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055706 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term48 _143061 _143062 _143063 f t) = (term49 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8055682 _143061 _143062 f) (@lem8055705 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055709 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term49 _143061 _143062 _143063 f t) = (term48 _143061 _143062 _143063 f t).
Proof. exact (SYM (@lem8055706 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055719 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055720 {_143061 _143062 : Type'} (P : type56 _143061 _143062) (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x P) = (P x).
Proof. exact (@lem8055719 (type24 _143061 _143062) P x). Qed.
Lemma lem8055721 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x f) = (f x).
Proof. exact (@lem8055720 _143061 _143062 f x). Qed.
Lemma lem8055722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055723 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (term8 _143061 _143062 x f) = (term9 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8055722) (@lem8055721 _143061 _143062 f x)). Qed.
Lemma lem8055725 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8055726 {_143061 _143062 : Type'} (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x (@EMPTY ((cart _143061 _143062) -> Prop))) = False.
Proof. exact (@lem8055725 (type24 _143061 _143062) x). Qed.
Lemma lem8055727 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : ((@IN ((cart _143061 _143062) -> Prop) x f) = (@IN ((cart _143061 _143062) -> Prop) x (@EMPTY ((cart _143061 _143062) -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem8055723 _143061 _143062 f x) (@lem8055726 _143061 _143062 x)). Qed.
Lemma lem8055729 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8055730 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : ((f x) = False) = (term10 _143061 _143062 f x).
Proof. exact (@lem8055729 (f x)). Qed.
Lemma lem8055731 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : ((@IN ((cart _143061 _143062) -> Prop) x f) = (@IN ((cart _143061 _143062) -> Prop) x (@EMPTY ((cart _143061 _143062) -> Prop)))) = (term10 _143061 _143062 f x).
Proof. exact (TRANS (@lem8055727 _143061 _143062 f x) (@lem8055730 _143061 _143062 f x)). Qed.
Lemma lem8055732 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term11 _143061 _143062 f) = (term12 _143061 _143062 f).
Proof. exact (fun_ext (fun x : type24 _143061 _143062 => @lem8055731 _143061 _143062 f x)). Qed.
Lemma lem8055733 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055734 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term2 _143061 _143062 f) = (term13 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055733 _143061 _143062) (@lem8055732 _143061 _143062 f)). Qed.
Lemma lem8055739 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8055740 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term44 _143061 _143062 f) = (term50 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055739) (@lem8055734 _143061 _143062 f)). Qed.
Lemma lem8055741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055742 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term46 _143061 _143062 f) = (term51 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055741) (@lem8055740 _143061 _143062 f)). Qed.
Lemma lem8055756 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8055757 {_143061 _143062 : Type'} (s : type56 _143061 _143062) (x : cart _143061 _143062) : (term17 _143061 _143062 x s) = (term18 _143061 _143062 s x).
Proof. exact (@lem8055756 (cart _143061 _143062) s x). Qed.
Lemma lem8055758 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term17 _143061 _143062 x f) = (term18 _143061 _143062 f x).
Proof. exact (@lem8055757 _143061 _143062 f x). Qed.
Lemma lem8055766 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055767 {_143061 _143062 : Type'} (P : type56 _143061 _143062) (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x P) = (P x).
Proof. exact (@lem8055766 (type24 _143061 _143062) P x). Qed.
Lemma lem8055768 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) t f) = (f t).
Proof. exact (@lem8055767 _143061 _143062 f t). Qed.
Lemma lem8055769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055770 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) : (term52 _143061 _143062 t f) = (term53 _143061 _143062 f t).
Proof. exact (MK_COMB (@lem8055769) (@lem8055768 _143061 _143062 f t)). Qed.
Lemma lem8055772 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055773 {_143061 _143062 : Type'} (P : type24 _143061 _143062) (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x P) = (P x).
Proof. exact (@lem8055772 (cart _143061 _143062) P x). Qed.
Lemma lem8055774 {_143061 _143062 : Type'} (t : type24 _143061 _143062) (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x t) = (t x).
Proof. exact (@lem8055773 _143061 _143062 t x). Qed.
Lemma lem8055775 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term54 _143061 _143062 f x t) = (term55 _143061 _143062 f t x).
Proof. exact (MK_COMB (@lem8055770 _143061 _143062 f t) (@lem8055774 _143061 _143062 t x)). Qed.
Lemma lem8055778 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term56 _143061 _143062 f x) = (term57 _143061 _143062 f x).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8055775 _143061 _143062 f t x)). Qed.
Lemma lem8055779 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055780 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term18 _143061 _143062 f x) = (term58 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8055779 _143061 _143062) (@lem8055778 _143061 _143062 f x)). Qed.
Lemma lem8055785 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term17 _143061 _143062 x f) = (term58 _143061 _143062 f x).
Proof. exact (TRANS (@lem8055758 _143061 _143062 f x) (@lem8055780 _143061 _143062 f x)). Qed.
Lemma lem8055786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8055787 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term59 _143061 _143062 x f) = (term60 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8055786) (@lem8055785 _143061 _143062 f x)). Qed.
Lemma lem8055789 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055790 {_143061 _143063 : Type'} (P : type24 _143061 _143063) (x : cart _143061 _143063) : (@IN (cart _143061 _143063) x P) = (P x).
Proof. exact (@lem8055789 (cart _143061 _143063) P x). Qed.
Lemma lem8055791 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (@IN (cart _143061 _143063) y t) = (t y).
Proof. exact (@lem8055790 _143061 _143063 t y). Qed.
Lemma lem8055792 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term61 _143061 _143062 _143063 x f y t) = (term62 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8055787 _143061 _143062 f x) (@lem8055791 _143061 _143063 t y)). Qed.
Lemma lem8055795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055796 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term63 _143061 _143062 _143063 x f y t) = (term64 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8055795) (@lem8055792 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055804 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055805 {_143061 _143062 : Type'} (P : type56 _143061 _143062) (x : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) x P) = (P x).
Proof. exact (@lem8055804 (type24 _143061 _143062) P x). Qed.
Lemma lem8055806 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (@IN ((cart _143061 _143062) -> Prop) s f) = (f s).
Proof. exact (@lem8055805 _143061 _143062 f s). Qed.
Lemma lem8055807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055808 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term52 _143061 _143062 s f) = (term53 _143061 _143062 f s).
Proof. exact (MK_COMB (@lem8055807) (@lem8055806 _143061 _143062 f s)). Qed.
Lemma lem8055812 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055813 {_143061 _143062 : Type'} (P : type24 _143061 _143062) (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x P) = (P x).
Proof. exact (@lem8055812 (cart _143061 _143062) P x). Qed.
Lemma lem8055814 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (@IN (cart _143061 _143062) x s) = (s x).
Proof. exact (@lem8055813 _143061 _143062 s x). Qed.
Lemma lem8055815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8055816 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term65 _143061 _143062 x s) = (term66 _143061 _143062 s x).
Proof. exact (MK_COMB (@lem8055815) (@lem8055814 _143061 _143062 s x)). Qed.
Lemma lem8055818 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8055819 {_143061 _143063 : Type'} (P : type24 _143061 _143063) (x : cart _143061 _143063) : (@IN (cart _143061 _143063) x P) = (P x).
Proof. exact (@lem8055818 (cart _143061 _143063) P x). Qed.
Lemma lem8055820 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (@IN (cart _143061 _143063) y t) = (t y).
Proof. exact (@lem8055819 _143061 _143063 t y). Qed.
Lemma lem8055821 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term67 _143061 _143062 _143063 x s y t) = (term68 _143061 _143062 _143063 s x t y).
Proof. exact (MK_COMB (@lem8055816 _143061 _143062 s x) (@lem8055820 _143061 _143063 t y)). Qed.
Lemma lem8055824 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term69 _143061 _143062 _143063 f x s y t) = (term70 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8055808 _143061 _143062 f s) (@lem8055821 _143061 _143062 _143063 s x t y)). Qed.
Lemma lem8055827 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term71 _143061 _143062 _143063 f x y t) = (term72 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8055824 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8055828 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055829 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term73 _143061 _143062 _143063 f x y t) = (term74 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8055828 _143061 _143062) (@lem8055827 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055834 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term61 _143061 _143062 _143063 x f y t) = (term73 _143061 _143062 _143063 f x y t)) = ((term62 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y)).
Proof. exact (MK_COMB (@lem8055796 _143061 _143062 _143063 f x t y) (@lem8055829 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055837 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term75 _143061 _143062 _143063 f x t) = (term76 _143061 _143062 _143063 f x t).
Proof. exact (fun_ext (fun y : cart _143061 _143063 => @lem8055834 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055838 {_143061 _143063 : Type'} : (@all (cart _143061 _143063)) = (@all (cart _143061 _143063)).
Proof. exact (eq_refl (@all (cart _143061 _143063))). Qed.
Lemma lem8055839 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term77 _143061 _143062 _143063 f x t) = (term78 _143061 _143062 _143063 f x t).
Proof. exact (MK_COMB (@lem8055838 _143061 _143063) (@lem8055837 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8055844 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term79 _143061 _143062 _143063 f t) = (term80 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun x : cart _143061 _143062 => @lem8055839 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8055845 {_143061 _143062 : Type'} : (@all (cart _143061 _143062)) = (@all (cart _143061 _143062)).
Proof. exact (eq_refl (@all (cart _143061 _143062))). Qed.
Lemma lem8055846 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term47 _143061 _143062 _143063 f t) = (term81 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8055845 _143061 _143062) (@lem8055844 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055851 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term49 _143061 _143062 _143063 f t) = (term82 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8055742 _143061 _143062 f) (@lem8055846 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055854 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term82 _143061 _143062 _143063 f t) = (term49 _143061 _143062 _143063 f t).
Proof. exact (SYM (@lem8055851 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055856 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8055857 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term82 _143061 _143062 _143063 f t) = (term84 _143061 _143062 _143063 f t).
Proof. exact (@lem8055856 (term82 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055858 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term84 _143061 _143062 _143063 f t) = (term82 _143061 _143062 _143063 f t).
Proof. exact (SYM (@lem8055857 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055859 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term85 _143061 _143062 _143063 f t) : term85 _143061 _143062 _143063 f t.
Proof. exact (h1). Qed.
Lemma lem8055862 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term84 _143061 _143062 _143063 f t) : term84 _143061 _143062 _143063 f t.
Proof. exact (h1). Qed.
Lemma lem8055863 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term86 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : term84 _143061 _143062 _143063 f t => @lem8055862 _143061 _143062 _143063 f t h0). Qed.
Lemma lem8055864 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term86 _143061 _143062 _143063 f t) : term86 _143061 _143062 _143063 f t.
Proof. exact (h1). Qed.
Lemma lem8055865 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term84 _143061 _143062 _143063 f t) : term84 _143061 _143062 _143063 f t.
Proof. exact (h1). Qed.
Lemma lem8055866 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term84 _143061 _143062 _143063 f t) (h2 : term86 _143061 _143062 _143063 f t) : term84 _143061 _143062 _143063 f t.
Proof. exact (@lem8055864 _143061 _143062 _143063 f t h2 (@lem8055865 _143061 _143062 _143063 f t h1)). Qed.
Lemma lem8055867 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term84 _143061 _143062 _143063 f t) : term87 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : term86 _143061 _143062 _143063 f t => @lem8055866 _143061 _143062 _143063 f t h1 h0). Qed.
Lemma lem8055868 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term86 _143061 _143062 _143063 f t) : term86 _143061 _143062 _143063 f t.
Proof. exact (h1). Qed.
Lemma lem8055869 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term84 _143061 _143062 _143063 f t) (h2 : term86 _143061 _143062 _143063 f t) : term84 _143061 _143062 _143063 f t.
Proof. exact (@lem8055867 _143061 _143062 _143063 f t h1 (@lem8055868 _143061 _143062 _143063 f t h2)). Qed.
Lemma lem8055870 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term86 _143061 _143062 _143063 f t) : term86 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : term84 _143061 _143062 _143063 f t => @lem8055869 _143061 _143062 _143063 f t h0 h1). Qed.
Lemma lem8055871 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term88 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : term86 _143061 _143062 _143063 f t => @lem8055870 _143061 _143062 _143063 f t h0). Qed.
Lemma lem8055874 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term86 _143061 _143062 _143063 f t.
Proof. exact (@lem8055871 _143061 _143062 _143063 f t (@lem8055863 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055875 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term86 _143061 _143062 _143063 f t.
Proof. exact (@lem8055874 _143061 _143062 _143063 f t). Qed.
Lemma lem8055885 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8055886 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term84 _143061 _143062 _143063 f t) = (term89 _143061 _143062 _143063 f t).
Proof. exact (@lem8055885 (term85 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055888 (t : Prop) : (term90 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8055889 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term89 _143061 _143062 _143063 f t) = (term82 _143061 _143062 _143063 f t).
Proof. exact (@lem8055888 (term82 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055892 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term84 _143061 _143062 _143063 f t) = (term82 _143061 _143062 _143063 f t).
Proof. exact (TRANS (@lem8055886 _143061 _143062 _143063 f t) (@lem8055889 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055921 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term91 _143061 _143062 _143063 t) = (term92 _143061 _143062 _143063 t).
Proof. exact (fun_ext (fun f : type56 _143061 _143062 => @lem8055892 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055922 {_143061 _143062 : Type'} : (@all (((cart _143061 _143062) -> Prop) -> Prop)) = (@all (((cart _143061 _143062) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _143061 _143062) -> Prop) -> Prop))). Qed.
Lemma lem8055923 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term93 _143061 _143062 _143063 t) = (term94 _143061 _143062 _143063 t).
Proof. exact (MK_COMB (@lem8055922 _143061 _143062) (@lem8055921 _143061 _143062 _143063 t)). Qed.
Lemma lem8055928 {_143061 _143062 _143063 : Type'} : (term95 _143061 _143062 _143063) = (term96 _143061 _143062 _143063).
Proof. exact (fun_ext (fun t : type24 _143061 _143063 => @lem8055923 _143061 _143062 _143063 t)). Qed.
Lemma lem8055929 {_143061 _143063 : Type'} : (@all ((cart _143061 _143063) -> Prop)) = (@all ((cart _143061 _143063) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143063) -> Prop))). Qed.
Lemma lem8055938 {_143061 _143062 _143063 : Type'} : (term97 _143061 _143062 _143063) = (term98 _143061 _143062 _143063).
Proof. exact (MK_COMB (@lem8055929 _143061 _143063) (@lem8055928 _143061 _143062 _143063)). Qed.
Lemma lem8055947 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term70 _143061 _143062 _143063 f s x t y) = (term70 _143061 _143062 _143063 f s x t y).
Proof. exact (eq_refl (term70 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8055948 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term72 _143061 _143062 _143063 f x t y) = (term72 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8055947 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8055949 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055950 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term74 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8055949 _143061 _143062) (@lem8055948 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055951 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (t y) = (t y).
Proof. exact (eq_refl (t y)). Qed.
Lemma lem8055956 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term55 _143061 _143062 f t x) = (term55 _143061 _143062 f t x).
Proof. exact (eq_refl (term55 _143061 _143062 f t x)). Qed.
Lemma lem8055957 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term57 _143061 _143062 f x) = (term57 _143061 _143062 f x).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8055956 _143061 _143062 f t x)). Qed.
Lemma lem8055958 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055959 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term58 _143061 _143062 f x) = (term58 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8055958 _143061 _143062) (@lem8055957 _143061 _143062 f x)). Qed.
Lemma lem8055960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8055961 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term60 _143061 _143062 f x) = (term60 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8055960) (@lem8055959 _143061 _143062 f x)). Qed.
Lemma lem8055962 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term62 _143061 _143062 _143063 f x t y) = (term62 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8055961 _143061 _143062 f x) (@lem8055951 _143061 _143063 t y)). Qed.
Lemma lem8055963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055964 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term64 _143061 _143062 _143063 f x t y) = (term64 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8055963) (@lem8055962 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055965 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term62 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y)) = ((term62 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y)).
Proof. exact (MK_COMB (@lem8055964 _143061 _143062 _143063 f x t y) (@lem8055950 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055966 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term76 _143061 _143062 _143063 f x t) = (term76 _143061 _143062 _143063 f x t).
Proof. exact (fun_ext (fun y : cart _143061 _143063 => @lem8055965 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8055967 {_143061 _143063 : Type'} : (@all (cart _143061 _143063)) = (@all (cart _143061 _143063)).
Proof. exact (eq_refl (@all (cart _143061 _143063))). Qed.
Lemma lem8055968 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term78 _143061 _143062 _143063 f x t) = (term78 _143061 _143062 _143063 f x t).
Proof. exact (MK_COMB (@lem8055967 _143061 _143063) (@lem8055966 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8055969 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term80 _143061 _143062 _143063 f t) = (term80 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun x : cart _143061 _143062 => @lem8055968 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8055970 {_143061 _143062 : Type'} : (@all (cart _143061 _143062)) = (@all (cart _143061 _143062)).
Proof. exact (eq_refl (@all (cart _143061 _143062))). Qed.
Lemma lem8055971 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term81 _143061 _143062 _143063 f t) = (term81 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8055970 _143061 _143062) (@lem8055969 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055974 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (term10 _143061 _143062 f x) = (term10 _143061 _143062 f x).
Proof. exact (eq_refl (term10 _143061 _143062 f x)). Qed.
Lemma lem8055975 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term12 _143061 _143062 f) = (term12 _143061 _143062 f).
Proof. exact (fun_ext (fun x : type24 _143061 _143062 => @lem8055974 _143061 _143062 f x)). Qed.
Lemma lem8055976 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8055977 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term13 _143061 _143062 f) = (term13 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055976 _143061 _143062) (@lem8055975 _143061 _143062 f)). Qed.
Lemma lem8055978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8055979 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term50 _143061 _143062 f) = (term50 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055978) (@lem8055977 _143061 _143062 f)). Qed.
Lemma lem8055980 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055981 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term51 _143061 _143062 f) = (term51 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8055980) (@lem8055979 _143061 _143062 f)). Qed.
Lemma lem8055982 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term82 _143061 _143062 _143063 f t) = (term82 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8055981 _143061 _143062 f) (@lem8055971 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055983 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term92 _143061 _143062 _143063 t) = (term92 _143061 _143062 _143063 t).
Proof. exact (fun_ext (fun f : type56 _143061 _143062 => @lem8055982 _143061 _143062 _143063 f t)). Qed.
Lemma lem8055984 {_143061 _143062 : Type'} : (@all (((cart _143061 _143062) -> Prop) -> Prop)) = (@all (((cart _143061 _143062) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _143061 _143062) -> Prop) -> Prop))). Qed.
Lemma lem8055985 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term94 _143061 _143062 _143063 t) = (term94 _143061 _143062 _143063 t).
Proof. exact (MK_COMB (@lem8055984 _143061 _143062) (@lem8055983 _143061 _143062 _143063 t)). Qed.
Lemma lem8055986 {_143061 _143062 _143063 : Type'} : (term96 _143061 _143062 _143063) = (term96 _143061 _143062 _143063).
Proof. exact (fun_ext (fun t : type24 _143061 _143063 => @lem8055985 _143061 _143062 _143063 t)). Qed.
Lemma lem8055987 {_143061 _143063 : Type'} : (@all ((cart _143061 _143063) -> Prop)) = (@all ((cart _143061 _143063) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143063) -> Prop))). Qed.
Lemma lem8055988 {_143061 _143062 _143063 : Type'} : (term98 _143061 _143062 _143063) = (term98 _143061 _143062 _143063).
Proof. exact (MK_COMB (@lem8055987 _143061 _143063) (@lem8055986 _143061 _143062 _143063)). Qed.
Lemma lem8056043 {_143061 _143062 _143063 : Type'} : (term97 _143061 _143062 _143063) = (term98 _143061 _143062 _143063).
Proof. exact (TRANS (@lem8055938 _143061 _143062 _143063) (@lem8055988 _143061 _143062 _143063)). Qed.
Lemma lem8056044 {_143061 _143062 _143063 : Type'} : (term98 _143061 _143062 _143063) = (term97 _143061 _143062 _143063).
Proof. exact (SYM (@lem8056043 _143061 _143062 _143063)). Qed.
Lemma lem8056045 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (h1 : term50 _143061 _143062 f) : term50 _143061 _143062 f.
Proof. exact (h1). Qed.
Lemma lem8056047 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8056048 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term62 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y)) = (term99 _143061 _143062 _143063 f x t y).
Proof. exact (@lem8056047 ((term62 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y))). Qed.
Lemma lem8056049 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term99 _143061 _143062 _143063 f x t y) = ((term62 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y)).
Proof. exact (SYM (@lem8056048 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056050 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term100 _143061 _143062 _143063 f x t y) : term100 _143061 _143062 _143063 f x t y.
Proof. exact (h1). Qed.
Lemma lem8056053 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (term101 _143061 _143062 f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem8056054 {_143061 _143062 : Type'} (P : type56 _143061 _143062) : (term102 _143061 _143062 P) = (term103 _143061 _143062 P).
Proof. exact (@lem18392 (type24 _143061 _143062) P). Qed.
Lemma lem8056055 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term50 _143061 _143062 f) = (term104 _143061 _143062 f).
Proof. exact (@lem8056054 _143061 _143062 (term12 _143061 _143062 f)). Qed.
Lemma lem8056056 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (term105 _143061 _143062 f x) = (term10 _143061 _143062 f x).
Proof. exact (eq_refl (term105 _143061 _143062 f x)). Qed.
Lemma lem8056057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056058 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (term106 _143061 _143062 f x) = (term101 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056057) (@lem8056056 _143061 _143062 f x)). Qed.
Lemma lem8056059 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (term106 _143061 _143062 f x) = (f x).
Proof. exact (TRANS (@lem8056058 _143061 _143062 f x) (@lem8056053 _143061 _143062 f x)). Qed.
Lemma lem8056060 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term107 _143061 _143062 f) = (term108 _143061 _143062 f).
Proof. exact (fun_ext (fun x : type24 _143061 _143062 => @lem8056059 _143061 _143062 f x)). Qed.
Lemma lem8056061 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056062 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term104 _143061 _143062 f) = (term109 _143061 _143062 f).
Proof. exact (MK_COMB (@lem8056061 _143061 _143062) (@lem8056060 _143061 _143062 f)). Qed.
Lemma lem8056071 {_143061 _143062 : Type'} (f : type56 _143061 _143062) : (term50 _143061 _143062 f) = (term109 _143061 _143062 f).
Proof. exact (TRANS (@lem8056055 _143061 _143062 f) (@lem8056062 _143061 _143062 f)). Qed.
Lemma lem8056072 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (h1 : term50 _143061 _143062 f) : term109 _143061 _143062 f.
Proof. exact (EQ_MP (@lem8056071 _143061 _143062 f) (@lem8056045 _143061 _143062 f h1)). Qed.
Lemma lem8056081 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term110 _143061 _143062 f t x) = (term111 _143061 _143062 f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem8056086 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term55 _143061 _143062 f t x) = (term112 _143061 _143062 f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem8056087 {_143061 _143062 : Type'} (P : type56 _143061 _143062) : (term102 _143061 _143062 P) = (term103 _143061 _143062 P).
Proof. exact (@lem18392 (type24 _143061 _143062) P). Qed.
Lemma lem8056088 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term113 _143061 _143062 f x) = (term114 _143061 _143062 f x).
Proof. exact (@lem8056087 _143061 _143062 (term57 _143061 _143062 f x)). Qed.
Lemma lem8056089 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term115 _143061 _143062 f x t) = (term55 _143061 _143062 f t x).
Proof. exact (eq_refl (term115 _143061 _143062 f x t)). Qed.
Lemma lem8056090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056091 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term116 _143061 _143062 f x t) = (term110 _143061 _143062 f t x).
Proof. exact (MK_COMB (@lem8056090) (@lem8056089 _143061 _143062 f t x)). Qed.
Lemma lem8056092 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term116 _143061 _143062 f x t) = (term111 _143061 _143062 f t x).
Proof. exact (TRANS (@lem8056091 _143061 _143062 f t x) (@lem8056081 _143061 _143062 f t x)). Qed.
Lemma lem8056093 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term117 _143061 _143062 f x) = (term118 _143061 _143062 f x).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8056092 _143061 _143062 f t x)). Qed.
Lemma lem8056094 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056095 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term114 _143061 _143062 f x) = (term119 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056094 _143061 _143062) (@lem8056093 _143061 _143062 f x)). Qed.
Lemma lem8056096 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term113 _143061 _143062 f x) = (term119 _143061 _143062 f x).
Proof. exact (TRANS (@lem8056088 _143061 _143062 f x) (@lem8056095 _143061 _143062 f x)). Qed.
Lemma lem8056097 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term57 _143061 _143062 f x) = (term120 _143061 _143062 f x).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8056086 _143061 _143062 f t x)). Qed.
Lemma lem8056098 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056099 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term58 _143061 _143062 f x) = (term121 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056098 _143061 _143062) (@lem8056097 _143061 _143062 f x)). Qed.
Lemma lem8056100 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term122 _143061 _143063 t y) = (term122 _143061 _143063 t y).
Proof. exact (eq_refl (term122 _143061 _143063 t y)). Qed.
Lemma lem8056101 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (t y) = (t y).
Proof. exact (eq_refl (t y)). Qed.
Lemma lem8056102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056103 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term123 _143061 _143062 f x) = (term124 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056102) (@lem8056096 _143061 _143062 f x)). Qed.
Lemma lem8056104 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term125 _143061 _143062 _143063 f x t y) = (term126 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056103 _143061 _143062 f x) (@lem8056100 _143061 _143063 t y)). Qed.
Lemma lem8056105 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term127 _143061 _143062 _143063 f x t y) = (term125 _143061 _143062 _143063 f x t y).
Proof. exact (@lem17045 (term58 _143061 _143062 f x) (t y)). Qed.
Lemma lem8056106 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term127 _143061 _143062 _143063 f x t y) = (term126 _143061 _143062 _143063 f x t y).
Proof. exact (TRANS (@lem8056105 _143061 _143062 _143063 f x t y) (@lem8056104 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056108 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term60 _143061 _143062 f x) = (term128 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056107) (@lem8056099 _143061 _143062 f x)). Qed.
Lemma lem8056109 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term62 _143061 _143062 _143063 f x t y) = (term129 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056108 _143061 _143062 f x) (@lem8056101 _143061 _143063 t y)). Qed.
Lemma lem8056120 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term130 _143061 _143062 _143063 s x t y) = (term131 _143061 _143062 _143063 s x t y).
Proof. exact (@lem17045 (s x) (t y)). Qed.
Lemma lem8056125 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term132 _143061 _143062 f s) = (term132 _143061 _143062 f s).
Proof. exact (eq_refl (term132 _143061 _143062 f s)). Qed.
Lemma lem8056126 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term133 _143061 _143062 _143063 f s x t y) = (term134 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056125 _143061 _143062 f s) (@lem8056120 _143061 _143062 _143063 s x t y)). Qed.
Lemma lem8056127 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term135 _143061 _143062 _143063 f s x t y) = (term133 _143061 _143062 _143063 f s x t y).
Proof. exact (@lem17362 (f s) (term68 _143061 _143062 _143063 s x t y)). Qed.
Lemma lem8056128 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term135 _143061 _143062 _143063 f s x t y) = (term134 _143061 _143062 _143063 f s x t y).
Proof. exact (TRANS (@lem8056127 _143061 _143062 _143063 f s x t y) (@lem8056126 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056133 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term70 _143061 _143062 _143063 f s x t y) = (term136 _143061 _143062 _143063 f s x t y).
Proof. exact (@lem17265 (f s) (term68 _143061 _143062 _143063 s x t y)). Qed.
Lemma lem8056134 {_143061 _143062 : Type'} (P : type56 _143061 _143062) : (term102 _143061 _143062 P) = (term103 _143061 _143062 P).
Proof. exact (@lem18392 (type24 _143061 _143062) P). Qed.
Lemma lem8056135 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term137 _143061 _143062 _143063 f x t y) = (term138 _143061 _143062 _143063 f x t y).
Proof. exact (@lem8056134 _143061 _143062 (term72 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056136 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term139 _143061 _143062 _143063 f x t y s) = (term70 _143061 _143062 _143063 f s x t y).
Proof. exact (eq_refl (term139 _143061 _143062 _143063 f x t y s)). Qed.
Lemma lem8056137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056138 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term140 _143061 _143062 _143063 f x t y s) = (term135 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056137) (@lem8056136 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056139 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term140 _143061 _143062 _143063 f x t y s) = (term134 _143061 _143062 _143063 f s x t y).
Proof. exact (TRANS (@lem8056138 _143061 _143062 _143063 f s x t y) (@lem8056128 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056140 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term141 _143061 _143062 _143063 f x t y) = (term142 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056139 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056141 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056142 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term138 _143061 _143062 _143063 f x t y) = (term143 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056141 _143061 _143062) (@lem8056140 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056143 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term137 _143061 _143062 _143063 f x t y) = (term143 _143061 _143062 _143063 f x t y).
Proof. exact (TRANS (@lem8056135 _143061 _143062 _143063 f x t y) (@lem8056142 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056144 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term72 _143061 _143062 _143063 f x t y) = (term144 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056133 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056145 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056146 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term74 _143061 _143062 _143063 f x t y) = (term145 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056145 _143061 _143062) (@lem8056144 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056148 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term146 _143061 _143062 _143063 f x t y) = (term147 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056147) (@lem8056106 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056149 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term148 _143061 _143062 _143063 f x t y) = (term149 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056148 _143061 _143062 _143063 f x t y) (@lem8056146 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056151 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term150 _143061 _143062 _143063 f x t y) = (term151 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056150) (@lem8056109 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056152 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term152 _143061 _143062 _143063 f x t y) = (term153 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056151 _143061 _143062 _143063 f x t y) (@lem8056143 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056154 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term154 _143061 _143062 _143063 f x t y) = (term155 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056153) (@lem8056152 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056155 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term156 _143061 _143062 _143063 f x t y) = (term157 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056154 _143061 _143062 _143063 f x t y) (@lem8056149 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056156 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term100 _143061 _143062 _143063 f x t y) = (term156 _143061 _143062 _143063 f x t y).
Proof. exact (@lem17646 (term62 _143061 _143062 _143063 f x t y) (term74 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056157 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term100 _143061 _143062 _143063 f x t y) = (term157 _143061 _143062 _143063 f x t y).
Proof. exact (TRANS (@lem8056156 _143061 _143062 _143063 f x t y) (@lem8056155 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056312 {A : Type'} (P : Prop) (Q : A -> Prop) : (term158 A P Q) = (term159 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8056313 {_143061 _143062 : Type'} (P : Prop) (Q : type56 _143061 _143062) : (term160 _143061 _143062 P Q) = (term161 _143061 _143062 P Q).
Proof. exact (@lem8056312 (type24 _143061 _143062) P Q). Qed.
Lemma lem8056314 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term162 _143061 _143062 _143063 f x t y) = (term163 _143061 _143062 _143063 f x t y).
Proof. exact (@lem8056313 _143061 _143062 (term129 _143061 _143062 _143063 f x t y) (term142 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056315 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term164 _143061 _143062 _143063 f x t y s) = (term134 _143061 _143062 _143063 f s x t y).
Proof. exact (eq_refl (term164 _143061 _143062 _143063 f x t y s)). Qed.
Lemma lem8056316 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term165 _143061 _143062 _143063 f x t y) = (term142 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056315 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056317 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056318 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term166 _143061 _143062 _143063 f x t y) = (term143 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056317 _143061 _143062) (@lem8056316 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056319 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term151 _143061 _143062 _143063 f x t y) = (term151 _143061 _143062 _143063 f x t y).
Proof. exact (eq_refl (term151 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056320 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term162 _143061 _143062 _143063 f x t y) = (term153 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056319 _143061 _143062 _143063 f x t y) (@lem8056318 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8056322 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term167 _143061 _143062 _143063 f x t y) = (term168 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056321) (@lem8056320 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056323 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term164 _143061 _143062 _143063 f x t y s) = (term134 _143061 _143062 _143063 f s x t y).
Proof. exact (eq_refl (term164 _143061 _143062 _143063 f x t y s)). Qed.
Lemma lem8056324 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term151 _143061 _143062 _143063 f x t y) = (term151 _143061 _143062 _143063 f x t y).
Proof. exact (eq_refl (term151 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056325 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term169 _143061 _143062 _143063 f x t y s) = (term170 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056324 _143061 _143062 _143063 f x t y) (@lem8056323 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056326 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term171 _143061 _143062 _143063 f x t y) = (term172 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056325 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056327 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056328 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term163 _143061 _143062 _143063 f x t y) = (term173 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056327 _143061 _143062) (@lem8056326 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056329 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term162 _143061 _143062 _143063 f x t y) = (term163 _143061 _143062 _143063 f x t y)) = ((term153 _143061 _143062 _143063 f x t y) = (term173 _143061 _143062 _143063 f x t y)).
Proof. exact (MK_COMB (@lem8056322 _143061 _143062 _143063 f x t y) (@lem8056328 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056330 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term153 _143061 _143062 _143063 f x t y) = (term173 _143061 _143062 _143063 f x t y).
Proof. exact (EQ_MP (@lem8056329 _143061 _143062 _143063 f x t y) (@lem8056314 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056332 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term155 _143061 _143062 _143063 f x t y) = (term174 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056331) (@lem8056330 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056334 {A : Type'} (P : A -> Prop) (Q : Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8056335 {_143061 _143062 : Type'} (P : type56 _143061 _143062) (Q : Prop) : (term177 _143061 _143062 P Q) = (term178 _143061 _143062 P Q).
Proof. exact (@lem8056334 (type24 _143061 _143062) P Q). Qed.
Lemma lem8056336 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term179 _143061 _143062 _143063 f x t y) = (term180 _143061 _143062 _143063 f x t y).
Proof. exact (@lem8056335 _143061 _143062 (term118 _143061 _143062 f x) (term122 _143061 _143063 t y)). Qed.
Lemma lem8056337 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term181 _143061 _143062 f x t) = (term111 _143061 _143062 f t x).
Proof. exact (eq_refl (term181 _143061 _143062 f x t)). Qed.
Lemma lem8056338 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term182 _143061 _143062 f x) = (term118 _143061 _143062 f x).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8056337 _143061 _143062 f t x)). Qed.
Lemma lem8056339 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056340 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term183 _143061 _143062 f x) = (term119 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056339 _143061 _143062) (@lem8056338 _143061 _143062 f x)). Qed.
Lemma lem8056341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056342 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term184 _143061 _143062 f x) = (term124 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056341) (@lem8056340 _143061 _143062 f x)). Qed.
Lemma lem8056343 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term122 _143061 _143063 t y) = (term122 _143061 _143063 t y).
Proof. exact (eq_refl (term122 _143061 _143063 t y)). Qed.
Lemma lem8056344 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term179 _143061 _143062 _143063 f x t y) = (term126 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056342 _143061 _143062 f x) (@lem8056343 _143061 _143063 t y)). Qed.
Lemma lem8056345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8056346 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term185 _143061 _143062 _143063 f x t y) = (term186 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056345) (@lem8056344 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056347 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term181 _143061 _143062 f x t) = (term111 _143061 _143062 f t x).
Proof. exact (eq_refl (term181 _143061 _143062 f x t)). Qed.
Lemma lem8056348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056349 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term187 _143061 _143062 f x t) = (term188 _143061 _143062 f t x).
Proof. exact (MK_COMB (@lem8056348) (@lem8056347 _143061 _143062 f t x)). Qed.
Lemma lem8056350 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term122 _143061 _143063 t y) = (term122 _143061 _143063 t y).
Proof. exact (eq_refl (term122 _143061 _143063 t y)). Qed.
Lemma lem8056351 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) (t' : type24 _143061 _143063) (y : cart _143061 _143063) : (term189 _143061 _143062 _143063 f x t t' y) = (term190 _143061 _143062 _143063 f t x t' y).
Proof. exact (MK_COMB (@lem8056349 _143061 _143062 f t x) (@lem8056350 _143061 _143063 t' y)). Qed.
Lemma lem8056352 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term191 _143061 _143062 _143063 f x t y) = (term192 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun t' : type24 _143061 _143062 => @lem8056351 _143061 _143062 _143063 f t' x t y)). Qed.
Lemma lem8056353 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056354 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term180 _143061 _143062 _143063 f x t y) = (term193 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056353 _143061 _143062) (@lem8056352 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056355 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term179 _143061 _143062 _143063 f x t y) = (term180 _143061 _143062 _143063 f x t y)) = ((term126 _143061 _143062 _143063 f x t y) = (term193 _143061 _143062 _143063 f x t y)).
Proof. exact (MK_COMB (@lem8056346 _143061 _143062 _143063 f x t y) (@lem8056354 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056356 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term126 _143061 _143062 _143063 f x t y) = (term193 _143061 _143062 _143063 f x t y).
Proof. exact (EQ_MP (@lem8056355 _143061 _143062 _143063 f x t y) (@lem8056336 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056358 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term147 _143061 _143062 _143063 f x t y) = (term194 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056357) (@lem8056356 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056359 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term145 _143061 _143062 _143063 f x t y) = (term145 _143061 _143062 _143063 f x t y).
Proof. exact (eq_refl (term145 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056360 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term149 _143061 _143062 _143063 f x t y) = (term195 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056358 _143061 _143062 _143063 f x t y) (@lem8056359 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056362 {A : Type'} (P : A -> Prop) (Q : Prop) : (term196 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8056363 {_143061 _143062 : Type'} (P : type56 _143061 _143062) (Q : Prop) : (term198 _143061 _143062 P Q) = (term199 _143061 _143062 P Q).
Proof. exact (@lem8056362 (type24 _143061 _143062) P Q). Qed.
Lemma lem8056364 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term200 _143061 _143062 _143063 f x t y) = (term201 _143061 _143062 _143063 f x t y).
Proof. exact (@lem8056363 _143061 _143062 (term192 _143061 _143062 _143063 f x t y) (term145 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056365 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) (t' : type24 _143061 _143063) (y : cart _143061 _143063) : (term202 _143061 _143062 _143063 f x t' y t) = (term190 _143061 _143062 _143063 f t x t' y).
Proof. exact (eq_refl (term202 _143061 _143062 _143063 f x t' y t)). Qed.
Lemma lem8056366 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term203 _143061 _143062 _143063 f x t y) = (term192 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun t' : type24 _143061 _143062 => @lem8056365 _143061 _143062 _143063 f t' x t y)). Qed.
Lemma lem8056367 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056368 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term204 _143061 _143062 _143063 f x t y) = (term193 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056367 _143061 _143062) (@lem8056366 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056370 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term205 _143061 _143062 _143063 f x t y) = (term194 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056369) (@lem8056368 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056371 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term145 _143061 _143062 _143063 f x t y) = (term145 _143061 _143062 _143063 f x t y).
Proof. exact (eq_refl (term145 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056372 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term200 _143061 _143062 _143063 f x t y) = (term195 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056370 _143061 _143062 _143063 f x t y) (@lem8056371 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8056374 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term206 _143061 _143062 _143063 f x t y) = (term207 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056373) (@lem8056372 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056375 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) (t' : type24 _143061 _143063) (y : cart _143061 _143063) : (term202 _143061 _143062 _143063 f x t' y t) = (term190 _143061 _143062 _143063 f t x t' y).
Proof. exact (eq_refl (term202 _143061 _143062 _143063 f x t' y t)). Qed.
Lemma lem8056376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056377 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) (t' : type24 _143061 _143063) (y : cart _143061 _143063) : (term208 _143061 _143062 _143063 f x t' y t) = (term209 _143061 _143062 _143063 f t x t' y).
Proof. exact (MK_COMB (@lem8056376) (@lem8056375 _143061 _143062 _143063 f t x t' y)). Qed.
Lemma lem8056378 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term145 _143061 _143062 _143063 f x t y) = (term145 _143061 _143062 _143063 f x t y).
Proof. exact (eq_refl (term145 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056379 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t' : type24 _143061 _143063) (y : cart _143061 _143063) : (term210 _143061 _143062 _143063 t f x t' y) = (term211 _143061 _143062 _143063 t f x t' y).
Proof. exact (MK_COMB (@lem8056377 _143061 _143062 _143063 f t x t' y) (@lem8056378 _143061 _143062 _143063 f x t' y)). Qed.
Lemma lem8056380 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term212 _143061 _143062 _143063 f x t y) = (term213 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun t' : type24 _143061 _143062 => @lem8056379 _143061 _143062 _143063 t' f x t y)). Qed.
Lemma lem8056381 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056382 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term201 _143061 _143062 _143063 f x t y) = (term214 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056381 _143061 _143062) (@lem8056380 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056383 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term200 _143061 _143062 _143063 f x t y) = (term201 _143061 _143062 _143063 f x t y)) = ((term195 _143061 _143062 _143063 f x t y) = (term214 _143061 _143062 _143063 f x t y)).
Proof. exact (MK_COMB (@lem8056374 _143061 _143062 _143063 f x t y) (@lem8056382 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056384 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term195 _143061 _143062 _143063 f x t y) = (term214 _143061 _143062 _143063 f x t y).
Proof. exact (EQ_MP (@lem8056383 _143061 _143062 _143063 f x t y) (@lem8056364 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056385 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term149 _143061 _143062 _143063 f x t y) = (term214 _143061 _143062 _143063 f x t y).
Proof. exact (TRANS (@lem8056360 _143061 _143062 _143063 f x t y) (@lem8056384 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056386 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term157 _143061 _143062 _143063 f x t y) = (term215 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056332 _143061 _143062 _143063 f x t y) (@lem8056385 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056388 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8056389 {_143061 _143062 : Type'} (P : type56 _143061 _143062) (Q : type56 _143061 _143062) : (term218 _143061 _143062 P Q) = (term219 _143061 _143062 P Q).
Proof. exact (@lem8056388 (type24 _143061 _143062) P Q). Qed.
Lemma lem8056390 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term220 _143061 _143062 _143063 f x t y) = (term221 _143061 _143062 _143063 f x t y).
Proof. exact (@lem8056389 _143061 _143062 (term172 _143061 _143062 _143063 f x t y) (term213 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056391 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term222 _143061 _143062 _143063 f x t y s) = (term170 _143061 _143062 _143063 f s x t y).
Proof. exact (eq_refl (term222 _143061 _143062 _143063 f x t y s)). Qed.
Lemma lem8056392 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term223 _143061 _143062 _143063 f x t y) = (term172 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056391 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056393 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056394 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term224 _143061 _143062 _143063 f x t y) = (term173 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056393 _143061 _143062) (@lem8056392 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056396 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term225 _143061 _143062 _143063 f x t y) = (term174 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056395) (@lem8056394 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056397 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term226 _143061 _143062 _143063 f x t y s) = (term211 _143061 _143062 _143063 s f x t y).
Proof. exact (eq_refl (term226 _143061 _143062 _143063 f x t y s)). Qed.
Lemma lem8056398 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term227 _143061 _143062 _143063 f x t y) = (term213 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056397 _143061 _143062 _143063 s f x t y)). Qed.
Lemma lem8056399 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056400 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term228 _143061 _143062 _143063 f x t y) = (term214 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056399 _143061 _143062) (@lem8056398 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056401 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term220 _143061 _143062 _143063 f x t y) = (term215 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056396 _143061 _143062 _143063 f x t y) (@lem8056400 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8056403 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term229 _143061 _143062 _143063 f x t y) = (term230 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056402) (@lem8056401 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056404 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term222 _143061 _143062 _143063 f x t y s) = (term170 _143061 _143062 _143063 f s x t y).
Proof. exact (eq_refl (term222 _143061 _143062 _143063 f x t y s)). Qed.
Lemma lem8056405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056406 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term231 _143061 _143062 _143063 f x t y s) = (term232 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056405) (@lem8056404 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056407 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term226 _143061 _143062 _143063 f x t y s) = (term211 _143061 _143062 _143063 s f x t y).
Proof. exact (eq_refl (term226 _143061 _143062 _143063 f x t y s)). Qed.
Lemma lem8056408 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term233 _143061 _143062 _143063 f x t y s) = (term234 _143061 _143062 _143063 s f x t y).
Proof. exact (MK_COMB (@lem8056406 _143061 _143062 _143063 f s x t y) (@lem8056407 _143061 _143062 _143063 s f x t y)). Qed.
Lemma lem8056409 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term235 _143061 _143062 _143063 f x t y) = (term236 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056408 _143061 _143062 _143063 s f x t y)). Qed.
Lemma lem8056410 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056411 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term221 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056410 _143061 _143062) (@lem8056409 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056412 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term220 _143061 _143062 _143063 f x t y) = (term221 _143061 _143062 _143063 f x t y)) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)).
Proof. exact (MK_COMB (@lem8056403 _143061 _143062 _143063 f x t y) (@lem8056411 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056413 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y).
Proof. exact (EQ_MP (@lem8056412 _143061 _143062 _143063 f x t y) (@lem8056390 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056416 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term238 _143061 _143062 _143063 f x t y) = (term238 _143061 _143062 _143063 f x t y).
Proof. exact (eq_refl (term238 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056417 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term238 _143061 _143062 _143063 f x t y) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)).
Proof. exact (eq_refl (term238 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056418 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term239 _143061 _143062 _143063 f x t y) = (term239 _143061 _143062 _143063 f x t y).
Proof. exact (eq_refl (term239 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056419 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term238 _143061 _143062 _143063 f x t y) = (term238 _143061 _143062 _143063 f x t y)) = ((term238 _143061 _143062 _143063 f x t y) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y))).
Proof. exact (MK_COMB (@lem8056418 _143061 _143062 _143063 f x t y) (@lem8056417 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056420 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term238 _143061 _143062 _143063 f x t y) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)).
Proof. exact (eq_refl (term238 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8056422 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term239 _143061 _143062 _143063 f x t y) = (term240 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056421) (@lem8056420 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056423 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)).
Proof. exact (eq_refl ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y))). Qed.
Lemma lem8056424 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term238 _143061 _143062 _143063 f x t y) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y))) = (((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y))).
Proof. exact (MK_COMB (@lem8056422 _143061 _143062 _143063 f x t y) (@lem8056423 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056425 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term238 _143061 _143062 _143063 f x t y) = (term238 _143061 _143062 _143063 f x t y)) = (((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y))).
Proof. exact (TRANS (@lem8056419 _143061 _143062 _143063 f x t y) (@lem8056424 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056426 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)) = ((term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y)).
Proof. exact (EQ_MP (@lem8056425 _143061 _143062 _143063 f x t y) (@lem8056416 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056427 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term215 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y).
Proof. exact (EQ_MP (@lem8056426 _143061 _143062 _143063 f x t y) (@lem8056413 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056429 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term157 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y).
Proof. exact (TRANS (@lem8056386 _143061 _143062 _143063 f x t y) (@lem8056427 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056430 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term100 _143061 _143062 _143063 f x t y) = (term237 _143061 _143062 _143063 f x t y).
Proof. exact (TRANS (@lem8056157 _143061 _143062 _143063 f x t y) (@lem8056429 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056431 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term100 _143061 _143062 _143063 f x t y) : term237 _143061 _143062 _143063 f x t y.
Proof. exact (EQ_MP (@lem8056430 _143061 _143062 _143063 f x t y) (@lem8056050 _143061 _143062 _143063 f x t y h1)). Qed.
Lemma lem8056432 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term234 _143061 _143062 _143063 s f x t y) : term234 _143061 _143062 _143063 s f x t y.
Proof. exact (h1). Qed.
Lemma lem8056433 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x' : type24 _143061 _143062) (h1 : f x') : f x'.
Proof. exact (h1). Qed.
Lemma lem8056438 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056439 {_143061 _143063 : Type'} (f : type24 _143061 _143063) (x : cart _143061 _143063) : (f x) = (@I ((cart _143061 _143063) -> Prop) f x).
Proof. exact (@lem8056438 (cart _143061 _143063) Prop f x). Qed.
Lemma lem8056441 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (t y) = (@I ((cart _143061 _143063) -> Prop) t y).
Proof. exact (@lem8056439 _143061 _143063 t y). Qed.
Lemma lem8056446 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056447 {_143061 _143062 : Type'} (f : type24 _143061 _143062) (x : cart _143061 _143062) : (f x) = (@I ((cart _143061 _143062) -> Prop) f x).
Proof. exact (@lem8056446 (cart _143061 _143062) Prop f x). Qed.
Lemma lem8056449 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (s x) = (@I ((cart _143061 _143062) -> Prop) s x).
Proof. exact (@lem8056447 _143061 _143062 s x). Qed.
Lemma lem8056450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056451 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term66 _143061 _143062 s x) = (term241 _143061 _143062 s x).
Proof. exact (MK_COMB (@lem8056450) (@lem8056449 _143061 _143062 s x)). Qed.
Lemma lem8056452 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term68 _143061 _143062 _143063 s x t y) = (term242 _143061 _143062 _143063 s x t y).
Proof. exact (MK_COMB (@lem8056451 _143061 _143062 s x) (@lem8056441 _143061 _143063 t y)). Qed.
Lemma lem8056453 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056459 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (f x) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f x).
Proof. exact (@lem8056458 (type24 _143061 _143062) Prop f x). Qed.
Lemma lem8056461 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (f s) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f s).
Proof. exact (@lem8056459 _143061 _143062 f s). Qed.
Lemma lem8056462 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term10 _143061 _143062 f s) = (term243 _143061 _143062 f s).
Proof. exact (MK_COMB (@lem8056453) (@lem8056461 _143061 _143062 f s)). Qed.
Lemma lem8056463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056464 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term244 _143061 _143062 f s) = (term245 _143061 _143062 f s).
Proof. exact (MK_COMB (@lem8056463) (@lem8056462 _143061 _143062 f s)). Qed.
Lemma lem8056465 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term136 _143061 _143062 _143063 f s x t y) = (term246 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056464 _143061 _143062 f s) (@lem8056452 _143061 _143062 _143063 s x t y)). Qed.
Lemma lem8056466 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term144 _143061 _143062 _143063 f x t y) = (term247 _143061 _143062 _143063 f x t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056465 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056467 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056468 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term145 _143061 _143062 _143063 f x t y) = (term248 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056467 _143061 _143062) (@lem8056466 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056474 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056475 {_143061 _143063 : Type'} (f : type24 _143061 _143063) (x : cart _143061 _143063) : (f x) = (@I ((cart _143061 _143063) -> Prop) f x).
Proof. exact (@lem8056474 (cart _143061 _143063) Prop f x). Qed.
Lemma lem8056477 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (t y) = (@I ((cart _143061 _143063) -> Prop) t y).
Proof. exact (@lem8056475 _143061 _143063 t y). Qed.
Lemma lem8056478 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term122 _143061 _143063 t y) = (term249 _143061 _143063 t y).
Proof. exact (MK_COMB (@lem8056469) (@lem8056477 _143061 _143063 t y)). Qed.
Lemma lem8056479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056485 {_143061 _143062 : Type'} (f : type24 _143061 _143062) (x : cart _143061 _143062) : (f x) = (@I ((cart _143061 _143062) -> Prop) f x).
Proof. exact (@lem8056484 (cart _143061 _143062) Prop f x). Qed.
Lemma lem8056487 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (s x) = (@I ((cart _143061 _143062) -> Prop) s x).
Proof. exact (@lem8056485 _143061 _143062 s x). Qed.
Lemma lem8056488 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term122 _143061 _143062 s x) = (term249 _143061 _143062 s x).
Proof. exact (MK_COMB (@lem8056479) (@lem8056487 _143061 _143062 s x)). Qed.
Lemma lem8056493 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056494 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (f x) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f x).
Proof. exact (@lem8056493 (type24 _143061 _143062) Prop f x). Qed.
Lemma lem8056496 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (f s) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f s).
Proof. exact (@lem8056494 _143061 _143062 f s). Qed.
Lemma lem8056497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056498 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term132 _143061 _143062 f s) = (term250 _143061 _143062 f s).
Proof. exact (MK_COMB (@lem8056497) (@lem8056496 _143061 _143062 f s)). Qed.
Lemma lem8056499 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term111 _143061 _143062 f s x) = (term251 _143061 _143062 f s x).
Proof. exact (MK_COMB (@lem8056498 _143061 _143062 f s) (@lem8056488 _143061 _143062 s x)). Qed.
Lemma lem8056500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056501 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term188 _143061 _143062 f s x) = (term252 _143061 _143062 f s x).
Proof. exact (MK_COMB (@lem8056500) (@lem8056499 _143061 _143062 f s x)). Qed.
Lemma lem8056502 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term190 _143061 _143062 _143063 f s x t y) = (term253 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056501 _143061 _143062 f s x) (@lem8056478 _143061 _143063 t y)). Qed.
Lemma lem8056503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056504 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term209 _143061 _143062 _143063 f s x t y) = (term254 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056503) (@lem8056502 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056505 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term211 _143061 _143062 _143063 s f x t y) = (term255 _143061 _143062 _143063 s f x t y).
Proof. exact (MK_COMB (@lem8056504 _143061 _143062 _143063 f s x t y) (@lem8056468 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056511 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056512 {_143061 _143063 : Type'} (f : type24 _143061 _143063) (x : cart _143061 _143063) : (f x) = (@I ((cart _143061 _143063) -> Prop) f x).
Proof. exact (@lem8056511 (cart _143061 _143063) Prop f x). Qed.
Lemma lem8056514 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (t y) = (@I ((cart _143061 _143063) -> Prop) t y).
Proof. exact (@lem8056512 _143061 _143063 t y). Qed.
Lemma lem8056515 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term122 _143061 _143063 t y) = (term249 _143061 _143063 t y).
Proof. exact (MK_COMB (@lem8056506) (@lem8056514 _143061 _143063 t y)). Qed.
Lemma lem8056516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056521 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056522 {_143061 _143062 : Type'} (f : type24 _143061 _143062) (x : cart _143061 _143062) : (f x) = (@I ((cart _143061 _143062) -> Prop) f x).
Proof. exact (@lem8056521 (cart _143061 _143062) Prop f x). Qed.
Lemma lem8056524 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (s x) = (@I ((cart _143061 _143062) -> Prop) s x).
Proof. exact (@lem8056522 _143061 _143062 s x). Qed.
Lemma lem8056525 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term122 _143061 _143062 s x) = (term249 _143061 _143062 s x).
Proof. exact (MK_COMB (@lem8056516) (@lem8056524 _143061 _143062 s x)). Qed.
Lemma lem8056526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056527 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term256 _143061 _143062 s x) = (term257 _143061 _143062 s x).
Proof. exact (MK_COMB (@lem8056526) (@lem8056525 _143061 _143062 s x)). Qed.
Lemma lem8056528 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term131 _143061 _143062 _143063 s x t y) = (term258 _143061 _143062 _143063 s x t y).
Proof. exact (MK_COMB (@lem8056527 _143061 _143062 s x) (@lem8056515 _143061 _143063 t y)). Qed.
Lemma lem8056533 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056534 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (f x) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f x).
Proof. exact (@lem8056533 (type24 _143061 _143062) Prop f x). Qed.
Lemma lem8056536 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (f s) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f s).
Proof. exact (@lem8056534 _143061 _143062 f s). Qed.
Lemma lem8056537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056538 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term132 _143061 _143062 f s) = (term250 _143061 _143062 f s).
Proof. exact (MK_COMB (@lem8056537) (@lem8056536 _143061 _143062 f s)). Qed.
Lemma lem8056539 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term134 _143061 _143062 _143063 f s x t y) = (term259 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056538 _143061 _143062 f s) (@lem8056528 _143061 _143062 _143063 s x t y)). Qed.
Lemma lem8056544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056545 {_143061 _143063 : Type'} (f : type24 _143061 _143063) (x : cart _143061 _143063) : (f x) = (@I ((cart _143061 _143063) -> Prop) f x).
Proof. exact (@lem8056544 (cart _143061 _143063) Prop f x). Qed.
Lemma lem8056547 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (t y) = (@I ((cart _143061 _143063) -> Prop) t y).
Proof. exact (@lem8056545 _143061 _143063 t y). Qed.
Lemma lem8056552 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056553 {_143061 _143062 : Type'} (f : type24 _143061 _143062) (x : cart _143061 _143062) : (f x) = (@I ((cart _143061 _143062) -> Prop) f x).
Proof. exact (@lem8056552 (cart _143061 _143062) Prop f x). Qed.
Lemma lem8056555 {_143061 _143062 : Type'} (t : type24 _143061 _143062) (x : cart _143061 _143062) : (t x) = (@I ((cart _143061 _143062) -> Prop) t x).
Proof. exact (@lem8056553 _143061 _143062 t x). Qed.
Lemma lem8056556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8056561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056562 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (f x) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f x).
Proof. exact (@lem8056561 (type24 _143061 _143062) Prop f x). Qed.
Lemma lem8056564 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) : (f t) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f t).
Proof. exact (@lem8056562 _143061 _143062 f t). Qed.
Lemma lem8056565 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) : (term10 _143061 _143062 f t) = (term243 _143061 _143062 f t).
Proof. exact (MK_COMB (@lem8056556) (@lem8056564 _143061 _143062 f t)). Qed.
Lemma lem8056566 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056567 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) : (term244 _143061 _143062 f t) = (term245 _143061 _143062 f t).
Proof. exact (MK_COMB (@lem8056566) (@lem8056565 _143061 _143062 f t)). Qed.
Lemma lem8056568 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term112 _143061 _143062 f t x) = (term260 _143061 _143062 f t x).
Proof. exact (MK_COMB (@lem8056567 _143061 _143062 f t) (@lem8056555 _143061 _143062 t x)). Qed.
Lemma lem8056569 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term120 _143061 _143062 f x) = (term261 _143061 _143062 f x).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8056568 _143061 _143062 f t x)). Qed.
Lemma lem8056570 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056571 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term121 _143061 _143062 f x) = (term262 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056570 _143061 _143062) (@lem8056569 _143061 _143062 f x)). Qed.
Lemma lem8056572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056573 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term128 _143061 _143062 f x) = (term263 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056572) (@lem8056571 _143061 _143062 f x)). Qed.
Lemma lem8056574 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term129 _143061 _143062 _143063 f x t y) = (term264 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056573 _143061 _143062 f x) (@lem8056547 _143061 _143063 t y)). Qed.
Lemma lem8056575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8056576 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term151 _143061 _143062 _143063 f x t y) = (term265 _143061 _143062 _143063 f x t y).
Proof. exact (MK_COMB (@lem8056575) (@lem8056574 _143061 _143062 _143063 f x t y)). Qed.
Lemma lem8056577 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term170 _143061 _143062 _143063 f s x t y) = (term266 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056576 _143061 _143062 _143063 f x t y) (@lem8056539 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8056579 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term232 _143061 _143062 _143063 f s x t y) = (term267 _143061 _143062 _143063 f s x t y).
Proof. exact (MK_COMB (@lem8056578) (@lem8056577 _143061 _143062 _143063 f s x t y)). Qed.
Lemma lem8056580 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term234 _143061 _143062 _143063 s f x t y) = (term268 _143061 _143062 _143063 s f x t y).
Proof. exact (MK_COMB (@lem8056579 _143061 _143062 _143063 f s x t y) (@lem8056505 _143061 _143062 _143063 s f x t y)). Qed.
Lemma lem8056581 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term234 _143061 _143062 _143063 s f x t y) : term268 _143061 _143062 _143063 s f x t y.
Proof. exact (EQ_MP (@lem8056580 _143061 _143062 _143063 s f x t y) (@lem8056432 _143061 _143062 _143063 s f x t y h1)). Qed.
Lemma lem8056586 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8056587 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : type24 _143061 _143062) : (f x) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f x).
Proof. exact (@lem8056586 (type24 _143061 _143062) Prop f x). Qed.
Lemma lem8056589 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x' : type24 _143061 _143062) : (f x') = (@I (((cart _143061 _143062) -> Prop) -> Prop) f x').
Proof. exact (@lem8056587 _143061 _143062 f x'). Qed.
Lemma lem8056591 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term266 _143061 _143062 _143063 f s x t y.
Proof. exact (h1). Qed.
Lemma lem8056592 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term255 _143061 _143062 _143063 s f x t y.
Proof. exact (h1). Qed.
Lemma lem8056593 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term259 _143061 _143062 _143063 f s x t y.
Proof. exact (proj2 (@lem8056591 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056594 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term264 _143061 _143062 _143063 f x t y.
Proof. exact (proj1 (@lem8056591 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056595 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term258 _143061 _143062 _143063 s x t y.
Proof. exact (proj2 (@lem8056593 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056598 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term262 _143061 _143062 f x.
Proof. exact (proj1 (@lem8056594 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056601 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term248 _143061 _143062 _143063 f x t y.
Proof. exact (proj2 (@lem8056592 _143061 _143062 _143063 s f x t y h1)). Qed.
Lemma lem8056602 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term253 _143061 _143062 _143063 f s x t y.
Proof. exact (proj1 (@lem8056592 _143061 _143062 _143063 s f x t y h1)). Qed.
Lemma lem8056603 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term251 _143061 _143062 f s x) : term251 _143061 _143062 f s x.
Proof. exact (h1). Qed.
Lemma lem8056622 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143062) (x : cart _143061 _143062) : (term260 _143061 _143062 f t x) = (term260 _143061 _143062 f t x).
Proof. exact (eq_refl (term260 _143061 _143062 f t x)). Qed.
Lemma lem8056623 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term261 _143061 _143062 f x) = (term261 _143061 _143062 f x).
Proof. exact (fun_ext (fun t : type24 _143061 _143062 => @lem8056622 _143061 _143062 f t x)). Qed.
Lemma lem8056624 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056626 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) : (term262 _143061 _143062 f x) = (term262 _143061 _143062 f x).
Proof. exact (MK_COMB (@lem8056624 _143061 _143062) (@lem8056623 _143061 _143062 f x)). Qed.
Lemma lem8056627 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term262 _143061 _143062 f x.
Proof. exact (EQ_MP (@lem8056626 _143061 _143062 f x) (@lem8056598 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056635 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term249 _143061 _143062 s x) : term249 _143061 _143062 s x.
Proof. exact (h1). Qed.
Lemma lem8056664 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) : term249 _143061 _143063 t y.
Proof. exact (h1). Qed.
Lemma lem8056686 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term246 _143061 _143062 _143063 f s x t y) = (term269 _143061 _143062 _143063 x f s t y).
Proof. exact (@lem19490 (@I ((cart _143061 _143062) -> Prop) s x) (term243 _143061 _143062 f s) (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8056687 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term247 _143061 _143062 _143063 f x t y) = (term270 _143061 _143062 _143063 x f t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056686 _143061 _143062 _143063 x f s t y)). Qed.
Lemma lem8056688 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056690 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term248 _143061 _143062 _143063 f x t y) = (term271 _143061 _143062 _143063 x f t y).
Proof. exact (MK_COMB (@lem8056688 _143061 _143062) (@lem8056687 _143061 _143062 _143063 x f t y)). Qed.
Lemma lem8056691 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term271 _143061 _143062 _143063 x f t y.
Proof. exact (EQ_MP (@lem8056690 _143061 _143062 _143063 x f t y) (@lem8056601 _143061 _143062 _143063 s f x t y h1)). Qed.
Lemma lem8056721 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term246 _143061 _143062 _143063 f s x t y) = (term269 _143061 _143062 _143063 x f s t y).
Proof. exact (@lem19490 (@I ((cart _143061 _143062) -> Prop) s x) (term243 _143061 _143062 f s) (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8056722 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term247 _143061 _143062 _143063 f x t y) = (term270 _143061 _143062 _143063 x f t y).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8056721 _143061 _143062 _143063 x f s t y)). Qed.
Lemma lem8056723 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8056725 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term248 _143061 _143062 _143063 f x t y) = (term271 _143061 _143062 _143063 x f t y).
Proof. exact (MK_COMB (@lem8056723 _143061 _143062) (@lem8056722 _143061 _143062 _143063 x f t y)). Qed.
Lemma lem8056726 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term271 _143061 _143062 _143063 x f t y.
Proof. exact (EQ_MP (@lem8056725 _143061 _143062 _143063 x f t y) (@lem8056601 _143061 _143062 _143063 s f x t y h1)). Qed.
Lemma lem8056730 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) : term249 _143061 _143063 t y.
Proof. exact (h1). Qed.
Lemma lem8056731 {_143061 _143062 _143063 : Type'} (_106215 : type24 _143061 _143062) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term272 _143061 _143062 f x _106215.
Proof. exact (@lem8056627 _143061 _143062 _143063 f s x t y h1 _106215). Qed.
Lemma lem8056732 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) (x : cart _143061 _143062) : (term272 _143061 _143062 f x _106215) = (term260 _143061 _143062 f _106215 x).
Proof. exact (eq_refl (term272 _143061 _143062 f x _106215)). Qed.
Lemma lem8056737 {_143061 _143062 _143063 : Type'} (_106217 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term273 _143061 _143062 _143063 x f t y _106217.
Proof. exact (@lem8056691 _143061 _143062 _143063 s f x t y h1 _106217). Qed.
Lemma lem8056738 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term273 _143061 _143062 _143063 x f t y _106217) = (term269 _143061 _143062 _143063 x f _106217 t y).
Proof. exact (eq_refl (term273 _143061 _143062 _143063 x f t y _106217)). Qed.
Lemma lem8056739 {_143061 _143062 _143063 : Type'} (_106217 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term269 _143061 _143062 _143063 x f _106217 t y.
Proof. exact (EQ_MP (@lem8056738 _143061 _143062 _143063 x f _106217 t y) (@lem8056737 _143061 _143062 _143063 _106217 s f x t y h1)). Qed.
Lemma lem8056740 {_143061 _143062 _143063 : Type'} (_106218 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term273 _143061 _143062 _143063 x f t y _106218.
Proof. exact (@lem8056726 _143061 _143062 _143063 s f x t y h1 _106218). Qed.
Lemma lem8056741 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term273 _143061 _143062 _143063 x f t y _106218) = (term269 _143061 _143062 _143063 x f _106218 t y).
Proof. exact (eq_refl (term273 _143061 _143062 _143063 x f t y _106218)). Qed.
Lemma lem8056742 {_143061 _143062 _143063 : Type'} (_106218 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term269 _143061 _143062 _143063 x f _106218 t y.
Proof. exact (EQ_MP (@lem8056741 _143061 _143062 _143063 x f _106218 t y) (@lem8056740 _143061 _143062 _143063 _106218 s f x t y h1)). Qed.
Lemma lem8056756 {_143061 _143062 _143063 : Type'} (_106215 : type24 _143061 _143062) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term260 _143061 _143062 f _106215 x.
Proof. exact (EQ_MP (@lem8056732 _143061 _143062 f _106215 x) (@lem8056731 _143061 _143062 _143063 _106215 f s x t y h1)). Qed.
Lemma lem8056760 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term249 _143061 _143062 s x) : term249 _143061 _143062 s x.
Proof. exact (h1). Qed.
Lemma lem8056774 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) : term249 _143061 _143063 t y.
Proof. exact (h1). Qed.
Lemma lem8056780 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term251 _143061 _143062 f s x) : term249 _143061 _143062 s x.
Proof. exact (proj2 (@lem8056603 _143061 _143062 f s x h1)). Qed.
Lemma lem8056786 {_143061 _143062 _143063 : Type'} (_106217 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term260 _143061 _143062 f _106217 x.
Proof. exact (proj1 (@lem8056739 _143061 _143062 _143063 _106217 s f x t y h1)). Qed.
Lemma lem8056796 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) : term249 _143061 _143063 t y.
Proof. exact (h1). Qed.
Lemma lem8056808 {_143061 _143062 _143063 : Type'} (_106218 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term274 _143061 _143062 _143063 f _106218 t y.
Proof. exact (proj2 (@lem8056742 _143061 _143062 _143063 _106218 s f x t y h1)). Qed.
Lemma lem8056810 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : @I (((cart _143061 _143062) -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem8056593 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056811 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term275 _143061 _143062 f s.
Proof. exact (fun h0 : term243 _143061 _143062 f s => @lem8056810 _143061 _143062 _143063 f s x t y h1). Qed.
Lemma lem8056813 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056814 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term275 _143061 _143062 f s) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f s).
Proof. exact (@lem8056813 (@I (((cart _143061 _143062) -> Prop) -> Prop) f s)). Qed.
Lemma lem8056815 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : @I (((cart _143061 _143062) -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem8056814 _143061 _143062 f s) (@lem8056811 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056821 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8056822 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : (term260 _143061 _143062 f _106215 x) = (term277 _143061 _143062 x f _106215).
Proof. exact (@lem8056821 (@I ((cart _143061 _143062) -> Prop) _106215 x) (term243 _143061 _143062 f _106215)). Qed.
Lemma lem8056828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8056829 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : (term278 _143061 _143062 f _106215 x) = (term279 _143061 _143062 x f _106215).
Proof. exact (MK_COMB (@lem8056828) (@lem8056822 _143061 _143062 x f _106215)). Qed.
Lemma lem8056835 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : (term277 _143061 _143062 x f _106215) = (term277 _143061 _143062 x f _106215).
Proof. exact (eq_refl (term277 _143061 _143062 x f _106215)). Qed.
Lemma lem8056836 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : ((term260 _143061 _143062 f _106215 x) = (term277 _143061 _143062 x f _106215)) = ((term277 _143061 _143062 x f _106215) = (term277 _143061 _143062 x f _106215)).
Proof. exact (MK_COMB (@lem8056829 _143061 _143062 x f _106215) (@lem8056835 _143061 _143062 x f _106215)). Qed.
Lemma lem8056838 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8056839 (x : Prop) : (x = x) = True.
Proof. exact (@lem8056838 Prop x). Qed.
Lemma lem8056840 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : ((term277 _143061 _143062 x f _106215) = (term277 _143061 _143062 x f _106215)) = True.
Proof. exact (@lem8056839 (term277 _143061 _143062 x f _106215)). Qed.
Lemma lem8056841 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : ((term260 _143061 _143062 f _106215 x) = (term277 _143061 _143062 x f _106215)) = True.
Proof. exact (TRANS (@lem8056836 _143061 _143062 x f _106215) (@lem8056840 _143061 _143062 x f _106215)). Qed.
Lemma lem8056842 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : True = ((term260 _143061 _143062 f _106215 x) = (term277 _143061 _143062 x f _106215)).
Proof. exact (SYM (@lem8056841 _143061 _143062 x f _106215)). Qed.
Lemma lem8056843 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : (term260 _143061 _143062 f _106215 x) = (term277 _143061 _143062 x f _106215).
Proof. exact (EQ_MP (@lem8056842 _143061 _143062 x f _106215) (@lem0)). Qed.
Lemma lem8056844 {_143061 _143062 _143063 : Type'} (_106215 : type24 _143061 _143062) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term277 _143061 _143062 x f _106215.
Proof. exact (EQ_MP (@lem8056843 _143061 _143062 x f _106215) (@lem8056756 _143061 _143062 _143063 _106215 f s x t y h1)). Qed.
Lemma lem8056846 (b : Prop) (a : Prop) : (a \/ b) = (term280 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8056847 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) (x : cart _143061 _143062) : (term277 _143061 _143062 x f _106215) = (term281 _143061 _143062 f _106215 x).
Proof. exact (@lem8056846 (term243 _143061 _143062 f _106215) (@I ((cart _143061 _143062) -> Prop) _106215 x)). Qed.
Lemma lem8056849 (a : Prop) : (term90 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8056850 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : (term282 _143061 _143062 f _106215) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f _106215).
Proof. exact (@lem8056849 (@I (((cart _143061 _143062) -> Prop) -> Prop) f _106215)). Qed.
Lemma lem8056851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8056852 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) : (term283 _143061 _143062 f _106215) = (term284 _143061 _143062 f _106215).
Proof. exact (MK_COMB (@lem8056851) (@lem8056850 _143061 _143062 f _106215)). Qed.
Lemma lem8056853 {_143061 _143062 : Type'} (_106215 : type24 _143061 _143062) (x : cart _143061 _143062) : (@I ((cart _143061 _143062) -> Prop) _106215 x) = (@I ((cart _143061 _143062) -> Prop) _106215 x).
Proof. exact (eq_refl (@I ((cart _143061 _143062) -> Prop) _106215 x)). Qed.
Lemma lem8056854 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) (x : cart _143061 _143062) : (term281 _143061 _143062 f _106215 x) = (term285 _143061 _143062 f _106215 x).
Proof. exact (MK_COMB (@lem8056852 _143061 _143062 f _106215) (@lem8056853 _143061 _143062 _106215 x)). Qed.
Lemma lem8056855 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106215 : type24 _143061 _143062) (x : cart _143061 _143062) : (term277 _143061 _143062 x f _106215) = (term285 _143061 _143062 f _106215 x).
Proof. exact (TRANS (@lem8056847 _143061 _143062 f _106215 x) (@lem8056854 _143061 _143062 f _106215 x)). Qed.
Lemma lem8056858 {_143061 _143062 _143063 : Type'} (_106215 : type24 _143061 _143062) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term285 _143061 _143062 f _106215 x.
Proof. exact (EQ_MP (@lem8056855 _143061 _143062 f _106215 x) (@lem8056844 _143061 _143062 _143063 _106215 f s x t y h1)). Qed.
Lemma lem8056859 {_143061 _143062 _143063 : Type'} (_106215 : type24 _143061 _143062) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term285 _143061 _143062 f _106215 x.
Proof. exact (@lem8056858 _143061 _143062 _143063 _106215 f s x t y h1). Qed.
Lemma lem8056860 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term285 _143061 _143062 f s x.
Proof. exact (@lem8056859 _143061 _143062 _143063 s f s x t y h1). Qed.
Lemma lem8056863 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : @I ((cart _143061 _143062) -> Prop) s x.
Proof. exact (@lem8056860 _143061 _143062 _143063 f s x t y h1 (@lem8056815 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056864 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term286 _143061 _143062 s x.
Proof. exact (fun h0 : term249 _143061 _143062 s x => @lem8056863 _143061 _143062 _143063 f s x t y h1). Qed.
Lemma lem8056866 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056867 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term286 _143061 _143062 s x) = (@I ((cart _143061 _143062) -> Prop) s x).
Proof. exact (@lem8056866 (@I ((cart _143061 _143062) -> Prop) s x)). Qed.
Lemma lem8056868 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : @I ((cart _143061 _143062) -> Prop) s x.
Proof. exact (EQ_MP (@lem8056867 _143061 _143062 s x) (@lem8056864 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056871 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8056873 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term249 _143061 _143062 s x) = (term287 _143061 _143062 s x).
Proof. exact (@lem8056871 (@I ((cart _143061 _143062) -> Prop) s x)). Qed.
Lemma lem8056876 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term249 _143061 _143062 s x) : term287 _143061 _143062 s x.
Proof. exact (EQ_MP (@lem8056873 _143061 _143062 s x) (@lem8056760 _143061 _143062 s x h1)). Qed.
Lemma lem8056879 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (@lem8056876 _143061 _143062 s x h1 (@lem8056868 _143061 _143062 _143063 f s x t y h2)). Qed.
Lemma lem8056880 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : term288.
Proof. exact (fun h0 : ~ False => @lem8056879 _143061 _143062 _143063 f s x t y h1 h2). Qed.
Lemma lem8056882 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056883 : term288 = False.
Proof. exact (@lem8056882 False). Qed.
Lemma lem8056884 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8056883) (@lem8056880 _143061 _143062 _143063 f s x t y h1 h2)). Qed.
Lemma lem8056886 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : @I ((cart _143061 _143063) -> Prop) t y.
Proof. exact (proj2 (@lem8056594 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056887 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : term286 _143061 _143063 t y.
Proof. exact (fun h0 : term249 _143061 _143063 t y => @lem8056886 _143061 _143062 _143063 f s x t y h1). Qed.
Lemma lem8056889 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056890 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term286 _143061 _143063 t y) = (@I ((cart _143061 _143063) -> Prop) t y).
Proof. exact (@lem8056889 (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8056891 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : @I ((cart _143061 _143063) -> Prop) t y.
Proof. exact (EQ_MP (@lem8056890 _143061 _143063 t y) (@lem8056887 _143061 _143062 _143063 f s x t y h1)). Qed.
Lemma lem8056894 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8056896 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term249 _143061 _143063 t y) = (term287 _143061 _143063 t y).
Proof. exact (@lem8056894 (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8056899 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) : term287 _143061 _143063 t y.
Proof. exact (EQ_MP (@lem8056896 _143061 _143063 t y) (@lem8056774 _143061 _143063 t y h1)). Qed.
Lemma lem8056902 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (@lem8056899 _143061 _143063 t y h1 (@lem8056891 _143061 _143062 _143063 f s x t y h2)). Qed.
Lemma lem8056903 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : term288.
Proof. exact (fun h0 : ~ False => @lem8056902 _143061 _143062 _143063 f s x t y h1 h2). Qed.
Lemma lem8056905 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056906 : term288 = False.
Proof. exact (@lem8056905 False). Qed.
Lemma lem8056907 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8056906) (@lem8056903 _143061 _143062 _143063 f s x t y h1 h2)). Qed.
Lemma lem8056909 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term251 _143061 _143062 f s x) : @I (((cart _143061 _143062) -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem8056603 _143061 _143062 f s x h1)). Qed.
Lemma lem8056910 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term251 _143061 _143062 f s x) : term275 _143061 _143062 f s.
Proof. exact (fun h0 : term243 _143061 _143062 f s => @lem8056909 _143061 _143062 f s x h1). Qed.
Lemma lem8056912 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056913 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) : (term275 _143061 _143062 f s) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f s).
Proof. exact (@lem8056912 (@I (((cart _143061 _143062) -> Prop) -> Prop) f s)). Qed.
Lemma lem8056914 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term251 _143061 _143062 f s x) : @I (((cart _143061 _143062) -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem8056913 _143061 _143062 f s) (@lem8056910 _143061 _143062 f s x h1)). Qed.
Lemma lem8056920 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8056921 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : (term260 _143061 _143062 f _106217 x) = (term277 _143061 _143062 x f _106217).
Proof. exact (@lem8056920 (@I ((cart _143061 _143062) -> Prop) _106217 x) (term243 _143061 _143062 f _106217)). Qed.
Lemma lem8056927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8056928 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : (term278 _143061 _143062 f _106217 x) = (term279 _143061 _143062 x f _106217).
Proof. exact (MK_COMB (@lem8056927) (@lem8056921 _143061 _143062 x f _106217)). Qed.
Lemma lem8056934 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : (term277 _143061 _143062 x f _106217) = (term277 _143061 _143062 x f _106217).
Proof. exact (eq_refl (term277 _143061 _143062 x f _106217)). Qed.
Lemma lem8056935 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : ((term260 _143061 _143062 f _106217 x) = (term277 _143061 _143062 x f _106217)) = ((term277 _143061 _143062 x f _106217) = (term277 _143061 _143062 x f _106217)).
Proof. exact (MK_COMB (@lem8056928 _143061 _143062 x f _106217) (@lem8056934 _143061 _143062 x f _106217)). Qed.
Lemma lem8056937 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8056938 (x : Prop) : (x = x) = True.
Proof. exact (@lem8056937 Prop x). Qed.
Lemma lem8056939 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : ((term277 _143061 _143062 x f _106217) = (term277 _143061 _143062 x f _106217)) = True.
Proof. exact (@lem8056938 (term277 _143061 _143062 x f _106217)). Qed.
Lemma lem8056940 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : ((term260 _143061 _143062 f _106217 x) = (term277 _143061 _143062 x f _106217)) = True.
Proof. exact (TRANS (@lem8056935 _143061 _143062 x f _106217) (@lem8056939 _143061 _143062 x f _106217)). Qed.
Lemma lem8056941 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : True = ((term260 _143061 _143062 f _106217 x) = (term277 _143061 _143062 x f _106217)).
Proof. exact (SYM (@lem8056940 _143061 _143062 x f _106217)). Qed.
Lemma lem8056942 {_143061 _143062 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : (term260 _143061 _143062 f _106217 x) = (term277 _143061 _143062 x f _106217).
Proof. exact (EQ_MP (@lem8056941 _143061 _143062 x f _106217) (@lem0)). Qed.
Lemma lem8056943 {_143061 _143062 _143063 : Type'} (_106217 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term277 _143061 _143062 x f _106217.
Proof. exact (EQ_MP (@lem8056942 _143061 _143062 x f _106217) (@lem8056786 _143061 _143062 _143063 _106217 s f x t y h1)). Qed.
Lemma lem8056945 (b : Prop) (a : Prop) : (a \/ b) = (term280 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8056946 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) (x : cart _143061 _143062) : (term277 _143061 _143062 x f _106217) = (term281 _143061 _143062 f _106217 x).
Proof. exact (@lem8056945 (term243 _143061 _143062 f _106217) (@I ((cart _143061 _143062) -> Prop) _106217 x)). Qed.
Lemma lem8056948 (a : Prop) : (term90 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8056949 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : (term282 _143061 _143062 f _106217) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f _106217).
Proof. exact (@lem8056948 (@I (((cart _143061 _143062) -> Prop) -> Prop) f _106217)). Qed.
Lemma lem8056950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8056951 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) : (term283 _143061 _143062 f _106217) = (term284 _143061 _143062 f _106217).
Proof. exact (MK_COMB (@lem8056950) (@lem8056949 _143061 _143062 f _106217)). Qed.
Lemma lem8056952 {_143061 _143062 : Type'} (_106217 : type24 _143061 _143062) (x : cart _143061 _143062) : (@I ((cart _143061 _143062) -> Prop) _106217 x) = (@I ((cart _143061 _143062) -> Prop) _106217 x).
Proof. exact (eq_refl (@I ((cart _143061 _143062) -> Prop) _106217 x)). Qed.
Lemma lem8056953 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) (x : cart _143061 _143062) : (term281 _143061 _143062 f _106217 x) = (term285 _143061 _143062 f _106217 x).
Proof. exact (MK_COMB (@lem8056951 _143061 _143062 f _106217) (@lem8056952 _143061 _143062 _106217 x)). Qed.
Lemma lem8056954 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106217 : type24 _143061 _143062) (x : cart _143061 _143062) : (term277 _143061 _143062 x f _106217) = (term285 _143061 _143062 f _106217 x).
Proof. exact (TRANS (@lem8056946 _143061 _143062 f _106217 x) (@lem8056953 _143061 _143062 f _106217 x)). Qed.
Lemma lem8056957 {_143061 _143062 _143063 : Type'} (_106217 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term285 _143061 _143062 f _106217 x.
Proof. exact (EQ_MP (@lem8056954 _143061 _143062 f _106217 x) (@lem8056943 _143061 _143062 _143063 _106217 s f x t y h1)). Qed.
Lemma lem8056958 {_143061 _143062 _143063 : Type'} (_106217 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term285 _143061 _143062 f _106217 x.
Proof. exact (@lem8056957 _143061 _143062 _143063 _106217 s f x t y h1). Qed.
Lemma lem8056959 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term285 _143061 _143062 f s x.
Proof. exact (@lem8056958 _143061 _143062 _143063 s s f x t y h1). Qed.
Lemma lem8056962 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term251 _143061 _143062 f s x) (h2 : term255 _143061 _143062 _143063 s f x t y) : @I ((cart _143061 _143062) -> Prop) s x.
Proof. exact (@lem8056959 _143061 _143062 _143063 s f x t y h2 (@lem8056914 _143061 _143062 f s x h1)). Qed.
Lemma lem8056963 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term251 _143061 _143062 f s x) (h2 : term255 _143061 _143062 _143063 s f x t y) : term286 _143061 _143062 s x.
Proof. exact (fun h0 : term249 _143061 _143062 s x => @lem8056962 _143061 _143062 _143063 s f x t y h1 h2). Qed.
Lemma lem8056965 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056966 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term286 _143061 _143062 s x) = (@I ((cart _143061 _143062) -> Prop) s x).
Proof. exact (@lem8056965 (@I ((cart _143061 _143062) -> Prop) s x)). Qed.
Lemma lem8056967 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term251 _143061 _143062 f s x) (h2 : term255 _143061 _143062 _143063 s f x t y) : @I ((cart _143061 _143062) -> Prop) s x.
Proof. exact (EQ_MP (@lem8056966 _143061 _143062 s x) (@lem8056963 _143061 _143062 _143063 s f x t y h1 h2)). Qed.
Lemma lem8056970 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8056972 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (x : cart _143061 _143062) : (term249 _143061 _143062 s x) = (term287 _143061 _143062 s x).
Proof. exact (@lem8056970 (@I ((cart _143061 _143062) -> Prop) s x)). Qed.
Lemma lem8056975 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (h1 : term251 _143061 _143062 f s x) : term287 _143061 _143062 s x.
Proof. exact (EQ_MP (@lem8056972 _143061 _143062 s x) (@lem8056780 _143061 _143062 f s x h1)). Qed.
Lemma lem8056978 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term251 _143061 _143062 f s x) (h2 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (@lem8056975 _143061 _143062 f s x h1 (@lem8056967 _143061 _143062 _143063 s f x t y h1 h2)). Qed.
Lemma lem8056979 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term251 _143061 _143062 f s x) (h2 : term255 _143061 _143062 _143063 s f x t y) : term288.
Proof. exact (fun h0 : ~ False => @lem8056978 _143061 _143062 _143063 s f x t y h1 h2). Qed.
Lemma lem8056981 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056982 : term288 = False.
Proof. exact (@lem8056981 False). Qed.
Lemma lem8056983 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term251 _143061 _143062 f s x) (h2 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (EQ_MP (@lem8056982) (@lem8056979 _143061 _143062 _143063 s f x t y h1 h2)). Qed.
Lemma lem8056985 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x' : type24 _143061 _143062) (h1 : f x') : @I (((cart _143061 _143062) -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem8056589 _143061 _143062 f x') (@lem8056433 _143061 _143062 f x' h1)). Qed.
Lemma lem8056986 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x' : type24 _143061 _143062) (h1 : f x') : term275 _143061 _143062 f x'.
Proof. exact (fun h0 : term243 _143061 _143062 f x' => @lem8056985 _143061 _143062 f x' h1). Qed.
Lemma lem8056988 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8056989 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x' : type24 _143061 _143062) : (term275 _143061 _143062 f x') = (@I (((cart _143061 _143062) -> Prop) -> Prop) f x').
Proof. exact (@lem8056988 (@I (((cart _143061 _143062) -> Prop) -> Prop) f x')). Qed.
Lemma lem8056990 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (x' : type24 _143061 _143062) (h1 : f x') : @I (((cart _143061 _143062) -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem8056989 _143061 _143062 f x') (@lem8056986 _143061 _143062 f x' h1)). Qed.
Lemma lem8056996 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8056997 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : (term274 _143061 _143062 _143063 f _106218 t y) = (term289 _143061 _143062 _143063 t y f _106218).
Proof. exact (@lem8056996 (@I ((cart _143061 _143063) -> Prop) t y) (term243 _143061 _143062 f _106218)). Qed.
Lemma lem8057003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8057004 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : (term290 _143061 _143062 _143063 f _106218 t y) = (term291 _143061 _143062 _143063 t y f _106218).
Proof. exact (MK_COMB (@lem8057003) (@lem8056997 _143061 _143062 _143063 t y f _106218)). Qed.
Lemma lem8057010 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : (term289 _143061 _143062 _143063 t y f _106218) = (term289 _143061 _143062 _143063 t y f _106218).
Proof. exact (eq_refl (term289 _143061 _143062 _143063 t y f _106218)). Qed.
Lemma lem8057011 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : ((term274 _143061 _143062 _143063 f _106218 t y) = (term289 _143061 _143062 _143063 t y f _106218)) = ((term289 _143061 _143062 _143063 t y f _106218) = (term289 _143061 _143062 _143063 t y f _106218)).
Proof. exact (MK_COMB (@lem8057004 _143061 _143062 _143063 t y f _106218) (@lem8057010 _143061 _143062 _143063 t y f _106218)). Qed.
Lemma lem8057013 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8057014 (x : Prop) : (x = x) = True.
Proof. exact (@lem8057013 Prop x). Qed.
Lemma lem8057015 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : ((term289 _143061 _143062 _143063 t y f _106218) = (term289 _143061 _143062 _143063 t y f _106218)) = True.
Proof. exact (@lem8057014 (term289 _143061 _143062 _143063 t y f _106218)). Qed.
Lemma lem8057016 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : ((term274 _143061 _143062 _143063 f _106218 t y) = (term289 _143061 _143062 _143063 t y f _106218)) = True.
Proof. exact (TRANS (@lem8057011 _143061 _143062 _143063 t y f _106218) (@lem8057015 _143061 _143062 _143063 t y f _106218)). Qed.
Lemma lem8057017 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : True = ((term274 _143061 _143062 _143063 f _106218 t y) = (term289 _143061 _143062 _143063 t y f _106218)).
Proof. exact (SYM (@lem8057016 _143061 _143062 _143063 t y f _106218)). Qed.
Lemma lem8057018 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : (term274 _143061 _143062 _143063 f _106218 t y) = (term289 _143061 _143062 _143063 t y f _106218).
Proof. exact (EQ_MP (@lem8057017 _143061 _143062 _143063 t y f _106218) (@lem0)). Qed.
Lemma lem8057019 {_143061 _143062 _143063 : Type'} (_106218 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term289 _143061 _143062 _143063 t y f _106218.
Proof. exact (EQ_MP (@lem8057018 _143061 _143062 _143063 t y f _106218) (@lem8056808 _143061 _143062 _143063 _106218 s f x t y h1)). Qed.
Lemma lem8057021 (b : Prop) (a : Prop) : (a \/ b) = (term280 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8057022 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term289 _143061 _143062 _143063 t y f _106218) = (term292 _143061 _143062 _143063 f _106218 t y).
Proof. exact (@lem8057021 (term243 _143061 _143062 f _106218) (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8057024 (a : Prop) : (term90 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8057025 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : (term282 _143061 _143062 f _106218) = (@I (((cart _143061 _143062) -> Prop) -> Prop) f _106218).
Proof. exact (@lem8057024 (@I (((cart _143061 _143062) -> Prop) -> Prop) f _106218)). Qed.
Lemma lem8057026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8057027 {_143061 _143062 : Type'} (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) : (term283 _143061 _143062 f _106218) = (term284 _143061 _143062 f _106218).
Proof. exact (MK_COMB (@lem8057026) (@lem8057025 _143061 _143062 f _106218)). Qed.
Lemma lem8057028 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (@I ((cart _143061 _143063) -> Prop) t y) = (@I ((cart _143061 _143063) -> Prop) t y).
Proof. exact (eq_refl (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8057029 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term292 _143061 _143062 _143063 f _106218 t y) = (term293 _143061 _143062 _143063 f _106218 t y).
Proof. exact (MK_COMB (@lem8057027 _143061 _143062 f _106218) (@lem8057028 _143061 _143063 t y)). Qed.
Lemma lem8057030 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (_106218 : type24 _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term289 _143061 _143062 _143063 t y f _106218) = (term293 _143061 _143062 _143063 f _106218 t y).
Proof. exact (TRANS (@lem8057022 _143061 _143062 _143063 f _106218 t y) (@lem8057029 _143061 _143062 _143063 f _106218 t y)). Qed.
Lemma lem8057033 {_143061 _143062 _143063 : Type'} (_106218 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term293 _143061 _143062 _143063 f _106218 t y.
Proof. exact (EQ_MP (@lem8057030 _143061 _143062 _143063 f _106218 t y) (@lem8057019 _143061 _143062 _143063 _106218 s f x t y h1)). Qed.
Lemma lem8057034 {_143061 _143062 _143063 : Type'} (_106218 : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term293 _143061 _143062 _143063 f _106218 t y.
Proof. exact (@lem8057033 _143061 _143062 _143063 _106218 s f x t y h1). Qed.
Lemma lem8057035 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term255 _143061 _143062 _143063 s f x t y) : term293 _143061 _143062 _143063 f x' t y.
Proof. exact (@lem8057034 _143061 _143062 _143063 x' s f x t y h1). Qed.
Lemma lem8057038 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : f x') (h2 : term255 _143061 _143062 _143063 s f x t y) : @I ((cart _143061 _143063) -> Prop) t y.
Proof. exact (@lem8057035 _143061 _143062 _143063 x' s f x t y h2 (@lem8056990 _143061 _143062 f x' h1)). Qed.
Lemma lem8057039 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : f x') (h2 : term255 _143061 _143062 _143063 s f x t y) : term286 _143061 _143063 t y.
Proof. exact (fun h0 : term249 _143061 _143063 t y => @lem8057038 _143061 _143062 _143063 x' s f x t y h1 h2). Qed.
Lemma lem8057041 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8057042 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term286 _143061 _143063 t y) = (@I ((cart _143061 _143063) -> Prop) t y).
Proof. exact (@lem8057041 (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8057043 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : f x') (h2 : term255 _143061 _143062 _143063 s f x t y) : @I ((cart _143061 _143063) -> Prop) t y.
Proof. exact (EQ_MP (@lem8057042 _143061 _143063 t y) (@lem8057039 _143061 _143062 _143063 x' s f x t y h1 h2)). Qed.
Lemma lem8057046 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8057048 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) : (term249 _143061 _143063 t y) = (term287 _143061 _143063 t y).
Proof. exact (@lem8057046 (@I ((cart _143061 _143063) -> Prop) t y)). Qed.
Lemma lem8057051 {_143061 _143063 : Type'} (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) : term287 _143061 _143063 t y.
Proof. exact (EQ_MP (@lem8057048 _143061 _143063 t y) (@lem8056796 _143061 _143063 t y h1)). Qed.
Lemma lem8057054 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (@lem8057051 _143061 _143063 t y h1 (@lem8057043 _143061 _143062 _143063 x' s f x t y h2 h3)). Qed.
Lemma lem8057055 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : term288.
Proof. exact (fun h0 : ~ False => @lem8057054 _143061 _143062 _143063 x' s f x t y h1 h2 h3). Qed.
Lemma lem8057057 (p : Prop) : (term276 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8057058 : term288 = False.
Proof. exact (@lem8057057 False). Qed.
Lemma lem8057059 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (EQ_MP (@lem8057058) (@lem8057055 _143061 _143062 _143063 x' s f x t y h1 h2 h3)). Qed.
Lemma lem8057060 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : (term249 _143061 _143063 t y) = False.
Proof. exact (prop_ext (fun h4 : term249 _143061 _143063 t y => @lem8057059 _143061 _143062 _143063 x' s f x t y h1 h2 h3) (fun h4 : False => @lem8056796 _143061 _143063 t y h1)). Qed.
Lemma lem8057061 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (EQ_MP (@lem8057060 _143061 _143062 _143063 x' s f x t y h1 h2 h3) (@lem8056796 _143061 _143063 t y h1)). Qed.
Lemma lem8057062 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : (term249 _143061 _143063 t y) = False.
Proof. exact (prop_ext (fun h3 : term249 _143061 _143063 t y => @lem8056907 _143061 _143062 _143063 f s x t y h1 h2) (fun h3 : False => @lem8056774 _143061 _143063 t y h1)). Qed.
Lemma lem8057063 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8057062 _143061 _143062 _143063 f s x t y h1 h2) (@lem8056774 _143061 _143063 t y h1)). Qed.
Lemma lem8057064 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : (term249 _143061 _143062 s x) = False.
Proof. exact (prop_ext (fun h3 : term249 _143061 _143062 s x => @lem8056884 _143061 _143062 _143063 f s x t y h1 h2) (fun h3 : False => @lem8056760 _143061 _143062 s x h1)). Qed.
Lemma lem8057065 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8057064 _143061 _143062 _143063 f s x t y h1 h2) (@lem8056760 _143061 _143062 s x h1)). Qed.
Lemma lem8057066 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : (term249 _143061 _143063 t y) = False.
Proof. exact (prop_ext (fun h4 : term249 _143061 _143063 t y => @lem8057061 _143061 _143062 _143063 x' s f x t y h1 h2 h3) (fun h4 : False => @lem8056730 _143061 _143063 t y h1)). Qed.
Lemma lem8057067 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (EQ_MP (@lem8057066 _143061 _143062 _143063 x' s f x t y h1 h2 h3) (@lem8056730 _143061 _143063 t y h1)). Qed.
Lemma lem8057068 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : (term249 _143061 _143063 t y) = False.
Proof. exact (prop_ext (fun h3 : term249 _143061 _143063 t y => @lem8057063 _143061 _143062 _143063 f s x t y h1 h2) (fun h3 : False => @lem8056664 _143061 _143063 t y h1)). Qed.
Lemma lem8057069 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8057068 _143061 _143062 _143063 f s x t y h1 h2) (@lem8056664 _143061 _143063 t y h1)). Qed.
Lemma lem8057070 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : (term249 _143061 _143062 s x) = False.
Proof. exact (prop_ext (fun h3 : term249 _143061 _143062 s x => @lem8057065 _143061 _143062 _143063 f s x t y h1 h2) (fun h3 : False => @lem8056635 _143061 _143062 s x h1)). Qed.
Lemma lem8057071 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8057070 _143061 _143062 _143063 f s x t y h1 h2) (@lem8056635 _143061 _143062 s x h1)). Qed.
Lemma lem8057072 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : (term249 _143061 _143063 t y) = False.
Proof. exact (prop_ext (fun h4 : term249 _143061 _143063 t y => @lem8057067 _143061 _143062 _143063 x' s f x t y h1 h2 h3) (fun h4 : False => @lem8056730 _143061 _143063 t y h1)). Qed.
Lemma lem8057073 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : f x') (h3 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (EQ_MP (@lem8057072 _143061 _143062 _143063 x' s f x t y h1 h2 h3) (@lem8056730 _143061 _143063 t y h1)). Qed.
Lemma lem8057074 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : (term249 _143061 _143063 t y) = False.
Proof. exact (prop_ext (fun h3 : term249 _143061 _143063 t y => @lem8057069 _143061 _143062 _143063 f s x t y h1 h2) (fun h3 : False => @lem8056664 _143061 _143063 t y h1)). Qed.
Lemma lem8057075 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143063 t y) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8057074 _143061 _143062 _143063 f s x t y h1 h2) (@lem8056664 _143061 _143063 t y h1)). Qed.
Lemma lem8057076 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : (term249 _143061 _143062 s x) = False.
Proof. exact (prop_ext (fun h3 : term249 _143061 _143062 s x => @lem8057071 _143061 _143062 _143063 f s x t y h1 h2) (fun h3 : False => @lem8056635 _143061 _143062 s x h1)). Qed.
Lemma lem8057077 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term249 _143061 _143062 s x) (h2 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (EQ_MP (@lem8057076 _143061 _143062 _143063 f s x t y h1 h2) (@lem8056635 _143061 _143062 s x h1)). Qed.
Lemma lem8057078 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : f x') (h2 : term255 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (or_elim (@lem8056602 _143061 _143062 _143063 s f x t y h2) (fun h0 : term251 _143061 _143062 f s x => @lem8056983 _143061 _143062 _143063 s f x t y h0 h2) (fun h0 : term249 _143061 _143063 t y => @lem8057073 _143061 _143062 _143063 x' s f x t y h0 h1 h2)). Qed.
Lemma lem8057079 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (s : type24 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term266 _143061 _143062 _143063 f s x t y) : False.
Proof. exact (or_elim (@lem8056595 _143061 _143062 _143063 f s x t y h1) (fun h0 : term249 _143061 _143062 s x => @lem8057077 _143061 _143062 _143063 f s x t y h0 h1) (fun h0 : term249 _143061 _143063 t y => @lem8057075 _143061 _143062 _143063 f s x t y h0 h1)). Qed.
Lemma lem8057080 {_143061 _143062 _143063 : Type'} (x' : type24 _143061 _143062) (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : f x') (h2 : term234 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (or_elim (@lem8056581 _143061 _143062 _143063 s f x t y h2) (fun h0 : term266 _143061 _143062 _143063 f s x t y => @lem8057079 _143061 _143062 _143063 f s x t y h0) (fun h0 : term255 _143061 _143062 _143063 s f x t y => @lem8057078 _143061 _143062 _143063 x' s f x t y h1 h0)). Qed.
Lemma lem8057081 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term50 _143061 _143062 f) (h2 : term234 _143061 _143062 _143063 s f x t y) : False.
Proof. exact (ex_elim (@lem8056072 _143061 _143062 f h1) (fun x' : type24 _143061 _143062 => fun h0 : term108 _143061 _143062 f x' => @lem8057080 _143061 _143062 _143063 x' s f x t y h0 h2)). Qed.
Lemma lem8057082 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term50 _143061 _143062 f) (h2 : term100 _143061 _143062 _143063 f x t y) : False.
Proof. exact (ex_elim (@lem8056431 _143061 _143062 _143063 f x t y h2) (fun s : type24 _143061 _143062 => fun h0 : term236 _143061 _143062 _143063 f x t y s => @lem8057081 _143061 _143062 _143063 s f x t y h1 h0)). Qed.
Lemma lem8057083 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term50 _143061 _143062 f) (h2 : term100 _143061 _143062 _143063 f x t y) : (term100 _143061 _143062 _143063 f x t y) = False.
Proof. exact (prop_ext (fun h3 : term100 _143061 _143062 _143063 f x t y => @lem8057082 _143061 _143062 _143063 f x t y h1 h2) (fun h3 : False => @lem8056050 _143061 _143062 _143063 f x t y h2)). Qed.
Lemma lem8057084 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (h1 : term50 _143061 _143062 f) (h2 : term100 _143061 _143062 _143063 f x t y) : False.
Proof. exact (EQ_MP (@lem8057083 _143061 _143062 _143063 f x t y h1 h2) (@lem8056050 _143061 _143062 _143063 f x t y h2)). Qed.
Lemma lem8057085 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (h1 : term50 _143061 _143062 f) : term99 _143061 _143062 _143063 f x t y.
Proof. exact (fun h0 : term100 _143061 _143062 _143063 f x t y => @lem8057084 _143061 _143062 _143063 f x t y h1 h0). Qed.
Lemma lem8057086 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (y : cart _143061 _143063) (f : type56 _143061 _143062) (h1 : term50 _143061 _143062 f) : (term62 _143061 _143062 _143063 f x t y) = (term74 _143061 _143062 _143063 f x t y).
Proof. exact (EQ_MP (@lem8056049 _143061 _143062 _143063 f x t y) (@lem8057085 _143061 _143062 _143063 x t y f h1)). Qed.
Lemma lem8057091 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : term50 _143061 _143062 f) : term78 _143061 _143062 _143063 f x t.
Proof. exact (fun y : cart _143061 _143063 => @lem8057086 _143061 _143062 _143063 x t y f h1). Qed.
Lemma lem8057096 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : term50 _143061 _143062 f) : term81 _143061 _143062 _143063 f t.
Proof. exact (fun x : cart _143061 _143062 => @lem8057091 _143061 _143062 _143063 x t f h1). Qed.
Lemma lem8057097 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term82 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : term50 _143061 _143062 f => @lem8057096 _143061 _143062 _143063 t f h0). Qed.
Lemma lem8057102 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : term94 _143061 _143062 _143063 t.
Proof. exact (fun f : type56 _143061 _143062 => @lem8057097 _143061 _143062 _143063 f t). Qed.
Lemma lem8057107 {_143061 _143062 _143063 : Type'} : term98 _143061 _143062 _143063.
Proof. exact (fun t : type24 _143061 _143063 => @lem8057102 _143061 _143062 _143063 t). Qed.
Lemma lem8057108 {_143061 _143062 _143063 : Type'} : term97 _143061 _143062 _143063.
Proof. exact (EQ_MP (@lem8056044 _143061 _143062 _143063) (@lem8057107 _143061 _143062 _143063)). Qed.
Lemma lem8057109 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : term294 _143061 _143062 _143063 t.
Proof. exact (@lem8057108 _143061 _143062 _143063 t). Qed.
Lemma lem8057110 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : (term294 _143061 _143062 _143063 t) = (term93 _143061 _143062 _143063 t).
Proof. exact (eq_refl (term294 _143061 _143062 _143063 t)). Qed.
Lemma lem8057111 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) : term93 _143061 _143062 _143063 t.
Proof. exact (EQ_MP (@lem8057110 _143061 _143062 _143063 t) (@lem8057109 _143061 _143062 _143063 t)). Qed.
Lemma lem8057112 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) : term295 _143061 _143062 _143063 t f.
Proof. exact (@lem8057111 _143061 _143062 _143063 t f). Qed.
Lemma lem8057113 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term295 _143061 _143062 _143063 t f) = (term84 _143061 _143062 _143063 f t).
Proof. exact (eq_refl (term295 _143061 _143062 _143063 t f)). Qed.
Lemma lem8057114 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term84 _143061 _143062 _143063 f t.
Proof. exact (EQ_MP (@lem8057113 _143061 _143062 _143063 f t) (@lem8057112 _143061 _143062 _143063 t f)). Qed.
Lemma lem8057116 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term84 _143061 _143062 _143063 f t.
Proof. exact (@lem8055875 _143061 _143062 _143063 f t (@lem8057114 _143061 _143062 _143063 f t)). Qed.
Lemma lem8057117 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term85 _143061 _143062 _143063 f t) : False.
Proof. exact (@lem8057116 _143061 _143062 _143063 f t (@lem8055859 _143061 _143062 _143063 f t h1)). Qed.
Lemma lem8057118 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term85 _143061 _143062 _143063 f t) : (term85 _143061 _143062 _143063 f t) = False.
Proof. exact (prop_ext (fun h2 : term85 _143061 _143062 _143063 f t => @lem8057117 _143061 _143062 _143063 f t h1) (fun h2 : False => @lem8055859 _143061 _143062 _143063 f t h1)). Qed.
Lemma lem8057119 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (h1 : term85 _143061 _143062 _143063 f t) : False.
Proof. exact (EQ_MP (@lem8057118 _143061 _143062 _143063 f t h1) (@lem8055859 _143061 _143062 _143063 f t h1)). Qed.
Lemma lem8057120 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term84 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : term85 _143061 _143062 _143063 f t => @lem8057119 _143061 _143062 _143063 f t h0). Qed.
Lemma lem8057121 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term82 _143061 _143062 _143063 f t.
Proof. exact (EQ_MP (@lem8055858 _143061 _143062 _143063 f t) (@lem8057120 _143061 _143062 _143063 f t)). Qed.
Lemma lem8057122 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term49 _143061 _143062 _143063 f t.
Proof. exact (EQ_MP (@lem8055854 _143061 _143062 _143063 f t) (@lem8057121 _143061 _143062 _143063 f t)). Qed.
Lemma lem8057123 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term48 _143061 _143062 _143063 f t.
Proof. exact (EQ_MP (@lem8055709 _143061 _143062 _143063 f t) (@lem8057122 _143061 _143062 _143063 f t)). Qed.
Lemma lem8057124 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : term43 _143061 _143062 f) : term47 _143061 _143062 _143063 f t.
Proof. exact (@lem8057123 _143061 _143062 _143063 f t (@lem8049087 _143061 _143062 f h1)). Qed.
Lemma lem8057134 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : term43 _143061 _143062 f) : (term296 _143061 _143062 _143063 f t) = (term297 _143061 _143062 _143063 f t).
Proof. exact (EQ_MP (@lem8050938 _143061 _143062 _143063 f t) (@lem8057124 _143061 _143062 _143063 t f h1)). Qed.
Lemma lem8057135 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : term43 _143061 _143062 f) : (term43 _143061 _143062 f) = ((term296 _143061 _143062 _143063 f t) = (term297 _143061 _143062 _143063 f t)).
Proof. exact (prop_ext (fun h2 : term43 _143061 _143062 f => @lem8057134 _143061 _143062 _143063 t f h1) (fun h2 : (term296 _143061 _143062 _143063 f t) = (term297 _143061 _143062 _143063 f t) => @lem8049087 _143061 _143062 f h1)). Qed.
Lemma lem8057136 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : term43 _143061 _143062 f) : (term296 _143061 _143062 _143063 f t) = (term297 _143061 _143062 _143063 f t).
Proof. exact (EQ_MP (@lem8057135 _143061 _143062 _143063 t f h1) (@lem8049087 _143061 _143062 f h1)). Qed.
Lemma lem8057137 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term298 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : term43 _143061 _143062 f => @lem8057136 _143061 _143062 _143063 t f h0). Qed.
Lemma lem8057138 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term296 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t).
Proof. exact (EQ_MP (@lem8050658 _143061 _143062 _143063 t f h1) (@lem8055652 _143061 _143062 _143063 t f h1)). Qed.
Lemma lem8057139 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (f = (@EMPTY ((cart _143061 _143062) -> Prop))) = ((term296 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t)).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY ((cart _143061 _143062) -> Prop)) => @lem8057138 _143061 _143062 _143063 t f h1) (fun h2 : (term296 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t) => @lem8049070 _143061 _143062 f h1)). Qed.
Lemma lem8057140 {_143061 _143062 _143063 : Type'} (t : type24 _143061 _143063) (f : type56 _143061 _143062) (h1 : f = (@EMPTY ((cart _143061 _143062) -> Prop))) : (term296 _143061 _143062 _143063 f t) = (@PCROSS _143061 _143062 _143063 (@UNIV (cart _143061 _143062)) t).
Proof. exact (EQ_MP (@lem8057139 _143061 _143062 _143063 t f h1) (@lem8049070 _143061 _143062 f h1)). Qed.
Lemma lem8057141 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term299 _143061 _143062 _143063 f t.
Proof. exact (fun h0 : f = (@EMPTY ((cart _143061 _143062) -> Prop)) => @lem8057140 _143061 _143062 _143063 t f h0). Qed.
Lemma lem8057142 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : term300 _143061 _143062 _143063 f t.
Proof. exact (conj (@lem8057141 _143061 _143062 _143063 f t) (@lem8057137 _143061 _143062 _143063 f t)). Qed.
Lemma lem8057143 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term296 _143061 _143062 _143063 f t) = (term301 _143061 _143062 _143063 f t).
Proof. exact (EQ_MP (@lem8049069 _143061 _143062 _143063 f t) (@lem8057142 _143061 _143062 _143063 f t)). Qed.
