Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_INSERT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3287487 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3287488 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3287487 A s t). Qed.
Lemma lem3287489 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1 A s x t) = (term2 A s x t).
Proof. exact (@lem3287488 A s (@INSERT A x t)). Qed.
Lemma lem3287496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3287497 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A s x t) = (term4 A s x t).
Proof. exact (MK_COMB (@lem3287496) (@lem3287489 A s x t)). Qed.
Lemma lem3287499 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3287500 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3287499 A s t). Qed.
Lemma lem3287507 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term1 A s x t) = (@SUBSET A s t)) = ((term2 A s x t) = (term0 A s t)).
Proof. exact (MK_COMB (@lem3287497 A s x t) (@lem3287500 A s t)). Qed.
Lemma lem3287512 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term6 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3287507 A x s t)). Qed.
Lemma lem3287513 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3287514 {A : Type'} (x : A) (s : A -> Prop) : (term7 A x s) = (term8 A x s).
Proof. exact (MK_COMB (@lem3287513 A) (@lem3287512 A x s)). Qed.
Lemma lem3287519 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term9 A x s).
Proof. exact (eq_refl (term9 A x s)). Qed.
Lemma lem3287520 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term11 A x s).
Proof. exact (MK_COMB (@lem3287519 A x s) (@lem3287514 A x s)). Qed.
Lemma lem3287523 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3287520 A x s)). Qed.
Lemma lem3287524 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3287525 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem3287524 A) (@lem3287523 A x)). Qed.
Lemma lem3287530 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (fun_ext (fun x : A => @lem3287525 A x)). Qed.
Lemma lem3287531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287532 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem3287531 A) (@lem3287530 A)). Qed.
Lemma lem3287537 {A : Type'} : (term19 A) = (term18 A).
Proof. exact (SYM (@lem3287532 A)). Qed.
Lemma lem3287549 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3287550 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3287549 A P x). Qed.
Lemma lem3287551 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3287550 A s x). Qed.
Lemma lem3287552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3287553 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3287552) (@lem3287551 A s x)). Qed.
Lemma lem3287554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3287555 {A : Type'} (s : A -> Prop) (x : A) : (term9 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3287554) (@lem3287553 A s x)). Qed.
Lemma lem3287569 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3287570 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3287569 A P x). Qed.
Lemma lem3287571 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3287570 A s x'). Qed.
Lemma lem3287572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3287573 {A : Type'} (s : A -> Prop) (x' : A) : (term23 A x' s) = (term24 A s x').
Proof. exact (MK_COMB (@lem3287572) (@lem3287571 A s x')). Qed.
Lemma lem3287575 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term25 A x y s) = (term26 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3287576 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term25 A x y s) = (term26 A y x s).
Proof. exact (@lem3287575 A y x s). Qed.
Lemma lem3287577 {A : Type'} (x : A) (x' : A) (t : A -> Prop) : (term25 A x' x t) = (term26 A x x' t).
Proof. exact (@lem3287576 A x x' t). Qed.
Lemma lem3287583 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3287584 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3287583 A P x). Qed.
Lemma lem3287585 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3287584 A t x'). Qed.
Lemma lem3287586 {A : Type'} (x' : A) (x : A) : (term27 A x' x) = (term27 A x' x).
Proof. exact (eq_refl (term27 A x' x)). Qed.
Lemma lem3287587 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term26 A x x' t) = (term28 A x t x').
Proof. exact (MK_COMB (@lem3287586 A x' x) (@lem3287585 A t x')). Qed.
Lemma lem3287590 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term25 A x' x t) = (term28 A x t x').
Proof. exact (TRANS (@lem3287577 A x x' t) (@lem3287587 A x t x')). Qed.
Lemma lem3287591 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term29 A s x' x t) = (term30 A s x t x').
Proof. exact (MK_COMB (@lem3287573 A s x') (@lem3287590 A x t x')). Qed.
Lemma lem3287594 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A s x t) = (term32 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3287591 A s x t x')). Qed.
Lemma lem3287595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287596 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term2 A s x t) = (term33 A s x t).
Proof. exact (MK_COMB (@lem3287595 A) (@lem3287594 A s x t)). Qed.
Lemma lem3287601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3287602 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A s x t) = (term34 A s x t).
Proof. exact (MK_COMB (@lem3287601) (@lem3287596 A s x t)). Qed.
Lemma lem3287610 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3287611 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3287610 A P x). Qed.
Lemma lem3287612 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3287611 A s x). Qed.
Lemma lem3287613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3287614 {A : Type'} (s : A -> Prop) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (MK_COMB (@lem3287613) (@lem3287612 A s x)). Qed.
Lemma lem3287616 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3287617 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3287616 A P x). Qed.
Lemma lem3287618 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3287617 A t x). Qed.
Lemma lem3287619 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term35 A s x t) = (term36 A s t x).
Proof. exact (MK_COMB (@lem3287614 A s x) (@lem3287618 A t x)). Qed.
Lemma lem3287622 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term37 A s t) = (term38 A s t).
Proof. exact (fun_ext (fun x : A => @lem3287619 A s t x)). Qed.
Lemma lem3287623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287624 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem3287623 A) (@lem3287622 A s t)). Qed.
Lemma lem3287629 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term2 A s x t) = (term0 A s t)) = ((term33 A s x t) = (term39 A s t)).
Proof. exact (MK_COMB (@lem3287602 A s x t) (@lem3287624 A s t)). Qed.
Lemma lem3287632 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = (term40 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3287629 A x s t)). Qed.
Lemma lem3287633 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3287634 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term41 A x s).
Proof. exact (MK_COMB (@lem3287633 A) (@lem3287632 A x s)). Qed.
Lemma lem3287639 {A : Type'} (x : A) (s : A -> Prop) : (term11 A x s) = (term42 A x s).
Proof. exact (MK_COMB (@lem3287555 A s x) (@lem3287634 A x s)). Qed.
Lemma lem3287642 {A : Type'} (x : A) : (term13 A x) = (term43 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3287639 A x s)). Qed.
Lemma lem3287643 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3287644 {A : Type'} (x : A) : (term15 A x) = (term44 A x).
Proof. exact (MK_COMB (@lem3287643 A) (@lem3287642 A x)). Qed.
Lemma lem3287649 {A : Type'} : (term17 A) = (term45 A).
Proof. exact (fun_ext (fun x : A => @lem3287644 A x)). Qed.
Lemma lem3287650 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287651 {A : Type'} : (term19 A) = (term46 A).
Proof. exact (MK_COMB (@lem3287650 A) (@lem3287649 A)). Qed.
Lemma lem3287656 {A : Type'} : (term46 A) = (term19 A).
Proof. exact (SYM (@lem3287651 A)). Qed.
Lemma lem3287658 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3287659 {A : Type'} : (term46 A) = (term48 A).
Proof. exact (@lem3287658 (term46 A)). Qed.
Lemma lem3287660 {A : Type'} : (term48 A) = (term46 A).
Proof. exact (SYM (@lem3287659 A)). Qed.
Lemma lem3287661 {A : Type'} (h1 : term49 A) : term49 A.
Proof. exact (h1). Qed.
Lemma lem3287664 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3287665 {A : Type'} : term50 A.
Proof. exact (fun h0 : term48 A => @lem3287664 A h0). Qed.
Lemma lem3287666 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (h1). Qed.
Lemma lem3287667 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3287668 {A : Type'} (h1 : term48 A) (h2 : term50 A) : term48 A.
Proof. exact (@lem3287666 A h2 (@lem3287667 A h1)). Qed.
Lemma lem3287669 {A : Type'} (h1 : term48 A) : term51 A.
Proof. exact (fun h0 : term50 A => @lem3287668 A h1 h0). Qed.
Lemma lem3287670 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (h1). Qed.
Lemma lem3287671 {A : Type'} (h1 : term48 A) (h2 : term50 A) : term48 A.
Proof. exact (@lem3287669 A h1 (@lem3287670 A h2)). Qed.
Lemma lem3287672 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (fun h0 : term48 A => @lem3287671 A h0 h1). Qed.
Lemma lem3287673 {A : Type'} : term52 A.
Proof. exact (fun h0 : term50 A => @lem3287672 A h0). Qed.
Lemma lem3287676 {A : Type'} : term50 A.
Proof. exact (@lem3287673 A (@lem3287665 A)). Qed.
Lemma lem3287677 {A : Type'} : term50 A.
Proof. exact (@lem3287676 A). Qed.
Lemma lem3287679 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3287680 {A : Type'} : (term48 A) = (term53 A).
Proof. exact (@lem3287679 (term49 A)). Qed.
Lemma lem3287682 (t : Prop) : (term54 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3287683 {A : Type'} : (term53 A) = (term46 A).
Proof. exact (@lem3287682 (term46 A)). Qed.
Lemma lem3287716 {A : Type'} : (term48 A) = (term46 A).
Proof. exact (TRANS (@lem3287680 A) (@lem3287683 A)). Qed.
Lemma lem3287721 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term36 A s t x) = (term36 A s t x).
Proof. exact (eq_refl (term36 A s t x)). Qed.
Lemma lem3287722 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term38 A s t).
Proof. exact (fun_ext (fun x : A => @lem3287721 A s t x)). Qed.
Lemma lem3287723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287724 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem3287723 A) (@lem3287722 A s t)). Qed.
Lemma lem3287733 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term30 A s x t x') = (term30 A s x t x').
Proof. exact (eq_refl (term30 A s x t x')). Qed.
Lemma lem3287734 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A s x t) = (term32 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3287733 A s x t x')). Qed.
Lemma lem3287735 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287736 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term33 A s x t) = (term33 A s x t).
Proof. exact (MK_COMB (@lem3287735 A) (@lem3287734 A s x t)). Qed.
Lemma lem3287737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3287738 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term34 A s x t) = (term34 A s x t).
Proof. exact (MK_COMB (@lem3287737) (@lem3287736 A s x t)). Qed.
Lemma lem3287739 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term33 A s x t) = (term39 A s t)) = ((term33 A s x t) = (term39 A s t)).
Proof. exact (MK_COMB (@lem3287738 A s x t) (@lem3287724 A s t)). Qed.
Lemma lem3287740 {A : Type'} (x : A) (s : A -> Prop) : (term40 A x s) = (term40 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3287739 A x s t)). Qed.
Lemma lem3287741 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3287742 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term41 A x s).
Proof. exact (MK_COMB (@lem3287741 A) (@lem3287740 A x s)). Qed.
Lemma lem3287747 {A : Type'} (s : A -> Prop) (x : A) : (term22 A s x) = (term22 A s x).
Proof. exact (eq_refl (term22 A s x)). Qed.
Lemma lem3287748 {A : Type'} (x : A) (s : A -> Prop) : (term42 A x s) = (term42 A x s).
Proof. exact (MK_COMB (@lem3287747 A s x) (@lem3287742 A x s)). Qed.
Lemma lem3287749 {A : Type'} (x : A) : (term43 A x) = (term43 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3287748 A x s)). Qed.
Lemma lem3287750 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3287751 {A : Type'} (x : A) : (term44 A x) = (term44 A x).
Proof. exact (MK_COMB (@lem3287750 A) (@lem3287749 A x)). Qed.
Lemma lem3287752 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (fun_ext (fun x : A => @lem3287751 A x)). Qed.
Lemma lem3287753 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287754 {A : Type'} : (term46 A) = (term46 A).
Proof. exact (MK_COMB (@lem3287753 A) (@lem3287752 A)). Qed.
Lemma lem3287795 {A : Type'} : (term48 A) = (term46 A).
Proof. exact (TRANS (@lem3287716 A) (@lem3287754 A)). Qed.
Lemma lem3287796 {A : Type'} : (term46 A) = (term48 A).
Proof. exact (SYM (@lem3287795 A)). Qed.
Lemma lem3287799 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3287800 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term33 A s x t) = (term39 A s t)) = (term55 A x s t).
Proof. exact (@lem3287799 ((term33 A s x t) = (term39 A s t))). Qed.
Lemma lem3287801 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term55 A x s t) = ((term33 A s x t) = (term39 A s t)).
Proof. exact (SYM (@lem3287800 A x s t)). Qed.
Lemma lem3287802 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term56 A x s t) : term56 A x s t.
Proof. exact (h1). Qed.
Lemma lem3287808 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term21 A s x.
Proof. exact (h1). Qed.
Lemma lem3287819 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term57 A x t x') = (term58 A x t x').
Proof. exact (@lem17160 (x' = x) (t x')). Qed.
Lemma lem3287824 {A : Type'} (s : A -> Prop) (x' : A) : (term59 A s x') = (term59 A s x').
Proof. exact (eq_refl (term59 A s x')). Qed.
Lemma lem3287825 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term60 A s x t x') = (term61 A s x t x').
Proof. exact (MK_COMB (@lem3287824 A s x') (@lem3287819 A x t x')). Qed.
Lemma lem3287826 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term62 A s x t x') = (term60 A s x t x').
Proof. exact (@lem17362 (s x') (term28 A x t x')). Qed.
Lemma lem3287827 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term62 A s x t x') = (term61 A s x t x').
Proof. exact (TRANS (@lem3287826 A s x t x') (@lem3287825 A s x t x')). Qed.
Lemma lem3287832 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term30 A s x t x') = (term63 A s x t x').
Proof. exact (@lem17265 (s x') (term28 A x t x')). Qed.
Lemma lem3287833 {A : Type'} (P : A -> Prop) : (term64 A P) = (term65 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3287834 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term66 A s x t) = (term67 A s x t).
Proof. exact (@lem3287833 A (term32 A s x t)). Qed.
Lemma lem3287835 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term68 A s x t x') = (term30 A s x t x').
Proof. exact (eq_refl (term68 A s x t x')). Qed.
Lemma lem3287836 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3287837 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term69 A s x t x') = (term62 A s x t x').
Proof. exact (MK_COMB (@lem3287836) (@lem3287835 A s x t x')). Qed.
Lemma lem3287838 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term69 A s x t x') = (term61 A s x t x').
Proof. exact (TRANS (@lem3287837 A s x t x') (@lem3287827 A s x t x')). Qed.
Lemma lem3287839 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term70 A s x t) = (term71 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3287838 A s x t x')). Qed.
Lemma lem3287840 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3287841 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term67 A s x t) = (term72 A s x t).
Proof. exact (MK_COMB (@lem3287840 A) (@lem3287839 A s x t)). Qed.
Lemma lem3287842 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term66 A s x t) = (term72 A s x t).
Proof. exact (TRANS (@lem3287834 A s x t) (@lem3287841 A s x t)). Qed.
Lemma lem3287843 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A s x t) = (term73 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3287832 A s x t x')). Qed.
Lemma lem3287844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287845 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term33 A s x t) = (term74 A s x t).
Proof. exact (MK_COMB (@lem3287844 A) (@lem3287843 A s x t)). Qed.
Lemma lem3287854 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term75 A s t x) = (term76 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3287859 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term36 A s t x) = (term77 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3287860 {A : Type'} (P : A -> Prop) : (term64 A P) = (term65 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3287861 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term79 A s t).
Proof. exact (@lem3287860 A (term38 A s t)). Qed.
Lemma lem3287862 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term80 A s t x) = (term36 A s t x).
Proof. exact (eq_refl (term80 A s t x)). Qed.
Lemma lem3287863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3287864 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term81 A s t x) = (term75 A s t x).
Proof. exact (MK_COMB (@lem3287863) (@lem3287862 A s t x)). Qed.
Lemma lem3287865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term81 A s t x) = (term76 A s t x).
Proof. exact (TRANS (@lem3287864 A s t x) (@lem3287854 A s t x)). Qed.
Lemma lem3287866 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term83 A s t).
Proof. exact (fun_ext (fun x : A => @lem3287865 A s t x)). Qed.
Lemma lem3287867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3287868 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term84 A s t).
Proof. exact (MK_COMB (@lem3287867 A) (@lem3287866 A s t)). Qed.
Lemma lem3287869 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term84 A s t).
Proof. exact (TRANS (@lem3287861 A s t) (@lem3287868 A s t)). Qed.
Lemma lem3287870 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3287859 A s t x)). Qed.
Lemma lem3287871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3287872 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3287871 A) (@lem3287870 A s t)). Qed.
Lemma lem3287873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3287874 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term87 A s x t) = (term88 A s x t).
Proof. exact (MK_COMB (@lem3287873) (@lem3287842 A s x t)). Qed.
Lemma lem3287875 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term89 A x s t) = (term90 A x s t).
Proof. exact (MK_COMB (@lem3287874 A s x t) (@lem3287872 A s t)). Qed.
Lemma lem3287876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3287877 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term91 A s x t) = (term92 A s x t).
Proof. exact (MK_COMB (@lem3287876) (@lem3287845 A s x t)). Qed.
Lemma lem3287878 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term93 A x s t) = (term94 A x s t).
Proof. exact (MK_COMB (@lem3287877 A s x t) (@lem3287869 A s t)). Qed.
Lemma lem3287879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3287880 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term95 A x s t) = (term96 A x s t).
Proof. exact (MK_COMB (@lem3287879) (@lem3287878 A x s t)). Qed.
Lemma lem3287881 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term97 A x s t) = (term98 A x s t).
Proof. exact (MK_COMB (@lem3287880 A x s t) (@lem3287875 A x s t)). Qed.
Lemma lem3287882 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term97 A x s t).
Proof. exact (@lem17646 (term33 A s x t) (term39 A s t)). Qed.
Lemma lem3287883 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term98 A x s t).
Proof. exact (TRANS (@lem3287882 A x s t) (@lem3287881 A x s t)). Qed.
Lemma lem3288022 {A : Type'} (P : Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3288023 {A : Type'} (P : Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (@lem3288022 A P Q). Qed.
Lemma lem3288024 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term101 A x s t) = (term102 A x s t).
Proof. exact (@lem3288023 A (term74 A s x t) (term83 A s t)). Qed.
Lemma lem3288025 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term76 A s t x).
Proof. exact (eq_refl (term103 A s t x)). Qed.
Lemma lem3288026 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term104 A s t) = (term83 A s t).
Proof. exact (fun_ext (fun x : A => @lem3288025 A s t x)). Qed.
Lemma lem3288027 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3288028 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term84 A s t).
Proof. exact (MK_COMB (@lem3288027 A) (@lem3288026 A s t)). Qed.
Lemma lem3288029 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term92 A s x t) = (term92 A s x t).
Proof. exact (eq_refl (term92 A s x t)). Qed.
Lemma lem3288030 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term101 A x s t) = (term94 A x s t).
Proof. exact (MK_COMB (@lem3288029 A s x t) (@lem3288028 A s t)). Qed.
Lemma lem3288031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3288032 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term106 A x s t) = (term107 A x s t).
Proof. exact (MK_COMB (@lem3288031) (@lem3288030 A x s t)). Qed.
Lemma lem3288033 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term103 A s t x') = (term76 A s t x').
Proof. exact (eq_refl (term103 A s t x')). Qed.
Lemma lem3288034 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term92 A s x t) = (term92 A s x t).
Proof. exact (eq_refl (term92 A s x t)). Qed.
Lemma lem3288035 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term108 A x s t x') = (term109 A x s t x').
Proof. exact (MK_COMB (@lem3288034 A s x t) (@lem3288033 A s t x')). Qed.
Lemma lem3288036 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term110 A x s t) = (term111 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3288035 A x s t x')). Qed.
Lemma lem3288037 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3288038 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term102 A x s t) = (term112 A x s t).
Proof. exact (MK_COMB (@lem3288037 A) (@lem3288036 A x s t)). Qed.
Lemma lem3288039 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term101 A x s t) = (term102 A x s t)) = ((term94 A x s t) = (term112 A x s t)).
Proof. exact (MK_COMB (@lem3288032 A x s t) (@lem3288038 A x s t)). Qed.
Lemma lem3288040 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term94 A x s t) = (term112 A x s t).
Proof. exact (EQ_MP (@lem3288039 A x s t) (@lem3288024 A x s t)). Qed.
Lemma lem3288041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3288042 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term96 A x s t) = (term113 A x s t).
Proof. exact (MK_COMB (@lem3288041) (@lem3288040 A x s t)). Qed.
Lemma lem3288044 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3288045 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (@lem3288044 A P Q). Qed.
Lemma lem3288046 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term116 A x s t) = (term117 A x s t).
Proof. exact (@lem3288045 A (term71 A s x t) (term86 A s t)). Qed.
Lemma lem3288047 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term118 A s x t x') = (term61 A s x t x').
Proof. exact (eq_refl (term118 A s x t x')). Qed.
Lemma lem3288048 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term119 A s x t) = (term71 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3288047 A s x t x')). Qed.
Lemma lem3288049 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3288050 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term120 A s x t) = (term72 A s x t).
Proof. exact (MK_COMB (@lem3288049 A) (@lem3288048 A s x t)). Qed.
Lemma lem3288051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3288052 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term121 A s x t) = (term88 A s x t).
Proof. exact (MK_COMB (@lem3288051) (@lem3288050 A s x t)). Qed.
Lemma lem3288053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (eq_refl (term86 A s t)). Qed.
Lemma lem3288054 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term116 A x s t) = (term90 A x s t).
Proof. exact (MK_COMB (@lem3288052 A s x t) (@lem3288053 A s t)). Qed.
Lemma lem3288055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3288056 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term122 A x s t) = (term123 A x s t).
Proof. exact (MK_COMB (@lem3288055) (@lem3288054 A x s t)). Qed.
Lemma lem3288057 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term118 A s x t x') = (term61 A s x t x').
Proof. exact (eq_refl (term118 A s x t x')). Qed.
Lemma lem3288058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3288059 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term124 A s x t x') = (term125 A s x t x').
Proof. exact (MK_COMB (@lem3288058) (@lem3288057 A s x t x')). Qed.
Lemma lem3288060 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (eq_refl (term86 A s t)). Qed.
Lemma lem3288061 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term126 A x x' s t) = (term127 A x x' s t).
Proof. exact (MK_COMB (@lem3288059 A s x t x') (@lem3288060 A s t)). Qed.
Lemma lem3288062 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term128 A x s t) = (term129 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3288061 A x x' s t)). Qed.
Lemma lem3288063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3288064 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term117 A x s t) = (term130 A x s t).
Proof. exact (MK_COMB (@lem3288063 A) (@lem3288062 A x s t)). Qed.
Lemma lem3288065 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term116 A x s t) = (term117 A x s t)) = ((term90 A x s t) = (term130 A x s t)).
Proof. exact (MK_COMB (@lem3288056 A x s t) (@lem3288064 A x s t)). Qed.
Lemma lem3288066 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term90 A x s t) = (term130 A x s t).
Proof. exact (EQ_MP (@lem3288065 A x s t) (@lem3288046 A x s t)). Qed.
Lemma lem3288067 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term98 A x s t) = (term131 A x s t).
Proof. exact (MK_COMB (@lem3288042 A x s t) (@lem3288066 A x s t)). Qed.
Lemma lem3288069 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3288070 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (@lem3288069 A P Q). Qed.
Lemma lem3288071 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term134 A x s t) = (term135 A x s t).
Proof. exact (@lem3288070 A (term111 A x s t) (term129 A x s t)). Qed.
Lemma lem3288072 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term136 A x s t x') = (term109 A x s t x').
Proof. exact (eq_refl (term136 A x s t x')). Qed.
Lemma lem3288073 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term137 A x s t) = (term111 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3288072 A x s t x')). Qed.
Lemma lem3288074 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3288075 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term138 A x s t) = (term112 A x s t).
Proof. exact (MK_COMB (@lem3288074 A) (@lem3288073 A x s t)). Qed.
Lemma lem3288076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3288077 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term139 A x s t) = (term113 A x s t).
Proof. exact (MK_COMB (@lem3288076) (@lem3288075 A x s t)). Qed.
Lemma lem3288078 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term140 A x s t x') = (term127 A x x' s t).
Proof. exact (eq_refl (term140 A x s t x')). Qed.
Lemma lem3288079 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term141 A x s t) = (term129 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3288078 A x x' s t)). Qed.
Lemma lem3288080 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3288081 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term142 A x s t) = (term130 A x s t).
Proof. exact (MK_COMB (@lem3288080 A) (@lem3288079 A x s t)). Qed.
Lemma lem3288082 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term134 A x s t) = (term131 A x s t).
Proof. exact (MK_COMB (@lem3288077 A x s t) (@lem3288081 A x s t)). Qed.
Lemma lem3288083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3288084 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term143 A x s t) = (term144 A x s t).
Proof. exact (MK_COMB (@lem3288083) (@lem3288082 A x s t)). Qed.
Lemma lem3288085 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term136 A x s t x') = (term109 A x s t x').
Proof. exact (eq_refl (term136 A x s t x')). Qed.
Lemma lem3288086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3288087 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term145 A x s t x') = (term146 A x s t x').
Proof. exact (MK_COMB (@lem3288086) (@lem3288085 A x s t x')). Qed.
Lemma lem3288088 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term140 A x s t x') = (term127 A x x' s t).
Proof. exact (eq_refl (term140 A x s t x')). Qed.
Lemma lem3288089 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term147 A x s t x') = (term148 A x x' s t).
Proof. exact (MK_COMB (@lem3288087 A x s t x') (@lem3288088 A x x' s t)). Qed.
Lemma lem3288090 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term149 A x s t) = (term150 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3288089 A x x' s t)). Qed.
Lemma lem3288091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3288092 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term135 A x s t) = (term151 A x s t).
Proof. exact (MK_COMB (@lem3288091 A) (@lem3288090 A x s t)). Qed.
Lemma lem3288093 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term134 A x s t) = (term135 A x s t)) = ((term131 A x s t) = (term151 A x s t)).
Proof. exact (MK_COMB (@lem3288084 A x s t) (@lem3288092 A x s t)). Qed.
Lemma lem3288094 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term131 A x s t) = (term151 A x s t).
Proof. exact (EQ_MP (@lem3288093 A x s t) (@lem3288071 A x s t)). Qed.
Lemma lem3288096 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term98 A x s t) = (term151 A x s t).
Proof. exact (TRANS (@lem3288067 A x s t) (@lem3288094 A x s t)). Qed.
Lemma lem3288097 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term151 A x s t).
Proof. exact (TRANS (@lem3287883 A x s t) (@lem3288096 A x s t)). Qed.
Lemma lem3288098 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term56 A x s t) : term151 A x s t.
Proof. exact (EQ_MP (@lem3288097 A x s t) (@lem3287802 A x s t h1)). Qed.
Lemma lem3288099 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term148 A x x' s t) : term148 A x x' s t.
Proof. exact (h1). Qed.
Lemma lem3288105 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term21 A s x.
Proof. exact (h1). Qed.
Lemma lem3288116 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term77 A s t x) = (term77 A s t x).
Proof. exact (eq_refl (term77 A s t x)). Qed.
Lemma lem3288117 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3288116 A s t x)). Qed.
Lemma lem3288118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288119 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3288118 A) (@lem3288117 A s t)). Qed.
Lemma lem3288142 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term125 A s x t x') = (term125 A s x t x').
Proof. exact (eq_refl (term125 A s x t x')). Qed.
Lemma lem3288143 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term127 A x x' s t) = (term127 A x x' s t).
Proof. exact (MK_COMB (@lem3288142 A s x t x') (@lem3288119 A s t)). Qed.
Lemma lem3288154 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term76 A s t x') = (term76 A s t x').
Proof. exact (eq_refl (term76 A s t x')). Qed.
Lemma lem3288173 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term63 A s x t x') = (term63 A s x t x').
Proof. exact (eq_refl (term63 A s x t x')). Qed.
Lemma lem3288174 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term73 A s x t) = (term73 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3288173 A s x t x')). Qed.
Lemma lem3288175 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288176 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term74 A s x t) = (term74 A s x t).
Proof. exact (MK_COMB (@lem3288175 A) (@lem3288174 A s x t)). Qed.
Lemma lem3288177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3288178 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term92 A s x t) = (term92 A s x t).
Proof. exact (MK_COMB (@lem3288177) (@lem3288176 A s x t)). Qed.
Lemma lem3288179 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term109 A x s t x') = (term109 A x s t x').
Proof. exact (MK_COMB (@lem3288178 A s x t) (@lem3288154 A s t x')). Qed.
Lemma lem3288180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3288181 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term146 A x s t x') = (term146 A x s t x').
Proof. exact (MK_COMB (@lem3288180) (@lem3288179 A x s t x')). Qed.
Lemma lem3288182 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term148 A x x' s t) = (term148 A x x' s t).
Proof. exact (MK_COMB (@lem3288181 A x s t x') (@lem3288143 A x x' s t)). Qed.
Lemma lem3288183 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term148 A x x' s t) : term148 A x x' s t.
Proof. exact (EQ_MP (@lem3288182 A x x' s t) (@lem3288099 A x x' s t h1)). Qed.
Lemma lem3288184 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term109 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3288185 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term127 A x x' s t.
Proof. exact (h1). Qed.
Lemma lem3288186 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term76 A s t x'.
Proof. exact (proj2 (@lem3288184 A x s t x' h1)). Qed.
Lemma lem3288187 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term74 A s x t.
Proof. exact (proj1 (@lem3288184 A x s t x' h1)). Qed.
Lemma lem3288190 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term86 A s t.
Proof. exact (proj2 (@lem3288185 A x x' s t h1)). Qed.
Lemma lem3288191 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term61 A s x t x'.
Proof. exact (proj1 (@lem3288185 A x x' s t h1)). Qed.
Lemma lem3288192 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term58 A x t x'.
Proof. exact (proj2 (@lem3288191 A x x' s t h1)). Qed.
Lemma lem3288199 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term21 A s x.
Proof. exact (h1). Qed.
Lemma lem3288213 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term63 A s x t x') = (term63 A s x t x').
Proof. exact (eq_refl (term63 A s x t x')). Qed.
Lemma lem3288214 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term73 A s x t) = (term73 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3288213 A s x t x')). Qed.
Lemma lem3288215 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288217 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term74 A s x t) = (term74 A s x t).
Proof. exact (MK_COMB (@lem3288215 A) (@lem3288214 A s x t)). Qed.
Lemma lem3288218 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term74 A s x t.
Proof. exact (EQ_MP (@lem3288217 A s x t) (@lem3288187 A x s t x' h1)). Qed.
Lemma lem3288238 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term77 A s t x) = (term77 A s t x).
Proof. exact (eq_refl (term77 A s t x)). Qed.
Lemma lem3288239 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3288238 A s t x)). Qed.
Lemma lem3288240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288242 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (MK_COMB (@lem3288240 A) (@lem3288239 A s t)). Qed.
Lemma lem3288243 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term86 A s t.
Proof. exact (EQ_MP (@lem3288242 A s t) (@lem3288190 A x x' s t h1)). Qed.
Lemma lem3288256 {A : Type'} (_33814 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term152 A s x t _33814.
Proof. exact (@lem3288218 A x s t x' h1 _33814). Qed.
Lemma lem3288257 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_33814 : A) : (term152 A s x t _33814) = (term63 A s x t _33814).
Proof. exact (eq_refl (term152 A s x t _33814)). Qed.
Lemma lem3288259 {A : Type'} (_33815 : A) (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term153 A s t _33815.
Proof. exact (@lem3288243 A x x' s t h1 _33815). Qed.
Lemma lem3288260 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33815 : A) : (term153 A s t _33815) = (term77 A s t _33815).
Proof. exact (eq_refl (term153 A s t _33815)). Qed.
Lemma lem3288263 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term21 A s x.
Proof. exact (h1). Qed.
Lemma lem3288273 {A : Type'} (_33814 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term63 A s x t _33814.
Proof. exact (EQ_MP (@lem3288257 A s x t _33814) (@lem3288256 A _33814 x s t x' h1)). Qed.
Lemma lem3288277 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term21 A t x'.
Proof. exact (proj2 (@lem3288186 A x s t x' h1)). Qed.
Lemma lem3288285 {A : Type'} (_33815 : A) (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term77 A s t _33815.
Proof. exact (EQ_MP (@lem3288260 A s t _33815) (@lem3288259 A _33815 x x' s t h1)). Qed.
Lemma lem3288291 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term21 A t x'.
Proof. exact (proj2 (@lem3288192 A x x' s t h1)). Qed.
Lemma lem3288304 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3288305 {A : Type'} (_33818 : A) (_33819 : A) (h1 : _33818 = _33819) : _33818 = _33819.
Proof. exact (h1). Qed.
Lemma lem3288306 {A : Type'} (s : A -> Prop) (_33818 : A) (_33819 : A) (h1 : _33818 = _33819) : (s _33818) = (s _33819).
Proof. exact (MK_COMB (@lem3288304 A s) (@lem3288305 A _33818 _33819 h1)). Qed.
Lemma lem3288308 (b : Prop) (a : Prop) : term154 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3288309 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : term155 A _33819 s _33818.
Proof. exact (@lem3288308 (s _33819) (s _33818)). Qed.
Lemma lem3288310 {A : Type'} (s : A -> Prop) (_33818 : A) (_33819 : A) (h1 : _33818 = _33819) : term156 A _33819 s _33818.
Proof. exact (@lem3288309 A _33819 s _33818 (@lem3288306 A s _33818 _33819 h1)). Qed.
Lemma lem3288311 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : term157 A _33819 s _33818.
Proof. exact (fun h0 : _33818 = _33819 => @lem3288310 A s _33818 _33819 h0). Qed.
Lemma lem3288313 (a : Prop) (b : Prop) : (a -> b) = (term158 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3288314 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : (term157 A _33819 s _33818) = (term159 A _33819 s _33818).
Proof. exact (@lem3288313 (_33818 = _33819) (term156 A _33819 s _33818)). Qed.
Lemma lem3288315 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : term159 A _33819 s _33818.
Proof. exact (EQ_MP (@lem3288314 A _33819 s _33818) (@lem3288311 A _33819 s _33818)). Qed.
Lemma lem3288319 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : s x'.
Proof. exact (proj1 (@lem3288186 A x s t x' h1)). Qed.
Lemma lem3288320 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term160 A s x'.
Proof. exact (fun h0 : term21 A s x' => @lem3288319 A x s t x' h1). Qed.
Lemma lem3288322 (p : Prop) : (term161 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3288323 {A : Type'} (s : A -> Prop) (x' : A) : (term160 A s x') = (s x').
Proof. exact (@lem3288322 (s x')). Qed.
Lemma lem3288324 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : s x'.
Proof. exact (EQ_MP (@lem3288323 A s x') (@lem3288320 A x s t x' h1)). Qed.
Lemma lem3288326 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term21 A s x.
Proof. exact (h1). Qed.
Lemma lem3288327 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term162 A s x.
Proof. exact (fun h0 : s x => @lem3288326 A s x h1). Qed.
Lemma lem3288329 (p : Prop) : (term163 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3288330 {A : Type'} (s : A -> Prop) (x : A) : (term162 A s x) = (term21 A s x).
Proof. exact (@lem3288329 (s x)). Qed.
Lemma lem3288331 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term21 A s x.
Proof. exact (EQ_MP (@lem3288330 A s x) (@lem3288327 A s x h1)). Qed.
Lemma lem3288333 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : s x'.
Proof. exact (proj1 (@lem3288186 A x s t x' h1)). Qed.
Lemma lem3288334 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term160 A s x'.
Proof. exact (fun h0 : term21 A s x' => @lem3288333 A x s t x' h1). Qed.
Lemma lem3288336 (p : Prop) : (term161 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3288337 {A : Type'} (s : A -> Prop) (x' : A) : (term160 A s x') = (s x').
Proof. exact (@lem3288336 (s x')). Qed.
Lemma lem3288338 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : s x'.
Proof. exact (EQ_MP (@lem3288337 A s x') (@lem3288334 A x s t x' h1)). Qed.
Lemma lem3288340 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3288341 {A : Type'} (s : A -> Prop) (_33818 : A) (_33819 : A) : (term159 A _33819 s _33818) = (term165 A s _33818 _33819).
Proof. exact (@lem3288340 (term156 A _33819 s _33818) (term166 A _33818 _33819)). Qed.
Lemma lem3288343 (a : Prop) (b : Prop) : (term167 a b) = (term168 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3288344 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : (term169 A _33819 s _33818) = (term170 A _33819 s _33818).
Proof. exact (@lem3288343 (s _33819) (term21 A s _33818)). Qed.
Lemma lem3288346 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3288347 {A : Type'} (s : A -> Prop) (_33818 : A) : (term171 A s _33818) = (s _33818).
Proof. exact (@lem3288346 (s _33818)). Qed.
Lemma lem3288348 {A : Type'} (s : A -> Prop) (_33819 : A) : (term172 A s _33819) = (term172 A s _33819).
Proof. exact (eq_refl (term172 A s _33819)). Qed.
Lemma lem3288349 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : (term170 A _33819 s _33818) = (term173 A _33819 s _33818).
Proof. exact (MK_COMB (@lem3288348 A s _33819) (@lem3288347 A s _33818)). Qed.
Lemma lem3288350 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : (term169 A _33819 s _33818) = (term173 A _33819 s _33818).
Proof. exact (TRANS (@lem3288344 A _33819 s _33818) (@lem3288349 A _33819 s _33818)). Qed.
Lemma lem3288351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3288352 {A : Type'} (_33819 : A) (s : A -> Prop) (_33818 : A) : (term174 A _33819 s _33818) = (term175 A _33819 s _33818).
Proof. exact (MK_COMB (@lem3288351) (@lem3288350 A _33819 s _33818)). Qed.
Lemma lem3288353 {A : Type'} (_33818 : A) (_33819 : A) : (term166 A _33818 _33819) = (term166 A _33818 _33819).
Proof. exact (eq_refl (term166 A _33818 _33819)). Qed.
Lemma lem3288354 {A : Type'} (s : A -> Prop) (_33818 : A) (_33819 : A) : (term165 A s _33818 _33819) = (term176 A s _33818 _33819).
Proof. exact (MK_COMB (@lem3288352 A _33819 s _33818) (@lem3288353 A _33818 _33819)). Qed.
Lemma lem3288355 {A : Type'} (s : A -> Prop) (_33818 : A) (_33819 : A) : (term159 A _33819 s _33818) = (term176 A s _33818 _33819).
Proof. exact (TRANS (@lem3288341 A s _33818 _33819) (@lem3288354 A s _33818 _33819)). Qed.
Lemma lem3288357 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : term173 A x s x'.
Proof. exact (conj (@lem3288331 A s x h1) (@lem3288338 A x s t x' h2)). Qed.
Lemma lem3288359 {A : Type'} (s : A -> Prop) (_33818 : A) (_33819 : A) : term176 A s _33818 _33819.
Proof. exact (EQ_MP (@lem3288355 A s _33818 _33819) (@lem3288315 A _33819 s _33818)). Qed.
Lemma lem3288360 {A : Type'} (s : A -> Prop) (_33818 : A) (_33819 : A) : term176 A s _33818 _33819.
Proof. exact (@lem3288359 A s _33818 _33819). Qed.
Lemma lem3288361 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : term176 A s x' x.
Proof. exact (@lem3288360 A s x' x). Qed.
Lemma lem3288364 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : term166 A x' x.
Proof. exact (@lem3288361 A s x' x (@lem3288357 A x s t x' h1 h2)). Qed.
Lemma lem3288365 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : term177 A x' x.
Proof. exact (fun h0 : x' = x => @lem3288364 A x s t x' h1 h2). Qed.
Lemma lem3288367 (p : Prop) : (term163 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3288368 {A : Type'} (x' : A) (x : A) : (term177 A x' x) = (term166 A x' x).
Proof. exact (@lem3288367 (x' = x)). Qed.
Lemma lem3288369 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : term166 A x' x.
Proof. exact (EQ_MP (@lem3288368 A x' x) (@lem3288365 A x s t x' h1 h2)). Qed.
Lemma lem3288375 (q : Prop) (p : Prop) (r : Prop) : (term178 p q r) = (term178 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3288376 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_33814 : A) : (term63 A s x t _33814) = (term179 A x s t _33814).
Proof. exact (@lem3288375 (_33814 = x) (term21 A s _33814) (t _33814)). Qed.
Lemma lem3288392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3288393 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33814 : A) : (term77 A s t _33814) = (term180 A t s _33814).
Proof. exact (@lem3288392 (t _33814) (term21 A s _33814)). Qed.
Lemma lem3288399 {A : Type'} (_33814 : A) (x : A) : (term27 A _33814 x) = (term27 A _33814 x).
Proof. exact (eq_refl (term27 A _33814 x)). Qed.
Lemma lem3288400 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_33814 : A) : (term179 A x s t _33814) = (term181 A x t s _33814).
Proof. exact (MK_COMB (@lem3288399 A _33814 x) (@lem3288393 A t s _33814)). Qed.
Lemma lem3288404 (q : Prop) (p : Prop) (r : Prop) : (term178 p q r) = (term178 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3288405 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_33814 : A) : (term181 A x t s _33814) = (term182 A t x s _33814).
Proof. exact (@lem3288404 (t _33814) (_33814 = x) (term21 A s _33814)). Qed.
Lemma lem3288423 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_33814 : A) : (term179 A x s t _33814) = (term182 A t x s _33814).
Proof. exact (TRANS (@lem3288400 A x t s _33814) (@lem3288405 A t x s _33814)). Qed.
Lemma lem3288424 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_33814 : A) : (term63 A s x t _33814) = (term182 A t x s _33814).
Proof. exact (TRANS (@lem3288376 A x s t _33814) (@lem3288423 A t x s _33814)). Qed.
Lemma lem3288425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3288426 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_33814 : A) : (term183 A s x t _33814) = (term184 A t x s _33814).
Proof. exact (MK_COMB (@lem3288425) (@lem3288424 A t x s _33814)). Qed.
Lemma lem3288440 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3288441 {A : Type'} (x : A) (s : A -> Prop) (_33814 : A) : (term185 A s _33814 x) = (term186 A x s _33814).
Proof. exact (@lem3288440 (_33814 = x) (term21 A s _33814)). Qed.
Lemma lem3288449 {A : Type'} (t : A -> Prop) (_33814 : A) : (term187 A t _33814) = (term187 A t _33814).
Proof. exact (eq_refl (term187 A t _33814)). Qed.
Lemma lem3288450 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_33814 : A) : (term188 A t s _33814 x) = (term182 A t x s _33814).
Proof. exact (MK_COMB (@lem3288449 A t _33814) (@lem3288441 A x s _33814)). Qed.
Lemma lem3288461 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_33814 : A) : ((term63 A s x t _33814) = (term188 A t s _33814 x)) = ((term182 A t x s _33814) = (term182 A t x s _33814)).
Proof. exact (MK_COMB (@lem3288426 A t x s _33814) (@lem3288450 A t x s _33814)). Qed.
Lemma lem3288463 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3288464 (x : Prop) : (x = x) = True.
Proof. exact (@lem3288463 Prop x). Qed.
Lemma lem3288465 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_33814 : A) : ((term182 A t x s _33814) = (term182 A t x s _33814)) = True.
Proof. exact (@lem3288464 (term182 A t x s _33814)). Qed.
Lemma lem3288466 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33814 : A) (x : A) : ((term63 A s x t _33814) = (term188 A t s _33814 x)) = True.
Proof. exact (TRANS (@lem3288461 A t x s _33814) (@lem3288465 A t x s _33814)). Qed.
Lemma lem3288467 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33814 : A) (x : A) : True = ((term63 A s x t _33814) = (term188 A t s _33814 x)).
Proof. exact (SYM (@lem3288466 A t s _33814 x)). Qed.
Lemma lem3288468 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33814 : A) (x : A) : (term63 A s x t _33814) = (term188 A t s _33814 x).
Proof. exact (EQ_MP (@lem3288467 A t s _33814 x) (@lem0)). Qed.
Lemma lem3288469 {A : Type'} (_33814 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term188 A t s _33814 x.
Proof. exact (EQ_MP (@lem3288468 A t s _33814 x) (@lem3288273 A _33814 x s t x' h1)). Qed.
Lemma lem3288471 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3288472 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_33814 : A) : (term188 A t s _33814 x) = (term189 A s x t _33814).
Proof. exact (@lem3288471 (term185 A s _33814 x) (t _33814)). Qed.
Lemma lem3288474 (a : Prop) (b : Prop) : (term167 a b) = (term168 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3288475 {A : Type'} (s : A -> Prop) (_33814 : A) (x : A) : (term190 A s _33814 x) = (term191 A s _33814 x).
Proof. exact (@lem3288474 (term21 A s _33814) (_33814 = x)). Qed.
Lemma lem3288477 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3288478 {A : Type'} (s : A -> Prop) (_33814 : A) : (term171 A s _33814) = (s _33814).
Proof. exact (@lem3288477 (s _33814)). Qed.
Lemma lem3288479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3288480 {A : Type'} (s : A -> Prop) (_33814 : A) : (term192 A s _33814) = (term59 A s _33814).
Proof. exact (MK_COMB (@lem3288479) (@lem3288478 A s _33814)). Qed.
Lemma lem3288481 {A : Type'} (_33814 : A) (x : A) : (term166 A _33814 x) = (term166 A _33814 x).
Proof. exact (eq_refl (term166 A _33814 x)). Qed.
Lemma lem3288482 {A : Type'} (s : A -> Prop) (_33814 : A) (x : A) : (term191 A s _33814 x) = (term193 A s _33814 x).
Proof. exact (MK_COMB (@lem3288480 A s _33814) (@lem3288481 A _33814 x)). Qed.
Lemma lem3288483 {A : Type'} (s : A -> Prop) (_33814 : A) (x : A) : (term190 A s _33814 x) = (term193 A s _33814 x).
Proof. exact (TRANS (@lem3288475 A s _33814 x) (@lem3288482 A s _33814 x)). Qed.
Lemma lem3288484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3288485 {A : Type'} (s : A -> Prop) (_33814 : A) (x : A) : (term194 A s _33814 x) = (term195 A s _33814 x).
Proof. exact (MK_COMB (@lem3288484) (@lem3288483 A s _33814 x)). Qed.
Lemma lem3288486 {A : Type'} (t : A -> Prop) (_33814 : A) : (t _33814) = (t _33814).
Proof. exact (eq_refl (t _33814)). Qed.
Lemma lem3288487 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_33814 : A) : (term189 A s x t _33814) = (term196 A s x t _33814).
Proof. exact (MK_COMB (@lem3288485 A s _33814 x) (@lem3288486 A t _33814)). Qed.
Lemma lem3288488 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_33814 : A) : (term188 A t s _33814 x) = (term196 A s x t _33814).
Proof. exact (TRANS (@lem3288472 A s x t _33814) (@lem3288487 A s x t _33814)). Qed.
Lemma lem3288490 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : term193 A s x' x.
Proof. exact (conj (@lem3288324 A x s t x' h2) (@lem3288369 A x s t x' h1 h2)). Qed.
Lemma lem3288492 {A : Type'} (_33814 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term196 A s x t _33814.
Proof. exact (EQ_MP (@lem3288488 A s x t _33814) (@lem3288469 A _33814 x s t x' h1)). Qed.
Lemma lem3288493 {A : Type'} (_33814 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term196 A s x t _33814.
Proof. exact (@lem3288492 A _33814 x s t x' h1). Qed.
Lemma lem3288494 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term196 A s x t x'.
Proof. exact (@lem3288493 A x' x s t x' h1). Qed.
Lemma lem3288497 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : t x'.
Proof. exact (@lem3288494 A x s t x' h2 (@lem3288490 A x s t x' h1 h2)). Qed.
Lemma lem3288498 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : term160 A t x'.
Proof. exact (fun h0 : term21 A t x' => @lem3288497 A x s t x' h1 h2). Qed.
Lemma lem3288500 (p : Prop) : (term161 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3288501 {A : Type'} (t : A -> Prop) (x' : A) : (term160 A t x') = (t x').
Proof. exact (@lem3288500 (t x')). Qed.
Lemma lem3288502 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : t x'.
Proof. exact (EQ_MP (@lem3288501 A t x') (@lem3288498 A x s t x' h1 h2)). Qed.
Lemma lem3288505 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3288507 {A : Type'} (t : A -> Prop) (x' : A) : (term21 A t x') = (term197 A t x').
Proof. exact (@lem3288505 (t x')). Qed.
Lemma lem3288510 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A x s t x') : term197 A t x'.
Proof. exact (EQ_MP (@lem3288507 A t x') (@lem3288277 A x s t x' h1)). Qed.
Lemma lem3288513 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : False.
Proof. exact (@lem3288510 A x s t x' h2 (@lem3288502 A x s t x' h1 h2)). Qed.
Lemma lem3288514 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : term198.
Proof. exact (fun h0 : ~ False => @lem3288513 A x s t x' h1 h2). Qed.
Lemma lem3288516 (p : Prop) : (term161 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3288517 : term198 = False.
Proof. exact (@lem3288516 False). Qed.
Lemma lem3288518 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : False.
Proof. exact (EQ_MP (@lem3288517) (@lem3288514 A x s t x' h1 h2)). Qed.
Lemma lem3288546 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : s x'.
Proof. exact (proj1 (@lem3288191 A x x' s t h1)). Qed.
Lemma lem3288547 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term160 A s x'.
Proof. exact (fun h0 : term21 A s x' => @lem3288546 A x x' s t h1). Qed.
Lemma lem3288549 (p : Prop) : (term161 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3288550 {A : Type'} (s : A -> Prop) (x' : A) : (term160 A s x') = (s x').
Proof. exact (@lem3288549 (s x')). Qed.
Lemma lem3288551 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : s x'.
Proof. exact (EQ_MP (@lem3288550 A s x') (@lem3288547 A x x' s t h1)). Qed.
Lemma lem3288557 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3288558 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : (term77 A s t _33815) = (term180 A t s _33815).
Proof. exact (@lem3288557 (t _33815) (term21 A s _33815)). Qed.
Lemma lem3288564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3288565 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : (term199 A s t _33815) = (term200 A t s _33815).
Proof. exact (MK_COMB (@lem3288564) (@lem3288558 A t s _33815)). Qed.
Lemma lem3288571 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : (term180 A t s _33815) = (term180 A t s _33815).
Proof. exact (eq_refl (term180 A t s _33815)). Qed.
Lemma lem3288572 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : ((term77 A s t _33815) = (term180 A t s _33815)) = ((term180 A t s _33815) = (term180 A t s _33815)).
Proof. exact (MK_COMB (@lem3288565 A t s _33815) (@lem3288571 A t s _33815)). Qed.
Lemma lem3288574 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3288575 (x : Prop) : (x = x) = True.
Proof. exact (@lem3288574 Prop x). Qed.
Lemma lem3288576 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : ((term180 A t s _33815) = (term180 A t s _33815)) = True.
Proof. exact (@lem3288575 (term180 A t s _33815)). Qed.
Lemma lem3288577 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : ((term77 A s t _33815) = (term180 A t s _33815)) = True.
Proof. exact (TRANS (@lem3288572 A t s _33815) (@lem3288576 A t s _33815)). Qed.
Lemma lem3288578 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : True = ((term77 A s t _33815) = (term180 A t s _33815)).
Proof. exact (SYM (@lem3288577 A t s _33815)). Qed.
Lemma lem3288579 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33815 : A) : (term77 A s t _33815) = (term180 A t s _33815).
Proof. exact (EQ_MP (@lem3288578 A t s _33815) (@lem0)). Qed.
Lemma lem3288580 {A : Type'} (_33815 : A) (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term180 A t s _33815.
Proof. exact (EQ_MP (@lem3288579 A t s _33815) (@lem3288285 A _33815 x x' s t h1)). Qed.
Lemma lem3288582 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3288583 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33815 : A) : (term180 A t s _33815) = (term201 A s t _33815).
Proof. exact (@lem3288582 (term21 A s _33815) (t _33815)). Qed.
Lemma lem3288585 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3288586 {A : Type'} (s : A -> Prop) (_33815 : A) : (term171 A s _33815) = (s _33815).
Proof. exact (@lem3288585 (s _33815)). Qed.
Lemma lem3288587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3288588 {A : Type'} (s : A -> Prop) (_33815 : A) : (term202 A s _33815) = (term24 A s _33815).
Proof. exact (MK_COMB (@lem3288587) (@lem3288586 A s _33815)). Qed.
Lemma lem3288589 {A : Type'} (t : A -> Prop) (_33815 : A) : (t _33815) = (t _33815).
Proof. exact (eq_refl (t _33815)). Qed.
Lemma lem3288590 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33815 : A) : (term201 A s t _33815) = (term36 A s t _33815).
Proof. exact (MK_COMB (@lem3288588 A s _33815) (@lem3288589 A t _33815)). Qed.
Lemma lem3288591 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33815 : A) : (term180 A t s _33815) = (term36 A s t _33815).
Proof. exact (TRANS (@lem3288583 A s t _33815) (@lem3288590 A s t _33815)). Qed.
Lemma lem3288594 {A : Type'} (_33815 : A) (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term36 A s t _33815.
Proof. exact (EQ_MP (@lem3288591 A s t _33815) (@lem3288580 A _33815 x x' s t h1)). Qed.
Lemma lem3288595 {A : Type'} (_33815 : A) (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term36 A s t _33815.
Proof. exact (@lem3288594 A _33815 x x' s t h1). Qed.
Lemma lem3288596 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term36 A s t x'.
Proof. exact (@lem3288595 A x' x x' s t h1). Qed.
Lemma lem3288599 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : t x'.
Proof. exact (@lem3288596 A x x' s t h1 (@lem3288551 A x x' s t h1)). Qed.
Lemma lem3288600 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term160 A t x'.
Proof. exact (fun h0 : term21 A t x' => @lem3288599 A x x' s t h1). Qed.
Lemma lem3288602 (p : Prop) : (term161 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3288603 {A : Type'} (t : A -> Prop) (x' : A) : (term160 A t x') = (t x').
Proof. exact (@lem3288602 (t x')). Qed.
Lemma lem3288604 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : t x'.
Proof. exact (EQ_MP (@lem3288603 A t x') (@lem3288600 A x x' s t h1)). Qed.
Lemma lem3288607 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3288609 {A : Type'} (t : A -> Prop) (x' : A) : (term21 A t x') = (term197 A t x').
Proof. exact (@lem3288607 (t x')). Qed.
Lemma lem3288612 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term197 A t x'.
Proof. exact (EQ_MP (@lem3288609 A t x') (@lem3288291 A x x' s t h1)). Qed.
Lemma lem3288615 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : False.
Proof. exact (@lem3288612 A x x' s t h1 (@lem3288604 A x x' s t h1)). Qed.
Lemma lem3288616 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : term198.
Proof. exact (fun h0 : ~ False => @lem3288615 A x x' s t h1). Qed.
Lemma lem3288618 (p : Prop) : (term161 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3288619 : term198 = False.
Proof. exact (@lem3288618 False). Qed.
Lemma lem3288620 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term127 A x x' s t) : False.
Proof. exact (EQ_MP (@lem3288619) (@lem3288616 A x x' s t h1)). Qed.
Lemma lem3288621 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : (term21 A s x) = False.
Proof. exact (prop_ext (fun h3 : term21 A s x => @lem3288518 A x s t x' h1 h2) (fun h3 : False => @lem3288263 A s x h1)). Qed.
Lemma lem3288622 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : False.
Proof. exact (EQ_MP (@lem3288621 A x s t x' h1 h2) (@lem3288263 A s x h1)). Qed.
Lemma lem3288623 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : (term21 A s x) = False.
Proof. exact (prop_ext (fun h3 : term21 A s x => @lem3288622 A x s t x' h1 h2) (fun h3 : False => @lem3288199 A s x h1)). Qed.
Lemma lem3288624 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : False.
Proof. exact (EQ_MP (@lem3288623 A x s t x' h1 h2) (@lem3288199 A s x h1)). Qed.
Lemma lem3288625 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : (term21 A s x) = False.
Proof. exact (prop_ext (fun h3 : term21 A s x => @lem3288624 A x s t x' h1 h2) (fun h3 : False => @lem3288199 A s x h1)). Qed.
Lemma lem3288626 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term21 A s x) (h2 : term109 A x s t x') : False.
Proof. exact (EQ_MP (@lem3288625 A x s t x' h1 h2) (@lem3288199 A s x h1)). Qed.
Lemma lem3288627 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term148 A x x' s t) : False.
Proof. exact (or_elim (@lem3288183 A x x' s t h2) (fun h0 : term109 A x s t x' => @lem3288626 A x s t x' h1 h0) (fun h0 : term127 A x x' s t => @lem3288620 A x x' s t h0)). Qed.
Lemma lem3288628 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term148 A x x' s t) : (term148 A x x' s t) = False.
Proof. exact (prop_ext (fun h3 : term148 A x x' s t => @lem3288627 A x x' s t h1 h2) (fun h3 : False => @lem3288183 A x x' s t h2)). Qed.
Lemma lem3288629 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term148 A x x' s t) : False.
Proof. exact (EQ_MP (@lem3288628 A x x' s t h1 h2) (@lem3288183 A x x' s t h2)). Qed.
Lemma lem3288630 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term148 A x x' s t) : (term21 A s x) = False.
Proof. exact (prop_ext (fun h3 : term21 A s x => @lem3288629 A x x' s t h1 h2) (fun h3 : False => @lem3288105 A s x h1)). Qed.
Lemma lem3288631 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term148 A x x' s t) : False.
Proof. exact (EQ_MP (@lem3288630 A x x' s t h1 h2) (@lem3288105 A s x h1)). Qed.
Lemma lem3288632 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term56 A x s t) : False.
Proof. exact (ex_elim (@lem3288098 A x s t h2) (fun x' : A => fun h0 : term150 A x s t x' => @lem3288631 A x x' s t h1 h0)). Qed.
Lemma lem3288633 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term56 A x s t) : (term21 A s x) = False.
Proof. exact (prop_ext (fun h3 : term21 A s x => @lem3288632 A x s t h1 h2) (fun h3 : False => @lem3287808 A s x h1)). Qed.
Lemma lem3288634 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term56 A x s t) : False.
Proof. exact (EQ_MP (@lem3288633 A x s t h1 h2) (@lem3287808 A s x h1)). Qed.
Lemma lem3288635 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term56 A x s t) : (term56 A x s t) = False.
Proof. exact (prop_ext (fun h3 : term56 A x s t => @lem3288634 A x s t h1 h2) (fun h3 : False => @lem3287802 A x s t h2)). Qed.
Lemma lem3288636 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term21 A s x) (h2 : term56 A x s t) : False.
Proof. exact (EQ_MP (@lem3288635 A x s t h1 h2) (@lem3287802 A x s t h2)). Qed.
Lemma lem3288637 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term21 A s x) : term55 A x s t.
Proof. exact (fun h0 : term56 A x s t => @lem3288636 A x s t h1 h0). Qed.
Lemma lem3288638 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term21 A s x) : (term33 A s x t) = (term39 A s t).
Proof. exact (EQ_MP (@lem3287801 A x s t) (@lem3288637 A t s x h1)). Qed.
Lemma lem3288643 {A : Type'} (s : A -> Prop) (x : A) (h1 : term21 A s x) : term41 A x s.
Proof. exact (fun t : A -> Prop => @lem3288638 A t s x h1). Qed.
Lemma lem3288644 {A : Type'} (x : A) (s : A -> Prop) : term42 A x s.
Proof. exact (fun h0 : term21 A s x => @lem3288643 A s x h0). Qed.
Lemma lem3288649 {A : Type'} (x : A) : term44 A x.
Proof. exact (fun s : A -> Prop => @lem3288644 A x s). Qed.
Lemma lem3288654 {A : Type'} : term46 A.
Proof. exact (fun x : A => @lem3288649 A x). Qed.
Lemma lem3288655 {A : Type'} : term48 A.
Proof. exact (EQ_MP (@lem3287796 A) (@lem3288654 A)). Qed.
Lemma lem3288657 {A : Type'} : term48 A.
Proof. exact (@lem3287677 A (@lem3288655 A)). Qed.
Lemma lem3288658 {A : Type'} (h1 : term49 A) : False.
Proof. exact (@lem3288657 A (@lem3287661 A h1)). Qed.
Lemma lem3288659 {A : Type'} (h1 : term49 A) : (term49 A) = False.
Proof. exact (prop_ext (fun h2 : term49 A => @lem3288658 A h1) (fun h2 : False => @lem3287661 A h1)). Qed.
Lemma lem3288660 {A : Type'} (h1 : term49 A) : False.
Proof. exact (EQ_MP (@lem3288659 A h1) (@lem3287661 A h1)). Qed.
Lemma lem3288661 {A : Type'} : term48 A.
Proof. exact (fun h0 : term49 A => @lem3288660 A h0). Qed.
Lemma lem3288662 {A : Type'} : term46 A.
Proof. exact (EQ_MP (@lem3287660 A) (@lem3288661 A)). Qed.
Lemma lem3288663 {A : Type'} : term19 A.
Proof. exact (EQ_MP (@lem3287656 A) (@lem3288662 A)). Qed.
Lemma lem3288664 {A : Type'} : term18 A.
Proof. exact (EQ_MP (@lem3287537 A) (@lem3288663 A)). Qed.
