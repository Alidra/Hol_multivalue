Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CARD_LE_UNION_term_abbrevs.
Require Import CARD_UNION_LE_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_UNION_spec.
Require Import LE_ADD2_spec.
Require Import LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm69_spec.
Lemma lem3924615 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3924616 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3924617 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3924616 t1) (@lem3924615 t1)). Qed.
Lemma lem3924618 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3924617 t1 t2). Qed.
Lemma lem3924619 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3924620 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3924619 t1 t2) (@lem3924618 t1 t2)). Qed.
Lemma lem3924621 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3924620 t1 t2 t3). Qed.
Lemma lem3924622 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3924623 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3924622 t1 t2 t3) (@lem3924621 t1 t2 t3)). Qed.
Lemma lem3924624 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3924623 t1 t2 t3)). Qed.
Lemma lem3924626 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3924627 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem3924626 (term8 A)). Qed.
Lemma lem3924628 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3924627 A)). Qed.
Lemma lem3924629 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3924630 {A : Type'} : term11 A.
Proof. exact (@lem3606772 A). Qed.
Lemma lem3924632 {A : Type'} : term12 A.
Proof. exact (@lem3924614 A). Qed.
Lemma lem3924637 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3924638 {A : Type'} : term14 A.
Proof. exact (fun h0 : term13 A => @lem3924637 A h0). Qed.
Lemma lem3924639 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3924640 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3924641 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3924639 A h2 (@lem3924640 A h1)). Qed.
Lemma lem3924642 {A : Type'} (h1 : term13 A) : term15 A.
Proof. exact (fun h0 : term14 A => @lem3924641 A h1 h0). Qed.
Lemma lem3924643 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3924644 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3924642 A h1 (@lem3924643 A h2)). Qed.
Lemma lem3924645 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (fun h0 : term13 A => @lem3924644 A h0 h1). Qed.
Lemma lem3924646 {A : Type'} : term16 A.
Proof. exact (fun h0 : term14 A => @lem3924645 A h0). Qed.
Lemma lem3924649 {A : Type'} : term14 A.
Proof. exact (@lem3924646 A (@lem3924638 A)). Qed.
Lemma lem3924650 {A : Type'} : term14 A.
Proof. exact (@lem3924649 A). Qed.
Lemma lem3924734 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3924735 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem3924734 (term11 A)). Qed.
Lemma lem3924746 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem3924747 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem3924746 A) (@lem3924735 A)). Qed.
Lemma lem3924750 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem3924751 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem3924750) (@lem3924747 A)). Qed.
Lemma lem3924754 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem3924755 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem3924754) (@lem3924751 A)). Qed.
Lemma lem3924758 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem3924765 {A : Type'} : (term13 A) = (term29 A).
Proof. exact (MK_COMB (@lem3924758 A) (@lem3924755 A)). Qed.
Lemma lem3924774 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term30 A s t) = (term31 A s t)) = ((term30 A s t) = (term31 A s t)).
Proof. exact (eq_refl ((term30 A s t) = (term31 A s t))). Qed.
Lemma lem3924775 {A : Type'} (s : A -> Prop) : (term32 A s) = (term32 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3924774 A s t)). Qed.
Lemma lem3924776 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924777 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem3924776 A) (@lem3924775 A s)). Qed.
Lemma lem3924778 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3924777 A s)). Qed.
Lemma lem3924779 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924780 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3924779 A) (@lem3924778 A)). Qed.
Lemma lem3924781 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3924782 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem3924781) (@lem3924780 A)). Qed.
Lemma lem3924791 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (eq_refl (term35 A s t)). Qed.
Lemma lem3924792 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3924791 A s t)). Qed.
Lemma lem3924793 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924794 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem3924793 A) (@lem3924792 A s)). Qed.
Lemma lem3924795 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3924794 A s)). Qed.
Lemma lem3924796 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924797 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3924796 A) (@lem3924795 A)). Qed.
Lemma lem3924798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3924799 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem3924798) (@lem3924797 A)). Qed.
Lemma lem3924800 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem3924799 A) (@lem3924782 A)). Qed.
Lemma lem3924809 (m : nat) (n : nat) (p : nat) (q : nat) : (term39 m n p q) = (term39 m n p q).
Proof. exact (eq_refl (term39 m n p q)). Qed.
Lemma lem3924810 (m : nat) (n : nat) (p : nat) : (term40 m n p) = (term40 m n p).
Proof. exact (fun_ext (fun q : nat => @lem3924809 m n p q)). Qed.
Lemma lem3924811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924812 (m : nat) (n : nat) (p : nat) : (term41 m n p) = (term41 m n p).
Proof. exact (MK_COMB (@lem3924811) (@lem3924810 m n p)). Qed.
Lemma lem3924813 (m : nat) (n : nat) : (term42 m n) = (term42 m n).
Proof. exact (fun_ext (fun p : nat => @lem3924812 m n p)). Qed.
Lemma lem3924814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924815 (m : nat) (n : nat) : (term43 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem3924814) (@lem3924813 m n)). Qed.
Lemma lem3924816 (m : nat) : (term44 m) = (term44 m).
Proof. exact (fun_ext (fun n : nat => @lem3924815 m n)). Qed.
Lemma lem3924817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924818 (m : nat) : (term45 m) = (term45 m).
Proof. exact (MK_COMB (@lem3924817) (@lem3924816 m)). Qed.
Lemma lem3924819 : term46 = term46.
Proof. exact (fun_ext (fun m : nat => @lem3924818 m)). Qed.
Lemma lem3924820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924821 : term47 = term47.
Proof. exact (MK_COMB (@lem3924820) (@lem3924819)). Qed.
Lemma lem3924822 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3924823 : term22 = term22.
Proof. exact (MK_COMB (@lem3924822) (@lem3924821)). Qed.
Lemma lem3924824 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem3924823) (@lem3924800 A)). Qed.
Lemma lem3924833 (n : nat) (m : nat) (p : nat) : (term48 n m p) = (term48 n m p).
Proof. exact (eq_refl (term48 n m p)). Qed.
Lemma lem3924834 (n : nat) (m : nat) : (term49 n m) = (term49 n m).
Proof. exact (fun_ext (fun p : nat => @lem3924833 n m p)). Qed.
Lemma lem3924835 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924836 (n : nat) (m : nat) : (term50 n m) = (term50 n m).
Proof. exact (MK_COMB (@lem3924835) (@lem3924834 n m)). Qed.
Lemma lem3924837 (m : nat) : (term51 m) = (term51 m).
Proof. exact (fun_ext (fun n : nat => @lem3924836 n m)). Qed.
Lemma lem3924838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924839 (m : nat) : (term52 m) = (term52 m).
Proof. exact (MK_COMB (@lem3924838) (@lem3924837 m)). Qed.
Lemma lem3924840 : term53 = term53.
Proof. exact (fun_ext (fun m : nat => @lem3924839 m)). Qed.
Lemma lem3924841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924842 : term54 = term54.
Proof. exact (MK_COMB (@lem3924841) (@lem3924840)). Qed.
Lemma lem3924843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3924844 : term25 = term25.
Proof. exact (MK_COMB (@lem3924843) (@lem3924842)). Qed.
Lemma lem3924845 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem3924844) (@lem3924824 A)). Qed.
Lemma lem3924866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term55 A s t m n) = (term55 A s t m n).
Proof. exact (eq_refl (term55 A s t m n)). Qed.
Lemma lem3924867 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term56 A s t m) = (term56 A s t m).
Proof. exact (fun_ext (fun n : nat => @lem3924866 A s t m n)). Qed.
Lemma lem3924868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term57 A s t m) = (term57 A s t m).
Proof. exact (MK_COMB (@lem3924868) (@lem3924867 A s t m)). Qed.
Lemma lem3924870 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (fun_ext (fun m : nat => @lem3924869 A s t m)). Qed.
Lemma lem3924871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3924872 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term59 A s t).
Proof. exact (MK_COMB (@lem3924871) (@lem3924870 A s t)). Qed.
Lemma lem3924873 {A : Type'} (s : A -> Prop) : (term60 A s) = (term60 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3924872 A s t)). Qed.
Lemma lem3924874 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924875 {A : Type'} (s : A -> Prop) : (term61 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3924874 A) (@lem3924873 A s)). Qed.
Lemma lem3924876 {A : Type'} : (term62 A) = (term62 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3924875 A s)). Qed.
Lemma lem3924877 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924878 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem3924877 A) (@lem3924876 A)). Qed.
Lemma lem3924879 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3924880 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem3924879) (@lem3924878 A)). Qed.
Lemma lem3924881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3924882 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3924881) (@lem3924880 A)). Qed.
Lemma lem3924883 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem3924882 A) (@lem3924845 A)). Qed.
Lemma lem3925008 {A : Type'} : (term13 A) = (term29 A).
Proof. exact (TRANS (@lem3924765 A) (@lem3924883 A)). Qed.
Lemma lem3925009 {A : Type'} : (term29 A) = (term13 A).
Proof. exact (SYM (@lem3925008 A)). Qed.
Lemma lem3925010 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3925011 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem3925012 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem3925013 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem3925014 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem3925034 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term63 A s t m n) = (term64 A s t m n).
Proof. exact (@lem17045 (term30 A s t) (term65 A s t m n)). Qed.
Lemma lem3925036 {A : Type'} (s : A -> Prop) (m : nat) (t : A -> Prop) (n : nat) : (term66 A s m t n) = (term66 A s m t n).
Proof. exact (eq_refl (term66 A s m t n)). Qed.
Lemma lem3925037 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term67 A s t m n) = (term68 A s t m n).
Proof. exact (MK_COMB (@lem3925036 A s m t n) (@lem3925034 A s t m n)). Qed.
Lemma lem3925038 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term69 A s t m n) = (term67 A s t m n).
Proof. exact (@lem17362 (term70 A s m t n) (term71 A s t m n)). Qed.
Lemma lem3925039 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term69 A s t m n) = (term68 A s t m n).
Proof. exact (TRANS (@lem3925038 A s t m n) (@lem3925037 A s t m n)). Qed.
Lemma lem3925040 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3925041 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term74 A s t m) = (term75 A s t m).
Proof. exact (@lem3925040 (term56 A s t m)). Qed.
Lemma lem3925042 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term76 A s t m n) = (term55 A s t m n).
Proof. exact (eq_refl (term76 A s t m n)). Qed.
Lemma lem3925043 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3925044 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term77 A s t m n) = (term69 A s t m n).
Proof. exact (MK_COMB (@lem3925043) (@lem3925042 A s t m n)). Qed.
Lemma lem3925045 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term77 A s t m n) = (term68 A s t m n).
Proof. exact (TRANS (@lem3925044 A s t m n) (@lem3925039 A s t m n)). Qed.
Lemma lem3925046 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term78 A s t m) = (term79 A s t m).
Proof. exact (fun_ext (fun n : nat => @lem3925045 A s t m n)). Qed.
Lemma lem3925047 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3925048 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term75 A s t m) = (term80 A s t m).
Proof. exact (MK_COMB (@lem3925047) (@lem3925046 A s t m)). Qed.
Lemma lem3925049 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term74 A s t m) = (term80 A s t m).
Proof. exact (TRANS (@lem3925041 A s t m) (@lem3925048 A s t m)). Qed.
Lemma lem3925050 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3925051 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term82 A s t).
Proof. exact (@lem3925050 (term58 A s t)). Qed.
Lemma lem3925052 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term83 A s t m) = (term57 A s t m).
Proof. exact (eq_refl (term83 A s t m)). Qed.
Lemma lem3925053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3925054 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term84 A s t m) = (term74 A s t m).
Proof. exact (MK_COMB (@lem3925053) (@lem3925052 A s t m)). Qed.
Lemma lem3925055 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) : (term84 A s t m) = (term80 A s t m).
Proof. exact (TRANS (@lem3925054 A s t m) (@lem3925049 A s t m)). Qed.
Lemma lem3925056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun m : nat => @lem3925055 A s t m)). Qed.
Lemma lem3925057 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3925058 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3925057) (@lem3925056 A s t)). Qed.
Lemma lem3925059 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term87 A s t).
Proof. exact (TRANS (@lem3925051 A s t) (@lem3925058 A s t)). Qed.
Lemma lem3925060 {A : Type'} (P : type686 A) : (term88 A P) = (term89 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3925061 {A : Type'} (s : A -> Prop) : (term90 A s) = (term91 A s).
Proof. exact (@lem3925060 A (term60 A s)). Qed.
Lemma lem3925062 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term59 A s t).
Proof. exact (eq_refl (term92 A s t)). Qed.
Lemma lem3925063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3925064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term81 A s t).
Proof. exact (MK_COMB (@lem3925063) (@lem3925062 A s t)). Qed.
Lemma lem3925065 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term87 A s t).
Proof. exact (TRANS (@lem3925064 A s t) (@lem3925059 A s t)). Qed.
Lemma lem3925066 {A : Type'} (s : A -> Prop) : (term94 A s) = (term95 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925065 A s t)). Qed.
Lemma lem3925067 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3925068 {A : Type'} (s : A -> Prop) : (term91 A s) = (term96 A s).
Proof. exact (MK_COMB (@lem3925067 A) (@lem3925066 A s)). Qed.
Lemma lem3925069 {A : Type'} (s : A -> Prop) : (term90 A s) = (term96 A s).
Proof. exact (TRANS (@lem3925061 A s) (@lem3925068 A s)). Qed.
Lemma lem3925070 {A : Type'} (P : type686 A) : (term88 A P) = (term89 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3925071 {A : Type'} : (term10 A) = (term97 A).
Proof. exact (@lem3925070 A (term62 A)). Qed.
Lemma lem3925072 {A : Type'} (s : A -> Prop) : (term98 A s) = (term61 A s).
Proof. exact (eq_refl (term98 A s)). Qed.
Lemma lem3925073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3925074 {A : Type'} (s : A -> Prop) : (term99 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem3925073) (@lem3925072 A s)). Qed.
Lemma lem3925075 {A : Type'} (s : A -> Prop) : (term99 A s) = (term96 A s).
Proof. exact (TRANS (@lem3925074 A s) (@lem3925069 A s)). Qed.
Lemma lem3925076 {A : Type'} : (term100 A) = (term101 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925075 A s)). Qed.
Lemma lem3925077 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3925078 {A : Type'} : (term97 A) = (term102 A).
Proof. exact (MK_COMB (@lem3925077 A) (@lem3925076 A)). Qed.
Lemma lem3925143 {A : Type'} : (term10 A) = (term102 A).
Proof. exact (TRANS (@lem3925071 A) (@lem3925078 A)). Qed.
Lemma lem3925144 {A : Type'} (h1 : term10 A) : term102 A.
Proof. exact (EQ_MP (@lem3925143 A) (@lem3925010 A h1)). Qed.
Lemma lem3925151 (m : nat) (n : nat) (p : nat) : (term103 m n p) = (term104 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem3925152 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem3925153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3925154 (m : nat) (n : nat) (p : nat) : (term105 m n p) = (term106 m n p).
Proof. exact (MK_COMB (@lem3925153) (@lem3925151 m n p)). Qed.
Lemma lem3925155 (n : nat) (m : nat) (p : nat) : (term107 n m p) = (term108 n m p).
Proof. exact (MK_COMB (@lem3925154 m n p) (@lem3925152 m p)). Qed.
Lemma lem3925156 (n : nat) (m : nat) (p : nat) : (term48 n m p) = (term107 n m p).
Proof. exact (@lem17265 (term109 m n p) (Peano.le m p)). Qed.
Lemma lem3925157 (n : nat) (m : nat) (p : nat) : (term48 n m p) = (term108 n m p).
Proof. exact (TRANS (@lem3925156 n m p) (@lem3925155 n m p)). Qed.
Lemma lem3925158 (n : nat) (m : nat) : (term49 n m) = (term110 n m).
Proof. exact (fun_ext (fun p : nat => @lem3925157 n m p)). Qed.
Lemma lem3925159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925160 (n : nat) (m : nat) : (term50 n m) = (term111 n m).
Proof. exact (MK_COMB (@lem3925159) (@lem3925158 n m)). Qed.
Lemma lem3925161 (m : nat) : (term51 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem3925160 n m)). Qed.
Lemma lem3925162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925163 (m : nat) : (term52 m) = (term113 m).
Proof. exact (MK_COMB (@lem3925162) (@lem3925161 m)). Qed.
Lemma lem3925164 : term53 = term114.
Proof. exact (fun_ext (fun m : nat => @lem3925163 m)). Qed.
Lemma lem3925165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925226 : term54 = term115.
Proof. exact (MK_COMB (@lem3925165) (@lem3925164)). Qed.
Lemma lem3925227 (h1 : term54) : term115.
Proof. exact (EQ_MP (@lem3925226) (@lem3925011 h1)). Qed.
Lemma lem3925234 (m : nat) (p : nat) (n : nat) (q : nat) : (term116 m p n q) = (term117 m p n q).
Proof. exact (@lem17045 (Peano.le m p) (Peano.le n q)). Qed.
Lemma lem3925235 (m : nat) (n : nat) (p : nat) (q : nat) : (term118 m n p q) = (term118 m n p q).
Proof. exact (eq_refl (term118 m n p q)). Qed.
Lemma lem3925236 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3925237 (m : nat) (p : nat) (n : nat) (q : nat) : (term119 m p n q) = (term120 m p n q).
Proof. exact (MK_COMB (@lem3925236) (@lem3925234 m p n q)). Qed.
Lemma lem3925238 (m : nat) (n : nat) (p : nat) (q : nat) : (term121 m n p q) = (term122 m n p q).
Proof. exact (MK_COMB (@lem3925237 m p n q) (@lem3925235 m n p q)). Qed.
Lemma lem3925239 (m : nat) (n : nat) (p : nat) (q : nat) : (term39 m n p q) = (term121 m n p q).
Proof. exact (@lem17265 (term123 m p n q) (term118 m n p q)). Qed.
Lemma lem3925240 (m : nat) (n : nat) (p : nat) (q : nat) : (term39 m n p q) = (term122 m n p q).
Proof. exact (TRANS (@lem3925239 m n p q) (@lem3925238 m n p q)). Qed.
Lemma lem3925241 (m : nat) (n : nat) (p : nat) : (term40 m n p) = (term124 m n p).
Proof. exact (fun_ext (fun q : nat => @lem3925240 m n p q)). Qed.
Lemma lem3925242 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925243 (m : nat) (n : nat) (p : nat) : (term41 m n p) = (term125 m n p).
Proof. exact (MK_COMB (@lem3925242) (@lem3925241 m n p)). Qed.
Lemma lem3925244 (m : nat) (n : nat) : (term42 m n) = (term126 m n).
Proof. exact (fun_ext (fun p : nat => @lem3925243 m n p)). Qed.
Lemma lem3925245 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925246 (m : nat) (n : nat) : (term43 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem3925245) (@lem3925244 m n)). Qed.
Lemma lem3925247 (m : nat) : (term44 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem3925246 m n)). Qed.
Lemma lem3925248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925249 (m : nat) : (term45 m) = (term129 m).
Proof. exact (MK_COMB (@lem3925248) (@lem3925247 m)). Qed.
Lemma lem3925250 : term46 = term130.
Proof. exact (fun_ext (fun m : nat => @lem3925249 m)). Qed.
Lemma lem3925251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925316 : term47 = term131.
Proof. exact (MK_COMB (@lem3925251) (@lem3925250)). Qed.
Lemma lem3925317 (h1 : term47) : term131.
Proof. exact (EQ_MP (@lem3925316) (@lem3925012 h1)). Qed.
Lemma lem3925324 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term133 A s t).
Proof. exact (@lem17045 (@FINITE A s) (@FINITE A t)). Qed.
Lemma lem3925325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term134 A s t) = (term134 A s t).
Proof. exact (eq_refl (term134 A s t)). Qed.
Lemma lem3925326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3925327 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term136 A s t).
Proof. exact (MK_COMB (@lem3925326) (@lem3925324 A s t)). Qed.
Lemma lem3925328 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term137 A s t) = (term138 A s t).
Proof. exact (MK_COMB (@lem3925327 A s t) (@lem3925325 A s t)). Qed.
Lemma lem3925329 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term137 A s t).
Proof. exact (@lem17265 (term31 A s t) (term134 A s t)). Qed.
Lemma lem3925330 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term138 A s t).
Proof. exact (TRANS (@lem3925329 A s t) (@lem3925328 A s t)). Qed.
Lemma lem3925331 {A : Type'} (s : A -> Prop) : (term36 A s) = (term139 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925330 A s t)). Qed.
Lemma lem3925332 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925333 {A : Type'} (s : A -> Prop) : (term37 A s) = (term140 A s).
Proof. exact (MK_COMB (@lem3925332 A) (@lem3925331 A s)). Qed.
Lemma lem3925334 {A : Type'} : (term38 A) = (term141 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925333 A s)). Qed.
Lemma lem3925335 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925392 {A : Type'} : (term12 A) = (term142 A).
Proof. exact (MK_COMB (@lem3925335 A) (@lem3925334 A)). Qed.
Lemma lem3925393 {A : Type'} (h1 : term12 A) : term142 A.
Proof. exact (EQ_MP (@lem3925392 A) (@lem3925013 A h1)). Qed.
Lemma lem3925404 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term133 A s t).
Proof. exact (@lem17045 (@FINITE A s) (@FINITE A t)). Qed.
Lemma lem3925410 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term143 A s t).
Proof. exact (eq_refl (term143 A s t)). Qed.
Lemma lem3925412 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term144 A s t).
Proof. exact (eq_refl (term144 A s t)). Qed.
Lemma lem3925413 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term145 A s t) = (term146 A s t).
Proof. exact (MK_COMB (@lem3925412 A s t) (@lem3925404 A s t)). Qed.
Lemma lem3925414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3925415 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term148 A s t).
Proof. exact (MK_COMB (@lem3925414) (@lem3925413 A s t)). Qed.
Lemma lem3925416 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term149 A s t) = (term150 A s t).
Proof. exact (MK_COMB (@lem3925415 A s t) (@lem3925410 A s t)). Qed.
Lemma lem3925417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term30 A s t) = (term31 A s t)) = (term149 A s t).
Proof. exact (@lem17784 (term30 A s t) (term31 A s t)). Qed.
Lemma lem3925418 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term30 A s t) = (term31 A s t)) = (term150 A s t).
Proof. exact (TRANS (@lem3925417 A s t) (@lem3925416 A s t)). Qed.
Lemma lem3925419 {A : Type'} (s : A -> Prop) : (term32 A s) = (term151 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925418 A s t)). Qed.
Lemma lem3925420 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925421 {A : Type'} (s : A -> Prop) : (term33 A s) = (term152 A s).
Proof. exact (MK_COMB (@lem3925420 A) (@lem3925419 A s)). Qed.
Lemma lem3925422 {A : Type'} : (term34 A) = (term153 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925421 A s)). Qed.
Lemma lem3925423 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925424 {A : Type'} : (term11 A) = (term154 A).
Proof. exact (MK_COMB (@lem3925423 A) (@lem3925422 A)). Qed.
Lemma lem3925430 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3925431 {A : Type'} (P : type686 A) (Q : type686 A) : (term157 A P Q) = (term158 A P Q).
Proof. exact (@lem3925430 (A -> Prop) P Q). Qed.
Lemma lem3925432 {A : Type'} (s : A -> Prop) : (term159 A s) = (term160 A s).
Proof. exact (@lem3925431 A (term161 A s) (term162 A s)). Qed.
Lemma lem3925433 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term163 A s t) = (term146 A s t).
Proof. exact (eq_refl (term163 A s t)). Qed.
Lemma lem3925434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3925435 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term164 A s t) = (term148 A s t).
Proof. exact (MK_COMB (@lem3925434) (@lem3925433 A s t)). Qed.
Lemma lem3925436 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term165 A s t) = (term143 A s t).
Proof. exact (eq_refl (term165 A s t)). Qed.
Lemma lem3925437 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term166 A s t) = (term150 A s t).
Proof. exact (MK_COMB (@lem3925435 A s t) (@lem3925436 A s t)). Qed.
Lemma lem3925438 {A : Type'} (s : A -> Prop) : (term167 A s) = (term151 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925437 A s t)). Qed.
Lemma lem3925439 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925440 {A : Type'} (s : A -> Prop) : (term159 A s) = (term152 A s).
Proof. exact (MK_COMB (@lem3925439 A) (@lem3925438 A s)). Qed.
Lemma lem3925441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3925442 {A : Type'} (s : A -> Prop) : (term168 A s) = (term169 A s).
Proof. exact (MK_COMB (@lem3925441) (@lem3925440 A s)). Qed.
Lemma lem3925443 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term163 A s t) = (term146 A s t).
Proof. exact (eq_refl (term163 A s t)). Qed.
Lemma lem3925444 {A : Type'} (s : A -> Prop) : (term170 A s) = (term161 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925443 A s t)). Qed.
Lemma lem3925445 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925446 {A : Type'} (s : A -> Prop) : (term171 A s) = (term172 A s).
Proof. exact (MK_COMB (@lem3925445 A) (@lem3925444 A s)). Qed.
Lemma lem3925447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3925448 {A : Type'} (s : A -> Prop) : (term173 A s) = (term174 A s).
Proof. exact (MK_COMB (@lem3925447) (@lem3925446 A s)). Qed.
Lemma lem3925449 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term165 A s t) = (term143 A s t).
Proof. exact (eq_refl (term165 A s t)). Qed.
Lemma lem3925450 {A : Type'} (s : A -> Prop) : (term175 A s) = (term162 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925449 A s t)). Qed.
Lemma lem3925451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925452 {A : Type'} (s : A -> Prop) : (term176 A s) = (term177 A s).
Proof. exact (MK_COMB (@lem3925451 A) (@lem3925450 A s)). Qed.
Lemma lem3925453 {A : Type'} (s : A -> Prop) : (term160 A s) = (term178 A s).
Proof. exact (MK_COMB (@lem3925448 A s) (@lem3925452 A s)). Qed.
Lemma lem3925454 {A : Type'} (s : A -> Prop) : ((term159 A s) = (term160 A s)) = ((term152 A s) = (term178 A s)).
Proof. exact (MK_COMB (@lem3925442 A s) (@lem3925453 A s)). Qed.
Lemma lem3925455 {A : Type'} (s : A -> Prop) : (term152 A s) = (term178 A s).
Proof. exact (EQ_MP (@lem3925454 A s) (@lem3925432 A s)). Qed.
Lemma lem3925552 {A : Type'} : (term153 A) = (term179 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925455 A s)). Qed.
Lemma lem3925553 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925554 {A : Type'} : (term154 A) = (term180 A).
Proof. exact (MK_COMB (@lem3925553 A) (@lem3925552 A)). Qed.
Lemma lem3925556 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3925557 {A : Type'} (P : type686 A) (Q : type686 A) : (term157 A P Q) = (term158 A P Q).
Proof. exact (@lem3925556 (A -> Prop) P Q). Qed.
Lemma lem3925558 {A : Type'} : (term181 A) = (term182 A).
Proof. exact (@lem3925557 A (term183 A) (term184 A)). Qed.
Lemma lem3925559 {A : Type'} (s : A -> Prop) : (term185 A s) = (term172 A s).
Proof. exact (eq_refl (term185 A s)). Qed.
Lemma lem3925560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3925561 {A : Type'} (s : A -> Prop) : (term186 A s) = (term174 A s).
Proof. exact (MK_COMB (@lem3925560) (@lem3925559 A s)). Qed.
Lemma lem3925562 {A : Type'} (s : A -> Prop) : (term187 A s) = (term177 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem3925563 {A : Type'} (s : A -> Prop) : (term188 A s) = (term178 A s).
Proof. exact (MK_COMB (@lem3925561 A s) (@lem3925562 A s)). Qed.
Lemma lem3925564 {A : Type'} : (term189 A) = (term179 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925563 A s)). Qed.
Lemma lem3925565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925566 {A : Type'} : (term181 A) = (term180 A).
Proof. exact (MK_COMB (@lem3925565 A) (@lem3925564 A)). Qed.
Lemma lem3925567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3925568 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (MK_COMB (@lem3925567) (@lem3925566 A)). Qed.
Lemma lem3925569 {A : Type'} (s : A -> Prop) : (term185 A s) = (term172 A s).
Proof. exact (eq_refl (term185 A s)). Qed.
Lemma lem3925570 {A : Type'} : (term192 A) = (term183 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925569 A s)). Qed.
Lemma lem3925571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925572 {A : Type'} : (term193 A) = (term194 A).
Proof. exact (MK_COMB (@lem3925571 A) (@lem3925570 A)). Qed.
Lemma lem3925573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3925574 {A : Type'} : (term195 A) = (term196 A).
Proof. exact (MK_COMB (@lem3925573) (@lem3925572 A)). Qed.
Lemma lem3925575 {A : Type'} (s : A -> Prop) : (term187 A s) = (term177 A s).
Proof. exact (eq_refl (term187 A s)). Qed.
Lemma lem3925576 {A : Type'} : (term197 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925575 A s)). Qed.
Lemma lem3925577 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925578 {A : Type'} : (term198 A) = (term199 A).
Proof. exact (MK_COMB (@lem3925577 A) (@lem3925576 A)). Qed.
Lemma lem3925579 {A : Type'} : (term182 A) = (term200 A).
Proof. exact (MK_COMB (@lem3925574 A) (@lem3925578 A)). Qed.
Lemma lem3925580 {A : Type'} : ((term181 A) = (term182 A)) = ((term180 A) = (term200 A)).
Proof. exact (MK_COMB (@lem3925568 A) (@lem3925579 A)). Qed.
Lemma lem3925581 {A : Type'} : (term180 A) = (term200 A).
Proof. exact (EQ_MP (@lem3925580 A) (@lem3925558 A)). Qed.
Lemma lem3925688 {A : Type'} : (term154 A) = (term200 A).
Proof. exact (TRANS (@lem3925554 A) (@lem3925581 A)). Qed.
Lemma lem3925689 {A : Type'} : (term11 A) = (term200 A).
Proof. exact (TRANS (@lem3925424 A) (@lem3925688 A)). Qed.
Lemma lem3925690 {A : Type'} (h1 : term11 A) : term200 A.
Proof. exact (EQ_MP (@lem3925689 A) (@lem3925014 A h1)). Qed.
Lemma lem3925691 {A : Type'} (s : A -> Prop) (h1 : term96 A s) : term96 A s.
Proof. exact (h1). Qed.
Lemma lem3925692 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term87 A s t) : term87 A s t.
Proof. exact (h1). Qed.
Lemma lem3925693 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (h1 : term80 A s t m) : term80 A s t m.
Proof. exact (h1). Qed.
Lemma lem3925719 (n : nat) (m : nat) (p : nat) : (term108 n m p) = (term108 n m p).
Proof. exact (eq_refl (term108 n m p)). Qed.
Lemma lem3925720 (n : nat) (m : nat) : (term110 n m) = (term110 n m).
Proof. exact (fun_ext (fun p : nat => @lem3925719 n m p)). Qed.
Lemma lem3925721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925722 (n : nat) (m : nat) : (term111 n m) = (term111 n m).
Proof. exact (MK_COMB (@lem3925721) (@lem3925720 n m)). Qed.
Lemma lem3925723 (m : nat) : (term112 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem3925722 n m)). Qed.
Lemma lem3925724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925725 (m : nat) : (term113 m) = (term113 m).
Proof. exact (MK_COMB (@lem3925724) (@lem3925723 m)). Qed.
Lemma lem3925726 : term114 = term114.
Proof. exact (fun_ext (fun m : nat => @lem3925725 m)). Qed.
Lemma lem3925727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925728 : term115 = term115.
Proof. exact (MK_COMB (@lem3925727) (@lem3925726)). Qed.
Lemma lem3925729 (h1 : term54) : term115.
Proof. exact (EQ_MP (@lem3925728) (@lem3925227 h1)). Qed.
Lemma lem3925762 (m : nat) (n : nat) (p : nat) (q : nat) : (term122 m n p q) = (term122 m n p q).
Proof. exact (eq_refl (term122 m n p q)). Qed.
Lemma lem3925763 (m : nat) (n : nat) (p : nat) : (term124 m n p) = (term124 m n p).
Proof. exact (fun_ext (fun q : nat => @lem3925762 m n p q)). Qed.
Lemma lem3925764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925765 (m : nat) (n : nat) (p : nat) : (term125 m n p) = (term125 m n p).
Proof. exact (MK_COMB (@lem3925764) (@lem3925763 m n p)). Qed.
Lemma lem3925766 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (fun_ext (fun p : nat => @lem3925765 m n p)). Qed.
Lemma lem3925767 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925768 (m : nat) (n : nat) : (term127 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem3925767) (@lem3925766 m n)). Qed.
Lemma lem3925769 (m : nat) : (term128 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem3925768 m n)). Qed.
Lemma lem3925770 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925771 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem3925770) (@lem3925769 m)). Qed.
Lemma lem3925772 : term130 = term130.
Proof. exact (fun_ext (fun m : nat => @lem3925771 m)). Qed.
Lemma lem3925773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3925774 : term131 = term131.
Proof. exact (MK_COMB (@lem3925773) (@lem3925772)). Qed.
Lemma lem3925775 (h1 : term47) : term131.
Proof. exact (EQ_MP (@lem3925774) (@lem3925317 h1)). Qed.
Lemma lem3925810 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term138 A s t).
Proof. exact (eq_refl (term138 A s t)). Qed.
Lemma lem3925811 {A : Type'} (s : A -> Prop) : (term139 A s) = (term139 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925810 A s t)). Qed.
Lemma lem3925812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925813 {A : Type'} (s : A -> Prop) : (term140 A s) = (term140 A s).
Proof. exact (MK_COMB (@lem3925812 A) (@lem3925811 A s)). Qed.
Lemma lem3925814 {A : Type'} : (term141 A) = (term141 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925813 A s)). Qed.
Lemma lem3925815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925816 {A : Type'} : (term142 A) = (term142 A).
Proof. exact (MK_COMB (@lem3925815 A) (@lem3925814 A)). Qed.
Lemma lem3925817 {A : Type'} (h1 : term12 A) : term142 A.
Proof. exact (EQ_MP (@lem3925816 A) (@lem3925393 A h1)). Qed.
Lemma lem3925838 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term143 A s t).
Proof. exact (eq_refl (term143 A s t)). Qed.
Lemma lem3925839 {A : Type'} (s : A -> Prop) : (term162 A s) = (term162 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925838 A s t)). Qed.
Lemma lem3925840 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925841 {A : Type'} (s : A -> Prop) : (term177 A s) = (term177 A s).
Proof. exact (MK_COMB (@lem3925840 A) (@lem3925839 A s)). Qed.
Lemma lem3925842 {A : Type'} : (term184 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925841 A s)). Qed.
Lemma lem3925843 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925844 {A : Type'} : (term199 A) = (term199 A).
Proof. exact (MK_COMB (@lem3925843 A) (@lem3925842 A)). Qed.
Lemma lem3925867 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term146 A s t) = (term146 A s t).
Proof. exact (eq_refl (term146 A s t)). Qed.
Lemma lem3925868 {A : Type'} (s : A -> Prop) : (term161 A s) = (term161 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3925867 A s t)). Qed.
Lemma lem3925869 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925870 {A : Type'} (s : A -> Prop) : (term172 A s) = (term172 A s).
Proof. exact (MK_COMB (@lem3925869 A) (@lem3925868 A s)). Qed.
Lemma lem3925871 {A : Type'} : (term183 A) = (term183 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3925870 A s)). Qed.
Lemma lem3925872 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3925873 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem3925872 A) (@lem3925871 A)). Qed.
Lemma lem3925874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3925875 {A : Type'} : (term196 A) = (term196 A).
Proof. exact (MK_COMB (@lem3925874) (@lem3925873 A)). Qed.
Lemma lem3925876 {A : Type'} : (term200 A) = (term200 A).
Proof. exact (MK_COMB (@lem3925875 A) (@lem3925844 A)). Qed.
Lemma lem3925877 {A : Type'} (h1 : term11 A) : term200 A.
Proof. exact (EQ_MP (@lem3925876 A) (@lem3925690 A h1)). Qed.
Lemma lem3925939 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term68 A s t m n.
Proof. exact (h1). Qed.
Lemma lem3925940 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term64 A s t m n.
Proof. exact (proj2 (@lem3925939 A s t m n h1)). Qed.
Lemma lem3925941 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term70 A s m t n.
Proof. exact (proj1 (@lem3925939 A s t m n h1)). Qed.
Lemma lem3925942 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term201 A t n.
Proof. exact (proj2 (@lem3925941 A s t m n h1)). Qed.
Lemma lem3925943 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term201 A s m.
Proof. exact (proj1 (@lem3925941 A s t m n h1)). Qed.
Lemma lem3925949 {A : Type'} (h1 : term11 A) : term194 A.
Proof. exact (proj1 (@lem3925877 A h1)). Qed.
Lemma lem3926056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term146 A s t) = (term146 A s t).
Proof. exact (eq_refl (term146 A s t)). Qed.
Lemma lem3926057 {A : Type'} (s : A -> Prop) : (term161 A s) = (term161 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3926056 A s t)). Qed.
Lemma lem3926058 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3926059 {A : Type'} (s : A -> Prop) : (term172 A s) = (term172 A s).
Proof. exact (MK_COMB (@lem3926058 A) (@lem3926057 A s)). Qed.
Lemma lem3926060 {A : Type'} : (term183 A) = (term183 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3926059 A s)). Qed.
Lemma lem3926061 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3926063 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (MK_COMB (@lem3926061 A) (@lem3926060 A)). Qed.
Lemma lem3926064 {A : Type'} (h1 : term11 A) : term194 A.
Proof. exact (EQ_MP (@lem3926063 A) (@lem3925949 A h1)). Qed.
Lemma lem3926094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term202 A s t) : term202 A s t.
Proof. exact (h1). Qed.
Lemma lem3926108 (n : nat) (m : nat) (p : nat) : (term108 n m p) = (term108 n m p).
Proof. exact (eq_refl (term108 n m p)). Qed.
Lemma lem3926109 (n : nat) (m : nat) : (term110 n m) = (term110 n m).
Proof. exact (fun_ext (fun p : nat => @lem3926108 n m p)). Qed.
Lemma lem3926110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3926111 (n : nat) (m : nat) : (term111 n m) = (term111 n m).
Proof. exact (MK_COMB (@lem3926110) (@lem3926109 n m)). Qed.
Lemma lem3926112 (m : nat) : (term112 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem3926111 n m)). Qed.
Lemma lem3926113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3926114 (m : nat) : (term113 m) = (term113 m).
Proof. exact (MK_COMB (@lem3926113) (@lem3926112 m)). Qed.
Lemma lem3926115 : term114 = term114.
Proof. exact (fun_ext (fun m : nat => @lem3926114 m)). Qed.
Lemma lem3926116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3926118 : term115 = term115.
Proof. exact (MK_COMB (@lem3926116) (@lem3926115)). Qed.
Lemma lem3926119 (h1 : term54) : term115.
Proof. exact (EQ_MP (@lem3926118) (@lem3925729 h1)). Qed.
Lemma lem3926133 (m : nat) (n : nat) (p : nat) (q : nat) : (term122 m n p q) = (term122 m n p q).
Proof. exact (eq_refl (term122 m n p q)). Qed.
Lemma lem3926134 (m : nat) (n : nat) (p : nat) : (term124 m n p) = (term124 m n p).
Proof. exact (fun_ext (fun q : nat => @lem3926133 m n p q)). Qed.
Lemma lem3926135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3926136 (m : nat) (n : nat) (p : nat) : (term125 m n p) = (term125 m n p).
Proof. exact (MK_COMB (@lem3926135) (@lem3926134 m n p)). Qed.
Lemma lem3926137 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (fun_ext (fun p : nat => @lem3926136 m n p)). Qed.
Lemma lem3926138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3926139 (m : nat) (n : nat) : (term127 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem3926138) (@lem3926137 m n)). Qed.
Lemma lem3926140 (m : nat) : (term128 m) = (term128 m).
Proof. exact (fun_ext (fun n : nat => @lem3926139 m n)). Qed.
Lemma lem3926141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3926142 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem3926141) (@lem3926140 m)). Qed.
Lemma lem3926143 : term130 = term130.
Proof. exact (fun_ext (fun m : nat => @lem3926142 m)). Qed.
Lemma lem3926144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3926146 : term131 = term131.
Proof. exact (MK_COMB (@lem3926144) (@lem3926143)). Qed.
Lemma lem3926147 (h1 : term47) : term131.
Proof. exact (EQ_MP (@lem3926146) (@lem3925775 h1)). Qed.
Lemma lem3926161 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term138 A s t).
Proof. exact (eq_refl (term138 A s t)). Qed.
Lemma lem3926162 {A : Type'} (s : A -> Prop) : (term139 A s) = (term139 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3926161 A s t)). Qed.
Lemma lem3926163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3926164 {A : Type'} (s : A -> Prop) : (term140 A s) = (term140 A s).
Proof. exact (MK_COMB (@lem3926163 A) (@lem3926162 A s)). Qed.
Lemma lem3926165 {A : Type'} : (term141 A) = (term141 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3926164 A s)). Qed.
Lemma lem3926166 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3926168 {A : Type'} : (term142 A) = (term142 A).
Proof. exact (MK_COMB (@lem3926166 A) (@lem3926165 A)). Qed.
Lemma lem3926169 {A : Type'} (h1 : term12 A) : term142 A.
Proof. exact (EQ_MP (@lem3926168 A) (@lem3925817 A h1)). Qed.
Lemma lem3926237 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term203 A s t m n) : term203 A s t m n.
Proof. exact (h1). Qed.
Lemma lem3926265 {A : Type'} (_45613 : A -> Prop) (h1 : term11 A) : term185 A _45613.
Proof. exact (@lem3926064 A h1 _45613). Qed.
Lemma lem3926266 {A : Type'} (_45613 : A -> Prop) : (term185 A _45613) = (term172 A _45613).
Proof. exact (eq_refl (term185 A _45613)). Qed.
Lemma lem3926267 {A : Type'} (_45613 : A -> Prop) (h1 : term11 A) : term172 A _45613.
Proof. exact (EQ_MP (@lem3926266 A _45613) (@lem3926265 A _45613 h1)). Qed.
Lemma lem3926268 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) (h1 : term11 A) : term163 A _45613 _45614.
Proof. exact (@lem3926267 A _45613 h1 _45614). Qed.
Lemma lem3926269 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term163 A _45613 _45614) = (term146 A _45613 _45614).
Proof. exact (eq_refl (term163 A _45613 _45614)). Qed.
Lemma lem3926277 (_45617 : nat) (h1 : term54) : term204 _45617.
Proof. exact (@lem3926119 h1 _45617). Qed.
Lemma lem3926278 (_45617 : nat) : (term204 _45617) = (term113 _45617).
Proof. exact (eq_refl (term204 _45617)). Qed.
Lemma lem3926279 (_45617 : nat) (h1 : term54) : term113 _45617.
Proof. exact (EQ_MP (@lem3926278 _45617) (@lem3926277 _45617 h1)). Qed.
Lemma lem3926280 (_45617 : nat) (_45618 : nat) (h1 : term54) : term205 _45617 _45618.
Proof. exact (@lem3926279 _45617 h1 _45618). Qed.
Lemma lem3926281 (_45618 : nat) (_45617 : nat) : (term205 _45617 _45618) = (term111 _45618 _45617).
Proof. exact (eq_refl (term205 _45617 _45618)). Qed.
Lemma lem3926282 (_45618 : nat) (_45617 : nat) (h1 : term54) : term111 _45618 _45617.
Proof. exact (EQ_MP (@lem3926281 _45618 _45617) (@lem3926280 _45617 _45618 h1)). Qed.
Lemma lem3926283 (_45618 : nat) (_45617 : nat) (_45619 : nat) (h1 : term54) : term206 _45618 _45617 _45619.
Proof. exact (@lem3926282 _45618 _45617 h1 _45619). Qed.
Lemma lem3926284 (_45618 : nat) (_45617 : nat) (_45619 : nat) : (term206 _45618 _45617 _45619) = (term108 _45618 _45617 _45619).
Proof. exact (eq_refl (term206 _45618 _45617 _45619)). Qed.
Lemma lem3926285 (_45618 : nat) (_45617 : nat) (_45619 : nat) (h1 : term54) : term108 _45618 _45617 _45619.
Proof. exact (EQ_MP (@lem3926284 _45618 _45617 _45619) (@lem3926283 _45618 _45617 _45619 h1)). Qed.
Lemma lem3926286 (_45620 : nat) (h1 : term47) : term207 _45620.
Proof. exact (@lem3926147 h1 _45620). Qed.
Lemma lem3926287 (_45620 : nat) : (term207 _45620) = (term129 _45620).
Proof. exact (eq_refl (term207 _45620)). Qed.
Lemma lem3926288 (_45620 : nat) (h1 : term47) : term129 _45620.
Proof. exact (EQ_MP (@lem3926287 _45620) (@lem3926286 _45620 h1)). Qed.
Lemma lem3926289 (_45620 : nat) (_45621 : nat) (h1 : term47) : term208 _45620 _45621.
Proof. exact (@lem3926288 _45620 h1 _45621). Qed.
Lemma lem3926290 (_45620 : nat) (_45621 : nat) : (term208 _45620 _45621) = (term127 _45620 _45621).
Proof. exact (eq_refl (term208 _45620 _45621)). Qed.
Lemma lem3926291 (_45620 : nat) (_45621 : nat) (h1 : term47) : term127 _45620 _45621.
Proof. exact (EQ_MP (@lem3926290 _45620 _45621) (@lem3926289 _45620 _45621 h1)). Qed.
Lemma lem3926292 (_45620 : nat) (_45621 : nat) (_45622 : nat) (h1 : term47) : term209 _45620 _45621 _45622.
Proof. exact (@lem3926291 _45620 _45621 h1 _45622). Qed.
Lemma lem3926293 (_45620 : nat) (_45621 : nat) (_45622 : nat) : (term209 _45620 _45621 _45622) = (term125 _45620 _45621 _45622).
Proof. exact (eq_refl (term209 _45620 _45621 _45622)). Qed.
Lemma lem3926294 (_45620 : nat) (_45621 : nat) (_45622 : nat) (h1 : term47) : term125 _45620 _45621 _45622.
Proof. exact (EQ_MP (@lem3926293 _45620 _45621 _45622) (@lem3926292 _45620 _45621 _45622 h1)). Qed.
Lemma lem3926295 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) (h1 : term47) : term210 _45620 _45621 _45622 _45623.
Proof. exact (@lem3926294 _45620 _45621 _45622 h1 _45623). Qed.
Lemma lem3926296 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) : (term210 _45620 _45621 _45622 _45623) = (term122 _45620 _45621 _45622 _45623).
Proof. exact (eq_refl (term210 _45620 _45621 _45622 _45623)). Qed.
Lemma lem3926297 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) (h1 : term47) : term122 _45620 _45621 _45622 _45623.
Proof. exact (EQ_MP (@lem3926296 _45620 _45621 _45622 _45623) (@lem3926295 _45620 _45621 _45622 _45623 h1)). Qed.
Lemma lem3926298 {A : Type'} (_45624 : A -> Prop) (h1 : term12 A) : term211 A _45624.
Proof. exact (@lem3926169 A h1 _45624). Qed.
Lemma lem3926299 {A : Type'} (_45624 : A -> Prop) : (term211 A _45624) = (term140 A _45624).
Proof. exact (eq_refl (term211 A _45624)). Qed.
Lemma lem3926300 {A : Type'} (_45624 : A -> Prop) (h1 : term12 A) : term140 A _45624.
Proof. exact (EQ_MP (@lem3926299 A _45624) (@lem3926298 A _45624 h1)). Qed.
Lemma lem3926301 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) (h1 : term12 A) : term212 A _45624 _45625.
Proof. exact (@lem3926300 A _45624 h1 _45625). Qed.
Lemma lem3926302 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term212 A _45624 _45625) = (term138 A _45624 _45625).
Proof. exact (eq_refl (term212 A _45624 _45625)). Qed.
Lemma lem3926303 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) (h1 : term12 A) : term138 A _45624 _45625.
Proof. exact (EQ_MP (@lem3926302 A _45624 _45625) (@lem3926301 A _45624 _45625 h1)). Qed.
Lemma lem3926373 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) (h1 : term11 A) : term146 A _45613 _45614.
Proof. exact (EQ_MP (@lem3926269 A _45613 _45614) (@lem3926268 A _45613 _45614 h1)). Qed.
Lemma lem3926375 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term202 A s t) : term202 A s t.
Proof. exact (h1). Qed.
Lemma lem3926398 (_45618 : nat) (_45617 : nat) (_45619 : nat) : (term108 _45618 _45617 _45619) = (term213 _45618 _45617 _45619).
Proof. exact (@lem3924624 (term214 _45617 _45618) (term214 _45618 _45619) (Peano.le _45617 _45619)). Qed.
Lemma lem3926399 (_45618 : nat) (_45617 : nat) (_45619 : nat) (h1 : term54) : term213 _45618 _45617 _45619.
Proof. exact (EQ_MP (@lem3926398 _45618 _45617 _45619) (@lem3926285 _45618 _45617 _45619 h1)). Qed.
Lemma lem3926410 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) : (term122 _45620 _45621 _45622 _45623) = (term215 _45620 _45621 _45622 _45623).
Proof. exact (@lem3924624 (term214 _45620 _45622) (term214 _45621 _45623) (term118 _45620 _45621 _45622 _45623)). Qed.
Lemma lem3926411 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) (h1 : term47) : term215 _45620 _45621 _45622 _45623.
Proof. exact (EQ_MP (@lem3926410 _45620 _45621 _45622 _45623) (@lem3926297 _45620 _45621 _45622 _45623 h1)). Qed.
Lemma lem3926422 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term138 A _45624 _45625) = (term216 A _45624 _45625).
Proof. exact (@lem3924624 (term217 A _45624) (term217 A _45625) (term134 A _45624 _45625)). Qed.
Lemma lem3926423 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) (h1 : term12 A) : term216 A _45624 _45625.
Proof. exact (EQ_MP (@lem3926422 A _45624 _45625) (@lem3926303 A _45624 _45625 h1)). Qed.
Lemma lem3926443 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term203 A s t m n) : term203 A s t m n.
Proof. exact (h1). Qed.
Lemma lem3926457 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A s.
Proof. exact (proj1 (@lem3925943 A s t m n h1)). Qed.
Lemma lem3926458 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term218 A s.
Proof. exact (fun h0 : term217 A s => @lem3926457 A s t m n h1). Qed.
Lemma lem3926460 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926461 {A : Type'} (s : A -> Prop) : (term218 A s) = (@FINITE A s).
Proof. exact (@lem3926460 (@FINITE A s)). Qed.
Lemma lem3926462 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A s.
Proof. exact (EQ_MP (@lem3926461 A s) (@lem3926458 A s t m n h1)). Qed.
Lemma lem3926464 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A t.
Proof. exact (proj1 (@lem3925942 A s t m n h1)). Qed.
Lemma lem3926465 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term218 A t.
Proof. exact (fun h0 : term217 A t => @lem3926464 A s t m n h1). Qed.
Lemma lem3926467 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926468 {A : Type'} (t : A -> Prop) : (term218 A t) = (@FINITE A t).
Proof. exact (@lem3926467 (@FINITE A t)). Qed.
Lemma lem3926469 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A t.
Proof. exact (EQ_MP (@lem3926468 A t) (@lem3926465 A s t m n h1)). Qed.
Lemma lem3926471 (b : Prop) (a : Prop) : (a \/ b) = (term220 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3926472 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term146 A _45613 _45614) = (term221 A _45613 _45614).
Proof. exact (@lem3926471 (term133 A _45613 _45614) (term30 A _45613 _45614)). Qed.
Lemma lem3926474 (a : Prop) (b : Prop) : (term222 a b) = (term223 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3926475 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term224 A _45613 _45614) = (term225 A _45613 _45614).
Proof. exact (@lem3926474 (term217 A _45613) (term217 A _45614)). Qed.
Lemma lem3926477 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926478 {A : Type'} (_45613 : A -> Prop) : (term227 A _45613) = (@FINITE A _45613).
Proof. exact (@lem3926477 (@FINITE A _45613)). Qed.
Lemma lem3926479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3926480 {A : Type'} (_45613 : A -> Prop) : (term228 A _45613) = (term229 A _45613).
Proof. exact (MK_COMB (@lem3926479) (@lem3926478 A _45613)). Qed.
Lemma lem3926482 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926483 {A : Type'} (_45614 : A -> Prop) : (term227 A _45614) = (@FINITE A _45614).
Proof. exact (@lem3926482 (@FINITE A _45614)). Qed.
Lemma lem3926484 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term225 A _45613 _45614) = (term31 A _45613 _45614).
Proof. exact (MK_COMB (@lem3926480 A _45613) (@lem3926483 A _45614)). Qed.
Lemma lem3926485 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term224 A _45613 _45614) = (term31 A _45613 _45614).
Proof. exact (TRANS (@lem3926475 A _45613 _45614) (@lem3926484 A _45613 _45614)). Qed.
Lemma lem3926486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3926487 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term230 A _45613 _45614) = (term231 A _45613 _45614).
Proof. exact (MK_COMB (@lem3926486) (@lem3926485 A _45613 _45614)). Qed.
Lemma lem3926488 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term30 A _45613 _45614) = (term30 A _45613 _45614).
Proof. exact (eq_refl (term30 A _45613 _45614)). Qed.
Lemma lem3926489 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term221 A _45613 _45614) = (term232 A _45613 _45614).
Proof. exact (MK_COMB (@lem3926487 A _45613 _45614) (@lem3926488 A _45613 _45614)). Qed.
Lemma lem3926490 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) : (term146 A _45613 _45614) = (term232 A _45613 _45614).
Proof. exact (TRANS (@lem3926472 A _45613 _45614) (@lem3926489 A _45613 _45614)). Qed.
Lemma lem3926492 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term31 A s t.
Proof. exact (conj (@lem3926462 A s t m n h1) (@lem3926469 A s t m n h1)). Qed.
Lemma lem3926494 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) (h1 : term11 A) : term232 A _45613 _45614.
Proof. exact (EQ_MP (@lem3926490 A _45613 _45614) (@lem3926373 A _45613 _45614 h1)). Qed.
Lemma lem3926495 {A : Type'} (_45613 : A -> Prop) (_45614 : A -> Prop) (h1 : term11 A) : term232 A _45613 _45614.
Proof. exact (@lem3926494 A _45613 _45614 h1). Qed.
Lemma lem3926496 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) : term232 A s t.
Proof. exact (@lem3926495 A s t h1). Qed.
Lemma lem3926499 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term68 A s t m n) : term30 A s t.
Proof. exact (@lem3926496 A s t h1 (@lem3926492 A s t m n h2)). Qed.
Lemma lem3926500 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term68 A s t m n) : term233 A s t.
Proof. exact (fun h0 : term202 A s t => @lem3926499 A s t m n h1 h2). Qed.
Lemma lem3926502 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926503 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term233 A s t) = (term30 A s t).
Proof. exact (@lem3926502 (term30 A s t)). Qed.
Lemma lem3926504 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term68 A s t m n) : term30 A s t.
Proof. exact (EQ_MP (@lem3926503 A s t) (@lem3926500 A s t m n h1 h2)). Qed.
Lemma lem3926507 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3926509 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term202 A s t) = (term234 A s t).
Proof. exact (@lem3926507 (term30 A s t)). Qed.
Lemma lem3926512 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term202 A s t) : term234 A s t.
Proof. exact (EQ_MP (@lem3926509 A s t) (@lem3926375 A s t h1)). Qed.
Lemma lem3926515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : False.
Proof. exact (@lem3926512 A s t h2 (@lem3926504 A s t m n h1 h3)). Qed.
Lemma lem3926516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : term235.
Proof. exact (fun h0 : ~ False => @lem3926515 A s t m n h1 h2 h3). Qed.
Lemma lem3926518 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926519 : term235 = False.
Proof. exact (@lem3926518 False). Qed.
Lemma lem3926520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926519) (@lem3926516 A s t m n h1 h2 h3)). Qed.
Lemma lem3926522 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A s.
Proof. exact (proj1 (@lem3925943 A s t m n h1)). Qed.
Lemma lem3926523 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term218 A s.
Proof. exact (fun h0 : term217 A s => @lem3926522 A s t m n h1). Qed.
Lemma lem3926525 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926526 {A : Type'} (s : A -> Prop) : (term218 A s) = (@FINITE A s).
Proof. exact (@lem3926525 (@FINITE A s)). Qed.
Lemma lem3926527 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A s.
Proof. exact (EQ_MP (@lem3926526 A s) (@lem3926523 A s t m n h1)). Qed.
Lemma lem3926529 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A t.
Proof. exact (proj1 (@lem3925942 A s t m n h1)). Qed.
Lemma lem3926530 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term218 A t.
Proof. exact (fun h0 : term217 A t => @lem3926529 A s t m n h1). Qed.
Lemma lem3926532 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926533 {A : Type'} (t : A -> Prop) : (term218 A t) = (@FINITE A t).
Proof. exact (@lem3926532 (@FINITE A t)). Qed.
Lemma lem3926534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : @FINITE A t.
Proof. exact (EQ_MP (@lem3926533 A t) (@lem3926530 A s t m n h1)). Qed.
Lemma lem3926550 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3926551 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term236 A _45624 _45625) = (term237 A _45624 _45625).
Proof. exact (@lem3926550 (term134 A _45624 _45625) (term217 A _45625)). Qed.
Lemma lem3926557 {A : Type'} (_45624 : A -> Prop) : (term238 A _45624) = (term238 A _45624).
Proof. exact (eq_refl (term238 A _45624)). Qed.
Lemma lem3926558 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term216 A _45624 _45625) = (term239 A _45624 _45625).
Proof. exact (MK_COMB (@lem3926557 A _45624) (@lem3926551 A _45624 _45625)). Qed.
Lemma lem3926562 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3926563 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term239 A _45624 _45625) = (term240 A _45624 _45625).
Proof. exact (@lem3926562 (term134 A _45624 _45625) (term217 A _45624) (term217 A _45625)). Qed.
Lemma lem3926579 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term216 A _45624 _45625) = (term240 A _45624 _45625).
Proof. exact (TRANS (@lem3926558 A _45624 _45625) (@lem3926563 A _45624 _45625)). Qed.
Lemma lem3926580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3926581 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term241 A _45624 _45625) = (term242 A _45624 _45625).
Proof. exact (MK_COMB (@lem3926580) (@lem3926579 A _45624 _45625)). Qed.
Lemma lem3926597 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term240 A _45624 _45625) = (term240 A _45624 _45625).
Proof. exact (eq_refl (term240 A _45624 _45625)). Qed.
Lemma lem3926598 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : ((term216 A _45624 _45625) = (term240 A _45624 _45625)) = ((term240 A _45624 _45625) = (term240 A _45624 _45625)).
Proof. exact (MK_COMB (@lem3926581 A _45624 _45625) (@lem3926597 A _45624 _45625)). Qed.
Lemma lem3926600 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3926601 (x : Prop) : (x = x) = True.
Proof. exact (@lem3926600 Prop x). Qed.
Lemma lem3926602 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : ((term240 A _45624 _45625) = (term240 A _45624 _45625)) = True.
Proof. exact (@lem3926601 (term240 A _45624 _45625)). Qed.
Lemma lem3926603 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : ((term216 A _45624 _45625) = (term240 A _45624 _45625)) = True.
Proof. exact (TRANS (@lem3926598 A _45624 _45625) (@lem3926602 A _45624 _45625)). Qed.
Lemma lem3926604 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : True = ((term216 A _45624 _45625) = (term240 A _45624 _45625)).
Proof. exact (SYM (@lem3926603 A _45624 _45625)). Qed.
Lemma lem3926605 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term216 A _45624 _45625) = (term240 A _45624 _45625).
Proof. exact (EQ_MP (@lem3926604 A _45624 _45625) (@lem0)). Qed.
Lemma lem3926606 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) (h1 : term12 A) : term240 A _45624 _45625.
Proof. exact (EQ_MP (@lem3926605 A _45624 _45625) (@lem3926423 A _45624 _45625 h1)). Qed.
Lemma lem3926608 (b : Prop) (a : Prop) : (a \/ b) = (term220 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3926609 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term240 A _45624 _45625) = (term243 A _45624 _45625).
Proof. exact (@lem3926608 (term133 A _45624 _45625) (term134 A _45624 _45625)). Qed.
Lemma lem3926611 (a : Prop) (b : Prop) : (term222 a b) = (term223 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3926612 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term224 A _45624 _45625) = (term225 A _45624 _45625).
Proof. exact (@lem3926611 (term217 A _45624) (term217 A _45625)). Qed.
Lemma lem3926614 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926615 {A : Type'} (_45624 : A -> Prop) : (term227 A _45624) = (@FINITE A _45624).
Proof. exact (@lem3926614 (@FINITE A _45624)). Qed.
Lemma lem3926616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3926617 {A : Type'} (_45624 : A -> Prop) : (term228 A _45624) = (term229 A _45624).
Proof. exact (MK_COMB (@lem3926616) (@lem3926615 A _45624)). Qed.
Lemma lem3926619 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926620 {A : Type'} (_45625 : A -> Prop) : (term227 A _45625) = (@FINITE A _45625).
Proof. exact (@lem3926619 (@FINITE A _45625)). Qed.
Lemma lem3926621 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term225 A _45624 _45625) = (term31 A _45624 _45625).
Proof. exact (MK_COMB (@lem3926617 A _45624) (@lem3926620 A _45625)). Qed.
Lemma lem3926622 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term224 A _45624 _45625) = (term31 A _45624 _45625).
Proof. exact (TRANS (@lem3926612 A _45624 _45625) (@lem3926621 A _45624 _45625)). Qed.
Lemma lem3926623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3926624 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term230 A _45624 _45625) = (term231 A _45624 _45625).
Proof. exact (MK_COMB (@lem3926623) (@lem3926622 A _45624 _45625)). Qed.
Lemma lem3926625 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term134 A _45624 _45625) = (term134 A _45624 _45625).
Proof. exact (eq_refl (term134 A _45624 _45625)). Qed.
Lemma lem3926626 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term243 A _45624 _45625) = (term35 A _45624 _45625).
Proof. exact (MK_COMB (@lem3926624 A _45624 _45625) (@lem3926625 A _45624 _45625)). Qed.
Lemma lem3926627 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) : (term240 A _45624 _45625) = (term35 A _45624 _45625).
Proof. exact (TRANS (@lem3926609 A _45624 _45625) (@lem3926626 A _45624 _45625)). Qed.
Lemma lem3926629 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term31 A s t.
Proof. exact (conj (@lem3926527 A s t m n h1) (@lem3926534 A s t m n h1)). Qed.
Lemma lem3926631 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) (h1 : term12 A) : term35 A _45624 _45625.
Proof. exact (EQ_MP (@lem3926627 A _45624 _45625) (@lem3926606 A _45624 _45625 h1)). Qed.
Lemma lem3926632 {A : Type'} (_45624 : A -> Prop) (_45625 : A -> Prop) (h1 : term12 A) : term35 A _45624 _45625.
Proof. exact (@lem3926631 A _45624 _45625 h1). Qed.
Lemma lem3926633 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) : term35 A s t.
Proof. exact (@lem3926632 A s t h1). Qed.
Lemma lem3926636 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term68 A s t m n) : term134 A s t.
Proof. exact (@lem3926633 A s t h1 (@lem3926629 A s t m n h2)). Qed.
Lemma lem3926637 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term68 A s t m n) : term244 A s t.
Proof. exact (fun h0 : term245 A s t => @lem3926636 A s t m n h1 h2). Qed.
Lemma lem3926639 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926640 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term244 A s t) = (term134 A s t).
Proof. exact (@lem3926639 (term134 A s t)). Qed.
Lemma lem3926641 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term68 A s t m n) : term134 A s t.
Proof. exact (EQ_MP (@lem3926640 A s t) (@lem3926637 A s t m n h1 h2)). Qed.
Lemma lem3926643 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term246 A s m.
Proof. exact (proj2 (@lem3925943 A s t m n h1)). Qed.
Lemma lem3926644 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term247 A s m.
Proof. exact (fun h0 : term248 A s m => @lem3926643 A s t m n h1). Qed.
Lemma lem3926646 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926647 {A : Type'} (s : A -> Prop) (m : nat) : (term247 A s m) = (term246 A s m).
Proof. exact (@lem3926646 (term246 A s m)). Qed.
Lemma lem3926648 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term246 A s m.
Proof. exact (EQ_MP (@lem3926647 A s m) (@lem3926644 A s t m n h1)). Qed.
Lemma lem3926650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term246 A t n.
Proof. exact (proj2 (@lem3925942 A s t m n h1)). Qed.
Lemma lem3926651 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term247 A t n.
Proof. exact (fun h0 : term248 A t n => @lem3926650 A s t m n h1). Qed.
Lemma lem3926653 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926654 {A : Type'} (t : A -> Prop) (n : nat) : (term247 A t n) = (term246 A t n).
Proof. exact (@lem3926653 (term246 A t n)). Qed.
Lemma lem3926655 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term246 A t n.
Proof. exact (EQ_MP (@lem3926654 A t n) (@lem3926651 A s t m n h1)). Qed.
Lemma lem3926671 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3926672 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term249 _45620 _45621 _45622 _45623) = (term250 _45620 _45622 _45621 _45623).
Proof. exact (@lem3926671 (term118 _45620 _45621 _45622 _45623) (term214 _45621 _45623)). Qed.
Lemma lem3926678 (_45620 : nat) (_45622 : nat) : (term251 _45620 _45622) = (term251 _45620 _45622).
Proof. exact (eq_refl (term251 _45620 _45622)). Qed.
Lemma lem3926679 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term215 _45620 _45621 _45622 _45623) = (term252 _45620 _45622 _45621 _45623).
Proof. exact (MK_COMB (@lem3926678 _45620 _45622) (@lem3926672 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926683 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3926684 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term252 _45620 _45622 _45621 _45623) = (term253 _45620 _45622 _45621 _45623).
Proof. exact (@lem3926683 (term118 _45620 _45621 _45622 _45623) (term214 _45620 _45622) (term214 _45621 _45623)). Qed.
Lemma lem3926700 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term215 _45620 _45621 _45622 _45623) = (term253 _45620 _45622 _45621 _45623).
Proof. exact (TRANS (@lem3926679 _45620 _45622 _45621 _45623) (@lem3926684 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3926702 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term254 _45620 _45621 _45622 _45623) = (term255 _45620 _45622 _45621 _45623).
Proof. exact (MK_COMB (@lem3926701) (@lem3926700 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926718 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term253 _45620 _45622 _45621 _45623) = (term253 _45620 _45622 _45621 _45623).
Proof. exact (eq_refl (term253 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926719 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : ((term215 _45620 _45621 _45622 _45623) = (term253 _45620 _45622 _45621 _45623)) = ((term253 _45620 _45622 _45621 _45623) = (term253 _45620 _45622 _45621 _45623)).
Proof. exact (MK_COMB (@lem3926702 _45620 _45622 _45621 _45623) (@lem3926718 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926721 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3926722 (x : Prop) : (x = x) = True.
Proof. exact (@lem3926721 Prop x). Qed.
Lemma lem3926723 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : ((term253 _45620 _45622 _45621 _45623) = (term253 _45620 _45622 _45621 _45623)) = True.
Proof. exact (@lem3926722 (term253 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926724 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : ((term215 _45620 _45621 _45622 _45623) = (term253 _45620 _45622 _45621 _45623)) = True.
Proof. exact (TRANS (@lem3926719 _45620 _45622 _45621 _45623) (@lem3926723 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926725 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : True = ((term215 _45620 _45621 _45622 _45623) = (term253 _45620 _45622 _45621 _45623)).
Proof. exact (SYM (@lem3926724 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926726 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term215 _45620 _45621 _45622 _45623) = (term253 _45620 _45622 _45621 _45623).
Proof. exact (EQ_MP (@lem3926725 _45620 _45622 _45621 _45623) (@lem0)). Qed.
Lemma lem3926727 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) (h1 : term47) : term253 _45620 _45622 _45621 _45623.
Proof. exact (EQ_MP (@lem3926726 _45620 _45622 _45621 _45623) (@lem3926411 _45620 _45621 _45622 _45623 h1)). Qed.
Lemma lem3926729 (b : Prop) (a : Prop) : (a \/ b) = (term220 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3926730 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) : (term253 _45620 _45622 _45621 _45623) = (term256 _45620 _45621 _45622 _45623).
Proof. exact (@lem3926729 (term117 _45620 _45622 _45621 _45623) (term118 _45620 _45621 _45622 _45623)). Qed.
Lemma lem3926732 (a : Prop) (b : Prop) : (term222 a b) = (term223 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3926733 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term257 _45620 _45622 _45621 _45623) = (term258 _45620 _45622 _45621 _45623).
Proof. exact (@lem3926732 (term214 _45620 _45622) (term214 _45621 _45623)). Qed.
Lemma lem3926735 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926736 (_45620 : nat) (_45622 : nat) : (term259 _45620 _45622) = (Peano.le _45620 _45622).
Proof. exact (@lem3926735 (Peano.le _45620 _45622)). Qed.
Lemma lem3926737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3926738 (_45620 : nat) (_45622 : nat) : (term260 _45620 _45622) = (term261 _45620 _45622).
Proof. exact (MK_COMB (@lem3926737) (@lem3926736 _45620 _45622)). Qed.
Lemma lem3926740 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926741 (_45621 : nat) (_45623 : nat) : (term259 _45621 _45623) = (Peano.le _45621 _45623).
Proof. exact (@lem3926740 (Peano.le _45621 _45623)). Qed.
Lemma lem3926742 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term258 _45620 _45622 _45621 _45623) = (term123 _45620 _45622 _45621 _45623).
Proof. exact (MK_COMB (@lem3926738 _45620 _45622) (@lem3926741 _45621 _45623)). Qed.
Lemma lem3926743 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term257 _45620 _45622 _45621 _45623) = (term123 _45620 _45622 _45621 _45623).
Proof. exact (TRANS (@lem3926733 _45620 _45622 _45621 _45623) (@lem3926742 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3926745 (_45620 : nat) (_45622 : nat) (_45621 : nat) (_45623 : nat) : (term262 _45620 _45622 _45621 _45623) = (term263 _45620 _45622 _45621 _45623).
Proof. exact (MK_COMB (@lem3926744) (@lem3926743 _45620 _45622 _45621 _45623)). Qed.
Lemma lem3926746 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) : (term118 _45620 _45621 _45622 _45623) = (term118 _45620 _45621 _45622 _45623).
Proof. exact (eq_refl (term118 _45620 _45621 _45622 _45623)). Qed.
Lemma lem3926747 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) : (term256 _45620 _45621 _45622 _45623) = (term39 _45620 _45621 _45622 _45623).
Proof. exact (MK_COMB (@lem3926745 _45620 _45622 _45621 _45623) (@lem3926746 _45620 _45621 _45622 _45623)). Qed.
Lemma lem3926748 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) : (term253 _45620 _45622 _45621 _45623) = (term39 _45620 _45621 _45622 _45623).
Proof. exact (TRANS (@lem3926730 _45620 _45621 _45622 _45623) (@lem3926747 _45620 _45621 _45622 _45623)). Qed.
Lemma lem3926750 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term68 A s t m n) : term264 A s m t n.
Proof. exact (conj (@lem3926648 A s t m n h1) (@lem3926655 A s t m n h1)). Qed.
Lemma lem3926752 (_45620 : nat) (_45621 : nat) (_45622 : nat) (_45623 : nat) (h1 : term47) : term39 _45620 _45621 _45622 _45623.
Proof. exact (EQ_MP (@lem3926748 _45620 _45621 _45622 _45623) (@lem3926727 _45620 _45622 _45621 _45623 h1)). Qed.
Lemma lem3926753 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term47) : term265 A s t m n.
Proof. exact (@lem3926752 (@CARD A s) (@CARD A t) m n h1). Qed.
Lemma lem3926756 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term47) (h2 : term68 A s t m n) : term266 A s t m n.
Proof. exact (@lem3926753 A s t m n h1 (@lem3926750 A s t m n h2)). Qed.
Lemma lem3926757 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term47) (h2 : term68 A s t m n) : term267 A s t m n.
Proof. exact (fun h0 : term268 A s t m n => @lem3926756 A s t m n h1 h2). Qed.
Lemma lem3926759 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926760 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term267 A s t m n) = (term266 A s t m n).
Proof. exact (@lem3926759 (term266 A s t m n)). Qed.
Lemma lem3926761 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term47) (h2 : term68 A s t m n) : term266 A s t m n.
Proof. exact (EQ_MP (@lem3926760 A s t m n) (@lem3926757 A s t m n h1 h2)). Qed.
Lemma lem3926777 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3926778 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term269 _45618 _45617 _45619) = (term270 _45617 _45618 _45619).
Proof. exact (@lem3926777 (Peano.le _45617 _45619) (term214 _45618 _45619)). Qed.
Lemma lem3926784 (_45617 : nat) (_45618 : nat) : (term251 _45617 _45618) = (term251 _45617 _45618).
Proof. exact (eq_refl (term251 _45617 _45618)). Qed.
Lemma lem3926785 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term213 _45618 _45617 _45619) = (term271 _45617 _45618 _45619).
Proof. exact (MK_COMB (@lem3926784 _45617 _45618) (@lem3926778 _45617 _45618 _45619)). Qed.
Lemma lem3926789 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3926790 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term271 _45617 _45618 _45619) = (term272 _45617 _45618 _45619).
Proof. exact (@lem3926789 (Peano.le _45617 _45619) (term214 _45617 _45618) (term214 _45618 _45619)). Qed.
Lemma lem3926806 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term213 _45618 _45617 _45619) = (term272 _45617 _45618 _45619).
Proof. exact (TRANS (@lem3926785 _45617 _45618 _45619) (@lem3926790 _45617 _45618 _45619)). Qed.
Lemma lem3926807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3926808 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term273 _45618 _45617 _45619) = (term274 _45617 _45618 _45619).
Proof. exact (MK_COMB (@lem3926807) (@lem3926806 _45617 _45618 _45619)). Qed.
Lemma lem3926824 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term272 _45617 _45618 _45619) = (term272 _45617 _45618 _45619).
Proof. exact (eq_refl (term272 _45617 _45618 _45619)). Qed.
Lemma lem3926825 (_45617 : nat) (_45618 : nat) (_45619 : nat) : ((term213 _45618 _45617 _45619) = (term272 _45617 _45618 _45619)) = ((term272 _45617 _45618 _45619) = (term272 _45617 _45618 _45619)).
Proof. exact (MK_COMB (@lem3926808 _45617 _45618 _45619) (@lem3926824 _45617 _45618 _45619)). Qed.
Lemma lem3926827 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3926828 (x : Prop) : (x = x) = True.
Proof. exact (@lem3926827 Prop x). Qed.
Lemma lem3926829 (_45617 : nat) (_45618 : nat) (_45619 : nat) : ((term272 _45617 _45618 _45619) = (term272 _45617 _45618 _45619)) = True.
Proof. exact (@lem3926828 (term272 _45617 _45618 _45619)). Qed.
Lemma lem3926830 (_45617 : nat) (_45618 : nat) (_45619 : nat) : ((term213 _45618 _45617 _45619) = (term272 _45617 _45618 _45619)) = True.
Proof. exact (TRANS (@lem3926825 _45617 _45618 _45619) (@lem3926829 _45617 _45618 _45619)). Qed.
Lemma lem3926831 (_45617 : nat) (_45618 : nat) (_45619 : nat) : True = ((term213 _45618 _45617 _45619) = (term272 _45617 _45618 _45619)).
Proof. exact (SYM (@lem3926830 _45617 _45618 _45619)). Qed.
Lemma lem3926832 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term213 _45618 _45617 _45619) = (term272 _45617 _45618 _45619).
Proof. exact (EQ_MP (@lem3926831 _45617 _45618 _45619) (@lem0)). Qed.
Lemma lem3926833 (_45617 : nat) (_45618 : nat) (_45619 : nat) (h1 : term54) : term272 _45617 _45618 _45619.
Proof. exact (EQ_MP (@lem3926832 _45617 _45618 _45619) (@lem3926399 _45618 _45617 _45619 h1)). Qed.
Lemma lem3926835 (b : Prop) (a : Prop) : (a \/ b) = (term220 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3926836 (_45618 : nat) (_45617 : nat) (_45619 : nat) : (term272 _45617 _45618 _45619) = (term275 _45618 _45617 _45619).
Proof. exact (@lem3926835 (term104 _45617 _45618 _45619) (Peano.le _45617 _45619)). Qed.
Lemma lem3926838 (a : Prop) (b : Prop) : (term222 a b) = (term223 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3926839 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term276 _45617 _45618 _45619) = (term277 _45617 _45618 _45619).
Proof. exact (@lem3926838 (term214 _45617 _45618) (term214 _45618 _45619)). Qed.
Lemma lem3926841 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926842 (_45617 : nat) (_45618 : nat) : (term259 _45617 _45618) = (Peano.le _45617 _45618).
Proof. exact (@lem3926841 (Peano.le _45617 _45618)). Qed.
Lemma lem3926843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3926844 (_45617 : nat) (_45618 : nat) : (term260 _45617 _45618) = (term261 _45617 _45618).
Proof. exact (MK_COMB (@lem3926843) (@lem3926842 _45617 _45618)). Qed.
Lemma lem3926846 (a : Prop) : (term226 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3926847 (_45618 : nat) (_45619 : nat) : (term259 _45618 _45619) = (Peano.le _45618 _45619).
Proof. exact (@lem3926846 (Peano.le _45618 _45619)). Qed.
Lemma lem3926848 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term277 _45617 _45618 _45619) = (term109 _45617 _45618 _45619).
Proof. exact (MK_COMB (@lem3926844 _45617 _45618) (@lem3926847 _45618 _45619)). Qed.
Lemma lem3926849 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term276 _45617 _45618 _45619) = (term109 _45617 _45618 _45619).
Proof. exact (TRANS (@lem3926839 _45617 _45618 _45619) (@lem3926848 _45617 _45618 _45619)). Qed.
Lemma lem3926850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3926851 (_45617 : nat) (_45618 : nat) (_45619 : nat) : (term278 _45617 _45618 _45619) = (term279 _45617 _45618 _45619).
Proof. exact (MK_COMB (@lem3926850) (@lem3926849 _45617 _45618 _45619)). Qed.
Lemma lem3926852 (_45617 : nat) (_45619 : nat) : (Peano.le _45617 _45619) = (Peano.le _45617 _45619).
Proof. exact (eq_refl (Peano.le _45617 _45619)). Qed.
Lemma lem3926853 (_45618 : nat) (_45617 : nat) (_45619 : nat) : (term275 _45618 _45617 _45619) = (term48 _45618 _45617 _45619).
Proof. exact (MK_COMB (@lem3926851 _45617 _45618 _45619) (@lem3926852 _45617 _45619)). Qed.
Lemma lem3926854 (_45618 : nat) (_45617 : nat) (_45619 : nat) : (term272 _45617 _45618 _45619) = (term48 _45618 _45617 _45619).
Proof. exact (TRANS (@lem3926836 _45618 _45617 _45619) (@lem3926853 _45618 _45617 _45619)). Qed.
Lemma lem3926856 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term68 A s t m n) : term280 A s t m n.
Proof. exact (conj (@lem3926641 A s t m n h1 h3) (@lem3926761 A s t m n h2 h3)). Qed.
Lemma lem3926858 (_45618 : nat) (_45617 : nat) (_45619 : nat) (h1 : term54) : term48 _45618 _45617 _45619.
Proof. exact (EQ_MP (@lem3926854 _45618 _45617 _45619) (@lem3926833 _45617 _45618 _45619 h1)). Qed.
Lemma lem3926859 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term54) : term281 A s t m n.
Proof. exact (@lem3926858 (term282 A s t) (term283 A s t) (Nat.add m n) h1). Qed.
Lemma lem3926862 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term68 A s t m n) : term65 A s t m n.
Proof. exact (@lem3926859 A s t m n h3 (@lem3926856 A s t m n h1 h2 h4)). Qed.
Lemma lem3926863 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term68 A s t m n) : term284 A s t m n.
Proof. exact (fun h0 : term203 A s t m n => @lem3926862 A s t m n h1 h2 h3 h4). Qed.
Lemma lem3926865 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term284 A s t m n) = (term65 A s t m n).
Proof. exact (@lem3926865 (term65 A s t m n)). Qed.
Lemma lem3926867 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term68 A s t m n) : term65 A s t m n.
Proof. exact (EQ_MP (@lem3926866 A s t m n) (@lem3926863 A s t m n h1 h2 h3 h4)). Qed.
Lemma lem3926870 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3926872 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) : (term203 A s t m n) = (term285 A s t m n).
Proof. exact (@lem3926870 (term65 A s t m n)). Qed.
Lemma lem3926875 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term203 A s t m n) : term285 A s t m n.
Proof. exact (EQ_MP (@lem3926872 A s t m n) (@lem3926443 A s t m n h1)). Qed.
Lemma lem3926878 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : False.
Proof. exact (@lem3926875 A s t m n h4 (@lem3926867 A s t m n h1 h2 h3 h5)). Qed.
Lemma lem3926879 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : term235.
Proof. exact (fun h0 : ~ False => @lem3926878 A s t m n h1 h2 h3 h4 h5). Qed.
Lemma lem3926881 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3926882 : term235 = False.
Proof. exact (@lem3926881 False). Qed.
Lemma lem3926883 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926882) (@lem3926879 A s t m n h1 h2 h3 h4 h5)). Qed.
Lemma lem3926884 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : (term203 A s t m n) = False.
Proof. exact (prop_ext (fun h6 : term203 A s t m n => @lem3926883 A s t m n h1 h2 h3 h4 h5) (fun h6 : False => @lem3926443 A s t m n h4)). Qed.
Lemma lem3926885 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926884 A s t m n h1 h2 h3 h4 h5) (@lem3926443 A s t m n h4)). Qed.
Lemma lem3926886 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : (term202 A s t) = False.
Proof. exact (prop_ext (fun h4 : term202 A s t => @lem3926520 A s t m n h1 h2 h3) (fun h4 : False => @lem3926375 A s t h2)). Qed.
Lemma lem3926887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926886 A s t m n h1 h2 h3) (@lem3926375 A s t h2)). Qed.
Lemma lem3926888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : (term203 A s t m n) = False.
Proof. exact (prop_ext (fun h6 : term203 A s t m n => @lem3926885 A s t m n h1 h2 h3 h4 h5) (fun h6 : False => @lem3926237 A s t m n h4)). Qed.
Lemma lem3926889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926888 A s t m n h1 h2 h3 h4 h5) (@lem3926237 A s t m n h4)). Qed.
Lemma lem3926890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : (term202 A s t) = False.
Proof. exact (prop_ext (fun h4 : term202 A s t => @lem3926887 A s t m n h1 h2 h3) (fun h4 : False => @lem3926094 A s t h2)). Qed.
Lemma lem3926891 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926890 A s t m n h1 h2 h3) (@lem3926094 A s t h2)). Qed.
Lemma lem3926892 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : (term203 A s t m n) = False.
Proof. exact (prop_ext (fun h6 : term203 A s t m n => @lem3926889 A s t m n h1 h2 h3 h4 h5) (fun h6 : False => @lem3926237 A s t m n h4)). Qed.
Lemma lem3926893 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term203 A s t m n) (h5 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926892 A s t m n h1 h2 h3 h4 h5) (@lem3926237 A s t m n h4)). Qed.
Lemma lem3926894 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : (term202 A s t) = False.
Proof. exact (prop_ext (fun h4 : term202 A s t => @lem3926891 A s t m n h1 h2 h3) (fun h4 : False => @lem3926094 A s t h2)). Qed.
Lemma lem3926895 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term202 A s t) (h3 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926894 A s t m n h1 h2 h3) (@lem3926094 A s t h2)). Qed.
Lemma lem3926896 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term12 A) (h3 : term47) (h4 : term54) (h5 : term68 A s t m n) : False.
Proof. exact (or_elim (@lem3925940 A s t m n h5) (fun h0 : term202 A s t => @lem3926895 A s t m n h1 h0 h5) (fun h0 : term203 A s t m n => @lem3926893 A s t m n h2 h3 h4 h0 h5)). Qed.
Lemma lem3926897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term12 A) (h3 : term47) (h4 : term54) (h5 : term68 A s t m n) : (term68 A s t m n) = False.
Proof. exact (prop_ext (fun h6 : term68 A s t m n => @lem3926896 A s t m n h1 h2 h3 h4 h5) (fun h6 : False => @lem3925939 A s t m n h5)). Qed.
Lemma lem3926898 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (n : nat) (h1 : term11 A) (h2 : term12 A) (h3 : term47) (h4 : term54) (h5 : term68 A s t m n) : False.
Proof. exact (EQ_MP (@lem3926897 A s t m n h1 h2 h3 h4 h5) (@lem3925939 A s t m n h5)). Qed.
Lemma lem3926899 {A : Type'} (s : A -> Prop) (t : A -> Prop) (m : nat) (h1 : term11 A) (h2 : term12 A) (h3 : term47) (h4 : term54) (h5 : term80 A s t m) : False.
Proof. exact (ex_elim (@lem3925693 A s t m h5) (fun n : nat => fun h0 : term79 A s t m n => @lem3926898 A s t m n h1 h2 h3 h4 h0)). Qed.
Lemma lem3926900 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) (h2 : term12 A) (h3 : term47) (h4 : term54) (h5 : term87 A s t) : False.
Proof. exact (ex_elim (@lem3925692 A s t h5) (fun m : nat => fun h0 : term86 A s t m => @lem3926899 A s t m h1 h2 h3 h4 h0)). Qed.
Lemma lem3926901 {A : Type'} (s : A -> Prop) (h1 : term11 A) (h2 : term12 A) (h3 : term47) (h4 : term54) (h5 : term96 A s) : False.
Proof. exact (ex_elim (@lem3925691 A s h5) (fun t : A -> Prop => fun h0 : term95 A s t => @lem3926900 A s t h1 h2 h3 h4 h0)). Qed.
Lemma lem3926902 {A : Type'} (h1 : term11 A) (h2 : term12 A) (h3 : term47) (h4 : term54) (h5 : term10 A) : False.
Proof. exact (ex_elim (@lem3925144 A h5) (fun s : A -> Prop => fun h0 : term101 A s => @lem3926901 A s h1 h2 h3 h4 h0)). Qed.
Lemma lem3926903 {A : Type'} (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term10 A) : term17 A.
Proof. exact (fun h0 : term11 A => @lem3926902 A h0 h1 h2 h3 h4). Qed.
Lemma lem3926904 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem3926905 {A : Type'} (h1 : term12 A) (h2 : term47) (h3 : term54) (h4 : term10 A) : term18 A.
Proof. exact (EQ_MP (@lem3926904 A) (@lem3926903 A h1 h2 h3 h4)). Qed.
Lemma lem3926906 {A : Type'} (h1 : term47) (h2 : term54) (h3 : term10 A) : term21 A.
Proof. exact (fun h0 : term12 A => @lem3926905 A h0 h1 h2 h3). Qed.
Lemma lem3926907 {A : Type'} (h1 : term54) (h2 : term10 A) : term24 A.
Proof. exact (fun h0 : term47 => @lem3926906 A h0 h1 h2). Qed.
Lemma lem3926908 {A : Type'} (h1 : term10 A) : term27 A.
Proof. exact (fun h0 : term54 => @lem3926907 A h0 h1). Qed.
Lemma lem3926909 {A : Type'} : term29 A.
Proof. exact (fun h0 : term10 A => @lem3926908 A h0). Qed.
Lemma lem3926910 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3925009 A) (@lem3926909 A)). Qed.
Lemma lem3926912 {A : Type'} : term13 A.
Proof. exact (@lem3924650 A (@lem3926910 A)). Qed.
Lemma lem3926913 {A : Type'} (h1 : term10 A) : term26 A.
Proof. exact (@lem3926912 A (@lem3924629 A h1)). Qed.
Lemma lem3926914 {A : Type'} (h1 : term10 A) : term23 A.
Proof. exact (@lem3926913 A h1 (@lem93743)). Qed.
Lemma lem3926915 {A : Type'} (h1 : term10 A) : term20 A.
Proof. exact (@lem3926914 A h1 (@lem101399)). Qed.
Lemma lem3926916 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem3926915 A h1 (@lem3924632 A)). Qed.
Lemma lem3926917 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem3926916 A h1 (@lem3924630 A)). Qed.
Lemma lem3926918 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem3926917 A h1) (fun h2 : False => @lem3924629 A h1)). Qed.
Lemma lem3926919 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem3926918 A h1) (@lem3924629 A h1)). Qed.
Lemma lem3926920 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem3926919 A h0). Qed.
Lemma lem3926921 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3924628 A) (@lem3926920 A)). Qed.
