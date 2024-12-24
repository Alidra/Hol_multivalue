Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_SUM_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import NSUM_CLAUSES_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1340339_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7168713 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem7168714 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem7168713 m n h1)). Qed.
Lemma lem7168715 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem7168716 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem7168715 m n h1)). Qed.
Lemma lem7168717 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem7168714 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem7168716 m n h1)). Qed.
Lemma lem7168718 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem7168717 m n)). Qed.
Lemma lem7168719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7168720 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem7168719) (@lem7168718 m)). Qed.
Lemma lem7168721 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem7168720 m)). Qed.
Lemma lem7168722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7168723 : term8 = term9.
Proof. exact (MK_COMB (@lem7168722) (@lem7168721)). Qed.
Lemma lem7168724 : term9.
Proof. exact (EQ_MP (@lem7168723) (@lem1340339)). Qed.
Lemma lem7168725 (m : nat) : term10 m.
Proof. exact (@lem7168724 m). Qed.
Lemma lem7168726 (m : nat) : (term10 m) = (term5 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem7168727 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem7168726 m) (@lem7168725 m)). Qed.
Lemma lem7168728 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem7168727 m n). Qed.
Lemma lem7168729 (m : nat) (n : nat) : (term11 m n) = ((term1 m n) = (term0 m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem7168731 {_126525 : Type'} : term12 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem7168732 {_126525 : Type'} (x : _126525) : term13 _126525 x.
Proof. exact (@lem7168731 _126525 x). Qed.
Lemma lem7168733 {_126525 : Type'} (x : _126525) : (term13 _126525 x) = (term14 _126525 x).
Proof. exact (eq_refl (term13 _126525 x)). Qed.
Lemma lem7168734 {_126525 : Type'} (x : _126525) : term14 _126525 x.
Proof. exact (EQ_MP (@lem7168733 _126525 x) (@lem7168732 _126525 x)). Qed.
Lemma lem7168735 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term15 _126525 x f.
Proof. exact (@lem7168734 _126525 x f). Qed.
Lemma lem7168736 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term15 _126525 x f) = (term16 _126525 x f).
Proof. exact (eq_refl (term15 _126525 x f)). Qed.
Lemma lem7168737 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term16 _126525 x f.
Proof. exact (EQ_MP (@lem7168736 _126525 x f) (@lem7168735 _126525 x f)). Qed.
Lemma lem7168738 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term17 _126525 x f s.
Proof. exact (@lem7168737 _126525 x f s). Qed.
Lemma lem7168739 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term17 _126525 x f s) = (term18 _126525 x s f).
Proof. exact (eq_refl (term17 _126525 x f s)). Qed.
Lemma lem7168740 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term18 _126525 x s f.
Proof. exact (EQ_MP (@lem7168739 _126525 x s f) (@lem7168738 _126525 x f s)). Qed.
Lemma lem7168741 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem7168742 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term19 _126525 x s f) = (term20 _126525 x s f).
Proof. exact (@lem7168740 _126525 x s f (@lem7168741 _126525 s h1)). Qed.
Lemma lem7168748 {_126486 : Type'} : term21 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem7168749 {_126486 : Type'} (f : _126486 -> nat) : term22 _126486 f.
Proof. exact (@lem7168748 _126486 f). Qed.
Lemma lem7168750 {_126486 : Type'} (f : _126486 -> nat) : (term22 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term22 _126486 f)). Qed.
Lemma lem7168752 {_131524 : Type'} : term23 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7168753 {_131524 : Type'} (x : _131524) : term24 _131524 x.
Proof. exact (@lem7168752 _131524 x). Qed.
Lemma lem7168754 {_131524 : Type'} (x : _131524) : (term24 _131524 x) = (term25 _131524 x).
Proof. exact (eq_refl (term24 _131524 x)). Qed.
Lemma lem7168755 {_131524 : Type'} (x : _131524) : term25 _131524 x.
Proof. exact (EQ_MP (@lem7168754 _131524 x) (@lem7168753 _131524 x)). Qed.
Lemma lem7168756 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term26 _131524 x f.
Proof. exact (@lem7168755 _131524 x f). Qed.
Lemma lem7168757 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term26 _131524 x f) = (term27 _131524 x f).
Proof. exact (eq_refl (term26 _131524 x f)). Qed.
Lemma lem7168758 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term27 _131524 x f.
Proof. exact (EQ_MP (@lem7168757 _131524 x f) (@lem7168756 _131524 x f)). Qed.
Lemma lem7168759 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term28 _131524 x f s.
Proof. exact (@lem7168758 _131524 x f s). Qed.
Lemma lem7168760 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term28 _131524 x f s) = (term29 _131524 x s f).
Proof. exact (eq_refl (term28 _131524 x f s)). Qed.
Lemma lem7168761 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term29 _131524 x s f.
Proof. exact (EQ_MP (@lem7168760 _131524 x s f) (@lem7168759 _131524 x f s)). Qed.
Lemma lem7168762 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7168763 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term30 _131524 x s f) = (term31 _131524 x s f).
Proof. exact (@lem7168761 _131524 x s f (@lem7168762 _131524 s h1)). Qed.
Lemma lem7168769 {_131483 : Type'} : term32 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7168770 {_131483 : Type'} (f : _131483 -> real) : term33 _131483 f.
Proof. exact (@lem7168769 _131483 f). Qed.
Lemma lem7168771 {_131483 : Type'} (f : _131483 -> real) : (term33 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term34).
Proof. exact (eq_refl (term33 _131483 f)). Qed.
Lemma lem7168773 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem7168774 {A : Type'} (P : type686 A) (h1 : term35 A) : term36 A P.
Proof. exact (@lem7168773 A h1 P). Qed.
Lemma lem7168775 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem7168776 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (EQ_MP (@lem7168775 A P) (@lem7168774 A P h1)). Qed.
Lemma lem7168777 {A : Type'} (P : type686 A) (h1 : term38 A P) : term38 A P.
Proof. exact (h1). Qed.
Lemma lem7168778 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem7168776 A P h1 (@lem7168777 A P h2)). Qed.
Lemma lem7168779 {A : Type'} (P : type686 A) (h1 : term38 A P) : term40 A P.
Proof. exact (fun h0 : term35 A => @lem7168778 A P h0 h1). Qed.
Lemma lem7168780 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem7168781 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem7168779 A P h2 (@lem7168780 A h1)). Qed.
Lemma lem7168782 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (fun h0 : term38 A P => @lem7168781 A P h1 h0). Qed.
Lemma lem7168783 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun P : type686 A => @lem7168782 A P h1). Qed.
Lemma lem7168784 {A : Type'} : term41 A.
Proof. exact (fun h0 : term35 A => @lem7168783 A h0). Qed.
Lemma lem7168785 {A : Type'} : term35 A.
Proof. exact (@lem7168784 A (@lem3558722 A)). Qed.
Lemma lem7168786 {A : Type'} (P : type686 A) : term36 A P.
Proof. exact (@lem7168785 A P). Qed.
Lemma lem7168787 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem7168790 {A : Type'} (P : type686 A) : term37 A P.
Proof. exact (EQ_MP (@lem7168787 A P) (@lem7168786 A P)). Qed.
Lemma lem7168791 {_134498 : Type'} (P : type686 _134498) : term37 _134498 P.
Proof. exact (@lem7168790 _134498 P). Qed.
Lemma lem7168792 {_134498 : Type'} (f : _134498 -> nat) : term42 _134498 f.
Proof. exact (@lem7168791 _134498 (term43 _134498 f)). Qed.
Lemma lem7168793 {_134498 : Type'} (f : _134498 -> nat) : (term44 _134498 f) = ((term45 _134498 f) = (term46 _134498 f)).
Proof. exact (eq_refl (term44 _134498 f)). Qed.
Lemma lem7168794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7168795 {_134498 : Type'} (f : _134498 -> nat) : (term47 _134498 f) = (term48 _134498 f).
Proof. exact (MK_COMB (@lem7168794) (@lem7168793 _134498 f)). Qed.
Lemma lem7168796 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term49 _134498 f s) = ((term50 _134498 s f) = (term51 _134498 s f)).
Proof. exact (eq_refl (term49 _134498 f s)). Qed.
Lemma lem7168797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7168798 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term52 _134498 f s) = (term53 _134498 s f).
Proof. exact (MK_COMB (@lem7168797) (@lem7168796 _134498 s f)). Qed.
Lemma lem7168799 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) : (term54 _134498 x s) = (term54 _134498 x s).
Proof. exact (eq_refl (term54 _134498 x s)). Qed.
Lemma lem7168800 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) : (term55 _134498 f x s) = (term56 _134498 f x s).
Proof. exact (MK_COMB (@lem7168798 _134498 s f) (@lem7168799 _134498 x s)). Qed.
Lemma lem7168801 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7168802 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) : (term57 _134498 f x s) = (term58 _134498 f x s).
Proof. exact (MK_COMB (@lem7168801) (@lem7168800 _134498 f x s)). Qed.
Lemma lem7168803 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term59 _134498 f x s) = ((term60 _134498 x s f) = (term61 _134498 x s f)).
Proof. exact (eq_refl (term59 _134498 f x s)). Qed.
Lemma lem7168804 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term62 _134498 f x s) = (term63 _134498 x s f).
Proof. exact (MK_COMB (@lem7168802 _134498 f x s) (@lem7168803 _134498 x s f)). Qed.
Lemma lem7168805 {_134498 : Type'} (x : _134498) (f : _134498 -> nat) : (term64 _134498 f x) = (term65 _134498 x f).
Proof. exact (fun_ext (fun s : _134498 -> Prop => @lem7168804 _134498 x s f)). Qed.
Lemma lem7168806 {_134498 : Type'} : (@all (_134498 -> Prop)) = (@all (_134498 -> Prop)).
Proof. exact (eq_refl (@all (_134498 -> Prop))). Qed.
Lemma lem7168807 {_134498 : Type'} (x : _134498) (f : _134498 -> nat) : (term66 _134498 f x) = (term67 _134498 x f).
Proof. exact (MK_COMB (@lem7168806 _134498) (@lem7168805 _134498 x f)). Qed.
Lemma lem7168808 {_134498 : Type'} (f : _134498 -> nat) : (term68 _134498 f) = (term69 _134498 f).
Proof. exact (fun_ext (fun x : _134498 => @lem7168807 _134498 x f)). Qed.
Lemma lem7168809 {_134498 : Type'} : (@all _134498) = (@all _134498).
Proof. exact (eq_refl (@all _134498)). Qed.
Lemma lem7168810 {_134498 : Type'} (f : _134498 -> nat) : (term70 _134498 f) = (term71 _134498 f).
Proof. exact (MK_COMB (@lem7168809 _134498) (@lem7168808 _134498 f)). Qed.
Lemma lem7168811 {_134498 : Type'} (f : _134498 -> nat) : (term72 _134498 f) = (term73 _134498 f).
Proof. exact (MK_COMB (@lem7168795 _134498 f) (@lem7168810 _134498 f)). Qed.
Lemma lem7168812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7168813 {_134498 : Type'} (f : _134498 -> nat) : (term74 _134498 f) = (term75 _134498 f).
Proof. exact (MK_COMB (@lem7168812) (@lem7168811 _134498 f)). Qed.
Lemma lem7168814 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term49 _134498 f s) = ((term50 _134498 s f) = (term51 _134498 s f)).
Proof. exact (eq_refl (term49 _134498 f s)). Qed.
Lemma lem7168815 {_134498 : Type'} (s : _134498 -> Prop) : (term76 _134498 s) = (term76 _134498 s).
Proof. exact (eq_refl (term76 _134498 s)). Qed.
Lemma lem7168816 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term77 _134498 f s) = (term78 _134498 s f).
Proof. exact (MK_COMB (@lem7168815 _134498 s) (@lem7168814 _134498 s f)). Qed.
Lemma lem7168817 {_134498 : Type'} (f : _134498 -> nat) : (term79 _134498 f) = (term80 _134498 f).
Proof. exact (fun_ext (fun s : _134498 -> Prop => @lem7168816 _134498 s f)). Qed.
Lemma lem7168818 {_134498 : Type'} : (@all (_134498 -> Prop)) = (@all (_134498 -> Prop)).
Proof. exact (eq_refl (@all (_134498 -> Prop))). Qed.
Lemma lem7168819 {_134498 : Type'} (f : _134498 -> nat) : (term81 _134498 f) = (term82 _134498 f).
Proof. exact (MK_COMB (@lem7168818 _134498) (@lem7168817 _134498 f)). Qed.
Lemma lem7168820 {_134498 : Type'} (f : _134498 -> nat) : (term42 _134498 f) = (term83 _134498 f).
Proof. exact (MK_COMB (@lem7168813 _134498 f) (@lem7168819 _134498 f)). Qed.
Lemma lem7168821 {_134498 : Type'} (f : _134498 -> nat) : term83 _134498 f.
Proof. exact (EQ_MP (@lem7168820 _134498 f) (@lem7168792 _134498 f)). Qed.
Lemma lem7168827 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7168750 _126486 f) (@lem7168749 _126486 f)). Qed.
Lemma lem7168828 {_134498 : Type'} (f : _134498 -> nat) : (@nsum _134498 (@EMPTY _134498) f) = (NUMERAL 0).
Proof. exact (@lem7168827 _134498 f). Qed.
Lemma lem7168829 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7168830 {_134498 : Type'} (f : _134498 -> nat) : (term45 _134498 f) = term34.
Proof. exact (MK_COMB (@lem7168829) (@lem7168828 _134498 f)). Qed.
Lemma lem7168831 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7168832 {_134498 : Type'} (f : _134498 -> nat) : (term84 _134498 f) = term85.
Proof. exact (MK_COMB (@lem7168831) (@lem7168830 _134498 f)). Qed.
Lemma lem7168834 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term34.
Proof. exact (EQ_MP (@lem7168771 _131483 f) (@lem7168770 _131483 f)). Qed.
Lemma lem7168835 {_134498 : Type'} (f : _134498 -> real) : (@sum _134498 (@EMPTY _134498) f) = term34.
Proof. exact (@lem7168834 _134498 f). Qed.
Lemma lem7168836 {_134498 : Type'} (f : _134498 -> nat) : (term46 _134498 f) = term34.
Proof. exact (@lem7168835 _134498 (term86 _134498 f)). Qed.
Lemma lem7168837 {_134498 : Type'} (f : _134498 -> nat) : ((term45 _134498 f) = (term46 _134498 f)) = (term34 = term34).
Proof. exact (MK_COMB (@lem7168832 _134498 f) (@lem7168836 _134498 f)). Qed.
Lemma lem7168839 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7168840 (x : real) : (x = x) = True.
Proof. exact (@lem7168839 real x). Qed.
Lemma lem7168841 : (term34 = term34) = True.
Proof. exact (@lem7168840 term34). Qed.
Lemma lem7168842 {_134498 : Type'} (f : _134498 -> nat) : ((term45 _134498 f) = (term46 _134498 f)) = True.
Proof. exact (TRANS (@lem7168837 _134498 f) (@lem7168841)). Qed.
Lemma lem7168843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7168844 {_134498 : Type'} (f : _134498 -> nat) : (term48 _134498 f) = (and True).
Proof. exact (MK_COMB (@lem7168843) (@lem7168842 _134498 f)). Qed.
Lemma lem7168856 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term87 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7168857 (p : Prop) (q : Prop) (p' : Prop) : term88 p q p'.
Proof. exact (fun q' : Prop => @lem7168856 p q p' q'). Qed.
Lemma lem7168858 (p : Prop) (q : Prop) : term89 p q.
Proof. exact (fun p' : Prop => @lem7168857 p q p'). Qed.
Lemma lem7168859 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term90 _134498 x s f.
Proof. exact (@lem7168858 (term56 _134498 f x s) ((term60 _134498 x s f) = (term61 _134498 x s f))). Qed.
Lemma lem7168860 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (p' : Prop) : term91 _134498 x s f p'.
Proof. exact (@lem7168859 _134498 x s f p'). Qed.
Lemma lem7168861 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (p' : Prop) : (term91 _134498 x s f p') = (term92 _134498 x s f p').
Proof. exact (eq_refl (term91 _134498 x s f p')). Qed.
Lemma lem7168862 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (p' : Prop) : term92 _134498 x s f p'.
Proof. exact (EQ_MP (@lem7168861 _134498 x s f p') (@lem7168860 _134498 x s f p')). Qed.
Lemma lem7168863 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (p' : Prop) (q' : Prop) : term93 _134498 x s f p' q'.
Proof. exact (@lem7168862 _134498 x s f p' q'). Qed.
Lemma lem7168864 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (p' : Prop) (q' : Prop) : (term93 _134498 x s f p' q') = (term94 _134498 x s f p' q').
Proof. exact (eq_refl (term93 _134498 x s f p' q')). Qed.
Lemma lem7168865 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (p' : Prop) (q' : Prop) : term94 _134498 x s f p' q'.
Proof. exact (EQ_MP (@lem7168864 _134498 x s f p' q') (@lem7168863 _134498 x s f p' q')). Qed.
Lemma lem7168872 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) : (term56 _134498 f x s) = (term56 _134498 f x s).
Proof. exact (eq_refl (term56 _134498 f x s)). Qed.
Lemma lem7168873 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (q' : Prop) : term95 _134498 f x s q'.
Proof. exact (@lem7168865 _134498 x s f (term56 _134498 f x s) q'). Qed.
Lemma lem7168874 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (q' : Prop) : term96 _134498 f x s q'.
Proof. exact (@lem7168873 _134498 f x s q' (@lem7168872 _134498 f x s)). Qed.
Lemma lem7168875 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term56 _134498 f x s.
Proof. exact (h1). Qed.
Lemma lem7168876 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term54 _134498 x s.
Proof. exact (proj2 (@lem7168875 _134498 f x s h1)). Qed.
Lemma lem7168877 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : @FINITE _134498 s.
Proof. exact (proj2 (@lem7168876 _134498 f x s h1)). Qed.
Lemma lem7168878 {_134498 : Type'} (s : _134498 -> Prop) : (@FINITE _134498 s) = ((@FINITE _134498 s) = True).
Proof. exact (@lem7 (@FINITE _134498 s)). Qed.
Lemma lem7168880 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term97 _134498 x s.
Proof. exact (proj1 (@lem7168876 _134498 f x s h1)). Qed.
Lemma lem7168881 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) : term98 _134498 x s.
Proof. exact (@lem82 (@IN _134498 x s)). Qed.
Lemma lem7168887 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term18 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem7168742 _126525 x f s h0). Qed.
Lemma lem7168888 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term18 _134498 x s f.
Proof. exact (@lem7168887 _134498 x s f). Qed.
Lemma lem7168890 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (@FINITE _134498 s) = True.
Proof. exact (EQ_MP (@lem7168878 _134498 s) (@lem7168877 _134498 f x s h1)). Qed.
Lemma lem7168891 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : True = (@FINITE _134498 s).
Proof. exact (SYM (@lem7168890 _134498 f x s h1)). Qed.
Lemma lem7168892 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : @FINITE _134498 s.
Proof. exact (EQ_MP (@lem7168891 _134498 f x s h1) (@lem0)). Qed.
Lemma lem7168893 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term19 _134498 x s f) = (term20 _134498 x s f).
Proof. exact (@lem7168888 _134498 x s f (@lem7168892 _134498 f x s h1)). Qed.
Lemma lem7168895 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term99 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7168896 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term100 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7168895 _2963 g t e g' t' e'). Qed.
Lemma lem7168897 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term101 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7168896 _2963 g t e g' t'). Qed.
Lemma lem7168898 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term102 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7168897 _2963 g t e g'). Qed.
Lemma lem7168899 (g : Prop) (t : nat) (e : nat) : term103 g t e.
Proof. exact (@lem7168898 nat g t e). Qed.
Lemma lem7168900 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term104 _134498 x s f.
Proof. exact (@lem7168899 (@IN _134498 x s) (@nsum _134498 s f) (term105 _134498 x s f)). Qed.
Lemma lem7168901 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) : term106 _134498 x s f g'.
Proof. exact (@lem7168900 _134498 x s f g'). Qed.
Lemma lem7168902 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) : (term106 _134498 x s f g') = (term107 _134498 x s f g').
Proof. exact (eq_refl (term106 _134498 x s f g')). Qed.
Lemma lem7168903 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) : term107 _134498 x s f g'.
Proof. exact (EQ_MP (@lem7168902 _134498 x s f g') (@lem7168901 _134498 x s f g')). Qed.
Lemma lem7168904 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : nat) : term108 _134498 x s f g' t'.
Proof. exact (@lem7168903 _134498 x s f g' t'). Qed.
Lemma lem7168905 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : nat) : (term108 _134498 x s f g' t') = (term109 _134498 x s f g' t').
Proof. exact (eq_refl (term108 _134498 x s f g' t')). Qed.
Lemma lem7168906 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : nat) : term109 _134498 x s f g' t'.
Proof. exact (EQ_MP (@lem7168905 _134498 x s f g' t') (@lem7168904 _134498 x s f g' t')). Qed.
Lemma lem7168907 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term110 _134498 x s f g' t' e'.
Proof. exact (@lem7168906 _134498 x s f g' t' e'). Qed.
Lemma lem7168908 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term110 _134498 x s f g' t' e') = (term111 _134498 x s f g' t' e').
Proof. exact (eq_refl (term110 _134498 x s f g' t' e')). Qed.
Lemma lem7168909 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term111 _134498 x s f g' t' e'.
Proof. exact (EQ_MP (@lem7168908 _134498 x s f g' t' e') (@lem7168907 _134498 x s f g' t' e')). Qed.
Lemma lem7168911 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (@IN _134498 x s) = False.
Proof. exact (@lem7168881 _134498 x s (@lem7168880 _134498 f x s h1)). Qed.
Lemma lem7168912 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (t' : nat) (e' : nat) : term112 _134498 x s f t' e'.
Proof. exact (@lem7168909 _134498 x s f False t' e'). Qed.
Lemma lem7168913 {_134498 : Type'} (t' : nat) (e' : nat) (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term113 _134498 x s f t' e'.
Proof. exact (@lem7168912 _134498 x s f t' e' (@lem7168911 _134498 f x s h1)). Qed.
Lemma lem7168917 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (@nsum _134498 s f) = (@nsum _134498 s f).
Proof. exact (eq_refl (@nsum _134498 s f)). Qed.
Lemma lem7168918 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : term114 _134498 s f.
Proof. exact (fun h0 : False => @lem7168917 _134498 s f). Qed.
Lemma lem7168919 {_134498 : Type'} (e' : nat) (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term115 _134498 x s f e'.
Proof. exact (@lem7168913 _134498 (@nsum _134498 s f) e' f x s h1). Qed.
Lemma lem7168920 {_134498 : Type'} (e' : nat) (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term116 _134498 x s f e'.
Proof. exact (@lem7168919 _134498 e' f x s h1 (@lem7168918 _134498 s f)). Qed.
Lemma lem7168926 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term105 _134498 x s f) = (term105 _134498 x s f).
Proof. exact (eq_refl (term105 _134498 x s f)). Qed.
Lemma lem7168927 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term117 _134498 x s f.
Proof. exact (fun h0 : ~ False => @lem7168926 _134498 x s f). Qed.
Lemma lem7168928 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term118 _134498 x s f.
Proof. exact (@lem7168920 _134498 (term105 _134498 x s f) f x s h1). Qed.
Lemma lem7168929 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term20 _134498 x s f) = (term119 _134498 x s f).
Proof. exact (@lem7168928 _134498 f x s h1 (@lem7168927 _134498 x s f)). Qed.
Lemma lem7168931 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7168932 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7168931 nat t1 t2). Qed.
Lemma lem7168933 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term119 _134498 x s f) = (term105 _134498 x s f).
Proof. exact (@lem7168932 (@nsum _134498 s f) (term105 _134498 x s f)). Qed.
Lemma lem7168934 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term20 _134498 x s f) = (term105 _134498 x s f).
Proof. exact (TRANS (@lem7168929 _134498 f x s h1) (@lem7168933 _134498 x s f)). Qed.
Lemma lem7168935 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term19 _134498 x s f) = (term105 _134498 x s f).
Proof. exact (TRANS (@lem7168893 _134498 f x s h1) (@lem7168934 _134498 f x s h1)). Qed.
Lemma lem7168936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7168937 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term60 _134498 x s f) = (term120 _134498 x s f).
Proof. exact (MK_COMB (@lem7168936) (@lem7168935 _134498 f x s h1)). Qed.
Lemma lem7168939 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (EQ_MP (@lem7168729 m n) (@lem7168728 m n)). Qed.
Lemma lem7168940 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term120 _134498 x s f) = (term121 _134498 x s f).
Proof. exact (@lem7168939 (f x) (@nsum _134498 s f)). Qed.
Lemma lem7168942 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term50 _134498 s f) = (term51 _134498 s f).
Proof. exact (proj1 (@lem7168875 _134498 f x s h1)). Qed.
Lemma lem7168943 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term122 _134498 f x) = (term122 _134498 f x).
Proof. exact (eq_refl (term122 _134498 f x)). Qed.
Lemma lem7168944 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term121 _134498 x s f) = (term123 _134498 x s f).
Proof. exact (MK_COMB (@lem7168943 _134498 f x) (@lem7168942 _134498 f x s h1)). Qed.
Lemma lem7168945 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term120 _134498 x s f) = (term123 _134498 x s f).
Proof. exact (TRANS (@lem7168940 _134498 x s f) (@lem7168944 _134498 f x s h1)). Qed.
Lemma lem7168946 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term60 _134498 x s f) = (term123 _134498 x s f).
Proof. exact (TRANS (@lem7168937 _134498 f x s h1) (@lem7168945 _134498 f x s h1)). Qed.
Lemma lem7168947 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7168948 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term124 _134498 x s f) = (term125 _134498 x s f).
Proof. exact (MK_COMB (@lem7168947) (@lem7168946 _134498 f x s h1)). Qed.
Lemma lem7168950 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term29 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7168763 _131524 x f s h0). Qed.
Lemma lem7168951 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> real) : term29 _134498 x s f.
Proof. exact (@lem7168950 _134498 x s f). Qed.
Lemma lem7168952 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term126 _134498 x s f.
Proof. exact (@lem7168951 _134498 x s (term86 _134498 f)). Qed.
Lemma lem7168954 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (@FINITE _134498 s) = True.
Proof. exact (EQ_MP (@lem7168878 _134498 s) (@lem7168877 _134498 f x s h1)). Qed.
Lemma lem7168955 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : True = (@FINITE _134498 s).
Proof. exact (SYM (@lem7168954 _134498 f x s h1)). Qed.
Lemma lem7168956 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : @FINITE _134498 s.
Proof. exact (EQ_MP (@lem7168955 _134498 f x s h1) (@lem0)). Qed.
Lemma lem7168957 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term61 _134498 x s f) = (term127 _134498 x s f).
Proof. exact (@lem7168952 _134498 x s f (@lem7168956 _134498 f x s h1)). Qed.
Lemma lem7168959 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term99 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7168960 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term100 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7168959 _2963 g t e g' t' e'). Qed.
Lemma lem7168961 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term101 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7168960 _2963 g t e g' t'). Qed.
Lemma lem7168962 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term102 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7168961 _2963 g t e g'). Qed.
Lemma lem7168963 (g : Prop) (t : real) (e : real) : term128 g t e.
Proof. exact (@lem7168962 real g t e). Qed.
Lemma lem7168964 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term129 _134498 x s f.
Proof. exact (@lem7168963 (@IN _134498 x s) (term51 _134498 s f) (term130 _134498 x s f)). Qed.
Lemma lem7168965 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) : term131 _134498 x s f g'.
Proof. exact (@lem7168964 _134498 x s f g'). Qed.
Lemma lem7168966 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) : (term131 _134498 x s f g') = (term132 _134498 x s f g').
Proof. exact (eq_refl (term131 _134498 x s f g')). Qed.
Lemma lem7168967 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) : term132 _134498 x s f g'.
Proof. exact (EQ_MP (@lem7168966 _134498 x s f g') (@lem7168965 _134498 x s f g')). Qed.
Lemma lem7168968 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : real) : term133 _134498 x s f g' t'.
Proof. exact (@lem7168967 _134498 x s f g' t'). Qed.
Lemma lem7168969 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : real) : (term133 _134498 x s f g' t') = (term134 _134498 x s f g' t').
Proof. exact (eq_refl (term133 _134498 x s f g' t')). Qed.
Lemma lem7168970 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : real) : term134 _134498 x s f g' t'.
Proof. exact (EQ_MP (@lem7168969 _134498 x s f g' t') (@lem7168968 _134498 x s f g' t')). Qed.
Lemma lem7168971 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : real) (e' : real) : term135 _134498 x s f g' t' e'.
Proof. exact (@lem7168970 _134498 x s f g' t' e'). Qed.
Lemma lem7168972 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : real) (e' : real) : (term135 _134498 x s f g' t' e') = (term136 _134498 x s f g' t' e').
Proof. exact (eq_refl (term135 _134498 x s f g' t' e')). Qed.
Lemma lem7168973 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (g' : Prop) (t' : real) (e' : real) : term136 _134498 x s f g' t' e'.
Proof. exact (EQ_MP (@lem7168972 _134498 x s f g' t' e') (@lem7168971 _134498 x s f g' t' e')). Qed.
Lemma lem7168975 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (@IN _134498 x s) = False.
Proof. exact (@lem7168881 _134498 x s (@lem7168880 _134498 f x s h1)). Qed.
Lemma lem7168976 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) (t' : real) (e' : real) : term137 _134498 x s f t' e'.
Proof. exact (@lem7168973 _134498 x s f False t' e'). Qed.
Lemma lem7168977 {_134498 : Type'} (t' : real) (e' : real) (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term138 _134498 x s f t' e'.
Proof. exact (@lem7168976 _134498 x s f t' e' (@lem7168975 _134498 f x s h1)). Qed.
Lemma lem7168981 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term51 _134498 s f) = (term51 _134498 s f).
Proof. exact (eq_refl (term51 _134498 s f)). Qed.
Lemma lem7168982 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : term139 _134498 s f.
Proof. exact (fun h0 : False => @lem7168981 _134498 s f). Qed.
Lemma lem7168983 {_134498 : Type'} (e' : real) (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term140 _134498 x s f e'.
Proof. exact (@lem7168977 _134498 (term51 _134498 s f) e' f x s h1). Qed.
Lemma lem7168984 {_134498 : Type'} (e' : real) (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term141 _134498 x s f e'.
Proof. exact (@lem7168983 _134498 e' f x s h1 (@lem7168982 _134498 s f)). Qed.
Lemma lem7168991 {A B : Type'} (f : A -> B) (y : A) : (term142 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7168992 {_134498 : Type'} (f : _134498 -> real) (y : _134498) : (term143 _134498 f y) = (f y).
Proof. exact (@lem7168991 _134498 real f y). Qed.
Lemma lem7168993 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term144 _134498 f x) = (term145 _134498 f x).
Proof. exact (@lem7168992 _134498 (term86 _134498 f) x). Qed.
Lemma lem7168994 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term145 _134498 f x) = (term146 _134498 f x).
Proof. exact (eq_refl (term145 _134498 f x)). Qed.
Lemma lem7168995 {_134498 : Type'} (f : _134498 -> nat) : (term147 _134498 f) = (term86 _134498 f).
Proof. exact (fun_ext (fun x : _134498 => @lem7168994 _134498 f x)). Qed.
Lemma lem7168996 {_134498 : Type'} (x : _134498) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7168997 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term144 _134498 f x) = (term145 _134498 f x).
Proof. exact (MK_COMB (@lem7168995 _134498 f) (@lem7168996 _134498 x)). Qed.
Lemma lem7168998 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7168999 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term148 _134498 f x) = (term149 _134498 f x).
Proof. exact (MK_COMB (@lem7168998) (@lem7168997 _134498 f x)). Qed.
Lemma lem7169000 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term145 _134498 f x) = (term146 _134498 f x).
Proof. exact (eq_refl (term145 _134498 f x)). Qed.
Lemma lem7169001 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : ((term144 _134498 f x) = (term145 _134498 f x)) = ((term145 _134498 f x) = (term146 _134498 f x)).
Proof. exact (MK_COMB (@lem7168999 _134498 f x) (@lem7169000 _134498 f x)). Qed.
Lemma lem7169002 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term145 _134498 f x) = (term146 _134498 f x).
Proof. exact (EQ_MP (@lem7169001 _134498 f x) (@lem7168993 _134498 f x)). Qed.
Lemma lem7169003 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169004 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) : (term150 _134498 f x) = (term122 _134498 f x).
Proof. exact (MK_COMB (@lem7169003) (@lem7169002 _134498 f x)). Qed.
Lemma lem7169005 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term51 _134498 s f) = (term51 _134498 s f).
Proof. exact (eq_refl (term51 _134498 s f)). Qed.
Lemma lem7169006 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term130 _134498 x s f) = (term123 _134498 x s f).
Proof. exact (MK_COMB (@lem7169004 _134498 f x) (@lem7169005 _134498 s f)). Qed.
Lemma lem7169007 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term151 _134498 x s f.
Proof. exact (fun h0 : ~ False => @lem7169006 _134498 x s f). Qed.
Lemma lem7169008 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : term152 _134498 x s f.
Proof. exact (@lem7168984 _134498 (term123 _134498 x s f) f x s h1). Qed.
Lemma lem7169009 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term127 _134498 x s f) = (term153 _134498 x s f).
Proof. exact (@lem7169008 _134498 f x s h1 (@lem7169007 _134498 x s f)). Qed.
Lemma lem7169011 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7169012 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7169011 real t1 t2). Qed.
Lemma lem7169013 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term153 _134498 x s f) = (term123 _134498 x s f).
Proof. exact (@lem7169012 (term51 _134498 s f) (term123 _134498 x s f)). Qed.
Lemma lem7169014 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term127 _134498 x s f) = (term123 _134498 x s f).
Proof. exact (TRANS (@lem7169009 _134498 f x s h1) (@lem7169013 _134498 x s f)). Qed.
Lemma lem7169015 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : (term61 _134498 x s f) = (term123 _134498 x s f).
Proof. exact (TRANS (@lem7168957 _134498 f x s h1) (@lem7169014 _134498 f x s h1)). Qed.
Lemma lem7169016 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : ((term60 _134498 x s f) = (term61 _134498 x s f)) = ((term123 _134498 x s f) = (term123 _134498 x s f)).
Proof. exact (MK_COMB (@lem7168948 _134498 f x s h1) (@lem7169015 _134498 f x s h1)). Qed.
Lemma lem7169018 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7169019 (x : real) : (x = x) = True.
Proof. exact (@lem7169018 real x). Qed.
Lemma lem7169020 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : ((term123 _134498 x s f) = (term123 _134498 x s f)) = True.
Proof. exact (@lem7169019 (term123 _134498 x s f)). Qed.
Lemma lem7169021 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) (h1 : term56 _134498 f x s) : ((term60 _134498 x s f) = (term61 _134498 x s f)) = True.
Proof. exact (TRANS (@lem7169016 _134498 f x s h1) (@lem7169020 _134498 x s f)). Qed.
Lemma lem7169022 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : term154 _134498 x s f.
Proof. exact (fun h0 : term56 _134498 f x s => @lem7169021 _134498 f x s h0). Qed.
Lemma lem7169023 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) : term155 _134498 f x s.
Proof. exact (@lem7168874 _134498 f x s True). Qed.
Lemma lem7169024 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) : (term63 _134498 x s f) = (term156 _134498 f x s).
Proof. exact (@lem7169023 _134498 f x s (@lem7169022 _134498 x s f)). Qed.
Lemma lem7169026 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7169027 {_134498 : Type'} (f : _134498 -> nat) (x : _134498) (s : _134498 -> Prop) : (term156 _134498 f x s) = True.
Proof. exact (@lem7169026 (term56 _134498 f x s)). Qed.
Lemma lem7169028 {_134498 : Type'} (x : _134498) (s : _134498 -> Prop) (f : _134498 -> nat) : (term63 _134498 x s f) = True.
Proof. exact (TRANS (@lem7169024 _134498 f x s) (@lem7169027 _134498 f x s)). Qed.
Lemma lem7169029 {_134498 : Type'} (x : _134498) (f : _134498 -> nat) : (term65 _134498 x f) = (term157 _134498).
Proof. exact (fun_ext (fun s : _134498 -> Prop => @lem7169028 _134498 x s f)). Qed.
Lemma lem7169030 {_134498 : Type'} : (@all (_134498 -> Prop)) = (@all (_134498 -> Prop)).
Proof. exact (eq_refl (@all (_134498 -> Prop))). Qed.
Lemma lem7169031 {_134498 : Type'} (x : _134498) (f : _134498 -> nat) : (term67 _134498 x f) = (term158 _134498).
Proof. exact (MK_COMB (@lem7169030 _134498) (@lem7169029 _134498 x f)). Qed.
Lemma lem7169033 {A : Type'} (t : Prop) : (term159 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7169034 {_134498 : Type'} (t : Prop) : (term160 _134498 t) = t.
Proof. exact (@lem7169033 (_134498 -> Prop) t). Qed.
Lemma lem7169035 {_134498 : Type'} : (term158 _134498) = True.
Proof. exact (@lem7169034 _134498 True). Qed.
Lemma lem7169036 {_134498 : Type'} (x : _134498) (f : _134498 -> nat) : (term67 _134498 x f) = True.
Proof. exact (TRANS (@lem7169031 _134498 x f) (@lem7169035 _134498)). Qed.
Lemma lem7169037 {_134498 : Type'} (f : _134498 -> nat) : (term69 _134498 f) = (term161 _134498).
Proof. exact (fun_ext (fun x : _134498 => @lem7169036 _134498 x f)). Qed.
Lemma lem7169038 {_134498 : Type'} : (@all _134498) = (@all _134498).
Proof. exact (eq_refl (@all _134498)). Qed.
Lemma lem7169039 {_134498 : Type'} (f : _134498 -> nat) : (term71 _134498 f) = (term162 _134498).
Proof. exact (MK_COMB (@lem7169038 _134498) (@lem7169037 _134498 f)). Qed.
Lemma lem7169041 {A : Type'} (t : Prop) : (term159 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7169042 {_134498 : Type'} (t : Prop) : (term159 _134498 t) = t.
Proof. exact (@lem7169041 _134498 t). Qed.
Lemma lem7169043 {_134498 : Type'} : (term162 _134498) = True.
Proof. exact (@lem7169042 _134498 True). Qed.
Lemma lem7169044 {_134498 : Type'} (f : _134498 -> nat) : (term71 _134498 f) = True.
Proof. exact (TRANS (@lem7169039 _134498 f) (@lem7169043 _134498)). Qed.
Lemma lem7169045 {_134498 : Type'} (f : _134498 -> nat) : (term73 _134498 f) = (True /\ True).
Proof. exact (MK_COMB (@lem7168844 _134498 f) (@lem7169044 _134498 f)). Qed.
Lemma lem7169047 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7169048 : (True /\ True) = True.
Proof. exact (@lem7169047 True). Qed.
Lemma lem7169049 {_134498 : Type'} (f : _134498 -> nat) : (term73 _134498 f) = True.
Proof. exact (TRANS (@lem7169045 _134498 f) (@lem7169048)). Qed.
Lemma lem7169050 {_134498 : Type'} (f : _134498 -> nat) : True = (term73 _134498 f).
Proof. exact (SYM (@lem7169049 _134498 f)). Qed.
Lemma lem7169051 {_134498 : Type'} (f : _134498 -> nat) : term73 _134498 f.
Proof. exact (EQ_MP (@lem7169050 _134498 f) (@lem0)). Qed.
Lemma lem7169052 {_134498 : Type'} (f : _134498 -> nat) : term82 _134498 f.
Proof. exact (@lem7168821 _134498 f (@lem7169051 _134498 f)). Qed.
Lemma lem7169057 {_134498 : Type'} : term163 _134498.
Proof. exact (fun f : _134498 -> nat => @lem7169052 _134498 f). Qed.
