Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2801043_term_abbrevs.
Require Import EXISTS_UNCURRY_spec.
Require Import INT_GCD_EXISTS_POS_spec.
Require Import SKOLEM_THM_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem2800652 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem2800653 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem2800655 {A B C : Type'} (P : type443 A B C) : term3 A B C P.
Proof. exact (@lem53486 A B C P). Qed.
Lemma lem2800656 {A B C : Type'} (P : type443 A B C) : (term3 A B C P) = ((term4 A B C P) = (term5 A B C P)).
Proof. exact (eq_refl (term3 A B C P)). Qed.
Lemma lem2800663 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2800653 A B P) (@lem2800652 A B P)). Qed.
Lemma lem2800664 (P : type1550) : (term6 P) = (term7 P).
Proof. exact (@lem2800663 int int P). Qed.
Lemma lem2800665 (a : int) : (term8 a) = (term9 a).
Proof. exact (@lem2800664 (term10 a)). Qed.
Lemma lem2800666 (a : int) (b : int) : (term11 a b) = (term12 a b).
Proof. exact (eq_refl (term11 a b)). Qed.
Lemma lem2800667 (d : int) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem2800668 (a : int) (b : int) (d : int) : (term13 a b d) = (term14 a b d).
Proof. exact (MK_COMB (@lem2800666 a b) (@lem2800667 d)). Qed.
Lemma lem2800669 (d : int) (a : int) (b : int) : (term14 a b d) = (term15 d a b).
Proof. exact (eq_refl (term14 a b d)). Qed.
Lemma lem2800670 (d : int) (a : int) (b : int) : (term13 a b d) = (term15 d a b).
Proof. exact (TRANS (@lem2800668 a b d) (@lem2800669 d a b)). Qed.
Lemma lem2800671 (a : int) (b : int) : (term16 a b) = (term12 a b).
Proof. exact (fun_ext (fun d : int => @lem2800670 d a b)). Qed.
Lemma lem2800672 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2800673 (a : int) (b : int) : (term17 a b) = (term18 a b).
Proof. exact (MK_COMB (@lem2800672) (@lem2800671 a b)). Qed.
Lemma lem2800674 (a : int) : (term19 a) = (term20 a).
Proof. exact (fun_ext (fun b : int => @lem2800673 a b)). Qed.
Lemma lem2800675 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2800676 (a : int) : (term8 a) = (term21 a).
Proof. exact (MK_COMB (@lem2800675) (@lem2800674 a)). Qed.
Lemma lem2800677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2800678 (a : int) : (term22 a) = (term23 a).
Proof. exact (MK_COMB (@lem2800677) (@lem2800676 a)). Qed.
Lemma lem2800679 (a : int) (b : int) : (term11 a b) = (term12 a b).
Proof. exact (eq_refl (term11 a b)). Qed.
Lemma lem2800680 (d : int -> int) (b : int) : (d b) = (d b).
Proof. exact (eq_refl (d b)). Qed.
Lemma lem2800681 (a : int) (d : int -> int) (b : int) : (term24 a d b) = (term25 a d b).
Proof. exact (MK_COMB (@lem2800679 a b) (@lem2800680 d b)). Qed.
Lemma lem2800682 (d : int -> int) (a : int) (b : int) : (term25 a d b) = (term26 d a b).
Proof. exact (eq_refl (term25 a d b)). Qed.
Lemma lem2800683 (d : int -> int) (a : int) (b : int) : (term24 a d b) = (term26 d a b).
Proof. exact (TRANS (@lem2800681 a d b) (@lem2800682 d a b)). Qed.
Lemma lem2800684 (d : int -> int) (a : int) : (term27 a d) = (term28 d a).
Proof. exact (fun_ext (fun b : int => @lem2800683 d a b)). Qed.
Lemma lem2800685 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2800686 (d : int -> int) (a : int) : (term29 a d) = (term30 d a).
Proof. exact (MK_COMB (@lem2800685) (@lem2800684 d a)). Qed.
Lemma lem2800687 (a : int) : (term31 a) = (term32 a).
Proof. exact (fun_ext (fun d : int -> int => @lem2800686 d a)). Qed.
Lemma lem2800688 : (@ex (int -> int)) = (@ex (int -> int)).
Proof. exact (eq_refl (@ex (int -> int))). Qed.
Lemma lem2800689 (a : int) : (term9 a) = (term33 a).
Proof. exact (MK_COMB (@lem2800688) (@lem2800687 a)). Qed.
Lemma lem2800690 (a : int) : ((term8 a) = (term9 a)) = ((term21 a) = (term33 a)).
Proof. exact (MK_COMB (@lem2800678 a) (@lem2800689 a)). Qed.
Lemma lem2800691 (a : int) : (term21 a) = (term33 a).
Proof. exact (EQ_MP (@lem2800690 a) (@lem2800665 a)). Qed.
Lemma lem2800722 : term34 = term35.
Proof. exact (fun_ext (fun a : int => @lem2800691 a)). Qed.
Lemma lem2800723 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2800724 : term36 = term37.
Proof. exact (MK_COMB (@lem2800723) (@lem2800722)). Qed.
Lemma lem2800726 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2800653 A B P) (@lem2800652 A B P)). Qed.
Lemma lem2800727 (P : type1548) : (term38 P) = (term39 P).
Proof. exact (@lem2800726 int (int -> int) P). Qed.
Lemma lem2800728 : term40 = term41.
Proof. exact (@lem2800727 term42). Qed.
Lemma lem2800729 (a : int) : (term43 a) = (term32 a).
Proof. exact (eq_refl (term43 a)). Qed.
Lemma lem2800730 (d : int -> int) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem2800731 (a : int) (d : int -> int) : (term44 a d) = (term45 a d).
Proof. exact (MK_COMB (@lem2800729 a) (@lem2800730 d)). Qed.
Lemma lem2800732 (d : int -> int) (a : int) : (term45 a d) = (term30 d a).
Proof. exact (eq_refl (term45 a d)). Qed.
Lemma lem2800733 (d : int -> int) (a : int) : (term44 a d) = (term30 d a).
Proof. exact (TRANS (@lem2800731 a d) (@lem2800732 d a)). Qed.
Lemma lem2800734 (a : int) : (term46 a) = (term32 a).
Proof. exact (fun_ext (fun d : int -> int => @lem2800733 d a)). Qed.
Lemma lem2800735 : (@ex (int -> int)) = (@ex (int -> int)).
Proof. exact (eq_refl (@ex (int -> int))). Qed.
Lemma lem2800736 (a : int) : (term47 a) = (term33 a).
Proof. exact (MK_COMB (@lem2800735) (@lem2800734 a)). Qed.
Lemma lem2800737 : term48 = term35.
Proof. exact (fun_ext (fun a : int => @lem2800736 a)). Qed.
Lemma lem2800738 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2800739 : term40 = term37.
Proof. exact (MK_COMB (@lem2800738) (@lem2800737)). Qed.
Lemma lem2800740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2800741 : term49 = term50.
Proof. exact (MK_COMB (@lem2800740) (@lem2800739)). Qed.
Lemma lem2800742 (a : int) : (term43 a) = (term32 a).
Proof. exact (eq_refl (term43 a)). Qed.
Lemma lem2800743 (d : type1551) (a : int) : (d a) = (d a).
Proof. exact (eq_refl (d a)). Qed.
Lemma lem2800744 (d : type1551) (a : int) : (term51 d a) = (term52 d a).
Proof. exact (MK_COMB (@lem2800742 a) (@lem2800743 d a)). Qed.
Lemma lem2800745 (d : type1551) (a : int) : (term52 d a) = (term53 d a).
Proof. exact (eq_refl (term52 d a)). Qed.
Lemma lem2800746 (d : type1551) (a : int) : (term51 d a) = (term53 d a).
Proof. exact (TRANS (@lem2800744 d a) (@lem2800745 d a)). Qed.
Lemma lem2800747 (d : type1551) : (term54 d) = (term55 d).
Proof. exact (fun_ext (fun a : int => @lem2800746 d a)). Qed.
Lemma lem2800748 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2800749 (d : type1551) : (term56 d) = (term57 d).
Proof. exact (MK_COMB (@lem2800748) (@lem2800747 d)). Qed.
Lemma lem2800750 : term58 = term59.
Proof. exact (fun_ext (fun d : type1551 => @lem2800749 d)). Qed.
Lemma lem2800751 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2800752 : term41 = term60.
Proof. exact (MK_COMB (@lem2800751) (@lem2800750)). Qed.
Lemma lem2800753 : (term40 = term41) = (term37 = term60).
Proof. exact (MK_COMB (@lem2800741) (@lem2800752)). Qed.
Lemma lem2800754 : term37 = term60.
Proof. exact (EQ_MP (@lem2800753) (@lem2800728)). Qed.
Lemma lem2800760 {A B C : Type'} (P : type443 A B C) : (term4 A B C P) = (term5 A B C P).
Proof. exact (EQ_MP (@lem2800656 A B C P) (@lem2800655 A B C P)). Qed.
Lemma lem2800761 (P : type924) : (term61 P) = (term62 P).
Proof. exact (@lem2800760 int int int P). Qed.
Lemma lem2800762 : term63 = term64.
Proof. exact (@lem2800761 term59). Qed.
Lemma lem2800763 (d : type1551) : (term65 d) = (term57 d).
Proof. exact (eq_refl (term65 d)). Qed.
Lemma lem2800764 : term66 = term59.
Proof. exact (fun_ext (fun d : type1551 => @lem2800763 d)). Qed.
Lemma lem2800765 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2800766 : term63 = term60.
Proof. exact (MK_COMB (@lem2800765) (@lem2800764)). Qed.
Lemma lem2800767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2800768 : term67 = term68.
Proof. exact (MK_COMB (@lem2800767) (@lem2800766)). Qed.
Lemma lem2800769 (d : type1234) : (term69 d) = (term70 d).
Proof. exact (eq_refl (term69 d)). Qed.
Lemma lem2800770 : term71 = term72.
Proof. exact (fun_ext (fun d : type1234 => @lem2800769 d)). Qed.
Lemma lem2800771 : (@ex ((prod int int) -> int)) = (@ex ((prod int int) -> int)).
Proof. exact (eq_refl (@ex ((prod int int) -> int))). Qed.
Lemma lem2800772 : term64 = term73.
Proof. exact (MK_COMB (@lem2800771) (@lem2800770)). Qed.
Lemma lem2800773 : (term63 = term64) = (term60 = term73).
Proof. exact (MK_COMB (@lem2800768) (@lem2800772)). Qed.
Lemma lem2800774 : term60 = term73.
Proof. exact (EQ_MP (@lem2800773) (@lem2800762)). Qed.
Lemma lem2800792 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800793 (f : type1551) (y : int) : (term75 f y) = (f y).
Proof. exact (@lem2800792 int (int -> int) f y). Qed.
Lemma lem2800794 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (@lem2800793 (term78 d) a). Qed.
Lemma lem2800795 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800796 (d : type1234) : (term80 d) = (term78 d).
Proof. exact (fun_ext (fun a : int => @lem2800795 d a)). Qed.
Lemma lem2800797 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem2800798 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (MK_COMB (@lem2800796 d) (@lem2800797 a)). Qed.
Lemma lem2800799 : (@eq (int -> int)) = (@eq (int -> int)).
Proof. exact (eq_refl (@eq (int -> int))). Qed.
Lemma lem2800800 (d : type1234) (a : int) : (term81 d a) = (term82 d a).
Proof. exact (MK_COMB (@lem2800799) (@lem2800798 d a)). Qed.
Lemma lem2800801 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800802 (d : type1234) (a : int) : ((term76 d a) = (term77 d a)) = ((term77 d a) = (term79 d a)).
Proof. exact (MK_COMB (@lem2800800 d a) (@lem2800801 d a)). Qed.
Lemma lem2800803 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (EQ_MP (@lem2800802 d a) (@lem2800794 d a)). Qed.
Lemma lem2800804 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800805 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800803 d a) (@lem2800804 b)). Qed.
Lemma lem2800807 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800808 (f : int -> int) (y : int) : (term85 f y) = (f y).
Proof. exact (@lem2800807 int int f y). Qed.
Lemma lem2800809 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (@lem2800808 (term79 d a) b). Qed.
Lemma lem2800810 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800811 (d : type1234) (a : int) : (term88 d a) = (term79 d a).
Proof. exact (fun_ext (fun b : int => @lem2800810 d a b)). Qed.
Lemma lem2800812 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800813 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800811 d a) (@lem2800812 b)). Qed.
Lemma lem2800814 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2800815 (d : type1234) (a : int) (b : int) : (term89 d a b) = (term90 d a b).
Proof. exact (MK_COMB (@lem2800814) (@lem2800813 d a b)). Qed.
Lemma lem2800816 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800817 (d : type1234) (a : int) (b : int) : ((term86 d a b) = (term84 d a b)) = ((term84 d a b) = (term87 d a b)).
Proof. exact (MK_COMB (@lem2800815 d a b) (@lem2800816 d a b)). Qed.
Lemma lem2800818 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (EQ_MP (@lem2800817 d a b) (@lem2800809 d a b)). Qed.
Lemma lem2800819 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term87 d a b).
Proof. exact (TRANS (@lem2800805 d a b) (@lem2800818 d a b)). Qed.
Lemma lem2800820 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem2800821 (d : type1234) (a : int) (b : int) : (term92 d a b) = (term93 d a b).
Proof. exact (MK_COMB (@lem2800820) (@lem2800819 d a b)). Qed.
Lemma lem2800822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2800823 (d : type1234) (a : int) (b : int) : (term94 d a b) = (term95 d a b).
Proof. exact (MK_COMB (@lem2800822) (@lem2800821 d a b)). Qed.
Lemma lem2800827 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800828 (f : type1551) (y : int) : (term75 f y) = (f y).
Proof. exact (@lem2800827 int (int -> int) f y). Qed.
Lemma lem2800829 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (@lem2800828 (term78 d) a). Qed.
Lemma lem2800830 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800831 (d : type1234) : (term80 d) = (term78 d).
Proof. exact (fun_ext (fun a : int => @lem2800830 d a)). Qed.
Lemma lem2800832 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem2800833 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (MK_COMB (@lem2800831 d) (@lem2800832 a)). Qed.
Lemma lem2800834 : (@eq (int -> int)) = (@eq (int -> int)).
Proof. exact (eq_refl (@eq (int -> int))). Qed.
Lemma lem2800835 (d : type1234) (a : int) : (term81 d a) = (term82 d a).
Proof. exact (MK_COMB (@lem2800834) (@lem2800833 d a)). Qed.
Lemma lem2800836 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800837 (d : type1234) (a : int) : ((term76 d a) = (term77 d a)) = ((term77 d a) = (term79 d a)).
Proof. exact (MK_COMB (@lem2800835 d a) (@lem2800836 d a)). Qed.
Lemma lem2800838 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (EQ_MP (@lem2800837 d a) (@lem2800829 d a)). Qed.
Lemma lem2800839 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800840 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800838 d a) (@lem2800839 b)). Qed.
Lemma lem2800842 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800843 (f : int -> int) (y : int) : (term85 f y) = (f y).
Proof. exact (@lem2800842 int int f y). Qed.
Lemma lem2800844 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (@lem2800843 (term79 d a) b). Qed.
Lemma lem2800845 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800846 (d : type1234) (a : int) : (term88 d a) = (term79 d a).
Proof. exact (fun_ext (fun b : int => @lem2800845 d a b)). Qed.
Lemma lem2800847 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800848 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800846 d a) (@lem2800847 b)). Qed.
Lemma lem2800849 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2800850 (d : type1234) (a : int) (b : int) : (term89 d a b) = (term90 d a b).
Proof. exact (MK_COMB (@lem2800849) (@lem2800848 d a b)). Qed.
Lemma lem2800851 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800852 (d : type1234) (a : int) (b : int) : ((term86 d a b) = (term84 d a b)) = ((term84 d a b) = (term87 d a b)).
Proof. exact (MK_COMB (@lem2800850 d a b) (@lem2800851 d a b)). Qed.
Lemma lem2800853 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (EQ_MP (@lem2800852 d a b) (@lem2800844 d a b)). Qed.
Lemma lem2800854 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term87 d a b).
Proof. exact (TRANS (@lem2800840 d a b) (@lem2800853 d a b)). Qed.
Lemma lem2800855 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem2800856 (d : type1234) (a : int) (b : int) : (term96 d a b) = (term97 d a b).
Proof. exact (MK_COMB (@lem2800855) (@lem2800854 d a b)). Qed.
Lemma lem2800857 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem2800858 (d : type1234) (b : int) (a : int) : (term98 d b a) = (term99 d b a).
Proof. exact (MK_COMB (@lem2800856 d a b) (@lem2800857 a)). Qed.
Lemma lem2800859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2800860 (d : type1234) (b : int) (a : int) : (term100 d b a) = (term101 d b a).
Proof. exact (MK_COMB (@lem2800859) (@lem2800858 d b a)). Qed.
Lemma lem2800864 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800865 (f : type1551) (y : int) : (term75 f y) = (f y).
Proof. exact (@lem2800864 int (int -> int) f y). Qed.
Lemma lem2800866 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (@lem2800865 (term78 d) a). Qed.
Lemma lem2800867 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800868 (d : type1234) : (term80 d) = (term78 d).
Proof. exact (fun_ext (fun a : int => @lem2800867 d a)). Qed.
Lemma lem2800869 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem2800870 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (MK_COMB (@lem2800868 d) (@lem2800869 a)). Qed.
Lemma lem2800871 : (@eq (int -> int)) = (@eq (int -> int)).
Proof. exact (eq_refl (@eq (int -> int))). Qed.
Lemma lem2800872 (d : type1234) (a : int) : (term81 d a) = (term82 d a).
Proof. exact (MK_COMB (@lem2800871) (@lem2800870 d a)). Qed.
Lemma lem2800873 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800874 (d : type1234) (a : int) : ((term76 d a) = (term77 d a)) = ((term77 d a) = (term79 d a)).
Proof. exact (MK_COMB (@lem2800872 d a) (@lem2800873 d a)). Qed.
Lemma lem2800875 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (EQ_MP (@lem2800874 d a) (@lem2800866 d a)). Qed.
Lemma lem2800876 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800877 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800875 d a) (@lem2800876 b)). Qed.
Lemma lem2800879 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800880 (f : int -> int) (y : int) : (term85 f y) = (f y).
Proof. exact (@lem2800879 int int f y). Qed.
Lemma lem2800881 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (@lem2800880 (term79 d a) b). Qed.
Lemma lem2800882 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800883 (d : type1234) (a : int) : (term88 d a) = (term79 d a).
Proof. exact (fun_ext (fun b : int => @lem2800882 d a b)). Qed.
Lemma lem2800884 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800885 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800883 d a) (@lem2800884 b)). Qed.
Lemma lem2800886 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2800887 (d : type1234) (a : int) (b : int) : (term89 d a b) = (term90 d a b).
Proof. exact (MK_COMB (@lem2800886) (@lem2800885 d a b)). Qed.
Lemma lem2800888 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800889 (d : type1234) (a : int) (b : int) : ((term86 d a b) = (term84 d a b)) = ((term84 d a b) = (term87 d a b)).
Proof. exact (MK_COMB (@lem2800887 d a b) (@lem2800888 d a b)). Qed.
Lemma lem2800890 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (EQ_MP (@lem2800889 d a b) (@lem2800881 d a b)). Qed.
Lemma lem2800891 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term87 d a b).
Proof. exact (TRANS (@lem2800877 d a b) (@lem2800890 d a b)). Qed.
Lemma lem2800892 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem2800893 (d : type1234) (a : int) (b : int) : (term96 d a b) = (term97 d a b).
Proof. exact (MK_COMB (@lem2800892) (@lem2800891 d a b)). Qed.
Lemma lem2800894 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800895 (d : type1234) (a : int) (b : int) : (term102 d a b) = (term103 d a b).
Proof. exact (MK_COMB (@lem2800893 d a b) (@lem2800894 b)). Qed.
Lemma lem2800896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2800897 (d : type1234) (a : int) (b : int) : (term104 d a b) = (term105 d a b).
Proof. exact (MK_COMB (@lem2800896) (@lem2800895 d a b)). Qed.
Lemma lem2800913 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800914 (f : type1551) (y : int) : (term75 f y) = (f y).
Proof. exact (@lem2800913 int (int -> int) f y). Qed.
Lemma lem2800915 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (@lem2800914 (term78 d) a). Qed.
Lemma lem2800916 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800917 (d : type1234) : (term80 d) = (term78 d).
Proof. exact (fun_ext (fun a : int => @lem2800916 d a)). Qed.
Lemma lem2800918 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem2800919 (d : type1234) (a : int) : (term76 d a) = (term77 d a).
Proof. exact (MK_COMB (@lem2800917 d) (@lem2800918 a)). Qed.
Lemma lem2800920 : (@eq (int -> int)) = (@eq (int -> int)).
Proof. exact (eq_refl (@eq (int -> int))). Qed.
Lemma lem2800921 (d : type1234) (a : int) : (term81 d a) = (term82 d a).
Proof. exact (MK_COMB (@lem2800920) (@lem2800919 d a)). Qed.
Lemma lem2800922 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (eq_refl (term77 d a)). Qed.
Lemma lem2800923 (d : type1234) (a : int) : ((term76 d a) = (term77 d a)) = ((term77 d a) = (term79 d a)).
Proof. exact (MK_COMB (@lem2800921 d a) (@lem2800922 d a)). Qed.
Lemma lem2800924 (d : type1234) (a : int) : (term77 d a) = (term79 d a).
Proof. exact (EQ_MP (@lem2800923 d a) (@lem2800915 d a)). Qed.
Lemma lem2800925 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800926 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800924 d a) (@lem2800925 b)). Qed.
Lemma lem2800928 {A B : Type'} (f : A -> B) (y : A) : (term74 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2800929 (f : int -> int) (y : int) : (term85 f y) = (f y).
Proof. exact (@lem2800928 int int f y). Qed.
Lemma lem2800930 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (@lem2800929 (term79 d a) b). Qed.
Lemma lem2800931 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800932 (d : type1234) (a : int) : (term88 d a) = (term79 d a).
Proof. exact (fun_ext (fun b : int => @lem2800931 d a b)). Qed.
Lemma lem2800933 (b : int) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem2800934 (d : type1234) (a : int) (b : int) : (term86 d a b) = (term84 d a b).
Proof. exact (MK_COMB (@lem2800932 d a) (@lem2800933 b)). Qed.
Lemma lem2800935 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2800936 (d : type1234) (a : int) (b : int) : (term89 d a b) = (term90 d a b).
Proof. exact (MK_COMB (@lem2800935) (@lem2800934 d a b)). Qed.
Lemma lem2800937 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (eq_refl (term84 d a b)). Qed.
Lemma lem2800938 (d : type1234) (a : int) (b : int) : ((term86 d a b) = (term84 d a b)) = ((term84 d a b) = (term87 d a b)).
Proof. exact (MK_COMB (@lem2800936 d a b) (@lem2800937 d a b)). Qed.
Lemma lem2800939 (d : type1234) (a : int) (b : int) : (term84 d a b) = (term87 d a b).
Proof. exact (EQ_MP (@lem2800938 d a b) (@lem2800930 d a b)). Qed.
Lemma lem2800940 (d : type1234) (a : int) (b : int) : (term83 d a b) = (term87 d a b).
Proof. exact (TRANS (@lem2800926 d a b) (@lem2800939 d a b)). Qed.
Lemma lem2800941 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2800942 (d : type1234) (a : int) (b : int) : (term106 d a b) = (term107 d a b).
Proof. exact (MK_COMB (@lem2800941) (@lem2800940 d a b)). Qed.
Lemma lem2800943 (a : int) (x : int) (b : int) (y : int) : (term108 a x b y) = (term108 a x b y).
Proof. exact (eq_refl (term108 a x b y)). Qed.
Lemma lem2800944 (d : type1234) (a : int) (x : int) (b : int) (y : int) : ((term83 d a b) = (term108 a x b y)) = ((term87 d a b) = (term108 a x b y)).
Proof. exact (MK_COMB (@lem2800942 d a b) (@lem2800943 a x b y)). Qed.
Lemma lem2800947 (d : type1234) (a : int) (x : int) (b : int) : (term109 d a x b) = (term110 d a x b).
Proof. exact (fun_ext (fun y : int => @lem2800944 d a x b y)). Qed.
Lemma lem2800948 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2800949 (d : type1234) (a : int) (x : int) (b : int) : (term111 d a x b) = (term112 d a x b).
Proof. exact (MK_COMB (@lem2800948) (@lem2800947 d a x b)). Qed.
Lemma lem2800956 (d : type1234) (a : int) (b : int) : (term113 d a b) = (term114 d a b).
Proof. exact (fun_ext (fun x : int => @lem2800949 d a x b)). Qed.
Lemma lem2800957 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2800958 (d : type1234) (a : int) (b : int) : (term115 d a b) = (term116 d a b).
Proof. exact (MK_COMB (@lem2800957) (@lem2800956 d a b)). Qed.
Lemma lem2800965 (d : type1234) (a : int) (b : int) : (term117 d a b) = (term118 d a b).
Proof. exact (MK_COMB (@lem2800897 d a b) (@lem2800958 d a b)). Qed.
Lemma lem2800968 (d : type1234) (a : int) (b : int) : (term119 d a b) = (term120 d a b).
Proof. exact (MK_COMB (@lem2800860 d b a) (@lem2800965 d a b)). Qed.
Lemma lem2800971 (d : type1234) (a : int) (b : int) : (term121 d a b) = (term122 d a b).
Proof. exact (MK_COMB (@lem2800823 d a b) (@lem2800968 d a b)). Qed.
Lemma lem2800974 (d : type1234) (a : int) : (term123 d a) = (term124 d a).
Proof. exact (fun_ext (fun b : int => @lem2800971 d a b)). Qed.
Lemma lem2800975 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2800976 (d : type1234) (a : int) : (term125 d a) = (term126 d a).
Proof. exact (MK_COMB (@lem2800975) (@lem2800974 d a)). Qed.
Lemma lem2800981 (d : type1234) : (term127 d) = (term128 d).
Proof. exact (fun_ext (fun a : int => @lem2800976 d a)). Qed.
Lemma lem2800982 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2800983 (d : type1234) : (term70 d) = (term129 d).
Proof. exact (MK_COMB (@lem2800982) (@lem2800981 d)). Qed.
Lemma lem2800988 : term72 = term130.
Proof. exact (fun_ext (fun d : type1234 => @lem2800983 d)). Qed.
Lemma lem2800989 : (@ex ((prod int int) -> int)) = (@ex ((prod int int) -> int)).
Proof. exact (eq_refl (@ex ((prod int int) -> int))). Qed.
Lemma lem2800990 : term73 = term131.
Proof. exact (MK_COMB (@lem2800989) (@lem2800988)). Qed.
Lemma lem2800997 : term60 = term131.
Proof. exact (TRANS (@lem2800774) (@lem2800990)). Qed.
Lemma lem2800998 : term37 = term131.
Proof. exact (TRANS (@lem2800754) (@lem2800997)). Qed.
Lemma lem2800999 : term36 = term131.
Proof. exact (TRANS (@lem2800724) (@lem2800998)). Qed.
Lemma lem2801000 : term131.
Proof. exact (EQ_MP (@lem2800999) (@lem2800651)). Qed.
Lemma lem2801001 : term132.
Proof. exact (fun _30833 : type1670 => @lem2801000). Qed.
Lemma lem2801002 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem2801003 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem2801006 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2801003 A B P) (@lem2801002 A B P)). Qed.
Lemma lem2801007 (P : type1254) : (term133 P) = (term134 P).
Proof. exact (@lem2801006 type1670 type1234 P). Qed.
Lemma lem2801008 : term135 = term136.
Proof. exact (@lem2801007 term137). Qed.
Lemma lem2801009 (_30833 : type1670) : (term138 _30833) = term130.
Proof. exact (eq_refl (term138 _30833)). Qed.
Lemma lem2801010 (d : type1234) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem2801011 (_30833 : type1670) (d : type1234) : (term139 _30833 d) = (term140 d).
Proof. exact (MK_COMB (@lem2801009 _30833) (@lem2801010 d)). Qed.
Lemma lem2801012 (d : type1234) : (term140 d) = (term129 d).
Proof. exact (eq_refl (term140 d)). Qed.
Lemma lem2801013 (_30833 : type1670) (d : type1234) : (term139 _30833 d) = (term129 d).
Proof. exact (TRANS (@lem2801011 _30833 d) (@lem2801012 d)). Qed.
Lemma lem2801014 (_30833 : type1670) : (term141 _30833) = term130.
Proof. exact (fun_ext (fun d : type1234 => @lem2801013 _30833 d)). Qed.
Lemma lem2801015 : (@ex ((prod int int) -> int)) = (@ex ((prod int int) -> int)).
Proof. exact (eq_refl (@ex ((prod int int) -> int))). Qed.
Lemma lem2801016 (_30833 : type1670) : (term142 _30833) = term131.
Proof. exact (MK_COMB (@lem2801015) (@lem2801014 _30833)). Qed.
Lemma lem2801017 : term143 = term144.
Proof. exact (fun_ext (fun _30833 : type1670 => @lem2801016 _30833)). Qed.
Lemma lem2801018 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem2801019 : term135 = term132.
Proof. exact (MK_COMB (@lem2801018) (@lem2801017)). Qed.
Lemma lem2801020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2801021 : term145 = term146.
Proof. exact (MK_COMB (@lem2801020) (@lem2801019)). Qed.
Lemma lem2801022 (_30833 : type1670) : (term138 _30833) = term130.
Proof. exact (eq_refl (term138 _30833)). Qed.
Lemma lem2801023 (d : type1259) (_30833 : type1670) : (d _30833) = (d _30833).
Proof. exact (eq_refl (d _30833)). Qed.
Lemma lem2801024 (d : type1259) (_30833 : type1670) : (term147 d _30833) = (term148 d _30833).
Proof. exact (MK_COMB (@lem2801022 _30833) (@lem2801023 d _30833)). Qed.
Lemma lem2801025 (d : type1259) (_30833 : type1670) : (term148 d _30833) = (term149 d _30833).
Proof. exact (eq_refl (term148 d _30833)). Qed.
Lemma lem2801026 (d : type1259) (_30833 : type1670) : (term147 d _30833) = (term149 d _30833).
Proof. exact (TRANS (@lem2801024 d _30833) (@lem2801025 d _30833)). Qed.
Lemma lem2801027 (d : type1259) : (term150 d) = (term151 d).
Proof. exact (fun_ext (fun _30833 : type1670 => @lem2801026 d _30833)). Qed.
Lemma lem2801028 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem2801029 (d : type1259) : (term152 d) = (term153 d).
Proof. exact (MK_COMB (@lem2801028) (@lem2801027 d)). Qed.
Lemma lem2801030 : term154 = term155.
Proof. exact (fun_ext (fun d : type1259 => @lem2801029 d)). Qed.
Lemma lem2801031 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod int int) -> int)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod int int) -> int)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod int int) -> int))). Qed.
Lemma lem2801032 : term136 = term156.
Proof. exact (MK_COMB (@lem2801031) (@lem2801030)). Qed.
Lemma lem2801033 : (term135 = term136) = (term132 = term156).
Proof. exact (MK_COMB (@lem2801021) (@lem2801032)). Qed.
Lemma lem2801034 : term132 = term156.
Proof. exact (EQ_MP (@lem2801033) (@lem2801008)). Qed.
Lemma lem2801035 : term156.
Proof. exact (EQ_MP (@lem2801034) (@lem2801001)). Qed.
Lemma lem2801037 {A : Type'} : (@ex A) = (term157 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem2801038 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod int int) -> int)) = term158.
Proof. exact (@lem2801037 type1259). Qed.
Lemma lem2801039 : term155 = term155.
Proof. exact (eq_refl term155). Qed.
Lemma lem2801040 : term156 = term159.
Proof. exact (MK_COMB (@lem2801038) (@lem2801039)). Qed.
Lemma lem2801041 : term159 = term160.
Proof. exact (eq_refl term159). Qed.
Lemma lem2801042 : term156 = term160.
Proof. exact (TRANS (@lem2801040) (@lem2801041)). Qed.
Lemma lem2801043 : term160.
Proof. exact (EQ_MP (@lem2801042) (@lem2801035)). Qed.
