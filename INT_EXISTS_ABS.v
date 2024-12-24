Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EXISTS_ABS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import INT_FORALL_ABS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2317749 (P : int -> Prop) : term0 P.
Proof. exact (@lem2317738 P). Qed.
Lemma lem2317750 (P : int -> Prop) : (term0 P) = ((term1 P) = (term2 P)).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem2317752 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem2317753 {A : Type'} (P : A -> Prop) : (term3 A P) = ((term4 A P) = (term5 A P)).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem2317763 (p : Prop) : term6 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem2317764 (p : Prop) : (term6 p) = (term7 p).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem2317765 (p : Prop) : term7 p.
Proof. exact (EQ_MP (@lem2317764 p) (@lem2317763 p)). Qed.
Lemma lem2317766 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem2317767 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem2317776 (q : Prop) : (term8 q) = (term8 q).
Proof. exact (eq_refl (term8 q)). Qed.
Lemma lem2317777 (q : Prop) (p : Prop) (h1 : p = True) : (term9 q p) = (term10 q).
Proof. exact (MK_COMB (@lem2317776 q) (@lem2317766 p h1)). Qed.
Lemma lem2317778 (q : Prop) : (term10 q) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl (term10 q)). Qed.
Lemma lem2317779 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem2317780 (p : Prop) (q : Prop) : ((term9 q p) = (term10 q)) = ((term9 q p) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem2317779 q p) (@lem2317778 q)). Qed.
Lemma lem2317781 (p : Prop) (q : Prop) : (term9 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term9 q p)). Qed.
Lemma lem2317782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317783 (p : Prop) (q : Prop) : (term11 q p) = (term12 p q).
Proof. exact (MK_COMB (@lem2317782) (@lem2317781 p q)). Qed.
Lemma lem2317784 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl ((True = q) = ((~ True) = (~ q)))). Qed.
Lemma lem2317785 (p : Prop) (q : Prop) : ((term9 q p) = ((True = q) = ((~ True) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem2317783 p q) (@lem2317784 q)). Qed.
Lemma lem2317786 (p : Prop) (q : Prop) : ((term9 q p) = (term10 q)) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (TRANS (@lem2317780 p q) (@lem2317785 p q)). Qed.
Lemma lem2317787 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (EQ_MP (@lem2317786 p q) (@lem2317777 q p h1)). Qed.
Lemma lem2317788 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = ((~ True) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem2317787 q p h1)). Qed.
Lemma lem2317789 (q : Prop) : (term8 q) = (term8 q).
Proof. exact (eq_refl (term8 q)). Qed.
Lemma lem2317790 (q : Prop) (p : Prop) (h1 : p = False) : (term9 q p) = (term13 q).
Proof. exact (MK_COMB (@lem2317789 q) (@lem2317767 p h1)). Qed.
Lemma lem2317791 (q : Prop) : (term13 q) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl (term13 q)). Qed.
Lemma lem2317792 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem2317793 (p : Prop) (q : Prop) : ((term9 q p) = (term13 q)) = ((term9 q p) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem2317792 q p) (@lem2317791 q)). Qed.
Lemma lem2317794 (p : Prop) (q : Prop) : (term9 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term9 q p)). Qed.
Lemma lem2317795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317796 (p : Prop) (q : Prop) : (term11 q p) = (term12 p q).
Proof. exact (MK_COMB (@lem2317795) (@lem2317794 p q)). Qed.
Lemma lem2317797 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl ((False = q) = ((~ False) = (~ q)))). Qed.
Lemma lem2317798 (p : Prop) (q : Prop) : ((term9 q p) = ((False = q) = ((~ False) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem2317796 p q) (@lem2317797 q)). Qed.
Lemma lem2317799 (p : Prop) (q : Prop) : ((term9 q p) = (term13 q)) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (TRANS (@lem2317793 p q) (@lem2317798 p q)). Qed.
Lemma lem2317800 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (EQ_MP (@lem2317799 p q) (@lem2317790 q p h1)). Qed.
Lemma lem2317801 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = ((~ False) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem2317800 q p h1)). Qed.
Lemma lem2317805 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2317806 (q : Prop) : (True = q) = q.
Proof. exact (@lem2317805 q). Qed.
Lemma lem2317807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317808 (q : Prop) : (term14 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem2317807) (@lem2317806 q)). Qed.
Lemma lem2317812 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem2317813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317814 : term15 = (@eq Prop False).
Proof. exact (MK_COMB (@lem2317813) (@lem2317812)). Qed.
Lemma lem2317815 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem2317816 (q : Prop) : ((~ True) = (~ q)) = (False = (~ q)).
Proof. exact (MK_COMB (@lem2317814) (@lem2317815 q)). Qed.
Lemma lem2317818 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2317819 (q : Prop) : (False = (~ q)) = (term16 q).
Proof. exact (@lem2317818 (~ q)). Qed.
Lemma lem2317821 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2317822 (q : Prop) : (term16 q) = q.
Proof. exact (@lem2317821 q). Qed.
Lemma lem2317823 (q : Prop) : (False = (~ q)) = q.
Proof. exact (TRANS (@lem2317819 q) (@lem2317822 q)). Qed.
Lemma lem2317824 (q : Prop) : ((~ True) = (~ q)) = q.
Proof. exact (TRANS (@lem2317816 q) (@lem2317823 q)). Qed.
Lemma lem2317825 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = (q = q).
Proof. exact (MK_COMB (@lem2317808 q) (@lem2317824 q)). Qed.
Lemma lem2317827 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2317828 (x : Prop) : (x = x) = True.
Proof. exact (@lem2317827 Prop x). Qed.
Lemma lem2317829 (q : Prop) : (q = q) = True.
Proof. exact (@lem2317828 q). Qed.
Lemma lem2317830 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = True.
Proof. exact (TRANS (@lem2317825 q) (@lem2317829 q)). Qed.
Lemma lem2317831 (q : Prop) : True = ((True = q) = ((~ True) = (~ q))).
Proof. exact (SYM (@lem2317830 q)). Qed.
Lemma lem2317832 (q : Prop) : (True = q) = ((~ True) = (~ q)).
Proof. exact (EQ_MP (@lem2317831 q) (@lem0)). Qed.
Lemma lem2317836 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2317837 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem2317836 q). Qed.
Lemma lem2317838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317839 (q : Prop) : (term17 q) = (term18 q).
Proof. exact (MK_COMB (@lem2317838) (@lem2317837 q)). Qed.
Lemma lem2317843 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2317844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317845 : term19 = (@eq Prop True).
Proof. exact (MK_COMB (@lem2317844) (@lem2317843)). Qed.
Lemma lem2317846 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem2317847 (q : Prop) : ((~ False) = (~ q)) = (True = (~ q)).
Proof. exact (MK_COMB (@lem2317845) (@lem2317846 q)). Qed.
Lemma lem2317849 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2317850 (q : Prop) : (True = (~ q)) = (~ q).
Proof. exact (@lem2317849 (~ q)). Qed.
Lemma lem2317851 (q : Prop) : ((~ False) = (~ q)) = (~ q).
Proof. exact (TRANS (@lem2317847 q) (@lem2317850 q)). Qed.
Lemma lem2317852 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem2317839 q) (@lem2317851 q)). Qed.
Lemma lem2317854 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2317855 (x : Prop) : (x = x) = True.
Proof. exact (@lem2317854 Prop x). Qed.
Lemma lem2317856 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem2317855 (~ q)). Qed.
Lemma lem2317857 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = True.
Proof. exact (TRANS (@lem2317852 q) (@lem2317856 q)). Qed.
Lemma lem2317858 (q : Prop) : True = ((False = q) = ((~ False) = (~ q))).
Proof. exact (SYM (@lem2317857 q)). Qed.
Lemma lem2317859 (q : Prop) : (False = q) = ((~ False) = (~ q)).
Proof. exact (EQ_MP (@lem2317858 q) (@lem0)). Qed.
Lemma lem2317860 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem2317801 q p h1) (@lem2317859 q)). Qed.
Lemma lem2317861 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem2317788 q p h1) (@lem2317832 q)). Qed.
Lemma lem2317866 (p : Prop) (q : Prop) : (p = q) = ((~ p) = (~ q)).
Proof. exact (or_elim (@lem2317765 p) (fun h0 : p = True => @lem2317861 q p h0) (fun h0 : p = False => @lem2317860 q p h0)). Qed.
Lemma lem2317867 (P : int -> Prop) : ((term20 P) = (term21 P)) = ((term22 P) = (term23 P)).
Proof. exact (@lem2317866 (term20 P) (term21 P)). Qed.
Lemma lem2317868 (P : int -> Prop) : ((term22 P) = (term23 P)) = ((term20 P) = (term21 P)).
Proof. exact (SYM (@lem2317867 P)). Qed.
Lemma lem2317872 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem2317753 A P) (@lem2317752 A P)). Qed.
Lemma lem2317873 (P : nat -> Prop) : (term24 P) = (term25 P).
Proof. exact (@lem2317872 nat P). Qed.
Lemma lem2317874 (P : int -> Prop) : (term26 P) = (term27 P).
Proof. exact (@lem2317873 (term28 P)). Qed.
Lemma lem2317875 (P : int -> Prop) (n : nat) : (term29 P n) = (term30 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem2317876 (P : int -> Prop) : (term31 P) = (term28 P).
Proof. exact (fun_ext (fun n : nat => @lem2317875 P n)). Qed.
Lemma lem2317877 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2317878 (P : int -> Prop) : (term32 P) = (term20 P).
Proof. exact (MK_COMB (@lem2317877) (@lem2317876 P)). Qed.
Lemma lem2317879 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2317880 (P : int -> Prop) : (term26 P) = (term22 P).
Proof. exact (MK_COMB (@lem2317879) (@lem2317878 P)). Qed.
Lemma lem2317881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317882 (P : int -> Prop) : (term33 P) = (term34 P).
Proof. exact (MK_COMB (@lem2317881) (@lem2317880 P)). Qed.
Lemma lem2317883 (P : int -> Prop) (n : nat) : (term29 P n) = (term30 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem2317884 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2317885 (P : int -> Prop) (n : nat) : (term35 P n) = (term36 P n).
Proof. exact (MK_COMB (@lem2317884) (@lem2317883 P n)). Qed.
Lemma lem2317886 (P : int -> Prop) : (term37 P) = (term38 P).
Proof. exact (fun_ext (fun n : nat => @lem2317885 P n)). Qed.
Lemma lem2317887 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2317888 (P : int -> Prop) : (term27 P) = (term39 P).
Proof. exact (MK_COMB (@lem2317887) (@lem2317886 P)). Qed.
Lemma lem2317889 (P : int -> Prop) : ((term26 P) = (term27 P)) = ((term22 P) = (term39 P)).
Proof. exact (MK_COMB (@lem2317882 P) (@lem2317888 P)). Qed.
Lemma lem2317890 (P : int -> Prop) : (term22 P) = (term39 P).
Proof. exact (EQ_MP (@lem2317889 P) (@lem2317874 P)). Qed.
Lemma lem2317896 (P : int -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem2317750 P) (@lem2317749 P)). Qed.
Lemma lem2317897 (P : int -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem2317896 (term42 P)). Qed.
Lemma lem2317898 (P : int -> Prop) (n : nat) : (term43 P n) = (term36 P n).
Proof. exact (eq_refl (term43 P n)). Qed.
Lemma lem2317899 (P : int -> Prop) : (term44 P) = (term38 P).
Proof. exact (fun_ext (fun n : nat => @lem2317898 P n)). Qed.
Lemma lem2317900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2317901 (P : int -> Prop) : (term40 P) = (term39 P).
Proof. exact (MK_COMB (@lem2317900) (@lem2317899 P)). Qed.
Lemma lem2317902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317903 (P : int -> Prop) : (term45 P) = (term46 P).
Proof. exact (MK_COMB (@lem2317902) (@lem2317901 P)). Qed.
Lemma lem2317904 (P : int -> Prop) (x : int) : (term47 P x) = (term48 P x).
Proof. exact (eq_refl (term47 P x)). Qed.
Lemma lem2317905 (P : int -> Prop) : (term49 P) = (term50 P).
Proof. exact (fun_ext (fun x : int => @lem2317904 P x)). Qed.
Lemma lem2317906 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2317907 (P : int -> Prop) : (term41 P) = (term51 P).
Proof. exact (MK_COMB (@lem2317906) (@lem2317905 P)). Qed.
Lemma lem2317908 (P : int -> Prop) : ((term40 P) = (term41 P)) = ((term39 P) = (term51 P)).
Proof. exact (MK_COMB (@lem2317903 P) (@lem2317907 P)). Qed.
Lemma lem2317909 (P : int -> Prop) : (term39 P) = (term51 P).
Proof. exact (EQ_MP (@lem2317908 P) (@lem2317897 P)). Qed.
Lemma lem2317916 (P : int -> Prop) : (term22 P) = (term51 P).
Proof. exact (TRANS (@lem2317890 P) (@lem2317909 P)). Qed.
Lemma lem2317917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317918 (P : int -> Prop) : (term34 P) = (term52 P).
Proof. exact (MK_COMB (@lem2317917) (@lem2317916 P)). Qed.
Lemma lem2317920 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem2317753 A P) (@lem2317752 A P)). Qed.
Lemma lem2317921 (P : int -> Prop) : (term53 P) = (term54 P).
Proof. exact (@lem2317920 int P). Qed.
Lemma lem2317922 (P : int -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem2317921 (term57 P)). Qed.
Lemma lem2317923 (P : int -> Prop) (x : int) : (term58 P x) = (term59 P x).
Proof. exact (eq_refl (term58 P x)). Qed.
Lemma lem2317924 (P : int -> Prop) : (term60 P) = (term57 P).
Proof. exact (fun_ext (fun x : int => @lem2317923 P x)). Qed.
Lemma lem2317925 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2317926 (P : int -> Prop) : (term61 P) = (term21 P).
Proof. exact (MK_COMB (@lem2317925) (@lem2317924 P)). Qed.
Lemma lem2317927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2317928 (P : int -> Prop) : (term55 P) = (term23 P).
Proof. exact (MK_COMB (@lem2317927) (@lem2317926 P)). Qed.
Lemma lem2317929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2317930 (P : int -> Prop) : (term62 P) = (term63 P).
Proof. exact (MK_COMB (@lem2317929) (@lem2317928 P)). Qed.
Lemma lem2317931 (P : int -> Prop) (x : int) : (term58 P x) = (term59 P x).
Proof. exact (eq_refl (term58 P x)). Qed.
Lemma lem2317932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2317933 (P : int -> Prop) (x : int) : (term64 P x) = (term48 P x).
Proof. exact (MK_COMB (@lem2317932) (@lem2317931 P x)). Qed.
Lemma lem2317934 (P : int -> Prop) : (term65 P) = (term50 P).
Proof. exact (fun_ext (fun x : int => @lem2317933 P x)). Qed.
Lemma lem2317935 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2317936 (P : int -> Prop) : (term56 P) = (term51 P).
Proof. exact (MK_COMB (@lem2317935) (@lem2317934 P)). Qed.
Lemma lem2317937 (P : int -> Prop) : ((term55 P) = (term56 P)) = ((term23 P) = (term51 P)).
Proof. exact (MK_COMB (@lem2317930 P) (@lem2317936 P)). Qed.
Lemma lem2317938 (P : int -> Prop) : (term23 P) = (term51 P).
Proof. exact (EQ_MP (@lem2317937 P) (@lem2317922 P)). Qed.
Lemma lem2317945 (P : int -> Prop) : ((term22 P) = (term23 P)) = ((term51 P) = (term51 P)).
Proof. exact (MK_COMB (@lem2317918 P) (@lem2317938 P)). Qed.
Lemma lem2317947 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2317948 (x : Prop) : (x = x) = True.
Proof. exact (@lem2317947 Prop x). Qed.
Lemma lem2317949 (P : int -> Prop) : ((term51 P) = (term51 P)) = True.
Proof. exact (@lem2317948 (term51 P)). Qed.
Lemma lem2317950 (P : int -> Prop) : ((term22 P) = (term23 P)) = True.
Proof. exact (TRANS (@lem2317945 P) (@lem2317949 P)). Qed.
Lemma lem2317951 (P : int -> Prop) : True = ((term22 P) = (term23 P)).
Proof. exact (SYM (@lem2317950 P)). Qed.
Lemma lem2317952 (P : int -> Prop) : (term22 P) = (term23 P).
Proof. exact (EQ_MP (@lem2317951 P) (@lem0)). Qed.
Lemma lem2317953 (P : int -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem2317868 P) (@lem2317952 P)). Qed.
Lemma lem2317958 : term66.
Proof. exact (fun P : int -> Prop => @lem2317953 P). Qed.
