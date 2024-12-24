Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1317906_term_abbrevs.
Require Import NADD_ADD_WELLDEF_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import thm1317744_spec.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1317789 : hreal_add = term0.
Proof. exact (@hreal_add_def). Qed.
Lemma lem1317790 (x : hreal) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1317791 (x : hreal) : (hreal_add x) = (term1 x).
Proof. exact (MK_COMB (@lem1317789) (@lem1317790 x)). Qed.
Lemma lem1317792 (x : hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1317793 (x : hreal) : (term3 x) = (term3 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1317794 (x : hreal) : ((hreal_add x) = (term1 x)) = ((hreal_add x) = (term2 x)).
Proof. exact (MK_COMB (@lem1317793 x) (@lem1317792 x)). Qed.
Lemma lem1317795 (x : hreal) : (hreal_add x) = (term2 x).
Proof. exact (EQ_MP (@lem1317794 x) (@lem1317791 x)). Qed.
Lemma lem1317796 (y : hreal) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1317797 (x : hreal) (y : hreal) : (hreal_add x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1317795 x) (@lem1317796 y)). Qed.
Lemma lem1317798 (x : hreal) (y : hreal) : (term4 x y) = (term5 x y).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1317799 (x : hreal) (y : hreal) : (term6 x y) = (term6 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1317800 (x : hreal) (y : hreal) : ((hreal_add x y) = (term4 x y)) = ((hreal_add x y) = (term5 x y)).
Proof. exact (MK_COMB (@lem1317799 x y) (@lem1317798 x y)). Qed.
Lemma lem1317801 (x : hreal) (y : hreal) : (hreal_add x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1317800 x y) (@lem1317797 x y)). Qed.
Lemma lem1317802 (x : nadd) : (term7 x) = ((term8 x) = (nadd_eq x)).
Proof. exact (@lem1317744 (nadd_eq x)). Qed.
Lemma lem1317803 (x : nadd) : (nadd_eq x) = (nadd_eq x).
Proof. exact (eq_refl (nadd_eq x)). Qed.
Lemma lem1317804 (x : nadd) : term7 x.
Proof. exact (ex_intro (term9 x) x (@lem1317803 x)). Qed.
Lemma lem1317805 (x : nadd) : (term8 x) = (nadd_eq x).
Proof. exact (EQ_MP (@lem1317802 x) (@lem1317804 x)). Qed.
Lemma lem1317806 (x : nadd) (y : nadd) : (term10 x y) = (term11 x y).
Proof. exact (@lem1317801 (term12 x) (term12 y)). Qed.
Lemma lem1317807 (x : nadd) : (term8 x) = (nadd_eq x).
Proof. exact (@lem1317805 x). Qed.
Lemma lem1317808 (y : nadd) : (term8 y) = (nadd_eq y).
Proof. exact (@lem1317805 y). Qed.
Lemma lem1317809 (x : nadd) (y : nadd) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1317810 (y : nadd) (x : nadd) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1317809 x y) (@lem1317807 x)). Qed.
Lemma lem1317811 (y : nadd) (x : nadd) : (term15 y x) = (term16 y x).
Proof. exact (eq_refl (term15 y x)). Qed.
Lemma lem1317812 (y : nadd) (x : nadd) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1317813 (y : nadd) (x : nadd) : ((term14 y x) = (term15 y x)) = ((term14 y x) = (term16 y x)).
Proof. exact (MK_COMB (@lem1317812 y x) (@lem1317811 y x)). Qed.
Lemma lem1317814 (y : nadd) (x : nadd) : (term14 y x) = (term18 y x).
Proof. exact (eq_refl (term14 y x)). Qed.
Lemma lem1317815 : (@eq ((nadd -> Prop) -> Prop)) = (@eq ((nadd -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((nadd -> Prop) -> Prop))). Qed.
Lemma lem1317816 (y : nadd) (x : nadd) : (term17 y x) = (term19 y x).
Proof. exact (MK_COMB (@lem1317815) (@lem1317814 y x)). Qed.
Lemma lem1317817 (y : nadd) (x : nadd) : (term16 y x) = (term16 y x).
Proof. exact (eq_refl (term16 y x)). Qed.
Lemma lem1317818 (y : nadd) (x : nadd) : ((term14 y x) = (term16 y x)) = ((term18 y x) = (term16 y x)).
Proof. exact (MK_COMB (@lem1317816 y x) (@lem1317817 y x)). Qed.
Lemma lem1317819 (y : nadd) (x : nadd) : ((term14 y x) = (term15 y x)) = ((term18 y x) = (term16 y x)).
Proof. exact (TRANS (@lem1317813 y x) (@lem1317818 y x)). Qed.
Lemma lem1317820 (y : nadd) (x : nadd) : (term18 y x) = (term16 y x).
Proof. exact (EQ_MP (@lem1317819 y x) (@lem1317810 y x)). Qed.
Lemma lem1317821 (x : nadd) (y : nadd) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1317820 y x) (@lem1317808 y)). Qed.
Lemma lem1317822 (x : nadd) (y : nadd) : (term21 x y) = ((term10 x y) = (term22 x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1317823 (x : nadd) (y : nadd) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1317824 (x : nadd) (y : nadd) : ((term20 x y) = (term21 x y)) = ((term20 x y) = ((term10 x y) = (term22 x y))).
Proof. exact (MK_COMB (@lem1317823 x y) (@lem1317822 x y)). Qed.
Lemma lem1317825 (x : nadd) (y : nadd) : (term20 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1317826 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1317827 (x : nadd) (y : nadd) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1317826) (@lem1317825 x y)). Qed.
Lemma lem1317828 (x : nadd) (y : nadd) : ((term10 x y) = (term22 x y)) = ((term10 x y) = (term22 x y)).
Proof. exact (eq_refl ((term10 x y) = (term22 x y))). Qed.
Lemma lem1317829 (x : nadd) (y : nadd) : ((term20 x y) = ((term10 x y) = (term22 x y))) = (((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y))).
Proof. exact (MK_COMB (@lem1317827 x y) (@lem1317828 x y)). Qed.
Lemma lem1317830 (x : nadd) (y : nadd) : ((term20 x y) = (term21 x y)) = (((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y))).
Proof. exact (TRANS (@lem1317824 x y) (@lem1317829 x y)). Qed.
Lemma lem1317831 (x : nadd) (y : nadd) : ((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y)).
Proof. exact (EQ_MP (@lem1317830 x y) (@lem1317821 x y)). Qed.
Lemma lem1317832 (x : nadd) (y : nadd) : (term10 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem1317831 x y) (@lem1317806 x y)). Qed.
Lemma lem1317833 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term25 u x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1317834 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term26 x x' y y'.
Proof. exact (proj2 (@lem1317833 u x x' y y' h1)). Qed.
Lemma lem1317835 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term27 x' y' u.
Proof. exact (proj1 (@lem1317833 u x x' y y' h1)). Qed.
Lemma lem1317836 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : nadd_eq y y'.
Proof. exact (proj2 (@lem1317834 u x x' y y' h1)). Qed.
Lemma lem1317837 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : nadd_eq x x'.
Proof. exact (proj1 (@lem1317834 u x x' y y' h1)). Qed.
Lemma lem1317838 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term26 x x' y y'.
Proof. exact (conj (@lem1317837 u x x' y y' h1) (@lem1317836 u x x' y y' h1)). Qed.
Lemma lem1317839 (x : nadd) : term28 x.
Proof. exact (@lem1274424 x). Qed.
Lemma lem1317840 (x : nadd) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1317841 (x : nadd) : term29 x.
Proof. exact (EQ_MP (@lem1317840 x) (@lem1317839 x)). Qed.
Lemma lem1317842 (x : nadd) (x' : nadd) : term30 x x'.
Proof. exact (@lem1317841 x x'). Qed.
Lemma lem1317843 (x : nadd) (x' : nadd) : (term30 x x') = (term31 x x').
Proof. exact (eq_refl (term30 x x')). Qed.
Lemma lem1317844 (x : nadd) (x' : nadd) : term31 x x'.
Proof. exact (EQ_MP (@lem1317843 x x') (@lem1317842 x x')). Qed.
Lemma lem1317845 (x : nadd) (x' : nadd) (y : nadd) : term32 x x' y.
Proof. exact (@lem1317844 x x' y). Qed.
Lemma lem1317846 (x : nadd) (y : nadd) (x' : nadd) : (term32 x x' y) = (term33 x y x').
Proof. exact (eq_refl (term32 x x' y)). Qed.
Lemma lem1317847 (x : nadd) (y : nadd) (x' : nadd) : term33 x y x'.
Proof. exact (EQ_MP (@lem1317846 x y x') (@lem1317845 x x' y)). Qed.
Lemma lem1317848 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term34 x y x' y'.
Proof. exact (@lem1317847 x y x' y'). Qed.
Lemma lem1317849 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term34 x y x' y') = (term35 x y x' y').
Proof. exact (eq_refl (term34 x y x' y')). Qed.
Lemma lem1317852 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term35 x y x' y'.
Proof. exact (EQ_MP (@lem1317849 x y x' y') (@lem1317848 x y x' y')). Qed.
Lemma lem1317853 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term36 x y x' y'.
Proof. exact (@lem1317852 x y x' y' (@lem1317838 u x x' y y' h1)). Qed.
Lemma lem1317854 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term37 x y x' y' u.
Proof. exact (conj (@lem1317853 u x x' y y' h1) (@lem1317835 u x x' y y' h1)). Qed.
Lemma lem1317855 (x : nadd) : term38 x.
Proof. exact (@lem1268295 x). Qed.
Lemma lem1317856 (x : nadd) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1317857 (x : nadd) : term39 x.
Proof. exact (EQ_MP (@lem1317856 x) (@lem1317855 x)). Qed.
Lemma lem1317858 (x : nadd) (y : nadd) : term40 x y.
Proof. exact (@lem1317857 x y). Qed.
Lemma lem1317859 (y : nadd) (x : nadd) : (term40 x y) = (term41 y x).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1317860 (y : nadd) (x : nadd) : term41 y x.
Proof. exact (EQ_MP (@lem1317859 y x) (@lem1317858 x y)). Qed.
Lemma lem1317861 (y : nadd) (x : nadd) (z : nadd) : term42 y x z.
Proof. exact (@lem1317860 y x z). Qed.
Lemma lem1317862 (y : nadd) (x : nadd) (z : nadd) : (term42 y x z) = (term43 y x z).
Proof. exact (eq_refl (term42 y x z)). Qed.
Lemma lem1317865 (y : nadd) (x : nadd) (z : nadd) : term43 y x z.
Proof. exact (EQ_MP (@lem1317862 y x z) (@lem1317861 y x z)). Qed.
Lemma lem1317866 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (u : nadd) : term44 x' y' x y u.
Proof. exact (@lem1317865 (nadd_add x' y') (nadd_add x y) u). Qed.
Lemma lem1317867 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term27 x y u.
Proof. exact (@lem1317866 x' y' x y u (@lem1317854 u x x' y y' h1)). Qed.
Lemma lem1317868 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (h1 : term45 u x x' y) : term45 u x x' y.
Proof. exact (h1). Qed.
Lemma lem1317869 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (h1 : term45 u x x' y) : term27 x y u.
Proof. exact (ex_elim (@lem1317868 u x x' y h1) (fun y' : nadd => fun h0 : term46 u x x' y y' => @lem1317867 u x x' y y' h0)). Qed.
Lemma lem1317870 (u : nadd) (x : nadd) (y : nadd) (h1 : term47 u x y) : term47 u x y.
Proof. exact (h1). Qed.
Lemma lem1317871 (u : nadd) (x : nadd) (y : nadd) (h1 : term47 u x y) : term27 x y u.
Proof. exact (ex_elim (@lem1317870 u x y h1) (fun x' : nadd => fun h0 : term48 u x y x' => @lem1317869 u x x' y h0)). Qed.
Lemma lem1317872 (x : nadd) (y : nadd) (u : nadd) (h1 : term27 x y u) : term27 x y u.
Proof. exact (h1). Qed.
Lemma lem1317873 (x : nadd) : term49 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1317874 (x : nadd) : (term49 x) = (nadd_eq x x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1317875 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1317874 x) (@lem1317873 x)). Qed.
Lemma lem1317876 (y : nadd) : term49 y.
Proof. exact (@lem1267990 y). Qed.
Lemma lem1317877 (y : nadd) : (term49 y) = (nadd_eq y y).
Proof. exact (eq_refl (term49 y)). Qed.
Lemma lem1317878 (y : nadd) : nadd_eq y y.
Proof. exact (EQ_MP (@lem1317877 y) (@lem1317876 y)). Qed.
Lemma lem1317879 (x : nadd) (y : nadd) : term50 x y.
Proof. exact (conj (@lem1317875 x) (@lem1317878 y)). Qed.
Lemma lem1317880 (x : nadd) (y : nadd) (u : nadd) (h1 : term27 x y u) : term51 u x y.
Proof. exact (conj (@lem1317872 x y u h1) (@lem1317879 x y)). Qed.
Lemma lem1317881 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term25 u x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1317882 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term45 u x x' y.
Proof. exact (ex_intro (term46 u x x' y) y' (@lem1317881 u x x' y y' h1)). Qed.
Lemma lem1317883 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term47 u x y.
Proof. exact (ex_intro (term48 u x y) x' (@lem1317882 u x x' y y' h1)). Qed.
Lemma lem1317886 (x' : nadd) (y' : nadd) (u : nadd) (x : nadd) (y : nadd) : term52 x' y' u x y.
Proof. exact (fun h0 : term25 u x x' y y' => @lem1317883 u x x' y y' h0). Qed.
Lemma lem1317887 (u : nadd) (x : nadd) (y : nadd) : term53 u x y.
Proof. exact (@lem1317886 x y u x y). Qed.
Lemma lem1317888 (x : nadd) (y : nadd) (u : nadd) (h1 : term27 x y u) : term47 u x y.
Proof. exact (@lem1317887 u x y (@lem1317880 x y u h1)). Qed.
Lemma lem1317889 (u : nadd) (x : nadd) (y : nadd) : term54 u x y.
Proof. exact (fun h0 : term27 x y u => @lem1317888 x y u h0). Qed.
Lemma lem1317890 (x : nadd) (y : nadd) (u : nadd) : term55 x y u.
Proof. exact (fun h0 : term47 u x y => @lem1317871 u x y h0). Qed.
Lemma lem1317891 (u : nadd) (x : nadd) (y : nadd) : term56 u x y.
Proof. exact (conj (@lem1317890 x y u) (@lem1317889 u x y)). Qed.
Lemma lem1317892 (x : nadd) (y : nadd) (u : nadd) : (term56 u x y) = ((term47 u x y) = (term27 x y u)).
Proof. exact (@lem32 (term47 u x y) (term27 x y u)). Qed.
Lemma lem1317893 (x : nadd) (y : nadd) (u : nadd) : (term47 u x y) = (term27 x y u).
Proof. exact (EQ_MP (@lem1317892 x y u) (@lem1317891 u x y)). Qed.
Lemma lem1317894 (x : nadd) (y : nadd) : (term57 x y) = (term58 x y).
Proof. exact (fun_ext (fun u : nadd => @lem1317893 x y u)). Qed.
Lemma lem1317895 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1317896 (x : nadd) (y : nadd) : (term22 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1317895) (@lem1317894 x y)). Qed.
Lemma lem1317897 (x : nadd) (y : nadd) : (term10 x y) = (term59 x y).
Proof. exact (TRANS (@lem1317832 x y) (@lem1317896 x y)). Qed.
Lemma lem1317898 (t : nadd -> Prop) : (term60 t) = t.
Proof. exact (@lem9127 nadd Prop t). Qed.
Lemma lem1317901 (x : nadd) (y : nadd) : (term58 x y) = (term61 x y).
Proof. exact (@lem1317898 (term61 x y)). Qed.
Lemma lem1317902 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1317903 (x : nadd) (y : nadd) : (term59 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1317902) (@lem1317901 x y)). Qed.
Lemma lem1317904 (x : nadd) (y : nadd) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1317905 (x : nadd) (y : nadd) : ((term10 x y) = (term59 x y)) = ((term10 x y) = (term62 x y)).
Proof. exact (MK_COMB (@lem1317904 x y) (@lem1317903 x y)). Qed.
Lemma lem1317906 (x : nadd) (y : nadd) : (term10 x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1317905 x y) (@lem1317897 x y)). Qed.
