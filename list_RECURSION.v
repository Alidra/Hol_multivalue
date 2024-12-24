Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import list_RECURSION_term_abbrevs.
Require Import BETA_THM_spec.
Require Import CONSTR_REC_spec.
Require Import thm0_spec.
Require Import thm1066089_spec.
Require Import thm1066561_spec.
Require Import thm1066562_spec.
Require Import thm1066568_spec.
Require Import thm1066569_spec.
Require Import thm1070927_spec.
Require Import thm1070977_spec.
Require Import thm1070978_spec.
Require Import thm1070982_spec.
Require Import thm1070983_spec.
Require Import thm1071333_spec.
Require Import thm1071695_spec.
Require Import thm7_spec.
Require Import thm9102_spec.
Lemma lem1071854 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : fn = (term0 A Z fn').
Proof. exact (h1). Qed.
Lemma lem1071855 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (NIL' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NIL' = (term1 A)) : (fn (@nil A)) = (term2 A Z fn' NIL').
Proof. exact (MK_COMB (@lem1071854 A Z fn fn' h1) (@lem1071333 A NIL' h2)). Qed.
Lemma lem1071856 {A Z : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term5 A Z fn' CONS' a0 a1).
Proof. exact (MK_COMB (@lem1071854 A Z fn fn' h2) (@lem1071695 A a0 a1 CONS' h1)). Qed.
Lemma lem1071857 {A Z : Type'} (fn : type1337 A Z) (NIL' : recspace A) : (term2 A Z fn NIL') = (term6 A Z fn NIL').
Proof. exact (eq_refl (term2 A Z fn NIL')). Qed.
Lemma lem1071858 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (NIL' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NIL' = (term1 A)) : (fn (@nil A)) = (term6 A Z fn' NIL').
Proof. exact (TRANS (@lem1071855 A Z fn fn' NIL' h1 h2) (@lem1071857 A Z fn' NIL')). Qed.
Lemma lem1071859 {A Z : Type'} (fn : type1337 A Z) (CONS' : type1399 A) (a0 : A) (a1 : list A) : (term5 A Z fn CONS' a0 a1) = (term7 A Z fn CONS' a0 a1).
Proof. exact (eq_refl (term5 A Z fn CONS' a0 a1)). Qed.
Lemma lem1071860 {A Z : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term7 A Z fn' CONS' a0 a1).
Proof. exact (TRANS (@lem1071856 A Z a0 a1 CONS' fn fn' h1 h2) (@lem1071859 A Z fn' CONS' a0 a1)). Qed.
Lemma lem1071861 {A : Type'} (a : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term9 A list' a) = ((term10 A a) = (@_dest_list A a)).
Proof. exact (@lem1070983 A (@_dest_list A a) list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071862 {A : Type'} : (@_dest_list A) = (@_dest_list A).
Proof. exact (eq_refl (@_dest_list A)). Qed.
Lemma lem1071863 {A : Type'} (a : list A) : (term10 A a) = (@_dest_list A a).
Proof. exact (MK_COMB (@lem1071862 A) (@lem1070977 A a)). Qed.
Lemma lem1071864 {A : Type'} (a : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : ((term10 A a) = (@_dest_list A a)) = (term9 A list' a).
Proof. exact (SYM (@lem1071861 A a list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071865 {A : Type'} (a : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : term9 A list' a.
Proof. exact (EQ_MP (@lem1071864 A a list' CONS' NIL' h1 h2 h3) (@lem1071863 A a)). Qed.
Lemma lem1071866 {A : Type'} (list' : type1338 A) (a : list A) : (term9 A list' a) = ((term9 A list' a) = True).
Proof. exact (@lem7 (term9 A list' a)). Qed.
Lemma lem1071868 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : term11 A list' CONS'.
Proof. exact (proj2 (@lem1070927 A list' NIL' CONS' h1)). Qed.
Lemma lem1071871 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : list' NIL'.
Proof. exact (proj1 (@lem1070927 A list' NIL' CONS' h1)). Qed.
Lemma lem1071873 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (list' r) = ((term12 A r) = r).
Proof. exact (TRANS (@lem1070982 A r list' CONS' NIL' h1 h2 h3) (@lem1070978 A r)). Qed.
Lemma lem1071874 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (list' r) = ((term12 A r) = r).
Proof. exact (@lem1071873 A r list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071875 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (list' NIL') = ((term12 A NIL') = NIL').
Proof. exact (@lem1071874 A NIL' list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071876 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term12 A NIL') = NIL'.
Proof. exact (EQ_MP (@lem1071875 A list' CONS' NIL' h1 h2 h3) (@lem1071871 A list' NIL' CONS' h2)). Qed.
Lemma lem1071877 {A : Type'} (a0 : A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : term13 A list' CONS' a0.
Proof. exact (@lem1071868 A list' NIL' CONS' h1 a0). Qed.
Lemma lem1071878 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) : (term13 A list' CONS' a0) = (term14 A list' CONS' a0).
Proof. exact (eq_refl (term13 A list' CONS' a0)). Qed.
Lemma lem1071879 {A : Type'} (a0 : A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : term14 A list' CONS' a0.
Proof. exact (EQ_MP (@lem1071878 A list' CONS' a0) (@lem1071877 A a0 list' NIL' CONS' h1)). Qed.
Lemma lem1071880 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : term15 A list' CONS' a0 a1.
Proof. exact (@lem1071879 A a0 list' NIL' CONS' h1 a1). Qed.
Lemma lem1071881 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term15 A list' CONS' a0 a1) = (term16 A list' CONS' a0 a1).
Proof. exact (eq_refl (term15 A list' CONS' a0 a1)). Qed.
Lemma lem1071884 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : term16 A list' CONS' a0 a1.
Proof. exact (EQ_MP (@lem1071881 A list' CONS' a0 a1) (@lem1071880 A a0 a1 list' NIL' CONS' h1)). Qed.
Lemma lem1071885 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : term16 A list' CONS' a0 a1.
Proof. exact (@lem1071884 A a0 a1 list' NIL' CONS' h1). Qed.
Lemma lem1071886 {A : Type'} (a0 : A) (a1 : list A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term8 A NIL' CONS')) : term17 A list' CONS' a0 a1.
Proof. exact (@lem1071885 A a0 (@_dest_list A a1) list' NIL' CONS' h1). Qed.
Lemma lem1071888 {A : Type'} (a : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term9 A list' a) = True.
Proof. exact (EQ_MP (@lem1071866 A list' a) (@lem1071865 A a list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071889 {A : Type'} (a : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term9 A list' a) = True.
Proof. exact (@lem1071888 A a list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071890 {A : Type'} (a1 : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term9 A list' a1) = True.
Proof. exact (@lem1071889 A a1 list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071891 {A : Type'} (a1 : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : True = (term9 A list' a1).
Proof. exact (SYM (@lem1071890 A a1 list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071892 {A : Type'} (a1 : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : term9 A list' a1.
Proof. exact (EQ_MP (@lem1071891 A a1 list' CONS' NIL' h1 h2 h3) (@lem0)). Qed.
Lemma lem1071893 {A : Type'} (a0 : A) (a1 : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : term18 A list' CONS' a0 a1.
Proof. exact (@lem1071886 A a0 a1 list' NIL' CONS' h2 (@lem1071892 A a1 list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071895 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (list' r) = ((term12 A r) = r).
Proof. exact (TRANS (@lem1070982 A r list' CONS' NIL' h1 h2 h3) (@lem1070978 A r)). Qed.
Lemma lem1071896 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (list' r) = ((term12 A r) = r).
Proof. exact (@lem1071895 A r list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071897 {A : Type'} (a0 : A) (a1 : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term18 A list' CONS' a0 a1) = ((term19 A CONS' a0 a1) = (term20 A CONS' a0 a1)).
Proof. exact (@lem1071896 A (term20 A CONS' a0 a1) list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071898 {A : Type'} (a0 : A) (a1 : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term19 A CONS' a0 a1) = (term20 A CONS' a0 a1).
Proof. exact (EQ_MP (@lem1071897 A a0 a1 list' CONS' NIL' h1 h2 h3) (@lem1071893 A a0 a1 list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071899 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1071900 {A Z : Type'} (fn : type1337 A Z) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term6 A Z fn NIL') = (fn NIL').
Proof. exact (MK_COMB (@lem1071899 A Z fn) (@lem1071876 A list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071901 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : list' = (term8 A NIL' CONS')) (h4 : NIL' = (term1 A)) : (fn (@nil A)) = (fn' NIL').
Proof. exact (TRANS (@lem1071858 A Z fn fn' NIL' h2 h4) (@lem1071900 A Z fn' list' CONS' NIL' h1 h3 h4)). Qed.
Lemma lem1071902 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1071903 {A Z : Type'} (fn : type1337 A Z) (a0 : A) (a1 : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : list' = (term8 A NIL' CONS')) (h3 : NIL' = (term1 A)) : (term7 A Z fn CONS' a0 a1) = (term21 A Z fn CONS' a0 a1).
Proof. exact (MK_COMB (@lem1071902 A Z fn) (@lem1071898 A a0 a1 list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071904 {A Z : Type'} (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : list' = (term8 A NIL' CONS')) (h4 : NIL' = (term1 A)) : (term4 A Z fn a0 a1) = (term21 A Z fn' CONS' a0 a1).
Proof. exact (TRANS (@lem1071860 A Z a0 a1 CONS' fn fn' h1 h2) (@lem1071903 A Z fn' a0 a1 list' CONS' NIL' h1 h3 h4)). Qed.
Lemma lem1071905 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term1 A)) : NIL' = (term1 A).
Proof. exact (h1). Qed.
Lemma lem1071906 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1071907 {A Z : Type'} (fn : type1337 A Z) (NIL' : recspace A) (h1 : NIL' = (term1 A)) : (fn NIL') = (term22 A Z fn).
Proof. exact (MK_COMB (@lem1071906 A Z fn) (@lem1071905 A NIL' h1)). Qed.
Lemma lem1071908 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : list' = (term8 A NIL' CONS')) (h4 : NIL' = (term1 A)) : (fn (@nil A)) = (term22 A Z fn').
Proof. exact (TRANS (@lem1071901 A Z fn fn' list' CONS' NIL' h1 h2 h3 h4) (@lem1071907 A Z fn' NIL' h4)). Qed.
Lemma lem1071909 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term3 A)) : CONS' = (term3 A).
Proof. exact (h1). Qed.
Lemma lem1071910 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem1071911 {A : Type'} (a0 : A) (CONS' : type1399 A) (h1 : CONS' = (term3 A)) : (CONS' a0) = (term23 A a0).
Proof. exact (MK_COMB (@lem1071909 A CONS' h1) (@lem1071910 A a0)). Qed.
Lemma lem1071912 {A : Type'} (a0 : A) : (term23 A a0) = (term24 A a0).
Proof. exact (eq_refl (term23 A a0)). Qed.
Lemma lem1071913 {A : Type'} (CONS' : type1399 A) (a0 : A) : (term25 A CONS' a0) = (term25 A CONS' a0).
Proof. exact (eq_refl (term25 A CONS' a0)). Qed.
Lemma lem1071914 {A : Type'} (CONS' : type1399 A) (a0 : A) : ((CONS' a0) = (term23 A a0)) = ((CONS' a0) = (term24 A a0)).
Proof. exact (MK_COMB (@lem1071913 A CONS' a0) (@lem1071912 A a0)). Qed.
Lemma lem1071915 {A : Type'} (a0 : A) (CONS' : type1399 A) (h1 : CONS' = (term3 A)) : (CONS' a0) = (term24 A a0).
Proof. exact (EQ_MP (@lem1071914 A CONS' a0) (@lem1071911 A a0 CONS' h1)). Qed.
Lemma lem1071916 {A : Type'} (a1 : list A) : (@_dest_list A a1) = (@_dest_list A a1).
Proof. exact (eq_refl (@_dest_list A a1)). Qed.
Lemma lem1071917 {A : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (h1 : CONS' = (term3 A)) : (term20 A CONS' a0 a1) = (term26 A a0 a1).
Proof. exact (MK_COMB (@lem1071915 A a0 CONS' h1) (@lem1071916 A a1)). Qed.
Lemma lem1071918 {A : Type'} (a0 : A) (a1 : list A) : (term26 A a0 a1) = (term27 A a0 a1).
Proof. exact (eq_refl (term26 A a0 a1)). Qed.
Lemma lem1071919 {A : Type'} (CONS' : type1399 A) (a0 : A) (a1 : list A) : (term28 A CONS' a0 a1) = (term28 A CONS' a0 a1).
Proof. exact (eq_refl (term28 A CONS' a0 a1)). Qed.
Lemma lem1071920 {A : Type'} (CONS' : type1399 A) (a0 : A) (a1 : list A) : ((term20 A CONS' a0 a1) = (term26 A a0 a1)) = ((term20 A CONS' a0 a1) = (term27 A a0 a1)).
Proof. exact (MK_COMB (@lem1071919 A CONS' a0 a1) (@lem1071918 A a0 a1)). Qed.
Lemma lem1071921 {A : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (h1 : CONS' = (term3 A)) : (term20 A CONS' a0 a1) = (term27 A a0 a1).
Proof. exact (EQ_MP (@lem1071920 A CONS' a0 a1) (@lem1071917 A a0 a1 CONS' h1)). Qed.
Lemma lem1071922 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1071923 {A Z : Type'} (fn : type1337 A Z) (a0 : A) (a1 : list A) (CONS' : type1399 A) (h1 : CONS' = (term3 A)) : (term21 A Z fn CONS' a0 a1) = (term29 A Z fn a0 a1).
Proof. exact (MK_COMB (@lem1071922 A Z fn) (@lem1071921 A a0 a1 CONS' h1)). Qed.
Lemma lem1071924 {A Z : Type'} (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : list' = (term8 A NIL' CONS')) (h4 : NIL' = (term1 A)) : (term4 A Z fn a0 a1) = (term29 A Z fn' a0 a1).
Proof. exact (TRANS (@lem1071904 A Z a0 a1 fn fn' list' CONS' NIL' h1 h2 h3 h4) (@lem1071923 A Z fn' a0 a1 CONS' h1)). Qed.
Lemma lem1071925 {A Z : Type'} (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : list' = (term8 A NIL' CONS')) (h4 : NIL' = (term1 A)) : term30 A Z fn fn' a0 a1.
Proof. exact (conj (@lem1071908 A Z fn fn' list' CONS' NIL' h1 h2 h3 h4) (@lem1071924 A Z a0 a1 fn fn' list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071926 {A Z : Type'} (list' : type1338 A) (a0 : A) (a1 : list A) (CONS' : type1399 A) (fn : type1142 A Z) (fn' : type1337 A Z) (NIL' : recspace A) (h1 : CONS' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : NIL' = (term1 A)) : term31 A Z list' NIL' CONS' fn fn' a0 a1.
Proof. exact (fun h0 : list' = (term8 A NIL' CONS') => @lem1071925 A Z a0 a1 fn fn' list' CONS' NIL' h1 h2 h0 h3). Qed.
Lemma lem1071927 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1071928 {A Z : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (NIL' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NIL' = (term1 A)) : term32 A Z list' NIL' CONS' fn fn' a0 a1.
Proof. exact (fun h0 : CONS' = (term3 A) => @lem1071926 A Z list' a0 a1 CONS' fn fn' NIL' h0 h1 h2). Qed.
Lemma lem1071929 {A Z : Type'} (list' : type1338 A) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (NIL' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NIL' = (term1 A)) : term33 A Z list' NIL' fn fn' a0 a1.
Proof. exact (@lem1071928 A Z list' (term3 A) a0 a1 fn fn' NIL' h1 h2). Qed.
Lemma lem1071930 {A Z : Type'} (list' : type1338 A) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (NIL' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NIL' = (term1 A)) : term34 A Z list' NIL' fn fn' a0 a1.
Proof. exact (@lem1071929 A Z list' a0 a1 fn fn' NIL' h1 h2 (@lem1071927 A)). Qed.
Lemma lem1071931 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem1071932 {A Z : Type'} (list' : type1338 A) (NIL' : recspace A) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term35 A Z list' NIL' fn fn' a0 a1.
Proof. exact (fun h0 : NIL' = (term1 A) => @lem1071930 A Z list' a0 a1 fn fn' NIL' h1 h0). Qed.
Lemma lem1071933 {A Z : Type'} (list' : type1338 A) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term36 A Z list' fn fn' a0 a1.
Proof. exact (@lem1071932 A Z list' (term1 A) a0 a1 fn fn' h1). Qed.
Lemma lem1071934 {A Z : Type'} (list' : type1338 A) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term37 A Z list' fn fn' a0 a1.
Proof. exact (@lem1071933 A Z list' a0 a1 fn fn' h1 (@lem1071931 A)). Qed.
Lemma lem1071935 {A : Type'} (list' : type1338 A) (h1 : list' = (term38 A)) : list' = (term38 A).
Proof. exact (h1). Qed.
Lemma lem1071936 {A Z : Type'} (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (list' : type1338 A) (h1 : fn = (term0 A Z fn')) (h2 : list' = (term38 A)) : term30 A Z fn fn' a0 a1.
Proof. exact (@lem1071934 A Z list' a0 a1 fn fn' h1 (@lem1071935 A list' h2)). Qed.
Lemma lem1071937 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (eq_refl (term38 A)). Qed.
Lemma lem1071938 {A Z : Type'} (list' : type1338 A) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term37 A Z list' fn fn' a0 a1.
Proof. exact (fun h0 : list' = (term38 A) => @lem1071936 A Z a0 a1 fn fn' list' h1 h0). Qed.
Lemma lem1071939 {A Z : Type'} (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term39 A Z fn fn' a0 a1.
Proof. exact (@lem1071938 A Z (term38 A) a0 a1 fn fn' h1). Qed.
Lemma lem1071940 {A Z : Type'} (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term30 A Z fn fn' a0 a1.
Proof. exact (@lem1071939 A Z a0 a1 fn fn' h1 (@lem1071937 A)). Qed.
Lemma lem1071942 {A Z : Type'} : term40 A Z.
Proof. exact (@lem1065430 A Z). Qed.
Lemma lem1071943 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term41 A Z NIL' CONS'.
Proof. exact (@lem1071942 A Z (term42 A Z NIL' CONS')). Qed.
Lemma lem1071944 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term41 A Z NIL' CONS') = (term43 A Z NIL' CONS').
Proof. exact (eq_refl (term41 A Z NIL' CONS')). Qed.
Lemma lem1071945 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term43 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1071944 A Z NIL' CONS') (@lem1071943 A Z NIL' CONS')). Qed.
Lemma lem1071946 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term44 A Z NIL' CONS' fn.
Proof. exact (h1). Qed.
Lemma lem1071947 {A Z : Type'} (c : nat) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term45 A Z NIL' CONS' fn c.
Proof. exact (@lem1071946 A Z NIL' CONS' fn h1 c). Qed.
Lemma lem1071948 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (c : nat) (fn : type1337 A Z) : (term45 A Z NIL' CONS' fn c) = (term46 A Z NIL' CONS' c fn).
Proof. exact (eq_refl (term45 A Z NIL' CONS' fn c)). Qed.
Lemma lem1071949 {A Z : Type'} (c : nat) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term46 A Z NIL' CONS' c fn.
Proof. exact (EQ_MP (@lem1071948 A Z NIL' CONS' c fn) (@lem1071947 A Z c NIL' CONS' fn h1)). Qed.
Lemma lem1071950 {A Z : Type'} (c : nat) (i : A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term47 A Z NIL' CONS' c fn i.
Proof. exact (@lem1071949 A Z c NIL' CONS' fn h1 i). Qed.
Lemma lem1071951 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (c : nat) (i : A) (fn : type1337 A Z) : (term47 A Z NIL' CONS' c fn i) = (term48 A Z NIL' CONS' c i fn).
Proof. exact (eq_refl (term47 A Z NIL' CONS' c fn i)). Qed.
Lemma lem1071952 {A Z : Type'} (c : nat) (i : A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term48 A Z NIL' CONS' c i fn.
Proof. exact (EQ_MP (@lem1071951 A Z NIL' CONS' c i fn) (@lem1071950 A Z c i NIL' CONS' fn h1)). Qed.
Lemma lem1071953 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term49 A Z NIL' CONS' c i fn r.
Proof. exact (@lem1071952 A Z c i NIL' CONS' fn h1 r). Qed.
Lemma lem1071954 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (c : nat) (i : A) (fn : type1337 A Z) (r : type1614 A) : (term49 A Z NIL' CONS' c i fn r) = ((term50 A Z fn c i r) = (term51 A Z NIL' CONS' c i fn r)).
Proof. exact (eq_refl (term49 A Z NIL' CONS' c i fn r)). Qed.
Lemma lem1071956 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : fn = (term0 A Z fn').
Proof. exact (h1). Qed.
Lemma lem1071957 {A : Type'} (a : list A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1071958 {A Z : Type'} (a : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (fn a) = (term52 A Z fn' a).
Proof. exact (MK_COMB (@lem1071956 A Z fn fn' h1) (@lem1071957 A a)). Qed.
Lemma lem1071959 {A Z : Type'} (fn : type1337 A Z) (a : list A) : (term52 A Z fn a) = (term53 A Z fn a).
Proof. exact (eq_refl (term52 A Z fn a)). Qed.
Lemma lem1071960 {A Z : Type'} (fn : type1142 A Z) (a : list A) : (term54 A Z fn a) = (term54 A Z fn a).
Proof. exact (eq_refl (term54 A Z fn a)). Qed.
Lemma lem1071961 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (a : list A) : ((fn a) = (term52 A Z fn' a)) = ((fn a) = (term53 A Z fn' a)).
Proof. exact (MK_COMB (@lem1071960 A Z fn a) (@lem1071959 A Z fn' a)). Qed.
Lemma lem1071962 {A Z : Type'} (a : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (fn a) = (term53 A Z fn' a).
Proof. exact (EQ_MP (@lem1071961 A Z fn fn' a) (@lem1071958 A Z a fn fn' h1)). Qed.
Lemma lem1071964 {A B : Type'} (f : A -> B) : term55 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1071965 {A B : Type'} (f : A -> B) : (term55 A B f) = (term56 A B f).
Proof. exact (eq_refl (term55 A B f)). Qed.
Lemma lem1071966 {A B : Type'} (f : A -> B) : term56 A B f.
Proof. exact (EQ_MP (@lem1071965 A B f) (@lem1071964 A B f)). Qed.
Lemma lem1071967 {A B : Type'} (f : A -> B) (y : A) : term57 A B f y.
Proof. exact (@lem1071966 A B f y). Qed.
Lemma lem1071968 {A B : Type'} (f : A -> B) (y : A) : (term57 A B f y) = ((term58 A B f y) = (f y)).
Proof. exact (eq_refl (term57 A B f y)). Qed.
Lemma lem1071980 {A : Type'} : term59 A.
Proof. exact (proj1 (@lem1066089 A)). Qed.
Lemma lem1071981 {A : Type'} (a : A) : term60 A a.
Proof. exact (@lem1071980 A a). Qed.
Lemma lem1071982 {A : Type'} (a : A) : (term60 A a) = (term61 A a).
Proof. exact (eq_refl (term60 A a)). Qed.
Lemma lem1071983 {A : Type'} (a : A) : term61 A a.
Proof. exact (EQ_MP (@lem1071982 A a) (@lem1071981 A a)). Qed.
Lemma lem1071984 {A : Type'} (a : A) (f : nat -> A) : term62 A a f.
Proof. exact (@lem1071983 A a f). Qed.
Lemma lem1071985 {A : Type'} (f : nat -> A) (a : A) : (term62 A a f) = ((term63 A a f) = a).
Proof. exact (eq_refl (term62 A a f)). Qed.
Lemma lem1071999 {A Z : Type'} (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term29 A Z fn' a0 a1).
Proof. exact (proj2 (@lem1071940 A Z a0 a1 fn fn' h1)). Qed.
Lemma lem1072000 {A Z : Type'} (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (fn (@nil A)) = (term22 A Z fn').
Proof. exact (proj1 (@lem1071940 A Z (@el A) (@el (list A)) fn fn' h1)). Qed.
Lemma lem1072002 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : (term50 A Z fn c i r) = (term51 A Z NIL' CONS' c i fn r).
Proof. exact (EQ_MP (@lem1071954 A Z NIL' CONS' c i fn r) (@lem1071953 A Z c i r NIL' CONS' fn h1)). Qed.
Lemma lem1072003 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : (term50 A Z fn c i r) = (term51 A Z NIL' CONS' c i fn r).
Proof. exact (@lem1072002 A Z c i r NIL' CONS' fn h1). Qed.
Lemma lem1072004 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : (term22 A Z fn) = (term64 A Z NIL' CONS' fn).
Proof. exact (@lem1072003 A Z (NUMERAL 0) (term65 A) (term66 A) NIL' CONS' fn h1). Qed.
Lemma lem1072005 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (fn (@nil A)) = (term64 A Z NIL' CONS' fn').
Proof. exact (TRANS (@lem1072000 A Z fn fn' h2) (@lem1072004 A Z NIL' CONS' fn' h1)). Qed.
Lemma lem1072007 {A : Type'} (f : nat -> A) (a : A) : (term63 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem1072008 {A Z : Type'} (f : type1592 A Z) (a : type1379 A Z) : (term67 A Z a f) = a.
Proof. exact (@lem1072007 (type1379 A Z) f a). Qed.
Lemma lem1072011 {A Z : Type'} (CONS' : type1394 A Z) (NIL' : Z) : (term68 A Z NIL' CONS') = (term69 A Z NIL').
Proof. exact (@lem1072008 A Z (term70 A Z CONS') (term69 A Z NIL')). Qed.
Lemma lem1072012 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (eq_refl (term65 A)). Qed.
Lemma lem1072013 {A Z : Type'} (CONS' : type1394 A Z) (NIL' : Z) : (term71 A Z NIL' CONS') = (term72 A Z NIL').
Proof. exact (MK_COMB (@lem1072011 A Z CONS' NIL') (@lem1072012 A)). Qed.
Lemma lem1072014 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (eq_refl (term66 A)). Qed.
Lemma lem1072015 {A Z : Type'} (CONS' : type1394 A Z) (NIL' : Z) : (term73 A Z NIL' CONS') = (term74 A Z NIL').
Proof. exact (MK_COMB (@lem1072013 A Z CONS' NIL') (@lem1072014 A)). Qed.
Lemma lem1072016 {A Z : Type'} (fn : type1337 A Z) : (term75 A Z fn) = (term75 A Z fn).
Proof. exact (eq_refl (term75 A Z fn)). Qed.
Lemma lem1072017 {A Z : Type'} (CONS' : type1394 A Z) (NIL' : Z) (fn : type1337 A Z) : (term64 A Z NIL' CONS' fn) = (term76 A Z NIL' fn).
Proof. exact (MK_COMB (@lem1072015 A Z CONS' NIL') (@lem1072016 A Z fn)). Qed.
Lemma lem1072018 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (fn (@nil A)) = (term76 A Z NIL' fn').
Proof. exact (TRANS (@lem1072005 A Z NIL' CONS' fn fn' h1 h2) (@lem1072017 A Z CONS' NIL' fn')). Qed.
Lemma lem1072019 {A Z : Type'} (NIL' : Z) : (term72 A Z NIL') = (term77 A Z NIL').
Proof. exact (eq_refl (term72 A Z NIL')). Qed.
Lemma lem1072020 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (eq_refl (term66 A)). Qed.
Lemma lem1072021 {A Z : Type'} (NIL' : Z) : (term74 A Z NIL') = (term78 A Z NIL').
Proof. exact (MK_COMB (@lem1072019 A Z NIL') (@lem1072020 A)). Qed.
Lemma lem1072022 {A Z : Type'} (fn : type1337 A Z) : (term75 A Z fn) = (term75 A Z fn).
Proof. exact (eq_refl (term75 A Z fn)). Qed.
Lemma lem1072023 {A Z : Type'} (NIL' : Z) (fn : type1337 A Z) : (term76 A Z NIL' fn) = (term79 A Z NIL' fn).
Proof. exact (MK_COMB (@lem1072021 A Z NIL') (@lem1072022 A Z fn)). Qed.
Lemma lem1072024 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (fn (@nil A)) = (term79 A Z NIL' fn').
Proof. exact (TRANS (@lem1072018 A Z NIL' CONS' fn fn' h1 h2) (@lem1072023 A Z NIL' fn')). Qed.
Lemma lem1072025 {A Z : Type'} (NIL' : Z) : (term78 A Z NIL') = (term80 Z NIL').
Proof. exact (eq_refl (term78 A Z NIL')). Qed.
Lemma lem1072026 {A Z : Type'} (fn : type1337 A Z) : (term75 A Z fn) = (term75 A Z fn).
Proof. exact (eq_refl (term75 A Z fn)). Qed.
Lemma lem1072027 {A Z : Type'} (NIL' : Z) (fn : type1337 A Z) : (term79 A Z NIL' fn) = (term81 A Z NIL' fn).
Proof. exact (MK_COMB (@lem1072025 A Z NIL') (@lem1072026 A Z fn)). Qed.
Lemma lem1072028 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (fn (@nil A)) = (term81 A Z NIL' fn').
Proof. exact (TRANS (@lem1072024 A Z NIL' CONS' fn fn' h1 h2) (@lem1072027 A Z NIL' fn')). Qed.
Lemma lem1072029 {A Z : Type'} (fn : type1337 A Z) (NIL' : Z) : (term81 A Z NIL' fn) = NIL'.
Proof. exact (eq_refl (term81 A Z NIL' fn)). Qed.
Lemma lem1072032 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (fn (@nil A)) = NIL'.
Proof. exact (TRANS (@lem1072028 A Z NIL' CONS' fn fn' h1 h2) (@lem1072029 A Z fn' NIL')). Qed.
Lemma lem1072034 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : (term50 A Z fn c i r) = (term51 A Z NIL' CONS' c i fn r).
Proof. exact (EQ_MP (@lem1071954 A Z NIL' CONS' c i fn r) (@lem1071953 A Z c i r NIL' CONS' fn h1)). Qed.
Lemma lem1072035 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : (term50 A Z fn c i r) = (term51 A Z NIL' CONS' c i fn r).
Proof. exact (@lem1072034 A Z c i r NIL' CONS' fn h1). Qed.
Lemma lem1072036 {A Z : Type'} (a0 : A) (a1 : list A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : (term29 A Z fn a0 a1) = (term82 A Z NIL' CONS' a0 fn a1).
Proof. exact (@lem1072035 A Z term83 a0 (term84 A a1) NIL' CONS' fn h1). Qed.
Lemma lem1072037 {A Z : Type'} (a0 : A) (a1 : list A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term82 A Z NIL' CONS' a0 fn' a1).
Proof. exact (TRANS (@lem1071999 A Z a0 a1 fn fn' h2) (@lem1072036 A Z a0 a1 NIL' CONS' fn' h1)). Qed.
Lemma lem1072039 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term85 A a f n) = (f n).
Proof. exact (EQ_MP (@lem1066562 A a f n) (@lem1066561 A a f n)). Qed.
Lemma lem1072040 {A Z : Type'} (a : type1379 A Z) (f : type1592 A Z) (n : nat) : (term86 A Z a f n) = (f n).
Proof. exact (@lem1072039 (type1379 A Z) a f n). Qed.
Lemma lem1072041 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term87 A Z NIL' CONS') = (term88 A Z CONS').
Proof. exact (@lem1072040 A Z (term69 A Z NIL') (term70 A Z CONS') (NUMERAL 0)). Qed.
Lemma lem1072043 {A : Type'} (f : nat -> A) (a : A) : (term63 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem1072044 {A Z : Type'} (f : type1592 A Z) (a : type1379 A Z) : (term67 A Z a f) = a.
Proof. exact (@lem1072043 (type1379 A Z) f a). Qed.
Lemma lem1072047 {A Z : Type'} (CONS' : type1394 A Z) : (term88 A Z CONS') = (term89 A Z CONS').
Proof. exact (@lem1072044 A Z (@FNIL (A -> (nat -> recspace A) -> (nat -> Z) -> Z)) (term89 A Z CONS')). Qed.
Lemma lem1072048 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term87 A Z NIL' CONS') = (term89 A Z CONS').
Proof. exact (TRANS (@lem1072041 A Z NIL' CONS') (@lem1072047 A Z CONS')). Qed.
Lemma lem1072049 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem1072050 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (a0 : A) : (term90 A Z NIL' CONS' a0) = (term91 A Z CONS' a0).
Proof. exact (MK_COMB (@lem1072048 A Z NIL' CONS') (@lem1072049 A a0)). Qed.
Lemma lem1072051 {A : Type'} (a1 : list A) : (term84 A a1) = (term84 A a1).
Proof. exact (eq_refl (term84 A a1)). Qed.
Lemma lem1072052 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (a0 : A) (a1 : list A) : (term92 A Z NIL' CONS' a0 a1) = (term93 A Z CONS' a0 a1).
Proof. exact (MK_COMB (@lem1072050 A Z NIL' CONS' a0) (@lem1072051 A a1)). Qed.
Lemma lem1072053 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term94 A Z fn a1) = (term94 A Z fn a1).
Proof. exact (eq_refl (term94 A Z fn a1)). Qed.
Lemma lem1072054 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (a0 : A) (fn : type1337 A Z) (a1 : list A) : (term82 A Z NIL' CONS' a0 fn a1) = (term95 A Z CONS' a0 fn a1).
Proof. exact (MK_COMB (@lem1072052 A Z NIL' CONS' a0 a1) (@lem1072053 A Z fn a1)). Qed.
Lemma lem1072055 {A Z : Type'} (a0 : A) (a1 : list A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term95 A Z CONS' a0 fn' a1).
Proof. exact (TRANS (@lem1072037 A Z a0 a1 NIL' CONS' fn fn' h1 h2) (@lem1072054 A Z NIL' CONS' a0 fn' a1)). Qed.
Lemma lem1072056 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) : (term91 A Z CONS' a0) = (term96 A Z CONS' a0).
Proof. exact (eq_refl (term91 A Z CONS' a0)). Qed.
Lemma lem1072057 {A : Type'} (a1 : list A) : (term84 A a1) = (term84 A a1).
Proof. exact (eq_refl (term84 A a1)). Qed.
Lemma lem1072058 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (a1 : list A) : (term93 A Z CONS' a0 a1) = (term97 A Z CONS' a0 a1).
Proof. exact (MK_COMB (@lem1072056 A Z CONS' a0) (@lem1072057 A a1)). Qed.
Lemma lem1072059 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term94 A Z fn a1) = (term94 A Z fn a1).
Proof. exact (eq_refl (term94 A Z fn a1)). Qed.
Lemma lem1072060 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (fn : type1337 A Z) (a1 : list A) : (term95 A Z CONS' a0 fn a1) = (term98 A Z CONS' a0 fn a1).
Proof. exact (MK_COMB (@lem1072058 A Z CONS' a0 a1) (@lem1072059 A Z fn a1)). Qed.
Lemma lem1072061 {A Z : Type'} (a0 : A) (a1 : list A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term98 A Z CONS' a0 fn' a1).
Proof. exact (TRANS (@lem1072055 A Z a0 a1 NIL' CONS' fn fn' h1 h2) (@lem1072060 A Z CONS' a0 fn' a1)). Qed.
Lemma lem1072062 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (a1 : list A) : (term97 A Z CONS' a0 a1) = (term99 A Z CONS' a0 a1).
Proof. exact (eq_refl (term97 A Z CONS' a0 a1)). Qed.
Lemma lem1072063 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term94 A Z fn a1) = (term94 A Z fn a1).
Proof. exact (eq_refl (term94 A Z fn a1)). Qed.
Lemma lem1072064 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (fn : type1337 A Z) (a1 : list A) : (term98 A Z CONS' a0 fn a1) = (term100 A Z CONS' a0 fn a1).
Proof. exact (MK_COMB (@lem1072062 A Z CONS' a0 a1) (@lem1072063 A Z fn a1)). Qed.
Lemma lem1072065 {A Z : Type'} (a0 : A) (a1 : list A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term100 A Z CONS' a0 fn' a1).
Proof. exact (TRANS (@lem1072061 A Z a0 a1 NIL' CONS' fn fn' h1 h2) (@lem1072064 A Z CONS' a0 fn' a1)). Qed.
Lemma lem1072066 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (fn : type1337 A Z) (a1 : list A) : (term100 A Z CONS' a0 fn a1) = (term101 A Z CONS' a0 fn a1).
Proof. exact (eq_refl (term100 A Z CONS' a0 fn a1)). Qed.
Lemma lem1072067 {A Z : Type'} (a0 : A) (a1 : list A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term101 A Z CONS' a0 fn' a1).
Proof. exact (TRANS (@lem1072065 A Z a0 a1 NIL' CONS' fn fn' h1 h2) (@lem1072066 A Z CONS' a0 fn' a1)). Qed.
Lemma lem1072069 {A : Type'} (f : nat -> A) (a : A) : (term63 A a f) = a.
Proof. exact (EQ_MP (@lem1071985 A f a) (@lem1071984 A a f)). Qed.
Lemma lem1072070 {A : Type'} (f : type1614 A) (a : recspace A) : (term102 A a f) = a.
Proof. exact (@lem1072069 (recspace A) f a). Qed.
Lemma lem1072071 {A : Type'} (a1 : list A) : (term103 A a1) = (@_dest_list A a1).
Proof. exact (@lem1072070 A (term66 A) (@_dest_list A a1)). Qed.
Lemma lem1072072 {A : Type'} : (@_mk_list A) = (@_mk_list A).
Proof. exact (eq_refl (@_mk_list A)). Qed.
Lemma lem1072073 {A : Type'} (a1 : list A) : (term104 A a1) = (term105 A a1).
Proof. exact (MK_COMB (@lem1072072 A) (@lem1072071 A a1)). Qed.
Lemma lem1072075 {A : Type'} (a : list A) : (term105 A a) = a.
Proof. exact (@axiom_15 A a). Qed.
Lemma lem1072076 {A : Type'} (a : list A) : (term105 A a) = a.
Proof. exact (@lem1072075 A a). Qed.
Lemma lem1072077 {A : Type'} (a1 : list A) : (term105 A a1) = a1.
Proof. exact (@lem1072076 A a1). Qed.
Lemma lem1072078 {A : Type'} (a1 : list A) : (term104 A a1) = a1.
Proof. exact (TRANS (@lem1072073 A a1) (@lem1072077 A a1)). Qed.
Lemma lem1072079 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) : (CONS' a0) = (CONS' a0).
Proof. exact (eq_refl (CONS' a0)). Qed.
Lemma lem1072080 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (a1 : list A) : (term106 A Z CONS' a0 a1) = (CONS' a0 a1).
Proof. exact (MK_COMB (@lem1072079 A Z CONS' a0) (@lem1072078 A a1)). Qed.
Lemma lem1072082 {A B : Type'} (f : A -> B) (y : A) : (term58 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1071968 A B f y) (@lem1071967 A B f y)). Qed.
Lemma lem1072083 {Z : Type'} (f : nat -> Z) (y : nat) : (term107 Z f y) = (f y).
Proof. exact (@lem1072082 nat Z f y). Qed.
Lemma lem1072084 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term108 A Z fn a1) = (term109 A Z fn a1).
Proof. exact (@lem1072083 Z (term94 A Z fn a1) (NUMERAL 0)). Qed.
Lemma lem1072085 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) (n : nat) : (term110 A Z fn a1 n) = (term111 A Z fn a1 n).
Proof. exact (eq_refl (term110 A Z fn a1 n)). Qed.
Lemma lem1072086 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term112 A Z fn a1) = (term94 A Z fn a1).
Proof. exact (fun_ext (fun n : nat => @lem1072085 A Z fn a1 n)). Qed.
Lemma lem1072087 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1072088 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term108 A Z fn a1) = (term109 A Z fn a1).
Proof. exact (MK_COMB (@lem1072086 A Z fn a1) (@lem1072087)). Qed.
Lemma lem1072089 {Z : Type'} : (@eq Z) = (@eq Z).
Proof. exact (eq_refl (@eq Z)). Qed.
Lemma lem1072090 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term113 A Z fn a1) = (term114 A Z fn a1).
Proof. exact (MK_COMB (@lem1072089 Z) (@lem1072088 A Z fn a1)). Qed.
Lemma lem1072091 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term109 A Z fn a1) = (term115 A Z fn a1).
Proof. exact (eq_refl (term109 A Z fn a1)). Qed.
Lemma lem1072092 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : ((term108 A Z fn a1) = (term109 A Z fn a1)) = ((term109 A Z fn a1) = (term115 A Z fn a1)).
Proof. exact (MK_COMB (@lem1072090 A Z fn a1) (@lem1072091 A Z fn a1)). Qed.
Lemma lem1072093 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term109 A Z fn a1) = (term115 A Z fn a1).
Proof. exact (EQ_MP (@lem1072092 A Z fn a1) (@lem1072084 A Z fn a1)). Qed.
Lemma lem1072095 {A : Type'} (f : nat -> A) (a : A) : (term63 A a f) = a.
Proof. exact (EQ_MP (@lem1071985 A f a) (@lem1071984 A a f)). Qed.
Lemma lem1072096 {A : Type'} (f : type1614 A) (a : recspace A) : (term102 A a f) = a.
Proof. exact (@lem1072095 (recspace A) f a). Qed.
Lemma lem1072097 {A : Type'} (a1 : list A) : (term103 A a1) = (@_dest_list A a1).
Proof. exact (@lem1072096 A (term66 A) (@_dest_list A a1)). Qed.
Lemma lem1072098 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1072099 {A Z : Type'} (fn : type1337 A Z) (a1 : list A) : (term115 A Z fn a1) = (term53 A Z fn a1).
Proof. exact (MK_COMB (@lem1072098 A Z fn) (@lem1072097 A a1)). Qed.
Lemma lem1072101 {A Z : Type'} (a : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term53 A Z fn' a) = (fn a).
Proof. exact (SYM (@lem1071962 A Z a fn fn' h1)). Qed.
Lemma lem1072102 {A Z : Type'} (a : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term53 A Z fn' a) = (fn a).
Proof. exact (@lem1072101 A Z a fn fn' h1). Qed.
Lemma lem1072103 {A Z : Type'} (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term53 A Z fn' a1) = (fn a1).
Proof. exact (@lem1072102 A Z a1 fn fn' h1). Qed.
Lemma lem1072104 {A Z : Type'} (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term115 A Z fn' a1) = (fn a1).
Proof. exact (TRANS (@lem1072099 A Z fn' a1) (@lem1072103 A Z a1 fn fn' h1)). Qed.
Lemma lem1072105 {A Z : Type'} (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term109 A Z fn' a1) = (fn a1).
Proof. exact (TRANS (@lem1072093 A Z fn' a1) (@lem1072104 A Z a1 fn fn' h1)). Qed.
Lemma lem1072106 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term101 A Z CONS' a0 fn' a1) = (term116 A Z CONS' a0 fn a1).
Proof. exact (MK_COMB (@lem1072080 A Z CONS' a0 a1) (@lem1072105 A Z a1 fn fn' h1)). Qed.
Lemma lem1072107 {A Z : Type'} (fn : type1142 A Z) (a0 : A) (a1 : list A) : (term117 A Z fn a0 a1) = (term117 A Z fn a0 a1).
Proof. exact (eq_refl (term117 A Z fn a0 a1)). Qed.
Lemma lem1072108 {A Z : Type'} (CONS' : type1394 A Z) (a0 : A) (a1 : list A) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : ((term4 A Z fn a0 a1) = (term101 A Z CONS' a0 fn' a1)) = ((term4 A Z fn a0 a1) = (term116 A Z CONS' a0 fn a1)).
Proof. exact (MK_COMB (@lem1072107 A Z fn a0 a1) (@lem1072106 A Z CONS' a0 a1 fn fn' h1)). Qed.
Lemma lem1072109 {A Z : Type'} (a0 : A) (a1 : list A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a0 a1) = (term116 A Z CONS' a0 fn a1).
Proof. exact (EQ_MP (@lem1072108 A Z CONS' a0 a1 fn fn' h2) (@lem1072067 A Z a0 a1 NIL' CONS' fn fn' h1 h2)). Qed.
Lemma lem1072110 {A Z : Type'} (a0 : A) (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : term118 A Z CONS' a0 fn.
Proof. exact (fun a1 : list A => @lem1072109 A Z a0 a1 NIL' CONS' fn fn' h1 h2). Qed.
Lemma lem1072111 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : term119 A Z CONS' fn.
Proof. exact (fun a0 : A => @lem1072110 A Z a0 NIL' CONS' fn fn' h1 h2). Qed.
Lemma lem1072112 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : term120 A Z NIL' CONS' fn.
Proof. exact (conj (@lem1072032 A Z NIL' CONS' fn fn' h1 h2) (@lem1072111 A Z NIL' CONS' fn fn' h1 h2)). Qed.
Lemma lem1072113 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) : (term121 A Z NIL' CONS' fn) = (term120 A Z NIL' CONS' fn).
Proof. exact (eq_refl (term121 A Z NIL' CONS' fn)). Qed.
Lemma lem1072114 {A Z : Type'} : term122 A Z.
Proof. exact (@lem9102 (type1142 A Z)). Qed.
Lemma lem1072115 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term123 A Z NIL' CONS'.
Proof. exact (@lem1072114 A Z (term124 A Z NIL' CONS')). Qed.
Lemma lem1072116 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term123 A Z NIL' CONS') = (term125 A Z NIL' CONS').
Proof. exact (eq_refl (term123 A Z NIL' CONS')). Qed.
Lemma lem1072117 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term125 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1072116 A Z NIL' CONS') (@lem1072115 A Z NIL' CONS')). Qed.
Lemma lem1072118 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) : term126 A Z NIL' CONS' fn.
Proof. exact (@lem1072117 A Z NIL' CONS' (term0 A Z fn)). Qed.
Lemma lem1072119 {A Z : Type'} (fn : type1337 A Z) (NIL' : Z) (CONS' : type1394 A Z) : (term126 A Z NIL' CONS' fn) = (term127 A Z fn NIL' CONS').
Proof. exact (eq_refl (term126 A Z NIL' CONS' fn)). Qed.
Lemma lem1072120 {A Z : Type'} (fn : type1337 A Z) (NIL' : Z) (CONS' : type1394 A Z) : term127 A Z fn NIL' CONS'.
Proof. exact (EQ_MP (@lem1072119 A Z fn NIL' CONS') (@lem1072118 A Z NIL' CONS' fn)). Qed.
Lemma lem1072121 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) : (term120 A Z NIL' CONS' fn) = (term121 A Z NIL' CONS' fn).
Proof. exact (SYM (@lem1072113 A Z NIL' CONS' fn)). Qed.
Lemma lem1072122 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1142 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') (h2 : fn = (term0 A Z fn')) : term121 A Z NIL' CONS' fn.
Proof. exact (EQ_MP (@lem1072121 A Z NIL' CONS' fn) (@lem1072112 A Z NIL' CONS' fn fn' h1 h2)). Qed.
Lemma lem1072123 {A Z : Type'} (fn : type1142 A Z) (NIL' : Z) (CONS' : type1394 A Z) (fn' : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn') : term128 A Z fn' NIL' CONS' fn.
Proof. exact (fun h0 : fn = (term0 A Z fn') => @lem1072122 A Z NIL' CONS' fn fn' h1 h0). Qed.
Lemma lem1072124 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term129 A Z fn NIL' CONS'.
Proof. exact (fun fn' : type1142 A Z => @lem1072123 A Z fn' NIL' CONS' fn h1). Qed.
Lemma lem1072125 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) (fn : type1337 A Z) (h1 : term44 A Z NIL' CONS' fn) : term130 A Z NIL' CONS'.
Proof. exact (@lem1072120 A Z fn NIL' CONS' (@lem1072124 A Z NIL' CONS' fn h1)). Qed.
Lemma lem1072126 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term130 A Z NIL' CONS'.
Proof. exact (ex_elim (@lem1071945 A Z NIL' CONS') (fun fn : type1337 A Z => fun h0 : term131 A Z NIL' CONS' fn => @lem1072125 A Z NIL' CONS' fn h0)). Qed.
Lemma lem1072127 {A Z : Type'} (NIL' : Z) : term132 A Z NIL'.
Proof. exact (fun CONS' : type1394 A Z => @lem1072126 A Z NIL' CONS'). Qed.
Lemma lem1072128 {A Z : Type'} : term133 A Z.
Proof. exact (fun NIL' : Z => @lem1072127 A Z NIL'). Qed.
