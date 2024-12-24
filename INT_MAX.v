Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1482687_spec.
Require Import thm1483205_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm1988348_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318511_spec.
Require Import thm2318512_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2319813 : term0 = term1.
Proof. exact (@lem2318604 term1). Qed.
Lemma lem2319828 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2319829 (x : int) : (term4 x) = (term5 x).
Proof. exact (@lem2319828 (term6 x)). Qed.
Lemma lem2319830 (y : int) (x : int) : (term7 x y) = ((int_max x y) = (term8 y x)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem2319831 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2319833 (y : int) (x : int) : (term9 x y) = (term10 y x).
Proof. exact (MK_COMB (@lem2319831) (@lem2319830 y x)). Qed.
Lemma lem2319834 (x : int) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : int => @lem2319833 y x)). Qed.
Lemma lem2319835 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319836 (x : int) : (term5 x) = (term13 x).
Proof. exact (MK_COMB (@lem2319835) (@lem2319834 x)). Qed.
Lemma lem2319837 (x : int) : (term4 x) = (term13 x).
Proof. exact (TRANS (@lem2319829 x) (@lem2319836 x)). Qed.
Lemma lem2319838 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2319839 : term14 = term15.
Proof. exact (@lem2319838 term16). Qed.
Lemma lem2319840 (x : int) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem2319841 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2319842 (x : int) : (term19 x) = (term4 x).
Proof. exact (MK_COMB (@lem2319841) (@lem2319840 x)). Qed.
Lemma lem2319843 (x : int) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem2319842 x) (@lem2319837 x)). Qed.
Lemma lem2319844 : term20 = term21.
Proof. exact (fun_ext (fun x : int => @lem2319843 x)). Qed.
Lemma lem2319845 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319846 : term15 = term22.
Proof. exact (MK_COMB (@lem2319845) (@lem2319844)). Qed.
Lemma lem2319848 : term14 = term22.
Proof. exact (TRANS (@lem2319839) (@lem2319846)). Qed.
Lemma lem2319852 (x : int) (y : int) (h1 : (int_le x y) = False) : (int_le x y) = False.
Proof. exact (h1). Qed.
Lemma lem2319853 : (@COND int) = (@COND int).
Proof. exact (eq_refl (@COND int)). Qed.
Lemma lem2319854 (x : int) (y : int) (h1 : (int_le x y) = False) : (term23 x y) = (@COND int False).
Proof. exact (MK_COMB (@lem2319853) (@lem2319852 x y h1)). Qed.
Lemma lem2319855 (y : int) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2319856 (x : int) (y : int) (h1 : (int_le x y) = False) : (term24 x y) = (@COND int False y).
Proof. exact (MK_COMB (@lem2319854 x y h1) (@lem2319855 y)). Qed.
Lemma lem2319857 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2319858 (x : int) (y : int) (h1 : (int_le x y) = False) : (term8 y x) = (@COND int False y x).
Proof. exact (MK_COMB (@lem2319856 x y h1) (@lem2319857 x)). Qed.
Lemma lem2319860 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem2319861 (t1 : int) (t2 : int) : (@COND int False t1 t2) = t2.
Proof. exact (@lem2319860 int t1 t2). Qed.
Lemma lem2319862 (y : int) (x : int) : (@COND int False y x) = x.
Proof. exact (@lem2319861 y x). Qed.
Lemma lem2319863 (x : int) (y : int) (h1 : (int_le x y) = False) : (term8 y x) = x.
Proof. exact (TRANS (@lem2319858 x y h1) (@lem2319862 y x)). Qed.
Lemma lem2319864 (x : int) (y : int) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2319865 (x : int) (y : int) (h1 : (int_le x y) = False) : ((int_max x y) = (term8 y x)) = ((int_max x y) = x).
Proof. exact (MK_COMB (@lem2319864 x y) (@lem2319863 x y h1)). Qed.
Lemma lem2319868 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2319869 (x : int) (y : int) (h1 : (int_le x y) = False) : (term10 y x) = (term26 y x).
Proof. exact (MK_COMB (@lem2319868) (@lem2319865 x y h1)). Qed.
Lemma lem2319870 (y : int) (x : int) : term27 y x.
Proof. exact (fun h0 : (int_le x y) = False => @lem2319869 x y h0). Qed.
Lemma lem2319872 (x : int) (y : int) (h1 : (int_le x y) = True) : (int_le x y) = True.
Proof. exact (h1). Qed.
Lemma lem2319873 : (@COND int) = (@COND int).
Proof. exact (eq_refl (@COND int)). Qed.
Lemma lem2319874 (x : int) (y : int) (h1 : (int_le x y) = True) : (term23 x y) = (@COND int True).
Proof. exact (MK_COMB (@lem2319873) (@lem2319872 x y h1)). Qed.
Lemma lem2319875 (y : int) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2319876 (x : int) (y : int) (h1 : (int_le x y) = True) : (term24 x y) = (@COND int True y).
Proof. exact (MK_COMB (@lem2319874 x y h1) (@lem2319875 y)). Qed.
Lemma lem2319877 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2319878 (x : int) (y : int) (h1 : (int_le x y) = True) : (term8 y x) = (@COND int True y x).
Proof. exact (MK_COMB (@lem2319876 x y h1) (@lem2319877 x)). Qed.
Lemma lem2319880 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem2319881 (t2 : int) (t1 : int) : (@COND int True t1 t2) = t1.
Proof. exact (@lem2319880 int t2 t1). Qed.
Lemma lem2319882 (x : int) (y : int) : (@COND int True y x) = y.
Proof. exact (@lem2319881 x y). Qed.
Lemma lem2319883 (x : int) (y : int) (h1 : (int_le x y) = True) : (term8 y x) = y.
Proof. exact (TRANS (@lem2319878 x y h1) (@lem2319882 x y)). Qed.
Lemma lem2319884 (x : int) (y : int) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2319885 (x : int) (y : int) (h1 : (int_le x y) = True) : ((int_max x y) = (term8 y x)) = ((int_max x y) = y).
Proof. exact (MK_COMB (@lem2319884 x y) (@lem2319883 x y h1)). Qed.
Lemma lem2319888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2319889 (x : int) (y : int) (h1 : (int_le x y) = True) : (term10 y x) = (term28 x y).
Proof. exact (MK_COMB (@lem2319888) (@lem2319885 x y h1)). Qed.
Lemma lem2319890 (x : int) (y : int) : term29 x y.
Proof. exact (fun h0 : (int_le x y) = True => @lem2319889 x y h0). Qed.
Lemma lem2319891 (x : int) (y : int) : term30 x y.
Proof. exact (conj (@lem2319870 y x) (@lem2319890 x y)). Qed.
Lemma lem2319893 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term31 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem2319894 (y : int) (x : int) : term32 y x.
Proof. exact (@lem2319893 (term10 y x) (term28 x y) (int_le x y) (term26 y x)). Qed.
Lemma lem2319931 (y : int) (x : int) : (term10 y x) = (term33 y x).
Proof. exact (@lem2319894 y x (@lem2319891 x y)). Qed.
Lemma lem2319932 (x : int) : (term12 x) = (term34 x).
Proof. exact (fun_ext (fun y : int => @lem2319931 y x)). Qed.
Lemma lem2319933 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319934 (x : int) : (term13 x) = (term35 x).
Proof. exact (MK_COMB (@lem2319933) (@lem2319932 x)). Qed.
Lemma lem2319935 : term21 = term36.
Proof. exact (fun_ext (fun x : int => @lem2319934 x)). Qed.
Lemma lem2319936 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319937 : term22 = term37.
Proof. exact (MK_COMB (@lem2319936) (@lem2319935)). Qed.
Lemma lem2319938 : term14 = term37.
Proof. exact (TRANS (@lem2319848) (@lem2319937)). Qed.
Lemma lem2319942 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2319944 (y : int) (x : int) : (term39 x y) = (term40 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2319945 (x : int) (y : int) : (term28 x y) = (term41 x y).
Proof. exact (@lem2319944 y (int_max x y)). Qed.
Lemma lem2319947 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2319948 (x : int) (y : int) : (term42 x y) = (term43 x y).
Proof. exact (@lem2319947 (term44 x y) y). Qed.
Lemma lem2319950 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2319951 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (@lem2319950 (int_max x y) term49). Qed.
Lemma lem2319953 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem2319954 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319955 (x : int) (y : int) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem2319954) (@lem2319953 x y)). Qed.
Lemma lem2319957 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2319958 : term55 = term56.
Proof. exact (@lem2319957 term57). Qed.
Lemma lem2319959 (x : int) (y : int) : (term48 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem2319955 x y) (@lem2319958)). Qed.
Lemma lem2319960 (x : int) (y : int) : (term47 x y) = (term58 x y).
Proof. exact (TRANS (@lem2319951 x y) (@lem2319959 x y)). Qed.
Lemma lem2319961 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2319962 (x : int) (y : int) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem2319961) (@lem2319960 x y)). Qed.
Lemma lem2319963 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2319964 (x : int) (y : int) : (term43 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem2319962 x y) (@lem2319963 y)). Qed.
Lemma lem2319965 (x : int) (y : int) : (term42 x y) = (term61 x y).
Proof. exact (TRANS (@lem2319948 x y) (@lem2319964 x y)). Qed.
Lemma lem2319966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2319967 (x : int) (y : int) : (term62 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem2319966) (@lem2319965 x y)). Qed.
Lemma lem2319969 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2319970 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (@lem2319969 (term66 y) (int_max x y)). Qed.
Lemma lem2319972 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2319973 (y : int) : (term67 y) = (term68 y).
Proof. exact (@lem2319972 y term49). Qed.
Lemma lem2319975 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2319976 : term55 = term56.
Proof. exact (@lem2319975 term57). Qed.
Lemma lem2319977 (y : int) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem2319978 (y : int) : (term68 y) = (term70 y).
Proof. exact (MK_COMB (@lem2319977 y) (@lem2319976)). Qed.
Lemma lem2319979 (y : int) : (term67 y) = (term70 y).
Proof. exact (TRANS (@lem2319973 y) (@lem2319978 y)). Qed.
Lemma lem2319980 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2319981 (y : int) : (term71 y) = (term72 y).
Proof. exact (MK_COMB (@lem2319980) (@lem2319979 y)). Qed.
Lemma lem2319983 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem2319984 (x : int) (y : int) : (term65 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem2319981 y) (@lem2319983 x y)). Qed.
Lemma lem2319985 (x : int) (y : int) : (term64 x y) = (term73 x y).
Proof. exact (TRANS (@lem2319970 x y) (@lem2319984 x y)). Qed.
Lemma lem2319986 (x : int) (y : int) : (term41 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem2319967 x y) (@lem2319985 x y)). Qed.
Lemma lem2319987 (x : int) (y : int) : (term28 x y) = (term74 x y).
Proof. exact (TRANS (@lem2319945 x y) (@lem2319986 x y)). Qed.
Lemma lem2319988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2319989 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem2319988) (@lem2319942 x y)). Qed.
Lemma lem2319990 (x : int) (y : int) : (term77 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem2319989 x y) (@lem2319987 x y)). Qed.
Lemma lem2319992 (y : int) (x : int) : (term79 x y) = (term80 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2319994 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2319995 (y : int) (x : int) : (term80 y x) = (term81 y x).
Proof. exact (@lem2319994 (term66 y) x). Qed.
Lemma lem2319997 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2319998 (y : int) : (term67 y) = (term68 y).
Proof. exact (@lem2319997 y term49). Qed.
Lemma lem2320000 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2320001 : term55 = term56.
Proof. exact (@lem2320000 term57). Qed.
Lemma lem2320002 (y : int) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem2320003 (y : int) : (term68 y) = (term70 y).
Proof. exact (MK_COMB (@lem2320002 y) (@lem2320001)). Qed.
Lemma lem2320004 (y : int) : (term67 y) = (term70 y).
Proof. exact (TRANS (@lem2319998 y) (@lem2320003 y)). Qed.
Lemma lem2320005 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2320006 (y : int) : (term71 y) = (term72 y).
Proof. exact (MK_COMB (@lem2320005) (@lem2320004 y)). Qed.
Lemma lem2320007 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2320008 (y : int) (x : int) : (term81 y x) = (term82 y x).
Proof. exact (MK_COMB (@lem2320006 y) (@lem2320007 x)). Qed.
Lemma lem2320009 (y : int) (x : int) : (term80 y x) = (term82 y x).
Proof. exact (TRANS (@lem2319995 y x) (@lem2320008 y x)). Qed.
Lemma lem2320010 (y : int) (x : int) : (term79 x y) = (term82 y x).
Proof. exact (TRANS (@lem2319992 y x) (@lem2320009 y x)). Qed.
Lemma lem2320012 (y : int) (x : int) : (term39 x y) = (term40 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2320013 (x : int) (y : int) : (term26 y x) = (term83 x y).
Proof. exact (@lem2320012 x (int_max x y)). Qed.
Lemma lem2320015 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2320016 (y : int) (x : int) : (term84 y x) = (term85 y x).
Proof. exact (@lem2320015 (term44 x y) x). Qed.
Lemma lem2320018 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2320019 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (@lem2320018 (int_max x y) term49). Qed.
Lemma lem2320021 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem2320022 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2320023 (x : int) (y : int) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem2320022) (@lem2320021 x y)). Qed.
Lemma lem2320025 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2320026 : term55 = term56.
Proof. exact (@lem2320025 term57). Qed.
Lemma lem2320027 (x : int) (y : int) : (term48 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem2320023 x y) (@lem2320026)). Qed.
Lemma lem2320028 (x : int) (y : int) : (term47 x y) = (term58 x y).
Proof. exact (TRANS (@lem2320019 x y) (@lem2320027 x y)). Qed.
Lemma lem2320029 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2320030 (x : int) (y : int) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem2320029) (@lem2320028 x y)). Qed.
Lemma lem2320031 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2320032 (y : int) (x : int) : (term85 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem2320030 x y) (@lem2320031 x)). Qed.
Lemma lem2320033 (y : int) (x : int) : (term84 y x) = (term86 y x).
Proof. exact (TRANS (@lem2320016 y x) (@lem2320032 y x)). Qed.
Lemma lem2320034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320035 (y : int) (x : int) : (term87 y x) = (term88 y x).
Proof. exact (MK_COMB (@lem2320034) (@lem2320033 y x)). Qed.
Lemma lem2320037 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2320038 (x : int) (y : int) : (term89 x y) = (term90 x y).
Proof. exact (@lem2320037 (term66 x) (int_max x y)). Qed.
Lemma lem2320040 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2320041 (x : int) : (term67 x) = (term68 x).
Proof. exact (@lem2320040 x term49). Qed.
Lemma lem2320043 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2320044 : term55 = term56.
Proof. exact (@lem2320043 term57). Qed.
Lemma lem2320045 (x : int) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem2320046 (x : int) : (term68 x) = (term70 x).
Proof. exact (MK_COMB (@lem2320045 x) (@lem2320044)). Qed.
Lemma lem2320047 (x : int) : (term67 x) = (term70 x).
Proof. exact (TRANS (@lem2320041 x) (@lem2320046 x)). Qed.
Lemma lem2320048 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2320049 (x : int) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem2320048) (@lem2320047 x)). Qed.
Lemma lem2320051 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem2320052 (x : int) (y : int) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem2320049 x) (@lem2320051 x y)). Qed.
Lemma lem2320053 (x : int) (y : int) : (term89 x y) = (term91 x y).
Proof. exact (TRANS (@lem2320038 x y) (@lem2320052 x y)). Qed.
Lemma lem2320054 (x : int) (y : int) : (term83 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem2320035 y x) (@lem2320053 x y)). Qed.
Lemma lem2320055 (x : int) (y : int) : (term26 y x) = (term92 x y).
Proof. exact (TRANS (@lem2320013 x y) (@lem2320054 x y)). Qed.
Lemma lem2320056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2320057 (y : int) (x : int) : (term93 x y) = (term94 y x).
Proof. exact (MK_COMB (@lem2320056) (@lem2320010 y x)). Qed.
Lemma lem2320058 (x : int) (y : int) : (term95 y x) = (term96 x y).
Proof. exact (MK_COMB (@lem2320057 y x) (@lem2320055 x y)). Qed.
Lemma lem2320059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320060 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem2320059) (@lem2319990 x y)). Qed.
Lemma lem2320061 (x : int) (y : int) : (term33 y x) = (term99 x y).
Proof. exact (MK_COMB (@lem2320060 x y) (@lem2320058 x y)). Qed.
Lemma lem2320062 (x : int) : (term34 x) = (term100 x).
Proof. exact (fun_ext (fun y : int => @lem2320061 x y)). Qed.
Lemma lem2320063 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320064 (x : int) : (term35 x) = (term101 x).
Proof. exact (MK_COMB (@lem2320063) (@lem2320062 x)). Qed.
Lemma lem2320065 : term36 = term102.
Proof. exact (fun_ext (fun x : int => @lem2320064 x)). Qed.
Lemma lem2320066 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320067 : term37 = term103.
Proof. exact (MK_COMB (@lem2320066) (@lem2320065)). Qed.
Lemma lem2320068 : term14 = term103.
Proof. exact (TRANS (@lem2319938) (@lem2320067)). Qed.
Lemma lem2320072 (t : Prop) : (term104 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2320073 : term105 = term103.
Proof. exact (@lem2320072 term103). Qed.
Lemma lem2320079 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2320080 (P : int -> Prop) (Q : int -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem2320079 int P Q). Qed.
Lemma lem2320081 (x : int) : (term110 x) = (term111 x).
Proof. exact (@lem2320080 (term112 x) (term113 x)). Qed.
Lemma lem2320082 (x : int) (y : int) : (term114 x y) = (term78 x y).
Proof. exact (eq_refl (term114 x y)). Qed.
Lemma lem2320083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320084 (x : int) (y : int) : (term115 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem2320083) (@lem2320082 x y)). Qed.
Lemma lem2320085 (x : int) (y : int) : (term116 x y) = (term96 x y).
Proof. exact (eq_refl (term116 x y)). Qed.
Lemma lem2320086 (x : int) (y : int) : (term117 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2320084 x y) (@lem2320085 x y)). Qed.
Lemma lem2320087 (x : int) : (term118 x) = (term100 x).
Proof. exact (fun_ext (fun y : int => @lem2320086 x y)). Qed.
Lemma lem2320088 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320089 (x : int) : (term110 x) = (term101 x).
Proof. exact (MK_COMB (@lem2320088) (@lem2320087 x)). Qed.
Lemma lem2320090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2320091 (x : int) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem2320090) (@lem2320089 x)). Qed.
Lemma lem2320092 (x : int) (y : int) : (term114 x y) = (term78 x y).
Proof. exact (eq_refl (term114 x y)). Qed.
Lemma lem2320093 (x : int) : (term121 x) = (term112 x).
Proof. exact (fun_ext (fun y : int => @lem2320092 x y)). Qed.
Lemma lem2320094 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320095 (x : int) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem2320094) (@lem2320093 x)). Qed.
Lemma lem2320096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320097 (x : int) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem2320096) (@lem2320095 x)). Qed.
Lemma lem2320098 (x : int) (y : int) : (term116 x y) = (term96 x y).
Proof. exact (eq_refl (term116 x y)). Qed.
Lemma lem2320099 (x : int) : (term126 x) = (term113 x).
Proof. exact (fun_ext (fun y : int => @lem2320098 x y)). Qed.
Lemma lem2320100 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320101 (x : int) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem2320100) (@lem2320099 x)). Qed.
Lemma lem2320102 (x : int) : (term111 x) = (term129 x).
Proof. exact (MK_COMB (@lem2320097 x) (@lem2320101 x)). Qed.
Lemma lem2320103 (x : int) : ((term110 x) = (term111 x)) = ((term101 x) = (term129 x)).
Proof. exact (MK_COMB (@lem2320091 x) (@lem2320102 x)). Qed.
Lemma lem2320104 (x : int) : (term101 x) = (term129 x).
Proof. exact (EQ_MP (@lem2320103 x) (@lem2320081 x)). Qed.
Lemma lem2320211 : term102 = term130.
Proof. exact (fun_ext (fun x : int => @lem2320104 x)). Qed.
Lemma lem2320212 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320213 : term103 = term131.
Proof. exact (MK_COMB (@lem2320212) (@lem2320211)). Qed.
Lemma lem2320215 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2320216 (P : int -> Prop) (Q : int -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem2320215 int P Q). Qed.
Lemma lem2320217 : term132 = term133.
Proof. exact (@lem2320216 term134 term135). Qed.
Lemma lem2320218 (x : int) : (term136 x) = (term123 x).
Proof. exact (eq_refl (term136 x)). Qed.
Lemma lem2320219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320220 (x : int) : (term137 x) = (term125 x).
Proof. exact (MK_COMB (@lem2320219) (@lem2320218 x)). Qed.
Lemma lem2320221 (x : int) : (term138 x) = (term128 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem2320222 (x : int) : (term139 x) = (term129 x).
Proof. exact (MK_COMB (@lem2320220 x) (@lem2320221 x)). Qed.
Lemma lem2320223 : term140 = term130.
Proof. exact (fun_ext (fun x : int => @lem2320222 x)). Qed.
Lemma lem2320224 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320225 : term132 = term131.
Proof. exact (MK_COMB (@lem2320224) (@lem2320223)). Qed.
Lemma lem2320226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2320227 : term141 = term142.
Proof. exact (MK_COMB (@lem2320226) (@lem2320225)). Qed.
Lemma lem2320228 (x : int) : (term136 x) = (term123 x).
Proof. exact (eq_refl (term136 x)). Qed.
Lemma lem2320229 : term143 = term134.
Proof. exact (fun_ext (fun x : int => @lem2320228 x)). Qed.
Lemma lem2320230 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320231 : term144 = term145.
Proof. exact (MK_COMB (@lem2320230) (@lem2320229)). Qed.
Lemma lem2320232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320233 : term146 = term147.
Proof. exact (MK_COMB (@lem2320232) (@lem2320231)). Qed.
Lemma lem2320234 (x : int) : (term138 x) = (term128 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem2320235 : term148 = term135.
Proof. exact (fun_ext (fun x : int => @lem2320234 x)). Qed.
Lemma lem2320236 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320237 : term149 = term150.
Proof. exact (MK_COMB (@lem2320236) (@lem2320235)). Qed.
Lemma lem2320238 : term133 = term151.
Proof. exact (MK_COMB (@lem2320233) (@lem2320237)). Qed.
Lemma lem2320239 : (term132 = term133) = (term131 = term151).
Proof. exact (MK_COMB (@lem2320227) (@lem2320238)). Qed.
Lemma lem2320240 : term131 = term151.
Proof. exact (EQ_MP (@lem2320239) (@lem2320217)). Qed.
Lemma lem2320355 : term103 = term151.
Proof. exact (TRANS (@lem2320213) (@lem2320240)). Qed.
Lemma lem2320357 : term105 = term151.
Proof. exact (TRANS (@lem2320073) (@lem2320355)). Qed.
Lemma lem2320366 (x : int) (y : int) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem2320367 (x : int) : (term112 x) = (term112 x).
Proof. exact (fun_ext (fun y : int => @lem2320366 x y)). Qed.
Lemma lem2320368 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320369 (x : int) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem2320368) (@lem2320367 x)). Qed.
Lemma lem2320370 : term134 = term134.
Proof. exact (fun_ext (fun x : int => @lem2320369 x)). Qed.
Lemma lem2320371 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320372 : term145 = term145.
Proof. exact (MK_COMB (@lem2320371) (@lem2320370)). Qed.
Lemma lem2320381 (x : int) (y : int) : (term96 x y) = (term96 x y).
Proof. exact (eq_refl (term96 x y)). Qed.
Lemma lem2320382 (x : int) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun y : int => @lem2320381 x y)). Qed.
Lemma lem2320383 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320384 (x : int) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2320383) (@lem2320382 x)). Qed.
Lemma lem2320385 : term135 = term135.
Proof. exact (fun_ext (fun x : int => @lem2320384 x)). Qed.
Lemma lem2320386 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320387 : term150 = term150.
Proof. exact (MK_COMB (@lem2320386) (@lem2320385)). Qed.
Lemma lem2320388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320389 : term147 = term147.
Proof. exact (MK_COMB (@lem2320388) (@lem2320372)). Qed.
Lemma lem2320390 : term151 = term151.
Proof. exact (MK_COMB (@lem2320389) (@lem2320387)). Qed.
Lemma lem2320391 : term105 = term151.
Proof. exact (TRANS (@lem2320357) (@lem2320390)). Qed.
Lemma lem2320400 (x : int) (y : int) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem2320401 (x : int) : (term112 x) = (term112 x).
Proof. exact (fun_ext (fun y : int => @lem2320400 x y)). Qed.
Lemma lem2320402 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320403 (x : int) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem2320402) (@lem2320401 x)). Qed.
Lemma lem2320404 : term134 = term134.
Proof. exact (fun_ext (fun x : int => @lem2320403 x)). Qed.
Lemma lem2320405 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320406 : term145 = term145.
Proof. exact (MK_COMB (@lem2320405) (@lem2320404)). Qed.
Lemma lem2320415 (x : int) (y : int) : (term96 x y) = (term96 x y).
Proof. exact (eq_refl (term96 x y)). Qed.
Lemma lem2320416 (x : int) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun y : int => @lem2320415 x y)). Qed.
Lemma lem2320417 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320418 (x : int) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2320417) (@lem2320416 x)). Qed.
Lemma lem2320419 : term135 = term135.
Proof. exact (fun_ext (fun x : int => @lem2320418 x)). Qed.
Lemma lem2320420 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320421 : term150 = term150.
Proof. exact (MK_COMB (@lem2320420) (@lem2320419)). Qed.
Lemma lem2320422 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320423 : term147 = term147.
Proof. exact (MK_COMB (@lem2320422) (@lem2320406)). Qed.
Lemma lem2320424 : term151 = term151.
Proof. exact (MK_COMB (@lem2320423) (@lem2320421)). Qed.
Lemma lem2320425 : term105 = term151.
Proof. exact (TRANS (@lem2320391) (@lem2320424)). Qed.
Lemma lem2320426 (y : int) (x : int) : (term38 x y) = (term152 y x).
Proof. exact (@lem1988287 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2320432 (y : int) (x : int) : (term153 y x) = (term154 y x).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2320437 (x : int) (y : int) : (term154 y x) = (term155 x y).
Proof. exact (@lem1982761 (term156 x) (real_of_int y)). Qed.
Lemma lem2320439 (x : int) (y : int) : (term153 y x) = (term155 x y).
Proof. exact (TRANS (@lem2320432 y x) (@lem2320437 x y)). Qed.
Lemma lem2320440 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2320441 (x : int) (y : int) : (term157 y x) = (term158 x y).
Proof. exact (MK_COMB (@lem2320440) (@lem2320439 x y)). Qed.
Lemma lem2320442 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2320443 (x : int) (y : int) : (term152 y x) = (term160 x y).
Proof. exact (MK_COMB (@lem2320441 x y) (@lem2320442)). Qed.
Lemma lem2320444 (x : int) (y : int) : (term38 x y) = (term160 x y).
Proof. exact (TRANS (@lem2320426 y x) (@lem2320443 x y)). Qed.
Lemma lem2320445 (x : int) (y : int) : (term61 x y) = (term161 x y).
Proof. exact (@lem1988287 (real_of_int y) (term58 x y)). Qed.
Lemma lem2320461 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (@lem1982792 (real_of_int y) (term58 x y)). Qed.
Lemma lem2320462 (x : int) (y : int) : (term164 x y) = (term165 x y).
Proof. exact (@lem1982781 (term51 x y) term166 term56). Qed.
Lemma lem2320464 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2320465 : term56 = term168.
Proof. exact (@lem2320464 term57). Qed.
Lemma lem2320467 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2320468 : term166 = term171.
Proof. exact (@lem2320467 term57). Qed.
Lemma lem2320469 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2320470 : term172 = term173.
Proof. exact (MK_COMB (@lem2320469) (@lem2320468)). Qed.
Lemma lem2320471 : term174 = term175.
Proof. exact (MK_COMB (@lem2320470) (@lem2320465)). Qed.
Lemma lem2320472 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2320474 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2320475 : term179 = term180.
Proof. exact (@lem2320474 term57 term57). Qed.
Lemma lem2320476 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320477 : term182 = term57.
Proof. exact (EQ_MP (@lem2320476) (@lem940073)). Qed.
Lemma lem2320478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320479 : term180 = term56.
Proof. exact (MK_COMB (@lem2320478) (@lem2320477)). Qed.
Lemma lem2320480 : term179 = term56.
Proof. exact (TRANS (@lem2320475) (@lem2320479)). Qed.
Lemma lem2320482 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2320483 : term174 = term185.
Proof. exact (@lem2320482 term57 term57). Qed.
Lemma lem2320484 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320485 : term182 = term57.
Proof. exact (EQ_MP (@lem2320484) (@lem940073)). Qed.
Lemma lem2320486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320487 : term180 = term56.
Proof. exact (MK_COMB (@lem2320486) (@lem2320485)). Qed.
Lemma lem2320488 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2320489 : term185 = term166.
Proof. exact (MK_COMB (@lem2320488) (@lem2320487)). Qed.
Lemma lem2320490 : term174 = term166.
Proof. exact (TRANS (@lem2320483) (@lem2320489)). Qed.
Lemma lem2320491 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2320492 : term186 = term187.
Proof. exact (MK_COMB (@lem2320491) (@lem2320490)). Qed.
Lemma lem2320493 : term176 = term171.
Proof. exact (MK_COMB (@lem2320492) (@lem2320480)). Qed.
Lemma lem2320494 : term175 = term171.
Proof. exact (TRANS (@lem2320472) (@lem2320493)). Qed.
Lemma lem2320495 : term174 = term171.
Proof. exact (TRANS (@lem2320471) (@lem2320494)). Qed.
Lemma lem2320497 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2320498 : term171 = term166.
Proof. exact (@lem2320497 term166). Qed.
Lemma lem2320499 : term174 = term166.
Proof. exact (TRANS (@lem2320495) (@lem2320498)). Qed.
Lemma lem2320502 (x : int) (y : int) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem2320503 (x : int) (y : int) : (term165 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem2320502 x y) (@lem2320499)). Qed.
Lemma lem2320504 (x : int) (y : int) : (term164 x y) = (term190 x y).
Proof. exact (TRANS (@lem2320462 x y) (@lem2320503 x y)). Qed.
Lemma lem2320505 (y : int) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem2320508 (x : int) (y : int) : (term163 x y) = (term191 x y).
Proof. exact (MK_COMB (@lem2320505 y) (@lem2320504 x y)). Qed.
Lemma lem2320510 (x : int) (y : int) : (term162 x y) = (term191 x y).
Proof. exact (TRANS (@lem2320461 x y) (@lem2320508 x y)). Qed.
Lemma lem2320511 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2320512 (x : int) (y : int) : (term192 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem2320511) (@lem2320510 x y)). Qed.
Lemma lem2320513 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2320514 (x : int) (y : int) : (term161 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem2320512 x y) (@lem2320513)). Qed.
Lemma lem2320515 (x : int) (y : int) : (term61 x y) = (term194 x y).
Proof. exact (TRANS (@lem2320445 x y) (@lem2320514 x y)). Qed.
Lemma lem2320516 (x : int) (y : int) : (term73 x y) = (term195 x y).
Proof. exact (@lem1988287 (term51 x y) (term70 y)). Qed.
Lemma lem2320532 (x : int) (y : int) : (term196 x y) = (term197 x y).
Proof. exact (@lem1982792 (term51 x y) (term70 y)). Qed.
Lemma lem2320533 (y : int) : (term198 y) = (term199 y).
Proof. exact (@lem1982781 (real_of_int y) term166 term56). Qed.
Lemma lem2320535 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2320536 : term56 = term168.
Proof. exact (@lem2320535 term57). Qed.
Lemma lem2320538 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2320539 : term166 = term171.
Proof. exact (@lem2320538 term57). Qed.
Lemma lem2320540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2320541 : term172 = term173.
Proof. exact (MK_COMB (@lem2320540) (@lem2320539)). Qed.
Lemma lem2320542 : term174 = term175.
Proof. exact (MK_COMB (@lem2320541) (@lem2320536)). Qed.
Lemma lem2320543 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2320545 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2320546 : term179 = term180.
Proof. exact (@lem2320545 term57 term57). Qed.
Lemma lem2320547 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320548 : term182 = term57.
Proof. exact (EQ_MP (@lem2320547) (@lem940073)). Qed.
Lemma lem2320549 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320550 : term180 = term56.
Proof. exact (MK_COMB (@lem2320549) (@lem2320548)). Qed.
Lemma lem2320551 : term179 = term56.
Proof. exact (TRANS (@lem2320546) (@lem2320550)). Qed.
Lemma lem2320553 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2320554 : term174 = term185.
Proof. exact (@lem2320553 term57 term57). Qed.
Lemma lem2320555 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320556 : term182 = term57.
Proof. exact (EQ_MP (@lem2320555) (@lem940073)). Qed.
Lemma lem2320557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320558 : term180 = term56.
Proof. exact (MK_COMB (@lem2320557) (@lem2320556)). Qed.
Lemma lem2320559 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2320560 : term185 = term166.
Proof. exact (MK_COMB (@lem2320559) (@lem2320558)). Qed.
Lemma lem2320561 : term174 = term166.
Proof. exact (TRANS (@lem2320554) (@lem2320560)). Qed.
Lemma lem2320562 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2320563 : term186 = term187.
Proof. exact (MK_COMB (@lem2320562) (@lem2320561)). Qed.
Lemma lem2320564 : term176 = term171.
Proof. exact (MK_COMB (@lem2320563) (@lem2320551)). Qed.
Lemma lem2320565 : term175 = term171.
Proof. exact (TRANS (@lem2320543) (@lem2320564)). Qed.
Lemma lem2320566 : term174 = term171.
Proof. exact (TRANS (@lem2320542) (@lem2320565)). Qed.
Lemma lem2320568 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2320569 : term171 = term166.
Proof. exact (@lem2320568 term166). Qed.
Lemma lem2320570 : term174 = term166.
Proof. exact (TRANS (@lem2320566) (@lem2320569)). Qed.
Lemma lem2320573 (y : int) : (term200 y) = (term200 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem2320574 (y : int) : (term199 y) = (term201 y).
Proof. exact (MK_COMB (@lem2320573 y) (@lem2320570)). Qed.
Lemma lem2320575 (y : int) : (term198 y) = (term201 y).
Proof. exact (TRANS (@lem2320533 y) (@lem2320574 y)). Qed.
Lemma lem2320576 (x : int) (y : int) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem2320577 (x : int) (y : int) : (term197 x y) = (term202 x y).
Proof. exact (MK_COMB (@lem2320576 x y) (@lem2320575 y)). Qed.
Lemma lem2320582 (x : int) (y : int) : (term202 x y) = (term203 x y).
Proof. exact (@lem1982757 (term156 y) (term51 x y) term166). Qed.
Lemma lem2320583 (x : int) (y : int) : (term197 x y) = (term203 x y).
Proof. exact (TRANS (@lem2320577 x y) (@lem2320582 x y)). Qed.
Lemma lem2320585 (x : int) (y : int) : (term196 x y) = (term203 x y).
Proof. exact (TRANS (@lem2320532 x y) (@lem2320583 x y)). Qed.
Lemma lem2320586 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2320587 (x : int) (y : int) : (term204 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem2320586) (@lem2320585 x y)). Qed.
Lemma lem2320588 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2320589 (x : int) (y : int) : (term195 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem2320587 x y) (@lem2320588)). Qed.
Lemma lem2320590 (x : int) (y : int) : (term73 x y) = (term206 x y).
Proof. exact (TRANS (@lem2320516 x y) (@lem2320589 x y)). Qed.
Lemma lem2320591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320592 (x : int) (y : int) : (term63 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem2320591) (@lem2320515 x y)). Qed.
Lemma lem2320593 (x : int) (y : int) : (term74 x y) = (term208 x y).
Proof. exact (MK_COMB (@lem2320592 x y) (@lem2320590 x y)). Qed.
Lemma lem2320594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2320595 (x : int) (y : int) : (term76 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem2320594) (@lem2320444 x y)). Qed.
Lemma lem2320596 (x : int) (y : int) : (term78 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem2320595 x y) (@lem2320593 x y)). Qed.
Lemma lem2320597 (x : int) : (term112 x) = (term211 x).
Proof. exact (fun_ext (fun y : int => @lem2320596 x y)). Qed.
Lemma lem2320598 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320599 (x : int) : (term123 x) = (term212 x).
Proof. exact (MK_COMB (@lem2320598) (@lem2320597 x)). Qed.
Lemma lem2320600 : term134 = term213.
Proof. exact (fun_ext (fun x : int => @lem2320599 x)). Qed.
Lemma lem2320601 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320602 : term145 = term214.
Proof. exact (MK_COMB (@lem2320601) (@lem2320600)). Qed.
Lemma lem2320603 (x : int) (y : int) : (term82 y x) = (term215 x y).
Proof. exact (@lem1988287 (real_of_int x) (term70 y)). Qed.
Lemma lem2320615 (x : int) (y : int) : (term216 x y) = (term217 x y).
Proof. exact (@lem1982792 (real_of_int x) (term70 y)). Qed.
Lemma lem2320616 (y : int) : (term198 y) = (term199 y).
Proof. exact (@lem1982781 (real_of_int y) term166 term56). Qed.
Lemma lem2320618 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2320619 : term56 = term168.
Proof. exact (@lem2320618 term57). Qed.
Lemma lem2320621 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2320622 : term166 = term171.
Proof. exact (@lem2320621 term57). Qed.
Lemma lem2320623 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2320624 : term172 = term173.
Proof. exact (MK_COMB (@lem2320623) (@lem2320622)). Qed.
Lemma lem2320625 : term174 = term175.
Proof. exact (MK_COMB (@lem2320624) (@lem2320619)). Qed.
Lemma lem2320626 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2320628 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2320629 : term179 = term180.
Proof. exact (@lem2320628 term57 term57). Qed.
Lemma lem2320630 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320631 : term182 = term57.
Proof. exact (EQ_MP (@lem2320630) (@lem940073)). Qed.
Lemma lem2320632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320633 : term180 = term56.
Proof. exact (MK_COMB (@lem2320632) (@lem2320631)). Qed.
Lemma lem2320634 : term179 = term56.
Proof. exact (TRANS (@lem2320629) (@lem2320633)). Qed.
Lemma lem2320636 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2320637 : term174 = term185.
Proof. exact (@lem2320636 term57 term57). Qed.
Lemma lem2320638 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320639 : term182 = term57.
Proof. exact (EQ_MP (@lem2320638) (@lem940073)). Qed.
Lemma lem2320640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320641 : term180 = term56.
Proof. exact (MK_COMB (@lem2320640) (@lem2320639)). Qed.
Lemma lem2320642 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2320643 : term185 = term166.
Proof. exact (MK_COMB (@lem2320642) (@lem2320641)). Qed.
Lemma lem2320644 : term174 = term166.
Proof. exact (TRANS (@lem2320637) (@lem2320643)). Qed.
Lemma lem2320645 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2320646 : term186 = term187.
Proof. exact (MK_COMB (@lem2320645) (@lem2320644)). Qed.
Lemma lem2320647 : term176 = term171.
Proof. exact (MK_COMB (@lem2320646) (@lem2320634)). Qed.
Lemma lem2320648 : term175 = term171.
Proof. exact (TRANS (@lem2320626) (@lem2320647)). Qed.
Lemma lem2320649 : term174 = term171.
Proof. exact (TRANS (@lem2320625) (@lem2320648)). Qed.
Lemma lem2320651 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2320652 : term171 = term166.
Proof. exact (@lem2320651 term166). Qed.
Lemma lem2320653 : term174 = term166.
Proof. exact (TRANS (@lem2320649) (@lem2320652)). Qed.
Lemma lem2320656 (y : int) : (term200 y) = (term200 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem2320657 (y : int) : (term199 y) = (term201 y).
Proof. exact (MK_COMB (@lem2320656 y) (@lem2320653)). Qed.
Lemma lem2320658 (y : int) : (term198 y) = (term201 y).
Proof. exact (TRANS (@lem2320616 y) (@lem2320657 y)). Qed.
Lemma lem2320659 (x : int) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem2320662 (x : int) (y : int) : (term217 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem2320659 x) (@lem2320658 y)). Qed.
Lemma lem2320664 (x : int) (y : int) : (term216 x y) = (term218 x y).
Proof. exact (TRANS (@lem2320615 x y) (@lem2320662 x y)). Qed.
Lemma lem2320665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2320666 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem2320665) (@lem2320664 x y)). Qed.
Lemma lem2320667 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2320668 (x : int) (y : int) : (term215 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem2320666 x y) (@lem2320667)). Qed.
Lemma lem2320669 (x : int) (y : int) : (term82 y x) = (term221 x y).
Proof. exact (TRANS (@lem2320603 x y) (@lem2320668 x y)). Qed.
Lemma lem2320670 (x : int) (y : int) : (term86 y x) = (term222 x y).
Proof. exact (@lem1988287 (real_of_int x) (term58 x y)). Qed.
Lemma lem2320686 (x : int) (y : int) : (term223 x y) = (term224 x y).
Proof. exact (@lem1982792 (real_of_int x) (term58 x y)). Qed.
Lemma lem2320687 (x : int) (y : int) : (term164 x y) = (term165 x y).
Proof. exact (@lem1982781 (term51 x y) term166 term56). Qed.
Lemma lem2320689 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2320690 : term56 = term168.
Proof. exact (@lem2320689 term57). Qed.
Lemma lem2320692 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2320693 : term166 = term171.
Proof. exact (@lem2320692 term57). Qed.
Lemma lem2320694 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2320695 : term172 = term173.
Proof. exact (MK_COMB (@lem2320694) (@lem2320693)). Qed.
Lemma lem2320696 : term174 = term175.
Proof. exact (MK_COMB (@lem2320695) (@lem2320690)). Qed.
Lemma lem2320697 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2320699 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2320700 : term179 = term180.
Proof. exact (@lem2320699 term57 term57). Qed.
Lemma lem2320701 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320702 : term182 = term57.
Proof. exact (EQ_MP (@lem2320701) (@lem940073)). Qed.
Lemma lem2320703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320704 : term180 = term56.
Proof. exact (MK_COMB (@lem2320703) (@lem2320702)). Qed.
Lemma lem2320705 : term179 = term56.
Proof. exact (TRANS (@lem2320700) (@lem2320704)). Qed.
Lemma lem2320707 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2320708 : term174 = term185.
Proof. exact (@lem2320707 term57 term57). Qed.
Lemma lem2320709 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320710 : term182 = term57.
Proof. exact (EQ_MP (@lem2320709) (@lem940073)). Qed.
Lemma lem2320711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320712 : term180 = term56.
Proof. exact (MK_COMB (@lem2320711) (@lem2320710)). Qed.
Lemma lem2320713 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2320714 : term185 = term166.
Proof. exact (MK_COMB (@lem2320713) (@lem2320712)). Qed.
Lemma lem2320715 : term174 = term166.
Proof. exact (TRANS (@lem2320708) (@lem2320714)). Qed.
Lemma lem2320716 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2320717 : term186 = term187.
Proof. exact (MK_COMB (@lem2320716) (@lem2320715)). Qed.
Lemma lem2320718 : term176 = term171.
Proof. exact (MK_COMB (@lem2320717) (@lem2320705)). Qed.
Lemma lem2320719 : term175 = term171.
Proof. exact (TRANS (@lem2320697) (@lem2320718)). Qed.
Lemma lem2320720 : term174 = term171.
Proof. exact (TRANS (@lem2320696) (@lem2320719)). Qed.
Lemma lem2320722 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2320723 : term171 = term166.
Proof. exact (@lem2320722 term166). Qed.
Lemma lem2320724 : term174 = term166.
Proof. exact (TRANS (@lem2320720) (@lem2320723)). Qed.
Lemma lem2320727 (x : int) (y : int) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem2320728 (x : int) (y : int) : (term165 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem2320727 x y) (@lem2320724)). Qed.
Lemma lem2320729 (x : int) (y : int) : (term164 x y) = (term190 x y).
Proof. exact (TRANS (@lem2320687 x y) (@lem2320728 x y)). Qed.
Lemma lem2320730 (x : int) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem2320733 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (MK_COMB (@lem2320730 x) (@lem2320729 x y)). Qed.
Lemma lem2320735 (x : int) (y : int) : (term223 x y) = (term225 x y).
Proof. exact (TRANS (@lem2320686 x y) (@lem2320733 x y)). Qed.
Lemma lem2320736 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2320737 (x : int) (y : int) : (term226 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem2320736) (@lem2320735 x y)). Qed.
Lemma lem2320738 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2320739 (x : int) (y : int) : (term222 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem2320737 x y) (@lem2320738)). Qed.
Lemma lem2320740 (x : int) (y : int) : (term86 y x) = (term228 x y).
Proof. exact (TRANS (@lem2320670 x y) (@lem2320739 x y)). Qed.
Lemma lem2320741 (y : int) (x : int) : (term91 x y) = (term229 y x).
Proof. exact (@lem1988287 (term51 x y) (term70 x)). Qed.
Lemma lem2320757 (y : int) (x : int) : (term230 y x) = (term231 y x).
Proof. exact (@lem1982792 (term51 x y) (term70 x)). Qed.
Lemma lem2320758 (x : int) : (term198 x) = (term199 x).
Proof. exact (@lem1982781 (real_of_int x) term166 term56). Qed.
Lemma lem2320760 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2320761 : term56 = term168.
Proof. exact (@lem2320760 term57). Qed.
Lemma lem2320763 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2320764 : term166 = term171.
Proof. exact (@lem2320763 term57). Qed.
Lemma lem2320765 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2320766 : term172 = term173.
Proof. exact (MK_COMB (@lem2320765) (@lem2320764)). Qed.
Lemma lem2320767 : term174 = term175.
Proof. exact (MK_COMB (@lem2320766) (@lem2320761)). Qed.
Lemma lem2320768 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2320770 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2320771 : term179 = term180.
Proof. exact (@lem2320770 term57 term57). Qed.
Lemma lem2320772 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320773 : term182 = term57.
Proof. exact (EQ_MP (@lem2320772) (@lem940073)). Qed.
Lemma lem2320774 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320775 : term180 = term56.
Proof. exact (MK_COMB (@lem2320774) (@lem2320773)). Qed.
Lemma lem2320776 : term179 = term56.
Proof. exact (TRANS (@lem2320771) (@lem2320775)). Qed.
Lemma lem2320778 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2320779 : term174 = term185.
Proof. exact (@lem2320778 term57 term57). Qed.
Lemma lem2320780 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2320781 : term182 = term57.
Proof. exact (EQ_MP (@lem2320780) (@lem940073)). Qed.
Lemma lem2320782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2320783 : term180 = term56.
Proof. exact (MK_COMB (@lem2320782) (@lem2320781)). Qed.
Lemma lem2320784 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2320785 : term185 = term166.
Proof. exact (MK_COMB (@lem2320784) (@lem2320783)). Qed.
Lemma lem2320786 : term174 = term166.
Proof. exact (TRANS (@lem2320779) (@lem2320785)). Qed.
Lemma lem2320787 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2320788 : term186 = term187.
Proof. exact (MK_COMB (@lem2320787) (@lem2320786)). Qed.
Lemma lem2320789 : term176 = term171.
Proof. exact (MK_COMB (@lem2320788) (@lem2320776)). Qed.
Lemma lem2320790 : term175 = term171.
Proof. exact (TRANS (@lem2320768) (@lem2320789)). Qed.
Lemma lem2320791 : term174 = term171.
Proof. exact (TRANS (@lem2320767) (@lem2320790)). Qed.
Lemma lem2320793 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2320794 : term171 = term166.
Proof. exact (@lem2320793 term166). Qed.
Lemma lem2320795 : term174 = term166.
Proof. exact (TRANS (@lem2320791) (@lem2320794)). Qed.
Lemma lem2320798 (x : int) : (term200 x) = (term200 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem2320799 (x : int) : (term199 x) = (term201 x).
Proof. exact (MK_COMB (@lem2320798 x) (@lem2320795)). Qed.
Lemma lem2320800 (x : int) : (term198 x) = (term201 x).
Proof. exact (TRANS (@lem2320758 x) (@lem2320799 x)). Qed.
Lemma lem2320801 (x : int) (y : int) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem2320802 (y : int) (x : int) : (term231 y x) = (term232 y x).
Proof. exact (MK_COMB (@lem2320801 x y) (@lem2320800 x)). Qed.
Lemma lem2320807 (x : int) (y : int) : (term232 y x) = (term233 x y).
Proof. exact (@lem1982757 (term156 x) (term51 x y) term166). Qed.
Lemma lem2320808 (x : int) (y : int) : (term231 y x) = (term233 x y).
Proof. exact (TRANS (@lem2320802 y x) (@lem2320807 x y)). Qed.
Lemma lem2320810 (x : int) (y : int) : (term230 y x) = (term233 x y).
Proof. exact (TRANS (@lem2320757 y x) (@lem2320808 x y)). Qed.
Lemma lem2320811 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2320812 (x : int) (y : int) : (term234 y x) = (term235 x y).
Proof. exact (MK_COMB (@lem2320811) (@lem2320810 x y)). Qed.
Lemma lem2320813 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2320814 (x : int) (y : int) : (term229 y x) = (term236 x y).
Proof. exact (MK_COMB (@lem2320812 x y) (@lem2320813)). Qed.
Lemma lem2320815 (x : int) (y : int) : (term91 x y) = (term236 x y).
Proof. exact (TRANS (@lem2320741 y x) (@lem2320814 x y)). Qed.
Lemma lem2320816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320817 (x : int) (y : int) : (term88 y x) = (term237 x y).
Proof. exact (MK_COMB (@lem2320816) (@lem2320740 x y)). Qed.
Lemma lem2320818 (x : int) (y : int) : (term92 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem2320817 x y) (@lem2320815 x y)). Qed.
Lemma lem2320819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2320820 (x : int) (y : int) : (term94 y x) = (term239 x y).
Proof. exact (MK_COMB (@lem2320819) (@lem2320669 x y)). Qed.
Lemma lem2320821 (x : int) (y : int) : (term96 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem2320820 x y) (@lem2320818 x y)). Qed.
Lemma lem2320822 (x : int) : (term113 x) = (term241 x).
Proof. exact (fun_ext (fun y : int => @lem2320821 x y)). Qed.
Lemma lem2320823 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320824 (x : int) : (term128 x) = (term242 x).
Proof. exact (MK_COMB (@lem2320823) (@lem2320822 x)). Qed.
Lemma lem2320825 : term135 = term243.
Proof. exact (fun_ext (fun x : int => @lem2320824 x)). Qed.
Lemma lem2320826 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320827 : term150 = term244.
Proof. exact (MK_COMB (@lem2320826) (@lem2320825)). Qed.
Lemma lem2320828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320829 : term147 = term245.
Proof. exact (MK_COMB (@lem2320828) (@lem2320602)). Qed.
Lemma lem2320830 : term151 = term246.
Proof. exact (MK_COMB (@lem2320829) (@lem2320827)). Qed.
Lemma lem2320831 : term105 = term246.
Proof. exact (TRANS (@lem2320425) (@lem2320830)). Qed.
Lemma lem2320938 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2320939 (P : int -> Prop) (Q : int -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem2320938 int P Q). Qed.
Lemma lem2320940 : term247 = term248.
Proof. exact (@lem2320939 term213 term243). Qed.
Lemma lem2320941 (x : int) : (term249 x) = (term212 x).
Proof. exact (eq_refl (term249 x)). Qed.
Lemma lem2320942 : term250 = term213.
Proof. exact (fun_ext (fun x : int => @lem2320941 x)). Qed.
Lemma lem2320943 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320944 : term251 = term214.
Proof. exact (MK_COMB (@lem2320943) (@lem2320942)). Qed.
Lemma lem2320945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320946 : term252 = term245.
Proof. exact (MK_COMB (@lem2320945) (@lem2320944)). Qed.
Lemma lem2320947 (x : int) : (term253 x) = (term242 x).
Proof. exact (eq_refl (term253 x)). Qed.
Lemma lem2320948 : term254 = term243.
Proof. exact (fun_ext (fun x : int => @lem2320947 x)). Qed.
Lemma lem2320949 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320950 : term255 = term244.
Proof. exact (MK_COMB (@lem2320949) (@lem2320948)). Qed.
Lemma lem2320951 : term247 = term246.
Proof. exact (MK_COMB (@lem2320946) (@lem2320950)). Qed.
Lemma lem2320952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2320953 : term256 = term257.
Proof. exact (MK_COMB (@lem2320952) (@lem2320951)). Qed.
Lemma lem2320954 (x : int) : (term249 x) = (term212 x).
Proof. exact (eq_refl (term249 x)). Qed.
Lemma lem2320955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320956 (x : int) : (term258 x) = (term259 x).
Proof. exact (MK_COMB (@lem2320955) (@lem2320954 x)). Qed.
Lemma lem2320957 (x : int) : (term253 x) = (term242 x).
Proof. exact (eq_refl (term253 x)). Qed.
Lemma lem2320958 (x : int) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem2320956 x) (@lem2320957 x)). Qed.
Lemma lem2320959 : term262 = term263.
Proof. exact (fun_ext (fun x : int => @lem2320958 x)). Qed.
Lemma lem2320960 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320961 : term248 = term264.
Proof. exact (MK_COMB (@lem2320960) (@lem2320959)). Qed.
Lemma lem2320962 : (term247 = term248) = (term246 = term264).
Proof. exact (MK_COMB (@lem2320953) (@lem2320961)). Qed.
Lemma lem2320963 : term246 = term264.
Proof. exact (EQ_MP (@lem2320962) (@lem2320940)). Qed.
Lemma lem2320965 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2320966 (P : int -> Prop) (Q : int -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem2320965 int P Q). Qed.
Lemma lem2320967 (x : int) : (term265 x) = (term266 x).
Proof. exact (@lem2320966 (term211 x) (term241 x)). Qed.
Lemma lem2320968 (x : int) (y : int) : (term267 x y) = (term210 x y).
Proof. exact (eq_refl (term267 x y)). Qed.
Lemma lem2320969 (x : int) : (term268 x) = (term211 x).
Proof. exact (fun_ext (fun y : int => @lem2320968 x y)). Qed.
Lemma lem2320970 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320971 (x : int) : (term269 x) = (term212 x).
Proof. exact (MK_COMB (@lem2320970) (@lem2320969 x)). Qed.
Lemma lem2320972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320973 (x : int) : (term270 x) = (term259 x).
Proof. exact (MK_COMB (@lem2320972) (@lem2320971 x)). Qed.
Lemma lem2320974 (x : int) (y : int) : (term271 x y) = (term240 x y).
Proof. exact (eq_refl (term271 x y)). Qed.
Lemma lem2320975 (x : int) : (term272 x) = (term241 x).
Proof. exact (fun_ext (fun y : int => @lem2320974 x y)). Qed.
Lemma lem2320976 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320977 (x : int) : (term273 x) = (term242 x).
Proof. exact (MK_COMB (@lem2320976) (@lem2320975 x)). Qed.
Lemma lem2320978 (x : int) : (term265 x) = (term261 x).
Proof. exact (MK_COMB (@lem2320973 x) (@lem2320977 x)). Qed.
Lemma lem2320979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2320980 (x : int) : (term274 x) = (term275 x).
Proof. exact (MK_COMB (@lem2320979) (@lem2320978 x)). Qed.
Lemma lem2320981 (x : int) (y : int) : (term267 x y) = (term210 x y).
Proof. exact (eq_refl (term267 x y)). Qed.
Lemma lem2320982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2320983 (x : int) (y : int) : (term276 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem2320982) (@lem2320981 x y)). Qed.
Lemma lem2320984 (x : int) (y : int) : (term271 x y) = (term240 x y).
Proof. exact (eq_refl (term271 x y)). Qed.
Lemma lem2320985 (x : int) (y : int) : (term278 x y) = (term279 x y).
Proof. exact (MK_COMB (@lem2320983 x y) (@lem2320984 x y)). Qed.
Lemma lem2320986 (x : int) : (term280 x) = (term281 x).
Proof. exact (fun_ext (fun y : int => @lem2320985 x y)). Qed.
Lemma lem2320987 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320988 (x : int) : (term266 x) = (term282 x).
Proof. exact (MK_COMB (@lem2320987) (@lem2320986 x)). Qed.
Lemma lem2320989 (x : int) : ((term265 x) = (term266 x)) = ((term261 x) = (term282 x)).
Proof. exact (MK_COMB (@lem2320980 x) (@lem2320988 x)). Qed.
Lemma lem2320990 (x : int) : (term261 x) = (term282 x).
Proof. exact (EQ_MP (@lem2320989 x) (@lem2320967 x)). Qed.
Lemma lem2320991 : term263 = term283.
Proof. exact (fun_ext (fun x : int => @lem2320990 x)). Qed.
Lemma lem2320992 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2320993 : term264 = term284.
Proof. exact (MK_COMB (@lem2320992) (@lem2320991)). Qed.
Lemma lem2320995 : term246 = term284.
Proof. exact (TRANS (@lem2320963) (@lem2320993)). Qed.
Lemma lem2320998 : term105 = term284.
Proof. exact (TRANS (@lem2320831) (@lem2320995)). Qed.
Lemma lem2321015 (x : int) (y : int) : (term240 x y) = (term285 x y).
Proof. exact (@lem19158 (term228 x y) (term221 x y) (term236 x y)). Qed.
Lemma lem2321032 (x : int) (y : int) : (term210 x y) = (term286 x y).
Proof. exact (@lem19158 (term194 x y) (term160 x y) (term206 x y)). Qed.
Lemma lem2321033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2321034 (x : int) (y : int) : (term277 x y) = (term287 x y).
Proof. exact (MK_COMB (@lem2321033) (@lem2321032 x y)). Qed.
Lemma lem2321035 (x : int) (y : int) : (term279 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem2321034 x y) (@lem2321015 x y)). Qed.
Lemma lem2321036 (x : int) : (term281 x) = (term289 x).
Proof. exact (fun_ext (fun y : int => @lem2321035 x y)). Qed.
Lemma lem2321037 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2321038 (x : int) : (term282 x) = (term290 x).
Proof. exact (MK_COMB (@lem2321037) (@lem2321036 x)). Qed.
Lemma lem2321039 : term283 = term291.
Proof. exact (fun_ext (fun x : int => @lem2321038 x)). Qed.
Lemma lem2321040 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2321041 : term284 = term292.
Proof. exact (MK_COMB (@lem2321040) (@lem2321039)). Qed.
Lemma lem2321042 : term105 = term292.
Proof. exact (TRANS (@lem2320998) (@lem2321041)). Qed.
Lemma lem2321044 (x : real) (a : real) (y : real) (b : real) (r : real) : (term293 a x y b r) = (term294 x a y b r).
Proof. exact (proj1 (@lem1482687 x a b y (@el real) r)). Qed.
Lemma lem2321045 (x : int) (y : int) : (term194 x y) = (term295 x y).
Proof. exact (@lem2321044 (real_of_int x) (real_of_int y) (real_of_int y) term166 term159). Qed.
Lemma lem2321063 (y : int) : (term296 y) = (term297 y).
Proof. exact (@lem1982763 (real_of_int y) (term156 y) term166). Qed.
Lemma lem2321064 (y : int) : (term298 y) = (term299 y).
Proof. exact (@lem1982715 term166 (real_of_int y)). Qed.
Lemma lem2321066 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321067 : term56 = term168.
Proof. exact (@lem2321066 term57). Qed.
Lemma lem2321069 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321070 : term166 = term171.
Proof. exact (@lem2321069 term57). Qed.
Lemma lem2321071 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321072 : term300 = term301.
Proof. exact (MK_COMB (@lem2321071) (@lem2321070)). Qed.
Lemma lem2321073 : term302 = term303.
Proof. exact (MK_COMB (@lem2321072) (@lem2321067)). Qed.
Lemma lem2321074 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2321076 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321077 : term306 = term307.
Proof. exact (@lem2321076 (NUMERAL 0) term57). Qed.
Lemma lem2321078 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321079 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321080 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321079 h1) (fun h1 : term307 = True => @lem2321078)). Qed.
Lemma lem2321081 : term307 = True.
Proof. exact (EQ_MP (@lem2321080) (@lem2321078)). Qed.
Lemma lem2321082 : term306 = True.
Proof. exact (TRANS (@lem2321077) (@lem2321081)). Qed.
Lemma lem2321083 : True = term306.
Proof. exact (SYM (@lem2321082)). Qed.
Lemma lem2321084 : term306.
Proof. exact (EQ_MP (@lem2321083) (@lem0)). Qed.
Lemma lem2321085 : term309.
Proof. exact (@lem2321074 (@lem2321084)). Qed.
Lemma lem2321087 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321088 : term306 = term307.
Proof. exact (@lem2321087 (NUMERAL 0) term57). Qed.
Lemma lem2321089 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321090 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321091 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321090 h1) (fun h1 : term307 = True => @lem2321089)). Qed.
Lemma lem2321092 : term307 = True.
Proof. exact (EQ_MP (@lem2321091) (@lem2321089)). Qed.
Lemma lem2321093 : term306 = True.
Proof. exact (TRANS (@lem2321088) (@lem2321092)). Qed.
Lemma lem2321094 : True = term306.
Proof. exact (SYM (@lem2321093)). Qed.
Lemma lem2321095 : term306.
Proof. exact (EQ_MP (@lem2321094) (@lem0)). Qed.
Lemma lem2321096 : term310.
Proof. exact (@lem2321085 (@lem2321095)). Qed.
Lemma lem2321098 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321099 : term306 = term307.
Proof. exact (@lem2321098 (NUMERAL 0) term57). Qed.
Lemma lem2321100 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321101 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321102 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321101 h1) (fun h1 : term307 = True => @lem2321100)). Qed.
Lemma lem2321103 : term307 = True.
Proof. exact (EQ_MP (@lem2321102) (@lem2321100)). Qed.
Lemma lem2321104 : term306 = True.
Proof. exact (TRANS (@lem2321099) (@lem2321103)). Qed.
Lemma lem2321105 : True = term306.
Proof. exact (SYM (@lem2321104)). Qed.
Lemma lem2321106 : term306.
Proof. exact (EQ_MP (@lem2321105) (@lem0)). Qed.
Lemma lem2321107 : term311.
Proof. exact (@lem2321096 (@lem2321106)). Qed.
Lemma lem2321109 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321110 : term179 = term180.
Proof. exact (@lem2321109 term57 term57). Qed.
Lemma lem2321111 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321112 : term182 = term57.
Proof. exact (EQ_MP (@lem2321111) (@lem940073)). Qed.
Lemma lem2321113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321114 : term180 = term56.
Proof. exact (MK_COMB (@lem2321113) (@lem2321112)). Qed.
Lemma lem2321115 : term179 = term56.
Proof. exact (TRANS (@lem2321110) (@lem2321114)). Qed.
Lemma lem2321117 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2321118 : term174 = term185.
Proof. exact (@lem2321117 term57 term57). Qed.
Lemma lem2321119 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321120 : term182 = term57.
Proof. exact (EQ_MP (@lem2321119) (@lem940073)). Qed.
Lemma lem2321121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321122 : term180 = term56.
Proof. exact (MK_COMB (@lem2321121) (@lem2321120)). Qed.
Lemma lem2321123 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2321124 : term185 = term166.
Proof. exact (MK_COMB (@lem2321123) (@lem2321122)). Qed.
Lemma lem2321125 : term174 = term166.
Proof. exact (TRANS (@lem2321118) (@lem2321124)). Qed.
Lemma lem2321126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321127 : term312 = term300.
Proof. exact (MK_COMB (@lem2321126) (@lem2321125)). Qed.
Lemma lem2321128 : term313 = term302.
Proof. exact (MK_COMB (@lem2321127) (@lem2321115)). Qed.
Lemma lem2321130 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2321131 : term302 = term159.
Proof. exact (@lem2321130 term57). Qed.
Lemma lem2321132 : term313 = term159.
Proof. exact (TRANS (@lem2321128) (@lem2321131)). Qed.
Lemma lem2321133 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321134 : term315 = term316.
Proof. exact (MK_COMB (@lem2321133) (@lem2321132)). Qed.
Lemma lem2321135 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2321136 : term317 = term318.
Proof. exact (MK_COMB (@lem2321134) (@lem2321135)). Qed.
Lemma lem2321138 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2321139 : term318 = term159.
Proof. exact (@lem2321138 term57). Qed.
Lemma lem2321140 : term317 = term159.
Proof. exact (TRANS (@lem2321136) (@lem2321139)). Qed.
Lemma lem2321142 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321143 : term179 = term180.
Proof. exact (@lem2321142 term57 term57). Qed.
Lemma lem2321144 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321145 : term182 = term57.
Proof. exact (EQ_MP (@lem2321144) (@lem940073)). Qed.
Lemma lem2321146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321147 : term180 = term56.
Proof. exact (MK_COMB (@lem2321146) (@lem2321145)). Qed.
Lemma lem2321148 : term179 = term56.
Proof. exact (TRANS (@lem2321143) (@lem2321147)). Qed.
Lemma lem2321149 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2321150 : term320 = term318.
Proof. exact (MK_COMB (@lem2321149) (@lem2321148)). Qed.
Lemma lem2321152 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2321153 : term318 = term159.
Proof. exact (@lem2321152 term57). Qed.
Lemma lem2321154 : term320 = term159.
Proof. exact (TRANS (@lem2321150) (@lem2321153)). Qed.
Lemma lem2321155 : term159 = term320.
Proof. exact (SYM (@lem2321154)). Qed.
Lemma lem2321156 : term317 = term320.
Proof. exact (TRANS (@lem2321140) (@lem2321155)). Qed.
Lemma lem2321157 : term303 = term321.
Proof. exact (@lem2321107 (@lem2321156)). Qed.
Lemma lem2321158 : term302 = term321.
Proof. exact (TRANS (@lem2321073) (@lem2321157)). Qed.
Lemma lem2321160 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2321161 : term321 = term159.
Proof. exact (@lem2321160 term159). Qed.
Lemma lem2321162 : term302 = term159.
Proof. exact (TRANS (@lem2321158) (@lem2321161)). Qed.
Lemma lem2321163 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321164 : term322 = term316.
Proof. exact (MK_COMB (@lem2321163) (@lem2321162)). Qed.
Lemma lem2321165 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2321166 (y : int) : (term299 y) = (term323 y).
Proof. exact (MK_COMB (@lem2321164) (@lem2321165 y)). Qed.
Lemma lem2321167 (y : int) : (term298 y) = (term323 y).
Proof. exact (TRANS (@lem2321064 y) (@lem2321166 y)). Qed.
Lemma lem2321168 (y : int) : (term323 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2321169 (y : int) : (term298 y) = term159.
Proof. exact (TRANS (@lem2321167 y) (@lem2321168 y)). Qed.
Lemma lem2321170 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321171 (y : int) : (term324 y) = term325.
Proof. exact (MK_COMB (@lem2321170) (@lem2321169 y)). Qed.
Lemma lem2321172 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2321173 (y : int) : (term297 y) = term326.
Proof. exact (MK_COMB (@lem2321171 y) (@lem2321172)). Qed.
Lemma lem2321174 (y : int) : (term296 y) = term326.
Proof. exact (TRANS (@lem2321063 y) (@lem2321173 y)). Qed.
Lemma lem2321175 : term326 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2321177 (y : int) : (term296 y) = term166.
Proof. exact (TRANS (@lem2321174 y) (@lem2321175)). Qed.
Lemma lem2321178 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321179 (y : int) : (term327 y) = term328.
Proof. exact (MK_COMB (@lem2321178) (@lem2321177 y)). Qed.
Lemma lem2321180 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321181 (y : int) : (term329 y) = term330.
Proof. exact (MK_COMB (@lem2321179 y) (@lem2321180)). Qed.
Lemma lem2321204 (x : int) (y : int) : (term218 y x) = (term331 x y).
Proof. exact (@lem1982757 (term156 x) (real_of_int y) term166). Qed.
Lemma lem2321205 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321206 (x : int) (y : int) : (term220 y x) = (term332 x y).
Proof. exact (MK_COMB (@lem2321205) (@lem2321204 x y)). Qed.
Lemma lem2321207 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321208 (x : int) (y : int) : (term221 y x) = (term333 x y).
Proof. exact (MK_COMB (@lem2321206 x y) (@lem2321207)). Qed.
Lemma lem2321209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321210 (x : int) (y : int) : (term239 y x) = (term334 x y).
Proof. exact (MK_COMB (@lem2321209) (@lem2321208 x y)). Qed.
Lemma lem2321211 (x : int) (y : int) : (term295 x y) = (term335 x y).
Proof. exact (MK_COMB (@lem2321210 x y) (@lem2321181 y)). Qed.
Lemma lem2321212 (x : int) (y : int) : (term194 x y) = (term335 x y).
Proof. exact (TRANS (@lem2321045 x y) (@lem2321211 x y)). Qed.
Lemma lem2321213 (x : int) (y : int) : (term209 x y) = (term209 x y).
Proof. exact (eq_refl (term209 x y)). Qed.
Lemma lem2321216 (x : int) (y : int) : (term336 x y) = (term337 x y).
Proof. exact (MK_COMB (@lem2321213 x y) (@lem2321212 x y)). Qed.
Lemma lem2321218 (x : int) (y : int) : (term338 x y) = (term339 x y).
Proof. exact (eq_refl (term338 x y)). Qed.
Lemma lem2321219 (x : int) (y : int) : (term339 x y) = (term338 x y).
Proof. exact (SYM (@lem2321218 x y)). Qed.
Lemma lem2321220 (y : int) (x : int) : (term338 x y) = (term340 y x).
Proof. exact (@lem1483205 (real_of_int y) (term341 x y) (real_of_int x)). Qed.
Lemma lem2321221 (y : int) (x : int) : (term339 x y) = (term340 y x).
Proof. exact (TRANS (@lem2321219 x y) (@lem2321220 y x)). Qed.
Lemma lem2321222 (y : int) (x : int) : (term342 y x) = (term343 y x).
Proof. exact (eq_refl (term342 y x)). Qed.
Lemma lem2321223 (x : int) (y : int) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem2321224 (y : int) (x : int) : (term345 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem2321223 x y) (@lem2321222 y x)). Qed.
Lemma lem2321225 (x : int) (y : int) : (term347 x y) = (term348 x y).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem2321226 (y : int) (x : int) : (term349 y x) = (term349 y x).
Proof. exact (eq_refl (term349 y x)). Qed.
Lemma lem2321227 (x : int) (y : int) : (term350 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem2321226 y x) (@lem2321225 x y)). Qed.
Lemma lem2321228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2321229 (x : int) (y : int) : (term352 x y) = (term353 x y).
Proof. exact (MK_COMB (@lem2321228) (@lem2321227 x y)). Qed.
Lemma lem2321230 (y : int) (x : int) : (term340 y x) = (term354 y x).
Proof. exact (MK_COMB (@lem2321229 x y) (@lem2321224 y x)). Qed.
Lemma lem2321231 (x : int) (y : int) : (term355 x y) = (term355 x y).
Proof. exact (eq_refl (term355 x y)). Qed.
Lemma lem2321232 (y : int) (x : int) : ((term339 x y) = (term340 y x)) = ((term339 x y) = (term354 y x)).
Proof. exact (MK_COMB (@lem2321231 x y) (@lem2321230 y x)). Qed.
Lemma lem2321233 (y : int) (x : int) : (term339 x y) = (term354 y x).
Proof. exact (EQ_MP (@lem2321232 y x) (@lem2321221 y x)). Qed.
Lemma lem2321234 (y : int) (x : int) : (term356 y x) = (term152 y x).
Proof. exact (@lem1988291 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2321240 (y : int) (x : int) : (term153 y x) = (term154 y x).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2321245 (x : int) (y : int) : (term154 y x) = (term155 x y).
Proof. exact (@lem1982761 (term156 x) (real_of_int y)). Qed.
Lemma lem2321247 (x : int) (y : int) : (term153 y x) = (term155 x y).
Proof. exact (TRANS (@lem2321240 y x) (@lem2321245 x y)). Qed.
Lemma lem2321248 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321249 (x : int) (y : int) : (term157 y x) = (term158 x y).
Proof. exact (MK_COMB (@lem2321248) (@lem2321247 x y)). Qed.
Lemma lem2321250 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321251 (x : int) (y : int) : (term152 y x) = (term160 x y).
Proof. exact (MK_COMB (@lem2321249 x y) (@lem2321250)). Qed.
Lemma lem2321252 (x : int) (y : int) : (term356 y x) = (term160 x y).
Proof. exact (TRANS (@lem2321234 y x) (@lem2321251 x y)). Qed.
Lemma lem2321253 (x : int) (y : int) : (term160 x y) = (term357 x y).
Proof. exact (@lem1988291 (term155 x y) term159). Qed.
Lemma lem2321271 (x : int) (y : int) : (term358 x y) = (term359 x y).
Proof. exact (@lem1982792 (term155 x y) term159). Qed.
Lemma lem2321273 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321274 : term159 = term321.
Proof. exact (@lem2321273 (NUMERAL 0)). Qed.
Lemma lem2321276 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321277 : term166 = term171.
Proof. exact (@lem2321276 term57). Qed.
Lemma lem2321278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321279 : term172 = term173.
Proof. exact (MK_COMB (@lem2321278) (@lem2321277)). Qed.
Lemma lem2321280 : term360 = term361.
Proof. exact (MK_COMB (@lem2321279) (@lem2321274)). Qed.
Lemma lem2321281 : term361 = term362.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2321283 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321284 : term179 = term180.
Proof. exact (@lem2321283 term57 term57). Qed.
Lemma lem2321285 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321286 : term182 = term57.
Proof. exact (EQ_MP (@lem2321285) (@lem940073)). Qed.
Lemma lem2321287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321288 : term180 = term56.
Proof. exact (MK_COMB (@lem2321287) (@lem2321286)). Qed.
Lemma lem2321289 : term179 = term56.
Proof. exact (TRANS (@lem2321284) (@lem2321288)). Qed.
Lemma lem2321291 (x : nat) : (term363 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2321292 : term360 = term159.
Proof. exact (@lem2321291 term57). Qed.
Lemma lem2321293 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2321294 : term364 = term365.
Proof. exact (MK_COMB (@lem2321293) (@lem2321292)). Qed.
Lemma lem2321295 : term362 = term321.
Proof. exact (MK_COMB (@lem2321294) (@lem2321289)). Qed.
Lemma lem2321296 : term361 = term321.
Proof. exact (TRANS (@lem2321281) (@lem2321295)). Qed.
Lemma lem2321297 : term360 = term321.
Proof. exact (TRANS (@lem2321280) (@lem2321296)). Qed.
Lemma lem2321299 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2321300 : term321 = term159.
Proof. exact (@lem2321299 term159). Qed.
Lemma lem2321301 : term360 = term159.
Proof. exact (TRANS (@lem2321297) (@lem2321300)). Qed.
Lemma lem2321302 (x : int) (y : int) : (term366 x y) = (term366 x y).
Proof. exact (eq_refl (term366 x y)). Qed.
Lemma lem2321303 (x : int) (y : int) : (term359 x y) = (term367 x y).
Proof. exact (MK_COMB (@lem2321302 x y) (@lem2321301)). Qed.
Lemma lem2321304 (x : int) (y : int) : (term367 x y) = (term155 x y).
Proof. exact (@lem1982723 (term155 x y)). Qed.
Lemma lem2321305 (x : int) (y : int) : (term359 x y) = (term155 x y).
Proof. exact (TRANS (@lem2321303 x y) (@lem2321304 x y)). Qed.
Lemma lem2321307 (x : int) (y : int) : (term358 x y) = (term155 x y).
Proof. exact (TRANS (@lem2321271 x y) (@lem2321305 x y)). Qed.
Lemma lem2321308 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321309 (x : int) (y : int) : (term368 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem2321308) (@lem2321307 x y)). Qed.
Lemma lem2321310 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321311 (x : int) (y : int) : (term357 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem2321309 x y) (@lem2321310)). Qed.
Lemma lem2321312 (x : int) (y : int) : (term160 x y) = (term160 x y).
Proof. exact (TRANS (@lem2321253 x y) (@lem2321311 x y)). Qed.
Lemma lem2321313 (y : int) : (term369 y) = (term370 y).
Proof. exact (@lem1988291 (term371 y) term159). Qed.
Lemma lem2321314 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321332 (y : int) : (term371 y) = (term372 y).
Proof. exact (@lem1982763 (term156 y) (real_of_int y) term166). Qed.
Lemma lem2321333 (y : int) : (term373 y) = (term299 y).
Proof. exact (@lem1982713 term166 (real_of_int y)). Qed.
Lemma lem2321335 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321336 : term56 = term168.
Proof. exact (@lem2321335 term57). Qed.
Lemma lem2321338 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321339 : term166 = term171.
Proof. exact (@lem2321338 term57). Qed.
Lemma lem2321340 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321341 : term300 = term301.
Proof. exact (MK_COMB (@lem2321340) (@lem2321339)). Qed.
Lemma lem2321342 : term302 = term303.
Proof. exact (MK_COMB (@lem2321341) (@lem2321336)). Qed.
Lemma lem2321343 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2321345 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321346 : term306 = term307.
Proof. exact (@lem2321345 (NUMERAL 0) term57). Qed.
Lemma lem2321347 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321348 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321349 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321348 h1) (fun h1 : term307 = True => @lem2321347)). Qed.
Lemma lem2321350 : term307 = True.
Proof. exact (EQ_MP (@lem2321349) (@lem2321347)). Qed.
Lemma lem2321351 : term306 = True.
Proof. exact (TRANS (@lem2321346) (@lem2321350)). Qed.
Lemma lem2321352 : True = term306.
Proof. exact (SYM (@lem2321351)). Qed.
Lemma lem2321353 : term306.
Proof. exact (EQ_MP (@lem2321352) (@lem0)). Qed.
Lemma lem2321354 : term309.
Proof. exact (@lem2321343 (@lem2321353)). Qed.
Lemma lem2321356 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321357 : term306 = term307.
Proof. exact (@lem2321356 (NUMERAL 0) term57). Qed.
Lemma lem2321358 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321359 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321360 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321359 h1) (fun h1 : term307 = True => @lem2321358)). Qed.
Lemma lem2321361 : term307 = True.
Proof. exact (EQ_MP (@lem2321360) (@lem2321358)). Qed.
Lemma lem2321362 : term306 = True.
Proof. exact (TRANS (@lem2321357) (@lem2321361)). Qed.
Lemma lem2321363 : True = term306.
Proof. exact (SYM (@lem2321362)). Qed.
Lemma lem2321364 : term306.
Proof. exact (EQ_MP (@lem2321363) (@lem0)). Qed.
Lemma lem2321365 : term310.
Proof. exact (@lem2321354 (@lem2321364)). Qed.
Lemma lem2321367 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321368 : term306 = term307.
Proof. exact (@lem2321367 (NUMERAL 0) term57). Qed.
Lemma lem2321369 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321370 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321371 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321370 h1) (fun h1 : term307 = True => @lem2321369)). Qed.
Lemma lem2321372 : term307 = True.
Proof. exact (EQ_MP (@lem2321371) (@lem2321369)). Qed.
Lemma lem2321373 : term306 = True.
Proof. exact (TRANS (@lem2321368) (@lem2321372)). Qed.
Lemma lem2321374 : True = term306.
Proof. exact (SYM (@lem2321373)). Qed.
Lemma lem2321375 : term306.
Proof. exact (EQ_MP (@lem2321374) (@lem0)). Qed.
Lemma lem2321376 : term311.
Proof. exact (@lem2321365 (@lem2321375)). Qed.
Lemma lem2321378 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321379 : term179 = term180.
Proof. exact (@lem2321378 term57 term57). Qed.
Lemma lem2321380 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321381 : term182 = term57.
Proof. exact (EQ_MP (@lem2321380) (@lem940073)). Qed.
Lemma lem2321382 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321383 : term180 = term56.
Proof. exact (MK_COMB (@lem2321382) (@lem2321381)). Qed.
Lemma lem2321384 : term179 = term56.
Proof. exact (TRANS (@lem2321379) (@lem2321383)). Qed.
Lemma lem2321386 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2321387 : term174 = term185.
Proof. exact (@lem2321386 term57 term57). Qed.
Lemma lem2321388 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321389 : term182 = term57.
Proof. exact (EQ_MP (@lem2321388) (@lem940073)). Qed.
Lemma lem2321390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321391 : term180 = term56.
Proof. exact (MK_COMB (@lem2321390) (@lem2321389)). Qed.
Lemma lem2321392 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2321393 : term185 = term166.
Proof. exact (MK_COMB (@lem2321392) (@lem2321391)). Qed.
Lemma lem2321394 : term174 = term166.
Proof. exact (TRANS (@lem2321387) (@lem2321393)). Qed.
Lemma lem2321395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321396 : term312 = term300.
Proof. exact (MK_COMB (@lem2321395) (@lem2321394)). Qed.
Lemma lem2321397 : term313 = term302.
Proof. exact (MK_COMB (@lem2321396) (@lem2321384)). Qed.
Lemma lem2321399 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2321400 : term302 = term159.
Proof. exact (@lem2321399 term57). Qed.
Lemma lem2321401 : term313 = term159.
Proof. exact (TRANS (@lem2321397) (@lem2321400)). Qed.
Lemma lem2321402 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321403 : term315 = term316.
Proof. exact (MK_COMB (@lem2321402) (@lem2321401)). Qed.
Lemma lem2321404 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2321405 : term317 = term318.
Proof. exact (MK_COMB (@lem2321403) (@lem2321404)). Qed.
Lemma lem2321407 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2321408 : term318 = term159.
Proof. exact (@lem2321407 term57). Qed.
Lemma lem2321409 : term317 = term159.
Proof. exact (TRANS (@lem2321405) (@lem2321408)). Qed.
Lemma lem2321411 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321412 : term179 = term180.
Proof. exact (@lem2321411 term57 term57). Qed.
Lemma lem2321413 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321414 : term182 = term57.
Proof. exact (EQ_MP (@lem2321413) (@lem940073)). Qed.
Lemma lem2321415 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321416 : term180 = term56.
Proof. exact (MK_COMB (@lem2321415) (@lem2321414)). Qed.
Lemma lem2321417 : term179 = term56.
Proof. exact (TRANS (@lem2321412) (@lem2321416)). Qed.
Lemma lem2321418 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2321419 : term320 = term318.
Proof. exact (MK_COMB (@lem2321418) (@lem2321417)). Qed.
Lemma lem2321421 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2321422 : term318 = term159.
Proof. exact (@lem2321421 term57). Qed.
Lemma lem2321423 : term320 = term159.
Proof. exact (TRANS (@lem2321419) (@lem2321422)). Qed.
Lemma lem2321424 : term159 = term320.
Proof. exact (SYM (@lem2321423)). Qed.
Lemma lem2321425 : term317 = term320.
Proof. exact (TRANS (@lem2321409) (@lem2321424)). Qed.
Lemma lem2321426 : term303 = term321.
Proof. exact (@lem2321376 (@lem2321425)). Qed.
Lemma lem2321427 : term302 = term321.
Proof. exact (TRANS (@lem2321342) (@lem2321426)). Qed.
Lemma lem2321429 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2321430 : term321 = term159.
Proof. exact (@lem2321429 term159). Qed.
Lemma lem2321431 : term302 = term159.
Proof. exact (TRANS (@lem2321427) (@lem2321430)). Qed.
Lemma lem2321432 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321433 : term322 = term316.
Proof. exact (MK_COMB (@lem2321432) (@lem2321431)). Qed.
Lemma lem2321434 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2321435 (y : int) : (term299 y) = (term323 y).
Proof. exact (MK_COMB (@lem2321433) (@lem2321434 y)). Qed.
Lemma lem2321436 (y : int) : (term373 y) = (term323 y).
Proof. exact (TRANS (@lem2321333 y) (@lem2321435 y)). Qed.
Lemma lem2321437 (y : int) : (term323 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2321438 (y : int) : (term373 y) = term159.
Proof. exact (TRANS (@lem2321436 y) (@lem2321437 y)). Qed.
Lemma lem2321439 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321440 (y : int) : (term374 y) = term325.
Proof. exact (MK_COMB (@lem2321439) (@lem2321438 y)). Qed.
Lemma lem2321441 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2321442 (y : int) : (term372 y) = term326.
Proof. exact (MK_COMB (@lem2321440 y) (@lem2321441)). Qed.
Lemma lem2321443 (y : int) : (term371 y) = term326.
Proof. exact (TRANS (@lem2321332 y) (@lem2321442 y)). Qed.
Lemma lem2321444 : term326 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2321446 (y : int) : (term371 y) = term166.
Proof. exact (TRANS (@lem2321443 y) (@lem2321444)). Qed.
Lemma lem2321447 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2321448 (y : int) : (term375 y) = term376.
Proof. exact (MK_COMB (@lem2321447) (@lem2321446 y)). Qed.
Lemma lem2321449 (y : int) : (term377 y) = term378.
Proof. exact (MK_COMB (@lem2321448 y) (@lem2321314)). Qed.
Lemma lem2321450 : term378 = term379.
Proof. exact (@lem1982792 term166 term159). Qed.
Lemma lem2321452 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321453 : term159 = term321.
Proof. exact (@lem2321452 (NUMERAL 0)). Qed.
Lemma lem2321455 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321456 : term166 = term171.
Proof. exact (@lem2321455 term57). Qed.
Lemma lem2321457 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321458 : term172 = term173.
Proof. exact (MK_COMB (@lem2321457) (@lem2321456)). Qed.
Lemma lem2321459 : term360 = term361.
Proof. exact (MK_COMB (@lem2321458) (@lem2321453)). Qed.
Lemma lem2321460 : term361 = term362.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2321462 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321463 : term179 = term180.
Proof. exact (@lem2321462 term57 term57). Qed.
Lemma lem2321464 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321465 : term182 = term57.
Proof. exact (EQ_MP (@lem2321464) (@lem940073)). Qed.
Lemma lem2321466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321467 : term180 = term56.
Proof. exact (MK_COMB (@lem2321466) (@lem2321465)). Qed.
Lemma lem2321468 : term179 = term56.
Proof. exact (TRANS (@lem2321463) (@lem2321467)). Qed.
Lemma lem2321470 (x : nat) : (term363 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2321471 : term360 = term159.
Proof. exact (@lem2321470 term57). Qed.
Lemma lem2321472 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2321473 : term364 = term365.
Proof. exact (MK_COMB (@lem2321472) (@lem2321471)). Qed.
Lemma lem2321474 : term362 = term321.
Proof. exact (MK_COMB (@lem2321473) (@lem2321468)). Qed.
Lemma lem2321475 : term361 = term321.
Proof. exact (TRANS (@lem2321460) (@lem2321474)). Qed.
Lemma lem2321476 : term360 = term321.
Proof. exact (TRANS (@lem2321459) (@lem2321475)). Qed.
Lemma lem2321478 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2321479 : term321 = term159.
Proof. exact (@lem2321478 term159). Qed.
Lemma lem2321480 : term360 = term159.
Proof. exact (TRANS (@lem2321476) (@lem2321479)). Qed.
Lemma lem2321481 : term300 = term300.
Proof. exact (eq_refl term300). Qed.
Lemma lem2321482 : term379 = term380.
Proof. exact (MK_COMB (@lem2321481) (@lem2321480)). Qed.
Lemma lem2321483 : term380 = term166.
Proof. exact (@lem1982723 term166). Qed.
Lemma lem2321484 : term379 = term166.
Proof. exact (TRANS (@lem2321482) (@lem2321483)). Qed.
Lemma lem2321485 : term378 = term166.
Proof. exact (TRANS (@lem2321450) (@lem2321484)). Qed.
Lemma lem2321486 (y : int) : (term377 y) = term166.
Proof. exact (TRANS (@lem2321449 y) (@lem2321485)). Qed.
Lemma lem2321487 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321488 (y : int) : (term381 y) = term328.
Proof. exact (MK_COMB (@lem2321487) (@lem2321486 y)). Qed.
Lemma lem2321489 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321490 (y : int) : (term370 y) = term330.
Proof. exact (MK_COMB (@lem2321488 y) (@lem2321489)). Qed.
Lemma lem2321491 (y : int) : (term369 y) = term330.
Proof. exact (TRANS (@lem2321313 y) (@lem2321490 y)). Qed.
Lemma lem2321492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321493 (x : int) (y : int) : (term209 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem2321492) (@lem2321312 x y)). Qed.
Lemma lem2321494 (x : int) (y : int) : (term348 x y) = (term382 x y).
Proof. exact (MK_COMB (@lem2321493 x y) (@lem2321491 y)). Qed.
Lemma lem2321495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321496 (x : int) (y : int) : (term349 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem2321495) (@lem2321252 x y)). Qed.
Lemma lem2321497 (x : int) (y : int) : (term351 x y) = (term383 x y).
Proof. exact (MK_COMB (@lem2321496 x y) (@lem2321494 x y)). Qed.
Lemma lem2321498 (x : int) (y : int) : (term384 x y) = (term385 x y).
Proof. exact (@lem1988289 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2321511 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2321512 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2321513 (x : int) (y : int) : (term386 x y) = (term387 x y).
Proof. exact (MK_COMB (@lem2321512) (@lem2321511 x y)). Qed.
Lemma lem2321514 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321515 (x : int) (y : int) : (term385 x y) = (term388 x y).
Proof. exact (MK_COMB (@lem2321513 x y) (@lem2321514)). Qed.
Lemma lem2321516 (x : int) (y : int) : (term384 x y) = (term388 x y).
Proof. exact (TRANS (@lem2321498 x y) (@lem2321515 x y)). Qed.
Lemma lem2321517 (y : int) (x : int) : (term333 y x) = (term389 y x).
Proof. exact (@lem1988291 (term331 y x) term159). Qed.
Lemma lem2321518 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321541 (x : int) (y : int) : (term331 y x) = (term218 x y).
Proof. exact (@lem1982757 (real_of_int x) (term156 y) term166). Qed.
Lemma lem2321542 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2321543 (x : int) (y : int) : (term390 y x) = (term391 x y).
Proof. exact (MK_COMB (@lem2321542) (@lem2321541 x y)). Qed.
Lemma lem2321544 (x : int) (y : int) : (term392 y x) = (term393 x y).
Proof. exact (MK_COMB (@lem2321543 x y) (@lem2321518)). Qed.
Lemma lem2321545 (x : int) (y : int) : (term393 x y) = (term394 x y).
Proof. exact (@lem1982792 (term218 x y) term159). Qed.
Lemma lem2321547 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321548 : term159 = term321.
Proof. exact (@lem2321547 (NUMERAL 0)). Qed.
Lemma lem2321550 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321551 : term166 = term171.
Proof. exact (@lem2321550 term57). Qed.
Lemma lem2321552 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321553 : term172 = term173.
Proof. exact (MK_COMB (@lem2321552) (@lem2321551)). Qed.
Lemma lem2321554 : term360 = term361.
Proof. exact (MK_COMB (@lem2321553) (@lem2321548)). Qed.
Lemma lem2321555 : term361 = term362.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2321557 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321558 : term179 = term180.
Proof. exact (@lem2321557 term57 term57). Qed.
Lemma lem2321559 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321560 : term182 = term57.
Proof. exact (EQ_MP (@lem2321559) (@lem940073)). Qed.
Lemma lem2321561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321562 : term180 = term56.
Proof. exact (MK_COMB (@lem2321561) (@lem2321560)). Qed.
Lemma lem2321563 : term179 = term56.
Proof. exact (TRANS (@lem2321558) (@lem2321562)). Qed.
Lemma lem2321565 (x : nat) : (term363 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2321566 : term360 = term159.
Proof. exact (@lem2321565 term57). Qed.
Lemma lem2321567 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2321568 : term364 = term365.
Proof. exact (MK_COMB (@lem2321567) (@lem2321566)). Qed.
Lemma lem2321569 : term362 = term321.
Proof. exact (MK_COMB (@lem2321568) (@lem2321563)). Qed.
Lemma lem2321570 : term361 = term321.
Proof. exact (TRANS (@lem2321555) (@lem2321569)). Qed.
Lemma lem2321571 : term360 = term321.
Proof. exact (TRANS (@lem2321554) (@lem2321570)). Qed.
Lemma lem2321573 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2321574 : term321 = term159.
Proof. exact (@lem2321573 term159). Qed.
Lemma lem2321575 : term360 = term159.
Proof. exact (TRANS (@lem2321571) (@lem2321574)). Qed.
Lemma lem2321576 (x : int) (y : int) : (term395 x y) = (term395 x y).
Proof. exact (eq_refl (term395 x y)). Qed.
Lemma lem2321577 (x : int) (y : int) : (term394 x y) = (term396 x y).
Proof. exact (MK_COMB (@lem2321576 x y) (@lem2321575)). Qed.
Lemma lem2321578 (x : int) (y : int) : (term396 x y) = (term218 x y).
Proof. exact (@lem1982723 (term218 x y)). Qed.
Lemma lem2321579 (x : int) (y : int) : (term394 x y) = (term218 x y).
Proof. exact (TRANS (@lem2321577 x y) (@lem2321578 x y)). Qed.
Lemma lem2321580 (x : int) (y : int) : (term393 x y) = (term218 x y).
Proof. exact (TRANS (@lem2321545 x y) (@lem2321579 x y)). Qed.
Lemma lem2321581 (x : int) (y : int) : (term392 y x) = (term218 x y).
Proof. exact (TRANS (@lem2321544 x y) (@lem2321580 x y)). Qed.
Lemma lem2321582 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321583 (x : int) (y : int) : (term397 y x) = (term220 x y).
Proof. exact (MK_COMB (@lem2321582) (@lem2321581 x y)). Qed.
Lemma lem2321584 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321585 (x : int) (y : int) : (term389 y x) = (term221 x y).
Proof. exact (MK_COMB (@lem2321583 x y) (@lem2321584)). Qed.
Lemma lem2321586 (x : int) (y : int) : (term333 y x) = (term221 x y).
Proof. exact (TRANS (@lem2321517 y x) (@lem2321585 x y)). Qed.
Lemma lem2321587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321588 (x : int) (y : int) : (term209 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem2321587) (@lem2321312 x y)). Qed.
Lemma lem2321589 (x : int) (y : int) : (term343 y x) = (term398 x y).
Proof. exact (MK_COMB (@lem2321588 x y) (@lem2321586 x y)). Qed.
Lemma lem2321590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321591 (x : int) (y : int) : (term344 x y) = (term399 x y).
Proof. exact (MK_COMB (@lem2321590) (@lem2321516 x y)). Qed.
Lemma lem2321592 (x : int) (y : int) : (term346 y x) = (term400 x y).
Proof. exact (MK_COMB (@lem2321591 x y) (@lem2321589 x y)). Qed.
Lemma lem2321593 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2321594 (x : int) (y : int) : (term353 x y) = (term401 x y).
Proof. exact (MK_COMB (@lem2321593) (@lem2321497 x y)). Qed.
Lemma lem2321595 (x : int) (y : int) : (term354 y x) = (term402 x y).
Proof. exact (MK_COMB (@lem2321594 x y) (@lem2321592 x y)). Qed.
Lemma lem2321607 (x : int) (y : int) : (term339 x y) = (term402 x y).
Proof. exact (TRANS (@lem2321233 y x) (@lem2321595 x y)). Qed.
Lemma lem2321608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2321609 (x : int) (y : int) : (term403 x y) = (term404 x y).
Proof. exact (MK_COMB (@lem2321608) (@lem2321216 x y)). Qed.
Lemma lem2321610 (x : int) (y : int) : (term286 x y) = (term405 x y).
Proof. exact (MK_COMB (@lem2321609 x y) (@lem2321607 x y)). Qed.
Lemma lem2321612 (x : real) (a : real) (y : real) (b : real) (r : real) : (term293 a x y b r) = (term294 x a y b r).
Proof. exact (proj1 (@lem1482687 x a b y (@el real) r)). Qed.
Lemma lem2321613 (x : int) (y : int) : (term228 x y) = (term406 x y).
Proof. exact (@lem2321612 (real_of_int x) (real_of_int x) (real_of_int y) term166 term159). Qed.
Lemma lem2321636 (x : int) (y : int) : (term221 x y) = (term221 x y).
Proof. exact (eq_refl (term221 x y)). Qed.
Lemma lem2321654 (x : int) : (term296 x) = (term297 x).
Proof. exact (@lem1982763 (real_of_int x) (term156 x) term166). Qed.
Lemma lem2321655 (x : int) : (term298 x) = (term299 x).
Proof. exact (@lem1982715 term166 (real_of_int x)). Qed.
Lemma lem2321657 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321658 : term56 = term168.
Proof. exact (@lem2321657 term57). Qed.
Lemma lem2321660 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321661 : term166 = term171.
Proof. exact (@lem2321660 term57). Qed.
Lemma lem2321662 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321663 : term300 = term301.
Proof. exact (MK_COMB (@lem2321662) (@lem2321661)). Qed.
Lemma lem2321664 : term302 = term303.
Proof. exact (MK_COMB (@lem2321663) (@lem2321658)). Qed.
Lemma lem2321665 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2321667 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321668 : term306 = term307.
Proof. exact (@lem2321667 (NUMERAL 0) term57). Qed.
Lemma lem2321669 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321670 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321671 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321670 h1) (fun h1 : term307 = True => @lem2321669)). Qed.
Lemma lem2321672 : term307 = True.
Proof. exact (EQ_MP (@lem2321671) (@lem2321669)). Qed.
Lemma lem2321673 : term306 = True.
Proof. exact (TRANS (@lem2321668) (@lem2321672)). Qed.
Lemma lem2321674 : True = term306.
Proof. exact (SYM (@lem2321673)). Qed.
Lemma lem2321675 : term306.
Proof. exact (EQ_MP (@lem2321674) (@lem0)). Qed.
Lemma lem2321676 : term309.
Proof. exact (@lem2321665 (@lem2321675)). Qed.
Lemma lem2321678 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321679 : term306 = term307.
Proof. exact (@lem2321678 (NUMERAL 0) term57). Qed.
Lemma lem2321680 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321681 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321682 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321681 h1) (fun h1 : term307 = True => @lem2321680)). Qed.
Lemma lem2321683 : term307 = True.
Proof. exact (EQ_MP (@lem2321682) (@lem2321680)). Qed.
Lemma lem2321684 : term306 = True.
Proof. exact (TRANS (@lem2321679) (@lem2321683)). Qed.
Lemma lem2321685 : True = term306.
Proof. exact (SYM (@lem2321684)). Qed.
Lemma lem2321686 : term306.
Proof. exact (EQ_MP (@lem2321685) (@lem0)). Qed.
Lemma lem2321687 : term310.
Proof. exact (@lem2321676 (@lem2321686)). Qed.
Lemma lem2321689 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321690 : term306 = term307.
Proof. exact (@lem2321689 (NUMERAL 0) term57). Qed.
Lemma lem2321691 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321692 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321693 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321692 h1) (fun h1 : term307 = True => @lem2321691)). Qed.
Lemma lem2321694 : term307 = True.
Proof. exact (EQ_MP (@lem2321693) (@lem2321691)). Qed.
Lemma lem2321695 : term306 = True.
Proof. exact (TRANS (@lem2321690) (@lem2321694)). Qed.
Lemma lem2321696 : True = term306.
Proof. exact (SYM (@lem2321695)). Qed.
Lemma lem2321697 : term306.
Proof. exact (EQ_MP (@lem2321696) (@lem0)). Qed.
Lemma lem2321698 : term311.
Proof. exact (@lem2321687 (@lem2321697)). Qed.
Lemma lem2321700 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321701 : term179 = term180.
Proof. exact (@lem2321700 term57 term57). Qed.
Lemma lem2321702 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321703 : term182 = term57.
Proof. exact (EQ_MP (@lem2321702) (@lem940073)). Qed.
Lemma lem2321704 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321705 : term180 = term56.
Proof. exact (MK_COMB (@lem2321704) (@lem2321703)). Qed.
Lemma lem2321706 : term179 = term56.
Proof. exact (TRANS (@lem2321701) (@lem2321705)). Qed.
Lemma lem2321708 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2321709 : term174 = term185.
Proof. exact (@lem2321708 term57 term57). Qed.
Lemma lem2321710 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321711 : term182 = term57.
Proof. exact (EQ_MP (@lem2321710) (@lem940073)). Qed.
Lemma lem2321712 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321713 : term180 = term56.
Proof. exact (MK_COMB (@lem2321712) (@lem2321711)). Qed.
Lemma lem2321714 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2321715 : term185 = term166.
Proof. exact (MK_COMB (@lem2321714) (@lem2321713)). Qed.
Lemma lem2321716 : term174 = term166.
Proof. exact (TRANS (@lem2321709) (@lem2321715)). Qed.
Lemma lem2321717 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321718 : term312 = term300.
Proof. exact (MK_COMB (@lem2321717) (@lem2321716)). Qed.
Lemma lem2321719 : term313 = term302.
Proof. exact (MK_COMB (@lem2321718) (@lem2321706)). Qed.
Lemma lem2321721 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2321722 : term302 = term159.
Proof. exact (@lem2321721 term57). Qed.
Lemma lem2321723 : term313 = term159.
Proof. exact (TRANS (@lem2321719) (@lem2321722)). Qed.
Lemma lem2321724 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321725 : term315 = term316.
Proof. exact (MK_COMB (@lem2321724) (@lem2321723)). Qed.
Lemma lem2321726 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2321727 : term317 = term318.
Proof. exact (MK_COMB (@lem2321725) (@lem2321726)). Qed.
Lemma lem2321729 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2321730 : term318 = term159.
Proof. exact (@lem2321729 term57). Qed.
Lemma lem2321731 : term317 = term159.
Proof. exact (TRANS (@lem2321727) (@lem2321730)). Qed.
Lemma lem2321733 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321734 : term179 = term180.
Proof. exact (@lem2321733 term57 term57). Qed.
Lemma lem2321735 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321736 : term182 = term57.
Proof. exact (EQ_MP (@lem2321735) (@lem940073)). Qed.
Lemma lem2321737 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321738 : term180 = term56.
Proof. exact (MK_COMB (@lem2321737) (@lem2321736)). Qed.
Lemma lem2321739 : term179 = term56.
Proof. exact (TRANS (@lem2321734) (@lem2321738)). Qed.
Lemma lem2321740 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2321741 : term320 = term318.
Proof. exact (MK_COMB (@lem2321740) (@lem2321739)). Qed.
Lemma lem2321743 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2321744 : term318 = term159.
Proof. exact (@lem2321743 term57). Qed.
Lemma lem2321745 : term320 = term159.
Proof. exact (TRANS (@lem2321741) (@lem2321744)). Qed.
Lemma lem2321746 : term159 = term320.
Proof. exact (SYM (@lem2321745)). Qed.
Lemma lem2321747 : term317 = term320.
Proof. exact (TRANS (@lem2321731) (@lem2321746)). Qed.
Lemma lem2321748 : term303 = term321.
Proof. exact (@lem2321698 (@lem2321747)). Qed.
Lemma lem2321749 : term302 = term321.
Proof. exact (TRANS (@lem2321664) (@lem2321748)). Qed.
Lemma lem2321751 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2321752 : term321 = term159.
Proof. exact (@lem2321751 term159). Qed.
Lemma lem2321753 : term302 = term159.
Proof. exact (TRANS (@lem2321749) (@lem2321752)). Qed.
Lemma lem2321754 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321755 : term322 = term316.
Proof. exact (MK_COMB (@lem2321754) (@lem2321753)). Qed.
Lemma lem2321756 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2321757 (x : int) : (term299 x) = (term323 x).
Proof. exact (MK_COMB (@lem2321755) (@lem2321756 x)). Qed.
Lemma lem2321758 (x : int) : (term298 x) = (term323 x).
Proof. exact (TRANS (@lem2321655 x) (@lem2321757 x)). Qed.
Lemma lem2321759 (x : int) : (term323 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2321760 (x : int) : (term298 x) = term159.
Proof. exact (TRANS (@lem2321758 x) (@lem2321759 x)). Qed.
Lemma lem2321761 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321762 (x : int) : (term324 x) = term325.
Proof. exact (MK_COMB (@lem2321761) (@lem2321760 x)). Qed.
Lemma lem2321763 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2321764 (x : int) : (term297 x) = term326.
Proof. exact (MK_COMB (@lem2321762 x) (@lem2321763)). Qed.
Lemma lem2321765 (x : int) : (term296 x) = term326.
Proof. exact (TRANS (@lem2321654 x) (@lem2321764 x)). Qed.
Lemma lem2321766 : term326 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2321768 (x : int) : (term296 x) = term166.
Proof. exact (TRANS (@lem2321765 x) (@lem2321766)). Qed.
Lemma lem2321769 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321770 (x : int) : (term327 x) = term328.
Proof. exact (MK_COMB (@lem2321769) (@lem2321768 x)). Qed.
Lemma lem2321771 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321772 (x : int) : (term329 x) = term330.
Proof. exact (MK_COMB (@lem2321770 x) (@lem2321771)). Qed.
Lemma lem2321773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321774 (x : int) : (term407 x) = term408.
Proof. exact (MK_COMB (@lem2321773) (@lem2321772 x)). Qed.
Lemma lem2321775 (x : int) (y : int) : (term406 x y) = (term409 x y).
Proof. exact (MK_COMB (@lem2321774 x) (@lem2321636 x y)). Qed.
Lemma lem2321776 (x : int) (y : int) : (term228 x y) = (term409 x y).
Proof. exact (TRANS (@lem2321613 x y) (@lem2321775 x y)). Qed.
Lemma lem2321777 (x : int) (y : int) : (term239 x y) = (term239 x y).
Proof. exact (eq_refl (term239 x y)). Qed.
Lemma lem2321780 (x : int) (y : int) : (term410 x y) = (term411 x y).
Proof. exact (MK_COMB (@lem2321777 x y) (@lem2321776 x y)). Qed.
Lemma lem2321782 (x : int) (y : int) : (term412 x y) = (term413 x y).
Proof. exact (eq_refl (term412 x y)). Qed.
Lemma lem2321783 (x : int) (y : int) : (term413 x y) = (term412 x y).
Proof. exact (SYM (@lem2321782 x y)). Qed.
Lemma lem2321784 (y : int) (x : int) : (term412 x y) = (term414 y x).
Proof. exact (@lem1483205 (real_of_int y) (term415 y x) (real_of_int x)). Qed.
Lemma lem2321785 (y : int) (x : int) : (term413 x y) = (term414 y x).
Proof. exact (TRANS (@lem2321783 x y) (@lem2321784 y x)). Qed.
Lemma lem2321786 (y : int) (x : int) : (term416 y x) = (term417 y x).
Proof. exact (eq_refl (term416 y x)). Qed.
Lemma lem2321787 (x : int) (y : int) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem2321788 (y : int) (x : int) : (term418 y x) = (term419 y x).
Proof. exact (MK_COMB (@lem2321787 x y) (@lem2321786 y x)). Qed.
Lemma lem2321789 (x : int) (y : int) : (term420 x y) = (term421 x y).
Proof. exact (eq_refl (term420 x y)). Qed.
Lemma lem2321790 (y : int) (x : int) : (term349 y x) = (term349 y x).
Proof. exact (eq_refl (term349 y x)). Qed.
Lemma lem2321791 (x : int) (y : int) : (term422 x y) = (term423 x y).
Proof. exact (MK_COMB (@lem2321790 y x) (@lem2321789 x y)). Qed.
Lemma lem2321792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2321793 (x : int) (y : int) : (term424 x y) = (term425 x y).
Proof. exact (MK_COMB (@lem2321792) (@lem2321791 x y)). Qed.
Lemma lem2321794 (y : int) (x : int) : (term414 y x) = (term426 y x).
Proof. exact (MK_COMB (@lem2321793 x y) (@lem2321788 y x)). Qed.
Lemma lem2321795 (x : int) (y : int) : (term427 x y) = (term427 x y).
Proof. exact (eq_refl (term427 x y)). Qed.
Lemma lem2321796 (y : int) (x : int) : ((term413 x y) = (term414 y x)) = ((term413 x y) = (term426 y x)).
Proof. exact (MK_COMB (@lem2321795 x y) (@lem2321794 y x)). Qed.
Lemma lem2321797 (y : int) (x : int) : (term413 x y) = (term426 y x).
Proof. exact (EQ_MP (@lem2321796 y x) (@lem2321785 y x)). Qed.
Lemma lem2321798 (x : int) (y : int) : (term221 x y) = (term428 x y).
Proof. exact (@lem1988291 (term218 x y) term159). Qed.
Lemma lem2321822 (x : int) (y : int) : (term393 x y) = (term394 x y).
Proof. exact (@lem1982792 (term218 x y) term159). Qed.
Lemma lem2321824 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321825 : term159 = term321.
Proof. exact (@lem2321824 (NUMERAL 0)). Qed.
Lemma lem2321827 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321828 : term166 = term171.
Proof. exact (@lem2321827 term57). Qed.
Lemma lem2321829 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321830 : term172 = term173.
Proof. exact (MK_COMB (@lem2321829) (@lem2321828)). Qed.
Lemma lem2321831 : term360 = term361.
Proof. exact (MK_COMB (@lem2321830) (@lem2321825)). Qed.
Lemma lem2321832 : term361 = term362.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2321834 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321835 : term179 = term180.
Proof. exact (@lem2321834 term57 term57). Qed.
Lemma lem2321836 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321837 : term182 = term57.
Proof. exact (EQ_MP (@lem2321836) (@lem940073)). Qed.
Lemma lem2321838 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321839 : term180 = term56.
Proof. exact (MK_COMB (@lem2321838) (@lem2321837)). Qed.
Lemma lem2321840 : term179 = term56.
Proof. exact (TRANS (@lem2321835) (@lem2321839)). Qed.
Lemma lem2321842 (x : nat) : (term363 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2321843 : term360 = term159.
Proof. exact (@lem2321842 term57). Qed.
Lemma lem2321844 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2321845 : term364 = term365.
Proof. exact (MK_COMB (@lem2321844) (@lem2321843)). Qed.
Lemma lem2321846 : term362 = term321.
Proof. exact (MK_COMB (@lem2321845) (@lem2321840)). Qed.
Lemma lem2321847 : term361 = term321.
Proof. exact (TRANS (@lem2321832) (@lem2321846)). Qed.
Lemma lem2321848 : term360 = term321.
Proof. exact (TRANS (@lem2321831) (@lem2321847)). Qed.
Lemma lem2321850 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2321851 : term321 = term159.
Proof. exact (@lem2321850 term159). Qed.
Lemma lem2321852 : term360 = term159.
Proof. exact (TRANS (@lem2321848) (@lem2321851)). Qed.
Lemma lem2321853 (x : int) (y : int) : (term395 x y) = (term395 x y).
Proof. exact (eq_refl (term395 x y)). Qed.
Lemma lem2321854 (x : int) (y : int) : (term394 x y) = (term396 x y).
Proof. exact (MK_COMB (@lem2321853 x y) (@lem2321852)). Qed.
Lemma lem2321855 (x : int) (y : int) : (term396 x y) = (term218 x y).
Proof. exact (@lem1982723 (term218 x y)). Qed.
Lemma lem2321856 (x : int) (y : int) : (term394 x y) = (term218 x y).
Proof. exact (TRANS (@lem2321854 x y) (@lem2321855 x y)). Qed.
Lemma lem2321858 (x : int) (y : int) : (term393 x y) = (term218 x y).
Proof. exact (TRANS (@lem2321822 x y) (@lem2321856 x y)). Qed.
Lemma lem2321859 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321860 (x : int) (y : int) : (term429 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem2321859) (@lem2321858 x y)). Qed.
Lemma lem2321861 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321862 (x : int) (y : int) : (term428 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem2321860 x y) (@lem2321861)). Qed.
Lemma lem2321863 (x : int) (y : int) : (term221 x y) = (term221 x y).
Proof. exact (TRANS (@lem2321798 x y) (@lem2321862 x y)). Qed.
Lemma lem2321864 (x : int) (y : int) : (term333 x y) = (term389 x y).
Proof. exact (@lem1988291 (term331 x y) term159). Qed.
Lemma lem2321888 (x : int) (y : int) : (term392 x y) = (term430 x y).
Proof. exact (@lem1982792 (term331 x y) term159). Qed.
Lemma lem2321890 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321891 : term159 = term321.
Proof. exact (@lem2321890 (NUMERAL 0)). Qed.
Lemma lem2321893 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321894 : term166 = term171.
Proof. exact (@lem2321893 term57). Qed.
Lemma lem2321895 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2321896 : term172 = term173.
Proof. exact (MK_COMB (@lem2321895) (@lem2321894)). Qed.
Lemma lem2321897 : term360 = term361.
Proof. exact (MK_COMB (@lem2321896) (@lem2321891)). Qed.
Lemma lem2321898 : term361 = term362.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2321900 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2321901 : term179 = term180.
Proof. exact (@lem2321900 term57 term57). Qed.
Lemma lem2321902 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2321903 : term182 = term57.
Proof. exact (EQ_MP (@lem2321902) (@lem940073)). Qed.
Lemma lem2321904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2321905 : term180 = term56.
Proof. exact (MK_COMB (@lem2321904) (@lem2321903)). Qed.
Lemma lem2321906 : term179 = term56.
Proof. exact (TRANS (@lem2321901) (@lem2321905)). Qed.
Lemma lem2321908 (x : nat) : (term363 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2321909 : term360 = term159.
Proof. exact (@lem2321908 term57). Qed.
Lemma lem2321910 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2321911 : term364 = term365.
Proof. exact (MK_COMB (@lem2321910) (@lem2321909)). Qed.
Lemma lem2321912 : term362 = term321.
Proof. exact (MK_COMB (@lem2321911) (@lem2321906)). Qed.
Lemma lem2321913 : term361 = term321.
Proof. exact (TRANS (@lem2321898) (@lem2321912)). Qed.
Lemma lem2321914 : term360 = term321.
Proof. exact (TRANS (@lem2321897) (@lem2321913)). Qed.
Lemma lem2321916 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2321917 : term321 = term159.
Proof. exact (@lem2321916 term159). Qed.
Lemma lem2321918 : term360 = term159.
Proof. exact (TRANS (@lem2321914) (@lem2321917)). Qed.
Lemma lem2321919 (x : int) (y : int) : (term431 x y) = (term431 x y).
Proof. exact (eq_refl (term431 x y)). Qed.
Lemma lem2321920 (x : int) (y : int) : (term430 x y) = (term432 x y).
Proof. exact (MK_COMB (@lem2321919 x y) (@lem2321918)). Qed.
Lemma lem2321921 (x : int) (y : int) : (term432 x y) = (term331 x y).
Proof. exact (@lem1982723 (term331 x y)). Qed.
Lemma lem2321922 (x : int) (y : int) : (term430 x y) = (term331 x y).
Proof. exact (TRANS (@lem2321920 x y) (@lem2321921 x y)). Qed.
Lemma lem2321924 (x : int) (y : int) : (term392 x y) = (term331 x y).
Proof. exact (TRANS (@lem2321888 x y) (@lem2321922 x y)). Qed.
Lemma lem2321925 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2321926 (x : int) (y : int) : (term397 x y) = (term332 x y).
Proof. exact (MK_COMB (@lem2321925) (@lem2321924 x y)). Qed.
Lemma lem2321927 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321928 (x : int) (y : int) : (term389 x y) = (term333 x y).
Proof. exact (MK_COMB (@lem2321926 x y) (@lem2321927)). Qed.
Lemma lem2321929 (x : int) (y : int) : (term333 x y) = (term333 x y).
Proof. exact (TRANS (@lem2321864 x y) (@lem2321928 x y)). Qed.
Lemma lem2321930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321931 (x : int) (y : int) : (term239 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem2321930) (@lem2321863 x y)). Qed.
Lemma lem2321932 (x : int) (y : int) : (term421 x y) = (term421 x y).
Proof. exact (MK_COMB (@lem2321931 x y) (@lem2321929 x y)). Qed.
Lemma lem2321933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2321934 (x : int) (y : int) : (term349 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem2321933) (@lem2321252 x y)). Qed.
Lemma lem2321935 (x : int) (y : int) : (term423 x y) = (term433 x y).
Proof. exact (MK_COMB (@lem2321934 x y) (@lem2321932 x y)). Qed.
Lemma lem2321936 (x : int) : (term369 x) = (term370 x).
Proof. exact (@lem1988291 (term371 x) term159). Qed.
Lemma lem2321937 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2321955 (x : int) : (term371 x) = (term372 x).
Proof. exact (@lem1982763 (term156 x) (real_of_int x) term166). Qed.
Lemma lem2321956 (x : int) : (term373 x) = (term299 x).
Proof. exact (@lem1982713 term166 (real_of_int x)). Qed.
Lemma lem2321958 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2321959 : term56 = term168.
Proof. exact (@lem2321958 term57). Qed.
Lemma lem2321961 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2321962 : term166 = term171.
Proof. exact (@lem2321961 term57). Qed.
Lemma lem2321963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2321964 : term300 = term301.
Proof. exact (MK_COMB (@lem2321963) (@lem2321962)). Qed.
Lemma lem2321965 : term302 = term303.
Proof. exact (MK_COMB (@lem2321964) (@lem2321959)). Qed.
Lemma lem2321966 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2321968 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321969 : term306 = term307.
Proof. exact (@lem2321968 (NUMERAL 0) term57). Qed.
Lemma lem2321970 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321971 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321972 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321971 h1) (fun h1 : term307 = True => @lem2321970)). Qed.
Lemma lem2321973 : term307 = True.
Proof. exact (EQ_MP (@lem2321972) (@lem2321970)). Qed.
Lemma lem2321974 : term306 = True.
Proof. exact (TRANS (@lem2321969) (@lem2321973)). Qed.
Lemma lem2321975 : True = term306.
Proof. exact (SYM (@lem2321974)). Qed.
Lemma lem2321976 : term306.
Proof. exact (EQ_MP (@lem2321975) (@lem0)). Qed.
Lemma lem2321977 : term309.
Proof. exact (@lem2321966 (@lem2321976)). Qed.
Lemma lem2321979 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321980 : term306 = term307.
Proof. exact (@lem2321979 (NUMERAL 0) term57). Qed.
Lemma lem2321981 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321982 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321983 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321982 h1) (fun h1 : term307 = True => @lem2321981)). Qed.
Lemma lem2321984 : term307 = True.
Proof. exact (EQ_MP (@lem2321983) (@lem2321981)). Qed.
Lemma lem2321985 : term306 = True.
Proof. exact (TRANS (@lem2321980) (@lem2321984)). Qed.
Lemma lem2321986 : True = term306.
Proof. exact (SYM (@lem2321985)). Qed.
Lemma lem2321987 : term306.
Proof. exact (EQ_MP (@lem2321986) (@lem0)). Qed.
Lemma lem2321988 : term310.
Proof. exact (@lem2321977 (@lem2321987)). Qed.
Lemma lem2321990 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2321991 : term306 = term307.
Proof. exact (@lem2321990 (NUMERAL 0) term57). Qed.
Lemma lem2321992 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2321993 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2321994 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2321993 h1) (fun h1 : term307 = True => @lem2321992)). Qed.
Lemma lem2321995 : term307 = True.
Proof. exact (EQ_MP (@lem2321994) (@lem2321992)). Qed.
Lemma lem2321996 : term306 = True.
Proof. exact (TRANS (@lem2321991) (@lem2321995)). Qed.
Lemma lem2321997 : True = term306.
Proof. exact (SYM (@lem2321996)). Qed.
Lemma lem2321998 : term306.
Proof. exact (EQ_MP (@lem2321997) (@lem0)). Qed.
Lemma lem2321999 : term311.
Proof. exact (@lem2321988 (@lem2321998)). Qed.
Lemma lem2322001 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322002 : term179 = term180.
Proof. exact (@lem2322001 term57 term57). Qed.
Lemma lem2322003 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322004 : term182 = term57.
Proof. exact (EQ_MP (@lem2322003) (@lem940073)). Qed.
Lemma lem2322005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322006 : term180 = term56.
Proof. exact (MK_COMB (@lem2322005) (@lem2322004)). Qed.
Lemma lem2322007 : term179 = term56.
Proof. exact (TRANS (@lem2322002) (@lem2322006)). Qed.
Lemma lem2322009 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2322010 : term174 = term185.
Proof. exact (@lem2322009 term57 term57). Qed.
Lemma lem2322011 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322012 : term182 = term57.
Proof. exact (EQ_MP (@lem2322011) (@lem940073)). Qed.
Lemma lem2322013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322014 : term180 = term56.
Proof. exact (MK_COMB (@lem2322013) (@lem2322012)). Qed.
Lemma lem2322015 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2322016 : term185 = term166.
Proof. exact (MK_COMB (@lem2322015) (@lem2322014)). Qed.
Lemma lem2322017 : term174 = term166.
Proof. exact (TRANS (@lem2322010) (@lem2322016)). Qed.
Lemma lem2322018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322019 : term312 = term300.
Proof. exact (MK_COMB (@lem2322018) (@lem2322017)). Qed.
Lemma lem2322020 : term313 = term302.
Proof. exact (MK_COMB (@lem2322019) (@lem2322007)). Qed.
Lemma lem2322022 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2322023 : term302 = term159.
Proof. exact (@lem2322022 term57). Qed.
Lemma lem2322024 : term313 = term159.
Proof. exact (TRANS (@lem2322020) (@lem2322023)). Qed.
Lemma lem2322025 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2322026 : term315 = term316.
Proof. exact (MK_COMB (@lem2322025) (@lem2322024)). Qed.
Lemma lem2322027 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2322028 : term317 = term318.
Proof. exact (MK_COMB (@lem2322026) (@lem2322027)). Qed.
Lemma lem2322030 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322031 : term318 = term159.
Proof. exact (@lem2322030 term57). Qed.
Lemma lem2322032 : term317 = term159.
Proof. exact (TRANS (@lem2322028) (@lem2322031)). Qed.
Lemma lem2322034 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322035 : term179 = term180.
Proof. exact (@lem2322034 term57 term57). Qed.
Lemma lem2322036 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322037 : term182 = term57.
Proof. exact (EQ_MP (@lem2322036) (@lem940073)). Qed.
Lemma lem2322038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322039 : term180 = term56.
Proof. exact (MK_COMB (@lem2322038) (@lem2322037)). Qed.
Lemma lem2322040 : term179 = term56.
Proof. exact (TRANS (@lem2322035) (@lem2322039)). Qed.
Lemma lem2322041 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2322042 : term320 = term318.
Proof. exact (MK_COMB (@lem2322041) (@lem2322040)). Qed.
Lemma lem2322044 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322045 : term318 = term159.
Proof. exact (@lem2322044 term57). Qed.
Lemma lem2322046 : term320 = term159.
Proof. exact (TRANS (@lem2322042) (@lem2322045)). Qed.
Lemma lem2322047 : term159 = term320.
Proof. exact (SYM (@lem2322046)). Qed.
Lemma lem2322048 : term317 = term320.
Proof. exact (TRANS (@lem2322032) (@lem2322047)). Qed.
Lemma lem2322049 : term303 = term321.
Proof. exact (@lem2321999 (@lem2322048)). Qed.
Lemma lem2322050 : term302 = term321.
Proof. exact (TRANS (@lem2321965) (@lem2322049)). Qed.
Lemma lem2322052 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2322053 : term321 = term159.
Proof. exact (@lem2322052 term159). Qed.
Lemma lem2322054 : term302 = term159.
Proof. exact (TRANS (@lem2322050) (@lem2322053)). Qed.
Lemma lem2322055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2322056 : term322 = term316.
Proof. exact (MK_COMB (@lem2322055) (@lem2322054)). Qed.
Lemma lem2322057 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2322058 (x : int) : (term299 x) = (term323 x).
Proof. exact (MK_COMB (@lem2322056) (@lem2322057 x)). Qed.
Lemma lem2322059 (x : int) : (term373 x) = (term323 x).
Proof. exact (TRANS (@lem2321956 x) (@lem2322058 x)). Qed.
Lemma lem2322060 (x : int) : (term323 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2322061 (x : int) : (term373 x) = term159.
Proof. exact (TRANS (@lem2322059 x) (@lem2322060 x)). Qed.
Lemma lem2322062 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322063 (x : int) : (term374 x) = term325.
Proof. exact (MK_COMB (@lem2322062) (@lem2322061 x)). Qed.
Lemma lem2322064 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2322065 (x : int) : (term372 x) = term326.
Proof. exact (MK_COMB (@lem2322063 x) (@lem2322064)). Qed.
Lemma lem2322066 (x : int) : (term371 x) = term326.
Proof. exact (TRANS (@lem2321955 x) (@lem2322065 x)). Qed.
Lemma lem2322067 : term326 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2322069 (x : int) : (term371 x) = term166.
Proof. exact (TRANS (@lem2322066 x) (@lem2322067)). Qed.
Lemma lem2322070 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2322071 (x : int) : (term375 x) = term376.
Proof. exact (MK_COMB (@lem2322070) (@lem2322069 x)). Qed.
Lemma lem2322072 (x : int) : (term377 x) = term378.
Proof. exact (MK_COMB (@lem2322071 x) (@lem2321937)). Qed.
Lemma lem2322073 : term378 = term379.
Proof. exact (@lem1982792 term166 term159). Qed.
Lemma lem2322075 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322076 : term159 = term321.
Proof. exact (@lem2322075 (NUMERAL 0)). Qed.
Lemma lem2322078 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2322079 : term166 = term171.
Proof. exact (@lem2322078 term57). Qed.
Lemma lem2322080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2322081 : term172 = term173.
Proof. exact (MK_COMB (@lem2322080) (@lem2322079)). Qed.
Lemma lem2322082 : term360 = term361.
Proof. exact (MK_COMB (@lem2322081) (@lem2322076)). Qed.
Lemma lem2322083 : term361 = term362.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2322085 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322086 : term179 = term180.
Proof. exact (@lem2322085 term57 term57). Qed.
Lemma lem2322087 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322088 : term182 = term57.
Proof. exact (EQ_MP (@lem2322087) (@lem940073)). Qed.
Lemma lem2322089 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322090 : term180 = term56.
Proof. exact (MK_COMB (@lem2322089) (@lem2322088)). Qed.
Lemma lem2322091 : term179 = term56.
Proof. exact (TRANS (@lem2322086) (@lem2322090)). Qed.
Lemma lem2322093 (x : nat) : (term363 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2322094 : term360 = term159.
Proof. exact (@lem2322093 term57). Qed.
Lemma lem2322095 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2322096 : term364 = term365.
Proof. exact (MK_COMB (@lem2322095) (@lem2322094)). Qed.
Lemma lem2322097 : term362 = term321.
Proof. exact (MK_COMB (@lem2322096) (@lem2322091)). Qed.
Lemma lem2322098 : term361 = term321.
Proof. exact (TRANS (@lem2322083) (@lem2322097)). Qed.
Lemma lem2322099 : term360 = term321.
Proof. exact (TRANS (@lem2322082) (@lem2322098)). Qed.
Lemma lem2322101 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2322102 : term321 = term159.
Proof. exact (@lem2322101 term159). Qed.
Lemma lem2322103 : term360 = term159.
Proof. exact (TRANS (@lem2322099) (@lem2322102)). Qed.
Lemma lem2322104 : term300 = term300.
Proof. exact (eq_refl term300). Qed.
Lemma lem2322105 : term379 = term380.
Proof. exact (MK_COMB (@lem2322104) (@lem2322103)). Qed.
Lemma lem2322106 : term380 = term166.
Proof. exact (@lem1982723 term166). Qed.
Lemma lem2322107 : term379 = term166.
Proof. exact (TRANS (@lem2322105) (@lem2322106)). Qed.
Lemma lem2322108 : term378 = term166.
Proof. exact (TRANS (@lem2322073) (@lem2322107)). Qed.
Lemma lem2322109 (x : int) : (term377 x) = term166.
Proof. exact (TRANS (@lem2322072 x) (@lem2322108)). Qed.
Lemma lem2322110 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2322111 (x : int) : (term381 x) = term328.
Proof. exact (MK_COMB (@lem2322110) (@lem2322109 x)). Qed.
Lemma lem2322112 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2322113 (x : int) : (term370 x) = term330.
Proof. exact (MK_COMB (@lem2322111 x) (@lem2322112)). Qed.
Lemma lem2322114 (x : int) : (term369 x) = term330.
Proof. exact (TRANS (@lem2321936 x) (@lem2322113 x)). Qed.
Lemma lem2322115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2322116 (x : int) (y : int) : (term239 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem2322115) (@lem2321863 x y)). Qed.
Lemma lem2322117 (x : int) (y : int) : (term417 y x) = (term434 x y).
Proof. exact (MK_COMB (@lem2322116 x y) (@lem2322114 x)). Qed.
Lemma lem2322118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2322119 (x : int) (y : int) : (term344 x y) = (term399 x y).
Proof. exact (MK_COMB (@lem2322118) (@lem2321516 x y)). Qed.
Lemma lem2322120 (x : int) (y : int) : (term419 y x) = (term435 x y).
Proof. exact (MK_COMB (@lem2322119 x y) (@lem2322117 x y)). Qed.
Lemma lem2322121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2322122 (x : int) (y : int) : (term425 x y) = (term436 x y).
Proof. exact (MK_COMB (@lem2322121) (@lem2321935 x y)). Qed.
Lemma lem2322123 (x : int) (y : int) : (term426 y x) = (term437 x y).
Proof. exact (MK_COMB (@lem2322122 x y) (@lem2322120 x y)). Qed.
Lemma lem2322135 (x : int) (y : int) : (term413 x y) = (term437 x y).
Proof. exact (TRANS (@lem2321797 y x) (@lem2322123 x y)). Qed.
Lemma lem2322136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2322137 (x : int) (y : int) : (term438 x y) = (term439 x y).
Proof. exact (MK_COMB (@lem2322136) (@lem2321780 x y)). Qed.
Lemma lem2322138 (x : int) (y : int) : (term285 x y) = (term440 x y).
Proof. exact (MK_COMB (@lem2322137 x y) (@lem2322135 x y)). Qed.
Lemma lem2322139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2322140 (x : int) (y : int) : (term287 x y) = (term441 x y).
Proof. exact (MK_COMB (@lem2322139) (@lem2321610 x y)). Qed.
Lemma lem2322141 (x : int) (y : int) : (term288 x y) = (term442 x y).
Proof. exact (MK_COMB (@lem2322140 x y) (@lem2322138 x y)). Qed.
Lemma lem2322142 (x : int) (y : int) (h1 : term442 x y) : term442 x y.
Proof. exact (h1). Qed.
Lemma lem2322143 (x : int) (y : int) (h1 : term405 x y) : term405 x y.
Proof. exact (h1). Qed.
Lemma lem2322144 (x : int) (y : int) (h1 : term337 x y) : term337 x y.
Proof. exact (h1). Qed.
Lemma lem2322145 (x : int) (y : int) (h1 : term337 x y) : term335 x y.
Proof. exact (proj2 (@lem2322144 x y h1)). Qed.
Lemma lem2322147 (x : int) (y : int) (h1 : term337 x y) : term330.
Proof. exact (proj2 (@lem2322145 x y h1)). Qed.
Lemma lem2322150 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2322151 : term330 = term443.
Proof. exact (@lem2322150 term159 term166). Qed.
Lemma lem2322153 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2322154 : term166 = term171.
Proof. exact (@lem2322153 term57). Qed.
Lemma lem2322156 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322157 : term159 = term321.
Proof. exact (@lem2322156 (NUMERAL 0)). Qed.
Lemma lem2322158 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2322159 : term444 = term445.
Proof. exact (MK_COMB (@lem2322158) (@lem2322157)). Qed.
Lemma lem2322160 : term443 = term446.
Proof. exact (MK_COMB (@lem2322159) (@lem2322154)). Qed.
Lemma lem2322161 : term447.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2322163 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322164 : term306 = term307.
Proof. exact (@lem2322163 (NUMERAL 0) term57). Qed.
Lemma lem2322165 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322166 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322167 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322166 h1) (fun h1 : term307 = True => @lem2322165)). Qed.
Lemma lem2322168 : term307 = True.
Proof. exact (EQ_MP (@lem2322167) (@lem2322165)). Qed.
Lemma lem2322169 : term306 = True.
Proof. exact (TRANS (@lem2322164) (@lem2322168)). Qed.
Lemma lem2322170 : True = term306.
Proof. exact (SYM (@lem2322169)). Qed.
Lemma lem2322171 : term306.
Proof. exact (EQ_MP (@lem2322170) (@lem0)). Qed.
Lemma lem2322172 : term448.
Proof. exact (@lem2322161 (@lem2322171)). Qed.
Lemma lem2322174 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322175 : term306 = term307.
Proof. exact (@lem2322174 (NUMERAL 0) term57). Qed.
Lemma lem2322176 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322177 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322178 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322177 h1) (fun h1 : term307 = True => @lem2322176)). Qed.
Lemma lem2322179 : term307 = True.
Proof. exact (EQ_MP (@lem2322178) (@lem2322176)). Qed.
Lemma lem2322180 : term306 = True.
Proof. exact (TRANS (@lem2322175) (@lem2322179)). Qed.
Lemma lem2322181 : True = term306.
Proof. exact (SYM (@lem2322180)). Qed.
Lemma lem2322182 : term306.
Proof. exact (EQ_MP (@lem2322181) (@lem0)). Qed.
Lemma lem2322183 : term446 = term449.
Proof. exact (@lem2322172 (@lem2322182)). Qed.
Lemma lem2322185 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2322186 : term174 = term185.
Proof. exact (@lem2322185 term57 term57). Qed.
Lemma lem2322187 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322188 : term182 = term57.
Proof. exact (EQ_MP (@lem2322187) (@lem940073)). Qed.
Lemma lem2322189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322190 : term180 = term56.
Proof. exact (MK_COMB (@lem2322189) (@lem2322188)). Qed.
Lemma lem2322191 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2322192 : term185 = term166.
Proof. exact (MK_COMB (@lem2322191) (@lem2322190)). Qed.
Lemma lem2322193 : term174 = term166.
Proof. exact (TRANS (@lem2322186) (@lem2322192)). Qed.
Lemma lem2322195 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322196 : term318 = term159.
Proof. exact (@lem2322195 term57). Qed.
Lemma lem2322197 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2322198 : term450 = term444.
Proof. exact (MK_COMB (@lem2322197) (@lem2322196)). Qed.
Lemma lem2322199 : term449 = term443.
Proof. exact (MK_COMB (@lem2322198) (@lem2322193)). Qed.
Lemma lem2322201 (m : nat) (n : nat) : (term451 m n) = (term452 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2322202 : term443 = term453.
Proof. exact (@lem2322201 (NUMERAL 0) term57). Qed.
Lemma lem2322203 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322204 (h1 : term308 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2322205 : (term308 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322204 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2322203)). Qed.
Lemma lem2322206 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2322205) (@lem2322203)). Qed.
Lemma lem2322207 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2322208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2322209 : term454 = (and True).
Proof. exact (MK_COMB (@lem2322208) (@lem2322207)). Qed.
Lemma lem2322210 : term453 = (True /\ False).
Proof. exact (MK_COMB (@lem2322209) (@lem2322206)). Qed.
Lemma lem2322212 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2322213 : term453 = False.
Proof. exact (TRANS (@lem2322210) (@lem2322212)). Qed.
Lemma lem2322214 : term443 = False.
Proof. exact (TRANS (@lem2322202) (@lem2322213)). Qed.
Lemma lem2322215 : term449 = False.
Proof. exact (TRANS (@lem2322199) (@lem2322214)). Qed.
Lemma lem2322216 : term446 = False.
Proof. exact (TRANS (@lem2322183) (@lem2322215)). Qed.
Lemma lem2322217 : term443 = False.
Proof. exact (TRANS (@lem2322160) (@lem2322216)). Qed.
Lemma lem2322218 : term330 = False.
Proof. exact (TRANS (@lem2322151) (@lem2322217)). Qed.
Lemma lem2322219 (x : int) (y : int) (h1 : term337 x y) : False.
Proof. exact (EQ_MP (@lem2322218) (@lem2322147 x y h1)). Qed.
Lemma lem2322220 (x : int) (y : int) (h1 : term402 x y) : term402 x y.
Proof. exact (h1). Qed.
Lemma lem2322221 (x : int) (y : int) (h1 : term383 x y) : term383 x y.
Proof. exact (h1). Qed.
Lemma lem2322222 (x : int) (y : int) (h1 : term383 x y) : term382 x y.
Proof. exact (proj2 (@lem2322221 x y h1)). Qed.
Lemma lem2322224 (x : int) (y : int) (h1 : term383 x y) : term330.
Proof. exact (proj2 (@lem2322222 x y h1)). Qed.
Lemma lem2322227 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2322228 : term330 = term443.
Proof. exact (@lem2322227 term159 term166). Qed.
Lemma lem2322230 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2322231 : term166 = term171.
Proof. exact (@lem2322230 term57). Qed.
Lemma lem2322233 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322234 : term159 = term321.
Proof. exact (@lem2322233 (NUMERAL 0)). Qed.
Lemma lem2322235 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2322236 : term444 = term445.
Proof. exact (MK_COMB (@lem2322235) (@lem2322234)). Qed.
Lemma lem2322237 : term443 = term446.
Proof. exact (MK_COMB (@lem2322236) (@lem2322231)). Qed.
Lemma lem2322238 : term447.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2322240 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322241 : term306 = term307.
Proof. exact (@lem2322240 (NUMERAL 0) term57). Qed.
Lemma lem2322242 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322243 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322244 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322243 h1) (fun h1 : term307 = True => @lem2322242)). Qed.
Lemma lem2322245 : term307 = True.
Proof. exact (EQ_MP (@lem2322244) (@lem2322242)). Qed.
Lemma lem2322246 : term306 = True.
Proof. exact (TRANS (@lem2322241) (@lem2322245)). Qed.
Lemma lem2322247 : True = term306.
Proof. exact (SYM (@lem2322246)). Qed.
Lemma lem2322248 : term306.
Proof. exact (EQ_MP (@lem2322247) (@lem0)). Qed.
Lemma lem2322249 : term448.
Proof. exact (@lem2322238 (@lem2322248)). Qed.
Lemma lem2322251 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322252 : term306 = term307.
Proof. exact (@lem2322251 (NUMERAL 0) term57). Qed.
Lemma lem2322253 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322254 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322255 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322254 h1) (fun h1 : term307 = True => @lem2322253)). Qed.
Lemma lem2322256 : term307 = True.
Proof. exact (EQ_MP (@lem2322255) (@lem2322253)). Qed.
Lemma lem2322257 : term306 = True.
Proof. exact (TRANS (@lem2322252) (@lem2322256)). Qed.
Lemma lem2322258 : True = term306.
Proof. exact (SYM (@lem2322257)). Qed.
Lemma lem2322259 : term306.
Proof. exact (EQ_MP (@lem2322258) (@lem0)). Qed.
Lemma lem2322260 : term446 = term449.
Proof. exact (@lem2322249 (@lem2322259)). Qed.
Lemma lem2322262 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2322263 : term174 = term185.
Proof. exact (@lem2322262 term57 term57). Qed.
Lemma lem2322264 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322265 : term182 = term57.
Proof. exact (EQ_MP (@lem2322264) (@lem940073)). Qed.
Lemma lem2322266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322267 : term180 = term56.
Proof. exact (MK_COMB (@lem2322266) (@lem2322265)). Qed.
Lemma lem2322268 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2322269 : term185 = term166.
Proof. exact (MK_COMB (@lem2322268) (@lem2322267)). Qed.
Lemma lem2322270 : term174 = term166.
Proof. exact (TRANS (@lem2322263) (@lem2322269)). Qed.
Lemma lem2322272 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322273 : term318 = term159.
Proof. exact (@lem2322272 term57). Qed.
Lemma lem2322274 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2322275 : term450 = term444.
Proof. exact (MK_COMB (@lem2322274) (@lem2322273)). Qed.
Lemma lem2322276 : term449 = term443.
Proof. exact (MK_COMB (@lem2322275) (@lem2322270)). Qed.
Lemma lem2322278 (m : nat) (n : nat) : (term451 m n) = (term452 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2322279 : term443 = term453.
Proof. exact (@lem2322278 (NUMERAL 0) term57). Qed.
Lemma lem2322280 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322281 (h1 : term308 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2322282 : (term308 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322281 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2322280)). Qed.
Lemma lem2322283 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2322282) (@lem2322280)). Qed.
Lemma lem2322284 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2322285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2322286 : term454 = (and True).
Proof. exact (MK_COMB (@lem2322285) (@lem2322284)). Qed.
Lemma lem2322287 : term453 = (True /\ False).
Proof. exact (MK_COMB (@lem2322286) (@lem2322283)). Qed.
Lemma lem2322289 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2322290 : term453 = False.
Proof. exact (TRANS (@lem2322287) (@lem2322289)). Qed.
Lemma lem2322291 : term443 = False.
Proof. exact (TRANS (@lem2322279) (@lem2322290)). Qed.
Lemma lem2322292 : term449 = False.
Proof. exact (TRANS (@lem2322276) (@lem2322291)). Qed.
Lemma lem2322293 : term446 = False.
Proof. exact (TRANS (@lem2322260) (@lem2322292)). Qed.
Lemma lem2322294 : term443 = False.
Proof. exact (TRANS (@lem2322237) (@lem2322293)). Qed.
Lemma lem2322295 : term330 = False.
Proof. exact (TRANS (@lem2322228) (@lem2322294)). Qed.
Lemma lem2322296 (x : int) (y : int) (h1 : term383 x y) : False.
Proof. exact (EQ_MP (@lem2322295) (@lem2322224 x y h1)). Qed.
Lemma lem2322297 (x : int) (y : int) (h1 : term400 x y) : term400 x y.
Proof. exact (h1). Qed.
Lemma lem2322298 (x : int) (y : int) (h1 : term400 x y) : term398 x y.
Proof. exact (proj2 (@lem2322297 x y h1)). Qed.
Lemma lem2322299 (x : int) (y : int) (h1 : term400 x y) : term388 x y.
Proof. exact (proj1 (@lem2322297 x y h1)). Qed.
Lemma lem2322301 (x : int) (y : int) (h1 : term400 x y) : term160 x y.
Proof. exact (proj1 (@lem2322298 x y h1)). Qed.
Lemma lem2322303 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2322304 : term455 = term306.
Proof. exact (@lem2322303 term159 term56). Qed.
Lemma lem2322306 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322307 : term56 = term168.
Proof. exact (@lem2322306 term57). Qed.
Lemma lem2322309 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322310 : term159 = term321.
Proof. exact (@lem2322309 (NUMERAL 0)). Qed.
Lemma lem2322311 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322312 : term456 = term457.
Proof. exact (MK_COMB (@lem2322311) (@lem2322310)). Qed.
Lemma lem2322313 : term306 = term458.
Proof. exact (MK_COMB (@lem2322312) (@lem2322307)). Qed.
Lemma lem2322314 : term459.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2322316 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322317 : term306 = term307.
Proof. exact (@lem2322316 (NUMERAL 0) term57). Qed.
Lemma lem2322318 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322319 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322320 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322319 h1) (fun h1 : term307 = True => @lem2322318)). Qed.
Lemma lem2322321 : term307 = True.
Proof. exact (EQ_MP (@lem2322320) (@lem2322318)). Qed.
Lemma lem2322322 : term306 = True.
Proof. exact (TRANS (@lem2322317) (@lem2322321)). Qed.
Lemma lem2322323 : True = term306.
Proof. exact (SYM (@lem2322322)). Qed.
Lemma lem2322324 : term306.
Proof. exact (EQ_MP (@lem2322323) (@lem0)). Qed.
Lemma lem2322325 : term460.
Proof. exact (@lem2322314 (@lem2322324)). Qed.
Lemma lem2322327 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322328 : term306 = term307.
Proof. exact (@lem2322327 (NUMERAL 0) term57). Qed.
Lemma lem2322329 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322330 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322331 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322330 h1) (fun h1 : term307 = True => @lem2322329)). Qed.
Lemma lem2322332 : term307 = True.
Proof. exact (EQ_MP (@lem2322331) (@lem2322329)). Qed.
Lemma lem2322333 : term306 = True.
Proof. exact (TRANS (@lem2322328) (@lem2322332)). Qed.
Lemma lem2322334 : True = term306.
Proof. exact (SYM (@lem2322333)). Qed.
Lemma lem2322335 : term306.
Proof. exact (EQ_MP (@lem2322334) (@lem0)). Qed.
Lemma lem2322336 : term458 = term461.
Proof. exact (@lem2322325 (@lem2322335)). Qed.
Lemma lem2322338 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322339 : term179 = term180.
Proof. exact (@lem2322338 term57 term57). Qed.
Lemma lem2322340 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322341 : term182 = term57.
Proof. exact (EQ_MP (@lem2322340) (@lem940073)). Qed.
Lemma lem2322342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322343 : term180 = term56.
Proof. exact (MK_COMB (@lem2322342) (@lem2322341)). Qed.
Lemma lem2322344 : term179 = term56.
Proof. exact (TRANS (@lem2322339) (@lem2322343)). Qed.
Lemma lem2322346 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322347 : term318 = term159.
Proof. exact (@lem2322346 term57). Qed.
Lemma lem2322348 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322349 : term462 = term456.
Proof. exact (MK_COMB (@lem2322348) (@lem2322347)). Qed.
Lemma lem2322350 : term461 = term306.
Proof. exact (MK_COMB (@lem2322349) (@lem2322344)). Qed.
Lemma lem2322352 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322353 : term306 = term307.
Proof. exact (@lem2322352 (NUMERAL 0) term57). Qed.
Lemma lem2322354 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322355 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322356 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322355 h1) (fun h1 : term307 = True => @lem2322354)). Qed.
Lemma lem2322357 : term307 = True.
Proof. exact (EQ_MP (@lem2322356) (@lem2322354)). Qed.
Lemma lem2322358 : term306 = True.
Proof. exact (TRANS (@lem2322353) (@lem2322357)). Qed.
Lemma lem2322359 : term461 = True.
Proof. exact (TRANS (@lem2322350) (@lem2322358)). Qed.
Lemma lem2322360 : term458 = True.
Proof. exact (TRANS (@lem2322336) (@lem2322359)). Qed.
Lemma lem2322361 : term306 = True.
Proof. exact (TRANS (@lem2322313) (@lem2322360)). Qed.
Lemma lem2322362 : term455 = True.
Proof. exact (TRANS (@lem2322304) (@lem2322361)). Qed.
Lemma lem2322363 : True = term455.
Proof. exact (SYM (@lem2322362)). Qed.
Lemma lem2322364 : term455.
Proof. exact (EQ_MP (@lem2322363) (@lem0)). Qed.
Lemma lem2322365 (x : int) (y : int) (h1 : term400 x y) : term463 x y.
Proof. exact (conj (@lem2322364) (@lem2322301 x y h1)). Qed.
Lemma lem2322367 (x : real) (y : real) : term464 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2322368 (x : int) (y : int) : term465 x y.
Proof. exact (@lem2322367 term56 (term155 x y)). Qed.
Lemma lem2322369 (x : int) (y : int) (h1 : term400 x y) : term466 x y.
Proof. exact (@lem2322368 x y (@lem2322365 x y h1)). Qed.
Lemma lem2322370 (x : int) (y : int) : (term467 x y) = (term155 x y).
Proof. exact (@lem1982733 (term155 x y)). Qed.
Lemma lem2322371 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2322372 (x : int) (y : int) : (term468 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem2322371) (@lem2322370 x y)). Qed.
Lemma lem2322373 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2322374 (x : int) (y : int) : (term466 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem2322372 x y) (@lem2322373)). Qed.
Lemma lem2322375 (x : int) (y : int) (h1 : term400 x y) : term160 x y.
Proof. exact (EQ_MP (@lem2322374 x y) (@lem2322369 x y h1)). Qed.
Lemma lem2322377 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2322378 : term455 = term306.
Proof. exact (@lem2322377 term159 term56). Qed.
Lemma lem2322380 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322381 : term56 = term168.
Proof. exact (@lem2322380 term57). Qed.
Lemma lem2322383 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322384 : term159 = term321.
Proof. exact (@lem2322383 (NUMERAL 0)). Qed.
Lemma lem2322385 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322386 : term456 = term457.
Proof. exact (MK_COMB (@lem2322385) (@lem2322384)). Qed.
Lemma lem2322387 : term306 = term458.
Proof. exact (MK_COMB (@lem2322386) (@lem2322381)). Qed.
Lemma lem2322388 : term459.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2322390 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322391 : term306 = term307.
Proof. exact (@lem2322390 (NUMERAL 0) term57). Qed.
Lemma lem2322392 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322393 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322394 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322393 h1) (fun h1 : term307 = True => @lem2322392)). Qed.
Lemma lem2322395 : term307 = True.
Proof. exact (EQ_MP (@lem2322394) (@lem2322392)). Qed.
Lemma lem2322396 : term306 = True.
Proof. exact (TRANS (@lem2322391) (@lem2322395)). Qed.
Lemma lem2322397 : True = term306.
Proof. exact (SYM (@lem2322396)). Qed.
Lemma lem2322398 : term306.
Proof. exact (EQ_MP (@lem2322397) (@lem0)). Qed.
Lemma lem2322399 : term460.
Proof. exact (@lem2322388 (@lem2322398)). Qed.
Lemma lem2322401 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322402 : term306 = term307.
Proof. exact (@lem2322401 (NUMERAL 0) term57). Qed.
Lemma lem2322403 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322404 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322405 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322404 h1) (fun h1 : term307 = True => @lem2322403)). Qed.
Lemma lem2322406 : term307 = True.
Proof. exact (EQ_MP (@lem2322405) (@lem2322403)). Qed.
Lemma lem2322407 : term306 = True.
Proof. exact (TRANS (@lem2322402) (@lem2322406)). Qed.
Lemma lem2322408 : True = term306.
Proof. exact (SYM (@lem2322407)). Qed.
Lemma lem2322409 : term306.
Proof. exact (EQ_MP (@lem2322408) (@lem0)). Qed.
Lemma lem2322410 : term458 = term461.
Proof. exact (@lem2322399 (@lem2322409)). Qed.
Lemma lem2322412 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322413 : term179 = term180.
Proof. exact (@lem2322412 term57 term57). Qed.
Lemma lem2322414 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322415 : term182 = term57.
Proof. exact (EQ_MP (@lem2322414) (@lem940073)). Qed.
Lemma lem2322416 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322417 : term180 = term56.
Proof. exact (MK_COMB (@lem2322416) (@lem2322415)). Qed.
Lemma lem2322418 : term179 = term56.
Proof. exact (TRANS (@lem2322413) (@lem2322417)). Qed.
Lemma lem2322420 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322421 : term318 = term159.
Proof. exact (@lem2322420 term57). Qed.
Lemma lem2322422 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322423 : term462 = term456.
Proof. exact (MK_COMB (@lem2322422) (@lem2322421)). Qed.
Lemma lem2322424 : term461 = term306.
Proof. exact (MK_COMB (@lem2322423) (@lem2322418)). Qed.
Lemma lem2322426 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322427 : term306 = term307.
Proof. exact (@lem2322426 (NUMERAL 0) term57). Qed.
Lemma lem2322428 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322429 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322430 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322429 h1) (fun h1 : term307 = True => @lem2322428)). Qed.
Lemma lem2322431 : term307 = True.
Proof. exact (EQ_MP (@lem2322430) (@lem2322428)). Qed.
Lemma lem2322432 : term306 = True.
Proof. exact (TRANS (@lem2322427) (@lem2322431)). Qed.
Lemma lem2322433 : term461 = True.
Proof. exact (TRANS (@lem2322424) (@lem2322432)). Qed.
Lemma lem2322434 : term458 = True.
Proof. exact (TRANS (@lem2322410) (@lem2322433)). Qed.
Lemma lem2322435 : term306 = True.
Proof. exact (TRANS (@lem2322387) (@lem2322434)). Qed.
Lemma lem2322436 : term455 = True.
Proof. exact (TRANS (@lem2322378) (@lem2322435)). Qed.
Lemma lem2322437 : True = term455.
Proof. exact (SYM (@lem2322436)). Qed.
Lemma lem2322438 : term455.
Proof. exact (EQ_MP (@lem2322437) (@lem0)). Qed.
Lemma lem2322439 (x : int) (y : int) (h1 : term400 x y) : term469 x y.
Proof. exact (conj (@lem2322438) (@lem2322299 x y h1)). Qed.
Lemma lem2322441 (x : real) (y : real) : term470 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2322442 (x : int) (y : int) : term471 x y.
Proof. exact (@lem2322441 term56 (term154 x y)). Qed.
Lemma lem2322443 (x : int) (y : int) (h1 : term400 x y) : term472 x y.
Proof. exact (@lem2322442 x y (@lem2322439 x y h1)). Qed.
Lemma lem2322444 (x : int) (y : int) : (term473 x y) = (term154 x y).
Proof. exact (@lem1982733 (term154 x y)). Qed.
Lemma lem2322445 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2322446 (x : int) (y : int) : (term474 x y) = (term387 x y).
Proof. exact (MK_COMB (@lem2322445) (@lem2322444 x y)). Qed.
Lemma lem2322447 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2322448 (x : int) (y : int) : (term472 x y) = (term388 x y).
Proof. exact (MK_COMB (@lem2322446 x y) (@lem2322447)). Qed.
Lemma lem2322449 (x : int) (y : int) (h1 : term400 x y) : term388 x y.
Proof. exact (EQ_MP (@lem2322448 x y) (@lem2322443 x y h1)). Qed.
Lemma lem2322450 (x : int) (y : int) (h1 : term400 x y) : term475 x y.
Proof. exact (conj (@lem2322449 x y h1) (@lem2322375 x y h1)). Qed.
Lemma lem2322452 (x : real) (y : real) : term476 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem2322453 (x : int) (y : int) : term477 x y.
Proof. exact (@lem2322452 (term154 x y) (term155 x y)). Qed.
Lemma lem2322454 (x : int) (y : int) (h1 : term400 x y) : term478 x y.
Proof. exact (@lem2322453 x y (@lem2322450 x y h1)). Qed.
Lemma lem2322455 (x : int) (y : int) : (term479 x y) = (term480 x y).
Proof. exact (@lem1982753 (real_of_int x) (term156 x) (term156 y) (real_of_int y)). Qed.
Lemma lem2322456 (x : int) : (term298 x) = (term299 x).
Proof. exact (@lem1982715 term166 (real_of_int x)). Qed.
Lemma lem2322458 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322459 : term56 = term168.
Proof. exact (@lem2322458 term57). Qed.
Lemma lem2322461 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2322462 : term166 = term171.
Proof. exact (@lem2322461 term57). Qed.
Lemma lem2322463 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322464 : term300 = term301.
Proof. exact (MK_COMB (@lem2322463) (@lem2322462)). Qed.
Lemma lem2322465 : term302 = term303.
Proof. exact (MK_COMB (@lem2322464) (@lem2322459)). Qed.
Lemma lem2322466 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2322468 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322469 : term306 = term307.
Proof. exact (@lem2322468 (NUMERAL 0) term57). Qed.
Lemma lem2322470 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322471 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322472 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322471 h1) (fun h1 : term307 = True => @lem2322470)). Qed.
Lemma lem2322473 : term307 = True.
Proof. exact (EQ_MP (@lem2322472) (@lem2322470)). Qed.
Lemma lem2322474 : term306 = True.
Proof. exact (TRANS (@lem2322469) (@lem2322473)). Qed.
Lemma lem2322475 : True = term306.
Proof. exact (SYM (@lem2322474)). Qed.
Lemma lem2322476 : term306.
Proof. exact (EQ_MP (@lem2322475) (@lem0)). Qed.
Lemma lem2322477 : term309.
Proof. exact (@lem2322466 (@lem2322476)). Qed.
Lemma lem2322479 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322480 : term306 = term307.
Proof. exact (@lem2322479 (NUMERAL 0) term57). Qed.
Lemma lem2322481 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322482 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322483 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322482 h1) (fun h1 : term307 = True => @lem2322481)). Qed.
Lemma lem2322484 : term307 = True.
Proof. exact (EQ_MP (@lem2322483) (@lem2322481)). Qed.
Lemma lem2322485 : term306 = True.
Proof. exact (TRANS (@lem2322480) (@lem2322484)). Qed.
Lemma lem2322486 : True = term306.
Proof. exact (SYM (@lem2322485)). Qed.
Lemma lem2322487 : term306.
Proof. exact (EQ_MP (@lem2322486) (@lem0)). Qed.
Lemma lem2322488 : term310.
Proof. exact (@lem2322477 (@lem2322487)). Qed.
Lemma lem2322490 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322491 : term306 = term307.
Proof. exact (@lem2322490 (NUMERAL 0) term57). Qed.
Lemma lem2322492 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322493 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322494 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322493 h1) (fun h1 : term307 = True => @lem2322492)). Qed.
Lemma lem2322495 : term307 = True.
Proof. exact (EQ_MP (@lem2322494) (@lem2322492)). Qed.
Lemma lem2322496 : term306 = True.
Proof. exact (TRANS (@lem2322491) (@lem2322495)). Qed.
Lemma lem2322497 : True = term306.
Proof. exact (SYM (@lem2322496)). Qed.
Lemma lem2322498 : term306.
Proof. exact (EQ_MP (@lem2322497) (@lem0)). Qed.
Lemma lem2322499 : term311.
Proof. exact (@lem2322488 (@lem2322498)). Qed.
Lemma lem2322501 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322502 : term179 = term180.
Proof. exact (@lem2322501 term57 term57). Qed.
Lemma lem2322503 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322504 : term182 = term57.
Proof. exact (EQ_MP (@lem2322503) (@lem940073)). Qed.
Lemma lem2322505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322506 : term180 = term56.
Proof. exact (MK_COMB (@lem2322505) (@lem2322504)). Qed.
Lemma lem2322507 : term179 = term56.
Proof. exact (TRANS (@lem2322502) (@lem2322506)). Qed.
Lemma lem2322509 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2322510 : term174 = term185.
Proof. exact (@lem2322509 term57 term57). Qed.
Lemma lem2322511 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322512 : term182 = term57.
Proof. exact (EQ_MP (@lem2322511) (@lem940073)). Qed.
Lemma lem2322513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322514 : term180 = term56.
Proof. exact (MK_COMB (@lem2322513) (@lem2322512)). Qed.
Lemma lem2322515 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2322516 : term185 = term166.
Proof. exact (MK_COMB (@lem2322515) (@lem2322514)). Qed.
Lemma lem2322517 : term174 = term166.
Proof. exact (TRANS (@lem2322510) (@lem2322516)). Qed.
Lemma lem2322518 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322519 : term312 = term300.
Proof. exact (MK_COMB (@lem2322518) (@lem2322517)). Qed.
Lemma lem2322520 : term313 = term302.
Proof. exact (MK_COMB (@lem2322519) (@lem2322507)). Qed.
Lemma lem2322522 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2322523 : term302 = term159.
Proof. exact (@lem2322522 term57). Qed.
Lemma lem2322524 : term313 = term159.
Proof. exact (TRANS (@lem2322520) (@lem2322523)). Qed.
Lemma lem2322525 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2322526 : term315 = term316.
Proof. exact (MK_COMB (@lem2322525) (@lem2322524)). Qed.
Lemma lem2322527 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2322528 : term317 = term318.
Proof. exact (MK_COMB (@lem2322526) (@lem2322527)). Qed.
Lemma lem2322530 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322531 : term318 = term159.
Proof. exact (@lem2322530 term57). Qed.
Lemma lem2322532 : term317 = term159.
Proof. exact (TRANS (@lem2322528) (@lem2322531)). Qed.
Lemma lem2322534 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322535 : term179 = term180.
Proof. exact (@lem2322534 term57 term57). Qed.
Lemma lem2322536 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322537 : term182 = term57.
Proof. exact (EQ_MP (@lem2322536) (@lem940073)). Qed.
Lemma lem2322538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322539 : term180 = term56.
Proof. exact (MK_COMB (@lem2322538) (@lem2322537)). Qed.
Lemma lem2322540 : term179 = term56.
Proof. exact (TRANS (@lem2322535) (@lem2322539)). Qed.
Lemma lem2322541 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2322542 : term320 = term318.
Proof. exact (MK_COMB (@lem2322541) (@lem2322540)). Qed.
Lemma lem2322544 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322545 : term318 = term159.
Proof. exact (@lem2322544 term57). Qed.
Lemma lem2322546 : term320 = term159.
Proof. exact (TRANS (@lem2322542) (@lem2322545)). Qed.
Lemma lem2322547 : term159 = term320.
Proof. exact (SYM (@lem2322546)). Qed.
Lemma lem2322548 : term317 = term320.
Proof. exact (TRANS (@lem2322532) (@lem2322547)). Qed.
Lemma lem2322549 : term303 = term321.
Proof. exact (@lem2322499 (@lem2322548)). Qed.
Lemma lem2322550 : term302 = term321.
Proof. exact (TRANS (@lem2322465) (@lem2322549)). Qed.
Lemma lem2322552 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2322553 : term321 = term159.
Proof. exact (@lem2322552 term159). Qed.
Lemma lem2322554 : term302 = term159.
Proof. exact (TRANS (@lem2322550) (@lem2322553)). Qed.
Lemma lem2322555 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2322556 : term322 = term316.
Proof. exact (MK_COMB (@lem2322555) (@lem2322554)). Qed.
Lemma lem2322557 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2322558 (x : int) : (term299 x) = (term323 x).
Proof. exact (MK_COMB (@lem2322556) (@lem2322557 x)). Qed.
Lemma lem2322559 (x : int) : (term298 x) = (term323 x).
Proof. exact (TRANS (@lem2322456 x) (@lem2322558 x)). Qed.
Lemma lem2322560 (x : int) : (term323 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2322561 (x : int) : (term298 x) = term159.
Proof. exact (TRANS (@lem2322559 x) (@lem2322560 x)). Qed.
Lemma lem2322562 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322563 (x : int) : (term324 x) = term325.
Proof. exact (MK_COMB (@lem2322562) (@lem2322561 x)). Qed.
Lemma lem2322564 (y : int) : (term373 y) = (term299 y).
Proof. exact (@lem1982713 term166 (real_of_int y)). Qed.
Lemma lem2322566 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322567 : term56 = term168.
Proof. exact (@lem2322566 term57). Qed.
Lemma lem2322569 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2322570 : term166 = term171.
Proof. exact (@lem2322569 term57). Qed.
Lemma lem2322571 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322572 : term300 = term301.
Proof. exact (MK_COMB (@lem2322571) (@lem2322570)). Qed.
Lemma lem2322573 : term302 = term303.
Proof. exact (MK_COMB (@lem2322572) (@lem2322567)). Qed.
Lemma lem2322574 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2322576 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322577 : term306 = term307.
Proof. exact (@lem2322576 (NUMERAL 0) term57). Qed.
Lemma lem2322578 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322579 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322580 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322579 h1) (fun h1 : term307 = True => @lem2322578)). Qed.
Lemma lem2322581 : term307 = True.
Proof. exact (EQ_MP (@lem2322580) (@lem2322578)). Qed.
Lemma lem2322582 : term306 = True.
Proof. exact (TRANS (@lem2322577) (@lem2322581)). Qed.
Lemma lem2322583 : True = term306.
Proof. exact (SYM (@lem2322582)). Qed.
Lemma lem2322584 : term306.
Proof. exact (EQ_MP (@lem2322583) (@lem0)). Qed.
Lemma lem2322585 : term309.
Proof. exact (@lem2322574 (@lem2322584)). Qed.
Lemma lem2322587 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322588 : term306 = term307.
Proof. exact (@lem2322587 (NUMERAL 0) term57). Qed.
Lemma lem2322589 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322590 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322591 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322590 h1) (fun h1 : term307 = True => @lem2322589)). Qed.
Lemma lem2322592 : term307 = True.
Proof. exact (EQ_MP (@lem2322591) (@lem2322589)). Qed.
Lemma lem2322593 : term306 = True.
Proof. exact (TRANS (@lem2322588) (@lem2322592)). Qed.
Lemma lem2322594 : True = term306.
Proof. exact (SYM (@lem2322593)). Qed.
Lemma lem2322595 : term306.
Proof. exact (EQ_MP (@lem2322594) (@lem0)). Qed.
Lemma lem2322596 : term310.
Proof. exact (@lem2322585 (@lem2322595)). Qed.
Lemma lem2322598 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322599 : term306 = term307.
Proof. exact (@lem2322598 (NUMERAL 0) term57). Qed.
Lemma lem2322600 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322601 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322602 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322601 h1) (fun h1 : term307 = True => @lem2322600)). Qed.
Lemma lem2322603 : term307 = True.
Proof. exact (EQ_MP (@lem2322602) (@lem2322600)). Qed.
Lemma lem2322604 : term306 = True.
Proof. exact (TRANS (@lem2322599) (@lem2322603)). Qed.
Lemma lem2322605 : True = term306.
Proof. exact (SYM (@lem2322604)). Qed.
Lemma lem2322606 : term306.
Proof. exact (EQ_MP (@lem2322605) (@lem0)). Qed.
Lemma lem2322607 : term311.
Proof. exact (@lem2322596 (@lem2322606)). Qed.
Lemma lem2322609 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322610 : term179 = term180.
Proof. exact (@lem2322609 term57 term57). Qed.
Lemma lem2322611 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322612 : term182 = term57.
Proof. exact (EQ_MP (@lem2322611) (@lem940073)). Qed.
Lemma lem2322613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322614 : term180 = term56.
Proof. exact (MK_COMB (@lem2322613) (@lem2322612)). Qed.
Lemma lem2322615 : term179 = term56.
Proof. exact (TRANS (@lem2322610) (@lem2322614)). Qed.
Lemma lem2322617 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2322618 : term174 = term185.
Proof. exact (@lem2322617 term57 term57). Qed.
Lemma lem2322619 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322620 : term182 = term57.
Proof. exact (EQ_MP (@lem2322619) (@lem940073)). Qed.
Lemma lem2322621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322622 : term180 = term56.
Proof. exact (MK_COMB (@lem2322621) (@lem2322620)). Qed.
Lemma lem2322623 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2322624 : term185 = term166.
Proof. exact (MK_COMB (@lem2322623) (@lem2322622)). Qed.
Lemma lem2322625 : term174 = term166.
Proof. exact (TRANS (@lem2322618) (@lem2322624)). Qed.
Lemma lem2322626 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322627 : term312 = term300.
Proof. exact (MK_COMB (@lem2322626) (@lem2322625)). Qed.
Lemma lem2322628 : term313 = term302.
Proof. exact (MK_COMB (@lem2322627) (@lem2322615)). Qed.
Lemma lem2322630 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2322631 : term302 = term159.
Proof. exact (@lem2322630 term57). Qed.
Lemma lem2322632 : term313 = term159.
Proof. exact (TRANS (@lem2322628) (@lem2322631)). Qed.
Lemma lem2322633 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2322634 : term315 = term316.
Proof. exact (MK_COMB (@lem2322633) (@lem2322632)). Qed.
Lemma lem2322635 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2322636 : term317 = term318.
Proof. exact (MK_COMB (@lem2322634) (@lem2322635)). Qed.
Lemma lem2322638 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322639 : term318 = term159.
Proof. exact (@lem2322638 term57). Qed.
Lemma lem2322640 : term317 = term159.
Proof. exact (TRANS (@lem2322636) (@lem2322639)). Qed.
Lemma lem2322642 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322643 : term179 = term180.
Proof. exact (@lem2322642 term57 term57). Qed.
Lemma lem2322644 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322645 : term182 = term57.
Proof. exact (EQ_MP (@lem2322644) (@lem940073)). Qed.
Lemma lem2322646 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322647 : term180 = term56.
Proof. exact (MK_COMB (@lem2322646) (@lem2322645)). Qed.
Lemma lem2322648 : term179 = term56.
Proof. exact (TRANS (@lem2322643) (@lem2322647)). Qed.
Lemma lem2322649 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2322650 : term320 = term318.
Proof. exact (MK_COMB (@lem2322649) (@lem2322648)). Qed.
Lemma lem2322652 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322653 : term318 = term159.
Proof. exact (@lem2322652 term57). Qed.
Lemma lem2322654 : term320 = term159.
Proof. exact (TRANS (@lem2322650) (@lem2322653)). Qed.
Lemma lem2322655 : term159 = term320.
Proof. exact (SYM (@lem2322654)). Qed.
Lemma lem2322656 : term317 = term320.
Proof. exact (TRANS (@lem2322640) (@lem2322655)). Qed.
Lemma lem2322657 : term303 = term321.
Proof. exact (@lem2322607 (@lem2322656)). Qed.
Lemma lem2322658 : term302 = term321.
Proof. exact (TRANS (@lem2322573) (@lem2322657)). Qed.
Lemma lem2322660 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2322661 : term321 = term159.
Proof. exact (@lem2322660 term159). Qed.
Lemma lem2322662 : term302 = term159.
Proof. exact (TRANS (@lem2322658) (@lem2322661)). Qed.
Lemma lem2322663 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2322664 : term322 = term316.
Proof. exact (MK_COMB (@lem2322663) (@lem2322662)). Qed.
Lemma lem2322665 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2322666 (y : int) : (term299 y) = (term323 y).
Proof. exact (MK_COMB (@lem2322664) (@lem2322665 y)). Qed.
Lemma lem2322667 (y : int) : (term373 y) = (term323 y).
Proof. exact (TRANS (@lem2322564 y) (@lem2322666 y)). Qed.
Lemma lem2322668 (y : int) : (term323 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2322669 (y : int) : (term373 y) = term159.
Proof. exact (TRANS (@lem2322667 y) (@lem2322668 y)). Qed.
Lemma lem2322670 (x : int) (y : int) : (term480 x y) = term481.
Proof. exact (MK_COMB (@lem2322563 x) (@lem2322669 y)). Qed.
Lemma lem2322671 (x : int) (y : int) : (term479 x y) = term481.
Proof. exact (TRANS (@lem2322455 x y) (@lem2322670 x y)). Qed.
Lemma lem2322672 : term481 = term159.
Proof. exact (@lem1982721 term159). Qed.
Lemma lem2322673 (x : int) (y : int) : (term479 x y) = term159.
Proof. exact (TRANS (@lem2322671 x y) (@lem2322672)). Qed.
Lemma lem2322674 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2322675 (x : int) (y : int) : (term482 x y) = term483.
Proof. exact (MK_COMB (@lem2322674) (@lem2322673 x y)). Qed.
Lemma lem2322676 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2322677 (x : int) (y : int) : (term478 x y) = term484.
Proof. exact (MK_COMB (@lem2322675 x y) (@lem2322676)). Qed.
Lemma lem2322678 (x : int) (y : int) (h1 : term400 x y) : term484.
Proof. exact (EQ_MP (@lem2322677 x y) (@lem2322454 x y h1)). Qed.
Lemma lem2322680 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2322681 : term484 = term485.
Proof. exact (@lem2322680 term159 term159). Qed.
Lemma lem2322683 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322684 : term159 = term321.
Proof. exact (@lem2322683 (NUMERAL 0)). Qed.
Lemma lem2322686 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322687 : term159 = term321.
Proof. exact (@lem2322686 (NUMERAL 0)). Qed.
Lemma lem2322688 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322689 : term456 = term457.
Proof. exact (MK_COMB (@lem2322688) (@lem2322687)). Qed.
Lemma lem2322690 : term485 = term486.
Proof. exact (MK_COMB (@lem2322689) (@lem2322684)). Qed.
Lemma lem2322691 : term487.
Proof. exact (@lem1980255 term159 term56 term159 term56). Qed.
Lemma lem2322693 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322694 : term306 = term307.
Proof. exact (@lem2322693 (NUMERAL 0) term57). Qed.
Lemma lem2322695 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322696 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322697 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322696 h1) (fun h1 : term307 = True => @lem2322695)). Qed.
Lemma lem2322698 : term307 = True.
Proof. exact (EQ_MP (@lem2322697) (@lem2322695)). Qed.
Lemma lem2322699 : term306 = True.
Proof. exact (TRANS (@lem2322694) (@lem2322698)). Qed.
Lemma lem2322700 : True = term306.
Proof. exact (SYM (@lem2322699)). Qed.
Lemma lem2322701 : term306.
Proof. exact (EQ_MP (@lem2322700) (@lem0)). Qed.
Lemma lem2322702 : term488.
Proof. exact (@lem2322691 (@lem2322701)). Qed.
Lemma lem2322704 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322705 : term306 = term307.
Proof. exact (@lem2322704 (NUMERAL 0) term57). Qed.
Lemma lem2322706 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322707 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322708 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322707 h1) (fun h1 : term307 = True => @lem2322706)). Qed.
Lemma lem2322709 : term307 = True.
Proof. exact (EQ_MP (@lem2322708) (@lem2322706)). Qed.
Lemma lem2322710 : term306 = True.
Proof. exact (TRANS (@lem2322705) (@lem2322709)). Qed.
Lemma lem2322711 : True = term306.
Proof. exact (SYM (@lem2322710)). Qed.
Lemma lem2322712 : term306.
Proof. exact (EQ_MP (@lem2322711) (@lem0)). Qed.
Lemma lem2322713 : term486 = term489.
Proof. exact (@lem2322702 (@lem2322712)). Qed.
Lemma lem2322715 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322716 : term318 = term159.
Proof. exact (@lem2322715 term57). Qed.
Lemma lem2322718 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322719 : term318 = term159.
Proof. exact (@lem2322718 term57). Qed.
Lemma lem2322720 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322721 : term462 = term456.
Proof. exact (MK_COMB (@lem2322720) (@lem2322719)). Qed.
Lemma lem2322722 : term489 = term485.
Proof. exact (MK_COMB (@lem2322721) (@lem2322716)). Qed.
Lemma lem2322724 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322725 : term485 = term490.
Proof. exact (@lem2322724 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2322726 : term490 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2322727 : term485 = False.
Proof. exact (TRANS (@lem2322725) (@lem2322726)). Qed.
Lemma lem2322728 : term489 = False.
Proof. exact (TRANS (@lem2322722) (@lem2322727)). Qed.
Lemma lem2322729 : term486 = False.
Proof. exact (TRANS (@lem2322713) (@lem2322728)). Qed.
Lemma lem2322730 : term485 = False.
Proof. exact (TRANS (@lem2322690) (@lem2322729)). Qed.
Lemma lem2322731 : term484 = False.
Proof. exact (TRANS (@lem2322681) (@lem2322730)). Qed.
Lemma lem2322732 (x : int) (y : int) (h1 : term400 x y) : False.
Proof. exact (EQ_MP (@lem2322731) (@lem2322678 x y h1)). Qed.
Lemma lem2322733 (x : int) (y : int) (h1 : term402 x y) : False.
Proof. exact (or_elim (@lem2322220 x y h1) (fun h0 : term383 x y => @lem2322296 x y h0) (fun h0 : term400 x y => @lem2322732 x y h0)). Qed.
Lemma lem2322734 (x : int) (y : int) (h1 : term405 x y) : False.
Proof. exact (or_elim (@lem2322143 x y h1) (fun h0 : term337 x y => @lem2322219 x y h0) (fun h0 : term402 x y => @lem2322733 x y h0)). Qed.
Lemma lem2322735 (x : int) (y : int) (h1 : term440 x y) : term440 x y.
Proof. exact (h1). Qed.
Lemma lem2322736 (x : int) (y : int) (h1 : term411 x y) : term411 x y.
Proof. exact (h1). Qed.
Lemma lem2322737 (x : int) (y : int) (h1 : term411 x y) : term409 x y.
Proof. exact (proj2 (@lem2322736 x y h1)). Qed.
Lemma lem2322740 (x : int) (y : int) (h1 : term411 x y) : term330.
Proof. exact (proj1 (@lem2322737 x y h1)). Qed.
Lemma lem2322742 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2322743 : term330 = term443.
Proof. exact (@lem2322742 term159 term166). Qed.
Lemma lem2322745 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2322746 : term166 = term171.
Proof. exact (@lem2322745 term57). Qed.
Lemma lem2322748 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322749 : term159 = term321.
Proof. exact (@lem2322748 (NUMERAL 0)). Qed.
Lemma lem2322750 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2322751 : term444 = term445.
Proof. exact (MK_COMB (@lem2322750) (@lem2322749)). Qed.
Lemma lem2322752 : term443 = term446.
Proof. exact (MK_COMB (@lem2322751) (@lem2322746)). Qed.
Lemma lem2322753 : term447.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2322755 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322756 : term306 = term307.
Proof. exact (@lem2322755 (NUMERAL 0) term57). Qed.
Lemma lem2322757 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322758 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322759 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322758 h1) (fun h1 : term307 = True => @lem2322757)). Qed.
Lemma lem2322760 : term307 = True.
Proof. exact (EQ_MP (@lem2322759) (@lem2322757)). Qed.
Lemma lem2322761 : term306 = True.
Proof. exact (TRANS (@lem2322756) (@lem2322760)). Qed.
Lemma lem2322762 : True = term306.
Proof. exact (SYM (@lem2322761)). Qed.
Lemma lem2322763 : term306.
Proof. exact (EQ_MP (@lem2322762) (@lem0)). Qed.
Lemma lem2322764 : term448.
Proof. exact (@lem2322753 (@lem2322763)). Qed.
Lemma lem2322766 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322767 : term306 = term307.
Proof. exact (@lem2322766 (NUMERAL 0) term57). Qed.
Lemma lem2322768 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322769 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322770 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322769 h1) (fun h1 : term307 = True => @lem2322768)). Qed.
Lemma lem2322771 : term307 = True.
Proof. exact (EQ_MP (@lem2322770) (@lem2322768)). Qed.
Lemma lem2322772 : term306 = True.
Proof. exact (TRANS (@lem2322767) (@lem2322771)). Qed.
Lemma lem2322773 : True = term306.
Proof. exact (SYM (@lem2322772)). Qed.
Lemma lem2322774 : term306.
Proof. exact (EQ_MP (@lem2322773) (@lem0)). Qed.
Lemma lem2322775 : term446 = term449.
Proof. exact (@lem2322764 (@lem2322774)). Qed.
Lemma lem2322777 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2322778 : term174 = term185.
Proof. exact (@lem2322777 term57 term57). Qed.
Lemma lem2322779 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322780 : term182 = term57.
Proof. exact (EQ_MP (@lem2322779) (@lem940073)). Qed.
Lemma lem2322781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322782 : term180 = term56.
Proof. exact (MK_COMB (@lem2322781) (@lem2322780)). Qed.
Lemma lem2322783 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2322784 : term185 = term166.
Proof. exact (MK_COMB (@lem2322783) (@lem2322782)). Qed.
Lemma lem2322785 : term174 = term166.
Proof. exact (TRANS (@lem2322778) (@lem2322784)). Qed.
Lemma lem2322787 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322788 : term318 = term159.
Proof. exact (@lem2322787 term57). Qed.
Lemma lem2322789 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2322790 : term450 = term444.
Proof. exact (MK_COMB (@lem2322789) (@lem2322788)). Qed.
Lemma lem2322791 : term449 = term443.
Proof. exact (MK_COMB (@lem2322790) (@lem2322785)). Qed.
Lemma lem2322793 (m : nat) (n : nat) : (term451 m n) = (term452 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2322794 : term443 = term453.
Proof. exact (@lem2322793 (NUMERAL 0) term57). Qed.
Lemma lem2322795 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322796 (h1 : term308 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2322797 : (term308 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322796 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2322795)). Qed.
Lemma lem2322798 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2322797) (@lem2322795)). Qed.
Lemma lem2322799 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2322800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2322801 : term454 = (and True).
Proof. exact (MK_COMB (@lem2322800) (@lem2322799)). Qed.
Lemma lem2322802 : term453 = (True /\ False).
Proof. exact (MK_COMB (@lem2322801) (@lem2322798)). Qed.
Lemma lem2322804 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2322805 : term453 = False.
Proof. exact (TRANS (@lem2322802) (@lem2322804)). Qed.
Lemma lem2322806 : term443 = False.
Proof. exact (TRANS (@lem2322794) (@lem2322805)). Qed.
Lemma lem2322807 : term449 = False.
Proof. exact (TRANS (@lem2322791) (@lem2322806)). Qed.
Lemma lem2322808 : term446 = False.
Proof. exact (TRANS (@lem2322775) (@lem2322807)). Qed.
Lemma lem2322809 : term443 = False.
Proof. exact (TRANS (@lem2322752) (@lem2322808)). Qed.
Lemma lem2322810 : term330 = False.
Proof. exact (TRANS (@lem2322743) (@lem2322809)). Qed.
Lemma lem2322811 (x : int) (y : int) (h1 : term411 x y) : False.
Proof. exact (EQ_MP (@lem2322810) (@lem2322740 x y h1)). Qed.
Lemma lem2322812 (x : int) (y : int) (h1 : term437 x y) : term437 x y.
Proof. exact (h1). Qed.
Lemma lem2322813 (x : int) (y : int) (h1 : term433 x y) : term433 x y.
Proof. exact (h1). Qed.
Lemma lem2322814 (x : int) (y : int) (h1 : term433 x y) : term421 x y.
Proof. exact (proj2 (@lem2322813 x y h1)). Qed.
Lemma lem2322816 (x : int) (y : int) (h1 : term433 x y) : term333 x y.
Proof. exact (proj2 (@lem2322814 x y h1)). Qed.
Lemma lem2322817 (x : int) (y : int) (h1 : term433 x y) : term221 x y.
Proof. exact (proj1 (@lem2322814 x y h1)). Qed.
Lemma lem2322819 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2322820 : term455 = term306.
Proof. exact (@lem2322819 term159 term56). Qed.
Lemma lem2322822 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322823 : term56 = term168.
Proof. exact (@lem2322822 term57). Qed.
Lemma lem2322825 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322826 : term159 = term321.
Proof. exact (@lem2322825 (NUMERAL 0)). Qed.
Lemma lem2322827 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322828 : term456 = term457.
Proof. exact (MK_COMB (@lem2322827) (@lem2322826)). Qed.
Lemma lem2322829 : term306 = term458.
Proof. exact (MK_COMB (@lem2322828) (@lem2322823)). Qed.
Lemma lem2322830 : term459.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2322832 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322833 : term306 = term307.
Proof. exact (@lem2322832 (NUMERAL 0) term57). Qed.
Lemma lem2322834 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322835 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322836 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322835 h1) (fun h1 : term307 = True => @lem2322834)). Qed.
Lemma lem2322837 : term307 = True.
Proof. exact (EQ_MP (@lem2322836) (@lem2322834)). Qed.
Lemma lem2322838 : term306 = True.
Proof. exact (TRANS (@lem2322833) (@lem2322837)). Qed.
Lemma lem2322839 : True = term306.
Proof. exact (SYM (@lem2322838)). Qed.
Lemma lem2322840 : term306.
Proof. exact (EQ_MP (@lem2322839) (@lem0)). Qed.
Lemma lem2322841 : term460.
Proof. exact (@lem2322830 (@lem2322840)). Qed.
Lemma lem2322843 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322844 : term306 = term307.
Proof. exact (@lem2322843 (NUMERAL 0) term57). Qed.
Lemma lem2322845 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322846 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322847 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322846 h1) (fun h1 : term307 = True => @lem2322845)). Qed.
Lemma lem2322848 : term307 = True.
Proof. exact (EQ_MP (@lem2322847) (@lem2322845)). Qed.
Lemma lem2322849 : term306 = True.
Proof. exact (TRANS (@lem2322844) (@lem2322848)). Qed.
Lemma lem2322850 : True = term306.
Proof. exact (SYM (@lem2322849)). Qed.
Lemma lem2322851 : term306.
Proof. exact (EQ_MP (@lem2322850) (@lem0)). Qed.
Lemma lem2322852 : term458 = term461.
Proof. exact (@lem2322841 (@lem2322851)). Qed.
Lemma lem2322854 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322855 : term179 = term180.
Proof. exact (@lem2322854 term57 term57). Qed.
Lemma lem2322856 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322857 : term182 = term57.
Proof. exact (EQ_MP (@lem2322856) (@lem940073)). Qed.
Lemma lem2322858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322859 : term180 = term56.
Proof. exact (MK_COMB (@lem2322858) (@lem2322857)). Qed.
Lemma lem2322860 : term179 = term56.
Proof. exact (TRANS (@lem2322855) (@lem2322859)). Qed.
Lemma lem2322862 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322863 : term318 = term159.
Proof. exact (@lem2322862 term57). Qed.
Lemma lem2322864 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322865 : term462 = term456.
Proof. exact (MK_COMB (@lem2322864) (@lem2322863)). Qed.
Lemma lem2322866 : term461 = term306.
Proof. exact (MK_COMB (@lem2322865) (@lem2322860)). Qed.
Lemma lem2322868 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322869 : term306 = term307.
Proof. exact (@lem2322868 (NUMERAL 0) term57). Qed.
Lemma lem2322870 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322871 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322872 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322871 h1) (fun h1 : term307 = True => @lem2322870)). Qed.
Lemma lem2322873 : term307 = True.
Proof. exact (EQ_MP (@lem2322872) (@lem2322870)). Qed.
Lemma lem2322874 : term306 = True.
Proof. exact (TRANS (@lem2322869) (@lem2322873)). Qed.
Lemma lem2322875 : term461 = True.
Proof. exact (TRANS (@lem2322866) (@lem2322874)). Qed.
Lemma lem2322876 : term458 = True.
Proof. exact (TRANS (@lem2322852) (@lem2322875)). Qed.
Lemma lem2322877 : term306 = True.
Proof. exact (TRANS (@lem2322829) (@lem2322876)). Qed.
Lemma lem2322878 : term455 = True.
Proof. exact (TRANS (@lem2322820) (@lem2322877)). Qed.
Lemma lem2322879 : True = term455.
Proof. exact (SYM (@lem2322878)). Qed.
Lemma lem2322880 : term455.
Proof. exact (EQ_MP (@lem2322879) (@lem0)). Qed.
Lemma lem2322881 (x : int) (y : int) (h1 : term433 x y) : term491 x y.
Proof. exact (conj (@lem2322880) (@lem2322816 x y h1)). Qed.
Lemma lem2322883 (x : real) (y : real) : term464 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2322884 (x : int) (y : int) : term492 x y.
Proof. exact (@lem2322883 term56 (term331 x y)). Qed.
Lemma lem2322885 (x : int) (y : int) (h1 : term433 x y) : term493 x y.
Proof. exact (@lem2322884 x y (@lem2322881 x y h1)). Qed.
Lemma lem2322886 (x : int) (y : int) : (term494 x y) = (term331 x y).
Proof. exact (@lem1982733 (term331 x y)). Qed.
Lemma lem2322887 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2322888 (x : int) (y : int) : (term495 x y) = (term332 x y).
Proof. exact (MK_COMB (@lem2322887) (@lem2322886 x y)). Qed.
Lemma lem2322889 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2322890 (x : int) (y : int) : (term493 x y) = (term333 x y).
Proof. exact (MK_COMB (@lem2322888 x y) (@lem2322889)). Qed.
Lemma lem2322891 (x : int) (y : int) (h1 : term433 x y) : term333 x y.
Proof. exact (EQ_MP (@lem2322890 x y) (@lem2322885 x y h1)). Qed.
Lemma lem2322893 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2322894 : term455 = term306.
Proof. exact (@lem2322893 term159 term56). Qed.
Lemma lem2322896 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322897 : term56 = term168.
Proof. exact (@lem2322896 term57). Qed.
Lemma lem2322899 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322900 : term159 = term321.
Proof. exact (@lem2322899 (NUMERAL 0)). Qed.
Lemma lem2322901 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322902 : term456 = term457.
Proof. exact (MK_COMB (@lem2322901) (@lem2322900)). Qed.
Lemma lem2322903 : term306 = term458.
Proof. exact (MK_COMB (@lem2322902) (@lem2322897)). Qed.
Lemma lem2322904 : term459.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2322906 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322907 : term306 = term307.
Proof. exact (@lem2322906 (NUMERAL 0) term57). Qed.
Lemma lem2322908 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322909 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322910 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322909 h1) (fun h1 : term307 = True => @lem2322908)). Qed.
Lemma lem2322911 : term307 = True.
Proof. exact (EQ_MP (@lem2322910) (@lem2322908)). Qed.
Lemma lem2322912 : term306 = True.
Proof. exact (TRANS (@lem2322907) (@lem2322911)). Qed.
Lemma lem2322913 : True = term306.
Proof. exact (SYM (@lem2322912)). Qed.
Lemma lem2322914 : term306.
Proof. exact (EQ_MP (@lem2322913) (@lem0)). Qed.
Lemma lem2322915 : term460.
Proof. exact (@lem2322904 (@lem2322914)). Qed.
Lemma lem2322917 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322918 : term306 = term307.
Proof. exact (@lem2322917 (NUMERAL 0) term57). Qed.
Lemma lem2322919 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322920 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322921 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322920 h1) (fun h1 : term307 = True => @lem2322919)). Qed.
Lemma lem2322922 : term307 = True.
Proof. exact (EQ_MP (@lem2322921) (@lem2322919)). Qed.
Lemma lem2322923 : term306 = True.
Proof. exact (TRANS (@lem2322918) (@lem2322922)). Qed.
Lemma lem2322924 : True = term306.
Proof. exact (SYM (@lem2322923)). Qed.
Lemma lem2322925 : term306.
Proof. exact (EQ_MP (@lem2322924) (@lem0)). Qed.
Lemma lem2322926 : term458 = term461.
Proof. exact (@lem2322915 (@lem2322925)). Qed.
Lemma lem2322928 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2322929 : term179 = term180.
Proof. exact (@lem2322928 term57 term57). Qed.
Lemma lem2322930 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2322931 : term182 = term57.
Proof. exact (EQ_MP (@lem2322930) (@lem940073)). Qed.
Lemma lem2322932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2322933 : term180 = term56.
Proof. exact (MK_COMB (@lem2322932) (@lem2322931)). Qed.
Lemma lem2322934 : term179 = term56.
Proof. exact (TRANS (@lem2322929) (@lem2322933)). Qed.
Lemma lem2322936 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2322937 : term318 = term159.
Proof. exact (@lem2322936 term57). Qed.
Lemma lem2322938 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2322939 : term462 = term456.
Proof. exact (MK_COMB (@lem2322938) (@lem2322937)). Qed.
Lemma lem2322940 : term461 = term306.
Proof. exact (MK_COMB (@lem2322939) (@lem2322934)). Qed.
Lemma lem2322942 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322943 : term306 = term307.
Proof. exact (@lem2322942 (NUMERAL 0) term57). Qed.
Lemma lem2322944 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322945 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322946 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322945 h1) (fun h1 : term307 = True => @lem2322944)). Qed.
Lemma lem2322947 : term307 = True.
Proof. exact (EQ_MP (@lem2322946) (@lem2322944)). Qed.
Lemma lem2322948 : term306 = True.
Proof. exact (TRANS (@lem2322943) (@lem2322947)). Qed.
Lemma lem2322949 : term461 = True.
Proof. exact (TRANS (@lem2322940) (@lem2322948)). Qed.
Lemma lem2322950 : term458 = True.
Proof. exact (TRANS (@lem2322926) (@lem2322949)). Qed.
Lemma lem2322951 : term306 = True.
Proof. exact (TRANS (@lem2322903) (@lem2322950)). Qed.
Lemma lem2322952 : term455 = True.
Proof. exact (TRANS (@lem2322894) (@lem2322951)). Qed.
Lemma lem2322953 : True = term455.
Proof. exact (SYM (@lem2322952)). Qed.
Lemma lem2322954 : term455.
Proof. exact (EQ_MP (@lem2322953) (@lem0)). Qed.
Lemma lem2322955 (x : int) (y : int) (h1 : term433 x y) : term496 x y.
Proof. exact (conj (@lem2322954) (@lem2322817 x y h1)). Qed.
Lemma lem2322957 (x : real) (y : real) : term464 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2322958 (x : int) (y : int) : term497 x y.
Proof. exact (@lem2322957 term56 (term218 x y)). Qed.
Lemma lem2322959 (x : int) (y : int) (h1 : term433 x y) : term498 x y.
Proof. exact (@lem2322958 x y (@lem2322955 x y h1)). Qed.
Lemma lem2322960 (x : int) (y : int) : (term499 x y) = (term218 x y).
Proof. exact (@lem1982733 (term218 x y)). Qed.
Lemma lem2322961 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2322962 (x : int) (y : int) : (term500 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem2322961) (@lem2322960 x y)). Qed.
Lemma lem2322963 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2322964 (x : int) (y : int) : (term498 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem2322962 x y) (@lem2322963)). Qed.
Lemma lem2322965 (x : int) (y : int) (h1 : term433 x y) : term221 x y.
Proof. exact (EQ_MP (@lem2322964 x y) (@lem2322959 x y h1)). Qed.
Lemma lem2322966 (x : int) (y : int) (h1 : term433 x y) : term421 x y.
Proof. exact (conj (@lem2322965 x y h1) (@lem2322891 x y h1)). Qed.
Lemma lem2322968 (x : real) (y : real) : term501 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2322969 (x : int) (y : int) : term502 x y.
Proof. exact (@lem2322968 (term218 x y) (term331 x y)). Qed.
Lemma lem2322970 (x : int) (y : int) (h1 : term433 x y) : term503 x y.
Proof. exact (@lem2322969 x y (@lem2322966 x y h1)). Qed.
Lemma lem2322971 (x : int) (y : int) : (term504 x y) = (term505 x y).
Proof. exact (@lem1982753 (real_of_int x) (term156 x) (term201 y) (term506 y)). Qed.
Lemma lem2322972 (x : int) : (term298 x) = (term299 x).
Proof. exact (@lem1982715 term166 (real_of_int x)). Qed.
Lemma lem2322974 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2322975 : term56 = term168.
Proof. exact (@lem2322974 term57). Qed.
Lemma lem2322977 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2322978 : term166 = term171.
Proof. exact (@lem2322977 term57). Qed.
Lemma lem2322979 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2322980 : term300 = term301.
Proof. exact (MK_COMB (@lem2322979) (@lem2322978)). Qed.
Lemma lem2322981 : term302 = term303.
Proof. exact (MK_COMB (@lem2322980) (@lem2322975)). Qed.
Lemma lem2322982 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2322984 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322985 : term306 = term307.
Proof. exact (@lem2322984 (NUMERAL 0) term57). Qed.
Lemma lem2322986 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322987 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322988 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322987 h1) (fun h1 : term307 = True => @lem2322986)). Qed.
Lemma lem2322989 : term307 = True.
Proof. exact (EQ_MP (@lem2322988) (@lem2322986)). Qed.
Lemma lem2322990 : term306 = True.
Proof. exact (TRANS (@lem2322985) (@lem2322989)). Qed.
Lemma lem2322991 : True = term306.
Proof. exact (SYM (@lem2322990)). Qed.
Lemma lem2322992 : term306.
Proof. exact (EQ_MP (@lem2322991) (@lem0)). Qed.
Lemma lem2322993 : term309.
Proof. exact (@lem2322982 (@lem2322992)). Qed.
Lemma lem2322995 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2322996 : term306 = term307.
Proof. exact (@lem2322995 (NUMERAL 0) term57). Qed.
Lemma lem2322997 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2322998 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2322999 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2322998 h1) (fun h1 : term307 = True => @lem2322997)). Qed.
Lemma lem2323000 : term307 = True.
Proof. exact (EQ_MP (@lem2322999) (@lem2322997)). Qed.
Lemma lem2323001 : term306 = True.
Proof. exact (TRANS (@lem2322996) (@lem2323000)). Qed.
Lemma lem2323002 : True = term306.
Proof. exact (SYM (@lem2323001)). Qed.
Lemma lem2323003 : term306.
Proof. exact (EQ_MP (@lem2323002) (@lem0)). Qed.
Lemma lem2323004 : term310.
Proof. exact (@lem2322993 (@lem2323003)). Qed.
Lemma lem2323006 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323007 : term306 = term307.
Proof. exact (@lem2323006 (NUMERAL 0) term57). Qed.
Lemma lem2323008 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323009 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323010 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323009 h1) (fun h1 : term307 = True => @lem2323008)). Qed.
Lemma lem2323011 : term307 = True.
Proof. exact (EQ_MP (@lem2323010) (@lem2323008)). Qed.
Lemma lem2323012 : term306 = True.
Proof. exact (TRANS (@lem2323007) (@lem2323011)). Qed.
Lemma lem2323013 : True = term306.
Proof. exact (SYM (@lem2323012)). Qed.
Lemma lem2323014 : term306.
Proof. exact (EQ_MP (@lem2323013) (@lem0)). Qed.
Lemma lem2323015 : term311.
Proof. exact (@lem2323004 (@lem2323014)). Qed.
Lemma lem2323017 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2323018 : term179 = term180.
Proof. exact (@lem2323017 term57 term57). Qed.
Lemma lem2323019 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323020 : term182 = term57.
Proof. exact (EQ_MP (@lem2323019) (@lem940073)). Qed.
Lemma lem2323021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323022 : term180 = term56.
Proof. exact (MK_COMB (@lem2323021) (@lem2323020)). Qed.
Lemma lem2323023 : term179 = term56.
Proof. exact (TRANS (@lem2323018) (@lem2323022)). Qed.
Lemma lem2323025 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323026 : term174 = term185.
Proof. exact (@lem2323025 term57 term57). Qed.
Lemma lem2323027 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323028 : term182 = term57.
Proof. exact (EQ_MP (@lem2323027) (@lem940073)). Qed.
Lemma lem2323029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323030 : term180 = term56.
Proof. exact (MK_COMB (@lem2323029) (@lem2323028)). Qed.
Lemma lem2323031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323032 : term185 = term166.
Proof. exact (MK_COMB (@lem2323031) (@lem2323030)). Qed.
Lemma lem2323033 : term174 = term166.
Proof. exact (TRANS (@lem2323026) (@lem2323032)). Qed.
Lemma lem2323034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323035 : term312 = term300.
Proof. exact (MK_COMB (@lem2323034) (@lem2323033)). Qed.
Lemma lem2323036 : term313 = term302.
Proof. exact (MK_COMB (@lem2323035) (@lem2323023)). Qed.
Lemma lem2323038 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2323039 : term302 = term159.
Proof. exact (@lem2323038 term57). Qed.
Lemma lem2323040 : term313 = term159.
Proof. exact (TRANS (@lem2323036) (@lem2323039)). Qed.
Lemma lem2323041 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2323042 : term315 = term316.
Proof. exact (MK_COMB (@lem2323041) (@lem2323040)). Qed.
Lemma lem2323043 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2323044 : term317 = term318.
Proof. exact (MK_COMB (@lem2323042) (@lem2323043)). Qed.
Lemma lem2323046 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2323047 : term318 = term159.
Proof. exact (@lem2323046 term57). Qed.
Lemma lem2323048 : term317 = term159.
Proof. exact (TRANS (@lem2323044) (@lem2323047)). Qed.
Lemma lem2323050 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2323051 : term179 = term180.
Proof. exact (@lem2323050 term57 term57). Qed.
Lemma lem2323052 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323053 : term182 = term57.
Proof. exact (EQ_MP (@lem2323052) (@lem940073)). Qed.
Lemma lem2323054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323055 : term180 = term56.
Proof. exact (MK_COMB (@lem2323054) (@lem2323053)). Qed.
Lemma lem2323056 : term179 = term56.
Proof. exact (TRANS (@lem2323051) (@lem2323055)). Qed.
Lemma lem2323057 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2323058 : term320 = term318.
Proof. exact (MK_COMB (@lem2323057) (@lem2323056)). Qed.
Lemma lem2323060 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2323061 : term318 = term159.
Proof. exact (@lem2323060 term57). Qed.
Lemma lem2323062 : term320 = term159.
Proof. exact (TRANS (@lem2323058) (@lem2323061)). Qed.
Lemma lem2323063 : term159 = term320.
Proof. exact (SYM (@lem2323062)). Qed.
Lemma lem2323064 : term317 = term320.
Proof. exact (TRANS (@lem2323048) (@lem2323063)). Qed.
Lemma lem2323065 : term303 = term321.
Proof. exact (@lem2323015 (@lem2323064)). Qed.
Lemma lem2323066 : term302 = term321.
Proof. exact (TRANS (@lem2322981) (@lem2323065)). Qed.
Lemma lem2323068 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2323069 : term321 = term159.
Proof. exact (@lem2323068 term159). Qed.
Lemma lem2323070 : term302 = term159.
Proof. exact (TRANS (@lem2323066) (@lem2323069)). Qed.
Lemma lem2323071 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2323072 : term322 = term316.
Proof. exact (MK_COMB (@lem2323071) (@lem2323070)). Qed.
Lemma lem2323073 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2323074 (x : int) : (term299 x) = (term323 x).
Proof. exact (MK_COMB (@lem2323072) (@lem2323073 x)). Qed.
Lemma lem2323075 (x : int) : (term298 x) = (term323 x).
Proof. exact (TRANS (@lem2322972 x) (@lem2323074 x)). Qed.
Lemma lem2323076 (x : int) : (term323 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2323077 (x : int) : (term298 x) = term159.
Proof. exact (TRANS (@lem2323075 x) (@lem2323076 x)). Qed.
Lemma lem2323078 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323079 (x : int) : (term324 x) = term325.
Proof. exact (MK_COMB (@lem2323078) (@lem2323077 x)). Qed.
Lemma lem2323080 (y : int) : (term507 y) = (term508 y).
Proof. exact (@lem1982753 (term156 y) (real_of_int y) term166 term166). Qed.
Lemma lem2323081 (y : int) : (term373 y) = (term299 y).
Proof. exact (@lem1982713 term166 (real_of_int y)). Qed.
Lemma lem2323083 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2323084 : term56 = term168.
Proof. exact (@lem2323083 term57). Qed.
Lemma lem2323086 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2323087 : term166 = term171.
Proof. exact (@lem2323086 term57). Qed.
Lemma lem2323088 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323089 : term300 = term301.
Proof. exact (MK_COMB (@lem2323088) (@lem2323087)). Qed.
Lemma lem2323090 : term302 = term303.
Proof. exact (MK_COMB (@lem2323089) (@lem2323084)). Qed.
Lemma lem2323091 : term304.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2323093 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323094 : term306 = term307.
Proof. exact (@lem2323093 (NUMERAL 0) term57). Qed.
Lemma lem2323095 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323096 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323097 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323096 h1) (fun h1 : term307 = True => @lem2323095)). Qed.
Lemma lem2323098 : term307 = True.
Proof. exact (EQ_MP (@lem2323097) (@lem2323095)). Qed.
Lemma lem2323099 : term306 = True.
Proof. exact (TRANS (@lem2323094) (@lem2323098)). Qed.
Lemma lem2323100 : True = term306.
Proof. exact (SYM (@lem2323099)). Qed.
Lemma lem2323101 : term306.
Proof. exact (EQ_MP (@lem2323100) (@lem0)). Qed.
Lemma lem2323102 : term309.
Proof. exact (@lem2323091 (@lem2323101)). Qed.
Lemma lem2323104 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323105 : term306 = term307.
Proof. exact (@lem2323104 (NUMERAL 0) term57). Qed.
Lemma lem2323106 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323107 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323108 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323107 h1) (fun h1 : term307 = True => @lem2323106)). Qed.
Lemma lem2323109 : term307 = True.
Proof. exact (EQ_MP (@lem2323108) (@lem2323106)). Qed.
Lemma lem2323110 : term306 = True.
Proof. exact (TRANS (@lem2323105) (@lem2323109)). Qed.
Lemma lem2323111 : True = term306.
Proof. exact (SYM (@lem2323110)). Qed.
Lemma lem2323112 : term306.
Proof. exact (EQ_MP (@lem2323111) (@lem0)). Qed.
Lemma lem2323113 : term310.
Proof. exact (@lem2323102 (@lem2323112)). Qed.
Lemma lem2323115 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323116 : term306 = term307.
Proof. exact (@lem2323115 (NUMERAL 0) term57). Qed.
Lemma lem2323117 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323118 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323119 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323118 h1) (fun h1 : term307 = True => @lem2323117)). Qed.
Lemma lem2323120 : term307 = True.
Proof. exact (EQ_MP (@lem2323119) (@lem2323117)). Qed.
Lemma lem2323121 : term306 = True.
Proof. exact (TRANS (@lem2323116) (@lem2323120)). Qed.
Lemma lem2323122 : True = term306.
Proof. exact (SYM (@lem2323121)). Qed.
Lemma lem2323123 : term306.
Proof. exact (EQ_MP (@lem2323122) (@lem0)). Qed.
Lemma lem2323124 : term311.
Proof. exact (@lem2323113 (@lem2323123)). Qed.
Lemma lem2323126 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2323127 : term179 = term180.
Proof. exact (@lem2323126 term57 term57). Qed.
Lemma lem2323128 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323129 : term182 = term57.
Proof. exact (EQ_MP (@lem2323128) (@lem940073)). Qed.
Lemma lem2323130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323131 : term180 = term56.
Proof. exact (MK_COMB (@lem2323130) (@lem2323129)). Qed.
Lemma lem2323132 : term179 = term56.
Proof. exact (TRANS (@lem2323127) (@lem2323131)). Qed.
Lemma lem2323134 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323135 : term174 = term185.
Proof. exact (@lem2323134 term57 term57). Qed.
Lemma lem2323136 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323137 : term182 = term57.
Proof. exact (EQ_MP (@lem2323136) (@lem940073)). Qed.
Lemma lem2323138 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323139 : term180 = term56.
Proof. exact (MK_COMB (@lem2323138) (@lem2323137)). Qed.
Lemma lem2323140 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323141 : term185 = term166.
Proof. exact (MK_COMB (@lem2323140) (@lem2323139)). Qed.
Lemma lem2323142 : term174 = term166.
Proof. exact (TRANS (@lem2323135) (@lem2323141)). Qed.
Lemma lem2323143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323144 : term312 = term300.
Proof. exact (MK_COMB (@lem2323143) (@lem2323142)). Qed.
Lemma lem2323145 : term313 = term302.
Proof. exact (MK_COMB (@lem2323144) (@lem2323132)). Qed.
Lemma lem2323147 (m : nat) : (term314 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2323148 : term302 = term159.
Proof. exact (@lem2323147 term57). Qed.
Lemma lem2323149 : term313 = term159.
Proof. exact (TRANS (@lem2323145) (@lem2323148)). Qed.
Lemma lem2323150 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2323151 : term315 = term316.
Proof. exact (MK_COMB (@lem2323150) (@lem2323149)). Qed.
Lemma lem2323152 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2323153 : term317 = term318.
Proof. exact (MK_COMB (@lem2323151) (@lem2323152)). Qed.
Lemma lem2323155 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2323156 : term318 = term159.
Proof. exact (@lem2323155 term57). Qed.
Lemma lem2323157 : term317 = term159.
Proof. exact (TRANS (@lem2323153) (@lem2323156)). Qed.
Lemma lem2323159 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2323160 : term179 = term180.
Proof. exact (@lem2323159 term57 term57). Qed.
Lemma lem2323161 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323162 : term182 = term57.
Proof. exact (EQ_MP (@lem2323161) (@lem940073)). Qed.
Lemma lem2323163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323164 : term180 = term56.
Proof. exact (MK_COMB (@lem2323163) (@lem2323162)). Qed.
Lemma lem2323165 : term179 = term56.
Proof. exact (TRANS (@lem2323160) (@lem2323164)). Qed.
Lemma lem2323166 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem2323167 : term320 = term318.
Proof. exact (MK_COMB (@lem2323166) (@lem2323165)). Qed.
Lemma lem2323169 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2323170 : term318 = term159.
Proof. exact (@lem2323169 term57). Qed.
Lemma lem2323171 : term320 = term159.
Proof. exact (TRANS (@lem2323167) (@lem2323170)). Qed.
Lemma lem2323172 : term159 = term320.
Proof. exact (SYM (@lem2323171)). Qed.
Lemma lem2323173 : term317 = term320.
Proof. exact (TRANS (@lem2323157) (@lem2323172)). Qed.
Lemma lem2323174 : term303 = term321.
Proof. exact (@lem2323124 (@lem2323173)). Qed.
Lemma lem2323175 : term302 = term321.
Proof. exact (TRANS (@lem2323090) (@lem2323174)). Qed.
Lemma lem2323177 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2323178 : term321 = term159.
Proof. exact (@lem2323177 term159). Qed.
Lemma lem2323179 : term302 = term159.
Proof. exact (TRANS (@lem2323175) (@lem2323178)). Qed.
Lemma lem2323180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2323181 : term322 = term316.
Proof. exact (MK_COMB (@lem2323180) (@lem2323179)). Qed.
Lemma lem2323182 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2323183 (y : int) : (term299 y) = (term323 y).
Proof. exact (MK_COMB (@lem2323181) (@lem2323182 y)). Qed.
Lemma lem2323184 (y : int) : (term373 y) = (term323 y).
Proof. exact (TRANS (@lem2323081 y) (@lem2323183 y)). Qed.
Lemma lem2323185 (y : int) : (term323 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2323186 (y : int) : (term373 y) = term159.
Proof. exact (TRANS (@lem2323184 y) (@lem2323185 y)). Qed.
Lemma lem2323187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323188 (y : int) : (term374 y) = term325.
Proof. exact (MK_COMB (@lem2323187) (@lem2323186 y)). Qed.
Lemma lem2323190 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2323191 : term166 = term171.
Proof. exact (@lem2323190 term57). Qed.
Lemma lem2323193 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2323194 : term166 = term171.
Proof. exact (@lem2323193 term57). Qed.
Lemma lem2323195 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323196 : term300 = term301.
Proof. exact (MK_COMB (@lem2323195) (@lem2323194)). Qed.
Lemma lem2323197 : term509 = term510.
Proof. exact (MK_COMB (@lem2323196) (@lem2323191)). Qed.
Lemma lem2323198 : term511.
Proof. exact (@lem1981473 term166 term56 term166 term56 term512 term56). Qed.
Lemma lem2323200 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323201 : term306 = term307.
Proof. exact (@lem2323200 (NUMERAL 0) term57). Qed.
Lemma lem2323202 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323203 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323204 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323203 h1) (fun h1 : term307 = True => @lem2323202)). Qed.
Lemma lem2323205 : term307 = True.
Proof. exact (EQ_MP (@lem2323204) (@lem2323202)). Qed.
Lemma lem2323206 : term306 = True.
Proof. exact (TRANS (@lem2323201) (@lem2323205)). Qed.
Lemma lem2323207 : True = term306.
Proof. exact (SYM (@lem2323206)). Qed.
Lemma lem2323208 : term306.
Proof. exact (EQ_MP (@lem2323207) (@lem0)). Qed.
Lemma lem2323209 : term513.
Proof. exact (@lem2323198 (@lem2323208)). Qed.
Lemma lem2323211 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323212 : term306 = term307.
Proof. exact (@lem2323211 (NUMERAL 0) term57). Qed.
Lemma lem2323213 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323214 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323215 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323214 h1) (fun h1 : term307 = True => @lem2323213)). Qed.
Lemma lem2323216 : term307 = True.
Proof. exact (EQ_MP (@lem2323215) (@lem2323213)). Qed.
Lemma lem2323217 : term306 = True.
Proof. exact (TRANS (@lem2323212) (@lem2323216)). Qed.
Lemma lem2323218 : True = term306.
Proof. exact (SYM (@lem2323217)). Qed.
Lemma lem2323219 : term306.
Proof. exact (EQ_MP (@lem2323218) (@lem0)). Qed.
Lemma lem2323220 : term514.
Proof. exact (@lem2323209 (@lem2323219)). Qed.
Lemma lem2323222 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323223 : term306 = term307.
Proof. exact (@lem2323222 (NUMERAL 0) term57). Qed.
Lemma lem2323224 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323225 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323226 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323225 h1) (fun h1 : term307 = True => @lem2323224)). Qed.
Lemma lem2323227 : term307 = True.
Proof. exact (EQ_MP (@lem2323226) (@lem2323224)). Qed.
Lemma lem2323228 : term306 = True.
Proof. exact (TRANS (@lem2323223) (@lem2323227)). Qed.
Lemma lem2323229 : True = term306.
Proof. exact (SYM (@lem2323228)). Qed.
Lemma lem2323230 : term306.
Proof. exact (EQ_MP (@lem2323229) (@lem0)). Qed.
Lemma lem2323231 : term515.
Proof. exact (@lem2323220 (@lem2323230)). Qed.
Lemma lem2323233 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323234 : term174 = term185.
Proof. exact (@lem2323233 term57 term57). Qed.
Lemma lem2323235 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323236 : term182 = term57.
Proof. exact (EQ_MP (@lem2323235) (@lem940073)). Qed.
Lemma lem2323237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323238 : term180 = term56.
Proof. exact (MK_COMB (@lem2323237) (@lem2323236)). Qed.
Lemma lem2323239 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323240 : term185 = term166.
Proof. exact (MK_COMB (@lem2323239) (@lem2323238)). Qed.
Lemma lem2323241 : term174 = term166.
Proof. exact (TRANS (@lem2323234) (@lem2323240)). Qed.
Lemma lem2323243 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323244 : term174 = term185.
Proof. exact (@lem2323243 term57 term57). Qed.
Lemma lem2323245 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323246 : term182 = term57.
Proof. exact (EQ_MP (@lem2323245) (@lem940073)). Qed.
Lemma lem2323247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323248 : term180 = term56.
Proof. exact (MK_COMB (@lem2323247) (@lem2323246)). Qed.
Lemma lem2323249 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323250 : term185 = term166.
Proof. exact (MK_COMB (@lem2323249) (@lem2323248)). Qed.
Lemma lem2323251 : term174 = term166.
Proof. exact (TRANS (@lem2323244) (@lem2323250)). Qed.
Lemma lem2323252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323253 : term312 = term300.
Proof. exact (MK_COMB (@lem2323252) (@lem2323251)). Qed.
Lemma lem2323254 : term516 = term509.
Proof. exact (MK_COMB (@lem2323253) (@lem2323241)). Qed.
Lemma lem2323255 : term509 = term517.
Proof. exact (@lem1367763 term57 term57). Qed.
Lemma lem2323256 : term518 = term519.
Proof. exact (@lem706885). Qed.
Lemma lem2323257 : (term518 = term519) = (term520 = term521).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term519). Qed.
Lemma lem2323258 : term520 = term521.
Proof. exact (EQ_MP (@lem2323257) (@lem2323256)). Qed.
Lemma lem2323259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323260 : term522 = term523.
Proof. exact (MK_COMB (@lem2323259) (@lem2323258)). Qed.
Lemma lem2323261 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323262 : term517 = term512.
Proof. exact (MK_COMB (@lem2323261) (@lem2323260)). Qed.
Lemma lem2323263 : term509 = term512.
Proof. exact (TRANS (@lem2323255) (@lem2323262)). Qed.
Lemma lem2323264 : term516 = term512.
Proof. exact (TRANS (@lem2323254) (@lem2323263)). Qed.
Lemma lem2323265 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2323266 : term524 = term525.
Proof. exact (MK_COMB (@lem2323265) (@lem2323264)). Qed.
Lemma lem2323267 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2323268 : term526 = term527.
Proof. exact (MK_COMB (@lem2323266) (@lem2323267)). Qed.
Lemma lem2323270 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323271 : term527 = term528.
Proof. exact (@lem2323270 term521 term57). Qed.
Lemma lem2323272 : term529 = term519.
Proof. exact (@lem996237 term519). Qed.
Lemma lem2323273 : (term529 = term519) = (term530 = term521).
Proof. exact (@lem1007663 term519 (BIT1 0) term519). Qed.
Lemma lem2323274 : term530 = term521.
Proof. exact (EQ_MP (@lem2323273) (@lem2323272)). Qed.
Lemma lem2323275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323276 : term531 = term523.
Proof. exact (MK_COMB (@lem2323275) (@lem2323274)). Qed.
Lemma lem2323277 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323278 : term528 = term512.
Proof. exact (MK_COMB (@lem2323277) (@lem2323276)). Qed.
Lemma lem2323279 : term527 = term512.
Proof. exact (TRANS (@lem2323271) (@lem2323278)). Qed.
Lemma lem2323280 : term526 = term512.
Proof. exact (TRANS (@lem2323268) (@lem2323279)). Qed.
Lemma lem2323282 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2323283 : term179 = term180.
Proof. exact (@lem2323282 term57 term57). Qed.
Lemma lem2323284 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323285 : term182 = term57.
Proof. exact (EQ_MP (@lem2323284) (@lem940073)). Qed.
Lemma lem2323286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323287 : term180 = term56.
Proof. exact (MK_COMB (@lem2323286) (@lem2323285)). Qed.
Lemma lem2323288 : term179 = term56.
Proof. exact (TRANS (@lem2323283) (@lem2323287)). Qed.
Lemma lem2323289 : term525 = term525.
Proof. exact (eq_refl term525). Qed.
Lemma lem2323290 : term532 = term527.
Proof. exact (MK_COMB (@lem2323289) (@lem2323288)). Qed.
Lemma lem2323292 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323293 : term527 = term528.
Proof. exact (@lem2323292 term521 term57). Qed.
Lemma lem2323294 : term529 = term519.
Proof. exact (@lem996237 term519). Qed.
Lemma lem2323295 : (term529 = term519) = (term530 = term521).
Proof. exact (@lem1007663 term519 (BIT1 0) term519). Qed.
Lemma lem2323296 : term530 = term521.
Proof. exact (EQ_MP (@lem2323295) (@lem2323294)). Qed.
Lemma lem2323297 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323298 : term531 = term523.
Proof. exact (MK_COMB (@lem2323297) (@lem2323296)). Qed.
Lemma lem2323299 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323300 : term528 = term512.
Proof. exact (MK_COMB (@lem2323299) (@lem2323298)). Qed.
Lemma lem2323301 : term527 = term512.
Proof. exact (TRANS (@lem2323293) (@lem2323300)). Qed.
Lemma lem2323302 : term532 = term512.
Proof. exact (TRANS (@lem2323290) (@lem2323301)). Qed.
Lemma lem2323303 : term512 = term532.
Proof. exact (SYM (@lem2323302)). Qed.
Lemma lem2323304 : term526 = term532.
Proof. exact (TRANS (@lem2323280) (@lem2323303)). Qed.
Lemma lem2323305 : term510 = term533.
Proof. exact (@lem2323231 (@lem2323304)). Qed.
Lemma lem2323306 : term509 = term533.
Proof. exact (TRANS (@lem2323197) (@lem2323305)). Qed.
Lemma lem2323308 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2323309 : term533 = term512.
Proof. exact (@lem2323308 term512). Qed.
Lemma lem2323310 : term509 = term512.
Proof. exact (TRANS (@lem2323306) (@lem2323309)). Qed.
Lemma lem2323311 (y : int) : (term508 y) = term534.
Proof. exact (MK_COMB (@lem2323188 y) (@lem2323310)). Qed.
Lemma lem2323312 (y : int) : (term507 y) = term534.
Proof. exact (TRANS (@lem2323080 y) (@lem2323311 y)). Qed.
Lemma lem2323313 : term534 = term512.
Proof. exact (@lem1982721 term512). Qed.
Lemma lem2323314 (y : int) : (term507 y) = term512.
Proof. exact (TRANS (@lem2323312 y) (@lem2323313)). Qed.
Lemma lem2323315 (x : int) (y : int) : (term505 x y) = term534.
Proof. exact (MK_COMB (@lem2323079 x) (@lem2323314 y)). Qed.
Lemma lem2323316 (x : int) (y : int) : (term504 x y) = term534.
Proof. exact (TRANS (@lem2322971 x y) (@lem2323315 x y)). Qed.
Lemma lem2323317 : term534 = term512.
Proof. exact (@lem1982721 term512). Qed.
Lemma lem2323318 (x : int) (y : int) : (term504 x y) = term512.
Proof. exact (TRANS (@lem2323316 x y) (@lem2323317)). Qed.
Lemma lem2323319 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2323320 (x : int) (y : int) : (term535 x y) = term536.
Proof. exact (MK_COMB (@lem2323319) (@lem2323318 x y)). Qed.
Lemma lem2323321 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2323322 (x : int) (y : int) : (term503 x y) = term537.
Proof. exact (MK_COMB (@lem2323320 x y) (@lem2323321)). Qed.
Lemma lem2323323 (x : int) (y : int) (h1 : term433 x y) : term537.
Proof. exact (EQ_MP (@lem2323322 x y) (@lem2322970 x y h1)). Qed.
Lemma lem2323325 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2323326 : term537 = term538.
Proof. exact (@lem2323325 term159 term512). Qed.
Lemma lem2323328 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2323329 : term512 = term533.
Proof. exact (@lem2323328 term521). Qed.
Lemma lem2323331 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2323332 : term159 = term321.
Proof. exact (@lem2323331 (NUMERAL 0)). Qed.
Lemma lem2323333 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323334 : term444 = term445.
Proof. exact (MK_COMB (@lem2323333) (@lem2323332)). Qed.
Lemma lem2323335 : term538 = term539.
Proof. exact (MK_COMB (@lem2323334) (@lem2323329)). Qed.
Lemma lem2323336 : term540.
Proof. exact (@lem1980026 term159 term56 term512 term56). Qed.
Lemma lem2323338 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323339 : term306 = term307.
Proof. exact (@lem2323338 (NUMERAL 0) term57). Qed.
Lemma lem2323340 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323341 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323342 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323341 h1) (fun h1 : term307 = True => @lem2323340)). Qed.
Lemma lem2323343 : term307 = True.
Proof. exact (EQ_MP (@lem2323342) (@lem2323340)). Qed.
Lemma lem2323344 : term306 = True.
Proof. exact (TRANS (@lem2323339) (@lem2323343)). Qed.
Lemma lem2323345 : True = term306.
Proof. exact (SYM (@lem2323344)). Qed.
Lemma lem2323346 : term306.
Proof. exact (EQ_MP (@lem2323345) (@lem0)). Qed.
Lemma lem2323347 : term541.
Proof. exact (@lem2323336 (@lem2323346)). Qed.
Lemma lem2323349 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323350 : term306 = term307.
Proof. exact (@lem2323349 (NUMERAL 0) term57). Qed.
Lemma lem2323351 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323352 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323353 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323352 h1) (fun h1 : term307 = True => @lem2323351)). Qed.
Lemma lem2323354 : term307 = True.
Proof. exact (EQ_MP (@lem2323353) (@lem2323351)). Qed.
Lemma lem2323355 : term306 = True.
Proof. exact (TRANS (@lem2323350) (@lem2323354)). Qed.
Lemma lem2323356 : True = term306.
Proof. exact (SYM (@lem2323355)). Qed.
Lemma lem2323357 : term306.
Proof. exact (EQ_MP (@lem2323356) (@lem0)). Qed.
Lemma lem2323358 : term539 = term542.
Proof. exact (@lem2323347 (@lem2323357)). Qed.
Lemma lem2323360 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323361 : term527 = term528.
Proof. exact (@lem2323360 term521 term57). Qed.
Lemma lem2323362 : term529 = term519.
Proof. exact (@lem996237 term519). Qed.
Lemma lem2323363 : (term529 = term519) = (term530 = term521).
Proof. exact (@lem1007663 term519 (BIT1 0) term519). Qed.
Lemma lem2323364 : term530 = term521.
Proof. exact (EQ_MP (@lem2323363) (@lem2323362)). Qed.
Lemma lem2323365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323366 : term531 = term523.
Proof. exact (MK_COMB (@lem2323365) (@lem2323364)). Qed.
Lemma lem2323367 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323368 : term528 = term512.
Proof. exact (MK_COMB (@lem2323367) (@lem2323366)). Qed.
Lemma lem2323369 : term527 = term512.
Proof. exact (TRANS (@lem2323361) (@lem2323368)). Qed.
Lemma lem2323371 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2323372 : term318 = term159.
Proof. exact (@lem2323371 term57). Qed.
Lemma lem2323373 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323374 : term450 = term444.
Proof. exact (MK_COMB (@lem2323373) (@lem2323372)). Qed.
Lemma lem2323375 : term542 = term538.
Proof. exact (MK_COMB (@lem2323374) (@lem2323369)). Qed.
Lemma lem2323377 (m : nat) (n : nat) : (term451 m n) = (term452 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2323378 : term538 = term543.
Proof. exact (@lem2323377 (NUMERAL 0) term521). Qed.
Lemma lem2323379 : term544 = term519.
Proof. exact (@lem912803). Qed.
Lemma lem2323380 (h1 : term544 = term519) : (term521 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term519 h1). Qed.
Lemma lem2323381 : (term544 = term519) = ((term521 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term544 = term519 => @lem2323380 h1) (fun h1 : (term521 = (NUMERAL 0)) = False => @lem2323379)). Qed.
Lemma lem2323382 : (term521 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2323381) (@lem2323379)). Qed.
Lemma lem2323383 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2323384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2323385 : term454 = (and True).
Proof. exact (MK_COMB (@lem2323384) (@lem2323383)). Qed.
Lemma lem2323386 : term543 = (True /\ False).
Proof. exact (MK_COMB (@lem2323385) (@lem2323382)). Qed.
Lemma lem2323388 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2323389 : term543 = False.
Proof. exact (TRANS (@lem2323386) (@lem2323388)). Qed.
Lemma lem2323390 : term538 = False.
Proof. exact (TRANS (@lem2323378) (@lem2323389)). Qed.
Lemma lem2323391 : term542 = False.
Proof. exact (TRANS (@lem2323375) (@lem2323390)). Qed.
Lemma lem2323392 : term539 = False.
Proof. exact (TRANS (@lem2323358) (@lem2323391)). Qed.
Lemma lem2323393 : term538 = False.
Proof. exact (TRANS (@lem2323335) (@lem2323392)). Qed.
Lemma lem2323394 : term537 = False.
Proof. exact (TRANS (@lem2323326) (@lem2323393)). Qed.
Lemma lem2323395 (x : int) (y : int) (h1 : term433 x y) : False.
Proof. exact (EQ_MP (@lem2323394) (@lem2323323 x y h1)). Qed.
Lemma lem2323396 (x : int) (y : int) (h1 : term435 x y) : term435 x y.
Proof. exact (h1). Qed.
Lemma lem2323397 (x : int) (y : int) (h1 : term435 x y) : term434 x y.
Proof. exact (proj2 (@lem2323396 x y h1)). Qed.
Lemma lem2323399 (x : int) (y : int) (h1 : term435 x y) : term330.
Proof. exact (proj2 (@lem2323397 x y h1)). Qed.
Lemma lem2323402 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2323403 : term330 = term443.
Proof. exact (@lem2323402 term159 term166). Qed.
Lemma lem2323405 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2323406 : term166 = term171.
Proof. exact (@lem2323405 term57). Qed.
Lemma lem2323408 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2323409 : term159 = term321.
Proof. exact (@lem2323408 (NUMERAL 0)). Qed.
Lemma lem2323410 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323411 : term444 = term445.
Proof. exact (MK_COMB (@lem2323410) (@lem2323409)). Qed.
Lemma lem2323412 : term443 = term446.
Proof. exact (MK_COMB (@lem2323411) (@lem2323406)). Qed.
Lemma lem2323413 : term447.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2323415 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323416 : term306 = term307.
Proof. exact (@lem2323415 (NUMERAL 0) term57). Qed.
Lemma lem2323417 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323418 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323419 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323418 h1) (fun h1 : term307 = True => @lem2323417)). Qed.
Lemma lem2323420 : term307 = True.
Proof. exact (EQ_MP (@lem2323419) (@lem2323417)). Qed.
Lemma lem2323421 : term306 = True.
Proof. exact (TRANS (@lem2323416) (@lem2323420)). Qed.
Lemma lem2323422 : True = term306.
Proof. exact (SYM (@lem2323421)). Qed.
Lemma lem2323423 : term306.
Proof. exact (EQ_MP (@lem2323422) (@lem0)). Qed.
Lemma lem2323424 : term448.
Proof. exact (@lem2323413 (@lem2323423)). Qed.
Lemma lem2323426 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2323427 : term306 = term307.
Proof. exact (@lem2323426 (NUMERAL 0) term57). Qed.
Lemma lem2323428 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323429 (h1 : term308 = (BIT1 0)) : term307 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2323430 : (term308 = (BIT1 0)) = (term307 = True).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323429 h1) (fun h1 : term307 = True => @lem2323428)). Qed.
Lemma lem2323431 : term307 = True.
Proof. exact (EQ_MP (@lem2323430) (@lem2323428)). Qed.
Lemma lem2323432 : term306 = True.
Proof. exact (TRANS (@lem2323427) (@lem2323431)). Qed.
Lemma lem2323433 : True = term306.
Proof. exact (SYM (@lem2323432)). Qed.
Lemma lem2323434 : term306.
Proof. exact (EQ_MP (@lem2323433) (@lem0)). Qed.
Lemma lem2323435 : term446 = term449.
Proof. exact (@lem2323424 (@lem2323434)). Qed.
Lemma lem2323437 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2323438 : term174 = term185.
Proof. exact (@lem2323437 term57 term57). Qed.
Lemma lem2323439 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2323440 : term182 = term57.
Proof. exact (EQ_MP (@lem2323439) (@lem940073)). Qed.
Lemma lem2323441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2323442 : term180 = term56.
Proof. exact (MK_COMB (@lem2323441) (@lem2323440)). Qed.
Lemma lem2323443 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2323444 : term185 = term166.
Proof. exact (MK_COMB (@lem2323443) (@lem2323442)). Qed.
Lemma lem2323445 : term174 = term166.
Proof. exact (TRANS (@lem2323438) (@lem2323444)). Qed.
Lemma lem2323447 (x : nat) : (term319 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2323448 : term318 = term159.
Proof. exact (@lem2323447 term57). Qed.
Lemma lem2323449 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323450 : term450 = term444.
Proof. exact (MK_COMB (@lem2323449) (@lem2323448)). Qed.
Lemma lem2323451 : term449 = term443.
Proof. exact (MK_COMB (@lem2323450) (@lem2323445)). Qed.
Lemma lem2323453 (m : nat) (n : nat) : (term451 m n) = (term452 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2323454 : term443 = term453.
Proof. exact (@lem2323453 (NUMERAL 0) term57). Qed.
Lemma lem2323455 : term308 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2323456 (h1 : term308 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2323457 : (term308 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term308 = (BIT1 0) => @lem2323456 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2323455)). Qed.
Lemma lem2323458 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2323457) (@lem2323455)). Qed.
Lemma lem2323459 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2323460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2323461 : term454 = (and True).
Proof. exact (MK_COMB (@lem2323460) (@lem2323459)). Qed.
Lemma lem2323462 : term453 = (True /\ False).
Proof. exact (MK_COMB (@lem2323461) (@lem2323458)). Qed.
Lemma lem2323464 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2323465 : term453 = False.
Proof. exact (TRANS (@lem2323462) (@lem2323464)). Qed.
Lemma lem2323466 : term443 = False.
Proof. exact (TRANS (@lem2323454) (@lem2323465)). Qed.
Lemma lem2323467 : term449 = False.
Proof. exact (TRANS (@lem2323451) (@lem2323466)). Qed.
Lemma lem2323468 : term446 = False.
Proof. exact (TRANS (@lem2323435) (@lem2323467)). Qed.
Lemma lem2323469 : term443 = False.
Proof. exact (TRANS (@lem2323412) (@lem2323468)). Qed.
Lemma lem2323470 : term330 = False.
Proof. exact (TRANS (@lem2323403) (@lem2323469)). Qed.
Lemma lem2323471 (x : int) (y : int) (h1 : term435 x y) : False.
Proof. exact (EQ_MP (@lem2323470) (@lem2323399 x y h1)). Qed.
Lemma lem2323472 (x : int) (y : int) (h1 : term437 x y) : False.
Proof. exact (or_elim (@lem2322812 x y h1) (fun h0 : term433 x y => @lem2323395 x y h0) (fun h0 : term435 x y => @lem2323471 x y h0)). Qed.
Lemma lem2323473 (x : int) (y : int) (h1 : term440 x y) : False.
Proof. exact (or_elim (@lem2322735 x y h1) (fun h0 : term411 x y => @lem2322811 x y h0) (fun h0 : term437 x y => @lem2323472 x y h0)). Qed.
Lemma lem2323474 (x : int) (y : int) (h1 : term442 x y) : False.
Proof. exact (or_elim (@lem2322142 x y h1) (fun h0 : term405 x y => @lem2322734 x y h0) (fun h0 : term440 x y => @lem2323473 x y h0)). Qed.
Lemma lem2323475 (x : int) (y : int) (h1 : term288 x y) : term288 x y.
Proof. exact (h1). Qed.
Lemma lem2323476 (x : int) (y : int) (h1 : term288 x y) : term442 x y.
Proof. exact (EQ_MP (@lem2322141 x y) (@lem2323475 x y h1)). Qed.
Lemma lem2323477 (x : int) (y : int) (h1 : term288 x y) : (term442 x y) = False.
Proof. exact (prop_ext (fun h2 : term442 x y => @lem2323474 x y h2) (fun h2 : False => @lem2323476 x y h1)). Qed.
Lemma lem2323478 (x : int) (y : int) (h1 : term288 x y) : False.
Proof. exact (EQ_MP (@lem2323477 x y h1) (@lem2323476 x y h1)). Qed.
Lemma lem2323479 (x : int) (h1 : term290 x) : term290 x.
Proof. exact (h1). Qed.
Lemma lem2323480 (x : int) (h1 : term290 x) : False.
Proof. exact (ex_elim (@lem2323479 x h1) (fun y : int => fun h0 : term289 x y => @lem2323478 x y h0)). Qed.
Lemma lem2323481 (h1 : term292) : term292.
Proof. exact (h1). Qed.
Lemma lem2323482 (h1 : term292) : False.
Proof. exact (ex_elim (@lem2323481 h1) (fun x : int => fun h0 : term291 x => @lem2323480 x h0)). Qed.
Lemma lem2323483 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem2323484 (h1 : term105) : term292.
Proof. exact (EQ_MP (@lem2321042) (@lem2323483 h1)). Qed.
Lemma lem2323485 (h1 : term105) : term292 = False.
Proof. exact (prop_ext (fun h2 : term292 => @lem2323482 h2) (fun h2 : False => @lem2323484 h1)). Qed.
Lemma lem2323486 (h1 : term105) : False.
Proof. exact (EQ_MP (@lem2323485 h1) (@lem2323484 h1)). Qed.
Lemma lem2323487 : term545.
Proof. exact (fun h0 : term105 => @lem2323486 h0). Qed.
Lemma lem2323488 : term546.
Proof. exact (@lem1386578 term547). Qed.
Lemma lem2323491 : term547.
Proof. exact (@lem2323488 (@lem2323487)). Qed.
Lemma lem2323492 : term103 = term14.
Proof. exact (SYM (@lem2320068)). Qed.
Lemma lem2323493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2323494 : term547 = term0.
Proof. exact (MK_COMB (@lem2323493) (@lem2323492)). Qed.
Lemma lem2323495 : term0.
Proof. exact (EQ_MP (@lem2323494) (@lem2323491)). Qed.
Lemma lem2323496 : term1.
Proof. exact (EQ_MP (@lem2319813) (@lem2323495)). Qed.
