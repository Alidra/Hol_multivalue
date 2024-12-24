Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_EXISTS_EL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import num_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1097080_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
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
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm89994_spec.
Lemma lem1160774 (n : nat) : term0 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem1160775 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1160776 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1160775 n) (@lem1160774 n)). Qed.
Lemma lem1160777 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1160779 (m : nat) : term2 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem1160780 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1160781 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem1160780 m) (@lem1160779 m)). Qed.
Lemma lem1160782 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem1160781 m n). Qed.
Lemma lem1160783 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1160796 (p : Prop) : p = (term6 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1160797 (P : nat -> Prop) : ((term7 P) = (term8 P)) = (term9 P).
Proof. exact (@lem1160796 ((term7 P) = (term8 P))). Qed.
Lemma lem1160798 (P : nat -> Prop) : (term9 P) = ((term7 P) = (term8 P)).
Proof. exact (SYM (@lem1160797 P)). Qed.
Lemma lem1160799 (P : nat -> Prop) (h1 : term10 P) : term10 P.
Proof. exact (h1). Qed.
Lemma lem1160802 (P : nat -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem1160803 (P : nat -> Prop) : term12 P.
Proof. exact (fun h0 : term11 P => @lem1160802 P h0). Qed.
Lemma lem1160804 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem1160805 (P : nat -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem1160806 (P : nat -> Prop) (h1 : term11 P) (h2 : term12 P) : term11 P.
Proof. exact (@lem1160804 P h2 (@lem1160805 P h1)). Qed.
Lemma lem1160807 (P : nat -> Prop) (h1 : term11 P) : term13 P.
Proof. exact (fun h0 : term12 P => @lem1160806 P h1 h0). Qed.
Lemma lem1160808 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem1160809 (P : nat -> Prop) (h1 : term11 P) (h2 : term12 P) : term11 P.
Proof. exact (@lem1160807 P h1 (@lem1160808 P h2)). Qed.
Lemma lem1160810 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (fun h0 : term11 P => @lem1160809 P h0 h1). Qed.
Lemma lem1160811 (P : nat -> Prop) : term14 P.
Proof. exact (fun h0 : term12 P => @lem1160810 P h0). Qed.
Lemma lem1160814 (P : nat -> Prop) : term12 P.
Proof. exact (@lem1160811 P (@lem1160803 P)). Qed.
Lemma lem1160832 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1160833 : term15 = term16.
Proof. exact (@lem1160832 term17). Qed.
Lemma lem1160888 (P : nat -> Prop) : (term18 P) = (term18 P).
Proof. exact (eq_refl (term18 P)). Qed.
Lemma lem1160889 (P : nat -> Prop) : (term11 P) = (term19 P).
Proof. exact (MK_COMB (@lem1160888 P) (@lem1160833)). Qed.
Lemma lem1160892 : term20 = term21.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem1160889 P)). Qed.
Lemma lem1160893 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem1160902 : term22 = term23.
Proof. exact (MK_COMB (@lem1160893) (@lem1160892)). Qed.
Lemma lem1160903 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem1160904 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1160903 m n)). Qed.
Lemma lem1160905 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1160906 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1160905) (@lem1160904 m)). Qed.
Lemma lem1160909 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1160910 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem1160909 m) (@lem1160906 m)). Qed.
Lemma lem1160911 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem1160910 m)). Qed.
Lemma lem1160912 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1160913 : term17 = term17.
Proof. exact (MK_COMB (@lem1160912) (@lem1160911)). Qed.
Lemma lem1160914 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1160915 : term16 = term16.
Proof. exact (MK_COMB (@lem1160914) (@lem1160913)). Qed.
Lemma lem1160916 (P : nat -> Prop) (i : nat) : (term29 P i) = (term29 P i).
Proof. exact (eq_refl (term29 P i)). Qed.
Lemma lem1160917 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (fun_ext (fun i : nat => @lem1160916 P i)). Qed.
Lemma lem1160918 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1160919 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem1160918) (@lem1160917 P)). Qed.
Lemma lem1160922 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (eq_refl (term32 P)). Qed.
Lemma lem1160923 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem1160922 P) (@lem1160919 P)). Qed.
Lemma lem1160924 (P : nat -> Prop) (i : nat) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem1160925 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (fun_ext (fun i : nat => @lem1160924 P i)). Qed.
Lemma lem1160926 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1160927 (P : nat -> Prop) : (term7 P) = (term7 P).
Proof. exact (MK_COMB (@lem1160926) (@lem1160925 P)). Qed.
Lemma lem1160928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1160929 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (MK_COMB (@lem1160928) (@lem1160927 P)). Qed.
Lemma lem1160930 (P : nat -> Prop) : ((term7 P) = (term8 P)) = ((term7 P) = (term8 P)).
Proof. exact (MK_COMB (@lem1160929 P) (@lem1160923 P)). Qed.
Lemma lem1160931 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1160932 (P : nat -> Prop) : (term10 P) = (term10 P).
Proof. exact (MK_COMB (@lem1160931) (@lem1160930 P)). Qed.
Lemma lem1160933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160934 (P : nat -> Prop) : (term18 P) = (term18 P).
Proof. exact (MK_COMB (@lem1160933) (@lem1160932 P)). Qed.
Lemma lem1160935 (P : nat -> Prop) : (term19 P) = (term19 P).
Proof. exact (MK_COMB (@lem1160934 P) (@lem1160915)). Qed.
Lemma lem1160936 : term21 = term21.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem1160935 P)). Qed.
Lemma lem1160937 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem1160938 : term23 = term23.
Proof. exact (MK_COMB (@lem1160937) (@lem1160936)). Qed.
Lemma lem1160977 : term22 = term23.
Proof. exact (TRANS (@lem1160902) (@lem1160938)). Qed.
Lemma lem1160978 : term23 = term22.
Proof. exact (SYM (@lem1160977)). Qed.
Lemma lem1160979 (P : nat -> Prop) (h1 : term10 P) : term10 P.
Proof. exact (h1). Qed.
Lemma lem1160980 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1160982 (P : nat -> Prop) (i : nat) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem1160983 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1160984 (P : nat -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem1160983 (term33 P)). Qed.
Lemma lem1160985 (P : nat -> Prop) (i : nat) : (term39 P i) = (P i).
Proof. exact (eq_refl (term39 P i)). Qed.
Lemma lem1160986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1160988 (P : nat -> Prop) (i : nat) : (term40 P i) = (term41 P i).
Proof. exact (MK_COMB (@lem1160986) (@lem1160985 P i)). Qed.
Lemma lem1160989 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (fun_ext (fun i : nat => @lem1160988 P i)). Qed.
Lemma lem1160990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1160991 (P : nat -> Prop) : (term38 P) = (term36 P).
Proof. exact (MK_COMB (@lem1160990) (@lem1160989 P)). Qed.
Lemma lem1160992 (P : nat -> Prop) : (term37 P) = (term36 P).
Proof. exact (TRANS (@lem1160984 P) (@lem1160991 P)). Qed.
Lemma lem1160993 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (fun_ext (fun i : nat => @lem1160982 P i)). Qed.
Lemma lem1160994 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1160995 (P : nat -> Prop) : (term7 P) = (term7 P).
Proof. exact (MK_COMB (@lem1160994) (@lem1160993 P)). Qed.
Lemma lem1160999 (P : nat -> Prop) (i : nat) : (term29 P i) = (term29 P i).
Proof. exact (eq_refl (term29 P i)). Qed.
Lemma lem1161000 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1161001 (P : nat -> Prop) : (term44 P) = (term45 P).
Proof. exact (@lem1161000 (term30 P)). Qed.
Lemma lem1161002 (P : nat -> Prop) (i : nat) : (term46 P i) = (term29 P i).
Proof. exact (eq_refl (term46 P i)). Qed.
Lemma lem1161003 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1161005 (P : nat -> Prop) (i : nat) : (term47 P i) = (term48 P i).
Proof. exact (MK_COMB (@lem1161003) (@lem1161002 P i)). Qed.
Lemma lem1161006 (P : nat -> Prop) : (term49 P) = (term50 P).
Proof. exact (fun_ext (fun i : nat => @lem1161005 P i)). Qed.
Lemma lem1161007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161008 (P : nat -> Prop) : (term45 P) = (term51 P).
Proof. exact (MK_COMB (@lem1161007) (@lem1161006 P)). Qed.
Lemma lem1161009 (P : nat -> Prop) : (term44 P) = (term51 P).
Proof. exact (TRANS (@lem1161001 P) (@lem1161008 P)). Qed.
Lemma lem1161010 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (fun_ext (fun i : nat => @lem1160999 P i)). Qed.
Lemma lem1161011 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161012 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem1161011) (@lem1161010 P)). Qed.
Lemma lem1161014 (P : nat -> Prop) : (term52 P) = (term52 P).
Proof. exact (eq_refl (term52 P)). Qed.
Lemma lem1161015 (P : nat -> Prop) : (term53 P) = (term54 P).
Proof. exact (MK_COMB (@lem1161014 P) (@lem1161009 P)). Qed.
Lemma lem1161016 (P : nat -> Prop) : (term55 P) = (term53 P).
Proof. exact (@lem17160 (term56 P) (term31 P)). Qed.
Lemma lem1161017 (P : nat -> Prop) : (term55 P) = (term54 P).
Proof. exact (TRANS (@lem1161016 P) (@lem1161015 P)). Qed.
Lemma lem1161019 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (eq_refl (term32 P)). Qed.
Lemma lem1161020 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem1161019 P) (@lem1161012 P)). Qed.
Lemma lem1161021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1161022 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (MK_COMB (@lem1161021) (@lem1160992 P)). Qed.
Lemma lem1161023 (P : nat -> Prop) : (term59 P) = (term60 P).
Proof. exact (MK_COMB (@lem1161022 P) (@lem1161020 P)). Qed.
Lemma lem1161024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1161025 (P : nat -> Prop) : (term61 P) = (term61 P).
Proof. exact (MK_COMB (@lem1161024) (@lem1160995 P)). Qed.
Lemma lem1161026 (P : nat -> Prop) : (term62 P) = (term63 P).
Proof. exact (MK_COMB (@lem1161025 P) (@lem1161017 P)). Qed.
Lemma lem1161027 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1161028 (P : nat -> Prop) : (term64 P) = (term65 P).
Proof. exact (MK_COMB (@lem1161027) (@lem1161026 P)). Qed.
Lemma lem1161029 (P : nat -> Prop) : (term66 P) = (term67 P).
Proof. exact (MK_COMB (@lem1161028 P) (@lem1161023 P)). Qed.
Lemma lem1161030 (P : nat -> Prop) : (term10 P) = (term66 P).
Proof. exact (@lem17646 (term7 P) (term8 P)). Qed.
Lemma lem1161031 (P : nat -> Prop) : (term10 P) = (term67 P).
Proof. exact (TRANS (@lem1161030 P) (@lem1161029 P)). Qed.
Lemma lem1161050 {A : Type'} (P : A -> Prop) (Q : Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1161051 (P : nat -> Prop) (Q : Prop) : (term70 P Q) = (term71 P Q).
Proof. exact (@lem1161050 nat P Q). Qed.
Lemma lem1161052 (P : nat -> Prop) : (term63 P) = (term72 P).
Proof. exact (@lem1161051 P (term54 P)). Qed.
Lemma lem1161053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1161054 (P : nat -> Prop) : (term65 P) = (term73 P).
Proof. exact (MK_COMB (@lem1161053) (@lem1161052 P)). Qed.
Lemma lem1161056 {A : Type'} (P : Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1161057 (P : Prop) (Q : nat -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1161056 nat P Q). Qed.
Lemma lem1161058 (P : nat -> Prop) : (term78 P) = (term79 P).
Proof. exact (@lem1161057 (term56 P) (term30 P)). Qed.
Lemma lem1161059 (P : nat -> Prop) (i : nat) : (term46 P i) = (term29 P i).
Proof. exact (eq_refl (term46 P i)). Qed.
Lemma lem1161060 (P : nat -> Prop) : (term80 P) = (term30 P).
Proof. exact (fun_ext (fun i : nat => @lem1161059 P i)). Qed.
Lemma lem1161061 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161062 (P : nat -> Prop) : (term81 P) = (term31 P).
Proof. exact (MK_COMB (@lem1161061) (@lem1161060 P)). Qed.
Lemma lem1161063 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (eq_refl (term32 P)). Qed.
Lemma lem1161064 (P : nat -> Prop) : (term78 P) = (term8 P).
Proof. exact (MK_COMB (@lem1161063 P) (@lem1161062 P)). Qed.
Lemma lem1161065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1161066 (P : nat -> Prop) : (term82 P) = (term83 P).
Proof. exact (MK_COMB (@lem1161065) (@lem1161064 P)). Qed.
Lemma lem1161067 (P : nat -> Prop) (i : nat) : (term46 P i) = (term29 P i).
Proof. exact (eq_refl (term46 P i)). Qed.
Lemma lem1161068 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (eq_refl (term32 P)). Qed.
Lemma lem1161069 (P : nat -> Prop) (i : nat) : (term84 P i) = (term85 P i).
Proof. exact (MK_COMB (@lem1161068 P) (@lem1161067 P i)). Qed.
Lemma lem1161070 (P : nat -> Prop) : (term86 P) = (term87 P).
Proof. exact (fun_ext (fun i : nat => @lem1161069 P i)). Qed.
Lemma lem1161071 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161072 (P : nat -> Prop) : (term79 P) = (term88 P).
Proof. exact (MK_COMB (@lem1161071) (@lem1161070 P)). Qed.
Lemma lem1161073 (P : nat -> Prop) : ((term78 P) = (term79 P)) = ((term8 P) = (term88 P)).
Proof. exact (MK_COMB (@lem1161066 P) (@lem1161072 P)). Qed.
Lemma lem1161074 (P : nat -> Prop) : (term8 P) = (term88 P).
Proof. exact (EQ_MP (@lem1161073 P) (@lem1161058 P)). Qed.
Lemma lem1161075 (P : nat -> Prop) : (term58 P) = (term58 P).
Proof. exact (eq_refl (term58 P)). Qed.
Lemma lem1161076 (P : nat -> Prop) : (term60 P) = (term89 P).
Proof. exact (MK_COMB (@lem1161075 P) (@lem1161074 P)). Qed.
Lemma lem1161078 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1161079 (P : Prop) (Q : nat -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1161078 nat P Q). Qed.
Lemma lem1161080 (P : nat -> Prop) : (term94 P) = (term95 P).
Proof. exact (@lem1161079 (term36 P) (term87 P)). Qed.
Lemma lem1161081 (P : nat -> Prop) (i : nat) : (term96 P i) = (term85 P i).
Proof. exact (eq_refl (term96 P i)). Qed.
Lemma lem1161082 (P : nat -> Prop) : (term97 P) = (term87 P).
Proof. exact (fun_ext (fun i : nat => @lem1161081 P i)). Qed.
Lemma lem1161083 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161084 (P : nat -> Prop) : (term98 P) = (term88 P).
Proof. exact (MK_COMB (@lem1161083) (@lem1161082 P)). Qed.
Lemma lem1161085 (P : nat -> Prop) : (term58 P) = (term58 P).
Proof. exact (eq_refl (term58 P)). Qed.
Lemma lem1161086 (P : nat -> Prop) : (term94 P) = (term89 P).
Proof. exact (MK_COMB (@lem1161085 P) (@lem1161084 P)). Qed.
Lemma lem1161087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1161088 (P : nat -> Prop) : (term99 P) = (term100 P).
Proof. exact (MK_COMB (@lem1161087) (@lem1161086 P)). Qed.
Lemma lem1161089 (P : nat -> Prop) (i : nat) : (term96 P i) = (term85 P i).
Proof. exact (eq_refl (term96 P i)). Qed.
Lemma lem1161090 (P : nat -> Prop) : (term58 P) = (term58 P).
Proof. exact (eq_refl (term58 P)). Qed.
Lemma lem1161091 (P : nat -> Prop) (i : nat) : (term101 P i) = (term102 P i).
Proof. exact (MK_COMB (@lem1161090 P) (@lem1161089 P i)). Qed.
Lemma lem1161092 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (fun_ext (fun i : nat => @lem1161091 P i)). Qed.
Lemma lem1161093 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161094 (P : nat -> Prop) : (term95 P) = (term105 P).
Proof. exact (MK_COMB (@lem1161093) (@lem1161092 P)). Qed.
Lemma lem1161095 (P : nat -> Prop) : ((term94 P) = (term95 P)) = ((term89 P) = (term105 P)).
Proof. exact (MK_COMB (@lem1161088 P) (@lem1161094 P)). Qed.
Lemma lem1161096 (P : nat -> Prop) : (term89 P) = (term105 P).
Proof. exact (EQ_MP (@lem1161095 P) (@lem1161080 P)). Qed.
Lemma lem1161097 (P : nat -> Prop) : (term60 P) = (term105 P).
Proof. exact (TRANS (@lem1161076 P) (@lem1161096 P)). Qed.
Lemma lem1161098 (P : nat -> Prop) : (term67 P) = (term106 P).
Proof. exact (MK_COMB (@lem1161054 P) (@lem1161097 P)). Qed.
Lemma lem1161100 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1161101 (P : nat -> Prop) (Q : nat -> Prop) : (term109 P Q) = (term110 P Q).
Proof. exact (@lem1161100 nat P Q). Qed.
Lemma lem1161102 (P : nat -> Prop) : (term111 P) = (term112 P).
Proof. exact (@lem1161101 (term113 P) (term104 P)). Qed.
Lemma lem1161103 (i : nat) (P : nat -> Prop) : (term114 P i) = (term115 i P).
Proof. exact (eq_refl (term114 P i)). Qed.
Lemma lem1161104 (P : nat -> Prop) : (term116 P) = (term113 P).
Proof. exact (fun_ext (fun i : nat => @lem1161103 i P)). Qed.
Lemma lem1161105 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161106 (P : nat -> Prop) : (term117 P) = (term72 P).
Proof. exact (MK_COMB (@lem1161105) (@lem1161104 P)). Qed.
Lemma lem1161107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1161108 (P : nat -> Prop) : (term118 P) = (term73 P).
Proof. exact (MK_COMB (@lem1161107) (@lem1161106 P)). Qed.
Lemma lem1161109 (P : nat -> Prop) (i : nat) : (term119 P i) = (term102 P i).
Proof. exact (eq_refl (term119 P i)). Qed.
Lemma lem1161110 (P : nat -> Prop) : (term120 P) = (term104 P).
Proof. exact (fun_ext (fun i : nat => @lem1161109 P i)). Qed.
Lemma lem1161111 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161112 (P : nat -> Prop) : (term121 P) = (term105 P).
Proof. exact (MK_COMB (@lem1161111) (@lem1161110 P)). Qed.
Lemma lem1161113 (P : nat -> Prop) : (term111 P) = (term106 P).
Proof. exact (MK_COMB (@lem1161108 P) (@lem1161112 P)). Qed.
Lemma lem1161114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1161115 (P : nat -> Prop) : (term122 P) = (term123 P).
Proof. exact (MK_COMB (@lem1161114) (@lem1161113 P)). Qed.
Lemma lem1161116 (i : nat) (P : nat -> Prop) : (term114 P i) = (term115 i P).
Proof. exact (eq_refl (term114 P i)). Qed.
Lemma lem1161117 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1161118 (i : nat) (P : nat -> Prop) : (term124 P i) = (term125 i P).
Proof. exact (MK_COMB (@lem1161117) (@lem1161116 i P)). Qed.
Lemma lem1161119 (P : nat -> Prop) (i : nat) : (term119 P i) = (term102 P i).
Proof. exact (eq_refl (term119 P i)). Qed.
Lemma lem1161120 (P : nat -> Prop) (i : nat) : (term126 P i) = (term127 P i).
Proof. exact (MK_COMB (@lem1161118 i P) (@lem1161119 P i)). Qed.
Lemma lem1161121 (P : nat -> Prop) : (term128 P) = (term129 P).
Proof. exact (fun_ext (fun i : nat => @lem1161120 P i)). Qed.
Lemma lem1161122 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161123 (P : nat -> Prop) : (term112 P) = (term130 P).
Proof. exact (MK_COMB (@lem1161122) (@lem1161121 P)). Qed.
Lemma lem1161124 (P : nat -> Prop) : ((term111 P) = (term112 P)) = ((term106 P) = (term130 P)).
Proof. exact (MK_COMB (@lem1161115 P) (@lem1161123 P)). Qed.
Lemma lem1161125 (P : nat -> Prop) : (term106 P) = (term130 P).
Proof. exact (EQ_MP (@lem1161124 P) (@lem1161102 P)). Qed.
Lemma lem1161127 (P : nat -> Prop) : (term67 P) = (term130 P).
Proof. exact (TRANS (@lem1161098 P) (@lem1161125 P)). Qed.
Lemma lem1161128 (P : nat -> Prop) : (term10 P) = (term130 P).
Proof. exact (TRANS (@lem1161031 P) (@lem1161127 P)). Qed.
Lemma lem1161129 (P : nat -> Prop) (h1 : term10 P) : term130 P.
Proof. exact (EQ_MP (@lem1161128 P) (@lem1160979 P h1)). Qed.
Lemma lem1161131 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem1161132 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1161131 m n)). Qed.
Lemma lem1161133 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161134 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1161133) (@lem1161132 m)). Qed.
Lemma lem1161136 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1161137 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem1161136 m) (@lem1161134 m)). Qed.
Lemma lem1161138 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem1161137 m)). Qed.
Lemma lem1161139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161140 : term17 = term17.
Proof. exact (MK_COMB (@lem1161139) (@lem1161138)). Qed.
Lemma lem1161195 {A : Type'} (P : Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1161196 (P : Prop) (Q : nat -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1161195 nat P Q). Qed.
Lemma lem1161197 (m : nat) : (term131 m) = (term132 m).
Proof. exact (@lem1161196 (m = (NUMERAL 0)) (term24 m)). Qed.
Lemma lem1161198 (m : nat) (n : nat) : (term133 m n) = (m = (S n)).
Proof. exact (eq_refl (term133 m n)). Qed.
Lemma lem1161199 (m : nat) : (term134 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1161198 m n)). Qed.
Lemma lem1161200 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161201 (m : nat) : (term135 m) = (term25 m).
Proof. exact (MK_COMB (@lem1161200) (@lem1161199 m)). Qed.
Lemma lem1161202 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1161203 (m : nat) : (term131 m) = (term27 m).
Proof. exact (MK_COMB (@lem1161202 m) (@lem1161201 m)). Qed.
Lemma lem1161204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1161205 (m : nat) : (term136 m) = (term137 m).
Proof. exact (MK_COMB (@lem1161204) (@lem1161203 m)). Qed.
Lemma lem1161206 (m : nat) (n : nat) : (term133 m n) = (m = (S n)).
Proof. exact (eq_refl (term133 m n)). Qed.
Lemma lem1161207 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1161208 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (MK_COMB (@lem1161207 m) (@lem1161206 m n)). Qed.
Lemma lem1161209 (m : nat) : (term140 m) = (term141 m).
Proof. exact (fun_ext (fun n : nat => @lem1161208 m n)). Qed.
Lemma lem1161210 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161211 (m : nat) : (term132 m) = (term142 m).
Proof. exact (MK_COMB (@lem1161210) (@lem1161209 m)). Qed.
Lemma lem1161212 (m : nat) : ((term131 m) = (term132 m)) = ((term27 m) = (term142 m)).
Proof. exact (MK_COMB (@lem1161205 m) (@lem1161211 m)). Qed.
Lemma lem1161213 (m : nat) : (term27 m) = (term142 m).
Proof. exact (EQ_MP (@lem1161212 m) (@lem1161197 m)). Qed.
Lemma lem1161214 : term28 = term143.
Proof. exact (fun_ext (fun m : nat => @lem1161213 m)). Qed.
Lemma lem1161215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161216 : term17 = term144.
Proof. exact (MK_COMB (@lem1161215) (@lem1161214)). Qed.
Lemma lem1161218 {A B : Type'} (P : type1413 A B) : (term145 A B P) = (term146 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1161219 (P : type1605) : (term147 P) = (term148 P).
Proof. exact (@lem1161218 nat nat P). Qed.
Lemma lem1161220 : term149 = term150.
Proof. exact (@lem1161219 term151). Qed.
Lemma lem1161221 (m : nat) : (term152 m) = (term141 m).
Proof. exact (eq_refl (term152 m)). Qed.
Lemma lem1161222 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1161223 (m : nat) (n : nat) : (term153 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem1161221 m) (@lem1161222 n)). Qed.
Lemma lem1161224 (m : nat) (n : nat) : (term154 m n) = (term139 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem1161225 (m : nat) (n : nat) : (term153 m n) = (term139 m n).
Proof. exact (TRANS (@lem1161223 m n) (@lem1161224 m n)). Qed.
Lemma lem1161226 (m : nat) : (term155 m) = (term141 m).
Proof. exact (fun_ext (fun n : nat => @lem1161225 m n)). Qed.
Lemma lem1161227 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161228 (m : nat) : (term156 m) = (term142 m).
Proof. exact (MK_COMB (@lem1161227) (@lem1161226 m)). Qed.
Lemma lem1161229 : term157 = term143.
Proof. exact (fun_ext (fun m : nat => @lem1161228 m)). Qed.
Lemma lem1161230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161231 : term149 = term144.
Proof. exact (MK_COMB (@lem1161230) (@lem1161229)). Qed.
Lemma lem1161232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1161233 : term158 = term159.
Proof. exact (MK_COMB (@lem1161232) (@lem1161231)). Qed.
Lemma lem1161234 (m : nat) : (term152 m) = (term141 m).
Proof. exact (eq_refl (term152 m)). Qed.
Lemma lem1161235 (n : nat -> nat) (m : nat) : (n m) = (n m).
Proof. exact (eq_refl (n m)). Qed.
Lemma lem1161236 (n : nat -> nat) (m : nat) : (term160 n m) = (term161 n m).
Proof. exact (MK_COMB (@lem1161234 m) (@lem1161235 n m)). Qed.
Lemma lem1161237 (n : nat -> nat) (m : nat) : (term161 n m) = (term162 n m).
Proof. exact (eq_refl (term161 n m)). Qed.
Lemma lem1161238 (n : nat -> nat) (m : nat) : (term160 n m) = (term162 n m).
Proof. exact (TRANS (@lem1161236 n m) (@lem1161237 n m)). Qed.
Lemma lem1161239 (n : nat -> nat) : (term163 n) = (term164 n).
Proof. exact (fun_ext (fun m : nat => @lem1161238 n m)). Qed.
Lemma lem1161240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161241 (n : nat -> nat) : (term165 n) = (term166 n).
Proof. exact (MK_COMB (@lem1161240) (@lem1161239 n)). Qed.
Lemma lem1161242 : term167 = term168.
Proof. exact (fun_ext (fun n : nat -> nat => @lem1161241 n)). Qed.
Lemma lem1161243 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1161244 : term150 = term169.
Proof. exact (MK_COMB (@lem1161243) (@lem1161242)). Qed.
Lemma lem1161245 : (term149 = term150) = (term144 = term169).
Proof. exact (MK_COMB (@lem1161233) (@lem1161244)). Qed.
Lemma lem1161246 : term144 = term169.
Proof. exact (EQ_MP (@lem1161245) (@lem1161220)). Qed.
Lemma lem1161248 : term17 = term169.
Proof. exact (TRANS (@lem1161216) (@lem1161246)). Qed.
Lemma lem1161249 : term17 = term169.
Proof. exact (TRANS (@lem1161140) (@lem1161248)). Qed.
Lemma lem1161250 (h1 : term17) : term169.
Proof. exact (EQ_MP (@lem1161249) (@lem1160980 h1)). Qed.
Lemma lem1161251 (n : nat -> nat) (h1 : term166 n) : term166 n.
Proof. exact (h1). Qed.
Lemma lem1161252 (P : nat -> Prop) (i : nat) (h1 : term127 P i) : term127 P i.
Proof. exact (h1). Qed.
Lemma lem1161271 (n : nat -> nat) (m : nat) : (term162 n m) = (term162 n m).
Proof. exact (eq_refl (term162 n m)). Qed.
Lemma lem1161272 (n : nat -> nat) : (term164 n) = (term164 n).
Proof. exact (fun_ext (fun m : nat => @lem1161271 n m)). Qed.
Lemma lem1161273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161274 (n : nat -> nat) : (term166 n) = (term166 n).
Proof. exact (MK_COMB (@lem1161273) (@lem1161272 n)). Qed.
Lemma lem1161275 (n : nat -> nat) (h1 : term166 n) : term166 n.
Proof. exact (EQ_MP (@lem1161274 n) (@lem1161251 n h1)). Qed.
Lemma lem1161288 (P : nat -> Prop) (i : nat) : (term85 P i) = (term85 P i).
Proof. exact (eq_refl (term85 P i)). Qed.
Lemma lem1161293 (P : nat -> Prop) (i : nat) : (term41 P i) = (term41 P i).
Proof. exact (eq_refl (term41 P i)). Qed.
Lemma lem1161294 (P : nat -> Prop) : (term43 P) = (term43 P).
Proof. exact (fun_ext (fun i : nat => @lem1161293 P i)). Qed.
Lemma lem1161295 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161296 (P : nat -> Prop) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem1161295) (@lem1161294 P)). Qed.
Lemma lem1161297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1161298 (P : nat -> Prop) : (term58 P) = (term58 P).
Proof. exact (MK_COMB (@lem1161297) (@lem1161296 P)). Qed.
Lemma lem1161299 (P : nat -> Prop) (i : nat) : (term102 P i) = (term102 P i).
Proof. exact (MK_COMB (@lem1161298 P) (@lem1161288 P i)). Qed.
Lemma lem1161306 (P : nat -> Prop) (i : nat) : (term48 P i) = (term48 P i).
Proof. exact (eq_refl (term48 P i)). Qed.
Lemma lem1161307 (P : nat -> Prop) : (term50 P) = (term50 P).
Proof. exact (fun_ext (fun i : nat => @lem1161306 P i)). Qed.
Lemma lem1161308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161309 (P : nat -> Prop) : (term51 P) = (term51 P).
Proof. exact (MK_COMB (@lem1161308) (@lem1161307 P)). Qed.
Lemma lem1161318 (P : nat -> Prop) : (term52 P) = (term52 P).
Proof. exact (eq_refl (term52 P)). Qed.
Lemma lem1161319 (P : nat -> Prop) : (term54 P) = (term54 P).
Proof. exact (MK_COMB (@lem1161318 P) (@lem1161309 P)). Qed.
Lemma lem1161324 (P : nat -> Prop) (i : nat) : (term170 P i) = (term170 P i).
Proof. exact (eq_refl (term170 P i)). Qed.
Lemma lem1161325 (i : nat) (P : nat -> Prop) : (term115 i P) = (term115 i P).
Proof. exact (MK_COMB (@lem1161324 P i) (@lem1161319 P)). Qed.
Lemma lem1161326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1161327 (i : nat) (P : nat -> Prop) : (term125 i P) = (term125 i P).
Proof. exact (MK_COMB (@lem1161326) (@lem1161325 i P)). Qed.
Lemma lem1161328 (P : nat -> Prop) (i : nat) : (term127 P i) = (term127 P i).
Proof. exact (MK_COMB (@lem1161327 i P) (@lem1161299 P i)). Qed.
Lemma lem1161329 (P : nat -> Prop) (i : nat) (h1 : term127 P i) : term127 P i.
Proof. exact (EQ_MP (@lem1161328 P i) (@lem1161252 P i h1)). Qed.
Lemma lem1161330 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term115 i P.
Proof. exact (h1). Qed.
Lemma lem1161331 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term102 P i.
Proof. exact (h1). Qed.
Lemma lem1161332 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term54 P.
Proof. exact (proj2 (@lem1161330 i P h1)). Qed.
Lemma lem1161334 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term51 P.
Proof. exact (proj2 (@lem1161332 i P h1)). Qed.
Lemma lem1161336 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term85 P i.
Proof. exact (proj2 (@lem1161331 P i h1)). Qed.
Lemma lem1161337 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term36 P.
Proof. exact (proj1 (@lem1161331 P i h1)). Qed.
Lemma lem1161347 (n : nat -> nat) (m : nat) : (term162 n m) = (term162 n m).
Proof. exact (eq_refl (term162 n m)). Qed.
Lemma lem1161348 (n : nat -> nat) : (term164 n) = (term164 n).
Proof. exact (fun_ext (fun m : nat => @lem1161347 n m)). Qed.
Lemma lem1161349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161351 (n : nat -> nat) : (term166 n) = (term166 n).
Proof. exact (MK_COMB (@lem1161349) (@lem1161348 n)). Qed.
Lemma lem1161352 (n : nat -> nat) (h1 : term166 n) : term166 n.
Proof. exact (EQ_MP (@lem1161351 n) (@lem1161275 n h1)). Qed.
Lemma lem1161362 (P : nat -> Prop) (i : nat) : (term48 P i) = (term48 P i).
Proof. exact (eq_refl (term48 P i)). Qed.
Lemma lem1161363 (P : nat -> Prop) : (term50 P) = (term50 P).
Proof. exact (fun_ext (fun i : nat => @lem1161362 P i)). Qed.
Lemma lem1161364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161366 (P : nat -> Prop) : (term51 P) = (term51 P).
Proof. exact (MK_COMB (@lem1161364) (@lem1161363 P)). Qed.
Lemma lem1161367 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term51 P.
Proof. exact (EQ_MP (@lem1161366 P) (@lem1161334 i P h1)). Qed.
Lemma lem1161382 (P : nat -> Prop) (i : nat) : (term41 P i) = (term41 P i).
Proof. exact (eq_refl (term41 P i)). Qed.
Lemma lem1161383 (P : nat -> Prop) : (term43 P) = (term43 P).
Proof. exact (fun_ext (fun i : nat => @lem1161382 P i)). Qed.
Lemma lem1161384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161386 (P : nat -> Prop) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem1161384) (@lem1161383 P)). Qed.
Lemma lem1161387 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term36 P.
Proof. exact (EQ_MP (@lem1161386 P) (@lem1161337 P i h1)). Qed.
Lemma lem1161391 (P : nat -> Prop) (h1 : term56 P) : term56 P.
Proof. exact (h1). Qed.
Lemma lem1161406 (P : nat -> Prop) (i : nat) : (term41 P i) = (term41 P i).
Proof. exact (eq_refl (term41 P i)). Qed.
Lemma lem1161407 (P : nat -> Prop) : (term43 P) = (term43 P).
Proof. exact (fun_ext (fun i : nat => @lem1161406 P i)). Qed.
Lemma lem1161408 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1161410 (P : nat -> Prop) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem1161408) (@lem1161407 P)). Qed.
Lemma lem1161411 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term36 P.
Proof. exact (EQ_MP (@lem1161410 P) (@lem1161337 P i h1)). Qed.
Lemma lem1161415 (P : nat -> Prop) (i : nat) (h1 : term29 P i) : term29 P i.
Proof. exact (h1). Qed.
Lemma lem1161416 (_19555 : nat) (n : nat -> nat) (h1 : term166 n) : term171 n _19555.
Proof. exact (@lem1161352 n h1 _19555). Qed.
Lemma lem1161417 (n : nat -> nat) (_19555 : nat) : (term171 n _19555) = (term162 n _19555).
Proof. exact (eq_refl (term171 n _19555)). Qed.
Lemma lem1161419 (_19556 : nat) (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term172 P _19556.
Proof. exact (@lem1161367 i P h1 _19556). Qed.
Lemma lem1161420 (P : nat -> Prop) (_19556 : nat) : (term172 P _19556) = (term48 P _19556).
Proof. exact (eq_refl (term172 P _19556)). Qed.
Lemma lem1161425 (_19558 : nat) (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term173 P _19558.
Proof. exact (@lem1161387 P i h1 _19558). Qed.
Lemma lem1161426 (P : nat -> Prop) (_19558 : nat) : (term173 P _19558) = (term41 P _19558).
Proof. exact (eq_refl (term173 P _19558)). Qed.
Lemma lem1161431 (_19560 : nat) (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term173 P _19560.
Proof. exact (@lem1161411 P i h1 _19560). Qed.
Lemma lem1161432 (P : nat -> Prop) (_19560 : nat) : (term173 P _19560) = (term41 P _19560).
Proof. exact (eq_refl (term173 P _19560)). Qed.
Lemma lem1161439 (_19555 : nat) (n : nat -> nat) (h1 : term166 n) : term162 n _19555.
Proof. exact (EQ_MP (@lem1161417 n _19555) (@lem1161416 _19555 n h1)). Qed.
Lemma lem1161445 (_19556 : nat) (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term48 P _19556.
Proof. exact (EQ_MP (@lem1161420 P _19556) (@lem1161419 _19556 i P h1)). Qed.
Lemma lem1161453 (_19558 : nat) (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term41 P _19558.
Proof. exact (EQ_MP (@lem1161426 P _19558) (@lem1161425 _19558 P i h1)). Qed.
Lemma lem1161455 (P : nat -> Prop) (h1 : term56 P) : term56 P.
Proof. exact (h1). Qed.
Lemma lem1161463 (_19560 : nat) (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term41 P _19560.
Proof. exact (EQ_MP (@lem1161432 P _19560) (@lem1161431 _19560 P i h1)). Qed.
Lemma lem1161465 (P : nat -> Prop) (i : nat) (h1 : term29 P i) : term29 P i.
Proof. exact (h1). Qed.
Lemma lem1161466 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1161467 (_19561 : nat) (_19562 : nat) (h1 : _19561 = _19562) : _19561 = _19562.
Proof. exact (h1). Qed.
Lemma lem1161468 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) (h1 : _19561 = _19562) : (P _19561) = (P _19562).
Proof. exact (MK_COMB (@lem1161466 P) (@lem1161467 _19561 _19562 h1)). Qed.
Lemma lem1161470 (b : Prop) (a : Prop) : term174 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1161471 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : term175 _19562 P _19561.
Proof. exact (@lem1161470 (P _19562) (P _19561)). Qed.
Lemma lem1161472 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) (h1 : _19561 = _19562) : term176 _19562 P _19561.
Proof. exact (@lem1161471 _19562 P _19561 (@lem1161468 P _19561 _19562 h1)). Qed.
Lemma lem1161473 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : term177 _19562 P _19561.
Proof. exact (fun h0 : _19561 = _19562 => @lem1161472 P _19561 _19562 h0). Qed.
Lemma lem1161475 (a : Prop) (b : Prop) : (a -> b) = (term178 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1161476 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term177 _19562 P _19561) = (term179 _19562 P _19561).
Proof. exact (@lem1161475 (_19561 = _19562) (term176 _19562 P _19561)). Qed.
Lemma lem1161477 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : term179 _19562 P _19561.
Proof. exact (EQ_MP (@lem1161476 _19562 P _19561) (@lem1161473 _19562 P _19561)). Qed.
Lemma lem1161505 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term180 P.
Proof. exact (proj1 (@lem1161332 i P h1)). Qed.
Lemma lem1161506 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term181 P.
Proof. exact (fun h0 : term56 P => @lem1161505 i P h1). Qed.
Lemma lem1161508 (p : Prop) : (term182 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1161509 (P : nat -> Prop) : (term181 P) = (term180 P).
Proof. exact (@lem1161508 (term56 P)). Qed.
Lemma lem1161510 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term180 P.
Proof. exact (EQ_MP (@lem1161509 P) (@lem1161506 i P h1)). Qed.
Lemma lem1161512 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : P i.
Proof. exact (proj1 (@lem1161330 i P h1)). Qed.
Lemma lem1161513 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term183 P i.
Proof. exact (fun h0 : term41 P i => @lem1161512 i P h1). Qed.
Lemma lem1161515 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161516 (P : nat -> Prop) (i : nat) : (term183 P i) = (P i).
Proof. exact (@lem1161515 (P i)). Qed.
Lemma lem1161517 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : P i.
Proof. exact (EQ_MP (@lem1161516 P i) (@lem1161513 i P h1)). Qed.
Lemma lem1161519 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1161520 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term179 _19562 P _19561) = (term186 P _19561 _19562).
Proof. exact (@lem1161519 (term176 _19562 P _19561) (term187 _19561 _19562)). Qed.
Lemma lem1161522 (a : Prop) (b : Prop) : (term188 a b) = (term189 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1161523 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term190 _19562 P _19561) = (term191 _19562 P _19561).
Proof. exact (@lem1161522 (P _19562) (term41 P _19561)). Qed.
Lemma lem1161525 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1161526 (P : nat -> Prop) (_19561 : nat) : (term193 P _19561) = (P _19561).
Proof. exact (@lem1161525 (P _19561)). Qed.
Lemma lem1161527 (P : nat -> Prop) (_19562 : nat) : (term194 P _19562) = (term194 P _19562).
Proof. exact (eq_refl (term194 P _19562)). Qed.
Lemma lem1161528 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term191 _19562 P _19561) = (term195 _19562 P _19561).
Proof. exact (MK_COMB (@lem1161527 P _19562) (@lem1161526 P _19561)). Qed.
Lemma lem1161529 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term190 _19562 P _19561) = (term195 _19562 P _19561).
Proof. exact (TRANS (@lem1161523 _19562 P _19561) (@lem1161528 _19562 P _19561)). Qed.
Lemma lem1161530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1161531 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term196 _19562 P _19561) = (term197 _19562 P _19561).
Proof. exact (MK_COMB (@lem1161530) (@lem1161529 _19562 P _19561)). Qed.
Lemma lem1161532 (_19561 : nat) (_19562 : nat) : (term187 _19561 _19562) = (term187 _19561 _19562).
Proof. exact (eq_refl (term187 _19561 _19562)). Qed.
Lemma lem1161533 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term186 P _19561 _19562) = (term198 P _19561 _19562).
Proof. exact (MK_COMB (@lem1161531 _19562 P _19561) (@lem1161532 _19561 _19562)). Qed.
Lemma lem1161534 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term179 _19562 P _19561) = (term198 P _19561 _19562).
Proof. exact (TRANS (@lem1161520 P _19561 _19562) (@lem1161533 P _19561 _19562)). Qed.
Lemma lem1161536 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term199 P i.
Proof. exact (conj (@lem1161510 i P h1) (@lem1161517 i P h1)). Qed.
Lemma lem1161538 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : term198 P _19561 _19562.
Proof. exact (EQ_MP (@lem1161534 P _19561 _19562) (@lem1161477 _19562 P _19561)). Qed.
Lemma lem1161539 (P : nat -> Prop) (i : nat) : term200 P i.
Proof. exact (@lem1161538 P i (NUMERAL 0)). Qed.
Lemma lem1161542 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term201 i.
Proof. exact (@lem1161539 P i (@lem1161536 i P h1)). Qed.
Lemma lem1161543 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term202 i.
Proof. exact (fun h0 : i = (NUMERAL 0) => @lem1161542 i P h1). Qed.
Lemma lem1161545 (p : Prop) : (term182 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1161546 (i : nat) : (term202 i) = (term201 i).
Proof. exact (@lem1161545 (i = (NUMERAL 0))). Qed.
Lemma lem1161547 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term201 i.
Proof. exact (EQ_MP (@lem1161546 i) (@lem1161543 i P h1)). Qed.
Lemma lem1161562 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1161563 (n : nat -> nat) (_19555 : nat) : (term203 n _19555) = (term162 n _19555).
Proof. exact (@lem1161562 (_19555 = (NUMERAL 0)) (_19555 = (term204 n _19555))). Qed.
Lemma lem1161573 (n : nat -> nat) (_19555 : nat) : (term205 n _19555) = (term205 n _19555).
Proof. exact (eq_refl (term205 n _19555)). Qed.
Lemma lem1161574 (n : nat -> nat) (_19555 : nat) : ((term162 n _19555) = (term203 n _19555)) = ((term162 n _19555) = (term162 n _19555)).
Proof. exact (MK_COMB (@lem1161573 n _19555) (@lem1161563 n _19555)). Qed.
Lemma lem1161576 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1161577 (x : Prop) : (x = x) = True.
Proof. exact (@lem1161576 Prop x). Qed.
Lemma lem1161578 (n : nat -> nat) (_19555 : nat) : ((term162 n _19555) = (term162 n _19555)) = True.
Proof. exact (@lem1161577 (term162 n _19555)). Qed.
Lemma lem1161579 (n : nat -> nat) (_19555 : nat) : ((term162 n _19555) = (term203 n _19555)) = True.
Proof. exact (TRANS (@lem1161574 n _19555) (@lem1161578 n _19555)). Qed.
Lemma lem1161580 (n : nat -> nat) (_19555 : nat) : True = ((term162 n _19555) = (term203 n _19555)).
Proof. exact (SYM (@lem1161579 n _19555)). Qed.
Lemma lem1161581 (n : nat -> nat) (_19555 : nat) : (term162 n _19555) = (term203 n _19555).
Proof. exact (EQ_MP (@lem1161580 n _19555) (@lem0)). Qed.
Lemma lem1161582 (_19555 : nat) (n : nat -> nat) (h1 : term166 n) : term203 n _19555.
Proof. exact (EQ_MP (@lem1161581 n _19555) (@lem1161439 _19555 n h1)). Qed.
Lemma lem1161584 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1161587 (n : nat -> nat) (_19555 : nat) : (term203 n _19555) = (term206 n _19555).
Proof. exact (@lem1161584 (_19555 = (NUMERAL 0)) (_19555 = (term204 n _19555))). Qed.
Lemma lem1161590 (_19555 : nat) (n : nat -> nat) (h1 : term166 n) : term206 n _19555.
Proof. exact (EQ_MP (@lem1161587 n _19555) (@lem1161582 _19555 n h1)). Qed.
Lemma lem1161591 (i : nat) (n : nat -> nat) (h1 : term166 n) : term206 n i.
Proof. exact (@lem1161590 i n h1). Qed.
Lemma lem1161594 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : i = (term204 n i).
Proof. exact (@lem1161591 i n h1 (@lem1161547 i P h2)). Qed.
Lemma lem1161595 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : term207 n i.
Proof. exact (fun h0 : term208 n i => @lem1161594 n i P h1 h2). Qed.
Lemma lem1161597 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161598 (n : nat -> nat) (i : nat) : (term207 n i) = (i = (term204 n i)).
Proof. exact (@lem1161597 (i = (term204 n i))). Qed.
Lemma lem1161599 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : i = (term204 n i).
Proof. exact (EQ_MP (@lem1161598 n i) (@lem1161595 n i P h1 h2)). Qed.
Lemma lem1161601 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : P i.
Proof. exact (proj1 (@lem1161330 i P h1)). Qed.
Lemma lem1161602 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term183 P i.
Proof. exact (fun h0 : term41 P i => @lem1161601 i P h1). Qed.
Lemma lem1161604 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161605 (P : nat -> Prop) (i : nat) : (term183 P i) = (P i).
Proof. exact (@lem1161604 (P i)). Qed.
Lemma lem1161606 (i : nat) (P : nat -> Prop) (h1 : term115 i P) : P i.
Proof. exact (EQ_MP (@lem1161605 P i) (@lem1161602 i P h1)). Qed.
Lemma lem1161612 (q : Prop) (p : Prop) (r : Prop) : (term209 p q r) = (term209 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1161613 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term179 _19562 P _19561) = (term210 _19562 P _19561).
Proof. exact (@lem1161612 (P _19562) (term187 _19561 _19562) (term41 P _19561)). Qed.
Lemma lem1161627 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1161628 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term211 _19562 P _19561) = (term212 P _19561 _19562).
Proof. exact (@lem1161627 (term41 P _19561) (term187 _19561 _19562)). Qed.
Lemma lem1161636 (P : nat -> Prop) (_19562 : nat) : (term213 P _19562) = (term213 P _19562).
Proof. exact (eq_refl (term213 P _19562)). Qed.
Lemma lem1161637 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term210 _19562 P _19561) = (term214 P _19561 _19562).
Proof. exact (MK_COMB (@lem1161636 P _19562) (@lem1161628 P _19561 _19562)). Qed.
Lemma lem1161648 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term179 _19562 P _19561) = (term214 P _19561 _19562).
Proof. exact (TRANS (@lem1161613 _19562 P _19561) (@lem1161637 P _19561 _19562)). Qed.
Lemma lem1161649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1161650 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term215 _19562 P _19561) = (term216 P _19561 _19562).
Proof. exact (MK_COMB (@lem1161649) (@lem1161648 P _19561 _19562)). Qed.
Lemma lem1161664 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1161665 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term211 _19562 P _19561) = (term212 P _19561 _19562).
Proof. exact (@lem1161664 (term41 P _19561) (term187 _19561 _19562)). Qed.
Lemma lem1161673 (P : nat -> Prop) (_19562 : nat) : (term213 P _19562) = (term213 P _19562).
Proof. exact (eq_refl (term213 P _19562)). Qed.
Lemma lem1161674 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : (term210 _19562 P _19561) = (term214 P _19561 _19562).
Proof. exact (MK_COMB (@lem1161673 P _19562) (@lem1161665 P _19561 _19562)). Qed.
Lemma lem1161685 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : ((term179 _19562 P _19561) = (term210 _19562 P _19561)) = ((term214 P _19561 _19562) = (term214 P _19561 _19562)).
Proof. exact (MK_COMB (@lem1161650 P _19561 _19562) (@lem1161674 P _19561 _19562)). Qed.
Lemma lem1161687 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1161688 (x : Prop) : (x = x) = True.
Proof. exact (@lem1161687 Prop x). Qed.
Lemma lem1161689 (P : nat -> Prop) (_19561 : nat) (_19562 : nat) : ((term214 P _19561 _19562) = (term214 P _19561 _19562)) = True.
Proof. exact (@lem1161688 (term214 P _19561 _19562)). Qed.
Lemma lem1161690 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : ((term179 _19562 P _19561) = (term210 _19562 P _19561)) = True.
Proof. exact (TRANS (@lem1161685 P _19561 _19562) (@lem1161689 P _19561 _19562)). Qed.
Lemma lem1161691 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : True = ((term179 _19562 P _19561) = (term210 _19562 P _19561)).
Proof. exact (SYM (@lem1161690 _19562 P _19561)). Qed.
Lemma lem1161692 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term179 _19562 P _19561) = (term210 _19562 P _19561).
Proof. exact (EQ_MP (@lem1161691 _19562 P _19561) (@lem0)). Qed.
Lemma lem1161693 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : term210 _19562 P _19561.
Proof. exact (EQ_MP (@lem1161692 _19562 P _19561) (@lem1161477 _19562 P _19561)). Qed.
Lemma lem1161695 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1161696 (_19561 : nat) (P : nat -> Prop) (_19562 : nat) : (term210 _19562 P _19561) = (term217 _19561 P _19562).
Proof. exact (@lem1161695 (term211 _19562 P _19561) (P _19562)). Qed.
Lemma lem1161698 (a : Prop) (b : Prop) : (term188 a b) = (term189 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1161699 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term218 _19562 P _19561) = (term219 _19562 P _19561).
Proof. exact (@lem1161698 (term187 _19561 _19562) (term41 P _19561)). Qed.
Lemma lem1161701 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1161702 (_19561 : nat) (_19562 : nat) : (term220 _19561 _19562) = (_19561 = _19562).
Proof. exact (@lem1161701 (_19561 = _19562)). Qed.
Lemma lem1161703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1161704 (_19561 : nat) (_19562 : nat) : (term221 _19561 _19562) = (term222 _19561 _19562).
Proof. exact (MK_COMB (@lem1161703) (@lem1161702 _19561 _19562)). Qed.
Lemma lem1161706 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1161707 (P : nat -> Prop) (_19561 : nat) : (term193 P _19561) = (P _19561).
Proof. exact (@lem1161706 (P _19561)). Qed.
Lemma lem1161708 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term219 _19562 P _19561) = (term223 _19562 P _19561).
Proof. exact (MK_COMB (@lem1161704 _19561 _19562) (@lem1161707 P _19561)). Qed.
Lemma lem1161709 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term218 _19562 P _19561) = (term223 _19562 P _19561).
Proof. exact (TRANS (@lem1161699 _19562 P _19561) (@lem1161708 _19562 P _19561)). Qed.
Lemma lem1161710 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1161711 (_19562 : nat) (P : nat -> Prop) (_19561 : nat) : (term224 _19562 P _19561) = (term225 _19562 P _19561).
Proof. exact (MK_COMB (@lem1161710) (@lem1161709 _19562 P _19561)). Qed.
Lemma lem1161712 (P : nat -> Prop) (_19562 : nat) : (P _19562) = (P _19562).
Proof. exact (eq_refl (P _19562)). Qed.
Lemma lem1161713 (_19561 : nat) (P : nat -> Prop) (_19562 : nat) : (term217 _19561 P _19562) = (term226 _19561 P _19562).
Proof. exact (MK_COMB (@lem1161711 _19562 P _19561) (@lem1161712 P _19562)). Qed.
Lemma lem1161714 (_19561 : nat) (P : nat -> Prop) (_19562 : nat) : (term210 _19562 P _19561) = (term226 _19561 P _19562).
Proof. exact (TRANS (@lem1161696 _19561 P _19562) (@lem1161713 _19561 P _19562)). Qed.
Lemma lem1161716 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : term227 n P i.
Proof. exact (conj (@lem1161599 n i P h1 h2) (@lem1161606 i P h2)). Qed.
Lemma lem1161718 (_19561 : nat) (P : nat -> Prop) (_19562 : nat) : term226 _19561 P _19562.
Proof. exact (EQ_MP (@lem1161714 _19561 P _19562) (@lem1161693 _19562 P _19561)). Qed.
Lemma lem1161719 (P : nat -> Prop) (n : nat -> nat) (i : nat) : term228 P n i.
Proof. exact (@lem1161718 i P (term204 n i)). Qed.
Lemma lem1161722 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : term229 P n i.
Proof. exact (@lem1161719 P n i (@lem1161716 n i P h1 h2)). Qed.
Lemma lem1161723 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : term230 P n i.
Proof. exact (fun h0 : term231 P n i => @lem1161722 n i P h1 h2). Qed.
Lemma lem1161725 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161726 (P : nat -> Prop) (n : nat -> nat) (i : nat) : (term230 P n i) = (term229 P n i).
Proof. exact (@lem1161725 (term229 P n i)). Qed.
Lemma lem1161727 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : term229 P n i.
Proof. exact (EQ_MP (@lem1161726 P n i) (@lem1161723 n i P h1 h2)). Qed.
Lemma lem1161730 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1161732 (P : nat -> Prop) (_19556 : nat) : (term48 P _19556) = (term232 P _19556).
Proof. exact (@lem1161730 (term29 P _19556)). Qed.
Lemma lem1161735 (_19556 : nat) (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term232 P _19556.
Proof. exact (EQ_MP (@lem1161732 P _19556) (@lem1161445 _19556 i P h1)). Qed.
Lemma lem1161736 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term115 i P) : term233 P n i.
Proof. exact (@lem1161735 (n i) i P h1). Qed.
Lemma lem1161739 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : False.
Proof. exact (@lem1161736 n i P h2 (@lem1161727 n i P h1 h2)). Qed.
Lemma lem1161740 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : term234.
Proof. exact (fun h0 : ~ False => @lem1161739 n i P h1 h2). Qed.
Lemma lem1161742 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161743 : term234 = False.
Proof. exact (@lem1161742 False). Qed.
Lemma lem1161744 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : False.
Proof. exact (EQ_MP (@lem1161743) (@lem1161740 n i P h1 h2)). Qed.
Lemma lem1161784 (P : nat -> Prop) (h1 : term56 P) : term56 P.
Proof. exact (h1). Qed.
Lemma lem1161785 (P : nat -> Prop) (h1 : term56 P) : term235 P.
Proof. exact (fun h0 : term180 P => @lem1161784 P h1). Qed.
Lemma lem1161787 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161788 (P : nat -> Prop) : (term235 P) = (term56 P).
Proof. exact (@lem1161787 (term56 P)). Qed.
Lemma lem1161789 (P : nat -> Prop) (h1 : term56 P) : term56 P.
Proof. exact (EQ_MP (@lem1161788 P) (@lem1161785 P h1)). Qed.
Lemma lem1161792 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1161794 (P : nat -> Prop) (_19558 : nat) : (term41 P _19558) = (term236 P _19558).
Proof. exact (@lem1161792 (P _19558)). Qed.
Lemma lem1161797 (_19558 : nat) (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term236 P _19558.
Proof. exact (EQ_MP (@lem1161794 P _19558) (@lem1161453 _19558 P i h1)). Qed.
Lemma lem1161798 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term237 P.
Proof. exact (@lem1161797 (NUMERAL 0) P i h1). Qed.
Lemma lem1161801 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : False.
Proof. exact (@lem1161798 P i h2 (@lem1161789 P h1)). Qed.
Lemma lem1161802 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : term234.
Proof. exact (fun h0 : ~ False => @lem1161801 P i h1 h2). Qed.
Lemma lem1161804 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161805 : term234 = False.
Proof. exact (@lem1161804 False). Qed.
Lemma lem1161806 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161805) (@lem1161802 P i h1 h2)). Qed.
Lemma lem1161846 (P : nat -> Prop) (i : nat) (h1 : term29 P i) : term29 P i.
Proof. exact (h1). Qed.
Lemma lem1161847 (P : nat -> Prop) (i : nat) (h1 : term29 P i) : term238 P i.
Proof. exact (fun h0 : term48 P i => @lem1161846 P i h1). Qed.
Lemma lem1161849 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161850 (P : nat -> Prop) (i : nat) : (term238 P i) = (term29 P i).
Proof. exact (@lem1161849 (term29 P i)). Qed.
Lemma lem1161851 (P : nat -> Prop) (i : nat) (h1 : term29 P i) : term29 P i.
Proof. exact (EQ_MP (@lem1161850 P i) (@lem1161847 P i h1)). Qed.
Lemma lem1161854 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1161856 (P : nat -> Prop) (_19560 : nat) : (term41 P _19560) = (term236 P _19560).
Proof. exact (@lem1161854 (P _19560)). Qed.
Lemma lem1161859 (_19560 : nat) (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term236 P _19560.
Proof. exact (EQ_MP (@lem1161856 P _19560) (@lem1161463 _19560 P i h1)). Qed.
Lemma lem1161860 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : term232 P i.
Proof. exact (@lem1161859 (S i) P i h1). Qed.
Lemma lem1161863 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : False.
Proof. exact (@lem1161860 P i h2 (@lem1161851 P i h1)). Qed.
Lemma lem1161864 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : term234.
Proof. exact (fun h0 : ~ False => @lem1161863 P i h1 h2). Qed.
Lemma lem1161866 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1161867 : term234 = False.
Proof. exact (@lem1161866 False). Qed.
Lemma lem1161868 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161867) (@lem1161864 P i h1 h2)). Qed.
Lemma lem1161869 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : (term29 P i) = False.
Proof. exact (prop_ext (fun h3 : term29 P i => @lem1161868 P i h1 h2) (fun h3 : False => @lem1161465 P i h1)). Qed.
Lemma lem1161870 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161869 P i h1 h2) (@lem1161465 P i h1)). Qed.
Lemma lem1161871 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : (term56 P) = False.
Proof. exact (prop_ext (fun h3 : term56 P => @lem1161806 P i h1 h2) (fun h3 : False => @lem1161455 P h1)). Qed.
Lemma lem1161872 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161871 P i h1 h2) (@lem1161455 P h1)). Qed.
Lemma lem1161873 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : (term29 P i) = False.
Proof. exact (prop_ext (fun h3 : term29 P i => @lem1161870 P i h1 h2) (fun h3 : False => @lem1161415 P i h1)). Qed.
Lemma lem1161874 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161873 P i h1 h2) (@lem1161415 P i h1)). Qed.
Lemma lem1161875 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : (term56 P) = False.
Proof. exact (prop_ext (fun h3 : term56 P => @lem1161872 P i h1 h2) (fun h3 : False => @lem1161391 P h1)). Qed.
Lemma lem1161876 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161875 P i h1 h2) (@lem1161391 P h1)). Qed.
Lemma lem1161877 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : (term29 P i) = False.
Proof. exact (prop_ext (fun h3 : term29 P i => @lem1161874 P i h1 h2) (fun h3 : False => @lem1161415 P i h1)). Qed.
Lemma lem1161878 (P : nat -> Prop) (i : nat) (h1 : term29 P i) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161877 P i h1 h2) (@lem1161415 P i h1)). Qed.
Lemma lem1161879 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : (term56 P) = False.
Proof. exact (prop_ext (fun h3 : term56 P => @lem1161876 P i h1 h2) (fun h3 : False => @lem1161391 P h1)). Qed.
Lemma lem1161880 (P : nat -> Prop) (i : nat) (h1 : term56 P) (h2 : term102 P i) : False.
Proof. exact (EQ_MP (@lem1161879 P i h1 h2) (@lem1161391 P h1)). Qed.
Lemma lem1161881 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : (term166 n) = False.
Proof. exact (prop_ext (fun h3 : term166 n => @lem1161744 n i P h1 h2) (fun h3 : False => @lem1161352 n h1)). Qed.
Lemma lem1161882 (n : nat -> nat) (i : nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term115 i P) : False.
Proof. exact (EQ_MP (@lem1161881 n i P h1 h2) (@lem1161352 n h1)). Qed.
Lemma lem1161883 (P : nat -> Prop) (i : nat) (h1 : term102 P i) : False.
Proof. exact (or_elim (@lem1161336 P i h1) (fun h0 : term56 P => @lem1161880 P i h0 h1) (fun h0 : term29 P i => @lem1161878 P i h0 h1)). Qed.
Lemma lem1161884 (n : nat -> nat) (P : nat -> Prop) (i : nat) (h1 : term166 n) (h2 : term127 P i) : False.
Proof. exact (or_elim (@lem1161329 P i h2) (fun h0 : term115 i P => @lem1161882 n i P h1 h0) (fun h0 : term102 P i => @lem1161883 P i h0)). Qed.
Lemma lem1161885 (n : nat -> nat) (P : nat -> Prop) (i : nat) (h1 : term166 n) (h2 : term127 P i) : (term127 P i) = False.
Proof. exact (prop_ext (fun h3 : term127 P i => @lem1161884 n P i h1 h2) (fun h3 : False => @lem1161329 P i h2)). Qed.
Lemma lem1161886 (n : nat -> nat) (P : nat -> Prop) (i : nat) (h1 : term166 n) (h2 : term127 P i) : False.
Proof. exact (EQ_MP (@lem1161885 n P i h1 h2) (@lem1161329 P i h2)). Qed.
Lemma lem1161887 (n : nat -> nat) (P : nat -> Prop) (i : nat) (h1 : term166 n) (h2 : term127 P i) : (term166 n) = False.
Proof. exact (prop_ext (fun h3 : term166 n => @lem1161886 n P i h1 h2) (fun h3 : False => @lem1161275 n h1)). Qed.
Lemma lem1161888 (n : nat -> nat) (P : nat -> Prop) (i : nat) (h1 : term166 n) (h2 : term127 P i) : False.
Proof. exact (EQ_MP (@lem1161887 n P i h1 h2) (@lem1161275 n h1)). Qed.
Lemma lem1161889 (n : nat -> nat) (P : nat -> Prop) (h1 : term166 n) (h2 : term10 P) : False.
Proof. exact (ex_elim (@lem1161129 P h2) (fun i : nat => fun h0 : term129 P i => @lem1161888 n P i h1 h0)). Qed.
Lemma lem1161890 (P : nat -> Prop) (h1 : term17) (h2 : term10 P) : False.
Proof. exact (ex_elim (@lem1161250 h1) (fun n : nat -> nat => fun h0 : term168 n => @lem1161889 n P h0 h2)). Qed.
Lemma lem1161891 (P : nat -> Prop) (h1 : term10 P) : term15.
Proof. exact (fun h0 : term17 => @lem1161890 P h0 h1). Qed.
Lemma lem1161892 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1161893 (P : nat -> Prop) (h1 : term10 P) : term16.
Proof. exact (EQ_MP (@lem1161892) (@lem1161891 P h1)). Qed.
Lemma lem1161894 (P : nat -> Prop) : term19 P.
Proof. exact (fun h0 : term10 P => @lem1161893 P h0). Qed.
Lemma lem1161899 : term23.
Proof. exact (fun P : nat -> Prop => @lem1161894 P). Qed.
Lemma lem1161900 : term22.
Proof. exact (EQ_MP (@lem1160978) (@lem1161899)). Qed.
Lemma lem1161901 (P : nat -> Prop) : term239 P.
Proof. exact (@lem1161900 P). Qed.
Lemma lem1161902 (P : nat -> Prop) : (term239 P) = (term11 P).
Proof. exact (eq_refl (term239 P)). Qed.
Lemma lem1161903 (P : nat -> Prop) : term11 P.
Proof. exact (EQ_MP (@lem1161902 P) (@lem1161901 P)). Qed.
Lemma lem1161905 (P : nat -> Prop) : term11 P.
Proof. exact (@lem1160814 P (@lem1161903 P)). Qed.
Lemma lem1161906 (P : nat -> Prop) (h1 : term10 P) : term15.
Proof. exact (@lem1161905 P (@lem1160799 P h1)). Qed.
Lemma lem1161907 (P : nat -> Prop) (h1 : term10 P) : False.
Proof. exact (@lem1161906 P h1 (@lem76132)). Qed.
Lemma lem1161908 (P : nat -> Prop) (h1 : term10 P) : (term10 P) = False.
Proof. exact (prop_ext (fun h2 : term10 P => @lem1161907 P h1) (fun h2 : False => @lem1160799 P h1)). Qed.
Lemma lem1161909 (P : nat -> Prop) (h1 : term10 P) : False.
Proof. exact (EQ_MP (@lem1161908 P h1) (@lem1160799 P h1)). Qed.
Lemma lem1161910 (P : nat -> Prop) : term9 P.
Proof. exact (fun h0 : term10 P => @lem1161909 P h0). Qed.
Lemma lem1161912 : term240.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1161914 {A : Type'} (P : type1143 A) : term241 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1161915 {_27312 : Type'} (P : type1143 _27312) : term241 _27312 P.
Proof. exact (@lem1161914 _27312 P). Qed.
Lemma lem1161916 {_27312 : Type'} : term242 _27312.
Proof. exact (@lem1161915 _27312 (term243 _27312)). Qed.
Lemma lem1161917 {_27312 : Type'} : (term244 _27312) = (term245 _27312).
Proof. exact (eq_refl (term244 _27312)). Qed.
Lemma lem1161918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1161919 {_27312 : Type'} : (term246 _27312) = (term247 _27312).
Proof. exact (MK_COMB (@lem1161918) (@lem1161917 _27312)). Qed.
Lemma lem1161920 {_27312 : Type'} (t : list _27312) : (term248 _27312 t) = (term249 _27312 t).
Proof. exact (eq_refl (term248 _27312 t)). Qed.
Lemma lem1161921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1161922 {_27312 : Type'} (t : list _27312) : (term250 _27312 t) = (term251 _27312 t).
Proof. exact (MK_COMB (@lem1161921) (@lem1161920 _27312 t)). Qed.
Lemma lem1161923 {_27312 : Type'} (h : _27312) (t : list _27312) : (term252 _27312 h t) = (term253 _27312 h t).
Proof. exact (eq_refl (term252 _27312 h t)). Qed.
Lemma lem1161924 {_27312 : Type'} (h : _27312) (t : list _27312) : (term254 _27312 h t) = (term255 _27312 h t).
Proof. exact (MK_COMB (@lem1161922 _27312 t) (@lem1161923 _27312 h t)). Qed.
Lemma lem1161925 {_27312 : Type'} (h : _27312) : (term256 _27312 h) = (term257 _27312 h).
Proof. exact (fun_ext (fun t : list _27312 => @lem1161924 _27312 h t)). Qed.
Lemma lem1161926 {_27312 : Type'} : (@all (list _27312)) = (@all (list _27312)).
Proof. exact (eq_refl (@all (list _27312))). Qed.
Lemma lem1161927 {_27312 : Type'} (h : _27312) : (term258 _27312 h) = (term259 _27312 h).
Proof. exact (MK_COMB (@lem1161926 _27312) (@lem1161925 _27312 h)). Qed.
Lemma lem1161928 {_27312 : Type'} : (term260 _27312) = (term261 _27312).
Proof. exact (fun_ext (fun h : _27312 => @lem1161927 _27312 h)). Qed.
Lemma lem1161929 {_27312 : Type'} : (@all _27312) = (@all _27312).
Proof. exact (eq_refl (@all _27312)). Qed.
Lemma lem1161930 {_27312 : Type'} : (term262 _27312) = (term263 _27312).
Proof. exact (MK_COMB (@lem1161929 _27312) (@lem1161928 _27312)). Qed.
Lemma lem1161931 {_27312 : Type'} : (term264 _27312) = (term265 _27312).
Proof. exact (MK_COMB (@lem1161919 _27312) (@lem1161930 _27312)). Qed.
Lemma lem1161932 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1161933 {_27312 : Type'} : (term266 _27312) = (term267 _27312).
Proof. exact (MK_COMB (@lem1161932) (@lem1161931 _27312)). Qed.
Lemma lem1161934 {_27312 : Type'} (l : list _27312) : (term248 _27312 l) = (term249 _27312 l).
Proof. exact (eq_refl (term248 _27312 l)). Qed.
Lemma lem1161935 {_27312 : Type'} : (term268 _27312) = (term243 _27312).
Proof. exact (fun_ext (fun l : list _27312 => @lem1161934 _27312 l)). Qed.
Lemma lem1161936 {_27312 : Type'} : (@all (list _27312)) = (@all (list _27312)).
Proof. exact (eq_refl (@all (list _27312))). Qed.
Lemma lem1161937 {_27312 : Type'} : (term269 _27312) = (term270 _27312).
Proof. exact (MK_COMB (@lem1161936 _27312) (@lem1161935 _27312)). Qed.
Lemma lem1161938 {_27312 : Type'} : (term242 _27312) = (term271 _27312).
Proof. exact (MK_COMB (@lem1161933 _27312) (@lem1161937 _27312)). Qed.
Lemma lem1161939 {_27312 : Type'} : term271 _27312.
Proof. exact (EQ_MP (@lem1161938 _27312) (@lem1161916 _27312)). Qed.
Lemma lem1161940 {_27312 : Type'} (t : list _27312) (h1 : term249 _27312 t) : term249 _27312 t.
Proof. exact (h1). Qed.
Lemma lem1161941 (m : nat) : term272 m.
Proof. exact (@lem1161912 m). Qed.
Lemma lem1161942 (m : nat) : (term272 m) = ((term273 m) = False).
Proof. exact (eq_refl (term272 m)). Qed.
Lemma lem1161963 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1161964 {_27312 : Type'} (x : _27312) : (@List.In _27312 x (@nil _27312)) = False.
Proof. exact (@lem1161963 _27312 x). Qed.
Lemma lem1161965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1161966 {_27312 : Type'} (x : _27312) : (term274 _27312 x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1161965) (@lem1161964 _27312 x)). Qed.
Lemma lem1161974 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1161975 {_27312 : Type'} : (@List.length _27312 (@nil _27312)) = (NUMERAL 0).
Proof. exact (@lem1161974 _27312). Qed.
Lemma lem1161976 (i : nat) : (Peano.lt i) = (Peano.lt i).
Proof. exact (eq_refl (Peano.lt i)). Qed.
Lemma lem1161977 {_27312 : Type'} (i : nat) : (term275 _27312 i) = (term273 i).
Proof. exact (MK_COMB (@lem1161976 i) (@lem1161975 _27312)). Qed.
Lemma lem1161979 (m : nat) : (term273 m) = False.
Proof. exact (EQ_MP (@lem1161942 m) (@lem1161941 m)). Qed.
Lemma lem1161980 (i : nat) : (term273 i) = False.
Proof. exact (@lem1161979 i). Qed.
Lemma lem1161981 {_27312 : Type'} (i : nat) : (term275 _27312 i) = False.
Proof. exact (TRANS (@lem1161977 _27312 i) (@lem1161980 i)). Qed.
Lemma lem1161982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1161983 {_27312 : Type'} (i : nat) : (term276 _27312 i) = (and False).
Proof. exact (MK_COMB (@lem1161982) (@lem1161981 _27312 i)). Qed.
Lemma lem1161986 {_27312 : Type'} (x : _27312) (i : nat) : (x = (@EL _27312 i (@nil _27312))) = (x = (@EL _27312 i (@nil _27312))).
Proof. exact (eq_refl (x = (@EL _27312 i (@nil _27312)))). Qed.
Lemma lem1161987 {_27312 : Type'} (x : _27312) (i : nat) : (term277 _27312 x i) = (term278 _27312 x i).
Proof. exact (MK_COMB (@lem1161983 _27312 i) (@lem1161986 _27312 x i)). Qed.
Lemma lem1161989 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1161990 {_27312 : Type'} (x : _27312) (i : nat) : (term278 _27312 x i) = False.
Proof. exact (@lem1161989 (x = (@EL _27312 i (@nil _27312)))). Qed.
Lemma lem1161991 {_27312 : Type'} (x : _27312) (i : nat) : (term277 _27312 x i) = False.
Proof. exact (TRANS (@lem1161987 _27312 x i) (@lem1161990 _27312 x i)). Qed.
Lemma lem1161992 {_27312 : Type'} (x : _27312) : (term279 _27312 x) = term280.
Proof. exact (fun_ext (fun i : nat => @lem1161991 _27312 x i)). Qed.
Lemma lem1161993 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1161994 {_27312 : Type'} (x : _27312) : (term281 _27312 x) = term282.
Proof. exact (MK_COMB (@lem1161993) (@lem1161992 _27312 x)). Qed.
Lemma lem1161996 {A : Type'} (t : Prop) : (term283 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1161997 (t : Prop) : (term284 t) = t.
Proof. exact (@lem1161996 nat t). Qed.
Lemma lem1161998 : term282 = False.
Proof. exact (@lem1161997 False). Qed.
Lemma lem1161999 {_27312 : Type'} (x : _27312) : (term281 _27312 x) = False.
Proof. exact (TRANS (@lem1161994 _27312 x) (@lem1161998)). Qed.
Lemma lem1162000 {_27312 : Type'} (x : _27312) : ((@List.In _27312 x (@nil _27312)) = (term281 _27312 x)) = (False = False).
Proof. exact (MK_COMB (@lem1161966 _27312 x) (@lem1161999 _27312 x)). Qed.
Lemma lem1162002 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1162003 : (False = False) = (~ False).
Proof. exact (@lem1162002 False). Qed.
Lemma lem1162005 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1162006 : (False = False) = True.
Proof. exact (TRANS (@lem1162003) (@lem1162005)). Qed.
Lemma lem1162007 {_27312 : Type'} (x : _27312) : ((@List.In _27312 x (@nil _27312)) = (term281 _27312 x)) = True.
Proof. exact (TRANS (@lem1162000 _27312 x) (@lem1162006)). Qed.
Lemma lem1162008 {_27312 : Type'} : (term285 _27312) = (term286 _27312).
Proof. exact (fun_ext (fun x : _27312 => @lem1162007 _27312 x)). Qed.
Lemma lem1162009 {_27312 : Type'} : (@all _27312) = (@all _27312).
Proof. exact (eq_refl (@all _27312)). Qed.
Lemma lem1162010 {_27312 : Type'} : (term245 _27312) = (term287 _27312).
Proof. exact (MK_COMB (@lem1162009 _27312) (@lem1162008 _27312)). Qed.
Lemma lem1162012 {A : Type'} (t : Prop) : (term288 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1162013 {_27312 : Type'} (t : Prop) : (term288 _27312 t) = t.
Proof. exact (@lem1162012 _27312 t). Qed.
Lemma lem1162014 {_27312 : Type'} : (term287 _27312) = True.
Proof. exact (@lem1162013 _27312 True). Qed.
Lemma lem1162015 {_27312 : Type'} : (term245 _27312) = True.
Proof. exact (TRANS (@lem1162010 _27312) (@lem1162014 _27312)). Qed.
Lemma lem1162016 {_27312 : Type'} : True = (term245 _27312).
Proof. exact (SYM (@lem1162015 _27312)). Qed.
Lemma lem1162017 {_27312 : Type'} : term245 _27312.
Proof. exact (EQ_MP (@lem1162016 _27312) (@lem0)). Qed.
Lemma lem1162025 {A : Type'} : term289 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1162026 {A : Type'} (h : A) : term290 A h.
Proof. exact (@lem1162025 A h). Qed.
Lemma lem1162027 {A : Type'} (h : A) : (term290 A h) = (term291 A h).
Proof. exact (eq_refl (term290 A h)). Qed.
Lemma lem1162028 {A : Type'} (h : A) : term291 A h.
Proof. exact (EQ_MP (@lem1162027 A h) (@lem1162026 A h)). Qed.
Lemma lem1162029 {A : Type'} (h : A) (t : list A) : term292 A h t.
Proof. exact (@lem1162028 A h t). Qed.
Lemma lem1162030 {A : Type'} (h : A) (t : list A) : (term292 A h t) = ((term293 A h t) = (term294 A t)).
Proof. exact (eq_refl (term292 A h t)). Qed.
Lemma lem1162033 {_27312 : Type'} (x : _27312) (t : list _27312) (h1 : term249 _27312 t) : term295 _27312 t x.
Proof. exact (@lem1161940 _27312 t h1 x). Qed.
Lemma lem1162034 {_27312 : Type'} (x : _27312) (t : list _27312) : (term295 _27312 t x) = ((@List.In _27312 x t) = (term296 _27312 x t)).
Proof. exact (eq_refl (term295 _27312 t x)). Qed.
Lemma lem1162043 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term297 _25376 x h t) = (term298 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1162044 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : (term297 _27312 x h t) = (term298 _27312 h x t).
Proof. exact (@lem1162043 _27312 h x t). Qed.
Lemma lem1162050 {_27312 : Type'} (x : _27312) (t : list _27312) (h1 : term249 _27312 t) : (@List.In _27312 x t) = (term296 _27312 x t).
Proof. exact (EQ_MP (@lem1162034 _27312 x t) (@lem1162033 _27312 x t h1)). Qed.
Lemma lem1162051 {_27312 : Type'} (x : _27312) (t : list _27312) (h1 : term249 _27312 t) : (@List.In _27312 x t) = (term296 _27312 x t).
Proof. exact (@lem1162050 _27312 x t h1). Qed.
Lemma lem1162060 {_27312 : Type'} (x : _27312) (h : _27312) : (term299 _27312 x h) = (term299 _27312 x h).
Proof. exact (eq_refl (term299 _27312 x h)). Qed.
Lemma lem1162061 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) (h1 : term249 _27312 t) : (term298 _27312 h x t) = (term300 _27312 h x t).
Proof. exact (MK_COMB (@lem1162060 _27312 x h) (@lem1162051 _27312 x t h1)). Qed.
Lemma lem1162064 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) (h1 : term249 _27312 t) : (term297 _27312 x h t) = (term300 _27312 h x t).
Proof. exact (TRANS (@lem1162044 _27312 h x t) (@lem1162061 _27312 h x t h1)). Qed.
Lemma lem1162065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1162066 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) (h1 : term249 _27312 t) : (term301 _27312 x h t) = (term302 _27312 h x t).
Proof. exact (MK_COMB (@lem1162065) (@lem1162064 _27312 h x t h1)). Qed.
Lemma lem1162074 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (EQ_MP (@lem1162030 A h t) (@lem1162029 A h t)). Qed.
Lemma lem1162075 {_27312 : Type'} (h : _27312) (t : list _27312) : (term293 _27312 h t) = (term294 _27312 t).
Proof. exact (@lem1162074 _27312 h t). Qed.
Lemma lem1162076 (i : nat) : (Peano.lt i) = (Peano.lt i).
Proof. exact (eq_refl (Peano.lt i)). Qed.
Lemma lem1162077 {_27312 : Type'} (h : _27312) (i : nat) (t : list _27312) : (term303 _27312 i h t) = (term304 _27312 i t).
Proof. exact (MK_COMB (@lem1162076 i) (@lem1162075 _27312 h t)). Qed.
Lemma lem1162078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162079 {_27312 : Type'} (h : _27312) (i : nat) (t : list _27312) : (term305 _27312 i h t) = (term306 _27312 i t).
Proof. exact (MK_COMB (@lem1162078) (@lem1162077 _27312 h i t)). Qed.
Lemma lem1162082 {_27312 : Type'} (x : _27312) (i : nat) (h : _27312) (t : list _27312) : (x = (term307 _27312 i h t)) = (x = (term307 _27312 i h t)).
Proof. exact (eq_refl (x = (term307 _27312 i h t))). Qed.
Lemma lem1162083 {_27312 : Type'} (x : _27312) (i : nat) (h : _27312) (t : list _27312) : (term308 _27312 x i h t) = (term309 _27312 x i h t).
Proof. exact (MK_COMB (@lem1162079 _27312 h i t) (@lem1162082 _27312 x i h t)). Qed.
Lemma lem1162086 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term310 _27312 x h t) = (term311 _27312 x h t).
Proof. exact (fun_ext (fun i : nat => @lem1162083 _27312 x i h t)). Qed.
Lemma lem1162087 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162088 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term312 _27312 x h t) = (term313 _27312 x h t).
Proof. exact (MK_COMB (@lem1162087) (@lem1162086 _27312 x h t)). Qed.
Lemma lem1162093 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) (h1 : term249 _27312 t) : ((term297 _27312 x h t) = (term312 _27312 x h t)) = ((term300 _27312 h x t) = (term313 _27312 x h t)).
Proof. exact (MK_COMB (@lem1162066 _27312 h x t h1) (@lem1162088 _27312 x h t)). Qed.
Lemma lem1162096 {_27312 : Type'} (h : _27312) (t : list _27312) (h1 : term249 _27312 t) : (term314 _27312 h t) = (term315 _27312 h t).
Proof. exact (fun_ext (fun x : _27312 => @lem1162093 _27312 x h t h1)). Qed.
Lemma lem1162097 {_27312 : Type'} : (@all _27312) = (@all _27312).
Proof. exact (eq_refl (@all _27312)). Qed.
Lemma lem1162098 {_27312 : Type'} (h : _27312) (t : list _27312) (h1 : term249 _27312 t) : (term253 _27312 h t) = (term316 _27312 h t).
Proof. exact (MK_COMB (@lem1162097 _27312) (@lem1162096 _27312 h t h1)). Qed.
Lemma lem1162103 {_27312 : Type'} (h : _27312) (t : list _27312) (h1 : term249 _27312 t) : (term316 _27312 h t) = (term253 _27312 h t).
Proof. exact (SYM (@lem1162098 _27312 h t h1)). Qed.
Lemma lem1162105 (P : nat -> Prop) : (term7 P) = (term8 P).
Proof. exact (EQ_MP (@lem1160798 P) (@lem1161910 P)). Qed.
Lemma lem1162106 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term317 _27312 x h t) = (term318 _27312 x h t).
Proof. exact (@lem1162105 (term311 _27312 x h t)). Qed.
Lemma lem1162107 {_27312 : Type'} (x : _27312) (i : nat) (h : _27312) (t : list _27312) : (term319 _27312 x h t i) = (term309 _27312 x i h t).
Proof. exact (eq_refl (term319 _27312 x h t i)). Qed.
Lemma lem1162108 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term320 _27312 x h t) = (term311 _27312 x h t).
Proof. exact (fun_ext (fun i : nat => @lem1162107 _27312 x i h t)). Qed.
Lemma lem1162109 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162110 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term317 _27312 x h t) = (term313 _27312 x h t).
Proof. exact (MK_COMB (@lem1162109) (@lem1162108 _27312 x h t)). Qed.
Lemma lem1162111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1162112 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term321 _27312 x h t) = (term322 _27312 x h t).
Proof. exact (MK_COMB (@lem1162111) (@lem1162110 _27312 x h t)). Qed.
Lemma lem1162113 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term323 _27312 x h t) = (term324 _27312 x h t).
Proof. exact (eq_refl (term323 _27312 x h t)). Qed.
Lemma lem1162114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1162115 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term325 _27312 x h t) = (term326 _27312 x h t).
Proof. exact (MK_COMB (@lem1162114) (@lem1162113 _27312 x h t)). Qed.
Lemma lem1162116 {_27312 : Type'} (x : _27312) (i : nat) (h : _27312) (t : list _27312) : (term327 _27312 x h t i) = (term328 _27312 x i h t).
Proof. exact (eq_refl (term327 _27312 x h t i)). Qed.
Lemma lem1162117 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term329 _27312 x h t) = (term330 _27312 x h t).
Proof. exact (fun_ext (fun i : nat => @lem1162116 _27312 x i h t)). Qed.
Lemma lem1162118 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162119 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term331 _27312 x h t) = (term332 _27312 x h t).
Proof. exact (MK_COMB (@lem1162118) (@lem1162117 _27312 x h t)). Qed.
Lemma lem1162120 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term318 _27312 x h t) = (term333 _27312 x h t).
Proof. exact (MK_COMB (@lem1162115 _27312 x h t) (@lem1162119 _27312 x h t)). Qed.
Lemma lem1162121 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : ((term317 _27312 x h t) = (term318 _27312 x h t)) = ((term313 _27312 x h t) = (term333 _27312 x h t)).
Proof. exact (MK_COMB (@lem1162112 _27312 x h t) (@lem1162120 _27312 x h t)). Qed.
Lemma lem1162122 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term313 _27312 x h t) = (term333 _27312 x h t).
Proof. exact (EQ_MP (@lem1162121 _27312 x h t) (@lem1162106 _27312 x h t)). Qed.
Lemma lem1162123 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : (term302 _27312 h x t) = (term302 _27312 h x t).
Proof. exact (eq_refl (term302 _27312 h x t)). Qed.
Lemma lem1162124 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : ((term300 _27312 h x t) = (term313 _27312 x h t)) = ((term300 _27312 h x t) = (term333 _27312 x h t)).
Proof. exact (MK_COMB (@lem1162123 _27312 h x t) (@lem1162122 _27312 x h t)). Qed.
Lemma lem1162125 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : ((term300 _27312 h x t) = (term333 _27312 x h t)) = ((term300 _27312 h x t) = (term313 _27312 x h t)).
Proof. exact (SYM (@lem1162124 _27312 x h t)). Qed.
Lemma lem1162145 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1160777 n) (@lem1160776 n)). Qed.
Lemma lem1162146 {_27312 : Type'} (t : list _27312) : (term334 _27312 t) = True.
Proof. exact (@lem1162145 (@List.length _27312 t)). Qed.
Lemma lem1162147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162148 {_27312 : Type'} (t : list _27312) : (term335 _27312 t) = (and True).
Proof. exact (MK_COMB (@lem1162147) (@lem1162146 _27312 t)). Qed.
Lemma lem1162152 {_25569 : Type'} (l : list _25569) : (term336 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1162153 {_27312 : Type'} (l : list _27312) : (term336 _27312 l) = (@hd _27312 l).
Proof. exact (@lem1162152 _27312 l). Qed.
Lemma lem1162154 {_27312 : Type'} (h : _27312) (t : list _27312) : (term337 _27312 h t) = (term338 _27312 h t).
Proof. exact (@lem1162153 _27312 (@cons _27312 h t)). Qed.
Lemma lem1162156 {A : Type'} (t : list A) (h : A) : (term338 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1162157 {_27312 : Type'} (t : list _27312) (h : _27312) : (term338 _27312 h t) = h.
Proof. exact (@lem1162156 _27312 t h). Qed.
Lemma lem1162158 {_27312 : Type'} (t : list _27312) (h : _27312) : (term337 _27312 h t) = h.
Proof. exact (TRANS (@lem1162154 _27312 h t) (@lem1162157 _27312 t h)). Qed.
Lemma lem1162159 {_27312 : Type'} (x : _27312) : (@eq _27312 x) = (@eq _27312 x).
Proof. exact (eq_refl (@eq _27312 x)). Qed.
Lemma lem1162160 {_27312 : Type'} (t : list _27312) (x : _27312) (h : _27312) : (x = (term337 _27312 h t)) = (x = h).
Proof. exact (MK_COMB (@lem1162159 _27312 x) (@lem1162158 _27312 t h)). Qed.
Lemma lem1162163 {_27312 : Type'} (t : list _27312) (x : _27312) (h : _27312) : (term324 _27312 x h t) = (term339 _27312 x h).
Proof. exact (MK_COMB (@lem1162148 _27312 t) (@lem1162160 _27312 t x h)). Qed.
Lemma lem1162165 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1162166 {_27312 : Type'} (x : _27312) (h : _27312) : (term339 _27312 x h) = (x = h).
Proof. exact (@lem1162165 (x = h)). Qed.
Lemma lem1162169 {_27312 : Type'} (t : list _27312) (x : _27312) (h : _27312) : (term324 _27312 x h t) = (x = h).
Proof. exact (TRANS (@lem1162163 _27312 t x h) (@lem1162166 _27312 x h)). Qed.
Lemma lem1162170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1162171 {_27312 : Type'} (t : list _27312) (x : _27312) (h : _27312) : (term326 _27312 x h t) = (term299 _27312 x h).
Proof. exact (MK_COMB (@lem1162170) (@lem1162169 _27312 t x h)). Qed.
Lemma lem1162179 (m : nat) (n : nat) : (term5 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1160783 m n) (@lem1160782 m n)). Qed.
Lemma lem1162180 {_27312 : Type'} (i : nat) (t : list _27312) : (term340 _27312 i t) = (term341 _27312 i t).
Proof. exact (@lem1162179 i (@List.length _27312 t)). Qed.
Lemma lem1162181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162182 {_27312 : Type'} (i : nat) (t : list _27312) : (term342 _27312 i t) = (term343 _27312 i t).
Proof. exact (MK_COMB (@lem1162181) (@lem1162180 _27312 i t)). Qed.
Lemma lem1162186 {_25569 : Type'} (n : nat) (l : list _25569) : (term344 _25569 n l) = (term345 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1162187 {_27312 : Type'} (n : nat) (l : list _27312) : (term344 _27312 n l) = (term345 _27312 n l).
Proof. exact (@lem1162186 _27312 n l). Qed.
Lemma lem1162188 {_27312 : Type'} (i : nat) (h : _27312) (t : list _27312) : (term346 _27312 i h t) = (term347 _27312 i h t).
Proof. exact (@lem1162187 _27312 i (@cons _27312 h t)). Qed.
Lemma lem1162190 {A : Type'} (h : A) (t : list A) : (term348 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1162191 {_27312 : Type'} (h : _27312) (t : list _27312) : (term348 _27312 h t) = t.
Proof. exact (@lem1162190 _27312 h t). Qed.
Lemma lem1162192 {_27312 : Type'} (i : nat) : (@EL _27312 i) = (@EL _27312 i).
Proof. exact (eq_refl (@EL _27312 i)). Qed.
Lemma lem1162193 {_27312 : Type'} (h : _27312) (i : nat) (t : list _27312) : (term347 _27312 i h t) = (@EL _27312 i t).
Proof. exact (MK_COMB (@lem1162192 _27312 i) (@lem1162191 _27312 h t)). Qed.
Lemma lem1162194 {_27312 : Type'} (h : _27312) (i : nat) (t : list _27312) : (term346 _27312 i h t) = (@EL _27312 i t).
Proof. exact (TRANS (@lem1162188 _27312 i h t) (@lem1162193 _27312 h i t)). Qed.
Lemma lem1162195 {_27312 : Type'} (x : _27312) : (@eq _27312 x) = (@eq _27312 x).
Proof. exact (eq_refl (@eq _27312 x)). Qed.
Lemma lem1162196 {_27312 : Type'} (h : _27312) (x : _27312) (i : nat) (t : list _27312) : (x = (term346 _27312 i h t)) = (x = (@EL _27312 i t)).
Proof. exact (MK_COMB (@lem1162195 _27312 x) (@lem1162194 _27312 h i t)). Qed.
Lemma lem1162199 {_27312 : Type'} (h : _27312) (x : _27312) (i : nat) (t : list _27312) : (term328 _27312 x i h t) = (term349 _27312 x i t).
Proof. exact (MK_COMB (@lem1162182 _27312 i t) (@lem1162196 _27312 h x i t)). Qed.
Lemma lem1162202 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : (term330 _27312 x h t) = (term350 _27312 x t).
Proof. exact (fun_ext (fun i : nat => @lem1162199 _27312 h x i t)). Qed.
Lemma lem1162203 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162204 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : (term332 _27312 x h t) = (term296 _27312 x t).
Proof. exact (MK_COMB (@lem1162203) (@lem1162202 _27312 h x t)). Qed.
Lemma lem1162209 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : (term333 _27312 x h t) = (term300 _27312 h x t).
Proof. exact (MK_COMB (@lem1162171 _27312 t x h) (@lem1162204 _27312 h x t)). Qed.
Lemma lem1162212 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : (term302 _27312 h x t) = (term302 _27312 h x t).
Proof. exact (eq_refl (term302 _27312 h x t)). Qed.
Lemma lem1162213 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : ((term300 _27312 h x t) = (term333 _27312 x h t)) = ((term300 _27312 h x t) = (term300 _27312 h x t)).
Proof. exact (MK_COMB (@lem1162212 _27312 h x t) (@lem1162209 _27312 h x t)). Qed.
Lemma lem1162215 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1162216 (x : Prop) : (x = x) = True.
Proof. exact (@lem1162215 Prop x). Qed.
Lemma lem1162217 {_27312 : Type'} (h : _27312) (x : _27312) (t : list _27312) : ((term300 _27312 h x t) = (term300 _27312 h x t)) = True.
Proof. exact (@lem1162216 (term300 _27312 h x t)). Qed.
Lemma lem1162218 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : ((term300 _27312 h x t) = (term333 _27312 x h t)) = True.
Proof. exact (TRANS (@lem1162213 _27312 h x t) (@lem1162217 _27312 h x t)). Qed.
Lemma lem1162219 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : True = ((term300 _27312 h x t) = (term333 _27312 x h t)).
Proof. exact (SYM (@lem1162218 _27312 x h t)). Qed.
Lemma lem1162220 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term300 _27312 h x t) = (term333 _27312 x h t).
Proof. exact (EQ_MP (@lem1162219 _27312 x h t) (@lem0)). Qed.
Lemma lem1162221 {_27312 : Type'} (x : _27312) (h : _27312) (t : list _27312) : (term300 _27312 h x t) = (term313 _27312 x h t).
Proof. exact (EQ_MP (@lem1162125 _27312 x h t) (@lem1162220 _27312 x h t)). Qed.
Lemma lem1162226 {_27312 : Type'} (h : _27312) (t : list _27312) : term316 _27312 h t.
Proof. exact (fun x : _27312 => @lem1162221 _27312 x h t). Qed.
Lemma lem1162227 {_27312 : Type'} (h : _27312) (t : list _27312) (h1 : term249 _27312 t) : term253 _27312 h t.
Proof. exact (EQ_MP (@lem1162103 _27312 h t h1) (@lem1162226 _27312 h t)). Qed.
Lemma lem1162228 {_27312 : Type'} (h : _27312) (t : list _27312) : term255 _27312 h t.
Proof. exact (fun h0 : term249 _27312 t => @lem1162227 _27312 h t h0). Qed.
Lemma lem1162233 {_27312 : Type'} (h : _27312) : term259 _27312 h.
Proof. exact (fun t : list _27312 => @lem1162228 _27312 h t). Qed.
Lemma lem1162238 {_27312 : Type'} : term263 _27312.
Proof. exact (fun h : _27312 => @lem1162233 _27312 h). Qed.
Lemma lem1162239 {_27312 : Type'} : term265 _27312.
Proof. exact (conj (@lem1162017 _27312) (@lem1162238 _27312)). Qed.
Lemma lem1162240 {_27312 : Type'} : term270 _27312.
Proof. exact (@lem1161939 _27312 (@lem1162239 _27312)). Qed.
