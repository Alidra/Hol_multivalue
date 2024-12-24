Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_MULT_LCANCEL_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem83874 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem83875 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem83874 m n p h1)). Qed.
Lemma lem83876 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem83877 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem83876 m n p h1)). Qed.
Lemma lem83878 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem83875 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem83877 m n p h1)). Qed.
Lemma lem83879 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem83878 m n p)). Qed.
Lemma lem83880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83881 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem83880) (@lem83879 m n)). Qed.
Lemma lem83882 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem83881 m n)). Qed.
Lemma lem83883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83884 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem83883) (@lem83882 m)). Qed.
Lemma lem83885 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem83884 m)). Qed.
Lemma lem83886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83887 : term12 = term13.
Proof. exact (MK_COMB (@lem83886) (@lem83885)). Qed.
Lemma lem83888 : term13.
Proof. exact (EQ_MP (@lem83887) (@lem77960)). Qed.
Lemma lem83902 (n : nat) : term14 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem83903 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem83904 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem83903 n) (@lem83902 n)). Qed.
Lemma lem83905 (n : nat) : term16 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem83918 : term17.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem83919 : term18.
Proof. exact (proj2 (@lem83918)). Qed.
Lemma lem83920 : term19.
Proof. exact (proj2 (@lem83919)). Qed.
Lemma lem83921 : term20.
Proof. exact (proj2 (@lem83920)). Qed.
Lemma lem83929 : term21.
Proof. exact (proj1 (@lem83921)). Qed.
Lemma lem83930 (m : nat) : term22 m.
Proof. exact (@lem83929 m). Qed.
Lemma lem83931 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem83932 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem83931 m) (@lem83930 m)). Qed.
Lemma lem83933 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem83932 m n). Qed.
Lemma lem83934 (m : nat) (n : nat) : (term24 m n) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem83948 : term27.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem83949 (n : nat) : term28 n.
Proof. exact (@lem83948 n). Qed.
Lemma lem83950 (n : nat) : (term28 n) = ((term29 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem83953 (P : nat -> Prop) : term30 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem83954 : term31.
Proof. exact (@lem83953 term32). Qed.
Lemma lem83955 : term33 = term34.
Proof. exact (eq_refl term33). Qed.
Lemma lem83956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem83957 : term35 = term36.
Proof. exact (MK_COMB (@lem83956) (@lem83955)). Qed.
Lemma lem83958 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem83959 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83960 (m : nat) : (term39 m) = (term40 m).
Proof. exact (MK_COMB (@lem83959) (@lem83958 m)). Qed.
Lemma lem83961 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem83962 (m : nat) : (term43 m) = (term44 m).
Proof. exact (MK_COMB (@lem83960 m) (@lem83961 m)). Qed.
Lemma lem83963 : term45 = term46.
Proof. exact (fun_ext (fun m : nat => @lem83962 m)). Qed.
Lemma lem83964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83965 : term47 = term48.
Proof. exact (MK_COMB (@lem83964) (@lem83963)). Qed.
Lemma lem83966 : term49 = term50.
Proof. exact (MK_COMB (@lem83957) (@lem83965)). Qed.
Lemma lem83967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83968 : term51 = term52.
Proof. exact (MK_COMB (@lem83967) (@lem83966)). Qed.
Lemma lem83969 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem83970 : term53 = term32.
Proof. exact (fun_ext (fun m : nat => @lem83969 m)). Qed.
Lemma lem83971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83972 : term54 = term55.
Proof. exact (MK_COMB (@lem83971) (@lem83970)). Qed.
Lemma lem83973 : term31 = term56.
Proof. exact (MK_COMB (@lem83968) (@lem83972)). Qed.
Lemma lem83974 : term56.
Proof. exact (EQ_MP (@lem83973) (@lem83954)). Qed.
Lemma lem83989 (n : nat) : (term29 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem83950 n) (@lem83949 n)). Qed.
Lemma lem83990 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem83991 (n : nat) : (term57 n) = term58.
Proof. exact (MK_COMB (@lem83990) (@lem83989 n)). Qed.
Lemma lem83993 (n : nat) : (term29 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem83950 n) (@lem83949 n)). Qed.
Lemma lem83994 (p : nat) : (term29 p) = (NUMERAL 0).
Proof. exact (@lem83993 p). Qed.
Lemma lem83995 (n : nat) (p : nat) : ((term29 n) = (term29 p)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem83991 n) (@lem83994 p)). Qed.
Lemma lem83997 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem83998 (x : nat) : (x = x) = True.
Proof. exact (@lem83997 nat x). Qed.
Lemma lem83999 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem83998 (NUMERAL 0)). Qed.
Lemma lem84000 (n : nat) (p : nat) : ((term29 n) = (term29 p)) = True.
Proof. exact (TRANS (@lem83995 n p) (@lem83999)). Qed.
Lemma lem84001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84002 (n : nat) (p : nat) : (term59 n p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem84001) (@lem84000 n p)). Qed.
Lemma lem84006 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem84007 (x : nat) : (x = x) = True.
Proof. exact (@lem84006 nat x). Qed.
Lemma lem84008 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem84007 (NUMERAL 0)). Qed.
Lemma lem84009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem84010 : term60 = (or True).
Proof. exact (MK_COMB (@lem84009) (@lem84008)). Qed.
Lemma lem84013 (n : nat) (p : nat) : (n = p) = (n = p).
Proof. exact (eq_refl (n = p)). Qed.
Lemma lem84014 (n : nat) (p : nat) : (term61 n p) = (term62 n p).
Proof. exact (MK_COMB (@lem84010) (@lem84013 n p)). Qed.
Lemma lem84016 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem84017 (n : nat) (p : nat) : (term62 n p) = True.
Proof. exact (@lem84016 (n = p)). Qed.
Lemma lem84018 (n : nat) (p : nat) : (term61 n p) = True.
Proof. exact (TRANS (@lem84014 n p) (@lem84017 n p)). Qed.
Lemma lem84019 (n : nat) (p : nat) : (((term29 n) = (term29 p)) = (term61 n p)) = (True = True).
Proof. exact (MK_COMB (@lem84002 n p) (@lem84018 n p)). Qed.
Lemma lem84021 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem84022 : (True = True) = True.
Proof. exact (@lem84021 True). Qed.
Lemma lem84023 (n : nat) (p : nat) : (((term29 n) = (term29 p)) = (term61 n p)) = True.
Proof. exact (TRANS (@lem84019 n p) (@lem84022)). Qed.
Lemma lem84024 (n : nat) : (term63 n) = term64.
Proof. exact (fun_ext (fun p : nat => @lem84023 n p)). Qed.
Lemma lem84025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84026 (n : nat) : (term65 n) = term66.
Proof. exact (MK_COMB (@lem84025) (@lem84024 n)). Qed.
Lemma lem84028 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem84029 (t : Prop) : (term68 t) = t.
Proof. exact (@lem84028 nat t). Qed.
Lemma lem84030 : term66 = True.
Proof. exact (@lem84029 True). Qed.
Lemma lem84031 (n : nat) : (term65 n) = True.
Proof. exact (TRANS (@lem84026 n) (@lem84030)). Qed.
Lemma lem84032 : term69 = term64.
Proof. exact (fun_ext (fun n : nat => @lem84031 n)). Qed.
Lemma lem84033 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84034 : term34 = term66.
Proof. exact (MK_COMB (@lem84033) (@lem84032)). Qed.
Lemma lem84036 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem84037 (t : Prop) : (term68 t) = t.
Proof. exact (@lem84036 nat t). Qed.
Lemma lem84038 : term66 = True.
Proof. exact (@lem84037 True). Qed.
Lemma lem84039 : term34 = True.
Proof. exact (TRANS (@lem84034) (@lem84038)). Qed.
Lemma lem84040 : True = term34.
Proof. exact (SYM (@lem84039)). Qed.
Lemma lem84041 : term34.
Proof. exact (EQ_MP (@lem84040) (@lem0)). Qed.
Lemma lem84055 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem83934 m n) (@lem83933 m n)). Qed.
Lemma lem84056 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem84057 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem84056) (@lem84055 m n)). Qed.
Lemma lem84059 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem83934 m n) (@lem83933 m n)). Qed.
Lemma lem84060 (m : nat) (p : nat) : (term25 m p) = (term26 m p).
Proof. exact (@lem84059 m p). Qed.
Lemma lem84061 (n : nat) (m : nat) (p : nat) : ((term25 m n) = (term25 m p)) = ((term26 m n) = (term26 m p)).
Proof. exact (MK_COMB (@lem84057 m n) (@lem84060 m p)). Qed.
Lemma lem84064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84065 (n : nat) (m : nat) (p : nat) : (term72 n m p) = (term73 n m p).
Proof. exact (MK_COMB (@lem84064) (@lem84061 n m p)). Qed.
Lemma lem84069 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem83905 n (@lem83904 n)). Qed.
Lemma lem84070 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem84069 m). Qed.
Lemma lem84071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem84072 (m : nat) : (term74 m) = (or False).
Proof. exact (MK_COMB (@lem84071) (@lem84070 m)). Qed.
Lemma lem84075 (n : nat) (p : nat) : (n = p) = (n = p).
Proof. exact (eq_refl (n = p)). Qed.
Lemma lem84076 (m : nat) (n : nat) (p : nat) : (term75 m n p) = (term76 n p).
Proof. exact (MK_COMB (@lem84072 m) (@lem84075 n p)). Qed.
Lemma lem84078 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem84079 (n : nat) (p : nat) : (term76 n p) = (n = p).
Proof. exact (@lem84078 (n = p)). Qed.
Lemma lem84082 (m : nat) (n : nat) (p : nat) : (term75 m n p) = (n = p).
Proof. exact (TRANS (@lem84076 m n p) (@lem84079 n p)). Qed.
Lemma lem84083 (m : nat) (n : nat) (p : nat) : (((term25 m n) = (term25 m p)) = (term75 m n p)) = (((term26 m n) = (term26 m p)) = (n = p)).
Proof. exact (MK_COMB (@lem84065 n m p) (@lem84082 m n p)). Qed.
Lemma lem84086 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (fun_ext (fun p : nat => @lem84083 m n p)). Qed.
Lemma lem84087 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84088 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem84087) (@lem84086 m n)). Qed.
Lemma lem84093 (m : nat) : (term81 m) = (term82 m).
Proof. exact (fun_ext (fun n : nat => @lem84088 m n)). Qed.
Lemma lem84094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84095 (m : nat) : (term42 m) = (term83 m).
Proof. exact (MK_COMB (@lem84094) (@lem84093 m)). Qed.
Lemma lem84100 (m : nat) : (term83 m) = (term42 m).
Proof. exact (SYM (@lem84095 m)). Qed.
Lemma lem84102 (P : nat -> Prop) : term30 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem84103 (m : nat) : term84 m.
Proof. exact (@lem84102 (term82 m)). Qed.
Lemma lem84104 (m : nat) : (term85 m) = (term86 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem84105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem84106 (m : nat) : (term87 m) = (term88 m).
Proof. exact (MK_COMB (@lem84105) (@lem84104 m)). Qed.
Lemma lem84107 (m : nat) (n : nat) : (term89 m n) = (term80 m n).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem84108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem84109 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem84108) (@lem84107 m n)). Qed.
Lemma lem84110 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem84111 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (MK_COMB (@lem84109 m n) (@lem84110 m n)). Qed.
Lemma lem84112 (m : nat) : (term96 m) = (term97 m).
Proof. exact (fun_ext (fun n : nat => @lem84111 m n)). Qed.
Lemma lem84113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84114 (m : nat) : (term98 m) = (term99 m).
Proof. exact (MK_COMB (@lem84113) (@lem84112 m)). Qed.
Lemma lem84115 (m : nat) : (term100 m) = (term101 m).
Proof. exact (MK_COMB (@lem84106 m) (@lem84114 m)). Qed.
Lemma lem84116 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem84117 (m : nat) : (term102 m) = (term103 m).
Proof. exact (MK_COMB (@lem84116) (@lem84115 m)). Qed.
Lemma lem84118 (m : nat) (n : nat) : (term89 m n) = (term80 m n).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem84119 (m : nat) : (term104 m) = (term82 m).
Proof. exact (fun_ext (fun n : nat => @lem84118 m n)). Qed.
Lemma lem84120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84121 (m : nat) : (term105 m) = (term83 m).
Proof. exact (MK_COMB (@lem84120) (@lem84119 m)). Qed.
Lemma lem84122 (m : nat) : (term84 m) = (term106 m).
Proof. exact (MK_COMB (@lem84117 m) (@lem84121 m)). Qed.
Lemma lem84123 (m : nat) : term106 m.
Proof. exact (EQ_MP (@lem84122 m) (@lem84103 m)). Qed.
Lemma lem84124 (m : nat) (n : nat) (h1 : term80 m n) : term80 m n.
Proof. exact (h1). Qed.
Lemma lem84126 (P : nat -> Prop) : term30 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem84127 (m : nat) : term107 m.
Proof. exact (@lem84126 (term108 m)). Qed.
Lemma lem84128 (m : nat) : (term109 m) = (((term110 m) = (term110 m)) = ((NUMERAL 0) = (NUMERAL 0))).
Proof. exact (eq_refl (term109 m)). Qed.
Lemma lem84129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem84130 (m : nat) : (term111 m) = (term112 m).
Proof. exact (MK_COMB (@lem84129) (@lem84128 m)). Qed.
Lemma lem84131 (m : nat) (p : nat) : (term113 m p) = (((term110 m) = (term26 m p)) = ((NUMERAL 0) = p)).
Proof. exact (eq_refl (term113 m p)). Qed.
Lemma lem84132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem84133 (m : nat) (p : nat) : (term114 m p) = (term115 m p).
Proof. exact (MK_COMB (@lem84132) (@lem84131 m p)). Qed.
Lemma lem84134 (m : nat) (p : nat) : (term116 m p) = (((term110 m) = (term117 m p)) = ((NUMERAL 0) = (S p))).
Proof. exact (eq_refl (term116 m p)). Qed.
Lemma lem84135 (m : nat) (p : nat) : (term118 m p) = (term119 m p).
Proof. exact (MK_COMB (@lem84133 m p) (@lem84134 m p)). Qed.
Lemma lem84136 (m : nat) : (term120 m) = (term121 m).
Proof. exact (fun_ext (fun p : nat => @lem84135 m p)). Qed.
Lemma lem84137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84138 (m : nat) : (term122 m) = (term123 m).
Proof. exact (MK_COMB (@lem84137) (@lem84136 m)). Qed.
Lemma lem84139 (m : nat) : (term124 m) = (term125 m).
Proof. exact (MK_COMB (@lem84130 m) (@lem84138 m)). Qed.
Lemma lem84140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem84141 (m : nat) : (term126 m) = (term127 m).
Proof. exact (MK_COMB (@lem84140) (@lem84139 m)). Qed.
Lemma lem84142 (m : nat) (p : nat) : (term113 m p) = (((term110 m) = (term26 m p)) = ((NUMERAL 0) = p)).
Proof. exact (eq_refl (term113 m p)). Qed.
Lemma lem84143 (m : nat) : (term128 m) = (term108 m).
Proof. exact (fun_ext (fun p : nat => @lem84142 m p)). Qed.
Lemma lem84144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84145 (m : nat) : (term129 m) = (term86 m).
Proof. exact (MK_COMB (@lem84144) (@lem84143 m)). Qed.
Lemma lem84146 (m : nat) : (term107 m) = (term130 m).
Proof. exact (MK_COMB (@lem84141 m) (@lem84145 m)). Qed.
Lemma lem84147 (m : nat) : term130 m.
Proof. exact (EQ_MP (@lem84146 m) (@lem84127 m)). Qed.
Lemma lem84154 (P : nat -> Prop) : term30 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem84155 (m : nat) (n : nat) : term131 m n.
Proof. exact (@lem84154 (term132 m n)). Qed.
Lemma lem84156 (m : nat) (n : nat) : (term133 m n) = (((term117 m n) = (term110 m)) = ((S n) = (NUMERAL 0))).
Proof. exact (eq_refl (term133 m n)). Qed.
Lemma lem84157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem84158 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (MK_COMB (@lem84157) (@lem84156 m n)). Qed.
Lemma lem84159 (m : nat) (n : nat) (p : nat) : (term136 m n p) = (((term117 m n) = (term26 m p)) = ((S n) = p)).
Proof. exact (eq_refl (term136 m n p)). Qed.
Lemma lem84160 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem84161 (m : nat) (n : nat) (p : nat) : (term137 m n p) = (term138 m n p).
Proof. exact (MK_COMB (@lem84160) (@lem84159 m n p)). Qed.
Lemma lem84162 (m : nat) (n : nat) (p : nat) : (term139 m n p) = (((term117 m n) = (term117 m p)) = ((S n) = (S p))).
Proof. exact (eq_refl (term139 m n p)). Qed.
Lemma lem84163 (m : nat) (n : nat) (p : nat) : (term140 m n p) = (term141 m n p).
Proof. exact (MK_COMB (@lem84161 m n p) (@lem84162 m n p)). Qed.
Lemma lem84164 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (fun_ext (fun p : nat => @lem84163 m n p)). Qed.
Lemma lem84165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84166 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (MK_COMB (@lem84165) (@lem84164 m n)). Qed.
Lemma lem84167 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (MK_COMB (@lem84158 m n) (@lem84166 m n)). Qed.
Lemma lem84168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem84169 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (MK_COMB (@lem84168) (@lem84167 m n)). Qed.
Lemma lem84170 (m : nat) (n : nat) (p : nat) : (term136 m n p) = (((term117 m n) = (term26 m p)) = ((S n) = p)).
Proof. exact (eq_refl (term136 m n p)). Qed.
Lemma lem84171 (m : nat) (n : nat) : (term150 m n) = (term132 m n).
Proof. exact (fun_ext (fun p : nat => @lem84170 m n p)). Qed.
Lemma lem84172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84173 (m : nat) (n : nat) : (term151 m n) = (term93 m n).
Proof. exact (MK_COMB (@lem84172) (@lem84171 m n)). Qed.
Lemma lem84174 (m : nat) (n : nat) : (term131 m n) = (term152 m n).
Proof. exact (MK_COMB (@lem84169 m n) (@lem84173 m n)). Qed.
Lemma lem84175 (m : nat) (n : nat) : term152 m n.
Proof. exact (EQ_MP (@lem84174 m n) (@lem84155 m n)). Qed.
Lemma lem84280 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem84281 (x : nat) : (x = x) = True.
Proof. exact (@lem84280 nat x). Qed.
Lemma lem84282 (m : nat) : ((term110 m) = (term110 m)) = True.
Proof. exact (@lem84281 (term110 m)). Qed.
Lemma lem84283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84284 (m : nat) : (term153 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem84283) (@lem84282 m)). Qed.
Lemma lem84286 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem84287 (x : nat) : (x = x) = True.
Proof. exact (@lem84286 nat x). Qed.
Lemma lem84288 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem84287 (NUMERAL 0)). Qed.
Lemma lem84289 (m : nat) : (((term110 m) = (term110 m)) = ((NUMERAL 0) = (NUMERAL 0))) = (True = True).
Proof. exact (MK_COMB (@lem84284 m) (@lem84288)). Qed.
Lemma lem84291 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem84292 : (True = True) = True.
Proof. exact (@lem84291 True). Qed.
Lemma lem84293 (m : nat) : (((term110 m) = (term110 m)) = ((NUMERAL 0) = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem84289 m) (@lem84292)). Qed.
Lemma lem84294 (m : nat) : True = (((term110 m) = (term110 m)) = ((NUMERAL 0) = (NUMERAL 0))).
Proof. exact (SYM (@lem84293 m)). Qed.
Lemma lem84295 (m : nat) : ((term110 m) = (term110 m)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem84294 m) (@lem0)). Qed.
Lemma lem84296 (n : nat) : term14 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem84297 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem84298 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem84297 n) (@lem84296 n)). Qed.
Lemma lem84302 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem84303 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem84302 n h1)). Qed.
Lemma lem84304 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem84305 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem84304 n h1)). Qed.
Lemma lem84306 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem84303 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem84305 n h1)). Qed.
Lemma lem84307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem84308 (n : nat) : (term15 n) = (term154 n).
Proof. exact (MK_COMB (@lem84307) (@lem84306 n)). Qed.
Lemma lem84309 (n : nat) : term154 n.
Proof. exact (EQ_MP (@lem84308 n) (@lem84298 n)). Qed.
Lemma lem84310 (n : nat) : term155 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem84328 : term156.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem84329 : term157.
Proof. exact (proj2 (@lem84328)). Qed.
Lemma lem84330 : term158.
Proof. exact (proj2 (@lem84329)). Qed.
Lemma lem84331 (m : nat) : term159 m.
Proof. exact (@lem84330 m). Qed.
Lemma lem84332 (m : nat) : (term159 m) = (term160 m).
Proof. exact (eq_refl (term159 m)). Qed.
Lemma lem84333 (m : nat) : term160 m.
Proof. exact (EQ_MP (@lem84332 m) (@lem84331 m)). Qed.
Lemma lem84334 (m : nat) (n : nat) : term161 m n.
Proof. exact (@lem84333 m n). Qed.
Lemma lem84335 (m : nat) (n : nat) : (term161 m n) = ((term162 m n) = (term163 m n)).
Proof. exact (eq_refl (term161 m n)). Qed.
Lemma lem84344 : term164.
Proof. exact (proj1 (@lem84328)). Qed.
Lemma lem84345 (m : nat) : term165 m.
Proof. exact (@lem84344 m). Qed.
Lemma lem84346 (m : nat) : (term165 m) = ((term166 m) = m).
Proof. exact (eq_refl (term165 m)). Qed.
Lemma lem84352 : term17.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem84353 : term18.
Proof. exact (proj2 (@lem84352)). Qed.
Lemma lem84354 : term19.
Proof. exact (proj2 (@lem84353)). Qed.
Lemma lem84355 : term20.
Proof. exact (proj2 (@lem84354)). Qed.
Lemma lem84356 : term167.
Proof. exact (proj2 (@lem84355)). Qed.
Lemma lem84357 (m : nat) : term168 m.
Proof. exact (@lem84356 m). Qed.
Lemma lem84358 (m : nat) : (term168 m) = (term169 m).
Proof. exact (eq_refl (term168 m)). Qed.
Lemma lem84359 (m : nat) : term169 m.
Proof. exact (EQ_MP (@lem84358 m) (@lem84357 m)). Qed.
Lemma lem84360 (m : nat) (n : nat) : term170 m n.
Proof. exact (@lem84359 m n). Qed.
Lemma lem84361 (m : nat) (n : nat) : (term170 m n) = ((term171 m n) = (term172 m n)).
Proof. exact (eq_refl (term170 m n)). Qed.
Lemma lem84378 : term173.
Proof. exact (proj1 (@lem84352)). Qed.
Lemma lem84379 (m : nat) : term174 m.
Proof. exact (@lem84378 m). Qed.
Lemma lem84380 (m : nat) : (term174 m) = ((term175 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term174 m)). Qed.
Lemma lem84397 (m : nat) : (term166 m) = m.
Proof. exact (EQ_MP (@lem84346 m) (@lem84345 m)). Qed.
Lemma lem84398 (m : nat) : (term110 m) = (term175 m).
Proof. exact (@lem84397 (term175 m)). Qed.
Lemma lem84400 (m : nat) : (term175 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem84380 m) (@lem84379 m)). Qed.
Lemma lem84401 (m : nat) : (term110 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem84398 m) (@lem84400 m)). Qed.
Lemma lem84402 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem84403 (m : nat) : (term176 m) = term58.
Proof. exact (MK_COMB (@lem84402) (@lem84401 m)). Qed.
Lemma lem84405 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (EQ_MP (@lem84335 m n) (@lem84334 m n)). Qed.
Lemma lem84406 (m : nat) (p : nat) : (term117 m p) = (term177 m p).
Proof. exact (@lem84405 (term171 m p) p). Qed.
Lemma lem84408 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (EQ_MP (@lem84361 m n) (@lem84360 m n)). Qed.
Lemma lem84409 (m : nat) (p : nat) : (term171 m p) = (term172 m p).
Proof. exact (@lem84408 m p). Qed.
Lemma lem84410 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem84411 (m : nat) (p : nat) : (term178 m p) = (term179 m p).
Proof. exact (MK_COMB (@lem84410) (@lem84409 m p)). Qed.
Lemma lem84412 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem84413 (m : nat) (p : nat) : (term180 m p) = (term181 m p).
Proof. exact (MK_COMB (@lem84411 m p) (@lem84412 p)). Qed.
Lemma lem84414 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem84415 (m : nat) (p : nat) : (term177 m p) = (term182 m p).
Proof. exact (MK_COMB (@lem84414) (@lem84413 m p)). Qed.
Lemma lem84416 (m : nat) (p : nat) : (term117 m p) = (term182 m p).
Proof. exact (TRANS (@lem84406 m p) (@lem84415 m p)). Qed.
Lemma lem84417 (m : nat) (p : nat) : ((term110 m) = (term117 m p)) = ((NUMERAL 0) = (term182 m p)).
Proof. exact (MK_COMB (@lem84403 m) (@lem84416 m p)). Qed.
Lemma lem84419 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem84310 n (@lem84309 n)). Qed.
Lemma lem84420 (m : nat) (p : nat) : ((NUMERAL 0) = (term182 m p)) = False.
Proof. exact (@lem84419 (term181 m p)). Qed.
Lemma lem84421 (m : nat) (p : nat) : ((term110 m) = (term117 m p)) = False.
Proof. exact (TRANS (@lem84417 m p) (@lem84420 m p)). Qed.
Lemma lem84422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84423 (m : nat) (p : nat) : (term183 m p) = (@eq Prop False).
Proof. exact (MK_COMB (@lem84422) (@lem84421 m p)). Qed.
Lemma lem84425 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem84310 n (@lem84309 n)). Qed.
Lemma lem84426 (p : nat) : ((NUMERAL 0) = (S p)) = False.
Proof. exact (@lem84425 p). Qed.
Lemma lem84427 (m : nat) (p : nat) : (((term110 m) = (term117 m p)) = ((NUMERAL 0) = (S p))) = (False = False).
Proof. exact (MK_COMB (@lem84423 m p) (@lem84426 p)). Qed.
Lemma lem84429 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem84430 : (False = False) = (~ False).
Proof. exact (@lem84429 False). Qed.
Lemma lem84432 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem84433 : (False = False) = True.
Proof. exact (TRANS (@lem84430) (@lem84432)). Qed.
Lemma lem84434 (m : nat) (p : nat) : (((term110 m) = (term117 m p)) = ((NUMERAL 0) = (S p))) = True.
Proof. exact (TRANS (@lem84427 m p) (@lem84433)). Qed.
Lemma lem84435 (m : nat) (p : nat) : True = (((term110 m) = (term117 m p)) = ((NUMERAL 0) = (S p))).
Proof. exact (SYM (@lem84434 m p)). Qed.
Lemma lem84436 (m : nat) (p : nat) : ((term110 m) = (term117 m p)) = ((NUMERAL 0) = (S p)).
Proof. exact (EQ_MP (@lem84435 m p) (@lem0)). Qed.
Lemma lem84437 (n : nat) : term14 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem84438 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem84439 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem84438 n) (@lem84437 n)). Qed.
Lemma lem84440 (n : nat) : term16 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem84469 : term156.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem84470 : term157.
Proof. exact (proj2 (@lem84469)). Qed.
Lemma lem84471 : term158.
Proof. exact (proj2 (@lem84470)). Qed.
Lemma lem84472 (m : nat) : term159 m.
Proof. exact (@lem84471 m). Qed.
Lemma lem84473 (m : nat) : (term159 m) = (term160 m).
Proof. exact (eq_refl (term159 m)). Qed.
Lemma lem84474 (m : nat) : term160 m.
Proof. exact (EQ_MP (@lem84473 m) (@lem84472 m)). Qed.
Lemma lem84475 (m : nat) (n : nat) : term161 m n.
Proof. exact (@lem84474 m n). Qed.
Lemma lem84476 (m : nat) (n : nat) : (term161 m n) = ((term162 m n) = (term163 m n)).
Proof. exact (eq_refl (term161 m n)). Qed.
Lemma lem84485 : term164.
Proof. exact (proj1 (@lem84469)). Qed.
Lemma lem84486 (m : nat) : term165 m.
Proof. exact (@lem84485 m). Qed.
Lemma lem84487 (m : nat) : (term165 m) = ((term166 m) = m).
Proof. exact (eq_refl (term165 m)). Qed.
Lemma lem84493 : term17.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem84494 : term18.
Proof. exact (proj2 (@lem84493)). Qed.
Lemma lem84495 : term19.
Proof. exact (proj2 (@lem84494)). Qed.
Lemma lem84496 : term20.
Proof. exact (proj2 (@lem84495)). Qed.
Lemma lem84497 : term167.
Proof. exact (proj2 (@lem84496)). Qed.
Lemma lem84498 (m : nat) : term168 m.
Proof. exact (@lem84497 m). Qed.
Lemma lem84499 (m : nat) : (term168 m) = (term169 m).
Proof. exact (eq_refl (term168 m)). Qed.
Lemma lem84500 (m : nat) : term169 m.
Proof. exact (EQ_MP (@lem84499 m) (@lem84498 m)). Qed.
Lemma lem84501 (m : nat) (n : nat) : term170 m n.
Proof. exact (@lem84500 m n). Qed.
Lemma lem84502 (m : nat) (n : nat) : (term170 m n) = ((term171 m n) = (term172 m n)).
Proof. exact (eq_refl (term170 m n)). Qed.
Lemma lem84519 : term173.
Proof. exact (proj1 (@lem84493)). Qed.
Lemma lem84520 (m : nat) : term174 m.
Proof. exact (@lem84519 m). Qed.
Lemma lem84521 (m : nat) : (term174 m) = ((term175 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term174 m)). Qed.
Lemma lem84541 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (EQ_MP (@lem84476 m n) (@lem84475 m n)). Qed.
Lemma lem84542 (m : nat) (n : nat) : (term117 m n) = (term177 m n).
Proof. exact (@lem84541 (term171 m n) n). Qed.
Lemma lem84544 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (EQ_MP (@lem84502 m n) (@lem84501 m n)). Qed.
Lemma lem84545 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem84546 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (MK_COMB (@lem84545) (@lem84544 m n)). Qed.
Lemma lem84547 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem84548 (m : nat) (n : nat) : (term180 m n) = (term181 m n).
Proof. exact (MK_COMB (@lem84546 m n) (@lem84547 n)). Qed.
Lemma lem84549 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem84550 (m : nat) (n : nat) : (term177 m n) = (term182 m n).
Proof. exact (MK_COMB (@lem84549) (@lem84548 m n)). Qed.
Lemma lem84551 (m : nat) (n : nat) : (term117 m n) = (term182 m n).
Proof. exact (TRANS (@lem84542 m n) (@lem84550 m n)). Qed.
Lemma lem84552 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem84553 (m : nat) (n : nat) : (term184 m n) = (term185 m n).
Proof. exact (MK_COMB (@lem84552) (@lem84551 m n)). Qed.
Lemma lem84555 (m : nat) : (term166 m) = m.
Proof. exact (EQ_MP (@lem84487 m) (@lem84486 m)). Qed.
Lemma lem84556 (m : nat) : (term110 m) = (term175 m).
Proof. exact (@lem84555 (term175 m)). Qed.
Lemma lem84558 (m : nat) : (term175 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem84521 m) (@lem84520 m)). Qed.
Lemma lem84559 (m : nat) : (term110 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem84556 m) (@lem84558 m)). Qed.
Lemma lem84560 (m : nat) (n : nat) : ((term117 m n) = (term110 m)) = ((term182 m n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem84553 m n) (@lem84559 m)). Qed.
Lemma lem84562 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem84440 n (@lem84439 n)). Qed.
Lemma lem84563 (m : nat) (n : nat) : ((term182 m n) = (NUMERAL 0)) = False.
Proof. exact (@lem84562 (term181 m n)). Qed.
Lemma lem84564 (n : nat) (m : nat) : ((term117 m n) = (term110 m)) = False.
Proof. exact (TRANS (@lem84560 m n) (@lem84563 m n)). Qed.
Lemma lem84565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84566 (n : nat) (m : nat) : (term186 n m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem84565) (@lem84564 n m)). Qed.
Lemma lem84568 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem84440 n (@lem84439 n)). Qed.
Lemma lem84569 (m : nat) (n : nat) : (((term117 m n) = (term110 m)) = ((S n) = (NUMERAL 0))) = (False = False).
Proof. exact (MK_COMB (@lem84566 n m) (@lem84568 n)). Qed.
Lemma lem84571 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem84572 : (False = False) = (~ False).
Proof. exact (@lem84571 False). Qed.
Lemma lem84574 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem84575 : (False = False) = True.
Proof. exact (TRANS (@lem84572) (@lem84574)). Qed.
Lemma lem84576 (m : nat) (n : nat) : (((term117 m n) = (term110 m)) = ((S n) = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem84569 m n) (@lem84575)). Qed.
Lemma lem84577 (m : nat) (n : nat) : True = (((term117 m n) = (term110 m)) = ((S n) = (NUMERAL 0))).
Proof. exact (SYM (@lem84576 m n)). Qed.
Lemma lem84578 (m : nat) (n : nat) : ((term117 m n) = (term110 m)) = ((S n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem84577 m n) (@lem0)). Qed.
Lemma lem84611 : term156.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem84612 : term157.
Proof. exact (proj2 (@lem84611)). Qed.
Lemma lem84613 : term158.
Proof. exact (proj2 (@lem84612)). Qed.
Lemma lem84614 (m : nat) : term159 m.
Proof. exact (@lem84613 m). Qed.
Lemma lem84615 (m : nat) : (term159 m) = (term160 m).
Proof. exact (eq_refl (term159 m)). Qed.
Lemma lem84616 (m : nat) : term160 m.
Proof. exact (EQ_MP (@lem84615 m) (@lem84614 m)). Qed.
Lemma lem84617 (m : nat) (n : nat) : term161 m n.
Proof. exact (@lem84616 m n). Qed.
Lemma lem84618 (m : nat) (n : nat) : (term161 m n) = ((term162 m n) = (term163 m n)).
Proof. exact (eq_refl (term161 m n)). Qed.
Lemma lem84635 : term17.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem84636 : term18.
Proof. exact (proj2 (@lem84635)). Qed.
Lemma lem84637 : term19.
Proof. exact (proj2 (@lem84636)). Qed.
Lemma lem84638 : term20.
Proof. exact (proj2 (@lem84637)). Qed.
Lemma lem84639 : term167.
Proof. exact (proj2 (@lem84638)). Qed.
Lemma lem84640 (m : nat) : term168 m.
Proof. exact (@lem84639 m). Qed.
Lemma lem84641 (m : nat) : (term168 m) = (term169 m).
Proof. exact (eq_refl (term168 m)). Qed.
Lemma lem84642 (m : nat) : term169 m.
Proof. exact (EQ_MP (@lem84641 m) (@lem84640 m)). Qed.
Lemma lem84643 (m : nat) (n : nat) : term170 m n.
Proof. exact (@lem84642 m n). Qed.
Lemma lem84644 (m : nat) (n : nat) : (term170 m n) = ((term171 m n) = (term172 m n)).
Proof. exact (eq_refl (term170 m n)). Qed.
Lemma lem84683 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (EQ_MP (@lem84618 m n) (@lem84617 m n)). Qed.
Lemma lem84684 (m : nat) (n : nat) : (term117 m n) = (term177 m n).
Proof. exact (@lem84683 (term171 m n) n). Qed.
Lemma lem84686 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (EQ_MP (@lem84644 m n) (@lem84643 m n)). Qed.
Lemma lem84687 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem84688 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (MK_COMB (@lem84687) (@lem84686 m n)). Qed.
Lemma lem84689 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem84690 (m : nat) (n : nat) : (term180 m n) = (term181 m n).
Proof. exact (MK_COMB (@lem84688 m n) (@lem84689 n)). Qed.
Lemma lem84691 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem84692 (m : nat) (n : nat) : (term177 m n) = (term182 m n).
Proof. exact (MK_COMB (@lem84691) (@lem84690 m n)). Qed.
Lemma lem84693 (m : nat) (n : nat) : (term117 m n) = (term182 m n).
Proof. exact (TRANS (@lem84684 m n) (@lem84692 m n)). Qed.
Lemma lem84694 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem84695 (m : nat) (n : nat) : (term184 m n) = (term185 m n).
Proof. exact (MK_COMB (@lem84694) (@lem84693 m n)). Qed.
Lemma lem84697 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (EQ_MP (@lem84618 m n) (@lem84617 m n)). Qed.
Lemma lem84698 (m : nat) (p : nat) : (term117 m p) = (term177 m p).
Proof. exact (@lem84697 (term171 m p) p). Qed.
Lemma lem84700 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (EQ_MP (@lem84644 m n) (@lem84643 m n)). Qed.
Lemma lem84701 (m : nat) (p : nat) : (term171 m p) = (term172 m p).
Proof. exact (@lem84700 m p). Qed.
Lemma lem84702 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem84703 (m : nat) (p : nat) : (term178 m p) = (term179 m p).
Proof. exact (MK_COMB (@lem84702) (@lem84701 m p)). Qed.
Lemma lem84704 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem84705 (m : nat) (p : nat) : (term180 m p) = (term181 m p).
Proof. exact (MK_COMB (@lem84703 m p) (@lem84704 p)). Qed.
Lemma lem84706 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem84707 (m : nat) (p : nat) : (term177 m p) = (term182 m p).
Proof. exact (MK_COMB (@lem84706) (@lem84705 m p)). Qed.
Lemma lem84708 (m : nat) (p : nat) : (term117 m p) = (term182 m p).
Proof. exact (TRANS (@lem84698 m p) (@lem84707 m p)). Qed.
Lemma lem84709 (n : nat) (m : nat) (p : nat) : ((term117 m n) = (term117 m p)) = ((term182 m n) = (term182 m p)).
Proof. exact (MK_COMB (@lem84695 m n) (@lem84708 m p)). Qed.
Lemma lem84712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84713 (n : nat) (m : nat) (p : nat) : (term187 n m p) = (term188 n m p).
Proof. exact (MK_COMB (@lem84712) (@lem84709 n m p)). Qed.
Lemma lem84716 (n : nat) (p : nat) : ((S n) = (S p)) = ((S n) = (S p)).
Proof. exact (eq_refl ((S n) = (S p))). Qed.
Lemma lem84717 (m : nat) (n : nat) (p : nat) : (((term117 m n) = (term117 m p)) = ((S n) = (S p))) = (((term182 m n) = (term182 m p)) = ((S n) = (S p))).
Proof. exact (MK_COMB (@lem84713 n m p) (@lem84716 n p)). Qed.
Lemma lem84720 (m : nat) (n : nat) (p : nat) : (((term182 m n) = (term182 m p)) = ((S n) = (S p))) = (((term117 m n) = (term117 m p)) = ((S n) = (S p))).
Proof. exact (SYM (@lem84717 m n p)). Qed.
Lemma lem84721 (m : nat) : term189 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem84722 (m : nat) : (term189 m) = (term190 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem84723 (m : nat) : term190 m.
Proof. exact (EQ_MP (@lem84722 m) (@lem84721 m)). Qed.
Lemma lem84724 (m : nat) (n : nat) : term191 m n.
Proof. exact (@lem84723 m n). Qed.
Lemma lem84725 (m : nat) (n : nat) : (term191 m n) = (term192 m n).
Proof. exact (eq_refl (term191 m n)). Qed.
Lemma lem84726 (m : nat) (n : nat) : term192 m n.
Proof. exact (EQ_MP (@lem84725 m n) (@lem84724 m n)). Qed.
Lemma lem84727 (m : nat) (n : nat) (p : nat) : term193 m n p.
Proof. exact (@lem84726 m n p). Qed.
Lemma lem84728 (m : nat) (n : nat) (p : nat) : (term193 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term193 m n p)). Qed.
Lemma lem84730 (m : nat) : term194 m.
Proof. exact (@lem83888 m). Qed.
Lemma lem84731 (m : nat) : (term194 m) = (term9 m).
Proof. exact (eq_refl (term194 m)). Qed.
Lemma lem84732 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem84731 m) (@lem84730 m)). Qed.
Lemma lem84733 (m : nat) (n : nat) : term195 m n.
Proof. exact (@lem84732 m n). Qed.
Lemma lem84734 (m : nat) (n : nat) : (term195 m n) = (term5 m n).
Proof. exact (eq_refl (term195 m n)). Qed.
Lemma lem84735 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem84734 m n) (@lem84733 m n)). Qed.
Lemma lem84736 (m : nat) (n : nat) (p : nat) : term196 m n p.
Proof. exact (@lem84735 m n p). Qed.
Lemma lem84737 (m : nat) (n : nat) (p : nat) : (term196 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term196 m n p)). Qed.
Lemma lem84739 (m : nat) : term197 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem84740 (m : nat) : (term197 m) = (term198 m).
Proof. exact (eq_refl (term197 m)). Qed.
Lemma lem84741 (m : nat) : term198 m.
Proof. exact (EQ_MP (@lem84740 m) (@lem84739 m)). Qed.
Lemma lem84742 (m : nat) (n : nat) : term199 m n.
Proof. exact (@lem84741 m n). Qed.
Lemma lem84743 (m : nat) (n : nat) : (term199 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term199 m n)). Qed.
Lemma lem84751 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : term200 m n p.
Proof. exact (@lem84124 m n h1 p). Qed.
Lemma lem84752 (m : nat) (n : nat) (p : nat) : (term200 m n p) = (((term26 m n) = (term26 m p)) = (n = p)).
Proof. exact (eq_refl (term200 m n p)). Qed.
Lemma lem84757 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem84743 m n) (@lem84742 m n)). Qed.
Lemma lem84758 (n : nat) (m : nat) (p : nat) : ((term182 m n) = (term182 m p)) = ((term181 m n) = (term181 m p)).
Proof. exact (@lem84757 (term181 m n) (term181 m p)). Qed.
Lemma lem84764 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem84737 m n p) (@lem84736 m n p)). Qed.
Lemma lem84765 (m : nat) (n : nat) : (term181 m n) = (term201 m n).
Proof. exact (@lem84764 m (Nat.mul m n) n). Qed.
Lemma lem84766 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem84767 (m : nat) (n : nat) : (term202 m n) = (term203 m n).
Proof. exact (MK_COMB (@lem84766) (@lem84765 m n)). Qed.
Lemma lem84769 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem84737 m n p) (@lem84736 m n p)). Qed.
Lemma lem84770 (m : nat) (p : nat) : (term181 m p) = (term201 m p).
Proof. exact (@lem84769 m (Nat.mul m p) p). Qed.
Lemma lem84771 (n : nat) (m : nat) (p : nat) : ((term181 m n) = (term181 m p)) = ((term201 m n) = (term201 m p)).
Proof. exact (MK_COMB (@lem84767 m n) (@lem84770 m p)). Qed.
Lemma lem84773 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem84728 m n p) (@lem84727 m n p)). Qed.
Lemma lem84774 (n : nat) (m : nat) (p : nat) : ((term201 m n) = (term201 m p)) = ((term26 m n) = (term26 m p)).
Proof. exact (@lem84773 m (term26 m n) (term26 m p)). Qed.
Lemma lem84776 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : ((term26 m n) = (term26 m p)) = (n = p).
Proof. exact (EQ_MP (@lem84752 m n p) (@lem84751 p m n h1)). Qed.
Lemma lem84779 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : ((term201 m n) = (term201 m p)) = (n = p).
Proof. exact (TRANS (@lem84774 n m p) (@lem84776 p m n h1)). Qed.
Lemma lem84780 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : ((term181 m n) = (term181 m p)) = (n = p).
Proof. exact (TRANS (@lem84771 n m p) (@lem84779 p m n h1)). Qed.
Lemma lem84781 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : ((term182 m n) = (term182 m p)) = (n = p).
Proof. exact (TRANS (@lem84758 n m p) (@lem84780 p m n h1)). Qed.
Lemma lem84782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84783 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : (term188 n m p) = (term204 n p).
Proof. exact (MK_COMB (@lem84782) (@lem84781 p m n h1)). Qed.
Lemma lem84785 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem84743 m n) (@lem84742 m n)). Qed.
Lemma lem84786 (n : nat) (p : nat) : ((S n) = (S p)) = (n = p).
Proof. exact (@lem84785 n p). Qed.
Lemma lem84789 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : (((term182 m n) = (term182 m p)) = ((S n) = (S p))) = ((n = p) = (n = p)).
Proof. exact (MK_COMB (@lem84783 p m n h1) (@lem84786 n p)). Qed.
Lemma lem84791 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem84792 (x : Prop) : (x = x) = True.
Proof. exact (@lem84791 Prop x). Qed.
Lemma lem84793 (n : nat) (p : nat) : ((n = p) = (n = p)) = True.
Proof. exact (@lem84792 (n = p)). Qed.
Lemma lem84794 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : (((term182 m n) = (term182 m p)) = ((S n) = (S p))) = True.
Proof. exact (TRANS (@lem84789 p m n h1) (@lem84793 n p)). Qed.
Lemma lem84795 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : True = (((term182 m n) = (term182 m p)) = ((S n) = (S p))).
Proof. exact (SYM (@lem84794 p m n h1)). Qed.
Lemma lem84796 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : ((term182 m n) = (term182 m p)) = ((S n) = (S p)).
Proof. exact (EQ_MP (@lem84795 p m n h1) (@lem0)). Qed.
Lemma lem84797 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : ((term117 m n) = (term117 m p)) = ((S n) = (S p)).
Proof. exact (EQ_MP (@lem84720 m n p) (@lem84796 p m n h1)). Qed.
Lemma lem84798 (p : nat) (m : nat) (n : nat) (h1 : term80 m n) : term141 m n p.
Proof. exact (fun h0 : ((term117 m n) = (term26 m p)) = ((S n) = p) => @lem84797 p m n h1). Qed.
Lemma lem84803 (m : nat) (n : nat) (h1 : term80 m n) : term145 m n.
Proof. exact (fun p : nat => @lem84798 p m n h1). Qed.
Lemma lem84804 (m : nat) (n : nat) (h1 : term80 m n) : term147 m n.
Proof. exact (conj (@lem84578 m n) (@lem84803 m n h1)). Qed.
Lemma lem84805 (m : nat) (n : nat) (h1 : term80 m n) : term93 m n.
Proof. exact (@lem84175 m n (@lem84804 m n h1)). Qed.
Lemma lem84806 (m : nat) (p : nat) : term119 m p.
Proof. exact (fun h0 : ((term110 m) = (term26 m p)) = ((NUMERAL 0) = p) => @lem84436 m p). Qed.
Lemma lem84811 (m : nat) : term123 m.
Proof. exact (fun p : nat => @lem84806 m p). Qed.
Lemma lem84812 (m : nat) : term125 m.
Proof. exact (conj (@lem84295 m) (@lem84811 m)). Qed.
Lemma lem84813 (m : nat) : term86 m.
Proof. exact (@lem84147 m (@lem84812 m)). Qed.
Lemma lem84814 (m : nat) (n : nat) : term95 m n.
Proof. exact (fun h0 : term80 m n => @lem84805 m n h0). Qed.
Lemma lem84819 (m : nat) : term99 m.
Proof. exact (fun n : nat => @lem84814 m n). Qed.
Lemma lem84820 (m : nat) : term101 m.
Proof. exact (conj (@lem84813 m) (@lem84819 m)). Qed.
Lemma lem84821 (m : nat) : term83 m.
Proof. exact (@lem84123 m (@lem84820 m)). Qed.
Lemma lem84822 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem84100 m) (@lem84821 m)). Qed.
Lemma lem84823 (m : nat) : term44 m.
Proof. exact (fun h0 : term38 m => @lem84822 m). Qed.
Lemma lem84828 : term48.
Proof. exact (fun m : nat => @lem84823 m). Qed.
Lemma lem84829 : term50.
Proof. exact (conj (@lem84041) (@lem84828)). Qed.
Lemma lem84830 : term55.
Proof. exact (@lem83974 (@lem84829)). Qed.
