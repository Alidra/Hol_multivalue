Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_SUB_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483486_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1511852 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1511853 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1511852 (term4 x)). Qed.
Lemma lem1511854 (x : real) (y : real) : (term5 x y) = ((term6 y x) = (real_neg y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1511855 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1511857 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1511855) (@lem1511854 x y)). Qed.
Lemma lem1511858 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1511857 x y)). Qed.
Lemma lem1511859 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511860 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1511859) (@lem1511858 x)). Qed.
Lemma lem1511861 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1511853 x) (@lem1511860 x)). Qed.
Lemma lem1511862 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1511863 : term12 = term13.
Proof. exact (@lem1511862 term14). Qed.
Lemma lem1511864 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1511865 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1511866 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1511865) (@lem1511864 x)). Qed.
Lemma lem1511867 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1511866 x) (@lem1511861 x)). Qed.
Lemma lem1511868 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1511867 x)). Qed.
Lemma lem1511869 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511870 : term13 = term20.
Proof. exact (MK_COMB (@lem1511869) (@lem1511868)). Qed.
Lemma lem1511872 : term12 = term20.
Proof. exact (TRANS (@lem1511863) (@lem1511870)). Qed.
Lemma lem1511875 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1511876 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1511875 x y)). Qed.
Lemma lem1511877 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511878 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1511877) (@lem1511876 x)). Qed.
Lemma lem1511879 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1511878 x)). Qed.
Lemma lem1511880 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511881 : term20 = term20.
Proof. exact (MK_COMB (@lem1511880) (@lem1511879)). Qed.
Lemma lem1511882 : term12 = term20.
Proof. exact (TRANS (@lem1511872) (@lem1511881)). Qed.
Lemma lem1511883 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (term6 y x) (real_neg y)). Qed.
Lemma lem1511890 (y : real) : (real_neg y) = (term22 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1511891 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1511904 (x : real) (y : real) : (real_sub x y) = (term23 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1511905 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1511906 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1511905) (@lem1511904 x y)). Qed.
Lemma lem1511907 (y : real) (x : real) : (term6 y x) = (term26 y x).
Proof. exact (MK_COMB (@lem1511906 x y) (@lem1511891 x)). Qed.
Lemma lem1511908 (y : real) (x : real) : (term26 y x) = (term27 y x).
Proof. exact (@lem1483519 (term23 x y) x). Qed.
Lemma lem1511912 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483486 x (term22 x) (term22 y)). Qed.
Lemma lem1511913 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483442 term31 x). Qed.
Lemma lem1511915 (m : nat) : (term32 m) = term33.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511916 : term34 = term33.
Proof. exact (@lem1511915 term35). Qed.
Lemma lem1511917 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511918 : term36 = term37.
Proof. exact (MK_COMB (@lem1511917) (@lem1511916)). Qed.
Lemma lem1511919 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1511920 (x : real) : (term30 x) = (term38 x).
Proof. exact (MK_COMB (@lem1511918) (@lem1511919 x)). Qed.
Lemma lem1511921 (x : real) : (term29 x) = (term38 x).
Proof. exact (TRANS (@lem1511913 x) (@lem1511920 x)). Qed.
Lemma lem1511922 (x : real) : (term38 x) = term33.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1511923 (x : real) : (term29 x) = term33.
Proof. exact (TRANS (@lem1511921 x) (@lem1511922 x)). Qed.
Lemma lem1511924 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1511925 (x : real) : (term39 x) = term40.
Proof. exact (MK_COMB (@lem1511924) (@lem1511923 x)). Qed.
Lemma lem1511926 (y : real) : (term22 y) = (term22 y).
Proof. exact (eq_refl (term22 y)). Qed.
Lemma lem1511927 (x : real) (y : real) : (term28 x y) = (term41 y).
Proof. exact (MK_COMB (@lem1511925 x) (@lem1511926 y)). Qed.
Lemma lem1511928 (x : real) (y : real) : (term27 y x) = (term41 y).
Proof. exact (TRANS (@lem1511912 x y) (@lem1511927 x y)). Qed.
Lemma lem1511929 (y : real) : (term41 y) = (term22 y).
Proof. exact (@lem1483448 (term22 y)). Qed.
Lemma lem1511931 (x : real) (y : real) : (term27 y x) = (term22 y).
Proof. exact (TRANS (@lem1511928 x y) (@lem1511929 y)). Qed.
Lemma lem1511932 (x : real) (y : real) : (term26 y x) = (term22 y).
Proof. exact (TRANS (@lem1511908 y x) (@lem1511931 x y)). Qed.
Lemma lem1511933 (x : real) (y : real) : (term6 y x) = (term22 y).
Proof. exact (TRANS (@lem1511907 y x) (@lem1511932 x y)). Qed.
Lemma lem1511934 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1511935 (x : real) (y : real) : (term42 y x) = (term43 y).
Proof. exact (MK_COMB (@lem1511934) (@lem1511933 x y)). Qed.
Lemma lem1511936 (x : real) (y : real) : (term44 x y) = (term45 y).
Proof. exact (MK_COMB (@lem1511935 x y) (@lem1511890 y)). Qed.
Lemma lem1511937 (y : real) : (term45 y) = (term46 y).
Proof. exact (@lem1483519 (term22 y) (term22 y)). Qed.
Lemma lem1511938 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1483476 term31 term31 y). Qed.
Lemma lem1511940 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1511941 : term51 = term52.
Proof. exact (@lem1511940 term35 term35). Qed.
Lemma lem1511942 : (term53 = (BIT1 0)) = (term54 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1511943 : term54 = term35.
Proof. exact (EQ_MP (@lem1511942) (@lem940073)). Qed.
Lemma lem1511944 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1511945 : term52 = term55.
Proof. exact (MK_COMB (@lem1511944) (@lem1511943)). Qed.
Lemma lem1511946 : term51 = term55.
Proof. exact (TRANS (@lem1511941) (@lem1511945)). Qed.
Lemma lem1511947 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511948 : term56 = term57.
Proof. exact (MK_COMB (@lem1511947) (@lem1511946)). Qed.
Lemma lem1511949 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1511950 (y : real) : (term48 y) = (term58 y).
Proof. exact (MK_COMB (@lem1511948) (@lem1511949 y)). Qed.
Lemma lem1511951 (y : real) : (term47 y) = (term58 y).
Proof. exact (TRANS (@lem1511938 y) (@lem1511950 y)). Qed.
Lemma lem1511952 (y : real) : (term58 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1511953 (y : real) : (term47 y) = y.
Proof. exact (TRANS (@lem1511951 y) (@lem1511952 y)). Qed.
Lemma lem1511954 (y : real) : (term59 y) = (term59 y).
Proof. exact (eq_refl (term59 y)). Qed.
Lemma lem1511955 (y : real) : (term46 y) = (term60 y).
Proof. exact (MK_COMB (@lem1511954 y) (@lem1511953 y)). Qed.
Lemma lem1511956 (y : real) : (term60 y) = (term30 y).
Proof. exact (@lem1483440 term31 y). Qed.
Lemma lem1511958 (m : nat) : (term32 m) = term33.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511959 : term34 = term33.
Proof. exact (@lem1511958 term35). Qed.
Lemma lem1511960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511961 : term36 = term37.
Proof. exact (MK_COMB (@lem1511960) (@lem1511959)). Qed.
Lemma lem1511962 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1511963 (y : real) : (term30 y) = (term38 y).
Proof. exact (MK_COMB (@lem1511961) (@lem1511962 y)). Qed.
Lemma lem1511964 (y : real) : (term60 y) = (term38 y).
Proof. exact (TRANS (@lem1511956 y) (@lem1511963 y)). Qed.
Lemma lem1511965 (y : real) : (term38 y) = term33.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1511966 (y : real) : (term60 y) = term33.
Proof. exact (TRANS (@lem1511964 y) (@lem1511965 y)). Qed.
Lemma lem1511967 (y : real) : (term46 y) = term33.
Proof. exact (TRANS (@lem1511955 y) (@lem1511966 y)). Qed.
Lemma lem1511968 (y : real) : (term45 y) = term33.
Proof. exact (TRANS (@lem1511937 y) (@lem1511967 y)). Qed.
Lemma lem1511969 (x : real) (y : real) : (term44 x y) = term33.
Proof. exact (TRANS (@lem1511936 x y) (@lem1511968 y)). Qed.
Lemma lem1511970 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1511971 (x : real) (y : real) : (term61 x y) = term62.
Proof. exact (MK_COMB (@lem1511970) (@lem1511969 x y)). Qed.
Lemma lem1511972 : term62 = term63.
Proof. exact (@lem1483512 term33). Qed.
Lemma lem1511974 (x : nat) : (term64 x) = term33.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1511975 : term63 = term33.
Proof. exact (@lem1511974 term35). Qed.
Lemma lem1511976 : term62 = term33.
Proof. exact (TRANS (@lem1511972) (@lem1511975)). Qed.
Lemma lem1511977 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1511978 (x : real) (y : real) : ((term61 x y) = term62) = ((term61 x y) = term33).
Proof. exact (MK_COMB (@lem1511977 x y) (@lem1511976)). Qed.
Lemma lem1511979 (x : real) (y : real) : (term61 x y) = term33.
Proof. exact (EQ_MP (@lem1511978 x y) (@lem1511971 x y)). Qed.
Lemma lem1511980 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511981 (x : real) (y : real) : (term66 x y) = term67.
Proof. exact (MK_COMB (@lem1511980) (@lem1511979 x y)). Qed.
Lemma lem1511982 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1511983 (x : real) (y : real) : (term68 x y) = term69.
Proof. exact (MK_COMB (@lem1511981 x y) (@lem1511982)). Qed.
Lemma lem1511984 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511985 (x : real) (y : real) : (term70 x y) = term67.
Proof. exact (MK_COMB (@lem1511984) (@lem1511969 x y)). Qed.
Lemma lem1511986 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1511987 (x : real) (y : real) : (term71 x y) = term69.
Proof. exact (MK_COMB (@lem1511985 x y) (@lem1511986)). Qed.
Lemma lem1511988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511989 (x : real) (y : real) : (term72 x y) = term73.
Proof. exact (MK_COMB (@lem1511988) (@lem1511987 x y)). Qed.
Lemma lem1511990 (x : real) (y : real) : (term21 x y) = term74.
Proof. exact (MK_COMB (@lem1511989 x y) (@lem1511983 x y)). Qed.
Lemma lem1511991 (x : real) (y : real) : (term8 x y) = term74.
Proof. exact (TRANS (@lem1511883 x y) (@lem1511990 x y)). Qed.
Lemma lem1511992 (x : real) : (term10 x) = term75.
Proof. exact (fun_ext (fun y : real => @lem1511991 x y)). Qed.
Lemma lem1511993 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511994 (x : real) : (term11 x) = term76.
Proof. exact (MK_COMB (@lem1511993) (@lem1511992 x)). Qed.
Lemma lem1511995 : term19 = term77.
Proof. exact (fun_ext (fun x : real => @lem1511994 x)). Qed.
Lemma lem1511996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511997 : term20 = term78.
Proof. exact (MK_COMB (@lem1511996) (@lem1511995)). Qed.
Lemma lem1511998 : term12 = term78.
Proof. exact (TRANS (@lem1511882) (@lem1511997)). Qed.
Lemma lem1512000 {A : Type'} (t : Prop) : (term79 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1512001 (t : Prop) : (term80 t) = t.
Proof. exact (@lem1512000 real t). Qed.
Lemma lem1512002 : term78 = term76.
Proof. exact (@lem1512001 term76). Qed.
Lemma lem1512004 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1512005 (P : real -> Prop) (Q : real -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem1512004 real P Q). Qed.
Lemma lem1512006 : term85 = term86.
Proof. exact (@lem1512005 term87 term87). Qed.
Lemma lem1512007 (y : real) : (term88 y) = term69.
Proof. exact (eq_refl (term88 y)). Qed.
Lemma lem1512008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512009 (y : real) : (term89 y) = term73.
Proof. exact (MK_COMB (@lem1512008) (@lem1512007 y)). Qed.
Lemma lem1512010 (y : real) : (term88 y) = term69.
Proof. exact (eq_refl (term88 y)). Qed.
Lemma lem1512011 (y : real) : (term90 y) = term74.
Proof. exact (MK_COMB (@lem1512009 y) (@lem1512010 y)). Qed.
Lemma lem1512012 : term91 = term75.
Proof. exact (fun_ext (fun y : real => @lem1512011 y)). Qed.
Lemma lem1512013 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512014 : term85 = term76.
Proof. exact (MK_COMB (@lem1512013) (@lem1512012)). Qed.
Lemma lem1512015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1512016 : term92 = term93.
Proof. exact (MK_COMB (@lem1512015) (@lem1512014)). Qed.
Lemma lem1512017 (y : real) : (term88 y) = term69.
Proof. exact (eq_refl (term88 y)). Qed.
Lemma lem1512018 : term94 = term87.
Proof. exact (fun_ext (fun y : real => @lem1512017 y)). Qed.
Lemma lem1512019 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512020 : term95 = term96.
Proof. exact (MK_COMB (@lem1512019) (@lem1512018)). Qed.
Lemma lem1512021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512022 : term97 = term98.
Proof. exact (MK_COMB (@lem1512021) (@lem1512020)). Qed.
Lemma lem1512023 (y : real) : (term88 y) = term69.
Proof. exact (eq_refl (term88 y)). Qed.
Lemma lem1512024 : term94 = term87.
Proof. exact (fun_ext (fun y : real => @lem1512023 y)). Qed.
Lemma lem1512025 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512026 : term95 = term96.
Proof. exact (MK_COMB (@lem1512025) (@lem1512024)). Qed.
Lemma lem1512027 : term86 = term99.
Proof. exact (MK_COMB (@lem1512022) (@lem1512026)). Qed.
Lemma lem1512028 : (term85 = term86) = (term76 = term99).
Proof. exact (MK_COMB (@lem1512016) (@lem1512027)). Qed.
Lemma lem1512029 : term76 = term99.
Proof. exact (EQ_MP (@lem1512028) (@lem1512006)). Qed.
Lemma lem1512030 : term78 = term99.
Proof. exact (TRANS (@lem1512002) (@lem1512029)). Qed.
Lemma lem1512032 {A : Type'} (t : Prop) : (term79 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1512033 (t : Prop) : (term80 t) = t.
Proof. exact (@lem1512032 real t). Qed.
Lemma lem1512034 : term96 = term69.
Proof. exact (@lem1512033 term69). Qed.
Lemma lem1512035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512036 : term98 = term73.
Proof. exact (MK_COMB (@lem1512035) (@lem1512034)). Qed.
Lemma lem1512038 {A : Type'} (t : Prop) : (term79 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1512039 (t : Prop) : (term80 t) = t.
Proof. exact (@lem1512038 real t). Qed.
Lemma lem1512040 : term96 = term69.
Proof. exact (@lem1512039 term69). Qed.
Lemma lem1512041 : term99 = term74.
Proof. exact (MK_COMB (@lem1512036) (@lem1512040)). Qed.
Lemma lem1512044 : term78 = term74.
Proof. exact (TRANS (@lem1512030) (@lem1512041)). Qed.
Lemma lem1512053 : term12 = term74.
Proof. exact (TRANS (@lem1511998) (@lem1512044)). Qed.
Lemma lem1512063 (h1 : term74) : term74.
Proof. exact (h1). Qed.
Lemma lem1512064 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1512066 (n : nat) (m : nat) : (term100 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1512067 : term69 = term101.
Proof. exact (@lem1512066 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1512068 : term101 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1512069 : term69 = False.
Proof. exact (TRANS (@lem1512067) (@lem1512068)). Qed.
Lemma lem1512070 (h1 : term69) : False.
Proof. exact (EQ_MP (@lem1512069) (@lem1512064 h1)). Qed.
Lemma lem1512071 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1512073 (n : nat) (m : nat) : (term100 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1512074 : term69 = term101.
Proof. exact (@lem1512073 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1512075 : term101 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1512076 : term69 = False.
Proof. exact (TRANS (@lem1512074) (@lem1512075)). Qed.
Lemma lem1512077 (h1 : term69) : False.
Proof. exact (EQ_MP (@lem1512076) (@lem1512071 h1)). Qed.
Lemma lem1512078 (h1 : term74) : False.
Proof. exact (or_elim (@lem1512063 h1) (fun h0 : term69 => @lem1512070 h0) (fun h0 : term69 => @lem1512077 h0)). Qed.
Lemma lem1512080 (h1 : term74) : term74.
Proof. exact (h1). Qed.
Lemma lem1512081 (h1 : term74) : term74 = False.
Proof. exact (prop_ext (fun h2 : term74 => @lem1512078 h1) (fun h2 : False => @lem1512080 h1)). Qed.
Lemma lem1512082 (h1 : term74) : False.
Proof. exact (EQ_MP (@lem1512081 h1) (@lem1512080 h1)). Qed.
Lemma lem1512083 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1512084 (h1 : term12) : term74.
Proof. exact (EQ_MP (@lem1512053) (@lem1512083 h1)). Qed.
Lemma lem1512085 (h1 : term12) : term74 = False.
Proof. exact (prop_ext (fun h2 : term74 => @lem1512082 h2) (fun h2 : False => @lem1512084 h1)). Qed.
Lemma lem1512086 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1512085 h1) (@lem1512084 h1)). Qed.
Lemma lem1512087 : term102.
Proof. exact (fun h0 : term12 => @lem1512086 h0). Qed.
Lemma lem1512088 : term103.
Proof. exact (@lem1386578 term104). Qed.
Lemma lem1512089 : term104.
Proof. exact (@lem1512088 (@lem1512087)). Qed.
