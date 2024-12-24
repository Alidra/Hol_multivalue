Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_ADD2_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483484_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Lemma lem1504877 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1504878 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1504877 (term4 x)). Qed.
Lemma lem1504879 (y : real) (x : real) : (term5 x y) = ((term6 x y) = x).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1504880 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1504882 (y : real) (x : real) : (term7 x y) = (term8 y x).
Proof. exact (MK_COMB (@lem1504880) (@lem1504879 y x)). Qed.
Lemma lem1504883 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1504882 y x)). Qed.
Lemma lem1504884 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504885 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1504884) (@lem1504883 x)). Qed.
Lemma lem1504886 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1504878 x) (@lem1504885 x)). Qed.
Lemma lem1504887 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1504888 : term12 = term13.
Proof. exact (@lem1504887 term14). Qed.
Lemma lem1504889 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1504890 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1504891 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1504890) (@lem1504889 x)). Qed.
Lemma lem1504892 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1504891 x) (@lem1504886 x)). Qed.
Lemma lem1504893 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1504892 x)). Qed.
Lemma lem1504894 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504895 : term13 = term20.
Proof. exact (MK_COMB (@lem1504894) (@lem1504893)). Qed.
Lemma lem1504897 : term12 = term20.
Proof. exact (TRANS (@lem1504888) (@lem1504895)). Qed.
Lemma lem1504900 (y : real) (x : real) : (term8 y x) = (term8 y x).
Proof. exact (eq_refl (term8 y x)). Qed.
Lemma lem1504901 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1504900 y x)). Qed.
Lemma lem1504902 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504903 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1504902) (@lem1504901 x)). Qed.
Lemma lem1504904 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1504903 x)). Qed.
Lemma lem1504905 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504906 : term20 = term20.
Proof. exact (MK_COMB (@lem1504905) (@lem1504904)). Qed.
Lemma lem1504907 : term12 = term20.
Proof. exact (TRANS (@lem1504897) (@lem1504906)). Qed.
Lemma lem1504908 (y : real) (x : real) : (term8 y x) = (term21 y x).
Proof. exact (@lem1483554 (term6 x y) x). Qed.
Lemma lem1504909 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1504922 (x : real) (y : real) : (real_sub x y) = (term22 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1504925 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1504926 (x : real) (y : real) : (term6 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1504925 y) (@lem1504922 x y)). Qed.
Lemma lem1504927 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (@lem1483484 x y (term25 y)). Qed.
Lemma lem1504928 (y : real) : (term26 y) = (term27 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1504930 (m : nat) : (term29 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504931 : term31 = term30.
Proof. exact (@lem1504930 term32). Qed.
Lemma lem1504932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504933 : term33 = term34.
Proof. exact (MK_COMB (@lem1504932) (@lem1504931)). Qed.
Lemma lem1504934 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1504935 (y : real) : (term27 y) = (term35 y).
Proof. exact (MK_COMB (@lem1504933) (@lem1504934 y)). Qed.
Lemma lem1504936 (y : real) : (term26 y) = (term35 y).
Proof. exact (TRANS (@lem1504928 y) (@lem1504935 y)). Qed.
Lemma lem1504937 (y : real) : (term35 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1504938 (y : real) : (term26 y) = term30.
Proof. exact (TRANS (@lem1504936 y) (@lem1504937 y)). Qed.
Lemma lem1504939 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1504940 (y : real) (x : real) : (term24 x y) = (term36 x).
Proof. exact (MK_COMB (@lem1504939 x) (@lem1504938 y)). Qed.
Lemma lem1504941 (y : real) (x : real) : (term23 x y) = (term36 x).
Proof. exact (TRANS (@lem1504927 x y) (@lem1504940 y x)). Qed.
Lemma lem1504942 (x : real) : (term36 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1504943 (y : real) (x : real) : (term23 x y) = x.
Proof. exact (TRANS (@lem1504941 y x) (@lem1504942 x)). Qed.
Lemma lem1504944 (y : real) (x : real) : (term6 x y) = x.
Proof. exact (TRANS (@lem1504926 x y) (@lem1504943 y x)). Qed.
Lemma lem1504945 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1504946 (y : real) (x : real) : (term37 x y) = (real_sub x).
Proof. exact (MK_COMB (@lem1504945) (@lem1504944 y x)). Qed.
Lemma lem1504947 (y : real) (x : real) : (term38 y x) = (real_sub x x).
Proof. exact (MK_COMB (@lem1504946 y x) (@lem1504909 x)). Qed.
Lemma lem1504948 (x : real) : (real_sub x x) = (term26 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1504952 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1504954 (m : nat) : (term29 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1504955 : term31 = term30.
Proof. exact (@lem1504954 term32). Qed.
Lemma lem1504956 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1504957 : term33 = term34.
Proof. exact (MK_COMB (@lem1504956) (@lem1504955)). Qed.
Lemma lem1504958 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1504959 (x : real) : (term27 x) = (term35 x).
Proof. exact (MK_COMB (@lem1504957) (@lem1504958 x)). Qed.
Lemma lem1504960 (x : real) : (term26 x) = (term35 x).
Proof. exact (TRANS (@lem1504952 x) (@lem1504959 x)). Qed.
Lemma lem1504961 (x : real) : (term35 x) = term30.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1504963 (x : real) : (term26 x) = term30.
Proof. exact (TRANS (@lem1504960 x) (@lem1504961 x)). Qed.
Lemma lem1504964 (x : real) : (real_sub x x) = term30.
Proof. exact (TRANS (@lem1504948 x) (@lem1504963 x)). Qed.
Lemma lem1504965 (y : real) (x : real) : (term38 y x) = term30.
Proof. exact (TRANS (@lem1504947 y x) (@lem1504964 x)). Qed.
Lemma lem1504966 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1504967 (y : real) (x : real) : (term39 y x) = term40.
Proof. exact (MK_COMB (@lem1504966) (@lem1504965 y x)). Qed.
Lemma lem1504968 : term40 = term41.
Proof. exact (@lem1483512 term30). Qed.
Lemma lem1504970 (x : nat) : (term42 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1504971 : term41 = term30.
Proof. exact (@lem1504970 term32). Qed.
Lemma lem1504972 : term40 = term30.
Proof. exact (TRANS (@lem1504968) (@lem1504971)). Qed.
Lemma lem1504973 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (eq_refl (term43 y x)). Qed.
Lemma lem1504974 (y : real) (x : real) : ((term39 y x) = term40) = ((term39 y x) = term30).
Proof. exact (MK_COMB (@lem1504973 y x) (@lem1504972)). Qed.
Lemma lem1504975 (y : real) (x : real) : (term39 y x) = term30.
Proof. exact (EQ_MP (@lem1504974 y x) (@lem1504967 y x)). Qed.
Lemma lem1504976 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504977 (y : real) (x : real) : (term44 y x) = term45.
Proof. exact (MK_COMB (@lem1504976) (@lem1504975 y x)). Qed.
Lemma lem1504978 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1504979 (y : real) (x : real) : (term46 y x) = term47.
Proof. exact (MK_COMB (@lem1504977 y x) (@lem1504978)). Qed.
Lemma lem1504980 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1504981 (y : real) (x : real) : (term48 y x) = term45.
Proof. exact (MK_COMB (@lem1504980) (@lem1504965 y x)). Qed.
Lemma lem1504982 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1504983 (y : real) (x : real) : (term49 y x) = term47.
Proof. exact (MK_COMB (@lem1504981 y x) (@lem1504982)). Qed.
Lemma lem1504984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1504985 (y : real) (x : real) : (term50 y x) = term51.
Proof. exact (MK_COMB (@lem1504984) (@lem1504983 y x)). Qed.
Lemma lem1504986 (y : real) (x : real) : (term21 y x) = term52.
Proof. exact (MK_COMB (@lem1504985 y x) (@lem1504979 y x)). Qed.
Lemma lem1504987 (y : real) (x : real) : (term8 y x) = term52.
Proof. exact (TRANS (@lem1504908 y x) (@lem1504986 y x)). Qed.
Lemma lem1504988 (x : real) : (term10 x) = term53.
Proof. exact (fun_ext (fun y : real => @lem1504987 y x)). Qed.
Lemma lem1504989 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504990 (x : real) : (term11 x) = term54.
Proof. exact (MK_COMB (@lem1504989) (@lem1504988 x)). Qed.
Lemma lem1504991 : term19 = term55.
Proof. exact (fun_ext (fun x : real => @lem1504990 x)). Qed.
Lemma lem1504992 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1504993 : term20 = term56.
Proof. exact (MK_COMB (@lem1504992) (@lem1504991)). Qed.
Lemma lem1504994 : term12 = term56.
Proof. exact (TRANS (@lem1504907) (@lem1504993)). Qed.
Lemma lem1504996 {A : Type'} (t : Prop) : (term57 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1504997 (t : Prop) : (term58 t) = t.
Proof. exact (@lem1504996 real t). Qed.
Lemma lem1504998 : term56 = term54.
Proof. exact (@lem1504997 term54). Qed.
Lemma lem1505000 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1505001 (P : real -> Prop) (Q : real -> Prop) : (term61 P Q) = (term62 P Q).
Proof. exact (@lem1505000 real P Q). Qed.
Lemma lem1505002 : term63 = term64.
Proof. exact (@lem1505001 term65 term65). Qed.
Lemma lem1505003 (y : real) : (term66 y) = term47.
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem1505004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505005 (y : real) : (term67 y) = term51.
Proof. exact (MK_COMB (@lem1505004) (@lem1505003 y)). Qed.
Lemma lem1505006 (y : real) : (term66 y) = term47.
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem1505007 (y : real) : (term68 y) = term52.
Proof. exact (MK_COMB (@lem1505005 y) (@lem1505006 y)). Qed.
Lemma lem1505008 : term69 = term53.
Proof. exact (fun_ext (fun y : real => @lem1505007 y)). Qed.
Lemma lem1505009 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505010 : term63 = term54.
Proof. exact (MK_COMB (@lem1505009) (@lem1505008)). Qed.
Lemma lem1505011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1505012 : term70 = term71.
Proof. exact (MK_COMB (@lem1505011) (@lem1505010)). Qed.
Lemma lem1505013 (y : real) : (term66 y) = term47.
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem1505014 : term72 = term65.
Proof. exact (fun_ext (fun y : real => @lem1505013 y)). Qed.
Lemma lem1505015 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505016 : term73 = term74.
Proof. exact (MK_COMB (@lem1505015) (@lem1505014)). Qed.
Lemma lem1505017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505018 : term75 = term76.
Proof. exact (MK_COMB (@lem1505017) (@lem1505016)). Qed.
Lemma lem1505019 (y : real) : (term66 y) = term47.
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem1505020 : term72 = term65.
Proof. exact (fun_ext (fun y : real => @lem1505019 y)). Qed.
Lemma lem1505021 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505022 : term73 = term74.
Proof. exact (MK_COMB (@lem1505021) (@lem1505020)). Qed.
Lemma lem1505023 : term64 = term77.
Proof. exact (MK_COMB (@lem1505018) (@lem1505022)). Qed.
Lemma lem1505024 : (term63 = term64) = (term54 = term77).
Proof. exact (MK_COMB (@lem1505012) (@lem1505023)). Qed.
Lemma lem1505025 : term54 = term77.
Proof. exact (EQ_MP (@lem1505024) (@lem1505002)). Qed.
Lemma lem1505026 : term56 = term77.
Proof. exact (TRANS (@lem1504998) (@lem1505025)). Qed.
Lemma lem1505028 {A : Type'} (t : Prop) : (term57 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1505029 (t : Prop) : (term58 t) = t.
Proof. exact (@lem1505028 real t). Qed.
Lemma lem1505030 : term74 = term47.
Proof. exact (@lem1505029 term47). Qed.
Lemma lem1505031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505032 : term76 = term51.
Proof. exact (MK_COMB (@lem1505031) (@lem1505030)). Qed.
Lemma lem1505034 {A : Type'} (t : Prop) : (term57 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1505035 (t : Prop) : (term58 t) = t.
Proof. exact (@lem1505034 real t). Qed.
Lemma lem1505036 : term74 = term47.
Proof. exact (@lem1505035 term47). Qed.
Lemma lem1505037 : term77 = term52.
Proof. exact (MK_COMB (@lem1505032) (@lem1505036)). Qed.
Lemma lem1505040 : term56 = term52.
Proof. exact (TRANS (@lem1505026) (@lem1505037)). Qed.
Lemma lem1505049 : term12 = term52.
Proof. exact (TRANS (@lem1504994) (@lem1505040)). Qed.
Lemma lem1505059 (h1 : term52) : term52.
Proof. exact (h1). Qed.
Lemma lem1505060 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1505062 (n : nat) (m : nat) : (term78 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505063 : term47 = term79.
Proof. exact (@lem1505062 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1505064 : term79 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1505065 : term47 = False.
Proof. exact (TRANS (@lem1505063) (@lem1505064)). Qed.
Lemma lem1505066 (h1 : term47) : False.
Proof. exact (EQ_MP (@lem1505065) (@lem1505060 h1)). Qed.
Lemma lem1505067 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1505069 (n : nat) (m : nat) : (term78 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505070 : term47 = term79.
Proof. exact (@lem1505069 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1505071 : term79 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1505072 : term47 = False.
Proof. exact (TRANS (@lem1505070) (@lem1505071)). Qed.
Lemma lem1505073 (h1 : term47) : False.
Proof. exact (EQ_MP (@lem1505072) (@lem1505067 h1)). Qed.
Lemma lem1505074 (h1 : term52) : False.
Proof. exact (or_elim (@lem1505059 h1) (fun h0 : term47 => @lem1505066 h0) (fun h0 : term47 => @lem1505073 h0)). Qed.
Lemma lem1505076 (h1 : term52) : term52.
Proof. exact (h1). Qed.
Lemma lem1505077 (h1 : term52) : term52 = False.
Proof. exact (prop_ext (fun h2 : term52 => @lem1505074 h1) (fun h2 : False => @lem1505076 h1)). Qed.
Lemma lem1505078 (h1 : term52) : False.
Proof. exact (EQ_MP (@lem1505077 h1) (@lem1505076 h1)). Qed.
Lemma lem1505079 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1505080 (h1 : term12) : term52.
Proof. exact (EQ_MP (@lem1505049) (@lem1505079 h1)). Qed.
Lemma lem1505081 (h1 : term12) : term52 = False.
Proof. exact (prop_ext (fun h2 : term52 => @lem1505078 h2) (fun h2 : False => @lem1505080 h1)). Qed.
Lemma lem1505082 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1505081 h1) (@lem1505080 h1)). Qed.
Lemma lem1505083 : term80.
Proof. exact (fun h0 : term12 => @lem1505082 h0). Qed.
Lemma lem1505084 : term81.
Proof. exact (@lem1386578 term82). Qed.
Lemma lem1505085 : term82.
Proof. exact (@lem1505084 (@lem1505083)). Qed.
