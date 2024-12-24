Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_MINUS1_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1508948 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1508949 : term2 = term3.
Proof. exact (@lem1508948 term4). Qed.
Lemma lem1508950 (x : real) : (term5 x) = ((real_neg x) = (term6 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1508951 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1508953 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1508951) (@lem1508950 x)). Qed.
Lemma lem1508954 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1508953 x)). Qed.
Lemma lem1508955 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508956 : term3 = term11.
Proof. exact (MK_COMB (@lem1508955) (@lem1508954)). Qed.
Lemma lem1508958 : term2 = term11.
Proof. exact (TRANS (@lem1508949) (@lem1508956)). Qed.
Lemma lem1508961 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1508962 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1508961 x)). Qed.
Lemma lem1508963 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508964 : term11 = term11.
Proof. exact (MK_COMB (@lem1508963) (@lem1508962)). Qed.
Lemma lem1508965 : term2 = term11.
Proof. exact (TRANS (@lem1508958) (@lem1508964)). Qed.
Lemma lem1508966 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483554 (real_neg x) (term6 x)). Qed.
Lemma lem1508973 (x : real) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1508980 (x : real) : (real_neg x) = (term6 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1508981 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1508982 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1508981) (@lem1508980 x)). Qed.
Lemma lem1508983 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1508982 x) (@lem1508973 x)). Qed.
Lemma lem1508984 (x : real) : (term16 x) = (term17 x).
Proof. exact (@lem1483519 (term6 x) (term6 x)). Qed.
Lemma lem1508985 (x : real) : (term18 x) = (term19 x).
Proof. exact (@lem1483476 term20 term20 x). Qed.
Lemma lem1508987 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1508988 : term23 = term24.
Proof. exact (@lem1508987 term25 term25). Qed.
Lemma lem1508989 : (term26 = (BIT1 0)) = (term27 = term25).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1508990 : term27 = term25.
Proof. exact (EQ_MP (@lem1508989) (@lem940073)). Qed.
Lemma lem1508991 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1508992 : term24 = term28.
Proof. exact (MK_COMB (@lem1508991) (@lem1508990)). Qed.
Lemma lem1508993 : term23 = term28.
Proof. exact (TRANS (@lem1508988) (@lem1508992)). Qed.
Lemma lem1508994 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508995 : term29 = term30.
Proof. exact (MK_COMB (@lem1508994) (@lem1508993)). Qed.
Lemma lem1508996 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1508997 (x : real) : (term19 x) = (term31 x).
Proof. exact (MK_COMB (@lem1508995) (@lem1508996 x)). Qed.
Lemma lem1508998 (x : real) : (term18 x) = (term31 x).
Proof. exact (TRANS (@lem1508985 x) (@lem1508997 x)). Qed.
Lemma lem1508999 (x : real) : (term31 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1509000 (x : real) : (term18 x) = x.
Proof. exact (TRANS (@lem1508998 x) (@lem1508999 x)). Qed.
Lemma lem1509001 (x : real) : (term32 x) = (term32 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1509002 (x : real) : (term17 x) = (term33 x).
Proof. exact (MK_COMB (@lem1509001 x) (@lem1509000 x)). Qed.
Lemma lem1509003 (x : real) : (term33 x) = (term34 x).
Proof. exact (@lem1483440 term20 x). Qed.
Lemma lem1509005 (m : nat) : (term35 m) = term36.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1509006 : term37 = term36.
Proof. exact (@lem1509005 term25). Qed.
Lemma lem1509007 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1509008 : term38 = term39.
Proof. exact (MK_COMB (@lem1509007) (@lem1509006)). Qed.
Lemma lem1509009 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1509010 (x : real) : (term34 x) = (term40 x).
Proof. exact (MK_COMB (@lem1509008) (@lem1509009 x)). Qed.
Lemma lem1509011 (x : real) : (term33 x) = (term40 x).
Proof. exact (TRANS (@lem1509003 x) (@lem1509010 x)). Qed.
Lemma lem1509012 (x : real) : (term40 x) = term36.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1509013 (x : real) : (term33 x) = term36.
Proof. exact (TRANS (@lem1509011 x) (@lem1509012 x)). Qed.
Lemma lem1509014 (x : real) : (term17 x) = term36.
Proof. exact (TRANS (@lem1509002 x) (@lem1509013 x)). Qed.
Lemma lem1509015 (x : real) : (term16 x) = term36.
Proof. exact (TRANS (@lem1508984 x) (@lem1509014 x)). Qed.
Lemma lem1509016 (x : real) : (term15 x) = term36.
Proof. exact (TRANS (@lem1508983 x) (@lem1509015 x)). Qed.
Lemma lem1509017 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1509018 (x : real) : (term41 x) = term42.
Proof. exact (MK_COMB (@lem1509017) (@lem1509016 x)). Qed.
Lemma lem1509019 : term42 = term43.
Proof. exact (@lem1483512 term36). Qed.
Lemma lem1509021 (x : nat) : (term44 x) = term36.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1509022 : term43 = term36.
Proof. exact (@lem1509021 term25). Qed.
Lemma lem1509023 : term42 = term36.
Proof. exact (TRANS (@lem1509019) (@lem1509022)). Qed.
Lemma lem1509024 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1509025 (x : real) : ((term41 x) = term42) = ((term41 x) = term36).
Proof. exact (MK_COMB (@lem1509024 x) (@lem1509023)). Qed.
Lemma lem1509026 (x : real) : (term41 x) = term36.
Proof. exact (EQ_MP (@lem1509025 x) (@lem1509018 x)). Qed.
Lemma lem1509027 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509028 (x : real) : (term46 x) = term47.
Proof. exact (MK_COMB (@lem1509027) (@lem1509026 x)). Qed.
Lemma lem1509029 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1509030 (x : real) : (term48 x) = term49.
Proof. exact (MK_COMB (@lem1509028 x) (@lem1509029)). Qed.
Lemma lem1509031 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509032 (x : real) : (term50 x) = term47.
Proof. exact (MK_COMB (@lem1509031) (@lem1509016 x)). Qed.
Lemma lem1509033 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1509034 (x : real) : (term51 x) = term49.
Proof. exact (MK_COMB (@lem1509032 x) (@lem1509033)). Qed.
Lemma lem1509035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509036 (x : real) : (term52 x) = term53.
Proof. exact (MK_COMB (@lem1509035) (@lem1509034 x)). Qed.
Lemma lem1509037 (x : real) : (term12 x) = term54.
Proof. exact (MK_COMB (@lem1509036 x) (@lem1509030 x)). Qed.
Lemma lem1509038 (x : real) : (term8 x) = term54.
Proof. exact (TRANS (@lem1508966 x) (@lem1509037 x)). Qed.
Lemma lem1509039 : term10 = term55.
Proof. exact (fun_ext (fun x : real => @lem1509038 x)). Qed.
Lemma lem1509040 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509041 : term11 = term56.
Proof. exact (MK_COMB (@lem1509040) (@lem1509039)). Qed.
Lemma lem1509042 : term2 = term56.
Proof. exact (TRANS (@lem1508965) (@lem1509041)). Qed.
Lemma lem1509044 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term57 A P Q) = (term58 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1509045 (P : real -> Prop) (Q : real -> Prop) : (term59 P Q) = (term60 P Q).
Proof. exact (@lem1509044 real P Q). Qed.
Lemma lem1509046 : term61 = term62.
Proof. exact (@lem1509045 term63 term63). Qed.
Lemma lem1509047 (x : real) : (term64 x) = term49.
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1509048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509049 (x : real) : (term65 x) = term53.
Proof. exact (MK_COMB (@lem1509048) (@lem1509047 x)). Qed.
Lemma lem1509050 (x : real) : (term64 x) = term49.
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1509051 (x : real) : (term66 x) = term54.
Proof. exact (MK_COMB (@lem1509049 x) (@lem1509050 x)). Qed.
Lemma lem1509052 : term67 = term55.
Proof. exact (fun_ext (fun x : real => @lem1509051 x)). Qed.
Lemma lem1509053 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509054 : term61 = term56.
Proof. exact (MK_COMB (@lem1509053) (@lem1509052)). Qed.
Lemma lem1509055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1509056 : term68 = term69.
Proof. exact (MK_COMB (@lem1509055) (@lem1509054)). Qed.
Lemma lem1509057 (x : real) : (term64 x) = term49.
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1509058 : term70 = term63.
Proof. exact (fun_ext (fun x : real => @lem1509057 x)). Qed.
Lemma lem1509059 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509060 : term71 = term72.
Proof. exact (MK_COMB (@lem1509059) (@lem1509058)). Qed.
Lemma lem1509061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509062 : term73 = term74.
Proof. exact (MK_COMB (@lem1509061) (@lem1509060)). Qed.
Lemma lem1509063 (x : real) : (term64 x) = term49.
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1509064 : term70 = term63.
Proof. exact (fun_ext (fun x : real => @lem1509063 x)). Qed.
Lemma lem1509065 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509066 : term71 = term72.
Proof. exact (MK_COMB (@lem1509065) (@lem1509064)). Qed.
Lemma lem1509067 : term62 = term75.
Proof. exact (MK_COMB (@lem1509062) (@lem1509066)). Qed.
Lemma lem1509068 : (term61 = term62) = (term56 = term75).
Proof. exact (MK_COMB (@lem1509056) (@lem1509067)). Qed.
Lemma lem1509069 : term56 = term75.
Proof. exact (EQ_MP (@lem1509068) (@lem1509046)). Qed.
Lemma lem1509071 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1509072 (t : Prop) : (term77 t) = t.
Proof. exact (@lem1509071 real t). Qed.
Lemma lem1509073 : term72 = term49.
Proof. exact (@lem1509072 term49). Qed.
Lemma lem1509074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509075 : term74 = term53.
Proof. exact (MK_COMB (@lem1509074) (@lem1509073)). Qed.
Lemma lem1509077 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1509078 (t : Prop) : (term77 t) = t.
Proof. exact (@lem1509077 real t). Qed.
Lemma lem1509079 : term72 = term49.
Proof. exact (@lem1509078 term49). Qed.
Lemma lem1509080 : term75 = term54.
Proof. exact (MK_COMB (@lem1509075) (@lem1509079)). Qed.
Lemma lem1509083 : term56 = term54.
Proof. exact (TRANS (@lem1509069) (@lem1509080)). Qed.
Lemma lem1509092 : term2 = term54.
Proof. exact (TRANS (@lem1509042) (@lem1509083)). Qed.
Lemma lem1509102 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1509103 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1509105 (n : nat) (m : nat) : (term78 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509106 : term49 = term79.
Proof. exact (@lem1509105 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1509107 : term79 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1509108 : term49 = False.
Proof. exact (TRANS (@lem1509106) (@lem1509107)). Qed.
Lemma lem1509109 (h1 : term49) : False.
Proof. exact (EQ_MP (@lem1509108) (@lem1509103 h1)). Qed.
Lemma lem1509110 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1509112 (n : nat) (m : nat) : (term78 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509113 : term49 = term79.
Proof. exact (@lem1509112 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1509114 : term79 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1509115 : term49 = False.
Proof. exact (TRANS (@lem1509113) (@lem1509114)). Qed.
Lemma lem1509116 (h1 : term49) : False.
Proof. exact (EQ_MP (@lem1509115) (@lem1509110 h1)). Qed.
Lemma lem1509117 (h1 : term54) : False.
Proof. exact (or_elim (@lem1509102 h1) (fun h0 : term49 => @lem1509109 h0) (fun h0 : term49 => @lem1509116 h0)). Qed.
Lemma lem1509119 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1509120 (h1 : term54) : term54 = False.
Proof. exact (prop_ext (fun h2 : term54 => @lem1509117 h1) (fun h2 : False => @lem1509119 h1)). Qed.
Lemma lem1509121 (h1 : term54) : False.
Proof. exact (EQ_MP (@lem1509120 h1) (@lem1509119 h1)). Qed.
Lemma lem1509122 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1509123 (h1 : term2) : term54.
Proof. exact (EQ_MP (@lem1509092) (@lem1509122 h1)). Qed.
Lemma lem1509124 (h1 : term2) : term54 = False.
Proof. exact (prop_ext (fun h2 : term54 => @lem1509121 h2) (fun h2 : False => @lem1509123 h1)). Qed.
Lemma lem1509125 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1509124 h1) (@lem1509123 h1)). Qed.
Lemma lem1509126 : term80.
Proof. exact (fun h0 : term2 => @lem1509125 h0). Qed.
Lemma lem1509127 : term81.
Proof. exact (@lem1386578 term82). Qed.
Lemma lem1509128 : term82.
Proof. exact (@lem1509127 (@lem1509126)). Qed.
