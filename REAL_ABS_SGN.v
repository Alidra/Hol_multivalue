Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_SGN_term_abbrevs.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482678_spec.
Require Import thm1482702_spec.
Require Import thm1482703_spec.
Require Import thm1482981_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483458_spec.
Require Import thm1483460_spec.
Require Import thm1483462_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1720941 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1720942 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1720951 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1720942 x) (@lem1720941 x)). Qed.
Lemma lem1720952 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1720953 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1720952) (@lem1720951 x)). Qed.
Lemma lem1720954 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1720955 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1720954) (@lem1720953 x)). Qed.
Lemma lem1720957 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1720942 x) (@lem1720941 x)). Qed.
Lemma lem1720958 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1720957 (real_abs x)). Qed.
Lemma lem1720959 (x : real) : ((term2 x) = (term6 x)) = ((term3 x) = (term7 x)).
Proof. exact (MK_COMB (@lem1720955 x) (@lem1720958 x)). Qed.
Lemma lem1720962 : term8 = term9.
Proof. exact (fun_ext (fun x : real => @lem1720959 x)). Qed.
Lemma lem1720963 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1720964 : term10 = term11.
Proof. exact (MK_COMB (@lem1720963) (@lem1720962)). Qed.
Lemma lem1720969 : term11 = term10.
Proof. exact (SYM (@lem1720964)). Qed.
Lemma lem1720978 (P : real -> Prop) : (term12 P) = (term13 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1720979 : term14 = term15.
Proof. exact (@lem1720978 term9). Qed.
Lemma lem1720980 (x : real) : (term16 x) = ((term3 x) = (term7 x)).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1720981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1720983 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1720981) (@lem1720980 x)). Qed.
Lemma lem1720984 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1720983 x)). Qed.
Lemma lem1720985 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1720986 : term15 = term21.
Proof. exact (MK_COMB (@lem1720985) (@lem1720984)). Qed.
Lemma lem1720988 : term14 = term21.
Proof. exact (TRANS (@lem1720979) (@lem1720986)). Qed.
Lemma lem1720992 (x : real) (h1 : (term22 x) = False) : (term22 x) = False.
Proof. exact (h1). Qed.
Lemma lem1720993 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1720994 (x : real) (h1 : (term22 x) = False) : (term23 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1720993) (@lem1720992 x h1)). Qed.
Lemma lem1720995 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1720996 (x : real) (h1 : (term22 x) = False) : (term25 x) = term26.
Proof. exact (MK_COMB (@lem1720994 x h1) (@lem1720995)). Qed.
Lemma lem1720997 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1720998 (x : real) (h1 : (term22 x) = False) : (term1 x) = (term28 x).
Proof. exact (MK_COMB (@lem1720996 x h1) (@lem1720997 x)). Qed.
Lemma lem1721000 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721001 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721000 real t1 t2). Qed.
Lemma lem1721002 (x : real) : (term28 x) = (term27 x).
Proof. exact (@lem1721001 term24 (term27 x)). Qed.
Lemma lem1721003 (x : real) (h1 : (term22 x) = False) : (term1 x) = (term27 x).
Proof. exact (TRANS (@lem1720998 x h1) (@lem1721002 x)). Qed.
Lemma lem1721004 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1721005 (x : real) (h1 : (term22 x) = False) : (term3 x) = (term29 x).
Proof. exact (MK_COMB (@lem1721004) (@lem1721003 x h1)). Qed.
Lemma lem1721006 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1721007 (x : real) (h1 : (term22 x) = False) : (term5 x) = (term30 x).
Proof. exact (MK_COMB (@lem1721006) (@lem1721005 x h1)). Qed.
Lemma lem1721008 (x : real) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1721009 (x : real) (h1 : (term22 x) = False) : ((term3 x) = (term7 x)) = ((term29 x) = (term7 x)).
Proof. exact (MK_COMB (@lem1721007 x h1) (@lem1721008 x)). Qed.
Lemma lem1721012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721013 (x : real) (h1 : (term22 x) = False) : (term18 x) = (term31 x).
Proof. exact (MK_COMB (@lem1721012) (@lem1721009 x h1)). Qed.
Lemma lem1721014 (x : real) : term32 x.
Proof. exact (fun h0 : (term22 x) = False => @lem1721013 x h0). Qed.
Lemma lem1721016 (x : real) (h1 : (term22 x) = True) : (term22 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721017 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721018 (x : real) (h1 : (term22 x) = True) : (term23 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721017) (@lem1721016 x h1)). Qed.
Lemma lem1721019 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1721020 (x : real) (h1 : (term22 x) = True) : (term25 x) = term33.
Proof. exact (MK_COMB (@lem1721018 x h1) (@lem1721019)). Qed.
Lemma lem1721021 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1721022 (x : real) (h1 : (term22 x) = True) : (term1 x) = (term34 x).
Proof. exact (MK_COMB (@lem1721020 x h1) (@lem1721021 x)). Qed.
Lemma lem1721024 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721025 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721024 real t2 t1). Qed.
Lemma lem1721026 (x : real) : (term34 x) = term24.
Proof. exact (@lem1721025 (term27 x) term24). Qed.
Lemma lem1721027 (x : real) (h1 : (term22 x) = True) : (term1 x) = term24.
Proof. exact (TRANS (@lem1721022 x h1) (@lem1721026 x)). Qed.
Lemma lem1721028 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1721029 (x : real) (h1 : (term22 x) = True) : (term3 x) = term35.
Proof. exact (MK_COMB (@lem1721028) (@lem1721027 x h1)). Qed.
Lemma lem1721030 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1721031 (x : real) (h1 : (term22 x) = True) : (term5 x) = term36.
Proof. exact (MK_COMB (@lem1721030) (@lem1721029 x h1)). Qed.
Lemma lem1721032 (x : real) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1721033 (x : real) (h1 : (term22 x) = True) : ((term3 x) = (term7 x)) = (term35 = (term7 x)).
Proof. exact (MK_COMB (@lem1721031 x h1) (@lem1721032 x)). Qed.
Lemma lem1721036 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721037 (x : real) (h1 : (term22 x) = True) : (term18 x) = (term37 x).
Proof. exact (MK_COMB (@lem1721036) (@lem1721033 x h1)). Qed.
Lemma lem1721038 (x : real) : term38 x.
Proof. exact (fun h0 : (term22 x) = True => @lem1721037 x h0). Qed.
Lemma lem1721039 (x : real) : term39 x.
Proof. exact (conj (@lem1721014 x) (@lem1721038 x)). Qed.
Lemma lem1721041 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term40 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1721042 (x : real) : term41 x.
Proof. exact (@lem1721041 (term18 x) (term37 x) (term22 x) (term31 x)). Qed.
Lemma lem1721057 (x : real) : (term18 x) = (term42 x).
Proof. exact (@lem1721042 x (@lem1721039 x)). Qed.
Lemma lem1721061 (x : real) (h1 : (term43 x) = False) : (term43 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721062 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721063 (x : real) (h1 : (term43 x) = False) : (term44 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721062) (@lem1721061 x h1)). Qed.
Lemma lem1721064 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1721065 (x : real) (h1 : (term43 x) = False) : (term45 x) = term26.
Proof. exact (MK_COMB (@lem1721063 x h1) (@lem1721064)). Qed.
Lemma lem1721066 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1721067 (x : real) (h1 : (term43 x) = False) : (term7 x) = (term47 x).
Proof. exact (MK_COMB (@lem1721065 x h1) (@lem1721066 x)). Qed.
Lemma lem1721069 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721070 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721069 real t1 t2). Qed.
Lemma lem1721071 (x : real) : (term47 x) = (term46 x).
Proof. exact (@lem1721070 term24 (term46 x)). Qed.
Lemma lem1721072 (x : real) (h1 : (term43 x) = False) : (term7 x) = (term46 x).
Proof. exact (TRANS (@lem1721067 x h1) (@lem1721071 x)). Qed.
Lemma lem1721073 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1721074 (x : real) (h1 : (term43 x) = False) : (term35 = (term7 x)) = (term35 = (term46 x)).
Proof. exact (MK_COMB (@lem1721073) (@lem1721072 x h1)). Qed.
Lemma lem1721077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721078 (x : real) (h1 : (term43 x) = False) : (term37 x) = (term48 x).
Proof. exact (MK_COMB (@lem1721077) (@lem1721074 x h1)). Qed.
Lemma lem1721079 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1721080 (x : real) (h1 : (term43 x) = False) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem1721079 x) (@lem1721078 x h1)). Qed.
Lemma lem1721083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721084 (x : real) (h1 : (term43 x) = False) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem1721083) (@lem1721080 x h1)). Qed.
Lemma lem1721086 (x : real) (h1 : (term43 x) = False) : (term43 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721087 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721088 (x : real) (h1 : (term43 x) = False) : (term44 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721087) (@lem1721086 x h1)). Qed.
Lemma lem1721089 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1721090 (x : real) (h1 : (term43 x) = False) : (term45 x) = term26.
Proof. exact (MK_COMB (@lem1721088 x h1) (@lem1721089)). Qed.
Lemma lem1721091 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1721092 (x : real) (h1 : (term43 x) = False) : (term7 x) = (term47 x).
Proof. exact (MK_COMB (@lem1721090 x h1) (@lem1721091 x)). Qed.
Lemma lem1721094 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721095 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721094 real t1 t2). Qed.
Lemma lem1721096 (x : real) : (term47 x) = (term46 x).
Proof. exact (@lem1721095 term24 (term46 x)). Qed.
Lemma lem1721097 (x : real) (h1 : (term43 x) = False) : (term7 x) = (term46 x).
Proof. exact (TRANS (@lem1721092 x h1) (@lem1721096 x)). Qed.
Lemma lem1721098 (x : real) : (term30 x) = (term30 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1721099 (x : real) (h1 : (term43 x) = False) : ((term29 x) = (term7 x)) = ((term29 x) = (term46 x)).
Proof. exact (MK_COMB (@lem1721098 x) (@lem1721097 x h1)). Qed.
Lemma lem1721102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721103 (x : real) (h1 : (term43 x) = False) : (term31 x) = (term54 x).
Proof. exact (MK_COMB (@lem1721102) (@lem1721099 x h1)). Qed.
Lemma lem1721104 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721105 (x : real) (h1 : (term43 x) = False) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem1721104 x) (@lem1721103 x h1)). Qed.
Lemma lem1721108 (x : real) (h1 : (term43 x) = False) : (term42 x) = (term58 x).
Proof. exact (MK_COMB (@lem1721084 x h1) (@lem1721105 x h1)). Qed.
Lemma lem1721111 (x : real) : term59 x.
Proof. exact (fun h0 : (term43 x) = False => @lem1721108 x h0). Qed.
Lemma lem1721113 (x : real) (h1 : (term43 x) = True) : (term43 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721114 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721115 (x : real) (h1 : (term43 x) = True) : (term44 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721114) (@lem1721113 x h1)). Qed.
Lemma lem1721116 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1721117 (x : real) (h1 : (term43 x) = True) : (term45 x) = term33.
Proof. exact (MK_COMB (@lem1721115 x h1) (@lem1721116)). Qed.
Lemma lem1721118 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1721119 (x : real) (h1 : (term43 x) = True) : (term7 x) = (term60 x).
Proof. exact (MK_COMB (@lem1721117 x h1) (@lem1721118 x)). Qed.
Lemma lem1721121 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721122 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721121 real t2 t1). Qed.
Lemma lem1721123 (x : real) : (term60 x) = term24.
Proof. exact (@lem1721122 (term46 x) term24). Qed.
Lemma lem1721124 (x : real) (h1 : (term43 x) = True) : (term7 x) = term24.
Proof. exact (TRANS (@lem1721119 x h1) (@lem1721123 x)). Qed.
Lemma lem1721125 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1721126 (x : real) (h1 : (term43 x) = True) : (term35 = (term7 x)) = (term35 = term24).
Proof. exact (MK_COMB (@lem1721125) (@lem1721124 x h1)). Qed.
Lemma lem1721129 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721130 (x : real) (h1 : (term43 x) = True) : (term37 x) = term61.
Proof. exact (MK_COMB (@lem1721129) (@lem1721126 x h1)). Qed.
Lemma lem1721131 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1721132 (x : real) (h1 : (term43 x) = True) : (term50 x) = (term62 x).
Proof. exact (MK_COMB (@lem1721131 x) (@lem1721130 x h1)). Qed.
Lemma lem1721135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721136 (x : real) (h1 : (term43 x) = True) : (term52 x) = (term63 x).
Proof. exact (MK_COMB (@lem1721135) (@lem1721132 x h1)). Qed.
Lemma lem1721138 (x : real) (h1 : (term43 x) = True) : (term43 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721139 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721140 (x : real) (h1 : (term43 x) = True) : (term44 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721139) (@lem1721138 x h1)). Qed.
Lemma lem1721141 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1721142 (x : real) (h1 : (term43 x) = True) : (term45 x) = term33.
Proof. exact (MK_COMB (@lem1721140 x h1) (@lem1721141)). Qed.
Lemma lem1721143 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1721144 (x : real) (h1 : (term43 x) = True) : (term7 x) = (term60 x).
Proof. exact (MK_COMB (@lem1721142 x h1) (@lem1721143 x)). Qed.
Lemma lem1721146 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721147 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721146 real t2 t1). Qed.
Lemma lem1721148 (x : real) : (term60 x) = term24.
Proof. exact (@lem1721147 (term46 x) term24). Qed.
Lemma lem1721149 (x : real) (h1 : (term43 x) = True) : (term7 x) = term24.
Proof. exact (TRANS (@lem1721144 x h1) (@lem1721148 x)). Qed.
Lemma lem1721150 (x : real) : (term30 x) = (term30 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1721151 (x : real) (h1 : (term43 x) = True) : ((term29 x) = (term7 x)) = ((term29 x) = term24).
Proof. exact (MK_COMB (@lem1721150 x) (@lem1721149 x h1)). Qed.
Lemma lem1721154 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721155 (x : real) (h1 : (term43 x) = True) : (term31 x) = (term64 x).
Proof. exact (MK_COMB (@lem1721154) (@lem1721151 x h1)). Qed.
Lemma lem1721156 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721157 (x : real) (h1 : (term43 x) = True) : (term56 x) = (term65 x).
Proof. exact (MK_COMB (@lem1721156 x) (@lem1721155 x h1)). Qed.
Lemma lem1721160 (x : real) (h1 : (term43 x) = True) : (term42 x) = (term66 x).
Proof. exact (MK_COMB (@lem1721136 x h1) (@lem1721157 x h1)). Qed.
Lemma lem1721163 (x : real) : term67 x.
Proof. exact (fun h0 : (term43 x) = True => @lem1721160 x h0). Qed.
Lemma lem1721164 (x : real) : term68 x.
Proof. exact (conj (@lem1721111 x) (@lem1721163 x)). Qed.
Lemma lem1721166 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term40 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1721167 (x : real) : term69 x.
Proof. exact (@lem1721166 (term42 x) (term66 x) (term43 x) (term58 x)). Qed.
Lemma lem1721182 (x : real) : (term42 x) = (term70 x).
Proof. exact (@lem1721167 x (@lem1721164 x)). Qed.
Lemma lem1721190 (x : real) (h1 : (term71 x) = False) : (term71 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721191 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721192 (x : real) (h1 : (term71 x) = False) : (term72 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721191) (@lem1721190 x h1)). Qed.
Lemma lem1721193 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721194 (x : real) (h1 : (term71 x) = False) : (term74 x) = term75.
Proof. exact (MK_COMB (@lem1721192 x h1) (@lem1721193)). Qed.
Lemma lem1721195 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721196 (x : real) (h1 : (term71 x) = False) : (term27 x) = term77.
Proof. exact (MK_COMB (@lem1721194 x h1) (@lem1721195)). Qed.
Lemma lem1721198 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721199 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721198 real t1 t2). Qed.
Lemma lem1721200 : term77 = term76.
Proof. exact (@lem1721199 term73 term76). Qed.
Lemma lem1721201 (x : real) (h1 : (term71 x) = False) : (term27 x) = term76.
Proof. exact (TRANS (@lem1721196 x h1) (@lem1721200)). Qed.
Lemma lem1721202 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1721203 (x : real) (h1 : (term71 x) = False) : (term29 x) = term78.
Proof. exact (MK_COMB (@lem1721202) (@lem1721201 x h1)). Qed.
Lemma lem1721204 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1721205 (x : real) (h1 : (term71 x) = False) : (term30 x) = term79.
Proof. exact (MK_COMB (@lem1721204) (@lem1721203 x h1)). Qed.
Lemma lem1721206 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1721207 (x : real) (h1 : (term71 x) = False) : ((term29 x) = term24) = (term78 = term24).
Proof. exact (MK_COMB (@lem1721205 x h1) (@lem1721206)). Qed.
Lemma lem1721210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721211 (x : real) (h1 : (term71 x) = False) : (term64 x) = term80.
Proof. exact (MK_COMB (@lem1721210) (@lem1721207 x h1)). Qed.
Lemma lem1721212 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721213 (x : real) (h1 : (term71 x) = False) : (term65 x) = (term81 x).
Proof. exact (MK_COMB (@lem1721212 x) (@lem1721211 x h1)). Qed.
Lemma lem1721216 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1721217 (x : real) (h1 : (term71 x) = False) : (term66 x) = (term82 x).
Proof. exact (MK_COMB (@lem1721216 x) (@lem1721213 x h1)). Qed.
Lemma lem1721220 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1721221 (x : real) (h1 : (term71 x) = False) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1721220 x) (@lem1721217 x h1)). Qed.
Lemma lem1721224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721225 (x : real) (h1 : (term71 x) = False) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1721224) (@lem1721221 x h1)). Qed.
Lemma lem1721231 (x : real) (h1 : (term71 x) = False) : (term71 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721232 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721233 (x : real) (h1 : (term71 x) = False) : (term72 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721232) (@lem1721231 x h1)). Qed.
Lemma lem1721234 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721235 (x : real) (h1 : (term71 x) = False) : (term74 x) = term75.
Proof. exact (MK_COMB (@lem1721233 x h1) (@lem1721234)). Qed.
Lemma lem1721236 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721237 (x : real) (h1 : (term71 x) = False) : (term27 x) = term77.
Proof. exact (MK_COMB (@lem1721235 x h1) (@lem1721236)). Qed.
Lemma lem1721239 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721240 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721239 real t1 t2). Qed.
Lemma lem1721241 : term77 = term76.
Proof. exact (@lem1721240 term73 term76). Qed.
Lemma lem1721242 (x : real) (h1 : (term71 x) = False) : (term27 x) = term76.
Proof. exact (TRANS (@lem1721237 x h1) (@lem1721241)). Qed.
Lemma lem1721243 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1721244 (x : real) (h1 : (term71 x) = False) : (term29 x) = term78.
Proof. exact (MK_COMB (@lem1721243) (@lem1721242 x h1)). Qed.
Lemma lem1721245 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1721246 (x : real) (h1 : (term71 x) = False) : (term30 x) = term79.
Proof. exact (MK_COMB (@lem1721245) (@lem1721244 x h1)). Qed.
Lemma lem1721247 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1721248 (x : real) (h1 : (term71 x) = False) : ((term29 x) = (term46 x)) = (term78 = (term46 x)).
Proof. exact (MK_COMB (@lem1721246 x h1) (@lem1721247 x)). Qed.
Lemma lem1721251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721252 (x : real) (h1 : (term71 x) = False) : (term54 x) = (term88 x).
Proof. exact (MK_COMB (@lem1721251) (@lem1721248 x h1)). Qed.
Lemma lem1721253 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721254 (x : real) (h1 : (term71 x) = False) : (term57 x) = (term89 x).
Proof. exact (MK_COMB (@lem1721253 x) (@lem1721252 x h1)). Qed.
Lemma lem1721257 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1721258 (x : real) (h1 : (term71 x) = False) : (term58 x) = (term90 x).
Proof. exact (MK_COMB (@lem1721257 x) (@lem1721254 x h1)). Qed.
Lemma lem1721261 (x : real) : (term91 x) = (term91 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1721262 (x : real) (h1 : (term71 x) = False) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem1721261 x) (@lem1721258 x h1)). Qed.
Lemma lem1721265 (x : real) (h1 : (term71 x) = False) : (term70 x) = (term94 x).
Proof. exact (MK_COMB (@lem1721225 x h1) (@lem1721262 x h1)). Qed.
Lemma lem1721268 (x : real) : term95 x.
Proof. exact (fun h0 : (term71 x) = False => @lem1721265 x h0). Qed.
Lemma lem1721274 (x : real) (h1 : (term71 x) = True) : (term71 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721275 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721276 (x : real) (h1 : (term71 x) = True) : (term72 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721275) (@lem1721274 x h1)). Qed.
Lemma lem1721277 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721278 (x : real) (h1 : (term71 x) = True) : (term74 x) = term96.
Proof. exact (MK_COMB (@lem1721276 x h1) (@lem1721277)). Qed.
Lemma lem1721279 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721280 (x : real) (h1 : (term71 x) = True) : (term27 x) = term97.
Proof. exact (MK_COMB (@lem1721278 x h1) (@lem1721279)). Qed.
Lemma lem1721282 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721283 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721282 real t2 t1). Qed.
Lemma lem1721284 : term97 = term73.
Proof. exact (@lem1721283 term76 term73). Qed.
Lemma lem1721285 (x : real) (h1 : (term71 x) = True) : (term27 x) = term73.
Proof. exact (TRANS (@lem1721280 x h1) (@lem1721284)). Qed.
Lemma lem1721286 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1721287 (x : real) (h1 : (term71 x) = True) : (term29 x) = term98.
Proof. exact (MK_COMB (@lem1721286) (@lem1721285 x h1)). Qed.
Lemma lem1721288 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1721289 (x : real) (h1 : (term71 x) = True) : (term30 x) = term99.
Proof. exact (MK_COMB (@lem1721288) (@lem1721287 x h1)). Qed.
Lemma lem1721290 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1721291 (x : real) (h1 : (term71 x) = True) : ((term29 x) = term24) = (term98 = term24).
Proof. exact (MK_COMB (@lem1721289 x h1) (@lem1721290)). Qed.
Lemma lem1721294 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721295 (x : real) (h1 : (term71 x) = True) : (term64 x) = term100.
Proof. exact (MK_COMB (@lem1721294) (@lem1721291 x h1)). Qed.
Lemma lem1721296 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721297 (x : real) (h1 : (term71 x) = True) : (term65 x) = (term101 x).
Proof. exact (MK_COMB (@lem1721296 x) (@lem1721295 x h1)). Qed.
Lemma lem1721300 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1721301 (x : real) (h1 : (term71 x) = True) : (term66 x) = (term102 x).
Proof. exact (MK_COMB (@lem1721300 x) (@lem1721297 x h1)). Qed.
Lemma lem1721304 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1721305 (x : real) (h1 : (term71 x) = True) : (term84 x) = (term103 x).
Proof. exact (MK_COMB (@lem1721304 x) (@lem1721301 x h1)). Qed.
Lemma lem1721308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721309 (x : real) (h1 : (term71 x) = True) : (term86 x) = (term104 x).
Proof. exact (MK_COMB (@lem1721308) (@lem1721305 x h1)). Qed.
Lemma lem1721315 (x : real) (h1 : (term71 x) = True) : (term71 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721316 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721317 (x : real) (h1 : (term71 x) = True) : (term72 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721316) (@lem1721315 x h1)). Qed.
Lemma lem1721318 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721319 (x : real) (h1 : (term71 x) = True) : (term74 x) = term96.
Proof. exact (MK_COMB (@lem1721317 x h1) (@lem1721318)). Qed.
Lemma lem1721320 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721321 (x : real) (h1 : (term71 x) = True) : (term27 x) = term97.
Proof. exact (MK_COMB (@lem1721319 x h1) (@lem1721320)). Qed.
Lemma lem1721323 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721324 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721323 real t2 t1). Qed.
Lemma lem1721325 : term97 = term73.
Proof. exact (@lem1721324 term76 term73). Qed.
Lemma lem1721326 (x : real) (h1 : (term71 x) = True) : (term27 x) = term73.
Proof. exact (TRANS (@lem1721321 x h1) (@lem1721325)). Qed.
Lemma lem1721327 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1721328 (x : real) (h1 : (term71 x) = True) : (term29 x) = term98.
Proof. exact (MK_COMB (@lem1721327) (@lem1721326 x h1)). Qed.
Lemma lem1721329 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1721330 (x : real) (h1 : (term71 x) = True) : (term30 x) = term99.
Proof. exact (MK_COMB (@lem1721329) (@lem1721328 x h1)). Qed.
Lemma lem1721331 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1721332 (x : real) (h1 : (term71 x) = True) : ((term29 x) = (term46 x)) = (term98 = (term46 x)).
Proof. exact (MK_COMB (@lem1721330 x h1) (@lem1721331 x)). Qed.
Lemma lem1721335 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721336 (x : real) (h1 : (term71 x) = True) : (term54 x) = (term105 x).
Proof. exact (MK_COMB (@lem1721335) (@lem1721332 x h1)). Qed.
Lemma lem1721337 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721338 (x : real) (h1 : (term71 x) = True) : (term57 x) = (term106 x).
Proof. exact (MK_COMB (@lem1721337 x) (@lem1721336 x h1)). Qed.
Lemma lem1721341 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1721342 (x : real) (h1 : (term71 x) = True) : (term58 x) = (term107 x).
Proof. exact (MK_COMB (@lem1721341 x) (@lem1721338 x h1)). Qed.
Lemma lem1721345 (x : real) : (term91 x) = (term91 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1721346 (x : real) (h1 : (term71 x) = True) : (term92 x) = (term108 x).
Proof. exact (MK_COMB (@lem1721345 x) (@lem1721342 x h1)). Qed.
Lemma lem1721349 (x : real) (h1 : (term71 x) = True) : (term70 x) = (term109 x).
Proof. exact (MK_COMB (@lem1721309 x h1) (@lem1721346 x h1)). Qed.
Lemma lem1721352 (x : real) : term110 x.
Proof. exact (fun h0 : (term71 x) = True => @lem1721349 x h0). Qed.
Lemma lem1721353 (x : real) : term111 x.
Proof. exact (conj (@lem1721268 x) (@lem1721352 x)). Qed.
Lemma lem1721355 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term40 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1721356 (x : real) : term112 x.
Proof. exact (@lem1721355 (term70 x) (term109 x) (term71 x) (term94 x)). Qed.
Lemma lem1721371 (x : real) : (term70 x) = (term113 x).
Proof. exact (@lem1721356 x (@lem1721353 x)). Qed.
Lemma lem1721387 (x : real) (h1 : (term114 x) = False) : (term114 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721388 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721389 (x : real) (h1 : (term114 x) = False) : (term115 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721388) (@lem1721387 x h1)). Qed.
Lemma lem1721390 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721391 (x : real) (h1 : (term114 x) = False) : (term116 x) = term75.
Proof. exact (MK_COMB (@lem1721389 x h1) (@lem1721390)). Qed.
Lemma lem1721392 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721393 (x : real) (h1 : (term114 x) = False) : (term46 x) = term77.
Proof. exact (MK_COMB (@lem1721391 x h1) (@lem1721392)). Qed.
Lemma lem1721395 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721396 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721395 real t1 t2). Qed.
Lemma lem1721397 : term77 = term76.
Proof. exact (@lem1721396 term73 term76). Qed.
Lemma lem1721398 (x : real) (h1 : (term114 x) = False) : (term46 x) = term76.
Proof. exact (TRANS (@lem1721393 x h1) (@lem1721397)). Qed.
Lemma lem1721399 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1721400 (x : real) (h1 : (term114 x) = False) : (term35 = (term46 x)) = (term35 = term76).
Proof. exact (MK_COMB (@lem1721399) (@lem1721398 x h1)). Qed.
Lemma lem1721403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721404 (x : real) (h1 : (term114 x) = False) : (term48 x) = term117.
Proof. exact (MK_COMB (@lem1721403) (@lem1721400 x h1)). Qed.
Lemma lem1721405 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1721406 (x : real) (h1 : (term114 x) = False) : (term51 x) = (term118 x).
Proof. exact (MK_COMB (@lem1721405 x) (@lem1721404 x h1)). Qed.
Lemma lem1721409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721410 (x : real) (h1 : (term114 x) = False) : (term53 x) = (term119 x).
Proof. exact (MK_COMB (@lem1721409) (@lem1721406 x h1)). Qed.
Lemma lem1721412 (x : real) (h1 : (term114 x) = False) : (term114 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721413 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721414 (x : real) (h1 : (term114 x) = False) : (term115 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721413) (@lem1721412 x h1)). Qed.
Lemma lem1721415 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721416 (x : real) (h1 : (term114 x) = False) : (term116 x) = term75.
Proof. exact (MK_COMB (@lem1721414 x h1) (@lem1721415)). Qed.
Lemma lem1721417 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721418 (x : real) (h1 : (term114 x) = False) : (term46 x) = term77.
Proof. exact (MK_COMB (@lem1721416 x h1) (@lem1721417)). Qed.
Lemma lem1721420 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721421 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721420 real t1 t2). Qed.
Lemma lem1721422 : term77 = term76.
Proof. exact (@lem1721421 term73 term76). Qed.
Lemma lem1721423 (x : real) (h1 : (term114 x) = False) : (term46 x) = term76.
Proof. exact (TRANS (@lem1721418 x h1) (@lem1721422)). Qed.
Lemma lem1721424 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem1721425 (x : real) (h1 : (term114 x) = False) : (term98 = (term46 x)) = (term98 = term76).
Proof. exact (MK_COMB (@lem1721424) (@lem1721423 x h1)). Qed.
Lemma lem1721428 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721429 (x : real) (h1 : (term114 x) = False) : (term105 x) = term120.
Proof. exact (MK_COMB (@lem1721428) (@lem1721425 x h1)). Qed.
Lemma lem1721430 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721431 (x : real) (h1 : (term114 x) = False) : (term106 x) = (term121 x).
Proof. exact (MK_COMB (@lem1721430 x) (@lem1721429 x h1)). Qed.
Lemma lem1721434 (x : real) (h1 : (term114 x) = False) : (term107 x) = (term122 x).
Proof. exact (MK_COMB (@lem1721410 x h1) (@lem1721431 x h1)). Qed.
Lemma lem1721437 (x : real) : (term91 x) = (term91 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1721438 (x : real) (h1 : (term114 x) = False) : (term108 x) = (term123 x).
Proof. exact (MK_COMB (@lem1721437 x) (@lem1721434 x h1)). Qed.
Lemma lem1721441 (x : real) : (term104 x) = (term104 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1721442 (x : real) (h1 : (term114 x) = False) : (term109 x) = (term124 x).
Proof. exact (MK_COMB (@lem1721441 x) (@lem1721438 x h1)). Qed.
Lemma lem1721445 (x : real) : (term125 x) = (term125 x).
Proof. exact (eq_refl (term125 x)). Qed.
Lemma lem1721446 (x : real) (h1 : (term114 x) = False) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1721445 x) (@lem1721442 x h1)). Qed.
Lemma lem1721449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721450 (x : real) (h1 : (term114 x) = False) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1721449) (@lem1721446 x h1)). Qed.
Lemma lem1721464 (x : real) (h1 : (term114 x) = False) : (term114 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721465 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721466 (x : real) (h1 : (term114 x) = False) : (term115 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721465) (@lem1721464 x h1)). Qed.
Lemma lem1721467 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721468 (x : real) (h1 : (term114 x) = False) : (term116 x) = term75.
Proof. exact (MK_COMB (@lem1721466 x h1) (@lem1721467)). Qed.
Lemma lem1721469 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721470 (x : real) (h1 : (term114 x) = False) : (term46 x) = term77.
Proof. exact (MK_COMB (@lem1721468 x h1) (@lem1721469)). Qed.
Lemma lem1721472 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721473 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721472 real t1 t2). Qed.
Lemma lem1721474 : term77 = term76.
Proof. exact (@lem1721473 term73 term76). Qed.
Lemma lem1721475 (x : real) (h1 : (term114 x) = False) : (term46 x) = term76.
Proof. exact (TRANS (@lem1721470 x h1) (@lem1721474)). Qed.
Lemma lem1721476 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1721477 (x : real) (h1 : (term114 x) = False) : (term35 = (term46 x)) = (term35 = term76).
Proof. exact (MK_COMB (@lem1721476) (@lem1721475 x h1)). Qed.
Lemma lem1721480 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721481 (x : real) (h1 : (term114 x) = False) : (term48 x) = term117.
Proof. exact (MK_COMB (@lem1721480) (@lem1721477 x h1)). Qed.
Lemma lem1721482 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1721483 (x : real) (h1 : (term114 x) = False) : (term51 x) = (term118 x).
Proof. exact (MK_COMB (@lem1721482 x) (@lem1721481 x h1)). Qed.
Lemma lem1721486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721487 (x : real) (h1 : (term114 x) = False) : (term53 x) = (term119 x).
Proof. exact (MK_COMB (@lem1721486) (@lem1721483 x h1)). Qed.
Lemma lem1721489 (x : real) (h1 : (term114 x) = False) : (term114 x) = False.
Proof. exact (h1). Qed.
Lemma lem1721490 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721491 (x : real) (h1 : (term114 x) = False) : (term115 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1721490) (@lem1721489 x h1)). Qed.
Lemma lem1721492 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721493 (x : real) (h1 : (term114 x) = False) : (term116 x) = term75.
Proof. exact (MK_COMB (@lem1721491 x h1) (@lem1721492)). Qed.
Lemma lem1721494 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721495 (x : real) (h1 : (term114 x) = False) : (term46 x) = term77.
Proof. exact (MK_COMB (@lem1721493 x h1) (@lem1721494)). Qed.
Lemma lem1721497 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1721498 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1721497 real t1 t2). Qed.
Lemma lem1721499 : term77 = term76.
Proof. exact (@lem1721498 term73 term76). Qed.
Lemma lem1721500 (x : real) (h1 : (term114 x) = False) : (term46 x) = term76.
Proof. exact (TRANS (@lem1721495 x h1) (@lem1721499)). Qed.
Lemma lem1721501 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem1721502 (x : real) (h1 : (term114 x) = False) : (term78 = (term46 x)) = (term78 = term76).
Proof. exact (MK_COMB (@lem1721501) (@lem1721500 x h1)). Qed.
Lemma lem1721505 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721506 (x : real) (h1 : (term114 x) = False) : (term88 x) = term130.
Proof. exact (MK_COMB (@lem1721505) (@lem1721502 x h1)). Qed.
Lemma lem1721507 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721508 (x : real) (h1 : (term114 x) = False) : (term89 x) = (term131 x).
Proof. exact (MK_COMB (@lem1721507 x) (@lem1721506 x h1)). Qed.
Lemma lem1721511 (x : real) (h1 : (term114 x) = False) : (term90 x) = (term132 x).
Proof. exact (MK_COMB (@lem1721487 x h1) (@lem1721508 x h1)). Qed.
Lemma lem1721514 (x : real) : (term91 x) = (term91 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1721515 (x : real) (h1 : (term114 x) = False) : (term93 x) = (term133 x).
Proof. exact (MK_COMB (@lem1721514 x) (@lem1721511 x h1)). Qed.
Lemma lem1721518 (x : real) : (term87 x) = (term87 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1721519 (x : real) (h1 : (term114 x) = False) : (term94 x) = (term134 x).
Proof. exact (MK_COMB (@lem1721518 x) (@lem1721515 x h1)). Qed.
Lemma lem1721522 (x : real) : (term135 x) = (term135 x).
Proof. exact (eq_refl (term135 x)). Qed.
Lemma lem1721523 (x : real) (h1 : (term114 x) = False) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1721522 x) (@lem1721519 x h1)). Qed.
Lemma lem1721526 (x : real) (h1 : (term114 x) = False) : (term113 x) = (term138 x).
Proof. exact (MK_COMB (@lem1721450 x h1) (@lem1721523 x h1)). Qed.
Lemma lem1721529 (x : real) : term139 x.
Proof. exact (fun h0 : (term114 x) = False => @lem1721526 x h0). Qed.
Lemma lem1721543 (x : real) (h1 : (term114 x) = True) : (term114 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721544 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721545 (x : real) (h1 : (term114 x) = True) : (term115 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721544) (@lem1721543 x h1)). Qed.
Lemma lem1721546 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721547 (x : real) (h1 : (term114 x) = True) : (term116 x) = term96.
Proof. exact (MK_COMB (@lem1721545 x h1) (@lem1721546)). Qed.
Lemma lem1721548 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721549 (x : real) (h1 : (term114 x) = True) : (term46 x) = term97.
Proof. exact (MK_COMB (@lem1721547 x h1) (@lem1721548)). Qed.
Lemma lem1721551 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721552 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721551 real t2 t1). Qed.
Lemma lem1721553 : term97 = term73.
Proof. exact (@lem1721552 term76 term73). Qed.
Lemma lem1721554 (x : real) (h1 : (term114 x) = True) : (term46 x) = term73.
Proof. exact (TRANS (@lem1721549 x h1) (@lem1721553)). Qed.
Lemma lem1721555 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1721556 (x : real) (h1 : (term114 x) = True) : (term35 = (term46 x)) = (term35 = term73).
Proof. exact (MK_COMB (@lem1721555) (@lem1721554 x h1)). Qed.
Lemma lem1721559 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721560 (x : real) (h1 : (term114 x) = True) : (term48 x) = term140.
Proof. exact (MK_COMB (@lem1721559) (@lem1721556 x h1)). Qed.
Lemma lem1721561 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1721562 (x : real) (h1 : (term114 x) = True) : (term51 x) = (term141 x).
Proof. exact (MK_COMB (@lem1721561 x) (@lem1721560 x h1)). Qed.
Lemma lem1721565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721566 (x : real) (h1 : (term114 x) = True) : (term53 x) = (term142 x).
Proof. exact (MK_COMB (@lem1721565) (@lem1721562 x h1)). Qed.
Lemma lem1721568 (x : real) (h1 : (term114 x) = True) : (term114 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721569 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721570 (x : real) (h1 : (term114 x) = True) : (term115 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721569) (@lem1721568 x h1)). Qed.
Lemma lem1721571 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721572 (x : real) (h1 : (term114 x) = True) : (term116 x) = term96.
Proof. exact (MK_COMB (@lem1721570 x h1) (@lem1721571)). Qed.
Lemma lem1721573 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721574 (x : real) (h1 : (term114 x) = True) : (term46 x) = term97.
Proof. exact (MK_COMB (@lem1721572 x h1) (@lem1721573)). Qed.
Lemma lem1721576 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721577 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721576 real t2 t1). Qed.
Lemma lem1721578 : term97 = term73.
Proof. exact (@lem1721577 term76 term73). Qed.
Lemma lem1721579 (x : real) (h1 : (term114 x) = True) : (term46 x) = term73.
Proof. exact (TRANS (@lem1721574 x h1) (@lem1721578)). Qed.
Lemma lem1721580 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem1721581 (x : real) (h1 : (term114 x) = True) : (term98 = (term46 x)) = (term98 = term73).
Proof. exact (MK_COMB (@lem1721580) (@lem1721579 x h1)). Qed.
Lemma lem1721584 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721585 (x : real) (h1 : (term114 x) = True) : (term105 x) = term143.
Proof. exact (MK_COMB (@lem1721584) (@lem1721581 x h1)). Qed.
Lemma lem1721586 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721587 (x : real) (h1 : (term114 x) = True) : (term106 x) = (term144 x).
Proof. exact (MK_COMB (@lem1721586 x) (@lem1721585 x h1)). Qed.
Lemma lem1721590 (x : real) (h1 : (term114 x) = True) : (term107 x) = (term145 x).
Proof. exact (MK_COMB (@lem1721566 x h1) (@lem1721587 x h1)). Qed.
Lemma lem1721593 (x : real) : (term91 x) = (term91 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1721594 (x : real) (h1 : (term114 x) = True) : (term108 x) = (term146 x).
Proof. exact (MK_COMB (@lem1721593 x) (@lem1721590 x h1)). Qed.
Lemma lem1721597 (x : real) : (term104 x) = (term104 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1721598 (x : real) (h1 : (term114 x) = True) : (term109 x) = (term147 x).
Proof. exact (MK_COMB (@lem1721597 x) (@lem1721594 x h1)). Qed.
Lemma lem1721601 (x : real) : (term125 x) = (term125 x).
Proof. exact (eq_refl (term125 x)). Qed.
Lemma lem1721602 (x : real) (h1 : (term114 x) = True) : (term126 x) = (term148 x).
Proof. exact (MK_COMB (@lem1721601 x) (@lem1721598 x h1)). Qed.
Lemma lem1721605 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721606 (x : real) (h1 : (term114 x) = True) : (term128 x) = (term149 x).
Proof. exact (MK_COMB (@lem1721605) (@lem1721602 x h1)). Qed.
Lemma lem1721620 (x : real) (h1 : (term114 x) = True) : (term114 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721621 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721622 (x : real) (h1 : (term114 x) = True) : (term115 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721621) (@lem1721620 x h1)). Qed.
Lemma lem1721623 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721624 (x : real) (h1 : (term114 x) = True) : (term116 x) = term96.
Proof. exact (MK_COMB (@lem1721622 x h1) (@lem1721623)). Qed.
Lemma lem1721625 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721626 (x : real) (h1 : (term114 x) = True) : (term46 x) = term97.
Proof. exact (MK_COMB (@lem1721624 x h1) (@lem1721625)). Qed.
Lemma lem1721628 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721629 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721628 real t2 t1). Qed.
Lemma lem1721630 : term97 = term73.
Proof. exact (@lem1721629 term76 term73). Qed.
Lemma lem1721631 (x : real) (h1 : (term114 x) = True) : (term46 x) = term73.
Proof. exact (TRANS (@lem1721626 x h1) (@lem1721630)). Qed.
Lemma lem1721632 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1721633 (x : real) (h1 : (term114 x) = True) : (term35 = (term46 x)) = (term35 = term73).
Proof. exact (MK_COMB (@lem1721632) (@lem1721631 x h1)). Qed.
Lemma lem1721636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721637 (x : real) (h1 : (term114 x) = True) : (term48 x) = term140.
Proof. exact (MK_COMB (@lem1721636) (@lem1721633 x h1)). Qed.
Lemma lem1721638 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1721639 (x : real) (h1 : (term114 x) = True) : (term51 x) = (term141 x).
Proof. exact (MK_COMB (@lem1721638 x) (@lem1721637 x h1)). Qed.
Lemma lem1721642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1721643 (x : real) (h1 : (term114 x) = True) : (term53 x) = (term142 x).
Proof. exact (MK_COMB (@lem1721642) (@lem1721639 x h1)). Qed.
Lemma lem1721645 (x : real) (h1 : (term114 x) = True) : (term114 x) = True.
Proof. exact (h1). Qed.
Lemma lem1721646 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1721647 (x : real) (h1 : (term114 x) = True) : (term115 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1721646) (@lem1721645 x h1)). Qed.
Lemma lem1721648 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1721649 (x : real) (h1 : (term114 x) = True) : (term116 x) = term96.
Proof. exact (MK_COMB (@lem1721647 x h1) (@lem1721648)). Qed.
Lemma lem1721650 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721651 (x : real) (h1 : (term114 x) = True) : (term46 x) = term97.
Proof. exact (MK_COMB (@lem1721649 x h1) (@lem1721650)). Qed.
Lemma lem1721653 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1721654 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1721653 real t2 t1). Qed.
Lemma lem1721655 : term97 = term73.
Proof. exact (@lem1721654 term76 term73). Qed.
Lemma lem1721656 (x : real) (h1 : (term114 x) = True) : (term46 x) = term73.
Proof. exact (TRANS (@lem1721651 x h1) (@lem1721655)). Qed.
Lemma lem1721657 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem1721658 (x : real) (h1 : (term114 x) = True) : (term78 = (term46 x)) = (term78 = term73).
Proof. exact (MK_COMB (@lem1721657) (@lem1721656 x h1)). Qed.
Lemma lem1721661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1721662 (x : real) (h1 : (term114 x) = True) : (term88 x) = term150.
Proof. exact (MK_COMB (@lem1721661) (@lem1721658 x h1)). Qed.
Lemma lem1721663 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1721664 (x : real) (h1 : (term114 x) = True) : (term89 x) = (term151 x).
Proof. exact (MK_COMB (@lem1721663 x) (@lem1721662 x h1)). Qed.
Lemma lem1721667 (x : real) (h1 : (term114 x) = True) : (term90 x) = (term152 x).
Proof. exact (MK_COMB (@lem1721643 x h1) (@lem1721664 x h1)). Qed.
Lemma lem1721670 (x : real) : (term91 x) = (term91 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1721671 (x : real) (h1 : (term114 x) = True) : (term93 x) = (term153 x).
Proof. exact (MK_COMB (@lem1721670 x) (@lem1721667 x h1)). Qed.
Lemma lem1721674 (x : real) : (term87 x) = (term87 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1721675 (x : real) (h1 : (term114 x) = True) : (term94 x) = (term154 x).
Proof. exact (MK_COMB (@lem1721674 x) (@lem1721671 x h1)). Qed.
Lemma lem1721678 (x : real) : (term135 x) = (term135 x).
Proof. exact (eq_refl (term135 x)). Qed.
Lemma lem1721679 (x : real) (h1 : (term114 x) = True) : (term136 x) = (term155 x).
Proof. exact (MK_COMB (@lem1721678 x) (@lem1721675 x h1)). Qed.
Lemma lem1721682 (x : real) (h1 : (term114 x) = True) : (term113 x) = (term156 x).
Proof. exact (MK_COMB (@lem1721606 x h1) (@lem1721679 x h1)). Qed.
Lemma lem1721685 (x : real) : term157 x.
Proof. exact (fun h0 : (term114 x) = True => @lem1721682 x h0). Qed.
Lemma lem1721686 (x : real) : term158 x.
Proof. exact (conj (@lem1721529 x) (@lem1721685 x)). Qed.
Lemma lem1721688 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term40 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1721689 (x : real) : term159 x.
Proof. exact (@lem1721688 (term113 x) (term156 x) (term114 x) (term138 x)). Qed.
Lemma lem1721950 (x : real) : (term113 x) = (term160 x).
Proof. exact (@lem1721689 x (@lem1721686 x)). Qed.
Lemma lem1721951 (x : real) : (term161 x) = (term161 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1721952 (x : real) : ((term70 x) = (term113 x)) = ((term70 x) = (term160 x)).
Proof. exact (MK_COMB (@lem1721951 x) (@lem1721950 x)). Qed.
Lemma lem1721953 (x : real) : (term70 x) = (term160 x).
Proof. exact (EQ_MP (@lem1721952 x) (@lem1721371 x)). Qed.
Lemma lem1721954 (x : real) : (term162 x) = (term162 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1721955 (x : real) : ((term42 x) = (term70 x)) = ((term42 x) = (term160 x)).
Proof. exact (MK_COMB (@lem1721954 x) (@lem1721953 x)). Qed.
Lemma lem1721956 (x : real) : (term42 x) = (term160 x).
Proof. exact (EQ_MP (@lem1721955 x) (@lem1721182 x)). Qed.
Lemma lem1721957 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1721958 (x : real) : ((term18 x) = (term42 x)) = ((term18 x) = (term160 x)).
Proof. exact (MK_COMB (@lem1721957 x) (@lem1721956 x)). Qed.
Lemma lem1721959 (x : real) : (term18 x) = (term160 x).
Proof. exact (EQ_MP (@lem1721958 x) (@lem1721057 x)). Qed.
Lemma lem1721960 : term20 = term164.
Proof. exact (fun_ext (fun x : real => @lem1721959 x)). Qed.
Lemma lem1721961 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1721962 : term21 = term165.
Proof. exact (MK_COMB (@lem1721961) (@lem1721960)). Qed.
Lemma lem1721963 : term14 = term165.
Proof. exact (TRANS (@lem1720988) (@lem1721962)). Qed.
Lemma lem1721964 (x : real) : (term114 x) = (term166 x).
Proof. exact (@lem1483521 term76 (real_abs x)). Qed.
Lemma lem1721970 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483519 term76 (real_abs x)). Qed.
Lemma lem1721975 (x : real) : (term168 x) = (term169 x).
Proof. exact (@lem1483448 (term169 x)). Qed.
Lemma lem1721977 (x : real) : (term167 x) = (term169 x).
Proof. exact (TRANS (@lem1721970 x) (@lem1721975 x)). Qed.
Lemma lem1721978 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1721979 (x : real) : (term170 x) = (term171 x).
Proof. exact (MK_COMB (@lem1721978) (@lem1721977 x)). Qed.
Lemma lem1721980 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1721981 (x : real) : (term166 x) = (term172 x).
Proof. exact (MK_COMB (@lem1721979 x) (@lem1721980)). Qed.
Lemma lem1721982 (x : real) : (term114 x) = (term172 x).
Proof. exact (TRANS (@lem1721964 x) (@lem1721981 x)). Qed.
Lemma lem1721983 (x : real) : (term71 x) = (term173 x).
Proof. exact (@lem1483521 term76 x). Qed.
Lemma lem1721989 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1721994 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1721996 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1721989 x) (@lem1721994 x)). Qed.
Lemma lem1721997 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1721998 (x : real) : (term177 x) = (term178 x).
Proof. exact (MK_COMB (@lem1721997) (@lem1721996 x)). Qed.
Lemma lem1721999 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722000 (x : real) : (term173 x) = (term179 x).
Proof. exact (MK_COMB (@lem1721998 x) (@lem1721999)). Qed.
Lemma lem1722001 (x : real) : (term71 x) = (term179 x).
Proof. exact (TRANS (@lem1721983 x) (@lem1722000 x)). Qed.
Lemma lem1722002 (x : real) : (term43 x) = (term180 x).
Proof. exact (@lem1483521 (real_abs x) term76). Qed.
Lemma lem1722008 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1483519 (real_abs x) term76). Qed.
Lemma lem1722010 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722011 : term184 = term76.
Proof. exact (@lem1722010 term185). Qed.
Lemma lem1722012 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1722013 (x : real) : (term182 x) = (term187 x).
Proof. exact (MK_COMB (@lem1722012 x) (@lem1722011)). Qed.
Lemma lem1722014 (x : real) : (term187 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1722015 (x : real) : (term182 x) = (real_abs x).
Proof. exact (TRANS (@lem1722013 x) (@lem1722014 x)). Qed.
Lemma lem1722017 (x : real) : (term181 x) = (real_abs x).
Proof. exact (TRANS (@lem1722008 x) (@lem1722015 x)). Qed.
Lemma lem1722018 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722019 (x : real) : (term188 x) = (term189 x).
Proof. exact (MK_COMB (@lem1722018) (@lem1722017 x)). Qed.
Lemma lem1722020 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722021 (x : real) : (term180 x) = (term190 x).
Proof. exact (MK_COMB (@lem1722019 x) (@lem1722020)). Qed.
Lemma lem1722022 (x : real) : (term43 x) = (term190 x).
Proof. exact (TRANS (@lem1722002 x) (@lem1722021 x)). Qed.
Lemma lem1722023 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1722029 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1722031 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722032 : term184 = term76.
Proof. exact (@lem1722031 term185). Qed.
Lemma lem1722033 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1722034 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1722033 x) (@lem1722032)). Qed.
Lemma lem1722035 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1722036 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1722034 x) (@lem1722035 x)). Qed.
Lemma lem1722038 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1722029 x) (@lem1722036 x)). Qed.
Lemma lem1722039 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722040 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1722039) (@lem1722038 x)). Qed.
Lemma lem1722041 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722042 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1722040 x) (@lem1722041)). Qed.
Lemma lem1722043 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1722023 x) (@lem1722042 x)). Qed.
Lemma lem1722044 : term61 = term197.
Proof. exact (@lem1483554 term35 term24). Qed.
Lemma lem1722050 : term198 = term199.
Proof. exact (@lem1483519 term35 term24). Qed.
Lemma lem1722052 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722053 : term202 = term203.
Proof. exact (@lem1722052 term185 term185). Qed.
Lemma lem1722054 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722055 : term205 = term185.
Proof. exact (EQ_MP (@lem1722054) (@lem940073)). Qed.
Lemma lem1722056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722057 : term206 = term24.
Proof. exact (MK_COMB (@lem1722056) (@lem1722055)). Qed.
Lemma lem1722058 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722059 : term203 = term73.
Proof. exact (MK_COMB (@lem1722058) (@lem1722057)). Qed.
Lemma lem1722060 : term202 = term73.
Proof. exact (TRANS (@lem1722053) (@lem1722059)). Qed.
Lemma lem1722061 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1722064 : term199 = term208.
Proof. exact (MK_COMB (@lem1722061) (@lem1722060)). Qed.
Lemma lem1722066 : term198 = term208.
Proof. exact (TRANS (@lem1722050) (@lem1722064)). Qed.
Lemma lem1722067 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722068 : term209 = term210.
Proof. exact (MK_COMB (@lem1722067) (@lem1722066)). Qed.
Lemma lem1722069 : term210 = term211.
Proof. exact (@lem1483512 term208). Qed.
Lemma lem1722070 : term211 = term212.
Proof. exact (@lem1483508 term35 term73 term73). Qed.
Lemma lem1722072 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722073 : term215 = term206.
Proof. exact (@lem1722072 term185 term185). Qed.
Lemma lem1722074 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722075 : term205 = term185.
Proof. exact (EQ_MP (@lem1722074) (@lem940073)). Qed.
Lemma lem1722076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722077 : term206 = term24.
Proof. exact (MK_COMB (@lem1722076) (@lem1722075)). Qed.
Lemma lem1722078 : term215 = term24.
Proof. exact (TRANS (@lem1722073) (@lem1722077)). Qed.
Lemma lem1722081 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1722082 : term212 = term217.
Proof. exact (MK_COMB (@lem1722081) (@lem1722078)). Qed.
Lemma lem1722083 : term211 = term217.
Proof. exact (TRANS (@lem1722070) (@lem1722082)). Qed.
Lemma lem1722084 : term210 = term217.
Proof. exact (TRANS (@lem1722069) (@lem1722083)). Qed.
Lemma lem1722085 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem1722086 : (term209 = term210) = (term209 = term217).
Proof. exact (MK_COMB (@lem1722085) (@lem1722084)). Qed.
Lemma lem1722087 : term209 = term217.
Proof. exact (EQ_MP (@lem1722086) (@lem1722068)). Qed.
Lemma lem1722088 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722089 : term219 = term220.
Proof. exact (MK_COMB (@lem1722088) (@lem1722087)). Qed.
Lemma lem1722090 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722091 : term221 = term222.
Proof. exact (MK_COMB (@lem1722089) (@lem1722090)). Qed.
Lemma lem1722092 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722093 : term223 = term224.
Proof. exact (MK_COMB (@lem1722092) (@lem1722066)). Qed.
Lemma lem1722094 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722095 : term225 = term226.
Proof. exact (MK_COMB (@lem1722093) (@lem1722094)). Qed.
Lemma lem1722096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722097 : term227 = term228.
Proof. exact (MK_COMB (@lem1722096) (@lem1722095)). Qed.
Lemma lem1722098 : term197 = term229.
Proof. exact (MK_COMB (@lem1722097) (@lem1722091)). Qed.
Lemma lem1722099 : term61 = term229.
Proof. exact (TRANS (@lem1722044) (@lem1722098)). Qed.
Lemma lem1722100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722101 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1722100) (@lem1722043 x)). Qed.
Lemma lem1722102 (x : real) : (term62 x) = (term231 x).
Proof. exact (MK_COMB (@lem1722101 x) (@lem1722099)). Qed.
Lemma lem1722103 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1722109 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1722114 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1722116 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1722109 x) (@lem1722114 x)). Qed.
Lemma lem1722117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722118 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1722117) (@lem1722116 x)). Qed.
Lemma lem1722119 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722120 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1722118 x) (@lem1722119)). Qed.
Lemma lem1722121 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1722103 x) (@lem1722120 x)). Qed.
Lemma lem1722122 : term100 = term237.
Proof. exact (@lem1483554 term98 term24). Qed.
Lemma lem1722128 : term238 = term239.
Proof. exact (@lem1483519 term98 term24). Qed.
Lemma lem1722130 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722131 : term202 = term203.
Proof. exact (@lem1722130 term185 term185). Qed.
Lemma lem1722132 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722133 : term205 = term185.
Proof. exact (EQ_MP (@lem1722132) (@lem940073)). Qed.
Lemma lem1722134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722135 : term206 = term24.
Proof. exact (MK_COMB (@lem1722134) (@lem1722133)). Qed.
Lemma lem1722136 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722137 : term203 = term73.
Proof. exact (MK_COMB (@lem1722136) (@lem1722135)). Qed.
Lemma lem1722138 : term202 = term73.
Proof. exact (TRANS (@lem1722131) (@lem1722137)). Qed.
Lemma lem1722139 : term240 = term240.
Proof. exact (eq_refl term240). Qed.
Lemma lem1722142 : term239 = term241.
Proof. exact (MK_COMB (@lem1722139) (@lem1722138)). Qed.
Lemma lem1722144 : term238 = term241.
Proof. exact (TRANS (@lem1722128) (@lem1722142)). Qed.
Lemma lem1722145 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722146 : term242 = term243.
Proof. exact (MK_COMB (@lem1722145) (@lem1722144)). Qed.
Lemma lem1722147 : term243 = term244.
Proof. exact (@lem1483512 term241). Qed.
Lemma lem1722148 : term244 = term245.
Proof. exact (@lem1483508 term98 term73 term73). Qed.
Lemma lem1722150 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722151 : term215 = term206.
Proof. exact (@lem1722150 term185 term185). Qed.
Lemma lem1722152 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722153 : term205 = term185.
Proof. exact (EQ_MP (@lem1722152) (@lem940073)). Qed.
Lemma lem1722154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722155 : term206 = term24.
Proof. exact (MK_COMB (@lem1722154) (@lem1722153)). Qed.
Lemma lem1722156 : term215 = term24.
Proof. exact (TRANS (@lem1722151) (@lem1722155)). Qed.
Lemma lem1722159 : term246 = term246.
Proof. exact (eq_refl term246). Qed.
Lemma lem1722160 : term245 = term247.
Proof. exact (MK_COMB (@lem1722159) (@lem1722156)). Qed.
Lemma lem1722161 : term244 = term247.
Proof. exact (TRANS (@lem1722148) (@lem1722160)). Qed.
Lemma lem1722162 : term243 = term247.
Proof. exact (TRANS (@lem1722147) (@lem1722161)). Qed.
Lemma lem1722163 : term248 = term248.
Proof. exact (eq_refl term248). Qed.
Lemma lem1722164 : (term242 = term243) = (term242 = term247).
Proof. exact (MK_COMB (@lem1722163) (@lem1722162)). Qed.
Lemma lem1722165 : term242 = term247.
Proof. exact (EQ_MP (@lem1722164) (@lem1722146)). Qed.
Lemma lem1722166 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722167 : term249 = term250.
Proof. exact (MK_COMB (@lem1722166) (@lem1722165)). Qed.
Lemma lem1722168 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722169 : term251 = term252.
Proof. exact (MK_COMB (@lem1722167) (@lem1722168)). Qed.
Lemma lem1722170 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722171 : term253 = term254.
Proof. exact (MK_COMB (@lem1722170) (@lem1722144)). Qed.
Lemma lem1722172 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722173 : term255 = term256.
Proof. exact (MK_COMB (@lem1722171) (@lem1722172)). Qed.
Lemma lem1722174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722175 : term257 = term258.
Proof. exact (MK_COMB (@lem1722174) (@lem1722173)). Qed.
Lemma lem1722176 : term237 = term259.
Proof. exact (MK_COMB (@lem1722175) (@lem1722169)). Qed.
Lemma lem1722177 : term100 = term259.
Proof. exact (TRANS (@lem1722122) (@lem1722176)). Qed.
Lemma lem1722178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722179 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1722178) (@lem1722121 x)). Qed.
Lemma lem1722180 (x : real) : (term101 x) = (term261 x).
Proof. exact (MK_COMB (@lem1722179 x) (@lem1722177)). Qed.
Lemma lem1722181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722182 (x : real) : (term63 x) = (term262 x).
Proof. exact (MK_COMB (@lem1722181) (@lem1722102 x)). Qed.
Lemma lem1722183 (x : real) : (term102 x) = (term263 x).
Proof. exact (MK_COMB (@lem1722182 x) (@lem1722180 x)). Qed.
Lemma lem1722184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722185 (x : real) : (term83 x) = (term264 x).
Proof. exact (MK_COMB (@lem1722184) (@lem1722022 x)). Qed.
Lemma lem1722186 (x : real) : (term103 x) = (term265 x).
Proof. exact (MK_COMB (@lem1722185 x) (@lem1722183 x)). Qed.
Lemma lem1722187 (x : real) : (term266 x) = (term267 x).
Proof. exact (@lem1483531 term76 (real_abs x)). Qed.
Lemma lem1722193 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483519 term76 (real_abs x)). Qed.
Lemma lem1722198 (x : real) : (term168 x) = (term169 x).
Proof. exact (@lem1483448 (term169 x)). Qed.
Lemma lem1722200 (x : real) : (term167 x) = (term169 x).
Proof. exact (TRANS (@lem1722193 x) (@lem1722198 x)). Qed.
Lemma lem1722201 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722202 (x : real) : (term268 x) = (term269 x).
Proof. exact (MK_COMB (@lem1722201) (@lem1722200 x)). Qed.
Lemma lem1722203 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722204 (x : real) : (term267 x) = (term270 x).
Proof. exact (MK_COMB (@lem1722202 x) (@lem1722203)). Qed.
Lemma lem1722205 (x : real) : (term266 x) = (term270 x).
Proof. exact (TRANS (@lem1722187 x) (@lem1722204 x)). Qed.
Lemma lem1722206 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1722212 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1722214 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722215 : term184 = term76.
Proof. exact (@lem1722214 term185). Qed.
Lemma lem1722216 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1722217 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1722216 x) (@lem1722215)). Qed.
Lemma lem1722218 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1722219 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1722217 x) (@lem1722218 x)). Qed.
Lemma lem1722221 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1722212 x) (@lem1722219 x)). Qed.
Lemma lem1722222 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722223 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1722222) (@lem1722221 x)). Qed.
Lemma lem1722224 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722225 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1722223 x) (@lem1722224)). Qed.
Lemma lem1722226 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1722206 x) (@lem1722225 x)). Qed.
Lemma lem1722227 : term140 = term271.
Proof. exact (@lem1483554 term35 term73). Qed.
Lemma lem1722233 : term272 = term273.
Proof. exact (@lem1483519 term35 term73). Qed.
Lemma lem1722235 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722236 : term215 = term206.
Proof. exact (@lem1722235 term185 term185). Qed.
Lemma lem1722237 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722238 : term205 = term185.
Proof. exact (EQ_MP (@lem1722237) (@lem940073)). Qed.
Lemma lem1722239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722240 : term206 = term24.
Proof. exact (MK_COMB (@lem1722239) (@lem1722238)). Qed.
Lemma lem1722241 : term215 = term24.
Proof. exact (TRANS (@lem1722236) (@lem1722240)). Qed.
Lemma lem1722242 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1722245 : term273 = term274.
Proof. exact (MK_COMB (@lem1722242) (@lem1722241)). Qed.
Lemma lem1722247 : term272 = term274.
Proof. exact (TRANS (@lem1722233) (@lem1722245)). Qed.
Lemma lem1722248 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722249 : term275 = term276.
Proof. exact (MK_COMB (@lem1722248) (@lem1722247)). Qed.
Lemma lem1722250 : term276 = term277.
Proof. exact (@lem1483512 term274). Qed.
Lemma lem1722251 : term277 = term278.
Proof. exact (@lem1483508 term35 term73 term24). Qed.
Lemma lem1722253 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722254 : term202 = term203.
Proof. exact (@lem1722253 term185 term185). Qed.
Lemma lem1722255 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722256 : term205 = term185.
Proof. exact (EQ_MP (@lem1722255) (@lem940073)). Qed.
Lemma lem1722257 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722258 : term206 = term24.
Proof. exact (MK_COMB (@lem1722257) (@lem1722256)). Qed.
Lemma lem1722259 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722260 : term203 = term73.
Proof. exact (MK_COMB (@lem1722259) (@lem1722258)). Qed.
Lemma lem1722261 : term202 = term73.
Proof. exact (TRANS (@lem1722254) (@lem1722260)). Qed.
Lemma lem1722264 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1722265 : term278 = term279.
Proof. exact (MK_COMB (@lem1722264) (@lem1722261)). Qed.
Lemma lem1722266 : term277 = term279.
Proof. exact (TRANS (@lem1722251) (@lem1722265)). Qed.
Lemma lem1722267 : term276 = term279.
Proof. exact (TRANS (@lem1722250) (@lem1722266)). Qed.
Lemma lem1722268 : term280 = term280.
Proof. exact (eq_refl term280). Qed.
Lemma lem1722269 : (term275 = term276) = (term275 = term279).
Proof. exact (MK_COMB (@lem1722268) (@lem1722267)). Qed.
Lemma lem1722270 : term275 = term279.
Proof. exact (EQ_MP (@lem1722269) (@lem1722249)). Qed.
Lemma lem1722271 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722272 : term281 = term282.
Proof. exact (MK_COMB (@lem1722271) (@lem1722270)). Qed.
Lemma lem1722273 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722274 : term283 = term284.
Proof. exact (MK_COMB (@lem1722272) (@lem1722273)). Qed.
Lemma lem1722275 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722276 : term285 = term286.
Proof. exact (MK_COMB (@lem1722275) (@lem1722247)). Qed.
Lemma lem1722277 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722278 : term287 = term288.
Proof. exact (MK_COMB (@lem1722276) (@lem1722277)). Qed.
Lemma lem1722279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722280 : term289 = term290.
Proof. exact (MK_COMB (@lem1722279) (@lem1722278)). Qed.
Lemma lem1722281 : term271 = term291.
Proof. exact (MK_COMB (@lem1722280) (@lem1722274)). Qed.
Lemma lem1722282 : term140 = term291.
Proof. exact (TRANS (@lem1722227) (@lem1722281)). Qed.
Lemma lem1722283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722284 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1722283) (@lem1722226 x)). Qed.
Lemma lem1722285 (x : real) : (term141 x) = (term292 x).
Proof. exact (MK_COMB (@lem1722284 x) (@lem1722282)). Qed.
Lemma lem1722286 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1722292 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1722297 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1722299 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1722292 x) (@lem1722297 x)). Qed.
Lemma lem1722300 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722301 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1722300) (@lem1722299 x)). Qed.
Lemma lem1722302 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722303 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1722301 x) (@lem1722302)). Qed.
Lemma lem1722304 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1722286 x) (@lem1722303 x)). Qed.
Lemma lem1722305 : term143 = term293.
Proof. exact (@lem1483554 term98 term73). Qed.
Lemma lem1722311 : term294 = term295.
Proof. exact (@lem1483519 term98 term73). Qed.
Lemma lem1722313 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722314 : term215 = term206.
Proof. exact (@lem1722313 term185 term185). Qed.
Lemma lem1722315 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722316 : term205 = term185.
Proof. exact (EQ_MP (@lem1722315) (@lem940073)). Qed.
Lemma lem1722317 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722318 : term206 = term24.
Proof. exact (MK_COMB (@lem1722317) (@lem1722316)). Qed.
Lemma lem1722319 : term215 = term24.
Proof. exact (TRANS (@lem1722314) (@lem1722318)). Qed.
Lemma lem1722320 : term240 = term240.
Proof. exact (eq_refl term240). Qed.
Lemma lem1722323 : term295 = term296.
Proof. exact (MK_COMB (@lem1722320) (@lem1722319)). Qed.
Lemma lem1722325 : term294 = term296.
Proof. exact (TRANS (@lem1722311) (@lem1722323)). Qed.
Lemma lem1722326 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722327 : term297 = term298.
Proof. exact (MK_COMB (@lem1722326) (@lem1722325)). Qed.
Lemma lem1722328 : term298 = term299.
Proof. exact (@lem1483512 term296). Qed.
Lemma lem1722329 : term299 = term300.
Proof. exact (@lem1483508 term98 term73 term24). Qed.
Lemma lem1722331 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722332 : term202 = term203.
Proof. exact (@lem1722331 term185 term185). Qed.
Lemma lem1722333 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722334 : term205 = term185.
Proof. exact (EQ_MP (@lem1722333) (@lem940073)). Qed.
Lemma lem1722335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722336 : term206 = term24.
Proof. exact (MK_COMB (@lem1722335) (@lem1722334)). Qed.
Lemma lem1722337 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722338 : term203 = term73.
Proof. exact (MK_COMB (@lem1722337) (@lem1722336)). Qed.
Lemma lem1722339 : term202 = term73.
Proof. exact (TRANS (@lem1722332) (@lem1722338)). Qed.
Lemma lem1722342 : term246 = term246.
Proof. exact (eq_refl term246). Qed.
Lemma lem1722343 : term300 = term301.
Proof. exact (MK_COMB (@lem1722342) (@lem1722339)). Qed.
Lemma lem1722344 : term299 = term301.
Proof. exact (TRANS (@lem1722329) (@lem1722343)). Qed.
Lemma lem1722345 : term298 = term301.
Proof. exact (TRANS (@lem1722328) (@lem1722344)). Qed.
Lemma lem1722346 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem1722347 : (term297 = term298) = (term297 = term301).
Proof. exact (MK_COMB (@lem1722346) (@lem1722345)). Qed.
Lemma lem1722348 : term297 = term301.
Proof. exact (EQ_MP (@lem1722347) (@lem1722327)). Qed.
Lemma lem1722349 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722350 : term303 = term304.
Proof. exact (MK_COMB (@lem1722349) (@lem1722348)). Qed.
Lemma lem1722351 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722352 : term305 = term306.
Proof. exact (MK_COMB (@lem1722350) (@lem1722351)). Qed.
Lemma lem1722353 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722354 : term307 = term308.
Proof. exact (MK_COMB (@lem1722353) (@lem1722325)). Qed.
Lemma lem1722355 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722356 : term309 = term310.
Proof. exact (MK_COMB (@lem1722354) (@lem1722355)). Qed.
Lemma lem1722357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722358 : term311 = term312.
Proof. exact (MK_COMB (@lem1722357) (@lem1722356)). Qed.
Lemma lem1722359 : term293 = term313.
Proof. exact (MK_COMB (@lem1722358) (@lem1722352)). Qed.
Lemma lem1722360 : term143 = term313.
Proof. exact (TRANS (@lem1722305) (@lem1722359)). Qed.
Lemma lem1722361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722362 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1722361) (@lem1722304 x)). Qed.
Lemma lem1722363 (x : real) : (term144 x) = (term314 x).
Proof. exact (MK_COMB (@lem1722362 x) (@lem1722360)). Qed.
Lemma lem1722364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722365 (x : real) : (term142 x) = (term315 x).
Proof. exact (MK_COMB (@lem1722364) (@lem1722285 x)). Qed.
Lemma lem1722366 (x : real) : (term145 x) = (term316 x).
Proof. exact (MK_COMB (@lem1722365 x) (@lem1722363 x)). Qed.
Lemma lem1722367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722368 (x : real) : (term91 x) = (term317 x).
Proof. exact (MK_COMB (@lem1722367) (@lem1722205 x)). Qed.
Lemma lem1722369 (x : real) : (term146 x) = (term318 x).
Proof. exact (MK_COMB (@lem1722368 x) (@lem1722366 x)). Qed.
Lemma lem1722370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722371 (x : real) : (term104 x) = (term319 x).
Proof. exact (MK_COMB (@lem1722370) (@lem1722186 x)). Qed.
Lemma lem1722372 (x : real) : (term147 x) = (term320 x).
Proof. exact (MK_COMB (@lem1722371 x) (@lem1722369 x)). Qed.
Lemma lem1722373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722374 (x : real) : (term125 x) = (term321 x).
Proof. exact (MK_COMB (@lem1722373) (@lem1722001 x)). Qed.
Lemma lem1722375 (x : real) : (term148 x) = (term322 x).
Proof. exact (MK_COMB (@lem1722374 x) (@lem1722372 x)). Qed.
Lemma lem1722376 (x : real) : (term323 x) = (term324 x).
Proof. exact (@lem1483531 x term76). Qed.
Lemma lem1722382 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1722384 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722385 : term184 = term76.
Proof. exact (@lem1722384 term185). Qed.
Lemma lem1722386 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1722387 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1722386 x) (@lem1722385)). Qed.
Lemma lem1722388 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1722389 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1722387 x) (@lem1722388 x)). Qed.
Lemma lem1722391 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1722382 x) (@lem1722389 x)). Qed.
Lemma lem1722392 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722393 (x : real) : (term325 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1722392) (@lem1722391 x)). Qed.
Lemma lem1722394 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722395 (x : real) : (term324 x) = (term326 x).
Proof. exact (MK_COMB (@lem1722393 x) (@lem1722394)). Qed.
Lemma lem1722396 (x : real) : (term323 x) = (term326 x).
Proof. exact (TRANS (@lem1722376 x) (@lem1722395 x)). Qed.
Lemma lem1722397 (x : real) : (term43 x) = (term180 x).
Proof. exact (@lem1483521 (real_abs x) term76). Qed.
Lemma lem1722403 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1483519 (real_abs x) term76). Qed.
Lemma lem1722405 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722406 : term184 = term76.
Proof. exact (@lem1722405 term185). Qed.
Lemma lem1722407 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1722408 (x : real) : (term182 x) = (term187 x).
Proof. exact (MK_COMB (@lem1722407 x) (@lem1722406)). Qed.
Lemma lem1722409 (x : real) : (term187 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1722410 (x : real) : (term182 x) = (real_abs x).
Proof. exact (TRANS (@lem1722408 x) (@lem1722409 x)). Qed.
Lemma lem1722412 (x : real) : (term181 x) = (real_abs x).
Proof. exact (TRANS (@lem1722403 x) (@lem1722410 x)). Qed.
Lemma lem1722413 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722414 (x : real) : (term188 x) = (term189 x).
Proof. exact (MK_COMB (@lem1722413) (@lem1722412 x)). Qed.
Lemma lem1722415 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722416 (x : real) : (term180 x) = (term190 x).
Proof. exact (MK_COMB (@lem1722414 x) (@lem1722415)). Qed.
Lemma lem1722417 (x : real) : (term43 x) = (term190 x).
Proof. exact (TRANS (@lem1722397 x) (@lem1722416 x)). Qed.
Lemma lem1722418 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1722424 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1722426 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722427 : term184 = term76.
Proof. exact (@lem1722426 term185). Qed.
Lemma lem1722428 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1722429 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1722428 x) (@lem1722427)). Qed.
Lemma lem1722430 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1722431 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1722429 x) (@lem1722430 x)). Qed.
Lemma lem1722433 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1722424 x) (@lem1722431 x)). Qed.
Lemma lem1722434 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722435 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1722434) (@lem1722433 x)). Qed.
Lemma lem1722436 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722437 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1722435 x) (@lem1722436)). Qed.
Lemma lem1722438 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1722418 x) (@lem1722437 x)). Qed.
Lemma lem1722439 : term61 = term197.
Proof. exact (@lem1483554 term35 term24). Qed.
Lemma lem1722445 : term198 = term199.
Proof. exact (@lem1483519 term35 term24). Qed.
Lemma lem1722447 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722448 : term202 = term203.
Proof. exact (@lem1722447 term185 term185). Qed.
Lemma lem1722449 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722450 : term205 = term185.
Proof. exact (EQ_MP (@lem1722449) (@lem940073)). Qed.
Lemma lem1722451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722452 : term206 = term24.
Proof. exact (MK_COMB (@lem1722451) (@lem1722450)). Qed.
Lemma lem1722453 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722454 : term203 = term73.
Proof. exact (MK_COMB (@lem1722453) (@lem1722452)). Qed.
Lemma lem1722455 : term202 = term73.
Proof. exact (TRANS (@lem1722448) (@lem1722454)). Qed.
Lemma lem1722456 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1722459 : term199 = term208.
Proof. exact (MK_COMB (@lem1722456) (@lem1722455)). Qed.
Lemma lem1722461 : term198 = term208.
Proof. exact (TRANS (@lem1722445) (@lem1722459)). Qed.
Lemma lem1722462 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722463 : term209 = term210.
Proof. exact (MK_COMB (@lem1722462) (@lem1722461)). Qed.
Lemma lem1722464 : term210 = term211.
Proof. exact (@lem1483512 term208). Qed.
Lemma lem1722465 : term211 = term212.
Proof. exact (@lem1483508 term35 term73 term73). Qed.
Lemma lem1722467 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722468 : term215 = term206.
Proof. exact (@lem1722467 term185 term185). Qed.
Lemma lem1722469 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722470 : term205 = term185.
Proof. exact (EQ_MP (@lem1722469) (@lem940073)). Qed.
Lemma lem1722471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722472 : term206 = term24.
Proof. exact (MK_COMB (@lem1722471) (@lem1722470)). Qed.
Lemma lem1722473 : term215 = term24.
Proof. exact (TRANS (@lem1722468) (@lem1722472)). Qed.
Lemma lem1722476 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1722477 : term212 = term217.
Proof. exact (MK_COMB (@lem1722476) (@lem1722473)). Qed.
Lemma lem1722478 : term211 = term217.
Proof. exact (TRANS (@lem1722465) (@lem1722477)). Qed.
Lemma lem1722479 : term210 = term217.
Proof. exact (TRANS (@lem1722464) (@lem1722478)). Qed.
Lemma lem1722480 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem1722481 : (term209 = term210) = (term209 = term217).
Proof. exact (MK_COMB (@lem1722480) (@lem1722479)). Qed.
Lemma lem1722482 : term209 = term217.
Proof. exact (EQ_MP (@lem1722481) (@lem1722463)). Qed.
Lemma lem1722483 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722484 : term219 = term220.
Proof. exact (MK_COMB (@lem1722483) (@lem1722482)). Qed.
Lemma lem1722485 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722486 : term221 = term222.
Proof. exact (MK_COMB (@lem1722484) (@lem1722485)). Qed.
Lemma lem1722487 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722488 : term223 = term224.
Proof. exact (MK_COMB (@lem1722487) (@lem1722461)). Qed.
Lemma lem1722489 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722490 : term225 = term226.
Proof. exact (MK_COMB (@lem1722488) (@lem1722489)). Qed.
Lemma lem1722491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722492 : term227 = term228.
Proof. exact (MK_COMB (@lem1722491) (@lem1722490)). Qed.
Lemma lem1722493 : term197 = term229.
Proof. exact (MK_COMB (@lem1722492) (@lem1722486)). Qed.
Lemma lem1722494 : term61 = term229.
Proof. exact (TRANS (@lem1722439) (@lem1722493)). Qed.
Lemma lem1722495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722496 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1722495) (@lem1722438 x)). Qed.
Lemma lem1722497 (x : real) : (term62 x) = (term231 x).
Proof. exact (MK_COMB (@lem1722496 x) (@lem1722494)). Qed.
Lemma lem1722498 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1722504 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1722509 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1722511 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1722504 x) (@lem1722509 x)). Qed.
Lemma lem1722512 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722513 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1722512) (@lem1722511 x)). Qed.
Lemma lem1722514 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722515 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1722513 x) (@lem1722514)). Qed.
Lemma lem1722516 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1722498 x) (@lem1722515 x)). Qed.
Lemma lem1722517 : term80 = term327.
Proof. exact (@lem1483554 term78 term24). Qed.
Lemma lem1722523 : term328 = term329.
Proof. exact (@lem1483519 term78 term24). Qed.
Lemma lem1722525 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722526 : term202 = term203.
Proof. exact (@lem1722525 term185 term185). Qed.
Lemma lem1722527 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722528 : term205 = term185.
Proof. exact (EQ_MP (@lem1722527) (@lem940073)). Qed.
Lemma lem1722529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722530 : term206 = term24.
Proof. exact (MK_COMB (@lem1722529) (@lem1722528)). Qed.
Lemma lem1722531 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722532 : term203 = term73.
Proof. exact (MK_COMB (@lem1722531) (@lem1722530)). Qed.
Lemma lem1722533 : term202 = term73.
Proof. exact (TRANS (@lem1722526) (@lem1722532)). Qed.
Lemma lem1722534 : term330 = term330.
Proof. exact (eq_refl term330). Qed.
Lemma lem1722537 : term329 = term331.
Proof. exact (MK_COMB (@lem1722534) (@lem1722533)). Qed.
Lemma lem1722539 : term328 = term331.
Proof. exact (TRANS (@lem1722523) (@lem1722537)). Qed.
Lemma lem1722540 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722541 : term332 = term333.
Proof. exact (MK_COMB (@lem1722540) (@lem1722539)). Qed.
Lemma lem1722542 : term333 = term334.
Proof. exact (@lem1483512 term331). Qed.
Lemma lem1722543 : term334 = term335.
Proof. exact (@lem1483508 term78 term73 term73). Qed.
Lemma lem1722545 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722546 : term215 = term206.
Proof. exact (@lem1722545 term185 term185). Qed.
Lemma lem1722547 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722548 : term205 = term185.
Proof. exact (EQ_MP (@lem1722547) (@lem940073)). Qed.
Lemma lem1722549 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722550 : term206 = term24.
Proof. exact (MK_COMB (@lem1722549) (@lem1722548)). Qed.
Lemma lem1722551 : term215 = term24.
Proof. exact (TRANS (@lem1722546) (@lem1722550)). Qed.
Lemma lem1722554 : term336 = term336.
Proof. exact (eq_refl term336). Qed.
Lemma lem1722555 : term335 = term337.
Proof. exact (MK_COMB (@lem1722554) (@lem1722551)). Qed.
Lemma lem1722556 : term334 = term337.
Proof. exact (TRANS (@lem1722543) (@lem1722555)). Qed.
Lemma lem1722557 : term333 = term337.
Proof. exact (TRANS (@lem1722542) (@lem1722556)). Qed.
Lemma lem1722558 : term338 = term338.
Proof. exact (eq_refl term338). Qed.
Lemma lem1722559 : (term332 = term333) = (term332 = term337).
Proof. exact (MK_COMB (@lem1722558) (@lem1722557)). Qed.
Lemma lem1722560 : term332 = term337.
Proof. exact (EQ_MP (@lem1722559) (@lem1722541)). Qed.
Lemma lem1722561 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722562 : term339 = term340.
Proof. exact (MK_COMB (@lem1722561) (@lem1722560)). Qed.
Lemma lem1722563 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722564 : term341 = term342.
Proof. exact (MK_COMB (@lem1722562) (@lem1722563)). Qed.
Lemma lem1722565 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722566 : term343 = term344.
Proof. exact (MK_COMB (@lem1722565) (@lem1722539)). Qed.
Lemma lem1722567 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722568 : term345 = term346.
Proof. exact (MK_COMB (@lem1722566) (@lem1722567)). Qed.
Lemma lem1722569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722570 : term347 = term348.
Proof. exact (MK_COMB (@lem1722569) (@lem1722568)). Qed.
Lemma lem1722571 : term327 = term349.
Proof. exact (MK_COMB (@lem1722570) (@lem1722564)). Qed.
Lemma lem1722572 : term80 = term349.
Proof. exact (TRANS (@lem1722517) (@lem1722571)). Qed.
Lemma lem1722573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722574 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1722573) (@lem1722516 x)). Qed.
Lemma lem1722575 (x : real) : (term81 x) = (term350 x).
Proof. exact (MK_COMB (@lem1722574 x) (@lem1722572)). Qed.
Lemma lem1722576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722577 (x : real) : (term63 x) = (term262 x).
Proof. exact (MK_COMB (@lem1722576) (@lem1722497 x)). Qed.
Lemma lem1722578 (x : real) : (term82 x) = (term351 x).
Proof. exact (MK_COMB (@lem1722577 x) (@lem1722575 x)). Qed.
Lemma lem1722579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722580 (x : real) : (term83 x) = (term264 x).
Proof. exact (MK_COMB (@lem1722579) (@lem1722417 x)). Qed.
Lemma lem1722581 (x : real) : (term85 x) = (term352 x).
Proof. exact (MK_COMB (@lem1722580 x) (@lem1722578 x)). Qed.
Lemma lem1722582 (x : real) : (term266 x) = (term267 x).
Proof. exact (@lem1483531 term76 (real_abs x)). Qed.
Lemma lem1722588 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483519 term76 (real_abs x)). Qed.
Lemma lem1722593 (x : real) : (term168 x) = (term169 x).
Proof. exact (@lem1483448 (term169 x)). Qed.
Lemma lem1722595 (x : real) : (term167 x) = (term169 x).
Proof. exact (TRANS (@lem1722588 x) (@lem1722593 x)). Qed.
Lemma lem1722596 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722597 (x : real) : (term268 x) = (term269 x).
Proof. exact (MK_COMB (@lem1722596) (@lem1722595 x)). Qed.
Lemma lem1722598 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722599 (x : real) : (term267 x) = (term270 x).
Proof. exact (MK_COMB (@lem1722597 x) (@lem1722598)). Qed.
Lemma lem1722600 (x : real) : (term266 x) = (term270 x).
Proof. exact (TRANS (@lem1722582 x) (@lem1722599 x)). Qed.
Lemma lem1722601 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1722607 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1722609 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722610 : term184 = term76.
Proof. exact (@lem1722609 term185). Qed.
Lemma lem1722611 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1722612 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1722611 x) (@lem1722610)). Qed.
Lemma lem1722613 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1722614 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1722612 x) (@lem1722613 x)). Qed.
Lemma lem1722616 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1722607 x) (@lem1722614 x)). Qed.
Lemma lem1722617 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722618 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1722617) (@lem1722616 x)). Qed.
Lemma lem1722619 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722620 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1722618 x) (@lem1722619)). Qed.
Lemma lem1722621 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1722601 x) (@lem1722620 x)). Qed.
Lemma lem1722622 : term140 = term271.
Proof. exact (@lem1483554 term35 term73). Qed.
Lemma lem1722628 : term272 = term273.
Proof. exact (@lem1483519 term35 term73). Qed.
Lemma lem1722630 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722631 : term215 = term206.
Proof. exact (@lem1722630 term185 term185). Qed.
Lemma lem1722632 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722633 : term205 = term185.
Proof. exact (EQ_MP (@lem1722632) (@lem940073)). Qed.
Lemma lem1722634 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722635 : term206 = term24.
Proof. exact (MK_COMB (@lem1722634) (@lem1722633)). Qed.
Lemma lem1722636 : term215 = term24.
Proof. exact (TRANS (@lem1722631) (@lem1722635)). Qed.
Lemma lem1722637 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1722640 : term273 = term274.
Proof. exact (MK_COMB (@lem1722637) (@lem1722636)). Qed.
Lemma lem1722642 : term272 = term274.
Proof. exact (TRANS (@lem1722628) (@lem1722640)). Qed.
Lemma lem1722643 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722644 : term275 = term276.
Proof. exact (MK_COMB (@lem1722643) (@lem1722642)). Qed.
Lemma lem1722645 : term276 = term277.
Proof. exact (@lem1483512 term274). Qed.
Lemma lem1722646 : term277 = term278.
Proof. exact (@lem1483508 term35 term73 term24). Qed.
Lemma lem1722648 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722649 : term202 = term203.
Proof. exact (@lem1722648 term185 term185). Qed.
Lemma lem1722650 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722651 : term205 = term185.
Proof. exact (EQ_MP (@lem1722650) (@lem940073)). Qed.
Lemma lem1722652 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722653 : term206 = term24.
Proof. exact (MK_COMB (@lem1722652) (@lem1722651)). Qed.
Lemma lem1722654 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722655 : term203 = term73.
Proof. exact (MK_COMB (@lem1722654) (@lem1722653)). Qed.
Lemma lem1722656 : term202 = term73.
Proof. exact (TRANS (@lem1722649) (@lem1722655)). Qed.
Lemma lem1722659 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1722660 : term278 = term279.
Proof. exact (MK_COMB (@lem1722659) (@lem1722656)). Qed.
Lemma lem1722661 : term277 = term279.
Proof. exact (TRANS (@lem1722646) (@lem1722660)). Qed.
Lemma lem1722662 : term276 = term279.
Proof. exact (TRANS (@lem1722645) (@lem1722661)). Qed.
Lemma lem1722663 : term280 = term280.
Proof. exact (eq_refl term280). Qed.
Lemma lem1722664 : (term275 = term276) = (term275 = term279).
Proof. exact (MK_COMB (@lem1722663) (@lem1722662)). Qed.
Lemma lem1722665 : term275 = term279.
Proof. exact (EQ_MP (@lem1722664) (@lem1722644)). Qed.
Lemma lem1722666 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722667 : term281 = term282.
Proof. exact (MK_COMB (@lem1722666) (@lem1722665)). Qed.
Lemma lem1722668 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722669 : term283 = term284.
Proof. exact (MK_COMB (@lem1722667) (@lem1722668)). Qed.
Lemma lem1722670 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722671 : term285 = term286.
Proof. exact (MK_COMB (@lem1722670) (@lem1722642)). Qed.
Lemma lem1722672 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722673 : term287 = term288.
Proof. exact (MK_COMB (@lem1722671) (@lem1722672)). Qed.
Lemma lem1722674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722675 : term289 = term290.
Proof. exact (MK_COMB (@lem1722674) (@lem1722673)). Qed.
Lemma lem1722676 : term271 = term291.
Proof. exact (MK_COMB (@lem1722675) (@lem1722669)). Qed.
Lemma lem1722677 : term140 = term291.
Proof. exact (TRANS (@lem1722622) (@lem1722676)). Qed.
Lemma lem1722678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722679 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1722678) (@lem1722621 x)). Qed.
Lemma lem1722680 (x : real) : (term141 x) = (term292 x).
Proof. exact (MK_COMB (@lem1722679 x) (@lem1722677)). Qed.
Lemma lem1722681 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1722687 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1722692 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1722694 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1722687 x) (@lem1722692 x)). Qed.
Lemma lem1722695 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722696 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1722695) (@lem1722694 x)). Qed.
Lemma lem1722697 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722698 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1722696 x) (@lem1722697)). Qed.
Lemma lem1722699 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1722681 x) (@lem1722698 x)). Qed.
Lemma lem1722700 : term150 = term353.
Proof. exact (@lem1483554 term78 term73). Qed.
Lemma lem1722706 : term354 = term355.
Proof. exact (@lem1483519 term78 term73). Qed.
Lemma lem1722708 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722709 : term215 = term206.
Proof. exact (@lem1722708 term185 term185). Qed.
Lemma lem1722710 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722711 : term205 = term185.
Proof. exact (EQ_MP (@lem1722710) (@lem940073)). Qed.
Lemma lem1722712 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722713 : term206 = term24.
Proof. exact (MK_COMB (@lem1722712) (@lem1722711)). Qed.
Lemma lem1722714 : term215 = term24.
Proof. exact (TRANS (@lem1722709) (@lem1722713)). Qed.
Lemma lem1722715 : term330 = term330.
Proof. exact (eq_refl term330). Qed.
Lemma lem1722718 : term355 = term356.
Proof. exact (MK_COMB (@lem1722715) (@lem1722714)). Qed.
Lemma lem1722720 : term354 = term356.
Proof. exact (TRANS (@lem1722706) (@lem1722718)). Qed.
Lemma lem1722721 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722722 : term357 = term358.
Proof. exact (MK_COMB (@lem1722721) (@lem1722720)). Qed.
Lemma lem1722723 : term358 = term359.
Proof. exact (@lem1483512 term356). Qed.
Lemma lem1722724 : term359 = term360.
Proof. exact (@lem1483508 term78 term73 term24). Qed.
Lemma lem1722726 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722727 : term202 = term203.
Proof. exact (@lem1722726 term185 term185). Qed.
Lemma lem1722728 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722729 : term205 = term185.
Proof. exact (EQ_MP (@lem1722728) (@lem940073)). Qed.
Lemma lem1722730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722731 : term206 = term24.
Proof. exact (MK_COMB (@lem1722730) (@lem1722729)). Qed.
Lemma lem1722732 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722733 : term203 = term73.
Proof. exact (MK_COMB (@lem1722732) (@lem1722731)). Qed.
Lemma lem1722734 : term202 = term73.
Proof. exact (TRANS (@lem1722727) (@lem1722733)). Qed.
Lemma lem1722737 : term336 = term336.
Proof. exact (eq_refl term336). Qed.
Lemma lem1722738 : term360 = term361.
Proof. exact (MK_COMB (@lem1722737) (@lem1722734)). Qed.
Lemma lem1722739 : term359 = term361.
Proof. exact (TRANS (@lem1722724) (@lem1722738)). Qed.
Lemma lem1722740 : term358 = term361.
Proof. exact (TRANS (@lem1722723) (@lem1722739)). Qed.
Lemma lem1722741 : term362 = term362.
Proof. exact (eq_refl term362). Qed.
Lemma lem1722742 : (term357 = term358) = (term357 = term361).
Proof. exact (MK_COMB (@lem1722741) (@lem1722740)). Qed.
Lemma lem1722743 : term357 = term361.
Proof. exact (EQ_MP (@lem1722742) (@lem1722722)). Qed.
Lemma lem1722744 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722745 : term363 = term364.
Proof. exact (MK_COMB (@lem1722744) (@lem1722743)). Qed.
Lemma lem1722746 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722747 : term365 = term366.
Proof. exact (MK_COMB (@lem1722745) (@lem1722746)). Qed.
Lemma lem1722748 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722749 : term367 = term368.
Proof. exact (MK_COMB (@lem1722748) (@lem1722720)). Qed.
Lemma lem1722750 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722751 : term369 = term370.
Proof. exact (MK_COMB (@lem1722749) (@lem1722750)). Qed.
Lemma lem1722752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722753 : term371 = term372.
Proof. exact (MK_COMB (@lem1722752) (@lem1722751)). Qed.
Lemma lem1722754 : term353 = term373.
Proof. exact (MK_COMB (@lem1722753) (@lem1722747)). Qed.
Lemma lem1722755 : term150 = term373.
Proof. exact (TRANS (@lem1722700) (@lem1722754)). Qed.
Lemma lem1722756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722757 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1722756) (@lem1722699 x)). Qed.
Lemma lem1722758 (x : real) : (term151 x) = (term374 x).
Proof. exact (MK_COMB (@lem1722757 x) (@lem1722755)). Qed.
Lemma lem1722759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722760 (x : real) : (term142 x) = (term315 x).
Proof. exact (MK_COMB (@lem1722759) (@lem1722680 x)). Qed.
Lemma lem1722761 (x : real) : (term152 x) = (term375 x).
Proof. exact (MK_COMB (@lem1722760 x) (@lem1722758 x)). Qed.
Lemma lem1722762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722763 (x : real) : (term91 x) = (term317 x).
Proof. exact (MK_COMB (@lem1722762) (@lem1722600 x)). Qed.
Lemma lem1722764 (x : real) : (term153 x) = (term376 x).
Proof. exact (MK_COMB (@lem1722763 x) (@lem1722761 x)). Qed.
Lemma lem1722765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722766 (x : real) : (term87 x) = (term377 x).
Proof. exact (MK_COMB (@lem1722765) (@lem1722581 x)). Qed.
Lemma lem1722767 (x : real) : (term154 x) = (term378 x).
Proof. exact (MK_COMB (@lem1722766 x) (@lem1722764 x)). Qed.
Lemma lem1722768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722769 (x : real) : (term135 x) = (term379 x).
Proof. exact (MK_COMB (@lem1722768) (@lem1722396 x)). Qed.
Lemma lem1722770 (x : real) : (term155 x) = (term380 x).
Proof. exact (MK_COMB (@lem1722769 x) (@lem1722767 x)). Qed.
Lemma lem1722771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722772 (x : real) : (term149 x) = (term381 x).
Proof. exact (MK_COMB (@lem1722771) (@lem1722375 x)). Qed.
Lemma lem1722773 (x : real) : (term156 x) = (term382 x).
Proof. exact (MK_COMB (@lem1722772 x) (@lem1722770 x)). Qed.
Lemma lem1722774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722775 (x : real) : (term383 x) = (term384 x).
Proof. exact (MK_COMB (@lem1722774) (@lem1721982 x)). Qed.
Lemma lem1722776 (x : real) : (term385 x) = (term386 x).
Proof. exact (MK_COMB (@lem1722775 x) (@lem1722773 x)). Qed.
Lemma lem1722777 (x : real) : (term387 x) = (term388 x).
Proof. exact (@lem1483531 (real_abs x) term76). Qed.
Lemma lem1722783 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1483519 (real_abs x) term76). Qed.
Lemma lem1722785 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722786 : term184 = term76.
Proof. exact (@lem1722785 term185). Qed.
Lemma lem1722787 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1722788 (x : real) : (term182 x) = (term187 x).
Proof. exact (MK_COMB (@lem1722787 x) (@lem1722786)). Qed.
Lemma lem1722789 (x : real) : (term187 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1722790 (x : real) : (term182 x) = (real_abs x).
Proof. exact (TRANS (@lem1722788 x) (@lem1722789 x)). Qed.
Lemma lem1722792 (x : real) : (term181 x) = (real_abs x).
Proof. exact (TRANS (@lem1722783 x) (@lem1722790 x)). Qed.
Lemma lem1722793 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722794 (x : real) : (term389 x) = (term390 x).
Proof. exact (MK_COMB (@lem1722793) (@lem1722792 x)). Qed.
Lemma lem1722795 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722796 (x : real) : (term388 x) = (term391 x).
Proof. exact (MK_COMB (@lem1722794 x) (@lem1722795)). Qed.
Lemma lem1722797 (x : real) : (term387 x) = (term391 x).
Proof. exact (TRANS (@lem1722777 x) (@lem1722796 x)). Qed.
Lemma lem1722798 (x : real) : (term71 x) = (term173 x).
Proof. exact (@lem1483521 term76 x). Qed.
Lemma lem1722804 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1722809 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1722811 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1722804 x) (@lem1722809 x)). Qed.
Lemma lem1722812 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722813 (x : real) : (term177 x) = (term178 x).
Proof. exact (MK_COMB (@lem1722812) (@lem1722811 x)). Qed.
Lemma lem1722814 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722815 (x : real) : (term173 x) = (term179 x).
Proof. exact (MK_COMB (@lem1722813 x) (@lem1722814)). Qed.
Lemma lem1722816 (x : real) : (term71 x) = (term179 x).
Proof. exact (TRANS (@lem1722798 x) (@lem1722815 x)). Qed.
Lemma lem1722817 (x : real) : (term43 x) = (term180 x).
Proof. exact (@lem1483521 (real_abs x) term76). Qed.
Lemma lem1722823 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1483519 (real_abs x) term76). Qed.
Lemma lem1722825 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722826 : term184 = term76.
Proof. exact (@lem1722825 term185). Qed.
Lemma lem1722827 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1722828 (x : real) : (term182 x) = (term187 x).
Proof. exact (MK_COMB (@lem1722827 x) (@lem1722826)). Qed.
Lemma lem1722829 (x : real) : (term187 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1722830 (x : real) : (term182 x) = (real_abs x).
Proof. exact (TRANS (@lem1722828 x) (@lem1722829 x)). Qed.
Lemma lem1722832 (x : real) : (term181 x) = (real_abs x).
Proof. exact (TRANS (@lem1722823 x) (@lem1722830 x)). Qed.
Lemma lem1722833 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722834 (x : real) : (term188 x) = (term189 x).
Proof. exact (MK_COMB (@lem1722833) (@lem1722832 x)). Qed.
Lemma lem1722835 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722836 (x : real) : (term180 x) = (term190 x).
Proof. exact (MK_COMB (@lem1722834 x) (@lem1722835)). Qed.
Lemma lem1722837 (x : real) : (term43 x) = (term190 x).
Proof. exact (TRANS (@lem1722817 x) (@lem1722836 x)). Qed.
Lemma lem1722838 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1722844 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1722846 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1722847 : term184 = term76.
Proof. exact (@lem1722846 term185). Qed.
Lemma lem1722848 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1722849 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1722848 x) (@lem1722847)). Qed.
Lemma lem1722850 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1722851 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1722849 x) (@lem1722850 x)). Qed.
Lemma lem1722853 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1722844 x) (@lem1722851 x)). Qed.
Lemma lem1722854 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722855 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1722854) (@lem1722853 x)). Qed.
Lemma lem1722856 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722857 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1722855 x) (@lem1722856)). Qed.
Lemma lem1722858 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1722838 x) (@lem1722857 x)). Qed.
Lemma lem1722859 : term61 = term197.
Proof. exact (@lem1483554 term35 term24). Qed.
Lemma lem1722865 : term198 = term199.
Proof. exact (@lem1483519 term35 term24). Qed.
Lemma lem1722867 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722868 : term202 = term203.
Proof. exact (@lem1722867 term185 term185). Qed.
Lemma lem1722869 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722870 : term205 = term185.
Proof. exact (EQ_MP (@lem1722869) (@lem940073)). Qed.
Lemma lem1722871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722872 : term206 = term24.
Proof. exact (MK_COMB (@lem1722871) (@lem1722870)). Qed.
Lemma lem1722873 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722874 : term203 = term73.
Proof. exact (MK_COMB (@lem1722873) (@lem1722872)). Qed.
Lemma lem1722875 : term202 = term73.
Proof. exact (TRANS (@lem1722868) (@lem1722874)). Qed.
Lemma lem1722876 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1722879 : term199 = term208.
Proof. exact (MK_COMB (@lem1722876) (@lem1722875)). Qed.
Lemma lem1722881 : term198 = term208.
Proof. exact (TRANS (@lem1722865) (@lem1722879)). Qed.
Lemma lem1722882 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722883 : term209 = term210.
Proof. exact (MK_COMB (@lem1722882) (@lem1722881)). Qed.
Lemma lem1722884 : term210 = term211.
Proof. exact (@lem1483512 term208). Qed.
Lemma lem1722885 : term211 = term212.
Proof. exact (@lem1483508 term35 term73 term73). Qed.
Lemma lem1722887 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722888 : term215 = term206.
Proof. exact (@lem1722887 term185 term185). Qed.
Lemma lem1722889 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722890 : term205 = term185.
Proof. exact (EQ_MP (@lem1722889) (@lem940073)). Qed.
Lemma lem1722891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722892 : term206 = term24.
Proof. exact (MK_COMB (@lem1722891) (@lem1722890)). Qed.
Lemma lem1722893 : term215 = term24.
Proof. exact (TRANS (@lem1722888) (@lem1722892)). Qed.
Lemma lem1722896 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1722897 : term212 = term217.
Proof. exact (MK_COMB (@lem1722896) (@lem1722893)). Qed.
Lemma lem1722898 : term211 = term217.
Proof. exact (TRANS (@lem1722885) (@lem1722897)). Qed.
Lemma lem1722899 : term210 = term217.
Proof. exact (TRANS (@lem1722884) (@lem1722898)). Qed.
Lemma lem1722900 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem1722901 : (term209 = term210) = (term209 = term217).
Proof. exact (MK_COMB (@lem1722900) (@lem1722899)). Qed.
Lemma lem1722902 : term209 = term217.
Proof. exact (EQ_MP (@lem1722901) (@lem1722883)). Qed.
Lemma lem1722903 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722904 : term219 = term220.
Proof. exact (MK_COMB (@lem1722903) (@lem1722902)). Qed.
Lemma lem1722905 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722906 : term221 = term222.
Proof. exact (MK_COMB (@lem1722904) (@lem1722905)). Qed.
Lemma lem1722907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722908 : term223 = term224.
Proof. exact (MK_COMB (@lem1722907) (@lem1722881)). Qed.
Lemma lem1722909 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722910 : term225 = term226.
Proof. exact (MK_COMB (@lem1722908) (@lem1722909)). Qed.
Lemma lem1722911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722912 : term227 = term228.
Proof. exact (MK_COMB (@lem1722911) (@lem1722910)). Qed.
Lemma lem1722913 : term197 = term229.
Proof. exact (MK_COMB (@lem1722912) (@lem1722906)). Qed.
Lemma lem1722914 : term61 = term229.
Proof. exact (TRANS (@lem1722859) (@lem1722913)). Qed.
Lemma lem1722915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722916 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1722915) (@lem1722858 x)). Qed.
Lemma lem1722917 (x : real) : (term62 x) = (term231 x).
Proof. exact (MK_COMB (@lem1722916 x) (@lem1722914)). Qed.
Lemma lem1722918 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1722924 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1722929 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1722931 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1722924 x) (@lem1722929 x)). Qed.
Lemma lem1722932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1722933 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1722932) (@lem1722931 x)). Qed.
Lemma lem1722934 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722935 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1722933 x) (@lem1722934)). Qed.
Lemma lem1722936 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1722918 x) (@lem1722935 x)). Qed.
Lemma lem1722937 : term100 = term237.
Proof. exact (@lem1483554 term98 term24). Qed.
Lemma lem1722943 : term238 = term239.
Proof. exact (@lem1483519 term98 term24). Qed.
Lemma lem1722945 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1722946 : term202 = term203.
Proof. exact (@lem1722945 term185 term185). Qed.
Lemma lem1722947 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722948 : term205 = term185.
Proof. exact (EQ_MP (@lem1722947) (@lem940073)). Qed.
Lemma lem1722949 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722950 : term206 = term24.
Proof. exact (MK_COMB (@lem1722949) (@lem1722948)). Qed.
Lemma lem1722951 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722952 : term203 = term73.
Proof. exact (MK_COMB (@lem1722951) (@lem1722950)). Qed.
Lemma lem1722953 : term202 = term73.
Proof. exact (TRANS (@lem1722946) (@lem1722952)). Qed.
Lemma lem1722954 : term240 = term240.
Proof. exact (eq_refl term240). Qed.
Lemma lem1722957 : term239 = term241.
Proof. exact (MK_COMB (@lem1722954) (@lem1722953)). Qed.
Lemma lem1722959 : term238 = term241.
Proof. exact (TRANS (@lem1722943) (@lem1722957)). Qed.
Lemma lem1722960 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1722961 : term242 = term243.
Proof. exact (MK_COMB (@lem1722960) (@lem1722959)). Qed.
Lemma lem1722962 : term243 = term244.
Proof. exact (@lem1483512 term241). Qed.
Lemma lem1722963 : term244 = term245.
Proof. exact (@lem1483508 term98 term73 term73). Qed.
Lemma lem1722965 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1722966 : term215 = term206.
Proof. exact (@lem1722965 term185 term185). Qed.
Lemma lem1722967 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1722968 : term205 = term185.
Proof. exact (EQ_MP (@lem1722967) (@lem940073)). Qed.
Lemma lem1722969 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1722970 : term206 = term24.
Proof. exact (MK_COMB (@lem1722969) (@lem1722968)). Qed.
Lemma lem1722971 : term215 = term24.
Proof. exact (TRANS (@lem1722966) (@lem1722970)). Qed.
Lemma lem1722974 : term246 = term246.
Proof. exact (eq_refl term246). Qed.
Lemma lem1722975 : term245 = term247.
Proof. exact (MK_COMB (@lem1722974) (@lem1722971)). Qed.
Lemma lem1722976 : term244 = term247.
Proof. exact (TRANS (@lem1722963) (@lem1722975)). Qed.
Lemma lem1722977 : term243 = term247.
Proof. exact (TRANS (@lem1722962) (@lem1722976)). Qed.
Lemma lem1722978 : term248 = term248.
Proof. exact (eq_refl term248). Qed.
Lemma lem1722979 : (term242 = term243) = (term242 = term247).
Proof. exact (MK_COMB (@lem1722978) (@lem1722977)). Qed.
Lemma lem1722980 : term242 = term247.
Proof. exact (EQ_MP (@lem1722979) (@lem1722961)). Qed.
Lemma lem1722981 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722982 : term249 = term250.
Proof. exact (MK_COMB (@lem1722981) (@lem1722980)). Qed.
Lemma lem1722983 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722984 : term251 = term252.
Proof. exact (MK_COMB (@lem1722982) (@lem1722983)). Qed.
Lemma lem1722985 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1722986 : term253 = term254.
Proof. exact (MK_COMB (@lem1722985) (@lem1722959)). Qed.
Lemma lem1722987 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1722988 : term255 = term256.
Proof. exact (MK_COMB (@lem1722986) (@lem1722987)). Qed.
Lemma lem1722989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722990 : term257 = term258.
Proof. exact (MK_COMB (@lem1722989) (@lem1722988)). Qed.
Lemma lem1722991 : term237 = term259.
Proof. exact (MK_COMB (@lem1722990) (@lem1722984)). Qed.
Lemma lem1722992 : term100 = term259.
Proof. exact (TRANS (@lem1722937) (@lem1722991)). Qed.
Lemma lem1722993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1722994 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1722993) (@lem1722936 x)). Qed.
Lemma lem1722995 (x : real) : (term101 x) = (term261 x).
Proof. exact (MK_COMB (@lem1722994 x) (@lem1722992)). Qed.
Lemma lem1722996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1722997 (x : real) : (term63 x) = (term262 x).
Proof. exact (MK_COMB (@lem1722996) (@lem1722917 x)). Qed.
Lemma lem1722998 (x : real) : (term102 x) = (term263 x).
Proof. exact (MK_COMB (@lem1722997 x) (@lem1722995 x)). Qed.
Lemma lem1722999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723000 (x : real) : (term83 x) = (term264 x).
Proof. exact (MK_COMB (@lem1722999) (@lem1722837 x)). Qed.
Lemma lem1723001 (x : real) : (term103 x) = (term265 x).
Proof. exact (MK_COMB (@lem1723000 x) (@lem1722998 x)). Qed.
Lemma lem1723002 (x : real) : (term266 x) = (term267 x).
Proof. exact (@lem1483531 term76 (real_abs x)). Qed.
Lemma lem1723008 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483519 term76 (real_abs x)). Qed.
Lemma lem1723013 (x : real) : (term168 x) = (term169 x).
Proof. exact (@lem1483448 (term169 x)). Qed.
Lemma lem1723015 (x : real) : (term167 x) = (term169 x).
Proof. exact (TRANS (@lem1723008 x) (@lem1723013 x)). Qed.
Lemma lem1723016 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1723017 (x : real) : (term268 x) = (term269 x).
Proof. exact (MK_COMB (@lem1723016) (@lem1723015 x)). Qed.
Lemma lem1723018 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723019 (x : real) : (term267 x) = (term270 x).
Proof. exact (MK_COMB (@lem1723017 x) (@lem1723018)). Qed.
Lemma lem1723020 (x : real) : (term266 x) = (term270 x).
Proof. exact (TRANS (@lem1723002 x) (@lem1723019 x)). Qed.
Lemma lem1723021 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1723027 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1723029 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723030 : term184 = term76.
Proof. exact (@lem1723029 term185). Qed.
Lemma lem1723031 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1723032 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1723031 x) (@lem1723030)). Qed.
Lemma lem1723033 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1723034 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1723032 x) (@lem1723033 x)). Qed.
Lemma lem1723036 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1723027 x) (@lem1723034 x)). Qed.
Lemma lem1723037 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723038 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1723037) (@lem1723036 x)). Qed.
Lemma lem1723039 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723040 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1723038 x) (@lem1723039)). Qed.
Lemma lem1723041 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1723021 x) (@lem1723040 x)). Qed.
Lemma lem1723042 : term117 = term392.
Proof. exact (@lem1483554 term35 term76). Qed.
Lemma lem1723048 : term393 = term394.
Proof. exact (@lem1483519 term35 term76). Qed.
Lemma lem1723050 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723051 : term184 = term76.
Proof. exact (@lem1723050 term185). Qed.
Lemma lem1723052 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1723053 : term394 = term395.
Proof. exact (MK_COMB (@lem1723052) (@lem1723051)). Qed.
Lemma lem1723054 : term395 = term35.
Proof. exact (@lem1483450 term35). Qed.
Lemma lem1723055 : term394 = term35.
Proof. exact (TRANS (@lem1723053) (@lem1723054)). Qed.
Lemma lem1723057 : term393 = term35.
Proof. exact (TRANS (@lem1723048) (@lem1723055)). Qed.
Lemma lem1723058 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723059 : term396 = term397.
Proof. exact (MK_COMB (@lem1723058) (@lem1723057)). Qed.
Lemma lem1723062 : term397 = term398.
Proof. exact (@lem1483512 term35). Qed.
Lemma lem1723063 : term399 = term399.
Proof. exact (eq_refl term399). Qed.
Lemma lem1723064 : (term396 = term397) = (term396 = term398).
Proof. exact (MK_COMB (@lem1723063) (@lem1723062)). Qed.
Lemma lem1723065 : term396 = term398.
Proof. exact (EQ_MP (@lem1723064) (@lem1723059)). Qed.
Lemma lem1723066 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723067 : term400 = term401.
Proof. exact (MK_COMB (@lem1723066) (@lem1723065)). Qed.
Lemma lem1723068 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723069 : term402 = term403.
Proof. exact (MK_COMB (@lem1723067) (@lem1723068)). Qed.
Lemma lem1723070 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723071 : term404 = term405.
Proof. exact (MK_COMB (@lem1723070) (@lem1723057)). Qed.
Lemma lem1723072 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723073 : term406 = term407.
Proof. exact (MK_COMB (@lem1723071) (@lem1723072)). Qed.
Lemma lem1723074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723075 : term408 = term409.
Proof. exact (MK_COMB (@lem1723074) (@lem1723073)). Qed.
Lemma lem1723076 : term392 = term410.
Proof. exact (MK_COMB (@lem1723075) (@lem1723069)). Qed.
Lemma lem1723077 : term117 = term410.
Proof. exact (TRANS (@lem1723042) (@lem1723076)). Qed.
Lemma lem1723078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723079 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1723078) (@lem1723041 x)). Qed.
Lemma lem1723080 (x : real) : (term118 x) = (term411 x).
Proof. exact (MK_COMB (@lem1723079 x) (@lem1723077)). Qed.
Lemma lem1723081 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1723087 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1723092 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1723094 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1723087 x) (@lem1723092 x)). Qed.
Lemma lem1723095 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1723096 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1723095) (@lem1723094 x)). Qed.
Lemma lem1723097 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723098 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1723096 x) (@lem1723097)). Qed.
Lemma lem1723099 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1723081 x) (@lem1723098 x)). Qed.
Lemma lem1723100 : term120 = term412.
Proof. exact (@lem1483554 term98 term76). Qed.
Lemma lem1723106 : term413 = term414.
Proof. exact (@lem1483519 term98 term76). Qed.
Lemma lem1723108 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723109 : term184 = term76.
Proof. exact (@lem1723108 term185). Qed.
Lemma lem1723110 : term240 = term240.
Proof. exact (eq_refl term240). Qed.
Lemma lem1723111 : term414 = term415.
Proof. exact (MK_COMB (@lem1723110) (@lem1723109)). Qed.
Lemma lem1723112 : term415 = term98.
Proof. exact (@lem1483450 term98). Qed.
Lemma lem1723113 : term414 = term98.
Proof. exact (TRANS (@lem1723111) (@lem1723112)). Qed.
Lemma lem1723115 : term413 = term98.
Proof. exact (TRANS (@lem1723106) (@lem1723113)). Qed.
Lemma lem1723116 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723117 : term416 = term417.
Proof. exact (MK_COMB (@lem1723116) (@lem1723115)). Qed.
Lemma lem1723120 : term417 = term418.
Proof. exact (@lem1483512 term98). Qed.
Lemma lem1723121 : term419 = term419.
Proof. exact (eq_refl term419). Qed.
Lemma lem1723122 : (term416 = term417) = (term416 = term418).
Proof. exact (MK_COMB (@lem1723121) (@lem1723120)). Qed.
Lemma lem1723123 : term416 = term418.
Proof. exact (EQ_MP (@lem1723122) (@lem1723117)). Qed.
Lemma lem1723124 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723125 : term420 = term421.
Proof. exact (MK_COMB (@lem1723124) (@lem1723123)). Qed.
Lemma lem1723126 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723127 : term422 = term423.
Proof. exact (MK_COMB (@lem1723125) (@lem1723126)). Qed.
Lemma lem1723128 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723129 : term424 = term425.
Proof. exact (MK_COMB (@lem1723128) (@lem1723115)). Qed.
Lemma lem1723130 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723131 : term426 = term427.
Proof. exact (MK_COMB (@lem1723129) (@lem1723130)). Qed.
Lemma lem1723132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723133 : term428 = term429.
Proof. exact (MK_COMB (@lem1723132) (@lem1723131)). Qed.
Lemma lem1723134 : term412 = term430.
Proof. exact (MK_COMB (@lem1723133) (@lem1723127)). Qed.
Lemma lem1723135 : term120 = term430.
Proof. exact (TRANS (@lem1723100) (@lem1723134)). Qed.
Lemma lem1723136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723137 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1723136) (@lem1723099 x)). Qed.
Lemma lem1723138 (x : real) : (term121 x) = (term431 x).
Proof. exact (MK_COMB (@lem1723137 x) (@lem1723135)). Qed.
Lemma lem1723139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723140 (x : real) : (term119 x) = (term432 x).
Proof. exact (MK_COMB (@lem1723139) (@lem1723080 x)). Qed.
Lemma lem1723141 (x : real) : (term122 x) = (term433 x).
Proof. exact (MK_COMB (@lem1723140 x) (@lem1723138 x)). Qed.
Lemma lem1723142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723143 (x : real) : (term91 x) = (term317 x).
Proof. exact (MK_COMB (@lem1723142) (@lem1723020 x)). Qed.
Lemma lem1723144 (x : real) : (term123 x) = (term434 x).
Proof. exact (MK_COMB (@lem1723143 x) (@lem1723141 x)). Qed.
Lemma lem1723145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723146 (x : real) : (term104 x) = (term319 x).
Proof. exact (MK_COMB (@lem1723145) (@lem1723001 x)). Qed.
Lemma lem1723147 (x : real) : (term124 x) = (term435 x).
Proof. exact (MK_COMB (@lem1723146 x) (@lem1723144 x)). Qed.
Lemma lem1723148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723149 (x : real) : (term125 x) = (term321 x).
Proof. exact (MK_COMB (@lem1723148) (@lem1722816 x)). Qed.
Lemma lem1723150 (x : real) : (term127 x) = (term436 x).
Proof. exact (MK_COMB (@lem1723149 x) (@lem1723147 x)). Qed.
Lemma lem1723151 (x : real) : (term323 x) = (term324 x).
Proof. exact (@lem1483531 x term76). Qed.
Lemma lem1723157 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1723159 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723160 : term184 = term76.
Proof. exact (@lem1723159 term185). Qed.
Lemma lem1723161 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1723162 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1723161 x) (@lem1723160)). Qed.
Lemma lem1723163 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1723164 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1723162 x) (@lem1723163 x)). Qed.
Lemma lem1723166 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1723157 x) (@lem1723164 x)). Qed.
Lemma lem1723167 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1723168 (x : real) : (term325 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1723167) (@lem1723166 x)). Qed.
Lemma lem1723169 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723170 (x : real) : (term324 x) = (term326 x).
Proof. exact (MK_COMB (@lem1723168 x) (@lem1723169)). Qed.
Lemma lem1723171 (x : real) : (term323 x) = (term326 x).
Proof. exact (TRANS (@lem1723151 x) (@lem1723170 x)). Qed.
Lemma lem1723172 (x : real) : (term43 x) = (term180 x).
Proof. exact (@lem1483521 (real_abs x) term76). Qed.
Lemma lem1723178 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1483519 (real_abs x) term76). Qed.
Lemma lem1723180 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723181 : term184 = term76.
Proof. exact (@lem1723180 term185). Qed.
Lemma lem1723182 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1723183 (x : real) : (term182 x) = (term187 x).
Proof. exact (MK_COMB (@lem1723182 x) (@lem1723181)). Qed.
Lemma lem1723184 (x : real) : (term187 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1723185 (x : real) : (term182 x) = (real_abs x).
Proof. exact (TRANS (@lem1723183 x) (@lem1723184 x)). Qed.
Lemma lem1723187 (x : real) : (term181 x) = (real_abs x).
Proof. exact (TRANS (@lem1723178 x) (@lem1723185 x)). Qed.
Lemma lem1723188 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723189 (x : real) : (term188 x) = (term189 x).
Proof. exact (MK_COMB (@lem1723188) (@lem1723187 x)). Qed.
Lemma lem1723190 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723191 (x : real) : (term180 x) = (term190 x).
Proof. exact (MK_COMB (@lem1723189 x) (@lem1723190)). Qed.
Lemma lem1723192 (x : real) : (term43 x) = (term190 x).
Proof. exact (TRANS (@lem1723172 x) (@lem1723191 x)). Qed.
Lemma lem1723193 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1723199 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1723201 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723202 : term184 = term76.
Proof. exact (@lem1723201 term185). Qed.
Lemma lem1723203 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1723204 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1723203 x) (@lem1723202)). Qed.
Lemma lem1723205 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1723206 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1723204 x) (@lem1723205 x)). Qed.
Lemma lem1723208 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1723199 x) (@lem1723206 x)). Qed.
Lemma lem1723209 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723210 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1723209) (@lem1723208 x)). Qed.
Lemma lem1723211 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723212 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1723210 x) (@lem1723211)). Qed.
Lemma lem1723213 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1723193 x) (@lem1723212 x)). Qed.
Lemma lem1723214 : term61 = term197.
Proof. exact (@lem1483554 term35 term24). Qed.
Lemma lem1723220 : term198 = term199.
Proof. exact (@lem1483519 term35 term24). Qed.
Lemma lem1723222 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1723223 : term202 = term203.
Proof. exact (@lem1723222 term185 term185). Qed.
Lemma lem1723224 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1723225 : term205 = term185.
Proof. exact (EQ_MP (@lem1723224) (@lem940073)). Qed.
Lemma lem1723226 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1723227 : term206 = term24.
Proof. exact (MK_COMB (@lem1723226) (@lem1723225)). Qed.
Lemma lem1723228 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723229 : term203 = term73.
Proof. exact (MK_COMB (@lem1723228) (@lem1723227)). Qed.
Lemma lem1723230 : term202 = term73.
Proof. exact (TRANS (@lem1723223) (@lem1723229)). Qed.
Lemma lem1723231 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1723234 : term199 = term208.
Proof. exact (MK_COMB (@lem1723231) (@lem1723230)). Qed.
Lemma lem1723236 : term198 = term208.
Proof. exact (TRANS (@lem1723220) (@lem1723234)). Qed.
Lemma lem1723237 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723238 : term209 = term210.
Proof. exact (MK_COMB (@lem1723237) (@lem1723236)). Qed.
Lemma lem1723239 : term210 = term211.
Proof. exact (@lem1483512 term208). Qed.
Lemma lem1723240 : term211 = term212.
Proof. exact (@lem1483508 term35 term73 term73). Qed.
Lemma lem1723242 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1723243 : term215 = term206.
Proof. exact (@lem1723242 term185 term185). Qed.
Lemma lem1723244 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1723245 : term205 = term185.
Proof. exact (EQ_MP (@lem1723244) (@lem940073)). Qed.
Lemma lem1723246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1723247 : term206 = term24.
Proof. exact (MK_COMB (@lem1723246) (@lem1723245)). Qed.
Lemma lem1723248 : term215 = term24.
Proof. exact (TRANS (@lem1723243) (@lem1723247)). Qed.
Lemma lem1723251 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem1723252 : term212 = term217.
Proof. exact (MK_COMB (@lem1723251) (@lem1723248)). Qed.
Lemma lem1723253 : term211 = term217.
Proof. exact (TRANS (@lem1723240) (@lem1723252)). Qed.
Lemma lem1723254 : term210 = term217.
Proof. exact (TRANS (@lem1723239) (@lem1723253)). Qed.
Lemma lem1723255 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem1723256 : (term209 = term210) = (term209 = term217).
Proof. exact (MK_COMB (@lem1723255) (@lem1723254)). Qed.
Lemma lem1723257 : term209 = term217.
Proof. exact (EQ_MP (@lem1723256) (@lem1723238)). Qed.
Lemma lem1723258 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723259 : term219 = term220.
Proof. exact (MK_COMB (@lem1723258) (@lem1723257)). Qed.
Lemma lem1723260 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723261 : term221 = term222.
Proof. exact (MK_COMB (@lem1723259) (@lem1723260)). Qed.
Lemma lem1723262 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723263 : term223 = term224.
Proof. exact (MK_COMB (@lem1723262) (@lem1723236)). Qed.
Lemma lem1723264 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723265 : term225 = term226.
Proof. exact (MK_COMB (@lem1723263) (@lem1723264)). Qed.
Lemma lem1723266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723267 : term227 = term228.
Proof. exact (MK_COMB (@lem1723266) (@lem1723265)). Qed.
Lemma lem1723268 : term197 = term229.
Proof. exact (MK_COMB (@lem1723267) (@lem1723261)). Qed.
Lemma lem1723269 : term61 = term229.
Proof. exact (TRANS (@lem1723214) (@lem1723268)). Qed.
Lemma lem1723270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723271 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1723270) (@lem1723213 x)). Qed.
Lemma lem1723272 (x : real) : (term62 x) = (term231 x).
Proof. exact (MK_COMB (@lem1723271 x) (@lem1723269)). Qed.
Lemma lem1723273 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1723279 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1723284 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1723286 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1723279 x) (@lem1723284 x)). Qed.
Lemma lem1723287 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1723288 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1723287) (@lem1723286 x)). Qed.
Lemma lem1723289 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723290 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1723288 x) (@lem1723289)). Qed.
Lemma lem1723291 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1723273 x) (@lem1723290 x)). Qed.
Lemma lem1723292 : term80 = term327.
Proof. exact (@lem1483554 term78 term24). Qed.
Lemma lem1723298 : term328 = term329.
Proof. exact (@lem1483519 term78 term24). Qed.
Lemma lem1723300 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1723301 : term202 = term203.
Proof. exact (@lem1723300 term185 term185). Qed.
Lemma lem1723302 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1723303 : term205 = term185.
Proof. exact (EQ_MP (@lem1723302) (@lem940073)). Qed.
Lemma lem1723304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1723305 : term206 = term24.
Proof. exact (MK_COMB (@lem1723304) (@lem1723303)). Qed.
Lemma lem1723306 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723307 : term203 = term73.
Proof. exact (MK_COMB (@lem1723306) (@lem1723305)). Qed.
Lemma lem1723308 : term202 = term73.
Proof. exact (TRANS (@lem1723301) (@lem1723307)). Qed.
Lemma lem1723309 : term330 = term330.
Proof. exact (eq_refl term330). Qed.
Lemma lem1723312 : term329 = term331.
Proof. exact (MK_COMB (@lem1723309) (@lem1723308)). Qed.
Lemma lem1723314 : term328 = term331.
Proof. exact (TRANS (@lem1723298) (@lem1723312)). Qed.
Lemma lem1723315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723316 : term332 = term333.
Proof. exact (MK_COMB (@lem1723315) (@lem1723314)). Qed.
Lemma lem1723317 : term333 = term334.
Proof. exact (@lem1483512 term331). Qed.
Lemma lem1723318 : term334 = term335.
Proof. exact (@lem1483508 term78 term73 term73). Qed.
Lemma lem1723320 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1723321 : term215 = term206.
Proof. exact (@lem1723320 term185 term185). Qed.
Lemma lem1723322 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1723323 : term205 = term185.
Proof. exact (EQ_MP (@lem1723322) (@lem940073)). Qed.
Lemma lem1723324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1723325 : term206 = term24.
Proof. exact (MK_COMB (@lem1723324) (@lem1723323)). Qed.
Lemma lem1723326 : term215 = term24.
Proof. exact (TRANS (@lem1723321) (@lem1723325)). Qed.
Lemma lem1723329 : term336 = term336.
Proof. exact (eq_refl term336). Qed.
Lemma lem1723330 : term335 = term337.
Proof. exact (MK_COMB (@lem1723329) (@lem1723326)). Qed.
Lemma lem1723331 : term334 = term337.
Proof. exact (TRANS (@lem1723318) (@lem1723330)). Qed.
Lemma lem1723332 : term333 = term337.
Proof. exact (TRANS (@lem1723317) (@lem1723331)). Qed.
Lemma lem1723333 : term338 = term338.
Proof. exact (eq_refl term338). Qed.
Lemma lem1723334 : (term332 = term333) = (term332 = term337).
Proof. exact (MK_COMB (@lem1723333) (@lem1723332)). Qed.
Lemma lem1723335 : term332 = term337.
Proof. exact (EQ_MP (@lem1723334) (@lem1723316)). Qed.
Lemma lem1723336 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723337 : term339 = term340.
Proof. exact (MK_COMB (@lem1723336) (@lem1723335)). Qed.
Lemma lem1723338 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723339 : term341 = term342.
Proof. exact (MK_COMB (@lem1723337) (@lem1723338)). Qed.
Lemma lem1723340 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723341 : term343 = term344.
Proof. exact (MK_COMB (@lem1723340) (@lem1723314)). Qed.
Lemma lem1723342 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723343 : term345 = term346.
Proof. exact (MK_COMB (@lem1723341) (@lem1723342)). Qed.
Lemma lem1723344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723345 : term347 = term348.
Proof. exact (MK_COMB (@lem1723344) (@lem1723343)). Qed.
Lemma lem1723346 : term327 = term349.
Proof. exact (MK_COMB (@lem1723345) (@lem1723339)). Qed.
Lemma lem1723347 : term80 = term349.
Proof. exact (TRANS (@lem1723292) (@lem1723346)). Qed.
Lemma lem1723348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723349 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1723348) (@lem1723291 x)). Qed.
Lemma lem1723350 (x : real) : (term81 x) = (term350 x).
Proof. exact (MK_COMB (@lem1723349 x) (@lem1723347)). Qed.
Lemma lem1723351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723352 (x : real) : (term63 x) = (term262 x).
Proof. exact (MK_COMB (@lem1723351) (@lem1723272 x)). Qed.
Lemma lem1723353 (x : real) : (term82 x) = (term351 x).
Proof. exact (MK_COMB (@lem1723352 x) (@lem1723350 x)). Qed.
Lemma lem1723354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723355 (x : real) : (term83 x) = (term264 x).
Proof. exact (MK_COMB (@lem1723354) (@lem1723192 x)). Qed.
Lemma lem1723356 (x : real) : (term85 x) = (term352 x).
Proof. exact (MK_COMB (@lem1723355 x) (@lem1723353 x)). Qed.
Lemma lem1723357 (x : real) : (term266 x) = (term267 x).
Proof. exact (@lem1483531 term76 (real_abs x)). Qed.
Lemma lem1723363 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483519 term76 (real_abs x)). Qed.
Lemma lem1723368 (x : real) : (term168 x) = (term169 x).
Proof. exact (@lem1483448 (term169 x)). Qed.
Lemma lem1723370 (x : real) : (term167 x) = (term169 x).
Proof. exact (TRANS (@lem1723363 x) (@lem1723368 x)). Qed.
Lemma lem1723371 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1723372 (x : real) : (term268 x) = (term269 x).
Proof. exact (MK_COMB (@lem1723371) (@lem1723370 x)). Qed.
Lemma lem1723373 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723374 (x : real) : (term267 x) = (term270 x).
Proof. exact (MK_COMB (@lem1723372 x) (@lem1723373)). Qed.
Lemma lem1723375 (x : real) : (term266 x) = (term270 x).
Proof. exact (TRANS (@lem1723357 x) (@lem1723374 x)). Qed.
Lemma lem1723376 (x : real) : (term22 x) = (term191 x).
Proof. exact (@lem1483521 x term76). Qed.
Lemma lem1723382 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1723384 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723385 : term184 = term76.
Proof. exact (@lem1723384 term185). Qed.
Lemma lem1723386 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1723387 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1723386 x) (@lem1723385)). Qed.
Lemma lem1723388 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1723389 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1723387 x) (@lem1723388 x)). Qed.
Lemma lem1723391 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1723382 x) (@lem1723389 x)). Qed.
Lemma lem1723392 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723393 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1723392) (@lem1723391 x)). Qed.
Lemma lem1723394 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723395 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1723393 x) (@lem1723394)). Qed.
Lemma lem1723396 (x : real) : (term22 x) = (term196 x).
Proof. exact (TRANS (@lem1723376 x) (@lem1723395 x)). Qed.
Lemma lem1723397 : term117 = term392.
Proof. exact (@lem1483554 term35 term76). Qed.
Lemma lem1723403 : term393 = term394.
Proof. exact (@lem1483519 term35 term76). Qed.
Lemma lem1723405 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723406 : term184 = term76.
Proof. exact (@lem1723405 term185). Qed.
Lemma lem1723407 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1723408 : term394 = term395.
Proof. exact (MK_COMB (@lem1723407) (@lem1723406)). Qed.
Lemma lem1723409 : term395 = term35.
Proof. exact (@lem1483450 term35). Qed.
Lemma lem1723410 : term394 = term35.
Proof. exact (TRANS (@lem1723408) (@lem1723409)). Qed.
Lemma lem1723412 : term393 = term35.
Proof. exact (TRANS (@lem1723403) (@lem1723410)). Qed.
Lemma lem1723413 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723414 : term396 = term397.
Proof. exact (MK_COMB (@lem1723413) (@lem1723412)). Qed.
Lemma lem1723417 : term397 = term398.
Proof. exact (@lem1483512 term35). Qed.
Lemma lem1723418 : term399 = term399.
Proof. exact (eq_refl term399). Qed.
Lemma lem1723419 : (term396 = term397) = (term396 = term398).
Proof. exact (MK_COMB (@lem1723418) (@lem1723417)). Qed.
Lemma lem1723420 : term396 = term398.
Proof. exact (EQ_MP (@lem1723419) (@lem1723414)). Qed.
Lemma lem1723421 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723422 : term400 = term401.
Proof. exact (MK_COMB (@lem1723421) (@lem1723420)). Qed.
Lemma lem1723423 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723424 : term402 = term403.
Proof. exact (MK_COMB (@lem1723422) (@lem1723423)). Qed.
Lemma lem1723425 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723426 : term404 = term405.
Proof. exact (MK_COMB (@lem1723425) (@lem1723412)). Qed.
Lemma lem1723427 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723428 : term406 = term407.
Proof. exact (MK_COMB (@lem1723426) (@lem1723427)). Qed.
Lemma lem1723429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723430 : term408 = term409.
Proof. exact (MK_COMB (@lem1723429) (@lem1723428)). Qed.
Lemma lem1723431 : term392 = term410.
Proof. exact (MK_COMB (@lem1723430) (@lem1723424)). Qed.
Lemma lem1723432 : term117 = term410.
Proof. exact (TRANS (@lem1723397) (@lem1723431)). Qed.
Lemma lem1723433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723434 (x : real) : (term49 x) = (term230 x).
Proof. exact (MK_COMB (@lem1723433) (@lem1723396 x)). Qed.
Lemma lem1723435 (x : real) : (term118 x) = (term411 x).
Proof. exact (MK_COMB (@lem1723434 x) (@lem1723432)). Qed.
Lemma lem1723436 (x : real) : (term232 x) = (term233 x).
Proof. exact (@lem1483531 term76 x). Qed.
Lemma lem1723442 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1723447 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1723449 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1723442 x) (@lem1723447 x)). Qed.
Lemma lem1723450 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1723451 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1723450) (@lem1723449 x)). Qed.
Lemma lem1723452 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723453 (x : real) : (term233 x) = (term236 x).
Proof. exact (MK_COMB (@lem1723451 x) (@lem1723452)). Qed.
Lemma lem1723454 (x : real) : (term232 x) = (term236 x).
Proof. exact (TRANS (@lem1723436 x) (@lem1723453 x)). Qed.
Lemma lem1723455 : term130 = term437.
Proof. exact (@lem1483554 term78 term76). Qed.
Lemma lem1723461 : term438 = term439.
Proof. exact (@lem1483519 term78 term76). Qed.
Lemma lem1723463 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1723464 : term184 = term76.
Proof. exact (@lem1723463 term185). Qed.
Lemma lem1723465 : term330 = term330.
Proof. exact (eq_refl term330). Qed.
Lemma lem1723466 : term439 = term440.
Proof. exact (MK_COMB (@lem1723465) (@lem1723464)). Qed.
Lemma lem1723467 : term440 = term78.
Proof. exact (@lem1483450 term78). Qed.
Lemma lem1723468 : term439 = term78.
Proof. exact (TRANS (@lem1723466) (@lem1723467)). Qed.
Lemma lem1723470 : term438 = term78.
Proof. exact (TRANS (@lem1723461) (@lem1723468)). Qed.
Lemma lem1723471 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1723472 : term441 = term442.
Proof. exact (MK_COMB (@lem1723471) (@lem1723470)). Qed.
Lemma lem1723475 : term442 = term443.
Proof. exact (@lem1483512 term78). Qed.
Lemma lem1723476 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem1723477 : (term441 = term442) = (term441 = term443).
Proof. exact (MK_COMB (@lem1723476) (@lem1723475)). Qed.
Lemma lem1723478 : term441 = term443.
Proof. exact (EQ_MP (@lem1723477) (@lem1723472)). Qed.
Lemma lem1723479 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723480 : term445 = term446.
Proof. exact (MK_COMB (@lem1723479) (@lem1723478)). Qed.
Lemma lem1723481 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723482 : term447 = term448.
Proof. exact (MK_COMB (@lem1723480) (@lem1723481)). Qed.
Lemma lem1723483 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1723484 : term449 = term450.
Proof. exact (MK_COMB (@lem1723483) (@lem1723470)). Qed.
Lemma lem1723485 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1723486 : term451 = term452.
Proof. exact (MK_COMB (@lem1723484) (@lem1723485)). Qed.
Lemma lem1723487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723488 : term453 = term454.
Proof. exact (MK_COMB (@lem1723487) (@lem1723486)). Qed.
Lemma lem1723489 : term437 = term455.
Proof. exact (MK_COMB (@lem1723488) (@lem1723482)). Qed.
Lemma lem1723490 : term130 = term455.
Proof. exact (TRANS (@lem1723455) (@lem1723489)). Qed.
Lemma lem1723491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723492 (x : real) : (term55 x) = (term260 x).
Proof. exact (MK_COMB (@lem1723491) (@lem1723454 x)). Qed.
Lemma lem1723493 (x : real) : (term131 x) = (term456 x).
Proof. exact (MK_COMB (@lem1723492 x) (@lem1723490)). Qed.
Lemma lem1723494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723495 (x : real) : (term119 x) = (term432 x).
Proof. exact (MK_COMB (@lem1723494) (@lem1723435 x)). Qed.
Lemma lem1723496 (x : real) : (term132 x) = (term457 x).
Proof. exact (MK_COMB (@lem1723495 x) (@lem1723493 x)). Qed.
Lemma lem1723497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723498 (x : real) : (term91 x) = (term317 x).
Proof. exact (MK_COMB (@lem1723497) (@lem1723375 x)). Qed.
Lemma lem1723499 (x : real) : (term133 x) = (term458 x).
Proof. exact (MK_COMB (@lem1723498 x) (@lem1723496 x)). Qed.
Lemma lem1723500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723501 (x : real) : (term87 x) = (term377 x).
Proof. exact (MK_COMB (@lem1723500) (@lem1723356 x)). Qed.
Lemma lem1723502 (x : real) : (term134 x) = (term459 x).
Proof. exact (MK_COMB (@lem1723501 x) (@lem1723499 x)). Qed.
Lemma lem1723503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723504 (x : real) : (term135 x) = (term379 x).
Proof. exact (MK_COMB (@lem1723503) (@lem1723171 x)). Qed.
Lemma lem1723505 (x : real) : (term137 x) = (term460 x).
Proof. exact (MK_COMB (@lem1723504 x) (@lem1723502 x)). Qed.
Lemma lem1723506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723507 (x : real) : (term129 x) = (term461 x).
Proof. exact (MK_COMB (@lem1723506) (@lem1723150 x)). Qed.
Lemma lem1723508 (x : real) : (term138 x) = (term462 x).
Proof. exact (MK_COMB (@lem1723507 x) (@lem1723505 x)). Qed.
Lemma lem1723509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1723510 (x : real) : (term463 x) = (term464 x).
Proof. exact (MK_COMB (@lem1723509) (@lem1722797 x)). Qed.
Lemma lem1723511 (x : real) : (term465 x) = (term466 x).
Proof. exact (MK_COMB (@lem1723510 x) (@lem1723508 x)). Qed.
Lemma lem1723512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723513 (x : real) : (term467 x) = (term468 x).
Proof. exact (MK_COMB (@lem1723512) (@lem1722776 x)). Qed.
Lemma lem1723514 (x : real) : (term160 x) = (term469 x).
Proof. exact (MK_COMB (@lem1723513 x) (@lem1723511 x)). Qed.
Lemma lem1723515 : term164 = term470.
Proof. exact (fun_ext (fun x : real => @lem1723514 x)). Qed.
Lemma lem1723516 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1723517 : term165 = term471.
Proof. exact (MK_COMB (@lem1723516) (@lem1723515)). Qed.
Lemma lem1723518 : term14 = term471.
Proof. exact (TRANS (@lem1721963) (@lem1723517)). Qed.
Lemma lem1723520 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term472 A P Q) = (term473 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1723521 (P : real -> Prop) (Q : real -> Prop) : (term474 P Q) = (term475 P Q).
Proof. exact (@lem1723520 real P Q). Qed.
Lemma lem1723522 : term476 = term477.
Proof. exact (@lem1723521 term478 term479). Qed.
Lemma lem1723523 (x : real) : (term480 x) = (term386 x).
Proof. exact (eq_refl (term480 x)). Qed.
Lemma lem1723524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723525 (x : real) : (term481 x) = (term468 x).
Proof. exact (MK_COMB (@lem1723524) (@lem1723523 x)). Qed.
Lemma lem1723526 (x : real) : (term482 x) = (term466 x).
Proof. exact (eq_refl (term482 x)). Qed.
Lemma lem1723527 (x : real) : (term483 x) = (term469 x).
Proof. exact (MK_COMB (@lem1723525 x) (@lem1723526 x)). Qed.
Lemma lem1723528 : term484 = term470.
Proof. exact (fun_ext (fun x : real => @lem1723527 x)). Qed.
Lemma lem1723529 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1723530 : term476 = term471.
Proof. exact (MK_COMB (@lem1723529) (@lem1723528)). Qed.
Lemma lem1723531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1723532 : term485 = term486.
Proof. exact (MK_COMB (@lem1723531) (@lem1723530)). Qed.
Lemma lem1723533 (x : real) : (term480 x) = (term386 x).
Proof. exact (eq_refl (term480 x)). Qed.
Lemma lem1723534 : term487 = term478.
Proof. exact (fun_ext (fun x : real => @lem1723533 x)). Qed.
Lemma lem1723535 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1723536 : term488 = term489.
Proof. exact (MK_COMB (@lem1723535) (@lem1723534)). Qed.
Lemma lem1723537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723538 : term490 = term491.
Proof. exact (MK_COMB (@lem1723537) (@lem1723536)). Qed.
Lemma lem1723539 (x : real) : (term482 x) = (term466 x).
Proof. exact (eq_refl (term482 x)). Qed.
Lemma lem1723540 : term492 = term479.
Proof. exact (fun_ext (fun x : real => @lem1723539 x)). Qed.
Lemma lem1723541 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1723542 : term493 = term494.
Proof. exact (MK_COMB (@lem1723541) (@lem1723540)). Qed.
Lemma lem1723543 : term477 = term495.
Proof. exact (MK_COMB (@lem1723538) (@lem1723542)). Qed.
Lemma lem1723544 : (term476 = term477) = (term471 = term495).
Proof. exact (MK_COMB (@lem1723532) (@lem1723543)). Qed.
Lemma lem1723545 : term471 = term495.
Proof. exact (EQ_MP (@lem1723544) (@lem1723522)). Qed.
Lemma lem1723643 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term473 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1723644 (P : real -> Prop) (Q : real -> Prop) : (term475 P Q) = (term474 P Q).
Proof. exact (@lem1723643 real P Q). Qed.
Lemma lem1723645 : term477 = term476.
Proof. exact (@lem1723644 term478 term479). Qed.
Lemma lem1723646 (x : real) : (term480 x) = (term386 x).
Proof. exact (eq_refl (term480 x)). Qed.
Lemma lem1723647 : term487 = term478.
Proof. exact (fun_ext (fun x : real => @lem1723646 x)). Qed.
Lemma lem1723648 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1723649 : term488 = term489.
Proof. exact (MK_COMB (@lem1723648) (@lem1723647)). Qed.
Lemma lem1723650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723651 : term490 = term491.
Proof. exact (MK_COMB (@lem1723650) (@lem1723649)). Qed.
Lemma lem1723652 (x : real) : (term482 x) = (term466 x).
Proof. exact (eq_refl (term482 x)). Qed.
Lemma lem1723653 : term492 = term479.
Proof. exact (fun_ext (fun x : real => @lem1723652 x)). Qed.
Lemma lem1723654 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1723655 : term493 = term494.
Proof. exact (MK_COMB (@lem1723654) (@lem1723653)). Qed.
Lemma lem1723656 : term477 = term495.
Proof. exact (MK_COMB (@lem1723651) (@lem1723655)). Qed.
Lemma lem1723657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1723658 : term496 = term497.
Proof. exact (MK_COMB (@lem1723657) (@lem1723656)). Qed.
Lemma lem1723659 (x : real) : (term480 x) = (term386 x).
Proof. exact (eq_refl (term480 x)). Qed.
Lemma lem1723660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723661 (x : real) : (term481 x) = (term468 x).
Proof. exact (MK_COMB (@lem1723660) (@lem1723659 x)). Qed.
Lemma lem1723662 (x : real) : (term482 x) = (term466 x).
Proof. exact (eq_refl (term482 x)). Qed.
Lemma lem1723663 (x : real) : (term483 x) = (term469 x).
Proof. exact (MK_COMB (@lem1723661 x) (@lem1723662 x)). Qed.
Lemma lem1723664 : term484 = term470.
Proof. exact (fun_ext (fun x : real => @lem1723663 x)). Qed.
Lemma lem1723665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1723666 : term476 = term471.
Proof. exact (MK_COMB (@lem1723665) (@lem1723664)). Qed.
Lemma lem1723667 : (term477 = term476) = (term495 = term471).
Proof. exact (MK_COMB (@lem1723658) (@lem1723666)). Qed.
Lemma lem1723668 : term495 = term471.
Proof. exact (EQ_MP (@lem1723667) (@lem1723645)). Qed.
Lemma lem1723669 : term471 = term471.
Proof. exact (TRANS (@lem1723545) (@lem1723668)). Qed.
Lemma lem1723672 : term14 = term471.
Proof. exact (TRANS (@lem1723518) (@lem1723669)). Qed.
Lemma lem1723689 (x : real) : (term456 x) = (term498 x).
Proof. exact (@lem19158 term452 (term236 x) term448). Qed.
Lemma lem1723706 (x : real) : (term411 x) = (term499 x).
Proof. exact (@lem19158 term407 (term196 x) term403). Qed.
Lemma lem1723707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723708 (x : real) : (term432 x) = (term500 x).
Proof. exact (MK_COMB (@lem1723707) (@lem1723706 x)). Qed.
Lemma lem1723709 (x : real) : (term457 x) = (term501 x).
Proof. exact (MK_COMB (@lem1723708 x) (@lem1723689 x)). Qed.
Lemma lem1723712 (x : real) : (term317 x) = (term317 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem1723713 (x : real) : (term458 x) = (term502 x).
Proof. exact (MK_COMB (@lem1723712 x) (@lem1723709 x)). Qed.
Lemma lem1723714 (x : real) : (term502 x) = (term503 x).
Proof. exact (@lem19158 (term499 x) (term270 x) (term498 x)). Qed.
Lemma lem1723721 (x : real) : (term504 x) = (term505 x).
Proof. exact (@lem19158 (term506 x) (term270 x) (term507 x)). Qed.
Lemma lem1723728 (x : real) : (term508 x) = (term509 x).
Proof. exact (@lem19158 (term510 x) (term270 x) (term511 x)). Qed.
Lemma lem1723729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723730 (x : real) : (term512 x) = (term513 x).
Proof. exact (MK_COMB (@lem1723729) (@lem1723728 x)). Qed.
Lemma lem1723731 (x : real) : (term503 x) = (term514 x).
Proof. exact (MK_COMB (@lem1723730 x) (@lem1723721 x)). Qed.
Lemma lem1723732 (x : real) : (term502 x) = (term514 x).
Proof. exact (TRANS (@lem1723714 x) (@lem1723731 x)). Qed.
Lemma lem1723733 (x : real) : (term458 x) = (term514 x).
Proof. exact (TRANS (@lem1723713 x) (@lem1723732 x)). Qed.
Lemma lem1723750 (x : real) : (term350 x) = (term515 x).
Proof. exact (@lem19158 term346 (term236 x) term342). Qed.
Lemma lem1723767 (x : real) : (term231 x) = (term516 x).
Proof. exact (@lem19158 term226 (term196 x) term222). Qed.
Lemma lem1723768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723769 (x : real) : (term262 x) = (term517 x).
Proof. exact (MK_COMB (@lem1723768) (@lem1723767 x)). Qed.
Lemma lem1723770 (x : real) : (term351 x) = (term518 x).
Proof. exact (MK_COMB (@lem1723769 x) (@lem1723750 x)). Qed.
Lemma lem1723773 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1723774 (x : real) : (term352 x) = (term519 x).
Proof. exact (MK_COMB (@lem1723773 x) (@lem1723770 x)). Qed.
Lemma lem1723775 (x : real) : (term519 x) = (term520 x).
Proof. exact (@lem19158 (term516 x) (term190 x) (term515 x)). Qed.
Lemma lem1723782 (x : real) : (term521 x) = (term522 x).
Proof. exact (@lem19158 (term523 x) (term190 x) (term524 x)). Qed.
Lemma lem1723789 (x : real) : (term525 x) = (term526 x).
Proof. exact (@lem19158 (term527 x) (term190 x) (term528 x)). Qed.
Lemma lem1723790 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723791 (x : real) : (term529 x) = (term530 x).
Proof. exact (MK_COMB (@lem1723790) (@lem1723789 x)). Qed.
Lemma lem1723792 (x : real) : (term520 x) = (term531 x).
Proof. exact (MK_COMB (@lem1723791 x) (@lem1723782 x)). Qed.
Lemma lem1723793 (x : real) : (term519 x) = (term531 x).
Proof. exact (TRANS (@lem1723775 x) (@lem1723792 x)). Qed.
Lemma lem1723794 (x : real) : (term352 x) = (term531 x).
Proof. exact (TRANS (@lem1723774 x) (@lem1723793 x)). Qed.
Lemma lem1723795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723796 (x : real) : (term377 x) = (term532 x).
Proof. exact (MK_COMB (@lem1723795) (@lem1723794 x)). Qed.
Lemma lem1723797 (x : real) : (term459 x) = (term533 x).
Proof. exact (MK_COMB (@lem1723796 x) (@lem1723733 x)). Qed.
Lemma lem1723800 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1723801 (x : real) : (term460 x) = (term534 x).
Proof. exact (MK_COMB (@lem1723800 x) (@lem1723797 x)). Qed.
Lemma lem1723802 (x : real) : (term534 x) = (term535 x).
Proof. exact (@lem19158 (term531 x) (term326 x) (term514 x)). Qed.
Lemma lem1723803 (x : real) : (term536 x) = (term537 x).
Proof. exact (@lem19158 (term509 x) (term326 x) (term505 x)). Qed.
Lemma lem1723810 (x : real) : (term538 x) = (term539 x).
Proof. exact (@lem19158 (term540 x) (term326 x) (term541 x)). Qed.
Lemma lem1723817 (x : real) : (term542 x) = (term543 x).
Proof. exact (@lem19158 (term544 x) (term326 x) (term545 x)). Qed.
Lemma lem1723818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723819 (x : real) : (term546 x) = (term547 x).
Proof. exact (MK_COMB (@lem1723818) (@lem1723817 x)). Qed.
Lemma lem1723820 (x : real) : (term537 x) = (term548 x).
Proof. exact (MK_COMB (@lem1723819 x) (@lem1723810 x)). Qed.
Lemma lem1723821 (x : real) : (term536 x) = (term548 x).
Proof. exact (TRANS (@lem1723803 x) (@lem1723820 x)). Qed.
Lemma lem1723822 (x : real) : (term549 x) = (term550 x).
Proof. exact (@lem19158 (term526 x) (term326 x) (term522 x)). Qed.
Lemma lem1723829 (x : real) : (term551 x) = (term552 x).
Proof. exact (@lem19158 (term553 x) (term326 x) (term554 x)). Qed.
Lemma lem1723836 (x : real) : (term555 x) = (term556 x).
Proof. exact (@lem19158 (term557 x) (term326 x) (term558 x)). Qed.
Lemma lem1723837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723838 (x : real) : (term559 x) = (term560 x).
Proof. exact (MK_COMB (@lem1723837) (@lem1723836 x)). Qed.
Lemma lem1723839 (x : real) : (term550 x) = (term561 x).
Proof. exact (MK_COMB (@lem1723838 x) (@lem1723829 x)). Qed.
Lemma lem1723840 (x : real) : (term549 x) = (term561 x).
Proof. exact (TRANS (@lem1723822 x) (@lem1723839 x)). Qed.
Lemma lem1723841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723842 (x : real) : (term562 x) = (term563 x).
Proof. exact (MK_COMB (@lem1723841) (@lem1723840 x)). Qed.
Lemma lem1723843 (x : real) : (term535 x) = (term564 x).
Proof. exact (MK_COMB (@lem1723842 x) (@lem1723821 x)). Qed.
Lemma lem1723844 (x : real) : (term534 x) = (term564 x).
Proof. exact (TRANS (@lem1723802 x) (@lem1723843 x)). Qed.
Lemma lem1723845 (x : real) : (term460 x) = (term564 x).
Proof. exact (TRANS (@lem1723801 x) (@lem1723844 x)). Qed.
Lemma lem1723862 (x : real) : (term431 x) = (term565 x).
Proof. exact (@lem19158 term427 (term236 x) term423). Qed.
Lemma lem1723879 (x : real) : (term411 x) = (term499 x).
Proof. exact (@lem19158 term407 (term196 x) term403). Qed.
Lemma lem1723880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723881 (x : real) : (term432 x) = (term500 x).
Proof. exact (MK_COMB (@lem1723880) (@lem1723879 x)). Qed.
Lemma lem1723882 (x : real) : (term433 x) = (term566 x).
Proof. exact (MK_COMB (@lem1723881 x) (@lem1723862 x)). Qed.
Lemma lem1723885 (x : real) : (term317 x) = (term317 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem1723886 (x : real) : (term434 x) = (term567 x).
Proof. exact (MK_COMB (@lem1723885 x) (@lem1723882 x)). Qed.
Lemma lem1723887 (x : real) : (term567 x) = (term568 x).
Proof. exact (@lem19158 (term499 x) (term270 x) (term565 x)). Qed.
Lemma lem1723894 (x : real) : (term569 x) = (term570 x).
Proof. exact (@lem19158 (term571 x) (term270 x) (term572 x)). Qed.
Lemma lem1723901 (x : real) : (term508 x) = (term509 x).
Proof. exact (@lem19158 (term510 x) (term270 x) (term511 x)). Qed.
Lemma lem1723902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723903 (x : real) : (term512 x) = (term513 x).
Proof. exact (MK_COMB (@lem1723902) (@lem1723901 x)). Qed.
Lemma lem1723904 (x : real) : (term568 x) = (term573 x).
Proof. exact (MK_COMB (@lem1723903 x) (@lem1723894 x)). Qed.
Lemma lem1723905 (x : real) : (term567 x) = (term573 x).
Proof. exact (TRANS (@lem1723887 x) (@lem1723904 x)). Qed.
Lemma lem1723906 (x : real) : (term434 x) = (term573 x).
Proof. exact (TRANS (@lem1723886 x) (@lem1723905 x)). Qed.
Lemma lem1723923 (x : real) : (term261 x) = (term574 x).
Proof. exact (@lem19158 term256 (term236 x) term252). Qed.
Lemma lem1723940 (x : real) : (term231 x) = (term516 x).
Proof. exact (@lem19158 term226 (term196 x) term222). Qed.
Lemma lem1723941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723942 (x : real) : (term262 x) = (term517 x).
Proof. exact (MK_COMB (@lem1723941) (@lem1723940 x)). Qed.
Lemma lem1723943 (x : real) : (term263 x) = (term575 x).
Proof. exact (MK_COMB (@lem1723942 x) (@lem1723923 x)). Qed.
Lemma lem1723946 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1723947 (x : real) : (term265 x) = (term576 x).
Proof. exact (MK_COMB (@lem1723946 x) (@lem1723943 x)). Qed.
Lemma lem1723948 (x : real) : (term576 x) = (term577 x).
Proof. exact (@lem19158 (term516 x) (term190 x) (term574 x)). Qed.
Lemma lem1723955 (x : real) : (term578 x) = (term579 x).
Proof. exact (@lem19158 (term580 x) (term190 x) (term581 x)). Qed.
Lemma lem1723962 (x : real) : (term525 x) = (term526 x).
Proof. exact (@lem19158 (term527 x) (term190 x) (term528 x)). Qed.
Lemma lem1723963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723964 (x : real) : (term529 x) = (term530 x).
Proof. exact (MK_COMB (@lem1723963) (@lem1723962 x)). Qed.
Lemma lem1723965 (x : real) : (term577 x) = (term582 x).
Proof. exact (MK_COMB (@lem1723964 x) (@lem1723955 x)). Qed.
Lemma lem1723966 (x : real) : (term576 x) = (term582 x).
Proof. exact (TRANS (@lem1723948 x) (@lem1723965 x)). Qed.
Lemma lem1723967 (x : real) : (term265 x) = (term582 x).
Proof. exact (TRANS (@lem1723947 x) (@lem1723966 x)). Qed.
Lemma lem1723968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723969 (x : real) : (term319 x) = (term583 x).
Proof. exact (MK_COMB (@lem1723968) (@lem1723967 x)). Qed.
Lemma lem1723970 (x : real) : (term435 x) = (term584 x).
Proof. exact (MK_COMB (@lem1723969 x) (@lem1723906 x)). Qed.
Lemma lem1723973 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1723974 (x : real) : (term436 x) = (term585 x).
Proof. exact (MK_COMB (@lem1723973 x) (@lem1723970 x)). Qed.
Lemma lem1723975 (x : real) : (term585 x) = (term586 x).
Proof. exact (@lem19158 (term582 x) (term179 x) (term573 x)). Qed.
Lemma lem1723976 (x : real) : (term587 x) = (term588 x).
Proof. exact (@lem19158 (term509 x) (term179 x) (term570 x)). Qed.
Lemma lem1723983 (x : real) : (term589 x) = (term590 x).
Proof. exact (@lem19158 (term591 x) (term179 x) (term592 x)). Qed.
Lemma lem1723990 (x : real) : (term593 x) = (term594 x).
Proof. exact (@lem19158 (term544 x) (term179 x) (term545 x)). Qed.
Lemma lem1723991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1723992 (x : real) : (term595 x) = (term596 x).
Proof. exact (MK_COMB (@lem1723991) (@lem1723990 x)). Qed.
Lemma lem1723993 (x : real) : (term588 x) = (term597 x).
Proof. exact (MK_COMB (@lem1723992 x) (@lem1723983 x)). Qed.
Lemma lem1723994 (x : real) : (term587 x) = (term597 x).
Proof. exact (TRANS (@lem1723976 x) (@lem1723993 x)). Qed.
Lemma lem1723995 (x : real) : (term598 x) = (term599 x).
Proof. exact (@lem19158 (term526 x) (term179 x) (term579 x)). Qed.
Lemma lem1724002 (x : real) : (term600 x) = (term601 x).
Proof. exact (@lem19158 (term602 x) (term179 x) (term603 x)). Qed.
Lemma lem1724009 (x : real) : (term604 x) = (term605 x).
Proof. exact (@lem19158 (term557 x) (term179 x) (term558 x)). Qed.
Lemma lem1724010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724011 (x : real) : (term606 x) = (term607 x).
Proof. exact (MK_COMB (@lem1724010) (@lem1724009 x)). Qed.
Lemma lem1724012 (x : real) : (term599 x) = (term608 x).
Proof. exact (MK_COMB (@lem1724011 x) (@lem1724002 x)). Qed.
Lemma lem1724013 (x : real) : (term598 x) = (term608 x).
Proof. exact (TRANS (@lem1723995 x) (@lem1724012 x)). Qed.
Lemma lem1724014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724015 (x : real) : (term609 x) = (term610 x).
Proof. exact (MK_COMB (@lem1724014) (@lem1724013 x)). Qed.
Lemma lem1724016 (x : real) : (term586 x) = (term611 x).
Proof. exact (MK_COMB (@lem1724015 x) (@lem1723994 x)). Qed.
Lemma lem1724017 (x : real) : (term585 x) = (term611 x).
Proof. exact (TRANS (@lem1723975 x) (@lem1724016 x)). Qed.
Lemma lem1724018 (x : real) : (term436 x) = (term611 x).
Proof. exact (TRANS (@lem1723974 x) (@lem1724017 x)). Qed.
Lemma lem1724019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724020 (x : real) : (term461 x) = (term612 x).
Proof. exact (MK_COMB (@lem1724019) (@lem1724018 x)). Qed.
Lemma lem1724021 (x : real) : (term462 x) = (term613 x).
Proof. exact (MK_COMB (@lem1724020 x) (@lem1723845 x)). Qed.
Lemma lem1724024 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1724025 (x : real) : (term466 x) = (term614 x).
Proof. exact (MK_COMB (@lem1724024 x) (@lem1724021 x)). Qed.
Lemma lem1724026 (x : real) : (term614 x) = (term615 x).
Proof. exact (@lem19158 (term611 x) (term391 x) (term564 x)). Qed.
Lemma lem1724027 (x : real) : (term616 x) = (term617 x).
Proof. exact (@lem19158 (term561 x) (term391 x) (term548 x)). Qed.
Lemma lem1724028 (x : real) : (term618 x) = (term619 x).
Proof. exact (@lem19158 (term543 x) (term391 x) (term539 x)). Qed.
Lemma lem1724035 (x : real) : (term620 x) = (term621 x).
Proof. exact (@lem19158 (term622 x) (term391 x) (term623 x)). Qed.
Lemma lem1724042 (x : real) : (term624 x) = (term625 x).
Proof. exact (@lem19158 (term626 x) (term391 x) (term627 x)). Qed.
Lemma lem1724043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724044 (x : real) : (term628 x) = (term629 x).
Proof. exact (MK_COMB (@lem1724043) (@lem1724042 x)). Qed.
Lemma lem1724045 (x : real) : (term619 x) = (term630 x).
Proof. exact (MK_COMB (@lem1724044 x) (@lem1724035 x)). Qed.
Lemma lem1724046 (x : real) : (term618 x) = (term630 x).
Proof. exact (TRANS (@lem1724028 x) (@lem1724045 x)). Qed.
Lemma lem1724047 (x : real) : (term631 x) = (term632 x).
Proof. exact (@lem19158 (term556 x) (term391 x) (term552 x)). Qed.
Lemma lem1724054 (x : real) : (term633 x) = (term634 x).
Proof. exact (@lem19158 (term635 x) (term391 x) (term636 x)). Qed.
Lemma lem1724061 (x : real) : (term637 x) = (term638 x).
Proof. exact (@lem19158 (term639 x) (term391 x) (term640 x)). Qed.
Lemma lem1724062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724063 (x : real) : (term641 x) = (term642 x).
Proof. exact (MK_COMB (@lem1724062) (@lem1724061 x)). Qed.
Lemma lem1724064 (x : real) : (term632 x) = (term643 x).
Proof. exact (MK_COMB (@lem1724063 x) (@lem1724054 x)). Qed.
Lemma lem1724065 (x : real) : (term631 x) = (term643 x).
Proof. exact (TRANS (@lem1724047 x) (@lem1724064 x)). Qed.
Lemma lem1724066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724067 (x : real) : (term644 x) = (term645 x).
Proof. exact (MK_COMB (@lem1724066) (@lem1724065 x)). Qed.
Lemma lem1724068 (x : real) : (term617 x) = (term646 x).
Proof. exact (MK_COMB (@lem1724067 x) (@lem1724046 x)). Qed.
Lemma lem1724069 (x : real) : (term616 x) = (term646 x).
Proof. exact (TRANS (@lem1724027 x) (@lem1724068 x)). Qed.
Lemma lem1724070 (x : real) : (term647 x) = (term648 x).
Proof. exact (@lem19158 (term608 x) (term391 x) (term597 x)). Qed.
Lemma lem1724071 (x : real) : (term649 x) = (term650 x).
Proof. exact (@lem19158 (term594 x) (term391 x) (term590 x)). Qed.
Lemma lem1724078 (x : real) : (term651 x) = (term652 x).
Proof. exact (@lem19158 (term653 x) (term391 x) (term654 x)). Qed.
Lemma lem1724085 (x : real) : (term655 x) = (term656 x).
Proof. exact (@lem19158 (term657 x) (term391 x) (term658 x)). Qed.
Lemma lem1724086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724087 (x : real) : (term659 x) = (term660 x).
Proof. exact (MK_COMB (@lem1724086) (@lem1724085 x)). Qed.
Lemma lem1724088 (x : real) : (term650 x) = (term661 x).
Proof. exact (MK_COMB (@lem1724087 x) (@lem1724078 x)). Qed.
Lemma lem1724089 (x : real) : (term649 x) = (term661 x).
Proof. exact (TRANS (@lem1724071 x) (@lem1724088 x)). Qed.
Lemma lem1724090 (x : real) : (term662 x) = (term663 x).
Proof. exact (@lem19158 (term605 x) (term391 x) (term601 x)). Qed.
Lemma lem1724097 (x : real) : (term664 x) = (term665 x).
Proof. exact (@lem19158 (term666 x) (term391 x) (term667 x)). Qed.
Lemma lem1724104 (x : real) : (term668 x) = (term669 x).
Proof. exact (@lem19158 (term670 x) (term391 x) (term671 x)). Qed.
Lemma lem1724105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724106 (x : real) : (term672 x) = (term673 x).
Proof. exact (MK_COMB (@lem1724105) (@lem1724104 x)). Qed.
Lemma lem1724107 (x : real) : (term663 x) = (term674 x).
Proof. exact (MK_COMB (@lem1724106 x) (@lem1724097 x)). Qed.
Lemma lem1724108 (x : real) : (term662 x) = (term674 x).
Proof. exact (TRANS (@lem1724090 x) (@lem1724107 x)). Qed.
Lemma lem1724109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724110 (x : real) : (term675 x) = (term676 x).
Proof. exact (MK_COMB (@lem1724109) (@lem1724108 x)). Qed.
Lemma lem1724111 (x : real) : (term648 x) = (term677 x).
Proof. exact (MK_COMB (@lem1724110 x) (@lem1724089 x)). Qed.
Lemma lem1724112 (x : real) : (term647 x) = (term677 x).
Proof. exact (TRANS (@lem1724070 x) (@lem1724111 x)). Qed.
Lemma lem1724113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724114 (x : real) : (term678 x) = (term679 x).
Proof. exact (MK_COMB (@lem1724113) (@lem1724112 x)). Qed.
Lemma lem1724115 (x : real) : (term615 x) = (term680 x).
Proof. exact (MK_COMB (@lem1724114 x) (@lem1724069 x)). Qed.
Lemma lem1724116 (x : real) : (term614 x) = (term680 x).
Proof. exact (TRANS (@lem1724026 x) (@lem1724115 x)). Qed.
Lemma lem1724117 (x : real) : (term466 x) = (term680 x).
Proof. exact (TRANS (@lem1724025 x) (@lem1724116 x)). Qed.
Lemma lem1724134 (x : real) : (term374 x) = (term681 x).
Proof. exact (@lem19158 term370 (term236 x) term366). Qed.
Lemma lem1724151 (x : real) : (term292 x) = (term682 x).
Proof. exact (@lem19158 term288 (term196 x) term284). Qed.
Lemma lem1724152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724153 (x : real) : (term315 x) = (term683 x).
Proof. exact (MK_COMB (@lem1724152) (@lem1724151 x)). Qed.
Lemma lem1724154 (x : real) : (term375 x) = (term684 x).
Proof. exact (MK_COMB (@lem1724153 x) (@lem1724134 x)). Qed.
Lemma lem1724157 (x : real) : (term317 x) = (term317 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem1724158 (x : real) : (term376 x) = (term685 x).
Proof. exact (MK_COMB (@lem1724157 x) (@lem1724154 x)). Qed.
Lemma lem1724159 (x : real) : (term685 x) = (term686 x).
Proof. exact (@lem19158 (term682 x) (term270 x) (term681 x)). Qed.
Lemma lem1724166 (x : real) : (term687 x) = (term688 x).
Proof. exact (@lem19158 (term689 x) (term270 x) (term690 x)). Qed.
Lemma lem1724173 (x : real) : (term691 x) = (term692 x).
Proof. exact (@lem19158 (term693 x) (term270 x) (term694 x)). Qed.
Lemma lem1724174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724175 (x : real) : (term695 x) = (term696 x).
Proof. exact (MK_COMB (@lem1724174) (@lem1724173 x)). Qed.
Lemma lem1724176 (x : real) : (term686 x) = (term697 x).
Proof. exact (MK_COMB (@lem1724175 x) (@lem1724166 x)). Qed.
Lemma lem1724177 (x : real) : (term685 x) = (term697 x).
Proof. exact (TRANS (@lem1724159 x) (@lem1724176 x)). Qed.
Lemma lem1724178 (x : real) : (term376 x) = (term697 x).
Proof. exact (TRANS (@lem1724158 x) (@lem1724177 x)). Qed.
Lemma lem1724195 (x : real) : (term350 x) = (term515 x).
Proof. exact (@lem19158 term346 (term236 x) term342). Qed.
Lemma lem1724212 (x : real) : (term231 x) = (term516 x).
Proof. exact (@lem19158 term226 (term196 x) term222). Qed.
Lemma lem1724213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724214 (x : real) : (term262 x) = (term517 x).
Proof. exact (MK_COMB (@lem1724213) (@lem1724212 x)). Qed.
Lemma lem1724215 (x : real) : (term351 x) = (term518 x).
Proof. exact (MK_COMB (@lem1724214 x) (@lem1724195 x)). Qed.
Lemma lem1724218 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1724219 (x : real) : (term352 x) = (term519 x).
Proof. exact (MK_COMB (@lem1724218 x) (@lem1724215 x)). Qed.
Lemma lem1724220 (x : real) : (term519 x) = (term520 x).
Proof. exact (@lem19158 (term516 x) (term190 x) (term515 x)). Qed.
Lemma lem1724227 (x : real) : (term521 x) = (term522 x).
Proof. exact (@lem19158 (term523 x) (term190 x) (term524 x)). Qed.
Lemma lem1724234 (x : real) : (term525 x) = (term526 x).
Proof. exact (@lem19158 (term527 x) (term190 x) (term528 x)). Qed.
Lemma lem1724235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724236 (x : real) : (term529 x) = (term530 x).
Proof. exact (MK_COMB (@lem1724235) (@lem1724234 x)). Qed.
Lemma lem1724237 (x : real) : (term520 x) = (term531 x).
Proof. exact (MK_COMB (@lem1724236 x) (@lem1724227 x)). Qed.
Lemma lem1724238 (x : real) : (term519 x) = (term531 x).
Proof. exact (TRANS (@lem1724220 x) (@lem1724237 x)). Qed.
Lemma lem1724239 (x : real) : (term352 x) = (term531 x).
Proof. exact (TRANS (@lem1724219 x) (@lem1724238 x)). Qed.
Lemma lem1724240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724241 (x : real) : (term377 x) = (term532 x).
Proof. exact (MK_COMB (@lem1724240) (@lem1724239 x)). Qed.
Lemma lem1724242 (x : real) : (term378 x) = (term698 x).
Proof. exact (MK_COMB (@lem1724241 x) (@lem1724178 x)). Qed.
Lemma lem1724245 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1724246 (x : real) : (term380 x) = (term699 x).
Proof. exact (MK_COMB (@lem1724245 x) (@lem1724242 x)). Qed.
Lemma lem1724247 (x : real) : (term699 x) = (term700 x).
Proof. exact (@lem19158 (term531 x) (term326 x) (term697 x)). Qed.
Lemma lem1724248 (x : real) : (term701 x) = (term702 x).
Proof. exact (@lem19158 (term692 x) (term326 x) (term688 x)). Qed.
Lemma lem1724255 (x : real) : (term703 x) = (term704 x).
Proof. exact (@lem19158 (term705 x) (term326 x) (term706 x)). Qed.
Lemma lem1724262 (x : real) : (term707 x) = (term708 x).
Proof. exact (@lem19158 (term709 x) (term326 x) (term710 x)). Qed.
Lemma lem1724263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724264 (x : real) : (term711 x) = (term712 x).
Proof. exact (MK_COMB (@lem1724263) (@lem1724262 x)). Qed.
Lemma lem1724265 (x : real) : (term702 x) = (term713 x).
Proof. exact (MK_COMB (@lem1724264 x) (@lem1724255 x)). Qed.
Lemma lem1724266 (x : real) : (term701 x) = (term713 x).
Proof. exact (TRANS (@lem1724248 x) (@lem1724265 x)). Qed.
Lemma lem1724267 (x : real) : (term549 x) = (term550 x).
Proof. exact (@lem19158 (term526 x) (term326 x) (term522 x)). Qed.
Lemma lem1724274 (x : real) : (term551 x) = (term552 x).
Proof. exact (@lem19158 (term553 x) (term326 x) (term554 x)). Qed.
Lemma lem1724281 (x : real) : (term555 x) = (term556 x).
Proof. exact (@lem19158 (term557 x) (term326 x) (term558 x)). Qed.
Lemma lem1724282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724283 (x : real) : (term559 x) = (term560 x).
Proof. exact (MK_COMB (@lem1724282) (@lem1724281 x)). Qed.
Lemma lem1724284 (x : real) : (term550 x) = (term561 x).
Proof. exact (MK_COMB (@lem1724283 x) (@lem1724274 x)). Qed.
Lemma lem1724285 (x : real) : (term549 x) = (term561 x).
Proof. exact (TRANS (@lem1724267 x) (@lem1724284 x)). Qed.
Lemma lem1724286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724287 (x : real) : (term562 x) = (term563 x).
Proof. exact (MK_COMB (@lem1724286) (@lem1724285 x)). Qed.
Lemma lem1724288 (x : real) : (term700 x) = (term714 x).
Proof. exact (MK_COMB (@lem1724287 x) (@lem1724266 x)). Qed.
Lemma lem1724289 (x : real) : (term699 x) = (term714 x).
Proof. exact (TRANS (@lem1724247 x) (@lem1724288 x)). Qed.
Lemma lem1724290 (x : real) : (term380 x) = (term714 x).
Proof. exact (TRANS (@lem1724246 x) (@lem1724289 x)). Qed.
Lemma lem1724307 (x : real) : (term314 x) = (term715 x).
Proof. exact (@lem19158 term310 (term236 x) term306). Qed.
Lemma lem1724324 (x : real) : (term292 x) = (term682 x).
Proof. exact (@lem19158 term288 (term196 x) term284). Qed.
Lemma lem1724325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724326 (x : real) : (term315 x) = (term683 x).
Proof. exact (MK_COMB (@lem1724325) (@lem1724324 x)). Qed.
Lemma lem1724327 (x : real) : (term316 x) = (term716 x).
Proof. exact (MK_COMB (@lem1724326 x) (@lem1724307 x)). Qed.
Lemma lem1724330 (x : real) : (term317 x) = (term317 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem1724331 (x : real) : (term318 x) = (term717 x).
Proof. exact (MK_COMB (@lem1724330 x) (@lem1724327 x)). Qed.
Lemma lem1724332 (x : real) : (term717 x) = (term718 x).
Proof. exact (@lem19158 (term682 x) (term270 x) (term715 x)). Qed.
Lemma lem1724339 (x : real) : (term719 x) = (term720 x).
Proof. exact (@lem19158 (term721 x) (term270 x) (term722 x)). Qed.
Lemma lem1724346 (x : real) : (term691 x) = (term692 x).
Proof. exact (@lem19158 (term693 x) (term270 x) (term694 x)). Qed.
Lemma lem1724347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724348 (x : real) : (term695 x) = (term696 x).
Proof. exact (MK_COMB (@lem1724347) (@lem1724346 x)). Qed.
Lemma lem1724349 (x : real) : (term718 x) = (term723 x).
Proof. exact (MK_COMB (@lem1724348 x) (@lem1724339 x)). Qed.
Lemma lem1724350 (x : real) : (term717 x) = (term723 x).
Proof. exact (TRANS (@lem1724332 x) (@lem1724349 x)). Qed.
Lemma lem1724351 (x : real) : (term318 x) = (term723 x).
Proof. exact (TRANS (@lem1724331 x) (@lem1724350 x)). Qed.
Lemma lem1724368 (x : real) : (term261 x) = (term574 x).
Proof. exact (@lem19158 term256 (term236 x) term252). Qed.
Lemma lem1724385 (x : real) : (term231 x) = (term516 x).
Proof. exact (@lem19158 term226 (term196 x) term222). Qed.
Lemma lem1724386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724387 (x : real) : (term262 x) = (term517 x).
Proof. exact (MK_COMB (@lem1724386) (@lem1724385 x)). Qed.
Lemma lem1724388 (x : real) : (term263 x) = (term575 x).
Proof. exact (MK_COMB (@lem1724387 x) (@lem1724368 x)). Qed.
Lemma lem1724391 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1724392 (x : real) : (term265 x) = (term576 x).
Proof. exact (MK_COMB (@lem1724391 x) (@lem1724388 x)). Qed.
Lemma lem1724393 (x : real) : (term576 x) = (term577 x).
Proof. exact (@lem19158 (term516 x) (term190 x) (term574 x)). Qed.
Lemma lem1724400 (x : real) : (term578 x) = (term579 x).
Proof. exact (@lem19158 (term580 x) (term190 x) (term581 x)). Qed.
Lemma lem1724407 (x : real) : (term525 x) = (term526 x).
Proof. exact (@lem19158 (term527 x) (term190 x) (term528 x)). Qed.
Lemma lem1724408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724409 (x : real) : (term529 x) = (term530 x).
Proof. exact (MK_COMB (@lem1724408) (@lem1724407 x)). Qed.
Lemma lem1724410 (x : real) : (term577 x) = (term582 x).
Proof. exact (MK_COMB (@lem1724409 x) (@lem1724400 x)). Qed.
Lemma lem1724411 (x : real) : (term576 x) = (term582 x).
Proof. exact (TRANS (@lem1724393 x) (@lem1724410 x)). Qed.
Lemma lem1724412 (x : real) : (term265 x) = (term582 x).
Proof. exact (TRANS (@lem1724392 x) (@lem1724411 x)). Qed.
Lemma lem1724413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724414 (x : real) : (term319 x) = (term583 x).
Proof. exact (MK_COMB (@lem1724413) (@lem1724412 x)). Qed.
Lemma lem1724415 (x : real) : (term320 x) = (term724 x).
Proof. exact (MK_COMB (@lem1724414 x) (@lem1724351 x)). Qed.
Lemma lem1724418 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1724419 (x : real) : (term322 x) = (term725 x).
Proof. exact (MK_COMB (@lem1724418 x) (@lem1724415 x)). Qed.
Lemma lem1724420 (x : real) : (term725 x) = (term726 x).
Proof. exact (@lem19158 (term582 x) (term179 x) (term723 x)). Qed.
Lemma lem1724421 (x : real) : (term727 x) = (term728 x).
Proof. exact (@lem19158 (term692 x) (term179 x) (term720 x)). Qed.
Lemma lem1724428 (x : real) : (term729 x) = (term730 x).
Proof. exact (@lem19158 (term731 x) (term179 x) (term732 x)). Qed.
Lemma lem1724435 (x : real) : (term733 x) = (term734 x).
Proof. exact (@lem19158 (term709 x) (term179 x) (term710 x)). Qed.
Lemma lem1724436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724437 (x : real) : (term735 x) = (term736 x).
Proof. exact (MK_COMB (@lem1724436) (@lem1724435 x)). Qed.
Lemma lem1724438 (x : real) : (term728 x) = (term737 x).
Proof. exact (MK_COMB (@lem1724437 x) (@lem1724428 x)). Qed.
Lemma lem1724439 (x : real) : (term727 x) = (term737 x).
Proof. exact (TRANS (@lem1724421 x) (@lem1724438 x)). Qed.
Lemma lem1724440 (x : real) : (term598 x) = (term599 x).
Proof. exact (@lem19158 (term526 x) (term179 x) (term579 x)). Qed.
Lemma lem1724447 (x : real) : (term600 x) = (term601 x).
Proof. exact (@lem19158 (term602 x) (term179 x) (term603 x)). Qed.
Lemma lem1724454 (x : real) : (term604 x) = (term605 x).
Proof. exact (@lem19158 (term557 x) (term179 x) (term558 x)). Qed.
Lemma lem1724455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724456 (x : real) : (term606 x) = (term607 x).
Proof. exact (MK_COMB (@lem1724455) (@lem1724454 x)). Qed.
Lemma lem1724457 (x : real) : (term599 x) = (term608 x).
Proof. exact (MK_COMB (@lem1724456 x) (@lem1724447 x)). Qed.
Lemma lem1724458 (x : real) : (term598 x) = (term608 x).
Proof. exact (TRANS (@lem1724440 x) (@lem1724457 x)). Qed.
Lemma lem1724459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724460 (x : real) : (term609 x) = (term610 x).
Proof. exact (MK_COMB (@lem1724459) (@lem1724458 x)). Qed.
Lemma lem1724461 (x : real) : (term726 x) = (term738 x).
Proof. exact (MK_COMB (@lem1724460 x) (@lem1724439 x)). Qed.
Lemma lem1724462 (x : real) : (term725 x) = (term738 x).
Proof. exact (TRANS (@lem1724420 x) (@lem1724461 x)). Qed.
Lemma lem1724463 (x : real) : (term322 x) = (term738 x).
Proof. exact (TRANS (@lem1724419 x) (@lem1724462 x)). Qed.
Lemma lem1724464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724465 (x : real) : (term381 x) = (term739 x).
Proof. exact (MK_COMB (@lem1724464) (@lem1724463 x)). Qed.
Lemma lem1724466 (x : real) : (term382 x) = (term740 x).
Proof. exact (MK_COMB (@lem1724465 x) (@lem1724290 x)). Qed.
Lemma lem1724469 (x : real) : (term384 x) = (term384 x).
Proof. exact (eq_refl (term384 x)). Qed.
Lemma lem1724470 (x : real) : (term386 x) = (term741 x).
Proof. exact (MK_COMB (@lem1724469 x) (@lem1724466 x)). Qed.
Lemma lem1724471 (x : real) : (term741 x) = (term742 x).
Proof. exact (@lem19158 (term738 x) (term172 x) (term714 x)). Qed.
Lemma lem1724472 (x : real) : (term743 x) = (term744 x).
Proof. exact (@lem19158 (term561 x) (term172 x) (term713 x)). Qed.
Lemma lem1724473 (x : real) : (term745 x) = (term746 x).
Proof. exact (@lem19158 (term708 x) (term172 x) (term704 x)). Qed.
Lemma lem1724480 (x : real) : (term747 x) = (term748 x).
Proof. exact (@lem19158 (term749 x) (term172 x) (term750 x)). Qed.
Lemma lem1724487 (x : real) : (term751 x) = (term752 x).
Proof. exact (@lem19158 (term753 x) (term172 x) (term754 x)). Qed.
Lemma lem1724488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724489 (x : real) : (term755 x) = (term756 x).
Proof. exact (MK_COMB (@lem1724488) (@lem1724487 x)). Qed.
Lemma lem1724490 (x : real) : (term746 x) = (term757 x).
Proof. exact (MK_COMB (@lem1724489 x) (@lem1724480 x)). Qed.
Lemma lem1724491 (x : real) : (term745 x) = (term757 x).
Proof. exact (TRANS (@lem1724473 x) (@lem1724490 x)). Qed.
Lemma lem1724492 (x : real) : (term758 x) = (term759 x).
Proof. exact (@lem19158 (term556 x) (term172 x) (term552 x)). Qed.
Lemma lem1724499 (x : real) : (term760 x) = (term761 x).
Proof. exact (@lem19158 (term635 x) (term172 x) (term636 x)). Qed.
Lemma lem1724506 (x : real) : (term762 x) = (term763 x).
Proof. exact (@lem19158 (term639 x) (term172 x) (term640 x)). Qed.
Lemma lem1724507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724508 (x : real) : (term764 x) = (term765 x).
Proof. exact (MK_COMB (@lem1724507) (@lem1724506 x)). Qed.
Lemma lem1724509 (x : real) : (term759 x) = (term766 x).
Proof. exact (MK_COMB (@lem1724508 x) (@lem1724499 x)). Qed.
Lemma lem1724510 (x : real) : (term758 x) = (term766 x).
Proof. exact (TRANS (@lem1724492 x) (@lem1724509 x)). Qed.
Lemma lem1724511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724512 (x : real) : (term767 x) = (term768 x).
Proof. exact (MK_COMB (@lem1724511) (@lem1724510 x)). Qed.
Lemma lem1724513 (x : real) : (term744 x) = (term769 x).
Proof. exact (MK_COMB (@lem1724512 x) (@lem1724491 x)). Qed.
Lemma lem1724514 (x : real) : (term743 x) = (term769 x).
Proof. exact (TRANS (@lem1724472 x) (@lem1724513 x)). Qed.
Lemma lem1724515 (x : real) : (term770 x) = (term771 x).
Proof. exact (@lem19158 (term608 x) (term172 x) (term737 x)). Qed.
Lemma lem1724516 (x : real) : (term772 x) = (term773 x).
Proof. exact (@lem19158 (term734 x) (term172 x) (term730 x)). Qed.
Lemma lem1724523 (x : real) : (term774 x) = (term775 x).
Proof. exact (@lem19158 (term776 x) (term172 x) (term777 x)). Qed.
Lemma lem1724530 (x : real) : (term778 x) = (term779 x).
Proof. exact (@lem19158 (term780 x) (term172 x) (term781 x)). Qed.
Lemma lem1724531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724532 (x : real) : (term782 x) = (term783 x).
Proof. exact (MK_COMB (@lem1724531) (@lem1724530 x)). Qed.
Lemma lem1724533 (x : real) : (term773 x) = (term784 x).
Proof. exact (MK_COMB (@lem1724532 x) (@lem1724523 x)). Qed.
Lemma lem1724534 (x : real) : (term772 x) = (term784 x).
Proof. exact (TRANS (@lem1724516 x) (@lem1724533 x)). Qed.
Lemma lem1724535 (x : real) : (term785 x) = (term786 x).
Proof. exact (@lem19158 (term605 x) (term172 x) (term601 x)). Qed.
Lemma lem1724542 (x : real) : (term787 x) = (term788 x).
Proof. exact (@lem19158 (term666 x) (term172 x) (term667 x)). Qed.
Lemma lem1724549 (x : real) : (term789 x) = (term790 x).
Proof. exact (@lem19158 (term670 x) (term172 x) (term671 x)). Qed.
Lemma lem1724550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724551 (x : real) : (term791 x) = (term792 x).
Proof. exact (MK_COMB (@lem1724550) (@lem1724549 x)). Qed.
Lemma lem1724552 (x : real) : (term786 x) = (term793 x).
Proof. exact (MK_COMB (@lem1724551 x) (@lem1724542 x)). Qed.
Lemma lem1724553 (x : real) : (term785 x) = (term793 x).
Proof. exact (TRANS (@lem1724535 x) (@lem1724552 x)). Qed.
Lemma lem1724554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724555 (x : real) : (term794 x) = (term795 x).
Proof. exact (MK_COMB (@lem1724554) (@lem1724553 x)). Qed.
Lemma lem1724556 (x : real) : (term771 x) = (term796 x).
Proof. exact (MK_COMB (@lem1724555 x) (@lem1724534 x)). Qed.
Lemma lem1724557 (x : real) : (term770 x) = (term796 x).
Proof. exact (TRANS (@lem1724515 x) (@lem1724556 x)). Qed.
Lemma lem1724558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724559 (x : real) : (term797 x) = (term798 x).
Proof. exact (MK_COMB (@lem1724558) (@lem1724557 x)). Qed.
Lemma lem1724560 (x : real) : (term742 x) = (term799 x).
Proof. exact (MK_COMB (@lem1724559 x) (@lem1724514 x)). Qed.
Lemma lem1724561 (x : real) : (term741 x) = (term799 x).
Proof. exact (TRANS (@lem1724471 x) (@lem1724560 x)). Qed.
Lemma lem1724562 (x : real) : (term386 x) = (term799 x).
Proof. exact (TRANS (@lem1724470 x) (@lem1724561 x)). Qed.
Lemma lem1724563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724564 (x : real) : (term468 x) = (term800 x).
Proof. exact (MK_COMB (@lem1724563) (@lem1724562 x)). Qed.
Lemma lem1724565 (x : real) : (term469 x) = (term801 x).
Proof. exact (MK_COMB (@lem1724564 x) (@lem1724117 x)). Qed.
Lemma lem1724566 : term470 = term802.
Proof. exact (fun_ext (fun x : real => @lem1724565 x)). Qed.
Lemma lem1724567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1724568 : term471 = term803.
Proof. exact (MK_COMB (@lem1724567) (@lem1724566)). Qed.
Lemma lem1724569 : term14 = term803.
Proof. exact (TRANS (@lem1723672) (@lem1724568)). Qed.
Lemma lem1724571 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1724572 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1724571 x term76). Qed.
Lemma lem1724579 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1724580 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724581 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1724580) (@lem1724579 x)). Qed.
Lemma lem1724582 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724583 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1724581 x) (@lem1724582)). Qed.
Lemma lem1724596 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1724597 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1724596 x) (@lem1724583 x)). Qed.
Lemma lem1724598 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1724572 x) (@lem1724597 x)). Qed.
Lemma lem1724599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724600 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1724599) (@lem1724598 x)). Qed.
Lemma lem1724601 (x : real) : (term670 x) = (term670 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1724602 (x : real) : (term812 x) = (term813 x).
Proof. exact (MK_COMB (@lem1724600 x) (@lem1724601 x)). Qed.
Lemma lem1724603 (x : real) : (term814 x) = (term813 x).
Proof. exact (eq_refl (term814 x)). Qed.
Lemma lem1724604 (x : real) : (term813 x) = (term814 x).
Proof. exact (SYM (@lem1724603 x)). Qed.
Lemma lem1724605 (x : real) : (term814 x) = (term815 x).
Proof. exact (@lem1482981 (term816 x) x). Qed.
Lemma lem1724606 (x : real) : (term813 x) = (term815 x).
Proof. exact (TRANS (@lem1724604 x) (@lem1724605 x)). Qed.
Lemma lem1724607 (x : real) : (term817 x) = (term818 x).
Proof. exact (eq_refl (term817 x)). Qed.
Lemma lem1724608 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1724609 (x : real) : (term820 x) = (term821 x).
Proof. exact (MK_COMB (@lem1724608 x) (@lem1724607 x)). Qed.
Lemma lem1724610 (x : real) : (term822 x) = (term823 x).
Proof. exact (eq_refl (term822 x)). Qed.
Lemma lem1724611 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1724612 (x : real) : (term824 x) = (term825 x).
Proof. exact (MK_COMB (@lem1724611 x) (@lem1724610 x)). Qed.
Lemma lem1724613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724614 (x : real) : (term826 x) = (term827 x).
Proof. exact (MK_COMB (@lem1724613) (@lem1724612 x)). Qed.
Lemma lem1724615 (x : real) : (term815 x) = (term828 x).
Proof. exact (MK_COMB (@lem1724614 x) (@lem1724609 x)). Qed.
Lemma lem1724616 (x : real) : (term829 x) = (term829 x).
Proof. exact (eq_refl (term829 x)). Qed.
Lemma lem1724617 (x : real) : ((term813 x) = (term815 x)) = ((term813 x) = (term828 x)).
Proof. exact (MK_COMB (@lem1724616 x) (@lem1724615 x)). Qed.
Lemma lem1724618 (x : real) : (term813 x) = (term828 x).
Proof. exact (EQ_MP (@lem1724617 x) (@lem1724606 x)). Qed.
Lemma lem1724619 (x : real) : (term326 x) = (term324 x).
Proof. exact (@lem1483527 x term76). Qed.
Lemma lem1724625 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1724627 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724628 : term184 = term76.
Proof. exact (@lem1724627 term185). Qed.
Lemma lem1724629 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1724630 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1724629 x) (@lem1724628)). Qed.
Lemma lem1724631 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1724632 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1724630 x) (@lem1724631 x)). Qed.
Lemma lem1724634 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1724625 x) (@lem1724632 x)). Qed.
Lemma lem1724635 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1724636 (x : real) : (term325 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1724635) (@lem1724634 x)). Qed.
Lemma lem1724637 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724638 (x : real) : (term324 x) = (term326 x).
Proof. exact (MK_COMB (@lem1724636 x) (@lem1724637)). Qed.
Lemma lem1724639 (x : real) : (term326 x) = (term326 x).
Proof. exact (TRANS (@lem1724619 x) (@lem1724638 x)). Qed.
Lemma lem1724640 (x : real) : (term179 x) = (term830 x).
Proof. exact (@lem1483525 (term176 x) term76). Qed.
Lemma lem1724652 (x : real) : (term831 x) = (term832 x).
Proof. exact (@lem1483519 (term176 x) term76). Qed.
Lemma lem1724654 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724655 : term184 = term76.
Proof. exact (@lem1724654 term185). Qed.
Lemma lem1724656 (x : real) : (term833 x) = (term833 x).
Proof. exact (eq_refl (term833 x)). Qed.
Lemma lem1724657 (x : real) : (term832 x) = (term834 x).
Proof. exact (MK_COMB (@lem1724656 x) (@lem1724655)). Qed.
Lemma lem1724658 (x : real) : (term834 x) = (term176 x).
Proof. exact (@lem1483450 (term176 x)). Qed.
Lemma lem1724659 (x : real) : (term832 x) = (term176 x).
Proof. exact (TRANS (@lem1724657 x) (@lem1724658 x)). Qed.
Lemma lem1724661 (x : real) : (term831 x) = (term176 x).
Proof. exact (TRANS (@lem1724652 x) (@lem1724659 x)). Qed.
Lemma lem1724662 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724663 (x : real) : (term835 x) = (term178 x).
Proof. exact (MK_COMB (@lem1724662) (@lem1724661 x)). Qed.
Lemma lem1724664 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724665 (x : real) : (term830 x) = (term179 x).
Proof. exact (MK_COMB (@lem1724663 x) (@lem1724664)). Qed.
Lemma lem1724666 (x : real) : (term179 x) = (term179 x).
Proof. exact (TRANS (@lem1724640 x) (@lem1724665 x)). Qed.
Lemma lem1724667 (x : real) : (term196 x) = (term191 x).
Proof. exact (@lem1483525 x term76). Qed.
Lemma lem1724673 (x : real) : (term192 x) = (term193 x).
Proof. exact (@lem1483519 x term76). Qed.
Lemma lem1724675 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724676 : term184 = term76.
Proof. exact (@lem1724675 term185). Qed.
Lemma lem1724677 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1724678 (x : real) : (term193 x) = (term194 x).
Proof. exact (MK_COMB (@lem1724677 x) (@lem1724676)). Qed.
Lemma lem1724679 (x : real) : (term194 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1724680 (x : real) : (term193 x) = x.
Proof. exact (TRANS (@lem1724678 x) (@lem1724679 x)). Qed.
Lemma lem1724682 (x : real) : (term192 x) = x.
Proof. exact (TRANS (@lem1724673 x) (@lem1724680 x)). Qed.
Lemma lem1724683 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724684 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1724683) (@lem1724682 x)). Qed.
Lemma lem1724685 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724686 (x : real) : (term191 x) = (term196 x).
Proof. exact (MK_COMB (@lem1724684 x) (@lem1724685)). Qed.
Lemma lem1724687 (x : real) : (term196 x) = (term196 x).
Proof. exact (TRANS (@lem1724667 x) (@lem1724686 x)). Qed.
Lemma lem1724688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724689 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724688) (@lem1724666 x)). Qed.
Lemma lem1724690 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1724689 x) (@lem1724687 x)). Qed.
Lemma lem1724691 : term226 = term836.
Proof. exact (@lem1483525 term208 term76). Qed.
Lemma lem1724703 : term837 = term838.
Proof. exact (@lem1483519 term208 term76). Qed.
Lemma lem1724705 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724706 : term184 = term76.
Proof. exact (@lem1724705 term185). Qed.
Lemma lem1724707 : term839 = term839.
Proof. exact (eq_refl term839). Qed.
Lemma lem1724708 : term838 = term840.
Proof. exact (MK_COMB (@lem1724707) (@lem1724706)). Qed.
Lemma lem1724709 : term840 = term208.
Proof. exact (@lem1483450 term208). Qed.
Lemma lem1724710 : term838 = term208.
Proof. exact (TRANS (@lem1724708) (@lem1724709)). Qed.
Lemma lem1724712 : term837 = term208.
Proof. exact (TRANS (@lem1724703) (@lem1724710)). Qed.
Lemma lem1724713 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724714 : term841 = term224.
Proof. exact (MK_COMB (@lem1724713) (@lem1724712)). Qed.
Lemma lem1724715 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724716 : term836 = term226.
Proof. exact (MK_COMB (@lem1724714) (@lem1724715)). Qed.
Lemma lem1724717 : term226 = term226.
Proof. exact (TRANS (@lem1724691) (@lem1724716)). Qed.
Lemma lem1724718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724719 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1724718) (@lem1724687 x)). Qed.
Lemma lem1724720 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1724719 x) (@lem1724717)). Qed.
Lemma lem1724721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724722 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1724721) (@lem1724687 x)). Qed.
Lemma lem1724723 (x : real) : (term842 x) = (term842 x).
Proof. exact (MK_COMB (@lem1724722 x) (@lem1724720 x)). Qed.
Lemma lem1724724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724725 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724724) (@lem1724666 x)). Qed.
Lemma lem1724726 (x : real) : (term843 x) = (term843 x).
Proof. exact (MK_COMB (@lem1724725 x) (@lem1724723 x)). Qed.
Lemma lem1724727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724728 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1724727) (@lem1724690 x)). Qed.
Lemma lem1724729 (x : real) : (term823 x) = (term823 x).
Proof. exact (MK_COMB (@lem1724728 x) (@lem1724726 x)). Qed.
Lemma lem1724730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724731 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1724730) (@lem1724639 x)). Qed.
Lemma lem1724732 (x : real) : (term825 x) = (term825 x).
Proof. exact (MK_COMB (@lem1724731 x) (@lem1724729 x)). Qed.
Lemma lem1724733 (x : real) : (term844 x) = (term173 x).
Proof. exact (@lem1483525 term76 x). Qed.
Lemma lem1724739 (x : real) : (term174 x) = (term175 x).
Proof. exact (@lem1483519 term76 x). Qed.
Lemma lem1724744 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483448 (term176 x)). Qed.
Lemma lem1724746 (x : real) : (term174 x) = (term176 x).
Proof. exact (TRANS (@lem1724739 x) (@lem1724744 x)). Qed.
Lemma lem1724747 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724748 (x : real) : (term177 x) = (term178 x).
Proof. exact (MK_COMB (@lem1724747) (@lem1724746 x)). Qed.
Lemma lem1724749 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724750 (x : real) : (term173 x) = (term179 x).
Proof. exact (MK_COMB (@lem1724748 x) (@lem1724749)). Qed.
Lemma lem1724751 (x : real) : (term844 x) = (term179 x).
Proof. exact (TRANS (@lem1724733 x) (@lem1724750 x)). Qed.
Lemma lem1724752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724753 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724752) (@lem1724666 x)). Qed.
Lemma lem1724754 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1724753 x) (@lem1724687 x)). Qed.
Lemma lem1724755 (x : real) : (term845 x) = (term846 x).
Proof. exact (@lem1483525 (real_neg x) term76). Qed.
Lemma lem1724756 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724763 (x : real) : (real_neg x) = (term176 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1724764 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1724765 (x : real) : (term847 x) = (term848 x).
Proof. exact (MK_COMB (@lem1724764) (@lem1724763 x)). Qed.
Lemma lem1724766 (x : real) : (term849 x) = (term831 x).
Proof. exact (MK_COMB (@lem1724765 x) (@lem1724756)). Qed.
Lemma lem1724767 (x : real) : (term831 x) = (term832 x).
Proof. exact (@lem1483519 (term176 x) term76). Qed.
Lemma lem1724769 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724770 : term184 = term76.
Proof. exact (@lem1724769 term185). Qed.
Lemma lem1724771 (x : real) : (term833 x) = (term833 x).
Proof. exact (eq_refl (term833 x)). Qed.
Lemma lem1724772 (x : real) : (term832 x) = (term834 x).
Proof. exact (MK_COMB (@lem1724771 x) (@lem1724770)). Qed.
Lemma lem1724773 (x : real) : (term834 x) = (term176 x).
Proof. exact (@lem1483450 (term176 x)). Qed.
Lemma lem1724774 (x : real) : (term832 x) = (term176 x).
Proof. exact (TRANS (@lem1724772 x) (@lem1724773 x)). Qed.
Lemma lem1724775 (x : real) : (term831 x) = (term176 x).
Proof. exact (TRANS (@lem1724767 x) (@lem1724774 x)). Qed.
Lemma lem1724776 (x : real) : (term849 x) = (term176 x).
Proof. exact (TRANS (@lem1724766 x) (@lem1724775 x)). Qed.
Lemma lem1724777 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724778 (x : real) : (term850 x) = (term178 x).
Proof. exact (MK_COMB (@lem1724777) (@lem1724776 x)). Qed.
Lemma lem1724779 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724780 (x : real) : (term846 x) = (term179 x).
Proof. exact (MK_COMB (@lem1724778 x) (@lem1724779)). Qed.
Lemma lem1724781 (x : real) : (term845 x) = (term179 x).
Proof. exact (TRANS (@lem1724755 x) (@lem1724780 x)). Qed.
Lemma lem1724782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724783 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1724782) (@lem1724687 x)). Qed.
Lemma lem1724784 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1724783 x) (@lem1724717)). Qed.
Lemma lem1724785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724786 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724785) (@lem1724781 x)). Qed.
Lemma lem1724787 (x : real) : (term852 x) = (term853 x).
Proof. exact (MK_COMB (@lem1724786 x) (@lem1724784 x)). Qed.
Lemma lem1724788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724789 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724788) (@lem1724666 x)). Qed.
Lemma lem1724790 (x : real) : (term854 x) = (term855 x).
Proof. exact (MK_COMB (@lem1724789 x) (@lem1724787 x)). Qed.
Lemma lem1724791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724792 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1724791) (@lem1724754 x)). Qed.
Lemma lem1724793 (x : real) : (term818 x) = (term856 x).
Proof. exact (MK_COMB (@lem1724792 x) (@lem1724790 x)). Qed.
Lemma lem1724794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724795 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724794) (@lem1724751 x)). Qed.
Lemma lem1724796 (x : real) : (term821 x) = (term857 x).
Proof. exact (MK_COMB (@lem1724795 x) (@lem1724793 x)). Qed.
Lemma lem1724797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724798 (x : real) : (term827 x) = (term827 x).
Proof. exact (MK_COMB (@lem1724797) (@lem1724732 x)). Qed.
Lemma lem1724799 (x : real) : (term828 x) = (term858 x).
Proof. exact (MK_COMB (@lem1724798 x) (@lem1724796 x)). Qed.
Lemma lem1724800 (x : real) : (term813 x) = (term858 x).
Proof. exact (TRANS (@lem1724618 x) (@lem1724799 x)). Qed.
Lemma lem1724802 (x : real) : (term859 x) = (term857 x).
Proof. exact (eq_refl (term859 x)). Qed.
Lemma lem1724803 (x : real) : (term857 x) = (term859 x).
Proof. exact (SYM (@lem1724802 x)). Qed.
Lemma lem1724804 (x : real) : (term859 x) = (term860 x).
Proof. exact (@lem1482981 (term861 x) term24). Qed.
Lemma lem1724805 (x : real) : (term857 x) = (term860 x).
Proof. exact (TRANS (@lem1724803 x) (@lem1724804 x)). Qed.
Lemma lem1724806 (x : real) : (term862 x) = (term863 x).
Proof. exact (eq_refl (term862 x)). Qed.
Lemma lem1724807 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1724808 (x : real) : (term865 x) = (term866 x).
Proof. exact (MK_COMB (@lem1724807) (@lem1724806 x)). Qed.
Lemma lem1724809 (x : real) : (term867 x) = (term868 x).
Proof. exact (eq_refl (term867 x)). Qed.
Lemma lem1724810 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1724811 (x : real) : (term870 x) = (term871 x).
Proof. exact (MK_COMB (@lem1724810) (@lem1724809 x)). Qed.
Lemma lem1724812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724813 (x : real) : (term872 x) = (term873 x).
Proof. exact (MK_COMB (@lem1724812) (@lem1724811 x)). Qed.
Lemma lem1724814 (x : real) : (term860 x) = (term874 x).
Proof. exact (MK_COMB (@lem1724813 x) (@lem1724808 x)). Qed.
Lemma lem1724815 (x : real) : (term875 x) = (term875 x).
Proof. exact (eq_refl (term875 x)). Qed.
Lemma lem1724816 (x : real) : ((term857 x) = (term860 x)) = ((term857 x) = (term874 x)).
Proof. exact (MK_COMB (@lem1724815 x) (@lem1724814 x)). Qed.
Lemma lem1724817 (x : real) : (term857 x) = (term874 x).
Proof. exact (EQ_MP (@lem1724816 x) (@lem1724805 x)). Qed.
Lemma lem1724818 : term876 = term877.
Proof. exact (@lem1483527 term24 term76). Qed.
Lemma lem1724824 : term878 = term879.
Proof. exact (@lem1483519 term24 term76). Qed.
Lemma lem1724826 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724827 : term184 = term76.
Proof. exact (@lem1724826 term185). Qed.
Lemma lem1724828 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1724829 : term879 = term881.
Proof. exact (MK_COMB (@lem1724828) (@lem1724827)). Qed.
Lemma lem1724830 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1724831 : term879 = term24.
Proof. exact (TRANS (@lem1724829) (@lem1724830)). Qed.
Lemma lem1724833 : term878 = term24.
Proof. exact (TRANS (@lem1724824) (@lem1724831)). Qed.
Lemma lem1724834 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1724835 : term882 = term883.
Proof. exact (MK_COMB (@lem1724834) (@lem1724833)). Qed.
Lemma lem1724836 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724837 : term877 = term876.
Proof. exact (MK_COMB (@lem1724835) (@lem1724836)). Qed.
Lemma lem1724838 : term876 = term876.
Proof. exact (TRANS (@lem1724818) (@lem1724837)). Qed.
Lemma lem1724839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724840 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724839) (@lem1724666 x)). Qed.
Lemma lem1724841 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1724840 x) (@lem1724687 x)). Qed.
Lemma lem1724842 : term884 = term885.
Proof. exact (@lem1483525 term886 term76). Qed.
Lemma lem1724843 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724850 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1724852 : term886 = term76.
Proof. exact (@lem1724850 term185). Qed.
Lemma lem1724853 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1724854 : term888 = term889.
Proof. exact (MK_COMB (@lem1724853) (@lem1724852)). Qed.
Lemma lem1724855 : term890 = term891.
Proof. exact (MK_COMB (@lem1724854) (@lem1724843)). Qed.
Lemma lem1724856 : term891 = term892.
Proof. exact (@lem1483519 term76 term76). Qed.
Lemma lem1724858 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724859 : term184 = term76.
Proof. exact (@lem1724858 term185). Qed.
Lemma lem1724860 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1724861 : term892 = term894.
Proof. exact (MK_COMB (@lem1724860) (@lem1724859)). Qed.
Lemma lem1724862 : term894 = term76.
Proof. exact (@lem1483448 term76). Qed.
Lemma lem1724863 : term892 = term76.
Proof. exact (TRANS (@lem1724861) (@lem1724862)). Qed.
Lemma lem1724864 : term891 = term76.
Proof. exact (TRANS (@lem1724856) (@lem1724863)). Qed.
Lemma lem1724865 : term890 = term76.
Proof. exact (TRANS (@lem1724855) (@lem1724864)). Qed.
Lemma lem1724866 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724867 : term895 = term896.
Proof. exact (MK_COMB (@lem1724866) (@lem1724865)). Qed.
Lemma lem1724868 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724869 : term885 = term897.
Proof. exact (MK_COMB (@lem1724867) (@lem1724868)). Qed.
Lemma lem1724870 : term884 = term897.
Proof. exact (TRANS (@lem1724842) (@lem1724869)). Qed.
Lemma lem1724871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724872 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1724871) (@lem1724687 x)). Qed.
Lemma lem1724873 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1724872 x) (@lem1724870)). Qed.
Lemma lem1724874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724875 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724874) (@lem1724666 x)). Qed.
Lemma lem1724876 (x : real) : (term900 x) = (term901 x).
Proof. exact (MK_COMB (@lem1724875 x) (@lem1724873 x)). Qed.
Lemma lem1724877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724878 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724877) (@lem1724666 x)). Qed.
Lemma lem1724879 (x : real) : (term902 x) = (term903 x).
Proof. exact (MK_COMB (@lem1724878 x) (@lem1724876 x)). Qed.
Lemma lem1724880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724881 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1724880) (@lem1724841 x)). Qed.
Lemma lem1724882 (x : real) : (term904 x) = (term905 x).
Proof. exact (MK_COMB (@lem1724881 x) (@lem1724879 x)). Qed.
Lemma lem1724883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724884 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724883) (@lem1724666 x)). Qed.
Lemma lem1724885 (x : real) : (term868 x) = (term906 x).
Proof. exact (MK_COMB (@lem1724884 x) (@lem1724882 x)). Qed.
Lemma lem1724886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724887 : term869 = term869.
Proof. exact (MK_COMB (@lem1724886) (@lem1724838)). Qed.
Lemma lem1724888 (x : real) : (term871 x) = (term907 x).
Proof. exact (MK_COMB (@lem1724887) (@lem1724885 x)). Qed.
Lemma lem1724889 : term908 = term909.
Proof. exact (@lem1483525 term76 term24). Qed.
Lemma lem1724895 : term910 = term911.
Proof. exact (@lem1483519 term76 term24). Qed.
Lemma lem1724897 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1724898 : term202 = term203.
Proof. exact (@lem1724897 term185 term185). Qed.
Lemma lem1724899 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1724900 : term205 = term185.
Proof. exact (EQ_MP (@lem1724899) (@lem940073)). Qed.
Lemma lem1724901 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1724902 : term206 = term24.
Proof. exact (MK_COMB (@lem1724901) (@lem1724900)). Qed.
Lemma lem1724903 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1724904 : term203 = term73.
Proof. exact (MK_COMB (@lem1724903) (@lem1724902)). Qed.
Lemma lem1724905 : term202 = term73.
Proof. exact (TRANS (@lem1724898) (@lem1724904)). Qed.
Lemma lem1724906 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1724907 : term911 = term912.
Proof. exact (MK_COMB (@lem1724906) (@lem1724905)). Qed.
Lemma lem1724908 : term912 = term73.
Proof. exact (@lem1483448 term73). Qed.
Lemma lem1724909 : term911 = term73.
Proof. exact (TRANS (@lem1724907) (@lem1724908)). Qed.
Lemma lem1724911 : term910 = term73.
Proof. exact (TRANS (@lem1724895) (@lem1724909)). Qed.
Lemma lem1724912 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724913 : term913 = term914.
Proof. exact (MK_COMB (@lem1724912) (@lem1724911)). Qed.
Lemma lem1724914 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724915 : term909 = term915.
Proof. exact (MK_COMB (@lem1724913) (@lem1724914)). Qed.
Lemma lem1724916 : term908 = term915.
Proof. exact (TRANS (@lem1724889) (@lem1724915)). Qed.
Lemma lem1724917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724918 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724917) (@lem1724666 x)). Qed.
Lemma lem1724919 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1724918 x) (@lem1724687 x)). Qed.
Lemma lem1724920 : term916 = term917.
Proof. exact (@lem1483525 term918 term76). Qed.
Lemma lem1724921 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724927 : term918 = term919.
Proof. exact (@lem1367763 term185 term185). Qed.
Lemma lem1724928 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1724929 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1724930 : term922 = term923.
Proof. exact (EQ_MP (@lem1724929) (@lem1724928)). Qed.
Lemma lem1724931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1724932 : term924 = term925.
Proof. exact (MK_COMB (@lem1724931) (@lem1724930)). Qed.
Lemma lem1724933 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1724934 : term919 = term926.
Proof. exact (MK_COMB (@lem1724933) (@lem1724932)). Qed.
Lemma lem1724936 : term918 = term926.
Proof. exact (TRANS (@lem1724927) (@lem1724934)). Qed.
Lemma lem1724937 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1724938 : term927 = term928.
Proof. exact (MK_COMB (@lem1724937) (@lem1724936)). Qed.
Lemma lem1724939 : term929 = term930.
Proof. exact (MK_COMB (@lem1724938) (@lem1724921)). Qed.
Lemma lem1724940 : term930 = term931.
Proof. exact (@lem1483519 term926 term76). Qed.
Lemma lem1724942 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1724943 : term184 = term76.
Proof. exact (@lem1724942 term185). Qed.
Lemma lem1724944 : term932 = term932.
Proof. exact (eq_refl term932). Qed.
Lemma lem1724945 : term931 = term933.
Proof. exact (MK_COMB (@lem1724944) (@lem1724943)). Qed.
Lemma lem1724946 : term933 = term926.
Proof. exact (@lem1483450 term926). Qed.
Lemma lem1724947 : term931 = term926.
Proof. exact (TRANS (@lem1724945) (@lem1724946)). Qed.
Lemma lem1724948 : term930 = term926.
Proof. exact (TRANS (@lem1724940) (@lem1724947)). Qed.
Lemma lem1724949 : term929 = term926.
Proof. exact (TRANS (@lem1724939) (@lem1724948)). Qed.
Lemma lem1724950 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1724951 : term934 = term935.
Proof. exact (MK_COMB (@lem1724950) (@lem1724949)). Qed.
Lemma lem1724952 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1724953 : term917 = term936.
Proof. exact (MK_COMB (@lem1724951) (@lem1724952)). Qed.
Lemma lem1724954 : term916 = term936.
Proof. exact (TRANS (@lem1724920) (@lem1724953)). Qed.
Lemma lem1724955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724956 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1724955) (@lem1724687 x)). Qed.
Lemma lem1724957 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1724956 x) (@lem1724954)). Qed.
Lemma lem1724958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724959 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724958) (@lem1724666 x)). Qed.
Lemma lem1724960 (x : real) : (term939 x) = (term940 x).
Proof. exact (MK_COMB (@lem1724959 x) (@lem1724957 x)). Qed.
Lemma lem1724961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724962 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724961) (@lem1724666 x)). Qed.
Lemma lem1724963 (x : real) : (term941 x) = (term942 x).
Proof. exact (MK_COMB (@lem1724962 x) (@lem1724960 x)). Qed.
Lemma lem1724964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724965 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1724964) (@lem1724919 x)). Qed.
Lemma lem1724966 (x : real) : (term943 x) = (term944 x).
Proof. exact (MK_COMB (@lem1724965 x) (@lem1724963 x)). Qed.
Lemma lem1724967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724968 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1724967) (@lem1724666 x)). Qed.
Lemma lem1724969 (x : real) : (term863 x) = (term945 x).
Proof. exact (MK_COMB (@lem1724968 x) (@lem1724966 x)). Qed.
Lemma lem1724970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1724971 : term864 = term946.
Proof. exact (MK_COMB (@lem1724970) (@lem1724916)). Qed.
Lemma lem1724972 (x : real) : (term866 x) = (term947 x).
Proof. exact (MK_COMB (@lem1724971) (@lem1724969 x)). Qed.
Lemma lem1724973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1724974 (x : real) : (term873 x) = (term948 x).
Proof. exact (MK_COMB (@lem1724973) (@lem1724888 x)). Qed.
Lemma lem1724975 (x : real) : (term874 x) = (term949 x).
Proof. exact (MK_COMB (@lem1724974 x) (@lem1724972 x)). Qed.
Lemma lem1724987 (x : real) : (term857 x) = (term949 x).
Proof. exact (TRANS (@lem1724817 x) (@lem1724975 x)). Qed.
Lemma lem1724989 (x : real) : (term950 x) = (term825 x).
Proof. exact (eq_refl (term950 x)). Qed.
Lemma lem1724990 (x : real) : (term825 x) = (term950 x).
Proof. exact (SYM (@lem1724989 x)). Qed.
Lemma lem1724991 (x : real) : (term950 x) = (term951 x).
Proof. exact (@lem1482981 (term952 x) term24). Qed.
Lemma lem1724992 (x : real) : (term825 x) = (term951 x).
Proof. exact (TRANS (@lem1724990 x) (@lem1724991 x)). Qed.
Lemma lem1724993 (x : real) : (term953 x) = (term954 x).
Proof. exact (eq_refl (term953 x)). Qed.
Lemma lem1724994 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1724995 (x : real) : (term955 x) = (term956 x).
Proof. exact (MK_COMB (@lem1724994) (@lem1724993 x)). Qed.
Lemma lem1724996 (x : real) : (term957 x) = (term958 x).
Proof. exact (eq_refl (term957 x)). Qed.
Lemma lem1724997 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1724998 (x : real) : (term959 x) = (term960 x).
Proof. exact (MK_COMB (@lem1724997) (@lem1724996 x)). Qed.
Lemma lem1724999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725000 (x : real) : (term961 x) = (term962 x).
Proof. exact (MK_COMB (@lem1724999) (@lem1724998 x)). Qed.
Lemma lem1725001 (x : real) : (term951 x) = (term963 x).
Proof. exact (MK_COMB (@lem1725000 x) (@lem1724995 x)). Qed.
Lemma lem1725002 (x : real) : (term964 x) = (term964 x).
Proof. exact (eq_refl (term964 x)). Qed.
Lemma lem1725003 (x : real) : ((term825 x) = (term951 x)) = ((term825 x) = (term963 x)).
Proof. exact (MK_COMB (@lem1725002 x) (@lem1725001 x)). Qed.
Lemma lem1725004 (x : real) : (term825 x) = (term963 x).
Proof. exact (EQ_MP (@lem1725003 x) (@lem1724992 x)). Qed.
Lemma lem1725005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725006 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725005) (@lem1724666 x)). Qed.
Lemma lem1725007 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725006 x) (@lem1724687 x)). Qed.
Lemma lem1725008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725009 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725008) (@lem1724687 x)). Qed.
Lemma lem1725010 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1725009 x) (@lem1724870)). Qed.
Lemma lem1725011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725012 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725011) (@lem1724687 x)). Qed.
Lemma lem1725013 (x : real) : (term965 x) = (term966 x).
Proof. exact (MK_COMB (@lem1725012 x) (@lem1725010 x)). Qed.
Lemma lem1725014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725015 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725014) (@lem1724666 x)). Qed.
Lemma lem1725016 (x : real) : (term967 x) = (term968 x).
Proof. exact (MK_COMB (@lem1725015 x) (@lem1725013 x)). Qed.
Lemma lem1725017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725018 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725017) (@lem1725007 x)). Qed.
Lemma lem1725019 (x : real) : (term969 x) = (term970 x).
Proof. exact (MK_COMB (@lem1725018 x) (@lem1725016 x)). Qed.
Lemma lem1725020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725021 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1725020) (@lem1724639 x)). Qed.
Lemma lem1725022 (x : real) : (term958 x) = (term971 x).
Proof. exact (MK_COMB (@lem1725021 x) (@lem1725019 x)). Qed.
Lemma lem1725023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725024 : term869 = term869.
Proof. exact (MK_COMB (@lem1725023) (@lem1724838)). Qed.
Lemma lem1725025 (x : real) : (term960 x) = (term972 x).
Proof. exact (MK_COMB (@lem1725024) (@lem1725022 x)). Qed.
Lemma lem1725026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725027 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725026) (@lem1724666 x)). Qed.
Lemma lem1725028 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725027 x) (@lem1724687 x)). Qed.
Lemma lem1725029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725030 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725029) (@lem1724687 x)). Qed.
Lemma lem1725031 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1725030 x) (@lem1724954)). Qed.
Lemma lem1725032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725033 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725032) (@lem1724687 x)). Qed.
Lemma lem1725034 (x : real) : (term973 x) = (term974 x).
Proof. exact (MK_COMB (@lem1725033 x) (@lem1725031 x)). Qed.
Lemma lem1725035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725036 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725035) (@lem1724666 x)). Qed.
Lemma lem1725037 (x : real) : (term975 x) = (term976 x).
Proof. exact (MK_COMB (@lem1725036 x) (@lem1725034 x)). Qed.
Lemma lem1725038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725039 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725038) (@lem1725028 x)). Qed.
Lemma lem1725040 (x : real) : (term977 x) = (term978 x).
Proof. exact (MK_COMB (@lem1725039 x) (@lem1725037 x)). Qed.
Lemma lem1725041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725042 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1725041) (@lem1724639 x)). Qed.
Lemma lem1725043 (x : real) : (term954 x) = (term979 x).
Proof. exact (MK_COMB (@lem1725042 x) (@lem1725040 x)). Qed.
Lemma lem1725044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725045 : term864 = term946.
Proof. exact (MK_COMB (@lem1725044) (@lem1724916)). Qed.
Lemma lem1725046 (x : real) : (term956 x) = (term980 x).
Proof. exact (MK_COMB (@lem1725045) (@lem1725043 x)). Qed.
Lemma lem1725047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725048 (x : real) : (term962 x) = (term981 x).
Proof. exact (MK_COMB (@lem1725047) (@lem1725025 x)). Qed.
Lemma lem1725049 (x : real) : (term963 x) = (term982 x).
Proof. exact (MK_COMB (@lem1725048 x) (@lem1725046 x)). Qed.
Lemma lem1725061 (x : real) : (term825 x) = (term982 x).
Proof. exact (TRANS (@lem1725004 x) (@lem1725049 x)). Qed.
Lemma lem1725062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725063 (x : real) : (term827 x) = (term983 x).
Proof. exact (MK_COMB (@lem1725062) (@lem1725061 x)). Qed.
Lemma lem1725064 (x : real) : (term858 x) = (term984 x).
Proof. exact (MK_COMB (@lem1725063 x) (@lem1724987 x)). Qed.
Lemma lem1725065 (x : real) : (term813 x) = (term984 x).
Proof. exact (TRANS (@lem1724800 x) (@lem1725064 x)). Qed.
Lemma lem1725066 (x : real) : (term812 x) = (term984 x).
Proof. exact (TRANS (@lem1724602 x) (@lem1725065 x)). Qed.
Lemma lem1725068 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1725069 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1725068 x term76). Qed.
Lemma lem1725076 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1725077 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725078 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1725077) (@lem1725076 x)). Qed.
Lemma lem1725079 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725080 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1725078 x) (@lem1725079)). Qed.
Lemma lem1725093 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1725094 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725093 x) (@lem1725080 x)). Qed.
Lemma lem1725095 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1725069 x) (@lem1725094 x)). Qed.
Lemma lem1725096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725097 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725096) (@lem1725095 x)). Qed.
Lemma lem1725099 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1725100 : term222 = term987.
Proof. exact (@lem1725099 term24 term24 term76). Qed.
Lemma lem1725107 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1725110 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1725111 : term989 = term990.
Proof. exact (MK_COMB (@lem1725110) (@lem1725107)). Qed.
Lemma lem1725112 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1725113 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1725114 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1725115 : term922 = term923.
Proof. exact (EQ_MP (@lem1725114) (@lem1725113)). Qed.
Lemma lem1725116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1725117 : term924 = term925.
Proof. exact (MK_COMB (@lem1725116) (@lem1725115)). Qed.
Lemma lem1725118 : term990 = term925.
Proof. exact (TRANS (@lem1725112) (@lem1725117)). Qed.
Lemma lem1725119 : term989 = term925.
Proof. exact (TRANS (@lem1725111) (@lem1725118)). Qed.
Lemma lem1725120 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725121 : term991 = term992.
Proof. exact (MK_COMB (@lem1725120) (@lem1725119)). Qed.
Lemma lem1725122 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725123 : term993 = term994.
Proof. exact (MK_COMB (@lem1725121) (@lem1725122)). Qed.
Lemma lem1725130 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1725133 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1725134 : term995 = term886.
Proof. exact (MK_COMB (@lem1725133) (@lem1725130)). Qed.
Lemma lem1725136 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1725137 : term886 = term76.
Proof. exact (@lem1725136 term185). Qed.
Lemma lem1725138 : term995 = term76.
Proof. exact (TRANS (@lem1725134) (@lem1725137)). Qed.
Lemma lem1725139 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725140 : term996 = term896.
Proof. exact (MK_COMB (@lem1725139) (@lem1725138)). Qed.
Lemma lem1725141 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725142 : term997 = term897.
Proof. exact (MK_COMB (@lem1725140) (@lem1725141)). Qed.
Lemma lem1725143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725144 : term998 = term999.
Proof. exact (MK_COMB (@lem1725143) (@lem1725142)). Qed.
Lemma lem1725145 : term987 = term1000.
Proof. exact (MK_COMB (@lem1725144) (@lem1725123)). Qed.
Lemma lem1725146 : term222 = term1000.
Proof. exact (TRANS (@lem1725100) (@lem1725145)). Qed.
Lemma lem1725147 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1725148 (x : real) : (term528 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1725147 x) (@lem1725146)). Qed.
Lemma lem1725149 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1725150 (x : real) : (term558 x) = (term1002 x).
Proof. exact (MK_COMB (@lem1725149 x) (@lem1725148 x)). Qed.
Lemma lem1725151 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1725152 (x : real) : (term671 x) = (term1003 x).
Proof. exact (MK_COMB (@lem1725151 x) (@lem1725150 x)). Qed.
Lemma lem1725153 (x : real) : (term1004 x) = (term1005 x).
Proof. exact (MK_COMB (@lem1725097 x) (@lem1725152 x)). Qed.
Lemma lem1725154 (x : real) : (term1006 x) = (term1005 x).
Proof. exact (eq_refl (term1006 x)). Qed.
Lemma lem1725155 (x : real) : (term1005 x) = (term1006 x).
Proof. exact (SYM (@lem1725154 x)). Qed.
Lemma lem1725156 (x : real) : (term1006 x) = (term1007 x).
Proof. exact (@lem1482981 (term1008 x) x). Qed.
Lemma lem1725157 (x : real) : (term1005 x) = (term1007 x).
Proof. exact (TRANS (@lem1725155 x) (@lem1725156 x)). Qed.
Lemma lem1725158 (x : real) : (term1009 x) = (term1010 x).
Proof. exact (eq_refl (term1009 x)). Qed.
Lemma lem1725159 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1725160 (x : real) : (term1011 x) = (term1012 x).
Proof. exact (MK_COMB (@lem1725159 x) (@lem1725158 x)). Qed.
Lemma lem1725161 (x : real) : (term1013 x) = (term1014 x).
Proof. exact (eq_refl (term1013 x)). Qed.
Lemma lem1725162 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1725163 (x : real) : (term1015 x) = (term1016 x).
Proof. exact (MK_COMB (@lem1725162 x) (@lem1725161 x)). Qed.
Lemma lem1725164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725165 (x : real) : (term1017 x) = (term1018 x).
Proof. exact (MK_COMB (@lem1725164) (@lem1725163 x)). Qed.
Lemma lem1725166 (x : real) : (term1007 x) = (term1019 x).
Proof. exact (MK_COMB (@lem1725165 x) (@lem1725160 x)). Qed.
Lemma lem1725167 (x : real) : (term1020 x) = (term1020 x).
Proof. exact (eq_refl (term1020 x)). Qed.
Lemma lem1725168 (x : real) : ((term1005 x) = (term1007 x)) = ((term1005 x) = (term1019 x)).
Proof. exact (MK_COMB (@lem1725167 x) (@lem1725166 x)). Qed.
Lemma lem1725169 (x : real) : (term1005 x) = (term1019 x).
Proof. exact (EQ_MP (@lem1725168 x) (@lem1725157 x)). Qed.
Lemma lem1725170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725171 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725170) (@lem1724666 x)). Qed.
Lemma lem1725172 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725171 x) (@lem1724687 x)). Qed.
Lemma lem1725173 : term897 = term1021.
Proof. exact (@lem1483525 term76 term76). Qed.
Lemma lem1725179 : term891 = term892.
Proof. exact (@lem1483519 term76 term76). Qed.
Lemma lem1725181 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725182 : term184 = term76.
Proof. exact (@lem1725181 term185). Qed.
Lemma lem1725183 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1725184 : term892 = term894.
Proof. exact (MK_COMB (@lem1725183) (@lem1725182)). Qed.
Lemma lem1725185 : term894 = term76.
Proof. exact (@lem1483448 term76). Qed.
Lemma lem1725186 : term892 = term76.
Proof. exact (TRANS (@lem1725184) (@lem1725185)). Qed.
Lemma lem1725188 : term891 = term76.
Proof. exact (TRANS (@lem1725179) (@lem1725186)). Qed.
Lemma lem1725189 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725190 : term1022 = term896.
Proof. exact (MK_COMB (@lem1725189) (@lem1725188)). Qed.
Lemma lem1725191 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725192 : term1021 = term897.
Proof. exact (MK_COMB (@lem1725190) (@lem1725191)). Qed.
Lemma lem1725193 : term897 = term897.
Proof. exact (TRANS (@lem1725173) (@lem1725192)). Qed.
Lemma lem1725194 : term994 = term1023.
Proof. exact (@lem1483525 term925 term76). Qed.
Lemma lem1725200 : term1024 = term1025.
Proof. exact (@lem1483519 term925 term76). Qed.
Lemma lem1725202 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725203 : term184 = term76.
Proof. exact (@lem1725202 term185). Qed.
Lemma lem1725204 : term1026 = term1026.
Proof. exact (eq_refl term1026). Qed.
Lemma lem1725205 : term1025 = term1027.
Proof. exact (MK_COMB (@lem1725204) (@lem1725203)). Qed.
Lemma lem1725206 : term1027 = term925.
Proof. exact (@lem1483450 term925). Qed.
Lemma lem1725207 : term1025 = term925.
Proof. exact (TRANS (@lem1725205) (@lem1725206)). Qed.
Lemma lem1725209 : term1024 = term925.
Proof. exact (TRANS (@lem1725200) (@lem1725207)). Qed.
Lemma lem1725210 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725211 : term1028 = term992.
Proof. exact (MK_COMB (@lem1725210) (@lem1725209)). Qed.
Lemma lem1725212 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725213 : term1023 = term994.
Proof. exact (MK_COMB (@lem1725211) (@lem1725212)). Qed.
Lemma lem1725214 : term994 = term994.
Proof. exact (TRANS (@lem1725194) (@lem1725213)). Qed.
Lemma lem1725215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725216 : term999 = term999.
Proof. exact (MK_COMB (@lem1725215) (@lem1725193)). Qed.
Lemma lem1725217 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1725216) (@lem1725214)). Qed.
Lemma lem1725218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725219 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725218) (@lem1724687 x)). Qed.
Lemma lem1725220 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1725219 x) (@lem1725217)). Qed.
Lemma lem1725221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725222 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725221) (@lem1724687 x)). Qed.
Lemma lem1725223 (x : real) : (term1029 x) = (term1029 x).
Proof. exact (MK_COMB (@lem1725222 x) (@lem1725220 x)). Qed.
Lemma lem1725224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725225 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725224) (@lem1724666 x)). Qed.
Lemma lem1725226 (x : real) : (term1030 x) = (term1030 x).
Proof. exact (MK_COMB (@lem1725225 x) (@lem1725223 x)). Qed.
Lemma lem1725227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725228 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725227) (@lem1725172 x)). Qed.
Lemma lem1725229 (x : real) : (term1014 x) = (term1014 x).
Proof. exact (MK_COMB (@lem1725228 x) (@lem1725226 x)). Qed.
Lemma lem1725230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725231 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1725230) (@lem1724639 x)). Qed.
Lemma lem1725232 (x : real) : (term1016 x) = (term1016 x).
Proof. exact (MK_COMB (@lem1725231 x) (@lem1725229 x)). Qed.
Lemma lem1725233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725234 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725233) (@lem1724666 x)). Qed.
Lemma lem1725235 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725234 x) (@lem1724687 x)). Qed.
Lemma lem1725236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725237 : term999 = term999.
Proof. exact (MK_COMB (@lem1725236) (@lem1725193)). Qed.
Lemma lem1725238 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1725237) (@lem1725214)). Qed.
Lemma lem1725239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725240 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725239) (@lem1724687 x)). Qed.
Lemma lem1725241 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1725240 x) (@lem1725238)). Qed.
Lemma lem1725242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725243 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725242) (@lem1724781 x)). Qed.
Lemma lem1725244 (x : real) : (term1031 x) = (term1032 x).
Proof. exact (MK_COMB (@lem1725243 x) (@lem1725241 x)). Qed.
Lemma lem1725245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725246 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725245) (@lem1724666 x)). Qed.
Lemma lem1725247 (x : real) : (term1033 x) = (term1034 x).
Proof. exact (MK_COMB (@lem1725246 x) (@lem1725244 x)). Qed.
Lemma lem1725248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725249 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725248) (@lem1725235 x)). Qed.
Lemma lem1725250 (x : real) : (term1010 x) = (term1035 x).
Proof. exact (MK_COMB (@lem1725249 x) (@lem1725247 x)). Qed.
Lemma lem1725251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725252 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725251) (@lem1724751 x)). Qed.
Lemma lem1725253 (x : real) : (term1012 x) = (term1036 x).
Proof. exact (MK_COMB (@lem1725252 x) (@lem1725250 x)). Qed.
Lemma lem1725254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725255 (x : real) : (term1018 x) = (term1018 x).
Proof. exact (MK_COMB (@lem1725254) (@lem1725232 x)). Qed.
Lemma lem1725256 (x : real) : (term1019 x) = (term1037 x).
Proof. exact (MK_COMB (@lem1725255 x) (@lem1725253 x)). Qed.
Lemma lem1725267 (x : real) : (term1005 x) = (term1037 x).
Proof. exact (TRANS (@lem1725169 x) (@lem1725256 x)). Qed.
Lemma lem1725268 (x : real) : (term1004 x) = (term1037 x).
Proof. exact (TRANS (@lem1725153 x) (@lem1725267 x)). Qed.
Lemma lem1725269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725270 (x : real) : (term1038 x) = (term1039 x).
Proof. exact (MK_COMB (@lem1725269) (@lem1725066 x)). Qed.
Lemma lem1725271 (x : real) : (term790 x) = (term1040 x).
Proof. exact (MK_COMB (@lem1725270 x) (@lem1725268 x)). Qed.
Lemma lem1725273 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1725274 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1725273 x term76). Qed.
Lemma lem1725281 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1725282 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725283 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1725282) (@lem1725281 x)). Qed.
Lemma lem1725284 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725285 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1725283 x) (@lem1725284)). Qed.
Lemma lem1725298 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1725299 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725298 x) (@lem1725285 x)). Qed.
Lemma lem1725300 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1725274 x) (@lem1725299 x)). Qed.
Lemma lem1725301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725302 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725301) (@lem1725300 x)). Qed.
Lemma lem1725303 (x : real) : (term666 x) = (term666 x).
Proof. exact (eq_refl (term666 x)). Qed.
Lemma lem1725304 (x : real) : (term1041 x) = (term1042 x).
Proof. exact (MK_COMB (@lem1725302 x) (@lem1725303 x)). Qed.
Lemma lem1725305 (x : real) : (term1043 x) = (term1042 x).
Proof. exact (eq_refl (term1043 x)). Qed.
Lemma lem1725306 (x : real) : (term1042 x) = (term1043 x).
Proof. exact (SYM (@lem1725305 x)). Qed.
Lemma lem1725307 (x : real) : (term1043 x) = (term1044 x).
Proof. exact (@lem1482981 (term1045 x) x). Qed.
Lemma lem1725308 (x : real) : (term1042 x) = (term1044 x).
Proof. exact (TRANS (@lem1725306 x) (@lem1725307 x)). Qed.
Lemma lem1725309 (x : real) : (term1046 x) = (term1047 x).
Proof. exact (eq_refl (term1046 x)). Qed.
Lemma lem1725310 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1725311 (x : real) : (term1048 x) = (term1049 x).
Proof. exact (MK_COMB (@lem1725310 x) (@lem1725309 x)). Qed.
Lemma lem1725312 (x : real) : (term1050 x) = (term1051 x).
Proof. exact (eq_refl (term1050 x)). Qed.
Lemma lem1725313 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1725314 (x : real) : (term1052 x) = (term1053 x).
Proof. exact (MK_COMB (@lem1725313 x) (@lem1725312 x)). Qed.
Lemma lem1725315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725316 (x : real) : (term1054 x) = (term1055 x).
Proof. exact (MK_COMB (@lem1725315) (@lem1725314 x)). Qed.
Lemma lem1725317 (x : real) : (term1044 x) = (term1056 x).
Proof. exact (MK_COMB (@lem1725316 x) (@lem1725311 x)). Qed.
Lemma lem1725318 (x : real) : (term1057 x) = (term1057 x).
Proof. exact (eq_refl (term1057 x)). Qed.
Lemma lem1725319 (x : real) : ((term1042 x) = (term1044 x)) = ((term1042 x) = (term1056 x)).
Proof. exact (MK_COMB (@lem1725318 x) (@lem1725317 x)). Qed.
Lemma lem1725320 (x : real) : (term1042 x) = (term1056 x).
Proof. exact (EQ_MP (@lem1725319 x) (@lem1725308 x)). Qed.
Lemma lem1725321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725322 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725321) (@lem1724666 x)). Qed.
Lemma lem1725323 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725322 x) (@lem1724687 x)). Qed.
Lemma lem1725324 (x : real) : (term236 x) = (term1058 x).
Proof. exact (@lem1483527 (term176 x) term76). Qed.
Lemma lem1725336 (x : real) : (term831 x) = (term832 x).
Proof. exact (@lem1483519 (term176 x) term76). Qed.
Lemma lem1725338 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725339 : term184 = term76.
Proof. exact (@lem1725338 term185). Qed.
Lemma lem1725340 (x : real) : (term833 x) = (term833 x).
Proof. exact (eq_refl (term833 x)). Qed.
Lemma lem1725341 (x : real) : (term832 x) = (term834 x).
Proof. exact (MK_COMB (@lem1725340 x) (@lem1725339)). Qed.
Lemma lem1725342 (x : real) : (term834 x) = (term176 x).
Proof. exact (@lem1483450 (term176 x)). Qed.
Lemma lem1725343 (x : real) : (term832 x) = (term176 x).
Proof. exact (TRANS (@lem1725341 x) (@lem1725342 x)). Qed.
Lemma lem1725345 (x : real) : (term831 x) = (term176 x).
Proof. exact (TRANS (@lem1725336 x) (@lem1725343 x)). Qed.
Lemma lem1725346 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1725347 (x : real) : (term1059 x) = (term235 x).
Proof. exact (MK_COMB (@lem1725346) (@lem1725345 x)). Qed.
Lemma lem1725348 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725349 (x : real) : (term1058 x) = (term236 x).
Proof. exact (MK_COMB (@lem1725347 x) (@lem1725348)). Qed.
Lemma lem1725350 (x : real) : (term236 x) = (term236 x).
Proof. exact (TRANS (@lem1725324 x) (@lem1725349 x)). Qed.
Lemma lem1725351 : term256 = term1060.
Proof. exact (@lem1483525 term241 term76). Qed.
Lemma lem1725363 : term1061 = term1062.
Proof. exact (@lem1483519 term241 term76). Qed.
Lemma lem1725365 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725366 : term184 = term76.
Proof. exact (@lem1725365 term185). Qed.
Lemma lem1725367 : term1063 = term1063.
Proof. exact (eq_refl term1063). Qed.
Lemma lem1725368 : term1062 = term1064.
Proof. exact (MK_COMB (@lem1725367) (@lem1725366)). Qed.
Lemma lem1725369 : term1064 = term241.
Proof. exact (@lem1483450 term241). Qed.
Lemma lem1725370 : term1062 = term241.
Proof. exact (TRANS (@lem1725368) (@lem1725369)). Qed.
Lemma lem1725372 : term1061 = term241.
Proof. exact (TRANS (@lem1725363) (@lem1725370)). Qed.
Lemma lem1725373 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725374 : term1065 = term254.
Proof. exact (MK_COMB (@lem1725373) (@lem1725372)). Qed.
Lemma lem1725375 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725376 : term1060 = term256.
Proof. exact (MK_COMB (@lem1725374) (@lem1725375)). Qed.
Lemma lem1725377 : term256 = term256.
Proof. exact (TRANS (@lem1725351) (@lem1725376)). Qed.
Lemma lem1725378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725379 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725378) (@lem1725350 x)). Qed.
Lemma lem1725380 (x : real) : (term580 x) = (term580 x).
Proof. exact (MK_COMB (@lem1725379 x) (@lem1725377)). Qed.
Lemma lem1725381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725382 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725381) (@lem1724687 x)). Qed.
Lemma lem1725383 (x : real) : (term1066 x) = (term1066 x).
Proof. exact (MK_COMB (@lem1725382 x) (@lem1725380 x)). Qed.
Lemma lem1725384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725385 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725384) (@lem1724666 x)). Qed.
Lemma lem1725386 (x : real) : (term1067 x) = (term1067 x).
Proof. exact (MK_COMB (@lem1725385 x) (@lem1725383 x)). Qed.
Lemma lem1725387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725388 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725387) (@lem1725323 x)). Qed.
Lemma lem1725389 (x : real) : (term1051 x) = (term1051 x).
Proof. exact (MK_COMB (@lem1725388 x) (@lem1725386 x)). Qed.
Lemma lem1725390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725391 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1725390) (@lem1724639 x)). Qed.
Lemma lem1725392 (x : real) : (term1053 x) = (term1053 x).
Proof. exact (MK_COMB (@lem1725391 x) (@lem1725389 x)). Qed.
Lemma lem1725393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725394 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725393) (@lem1724666 x)). Qed.
Lemma lem1725395 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725394 x) (@lem1724687 x)). Qed.
Lemma lem1725396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725397 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725396) (@lem1725350 x)). Qed.
Lemma lem1725398 (x : real) : (term580 x) = (term580 x).
Proof. exact (MK_COMB (@lem1725397 x) (@lem1725377)). Qed.
Lemma lem1725399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725400 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725399) (@lem1724781 x)). Qed.
Lemma lem1725401 (x : real) : (term1068 x) = (term1069 x).
Proof. exact (MK_COMB (@lem1725400 x) (@lem1725398 x)). Qed.
Lemma lem1725402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725403 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725402) (@lem1724666 x)). Qed.
Lemma lem1725404 (x : real) : (term1070 x) = (term1071 x).
Proof. exact (MK_COMB (@lem1725403 x) (@lem1725401 x)). Qed.
Lemma lem1725405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725406 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725405) (@lem1725395 x)). Qed.
Lemma lem1725407 (x : real) : (term1047 x) = (term1072 x).
Proof. exact (MK_COMB (@lem1725406 x) (@lem1725404 x)). Qed.
Lemma lem1725408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725409 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725408) (@lem1724751 x)). Qed.
Lemma lem1725410 (x : real) : (term1049 x) = (term1073 x).
Proof. exact (MK_COMB (@lem1725409 x) (@lem1725407 x)). Qed.
Lemma lem1725411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725412 (x : real) : (term1055 x) = (term1055 x).
Proof. exact (MK_COMB (@lem1725411) (@lem1725392 x)). Qed.
Lemma lem1725413 (x : real) : (term1056 x) = (term1074 x).
Proof. exact (MK_COMB (@lem1725412 x) (@lem1725410 x)). Qed.
Lemma lem1725414 (x : real) : (term1042 x) = (term1074 x).
Proof. exact (TRANS (@lem1725320 x) (@lem1725413 x)). Qed.
Lemma lem1725416 (x : real) : (term1075 x) = (term1073 x).
Proof. exact (eq_refl (term1075 x)). Qed.
Lemma lem1725417 (x : real) : (term1073 x) = (term1075 x).
Proof. exact (SYM (@lem1725416 x)). Qed.
Lemma lem1725418 (x : real) : (term1075 x) = (term1076 x).
Proof. exact (@lem1482981 (term1077 x) term73). Qed.
Lemma lem1725419 (x : real) : (term1073 x) = (term1076 x).
Proof. exact (TRANS (@lem1725417 x) (@lem1725418 x)). Qed.
Lemma lem1725420 (x : real) : (term1078 x) = (term1079 x).
Proof. exact (eq_refl (term1078 x)). Qed.
Lemma lem1725421 : term1080 = term1080.
Proof. exact (eq_refl term1080). Qed.
Lemma lem1725422 (x : real) : (term1081 x) = (term1082 x).
Proof. exact (MK_COMB (@lem1725421) (@lem1725420 x)). Qed.
Lemma lem1725423 (x : real) : (term1083 x) = (term1084 x).
Proof. exact (eq_refl (term1083 x)). Qed.
Lemma lem1725424 : term1085 = term1085.
Proof. exact (eq_refl term1085). Qed.
Lemma lem1725425 (x : real) : (term1086 x) = (term1087 x).
Proof. exact (MK_COMB (@lem1725424) (@lem1725423 x)). Qed.
Lemma lem1725426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725427 (x : real) : (term1088 x) = (term1089 x).
Proof. exact (MK_COMB (@lem1725426) (@lem1725425 x)). Qed.
Lemma lem1725428 (x : real) : (term1076 x) = (term1090 x).
Proof. exact (MK_COMB (@lem1725427 x) (@lem1725422 x)). Qed.
Lemma lem1725429 (x : real) : (term1091 x) = (term1091 x).
Proof. exact (eq_refl (term1091 x)). Qed.
Lemma lem1725430 (x : real) : ((term1073 x) = (term1076 x)) = ((term1073 x) = (term1090 x)).
Proof. exact (MK_COMB (@lem1725429 x) (@lem1725428 x)). Qed.
Lemma lem1725431 (x : real) : (term1073 x) = (term1090 x).
Proof. exact (EQ_MP (@lem1725430 x) (@lem1725419 x)). Qed.
Lemma lem1725432 : term1092 = term1093.
Proof. exact (@lem1483527 term73 term76). Qed.
Lemma lem1725438 : term1094 = term1095.
Proof. exact (@lem1483519 term73 term76). Qed.
Lemma lem1725440 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725441 : term184 = term76.
Proof. exact (@lem1725440 term185). Qed.
Lemma lem1725442 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1725443 : term1095 = term1097.
Proof. exact (MK_COMB (@lem1725442) (@lem1725441)). Qed.
Lemma lem1725444 : term1097 = term73.
Proof. exact (@lem1483450 term73). Qed.
Lemma lem1725445 : term1095 = term73.
Proof. exact (TRANS (@lem1725443) (@lem1725444)). Qed.
Lemma lem1725447 : term1094 = term73.
Proof. exact (TRANS (@lem1725438) (@lem1725445)). Qed.
Lemma lem1725448 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1725449 : term1098 = term1099.
Proof. exact (MK_COMB (@lem1725448) (@lem1725447)). Qed.
Lemma lem1725450 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725451 : term1093 = term1092.
Proof. exact (MK_COMB (@lem1725449) (@lem1725450)). Qed.
Lemma lem1725452 : term1092 = term1092.
Proof. exact (TRANS (@lem1725432) (@lem1725451)). Qed.
Lemma lem1725453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725454 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725453) (@lem1724666 x)). Qed.
Lemma lem1725455 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725454 x) (@lem1724687 x)). Qed.
Lemma lem1725456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725457 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725456) (@lem1725350 x)). Qed.
Lemma lem1725458 (x : real) : (term1100 x) = (term1101 x).
Proof. exact (MK_COMB (@lem1725457 x) (@lem1724954)). Qed.
Lemma lem1725459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725460 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725459) (@lem1724666 x)). Qed.
Lemma lem1725461 (x : real) : (term1102 x) = (term1103 x).
Proof. exact (MK_COMB (@lem1725460 x) (@lem1725458 x)). Qed.
Lemma lem1725462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725463 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725462) (@lem1724666 x)). Qed.
Lemma lem1725464 (x : real) : (term1104 x) = (term1105 x).
Proof. exact (MK_COMB (@lem1725463 x) (@lem1725461 x)). Qed.
Lemma lem1725465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725466 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725465) (@lem1725455 x)). Qed.
Lemma lem1725467 (x : real) : (term1106 x) = (term1107 x).
Proof. exact (MK_COMB (@lem1725466 x) (@lem1725464 x)). Qed.
Lemma lem1725468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725469 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725468) (@lem1724666 x)). Qed.
Lemma lem1725470 (x : real) : (term1084 x) = (term1108 x).
Proof. exact (MK_COMB (@lem1725469 x) (@lem1725467 x)). Qed.
Lemma lem1725471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725472 : term1085 = term1085.
Proof. exact (MK_COMB (@lem1725471) (@lem1725452)). Qed.
Lemma lem1725473 (x : real) : (term1087 x) = (term1109 x).
Proof. exact (MK_COMB (@lem1725472) (@lem1725470 x)). Qed.
Lemma lem1725474 : term1110 = term1111.
Proof. exact (@lem1483525 term76 term73). Qed.
Lemma lem1725480 : term1112 = term1113.
Proof. exact (@lem1483519 term76 term73). Qed.
Lemma lem1725482 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1725483 : term215 = term206.
Proof. exact (@lem1725482 term185 term185). Qed.
Lemma lem1725484 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1725485 : term205 = term185.
Proof. exact (EQ_MP (@lem1725484) (@lem940073)). Qed.
Lemma lem1725486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1725487 : term206 = term24.
Proof. exact (MK_COMB (@lem1725486) (@lem1725485)). Qed.
Lemma lem1725488 : term215 = term24.
Proof. exact (TRANS (@lem1725483) (@lem1725487)). Qed.
Lemma lem1725489 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1725490 : term1113 = term1114.
Proof. exact (MK_COMB (@lem1725489) (@lem1725488)). Qed.
Lemma lem1725491 : term1114 = term24.
Proof. exact (@lem1483448 term24). Qed.
Lemma lem1725492 : term1113 = term24.
Proof. exact (TRANS (@lem1725490) (@lem1725491)). Qed.
Lemma lem1725494 : term1112 = term24.
Proof. exact (TRANS (@lem1725480) (@lem1725492)). Qed.
Lemma lem1725495 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725496 : term1115 = term1116.
Proof. exact (MK_COMB (@lem1725495) (@lem1725494)). Qed.
Lemma lem1725497 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725498 : term1111 = term1117.
Proof. exact (MK_COMB (@lem1725496) (@lem1725497)). Qed.
Lemma lem1725499 : term1110 = term1117.
Proof. exact (TRANS (@lem1725474) (@lem1725498)). Qed.
Lemma lem1725500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725501 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725500) (@lem1724666 x)). Qed.
Lemma lem1725502 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725501 x) (@lem1724687 x)). Qed.
Lemma lem1725503 : term1118 = term1119.
Proof. exact (@lem1483525 term1120 term76). Qed.
Lemma lem1725504 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725505 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1725509 : term1121 = term215.
Proof. exact (@lem1483512 term73). Qed.
Lemma lem1725511 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1725512 : term215 = term206.
Proof. exact (@lem1725511 term185 term185). Qed.
Lemma lem1725513 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1725514 : term205 = term185.
Proof. exact (EQ_MP (@lem1725513) (@lem940073)). Qed.
Lemma lem1725515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1725516 : term206 = term24.
Proof. exact (MK_COMB (@lem1725515) (@lem1725514)). Qed.
Lemma lem1725517 : term215 = term24.
Proof. exact (TRANS (@lem1725512) (@lem1725516)). Qed.
Lemma lem1725519 : term1121 = term24.
Proof. exact (TRANS (@lem1725509) (@lem1725517)). Qed.
Lemma lem1725520 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1725521 : term1122 = term880.
Proof. exact (MK_COMB (@lem1725520) (@lem1725519)). Qed.
Lemma lem1725522 : term1120 = term886.
Proof. exact (MK_COMB (@lem1725521) (@lem1725505)). Qed.
Lemma lem1725524 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1725525 : term886 = term76.
Proof. exact (@lem1725524 term185). Qed.
Lemma lem1725526 : term1120 = term76.
Proof. exact (TRANS (@lem1725522) (@lem1725525)). Qed.
Lemma lem1725527 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1725528 : term1123 = term889.
Proof. exact (MK_COMB (@lem1725527) (@lem1725526)). Qed.
Lemma lem1725529 : term1124 = term891.
Proof. exact (MK_COMB (@lem1725528) (@lem1725504)). Qed.
Lemma lem1725530 : term891 = term892.
Proof. exact (@lem1483519 term76 term76). Qed.
Lemma lem1725532 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725533 : term184 = term76.
Proof. exact (@lem1725532 term185). Qed.
Lemma lem1725534 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1725535 : term892 = term894.
Proof. exact (MK_COMB (@lem1725534) (@lem1725533)). Qed.
Lemma lem1725536 : term894 = term76.
Proof. exact (@lem1483448 term76). Qed.
Lemma lem1725537 : term892 = term76.
Proof. exact (TRANS (@lem1725535) (@lem1725536)). Qed.
Lemma lem1725538 : term891 = term76.
Proof. exact (TRANS (@lem1725530) (@lem1725537)). Qed.
Lemma lem1725539 : term1124 = term76.
Proof. exact (TRANS (@lem1725529) (@lem1725538)). Qed.
Lemma lem1725540 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725541 : term1125 = term896.
Proof. exact (MK_COMB (@lem1725540) (@lem1725539)). Qed.
Lemma lem1725542 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725543 : term1119 = term897.
Proof. exact (MK_COMB (@lem1725541) (@lem1725542)). Qed.
Lemma lem1725544 : term1118 = term897.
Proof. exact (TRANS (@lem1725503) (@lem1725543)). Qed.
Lemma lem1725545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725546 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725545) (@lem1725350 x)). Qed.
Lemma lem1725547 (x : real) : (term1126 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1725546 x) (@lem1725544)). Qed.
Lemma lem1725548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725549 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725548) (@lem1724666 x)). Qed.
Lemma lem1725550 (x : real) : (term1128 x) = (term1129 x).
Proof. exact (MK_COMB (@lem1725549 x) (@lem1725547 x)). Qed.
Lemma lem1725551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725552 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725551) (@lem1724666 x)). Qed.
Lemma lem1725553 (x : real) : (term1130 x) = (term1131 x).
Proof. exact (MK_COMB (@lem1725552 x) (@lem1725550 x)). Qed.
Lemma lem1725554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725555 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725554) (@lem1725502 x)). Qed.
Lemma lem1725556 (x : real) : (term1132 x) = (term1133 x).
Proof. exact (MK_COMB (@lem1725555 x) (@lem1725553 x)). Qed.
Lemma lem1725557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725558 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725557) (@lem1724666 x)). Qed.
Lemma lem1725559 (x : real) : (term1079 x) = (term1134 x).
Proof. exact (MK_COMB (@lem1725558 x) (@lem1725556 x)). Qed.
Lemma lem1725560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725561 : term1080 = term1135.
Proof. exact (MK_COMB (@lem1725560) (@lem1725499)). Qed.
Lemma lem1725562 (x : real) : (term1082 x) = (term1136 x).
Proof. exact (MK_COMB (@lem1725561) (@lem1725559 x)). Qed.
Lemma lem1725563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725564 (x : real) : (term1089 x) = (term1137 x).
Proof. exact (MK_COMB (@lem1725563) (@lem1725473 x)). Qed.
Lemma lem1725565 (x : real) : (term1090 x) = (term1138 x).
Proof. exact (MK_COMB (@lem1725564 x) (@lem1725562 x)). Qed.
Lemma lem1725577 (x : real) : (term1073 x) = (term1138 x).
Proof. exact (TRANS (@lem1725431 x) (@lem1725565 x)). Qed.
Lemma lem1725579 (x : real) : (term1139 x) = (term1053 x).
Proof. exact (eq_refl (term1139 x)). Qed.
Lemma lem1725580 (x : real) : (term1053 x) = (term1139 x).
Proof. exact (SYM (@lem1725579 x)). Qed.
Lemma lem1725581 (x : real) : (term1139 x) = (term1140 x).
Proof. exact (@lem1482981 (term1141 x) term73). Qed.
Lemma lem1725582 (x : real) : (term1053 x) = (term1140 x).
Proof. exact (TRANS (@lem1725580 x) (@lem1725581 x)). Qed.
Lemma lem1725583 (x : real) : (term1142 x) = (term1143 x).
Proof. exact (eq_refl (term1142 x)). Qed.
Lemma lem1725584 : term1080 = term1080.
Proof. exact (eq_refl term1080). Qed.
Lemma lem1725585 (x : real) : (term1144 x) = (term1145 x).
Proof. exact (MK_COMB (@lem1725584) (@lem1725583 x)). Qed.
Lemma lem1725586 (x : real) : (term1146 x) = (term1147 x).
Proof. exact (eq_refl (term1146 x)). Qed.
Lemma lem1725587 : term1085 = term1085.
Proof. exact (eq_refl term1085). Qed.
Lemma lem1725588 (x : real) : (term1148 x) = (term1149 x).
Proof. exact (MK_COMB (@lem1725587) (@lem1725586 x)). Qed.
Lemma lem1725589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725590 (x : real) : (term1150 x) = (term1151 x).
Proof. exact (MK_COMB (@lem1725589) (@lem1725588 x)). Qed.
Lemma lem1725591 (x : real) : (term1140 x) = (term1152 x).
Proof. exact (MK_COMB (@lem1725590 x) (@lem1725585 x)). Qed.
Lemma lem1725592 (x : real) : (term1153 x) = (term1153 x).
Proof. exact (eq_refl (term1153 x)). Qed.
Lemma lem1725593 (x : real) : ((term1053 x) = (term1140 x)) = ((term1053 x) = (term1152 x)).
Proof. exact (MK_COMB (@lem1725592 x) (@lem1725591 x)). Qed.
Lemma lem1725594 (x : real) : (term1053 x) = (term1152 x).
Proof. exact (EQ_MP (@lem1725593 x) (@lem1725582 x)). Qed.
Lemma lem1725595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725596 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725595) (@lem1724666 x)). Qed.
Lemma lem1725597 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725596 x) (@lem1724687 x)). Qed.
Lemma lem1725598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725599 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725598) (@lem1725350 x)). Qed.
Lemma lem1725600 (x : real) : (term1100 x) = (term1101 x).
Proof. exact (MK_COMB (@lem1725599 x) (@lem1724954)). Qed.
Lemma lem1725601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725602 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725601) (@lem1724687 x)). Qed.
Lemma lem1725603 (x : real) : (term1154 x) = (term1155 x).
Proof. exact (MK_COMB (@lem1725602 x) (@lem1725600 x)). Qed.
Lemma lem1725604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725605 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725604) (@lem1724666 x)). Qed.
Lemma lem1725606 (x : real) : (term1156 x) = (term1157 x).
Proof. exact (MK_COMB (@lem1725605 x) (@lem1725603 x)). Qed.
Lemma lem1725607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725608 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725607) (@lem1725597 x)). Qed.
Lemma lem1725609 (x : real) : (term1158 x) = (term1159 x).
Proof. exact (MK_COMB (@lem1725608 x) (@lem1725606 x)). Qed.
Lemma lem1725610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725611 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1725610) (@lem1724639 x)). Qed.
Lemma lem1725612 (x : real) : (term1147 x) = (term1160 x).
Proof. exact (MK_COMB (@lem1725611 x) (@lem1725609 x)). Qed.
Lemma lem1725613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725614 : term1085 = term1085.
Proof. exact (MK_COMB (@lem1725613) (@lem1725452)). Qed.
Lemma lem1725615 (x : real) : (term1149 x) = (term1161 x).
Proof. exact (MK_COMB (@lem1725614) (@lem1725612 x)). Qed.
Lemma lem1725616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725617 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725616) (@lem1724666 x)). Qed.
Lemma lem1725618 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725617 x) (@lem1724687 x)). Qed.
Lemma lem1725619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725620 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725619) (@lem1725350 x)). Qed.
Lemma lem1725621 (x : real) : (term1126 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1725620 x) (@lem1725544)). Qed.
Lemma lem1725622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725623 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725622) (@lem1724687 x)). Qed.
Lemma lem1725624 (x : real) : (term1162 x) = (term1163 x).
Proof. exact (MK_COMB (@lem1725623 x) (@lem1725621 x)). Qed.
Lemma lem1725625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725626 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725625) (@lem1724666 x)). Qed.
Lemma lem1725627 (x : real) : (term1164 x) = (term1165 x).
Proof. exact (MK_COMB (@lem1725626 x) (@lem1725624 x)). Qed.
Lemma lem1725628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725629 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725628) (@lem1725618 x)). Qed.
Lemma lem1725630 (x : real) : (term1166 x) = (term1167 x).
Proof. exact (MK_COMB (@lem1725629 x) (@lem1725627 x)). Qed.
Lemma lem1725631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725632 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1725631) (@lem1724639 x)). Qed.
Lemma lem1725633 (x : real) : (term1143 x) = (term1168 x).
Proof. exact (MK_COMB (@lem1725632 x) (@lem1725630 x)). Qed.
Lemma lem1725634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725635 : term1080 = term1135.
Proof. exact (MK_COMB (@lem1725634) (@lem1725499)). Qed.
Lemma lem1725636 (x : real) : (term1145 x) = (term1169 x).
Proof. exact (MK_COMB (@lem1725635) (@lem1725633 x)). Qed.
Lemma lem1725637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725638 (x : real) : (term1151 x) = (term1170 x).
Proof. exact (MK_COMB (@lem1725637) (@lem1725615 x)). Qed.
Lemma lem1725639 (x : real) : (term1152 x) = (term1171 x).
Proof. exact (MK_COMB (@lem1725638 x) (@lem1725636 x)). Qed.
Lemma lem1725651 (x : real) : (term1053 x) = (term1171 x).
Proof. exact (TRANS (@lem1725594 x) (@lem1725639 x)). Qed.
Lemma lem1725652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725653 (x : real) : (term1055 x) = (term1172 x).
Proof. exact (MK_COMB (@lem1725652) (@lem1725651 x)). Qed.
Lemma lem1725654 (x : real) : (term1074 x) = (term1173 x).
Proof. exact (MK_COMB (@lem1725653 x) (@lem1725577 x)). Qed.
Lemma lem1725655 (x : real) : (term1042 x) = (term1173 x).
Proof. exact (TRANS (@lem1725414 x) (@lem1725654 x)). Qed.
Lemma lem1725656 (x : real) : (term1041 x) = (term1173 x).
Proof. exact (TRANS (@lem1725304 x) (@lem1725655 x)). Qed.
Lemma lem1725658 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1725659 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1725658 x term76). Qed.
Lemma lem1725666 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1725667 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725668 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1725667) (@lem1725666 x)). Qed.
Lemma lem1725669 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725670 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1725668 x) (@lem1725669)). Qed.
Lemma lem1725683 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1725684 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725683 x) (@lem1725670 x)). Qed.
Lemma lem1725685 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1725659 x) (@lem1725684 x)). Qed.
Lemma lem1725686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725687 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725686) (@lem1725685 x)). Qed.
Lemma lem1725689 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1725690 : term252 = term1174.
Proof. exact (@lem1725689 term24 term73 term76). Qed.
Lemma lem1725697 : term1175 = term73.
Proof. exact (@lem1483460 term73). Qed.
Lemma lem1725700 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1725701 : term1176 = term886.
Proof. exact (MK_COMB (@lem1725700) (@lem1725697)). Qed.
Lemma lem1725703 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1725704 : term886 = term76.
Proof. exact (@lem1725703 term185). Qed.
Lemma lem1725705 : term1176 = term76.
Proof. exact (TRANS (@lem1725701) (@lem1725704)). Qed.
Lemma lem1725706 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725707 : term1177 = term896.
Proof. exact (MK_COMB (@lem1725706) (@lem1725705)). Qed.
Lemma lem1725708 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725709 : term1178 = term897.
Proof. exact (MK_COMB (@lem1725707) (@lem1725708)). Qed.
Lemma lem1725716 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1725717 : term215 = term206.
Proof. exact (@lem1725716 term185 term185). Qed.
Lemma lem1725718 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1725719 : term205 = term185.
Proof. exact (EQ_MP (@lem1725718) (@lem940073)). Qed.
Lemma lem1725720 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1725721 : term206 = term24.
Proof. exact (MK_COMB (@lem1725720) (@lem1725719)). Qed.
Lemma lem1725723 : term215 = term24.
Proof. exact (TRANS (@lem1725717) (@lem1725721)). Qed.
Lemma lem1725726 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1725727 : term1179 = term990.
Proof. exact (MK_COMB (@lem1725726) (@lem1725723)). Qed.
Lemma lem1725728 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1725729 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1725730 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1725731 : term922 = term923.
Proof. exact (EQ_MP (@lem1725730) (@lem1725729)). Qed.
Lemma lem1725732 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1725733 : term924 = term925.
Proof. exact (MK_COMB (@lem1725732) (@lem1725731)). Qed.
Lemma lem1725734 : term990 = term925.
Proof. exact (TRANS (@lem1725728) (@lem1725733)). Qed.
Lemma lem1725735 : term1179 = term925.
Proof. exact (TRANS (@lem1725727) (@lem1725734)). Qed.
Lemma lem1725736 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725737 : term1180 = term992.
Proof. exact (MK_COMB (@lem1725736) (@lem1725735)). Qed.
Lemma lem1725738 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725739 : term1181 = term994.
Proof. exact (MK_COMB (@lem1725737) (@lem1725738)). Qed.
Lemma lem1725740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725741 : term1182 = term1183.
Proof. exact (MK_COMB (@lem1725740) (@lem1725739)). Qed.
Lemma lem1725742 : term1174 = term1184.
Proof. exact (MK_COMB (@lem1725741) (@lem1725709)). Qed.
Lemma lem1725743 : term252 = term1184.
Proof. exact (TRANS (@lem1725690) (@lem1725742)). Qed.
Lemma lem1725744 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1725745 (x : real) : (term581 x) = (term1185 x).
Proof. exact (MK_COMB (@lem1725744 x) (@lem1725743)). Qed.
Lemma lem1725746 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1725747 (x : real) : (term603 x) = (term1186 x).
Proof. exact (MK_COMB (@lem1725746 x) (@lem1725745 x)). Qed.
Lemma lem1725748 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1725749 (x : real) : (term667 x) = (term1187 x).
Proof. exact (MK_COMB (@lem1725748 x) (@lem1725747 x)). Qed.
Lemma lem1725750 (x : real) : (term1188 x) = (term1189 x).
Proof. exact (MK_COMB (@lem1725687 x) (@lem1725749 x)). Qed.
Lemma lem1725751 (x : real) : (term1190 x) = (term1189 x).
Proof. exact (eq_refl (term1190 x)). Qed.
Lemma lem1725752 (x : real) : (term1189 x) = (term1190 x).
Proof. exact (SYM (@lem1725751 x)). Qed.
Lemma lem1725753 (x : real) : (term1190 x) = (term1191 x).
Proof. exact (@lem1482981 (term1192 x) x). Qed.
Lemma lem1725754 (x : real) : (term1189 x) = (term1191 x).
Proof. exact (TRANS (@lem1725752 x) (@lem1725753 x)). Qed.
Lemma lem1725755 (x : real) : (term1193 x) = (term1194 x).
Proof. exact (eq_refl (term1193 x)). Qed.
Lemma lem1725756 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1725757 (x : real) : (term1195 x) = (term1196 x).
Proof. exact (MK_COMB (@lem1725756 x) (@lem1725755 x)). Qed.
Lemma lem1725758 (x : real) : (term1197 x) = (term1198 x).
Proof. exact (eq_refl (term1197 x)). Qed.
Lemma lem1725759 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1725760 (x : real) : (term1199 x) = (term1200 x).
Proof. exact (MK_COMB (@lem1725759 x) (@lem1725758 x)). Qed.
Lemma lem1725761 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725762 (x : real) : (term1201 x) = (term1202 x).
Proof. exact (MK_COMB (@lem1725761) (@lem1725760 x)). Qed.
Lemma lem1725763 (x : real) : (term1191 x) = (term1203 x).
Proof. exact (MK_COMB (@lem1725762 x) (@lem1725757 x)). Qed.
Lemma lem1725764 (x : real) : (term1204 x) = (term1204 x).
Proof. exact (eq_refl (term1204 x)). Qed.
Lemma lem1725765 (x : real) : ((term1189 x) = (term1191 x)) = ((term1189 x) = (term1203 x)).
Proof. exact (MK_COMB (@lem1725764 x) (@lem1725763 x)). Qed.
Lemma lem1725766 (x : real) : (term1189 x) = (term1203 x).
Proof. exact (EQ_MP (@lem1725765 x) (@lem1725754 x)). Qed.
Lemma lem1725767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725768 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725767) (@lem1724666 x)). Qed.
Lemma lem1725769 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725768 x) (@lem1724687 x)). Qed.
Lemma lem1725770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725771 : term1183 = term1183.
Proof. exact (MK_COMB (@lem1725770) (@lem1725214)). Qed.
Lemma lem1725772 : term1184 = term1184.
Proof. exact (MK_COMB (@lem1725771) (@lem1725193)). Qed.
Lemma lem1725773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725774 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725773) (@lem1725350 x)). Qed.
Lemma lem1725775 (x : real) : (term1185 x) = (term1185 x).
Proof. exact (MK_COMB (@lem1725774 x) (@lem1725772)). Qed.
Lemma lem1725776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725777 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725776) (@lem1724687 x)). Qed.
Lemma lem1725778 (x : real) : (term1205 x) = (term1205 x).
Proof. exact (MK_COMB (@lem1725777 x) (@lem1725775 x)). Qed.
Lemma lem1725779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725780 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725779) (@lem1724666 x)). Qed.
Lemma lem1725781 (x : real) : (term1206 x) = (term1206 x).
Proof. exact (MK_COMB (@lem1725780 x) (@lem1725778 x)). Qed.
Lemma lem1725782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725783 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725782) (@lem1725769 x)). Qed.
Lemma lem1725784 (x : real) : (term1198 x) = (term1198 x).
Proof. exact (MK_COMB (@lem1725783 x) (@lem1725781 x)). Qed.
Lemma lem1725785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725786 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1725785) (@lem1724639 x)). Qed.
Lemma lem1725787 (x : real) : (term1200 x) = (term1200 x).
Proof. exact (MK_COMB (@lem1725786 x) (@lem1725784 x)). Qed.
Lemma lem1725788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725789 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725788) (@lem1724666 x)). Qed.
Lemma lem1725790 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725789 x) (@lem1724687 x)). Qed.
Lemma lem1725791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725792 : term1183 = term1183.
Proof. exact (MK_COMB (@lem1725791) (@lem1725214)). Qed.
Lemma lem1725793 : term1184 = term1184.
Proof. exact (MK_COMB (@lem1725792) (@lem1725193)). Qed.
Lemma lem1725794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725795 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725794) (@lem1725350 x)). Qed.
Lemma lem1725796 (x : real) : (term1185 x) = (term1185 x).
Proof. exact (MK_COMB (@lem1725795 x) (@lem1725793)). Qed.
Lemma lem1725797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725798 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725797) (@lem1724781 x)). Qed.
Lemma lem1725799 (x : real) : (term1207 x) = (term1208 x).
Proof. exact (MK_COMB (@lem1725798 x) (@lem1725796 x)). Qed.
Lemma lem1725800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725801 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725800) (@lem1724666 x)). Qed.
Lemma lem1725802 (x : real) : (term1209 x) = (term1210 x).
Proof. exact (MK_COMB (@lem1725801 x) (@lem1725799 x)). Qed.
Lemma lem1725803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725804 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725803) (@lem1725790 x)). Qed.
Lemma lem1725805 (x : real) : (term1194 x) = (term1211 x).
Proof. exact (MK_COMB (@lem1725804 x) (@lem1725802 x)). Qed.
Lemma lem1725806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725807 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725806) (@lem1724751 x)). Qed.
Lemma lem1725808 (x : real) : (term1196 x) = (term1212 x).
Proof. exact (MK_COMB (@lem1725807 x) (@lem1725805 x)). Qed.
Lemma lem1725809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725810 (x : real) : (term1202 x) = (term1202 x).
Proof. exact (MK_COMB (@lem1725809) (@lem1725787 x)). Qed.
Lemma lem1725811 (x : real) : (term1203 x) = (term1213 x).
Proof. exact (MK_COMB (@lem1725810 x) (@lem1725808 x)). Qed.
Lemma lem1725822 (x : real) : (term1189 x) = (term1213 x).
Proof. exact (TRANS (@lem1725766 x) (@lem1725811 x)). Qed.
Lemma lem1725823 (x : real) : (term1188 x) = (term1213 x).
Proof. exact (TRANS (@lem1725750 x) (@lem1725822 x)). Qed.
Lemma lem1725824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725825 (x : real) : (term1214 x) = (term1215 x).
Proof. exact (MK_COMB (@lem1725824) (@lem1725656 x)). Qed.
Lemma lem1725826 (x : real) : (term788 x) = (term1216 x).
Proof. exact (MK_COMB (@lem1725825 x) (@lem1725823 x)). Qed.
Lemma lem1725827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725828 (x : real) : (term792 x) = (term1217 x).
Proof. exact (MK_COMB (@lem1725827) (@lem1725271 x)). Qed.
Lemma lem1725829 (x : real) : (term793 x) = (term1218 x).
Proof. exact (MK_COMB (@lem1725828 x) (@lem1725826 x)). Qed.
Lemma lem1725831 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1725832 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1725831 x term76). Qed.
Lemma lem1725839 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1725840 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725841 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1725840) (@lem1725839 x)). Qed.
Lemma lem1725842 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725843 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1725841 x) (@lem1725842)). Qed.
Lemma lem1725856 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1725857 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725856 x) (@lem1725843 x)). Qed.
Lemma lem1725858 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1725832 x) (@lem1725857 x)). Qed.
Lemma lem1725859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725860 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725859) (@lem1725858 x)). Qed.
Lemma lem1725862 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1725863 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1725862 x term76). Qed.
Lemma lem1725870 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1725871 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1725872 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1725871) (@lem1725870 x)). Qed.
Lemma lem1725873 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725874 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1725872 x) (@lem1725873)). Qed.
Lemma lem1725887 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1725888 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1725887 x) (@lem1725874 x)). Qed.
Lemma lem1725889 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1725863 x) (@lem1725888 x)). Qed.
Lemma lem1725890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725891 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1725890) (@lem1725889 x)). Qed.
Lemma lem1725892 (x : real) : (term693 x) = (term693 x).
Proof. exact (eq_refl (term693 x)). Qed.
Lemma lem1725893 (x : real) : (term709 x) = (term1226 x).
Proof. exact (MK_COMB (@lem1725891 x) (@lem1725892 x)). Qed.
Lemma lem1725894 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1725895 (x : real) : (term780 x) = (term1227 x).
Proof. exact (MK_COMB (@lem1725894 x) (@lem1725893 x)). Qed.
Lemma lem1725896 (x : real) : (term1228 x) = (term1229 x).
Proof. exact (MK_COMB (@lem1725860 x) (@lem1725895 x)). Qed.
Lemma lem1725897 (x : real) : (term1230 x) = (term1229 x).
Proof. exact (eq_refl (term1230 x)). Qed.
Lemma lem1725898 (x : real) : (term1229 x) = (term1230 x).
Proof. exact (SYM (@lem1725897 x)). Qed.
Lemma lem1725899 (x : real) : (term1230 x) = (term1231 x).
Proof. exact (@lem1482981 (term1232 x) term24). Qed.
Lemma lem1725900 (x : real) : (term1229 x) = (term1231 x).
Proof. exact (TRANS (@lem1725898 x) (@lem1725899 x)). Qed.
Lemma lem1725901 (x : real) : (term1233 x) = (term1234 x).
Proof. exact (eq_refl (term1233 x)). Qed.
Lemma lem1725902 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1725903 (x : real) : (term1235 x) = (term1236 x).
Proof. exact (MK_COMB (@lem1725902) (@lem1725901 x)). Qed.
Lemma lem1725904 (x : real) : (term1237 x) = (term1238 x).
Proof. exact (eq_refl (term1237 x)). Qed.
Lemma lem1725905 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1725906 (x : real) : (term1239 x) = (term1240 x).
Proof. exact (MK_COMB (@lem1725905) (@lem1725904 x)). Qed.
Lemma lem1725907 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1725908 (x : real) : (term1241 x) = (term1242 x).
Proof. exact (MK_COMB (@lem1725907) (@lem1725906 x)). Qed.
Lemma lem1725909 (x : real) : (term1231 x) = (term1243 x).
Proof. exact (MK_COMB (@lem1725908 x) (@lem1725903 x)). Qed.
Lemma lem1725910 (x : real) : (term1244 x) = (term1244 x).
Proof. exact (eq_refl (term1244 x)). Qed.
Lemma lem1725911 (x : real) : ((term1229 x) = (term1231 x)) = ((term1229 x) = (term1243 x)).
Proof. exact (MK_COMB (@lem1725910 x) (@lem1725909 x)). Qed.
Lemma lem1725912 (x : real) : (term1229 x) = (term1243 x).
Proof. exact (EQ_MP (@lem1725911 x) (@lem1725900 x)). Qed.
Lemma lem1725913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725914 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725913) (@lem1724666 x)). Qed.
Lemma lem1725915 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725914 x) (@lem1724687 x)). Qed.
Lemma lem1725916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725917 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725916) (@lem1725350 x)). Qed.
Lemma lem1725918 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1725917 x) (@lem1724639 x)). Qed.
Lemma lem1725919 : term1245 = term1246.
Proof. exact (@lem1483525 term990 term76). Qed.
Lemma lem1725920 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725926 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1725927 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1725928 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1725929 : term922 = term923.
Proof. exact (EQ_MP (@lem1725928) (@lem1725927)). Qed.
Lemma lem1725930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1725931 : term924 = term925.
Proof. exact (MK_COMB (@lem1725930) (@lem1725929)). Qed.
Lemma lem1725933 : term990 = term925.
Proof. exact (TRANS (@lem1725926) (@lem1725931)). Qed.
Lemma lem1725934 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1725935 : term1247 = term1248.
Proof. exact (MK_COMB (@lem1725934) (@lem1725933)). Qed.
Lemma lem1725936 : term1249 = term1024.
Proof. exact (MK_COMB (@lem1725935) (@lem1725920)). Qed.
Lemma lem1725937 : term1024 = term1025.
Proof. exact (@lem1483519 term925 term76). Qed.
Lemma lem1725939 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725940 : term184 = term76.
Proof. exact (@lem1725939 term185). Qed.
Lemma lem1725941 : term1026 = term1026.
Proof. exact (eq_refl term1026). Qed.
Lemma lem1725942 : term1025 = term1027.
Proof. exact (MK_COMB (@lem1725941) (@lem1725940)). Qed.
Lemma lem1725943 : term1027 = term925.
Proof. exact (@lem1483450 term925). Qed.
Lemma lem1725944 : term1025 = term925.
Proof. exact (TRANS (@lem1725942) (@lem1725943)). Qed.
Lemma lem1725945 : term1024 = term925.
Proof. exact (TRANS (@lem1725937) (@lem1725944)). Qed.
Lemma lem1725946 : term1249 = term925.
Proof. exact (TRANS (@lem1725936) (@lem1725945)). Qed.
Lemma lem1725947 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725948 : term1250 = term992.
Proof. exact (MK_COMB (@lem1725947) (@lem1725946)). Qed.
Lemma lem1725949 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725950 : term1246 = term994.
Proof. exact (MK_COMB (@lem1725948) (@lem1725949)). Qed.
Lemma lem1725951 : term1245 = term994.
Proof. exact (TRANS (@lem1725919) (@lem1725950)). Qed.
Lemma lem1725952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725953 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1725952) (@lem1724687 x)). Qed.
Lemma lem1725954 (x : real) : (term1251 x) = (term1252 x).
Proof. exact (MK_COMB (@lem1725953 x) (@lem1725951)). Qed.
Lemma lem1725955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725956 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1725955) (@lem1725918 x)). Qed.
Lemma lem1725957 (x : real) : (term1253 x) = (term1254 x).
Proof. exact (MK_COMB (@lem1725956 x) (@lem1725954 x)). Qed.
Lemma lem1725958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725959 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725958) (@lem1724666 x)). Qed.
Lemma lem1725960 (x : real) : (term1255 x) = (term1256 x).
Proof. exact (MK_COMB (@lem1725959 x) (@lem1725957 x)). Qed.
Lemma lem1725961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725962 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1725961) (@lem1725915 x)). Qed.
Lemma lem1725963 (x : real) : (term1238 x) = (term1257 x).
Proof. exact (MK_COMB (@lem1725962 x) (@lem1725960 x)). Qed.
Lemma lem1725964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725965 : term869 = term869.
Proof. exact (MK_COMB (@lem1725964) (@lem1724838)). Qed.
Lemma lem1725966 (x : real) : (term1240 x) = (term1258 x).
Proof. exact (MK_COMB (@lem1725965) (@lem1725963 x)). Qed.
Lemma lem1725967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725968 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1725967) (@lem1724666 x)). Qed.
Lemma lem1725969 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1725968 x) (@lem1724687 x)). Qed.
Lemma lem1725970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1725971 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1725970) (@lem1725350 x)). Qed.
Lemma lem1725972 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1725971 x) (@lem1724639 x)). Qed.
Lemma lem1725973 : term1259 = term1260.
Proof. exact (@lem1483525 term1261 term76). Qed.
Lemma lem1725974 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1725981 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1725983 : term1261 = term76.
Proof. exact (@lem1725981 term185). Qed.
Lemma lem1725984 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1725985 : term1263 = term889.
Proof. exact (MK_COMB (@lem1725984) (@lem1725983)). Qed.
Lemma lem1725986 : term1264 = term891.
Proof. exact (MK_COMB (@lem1725985) (@lem1725974)). Qed.
Lemma lem1725987 : term891 = term892.
Proof. exact (@lem1483519 term76 term76). Qed.
Lemma lem1725989 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1725990 : term184 = term76.
Proof. exact (@lem1725989 term185). Qed.
Lemma lem1725991 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1725992 : term892 = term894.
Proof. exact (MK_COMB (@lem1725991) (@lem1725990)). Qed.
Lemma lem1725993 : term894 = term76.
Proof. exact (@lem1483448 term76). Qed.
Lemma lem1725994 : term892 = term76.
Proof. exact (TRANS (@lem1725992) (@lem1725993)). Qed.
Lemma lem1725995 : term891 = term76.
Proof. exact (TRANS (@lem1725987) (@lem1725994)). Qed.
Lemma lem1725996 : term1264 = term76.
Proof. exact (TRANS (@lem1725986) (@lem1725995)). Qed.
Lemma lem1725997 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1725998 : term1265 = term896.
Proof. exact (MK_COMB (@lem1725997) (@lem1725996)). Qed.
Lemma lem1725999 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726000 : term1260 = term897.
Proof. exact (MK_COMB (@lem1725998) (@lem1725999)). Qed.
Lemma lem1726001 : term1259 = term897.
Proof. exact (TRANS (@lem1725973) (@lem1726000)). Qed.
Lemma lem1726002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726003 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726002) (@lem1724687 x)). Qed.
Lemma lem1726004 (x : real) : (term1266 x) = (term899 x).
Proof. exact (MK_COMB (@lem1726003 x) (@lem1726001)). Qed.
Lemma lem1726005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726006 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1726005) (@lem1725972 x)). Qed.
Lemma lem1726007 (x : real) : (term1267 x) = (term1268 x).
Proof. exact (MK_COMB (@lem1726006 x) (@lem1726004 x)). Qed.
Lemma lem1726008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726009 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726008) (@lem1724666 x)). Qed.
Lemma lem1726010 (x : real) : (term1269 x) = (term1270 x).
Proof. exact (MK_COMB (@lem1726009 x) (@lem1726007 x)). Qed.
Lemma lem1726011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726012 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726011) (@lem1725969 x)). Qed.
Lemma lem1726013 (x : real) : (term1234 x) = (term1271 x).
Proof. exact (MK_COMB (@lem1726012 x) (@lem1726010 x)). Qed.
Lemma lem1726014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726015 : term864 = term946.
Proof. exact (MK_COMB (@lem1726014) (@lem1724916)). Qed.
Lemma lem1726016 (x : real) : (term1236 x) = (term1272 x).
Proof. exact (MK_COMB (@lem1726015) (@lem1726013 x)). Qed.
Lemma lem1726017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726018 (x : real) : (term1242 x) = (term1273 x).
Proof. exact (MK_COMB (@lem1726017) (@lem1725966 x)). Qed.
Lemma lem1726019 (x : real) : (term1243 x) = (term1274 x).
Proof. exact (MK_COMB (@lem1726018 x) (@lem1726016 x)). Qed.
Lemma lem1726030 (x : real) : (term1229 x) = (term1274 x).
Proof. exact (TRANS (@lem1725912 x) (@lem1726019 x)). Qed.
Lemma lem1726031 (x : real) : (term1228 x) = (term1274 x).
Proof. exact (TRANS (@lem1725896 x) (@lem1726030 x)). Qed.
Lemma lem1726033 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726034 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1726033 x term76). Qed.
Lemma lem1726041 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726042 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726043 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1726042) (@lem1726041 x)). Qed.
Lemma lem1726044 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726045 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1726043 x) (@lem1726044)). Qed.
Lemma lem1726058 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726059 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726058 x) (@lem1726045 x)). Qed.
Lemma lem1726060 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1726034 x) (@lem1726059 x)). Qed.
Lemma lem1726061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726062 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726061) (@lem1726060 x)). Qed.
Lemma lem1726064 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726065 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1726064 x term76). Qed.
Lemma lem1726072 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726073 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1726074 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1726073) (@lem1726072 x)). Qed.
Lemma lem1726075 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726076 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1726074 x) (@lem1726075)). Qed.
Lemma lem1726089 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1726090 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1726089 x) (@lem1726076 x)). Qed.
Lemma lem1726091 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1726065 x) (@lem1726090 x)). Qed.
Lemma lem1726092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726093 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1726092) (@lem1726091 x)). Qed.
Lemma lem1726095 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726096 : term284 = term1275.
Proof. exact (@lem1726095 term73 term24 term76). Qed.
Lemma lem1726103 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1726106 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1726107 : term1276 = term1261.
Proof. exact (MK_COMB (@lem1726106) (@lem1726103)). Qed.
Lemma lem1726109 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1726110 : term1261 = term76.
Proof. exact (@lem1726109 term185). Qed.
Lemma lem1726111 : term1276 = term76.
Proof. exact (TRANS (@lem1726107) (@lem1726110)). Qed.
Lemma lem1726112 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726113 : term1277 = term896.
Proof. exact (MK_COMB (@lem1726112) (@lem1726111)). Qed.
Lemma lem1726114 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726115 : term1278 = term897.
Proof. exact (MK_COMB (@lem1726113) (@lem1726114)). Qed.
Lemma lem1726122 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1726125 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1726126 : term1279 = term918.
Proof. exact (MK_COMB (@lem1726125) (@lem1726122)). Qed.
Lemma lem1726127 : term918 = term919.
Proof. exact (@lem1367763 term185 term185). Qed.
Lemma lem1726128 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1726129 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1726130 : term922 = term923.
Proof. exact (EQ_MP (@lem1726129) (@lem1726128)). Qed.
Lemma lem1726131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1726132 : term924 = term925.
Proof. exact (MK_COMB (@lem1726131) (@lem1726130)). Qed.
Lemma lem1726133 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1726134 : term919 = term926.
Proof. exact (MK_COMB (@lem1726133) (@lem1726132)). Qed.
Lemma lem1726135 : term918 = term926.
Proof. exact (TRANS (@lem1726127) (@lem1726134)). Qed.
Lemma lem1726136 : term1279 = term926.
Proof. exact (TRANS (@lem1726126) (@lem1726135)). Qed.
Lemma lem1726137 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726138 : term1280 = term935.
Proof. exact (MK_COMB (@lem1726137) (@lem1726136)). Qed.
Lemma lem1726139 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726140 : term1281 = term936.
Proof. exact (MK_COMB (@lem1726138) (@lem1726139)). Qed.
Lemma lem1726141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726142 : term1282 = term1283.
Proof. exact (MK_COMB (@lem1726141) (@lem1726140)). Qed.
Lemma lem1726143 : term1275 = term1284.
Proof. exact (MK_COMB (@lem1726142) (@lem1726115)). Qed.
Lemma lem1726144 : term284 = term1284.
Proof. exact (TRANS (@lem1726096) (@lem1726143)). Qed.
Lemma lem1726145 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1726146 (x : real) : (term694 x) = (term1285 x).
Proof. exact (MK_COMB (@lem1726145 x) (@lem1726144)). Qed.
Lemma lem1726147 (x : real) : (term710 x) = (term1286 x).
Proof. exact (MK_COMB (@lem1726093 x) (@lem1726146 x)). Qed.
Lemma lem1726148 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726149 (x : real) : (term781 x) = (term1287 x).
Proof. exact (MK_COMB (@lem1726148 x) (@lem1726147 x)). Qed.
Lemma lem1726152 (x : real) : (term1288 x) = (term1289 x).
Proof. exact (MK_COMB (@lem1726062 x) (@lem1726149 x)). Qed.
Lemma lem1726153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726154 (x : real) : (term1290 x) = (term1291 x).
Proof. exact (MK_COMB (@lem1726153) (@lem1726031 x)). Qed.
Lemma lem1726155 (x : real) : (term779 x) = (term1292 x).
Proof. exact (MK_COMB (@lem1726154 x) (@lem1726152 x)). Qed.
Lemma lem1726157 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726158 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1726157 x term76). Qed.
Lemma lem1726165 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726166 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726167 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1726166) (@lem1726165 x)). Qed.
Lemma lem1726168 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726169 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1726167 x) (@lem1726168)). Qed.
Lemma lem1726182 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726183 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726182 x) (@lem1726169 x)). Qed.
Lemma lem1726184 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1726158 x) (@lem1726183 x)). Qed.
Lemma lem1726185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726186 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726185) (@lem1726184 x)). Qed.
Lemma lem1726188 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726189 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1726188 x term76). Qed.
Lemma lem1726196 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726197 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1726198 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1726197) (@lem1726196 x)). Qed.
Lemma lem1726199 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726200 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1726198 x) (@lem1726199)). Qed.
Lemma lem1726213 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1726214 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1726213 x) (@lem1726200 x)). Qed.
Lemma lem1726215 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1726189 x) (@lem1726214 x)). Qed.
Lemma lem1726216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726217 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1726216) (@lem1726215 x)). Qed.
Lemma lem1726218 (x : real) : (term721 x) = (term721 x).
Proof. exact (eq_refl (term721 x)). Qed.
Lemma lem1726219 (x : real) : (term731 x) = (term1293 x).
Proof. exact (MK_COMB (@lem1726217 x) (@lem1726218 x)). Qed.
Lemma lem1726220 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726221 (x : real) : (term776 x) = (term1294 x).
Proof. exact (MK_COMB (@lem1726220 x) (@lem1726219 x)). Qed.
Lemma lem1726222 (x : real) : (term1295 x) = (term1296 x).
Proof. exact (MK_COMB (@lem1726186 x) (@lem1726221 x)). Qed.
Lemma lem1726223 (x : real) : (term1297 x) = (term1296 x).
Proof. exact (eq_refl (term1297 x)). Qed.
Lemma lem1726224 (x : real) : (term1296 x) = (term1297 x).
Proof. exact (SYM (@lem1726223 x)). Qed.
Lemma lem1726225 (x : real) : (term1297 x) = (term1298 x).
Proof. exact (@lem1482981 (term1299 x) term73). Qed.
Lemma lem1726226 (x : real) : (term1296 x) = (term1298 x).
Proof. exact (TRANS (@lem1726224 x) (@lem1726225 x)). Qed.
Lemma lem1726227 (x : real) : (term1300 x) = (term1301 x).
Proof. exact (eq_refl (term1300 x)). Qed.
Lemma lem1726228 : term1080 = term1080.
Proof. exact (eq_refl term1080). Qed.
Lemma lem1726229 (x : real) : (term1302 x) = (term1303 x).
Proof. exact (MK_COMB (@lem1726228) (@lem1726227 x)). Qed.
Lemma lem1726230 (x : real) : (term1304 x) = (term1305 x).
Proof. exact (eq_refl (term1304 x)). Qed.
Lemma lem1726231 : term1085 = term1085.
Proof. exact (eq_refl term1085). Qed.
Lemma lem1726232 (x : real) : (term1306 x) = (term1307 x).
Proof. exact (MK_COMB (@lem1726231) (@lem1726230 x)). Qed.
Lemma lem1726233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726234 (x : real) : (term1308 x) = (term1309 x).
Proof. exact (MK_COMB (@lem1726233) (@lem1726232 x)). Qed.
Lemma lem1726235 (x : real) : (term1298 x) = (term1310 x).
Proof. exact (MK_COMB (@lem1726234 x) (@lem1726229 x)). Qed.
Lemma lem1726236 (x : real) : (term1311 x) = (term1311 x).
Proof. exact (eq_refl (term1311 x)). Qed.
Lemma lem1726237 (x : real) : ((term1296 x) = (term1298 x)) = ((term1296 x) = (term1310 x)).
Proof. exact (MK_COMB (@lem1726236 x) (@lem1726235 x)). Qed.
Lemma lem1726238 (x : real) : (term1296 x) = (term1310 x).
Proof. exact (EQ_MP (@lem1726237 x) (@lem1726226 x)). Qed.
Lemma lem1726239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726240 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726239) (@lem1724666 x)). Qed.
Lemma lem1726241 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726240 x) (@lem1724687 x)). Qed.
Lemma lem1726242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726243 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1726242) (@lem1725350 x)). Qed.
Lemma lem1726244 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1726243 x) (@lem1724639 x)). Qed.
Lemma lem1726245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726246 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1726245) (@lem1725350 x)). Qed.
Lemma lem1726247 (x : real) : (term1312 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1726246 x) (@lem1726001)). Qed.
Lemma lem1726248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726249 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1726248) (@lem1726244 x)). Qed.
Lemma lem1726250 (x : real) : (term1313 x) = (term1314 x).
Proof. exact (MK_COMB (@lem1726249 x) (@lem1726247 x)). Qed.
Lemma lem1726251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726252 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726251) (@lem1724666 x)). Qed.
Lemma lem1726253 (x : real) : (term1315 x) = (term1316 x).
Proof. exact (MK_COMB (@lem1726252 x) (@lem1726250 x)). Qed.
Lemma lem1726254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726255 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726254) (@lem1726241 x)). Qed.
Lemma lem1726256 (x : real) : (term1305 x) = (term1317 x).
Proof. exact (MK_COMB (@lem1726255 x) (@lem1726253 x)). Qed.
Lemma lem1726257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726258 : term1085 = term1085.
Proof. exact (MK_COMB (@lem1726257) (@lem1725452)). Qed.
Lemma lem1726259 (x : real) : (term1307 x) = (term1318 x).
Proof. exact (MK_COMB (@lem1726258) (@lem1726256 x)). Qed.
Lemma lem1726260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726261 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726260) (@lem1724666 x)). Qed.
Lemma lem1726262 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726261 x) (@lem1724687 x)). Qed.
Lemma lem1726263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726264 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1726263) (@lem1725350 x)). Qed.
Lemma lem1726265 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1726264 x) (@lem1724639 x)). Qed.
Lemma lem1726266 : term1319 = term1320.
Proof. exact (@lem1483525 term1321 term76). Qed.
Lemma lem1726267 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726268 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1726272 : term1121 = term215.
Proof. exact (@lem1483512 term73). Qed.
Lemma lem1726274 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1726275 : term215 = term206.
Proof. exact (@lem1726274 term185 term185). Qed.
Lemma lem1726276 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1726277 : term205 = term185.
Proof. exact (EQ_MP (@lem1726276) (@lem940073)). Qed.
Lemma lem1726278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1726279 : term206 = term24.
Proof. exact (MK_COMB (@lem1726278) (@lem1726277)). Qed.
Lemma lem1726280 : term215 = term24.
Proof. exact (TRANS (@lem1726275) (@lem1726279)). Qed.
Lemma lem1726282 : term1121 = term24.
Proof. exact (TRANS (@lem1726272) (@lem1726280)). Qed.
Lemma lem1726283 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1726284 : term1122 = term880.
Proof. exact (MK_COMB (@lem1726283) (@lem1726282)). Qed.
Lemma lem1726285 : term1321 = term990.
Proof. exact (MK_COMB (@lem1726284) (@lem1726268)). Qed.
Lemma lem1726286 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1726287 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1726288 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1726289 : term922 = term923.
Proof. exact (EQ_MP (@lem1726288) (@lem1726287)). Qed.
Lemma lem1726290 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1726291 : term924 = term925.
Proof. exact (MK_COMB (@lem1726290) (@lem1726289)). Qed.
Lemma lem1726292 : term990 = term925.
Proof. exact (TRANS (@lem1726286) (@lem1726291)). Qed.
Lemma lem1726293 : term1321 = term925.
Proof. exact (TRANS (@lem1726285) (@lem1726292)). Qed.
Lemma lem1726294 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1726295 : term1322 = term1248.
Proof. exact (MK_COMB (@lem1726294) (@lem1726293)). Qed.
Lemma lem1726296 : term1323 = term1024.
Proof. exact (MK_COMB (@lem1726295) (@lem1726267)). Qed.
Lemma lem1726297 : term1024 = term1025.
Proof. exact (@lem1483519 term925 term76). Qed.
Lemma lem1726299 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1726300 : term184 = term76.
Proof. exact (@lem1726299 term185). Qed.
Lemma lem1726301 : term1026 = term1026.
Proof. exact (eq_refl term1026). Qed.
Lemma lem1726302 : term1025 = term1027.
Proof. exact (MK_COMB (@lem1726301) (@lem1726300)). Qed.
Lemma lem1726303 : term1027 = term925.
Proof. exact (@lem1483450 term925). Qed.
Lemma lem1726304 : term1025 = term925.
Proof. exact (TRANS (@lem1726302) (@lem1726303)). Qed.
Lemma lem1726305 : term1024 = term925.
Proof. exact (TRANS (@lem1726297) (@lem1726304)). Qed.
Lemma lem1726306 : term1323 = term925.
Proof. exact (TRANS (@lem1726296) (@lem1726305)). Qed.
Lemma lem1726307 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726308 : term1324 = term992.
Proof. exact (MK_COMB (@lem1726307) (@lem1726306)). Qed.
Lemma lem1726309 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726310 : term1320 = term994.
Proof. exact (MK_COMB (@lem1726308) (@lem1726309)). Qed.
Lemma lem1726311 : term1319 = term994.
Proof. exact (TRANS (@lem1726266) (@lem1726310)). Qed.
Lemma lem1726312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726313 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1726312) (@lem1725350 x)). Qed.
Lemma lem1726314 (x : real) : (term1325 x) = (term1326 x).
Proof. exact (MK_COMB (@lem1726313 x) (@lem1726311)). Qed.
Lemma lem1726315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726316 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1726315) (@lem1726265 x)). Qed.
Lemma lem1726317 (x : real) : (term1327 x) = (term1328 x).
Proof. exact (MK_COMB (@lem1726316 x) (@lem1726314 x)). Qed.
Lemma lem1726318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726319 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726318) (@lem1724666 x)). Qed.
Lemma lem1726320 (x : real) : (term1329 x) = (term1330 x).
Proof. exact (MK_COMB (@lem1726319 x) (@lem1726317 x)). Qed.
Lemma lem1726321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726322 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726321) (@lem1726262 x)). Qed.
Lemma lem1726323 (x : real) : (term1301 x) = (term1331 x).
Proof. exact (MK_COMB (@lem1726322 x) (@lem1726320 x)). Qed.
Lemma lem1726324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726325 : term1080 = term1135.
Proof. exact (MK_COMB (@lem1726324) (@lem1725499)). Qed.
Lemma lem1726326 (x : real) : (term1303 x) = (term1332 x).
Proof. exact (MK_COMB (@lem1726325) (@lem1726323 x)). Qed.
Lemma lem1726327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726328 (x : real) : (term1309 x) = (term1333 x).
Proof. exact (MK_COMB (@lem1726327) (@lem1726259 x)). Qed.
Lemma lem1726329 (x : real) : (term1310 x) = (term1334 x).
Proof. exact (MK_COMB (@lem1726328 x) (@lem1726326 x)). Qed.
Lemma lem1726340 (x : real) : (term1296 x) = (term1334 x).
Proof. exact (TRANS (@lem1726238 x) (@lem1726329 x)). Qed.
Lemma lem1726341 (x : real) : (term1295 x) = (term1334 x).
Proof. exact (TRANS (@lem1726222 x) (@lem1726340 x)). Qed.
Lemma lem1726343 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726344 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1726343 x term76). Qed.
Lemma lem1726351 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726352 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726353 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1726352) (@lem1726351 x)). Qed.
Lemma lem1726354 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726355 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1726353 x) (@lem1726354)). Qed.
Lemma lem1726368 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726369 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726368 x) (@lem1726355 x)). Qed.
Lemma lem1726370 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1726344 x) (@lem1726369 x)). Qed.
Lemma lem1726371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726372 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726371) (@lem1726370 x)). Qed.
Lemma lem1726374 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726375 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1726374 x term76). Qed.
Lemma lem1726382 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726383 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1726384 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1726383) (@lem1726382 x)). Qed.
Lemma lem1726385 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726386 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1726384 x) (@lem1726385)). Qed.
Lemma lem1726399 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1726400 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1726399 x) (@lem1726386 x)). Qed.
Lemma lem1726401 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1726375 x) (@lem1726400 x)). Qed.
Lemma lem1726402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726403 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1726402) (@lem1726401 x)). Qed.
Lemma lem1726405 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726406 : term306 = term1335.
Proof. exact (@lem1726405 term73 term73 term76). Qed.
Lemma lem1726413 : term1175 = term73.
Proof. exact (@lem1483460 term73). Qed.
Lemma lem1726416 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1726417 : term1336 = term918.
Proof. exact (MK_COMB (@lem1726416) (@lem1726413)). Qed.
Lemma lem1726418 : term918 = term919.
Proof. exact (@lem1367763 term185 term185). Qed.
Lemma lem1726419 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1726420 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1726421 : term922 = term923.
Proof. exact (EQ_MP (@lem1726420) (@lem1726419)). Qed.
Lemma lem1726422 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1726423 : term924 = term925.
Proof. exact (MK_COMB (@lem1726422) (@lem1726421)). Qed.
Lemma lem1726424 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1726425 : term919 = term926.
Proof. exact (MK_COMB (@lem1726424) (@lem1726423)). Qed.
Lemma lem1726426 : term918 = term926.
Proof. exact (TRANS (@lem1726418) (@lem1726425)). Qed.
Lemma lem1726427 : term1336 = term926.
Proof. exact (TRANS (@lem1726417) (@lem1726426)). Qed.
Lemma lem1726428 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726429 : term1337 = term935.
Proof. exact (MK_COMB (@lem1726428) (@lem1726427)). Qed.
Lemma lem1726430 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726431 : term1338 = term936.
Proof. exact (MK_COMB (@lem1726429) (@lem1726430)). Qed.
Lemma lem1726438 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1726439 : term215 = term206.
Proof. exact (@lem1726438 term185 term185). Qed.
Lemma lem1726440 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1726441 : term205 = term185.
Proof. exact (EQ_MP (@lem1726440) (@lem940073)). Qed.
Lemma lem1726442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1726443 : term206 = term24.
Proof. exact (MK_COMB (@lem1726442) (@lem1726441)). Qed.
Lemma lem1726445 : term215 = term24.
Proof. exact (TRANS (@lem1726439) (@lem1726443)). Qed.
Lemma lem1726448 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1726449 : term1339 = term1261.
Proof. exact (MK_COMB (@lem1726448) (@lem1726445)). Qed.
Lemma lem1726451 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1726452 : term1261 = term76.
Proof. exact (@lem1726451 term185). Qed.
Lemma lem1726453 : term1339 = term76.
Proof. exact (TRANS (@lem1726449) (@lem1726452)). Qed.
Lemma lem1726454 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726455 : term1340 = term896.
Proof. exact (MK_COMB (@lem1726454) (@lem1726453)). Qed.
Lemma lem1726456 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726457 : term1341 = term897.
Proof. exact (MK_COMB (@lem1726455) (@lem1726456)). Qed.
Lemma lem1726458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726459 : term1342 = term999.
Proof. exact (MK_COMB (@lem1726458) (@lem1726457)). Qed.
Lemma lem1726460 : term1335 = term1343.
Proof. exact (MK_COMB (@lem1726459) (@lem1726431)). Qed.
Lemma lem1726461 : term306 = term1343.
Proof. exact (TRANS (@lem1726406) (@lem1726460)). Qed.
Lemma lem1726462 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1726463 (x : real) : (term722 x) = (term1344 x).
Proof. exact (MK_COMB (@lem1726462 x) (@lem1726461)). Qed.
Lemma lem1726464 (x : real) : (term732 x) = (term1345 x).
Proof. exact (MK_COMB (@lem1726403 x) (@lem1726463 x)). Qed.
Lemma lem1726465 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726466 (x : real) : (term777 x) = (term1346 x).
Proof. exact (MK_COMB (@lem1726465 x) (@lem1726464 x)). Qed.
Lemma lem1726469 (x : real) : (term1347 x) = (term1348 x).
Proof. exact (MK_COMB (@lem1726372 x) (@lem1726466 x)). Qed.
Lemma lem1726470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726471 (x : real) : (term1349 x) = (term1350 x).
Proof. exact (MK_COMB (@lem1726470) (@lem1726341 x)). Qed.
Lemma lem1726472 (x : real) : (term775 x) = (term1351 x).
Proof. exact (MK_COMB (@lem1726471 x) (@lem1726469 x)). Qed.
Lemma lem1726473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726474 (x : real) : (term783 x) = (term1352 x).
Proof. exact (MK_COMB (@lem1726473) (@lem1726155 x)). Qed.
Lemma lem1726475 (x : real) : (term784 x) = (term1353 x).
Proof. exact (MK_COMB (@lem1726474 x) (@lem1726472 x)). Qed.
Lemma lem1726476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726477 (x : real) : (term795 x) = (term1354 x).
Proof. exact (MK_COMB (@lem1726476) (@lem1725829 x)). Qed.
Lemma lem1726478 (x : real) : (term796 x) = (term1355 x).
Proof. exact (MK_COMB (@lem1726477 x) (@lem1726475 x)). Qed.
Lemma lem1726480 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726481 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1726480 x term76). Qed.
Lemma lem1726488 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726489 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726490 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1726489) (@lem1726488 x)). Qed.
Lemma lem1726491 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726492 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1726490 x) (@lem1726491)). Qed.
Lemma lem1726505 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726506 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726505 x) (@lem1726492 x)). Qed.
Lemma lem1726507 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1726481 x) (@lem1726506 x)). Qed.
Lemma lem1726508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726509 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726508) (@lem1726507 x)). Qed.
Lemma lem1726510 (x : real) : (term639 x) = (term639 x).
Proof. exact (eq_refl (term639 x)). Qed.
Lemma lem1726511 (x : real) : (term1356 x) = (term1357 x).
Proof. exact (MK_COMB (@lem1726509 x) (@lem1726510 x)). Qed.
Lemma lem1726512 (x : real) : (term1358 x) = (term1357 x).
Proof. exact (eq_refl (term1358 x)). Qed.
Lemma lem1726513 (x : real) : (term1357 x) = (term1358 x).
Proof. exact (SYM (@lem1726512 x)). Qed.
Lemma lem1726514 (x : real) : (term1358 x) = (term1359 x).
Proof. exact (@lem1482981 (term1360 x) x). Qed.
Lemma lem1726515 (x : real) : (term1357 x) = (term1359 x).
Proof. exact (TRANS (@lem1726513 x) (@lem1726514 x)). Qed.
Lemma lem1726516 (x : real) : (term1361 x) = (term1362 x).
Proof. exact (eq_refl (term1361 x)). Qed.
Lemma lem1726517 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1726518 (x : real) : (term1363 x) = (term1364 x).
Proof. exact (MK_COMB (@lem1726517 x) (@lem1726516 x)). Qed.
Lemma lem1726519 (x : real) : (term1365 x) = (term1366 x).
Proof. exact (eq_refl (term1365 x)). Qed.
Lemma lem1726520 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1726521 (x : real) : (term1367 x) = (term1368 x).
Proof. exact (MK_COMB (@lem1726520 x) (@lem1726519 x)). Qed.
Lemma lem1726522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726523 (x : real) : (term1369 x) = (term1370 x).
Proof. exact (MK_COMB (@lem1726522) (@lem1726521 x)). Qed.
Lemma lem1726524 (x : real) : (term1359 x) = (term1371 x).
Proof. exact (MK_COMB (@lem1726523 x) (@lem1726518 x)). Qed.
Lemma lem1726525 (x : real) : (term1372 x) = (term1372 x).
Proof. exact (eq_refl (term1372 x)). Qed.
Lemma lem1726526 (x : real) : ((term1357 x) = (term1359 x)) = ((term1357 x) = (term1371 x)).
Proof. exact (MK_COMB (@lem1726525 x) (@lem1726524 x)). Qed.
Lemma lem1726527 (x : real) : (term1357 x) = (term1371 x).
Proof. exact (EQ_MP (@lem1726526 x) (@lem1726515 x)). Qed.
Lemma lem1726528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726529 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726528) (@lem1724666 x)). Qed.
Lemma lem1726530 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726529 x) (@lem1724687 x)). Qed.
Lemma lem1726531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726532 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726531) (@lem1724687 x)). Qed.
Lemma lem1726533 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1726532 x) (@lem1724717)). Qed.
Lemma lem1726534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726535 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726534) (@lem1724687 x)). Qed.
Lemma lem1726536 (x : real) : (term842 x) = (term842 x).
Proof. exact (MK_COMB (@lem1726535 x) (@lem1726533 x)). Qed.
Lemma lem1726537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726538 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726537) (@lem1724639 x)). Qed.
Lemma lem1726539 (x : real) : (term1373 x) = (term1373 x).
Proof. exact (MK_COMB (@lem1726538 x) (@lem1726536 x)). Qed.
Lemma lem1726540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726541 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726540) (@lem1726530 x)). Qed.
Lemma lem1726542 (x : real) : (term1366 x) = (term1366 x).
Proof. exact (MK_COMB (@lem1726541 x) (@lem1726539 x)). Qed.
Lemma lem1726543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726544 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726543) (@lem1724639 x)). Qed.
Lemma lem1726545 (x : real) : (term1368 x) = (term1368 x).
Proof. exact (MK_COMB (@lem1726544 x) (@lem1726542 x)). Qed.
Lemma lem1726546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726547 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726546) (@lem1724666 x)). Qed.
Lemma lem1726548 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726547 x) (@lem1724687 x)). Qed.
Lemma lem1726549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726550 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726549) (@lem1724687 x)). Qed.
Lemma lem1726551 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1726550 x) (@lem1724717)). Qed.
Lemma lem1726552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726553 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726552) (@lem1724781 x)). Qed.
Lemma lem1726554 (x : real) : (term852 x) = (term853 x).
Proof. exact (MK_COMB (@lem1726553 x) (@lem1726551 x)). Qed.
Lemma lem1726555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726556 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726555) (@lem1724639 x)). Qed.
Lemma lem1726557 (x : real) : (term1374 x) = (term1375 x).
Proof. exact (MK_COMB (@lem1726556 x) (@lem1726554 x)). Qed.
Lemma lem1726558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726559 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726558) (@lem1726548 x)). Qed.
Lemma lem1726560 (x : real) : (term1362 x) = (term1376 x).
Proof. exact (MK_COMB (@lem1726559 x) (@lem1726557 x)). Qed.
Lemma lem1726561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726562 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726561) (@lem1724751 x)). Qed.
Lemma lem1726563 (x : real) : (term1364 x) = (term1377 x).
Proof. exact (MK_COMB (@lem1726562 x) (@lem1726560 x)). Qed.
Lemma lem1726564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726565 (x : real) : (term1370 x) = (term1370 x).
Proof. exact (MK_COMB (@lem1726564) (@lem1726545 x)). Qed.
Lemma lem1726566 (x : real) : (term1371 x) = (term1378 x).
Proof. exact (MK_COMB (@lem1726565 x) (@lem1726563 x)). Qed.
Lemma lem1726567 (x : real) : (term1357 x) = (term1378 x).
Proof. exact (TRANS (@lem1726527 x) (@lem1726566 x)). Qed.
Lemma lem1726569 (x : real) : (term1379 x) = (term1377 x).
Proof. exact (eq_refl (term1379 x)). Qed.
Lemma lem1726570 (x : real) : (term1377 x) = (term1379 x).
Proof. exact (SYM (@lem1726569 x)). Qed.
Lemma lem1726571 (x : real) : (term1379 x) = (term1380 x).
Proof. exact (@lem1482981 (term1381 x) term24). Qed.
Lemma lem1726572 (x : real) : (term1377 x) = (term1380 x).
Proof. exact (TRANS (@lem1726570 x) (@lem1726571 x)). Qed.
Lemma lem1726573 (x : real) : (term1382 x) = (term1383 x).
Proof. exact (eq_refl (term1382 x)). Qed.
Lemma lem1726574 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1726575 (x : real) : (term1384 x) = (term1385 x).
Proof. exact (MK_COMB (@lem1726574) (@lem1726573 x)). Qed.
Lemma lem1726576 (x : real) : (term1386 x) = (term1387 x).
Proof. exact (eq_refl (term1386 x)). Qed.
Lemma lem1726577 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1726578 (x : real) : (term1388 x) = (term1389 x).
Proof. exact (MK_COMB (@lem1726577) (@lem1726576 x)). Qed.
Lemma lem1726579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726580 (x : real) : (term1390 x) = (term1391 x).
Proof. exact (MK_COMB (@lem1726579) (@lem1726578 x)). Qed.
Lemma lem1726581 (x : real) : (term1380 x) = (term1392 x).
Proof. exact (MK_COMB (@lem1726580 x) (@lem1726575 x)). Qed.
Lemma lem1726582 (x : real) : (term1393 x) = (term1393 x).
Proof. exact (eq_refl (term1393 x)). Qed.
Lemma lem1726583 (x : real) : ((term1377 x) = (term1380 x)) = ((term1377 x) = (term1392 x)).
Proof. exact (MK_COMB (@lem1726582 x) (@lem1726581 x)). Qed.
Lemma lem1726584 (x : real) : (term1377 x) = (term1392 x).
Proof. exact (EQ_MP (@lem1726583 x) (@lem1726572 x)). Qed.
Lemma lem1726585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726586 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726585) (@lem1724666 x)). Qed.
Lemma lem1726587 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726586 x) (@lem1724687 x)). Qed.
Lemma lem1726588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726589 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726588) (@lem1724687 x)). Qed.
Lemma lem1726590 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1726589 x) (@lem1724870)). Qed.
Lemma lem1726591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726592 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726591) (@lem1724666 x)). Qed.
Lemma lem1726593 (x : real) : (term900 x) = (term901 x).
Proof. exact (MK_COMB (@lem1726592 x) (@lem1726590 x)). Qed.
Lemma lem1726594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726595 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726594) (@lem1724639 x)). Qed.
Lemma lem1726596 (x : real) : (term1394 x) = (term1395 x).
Proof. exact (MK_COMB (@lem1726595 x) (@lem1726593 x)). Qed.
Lemma lem1726597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726598 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726597) (@lem1726587 x)). Qed.
Lemma lem1726599 (x : real) : (term1396 x) = (term1397 x).
Proof. exact (MK_COMB (@lem1726598 x) (@lem1726596 x)). Qed.
Lemma lem1726600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726601 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726600) (@lem1724666 x)). Qed.
Lemma lem1726602 (x : real) : (term1387 x) = (term1398 x).
Proof. exact (MK_COMB (@lem1726601 x) (@lem1726599 x)). Qed.
Lemma lem1726603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726604 : term869 = term869.
Proof. exact (MK_COMB (@lem1726603) (@lem1724838)). Qed.
Lemma lem1726605 (x : real) : (term1389 x) = (term1399 x).
Proof. exact (MK_COMB (@lem1726604) (@lem1726602 x)). Qed.
Lemma lem1726606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726607 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726606) (@lem1724666 x)). Qed.
Lemma lem1726608 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726607 x) (@lem1724687 x)). Qed.
Lemma lem1726609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726610 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726609) (@lem1724687 x)). Qed.
Lemma lem1726611 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1726610 x) (@lem1724954)). Qed.
Lemma lem1726612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726613 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726612) (@lem1724666 x)). Qed.
Lemma lem1726614 (x : real) : (term939 x) = (term940 x).
Proof. exact (MK_COMB (@lem1726613 x) (@lem1726611 x)). Qed.
Lemma lem1726615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726616 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726615) (@lem1724639 x)). Qed.
Lemma lem1726617 (x : real) : (term1400 x) = (term1401 x).
Proof. exact (MK_COMB (@lem1726616 x) (@lem1726614 x)). Qed.
Lemma lem1726618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726619 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726618) (@lem1726608 x)). Qed.
Lemma lem1726620 (x : real) : (term1402 x) = (term1403 x).
Proof. exact (MK_COMB (@lem1726619 x) (@lem1726617 x)). Qed.
Lemma lem1726621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726622 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726621) (@lem1724666 x)). Qed.
Lemma lem1726623 (x : real) : (term1383 x) = (term1404 x).
Proof. exact (MK_COMB (@lem1726622 x) (@lem1726620 x)). Qed.
Lemma lem1726624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726625 : term864 = term946.
Proof. exact (MK_COMB (@lem1726624) (@lem1724916)). Qed.
Lemma lem1726626 (x : real) : (term1385 x) = (term1405 x).
Proof. exact (MK_COMB (@lem1726625) (@lem1726623 x)). Qed.
Lemma lem1726627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726628 (x : real) : (term1391 x) = (term1406 x).
Proof. exact (MK_COMB (@lem1726627) (@lem1726605 x)). Qed.
Lemma lem1726629 (x : real) : (term1392 x) = (term1407 x).
Proof. exact (MK_COMB (@lem1726628 x) (@lem1726626 x)). Qed.
Lemma lem1726641 (x : real) : (term1377 x) = (term1407 x).
Proof. exact (TRANS (@lem1726584 x) (@lem1726629 x)). Qed.
Lemma lem1726643 (x : real) : (term1408 x) = (term1368 x).
Proof. exact (eq_refl (term1408 x)). Qed.
Lemma lem1726644 (x : real) : (term1368 x) = (term1408 x).
Proof. exact (SYM (@lem1726643 x)). Qed.
Lemma lem1726645 (x : real) : (term1408 x) = (term1409 x).
Proof. exact (@lem1482981 (term1410 x) term24). Qed.
Lemma lem1726646 (x : real) : (term1368 x) = (term1409 x).
Proof. exact (TRANS (@lem1726644 x) (@lem1726645 x)). Qed.
Lemma lem1726647 (x : real) : (term1411 x) = (term1412 x).
Proof. exact (eq_refl (term1411 x)). Qed.
Lemma lem1726648 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1726649 (x : real) : (term1413 x) = (term1414 x).
Proof. exact (MK_COMB (@lem1726648) (@lem1726647 x)). Qed.
Lemma lem1726650 (x : real) : (term1415 x) = (term1416 x).
Proof. exact (eq_refl (term1415 x)). Qed.
Lemma lem1726651 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1726652 (x : real) : (term1417 x) = (term1418 x).
Proof. exact (MK_COMB (@lem1726651) (@lem1726650 x)). Qed.
Lemma lem1726653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726654 (x : real) : (term1419 x) = (term1420 x).
Proof. exact (MK_COMB (@lem1726653) (@lem1726652 x)). Qed.
Lemma lem1726655 (x : real) : (term1409 x) = (term1421 x).
Proof. exact (MK_COMB (@lem1726654 x) (@lem1726649 x)). Qed.
Lemma lem1726656 (x : real) : (term1422 x) = (term1422 x).
Proof. exact (eq_refl (term1422 x)). Qed.
Lemma lem1726657 (x : real) : ((term1368 x) = (term1409 x)) = ((term1368 x) = (term1421 x)).
Proof. exact (MK_COMB (@lem1726656 x) (@lem1726655 x)). Qed.
Lemma lem1726658 (x : real) : (term1368 x) = (term1421 x).
Proof. exact (EQ_MP (@lem1726657 x) (@lem1726646 x)). Qed.
Lemma lem1726659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726660 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726659) (@lem1724666 x)). Qed.
Lemma lem1726661 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726660 x) (@lem1724687 x)). Qed.
Lemma lem1726662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726663 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726662) (@lem1724687 x)). Qed.
Lemma lem1726664 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1726663 x) (@lem1724870)). Qed.
Lemma lem1726665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726666 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726665) (@lem1724687 x)). Qed.
Lemma lem1726667 (x : real) : (term965 x) = (term966 x).
Proof. exact (MK_COMB (@lem1726666 x) (@lem1726664 x)). Qed.
Lemma lem1726668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726669 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726668) (@lem1724639 x)). Qed.
Lemma lem1726670 (x : real) : (term1423 x) = (term1424 x).
Proof. exact (MK_COMB (@lem1726669 x) (@lem1726667 x)). Qed.
Lemma lem1726671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726672 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726671) (@lem1726661 x)). Qed.
Lemma lem1726673 (x : real) : (term1425 x) = (term1426 x).
Proof. exact (MK_COMB (@lem1726672 x) (@lem1726670 x)). Qed.
Lemma lem1726674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726675 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726674) (@lem1724639 x)). Qed.
Lemma lem1726676 (x : real) : (term1416 x) = (term1427 x).
Proof. exact (MK_COMB (@lem1726675 x) (@lem1726673 x)). Qed.
Lemma lem1726677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726678 : term869 = term869.
Proof. exact (MK_COMB (@lem1726677) (@lem1724838)). Qed.
Lemma lem1726679 (x : real) : (term1418 x) = (term1428 x).
Proof. exact (MK_COMB (@lem1726678) (@lem1726676 x)). Qed.
Lemma lem1726680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726681 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726680) (@lem1724666 x)). Qed.
Lemma lem1726682 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726681 x) (@lem1724687 x)). Qed.
Lemma lem1726683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726684 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726683) (@lem1724687 x)). Qed.
Lemma lem1726685 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1726684 x) (@lem1724954)). Qed.
Lemma lem1726686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726687 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726686) (@lem1724687 x)). Qed.
Lemma lem1726688 (x : real) : (term973 x) = (term974 x).
Proof. exact (MK_COMB (@lem1726687 x) (@lem1726685 x)). Qed.
Lemma lem1726689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726690 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726689) (@lem1724639 x)). Qed.
Lemma lem1726691 (x : real) : (term1429 x) = (term1430 x).
Proof. exact (MK_COMB (@lem1726690 x) (@lem1726688 x)). Qed.
Lemma lem1726692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726693 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726692) (@lem1726682 x)). Qed.
Lemma lem1726694 (x : real) : (term1431 x) = (term1432 x).
Proof. exact (MK_COMB (@lem1726693 x) (@lem1726691 x)). Qed.
Lemma lem1726695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726696 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726695) (@lem1724639 x)). Qed.
Lemma lem1726697 (x : real) : (term1412 x) = (term1433 x).
Proof. exact (MK_COMB (@lem1726696 x) (@lem1726694 x)). Qed.
Lemma lem1726698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726699 : term864 = term946.
Proof. exact (MK_COMB (@lem1726698) (@lem1724916)). Qed.
Lemma lem1726700 (x : real) : (term1414 x) = (term1434 x).
Proof. exact (MK_COMB (@lem1726699) (@lem1726697 x)). Qed.
Lemma lem1726701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726702 (x : real) : (term1420 x) = (term1435 x).
Proof. exact (MK_COMB (@lem1726701) (@lem1726679 x)). Qed.
Lemma lem1726703 (x : real) : (term1421 x) = (term1436 x).
Proof. exact (MK_COMB (@lem1726702 x) (@lem1726700 x)). Qed.
Lemma lem1726715 (x : real) : (term1368 x) = (term1436 x).
Proof. exact (TRANS (@lem1726658 x) (@lem1726703 x)). Qed.
Lemma lem1726716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726717 (x : real) : (term1370 x) = (term1437 x).
Proof. exact (MK_COMB (@lem1726716) (@lem1726715 x)). Qed.
Lemma lem1726718 (x : real) : (term1378 x) = (term1438 x).
Proof. exact (MK_COMB (@lem1726717 x) (@lem1726641 x)). Qed.
Lemma lem1726719 (x : real) : (term1357 x) = (term1438 x).
Proof. exact (TRANS (@lem1726567 x) (@lem1726718 x)). Qed.
Lemma lem1726720 (x : real) : (term1356 x) = (term1438 x).
Proof. exact (TRANS (@lem1726511 x) (@lem1726719 x)). Qed.
Lemma lem1726722 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726723 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1726722 x term76). Qed.
Lemma lem1726730 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726731 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726732 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1726731) (@lem1726730 x)). Qed.
Lemma lem1726733 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726734 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1726732 x) (@lem1726733)). Qed.
Lemma lem1726747 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726748 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726747 x) (@lem1726734 x)). Qed.
Lemma lem1726749 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1726723 x) (@lem1726748 x)). Qed.
Lemma lem1726750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726751 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726750) (@lem1726749 x)). Qed.
Lemma lem1726753 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726754 : term222 = term987.
Proof. exact (@lem1726753 term24 term24 term76). Qed.
Lemma lem1726761 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1726764 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1726765 : term989 = term990.
Proof. exact (MK_COMB (@lem1726764) (@lem1726761)). Qed.
Lemma lem1726766 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1726767 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1726768 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1726769 : term922 = term923.
Proof. exact (EQ_MP (@lem1726768) (@lem1726767)). Qed.
Lemma lem1726770 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1726771 : term924 = term925.
Proof. exact (MK_COMB (@lem1726770) (@lem1726769)). Qed.
Lemma lem1726772 : term990 = term925.
Proof. exact (TRANS (@lem1726766) (@lem1726771)). Qed.
Lemma lem1726773 : term989 = term925.
Proof. exact (TRANS (@lem1726765) (@lem1726772)). Qed.
Lemma lem1726774 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726775 : term991 = term992.
Proof. exact (MK_COMB (@lem1726774) (@lem1726773)). Qed.
Lemma lem1726776 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726777 : term993 = term994.
Proof. exact (MK_COMB (@lem1726775) (@lem1726776)). Qed.
Lemma lem1726784 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1726787 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1726788 : term995 = term886.
Proof. exact (MK_COMB (@lem1726787) (@lem1726784)). Qed.
Lemma lem1726790 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1726791 : term886 = term76.
Proof. exact (@lem1726790 term185). Qed.
Lemma lem1726792 : term995 = term76.
Proof. exact (TRANS (@lem1726788) (@lem1726791)). Qed.
Lemma lem1726793 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726794 : term996 = term896.
Proof. exact (MK_COMB (@lem1726793) (@lem1726792)). Qed.
Lemma lem1726795 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726796 : term997 = term897.
Proof. exact (MK_COMB (@lem1726794) (@lem1726795)). Qed.
Lemma lem1726797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726798 : term998 = term999.
Proof. exact (MK_COMB (@lem1726797) (@lem1726796)). Qed.
Lemma lem1726799 : term987 = term1000.
Proof. exact (MK_COMB (@lem1726798) (@lem1726777)). Qed.
Lemma lem1726800 : term222 = term1000.
Proof. exact (TRANS (@lem1726754) (@lem1726799)). Qed.
Lemma lem1726801 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1726802 (x : real) : (term528 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1726801 x) (@lem1726800)). Qed.
Lemma lem1726803 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1726804 (x : real) : (term558 x) = (term1002 x).
Proof. exact (MK_COMB (@lem1726803 x) (@lem1726802 x)). Qed.
Lemma lem1726805 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1726806 (x : real) : (term640 x) = (term1439 x).
Proof. exact (MK_COMB (@lem1726805 x) (@lem1726804 x)). Qed.
Lemma lem1726807 (x : real) : (term1440 x) = (term1441 x).
Proof. exact (MK_COMB (@lem1726751 x) (@lem1726806 x)). Qed.
Lemma lem1726808 (x : real) : (term1442 x) = (term1441 x).
Proof. exact (eq_refl (term1442 x)). Qed.
Lemma lem1726809 (x : real) : (term1441 x) = (term1442 x).
Proof. exact (SYM (@lem1726808 x)). Qed.
Lemma lem1726810 (x : real) : (term1442 x) = (term1443 x).
Proof. exact (@lem1482981 (term1444 x) x). Qed.
Lemma lem1726811 (x : real) : (term1441 x) = (term1443 x).
Proof. exact (TRANS (@lem1726809 x) (@lem1726810 x)). Qed.
Lemma lem1726812 (x : real) : (term1445 x) = (term1446 x).
Proof. exact (eq_refl (term1445 x)). Qed.
Lemma lem1726813 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1726814 (x : real) : (term1447 x) = (term1448 x).
Proof. exact (MK_COMB (@lem1726813 x) (@lem1726812 x)). Qed.
Lemma lem1726815 (x : real) : (term1449 x) = (term1450 x).
Proof. exact (eq_refl (term1449 x)). Qed.
Lemma lem1726816 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1726817 (x : real) : (term1451 x) = (term1452 x).
Proof. exact (MK_COMB (@lem1726816 x) (@lem1726815 x)). Qed.
Lemma lem1726818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726819 (x : real) : (term1453 x) = (term1454 x).
Proof. exact (MK_COMB (@lem1726818) (@lem1726817 x)). Qed.
Lemma lem1726820 (x : real) : (term1443 x) = (term1455 x).
Proof. exact (MK_COMB (@lem1726819 x) (@lem1726814 x)). Qed.
Lemma lem1726821 (x : real) : (term1456 x) = (term1456 x).
Proof. exact (eq_refl (term1456 x)). Qed.
Lemma lem1726822 (x : real) : ((term1441 x) = (term1443 x)) = ((term1441 x) = (term1455 x)).
Proof. exact (MK_COMB (@lem1726821 x) (@lem1726820 x)). Qed.
Lemma lem1726823 (x : real) : (term1441 x) = (term1455 x).
Proof. exact (EQ_MP (@lem1726822 x) (@lem1726811 x)). Qed.
Lemma lem1726824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726825 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726824) (@lem1724666 x)). Qed.
Lemma lem1726826 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726825 x) (@lem1724687 x)). Qed.
Lemma lem1726827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726828 : term999 = term999.
Proof. exact (MK_COMB (@lem1726827) (@lem1725193)). Qed.
Lemma lem1726829 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1726828) (@lem1725214)). Qed.
Lemma lem1726830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726831 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726830) (@lem1724687 x)). Qed.
Lemma lem1726832 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1726831 x) (@lem1726829)). Qed.
Lemma lem1726833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726834 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726833) (@lem1724687 x)). Qed.
Lemma lem1726835 (x : real) : (term1029 x) = (term1029 x).
Proof. exact (MK_COMB (@lem1726834 x) (@lem1726832 x)). Qed.
Lemma lem1726836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726837 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726836) (@lem1724639 x)). Qed.
Lemma lem1726838 (x : real) : (term1457 x) = (term1457 x).
Proof. exact (MK_COMB (@lem1726837 x) (@lem1726835 x)). Qed.
Lemma lem1726839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726840 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726839) (@lem1726826 x)). Qed.
Lemma lem1726841 (x : real) : (term1450 x) = (term1450 x).
Proof. exact (MK_COMB (@lem1726840 x) (@lem1726838 x)). Qed.
Lemma lem1726842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726843 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726842) (@lem1724639 x)). Qed.
Lemma lem1726844 (x : real) : (term1452 x) = (term1452 x).
Proof. exact (MK_COMB (@lem1726843 x) (@lem1726841 x)). Qed.
Lemma lem1726845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726846 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726845) (@lem1724666 x)). Qed.
Lemma lem1726847 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726846 x) (@lem1724687 x)). Qed.
Lemma lem1726848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726849 : term999 = term999.
Proof. exact (MK_COMB (@lem1726848) (@lem1725193)). Qed.
Lemma lem1726850 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1726849) (@lem1725214)). Qed.
Lemma lem1726851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726852 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726851) (@lem1724687 x)). Qed.
Lemma lem1726853 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1726852 x) (@lem1726850)). Qed.
Lemma lem1726854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726855 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726854) (@lem1724781 x)). Qed.
Lemma lem1726856 (x : real) : (term1031 x) = (term1032 x).
Proof. exact (MK_COMB (@lem1726855 x) (@lem1726853 x)). Qed.
Lemma lem1726857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726858 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726857) (@lem1724639 x)). Qed.
Lemma lem1726859 (x : real) : (term1458 x) = (term1459 x).
Proof. exact (MK_COMB (@lem1726858 x) (@lem1726856 x)). Qed.
Lemma lem1726860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726861 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726860) (@lem1726847 x)). Qed.
Lemma lem1726862 (x : real) : (term1446 x) = (term1460 x).
Proof. exact (MK_COMB (@lem1726861 x) (@lem1726859 x)). Qed.
Lemma lem1726863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726864 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726863) (@lem1724751 x)). Qed.
Lemma lem1726865 (x : real) : (term1448 x) = (term1461 x).
Proof. exact (MK_COMB (@lem1726864 x) (@lem1726862 x)). Qed.
Lemma lem1726866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726867 (x : real) : (term1454 x) = (term1454 x).
Proof. exact (MK_COMB (@lem1726866) (@lem1726844 x)). Qed.
Lemma lem1726868 (x : real) : (term1455 x) = (term1462 x).
Proof. exact (MK_COMB (@lem1726867 x) (@lem1726865 x)). Qed.
Lemma lem1726879 (x : real) : (term1441 x) = (term1462 x).
Proof. exact (TRANS (@lem1726823 x) (@lem1726868 x)). Qed.
Lemma lem1726880 (x : real) : (term1440 x) = (term1462 x).
Proof. exact (TRANS (@lem1726807 x) (@lem1726879 x)). Qed.
Lemma lem1726881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726882 (x : real) : (term1463 x) = (term1464 x).
Proof. exact (MK_COMB (@lem1726881) (@lem1726720 x)). Qed.
Lemma lem1726883 (x : real) : (term763 x) = (term1465 x).
Proof. exact (MK_COMB (@lem1726882 x) (@lem1726880 x)). Qed.
Lemma lem1726885 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1726886 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1726885 x term76). Qed.
Lemma lem1726893 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1726894 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726895 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1726894) (@lem1726893 x)). Qed.
Lemma lem1726896 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726897 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1726895 x) (@lem1726896)). Qed.
Lemma lem1726910 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1726911 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726910 x) (@lem1726897 x)). Qed.
Lemma lem1726912 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1726886 x) (@lem1726911 x)). Qed.
Lemma lem1726913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726914 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726913) (@lem1726912 x)). Qed.
Lemma lem1726915 (x : real) : (term635 x) = (term635 x).
Proof. exact (eq_refl (term635 x)). Qed.
Lemma lem1726916 (x : real) : (term1466 x) = (term1467 x).
Proof. exact (MK_COMB (@lem1726914 x) (@lem1726915 x)). Qed.
Lemma lem1726917 (x : real) : (term1468 x) = (term1467 x).
Proof. exact (eq_refl (term1468 x)). Qed.
Lemma lem1726918 (x : real) : (term1467 x) = (term1468 x).
Proof. exact (SYM (@lem1726917 x)). Qed.
Lemma lem1726919 (x : real) : (term1468 x) = (term1469 x).
Proof. exact (@lem1482981 (term1470 x) x). Qed.
Lemma lem1726920 (x : real) : (term1467 x) = (term1469 x).
Proof. exact (TRANS (@lem1726918 x) (@lem1726919 x)). Qed.
Lemma lem1726921 (x : real) : (term1471 x) = (term1472 x).
Proof. exact (eq_refl (term1471 x)). Qed.
Lemma lem1726922 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1726923 (x : real) : (term1473 x) = (term1474 x).
Proof. exact (MK_COMB (@lem1726922 x) (@lem1726921 x)). Qed.
Lemma lem1726924 (x : real) : (term1475 x) = (term1476 x).
Proof. exact (eq_refl (term1475 x)). Qed.
Lemma lem1726925 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1726926 (x : real) : (term1477 x) = (term1478 x).
Proof. exact (MK_COMB (@lem1726925 x) (@lem1726924 x)). Qed.
Lemma lem1726927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726928 (x : real) : (term1479 x) = (term1480 x).
Proof. exact (MK_COMB (@lem1726927) (@lem1726926 x)). Qed.
Lemma lem1726929 (x : real) : (term1469 x) = (term1481 x).
Proof. exact (MK_COMB (@lem1726928 x) (@lem1726923 x)). Qed.
Lemma lem1726930 (x : real) : (term1482 x) = (term1482 x).
Proof. exact (eq_refl (term1482 x)). Qed.
Lemma lem1726931 (x : real) : ((term1467 x) = (term1469 x)) = ((term1467 x) = (term1481 x)).
Proof. exact (MK_COMB (@lem1726930 x) (@lem1726929 x)). Qed.
Lemma lem1726932 (x : real) : (term1467 x) = (term1481 x).
Proof. exact (EQ_MP (@lem1726931 x) (@lem1726920 x)). Qed.
Lemma lem1726933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726934 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726933) (@lem1724666 x)). Qed.
Lemma lem1726935 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726934 x) (@lem1724687 x)). Qed.
Lemma lem1726936 : term346 = term1483.
Proof. exact (@lem1483525 term331 term76). Qed.
Lemma lem1726948 : term1484 = term1485.
Proof. exact (@lem1483519 term331 term76). Qed.
Lemma lem1726950 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1726951 : term184 = term76.
Proof. exact (@lem1726950 term185). Qed.
Lemma lem1726952 : term1486 = term1486.
Proof. exact (eq_refl term1486). Qed.
Lemma lem1726953 : term1485 = term1487.
Proof. exact (MK_COMB (@lem1726952) (@lem1726951)). Qed.
Lemma lem1726954 : term1487 = term331.
Proof. exact (@lem1483450 term331). Qed.
Lemma lem1726955 : term1485 = term331.
Proof. exact (TRANS (@lem1726953) (@lem1726954)). Qed.
Lemma lem1726957 : term1484 = term331.
Proof. exact (TRANS (@lem1726948) (@lem1726955)). Qed.
Lemma lem1726958 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1726959 : term1488 = term344.
Proof. exact (MK_COMB (@lem1726958) (@lem1726957)). Qed.
Lemma lem1726960 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1726961 : term1483 = term346.
Proof. exact (MK_COMB (@lem1726959) (@lem1726960)). Qed.
Lemma lem1726962 : term346 = term346.
Proof. exact (TRANS (@lem1726936) (@lem1726961)). Qed.
Lemma lem1726963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726964 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1726963) (@lem1725350 x)). Qed.
Lemma lem1726965 (x : real) : (term523 x) = (term523 x).
Proof. exact (MK_COMB (@lem1726964 x) (@lem1726962)). Qed.
Lemma lem1726966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726967 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1726966) (@lem1724687 x)). Qed.
Lemma lem1726968 (x : real) : (term1489 x) = (term1489 x).
Proof. exact (MK_COMB (@lem1726967 x) (@lem1726965 x)). Qed.
Lemma lem1726969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726970 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726969) (@lem1724639 x)). Qed.
Lemma lem1726971 (x : real) : (term1490 x) = (term1490 x).
Proof. exact (MK_COMB (@lem1726970 x) (@lem1726968 x)). Qed.
Lemma lem1726972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726973 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726972) (@lem1726935 x)). Qed.
Lemma lem1726974 (x : real) : (term1476 x) = (term1476 x).
Proof. exact (MK_COMB (@lem1726973 x) (@lem1726971 x)). Qed.
Lemma lem1726975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726976 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726975) (@lem1724639 x)). Qed.
Lemma lem1726977 (x : real) : (term1478 x) = (term1478 x).
Proof. exact (MK_COMB (@lem1726976 x) (@lem1726974 x)). Qed.
Lemma lem1726978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726979 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726978) (@lem1724666 x)). Qed.
Lemma lem1726980 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1726979 x) (@lem1724687 x)). Qed.
Lemma lem1726981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726982 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1726981) (@lem1725350 x)). Qed.
Lemma lem1726983 (x : real) : (term523 x) = (term523 x).
Proof. exact (MK_COMB (@lem1726982 x) (@lem1726962)). Qed.
Lemma lem1726984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726985 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726984) (@lem1724781 x)). Qed.
Lemma lem1726986 (x : real) : (term1491 x) = (term1492 x).
Proof. exact (MK_COMB (@lem1726985 x) (@lem1726983 x)). Qed.
Lemma lem1726987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726988 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1726987) (@lem1724639 x)). Qed.
Lemma lem1726989 (x : real) : (term1493 x) = (term1494 x).
Proof. exact (MK_COMB (@lem1726988 x) (@lem1726986 x)). Qed.
Lemma lem1726990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726991 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1726990) (@lem1726980 x)). Qed.
Lemma lem1726992 (x : real) : (term1472 x) = (term1495 x).
Proof. exact (MK_COMB (@lem1726991 x) (@lem1726989 x)). Qed.
Lemma lem1726993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1726994 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1726993) (@lem1724751 x)). Qed.
Lemma lem1726995 (x : real) : (term1474 x) = (term1496 x).
Proof. exact (MK_COMB (@lem1726994 x) (@lem1726992 x)). Qed.
Lemma lem1726996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1726997 (x : real) : (term1480 x) = (term1480 x).
Proof. exact (MK_COMB (@lem1726996) (@lem1726977 x)). Qed.
Lemma lem1726998 (x : real) : (term1481 x) = (term1497 x).
Proof. exact (MK_COMB (@lem1726997 x) (@lem1726995 x)). Qed.
Lemma lem1726999 (x : real) : (term1467 x) = (term1497 x).
Proof. exact (TRANS (@lem1726932 x) (@lem1726998 x)). Qed.
Lemma lem1727001 (x : real) : (term1498 x) = (term1496 x).
Proof. exact (eq_refl (term1498 x)). Qed.
Lemma lem1727002 (x : real) : (term1496 x) = (term1498 x).
Proof. exact (SYM (@lem1727001 x)). Qed.
Lemma lem1727003 (x : real) : (term1498 x) = (term1499 x).
Proof. exact (@lem1482981 (term1500 x) term76). Qed.
Lemma lem1727004 (x : real) : (term1496 x) = (term1499 x).
Proof. exact (TRANS (@lem1727002 x) (@lem1727003 x)). Qed.
Lemma lem1727005 (x : real) : (term1501 x) = (term1502 x).
Proof. exact (eq_refl (term1501 x)). Qed.
Lemma lem1727006 : term999 = term999.
Proof. exact (eq_refl term999). Qed.
Lemma lem1727007 (x : real) : (term1503 x) = (term1504 x).
Proof. exact (MK_COMB (@lem1727006) (@lem1727005 x)). Qed.
Lemma lem1727008 (x : real) : (term1505 x) = (term1506 x).
Proof. exact (eq_refl (term1505 x)). Qed.
Lemma lem1727009 : term1507 = term1507.
Proof. exact (eq_refl term1507). Qed.
Lemma lem1727010 (x : real) : (term1508 x) = (term1509 x).
Proof. exact (MK_COMB (@lem1727009) (@lem1727008 x)). Qed.
Lemma lem1727011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727012 (x : real) : (term1510 x) = (term1511 x).
Proof. exact (MK_COMB (@lem1727011) (@lem1727010 x)). Qed.
Lemma lem1727013 (x : real) : (term1499 x) = (term1512 x).
Proof. exact (MK_COMB (@lem1727012 x) (@lem1727007 x)). Qed.
Lemma lem1727014 (x : real) : (term1513 x) = (term1513 x).
Proof. exact (eq_refl (term1513 x)). Qed.
Lemma lem1727015 (x : real) : ((term1496 x) = (term1499 x)) = ((term1496 x) = (term1512 x)).
Proof. exact (MK_COMB (@lem1727014 x) (@lem1727013 x)). Qed.
Lemma lem1727016 (x : real) : (term1496 x) = (term1512 x).
Proof. exact (EQ_MP (@lem1727015 x) (@lem1727004 x)). Qed.
Lemma lem1727017 : term1514 = term1515.
Proof. exact (@lem1483527 term76 term76). Qed.
Lemma lem1727023 : term891 = term892.
Proof. exact (@lem1483519 term76 term76). Qed.
Lemma lem1727025 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727026 : term184 = term76.
Proof. exact (@lem1727025 term185). Qed.
Lemma lem1727027 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1727028 : term892 = term894.
Proof. exact (MK_COMB (@lem1727027) (@lem1727026)). Qed.
Lemma lem1727029 : term894 = term76.
Proof. exact (@lem1483448 term76). Qed.
Lemma lem1727030 : term892 = term76.
Proof. exact (TRANS (@lem1727028) (@lem1727029)). Qed.
Lemma lem1727032 : term891 = term76.
Proof. exact (TRANS (@lem1727023) (@lem1727030)). Qed.
Lemma lem1727033 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1727034 : term1516 = term1517.
Proof. exact (MK_COMB (@lem1727033) (@lem1727032)). Qed.
Lemma lem1727035 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727036 : term1515 = term1514.
Proof. exact (MK_COMB (@lem1727034) (@lem1727035)). Qed.
Lemma lem1727037 : term1514 = term1514.
Proof. exact (TRANS (@lem1727017) (@lem1727036)). Qed.
Lemma lem1727038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727039 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727038) (@lem1724666 x)). Qed.
Lemma lem1727040 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727039 x) (@lem1724687 x)). Qed.
Lemma lem1727041 : term1518 = term1519.
Proof. exact (@lem1483525 term912 term76). Qed.
Lemma lem1727042 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727049 : term912 = term73.
Proof. exact (@lem1483448 term73). Qed.
Lemma lem1727050 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1727051 : term1520 = term1521.
Proof. exact (MK_COMB (@lem1727050) (@lem1727049)). Qed.
Lemma lem1727052 : term1522 = term1094.
Proof. exact (MK_COMB (@lem1727051) (@lem1727042)). Qed.
Lemma lem1727053 : term1094 = term1095.
Proof. exact (@lem1483519 term73 term76). Qed.
Lemma lem1727055 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727056 : term184 = term76.
Proof. exact (@lem1727055 term185). Qed.
Lemma lem1727057 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1727058 : term1095 = term1097.
Proof. exact (MK_COMB (@lem1727057) (@lem1727056)). Qed.
Lemma lem1727059 : term1097 = term73.
Proof. exact (@lem1483450 term73). Qed.
Lemma lem1727060 : term1095 = term73.
Proof. exact (TRANS (@lem1727058) (@lem1727059)). Qed.
Lemma lem1727061 : term1094 = term73.
Proof. exact (TRANS (@lem1727053) (@lem1727060)). Qed.
Lemma lem1727062 : term1522 = term73.
Proof. exact (TRANS (@lem1727052) (@lem1727061)). Qed.
Lemma lem1727063 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727064 : term1523 = term914.
Proof. exact (MK_COMB (@lem1727063) (@lem1727062)). Qed.
Lemma lem1727065 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727066 : term1519 = term915.
Proof. exact (MK_COMB (@lem1727064) (@lem1727065)). Qed.
Lemma lem1727067 : term1518 = term915.
Proof. exact (TRANS (@lem1727041) (@lem1727066)). Qed.
Lemma lem1727068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727069 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727068) (@lem1725350 x)). Qed.
Lemma lem1727070 (x : real) : (term1524 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1727069 x) (@lem1727067)). Qed.
Lemma lem1727071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727072 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727071) (@lem1724666 x)). Qed.
Lemma lem1727073 (x : real) : (term1526 x) = (term1527 x).
Proof. exact (MK_COMB (@lem1727072 x) (@lem1727070 x)). Qed.
Lemma lem1727074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727075 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727074) (@lem1724639 x)). Qed.
Lemma lem1727076 (x : real) : (term1528 x) = (term1529 x).
Proof. exact (MK_COMB (@lem1727075 x) (@lem1727073 x)). Qed.
Lemma lem1727077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727078 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727077) (@lem1727040 x)). Qed.
Lemma lem1727079 (x : real) : (term1530 x) = (term1531 x).
Proof. exact (MK_COMB (@lem1727078 x) (@lem1727076 x)). Qed.
Lemma lem1727080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727081 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727080) (@lem1724666 x)). Qed.
Lemma lem1727082 (x : real) : (term1506 x) = (term1532 x).
Proof. exact (MK_COMB (@lem1727081 x) (@lem1727079 x)). Qed.
Lemma lem1727083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727084 : term1507 = term1507.
Proof. exact (MK_COMB (@lem1727083) (@lem1727037)). Qed.
Lemma lem1727085 (x : real) : (term1509 x) = (term1533 x).
Proof. exact (MK_COMB (@lem1727084) (@lem1727082 x)). Qed.
Lemma lem1727086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727087 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727086) (@lem1724666 x)). Qed.
Lemma lem1727088 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727087 x) (@lem1724687 x)). Qed.
Lemma lem1727089 : term1534 = term1535.
Proof. exact (@lem1483525 term1536 term76). Qed.
Lemma lem1727090 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727091 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1727095 : term1537 = term184.
Proof. exact (@lem1483512 term76). Qed.
Lemma lem1727097 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727098 : term184 = term76.
Proof. exact (@lem1727097 term185). Qed.
Lemma lem1727100 : term1537 = term76.
Proof. exact (TRANS (@lem1727095) (@lem1727098)). Qed.
Lemma lem1727101 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1727102 : term1538 = term893.
Proof. exact (MK_COMB (@lem1727101) (@lem1727100)). Qed.
Lemma lem1727103 : term1536 = term912.
Proof. exact (MK_COMB (@lem1727102) (@lem1727091)). Qed.
Lemma lem1727104 : term912 = term73.
Proof. exact (@lem1483448 term73). Qed.
Lemma lem1727105 : term1536 = term73.
Proof. exact (TRANS (@lem1727103) (@lem1727104)). Qed.
Lemma lem1727106 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1727107 : term1539 = term1521.
Proof. exact (MK_COMB (@lem1727106) (@lem1727105)). Qed.
Lemma lem1727108 : term1540 = term1094.
Proof. exact (MK_COMB (@lem1727107) (@lem1727090)). Qed.
Lemma lem1727109 : term1094 = term1095.
Proof. exact (@lem1483519 term73 term76). Qed.
Lemma lem1727111 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727112 : term184 = term76.
Proof. exact (@lem1727111 term185). Qed.
Lemma lem1727113 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1727114 : term1095 = term1097.
Proof. exact (MK_COMB (@lem1727113) (@lem1727112)). Qed.
Lemma lem1727115 : term1097 = term73.
Proof. exact (@lem1483450 term73). Qed.
Lemma lem1727116 : term1095 = term73.
Proof. exact (TRANS (@lem1727114) (@lem1727115)). Qed.
Lemma lem1727117 : term1094 = term73.
Proof. exact (TRANS (@lem1727109) (@lem1727116)). Qed.
Lemma lem1727118 : term1540 = term73.
Proof. exact (TRANS (@lem1727108) (@lem1727117)). Qed.
Lemma lem1727119 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727120 : term1541 = term914.
Proof. exact (MK_COMB (@lem1727119) (@lem1727118)). Qed.
Lemma lem1727121 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727122 : term1535 = term915.
Proof. exact (MK_COMB (@lem1727120) (@lem1727121)). Qed.
Lemma lem1727123 : term1534 = term915.
Proof. exact (TRANS (@lem1727089) (@lem1727122)). Qed.
Lemma lem1727124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727125 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727124) (@lem1725350 x)). Qed.
Lemma lem1727126 (x : real) : (term1542 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1727125 x) (@lem1727123)). Qed.
Lemma lem1727127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727128 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727127) (@lem1724666 x)). Qed.
Lemma lem1727129 (x : real) : (term1543 x) = (term1527 x).
Proof. exact (MK_COMB (@lem1727128 x) (@lem1727126 x)). Qed.
Lemma lem1727130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727131 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727130) (@lem1724639 x)). Qed.
Lemma lem1727132 (x : real) : (term1544 x) = (term1529 x).
Proof. exact (MK_COMB (@lem1727131 x) (@lem1727129 x)). Qed.
Lemma lem1727133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727134 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727133) (@lem1727088 x)). Qed.
Lemma lem1727135 (x : real) : (term1545 x) = (term1531 x).
Proof. exact (MK_COMB (@lem1727134 x) (@lem1727132 x)). Qed.
Lemma lem1727136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727137 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727136) (@lem1724666 x)). Qed.
Lemma lem1727138 (x : real) : (term1502 x) = (term1532 x).
Proof. exact (MK_COMB (@lem1727137 x) (@lem1727135 x)). Qed.
Lemma lem1727139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727140 : term999 = term999.
Proof. exact (MK_COMB (@lem1727139) (@lem1725193)). Qed.
Lemma lem1727141 (x : real) : (term1504 x) = (term1546 x).
Proof. exact (MK_COMB (@lem1727140) (@lem1727138 x)). Qed.
Lemma lem1727142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727143 (x : real) : (term1511 x) = (term1547 x).
Proof. exact (MK_COMB (@lem1727142) (@lem1727085 x)). Qed.
Lemma lem1727144 (x : real) : (term1512 x) = (term1548 x).
Proof. exact (MK_COMB (@lem1727143 x) (@lem1727141 x)). Qed.
Lemma lem1727156 (x : real) : (term1496 x) = (term1548 x).
Proof. exact (TRANS (@lem1727016 x) (@lem1727144 x)). Qed.
Lemma lem1727158 (x : real) : (term1549 x) = (term1478 x).
Proof. exact (eq_refl (term1549 x)). Qed.
Lemma lem1727159 (x : real) : (term1478 x) = (term1549 x).
Proof. exact (SYM (@lem1727158 x)). Qed.
Lemma lem1727160 (x : real) : (term1549 x) = (term1550 x).
Proof. exact (@lem1482981 (term1551 x) term76). Qed.
Lemma lem1727161 (x : real) : (term1478 x) = (term1550 x).
Proof. exact (TRANS (@lem1727159 x) (@lem1727160 x)). Qed.
Lemma lem1727162 (x : real) : (term1552 x) = (term1553 x).
Proof. exact (eq_refl (term1552 x)). Qed.
Lemma lem1727163 : term999 = term999.
Proof. exact (eq_refl term999). Qed.
Lemma lem1727164 (x : real) : (term1554 x) = (term1555 x).
Proof. exact (MK_COMB (@lem1727163) (@lem1727162 x)). Qed.
Lemma lem1727165 (x : real) : (term1556 x) = (term1557 x).
Proof. exact (eq_refl (term1556 x)). Qed.
Lemma lem1727166 : term1507 = term1507.
Proof. exact (eq_refl term1507). Qed.
Lemma lem1727167 (x : real) : (term1558 x) = (term1559 x).
Proof. exact (MK_COMB (@lem1727166) (@lem1727165 x)). Qed.
Lemma lem1727168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727169 (x : real) : (term1560 x) = (term1561 x).
Proof. exact (MK_COMB (@lem1727168) (@lem1727167 x)). Qed.
Lemma lem1727170 (x : real) : (term1550 x) = (term1562 x).
Proof. exact (MK_COMB (@lem1727169 x) (@lem1727164 x)). Qed.
Lemma lem1727171 (x : real) : (term1563 x) = (term1563 x).
Proof. exact (eq_refl (term1563 x)). Qed.
Lemma lem1727172 (x : real) : ((term1478 x) = (term1550 x)) = ((term1478 x) = (term1562 x)).
Proof. exact (MK_COMB (@lem1727171 x) (@lem1727170 x)). Qed.
Lemma lem1727173 (x : real) : (term1478 x) = (term1562 x).
Proof. exact (EQ_MP (@lem1727172 x) (@lem1727161 x)). Qed.
Lemma lem1727174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727175 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727174) (@lem1724666 x)). Qed.
Lemma lem1727176 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727175 x) (@lem1724687 x)). Qed.
Lemma lem1727177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727178 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727177) (@lem1725350 x)). Qed.
Lemma lem1727179 (x : real) : (term1524 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1727178 x) (@lem1727067)). Qed.
Lemma lem1727180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727181 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1727180) (@lem1724687 x)). Qed.
Lemma lem1727182 (x : real) : (term1564 x) = (term1565 x).
Proof. exact (MK_COMB (@lem1727181 x) (@lem1727179 x)). Qed.
Lemma lem1727183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727184 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727183) (@lem1724639 x)). Qed.
Lemma lem1727185 (x : real) : (term1566 x) = (term1567 x).
Proof. exact (MK_COMB (@lem1727184 x) (@lem1727182 x)). Qed.
Lemma lem1727186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727187 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727186) (@lem1727176 x)). Qed.
Lemma lem1727188 (x : real) : (term1568 x) = (term1569 x).
Proof. exact (MK_COMB (@lem1727187 x) (@lem1727185 x)). Qed.
Lemma lem1727189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727190 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727189) (@lem1724639 x)). Qed.
Lemma lem1727191 (x : real) : (term1557 x) = (term1570 x).
Proof. exact (MK_COMB (@lem1727190 x) (@lem1727188 x)). Qed.
Lemma lem1727192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727193 : term1507 = term1507.
Proof. exact (MK_COMB (@lem1727192) (@lem1727037)). Qed.
Lemma lem1727194 (x : real) : (term1559 x) = (term1571 x).
Proof. exact (MK_COMB (@lem1727193) (@lem1727191 x)). Qed.
Lemma lem1727195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727196 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727195) (@lem1724666 x)). Qed.
Lemma lem1727197 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727196 x) (@lem1724687 x)). Qed.
Lemma lem1727198 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727199 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727198) (@lem1725350 x)). Qed.
Lemma lem1727200 (x : real) : (term1542 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1727199 x) (@lem1727123)). Qed.
Lemma lem1727201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727202 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1727201) (@lem1724687 x)). Qed.
Lemma lem1727203 (x : real) : (term1572 x) = (term1565 x).
Proof. exact (MK_COMB (@lem1727202 x) (@lem1727200 x)). Qed.
Lemma lem1727204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727205 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727204) (@lem1724639 x)). Qed.
Lemma lem1727206 (x : real) : (term1573 x) = (term1567 x).
Proof. exact (MK_COMB (@lem1727205 x) (@lem1727203 x)). Qed.
Lemma lem1727207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727208 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727207) (@lem1727197 x)). Qed.
Lemma lem1727209 (x : real) : (term1574 x) = (term1569 x).
Proof. exact (MK_COMB (@lem1727208 x) (@lem1727206 x)). Qed.
Lemma lem1727210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727211 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727210) (@lem1724639 x)). Qed.
Lemma lem1727212 (x : real) : (term1553 x) = (term1570 x).
Proof. exact (MK_COMB (@lem1727211 x) (@lem1727209 x)). Qed.
Lemma lem1727213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727214 : term999 = term999.
Proof. exact (MK_COMB (@lem1727213) (@lem1725193)). Qed.
Lemma lem1727215 (x : real) : (term1555 x) = (term1575 x).
Proof. exact (MK_COMB (@lem1727214) (@lem1727212 x)). Qed.
Lemma lem1727216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727217 (x : real) : (term1561 x) = (term1576 x).
Proof. exact (MK_COMB (@lem1727216) (@lem1727194 x)). Qed.
Lemma lem1727218 (x : real) : (term1562 x) = (term1577 x).
Proof. exact (MK_COMB (@lem1727217 x) (@lem1727215 x)). Qed.
Lemma lem1727230 (x : real) : (term1478 x) = (term1577 x).
Proof. exact (TRANS (@lem1727173 x) (@lem1727218 x)). Qed.
Lemma lem1727231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727232 (x : real) : (term1480 x) = (term1578 x).
Proof. exact (MK_COMB (@lem1727231) (@lem1727230 x)). Qed.
Lemma lem1727233 (x : real) : (term1497 x) = (term1579 x).
Proof. exact (MK_COMB (@lem1727232 x) (@lem1727156 x)). Qed.
Lemma lem1727234 (x : real) : (term1467 x) = (term1579 x).
Proof. exact (TRANS (@lem1726999 x) (@lem1727233 x)). Qed.
Lemma lem1727235 (x : real) : (term1466 x) = (term1579 x).
Proof. exact (TRANS (@lem1726916 x) (@lem1727234 x)). Qed.
Lemma lem1727237 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727238 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1727237 x term76). Qed.
Lemma lem1727245 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727246 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727247 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1727246) (@lem1727245 x)). Qed.
Lemma lem1727248 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727249 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1727247 x) (@lem1727248)). Qed.
Lemma lem1727262 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1727263 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727262 x) (@lem1727249 x)). Qed.
Lemma lem1727264 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1727238 x) (@lem1727263 x)). Qed.
Lemma lem1727265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727266 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727265) (@lem1727264 x)). Qed.
Lemma lem1727268 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727269 : term342 = term1580.
Proof. exact (@lem1727268 term24 term76 term76). Qed.
Lemma lem1727276 : term1581 = term76.
Proof. exact (@lem1483458 term24). Qed.
Lemma lem1727279 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1727280 : term1582 = term881.
Proof. exact (MK_COMB (@lem1727279) (@lem1727276)). Qed.
Lemma lem1727281 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1727282 : term1582 = term24.
Proof. exact (TRANS (@lem1727280) (@lem1727281)). Qed.
Lemma lem1727283 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727284 : term1583 = term1116.
Proof. exact (MK_COMB (@lem1727283) (@lem1727282)). Qed.
Lemma lem1727285 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727286 : term1584 = term1117.
Proof. exact (MK_COMB (@lem1727284) (@lem1727285)). Qed.
Lemma lem1727293 : term184 = term76.
Proof. exact (@lem1483458 term73). Qed.
Lemma lem1727296 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1727297 : term879 = term881.
Proof. exact (MK_COMB (@lem1727296) (@lem1727293)). Qed.
Lemma lem1727298 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1727299 : term879 = term24.
Proof. exact (TRANS (@lem1727297) (@lem1727298)). Qed.
Lemma lem1727300 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727301 : term1585 = term1116.
Proof. exact (MK_COMB (@lem1727300) (@lem1727299)). Qed.
Lemma lem1727302 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727303 : term1586 = term1117.
Proof. exact (MK_COMB (@lem1727301) (@lem1727302)). Qed.
Lemma lem1727304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727305 : term1587 = term1135.
Proof. exact (MK_COMB (@lem1727304) (@lem1727303)). Qed.
Lemma lem1727306 : term1580 = term1588.
Proof. exact (MK_COMB (@lem1727305) (@lem1727286)). Qed.
Lemma lem1727307 : term342 = term1588.
Proof. exact (TRANS (@lem1727269) (@lem1727306)). Qed.
Lemma lem1727308 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1727309 (x : real) : (term524 x) = (term1589 x).
Proof. exact (MK_COMB (@lem1727308 x) (@lem1727307)). Qed.
Lemma lem1727310 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1727311 (x : real) : (term554 x) = (term1590 x).
Proof. exact (MK_COMB (@lem1727310 x) (@lem1727309 x)). Qed.
Lemma lem1727312 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1727313 (x : real) : (term636 x) = (term1591 x).
Proof. exact (MK_COMB (@lem1727312 x) (@lem1727311 x)). Qed.
Lemma lem1727314 (x : real) : (term1592 x) = (term1593 x).
Proof. exact (MK_COMB (@lem1727266 x) (@lem1727313 x)). Qed.
Lemma lem1727315 (x : real) : (term1594 x) = (term1593 x).
Proof. exact (eq_refl (term1594 x)). Qed.
Lemma lem1727316 (x : real) : (term1593 x) = (term1594 x).
Proof. exact (SYM (@lem1727315 x)). Qed.
Lemma lem1727317 (x : real) : (term1594 x) = (term1595 x).
Proof. exact (@lem1482981 (term1596 x) x). Qed.
Lemma lem1727318 (x : real) : (term1593 x) = (term1595 x).
Proof. exact (TRANS (@lem1727316 x) (@lem1727317 x)). Qed.
Lemma lem1727319 (x : real) : (term1597 x) = (term1598 x).
Proof. exact (eq_refl (term1597 x)). Qed.
Lemma lem1727320 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1727321 (x : real) : (term1599 x) = (term1600 x).
Proof. exact (MK_COMB (@lem1727320 x) (@lem1727319 x)). Qed.
Lemma lem1727322 (x : real) : (term1601 x) = (term1602 x).
Proof. exact (eq_refl (term1601 x)). Qed.
Lemma lem1727323 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1727324 (x : real) : (term1603 x) = (term1604 x).
Proof. exact (MK_COMB (@lem1727323 x) (@lem1727322 x)). Qed.
Lemma lem1727325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727326 (x : real) : (term1605 x) = (term1606 x).
Proof. exact (MK_COMB (@lem1727325) (@lem1727324 x)). Qed.
Lemma lem1727327 (x : real) : (term1595 x) = (term1607 x).
Proof. exact (MK_COMB (@lem1727326 x) (@lem1727321 x)). Qed.
Lemma lem1727328 (x : real) : (term1608 x) = (term1608 x).
Proof. exact (eq_refl (term1608 x)). Qed.
Lemma lem1727329 (x : real) : ((term1593 x) = (term1595 x)) = ((term1593 x) = (term1607 x)).
Proof. exact (MK_COMB (@lem1727328 x) (@lem1727327 x)). Qed.
Lemma lem1727330 (x : real) : (term1593 x) = (term1607 x).
Proof. exact (EQ_MP (@lem1727329 x) (@lem1727318 x)). Qed.
Lemma lem1727331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727332 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727331) (@lem1724666 x)). Qed.
Lemma lem1727333 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727332 x) (@lem1724687 x)). Qed.
Lemma lem1727334 : term1117 = term1609.
Proof. exact (@lem1483525 term24 term76). Qed.
Lemma lem1727340 : term878 = term879.
Proof. exact (@lem1483519 term24 term76). Qed.
Lemma lem1727342 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727343 : term184 = term76.
Proof. exact (@lem1727342 term185). Qed.
Lemma lem1727344 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1727345 : term879 = term881.
Proof. exact (MK_COMB (@lem1727344) (@lem1727343)). Qed.
Lemma lem1727346 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1727347 : term879 = term24.
Proof. exact (TRANS (@lem1727345) (@lem1727346)). Qed.
Lemma lem1727349 : term878 = term24.
Proof. exact (TRANS (@lem1727340) (@lem1727347)). Qed.
Lemma lem1727350 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727351 : term1610 = term1116.
Proof. exact (MK_COMB (@lem1727350) (@lem1727349)). Qed.
Lemma lem1727352 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727353 : term1609 = term1117.
Proof. exact (MK_COMB (@lem1727351) (@lem1727352)). Qed.
Lemma lem1727354 : term1117 = term1117.
Proof. exact (TRANS (@lem1727334) (@lem1727353)). Qed.
Lemma lem1727355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727356 : term1135 = term1135.
Proof. exact (MK_COMB (@lem1727355) (@lem1727354)). Qed.
Lemma lem1727357 : term1588 = term1588.
Proof. exact (MK_COMB (@lem1727356) (@lem1727354)). Qed.
Lemma lem1727358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727359 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727358) (@lem1725350 x)). Qed.
Lemma lem1727360 (x : real) : (term1589 x) = (term1589 x).
Proof. exact (MK_COMB (@lem1727359 x) (@lem1727357)). Qed.
Lemma lem1727361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727362 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1727361) (@lem1724687 x)). Qed.
Lemma lem1727363 (x : real) : (term1611 x) = (term1611 x).
Proof. exact (MK_COMB (@lem1727362 x) (@lem1727360 x)). Qed.
Lemma lem1727364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727365 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727364) (@lem1724639 x)). Qed.
Lemma lem1727366 (x : real) : (term1612 x) = (term1612 x).
Proof. exact (MK_COMB (@lem1727365 x) (@lem1727363 x)). Qed.
Lemma lem1727367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727368 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727367) (@lem1727333 x)). Qed.
Lemma lem1727369 (x : real) : (term1602 x) = (term1602 x).
Proof. exact (MK_COMB (@lem1727368 x) (@lem1727366 x)). Qed.
Lemma lem1727370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727371 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727370) (@lem1724639 x)). Qed.
Lemma lem1727372 (x : real) : (term1604 x) = (term1604 x).
Proof. exact (MK_COMB (@lem1727371 x) (@lem1727369 x)). Qed.
Lemma lem1727373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727374 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727373) (@lem1724666 x)). Qed.
Lemma lem1727375 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727374 x) (@lem1724687 x)). Qed.
Lemma lem1727376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727377 : term1135 = term1135.
Proof. exact (MK_COMB (@lem1727376) (@lem1727354)). Qed.
Lemma lem1727378 : term1588 = term1588.
Proof. exact (MK_COMB (@lem1727377) (@lem1727354)). Qed.
Lemma lem1727379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727380 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727379) (@lem1725350 x)). Qed.
Lemma lem1727381 (x : real) : (term1589 x) = (term1589 x).
Proof. exact (MK_COMB (@lem1727380 x) (@lem1727378)). Qed.
Lemma lem1727382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727383 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727382) (@lem1724781 x)). Qed.
Lemma lem1727384 (x : real) : (term1613 x) = (term1614 x).
Proof. exact (MK_COMB (@lem1727383 x) (@lem1727381 x)). Qed.
Lemma lem1727385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727386 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727385) (@lem1724639 x)). Qed.
Lemma lem1727387 (x : real) : (term1615 x) = (term1616 x).
Proof. exact (MK_COMB (@lem1727386 x) (@lem1727384 x)). Qed.
Lemma lem1727388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727389 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727388) (@lem1727375 x)). Qed.
Lemma lem1727390 (x : real) : (term1598 x) = (term1617 x).
Proof. exact (MK_COMB (@lem1727389 x) (@lem1727387 x)). Qed.
Lemma lem1727391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727392 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727391) (@lem1724751 x)). Qed.
Lemma lem1727393 (x : real) : (term1600 x) = (term1618 x).
Proof. exact (MK_COMB (@lem1727392 x) (@lem1727390 x)). Qed.
Lemma lem1727394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727395 (x : real) : (term1606 x) = (term1606 x).
Proof. exact (MK_COMB (@lem1727394) (@lem1727372 x)). Qed.
Lemma lem1727396 (x : real) : (term1607 x) = (term1619 x).
Proof. exact (MK_COMB (@lem1727395 x) (@lem1727393 x)). Qed.
Lemma lem1727407 (x : real) : (term1593 x) = (term1619 x).
Proof. exact (TRANS (@lem1727330 x) (@lem1727396 x)). Qed.
Lemma lem1727408 (x : real) : (term1592 x) = (term1619 x).
Proof. exact (TRANS (@lem1727314 x) (@lem1727407 x)). Qed.
Lemma lem1727409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727410 (x : real) : (term1620 x) = (term1621 x).
Proof. exact (MK_COMB (@lem1727409) (@lem1727235 x)). Qed.
Lemma lem1727411 (x : real) : (term761 x) = (term1622 x).
Proof. exact (MK_COMB (@lem1727410 x) (@lem1727408 x)). Qed.
Lemma lem1727412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727413 (x : real) : (term765 x) = (term1623 x).
Proof. exact (MK_COMB (@lem1727412) (@lem1726883 x)). Qed.
Lemma lem1727414 (x : real) : (term766 x) = (term1624 x).
Proof. exact (MK_COMB (@lem1727413 x) (@lem1727411 x)). Qed.
Lemma lem1727416 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727417 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1727416 x term76). Qed.
Lemma lem1727424 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727425 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727426 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1727425) (@lem1727424 x)). Qed.
Lemma lem1727427 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727428 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1727426 x) (@lem1727427)). Qed.
Lemma lem1727441 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1727442 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727441 x) (@lem1727428 x)). Qed.
Lemma lem1727443 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1727417 x) (@lem1727442 x)). Qed.
Lemma lem1727444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727445 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727444) (@lem1727443 x)). Qed.
Lemma lem1727447 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727448 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1727447 x term76). Qed.
Lemma lem1727455 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727456 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1727457 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1727456) (@lem1727455 x)). Qed.
Lemma lem1727458 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727459 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1727457 x) (@lem1727458)). Qed.
Lemma lem1727472 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1727473 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727472 x) (@lem1727459 x)). Qed.
Lemma lem1727474 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1727448 x) (@lem1727473 x)). Qed.
Lemma lem1727475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727476 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727475) (@lem1727474 x)). Qed.
Lemma lem1727477 (x : real) : (term693 x) = (term693 x).
Proof. exact (eq_refl (term693 x)). Qed.
Lemma lem1727478 (x : real) : (term709 x) = (term1226 x).
Proof. exact (MK_COMB (@lem1727476 x) (@lem1727477 x)). Qed.
Lemma lem1727479 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1727480 (x : real) : (term753 x) = (term1625 x).
Proof. exact (MK_COMB (@lem1727479 x) (@lem1727478 x)). Qed.
Lemma lem1727481 (x : real) : (term1626 x) = (term1627 x).
Proof. exact (MK_COMB (@lem1727445 x) (@lem1727480 x)). Qed.
Lemma lem1727482 (x : real) : (term1628 x) = (term1627 x).
Proof. exact (eq_refl (term1628 x)). Qed.
Lemma lem1727483 (x : real) : (term1627 x) = (term1628 x).
Proof. exact (SYM (@lem1727482 x)). Qed.
Lemma lem1727484 (x : real) : (term1628 x) = (term1629 x).
Proof. exact (@lem1482981 (term1630 x) term24). Qed.
Lemma lem1727485 (x : real) : (term1627 x) = (term1629 x).
Proof. exact (TRANS (@lem1727483 x) (@lem1727484 x)). Qed.
Lemma lem1727486 (x : real) : (term1631 x) = (term1632 x).
Proof. exact (eq_refl (term1631 x)). Qed.
Lemma lem1727487 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1727488 (x : real) : (term1633 x) = (term1634 x).
Proof. exact (MK_COMB (@lem1727487) (@lem1727486 x)). Qed.
Lemma lem1727489 (x : real) : (term1635 x) = (term1636 x).
Proof. exact (eq_refl (term1635 x)). Qed.
Lemma lem1727490 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1727491 (x : real) : (term1637 x) = (term1638 x).
Proof. exact (MK_COMB (@lem1727490) (@lem1727489 x)). Qed.
Lemma lem1727492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727493 (x : real) : (term1639 x) = (term1640 x).
Proof. exact (MK_COMB (@lem1727492) (@lem1727491 x)). Qed.
Lemma lem1727494 (x : real) : (term1629 x) = (term1641 x).
Proof. exact (MK_COMB (@lem1727493 x) (@lem1727488 x)). Qed.
Lemma lem1727495 (x : real) : (term1642 x) = (term1642 x).
Proof. exact (eq_refl (term1642 x)). Qed.
Lemma lem1727496 (x : real) : ((term1627 x) = (term1629 x)) = ((term1627 x) = (term1641 x)).
Proof. exact (MK_COMB (@lem1727495 x) (@lem1727494 x)). Qed.
Lemma lem1727497 (x : real) : (term1627 x) = (term1641 x).
Proof. exact (EQ_MP (@lem1727496 x) (@lem1727485 x)). Qed.
Lemma lem1727498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727499 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727498) (@lem1724666 x)). Qed.
Lemma lem1727500 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727499 x) (@lem1724687 x)). Qed.
Lemma lem1727501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727502 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727501) (@lem1725350 x)). Qed.
Lemma lem1727503 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727502 x) (@lem1724639 x)). Qed.
Lemma lem1727504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727505 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1727504) (@lem1724687 x)). Qed.
Lemma lem1727506 (x : real) : (term1251 x) = (term1252 x).
Proof. exact (MK_COMB (@lem1727505 x) (@lem1725951)). Qed.
Lemma lem1727507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727508 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727507) (@lem1727503 x)). Qed.
Lemma lem1727509 (x : real) : (term1253 x) = (term1254 x).
Proof. exact (MK_COMB (@lem1727508 x) (@lem1727506 x)). Qed.
Lemma lem1727510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727511 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727510) (@lem1724639 x)). Qed.
Lemma lem1727512 (x : real) : (term1643 x) = (term1644 x).
Proof. exact (MK_COMB (@lem1727511 x) (@lem1727509 x)). Qed.
Lemma lem1727513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727514 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727513) (@lem1727500 x)). Qed.
Lemma lem1727515 (x : real) : (term1636 x) = (term1645 x).
Proof. exact (MK_COMB (@lem1727514 x) (@lem1727512 x)). Qed.
Lemma lem1727516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727517 : term869 = term869.
Proof. exact (MK_COMB (@lem1727516) (@lem1724838)). Qed.
Lemma lem1727518 (x : real) : (term1638 x) = (term1646 x).
Proof. exact (MK_COMB (@lem1727517) (@lem1727515 x)). Qed.
Lemma lem1727519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727520 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727519) (@lem1724666 x)). Qed.
Lemma lem1727521 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727520 x) (@lem1724687 x)). Qed.
Lemma lem1727522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727523 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727522) (@lem1725350 x)). Qed.
Lemma lem1727524 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727523 x) (@lem1724639 x)). Qed.
Lemma lem1727525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727526 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1727525) (@lem1724687 x)). Qed.
Lemma lem1727527 (x : real) : (term1266 x) = (term899 x).
Proof. exact (MK_COMB (@lem1727526 x) (@lem1726001)). Qed.
Lemma lem1727528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727529 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727528) (@lem1727524 x)). Qed.
Lemma lem1727530 (x : real) : (term1267 x) = (term1268 x).
Proof. exact (MK_COMB (@lem1727529 x) (@lem1727527 x)). Qed.
Lemma lem1727531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727532 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727531) (@lem1724639 x)). Qed.
Lemma lem1727533 (x : real) : (term1647 x) = (term1648 x).
Proof. exact (MK_COMB (@lem1727532 x) (@lem1727530 x)). Qed.
Lemma lem1727534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727535 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727534) (@lem1727521 x)). Qed.
Lemma lem1727536 (x : real) : (term1632 x) = (term1649 x).
Proof. exact (MK_COMB (@lem1727535 x) (@lem1727533 x)). Qed.
Lemma lem1727537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727538 : term864 = term946.
Proof. exact (MK_COMB (@lem1727537) (@lem1724916)). Qed.
Lemma lem1727539 (x : real) : (term1634 x) = (term1650 x).
Proof. exact (MK_COMB (@lem1727538) (@lem1727536 x)). Qed.
Lemma lem1727540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727541 (x : real) : (term1640 x) = (term1651 x).
Proof. exact (MK_COMB (@lem1727540) (@lem1727518 x)). Qed.
Lemma lem1727542 (x : real) : (term1641 x) = (term1652 x).
Proof. exact (MK_COMB (@lem1727541 x) (@lem1727539 x)). Qed.
Lemma lem1727553 (x : real) : (term1627 x) = (term1652 x).
Proof. exact (TRANS (@lem1727497 x) (@lem1727542 x)). Qed.
Lemma lem1727554 (x : real) : (term1626 x) = (term1652 x).
Proof. exact (TRANS (@lem1727481 x) (@lem1727553 x)). Qed.
Lemma lem1727556 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727557 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1727556 x term76). Qed.
Lemma lem1727564 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727565 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727566 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1727565) (@lem1727564 x)). Qed.
Lemma lem1727567 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727568 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1727566 x) (@lem1727567)). Qed.
Lemma lem1727581 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1727582 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727581 x) (@lem1727568 x)). Qed.
Lemma lem1727583 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1727557 x) (@lem1727582 x)). Qed.
Lemma lem1727584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727585 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727584) (@lem1727583 x)). Qed.
Lemma lem1727587 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727588 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1727587 x term76). Qed.
Lemma lem1727595 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727596 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1727597 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1727596) (@lem1727595 x)). Qed.
Lemma lem1727598 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727599 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1727597 x) (@lem1727598)). Qed.
Lemma lem1727612 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1727613 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727612 x) (@lem1727599 x)). Qed.
Lemma lem1727614 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1727588 x) (@lem1727613 x)). Qed.
Lemma lem1727615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727616 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727615) (@lem1727614 x)). Qed.
Lemma lem1727618 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727619 : term284 = term1275.
Proof. exact (@lem1727618 term73 term24 term76). Qed.
Lemma lem1727626 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1727629 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1727630 : term1276 = term1261.
Proof. exact (MK_COMB (@lem1727629) (@lem1727626)). Qed.
Lemma lem1727632 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1727633 : term1261 = term76.
Proof. exact (@lem1727632 term185). Qed.
Lemma lem1727634 : term1276 = term76.
Proof. exact (TRANS (@lem1727630) (@lem1727633)). Qed.
Lemma lem1727635 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727636 : term1277 = term896.
Proof. exact (MK_COMB (@lem1727635) (@lem1727634)). Qed.
Lemma lem1727637 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727638 : term1278 = term897.
Proof. exact (MK_COMB (@lem1727636) (@lem1727637)). Qed.
Lemma lem1727645 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1727648 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1727649 : term1279 = term918.
Proof. exact (MK_COMB (@lem1727648) (@lem1727645)). Qed.
Lemma lem1727650 : term918 = term919.
Proof. exact (@lem1367763 term185 term185). Qed.
Lemma lem1727651 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1727652 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1727653 : term922 = term923.
Proof. exact (EQ_MP (@lem1727652) (@lem1727651)). Qed.
Lemma lem1727654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1727655 : term924 = term925.
Proof. exact (MK_COMB (@lem1727654) (@lem1727653)). Qed.
Lemma lem1727656 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1727657 : term919 = term926.
Proof. exact (MK_COMB (@lem1727656) (@lem1727655)). Qed.
Lemma lem1727658 : term918 = term926.
Proof. exact (TRANS (@lem1727650) (@lem1727657)). Qed.
Lemma lem1727659 : term1279 = term926.
Proof. exact (TRANS (@lem1727649) (@lem1727658)). Qed.
Lemma lem1727660 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727661 : term1280 = term935.
Proof. exact (MK_COMB (@lem1727660) (@lem1727659)). Qed.
Lemma lem1727662 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727663 : term1281 = term936.
Proof. exact (MK_COMB (@lem1727661) (@lem1727662)). Qed.
Lemma lem1727664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727665 : term1282 = term1283.
Proof. exact (MK_COMB (@lem1727664) (@lem1727663)). Qed.
Lemma lem1727666 : term1275 = term1284.
Proof. exact (MK_COMB (@lem1727665) (@lem1727638)). Qed.
Lemma lem1727667 : term284 = term1284.
Proof. exact (TRANS (@lem1727619) (@lem1727666)). Qed.
Lemma lem1727668 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1727669 (x : real) : (term694 x) = (term1285 x).
Proof. exact (MK_COMB (@lem1727668 x) (@lem1727667)). Qed.
Lemma lem1727670 (x : real) : (term710 x) = (term1286 x).
Proof. exact (MK_COMB (@lem1727616 x) (@lem1727669 x)). Qed.
Lemma lem1727671 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1727672 (x : real) : (term754 x) = (term1653 x).
Proof. exact (MK_COMB (@lem1727671 x) (@lem1727670 x)). Qed.
Lemma lem1727675 (x : real) : (term1654 x) = (term1655 x).
Proof. exact (MK_COMB (@lem1727585 x) (@lem1727672 x)). Qed.
Lemma lem1727676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727677 (x : real) : (term1656 x) = (term1657 x).
Proof. exact (MK_COMB (@lem1727676) (@lem1727554 x)). Qed.
Lemma lem1727678 (x : real) : (term752 x) = (term1658 x).
Proof. exact (MK_COMB (@lem1727677 x) (@lem1727675 x)). Qed.
Lemma lem1727680 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727681 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1727680 x term76). Qed.
Lemma lem1727688 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727689 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727690 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1727689) (@lem1727688 x)). Qed.
Lemma lem1727691 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727692 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1727690 x) (@lem1727691)). Qed.
Lemma lem1727705 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1727706 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727705 x) (@lem1727692 x)). Qed.
Lemma lem1727707 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1727681 x) (@lem1727706 x)). Qed.
Lemma lem1727708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727709 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727708) (@lem1727707 x)). Qed.
Lemma lem1727711 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727712 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1727711 x term76). Qed.
Lemma lem1727719 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727720 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1727721 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1727720) (@lem1727719 x)). Qed.
Lemma lem1727722 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727723 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1727721 x) (@lem1727722)). Qed.
Lemma lem1727736 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1727737 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727736 x) (@lem1727723 x)). Qed.
Lemma lem1727738 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1727712 x) (@lem1727737 x)). Qed.
Lemma lem1727739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727740 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727739) (@lem1727738 x)). Qed.
Lemma lem1727741 (x : real) : (term689 x) = (term689 x).
Proof. exact (eq_refl (term689 x)). Qed.
Lemma lem1727742 (x : real) : (term705 x) = (term1659 x).
Proof. exact (MK_COMB (@lem1727740 x) (@lem1727741 x)). Qed.
Lemma lem1727743 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1727744 (x : real) : (term749 x) = (term1660 x).
Proof. exact (MK_COMB (@lem1727743 x) (@lem1727742 x)). Qed.
Lemma lem1727745 (x : real) : (term1661 x) = (term1662 x).
Proof. exact (MK_COMB (@lem1727709 x) (@lem1727744 x)). Qed.
Lemma lem1727746 (x : real) : (term1663 x) = (term1662 x).
Proof. exact (eq_refl (term1663 x)). Qed.
Lemma lem1727747 (x : real) : (term1662 x) = (term1663 x).
Proof. exact (SYM (@lem1727746 x)). Qed.
Lemma lem1727748 (x : real) : (term1663 x) = (term1664 x).
Proof. exact (@lem1482981 (term1665 x) term76). Qed.
Lemma lem1727749 (x : real) : (term1662 x) = (term1664 x).
Proof. exact (TRANS (@lem1727747 x) (@lem1727748 x)). Qed.
Lemma lem1727750 (x : real) : (term1666 x) = (term1667 x).
Proof. exact (eq_refl (term1666 x)). Qed.
Lemma lem1727751 : term999 = term999.
Proof. exact (eq_refl term999). Qed.
Lemma lem1727752 (x : real) : (term1668 x) = (term1669 x).
Proof. exact (MK_COMB (@lem1727751) (@lem1727750 x)). Qed.
Lemma lem1727753 (x : real) : (term1670 x) = (term1671 x).
Proof. exact (eq_refl (term1670 x)). Qed.
Lemma lem1727754 : term1507 = term1507.
Proof. exact (eq_refl term1507). Qed.
Lemma lem1727755 (x : real) : (term1672 x) = (term1673 x).
Proof. exact (MK_COMB (@lem1727754) (@lem1727753 x)). Qed.
Lemma lem1727756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727757 (x : real) : (term1674 x) = (term1675 x).
Proof. exact (MK_COMB (@lem1727756) (@lem1727755 x)). Qed.
Lemma lem1727758 (x : real) : (term1664 x) = (term1676 x).
Proof. exact (MK_COMB (@lem1727757 x) (@lem1727752 x)). Qed.
Lemma lem1727759 (x : real) : (term1677 x) = (term1677 x).
Proof. exact (eq_refl (term1677 x)). Qed.
Lemma lem1727760 (x : real) : ((term1662 x) = (term1664 x)) = ((term1662 x) = (term1676 x)).
Proof. exact (MK_COMB (@lem1727759 x) (@lem1727758 x)). Qed.
Lemma lem1727761 (x : real) : (term1662 x) = (term1676 x).
Proof. exact (EQ_MP (@lem1727760 x) (@lem1727749 x)). Qed.
Lemma lem1727762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727763 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727762) (@lem1724666 x)). Qed.
Lemma lem1727764 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727763 x) (@lem1724687 x)). Qed.
Lemma lem1727765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727766 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727765) (@lem1725350 x)). Qed.
Lemma lem1727767 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727766 x) (@lem1724639 x)). Qed.
Lemma lem1727768 : term1678 = term1679.
Proof. exact (@lem1483525 term1114 term76). Qed.
Lemma lem1727769 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727776 : term1114 = term24.
Proof. exact (@lem1483448 term24). Qed.
Lemma lem1727777 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1727778 : term1680 = term1681.
Proof. exact (MK_COMB (@lem1727777) (@lem1727776)). Qed.
Lemma lem1727779 : term1682 = term878.
Proof. exact (MK_COMB (@lem1727778) (@lem1727769)). Qed.
Lemma lem1727780 : term878 = term879.
Proof. exact (@lem1483519 term24 term76). Qed.
Lemma lem1727782 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727783 : term184 = term76.
Proof. exact (@lem1727782 term185). Qed.
Lemma lem1727784 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1727785 : term879 = term881.
Proof. exact (MK_COMB (@lem1727784) (@lem1727783)). Qed.
Lemma lem1727786 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1727787 : term879 = term24.
Proof. exact (TRANS (@lem1727785) (@lem1727786)). Qed.
Lemma lem1727788 : term878 = term24.
Proof. exact (TRANS (@lem1727780) (@lem1727787)). Qed.
Lemma lem1727789 : term1682 = term24.
Proof. exact (TRANS (@lem1727779) (@lem1727788)). Qed.
Lemma lem1727790 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727791 : term1683 = term1116.
Proof. exact (MK_COMB (@lem1727790) (@lem1727789)). Qed.
Lemma lem1727792 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727793 : term1679 = term1117.
Proof. exact (MK_COMB (@lem1727791) (@lem1727792)). Qed.
Lemma lem1727794 : term1678 = term1117.
Proof. exact (TRANS (@lem1727768) (@lem1727793)). Qed.
Lemma lem1727795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727796 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727795) (@lem1725350 x)). Qed.
Lemma lem1727797 (x : real) : (term1684 x) = (term1685 x).
Proof. exact (MK_COMB (@lem1727796 x) (@lem1727794)). Qed.
Lemma lem1727798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727799 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727798) (@lem1727767 x)). Qed.
Lemma lem1727800 (x : real) : (term1686 x) = (term1687 x).
Proof. exact (MK_COMB (@lem1727799 x) (@lem1727797 x)). Qed.
Lemma lem1727801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727802 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727801) (@lem1724639 x)). Qed.
Lemma lem1727803 (x : real) : (term1688 x) = (term1689 x).
Proof. exact (MK_COMB (@lem1727802 x) (@lem1727800 x)). Qed.
Lemma lem1727804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727805 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727804) (@lem1727764 x)). Qed.
Lemma lem1727806 (x : real) : (term1671 x) = (term1690 x).
Proof. exact (MK_COMB (@lem1727805 x) (@lem1727803 x)). Qed.
Lemma lem1727807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727808 : term1507 = term1507.
Proof. exact (MK_COMB (@lem1727807) (@lem1727037)). Qed.
Lemma lem1727809 (x : real) : (term1673 x) = (term1691 x).
Proof. exact (MK_COMB (@lem1727808) (@lem1727806 x)). Qed.
Lemma lem1727810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727811 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1727810) (@lem1724666 x)). Qed.
Lemma lem1727812 (x : real) : (term810 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727811 x) (@lem1724687 x)). Qed.
Lemma lem1727813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727814 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727813) (@lem1725350 x)). Qed.
Lemma lem1727815 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727814 x) (@lem1724639 x)). Qed.
Lemma lem1727816 : term1692 = term1693.
Proof. exact (@lem1483525 term1694 term76). Qed.
Lemma lem1727817 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727818 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1727822 : term1537 = term184.
Proof. exact (@lem1483512 term76). Qed.
Lemma lem1727824 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727825 : term184 = term76.
Proof. exact (@lem1727824 term185). Qed.
Lemma lem1727827 : term1537 = term76.
Proof. exact (TRANS (@lem1727822) (@lem1727825)). Qed.
Lemma lem1727828 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1727829 : term1538 = term893.
Proof. exact (MK_COMB (@lem1727828) (@lem1727827)). Qed.
Lemma lem1727830 : term1694 = term1114.
Proof. exact (MK_COMB (@lem1727829) (@lem1727818)). Qed.
Lemma lem1727831 : term1114 = term24.
Proof. exact (@lem1483448 term24). Qed.
Lemma lem1727832 : term1694 = term24.
Proof. exact (TRANS (@lem1727830) (@lem1727831)). Qed.
Lemma lem1727833 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1727834 : term1695 = term1681.
Proof. exact (MK_COMB (@lem1727833) (@lem1727832)). Qed.
Lemma lem1727835 : term1696 = term878.
Proof. exact (MK_COMB (@lem1727834) (@lem1727817)). Qed.
Lemma lem1727836 : term878 = term879.
Proof. exact (@lem1483519 term24 term76). Qed.
Lemma lem1727838 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1727839 : term184 = term76.
Proof. exact (@lem1727838 term185). Qed.
Lemma lem1727840 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1727841 : term879 = term881.
Proof. exact (MK_COMB (@lem1727840) (@lem1727839)). Qed.
Lemma lem1727842 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1727843 : term879 = term24.
Proof. exact (TRANS (@lem1727841) (@lem1727842)). Qed.
Lemma lem1727844 : term878 = term24.
Proof. exact (TRANS (@lem1727836) (@lem1727843)). Qed.
Lemma lem1727845 : term1696 = term24.
Proof. exact (TRANS (@lem1727835) (@lem1727844)). Qed.
Lemma lem1727846 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727847 : term1697 = term1116.
Proof. exact (MK_COMB (@lem1727846) (@lem1727845)). Qed.
Lemma lem1727848 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727849 : term1693 = term1117.
Proof. exact (MK_COMB (@lem1727847) (@lem1727848)). Qed.
Lemma lem1727850 : term1692 = term1117.
Proof. exact (TRANS (@lem1727816) (@lem1727849)). Qed.
Lemma lem1727851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727852 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1727851) (@lem1725350 x)). Qed.
Lemma lem1727853 (x : real) : (term1698 x) = (term1685 x).
Proof. exact (MK_COMB (@lem1727852 x) (@lem1727850)). Qed.
Lemma lem1727854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727855 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727854) (@lem1727815 x)). Qed.
Lemma lem1727856 (x : real) : (term1699 x) = (term1687 x).
Proof. exact (MK_COMB (@lem1727855 x) (@lem1727853 x)). Qed.
Lemma lem1727857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727858 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1727857) (@lem1724639 x)). Qed.
Lemma lem1727859 (x : real) : (term1700 x) = (term1689 x).
Proof. exact (MK_COMB (@lem1727858 x) (@lem1727856 x)). Qed.
Lemma lem1727860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727861 (x : real) : (term811 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727860) (@lem1727812 x)). Qed.
Lemma lem1727862 (x : real) : (term1667 x) = (term1690 x).
Proof. exact (MK_COMB (@lem1727861 x) (@lem1727859 x)). Qed.
Lemma lem1727863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727864 : term999 = term999.
Proof. exact (MK_COMB (@lem1727863) (@lem1725193)). Qed.
Lemma lem1727865 (x : real) : (term1669 x) = (term1701 x).
Proof. exact (MK_COMB (@lem1727864) (@lem1727862 x)). Qed.
Lemma lem1727866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727867 (x : real) : (term1675 x) = (term1702 x).
Proof. exact (MK_COMB (@lem1727866) (@lem1727809 x)). Qed.
Lemma lem1727868 (x : real) : (term1676 x) = (term1703 x).
Proof. exact (MK_COMB (@lem1727867 x) (@lem1727865 x)). Qed.
Lemma lem1727879 (x : real) : (term1662 x) = (term1703 x).
Proof. exact (TRANS (@lem1727761 x) (@lem1727868 x)). Qed.
Lemma lem1727880 (x : real) : (term1661 x) = (term1703 x).
Proof. exact (TRANS (@lem1727745 x) (@lem1727879 x)). Qed.
Lemma lem1727882 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727883 (x : real) : (term172 x) = (term806 x).
Proof. exact (@lem1727882 x term76). Qed.
Lemma lem1727890 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727891 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727892 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1727891) (@lem1727890 x)). Qed.
Lemma lem1727893 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727894 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1727892 x) (@lem1727893)). Qed.
Lemma lem1727907 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1727908 (x : real) : (term806 x) = (term810 x).
Proof. exact (MK_COMB (@lem1727907 x) (@lem1727894 x)). Qed.
Lemma lem1727909 (x : real) : (term172 x) = (term810 x).
Proof. exact (TRANS (@lem1727883 x) (@lem1727908 x)). Qed.
Lemma lem1727910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727911 (x : real) : (term384 x) = (term811 x).
Proof. exact (MK_COMB (@lem1727910) (@lem1727909 x)). Qed.
Lemma lem1727913 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727914 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1727913 x term76). Qed.
Lemma lem1727921 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1727922 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1727923 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1727922) (@lem1727921 x)). Qed.
Lemma lem1727924 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727925 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1727923 x) (@lem1727924)). Qed.
Lemma lem1727938 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1727939 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1727938 x) (@lem1727925 x)). Qed.
Lemma lem1727940 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1727914 x) (@lem1727939 x)). Qed.
Lemma lem1727941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727942 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1727941) (@lem1727940 x)). Qed.
Lemma lem1727944 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1727945 : term366 = term1704.
Proof. exact (@lem1727944 term73 term76 term76). Qed.
Lemma lem1727952 : term1581 = term76.
Proof. exact (@lem1483458 term24). Qed.
Lemma lem1727955 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1727956 : term1705 = term1097.
Proof. exact (MK_COMB (@lem1727955) (@lem1727952)). Qed.
Lemma lem1727957 : term1097 = term73.
Proof. exact (@lem1483450 term73). Qed.
Lemma lem1727958 : term1705 = term73.
Proof. exact (TRANS (@lem1727956) (@lem1727957)). Qed.
Lemma lem1727959 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727960 : term1706 = term914.
Proof. exact (MK_COMB (@lem1727959) (@lem1727958)). Qed.
Lemma lem1727961 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727962 : term1707 = term915.
Proof. exact (MK_COMB (@lem1727960) (@lem1727961)). Qed.
Lemma lem1727969 : term184 = term76.
Proof. exact (@lem1483458 term73). Qed.
Lemma lem1727972 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1727973 : term1095 = term1097.
Proof. exact (MK_COMB (@lem1727972) (@lem1727969)). Qed.
Lemma lem1727974 : term1097 = term73.
Proof. exact (@lem1483450 term73). Qed.
Lemma lem1727975 : term1095 = term73.
Proof. exact (TRANS (@lem1727973) (@lem1727974)). Qed.
Lemma lem1727976 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1727977 : term1708 = term914.
Proof. exact (MK_COMB (@lem1727976) (@lem1727975)). Qed.
Lemma lem1727978 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1727979 : term1709 = term915.
Proof. exact (MK_COMB (@lem1727977) (@lem1727978)). Qed.
Lemma lem1727980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1727981 : term1710 = term946.
Proof. exact (MK_COMB (@lem1727980) (@lem1727979)). Qed.
Lemma lem1727982 : term1704 = term1711.
Proof. exact (MK_COMB (@lem1727981) (@lem1727962)). Qed.
Lemma lem1727983 : term366 = term1711.
Proof. exact (TRANS (@lem1727945) (@lem1727982)). Qed.
Lemma lem1727984 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1727985 (x : real) : (term690 x) = (term1712 x).
Proof. exact (MK_COMB (@lem1727984 x) (@lem1727983)). Qed.
Lemma lem1727986 (x : real) : (term706 x) = (term1713 x).
Proof. exact (MK_COMB (@lem1727942 x) (@lem1727985 x)). Qed.
Lemma lem1727987 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1727988 (x : real) : (term750 x) = (term1714 x).
Proof. exact (MK_COMB (@lem1727987 x) (@lem1727986 x)). Qed.
Lemma lem1727991 (x : real) : (term1715 x) = (term1716 x).
Proof. exact (MK_COMB (@lem1727911 x) (@lem1727988 x)). Qed.
Lemma lem1727992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727993 (x : real) : (term1717 x) = (term1718 x).
Proof. exact (MK_COMB (@lem1727992) (@lem1727880 x)). Qed.
Lemma lem1727994 (x : real) : (term748 x) = (term1719 x).
Proof. exact (MK_COMB (@lem1727993 x) (@lem1727991 x)). Qed.
Lemma lem1727995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727996 (x : real) : (term756 x) = (term1720 x).
Proof. exact (MK_COMB (@lem1727995) (@lem1727678 x)). Qed.
Lemma lem1727997 (x : real) : (term757 x) = (term1721 x).
Proof. exact (MK_COMB (@lem1727996 x) (@lem1727994 x)). Qed.
Lemma lem1727998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1727999 (x : real) : (term768 x) = (term1722 x).
Proof. exact (MK_COMB (@lem1727998) (@lem1727414 x)). Qed.
Lemma lem1728000 (x : real) : (term769 x) = (term1723 x).
Proof. exact (MK_COMB (@lem1727999 x) (@lem1727997 x)). Qed.
Lemma lem1728001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728002 (x : real) : (term798 x) = (term1724 x).
Proof. exact (MK_COMB (@lem1728001) (@lem1726478 x)). Qed.
Lemma lem1728003 (x : real) : (term799 x) = (term1725 x).
Proof. exact (MK_COMB (@lem1728002 x) (@lem1728000 x)). Qed.
Lemma lem1728005 (x : real) : (term1726 x) = (term1727 x).
Proof. exact (eq_refl (term1726 x)). Qed.
Lemma lem1728006 (x : real) : (term1727 x) = (term1726 x).
Proof. exact (SYM (@lem1728005 x)). Qed.
Lemma lem1728007 (x : real) : (term1726 x) = (term1728 x).
Proof. exact (@lem1482981 (term1729 x) x). Qed.
Lemma lem1728008 (x : real) : (term1727 x) = (term1728 x).
Proof. exact (TRANS (@lem1728006 x) (@lem1728007 x)). Qed.
Lemma lem1728009 (x : real) : (term1730 x) = (term1731 x).
Proof. exact (eq_refl (term1730 x)). Qed.
Lemma lem1728010 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1728011 (x : real) : (term1732 x) = (term1733 x).
Proof. exact (MK_COMB (@lem1728010 x) (@lem1728009 x)). Qed.
Lemma lem1728012 (x : real) : (term1734 x) = (term1735 x).
Proof. exact (eq_refl (term1734 x)). Qed.
Lemma lem1728013 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1728014 (x : real) : (term1736 x) = (term1737 x).
Proof. exact (MK_COMB (@lem1728013 x) (@lem1728012 x)). Qed.
Lemma lem1728015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728016 (x : real) : (term1738 x) = (term1739 x).
Proof. exact (MK_COMB (@lem1728015) (@lem1728014 x)). Qed.
Lemma lem1728017 (x : real) : (term1728 x) = (term1740 x).
Proof. exact (MK_COMB (@lem1728016 x) (@lem1728011 x)). Qed.
Lemma lem1728018 (x : real) : (term1741 x) = (term1741 x).
Proof. exact (eq_refl (term1741 x)). Qed.
Lemma lem1728019 (x : real) : ((term1727 x) = (term1728 x)) = ((term1727 x) = (term1740 x)).
Proof. exact (MK_COMB (@lem1728018 x) (@lem1728017 x)). Qed.
Lemma lem1728020 (x : real) : (term1727 x) = (term1740 x).
Proof. exact (EQ_MP (@lem1728019 x) (@lem1728008 x)). Qed.
Lemma lem1728021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728022 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728021) (@lem1724687 x)). Qed.
Lemma lem1728023 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1728022 x) (@lem1724717)). Qed.
Lemma lem1728024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728025 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728024) (@lem1724687 x)). Qed.
Lemma lem1728026 (x : real) : (term842 x) = (term842 x).
Proof. exact (MK_COMB (@lem1728025 x) (@lem1728023 x)). Qed.
Lemma lem1728027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728028 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728027) (@lem1724666 x)). Qed.
Lemma lem1728029 (x : real) : (term843 x) = (term843 x).
Proof. exact (MK_COMB (@lem1728028 x) (@lem1728026 x)). Qed.
Lemma lem1728030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728031 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728030) (@lem1724639 x)). Qed.
Lemma lem1728032 (x : real) : (term1735 x) = (term1735 x).
Proof. exact (MK_COMB (@lem1728031 x) (@lem1728029 x)). Qed.
Lemma lem1728033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728034 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728033) (@lem1724639 x)). Qed.
Lemma lem1728035 (x : real) : (term1737 x) = (term1737 x).
Proof. exact (MK_COMB (@lem1728034 x) (@lem1728032 x)). Qed.
Lemma lem1728036 (x : real) : (term1742 x) = (term1743 x).
Proof. exact (@lem1483527 (real_neg x) term76). Qed.
Lemma lem1728037 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728044 (x : real) : (real_neg x) = (term176 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1728045 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1728046 (x : real) : (term847 x) = (term848 x).
Proof. exact (MK_COMB (@lem1728045) (@lem1728044 x)). Qed.
Lemma lem1728047 (x : real) : (term849 x) = (term831 x).
Proof. exact (MK_COMB (@lem1728046 x) (@lem1728037)). Qed.
Lemma lem1728048 (x : real) : (term831 x) = (term832 x).
Proof. exact (@lem1483519 (term176 x) term76). Qed.
Lemma lem1728050 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1728051 : term184 = term76.
Proof. exact (@lem1728050 term185). Qed.
Lemma lem1728052 (x : real) : (term833 x) = (term833 x).
Proof. exact (eq_refl (term833 x)). Qed.
Lemma lem1728053 (x : real) : (term832 x) = (term834 x).
Proof. exact (MK_COMB (@lem1728052 x) (@lem1728051)). Qed.
Lemma lem1728054 (x : real) : (term834 x) = (term176 x).
Proof. exact (@lem1483450 (term176 x)). Qed.
Lemma lem1728055 (x : real) : (term832 x) = (term176 x).
Proof. exact (TRANS (@lem1728053 x) (@lem1728054 x)). Qed.
Lemma lem1728056 (x : real) : (term831 x) = (term176 x).
Proof. exact (TRANS (@lem1728048 x) (@lem1728055 x)). Qed.
Lemma lem1728057 (x : real) : (term849 x) = (term176 x).
Proof. exact (TRANS (@lem1728047 x) (@lem1728056 x)). Qed.
Lemma lem1728058 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1728059 (x : real) : (term1744 x) = (term235 x).
Proof. exact (MK_COMB (@lem1728058) (@lem1728057 x)). Qed.
Lemma lem1728060 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728061 (x : real) : (term1743 x) = (term236 x).
Proof. exact (MK_COMB (@lem1728059 x) (@lem1728060)). Qed.
Lemma lem1728062 (x : real) : (term1742 x) = (term236 x).
Proof. exact (TRANS (@lem1728036 x) (@lem1728061 x)). Qed.
Lemma lem1728063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728064 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728063) (@lem1724687 x)). Qed.
Lemma lem1728065 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1728064 x) (@lem1724717)). Qed.
Lemma lem1728066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728067 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728066) (@lem1724781 x)). Qed.
Lemma lem1728068 (x : real) : (term852 x) = (term853 x).
Proof. exact (MK_COMB (@lem1728067 x) (@lem1728065 x)). Qed.
Lemma lem1728069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728070 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728069) (@lem1724666 x)). Qed.
Lemma lem1728071 (x : real) : (term854 x) = (term855 x).
Proof. exact (MK_COMB (@lem1728070 x) (@lem1728068 x)). Qed.
Lemma lem1728072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728073 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728072) (@lem1728062 x)). Qed.
Lemma lem1728074 (x : real) : (term1731 x) = (term1746 x).
Proof. exact (MK_COMB (@lem1728073 x) (@lem1728071 x)). Qed.
Lemma lem1728075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728076 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728075) (@lem1724751 x)). Qed.
Lemma lem1728077 (x : real) : (term1733 x) = (term1747 x).
Proof. exact (MK_COMB (@lem1728076 x) (@lem1728074 x)). Qed.
Lemma lem1728078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728079 (x : real) : (term1739 x) = (term1739 x).
Proof. exact (MK_COMB (@lem1728078) (@lem1728035 x)). Qed.
Lemma lem1728080 (x : real) : (term1740 x) = (term1748 x).
Proof. exact (MK_COMB (@lem1728079 x) (@lem1728077 x)). Qed.
Lemma lem1728081 (x : real) : (term1727 x) = (term1748 x).
Proof. exact (TRANS (@lem1728020 x) (@lem1728080 x)). Qed.
Lemma lem1728083 (x : real) : (term1749 x) = (term1747 x).
Proof. exact (eq_refl (term1749 x)). Qed.
Lemma lem1728084 (x : real) : (term1747 x) = (term1749 x).
Proof. exact (SYM (@lem1728083 x)). Qed.
Lemma lem1728085 (x : real) : (term1749 x) = (term1750 x).
Proof. exact (@lem1482981 (term1751 x) term24). Qed.
Lemma lem1728086 (x : real) : (term1747 x) = (term1750 x).
Proof. exact (TRANS (@lem1728084 x) (@lem1728085 x)). Qed.
Lemma lem1728087 (x : real) : (term1752 x) = (term1753 x).
Proof. exact (eq_refl (term1752 x)). Qed.
Lemma lem1728088 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1728089 (x : real) : (term1754 x) = (term1755 x).
Proof. exact (MK_COMB (@lem1728088) (@lem1728087 x)). Qed.
Lemma lem1728090 (x : real) : (term1756 x) = (term1757 x).
Proof. exact (eq_refl (term1756 x)). Qed.
Lemma lem1728091 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1728092 (x : real) : (term1758 x) = (term1759 x).
Proof. exact (MK_COMB (@lem1728091) (@lem1728090 x)). Qed.
Lemma lem1728093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728094 (x : real) : (term1760 x) = (term1761 x).
Proof. exact (MK_COMB (@lem1728093) (@lem1728092 x)). Qed.
Lemma lem1728095 (x : real) : (term1750 x) = (term1762 x).
Proof. exact (MK_COMB (@lem1728094 x) (@lem1728089 x)). Qed.
Lemma lem1728096 (x : real) : (term1763 x) = (term1763 x).
Proof. exact (eq_refl (term1763 x)). Qed.
Lemma lem1728097 (x : real) : ((term1747 x) = (term1750 x)) = ((term1747 x) = (term1762 x)).
Proof. exact (MK_COMB (@lem1728096 x) (@lem1728095 x)). Qed.
Lemma lem1728098 (x : real) : (term1747 x) = (term1762 x).
Proof. exact (EQ_MP (@lem1728097 x) (@lem1728086 x)). Qed.
Lemma lem1728099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728100 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728099) (@lem1724687 x)). Qed.
Lemma lem1728101 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1728100 x) (@lem1724870)). Qed.
Lemma lem1728102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728103 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728102) (@lem1724666 x)). Qed.
Lemma lem1728104 (x : real) : (term900 x) = (term901 x).
Proof. exact (MK_COMB (@lem1728103 x) (@lem1728101 x)). Qed.
Lemma lem1728105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728106 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728105) (@lem1724666 x)). Qed.
Lemma lem1728107 (x : real) : (term902 x) = (term903 x).
Proof. exact (MK_COMB (@lem1728106 x) (@lem1728104 x)). Qed.
Lemma lem1728108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728109 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728108) (@lem1725350 x)). Qed.
Lemma lem1728110 (x : real) : (term1764 x) = (term1765 x).
Proof. exact (MK_COMB (@lem1728109 x) (@lem1728107 x)). Qed.
Lemma lem1728111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728112 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728111) (@lem1724666 x)). Qed.
Lemma lem1728113 (x : real) : (term1757 x) = (term1766 x).
Proof. exact (MK_COMB (@lem1728112 x) (@lem1728110 x)). Qed.
Lemma lem1728114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728115 : term869 = term869.
Proof. exact (MK_COMB (@lem1728114) (@lem1724838)). Qed.
Lemma lem1728116 (x : real) : (term1759 x) = (term1767 x).
Proof. exact (MK_COMB (@lem1728115) (@lem1728113 x)). Qed.
Lemma lem1728117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728118 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728117) (@lem1724687 x)). Qed.
Lemma lem1728119 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1728118 x) (@lem1724954)). Qed.
Lemma lem1728120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728121 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728120) (@lem1724666 x)). Qed.
Lemma lem1728122 (x : real) : (term939 x) = (term940 x).
Proof. exact (MK_COMB (@lem1728121 x) (@lem1728119 x)). Qed.
Lemma lem1728123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728124 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728123) (@lem1724666 x)). Qed.
Lemma lem1728125 (x : real) : (term941 x) = (term942 x).
Proof. exact (MK_COMB (@lem1728124 x) (@lem1728122 x)). Qed.
Lemma lem1728126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728127 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728126) (@lem1725350 x)). Qed.
Lemma lem1728128 (x : real) : (term1768 x) = (term1769 x).
Proof. exact (MK_COMB (@lem1728127 x) (@lem1728125 x)). Qed.
Lemma lem1728129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728130 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728129) (@lem1724666 x)). Qed.
Lemma lem1728131 (x : real) : (term1753 x) = (term1770 x).
Proof. exact (MK_COMB (@lem1728130 x) (@lem1728128 x)). Qed.
Lemma lem1728132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728133 : term864 = term946.
Proof. exact (MK_COMB (@lem1728132) (@lem1724916)). Qed.
Lemma lem1728134 (x : real) : (term1755 x) = (term1771 x).
Proof. exact (MK_COMB (@lem1728133) (@lem1728131 x)). Qed.
Lemma lem1728135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728136 (x : real) : (term1761 x) = (term1772 x).
Proof. exact (MK_COMB (@lem1728135) (@lem1728116 x)). Qed.
Lemma lem1728137 (x : real) : (term1762 x) = (term1773 x).
Proof. exact (MK_COMB (@lem1728136 x) (@lem1728134 x)). Qed.
Lemma lem1728149 (x : real) : (term1747 x) = (term1773 x).
Proof. exact (TRANS (@lem1728098 x) (@lem1728137 x)). Qed.
Lemma lem1728151 (x : real) : (term1774 x) = (term1737 x).
Proof. exact (eq_refl (term1774 x)). Qed.
Lemma lem1728152 (x : real) : (term1737 x) = (term1774 x).
Proof. exact (SYM (@lem1728151 x)). Qed.
Lemma lem1728153 (x : real) : (term1774 x) = (term1775 x).
Proof. exact (@lem1482981 (term1776 x) term24). Qed.
Lemma lem1728154 (x : real) : (term1737 x) = (term1775 x).
Proof. exact (TRANS (@lem1728152 x) (@lem1728153 x)). Qed.
Lemma lem1728155 (x : real) : (term1777 x) = (term1778 x).
Proof. exact (eq_refl (term1777 x)). Qed.
Lemma lem1728156 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1728157 (x : real) : (term1779 x) = (term1780 x).
Proof. exact (MK_COMB (@lem1728156) (@lem1728155 x)). Qed.
Lemma lem1728158 (x : real) : (term1781 x) = (term1782 x).
Proof. exact (eq_refl (term1781 x)). Qed.
Lemma lem1728159 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1728160 (x : real) : (term1783 x) = (term1784 x).
Proof. exact (MK_COMB (@lem1728159) (@lem1728158 x)). Qed.
Lemma lem1728161 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728162 (x : real) : (term1785 x) = (term1786 x).
Proof. exact (MK_COMB (@lem1728161) (@lem1728160 x)). Qed.
Lemma lem1728163 (x : real) : (term1775 x) = (term1787 x).
Proof. exact (MK_COMB (@lem1728162 x) (@lem1728157 x)). Qed.
Lemma lem1728164 (x : real) : (term1788 x) = (term1788 x).
Proof. exact (eq_refl (term1788 x)). Qed.
Lemma lem1728165 (x : real) : ((term1737 x) = (term1775 x)) = ((term1737 x) = (term1787 x)).
Proof. exact (MK_COMB (@lem1728164 x) (@lem1728163 x)). Qed.
Lemma lem1728166 (x : real) : (term1737 x) = (term1787 x).
Proof. exact (EQ_MP (@lem1728165 x) (@lem1728154 x)). Qed.
Lemma lem1728167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728168 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728167) (@lem1724687 x)). Qed.
Lemma lem1728169 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1728168 x) (@lem1724870)). Qed.
Lemma lem1728170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728171 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728170) (@lem1724687 x)). Qed.
Lemma lem1728172 (x : real) : (term965 x) = (term966 x).
Proof. exact (MK_COMB (@lem1728171 x) (@lem1728169 x)). Qed.
Lemma lem1728173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728174 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728173) (@lem1724666 x)). Qed.
Lemma lem1728175 (x : real) : (term967 x) = (term968 x).
Proof. exact (MK_COMB (@lem1728174 x) (@lem1728172 x)). Qed.
Lemma lem1728176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728177 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728176) (@lem1724639 x)). Qed.
Lemma lem1728178 (x : real) : (term1789 x) = (term1790 x).
Proof. exact (MK_COMB (@lem1728177 x) (@lem1728175 x)). Qed.
Lemma lem1728179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728180 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728179) (@lem1724639 x)). Qed.
Lemma lem1728181 (x : real) : (term1782 x) = (term1791 x).
Proof. exact (MK_COMB (@lem1728180 x) (@lem1728178 x)). Qed.
Lemma lem1728182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728183 : term869 = term869.
Proof. exact (MK_COMB (@lem1728182) (@lem1724838)). Qed.
Lemma lem1728184 (x : real) : (term1784 x) = (term1792 x).
Proof. exact (MK_COMB (@lem1728183) (@lem1728181 x)). Qed.
Lemma lem1728185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728186 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728185) (@lem1724687 x)). Qed.
Lemma lem1728187 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1728186 x) (@lem1724954)). Qed.
Lemma lem1728188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728189 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728188) (@lem1724687 x)). Qed.
Lemma lem1728190 (x : real) : (term973 x) = (term974 x).
Proof. exact (MK_COMB (@lem1728189 x) (@lem1728187 x)). Qed.
Lemma lem1728191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728192 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728191) (@lem1724666 x)). Qed.
Lemma lem1728193 (x : real) : (term975 x) = (term976 x).
Proof. exact (MK_COMB (@lem1728192 x) (@lem1728190 x)). Qed.
Lemma lem1728194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728195 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728194) (@lem1724639 x)). Qed.
Lemma lem1728196 (x : real) : (term1793 x) = (term1794 x).
Proof. exact (MK_COMB (@lem1728195 x) (@lem1728193 x)). Qed.
Lemma lem1728197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728198 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728197) (@lem1724639 x)). Qed.
Lemma lem1728199 (x : real) : (term1778 x) = (term1795 x).
Proof. exact (MK_COMB (@lem1728198 x) (@lem1728196 x)). Qed.
Lemma lem1728200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728201 : term864 = term946.
Proof. exact (MK_COMB (@lem1728200) (@lem1724916)). Qed.
Lemma lem1728202 (x : real) : (term1780 x) = (term1796 x).
Proof. exact (MK_COMB (@lem1728201) (@lem1728199 x)). Qed.
Lemma lem1728203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728204 (x : real) : (term1786 x) = (term1797 x).
Proof. exact (MK_COMB (@lem1728203) (@lem1728184 x)). Qed.
Lemma lem1728205 (x : real) : (term1787 x) = (term1798 x).
Proof. exact (MK_COMB (@lem1728204 x) (@lem1728202 x)). Qed.
Lemma lem1728217 (x : real) : (term1737 x) = (term1798 x).
Proof. exact (TRANS (@lem1728166 x) (@lem1728205 x)). Qed.
Lemma lem1728218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728219 (x : real) : (term1739 x) = (term1799 x).
Proof. exact (MK_COMB (@lem1728218) (@lem1728217 x)). Qed.
Lemma lem1728220 (x : real) : (term1748 x) = (term1800 x).
Proof. exact (MK_COMB (@lem1728219 x) (@lem1728149 x)). Qed.
Lemma lem1728222 (x : real) : (term1727 x) = (term1800 x).
Proof. exact (TRANS (@lem1728081 x) (@lem1728220 x)). Qed.
Lemma lem1728224 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1728225 : term222 = term987.
Proof. exact (@lem1728224 term24 term24 term76). Qed.
Lemma lem1728232 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1728235 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1728236 : term989 = term990.
Proof. exact (MK_COMB (@lem1728235) (@lem1728232)). Qed.
Lemma lem1728237 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1728238 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1728239 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1728240 : term922 = term923.
Proof. exact (EQ_MP (@lem1728239) (@lem1728238)). Qed.
Lemma lem1728241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1728242 : term924 = term925.
Proof. exact (MK_COMB (@lem1728241) (@lem1728240)). Qed.
Lemma lem1728243 : term990 = term925.
Proof. exact (TRANS (@lem1728237) (@lem1728242)). Qed.
Lemma lem1728244 : term989 = term925.
Proof. exact (TRANS (@lem1728236) (@lem1728243)). Qed.
Lemma lem1728245 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1728246 : term991 = term992.
Proof. exact (MK_COMB (@lem1728245) (@lem1728244)). Qed.
Lemma lem1728247 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728248 : term993 = term994.
Proof. exact (MK_COMB (@lem1728246) (@lem1728247)). Qed.
Lemma lem1728255 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1728258 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1728259 : term995 = term886.
Proof. exact (MK_COMB (@lem1728258) (@lem1728255)). Qed.
Lemma lem1728261 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1728262 : term886 = term76.
Proof. exact (@lem1728261 term185). Qed.
Lemma lem1728263 : term995 = term76.
Proof. exact (TRANS (@lem1728259) (@lem1728262)). Qed.
Lemma lem1728264 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1728265 : term996 = term896.
Proof. exact (MK_COMB (@lem1728264) (@lem1728263)). Qed.
Lemma lem1728266 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728267 : term997 = term897.
Proof. exact (MK_COMB (@lem1728265) (@lem1728266)). Qed.
Lemma lem1728268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728269 : term998 = term999.
Proof. exact (MK_COMB (@lem1728268) (@lem1728267)). Qed.
Lemma lem1728270 : term987 = term1000.
Proof. exact (MK_COMB (@lem1728269) (@lem1728248)). Qed.
Lemma lem1728271 : term222 = term1000.
Proof. exact (TRANS (@lem1728225) (@lem1728270)). Qed.
Lemma lem1728272 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1728273 (x : real) : (term528 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1728272 x) (@lem1728271)). Qed.
Lemma lem1728274 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1728275 (x : real) : (term558 x) = (term1002 x).
Proof. exact (MK_COMB (@lem1728274 x) (@lem1728273 x)). Qed.
Lemma lem1728276 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1728277 (x : real) : (term671 x) = (term1003 x).
Proof. exact (MK_COMB (@lem1728276 x) (@lem1728275 x)). Qed.
Lemma lem1728278 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1728279 (x : real) : (term1801 x) = (term1802 x).
Proof. exact (MK_COMB (@lem1728278 x) (@lem1728277 x)). Qed.
Lemma lem1728280 (x : real) : (term1803 x) = (term1802 x).
Proof. exact (eq_refl (term1803 x)). Qed.
Lemma lem1728281 (x : real) : (term1802 x) = (term1803 x).
Proof. exact (SYM (@lem1728280 x)). Qed.
Lemma lem1728282 (x : real) : (term1803 x) = (term1804 x).
Proof. exact (@lem1482981 (term1805 x) x). Qed.
Lemma lem1728283 (x : real) : (term1802 x) = (term1804 x).
Proof. exact (TRANS (@lem1728281 x) (@lem1728282 x)). Qed.
Lemma lem1728284 (x : real) : (term1806 x) = (term1807 x).
Proof. exact (eq_refl (term1806 x)). Qed.
Lemma lem1728285 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1728286 (x : real) : (term1808 x) = (term1809 x).
Proof. exact (MK_COMB (@lem1728285 x) (@lem1728284 x)). Qed.
Lemma lem1728287 (x : real) : (term1810 x) = (term1811 x).
Proof. exact (eq_refl (term1810 x)). Qed.
Lemma lem1728288 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1728289 (x : real) : (term1812 x) = (term1813 x).
Proof. exact (MK_COMB (@lem1728288 x) (@lem1728287 x)). Qed.
Lemma lem1728290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728291 (x : real) : (term1814 x) = (term1815 x).
Proof. exact (MK_COMB (@lem1728290) (@lem1728289 x)). Qed.
Lemma lem1728292 (x : real) : (term1804 x) = (term1816 x).
Proof. exact (MK_COMB (@lem1728291 x) (@lem1728286 x)). Qed.
Lemma lem1728293 (x : real) : (term1817 x) = (term1817 x).
Proof. exact (eq_refl (term1817 x)). Qed.
Lemma lem1728294 (x : real) : ((term1802 x) = (term1804 x)) = ((term1802 x) = (term1816 x)).
Proof. exact (MK_COMB (@lem1728293 x) (@lem1728292 x)). Qed.
Lemma lem1728295 (x : real) : (term1802 x) = (term1816 x).
Proof. exact (EQ_MP (@lem1728294 x) (@lem1728283 x)). Qed.
Lemma lem1728296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728297 : term999 = term999.
Proof. exact (MK_COMB (@lem1728296) (@lem1725193)). Qed.
Lemma lem1728298 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1728297) (@lem1725214)). Qed.
Lemma lem1728299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728300 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728299) (@lem1724687 x)). Qed.
Lemma lem1728301 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1728300 x) (@lem1728298)). Qed.
Lemma lem1728302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728303 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728302) (@lem1724687 x)). Qed.
Lemma lem1728304 (x : real) : (term1029 x) = (term1029 x).
Proof. exact (MK_COMB (@lem1728303 x) (@lem1728301 x)). Qed.
Lemma lem1728305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728306 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728305) (@lem1724666 x)). Qed.
Lemma lem1728307 (x : real) : (term1030 x) = (term1030 x).
Proof. exact (MK_COMB (@lem1728306 x) (@lem1728304 x)). Qed.
Lemma lem1728308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728309 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728308) (@lem1724639 x)). Qed.
Lemma lem1728310 (x : real) : (term1811 x) = (term1811 x).
Proof. exact (MK_COMB (@lem1728309 x) (@lem1728307 x)). Qed.
Lemma lem1728311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728312 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728311) (@lem1724639 x)). Qed.
Lemma lem1728313 (x : real) : (term1813 x) = (term1813 x).
Proof. exact (MK_COMB (@lem1728312 x) (@lem1728310 x)). Qed.
Lemma lem1728314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728315 : term999 = term999.
Proof. exact (MK_COMB (@lem1728314) (@lem1725193)). Qed.
Lemma lem1728316 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1728315) (@lem1725214)). Qed.
Lemma lem1728317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728318 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728317) (@lem1724687 x)). Qed.
Lemma lem1728319 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1728318 x) (@lem1728316)). Qed.
Lemma lem1728320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728321 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728320) (@lem1724781 x)). Qed.
Lemma lem1728322 (x : real) : (term1031 x) = (term1032 x).
Proof. exact (MK_COMB (@lem1728321 x) (@lem1728319 x)). Qed.
Lemma lem1728323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728324 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728323) (@lem1724666 x)). Qed.
Lemma lem1728325 (x : real) : (term1033 x) = (term1034 x).
Proof. exact (MK_COMB (@lem1728324 x) (@lem1728322 x)). Qed.
Lemma lem1728326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728327 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728326) (@lem1728062 x)). Qed.
Lemma lem1728328 (x : real) : (term1807 x) = (term1818 x).
Proof. exact (MK_COMB (@lem1728327 x) (@lem1728325 x)). Qed.
Lemma lem1728329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728330 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728329) (@lem1724751 x)). Qed.
Lemma lem1728331 (x : real) : (term1809 x) = (term1819 x).
Proof. exact (MK_COMB (@lem1728330 x) (@lem1728328 x)). Qed.
Lemma lem1728332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728333 (x : real) : (term1815 x) = (term1815 x).
Proof. exact (MK_COMB (@lem1728332) (@lem1728313 x)). Qed.
Lemma lem1728334 (x : real) : (term1816 x) = (term1820 x).
Proof. exact (MK_COMB (@lem1728333 x) (@lem1728331 x)). Qed.
Lemma lem1728345 (x : real) : (term1802 x) = (term1820 x).
Proof. exact (TRANS (@lem1728295 x) (@lem1728334 x)). Qed.
Lemma lem1728346 (x : real) : (term1801 x) = (term1820 x).
Proof. exact (TRANS (@lem1728279 x) (@lem1728345 x)). Qed.
Lemma lem1728347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728348 (x : real) : (term1821 x) = (term1822 x).
Proof. exact (MK_COMB (@lem1728347) (@lem1728222 x)). Qed.
Lemma lem1728349 (x : real) : (term669 x) = (term1823 x).
Proof. exact (MK_COMB (@lem1728348 x) (@lem1728346 x)). Qed.
Lemma lem1728351 (x : real) : (term1824 x) = (term1825 x).
Proof. exact (eq_refl (term1824 x)). Qed.
Lemma lem1728352 (x : real) : (term1825 x) = (term1824 x).
Proof. exact (SYM (@lem1728351 x)). Qed.
Lemma lem1728353 (x : real) : (term1824 x) = (term1826 x).
Proof. exact (@lem1482981 (term1827 x) x). Qed.
Lemma lem1728354 (x : real) : (term1825 x) = (term1826 x).
Proof. exact (TRANS (@lem1728352 x) (@lem1728353 x)). Qed.
Lemma lem1728355 (x : real) : (term1828 x) = (term1829 x).
Proof. exact (eq_refl (term1828 x)). Qed.
Lemma lem1728356 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1728357 (x : real) : (term1830 x) = (term1831 x).
Proof. exact (MK_COMB (@lem1728356 x) (@lem1728355 x)). Qed.
Lemma lem1728358 (x : real) : (term1832 x) = (term1833 x).
Proof. exact (eq_refl (term1832 x)). Qed.
Lemma lem1728359 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1728360 (x : real) : (term1834 x) = (term1835 x).
Proof. exact (MK_COMB (@lem1728359 x) (@lem1728358 x)). Qed.
Lemma lem1728361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728362 (x : real) : (term1836 x) = (term1837 x).
Proof. exact (MK_COMB (@lem1728361) (@lem1728360 x)). Qed.
Lemma lem1728363 (x : real) : (term1826 x) = (term1838 x).
Proof. exact (MK_COMB (@lem1728362 x) (@lem1728357 x)). Qed.
Lemma lem1728364 (x : real) : (term1839 x) = (term1839 x).
Proof. exact (eq_refl (term1839 x)). Qed.
Lemma lem1728365 (x : real) : ((term1825 x) = (term1826 x)) = ((term1825 x) = (term1838 x)).
Proof. exact (MK_COMB (@lem1728364 x) (@lem1728363 x)). Qed.
Lemma lem1728366 (x : real) : (term1825 x) = (term1838 x).
Proof. exact (EQ_MP (@lem1728365 x) (@lem1728354 x)). Qed.
Lemma lem1728367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728368 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728367) (@lem1725350 x)). Qed.
Lemma lem1728369 (x : real) : (term580 x) = (term580 x).
Proof. exact (MK_COMB (@lem1728368 x) (@lem1725377)). Qed.
Lemma lem1728370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728371 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728370) (@lem1724687 x)). Qed.
Lemma lem1728372 (x : real) : (term1066 x) = (term1066 x).
Proof. exact (MK_COMB (@lem1728371 x) (@lem1728369 x)). Qed.
Lemma lem1728373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728374 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728373) (@lem1724666 x)). Qed.
Lemma lem1728375 (x : real) : (term1067 x) = (term1067 x).
Proof. exact (MK_COMB (@lem1728374 x) (@lem1728372 x)). Qed.
Lemma lem1728376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728377 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728376) (@lem1724639 x)). Qed.
Lemma lem1728378 (x : real) : (term1833 x) = (term1833 x).
Proof. exact (MK_COMB (@lem1728377 x) (@lem1728375 x)). Qed.
Lemma lem1728379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728380 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728379) (@lem1724639 x)). Qed.
Lemma lem1728381 (x : real) : (term1835 x) = (term1835 x).
Proof. exact (MK_COMB (@lem1728380 x) (@lem1728378 x)). Qed.
Lemma lem1728382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728383 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728382) (@lem1725350 x)). Qed.
Lemma lem1728384 (x : real) : (term580 x) = (term580 x).
Proof. exact (MK_COMB (@lem1728383 x) (@lem1725377)). Qed.
Lemma lem1728385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728386 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728385) (@lem1724781 x)). Qed.
Lemma lem1728387 (x : real) : (term1068 x) = (term1069 x).
Proof. exact (MK_COMB (@lem1728386 x) (@lem1728384 x)). Qed.
Lemma lem1728388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728389 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728388) (@lem1724666 x)). Qed.
Lemma lem1728390 (x : real) : (term1070 x) = (term1071 x).
Proof. exact (MK_COMB (@lem1728389 x) (@lem1728387 x)). Qed.
Lemma lem1728391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728392 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728391) (@lem1728062 x)). Qed.
Lemma lem1728393 (x : real) : (term1829 x) = (term1840 x).
Proof. exact (MK_COMB (@lem1728392 x) (@lem1728390 x)). Qed.
Lemma lem1728394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728395 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728394) (@lem1724751 x)). Qed.
Lemma lem1728396 (x : real) : (term1831 x) = (term1841 x).
Proof. exact (MK_COMB (@lem1728395 x) (@lem1728393 x)). Qed.
Lemma lem1728397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728398 (x : real) : (term1837 x) = (term1837 x).
Proof. exact (MK_COMB (@lem1728397) (@lem1728381 x)). Qed.
Lemma lem1728399 (x : real) : (term1838 x) = (term1842 x).
Proof. exact (MK_COMB (@lem1728398 x) (@lem1728396 x)). Qed.
Lemma lem1728400 (x : real) : (term1825 x) = (term1842 x).
Proof. exact (TRANS (@lem1728366 x) (@lem1728399 x)). Qed.
Lemma lem1728402 (x : real) : (term1843 x) = (term1841 x).
Proof. exact (eq_refl (term1843 x)). Qed.
Lemma lem1728403 (x : real) : (term1841 x) = (term1843 x).
Proof. exact (SYM (@lem1728402 x)). Qed.
Lemma lem1728404 (x : real) : (term1843 x) = (term1844 x).
Proof. exact (@lem1482981 (term1845 x) term73). Qed.
Lemma lem1728405 (x : real) : (term1841 x) = (term1844 x).
Proof. exact (TRANS (@lem1728403 x) (@lem1728404 x)). Qed.
Lemma lem1728406 (x : real) : (term1846 x) = (term1847 x).
Proof. exact (eq_refl (term1846 x)). Qed.
Lemma lem1728407 : term1080 = term1080.
Proof. exact (eq_refl term1080). Qed.
Lemma lem1728408 (x : real) : (term1848 x) = (term1849 x).
Proof. exact (MK_COMB (@lem1728407) (@lem1728406 x)). Qed.
Lemma lem1728409 (x : real) : (term1850 x) = (term1851 x).
Proof. exact (eq_refl (term1850 x)). Qed.
Lemma lem1728410 : term1085 = term1085.
Proof. exact (eq_refl term1085). Qed.
Lemma lem1728411 (x : real) : (term1852 x) = (term1853 x).
Proof. exact (MK_COMB (@lem1728410) (@lem1728409 x)). Qed.
Lemma lem1728412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728413 (x : real) : (term1854 x) = (term1855 x).
Proof. exact (MK_COMB (@lem1728412) (@lem1728411 x)). Qed.
Lemma lem1728414 (x : real) : (term1844 x) = (term1856 x).
Proof. exact (MK_COMB (@lem1728413 x) (@lem1728408 x)). Qed.
Lemma lem1728415 (x : real) : (term1857 x) = (term1857 x).
Proof. exact (eq_refl (term1857 x)). Qed.
Lemma lem1728416 (x : real) : ((term1841 x) = (term1844 x)) = ((term1841 x) = (term1856 x)).
Proof. exact (MK_COMB (@lem1728415 x) (@lem1728414 x)). Qed.
Lemma lem1728417 (x : real) : (term1841 x) = (term1856 x).
Proof. exact (EQ_MP (@lem1728416 x) (@lem1728405 x)). Qed.
Lemma lem1728418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728419 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728418) (@lem1725350 x)). Qed.
Lemma lem1728420 (x : real) : (term1100 x) = (term1101 x).
Proof. exact (MK_COMB (@lem1728419 x) (@lem1724954)). Qed.
Lemma lem1728421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728422 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728421) (@lem1724666 x)). Qed.
Lemma lem1728423 (x : real) : (term1102 x) = (term1103 x).
Proof. exact (MK_COMB (@lem1728422 x) (@lem1728420 x)). Qed.
Lemma lem1728424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728425 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728424) (@lem1724666 x)). Qed.
Lemma lem1728426 (x : real) : (term1104 x) = (term1105 x).
Proof. exact (MK_COMB (@lem1728425 x) (@lem1728423 x)). Qed.
Lemma lem1728427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728428 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728427) (@lem1725350 x)). Qed.
Lemma lem1728429 (x : real) : (term1858 x) = (term1859 x).
Proof. exact (MK_COMB (@lem1728428 x) (@lem1728426 x)). Qed.
Lemma lem1728430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728431 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728430) (@lem1724666 x)). Qed.
Lemma lem1728432 (x : real) : (term1851 x) = (term1860 x).
Proof. exact (MK_COMB (@lem1728431 x) (@lem1728429 x)). Qed.
Lemma lem1728433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728434 : term1085 = term1085.
Proof. exact (MK_COMB (@lem1728433) (@lem1725452)). Qed.
Lemma lem1728435 (x : real) : (term1853 x) = (term1861 x).
Proof. exact (MK_COMB (@lem1728434) (@lem1728432 x)). Qed.
Lemma lem1728436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728437 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728436) (@lem1725350 x)). Qed.
Lemma lem1728438 (x : real) : (term1126 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1728437 x) (@lem1725544)). Qed.
Lemma lem1728439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728440 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728439) (@lem1724666 x)). Qed.
Lemma lem1728441 (x : real) : (term1128 x) = (term1129 x).
Proof. exact (MK_COMB (@lem1728440 x) (@lem1728438 x)). Qed.
Lemma lem1728442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728443 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728442) (@lem1724666 x)). Qed.
Lemma lem1728444 (x : real) : (term1130 x) = (term1131 x).
Proof. exact (MK_COMB (@lem1728443 x) (@lem1728441 x)). Qed.
Lemma lem1728445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728446 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728445) (@lem1725350 x)). Qed.
Lemma lem1728447 (x : real) : (term1862 x) = (term1863 x).
Proof. exact (MK_COMB (@lem1728446 x) (@lem1728444 x)). Qed.
Lemma lem1728448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728449 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728448) (@lem1724666 x)). Qed.
Lemma lem1728450 (x : real) : (term1847 x) = (term1864 x).
Proof. exact (MK_COMB (@lem1728449 x) (@lem1728447 x)). Qed.
Lemma lem1728451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728452 : term1080 = term1135.
Proof. exact (MK_COMB (@lem1728451) (@lem1725499)). Qed.
Lemma lem1728453 (x : real) : (term1849 x) = (term1865 x).
Proof. exact (MK_COMB (@lem1728452) (@lem1728450 x)). Qed.
Lemma lem1728454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728455 (x : real) : (term1855 x) = (term1866 x).
Proof. exact (MK_COMB (@lem1728454) (@lem1728435 x)). Qed.
Lemma lem1728456 (x : real) : (term1856 x) = (term1867 x).
Proof. exact (MK_COMB (@lem1728455 x) (@lem1728453 x)). Qed.
Lemma lem1728468 (x : real) : (term1841 x) = (term1867 x).
Proof. exact (TRANS (@lem1728417 x) (@lem1728456 x)). Qed.
Lemma lem1728470 (x : real) : (term1868 x) = (term1835 x).
Proof. exact (eq_refl (term1868 x)). Qed.
Lemma lem1728471 (x : real) : (term1835 x) = (term1868 x).
Proof. exact (SYM (@lem1728470 x)). Qed.
Lemma lem1728472 (x : real) : (term1868 x) = (term1869 x).
Proof. exact (@lem1482981 (term1870 x) term73). Qed.
Lemma lem1728473 (x : real) : (term1835 x) = (term1869 x).
Proof. exact (TRANS (@lem1728471 x) (@lem1728472 x)). Qed.
Lemma lem1728474 (x : real) : (term1871 x) = (term1872 x).
Proof. exact (eq_refl (term1871 x)). Qed.
Lemma lem1728475 : term1080 = term1080.
Proof. exact (eq_refl term1080). Qed.
Lemma lem1728476 (x : real) : (term1873 x) = (term1874 x).
Proof. exact (MK_COMB (@lem1728475) (@lem1728474 x)). Qed.
Lemma lem1728477 (x : real) : (term1875 x) = (term1876 x).
Proof. exact (eq_refl (term1875 x)). Qed.
Lemma lem1728478 : term1085 = term1085.
Proof. exact (eq_refl term1085). Qed.
Lemma lem1728479 (x : real) : (term1877 x) = (term1878 x).
Proof. exact (MK_COMB (@lem1728478) (@lem1728477 x)). Qed.
Lemma lem1728480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728481 (x : real) : (term1879 x) = (term1880 x).
Proof. exact (MK_COMB (@lem1728480) (@lem1728479 x)). Qed.
Lemma lem1728482 (x : real) : (term1869 x) = (term1881 x).
Proof. exact (MK_COMB (@lem1728481 x) (@lem1728476 x)). Qed.
Lemma lem1728483 (x : real) : (term1882 x) = (term1882 x).
Proof. exact (eq_refl (term1882 x)). Qed.
Lemma lem1728484 (x : real) : ((term1835 x) = (term1869 x)) = ((term1835 x) = (term1881 x)).
Proof. exact (MK_COMB (@lem1728483 x) (@lem1728482 x)). Qed.
Lemma lem1728485 (x : real) : (term1835 x) = (term1881 x).
Proof. exact (EQ_MP (@lem1728484 x) (@lem1728473 x)). Qed.
Lemma lem1728486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728487 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728486) (@lem1725350 x)). Qed.
Lemma lem1728488 (x : real) : (term1100 x) = (term1101 x).
Proof. exact (MK_COMB (@lem1728487 x) (@lem1724954)). Qed.
Lemma lem1728489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728490 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728489) (@lem1724687 x)). Qed.
Lemma lem1728491 (x : real) : (term1154 x) = (term1155 x).
Proof. exact (MK_COMB (@lem1728490 x) (@lem1728488 x)). Qed.
Lemma lem1728492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728493 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728492) (@lem1724666 x)). Qed.
Lemma lem1728494 (x : real) : (term1156 x) = (term1157 x).
Proof. exact (MK_COMB (@lem1728493 x) (@lem1728491 x)). Qed.
Lemma lem1728495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728496 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728495) (@lem1724639 x)). Qed.
Lemma lem1728497 (x : real) : (term1883 x) = (term1884 x).
Proof. exact (MK_COMB (@lem1728496 x) (@lem1728494 x)). Qed.
Lemma lem1728498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728499 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728498) (@lem1724639 x)). Qed.
Lemma lem1728500 (x : real) : (term1876 x) = (term1885 x).
Proof. exact (MK_COMB (@lem1728499 x) (@lem1728497 x)). Qed.
Lemma lem1728501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728502 : term1085 = term1085.
Proof. exact (MK_COMB (@lem1728501) (@lem1725452)). Qed.
Lemma lem1728503 (x : real) : (term1878 x) = (term1886 x).
Proof. exact (MK_COMB (@lem1728502) (@lem1728500 x)). Qed.
Lemma lem1728504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728505 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728504) (@lem1725350 x)). Qed.
Lemma lem1728506 (x : real) : (term1126 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1728505 x) (@lem1725544)). Qed.
Lemma lem1728507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728508 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728507) (@lem1724687 x)). Qed.
Lemma lem1728509 (x : real) : (term1162 x) = (term1163 x).
Proof. exact (MK_COMB (@lem1728508 x) (@lem1728506 x)). Qed.
Lemma lem1728510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728511 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728510) (@lem1724666 x)). Qed.
Lemma lem1728512 (x : real) : (term1164 x) = (term1165 x).
Proof. exact (MK_COMB (@lem1728511 x) (@lem1728509 x)). Qed.
Lemma lem1728513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728514 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728513) (@lem1724639 x)). Qed.
Lemma lem1728515 (x : real) : (term1887 x) = (term1888 x).
Proof. exact (MK_COMB (@lem1728514 x) (@lem1728512 x)). Qed.
Lemma lem1728516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728517 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728516) (@lem1724639 x)). Qed.
Lemma lem1728518 (x : real) : (term1872 x) = (term1889 x).
Proof. exact (MK_COMB (@lem1728517 x) (@lem1728515 x)). Qed.
Lemma lem1728519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728520 : term1080 = term1135.
Proof. exact (MK_COMB (@lem1728519) (@lem1725499)). Qed.
Lemma lem1728521 (x : real) : (term1874 x) = (term1890 x).
Proof. exact (MK_COMB (@lem1728520) (@lem1728518 x)). Qed.
Lemma lem1728522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728523 (x : real) : (term1880 x) = (term1891 x).
Proof. exact (MK_COMB (@lem1728522) (@lem1728503 x)). Qed.
Lemma lem1728524 (x : real) : (term1881 x) = (term1892 x).
Proof. exact (MK_COMB (@lem1728523 x) (@lem1728521 x)). Qed.
Lemma lem1728536 (x : real) : (term1835 x) = (term1892 x).
Proof. exact (TRANS (@lem1728485 x) (@lem1728524 x)). Qed.
Lemma lem1728537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728538 (x : real) : (term1837 x) = (term1893 x).
Proof. exact (MK_COMB (@lem1728537) (@lem1728536 x)). Qed.
Lemma lem1728539 (x : real) : (term1842 x) = (term1894 x).
Proof. exact (MK_COMB (@lem1728538 x) (@lem1728468 x)). Qed.
Lemma lem1728541 (x : real) : (term1825 x) = (term1894 x).
Proof. exact (TRANS (@lem1728400 x) (@lem1728539 x)). Qed.
Lemma lem1728543 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1728544 : term252 = term1174.
Proof. exact (@lem1728543 term24 term73 term76). Qed.
Lemma lem1728551 : term1175 = term73.
Proof. exact (@lem1483460 term73). Qed.
Lemma lem1728554 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1728555 : term1176 = term886.
Proof. exact (MK_COMB (@lem1728554) (@lem1728551)). Qed.
Lemma lem1728557 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1728558 : term886 = term76.
Proof. exact (@lem1728557 term185). Qed.
Lemma lem1728559 : term1176 = term76.
Proof. exact (TRANS (@lem1728555) (@lem1728558)). Qed.
Lemma lem1728560 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1728561 : term1177 = term896.
Proof. exact (MK_COMB (@lem1728560) (@lem1728559)). Qed.
Lemma lem1728562 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728563 : term1178 = term897.
Proof. exact (MK_COMB (@lem1728561) (@lem1728562)). Qed.
Lemma lem1728570 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1728571 : term215 = term206.
Proof. exact (@lem1728570 term185 term185). Qed.
Lemma lem1728572 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1728573 : term205 = term185.
Proof. exact (EQ_MP (@lem1728572) (@lem940073)). Qed.
Lemma lem1728574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1728575 : term206 = term24.
Proof. exact (MK_COMB (@lem1728574) (@lem1728573)). Qed.
Lemma lem1728577 : term215 = term24.
Proof. exact (TRANS (@lem1728571) (@lem1728575)). Qed.
Lemma lem1728580 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1728581 : term1179 = term990.
Proof. exact (MK_COMB (@lem1728580) (@lem1728577)). Qed.
Lemma lem1728582 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1728583 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1728584 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1728585 : term922 = term923.
Proof. exact (EQ_MP (@lem1728584) (@lem1728583)). Qed.
Lemma lem1728586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1728587 : term924 = term925.
Proof. exact (MK_COMB (@lem1728586) (@lem1728585)). Qed.
Lemma lem1728588 : term990 = term925.
Proof. exact (TRANS (@lem1728582) (@lem1728587)). Qed.
Lemma lem1728589 : term1179 = term925.
Proof. exact (TRANS (@lem1728581) (@lem1728588)). Qed.
Lemma lem1728590 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1728591 : term1180 = term992.
Proof. exact (MK_COMB (@lem1728590) (@lem1728589)). Qed.
Lemma lem1728592 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728593 : term1181 = term994.
Proof. exact (MK_COMB (@lem1728591) (@lem1728592)). Qed.
Lemma lem1728594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728595 : term1182 = term1183.
Proof. exact (MK_COMB (@lem1728594) (@lem1728593)). Qed.
Lemma lem1728596 : term1174 = term1184.
Proof. exact (MK_COMB (@lem1728595) (@lem1728563)). Qed.
Lemma lem1728597 : term252 = term1184.
Proof. exact (TRANS (@lem1728544) (@lem1728596)). Qed.
Lemma lem1728598 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1728599 (x : real) : (term581 x) = (term1185 x).
Proof. exact (MK_COMB (@lem1728598 x) (@lem1728597)). Qed.
Lemma lem1728600 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1728601 (x : real) : (term603 x) = (term1186 x).
Proof. exact (MK_COMB (@lem1728600 x) (@lem1728599 x)). Qed.
Lemma lem1728602 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1728603 (x : real) : (term667 x) = (term1187 x).
Proof. exact (MK_COMB (@lem1728602 x) (@lem1728601 x)). Qed.
Lemma lem1728604 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1728605 (x : real) : (term1895 x) = (term1896 x).
Proof. exact (MK_COMB (@lem1728604 x) (@lem1728603 x)). Qed.
Lemma lem1728606 (x : real) : (term1897 x) = (term1896 x).
Proof. exact (eq_refl (term1897 x)). Qed.
Lemma lem1728607 (x : real) : (term1896 x) = (term1897 x).
Proof. exact (SYM (@lem1728606 x)). Qed.
Lemma lem1728608 (x : real) : (term1897 x) = (term1898 x).
Proof. exact (@lem1482981 (term1899 x) x). Qed.
Lemma lem1728609 (x : real) : (term1896 x) = (term1898 x).
Proof. exact (TRANS (@lem1728607 x) (@lem1728608 x)). Qed.
Lemma lem1728610 (x : real) : (term1900 x) = (term1901 x).
Proof. exact (eq_refl (term1900 x)). Qed.
Lemma lem1728611 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1728612 (x : real) : (term1902 x) = (term1903 x).
Proof. exact (MK_COMB (@lem1728611 x) (@lem1728610 x)). Qed.
Lemma lem1728613 (x : real) : (term1904 x) = (term1905 x).
Proof. exact (eq_refl (term1904 x)). Qed.
Lemma lem1728614 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1728615 (x : real) : (term1906 x) = (term1907 x).
Proof. exact (MK_COMB (@lem1728614 x) (@lem1728613 x)). Qed.
Lemma lem1728616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728617 (x : real) : (term1908 x) = (term1909 x).
Proof. exact (MK_COMB (@lem1728616) (@lem1728615 x)). Qed.
Lemma lem1728618 (x : real) : (term1898 x) = (term1910 x).
Proof. exact (MK_COMB (@lem1728617 x) (@lem1728612 x)). Qed.
Lemma lem1728619 (x : real) : (term1911 x) = (term1911 x).
Proof. exact (eq_refl (term1911 x)). Qed.
Lemma lem1728620 (x : real) : ((term1896 x) = (term1898 x)) = ((term1896 x) = (term1910 x)).
Proof. exact (MK_COMB (@lem1728619 x) (@lem1728618 x)). Qed.
Lemma lem1728621 (x : real) : (term1896 x) = (term1910 x).
Proof. exact (EQ_MP (@lem1728620 x) (@lem1728609 x)). Qed.
Lemma lem1728622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728623 : term1183 = term1183.
Proof. exact (MK_COMB (@lem1728622) (@lem1725214)). Qed.
Lemma lem1728624 : term1184 = term1184.
Proof. exact (MK_COMB (@lem1728623) (@lem1725193)). Qed.
Lemma lem1728625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728626 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728625) (@lem1725350 x)). Qed.
Lemma lem1728627 (x : real) : (term1185 x) = (term1185 x).
Proof. exact (MK_COMB (@lem1728626 x) (@lem1728624)). Qed.
Lemma lem1728628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728629 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728628) (@lem1724687 x)). Qed.
Lemma lem1728630 (x : real) : (term1205 x) = (term1205 x).
Proof. exact (MK_COMB (@lem1728629 x) (@lem1728627 x)). Qed.
Lemma lem1728631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728632 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728631) (@lem1724666 x)). Qed.
Lemma lem1728633 (x : real) : (term1206 x) = (term1206 x).
Proof. exact (MK_COMB (@lem1728632 x) (@lem1728630 x)). Qed.
Lemma lem1728634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728635 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728634) (@lem1724639 x)). Qed.
Lemma lem1728636 (x : real) : (term1905 x) = (term1905 x).
Proof. exact (MK_COMB (@lem1728635 x) (@lem1728633 x)). Qed.
Lemma lem1728637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728638 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728637) (@lem1724639 x)). Qed.
Lemma lem1728639 (x : real) : (term1907 x) = (term1907 x).
Proof. exact (MK_COMB (@lem1728638 x) (@lem1728636 x)). Qed.
Lemma lem1728640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728641 : term1183 = term1183.
Proof. exact (MK_COMB (@lem1728640) (@lem1725214)). Qed.
Lemma lem1728642 : term1184 = term1184.
Proof. exact (MK_COMB (@lem1728641) (@lem1725193)). Qed.
Lemma lem1728643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728644 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728643) (@lem1725350 x)). Qed.
Lemma lem1728645 (x : real) : (term1185 x) = (term1185 x).
Proof. exact (MK_COMB (@lem1728644 x) (@lem1728642)). Qed.
Lemma lem1728646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728647 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728646) (@lem1724781 x)). Qed.
Lemma lem1728648 (x : real) : (term1207 x) = (term1208 x).
Proof. exact (MK_COMB (@lem1728647 x) (@lem1728645 x)). Qed.
Lemma lem1728649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728650 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728649) (@lem1724666 x)). Qed.
Lemma lem1728651 (x : real) : (term1209 x) = (term1210 x).
Proof. exact (MK_COMB (@lem1728650 x) (@lem1728648 x)). Qed.
Lemma lem1728652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728653 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728652) (@lem1728062 x)). Qed.
Lemma lem1728654 (x : real) : (term1901 x) = (term1912 x).
Proof. exact (MK_COMB (@lem1728653 x) (@lem1728651 x)). Qed.
Lemma lem1728655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728656 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728655) (@lem1724751 x)). Qed.
Lemma lem1728657 (x : real) : (term1903 x) = (term1913 x).
Proof. exact (MK_COMB (@lem1728656 x) (@lem1728654 x)). Qed.
Lemma lem1728658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728659 (x : real) : (term1909 x) = (term1909 x).
Proof. exact (MK_COMB (@lem1728658) (@lem1728639 x)). Qed.
Lemma lem1728660 (x : real) : (term1910 x) = (term1914 x).
Proof. exact (MK_COMB (@lem1728659 x) (@lem1728657 x)). Qed.
Lemma lem1728671 (x : real) : (term1896 x) = (term1914 x).
Proof. exact (TRANS (@lem1728621 x) (@lem1728660 x)). Qed.
Lemma lem1728672 (x : real) : (term1895 x) = (term1914 x).
Proof. exact (TRANS (@lem1728605 x) (@lem1728671 x)). Qed.
Lemma lem1728673 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728674 (x : real) : (term1915 x) = (term1916 x).
Proof. exact (MK_COMB (@lem1728673) (@lem1728541 x)). Qed.
Lemma lem1728675 (x : real) : (term665 x) = (term1917 x).
Proof. exact (MK_COMB (@lem1728674 x) (@lem1728672 x)). Qed.
Lemma lem1728676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728677 (x : real) : (term673 x) = (term1918 x).
Proof. exact (MK_COMB (@lem1728676) (@lem1728349 x)). Qed.
Lemma lem1728678 (x : real) : (term674 x) = (term1919 x).
Proof. exact (MK_COMB (@lem1728677 x) (@lem1728675 x)). Qed.
Lemma lem1728680 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1728681 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1728680 x term76). Qed.
Lemma lem1728688 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1728689 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1728690 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1728689) (@lem1728688 x)). Qed.
Lemma lem1728691 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728692 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1728690 x) (@lem1728691)). Qed.
Lemma lem1728705 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1728706 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728705 x) (@lem1728692 x)). Qed.
Lemma lem1728707 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1728681 x) (@lem1728706 x)). Qed.
Lemma lem1728708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728709 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728708) (@lem1728707 x)). Qed.
Lemma lem1728710 (x : real) : (term510 x) = (term510 x).
Proof. exact (eq_refl (term510 x)). Qed.
Lemma lem1728711 (x : real) : (term544 x) = (term1920 x).
Proof. exact (MK_COMB (@lem1728709 x) (@lem1728710 x)). Qed.
Lemma lem1728712 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1728713 (x : real) : (term657 x) = (term1921 x).
Proof. exact (MK_COMB (@lem1728712 x) (@lem1728711 x)). Qed.
Lemma lem1728714 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1728715 (x : real) : (term1922 x) = (term1923 x).
Proof. exact (MK_COMB (@lem1728714 x) (@lem1728713 x)). Qed.
Lemma lem1728716 (x : real) : (term1924 x) = (term1923 x).
Proof. exact (eq_refl (term1924 x)). Qed.
Lemma lem1728717 (x : real) : (term1923 x) = (term1924 x).
Proof. exact (SYM (@lem1728716 x)). Qed.
Lemma lem1728718 (x : real) : (term1924 x) = (term1925 x).
Proof. exact (@lem1482981 (term1926 x) x). Qed.
Lemma lem1728719 (x : real) : (term1923 x) = (term1925 x).
Proof. exact (TRANS (@lem1728717 x) (@lem1728718 x)). Qed.
Lemma lem1728720 (x : real) : (term1927 x) = (term1928 x).
Proof. exact (eq_refl (term1927 x)). Qed.
Lemma lem1728721 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1728722 (x : real) : (term1929 x) = (term1930 x).
Proof. exact (MK_COMB (@lem1728721 x) (@lem1728720 x)). Qed.
Lemma lem1728723 (x : real) : (term1931 x) = (term1932 x).
Proof. exact (eq_refl (term1931 x)). Qed.
Lemma lem1728724 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1728725 (x : real) : (term1933 x) = (term1934 x).
Proof. exact (MK_COMB (@lem1728724 x) (@lem1728723 x)). Qed.
Lemma lem1728726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728727 (x : real) : (term1935 x) = (term1936 x).
Proof. exact (MK_COMB (@lem1728726) (@lem1728725 x)). Qed.
Lemma lem1728728 (x : real) : (term1925 x) = (term1937 x).
Proof. exact (MK_COMB (@lem1728727 x) (@lem1728722 x)). Qed.
Lemma lem1728729 (x : real) : (term1938 x) = (term1938 x).
Proof. exact (eq_refl (term1938 x)). Qed.
Lemma lem1728730 (x : real) : ((term1923 x) = (term1925 x)) = ((term1923 x) = (term1937 x)).
Proof. exact (MK_COMB (@lem1728729 x) (@lem1728728 x)). Qed.
Lemma lem1728731 (x : real) : (term1923 x) = (term1937 x).
Proof. exact (EQ_MP (@lem1728730 x) (@lem1728719 x)). Qed.
Lemma lem1728732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728733 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728732) (@lem1725350 x)). Qed.
Lemma lem1728734 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728733 x) (@lem1724639 x)). Qed.
Lemma lem1728735 : term407 = term406.
Proof. exact (@lem1483525 term35 term76). Qed.
Lemma lem1728741 : term393 = term394.
Proof. exact (@lem1483519 term35 term76). Qed.
Lemma lem1728743 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1728744 : term184 = term76.
Proof. exact (@lem1728743 term185). Qed.
Lemma lem1728745 : term207 = term207.
Proof. exact (eq_refl term207). Qed.
Lemma lem1728746 : term394 = term395.
Proof. exact (MK_COMB (@lem1728745) (@lem1728744)). Qed.
Lemma lem1728747 : term395 = term35.
Proof. exact (@lem1483450 term35). Qed.
Lemma lem1728748 : term394 = term35.
Proof. exact (TRANS (@lem1728746) (@lem1728747)). Qed.
Lemma lem1728750 : term393 = term35.
Proof. exact (TRANS (@lem1728741) (@lem1728748)). Qed.
Lemma lem1728751 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1728752 : term404 = term405.
Proof. exact (MK_COMB (@lem1728751) (@lem1728750)). Qed.
Lemma lem1728753 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728754 : term406 = term407.
Proof. exact (MK_COMB (@lem1728752) (@lem1728753)). Qed.
Lemma lem1728755 : term407 = term407.
Proof. exact (TRANS (@lem1728735) (@lem1728754)). Qed.
Lemma lem1728756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728757 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728756) (@lem1724687 x)). Qed.
Lemma lem1728758 (x : real) : (term510 x) = (term510 x).
Proof. exact (MK_COMB (@lem1728757 x) (@lem1728755)). Qed.
Lemma lem1728759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728760 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728759) (@lem1728734 x)). Qed.
Lemma lem1728761 (x : real) : (term1920 x) = (term1920 x).
Proof. exact (MK_COMB (@lem1728760 x) (@lem1728758 x)). Qed.
Lemma lem1728762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728763 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728762) (@lem1724666 x)). Qed.
Lemma lem1728764 (x : real) : (term1921 x) = (term1921 x).
Proof. exact (MK_COMB (@lem1728763 x) (@lem1728761 x)). Qed.
Lemma lem1728765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728766 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728765) (@lem1724639 x)). Qed.
Lemma lem1728767 (x : real) : (term1932 x) = (term1932 x).
Proof. exact (MK_COMB (@lem1728766 x) (@lem1728764 x)). Qed.
Lemma lem1728768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728769 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728768) (@lem1724639 x)). Qed.
Lemma lem1728770 (x : real) : (term1934 x) = (term1934 x).
Proof. exact (MK_COMB (@lem1728769 x) (@lem1728767 x)). Qed.
Lemma lem1728771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728772 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728771) (@lem1725350 x)). Qed.
Lemma lem1728773 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728772 x) (@lem1724639 x)). Qed.
Lemma lem1728774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728775 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728774) (@lem1724687 x)). Qed.
Lemma lem1728776 (x : real) : (term510 x) = (term510 x).
Proof. exact (MK_COMB (@lem1728775 x) (@lem1728755)). Qed.
Lemma lem1728777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728778 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728777) (@lem1728773 x)). Qed.
Lemma lem1728779 (x : real) : (term1920 x) = (term1920 x).
Proof. exact (MK_COMB (@lem1728778 x) (@lem1728776 x)). Qed.
Lemma lem1728780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728781 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728780) (@lem1724666 x)). Qed.
Lemma lem1728782 (x : real) : (term1921 x) = (term1921 x).
Proof. exact (MK_COMB (@lem1728781 x) (@lem1728779 x)). Qed.
Lemma lem1728783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728784 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728783) (@lem1728062 x)). Qed.
Lemma lem1728785 (x : real) : (term1928 x) = (term1939 x).
Proof. exact (MK_COMB (@lem1728784 x) (@lem1728782 x)). Qed.
Lemma lem1728786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728787 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728786) (@lem1724751 x)). Qed.
Lemma lem1728788 (x : real) : (term1930 x) = (term1940 x).
Proof. exact (MK_COMB (@lem1728787 x) (@lem1728785 x)). Qed.
Lemma lem1728789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728790 (x : real) : (term1936 x) = (term1936 x).
Proof. exact (MK_COMB (@lem1728789) (@lem1728770 x)). Qed.
Lemma lem1728791 (x : real) : (term1937 x) = (term1941 x).
Proof. exact (MK_COMB (@lem1728790 x) (@lem1728788 x)). Qed.
Lemma lem1728792 (x : real) : (term1923 x) = (term1941 x).
Proof. exact (TRANS (@lem1728731 x) (@lem1728791 x)). Qed.
Lemma lem1728794 (x : real) : (term1942 x) = (term1940 x).
Proof. exact (eq_refl (term1942 x)). Qed.
Lemma lem1728795 (x : real) : (term1940 x) = (term1942 x).
Proof. exact (SYM (@lem1728794 x)). Qed.
Lemma lem1728796 (x : real) : (term1942 x) = (term1943 x).
Proof. exact (@lem1482981 (term1944 x) term24). Qed.
Lemma lem1728797 (x : real) : (term1940 x) = (term1943 x).
Proof. exact (TRANS (@lem1728795 x) (@lem1728796 x)). Qed.
Lemma lem1728798 (x : real) : (term1945 x) = (term1946 x).
Proof. exact (eq_refl (term1945 x)). Qed.
Lemma lem1728799 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1728800 (x : real) : (term1947 x) = (term1948 x).
Proof. exact (MK_COMB (@lem1728799) (@lem1728798 x)). Qed.
Lemma lem1728801 (x : real) : (term1949 x) = (term1950 x).
Proof. exact (eq_refl (term1949 x)). Qed.
Lemma lem1728802 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1728803 (x : real) : (term1951 x) = (term1952 x).
Proof. exact (MK_COMB (@lem1728802) (@lem1728801 x)). Qed.
Lemma lem1728804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728805 (x : real) : (term1953 x) = (term1954 x).
Proof. exact (MK_COMB (@lem1728804) (@lem1728803 x)). Qed.
Lemma lem1728806 (x : real) : (term1943 x) = (term1955 x).
Proof. exact (MK_COMB (@lem1728805 x) (@lem1728800 x)). Qed.
Lemma lem1728807 (x : real) : (term1956 x) = (term1956 x).
Proof. exact (eq_refl (term1956 x)). Qed.
Lemma lem1728808 (x : real) : ((term1940 x) = (term1943 x)) = ((term1940 x) = (term1955 x)).
Proof. exact (MK_COMB (@lem1728807 x) (@lem1728806 x)). Qed.
Lemma lem1728809 (x : real) : (term1940 x) = (term1955 x).
Proof. exact (EQ_MP (@lem1728808 x) (@lem1728797 x)). Qed.
Lemma lem1728810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728811 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728810) (@lem1725350 x)). Qed.
Lemma lem1728812 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728811 x) (@lem1724639 x)). Qed.
Lemma lem1728813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728814 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728813) (@lem1724687 x)). Qed.
Lemma lem1728815 (x : real) : (term1957 x) = (term1957 x).
Proof. exact (MK_COMB (@lem1728814 x) (@lem1727354)). Qed.
Lemma lem1728816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728817 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728816) (@lem1728812 x)). Qed.
Lemma lem1728818 (x : real) : (term1958 x) = (term1958 x).
Proof. exact (MK_COMB (@lem1728817 x) (@lem1728815 x)). Qed.
Lemma lem1728819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728820 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728819) (@lem1724666 x)). Qed.
Lemma lem1728821 (x : real) : (term1959 x) = (term1959 x).
Proof. exact (MK_COMB (@lem1728820 x) (@lem1728818 x)). Qed.
Lemma lem1728822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728823 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728822) (@lem1725350 x)). Qed.
Lemma lem1728824 (x : real) : (term1960 x) = (term1960 x).
Proof. exact (MK_COMB (@lem1728823 x) (@lem1728821 x)). Qed.
Lemma lem1728825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728826 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728825) (@lem1724666 x)). Qed.
Lemma lem1728827 (x : real) : (term1950 x) = (term1950 x).
Proof. exact (MK_COMB (@lem1728826 x) (@lem1728824 x)). Qed.
Lemma lem1728828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728829 : term869 = term869.
Proof. exact (MK_COMB (@lem1728828) (@lem1724838)). Qed.
Lemma lem1728830 (x : real) : (term1952 x) = (term1952 x).
Proof. exact (MK_COMB (@lem1728829) (@lem1728827 x)). Qed.
Lemma lem1728831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728832 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728831) (@lem1725350 x)). Qed.
Lemma lem1728833 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728832 x) (@lem1724639 x)). Qed.
Lemma lem1728834 : term915 = term1961.
Proof. exact (@lem1483525 term73 term76). Qed.
Lemma lem1728840 : term1094 = term1095.
Proof. exact (@lem1483519 term73 term76). Qed.
Lemma lem1728842 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1728843 : term184 = term76.
Proof. exact (@lem1728842 term185). Qed.
Lemma lem1728844 : term1096 = term1096.
Proof. exact (eq_refl term1096). Qed.
Lemma lem1728845 : term1095 = term1097.
Proof. exact (MK_COMB (@lem1728844) (@lem1728843)). Qed.
Lemma lem1728846 : term1097 = term73.
Proof. exact (@lem1483450 term73). Qed.
Lemma lem1728847 : term1095 = term73.
Proof. exact (TRANS (@lem1728845) (@lem1728846)). Qed.
Lemma lem1728849 : term1094 = term73.
Proof. exact (TRANS (@lem1728840) (@lem1728847)). Qed.
Lemma lem1728850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1728851 : term1962 = term914.
Proof. exact (MK_COMB (@lem1728850) (@lem1728849)). Qed.
Lemma lem1728852 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728853 : term1961 = term915.
Proof. exact (MK_COMB (@lem1728851) (@lem1728852)). Qed.
Lemma lem1728854 : term915 = term915.
Proof. exact (TRANS (@lem1728834) (@lem1728853)). Qed.
Lemma lem1728855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728856 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728855) (@lem1724687 x)). Qed.
Lemma lem1728857 (x : real) : (term1963 x) = (term1963 x).
Proof. exact (MK_COMB (@lem1728856 x) (@lem1728854)). Qed.
Lemma lem1728858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728859 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728858) (@lem1728833 x)). Qed.
Lemma lem1728860 (x : real) : (term1964 x) = (term1964 x).
Proof. exact (MK_COMB (@lem1728859 x) (@lem1728857 x)). Qed.
Lemma lem1728861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728862 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728861) (@lem1724666 x)). Qed.
Lemma lem1728863 (x : real) : (term1965 x) = (term1965 x).
Proof. exact (MK_COMB (@lem1728862 x) (@lem1728860 x)). Qed.
Lemma lem1728864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728865 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728864) (@lem1725350 x)). Qed.
Lemma lem1728866 (x : real) : (term1966 x) = (term1966 x).
Proof. exact (MK_COMB (@lem1728865 x) (@lem1728863 x)). Qed.
Lemma lem1728867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728868 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728867) (@lem1724666 x)). Qed.
Lemma lem1728869 (x : real) : (term1946 x) = (term1946 x).
Proof. exact (MK_COMB (@lem1728868 x) (@lem1728866 x)). Qed.
Lemma lem1728870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728871 : term864 = term946.
Proof. exact (MK_COMB (@lem1728870) (@lem1724916)). Qed.
Lemma lem1728872 (x : real) : (term1948 x) = (term1967 x).
Proof. exact (MK_COMB (@lem1728871) (@lem1728869 x)). Qed.
Lemma lem1728873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728874 (x : real) : (term1954 x) = (term1954 x).
Proof. exact (MK_COMB (@lem1728873) (@lem1728830 x)). Qed.
Lemma lem1728875 (x : real) : (term1955 x) = (term1968 x).
Proof. exact (MK_COMB (@lem1728874 x) (@lem1728872 x)). Qed.
Lemma lem1728887 (x : real) : (term1940 x) = (term1968 x).
Proof. exact (TRANS (@lem1728809 x) (@lem1728875 x)). Qed.
Lemma lem1728889 (x : real) : (term1969 x) = (term1934 x).
Proof. exact (eq_refl (term1969 x)). Qed.
Lemma lem1728890 (x : real) : (term1934 x) = (term1969 x).
Proof. exact (SYM (@lem1728889 x)). Qed.
Lemma lem1728891 (x : real) : (term1969 x) = (term1970 x).
Proof. exact (@lem1482981 (term1971 x) term24). Qed.
Lemma lem1728892 (x : real) : (term1934 x) = (term1970 x).
Proof. exact (TRANS (@lem1728890 x) (@lem1728891 x)). Qed.
Lemma lem1728893 (x : real) : (term1972 x) = (term1973 x).
Proof. exact (eq_refl (term1972 x)). Qed.
Lemma lem1728894 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1728895 (x : real) : (term1974 x) = (term1975 x).
Proof. exact (MK_COMB (@lem1728894) (@lem1728893 x)). Qed.
Lemma lem1728896 (x : real) : (term1976 x) = (term1977 x).
Proof. exact (eq_refl (term1976 x)). Qed.
Lemma lem1728897 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1728898 (x : real) : (term1978 x) = (term1979 x).
Proof. exact (MK_COMB (@lem1728897) (@lem1728896 x)). Qed.
Lemma lem1728899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728900 (x : real) : (term1980 x) = (term1981 x).
Proof. exact (MK_COMB (@lem1728899) (@lem1728898 x)). Qed.
Lemma lem1728901 (x : real) : (term1970 x) = (term1982 x).
Proof. exact (MK_COMB (@lem1728900 x) (@lem1728895 x)). Qed.
Lemma lem1728902 (x : real) : (term1983 x) = (term1983 x).
Proof. exact (eq_refl (term1983 x)). Qed.
Lemma lem1728903 (x : real) : ((term1934 x) = (term1970 x)) = ((term1934 x) = (term1982 x)).
Proof. exact (MK_COMB (@lem1728902 x) (@lem1728901 x)). Qed.
Lemma lem1728904 (x : real) : (term1934 x) = (term1982 x).
Proof. exact (EQ_MP (@lem1728903 x) (@lem1728892 x)). Qed.
Lemma lem1728905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728906 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728905) (@lem1725350 x)). Qed.
Lemma lem1728907 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728906 x) (@lem1724639 x)). Qed.
Lemma lem1728908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728909 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728908) (@lem1724687 x)). Qed.
Lemma lem1728910 (x : real) : (term1957 x) = (term1957 x).
Proof. exact (MK_COMB (@lem1728909 x) (@lem1727354)). Qed.
Lemma lem1728911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728912 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728911) (@lem1728907 x)). Qed.
Lemma lem1728913 (x : real) : (term1958 x) = (term1958 x).
Proof. exact (MK_COMB (@lem1728912 x) (@lem1728910 x)). Qed.
Lemma lem1728914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728915 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728914) (@lem1724666 x)). Qed.
Lemma lem1728916 (x : real) : (term1959 x) = (term1959 x).
Proof. exact (MK_COMB (@lem1728915 x) (@lem1728913 x)). Qed.
Lemma lem1728917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728918 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728917) (@lem1724639 x)). Qed.
Lemma lem1728919 (x : real) : (term1984 x) = (term1984 x).
Proof. exact (MK_COMB (@lem1728918 x) (@lem1728916 x)). Qed.
Lemma lem1728920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728921 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728920) (@lem1724639 x)). Qed.
Lemma lem1728922 (x : real) : (term1977 x) = (term1977 x).
Proof. exact (MK_COMB (@lem1728921 x) (@lem1728919 x)). Qed.
Lemma lem1728923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728924 : term869 = term869.
Proof. exact (MK_COMB (@lem1728923) (@lem1724838)). Qed.
Lemma lem1728925 (x : real) : (term1979 x) = (term1979 x).
Proof. exact (MK_COMB (@lem1728924) (@lem1728922 x)). Qed.
Lemma lem1728926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728927 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1728926) (@lem1725350 x)). Qed.
Lemma lem1728928 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728927 x) (@lem1724639 x)). Qed.
Lemma lem1728929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728930 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1728929) (@lem1724687 x)). Qed.
Lemma lem1728931 (x : real) : (term1963 x) = (term1963 x).
Proof. exact (MK_COMB (@lem1728930 x) (@lem1728854)). Qed.
Lemma lem1728932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728933 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728932) (@lem1728928 x)). Qed.
Lemma lem1728934 (x : real) : (term1964 x) = (term1964 x).
Proof. exact (MK_COMB (@lem1728933 x) (@lem1728931 x)). Qed.
Lemma lem1728935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728936 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1728935) (@lem1724666 x)). Qed.
Lemma lem1728937 (x : real) : (term1965 x) = (term1965 x).
Proof. exact (MK_COMB (@lem1728936 x) (@lem1728934 x)). Qed.
Lemma lem1728938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728939 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728938) (@lem1724639 x)). Qed.
Lemma lem1728940 (x : real) : (term1985 x) = (term1985 x).
Proof. exact (MK_COMB (@lem1728939 x) (@lem1728937 x)). Qed.
Lemma lem1728941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728942 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1728941) (@lem1724639 x)). Qed.
Lemma lem1728943 (x : real) : (term1973 x) = (term1973 x).
Proof. exact (MK_COMB (@lem1728942 x) (@lem1728940 x)). Qed.
Lemma lem1728944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728945 : term864 = term946.
Proof. exact (MK_COMB (@lem1728944) (@lem1724916)). Qed.
Lemma lem1728946 (x : real) : (term1975 x) = (term1986 x).
Proof. exact (MK_COMB (@lem1728945) (@lem1728943 x)). Qed.
Lemma lem1728947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728948 (x : real) : (term1981 x) = (term1981 x).
Proof. exact (MK_COMB (@lem1728947) (@lem1728925 x)). Qed.
Lemma lem1728949 (x : real) : (term1982 x) = (term1987 x).
Proof. exact (MK_COMB (@lem1728948 x) (@lem1728946 x)). Qed.
Lemma lem1728961 (x : real) : (term1934 x) = (term1987 x).
Proof. exact (TRANS (@lem1728904 x) (@lem1728949 x)). Qed.
Lemma lem1728962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1728963 (x : real) : (term1936 x) = (term1988 x).
Proof. exact (MK_COMB (@lem1728962) (@lem1728961 x)). Qed.
Lemma lem1728964 (x : real) : (term1941 x) = (term1989 x).
Proof. exact (MK_COMB (@lem1728963 x) (@lem1728887 x)). Qed.
Lemma lem1728965 (x : real) : (term1923 x) = (term1989 x).
Proof. exact (TRANS (@lem1728792 x) (@lem1728964 x)). Qed.
Lemma lem1728966 (x : real) : (term1922 x) = (term1989 x).
Proof. exact (TRANS (@lem1728715 x) (@lem1728965 x)). Qed.
Lemma lem1728968 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1728969 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1728968 x term76). Qed.
Lemma lem1728976 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1728977 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1728978 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1728977) (@lem1728976 x)). Qed.
Lemma lem1728979 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1728980 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1728978 x) (@lem1728979)). Qed.
Lemma lem1728993 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1728994 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1728993 x) (@lem1728980 x)). Qed.
Lemma lem1728995 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1728969 x) (@lem1728994 x)). Qed.
Lemma lem1728996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1728997 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1728996) (@lem1728995 x)). Qed.
Lemma lem1728999 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1729000 : term403 = term1990.
Proof. exact (@lem1728999 term24 term76). Qed.
Lemma lem1729007 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1729008 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729009 : term1991 = term1116.
Proof. exact (MK_COMB (@lem1729008) (@lem1729007)). Qed.
Lemma lem1729010 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729011 : term1992 = term1117.
Proof. exact (MK_COMB (@lem1729009) (@lem1729010)). Qed.
Lemma lem1729018 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1729019 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729020 : term1993 = term914.
Proof. exact (MK_COMB (@lem1729019) (@lem1729018)). Qed.
Lemma lem1729021 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729022 : term1994 = term915.
Proof. exact (MK_COMB (@lem1729020) (@lem1729021)). Qed.
Lemma lem1729023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729024 : term1995 = term946.
Proof. exact (MK_COMB (@lem1729023) (@lem1729022)). Qed.
Lemma lem1729025 : term1990 = term1996.
Proof. exact (MK_COMB (@lem1729024) (@lem1729011)). Qed.
Lemma lem1729026 : term403 = term1996.
Proof. exact (TRANS (@lem1729000) (@lem1729025)). Qed.
Lemma lem1729027 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1729028 (x : real) : (term511 x) = (term1997 x).
Proof. exact (MK_COMB (@lem1729027 x) (@lem1729026)). Qed.
Lemma lem1729029 (x : real) : (term545 x) = (term1998 x).
Proof. exact (MK_COMB (@lem1728997 x) (@lem1729028 x)). Qed.
Lemma lem1729030 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1729031 (x : real) : (term658 x) = (term1999 x).
Proof. exact (MK_COMB (@lem1729030 x) (@lem1729029 x)). Qed.
Lemma lem1729032 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1729033 (x : real) : (term2000 x) = (term2001 x).
Proof. exact (MK_COMB (@lem1729032 x) (@lem1729031 x)). Qed.
Lemma lem1729034 (x : real) : (term2002 x) = (term2001 x).
Proof. exact (eq_refl (term2002 x)). Qed.
Lemma lem1729035 (x : real) : (term2001 x) = (term2002 x).
Proof. exact (SYM (@lem1729034 x)). Qed.
Lemma lem1729036 (x : real) : (term2002 x) = (term2003 x).
Proof. exact (@lem1482981 (term2004 x) x). Qed.
Lemma lem1729037 (x : real) : (term2001 x) = (term2003 x).
Proof. exact (TRANS (@lem1729035 x) (@lem1729036 x)). Qed.
Lemma lem1729038 (x : real) : (term2005 x) = (term2006 x).
Proof. exact (eq_refl (term2005 x)). Qed.
Lemma lem1729039 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1729040 (x : real) : (term2007 x) = (term2008 x).
Proof. exact (MK_COMB (@lem1729039 x) (@lem1729038 x)). Qed.
Lemma lem1729041 (x : real) : (term2009 x) = (term2010 x).
Proof. exact (eq_refl (term2009 x)). Qed.
Lemma lem1729042 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1729043 (x : real) : (term2011 x) = (term2012 x).
Proof. exact (MK_COMB (@lem1729042 x) (@lem1729041 x)). Qed.
Lemma lem1729044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729045 (x : real) : (term2013 x) = (term2014 x).
Proof. exact (MK_COMB (@lem1729044) (@lem1729043 x)). Qed.
Lemma lem1729046 (x : real) : (term2003 x) = (term2015 x).
Proof. exact (MK_COMB (@lem1729045 x) (@lem1729040 x)). Qed.
Lemma lem1729047 (x : real) : (term2016 x) = (term2016 x).
Proof. exact (eq_refl (term2016 x)). Qed.
Lemma lem1729048 (x : real) : ((term2001 x) = (term2003 x)) = ((term2001 x) = (term2015 x)).
Proof. exact (MK_COMB (@lem1729047 x) (@lem1729046 x)). Qed.
Lemma lem1729049 (x : real) : (term2001 x) = (term2015 x).
Proof. exact (EQ_MP (@lem1729048 x) (@lem1729037 x)). Qed.
Lemma lem1729050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729051 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729050) (@lem1725350 x)). Qed.
Lemma lem1729052 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729051 x) (@lem1724639 x)). Qed.
Lemma lem1729053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729054 : term946 = term946.
Proof. exact (MK_COMB (@lem1729053) (@lem1728854)). Qed.
Lemma lem1729055 : term1996 = term1996.
Proof. exact (MK_COMB (@lem1729054) (@lem1727354)). Qed.
Lemma lem1729056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729057 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729056) (@lem1724687 x)). Qed.
Lemma lem1729058 (x : real) : (term1997 x) = (term1997 x).
Proof. exact (MK_COMB (@lem1729057 x) (@lem1729055)). Qed.
Lemma lem1729059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729060 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729059) (@lem1729052 x)). Qed.
Lemma lem1729061 (x : real) : (term1998 x) = (term1998 x).
Proof. exact (MK_COMB (@lem1729060 x) (@lem1729058 x)). Qed.
Lemma lem1729062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729063 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729062) (@lem1724666 x)). Qed.
Lemma lem1729064 (x : real) : (term1999 x) = (term1999 x).
Proof. exact (MK_COMB (@lem1729063 x) (@lem1729061 x)). Qed.
Lemma lem1729065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729066 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729065) (@lem1724639 x)). Qed.
Lemma lem1729067 (x : real) : (term2010 x) = (term2010 x).
Proof. exact (MK_COMB (@lem1729066 x) (@lem1729064 x)). Qed.
Lemma lem1729068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729069 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729068) (@lem1724639 x)). Qed.
Lemma lem1729070 (x : real) : (term2012 x) = (term2012 x).
Proof. exact (MK_COMB (@lem1729069 x) (@lem1729067 x)). Qed.
Lemma lem1729071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729072 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729071) (@lem1725350 x)). Qed.
Lemma lem1729073 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729072 x) (@lem1724639 x)). Qed.
Lemma lem1729074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729075 : term946 = term946.
Proof. exact (MK_COMB (@lem1729074) (@lem1728854)). Qed.
Lemma lem1729076 : term1996 = term1996.
Proof. exact (MK_COMB (@lem1729075) (@lem1727354)). Qed.
Lemma lem1729077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729078 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729077) (@lem1724687 x)). Qed.
Lemma lem1729079 (x : real) : (term1997 x) = (term1997 x).
Proof. exact (MK_COMB (@lem1729078 x) (@lem1729076)). Qed.
Lemma lem1729080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729081 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729080) (@lem1729073 x)). Qed.
Lemma lem1729082 (x : real) : (term1998 x) = (term1998 x).
Proof. exact (MK_COMB (@lem1729081 x) (@lem1729079 x)). Qed.
Lemma lem1729083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729084 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729083) (@lem1724666 x)). Qed.
Lemma lem1729085 (x : real) : (term1999 x) = (term1999 x).
Proof. exact (MK_COMB (@lem1729084 x) (@lem1729082 x)). Qed.
Lemma lem1729086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729087 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729086) (@lem1728062 x)). Qed.
Lemma lem1729088 (x : real) : (term2006 x) = (term2017 x).
Proof. exact (MK_COMB (@lem1729087 x) (@lem1729085 x)). Qed.
Lemma lem1729089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729090 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729089) (@lem1724751 x)). Qed.
Lemma lem1729091 (x : real) : (term2008 x) = (term2018 x).
Proof. exact (MK_COMB (@lem1729090 x) (@lem1729088 x)). Qed.
Lemma lem1729092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729093 (x : real) : (term2014 x) = (term2014 x).
Proof. exact (MK_COMB (@lem1729092) (@lem1729070 x)). Qed.
Lemma lem1729094 (x : real) : (term2015 x) = (term2019 x).
Proof. exact (MK_COMB (@lem1729093 x) (@lem1729091 x)). Qed.
Lemma lem1729105 (x : real) : (term2001 x) = (term2019 x).
Proof. exact (TRANS (@lem1729049 x) (@lem1729094 x)). Qed.
Lemma lem1729106 (x : real) : (term2000 x) = (term2019 x).
Proof. exact (TRANS (@lem1729033 x) (@lem1729105 x)). Qed.
Lemma lem1729107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729108 (x : real) : (term2020 x) = (term2021 x).
Proof. exact (MK_COMB (@lem1729107) (@lem1728966 x)). Qed.
Lemma lem1729109 (x : real) : (term656 x) = (term2022 x).
Proof. exact (MK_COMB (@lem1729108 x) (@lem1729106 x)). Qed.
Lemma lem1729111 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1729112 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1729111 x term76). Qed.
Lemma lem1729119 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1729120 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1729121 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1729120) (@lem1729119 x)). Qed.
Lemma lem1729122 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729123 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1729121 x) (@lem1729122)). Qed.
Lemma lem1729136 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1729137 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729136 x) (@lem1729123 x)). Qed.
Lemma lem1729138 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1729112 x) (@lem1729137 x)). Qed.
Lemma lem1729139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729140 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729139) (@lem1729138 x)). Qed.
Lemma lem1729141 (x : real) : (term571 x) = (term571 x).
Proof. exact (eq_refl (term571 x)). Qed.
Lemma lem1729142 (x : real) : (term591 x) = (term2023 x).
Proof. exact (MK_COMB (@lem1729140 x) (@lem1729141 x)). Qed.
Lemma lem1729143 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1729144 (x : real) : (term653 x) = (term2024 x).
Proof. exact (MK_COMB (@lem1729143 x) (@lem1729142 x)). Qed.
Lemma lem1729145 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1729146 (x : real) : (term2025 x) = (term2026 x).
Proof. exact (MK_COMB (@lem1729145 x) (@lem1729144 x)). Qed.
Lemma lem1729147 (x : real) : (term2027 x) = (term2026 x).
Proof. exact (eq_refl (term2027 x)). Qed.
Lemma lem1729148 (x : real) : (term2026 x) = (term2027 x).
Proof. exact (SYM (@lem1729147 x)). Qed.
Lemma lem1729149 (x : real) : (term2027 x) = (term2028 x).
Proof. exact (@lem1482981 (term2029 x) x). Qed.
Lemma lem1729150 (x : real) : (term2026 x) = (term2028 x).
Proof. exact (TRANS (@lem1729148 x) (@lem1729149 x)). Qed.
Lemma lem1729151 (x : real) : (term2030 x) = (term2031 x).
Proof. exact (eq_refl (term2030 x)). Qed.
Lemma lem1729152 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1729153 (x : real) : (term2032 x) = (term2033 x).
Proof. exact (MK_COMB (@lem1729152 x) (@lem1729151 x)). Qed.
Lemma lem1729154 (x : real) : (term2034 x) = (term2035 x).
Proof. exact (eq_refl (term2034 x)). Qed.
Lemma lem1729155 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1729156 (x : real) : (term2036 x) = (term2037 x).
Proof. exact (MK_COMB (@lem1729155 x) (@lem1729154 x)). Qed.
Lemma lem1729157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729158 (x : real) : (term2038 x) = (term2039 x).
Proof. exact (MK_COMB (@lem1729157) (@lem1729156 x)). Qed.
Lemma lem1729159 (x : real) : (term2028 x) = (term2040 x).
Proof. exact (MK_COMB (@lem1729158 x) (@lem1729153 x)). Qed.
Lemma lem1729160 (x : real) : (term2041 x) = (term2041 x).
Proof. exact (eq_refl (term2041 x)). Qed.
Lemma lem1729161 (x : real) : ((term2026 x) = (term2028 x)) = ((term2026 x) = (term2040 x)).
Proof. exact (MK_COMB (@lem1729160 x) (@lem1729159 x)). Qed.
Lemma lem1729162 (x : real) : (term2026 x) = (term2040 x).
Proof. exact (EQ_MP (@lem1729161 x) (@lem1729150 x)). Qed.
Lemma lem1729163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729164 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729163) (@lem1725350 x)). Qed.
Lemma lem1729165 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729164 x) (@lem1724639 x)). Qed.
Lemma lem1729166 : term427 = term426.
Proof. exact (@lem1483525 term98 term76). Qed.
Lemma lem1729172 : term413 = term414.
Proof. exact (@lem1483519 term98 term76). Qed.
Lemma lem1729174 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1729175 : term184 = term76.
Proof. exact (@lem1729174 term185). Qed.
Lemma lem1729176 : term240 = term240.
Proof. exact (eq_refl term240). Qed.
Lemma lem1729177 : term414 = term415.
Proof. exact (MK_COMB (@lem1729176) (@lem1729175)). Qed.
Lemma lem1729178 : term415 = term98.
Proof. exact (@lem1483450 term98). Qed.
Lemma lem1729179 : term414 = term98.
Proof. exact (TRANS (@lem1729177) (@lem1729178)). Qed.
Lemma lem1729181 : term413 = term98.
Proof. exact (TRANS (@lem1729172) (@lem1729179)). Qed.
Lemma lem1729182 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729183 : term424 = term425.
Proof. exact (MK_COMB (@lem1729182) (@lem1729181)). Qed.
Lemma lem1729184 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729185 : term426 = term427.
Proof. exact (MK_COMB (@lem1729183) (@lem1729184)). Qed.
Lemma lem1729186 : term427 = term427.
Proof. exact (TRANS (@lem1729166) (@lem1729185)). Qed.
Lemma lem1729187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729188 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729187) (@lem1725350 x)). Qed.
Lemma lem1729189 (x : real) : (term571 x) = (term571 x).
Proof. exact (MK_COMB (@lem1729188 x) (@lem1729186)). Qed.
Lemma lem1729190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729191 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729190) (@lem1729165 x)). Qed.
Lemma lem1729192 (x : real) : (term2023 x) = (term2023 x).
Proof. exact (MK_COMB (@lem1729191 x) (@lem1729189 x)). Qed.
Lemma lem1729193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729194 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729193) (@lem1724666 x)). Qed.
Lemma lem1729195 (x : real) : (term2024 x) = (term2024 x).
Proof. exact (MK_COMB (@lem1729194 x) (@lem1729192 x)). Qed.
Lemma lem1729196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729197 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729196) (@lem1724639 x)). Qed.
Lemma lem1729198 (x : real) : (term2035 x) = (term2035 x).
Proof. exact (MK_COMB (@lem1729197 x) (@lem1729195 x)). Qed.
Lemma lem1729199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729200 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729199) (@lem1724639 x)). Qed.
Lemma lem1729201 (x : real) : (term2037 x) = (term2037 x).
Proof. exact (MK_COMB (@lem1729200 x) (@lem1729198 x)). Qed.
Lemma lem1729202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729203 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729202) (@lem1725350 x)). Qed.
Lemma lem1729204 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729203 x) (@lem1724639 x)). Qed.
Lemma lem1729205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729206 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729205) (@lem1725350 x)). Qed.
Lemma lem1729207 (x : real) : (term571 x) = (term571 x).
Proof. exact (MK_COMB (@lem1729206 x) (@lem1729186)). Qed.
Lemma lem1729208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729209 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729208) (@lem1729204 x)). Qed.
Lemma lem1729210 (x : real) : (term2023 x) = (term2023 x).
Proof. exact (MK_COMB (@lem1729209 x) (@lem1729207 x)). Qed.
Lemma lem1729211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729212 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729211) (@lem1724666 x)). Qed.
Lemma lem1729213 (x : real) : (term2024 x) = (term2024 x).
Proof. exact (MK_COMB (@lem1729212 x) (@lem1729210 x)). Qed.
Lemma lem1729214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729215 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729214) (@lem1728062 x)). Qed.
Lemma lem1729216 (x : real) : (term2031 x) = (term2042 x).
Proof. exact (MK_COMB (@lem1729215 x) (@lem1729213 x)). Qed.
Lemma lem1729217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729218 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729217) (@lem1724751 x)). Qed.
Lemma lem1729219 (x : real) : (term2033 x) = (term2043 x).
Proof. exact (MK_COMB (@lem1729218 x) (@lem1729216 x)). Qed.
Lemma lem1729220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729221 (x : real) : (term2039 x) = (term2039 x).
Proof. exact (MK_COMB (@lem1729220) (@lem1729201 x)). Qed.
Lemma lem1729222 (x : real) : (term2040 x) = (term2044 x).
Proof. exact (MK_COMB (@lem1729221 x) (@lem1729219 x)). Qed.
Lemma lem1729223 (x : real) : (term2026 x) = (term2044 x).
Proof. exact (TRANS (@lem1729162 x) (@lem1729222 x)). Qed.
Lemma lem1729225 (x : real) : (term2045 x) = (term2043 x).
Proof. exact (eq_refl (term2045 x)). Qed.
Lemma lem1729226 (x : real) : (term2043 x) = (term2045 x).
Proof. exact (SYM (@lem1729225 x)). Qed.
Lemma lem1729227 (x : real) : (term2045 x) = (term2046 x).
Proof. exact (@lem1482981 (term2047 x) term73). Qed.
Lemma lem1729228 (x : real) : (term2043 x) = (term2046 x).
Proof. exact (TRANS (@lem1729226 x) (@lem1729227 x)). Qed.
Lemma lem1729229 (x : real) : (term2048 x) = (term2049 x).
Proof. exact (eq_refl (term2048 x)). Qed.
Lemma lem1729230 : term1080 = term1080.
Proof. exact (eq_refl term1080). Qed.
Lemma lem1729231 (x : real) : (term2050 x) = (term2051 x).
Proof. exact (MK_COMB (@lem1729230) (@lem1729229 x)). Qed.
Lemma lem1729232 (x : real) : (term2052 x) = (term2053 x).
Proof. exact (eq_refl (term2052 x)). Qed.
Lemma lem1729233 : term1085 = term1085.
Proof. exact (eq_refl term1085). Qed.
Lemma lem1729234 (x : real) : (term2054 x) = (term2055 x).
Proof. exact (MK_COMB (@lem1729233) (@lem1729232 x)). Qed.
Lemma lem1729235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729236 (x : real) : (term2056 x) = (term2057 x).
Proof. exact (MK_COMB (@lem1729235) (@lem1729234 x)). Qed.
Lemma lem1729237 (x : real) : (term2046 x) = (term2058 x).
Proof. exact (MK_COMB (@lem1729236 x) (@lem1729231 x)). Qed.
Lemma lem1729238 (x : real) : (term2059 x) = (term2059 x).
Proof. exact (eq_refl (term2059 x)). Qed.
Lemma lem1729239 (x : real) : ((term2043 x) = (term2046 x)) = ((term2043 x) = (term2058 x)).
Proof. exact (MK_COMB (@lem1729238 x) (@lem1729237 x)). Qed.
Lemma lem1729240 (x : real) : (term2043 x) = (term2058 x).
Proof. exact (EQ_MP (@lem1729239 x) (@lem1729228 x)). Qed.
Lemma lem1729241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729242 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729241) (@lem1725350 x)). Qed.
Lemma lem1729243 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729242 x) (@lem1724639 x)). Qed.
Lemma lem1729244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729245 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729244) (@lem1725350 x)). Qed.
Lemma lem1729246 (x : real) : (term1525 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1729245 x) (@lem1728854)). Qed.
Lemma lem1729247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729248 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729247) (@lem1729243 x)). Qed.
Lemma lem1729249 (x : real) : (term2060 x) = (term2060 x).
Proof. exact (MK_COMB (@lem1729248 x) (@lem1729246 x)). Qed.
Lemma lem1729250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729251 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729250) (@lem1724666 x)). Qed.
Lemma lem1729252 (x : real) : (term2061 x) = (term2061 x).
Proof. exact (MK_COMB (@lem1729251 x) (@lem1729249 x)). Qed.
Lemma lem1729253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729254 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729253) (@lem1725350 x)). Qed.
Lemma lem1729255 (x : real) : (term2062 x) = (term2062 x).
Proof. exact (MK_COMB (@lem1729254 x) (@lem1729252 x)). Qed.
Lemma lem1729256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729257 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729256) (@lem1724666 x)). Qed.
Lemma lem1729258 (x : real) : (term2053 x) = (term2053 x).
Proof. exact (MK_COMB (@lem1729257 x) (@lem1729255 x)). Qed.
Lemma lem1729259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729260 : term1085 = term1085.
Proof. exact (MK_COMB (@lem1729259) (@lem1725452)). Qed.
Lemma lem1729261 (x : real) : (term2055 x) = (term2055 x).
Proof. exact (MK_COMB (@lem1729260) (@lem1729258 x)). Qed.
Lemma lem1729262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729263 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729262) (@lem1725350 x)). Qed.
Lemma lem1729264 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729263 x) (@lem1724639 x)). Qed.
Lemma lem1729265 : term2063 = term2064.
Proof. exact (@lem1483525 term1121 term76). Qed.
Lemma lem1729266 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729270 : term1121 = term215.
Proof. exact (@lem1483512 term73). Qed.
Lemma lem1729272 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1729273 : term215 = term206.
Proof. exact (@lem1729272 term185 term185). Qed.
Lemma lem1729274 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1729275 : term205 = term185.
Proof. exact (EQ_MP (@lem1729274) (@lem940073)). Qed.
Lemma lem1729276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1729277 : term206 = term24.
Proof. exact (MK_COMB (@lem1729276) (@lem1729275)). Qed.
Lemma lem1729278 : term215 = term24.
Proof. exact (TRANS (@lem1729273) (@lem1729277)). Qed.
Lemma lem1729280 : term1121 = term24.
Proof. exact (TRANS (@lem1729270) (@lem1729278)). Qed.
Lemma lem1729281 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1729282 : term2065 = term1681.
Proof. exact (MK_COMB (@lem1729281) (@lem1729280)). Qed.
Lemma lem1729283 : term2066 = term878.
Proof. exact (MK_COMB (@lem1729282) (@lem1729266)). Qed.
Lemma lem1729284 : term878 = term879.
Proof. exact (@lem1483519 term24 term76). Qed.
Lemma lem1729286 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1729287 : term184 = term76.
Proof. exact (@lem1729286 term185). Qed.
Lemma lem1729288 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1729289 : term879 = term881.
Proof. exact (MK_COMB (@lem1729288) (@lem1729287)). Qed.
Lemma lem1729290 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1729291 : term879 = term24.
Proof. exact (TRANS (@lem1729289) (@lem1729290)). Qed.
Lemma lem1729292 : term878 = term24.
Proof. exact (TRANS (@lem1729284) (@lem1729291)). Qed.
Lemma lem1729293 : term2066 = term24.
Proof. exact (TRANS (@lem1729283) (@lem1729292)). Qed.
Lemma lem1729294 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729295 : term2067 = term1116.
Proof. exact (MK_COMB (@lem1729294) (@lem1729293)). Qed.
Lemma lem1729296 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729297 : term2064 = term1117.
Proof. exact (MK_COMB (@lem1729295) (@lem1729296)). Qed.
Lemma lem1729298 : term2063 = term1117.
Proof. exact (TRANS (@lem1729265) (@lem1729297)). Qed.
Lemma lem1729299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729300 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729299) (@lem1725350 x)). Qed.
Lemma lem1729301 (x : real) : (term2068 x) = (term1685 x).
Proof. exact (MK_COMB (@lem1729300 x) (@lem1729298)). Qed.
Lemma lem1729302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729303 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729302) (@lem1729264 x)). Qed.
Lemma lem1729304 (x : real) : (term2069 x) = (term1687 x).
Proof. exact (MK_COMB (@lem1729303 x) (@lem1729301 x)). Qed.
Lemma lem1729305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729306 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729305) (@lem1724666 x)). Qed.
Lemma lem1729307 (x : real) : (term2070 x) = (term2071 x).
Proof. exact (MK_COMB (@lem1729306 x) (@lem1729304 x)). Qed.
Lemma lem1729308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729309 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729308) (@lem1725350 x)). Qed.
Lemma lem1729310 (x : real) : (term2072 x) = (term2073 x).
Proof. exact (MK_COMB (@lem1729309 x) (@lem1729307 x)). Qed.
Lemma lem1729311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729312 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729311) (@lem1724666 x)). Qed.
Lemma lem1729313 (x : real) : (term2049 x) = (term2074 x).
Proof. exact (MK_COMB (@lem1729312 x) (@lem1729310 x)). Qed.
Lemma lem1729314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729315 : term1080 = term1135.
Proof. exact (MK_COMB (@lem1729314) (@lem1725499)). Qed.
Lemma lem1729316 (x : real) : (term2051 x) = (term2075 x).
Proof. exact (MK_COMB (@lem1729315) (@lem1729313 x)). Qed.
Lemma lem1729317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729318 (x : real) : (term2057 x) = (term2057 x).
Proof. exact (MK_COMB (@lem1729317) (@lem1729261 x)). Qed.
Lemma lem1729319 (x : real) : (term2058 x) = (term2076 x).
Proof. exact (MK_COMB (@lem1729318 x) (@lem1729316 x)). Qed.
Lemma lem1729331 (x : real) : (term2043 x) = (term2076 x).
Proof. exact (TRANS (@lem1729240 x) (@lem1729319 x)). Qed.
Lemma lem1729333 (x : real) : (term2077 x) = (term2037 x).
Proof. exact (eq_refl (term2077 x)). Qed.
Lemma lem1729334 (x : real) : (term2037 x) = (term2077 x).
Proof. exact (SYM (@lem1729333 x)). Qed.
Lemma lem1729335 (x : real) : (term2077 x) = (term2078 x).
Proof. exact (@lem1482981 (term2079 x) term73). Qed.
Lemma lem1729336 (x : real) : (term2037 x) = (term2078 x).
Proof. exact (TRANS (@lem1729334 x) (@lem1729335 x)). Qed.
Lemma lem1729337 (x : real) : (term2080 x) = (term2081 x).
Proof. exact (eq_refl (term2080 x)). Qed.
Lemma lem1729338 : term1080 = term1080.
Proof. exact (eq_refl term1080). Qed.
Lemma lem1729339 (x : real) : (term2082 x) = (term2083 x).
Proof. exact (MK_COMB (@lem1729338) (@lem1729337 x)). Qed.
Lemma lem1729340 (x : real) : (term2084 x) = (term2085 x).
Proof. exact (eq_refl (term2084 x)). Qed.
Lemma lem1729341 : term1085 = term1085.
Proof. exact (eq_refl term1085). Qed.
Lemma lem1729342 (x : real) : (term2086 x) = (term2087 x).
Proof. exact (MK_COMB (@lem1729341) (@lem1729340 x)). Qed.
Lemma lem1729343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729344 (x : real) : (term2088 x) = (term2089 x).
Proof. exact (MK_COMB (@lem1729343) (@lem1729342 x)). Qed.
Lemma lem1729345 (x : real) : (term2078 x) = (term2090 x).
Proof. exact (MK_COMB (@lem1729344 x) (@lem1729339 x)). Qed.
Lemma lem1729346 (x : real) : (term2091 x) = (term2091 x).
Proof. exact (eq_refl (term2091 x)). Qed.
Lemma lem1729347 (x : real) : ((term2037 x) = (term2078 x)) = ((term2037 x) = (term2090 x)).
Proof. exact (MK_COMB (@lem1729346 x) (@lem1729345 x)). Qed.
Lemma lem1729348 (x : real) : (term2037 x) = (term2090 x).
Proof. exact (EQ_MP (@lem1729347 x) (@lem1729336 x)). Qed.
Lemma lem1729349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729350 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729349) (@lem1725350 x)). Qed.
Lemma lem1729351 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729350 x) (@lem1724639 x)). Qed.
Lemma lem1729352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729353 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729352) (@lem1725350 x)). Qed.
Lemma lem1729354 (x : real) : (term1525 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1729353 x) (@lem1728854)). Qed.
Lemma lem1729355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729356 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729355) (@lem1729351 x)). Qed.
Lemma lem1729357 (x : real) : (term2060 x) = (term2060 x).
Proof. exact (MK_COMB (@lem1729356 x) (@lem1729354 x)). Qed.
Lemma lem1729358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729359 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729358) (@lem1724666 x)). Qed.
Lemma lem1729360 (x : real) : (term2061 x) = (term2061 x).
Proof. exact (MK_COMB (@lem1729359 x) (@lem1729357 x)). Qed.
Lemma lem1729361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729362 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729361) (@lem1724639 x)). Qed.
Lemma lem1729363 (x : real) : (term2092 x) = (term2092 x).
Proof. exact (MK_COMB (@lem1729362 x) (@lem1729360 x)). Qed.
Lemma lem1729364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729365 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729364) (@lem1724639 x)). Qed.
Lemma lem1729366 (x : real) : (term2085 x) = (term2085 x).
Proof. exact (MK_COMB (@lem1729365 x) (@lem1729363 x)). Qed.
Lemma lem1729367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729368 : term1085 = term1085.
Proof. exact (MK_COMB (@lem1729367) (@lem1725452)). Qed.
Lemma lem1729369 (x : real) : (term2087 x) = (term2087 x).
Proof. exact (MK_COMB (@lem1729368) (@lem1729366 x)). Qed.
Lemma lem1729370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729371 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729370) (@lem1725350 x)). Qed.
Lemma lem1729372 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729371 x) (@lem1724639 x)). Qed.
Lemma lem1729373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729374 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729373) (@lem1725350 x)). Qed.
Lemma lem1729375 (x : real) : (term2068 x) = (term1685 x).
Proof. exact (MK_COMB (@lem1729374 x) (@lem1729298)). Qed.
Lemma lem1729376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729377 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729376) (@lem1729372 x)). Qed.
Lemma lem1729378 (x : real) : (term2069 x) = (term1687 x).
Proof. exact (MK_COMB (@lem1729377 x) (@lem1729375 x)). Qed.
Lemma lem1729379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729380 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729379) (@lem1724666 x)). Qed.
Lemma lem1729381 (x : real) : (term2070 x) = (term2071 x).
Proof. exact (MK_COMB (@lem1729380 x) (@lem1729378 x)). Qed.
Lemma lem1729382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729383 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729382) (@lem1724639 x)). Qed.
Lemma lem1729384 (x : real) : (term2093 x) = (term2094 x).
Proof. exact (MK_COMB (@lem1729383 x) (@lem1729381 x)). Qed.
Lemma lem1729385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729386 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729385) (@lem1724639 x)). Qed.
Lemma lem1729387 (x : real) : (term2081 x) = (term2095 x).
Proof. exact (MK_COMB (@lem1729386 x) (@lem1729384 x)). Qed.
Lemma lem1729388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729389 : term1080 = term1135.
Proof. exact (MK_COMB (@lem1729388) (@lem1725499)). Qed.
Lemma lem1729390 (x : real) : (term2083 x) = (term2096 x).
Proof. exact (MK_COMB (@lem1729389) (@lem1729387 x)). Qed.
Lemma lem1729391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729392 (x : real) : (term2089 x) = (term2089 x).
Proof. exact (MK_COMB (@lem1729391) (@lem1729369 x)). Qed.
Lemma lem1729393 (x : real) : (term2090 x) = (term2097 x).
Proof. exact (MK_COMB (@lem1729392 x) (@lem1729390 x)). Qed.
Lemma lem1729405 (x : real) : (term2037 x) = (term2097 x).
Proof. exact (TRANS (@lem1729348 x) (@lem1729393 x)). Qed.
Lemma lem1729406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729407 (x : real) : (term2039 x) = (term2098 x).
Proof. exact (MK_COMB (@lem1729406) (@lem1729405 x)). Qed.
Lemma lem1729408 (x : real) : (term2044 x) = (term2099 x).
Proof. exact (MK_COMB (@lem1729407 x) (@lem1729331 x)). Qed.
Lemma lem1729409 (x : real) : (term2026 x) = (term2099 x).
Proof. exact (TRANS (@lem1729223 x) (@lem1729408 x)). Qed.
Lemma lem1729410 (x : real) : (term2025 x) = (term2099 x).
Proof. exact (TRANS (@lem1729146 x) (@lem1729409 x)). Qed.
Lemma lem1729412 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1729413 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1729412 x term76). Qed.
Lemma lem1729420 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1729421 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1729422 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1729421) (@lem1729420 x)). Qed.
Lemma lem1729423 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729424 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1729422 x) (@lem1729423)). Qed.
Lemma lem1729437 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1729438 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729437 x) (@lem1729424 x)). Qed.
Lemma lem1729439 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1729413 x) (@lem1729438 x)). Qed.
Lemma lem1729440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729441 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729440) (@lem1729439 x)). Qed.
Lemma lem1729443 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1729444 : term423 = term2100.
Proof. exact (@lem1729443 term73 term76). Qed.
Lemma lem1729451 : term1175 = term73.
Proof. exact (@lem1483460 term73). Qed.
Lemma lem1729452 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729453 : term2101 = term914.
Proof. exact (MK_COMB (@lem1729452) (@lem1729451)). Qed.
Lemma lem1729454 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729455 : term2102 = term915.
Proof. exact (MK_COMB (@lem1729453) (@lem1729454)). Qed.
Lemma lem1729462 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1729463 : term215 = term206.
Proof. exact (@lem1729462 term185 term185). Qed.
Lemma lem1729464 : (term204 = (BIT1 0)) = (term205 = term185).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1729465 : term205 = term185.
Proof. exact (EQ_MP (@lem1729464) (@lem940073)). Qed.
Lemma lem1729466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1729467 : term206 = term24.
Proof. exact (MK_COMB (@lem1729466) (@lem1729465)). Qed.
Lemma lem1729469 : term215 = term24.
Proof. exact (TRANS (@lem1729463) (@lem1729467)). Qed.
Lemma lem1729470 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729471 : term2103 = term1116.
Proof. exact (MK_COMB (@lem1729470) (@lem1729469)). Qed.
Lemma lem1729472 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729473 : term2104 = term1117.
Proof. exact (MK_COMB (@lem1729471) (@lem1729472)). Qed.
Lemma lem1729474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729475 : term2105 = term1135.
Proof. exact (MK_COMB (@lem1729474) (@lem1729473)). Qed.
Lemma lem1729476 : term2100 = term2106.
Proof. exact (MK_COMB (@lem1729475) (@lem1729455)). Qed.
Lemma lem1729477 : term423 = term2106.
Proof. exact (TRANS (@lem1729444) (@lem1729476)). Qed.
Lemma lem1729478 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1729479 (x : real) : (term572 x) = (term2107 x).
Proof. exact (MK_COMB (@lem1729478 x) (@lem1729477)). Qed.
Lemma lem1729480 (x : real) : (term592 x) = (term2108 x).
Proof. exact (MK_COMB (@lem1729441 x) (@lem1729479 x)). Qed.
Lemma lem1729481 (x : real) : (term321 x) = (term321 x).
Proof. exact (eq_refl (term321 x)). Qed.
Lemma lem1729482 (x : real) : (term654 x) = (term2109 x).
Proof. exact (MK_COMB (@lem1729481 x) (@lem1729480 x)). Qed.
Lemma lem1729483 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1729484 (x : real) : (term2110 x) = (term2111 x).
Proof. exact (MK_COMB (@lem1729483 x) (@lem1729482 x)). Qed.
Lemma lem1729485 (x : real) : (term2112 x) = (term2111 x).
Proof. exact (eq_refl (term2112 x)). Qed.
Lemma lem1729486 (x : real) : (term2111 x) = (term2112 x).
Proof. exact (SYM (@lem1729485 x)). Qed.
Lemma lem1729487 (x : real) : (term2112 x) = (term2113 x).
Proof. exact (@lem1482981 (term2114 x) x). Qed.
Lemma lem1729488 (x : real) : (term2111 x) = (term2113 x).
Proof. exact (TRANS (@lem1729486 x) (@lem1729487 x)). Qed.
Lemma lem1729489 (x : real) : (term2115 x) = (term2116 x).
Proof. exact (eq_refl (term2115 x)). Qed.
Lemma lem1729490 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1729491 (x : real) : (term2117 x) = (term2118 x).
Proof. exact (MK_COMB (@lem1729490 x) (@lem1729489 x)). Qed.
Lemma lem1729492 (x : real) : (term2119 x) = (term2120 x).
Proof. exact (eq_refl (term2119 x)). Qed.
Lemma lem1729493 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1729494 (x : real) : (term2121 x) = (term2122 x).
Proof. exact (MK_COMB (@lem1729493 x) (@lem1729492 x)). Qed.
Lemma lem1729495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729496 (x : real) : (term2123 x) = (term2124 x).
Proof. exact (MK_COMB (@lem1729495) (@lem1729494 x)). Qed.
Lemma lem1729497 (x : real) : (term2113 x) = (term2125 x).
Proof. exact (MK_COMB (@lem1729496 x) (@lem1729491 x)). Qed.
Lemma lem1729498 (x : real) : (term2126 x) = (term2126 x).
Proof. exact (eq_refl (term2126 x)). Qed.
Lemma lem1729499 (x : real) : ((term2111 x) = (term2113 x)) = ((term2111 x) = (term2125 x)).
Proof. exact (MK_COMB (@lem1729498 x) (@lem1729497 x)). Qed.
Lemma lem1729500 (x : real) : (term2111 x) = (term2125 x).
Proof. exact (EQ_MP (@lem1729499 x) (@lem1729488 x)). Qed.
Lemma lem1729501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729502 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729501) (@lem1725350 x)). Qed.
Lemma lem1729503 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729502 x) (@lem1724639 x)). Qed.
Lemma lem1729504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729505 : term1135 = term1135.
Proof. exact (MK_COMB (@lem1729504) (@lem1727354)). Qed.
Lemma lem1729506 : term2106 = term2106.
Proof. exact (MK_COMB (@lem1729505) (@lem1728854)). Qed.
Lemma lem1729507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729508 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729507) (@lem1725350 x)). Qed.
Lemma lem1729509 (x : real) : (term2107 x) = (term2107 x).
Proof. exact (MK_COMB (@lem1729508 x) (@lem1729506)). Qed.
Lemma lem1729510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729511 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729510) (@lem1729503 x)). Qed.
Lemma lem1729512 (x : real) : (term2108 x) = (term2108 x).
Proof. exact (MK_COMB (@lem1729511 x) (@lem1729509 x)). Qed.
Lemma lem1729513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729514 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729513) (@lem1724666 x)). Qed.
Lemma lem1729515 (x : real) : (term2109 x) = (term2109 x).
Proof. exact (MK_COMB (@lem1729514 x) (@lem1729512 x)). Qed.
Lemma lem1729516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729517 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729516) (@lem1724639 x)). Qed.
Lemma lem1729518 (x : real) : (term2120 x) = (term2120 x).
Proof. exact (MK_COMB (@lem1729517 x) (@lem1729515 x)). Qed.
Lemma lem1729519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729520 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729519) (@lem1724639 x)). Qed.
Lemma lem1729521 (x : real) : (term2122 x) = (term2122 x).
Proof. exact (MK_COMB (@lem1729520 x) (@lem1729518 x)). Qed.
Lemma lem1729522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729523 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729522) (@lem1725350 x)). Qed.
Lemma lem1729524 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1729523 x) (@lem1724639 x)). Qed.
Lemma lem1729525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729526 : term1135 = term1135.
Proof. exact (MK_COMB (@lem1729525) (@lem1727354)). Qed.
Lemma lem1729527 : term2106 = term2106.
Proof. exact (MK_COMB (@lem1729526) (@lem1728854)). Qed.
Lemma lem1729528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729529 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729528) (@lem1725350 x)). Qed.
Lemma lem1729530 (x : real) : (term2107 x) = (term2107 x).
Proof. exact (MK_COMB (@lem1729529 x) (@lem1729527)). Qed.
Lemma lem1729531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729532 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1729531) (@lem1729524 x)). Qed.
Lemma lem1729533 (x : real) : (term2108 x) = (term2108 x).
Proof. exact (MK_COMB (@lem1729532 x) (@lem1729530 x)). Qed.
Lemma lem1729534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729535 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729534) (@lem1724666 x)). Qed.
Lemma lem1729536 (x : real) : (term2109 x) = (term2109 x).
Proof. exact (MK_COMB (@lem1729535 x) (@lem1729533 x)). Qed.
Lemma lem1729537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729538 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729537) (@lem1728062 x)). Qed.
Lemma lem1729539 (x : real) : (term2116 x) = (term2127 x).
Proof. exact (MK_COMB (@lem1729538 x) (@lem1729536 x)). Qed.
Lemma lem1729540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729541 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729540) (@lem1724751 x)). Qed.
Lemma lem1729542 (x : real) : (term2118 x) = (term2128 x).
Proof. exact (MK_COMB (@lem1729541 x) (@lem1729539 x)). Qed.
Lemma lem1729543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729544 (x : real) : (term2124 x) = (term2124 x).
Proof. exact (MK_COMB (@lem1729543) (@lem1729521 x)). Qed.
Lemma lem1729545 (x : real) : (term2125 x) = (term2129 x).
Proof. exact (MK_COMB (@lem1729544 x) (@lem1729542 x)). Qed.
Lemma lem1729556 (x : real) : (term2111 x) = (term2129 x).
Proof. exact (TRANS (@lem1729500 x) (@lem1729545 x)). Qed.
Lemma lem1729557 (x : real) : (term2110 x) = (term2129 x).
Proof. exact (TRANS (@lem1729484 x) (@lem1729556 x)). Qed.
Lemma lem1729558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729559 (x : real) : (term2130 x) = (term2131 x).
Proof. exact (MK_COMB (@lem1729558) (@lem1729410 x)). Qed.
Lemma lem1729560 (x : real) : (term652 x) = (term2132 x).
Proof. exact (MK_COMB (@lem1729559 x) (@lem1729557 x)). Qed.
Lemma lem1729561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729562 (x : real) : (term660 x) = (term2133 x).
Proof. exact (MK_COMB (@lem1729561) (@lem1729109 x)). Qed.
Lemma lem1729563 (x : real) : (term661 x) = (term2134 x).
Proof. exact (MK_COMB (@lem1729562 x) (@lem1729560 x)). Qed.
Lemma lem1729564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729565 (x : real) : (term676 x) = (term2135 x).
Proof. exact (MK_COMB (@lem1729564) (@lem1728678 x)). Qed.
Lemma lem1729566 (x : real) : (term677 x) = (term2136 x).
Proof. exact (MK_COMB (@lem1729565 x) (@lem1729563 x)). Qed.
Lemma lem1729568 (x : real) : (term2137 x) = (term2138 x).
Proof. exact (eq_refl (term2137 x)). Qed.
Lemma lem1729569 (x : real) : (term2138 x) = (term2137 x).
Proof. exact (SYM (@lem1729568 x)). Qed.
Lemma lem1729570 (x : real) : (term2137 x) = (term2139 x).
Proof. exact (@lem1482981 (term2140 x) x). Qed.
Lemma lem1729571 (x : real) : (term2138 x) = (term2139 x).
Proof. exact (TRANS (@lem1729569 x) (@lem1729570 x)). Qed.
Lemma lem1729572 (x : real) : (term2141 x) = (term2142 x).
Proof. exact (eq_refl (term2141 x)). Qed.
Lemma lem1729573 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1729574 (x : real) : (term2143 x) = (term2144 x).
Proof. exact (MK_COMB (@lem1729573 x) (@lem1729572 x)). Qed.
Lemma lem1729575 (x : real) : (term2145 x) = (term2146 x).
Proof. exact (eq_refl (term2145 x)). Qed.
Lemma lem1729576 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1729577 (x : real) : (term2147 x) = (term2148 x).
Proof. exact (MK_COMB (@lem1729576 x) (@lem1729575 x)). Qed.
Lemma lem1729578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729579 (x : real) : (term2149 x) = (term2150 x).
Proof. exact (MK_COMB (@lem1729578) (@lem1729577 x)). Qed.
Lemma lem1729580 (x : real) : (term2139 x) = (term2151 x).
Proof. exact (MK_COMB (@lem1729579 x) (@lem1729574 x)). Qed.
Lemma lem1729581 (x : real) : (term2152 x) = (term2152 x).
Proof. exact (eq_refl (term2152 x)). Qed.
Lemma lem1729582 (x : real) : ((term2138 x) = (term2139 x)) = ((term2138 x) = (term2151 x)).
Proof. exact (MK_COMB (@lem1729581 x) (@lem1729580 x)). Qed.
Lemma lem1729583 (x : real) : (term2138 x) = (term2151 x).
Proof. exact (EQ_MP (@lem1729582 x) (@lem1729571 x)). Qed.
Lemma lem1729584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729585 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729584) (@lem1724687 x)). Qed.
Lemma lem1729586 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1729585 x) (@lem1724717)). Qed.
Lemma lem1729587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729588 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729587) (@lem1724687 x)). Qed.
Lemma lem1729589 (x : real) : (term842 x) = (term842 x).
Proof. exact (MK_COMB (@lem1729588 x) (@lem1729586 x)). Qed.
Lemma lem1729590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729591 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729590) (@lem1724639 x)). Qed.
Lemma lem1729592 (x : real) : (term1373 x) = (term1373 x).
Proof. exact (MK_COMB (@lem1729591 x) (@lem1729589 x)). Qed.
Lemma lem1729593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729594 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729593) (@lem1724639 x)). Qed.
Lemma lem1729595 (x : real) : (term2146 x) = (term2146 x).
Proof. exact (MK_COMB (@lem1729594 x) (@lem1729592 x)). Qed.
Lemma lem1729596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729597 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729596) (@lem1724639 x)). Qed.
Lemma lem1729598 (x : real) : (term2148 x) = (term2148 x).
Proof. exact (MK_COMB (@lem1729597 x) (@lem1729595 x)). Qed.
Lemma lem1729599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729600 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729599) (@lem1724687 x)). Qed.
Lemma lem1729601 (x : real) : (term527 x) = (term527 x).
Proof. exact (MK_COMB (@lem1729600 x) (@lem1724717)). Qed.
Lemma lem1729602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729603 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729602) (@lem1724781 x)). Qed.
Lemma lem1729604 (x : real) : (term852 x) = (term853 x).
Proof. exact (MK_COMB (@lem1729603 x) (@lem1729601 x)). Qed.
Lemma lem1729605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729606 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729605) (@lem1724639 x)). Qed.
Lemma lem1729607 (x : real) : (term1374 x) = (term1375 x).
Proof. exact (MK_COMB (@lem1729606 x) (@lem1729604 x)). Qed.
Lemma lem1729608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729609 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729608) (@lem1728062 x)). Qed.
Lemma lem1729610 (x : real) : (term2142 x) = (term2153 x).
Proof. exact (MK_COMB (@lem1729609 x) (@lem1729607 x)). Qed.
Lemma lem1729611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729612 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729611) (@lem1724751 x)). Qed.
Lemma lem1729613 (x : real) : (term2144 x) = (term2154 x).
Proof. exact (MK_COMB (@lem1729612 x) (@lem1729610 x)). Qed.
Lemma lem1729614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729615 (x : real) : (term2150 x) = (term2150 x).
Proof. exact (MK_COMB (@lem1729614) (@lem1729598 x)). Qed.
Lemma lem1729616 (x : real) : (term2151 x) = (term2155 x).
Proof. exact (MK_COMB (@lem1729615 x) (@lem1729613 x)). Qed.
Lemma lem1729617 (x : real) : (term2138 x) = (term2155 x).
Proof. exact (TRANS (@lem1729583 x) (@lem1729616 x)). Qed.
Lemma lem1729619 (x : real) : (term2156 x) = (term2154 x).
Proof. exact (eq_refl (term2156 x)). Qed.
Lemma lem1729620 (x : real) : (term2154 x) = (term2156 x).
Proof. exact (SYM (@lem1729619 x)). Qed.
Lemma lem1729621 (x : real) : (term2156 x) = (term2157 x).
Proof. exact (@lem1482981 (term2158 x) term24). Qed.
Lemma lem1729622 (x : real) : (term2154 x) = (term2157 x).
Proof. exact (TRANS (@lem1729620 x) (@lem1729621 x)). Qed.
Lemma lem1729623 (x : real) : (term2159 x) = (term2160 x).
Proof. exact (eq_refl (term2159 x)). Qed.
Lemma lem1729624 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1729625 (x : real) : (term2161 x) = (term2162 x).
Proof. exact (MK_COMB (@lem1729624) (@lem1729623 x)). Qed.
Lemma lem1729626 (x : real) : (term2163 x) = (term2164 x).
Proof. exact (eq_refl (term2163 x)). Qed.
Lemma lem1729627 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1729628 (x : real) : (term2165 x) = (term2166 x).
Proof. exact (MK_COMB (@lem1729627) (@lem1729626 x)). Qed.
Lemma lem1729629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729630 (x : real) : (term2167 x) = (term2168 x).
Proof. exact (MK_COMB (@lem1729629) (@lem1729628 x)). Qed.
Lemma lem1729631 (x : real) : (term2157 x) = (term2169 x).
Proof. exact (MK_COMB (@lem1729630 x) (@lem1729625 x)). Qed.
Lemma lem1729632 (x : real) : (term2170 x) = (term2170 x).
Proof. exact (eq_refl (term2170 x)). Qed.
Lemma lem1729633 (x : real) : ((term2154 x) = (term2157 x)) = ((term2154 x) = (term2169 x)).
Proof. exact (MK_COMB (@lem1729632 x) (@lem1729631 x)). Qed.
Lemma lem1729634 (x : real) : (term2154 x) = (term2169 x).
Proof. exact (EQ_MP (@lem1729633 x) (@lem1729622 x)). Qed.
Lemma lem1729635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729636 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729635) (@lem1724687 x)). Qed.
Lemma lem1729637 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1729636 x) (@lem1724870)). Qed.
Lemma lem1729638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729639 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729638) (@lem1724666 x)). Qed.
Lemma lem1729640 (x : real) : (term900 x) = (term901 x).
Proof. exact (MK_COMB (@lem1729639 x) (@lem1729637 x)). Qed.
Lemma lem1729641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729642 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729641) (@lem1724639 x)). Qed.
Lemma lem1729643 (x : real) : (term1394 x) = (term1395 x).
Proof. exact (MK_COMB (@lem1729642 x) (@lem1729640 x)). Qed.
Lemma lem1729644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729645 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729644) (@lem1725350 x)). Qed.
Lemma lem1729646 (x : real) : (term2171 x) = (term2172 x).
Proof. exact (MK_COMB (@lem1729645 x) (@lem1729643 x)). Qed.
Lemma lem1729647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729648 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729647) (@lem1724666 x)). Qed.
Lemma lem1729649 (x : real) : (term2164 x) = (term2173 x).
Proof. exact (MK_COMB (@lem1729648 x) (@lem1729646 x)). Qed.
Lemma lem1729650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729651 : term869 = term869.
Proof. exact (MK_COMB (@lem1729650) (@lem1724838)). Qed.
Lemma lem1729652 (x : real) : (term2166 x) = (term2174 x).
Proof. exact (MK_COMB (@lem1729651) (@lem1729649 x)). Qed.
Lemma lem1729653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729654 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729653) (@lem1724687 x)). Qed.
Lemma lem1729655 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1729654 x) (@lem1724954)). Qed.
Lemma lem1729656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729657 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729656) (@lem1724666 x)). Qed.
Lemma lem1729658 (x : real) : (term939 x) = (term940 x).
Proof. exact (MK_COMB (@lem1729657 x) (@lem1729655 x)). Qed.
Lemma lem1729659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729660 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729659) (@lem1724639 x)). Qed.
Lemma lem1729661 (x : real) : (term1400 x) = (term1401 x).
Proof. exact (MK_COMB (@lem1729660 x) (@lem1729658 x)). Qed.
Lemma lem1729662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729663 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729662) (@lem1725350 x)). Qed.
Lemma lem1729664 (x : real) : (term2175 x) = (term2176 x).
Proof. exact (MK_COMB (@lem1729663 x) (@lem1729661 x)). Qed.
Lemma lem1729665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729666 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729665) (@lem1724666 x)). Qed.
Lemma lem1729667 (x : real) : (term2160 x) = (term2177 x).
Proof. exact (MK_COMB (@lem1729666 x) (@lem1729664 x)). Qed.
Lemma lem1729668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729669 : term864 = term946.
Proof. exact (MK_COMB (@lem1729668) (@lem1724916)). Qed.
Lemma lem1729670 (x : real) : (term2162 x) = (term2178 x).
Proof. exact (MK_COMB (@lem1729669) (@lem1729667 x)). Qed.
Lemma lem1729671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729672 (x : real) : (term2168 x) = (term2179 x).
Proof. exact (MK_COMB (@lem1729671) (@lem1729652 x)). Qed.
Lemma lem1729673 (x : real) : (term2169 x) = (term2180 x).
Proof. exact (MK_COMB (@lem1729672 x) (@lem1729670 x)). Qed.
Lemma lem1729685 (x : real) : (term2154 x) = (term2180 x).
Proof. exact (TRANS (@lem1729634 x) (@lem1729673 x)). Qed.
Lemma lem1729687 (x : real) : (term2181 x) = (term2148 x).
Proof. exact (eq_refl (term2181 x)). Qed.
Lemma lem1729688 (x : real) : (term2148 x) = (term2181 x).
Proof. exact (SYM (@lem1729687 x)). Qed.
Lemma lem1729689 (x : real) : (term2181 x) = (term2182 x).
Proof. exact (@lem1482981 (term2183 x) term24). Qed.
Lemma lem1729690 (x : real) : (term2148 x) = (term2182 x).
Proof. exact (TRANS (@lem1729688 x) (@lem1729689 x)). Qed.
Lemma lem1729691 (x : real) : (term2184 x) = (term2185 x).
Proof. exact (eq_refl (term2184 x)). Qed.
Lemma lem1729692 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1729693 (x : real) : (term2186 x) = (term2187 x).
Proof. exact (MK_COMB (@lem1729692) (@lem1729691 x)). Qed.
Lemma lem1729694 (x : real) : (term2188 x) = (term2189 x).
Proof. exact (eq_refl (term2188 x)). Qed.
Lemma lem1729695 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1729696 (x : real) : (term2190 x) = (term2191 x).
Proof. exact (MK_COMB (@lem1729695) (@lem1729694 x)). Qed.
Lemma lem1729697 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729698 (x : real) : (term2192 x) = (term2193 x).
Proof. exact (MK_COMB (@lem1729697) (@lem1729696 x)). Qed.
Lemma lem1729699 (x : real) : (term2182 x) = (term2194 x).
Proof. exact (MK_COMB (@lem1729698 x) (@lem1729693 x)). Qed.
Lemma lem1729700 (x : real) : (term2195 x) = (term2195 x).
Proof. exact (eq_refl (term2195 x)). Qed.
Lemma lem1729701 (x : real) : ((term2148 x) = (term2182 x)) = ((term2148 x) = (term2194 x)).
Proof. exact (MK_COMB (@lem1729700 x) (@lem1729699 x)). Qed.
Lemma lem1729702 (x : real) : (term2148 x) = (term2194 x).
Proof. exact (EQ_MP (@lem1729701 x) (@lem1729690 x)). Qed.
Lemma lem1729703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729704 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729703) (@lem1724687 x)). Qed.
Lemma lem1729705 (x : real) : (term898 x) = (term899 x).
Proof. exact (MK_COMB (@lem1729704 x) (@lem1724870)). Qed.
Lemma lem1729706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729707 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729706) (@lem1724687 x)). Qed.
Lemma lem1729708 (x : real) : (term965 x) = (term966 x).
Proof. exact (MK_COMB (@lem1729707 x) (@lem1729705 x)). Qed.
Lemma lem1729709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729710 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729709) (@lem1724639 x)). Qed.
Lemma lem1729711 (x : real) : (term1423 x) = (term1424 x).
Proof. exact (MK_COMB (@lem1729710 x) (@lem1729708 x)). Qed.
Lemma lem1729712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729713 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729712) (@lem1724639 x)). Qed.
Lemma lem1729714 (x : real) : (term2196 x) = (term2197 x).
Proof. exact (MK_COMB (@lem1729713 x) (@lem1729711 x)). Qed.
Lemma lem1729715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729716 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729715) (@lem1724639 x)). Qed.
Lemma lem1729717 (x : real) : (term2189 x) = (term2198 x).
Proof. exact (MK_COMB (@lem1729716 x) (@lem1729714 x)). Qed.
Lemma lem1729718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729719 : term869 = term869.
Proof. exact (MK_COMB (@lem1729718) (@lem1724838)). Qed.
Lemma lem1729720 (x : real) : (term2191 x) = (term2199 x).
Proof. exact (MK_COMB (@lem1729719) (@lem1729717 x)). Qed.
Lemma lem1729721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729722 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729721) (@lem1724687 x)). Qed.
Lemma lem1729723 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1729722 x) (@lem1724954)). Qed.
Lemma lem1729724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729725 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729724) (@lem1724687 x)). Qed.
Lemma lem1729726 (x : real) : (term973 x) = (term974 x).
Proof. exact (MK_COMB (@lem1729725 x) (@lem1729723 x)). Qed.
Lemma lem1729727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729728 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729727) (@lem1724639 x)). Qed.
Lemma lem1729729 (x : real) : (term1429 x) = (term1430 x).
Proof. exact (MK_COMB (@lem1729728 x) (@lem1729726 x)). Qed.
Lemma lem1729730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729731 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729730) (@lem1724639 x)). Qed.
Lemma lem1729732 (x : real) : (term2200 x) = (term2201 x).
Proof. exact (MK_COMB (@lem1729731 x) (@lem1729729 x)). Qed.
Lemma lem1729733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729734 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729733) (@lem1724639 x)). Qed.
Lemma lem1729735 (x : real) : (term2185 x) = (term2202 x).
Proof. exact (MK_COMB (@lem1729734 x) (@lem1729732 x)). Qed.
Lemma lem1729736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729737 : term864 = term946.
Proof. exact (MK_COMB (@lem1729736) (@lem1724916)). Qed.
Lemma lem1729738 (x : real) : (term2187 x) = (term2203 x).
Proof. exact (MK_COMB (@lem1729737) (@lem1729735 x)). Qed.
Lemma lem1729739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729740 (x : real) : (term2193 x) = (term2204 x).
Proof. exact (MK_COMB (@lem1729739) (@lem1729720 x)). Qed.
Lemma lem1729741 (x : real) : (term2194 x) = (term2205 x).
Proof. exact (MK_COMB (@lem1729740 x) (@lem1729738 x)). Qed.
Lemma lem1729753 (x : real) : (term2148 x) = (term2205 x).
Proof. exact (TRANS (@lem1729702 x) (@lem1729741 x)). Qed.
Lemma lem1729754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729755 (x : real) : (term2150 x) = (term2206 x).
Proof. exact (MK_COMB (@lem1729754) (@lem1729753 x)). Qed.
Lemma lem1729756 (x : real) : (term2155 x) = (term2207 x).
Proof. exact (MK_COMB (@lem1729755 x) (@lem1729685 x)). Qed.
Lemma lem1729758 (x : real) : (term2138 x) = (term2207 x).
Proof. exact (TRANS (@lem1729617 x) (@lem1729756 x)). Qed.
Lemma lem1729760 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1729761 : term222 = term987.
Proof. exact (@lem1729760 term24 term24 term76). Qed.
Lemma lem1729768 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1729771 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1729772 : term989 = term990.
Proof. exact (MK_COMB (@lem1729771) (@lem1729768)). Qed.
Lemma lem1729773 : term990 = term924.
Proof. exact (@lem1367770 term185 term185). Qed.
Lemma lem1729774 : term920 = term921.
Proof. exact (@lem706885). Qed.
Lemma lem1729775 : (term920 = term921) = (term922 = term923).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term921). Qed.
Lemma lem1729776 : term922 = term923.
Proof. exact (EQ_MP (@lem1729775) (@lem1729774)). Qed.
Lemma lem1729777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1729778 : term924 = term925.
Proof. exact (MK_COMB (@lem1729777) (@lem1729776)). Qed.
Lemma lem1729779 : term990 = term925.
Proof. exact (TRANS (@lem1729773) (@lem1729778)). Qed.
Lemma lem1729780 : term989 = term925.
Proof. exact (TRANS (@lem1729772) (@lem1729779)). Qed.
Lemma lem1729781 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729782 : term991 = term992.
Proof. exact (MK_COMB (@lem1729781) (@lem1729780)). Qed.
Lemma lem1729783 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729784 : term993 = term994.
Proof. exact (MK_COMB (@lem1729782) (@lem1729783)). Qed.
Lemma lem1729791 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1729794 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1729795 : term995 = term886.
Proof. exact (MK_COMB (@lem1729794) (@lem1729791)). Qed.
Lemma lem1729797 (m : nat) : (term887 m) = term76.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1729798 : term886 = term76.
Proof. exact (@lem1729797 term185). Qed.
Lemma lem1729799 : term995 = term76.
Proof. exact (TRANS (@lem1729795) (@lem1729798)). Qed.
Lemma lem1729800 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1729801 : term996 = term896.
Proof. exact (MK_COMB (@lem1729800) (@lem1729799)). Qed.
Lemma lem1729802 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1729803 : term997 = term897.
Proof. exact (MK_COMB (@lem1729801) (@lem1729802)). Qed.
Lemma lem1729804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729805 : term998 = term999.
Proof. exact (MK_COMB (@lem1729804) (@lem1729803)). Qed.
Lemma lem1729806 : term987 = term1000.
Proof. exact (MK_COMB (@lem1729805) (@lem1729784)). Qed.
Lemma lem1729807 : term222 = term1000.
Proof. exact (TRANS (@lem1729761) (@lem1729806)). Qed.
Lemma lem1729808 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1729809 (x : real) : (term528 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1729808 x) (@lem1729807)). Qed.
Lemma lem1729810 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1729811 (x : real) : (term558 x) = (term1002 x).
Proof. exact (MK_COMB (@lem1729810 x) (@lem1729809 x)). Qed.
Lemma lem1729812 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1729813 (x : real) : (term640 x) = (term1439 x).
Proof. exact (MK_COMB (@lem1729812 x) (@lem1729811 x)). Qed.
Lemma lem1729814 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1729815 (x : real) : (term2208 x) = (term2209 x).
Proof. exact (MK_COMB (@lem1729814 x) (@lem1729813 x)). Qed.
Lemma lem1729816 (x : real) : (term2210 x) = (term2209 x).
Proof. exact (eq_refl (term2210 x)). Qed.
Lemma lem1729817 (x : real) : (term2209 x) = (term2210 x).
Proof. exact (SYM (@lem1729816 x)). Qed.
Lemma lem1729818 (x : real) : (term2210 x) = (term2211 x).
Proof. exact (@lem1482981 (term2212 x) x). Qed.
Lemma lem1729819 (x : real) : (term2209 x) = (term2211 x).
Proof. exact (TRANS (@lem1729817 x) (@lem1729818 x)). Qed.
Lemma lem1729820 (x : real) : (term2213 x) = (term2214 x).
Proof. exact (eq_refl (term2213 x)). Qed.
Lemma lem1729821 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1729822 (x : real) : (term2215 x) = (term2216 x).
Proof. exact (MK_COMB (@lem1729821 x) (@lem1729820 x)). Qed.
Lemma lem1729823 (x : real) : (term2217 x) = (term2218 x).
Proof. exact (eq_refl (term2217 x)). Qed.
Lemma lem1729824 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1729825 (x : real) : (term2219 x) = (term2220 x).
Proof. exact (MK_COMB (@lem1729824 x) (@lem1729823 x)). Qed.
Lemma lem1729826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729827 (x : real) : (term2221 x) = (term2222 x).
Proof. exact (MK_COMB (@lem1729826) (@lem1729825 x)). Qed.
Lemma lem1729828 (x : real) : (term2211 x) = (term2223 x).
Proof. exact (MK_COMB (@lem1729827 x) (@lem1729822 x)). Qed.
Lemma lem1729829 (x : real) : (term2224 x) = (term2224 x).
Proof. exact (eq_refl (term2224 x)). Qed.
Lemma lem1729830 (x : real) : ((term2209 x) = (term2211 x)) = ((term2209 x) = (term2223 x)).
Proof. exact (MK_COMB (@lem1729829 x) (@lem1729828 x)). Qed.
Lemma lem1729831 (x : real) : (term2209 x) = (term2223 x).
Proof. exact (EQ_MP (@lem1729830 x) (@lem1729819 x)). Qed.
Lemma lem1729832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729833 : term999 = term999.
Proof. exact (MK_COMB (@lem1729832) (@lem1725193)). Qed.
Lemma lem1729834 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1729833) (@lem1725214)). Qed.
Lemma lem1729835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729836 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729835) (@lem1724687 x)). Qed.
Lemma lem1729837 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1729836 x) (@lem1729834)). Qed.
Lemma lem1729838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729839 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729838) (@lem1724687 x)). Qed.
Lemma lem1729840 (x : real) : (term1029 x) = (term1029 x).
Proof. exact (MK_COMB (@lem1729839 x) (@lem1729837 x)). Qed.
Lemma lem1729841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729842 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729841) (@lem1724639 x)). Qed.
Lemma lem1729843 (x : real) : (term1457 x) = (term1457 x).
Proof. exact (MK_COMB (@lem1729842 x) (@lem1729840 x)). Qed.
Lemma lem1729844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729845 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729844) (@lem1724639 x)). Qed.
Lemma lem1729846 (x : real) : (term2218 x) = (term2218 x).
Proof. exact (MK_COMB (@lem1729845 x) (@lem1729843 x)). Qed.
Lemma lem1729847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729848 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729847) (@lem1724639 x)). Qed.
Lemma lem1729849 (x : real) : (term2220 x) = (term2220 x).
Proof. exact (MK_COMB (@lem1729848 x) (@lem1729846 x)). Qed.
Lemma lem1729850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729851 : term999 = term999.
Proof. exact (MK_COMB (@lem1729850) (@lem1725193)). Qed.
Lemma lem1729852 : term1000 = term1000.
Proof. exact (MK_COMB (@lem1729851) (@lem1725214)). Qed.
Lemma lem1729853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729854 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729853) (@lem1724687 x)). Qed.
Lemma lem1729855 (x : real) : (term1001 x) = (term1001 x).
Proof. exact (MK_COMB (@lem1729854 x) (@lem1729852)). Qed.
Lemma lem1729856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729857 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729856) (@lem1724781 x)). Qed.
Lemma lem1729858 (x : real) : (term1031 x) = (term1032 x).
Proof. exact (MK_COMB (@lem1729857 x) (@lem1729855 x)). Qed.
Lemma lem1729859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729860 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729859) (@lem1724639 x)). Qed.
Lemma lem1729861 (x : real) : (term1458 x) = (term1459 x).
Proof. exact (MK_COMB (@lem1729860 x) (@lem1729858 x)). Qed.
Lemma lem1729862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729863 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729862) (@lem1728062 x)). Qed.
Lemma lem1729864 (x : real) : (term2214 x) = (term2225 x).
Proof. exact (MK_COMB (@lem1729863 x) (@lem1729861 x)). Qed.
Lemma lem1729865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729866 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729865) (@lem1724751 x)). Qed.
Lemma lem1729867 (x : real) : (term2216 x) = (term2226 x).
Proof. exact (MK_COMB (@lem1729866 x) (@lem1729864 x)). Qed.
Lemma lem1729868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729869 (x : real) : (term2222 x) = (term2222 x).
Proof. exact (MK_COMB (@lem1729868) (@lem1729849 x)). Qed.
Lemma lem1729870 (x : real) : (term2223 x) = (term2227 x).
Proof. exact (MK_COMB (@lem1729869 x) (@lem1729867 x)). Qed.
Lemma lem1729881 (x : real) : (term2209 x) = (term2227 x).
Proof. exact (TRANS (@lem1729831 x) (@lem1729870 x)). Qed.
Lemma lem1729882 (x : real) : (term2208 x) = (term2227 x).
Proof. exact (TRANS (@lem1729815 x) (@lem1729881 x)). Qed.
Lemma lem1729883 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729884 (x : real) : (term2228 x) = (term2229 x).
Proof. exact (MK_COMB (@lem1729883) (@lem1729758 x)). Qed.
Lemma lem1729885 (x : real) : (term638 x) = (term2230 x).
Proof. exact (MK_COMB (@lem1729884 x) (@lem1729882 x)). Qed.
Lemma lem1729887 (x : real) : (term2231 x) = (term2232 x).
Proof. exact (eq_refl (term2231 x)). Qed.
Lemma lem1729888 (x : real) : (term2232 x) = (term2231 x).
Proof. exact (SYM (@lem1729887 x)). Qed.
Lemma lem1729889 (x : real) : (term2231 x) = (term2233 x).
Proof. exact (@lem1482981 (term2234 x) x). Qed.
Lemma lem1729890 (x : real) : (term2232 x) = (term2233 x).
Proof. exact (TRANS (@lem1729888 x) (@lem1729889 x)). Qed.
Lemma lem1729891 (x : real) : (term2235 x) = (term2236 x).
Proof. exact (eq_refl (term2235 x)). Qed.
Lemma lem1729892 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1729893 (x : real) : (term2237 x) = (term2238 x).
Proof. exact (MK_COMB (@lem1729892 x) (@lem1729891 x)). Qed.
Lemma lem1729894 (x : real) : (term2239 x) = (term2240 x).
Proof. exact (eq_refl (term2239 x)). Qed.
Lemma lem1729895 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1729896 (x : real) : (term2241 x) = (term2242 x).
Proof. exact (MK_COMB (@lem1729895 x) (@lem1729894 x)). Qed.
Lemma lem1729897 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729898 (x : real) : (term2243 x) = (term2244 x).
Proof. exact (MK_COMB (@lem1729897) (@lem1729896 x)). Qed.
Lemma lem1729899 (x : real) : (term2233 x) = (term2245 x).
Proof. exact (MK_COMB (@lem1729898 x) (@lem1729893 x)). Qed.
Lemma lem1729900 (x : real) : (term2246 x) = (term2246 x).
Proof. exact (eq_refl (term2246 x)). Qed.
Lemma lem1729901 (x : real) : ((term2232 x) = (term2233 x)) = ((term2232 x) = (term2245 x)).
Proof. exact (MK_COMB (@lem1729900 x) (@lem1729899 x)). Qed.
Lemma lem1729902 (x : real) : (term2232 x) = (term2245 x).
Proof. exact (EQ_MP (@lem1729901 x) (@lem1729890 x)). Qed.
Lemma lem1729903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729904 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729903) (@lem1725350 x)). Qed.
Lemma lem1729905 (x : real) : (term523 x) = (term523 x).
Proof. exact (MK_COMB (@lem1729904 x) (@lem1726962)). Qed.
Lemma lem1729906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729907 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1729906) (@lem1724687 x)). Qed.
Lemma lem1729908 (x : real) : (term1489 x) = (term1489 x).
Proof. exact (MK_COMB (@lem1729907 x) (@lem1729905 x)). Qed.
Lemma lem1729909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729910 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729909) (@lem1724639 x)). Qed.
Lemma lem1729911 (x : real) : (term1490 x) = (term1490 x).
Proof. exact (MK_COMB (@lem1729910 x) (@lem1729908 x)). Qed.
Lemma lem1729912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729913 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729912) (@lem1724639 x)). Qed.
Lemma lem1729914 (x : real) : (term2240 x) = (term2240 x).
Proof. exact (MK_COMB (@lem1729913 x) (@lem1729911 x)). Qed.
Lemma lem1729915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729916 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729915) (@lem1724639 x)). Qed.
Lemma lem1729917 (x : real) : (term2242 x) = (term2242 x).
Proof. exact (MK_COMB (@lem1729916 x) (@lem1729914 x)). Qed.
Lemma lem1729918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729919 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729918) (@lem1725350 x)). Qed.
Lemma lem1729920 (x : real) : (term523 x) = (term523 x).
Proof. exact (MK_COMB (@lem1729919 x) (@lem1726962)). Qed.
Lemma lem1729921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729922 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729921) (@lem1724781 x)). Qed.
Lemma lem1729923 (x : real) : (term1491 x) = (term1492 x).
Proof. exact (MK_COMB (@lem1729922 x) (@lem1729920 x)). Qed.
Lemma lem1729924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729925 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729924) (@lem1724639 x)). Qed.
Lemma lem1729926 (x : real) : (term1493 x) = (term1494 x).
Proof. exact (MK_COMB (@lem1729925 x) (@lem1729923 x)). Qed.
Lemma lem1729927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729928 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729927) (@lem1728062 x)). Qed.
Lemma lem1729929 (x : real) : (term2236 x) = (term2247 x).
Proof. exact (MK_COMB (@lem1729928 x) (@lem1729926 x)). Qed.
Lemma lem1729930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729931 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729930) (@lem1724751 x)). Qed.
Lemma lem1729932 (x : real) : (term2238 x) = (term2248 x).
Proof. exact (MK_COMB (@lem1729931 x) (@lem1729929 x)). Qed.
Lemma lem1729933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729934 (x : real) : (term2244 x) = (term2244 x).
Proof. exact (MK_COMB (@lem1729933) (@lem1729917 x)). Qed.
Lemma lem1729935 (x : real) : (term2245 x) = (term2249 x).
Proof. exact (MK_COMB (@lem1729934 x) (@lem1729932 x)). Qed.
Lemma lem1729936 (x : real) : (term2232 x) = (term2249 x).
Proof. exact (TRANS (@lem1729902 x) (@lem1729935 x)). Qed.
Lemma lem1729938 (x : real) : (term2250 x) = (term2248 x).
Proof. exact (eq_refl (term2250 x)). Qed.
Lemma lem1729939 (x : real) : (term2248 x) = (term2250 x).
Proof. exact (SYM (@lem1729938 x)). Qed.
Lemma lem1729940 (x : real) : (term2250 x) = (term2251 x).
Proof. exact (@lem1482981 (term2252 x) term76). Qed.
Lemma lem1729941 (x : real) : (term2248 x) = (term2251 x).
Proof. exact (TRANS (@lem1729939 x) (@lem1729940 x)). Qed.
Lemma lem1729942 (x : real) : (term2253 x) = (term2254 x).
Proof. exact (eq_refl (term2253 x)). Qed.
Lemma lem1729943 : term999 = term999.
Proof. exact (eq_refl term999). Qed.
Lemma lem1729944 (x : real) : (term2255 x) = (term2256 x).
Proof. exact (MK_COMB (@lem1729943) (@lem1729942 x)). Qed.
Lemma lem1729945 (x : real) : (term2257 x) = (term2258 x).
Proof. exact (eq_refl (term2257 x)). Qed.
Lemma lem1729946 : term1507 = term1507.
Proof. exact (eq_refl term1507). Qed.
Lemma lem1729947 (x : real) : (term2259 x) = (term2260 x).
Proof. exact (MK_COMB (@lem1729946) (@lem1729945 x)). Qed.
Lemma lem1729948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729949 (x : real) : (term2261 x) = (term2262 x).
Proof. exact (MK_COMB (@lem1729948) (@lem1729947 x)). Qed.
Lemma lem1729950 (x : real) : (term2251 x) = (term2263 x).
Proof. exact (MK_COMB (@lem1729949 x) (@lem1729944 x)). Qed.
Lemma lem1729951 (x : real) : (term2264 x) = (term2264 x).
Proof. exact (eq_refl (term2264 x)). Qed.
Lemma lem1729952 (x : real) : ((term2248 x) = (term2251 x)) = ((term2248 x) = (term2263 x)).
Proof. exact (MK_COMB (@lem1729951 x) (@lem1729950 x)). Qed.
Lemma lem1729953 (x : real) : (term2248 x) = (term2263 x).
Proof. exact (EQ_MP (@lem1729952 x) (@lem1729941 x)). Qed.
Lemma lem1729954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729955 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729954) (@lem1725350 x)). Qed.
Lemma lem1729956 (x : real) : (term1524 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1729955 x) (@lem1727067)). Qed.
Lemma lem1729957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729958 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729957) (@lem1724666 x)). Qed.
Lemma lem1729959 (x : real) : (term1526 x) = (term1527 x).
Proof. exact (MK_COMB (@lem1729958 x) (@lem1729956 x)). Qed.
Lemma lem1729960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729961 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729960) (@lem1724639 x)). Qed.
Lemma lem1729962 (x : real) : (term1528 x) = (term1529 x).
Proof. exact (MK_COMB (@lem1729961 x) (@lem1729959 x)). Qed.
Lemma lem1729963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729964 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729963) (@lem1725350 x)). Qed.
Lemma lem1729965 (x : real) : (term2265 x) = (term2266 x).
Proof. exact (MK_COMB (@lem1729964 x) (@lem1729962 x)). Qed.
Lemma lem1729966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729967 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729966) (@lem1724666 x)). Qed.
Lemma lem1729968 (x : real) : (term2258 x) = (term2267 x).
Proof. exact (MK_COMB (@lem1729967 x) (@lem1729965 x)). Qed.
Lemma lem1729969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729970 : term1507 = term1507.
Proof. exact (MK_COMB (@lem1729969) (@lem1727037)). Qed.
Lemma lem1729971 (x : real) : (term2260 x) = (term2268 x).
Proof. exact (MK_COMB (@lem1729970) (@lem1729968 x)). Qed.
Lemma lem1729972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729973 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729972) (@lem1725350 x)). Qed.
Lemma lem1729974 (x : real) : (term1542 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1729973 x) (@lem1727123)). Qed.
Lemma lem1729975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729976 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729975) (@lem1724666 x)). Qed.
Lemma lem1729977 (x : real) : (term1543 x) = (term1527 x).
Proof. exact (MK_COMB (@lem1729976 x) (@lem1729974 x)). Qed.
Lemma lem1729978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729979 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1729978) (@lem1724639 x)). Qed.
Lemma lem1729980 (x : real) : (term1544 x) = (term1529 x).
Proof. exact (MK_COMB (@lem1729979 x) (@lem1729977 x)). Qed.
Lemma lem1729981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729982 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1729981) (@lem1725350 x)). Qed.
Lemma lem1729983 (x : real) : (term2269 x) = (term2266 x).
Proof. exact (MK_COMB (@lem1729982 x) (@lem1729980 x)). Qed.
Lemma lem1729984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729985 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1729984) (@lem1724666 x)). Qed.
Lemma lem1729986 (x : real) : (term2254 x) = (term2267 x).
Proof. exact (MK_COMB (@lem1729985 x) (@lem1729983 x)). Qed.
Lemma lem1729987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1729988 : term999 = term999.
Proof. exact (MK_COMB (@lem1729987) (@lem1725193)). Qed.
Lemma lem1729989 (x : real) : (term2256 x) = (term2270 x).
Proof. exact (MK_COMB (@lem1729988) (@lem1729986 x)). Qed.
Lemma lem1729990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1729991 (x : real) : (term2262 x) = (term2271 x).
Proof. exact (MK_COMB (@lem1729990) (@lem1729971 x)). Qed.
Lemma lem1729992 (x : real) : (term2263 x) = (term2272 x).
Proof. exact (MK_COMB (@lem1729991 x) (@lem1729989 x)). Qed.
Lemma lem1730004 (x : real) : (term2248 x) = (term2272 x).
Proof. exact (TRANS (@lem1729953 x) (@lem1729992 x)). Qed.
Lemma lem1730006 (x : real) : (term2273 x) = (term2242 x).
Proof. exact (eq_refl (term2273 x)). Qed.
Lemma lem1730007 (x : real) : (term2242 x) = (term2273 x).
Proof. exact (SYM (@lem1730006 x)). Qed.
Lemma lem1730008 (x : real) : (term2273 x) = (term2274 x).
Proof. exact (@lem1482981 (term2275 x) term76). Qed.
Lemma lem1730009 (x : real) : (term2242 x) = (term2274 x).
Proof. exact (TRANS (@lem1730007 x) (@lem1730008 x)). Qed.
Lemma lem1730010 (x : real) : (term2276 x) = (term2277 x).
Proof. exact (eq_refl (term2276 x)). Qed.
Lemma lem1730011 : term999 = term999.
Proof. exact (eq_refl term999). Qed.
Lemma lem1730012 (x : real) : (term2278 x) = (term2279 x).
Proof. exact (MK_COMB (@lem1730011) (@lem1730010 x)). Qed.
Lemma lem1730013 (x : real) : (term2280 x) = (term2281 x).
Proof. exact (eq_refl (term2280 x)). Qed.
Lemma lem1730014 : term1507 = term1507.
Proof. exact (eq_refl term1507). Qed.
Lemma lem1730015 (x : real) : (term2282 x) = (term2283 x).
Proof. exact (MK_COMB (@lem1730014) (@lem1730013 x)). Qed.
Lemma lem1730016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730017 (x : real) : (term2284 x) = (term2285 x).
Proof. exact (MK_COMB (@lem1730016) (@lem1730015 x)). Qed.
Lemma lem1730018 (x : real) : (term2274 x) = (term2286 x).
Proof. exact (MK_COMB (@lem1730017 x) (@lem1730012 x)). Qed.
Lemma lem1730019 (x : real) : (term2287 x) = (term2287 x).
Proof. exact (eq_refl (term2287 x)). Qed.
Lemma lem1730020 (x : real) : ((term2242 x) = (term2274 x)) = ((term2242 x) = (term2286 x)).
Proof. exact (MK_COMB (@lem1730019 x) (@lem1730018 x)). Qed.
Lemma lem1730021 (x : real) : (term2242 x) = (term2286 x).
Proof. exact (EQ_MP (@lem1730020 x) (@lem1730009 x)). Qed.
Lemma lem1730022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730023 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730022) (@lem1725350 x)). Qed.
Lemma lem1730024 (x : real) : (term1524 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1730023 x) (@lem1727067)). Qed.
Lemma lem1730025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730026 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730025) (@lem1724687 x)). Qed.
Lemma lem1730027 (x : real) : (term1564 x) = (term1565 x).
Proof. exact (MK_COMB (@lem1730026 x) (@lem1730024 x)). Qed.
Lemma lem1730028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730029 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730028) (@lem1724639 x)). Qed.
Lemma lem1730030 (x : real) : (term1566 x) = (term1567 x).
Proof. exact (MK_COMB (@lem1730029 x) (@lem1730027 x)). Qed.
Lemma lem1730031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730032 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730031) (@lem1724639 x)). Qed.
Lemma lem1730033 (x : real) : (term2288 x) = (term2289 x).
Proof. exact (MK_COMB (@lem1730032 x) (@lem1730030 x)). Qed.
Lemma lem1730034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730035 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730034) (@lem1724639 x)). Qed.
Lemma lem1730036 (x : real) : (term2281 x) = (term2290 x).
Proof. exact (MK_COMB (@lem1730035 x) (@lem1730033 x)). Qed.
Lemma lem1730037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730038 : term1507 = term1507.
Proof. exact (MK_COMB (@lem1730037) (@lem1727037)). Qed.
Lemma lem1730039 (x : real) : (term2283 x) = (term2291 x).
Proof. exact (MK_COMB (@lem1730038) (@lem1730036 x)). Qed.
Lemma lem1730040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730041 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730040) (@lem1725350 x)). Qed.
Lemma lem1730042 (x : real) : (term1542 x) = (term1525 x).
Proof. exact (MK_COMB (@lem1730041 x) (@lem1727123)). Qed.
Lemma lem1730043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730044 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730043) (@lem1724687 x)). Qed.
Lemma lem1730045 (x : real) : (term1572 x) = (term1565 x).
Proof. exact (MK_COMB (@lem1730044 x) (@lem1730042 x)). Qed.
Lemma lem1730046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730047 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730046) (@lem1724639 x)). Qed.
Lemma lem1730048 (x : real) : (term1573 x) = (term1567 x).
Proof. exact (MK_COMB (@lem1730047 x) (@lem1730045 x)). Qed.
Lemma lem1730049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730050 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730049) (@lem1724639 x)). Qed.
Lemma lem1730051 (x : real) : (term2292 x) = (term2289 x).
Proof. exact (MK_COMB (@lem1730050 x) (@lem1730048 x)). Qed.
Lemma lem1730052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730053 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730052) (@lem1724639 x)). Qed.
Lemma lem1730054 (x : real) : (term2277 x) = (term2290 x).
Proof. exact (MK_COMB (@lem1730053 x) (@lem1730051 x)). Qed.
Lemma lem1730055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730056 : term999 = term999.
Proof. exact (MK_COMB (@lem1730055) (@lem1725193)). Qed.
Lemma lem1730057 (x : real) : (term2279 x) = (term2293 x).
Proof. exact (MK_COMB (@lem1730056) (@lem1730054 x)). Qed.
Lemma lem1730058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730059 (x : real) : (term2285 x) = (term2294 x).
Proof. exact (MK_COMB (@lem1730058) (@lem1730039 x)). Qed.
Lemma lem1730060 (x : real) : (term2286 x) = (term2295 x).
Proof. exact (MK_COMB (@lem1730059 x) (@lem1730057 x)). Qed.
Lemma lem1730072 (x : real) : (term2242 x) = (term2295 x).
Proof. exact (TRANS (@lem1730021 x) (@lem1730060 x)). Qed.
Lemma lem1730073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730074 (x : real) : (term2244 x) = (term2296 x).
Proof. exact (MK_COMB (@lem1730073) (@lem1730072 x)). Qed.
Lemma lem1730075 (x : real) : (term2249 x) = (term2297 x).
Proof. exact (MK_COMB (@lem1730074 x) (@lem1730004 x)). Qed.
Lemma lem1730077 (x : real) : (term2232 x) = (term2297 x).
Proof. exact (TRANS (@lem1729936 x) (@lem1730075 x)). Qed.
Lemma lem1730079 (a : real) (x : real) (r : real) : (term985 x a r) = (term986 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1730080 : term342 = term1580.
Proof. exact (@lem1730079 term24 term76 term76). Qed.
Lemma lem1730087 : term1581 = term76.
Proof. exact (@lem1483458 term24). Qed.
Lemma lem1730090 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1730091 : term1582 = term881.
Proof. exact (MK_COMB (@lem1730090) (@lem1730087)). Qed.
Lemma lem1730092 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1730093 : term1582 = term24.
Proof. exact (TRANS (@lem1730091) (@lem1730092)). Qed.
Lemma lem1730094 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730095 : term1583 = term1116.
Proof. exact (MK_COMB (@lem1730094) (@lem1730093)). Qed.
Lemma lem1730096 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730097 : term1584 = term1117.
Proof. exact (MK_COMB (@lem1730095) (@lem1730096)). Qed.
Lemma lem1730104 : term184 = term76.
Proof. exact (@lem1483458 term73). Qed.
Lemma lem1730107 : term880 = term880.
Proof. exact (eq_refl term880). Qed.
Lemma lem1730108 : term879 = term881.
Proof. exact (MK_COMB (@lem1730107) (@lem1730104)). Qed.
Lemma lem1730109 : term881 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1730110 : term879 = term24.
Proof. exact (TRANS (@lem1730108) (@lem1730109)). Qed.
Lemma lem1730111 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730112 : term1585 = term1116.
Proof. exact (MK_COMB (@lem1730111) (@lem1730110)). Qed.
Lemma lem1730113 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730114 : term1586 = term1117.
Proof. exact (MK_COMB (@lem1730112) (@lem1730113)). Qed.
Lemma lem1730115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730116 : term1587 = term1135.
Proof. exact (MK_COMB (@lem1730115) (@lem1730114)). Qed.
Lemma lem1730117 : term1580 = term1588.
Proof. exact (MK_COMB (@lem1730116) (@lem1730097)). Qed.
Lemma lem1730118 : term342 = term1588.
Proof. exact (TRANS (@lem1730080) (@lem1730117)). Qed.
Lemma lem1730119 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1730120 (x : real) : (term524 x) = (term1589 x).
Proof. exact (MK_COMB (@lem1730119 x) (@lem1730118)). Qed.
Lemma lem1730121 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1730122 (x : real) : (term554 x) = (term1590 x).
Proof. exact (MK_COMB (@lem1730121 x) (@lem1730120 x)). Qed.
Lemma lem1730123 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730124 (x : real) : (term636 x) = (term1591 x).
Proof. exact (MK_COMB (@lem1730123 x) (@lem1730122 x)). Qed.
Lemma lem1730125 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1730126 (x : real) : (term2298 x) = (term2299 x).
Proof. exact (MK_COMB (@lem1730125 x) (@lem1730124 x)). Qed.
Lemma lem1730127 (x : real) : (term2300 x) = (term2299 x).
Proof. exact (eq_refl (term2300 x)). Qed.
Lemma lem1730128 (x : real) : (term2299 x) = (term2300 x).
Proof. exact (SYM (@lem1730127 x)). Qed.
Lemma lem1730129 (x : real) : (term2300 x) = (term2301 x).
Proof. exact (@lem1482981 (term2302 x) x). Qed.
Lemma lem1730130 (x : real) : (term2299 x) = (term2301 x).
Proof. exact (TRANS (@lem1730128 x) (@lem1730129 x)). Qed.
Lemma lem1730131 (x : real) : (term2303 x) = (term2304 x).
Proof. exact (eq_refl (term2303 x)). Qed.
Lemma lem1730132 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1730133 (x : real) : (term2305 x) = (term2306 x).
Proof. exact (MK_COMB (@lem1730132 x) (@lem1730131 x)). Qed.
Lemma lem1730134 (x : real) : (term2307 x) = (term2308 x).
Proof. exact (eq_refl (term2307 x)). Qed.
Lemma lem1730135 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730136 (x : real) : (term2309 x) = (term2310 x).
Proof. exact (MK_COMB (@lem1730135 x) (@lem1730134 x)). Qed.
Lemma lem1730137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730138 (x : real) : (term2311 x) = (term2312 x).
Proof. exact (MK_COMB (@lem1730137) (@lem1730136 x)). Qed.
Lemma lem1730139 (x : real) : (term2301 x) = (term2313 x).
Proof. exact (MK_COMB (@lem1730138 x) (@lem1730133 x)). Qed.
Lemma lem1730140 (x : real) : (term2314 x) = (term2314 x).
Proof. exact (eq_refl (term2314 x)). Qed.
Lemma lem1730141 (x : real) : ((term2299 x) = (term2301 x)) = ((term2299 x) = (term2313 x)).
Proof. exact (MK_COMB (@lem1730140 x) (@lem1730139 x)). Qed.
Lemma lem1730142 (x : real) : (term2299 x) = (term2313 x).
Proof. exact (EQ_MP (@lem1730141 x) (@lem1730130 x)). Qed.
Lemma lem1730143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730144 : term1135 = term1135.
Proof. exact (MK_COMB (@lem1730143) (@lem1727354)). Qed.
Lemma lem1730145 : term1588 = term1588.
Proof. exact (MK_COMB (@lem1730144) (@lem1727354)). Qed.
Lemma lem1730146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730147 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730146) (@lem1725350 x)). Qed.
Lemma lem1730148 (x : real) : (term1589 x) = (term1589 x).
Proof. exact (MK_COMB (@lem1730147 x) (@lem1730145)). Qed.
Lemma lem1730149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730150 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730149) (@lem1724687 x)). Qed.
Lemma lem1730151 (x : real) : (term1611 x) = (term1611 x).
Proof. exact (MK_COMB (@lem1730150 x) (@lem1730148 x)). Qed.
Lemma lem1730152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730153 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730152) (@lem1724639 x)). Qed.
Lemma lem1730154 (x : real) : (term1612 x) = (term1612 x).
Proof. exact (MK_COMB (@lem1730153 x) (@lem1730151 x)). Qed.
Lemma lem1730155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730156 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730155) (@lem1724639 x)). Qed.
Lemma lem1730157 (x : real) : (term2308 x) = (term2308 x).
Proof. exact (MK_COMB (@lem1730156 x) (@lem1730154 x)). Qed.
Lemma lem1730158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730159 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730158) (@lem1724639 x)). Qed.
Lemma lem1730160 (x : real) : (term2310 x) = (term2310 x).
Proof. exact (MK_COMB (@lem1730159 x) (@lem1730157 x)). Qed.
Lemma lem1730161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730162 : term1135 = term1135.
Proof. exact (MK_COMB (@lem1730161) (@lem1727354)). Qed.
Lemma lem1730163 : term1588 = term1588.
Proof. exact (MK_COMB (@lem1730162) (@lem1727354)). Qed.
Lemma lem1730164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730165 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730164) (@lem1725350 x)). Qed.
Lemma lem1730166 (x : real) : (term1589 x) = (term1589 x).
Proof. exact (MK_COMB (@lem1730165 x) (@lem1730163)). Qed.
Lemma lem1730167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730168 (x : real) : (term851 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730167) (@lem1724781 x)). Qed.
Lemma lem1730169 (x : real) : (term1613 x) = (term1614 x).
Proof. exact (MK_COMB (@lem1730168 x) (@lem1730166 x)). Qed.
Lemma lem1730170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730171 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730170) (@lem1724639 x)). Qed.
Lemma lem1730172 (x : real) : (term1615 x) = (term1616 x).
Proof. exact (MK_COMB (@lem1730171 x) (@lem1730169 x)). Qed.
Lemma lem1730173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730174 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730173) (@lem1728062 x)). Qed.
Lemma lem1730175 (x : real) : (term2304 x) = (term2315 x).
Proof. exact (MK_COMB (@lem1730174 x) (@lem1730172 x)). Qed.
Lemma lem1730176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730177 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730176) (@lem1724751 x)). Qed.
Lemma lem1730178 (x : real) : (term2306 x) = (term2316 x).
Proof. exact (MK_COMB (@lem1730177 x) (@lem1730175 x)). Qed.
Lemma lem1730179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730180 (x : real) : (term2312 x) = (term2312 x).
Proof. exact (MK_COMB (@lem1730179) (@lem1730160 x)). Qed.
Lemma lem1730181 (x : real) : (term2313 x) = (term2317 x).
Proof. exact (MK_COMB (@lem1730180 x) (@lem1730178 x)). Qed.
Lemma lem1730192 (x : real) : (term2299 x) = (term2317 x).
Proof. exact (TRANS (@lem1730142 x) (@lem1730181 x)). Qed.
Lemma lem1730193 (x : real) : (term2298 x) = (term2317 x).
Proof. exact (TRANS (@lem1730126 x) (@lem1730192 x)). Qed.
Lemma lem1730194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730195 (x : real) : (term2318 x) = (term2319 x).
Proof. exact (MK_COMB (@lem1730194) (@lem1730077 x)). Qed.
Lemma lem1730196 (x : real) : (term634 x) = (term2320 x).
Proof. exact (MK_COMB (@lem1730195 x) (@lem1730193 x)). Qed.
Lemma lem1730197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730198 (x : real) : (term642 x) = (term2321 x).
Proof. exact (MK_COMB (@lem1730197) (@lem1729885 x)). Qed.
Lemma lem1730199 (x : real) : (term643 x) = (term2322 x).
Proof. exact (MK_COMB (@lem1730198 x) (@lem1730196 x)). Qed.
Lemma lem1730201 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1730202 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1730201 x term76). Qed.
Lemma lem1730209 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1730210 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1730211 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1730210) (@lem1730209 x)). Qed.
Lemma lem1730212 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730213 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1730211 x) (@lem1730212)). Qed.
Lemma lem1730226 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1730227 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730226 x) (@lem1730213 x)). Qed.
Lemma lem1730228 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1730202 x) (@lem1730227 x)). Qed.
Lemma lem1730229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730230 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730229) (@lem1730228 x)). Qed.
Lemma lem1730231 (x : real) : (term510 x) = (term510 x).
Proof. exact (eq_refl (term510 x)). Qed.
Lemma lem1730232 (x : real) : (term544 x) = (term1920 x).
Proof. exact (MK_COMB (@lem1730230 x) (@lem1730231 x)). Qed.
Lemma lem1730233 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730234 (x : real) : (term626 x) = (term2323 x).
Proof. exact (MK_COMB (@lem1730233 x) (@lem1730232 x)). Qed.
Lemma lem1730235 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1730236 (x : real) : (term2324 x) = (term2325 x).
Proof. exact (MK_COMB (@lem1730235 x) (@lem1730234 x)). Qed.
Lemma lem1730237 (x : real) : (term2326 x) = (term2325 x).
Proof. exact (eq_refl (term2326 x)). Qed.
Lemma lem1730238 (x : real) : (term2325 x) = (term2326 x).
Proof. exact (SYM (@lem1730237 x)). Qed.
Lemma lem1730239 (x : real) : (term2326 x) = (term2327 x).
Proof. exact (@lem1482981 (term2328 x) x). Qed.
Lemma lem1730240 (x : real) : (term2325 x) = (term2327 x).
Proof. exact (TRANS (@lem1730238 x) (@lem1730239 x)). Qed.
Lemma lem1730241 (x : real) : (term2329 x) = (term2330 x).
Proof. exact (eq_refl (term2329 x)). Qed.
Lemma lem1730242 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1730243 (x : real) : (term2331 x) = (term2332 x).
Proof. exact (MK_COMB (@lem1730242 x) (@lem1730241 x)). Qed.
Lemma lem1730244 (x : real) : (term2333 x) = (term2334 x).
Proof. exact (eq_refl (term2333 x)). Qed.
Lemma lem1730245 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730246 (x : real) : (term2335 x) = (term2336 x).
Proof. exact (MK_COMB (@lem1730245 x) (@lem1730244 x)). Qed.
Lemma lem1730247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730248 (x : real) : (term2337 x) = (term2338 x).
Proof. exact (MK_COMB (@lem1730247) (@lem1730246 x)). Qed.
Lemma lem1730249 (x : real) : (term2327 x) = (term2339 x).
Proof. exact (MK_COMB (@lem1730248 x) (@lem1730243 x)). Qed.
Lemma lem1730250 (x : real) : (term2340 x) = (term2340 x).
Proof. exact (eq_refl (term2340 x)). Qed.
Lemma lem1730251 (x : real) : ((term2325 x) = (term2327 x)) = ((term2325 x) = (term2339 x)).
Proof. exact (MK_COMB (@lem1730250 x) (@lem1730249 x)). Qed.
Lemma lem1730252 (x : real) : (term2325 x) = (term2339 x).
Proof. exact (EQ_MP (@lem1730251 x) (@lem1730240 x)). Qed.
Lemma lem1730253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730254 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730253) (@lem1725350 x)). Qed.
Lemma lem1730255 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730254 x) (@lem1724639 x)). Qed.
Lemma lem1730256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730257 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730256) (@lem1724687 x)). Qed.
Lemma lem1730258 (x : real) : (term510 x) = (term510 x).
Proof. exact (MK_COMB (@lem1730257 x) (@lem1728755)). Qed.
Lemma lem1730259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730260 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730259) (@lem1730255 x)). Qed.
Lemma lem1730261 (x : real) : (term1920 x) = (term1920 x).
Proof. exact (MK_COMB (@lem1730260 x) (@lem1730258 x)). Qed.
Lemma lem1730262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730263 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730262) (@lem1724639 x)). Qed.
Lemma lem1730264 (x : real) : (term2323 x) = (term2323 x).
Proof. exact (MK_COMB (@lem1730263 x) (@lem1730261 x)). Qed.
Lemma lem1730265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730266 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730265) (@lem1724639 x)). Qed.
Lemma lem1730267 (x : real) : (term2334 x) = (term2334 x).
Proof. exact (MK_COMB (@lem1730266 x) (@lem1730264 x)). Qed.
Lemma lem1730268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730269 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730268) (@lem1724639 x)). Qed.
Lemma lem1730270 (x : real) : (term2336 x) = (term2336 x).
Proof. exact (MK_COMB (@lem1730269 x) (@lem1730267 x)). Qed.
Lemma lem1730271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730272 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730271) (@lem1725350 x)). Qed.
Lemma lem1730273 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730272 x) (@lem1724639 x)). Qed.
Lemma lem1730274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730275 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730274) (@lem1724687 x)). Qed.
Lemma lem1730276 (x : real) : (term510 x) = (term510 x).
Proof. exact (MK_COMB (@lem1730275 x) (@lem1728755)). Qed.
Lemma lem1730277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730278 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730277) (@lem1730273 x)). Qed.
Lemma lem1730279 (x : real) : (term1920 x) = (term1920 x).
Proof. exact (MK_COMB (@lem1730278 x) (@lem1730276 x)). Qed.
Lemma lem1730280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730281 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730280) (@lem1724639 x)). Qed.
Lemma lem1730282 (x : real) : (term2323 x) = (term2323 x).
Proof. exact (MK_COMB (@lem1730281 x) (@lem1730279 x)). Qed.
Lemma lem1730283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730284 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730283) (@lem1728062 x)). Qed.
Lemma lem1730285 (x : real) : (term2330 x) = (term2341 x).
Proof. exact (MK_COMB (@lem1730284 x) (@lem1730282 x)). Qed.
Lemma lem1730286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730287 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730286) (@lem1724751 x)). Qed.
Lemma lem1730288 (x : real) : (term2332 x) = (term2342 x).
Proof. exact (MK_COMB (@lem1730287 x) (@lem1730285 x)). Qed.
Lemma lem1730289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730290 (x : real) : (term2338 x) = (term2338 x).
Proof. exact (MK_COMB (@lem1730289) (@lem1730270 x)). Qed.
Lemma lem1730291 (x : real) : (term2339 x) = (term2343 x).
Proof. exact (MK_COMB (@lem1730290 x) (@lem1730288 x)). Qed.
Lemma lem1730292 (x : real) : (term2325 x) = (term2343 x).
Proof. exact (TRANS (@lem1730252 x) (@lem1730291 x)). Qed.
Lemma lem1730294 (x : real) : (term2344 x) = (term2342 x).
Proof. exact (eq_refl (term2344 x)). Qed.
Lemma lem1730295 (x : real) : (term2342 x) = (term2344 x).
Proof. exact (SYM (@lem1730294 x)). Qed.
Lemma lem1730296 (x : real) : (term2344 x) = (term2345 x).
Proof. exact (@lem1482981 (term2346 x) term24). Qed.
Lemma lem1730297 (x : real) : (term2342 x) = (term2345 x).
Proof. exact (TRANS (@lem1730295 x) (@lem1730296 x)). Qed.
Lemma lem1730298 (x : real) : (term2347 x) = (term2348 x).
Proof. exact (eq_refl (term2347 x)). Qed.
Lemma lem1730299 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1730300 (x : real) : (term2349 x) = (term2350 x).
Proof. exact (MK_COMB (@lem1730299) (@lem1730298 x)). Qed.
Lemma lem1730301 (x : real) : (term2351 x) = (term2352 x).
Proof. exact (eq_refl (term2351 x)). Qed.
Lemma lem1730302 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1730303 (x : real) : (term2353 x) = (term2354 x).
Proof. exact (MK_COMB (@lem1730302) (@lem1730301 x)). Qed.
Lemma lem1730304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730305 (x : real) : (term2355 x) = (term2356 x).
Proof. exact (MK_COMB (@lem1730304) (@lem1730303 x)). Qed.
Lemma lem1730306 (x : real) : (term2345 x) = (term2357 x).
Proof. exact (MK_COMB (@lem1730305 x) (@lem1730300 x)). Qed.
Lemma lem1730307 (x : real) : (term2358 x) = (term2358 x).
Proof. exact (eq_refl (term2358 x)). Qed.
Lemma lem1730308 (x : real) : ((term2342 x) = (term2345 x)) = ((term2342 x) = (term2357 x)).
Proof. exact (MK_COMB (@lem1730307 x) (@lem1730306 x)). Qed.
Lemma lem1730309 (x : real) : (term2342 x) = (term2357 x).
Proof. exact (EQ_MP (@lem1730308 x) (@lem1730297 x)). Qed.
Lemma lem1730310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730311 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730310) (@lem1725350 x)). Qed.
Lemma lem1730312 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730311 x) (@lem1724639 x)). Qed.
Lemma lem1730313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730314 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730313) (@lem1724687 x)). Qed.
Lemma lem1730315 (x : real) : (term1957 x) = (term1957 x).
Proof. exact (MK_COMB (@lem1730314 x) (@lem1727354)). Qed.
Lemma lem1730316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730317 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730316) (@lem1730312 x)). Qed.
Lemma lem1730318 (x : real) : (term1958 x) = (term1958 x).
Proof. exact (MK_COMB (@lem1730317 x) (@lem1730315 x)). Qed.
Lemma lem1730319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730320 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730319) (@lem1724639 x)). Qed.
Lemma lem1730321 (x : real) : (term2359 x) = (term2359 x).
Proof. exact (MK_COMB (@lem1730320 x) (@lem1730318 x)). Qed.
Lemma lem1730322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730323 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730322) (@lem1725350 x)). Qed.
Lemma lem1730324 (x : real) : (term2360 x) = (term2360 x).
Proof. exact (MK_COMB (@lem1730323 x) (@lem1730321 x)). Qed.
Lemma lem1730325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730326 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730325) (@lem1724666 x)). Qed.
Lemma lem1730327 (x : real) : (term2352 x) = (term2352 x).
Proof. exact (MK_COMB (@lem1730326 x) (@lem1730324 x)). Qed.
Lemma lem1730328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730329 : term869 = term869.
Proof. exact (MK_COMB (@lem1730328) (@lem1724838)). Qed.
Lemma lem1730330 (x : real) : (term2354 x) = (term2354 x).
Proof. exact (MK_COMB (@lem1730329) (@lem1730327 x)). Qed.
Lemma lem1730331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730332 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730331) (@lem1725350 x)). Qed.
Lemma lem1730333 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730332 x) (@lem1724639 x)). Qed.
Lemma lem1730334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730335 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730334) (@lem1724687 x)). Qed.
Lemma lem1730336 (x : real) : (term1963 x) = (term1963 x).
Proof. exact (MK_COMB (@lem1730335 x) (@lem1728854)). Qed.
Lemma lem1730337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730338 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730337) (@lem1730333 x)). Qed.
Lemma lem1730339 (x : real) : (term1964 x) = (term1964 x).
Proof. exact (MK_COMB (@lem1730338 x) (@lem1730336 x)). Qed.
Lemma lem1730340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730341 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730340) (@lem1724639 x)). Qed.
Lemma lem1730342 (x : real) : (term2361 x) = (term2361 x).
Proof. exact (MK_COMB (@lem1730341 x) (@lem1730339 x)). Qed.
Lemma lem1730343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730344 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730343) (@lem1725350 x)). Qed.
Lemma lem1730345 (x : real) : (term2362 x) = (term2362 x).
Proof. exact (MK_COMB (@lem1730344 x) (@lem1730342 x)). Qed.
Lemma lem1730346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730347 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730346) (@lem1724666 x)). Qed.
Lemma lem1730348 (x : real) : (term2348 x) = (term2348 x).
Proof. exact (MK_COMB (@lem1730347 x) (@lem1730345 x)). Qed.
Lemma lem1730349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730350 : term864 = term946.
Proof. exact (MK_COMB (@lem1730349) (@lem1724916)). Qed.
Lemma lem1730351 (x : real) : (term2350 x) = (term2363 x).
Proof. exact (MK_COMB (@lem1730350) (@lem1730348 x)). Qed.
Lemma lem1730352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730353 (x : real) : (term2356 x) = (term2356 x).
Proof. exact (MK_COMB (@lem1730352) (@lem1730330 x)). Qed.
Lemma lem1730354 (x : real) : (term2357 x) = (term2364 x).
Proof. exact (MK_COMB (@lem1730353 x) (@lem1730351 x)). Qed.
Lemma lem1730366 (x : real) : (term2342 x) = (term2364 x).
Proof. exact (TRANS (@lem1730309 x) (@lem1730354 x)). Qed.
Lemma lem1730368 (x : real) : (term2365 x) = (term2336 x).
Proof. exact (eq_refl (term2365 x)). Qed.
Lemma lem1730369 (x : real) : (term2336 x) = (term2365 x).
Proof. exact (SYM (@lem1730368 x)). Qed.
Lemma lem1730370 (x : real) : (term2365 x) = (term2366 x).
Proof. exact (@lem1482981 (term2367 x) term24). Qed.
Lemma lem1730371 (x : real) : (term2336 x) = (term2366 x).
Proof. exact (TRANS (@lem1730369 x) (@lem1730370 x)). Qed.
Lemma lem1730372 (x : real) : (term2368 x) = (term2369 x).
Proof. exact (eq_refl (term2368 x)). Qed.
Lemma lem1730373 : term864 = term864.
Proof. exact (eq_refl term864). Qed.
Lemma lem1730374 (x : real) : (term2370 x) = (term2371 x).
Proof. exact (MK_COMB (@lem1730373) (@lem1730372 x)). Qed.
Lemma lem1730375 (x : real) : (term2372 x) = (term2373 x).
Proof. exact (eq_refl (term2372 x)). Qed.
Lemma lem1730376 : term869 = term869.
Proof. exact (eq_refl term869). Qed.
Lemma lem1730377 (x : real) : (term2374 x) = (term2375 x).
Proof. exact (MK_COMB (@lem1730376) (@lem1730375 x)). Qed.
Lemma lem1730378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730379 (x : real) : (term2376 x) = (term2377 x).
Proof. exact (MK_COMB (@lem1730378) (@lem1730377 x)). Qed.
Lemma lem1730380 (x : real) : (term2366 x) = (term2378 x).
Proof. exact (MK_COMB (@lem1730379 x) (@lem1730374 x)). Qed.
Lemma lem1730381 (x : real) : (term2379 x) = (term2379 x).
Proof. exact (eq_refl (term2379 x)). Qed.
Lemma lem1730382 (x : real) : ((term2336 x) = (term2366 x)) = ((term2336 x) = (term2378 x)).
Proof. exact (MK_COMB (@lem1730381 x) (@lem1730380 x)). Qed.
Lemma lem1730383 (x : real) : (term2336 x) = (term2378 x).
Proof. exact (EQ_MP (@lem1730382 x) (@lem1730371 x)). Qed.
Lemma lem1730384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730385 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730384) (@lem1725350 x)). Qed.
Lemma lem1730386 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730385 x) (@lem1724639 x)). Qed.
Lemma lem1730387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730388 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730387) (@lem1724687 x)). Qed.
Lemma lem1730389 (x : real) : (term1957 x) = (term1957 x).
Proof. exact (MK_COMB (@lem1730388 x) (@lem1727354)). Qed.
Lemma lem1730390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730391 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730390) (@lem1730386 x)). Qed.
Lemma lem1730392 (x : real) : (term1958 x) = (term1958 x).
Proof. exact (MK_COMB (@lem1730391 x) (@lem1730389 x)). Qed.
Lemma lem1730393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730394 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730393) (@lem1724639 x)). Qed.
Lemma lem1730395 (x : real) : (term2359 x) = (term2359 x).
Proof. exact (MK_COMB (@lem1730394 x) (@lem1730392 x)). Qed.
Lemma lem1730396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730397 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730396) (@lem1724639 x)). Qed.
Lemma lem1730398 (x : real) : (term2380 x) = (term2380 x).
Proof. exact (MK_COMB (@lem1730397 x) (@lem1730395 x)). Qed.
Lemma lem1730399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730400 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730399) (@lem1724639 x)). Qed.
Lemma lem1730401 (x : real) : (term2373 x) = (term2373 x).
Proof. exact (MK_COMB (@lem1730400 x) (@lem1730398 x)). Qed.
Lemma lem1730402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730403 : term869 = term869.
Proof. exact (MK_COMB (@lem1730402) (@lem1724838)). Qed.
Lemma lem1730404 (x : real) : (term2375 x) = (term2375 x).
Proof. exact (MK_COMB (@lem1730403) (@lem1730401 x)). Qed.
Lemma lem1730405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730406 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730405) (@lem1725350 x)). Qed.
Lemma lem1730407 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730406 x) (@lem1724639 x)). Qed.
Lemma lem1730408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730409 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730408) (@lem1724687 x)). Qed.
Lemma lem1730410 (x : real) : (term1963 x) = (term1963 x).
Proof. exact (MK_COMB (@lem1730409 x) (@lem1728854)). Qed.
Lemma lem1730411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730412 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730411) (@lem1730407 x)). Qed.
Lemma lem1730413 (x : real) : (term1964 x) = (term1964 x).
Proof. exact (MK_COMB (@lem1730412 x) (@lem1730410 x)). Qed.
Lemma lem1730414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730415 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730414) (@lem1724639 x)). Qed.
Lemma lem1730416 (x : real) : (term2361 x) = (term2361 x).
Proof. exact (MK_COMB (@lem1730415 x) (@lem1730413 x)). Qed.
Lemma lem1730417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730418 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730417) (@lem1724639 x)). Qed.
Lemma lem1730419 (x : real) : (term2381 x) = (term2381 x).
Proof. exact (MK_COMB (@lem1730418 x) (@lem1730416 x)). Qed.
Lemma lem1730420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730421 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730420) (@lem1724639 x)). Qed.
Lemma lem1730422 (x : real) : (term2369 x) = (term2369 x).
Proof. exact (MK_COMB (@lem1730421 x) (@lem1730419 x)). Qed.
Lemma lem1730423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730424 : term864 = term946.
Proof. exact (MK_COMB (@lem1730423) (@lem1724916)). Qed.
Lemma lem1730425 (x : real) : (term2371 x) = (term2382 x).
Proof. exact (MK_COMB (@lem1730424) (@lem1730422 x)). Qed.
Lemma lem1730426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730427 (x : real) : (term2377 x) = (term2377 x).
Proof. exact (MK_COMB (@lem1730426) (@lem1730404 x)). Qed.
Lemma lem1730428 (x : real) : (term2378 x) = (term2383 x).
Proof. exact (MK_COMB (@lem1730427 x) (@lem1730425 x)). Qed.
Lemma lem1730440 (x : real) : (term2336 x) = (term2383 x).
Proof. exact (TRANS (@lem1730383 x) (@lem1730428 x)). Qed.
Lemma lem1730441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730442 (x : real) : (term2338 x) = (term2384 x).
Proof. exact (MK_COMB (@lem1730441) (@lem1730440 x)). Qed.
Lemma lem1730443 (x : real) : (term2343 x) = (term2385 x).
Proof. exact (MK_COMB (@lem1730442 x) (@lem1730366 x)). Qed.
Lemma lem1730444 (x : real) : (term2325 x) = (term2385 x).
Proof. exact (TRANS (@lem1730292 x) (@lem1730443 x)). Qed.
Lemma lem1730445 (x : real) : (term2324 x) = (term2385 x).
Proof. exact (TRANS (@lem1730236 x) (@lem1730444 x)). Qed.
Lemma lem1730447 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1730448 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1730447 x term76). Qed.
Lemma lem1730455 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1730456 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1730457 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1730456) (@lem1730455 x)). Qed.
Lemma lem1730458 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730459 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1730457 x) (@lem1730458)). Qed.
Lemma lem1730472 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1730473 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730472 x) (@lem1730459 x)). Qed.
Lemma lem1730474 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1730448 x) (@lem1730473 x)). Qed.
Lemma lem1730475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730476 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730475) (@lem1730474 x)). Qed.
Lemma lem1730478 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1730479 : term403 = term1990.
Proof. exact (@lem1730478 term24 term76). Qed.
Lemma lem1730486 : term988 = term24.
Proof. exact (@lem1483460 term24). Qed.
Lemma lem1730487 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730488 : term1991 = term1116.
Proof. exact (MK_COMB (@lem1730487) (@lem1730486)). Qed.
Lemma lem1730489 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730490 : term1992 = term1117.
Proof. exact (MK_COMB (@lem1730488) (@lem1730489)). Qed.
Lemma lem1730497 : term202 = term73.
Proof. exact (@lem1483462 term73). Qed.
Lemma lem1730498 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730499 : term1993 = term914.
Proof. exact (MK_COMB (@lem1730498) (@lem1730497)). Qed.
Lemma lem1730500 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730501 : term1994 = term915.
Proof. exact (MK_COMB (@lem1730499) (@lem1730500)). Qed.
Lemma lem1730502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730503 : term1995 = term946.
Proof. exact (MK_COMB (@lem1730502) (@lem1730501)). Qed.
Lemma lem1730504 : term1990 = term1996.
Proof. exact (MK_COMB (@lem1730503) (@lem1730490)). Qed.
Lemma lem1730505 : term403 = term1996.
Proof. exact (TRANS (@lem1730479) (@lem1730504)). Qed.
Lemma lem1730506 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1730507 (x : real) : (term511 x) = (term1997 x).
Proof. exact (MK_COMB (@lem1730506 x) (@lem1730505)). Qed.
Lemma lem1730508 (x : real) : (term545 x) = (term1998 x).
Proof. exact (MK_COMB (@lem1730476 x) (@lem1730507 x)). Qed.
Lemma lem1730509 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730510 (x : real) : (term627 x) = (term2386 x).
Proof. exact (MK_COMB (@lem1730509 x) (@lem1730508 x)). Qed.
Lemma lem1730511 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1730512 (x : real) : (term2387 x) = (term2388 x).
Proof. exact (MK_COMB (@lem1730511 x) (@lem1730510 x)). Qed.
Lemma lem1730513 (x : real) : (term2389 x) = (term2388 x).
Proof. exact (eq_refl (term2389 x)). Qed.
Lemma lem1730514 (x : real) : (term2388 x) = (term2389 x).
Proof. exact (SYM (@lem1730513 x)). Qed.
Lemma lem1730515 (x : real) : (term2389 x) = (term2390 x).
Proof. exact (@lem1482981 (term2391 x) x). Qed.
Lemma lem1730516 (x : real) : (term2388 x) = (term2390 x).
Proof. exact (TRANS (@lem1730514 x) (@lem1730515 x)). Qed.
Lemma lem1730517 (x : real) : (term2392 x) = (term2393 x).
Proof. exact (eq_refl (term2392 x)). Qed.
Lemma lem1730518 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1730519 (x : real) : (term2394 x) = (term2395 x).
Proof. exact (MK_COMB (@lem1730518 x) (@lem1730517 x)). Qed.
Lemma lem1730520 (x : real) : (term2396 x) = (term2397 x).
Proof. exact (eq_refl (term2396 x)). Qed.
Lemma lem1730521 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730522 (x : real) : (term2398 x) = (term2399 x).
Proof. exact (MK_COMB (@lem1730521 x) (@lem1730520 x)). Qed.
Lemma lem1730523 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730524 (x : real) : (term2400 x) = (term2401 x).
Proof. exact (MK_COMB (@lem1730523) (@lem1730522 x)). Qed.
Lemma lem1730525 (x : real) : (term2390 x) = (term2402 x).
Proof. exact (MK_COMB (@lem1730524 x) (@lem1730519 x)). Qed.
Lemma lem1730526 (x : real) : (term2403 x) = (term2403 x).
Proof. exact (eq_refl (term2403 x)). Qed.
Lemma lem1730527 (x : real) : ((term2388 x) = (term2390 x)) = ((term2388 x) = (term2402 x)).
Proof. exact (MK_COMB (@lem1730526 x) (@lem1730525 x)). Qed.
Lemma lem1730528 (x : real) : (term2388 x) = (term2402 x).
Proof. exact (EQ_MP (@lem1730527 x) (@lem1730516 x)). Qed.
Lemma lem1730529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730530 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730529) (@lem1725350 x)). Qed.
Lemma lem1730531 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730530 x) (@lem1724639 x)). Qed.
Lemma lem1730532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730533 : term946 = term946.
Proof. exact (MK_COMB (@lem1730532) (@lem1728854)). Qed.
Lemma lem1730534 : term1996 = term1996.
Proof. exact (MK_COMB (@lem1730533) (@lem1727354)). Qed.
Lemma lem1730535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730536 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730535) (@lem1724687 x)). Qed.
Lemma lem1730537 (x : real) : (term1997 x) = (term1997 x).
Proof. exact (MK_COMB (@lem1730536 x) (@lem1730534)). Qed.
Lemma lem1730538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730539 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730538) (@lem1730531 x)). Qed.
Lemma lem1730540 (x : real) : (term1998 x) = (term1998 x).
Proof. exact (MK_COMB (@lem1730539 x) (@lem1730537 x)). Qed.
Lemma lem1730541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730542 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730541) (@lem1724639 x)). Qed.
Lemma lem1730543 (x : real) : (term2386 x) = (term2386 x).
Proof. exact (MK_COMB (@lem1730542 x) (@lem1730540 x)). Qed.
Lemma lem1730544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730545 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730544) (@lem1724639 x)). Qed.
Lemma lem1730546 (x : real) : (term2397 x) = (term2397 x).
Proof. exact (MK_COMB (@lem1730545 x) (@lem1730543 x)). Qed.
Lemma lem1730547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730548 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730547) (@lem1724639 x)). Qed.
Lemma lem1730549 (x : real) : (term2399 x) = (term2399 x).
Proof. exact (MK_COMB (@lem1730548 x) (@lem1730546 x)). Qed.
Lemma lem1730550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730551 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730550) (@lem1725350 x)). Qed.
Lemma lem1730552 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730551 x) (@lem1724639 x)). Qed.
Lemma lem1730553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730554 : term946 = term946.
Proof. exact (MK_COMB (@lem1730553) (@lem1728854)). Qed.
Lemma lem1730555 : term1996 = term1996.
Proof. exact (MK_COMB (@lem1730554) (@lem1727354)). Qed.
Lemma lem1730556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730557 (x : real) : (term230 x) = (term230 x).
Proof. exact (MK_COMB (@lem1730556) (@lem1724687 x)). Qed.
Lemma lem1730558 (x : real) : (term1997 x) = (term1997 x).
Proof. exact (MK_COMB (@lem1730557 x) (@lem1730555)). Qed.
Lemma lem1730559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730560 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730559) (@lem1730552 x)). Qed.
Lemma lem1730561 (x : real) : (term1998 x) = (term1998 x).
Proof. exact (MK_COMB (@lem1730560 x) (@lem1730558 x)). Qed.
Lemma lem1730562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730563 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730562) (@lem1724639 x)). Qed.
Lemma lem1730564 (x : real) : (term2386 x) = (term2386 x).
Proof. exact (MK_COMB (@lem1730563 x) (@lem1730561 x)). Qed.
Lemma lem1730565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730566 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730565) (@lem1728062 x)). Qed.
Lemma lem1730567 (x : real) : (term2393 x) = (term2404 x).
Proof. exact (MK_COMB (@lem1730566 x) (@lem1730564 x)). Qed.
Lemma lem1730568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730569 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730568) (@lem1724751 x)). Qed.
Lemma lem1730570 (x : real) : (term2395 x) = (term2405 x).
Proof. exact (MK_COMB (@lem1730569 x) (@lem1730567 x)). Qed.
Lemma lem1730571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730572 (x : real) : (term2401 x) = (term2401 x).
Proof. exact (MK_COMB (@lem1730571) (@lem1730549 x)). Qed.
Lemma lem1730573 (x : real) : (term2402 x) = (term2406 x).
Proof. exact (MK_COMB (@lem1730572 x) (@lem1730570 x)). Qed.
Lemma lem1730584 (x : real) : (term2388 x) = (term2406 x).
Proof. exact (TRANS (@lem1730528 x) (@lem1730573 x)). Qed.
Lemma lem1730585 (x : real) : (term2387 x) = (term2406 x).
Proof. exact (TRANS (@lem1730512 x) (@lem1730584 x)). Qed.
Lemma lem1730586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730587 (x : real) : (term2407 x) = (term2408 x).
Proof. exact (MK_COMB (@lem1730586) (@lem1730445 x)). Qed.
Lemma lem1730588 (x : real) : (term625 x) = (term2409 x).
Proof. exact (MK_COMB (@lem1730587 x) (@lem1730585 x)). Qed.
Lemma lem1730590 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1730591 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1730590 x term76). Qed.
Lemma lem1730598 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1730599 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1730600 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1730599) (@lem1730598 x)). Qed.
Lemma lem1730601 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730602 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1730600 x) (@lem1730601)). Qed.
Lemma lem1730615 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1730616 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730615 x) (@lem1730602 x)). Qed.
Lemma lem1730617 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1730591 x) (@lem1730616 x)). Qed.
Lemma lem1730618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730619 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730618) (@lem1730617 x)). Qed.
Lemma lem1730620 (x : real) : (term506 x) = (term506 x).
Proof. exact (eq_refl (term506 x)). Qed.
Lemma lem1730621 (x : real) : (term540 x) = (term2410 x).
Proof. exact (MK_COMB (@lem1730619 x) (@lem1730620 x)). Qed.
Lemma lem1730622 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730623 (x : real) : (term622 x) = (term2411 x).
Proof. exact (MK_COMB (@lem1730622 x) (@lem1730621 x)). Qed.
Lemma lem1730624 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1730625 (x : real) : (term2412 x) = (term2413 x).
Proof. exact (MK_COMB (@lem1730624 x) (@lem1730623 x)). Qed.
Lemma lem1730626 (x : real) : (term2414 x) = (term2413 x).
Proof. exact (eq_refl (term2414 x)). Qed.
Lemma lem1730627 (x : real) : (term2413 x) = (term2414 x).
Proof. exact (SYM (@lem1730626 x)). Qed.
Lemma lem1730628 (x : real) : (term2414 x) = (term2415 x).
Proof. exact (@lem1482981 (term2416 x) x). Qed.
Lemma lem1730629 (x : real) : (term2413 x) = (term2415 x).
Proof. exact (TRANS (@lem1730627 x) (@lem1730628 x)). Qed.
Lemma lem1730630 (x : real) : (term2417 x) = (term2418 x).
Proof. exact (eq_refl (term2417 x)). Qed.
Lemma lem1730631 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1730632 (x : real) : (term2419 x) = (term2420 x).
Proof. exact (MK_COMB (@lem1730631 x) (@lem1730630 x)). Qed.
Lemma lem1730633 (x : real) : (term2421 x) = (term2422 x).
Proof. exact (eq_refl (term2421 x)). Qed.
Lemma lem1730634 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730635 (x : real) : (term2423 x) = (term2424 x).
Proof. exact (MK_COMB (@lem1730634 x) (@lem1730633 x)). Qed.
Lemma lem1730636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730637 (x : real) : (term2425 x) = (term2426 x).
Proof. exact (MK_COMB (@lem1730636) (@lem1730635 x)). Qed.
Lemma lem1730638 (x : real) : (term2415 x) = (term2427 x).
Proof. exact (MK_COMB (@lem1730637 x) (@lem1730632 x)). Qed.
Lemma lem1730639 (x : real) : (term2428 x) = (term2428 x).
Proof. exact (eq_refl (term2428 x)). Qed.
Lemma lem1730640 (x : real) : ((term2413 x) = (term2415 x)) = ((term2413 x) = (term2427 x)).
Proof. exact (MK_COMB (@lem1730639 x) (@lem1730638 x)). Qed.
Lemma lem1730641 (x : real) : (term2413 x) = (term2427 x).
Proof. exact (EQ_MP (@lem1730640 x) (@lem1730629 x)). Qed.
Lemma lem1730642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730643 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730642) (@lem1725350 x)). Qed.
Lemma lem1730644 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730643 x) (@lem1724639 x)). Qed.
Lemma lem1730645 : term452 = term451.
Proof. exact (@lem1483525 term78 term76). Qed.
Lemma lem1730651 : term438 = term439.
Proof. exact (@lem1483519 term78 term76). Qed.
Lemma lem1730653 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1730654 : term184 = term76.
Proof. exact (@lem1730653 term185). Qed.
Lemma lem1730655 : term330 = term330.
Proof. exact (eq_refl term330). Qed.
Lemma lem1730656 : term439 = term440.
Proof. exact (MK_COMB (@lem1730655) (@lem1730654)). Qed.
Lemma lem1730657 : term440 = term78.
Proof. exact (@lem1483450 term78). Qed.
Lemma lem1730658 : term439 = term78.
Proof. exact (TRANS (@lem1730656) (@lem1730657)). Qed.
Lemma lem1730660 : term438 = term78.
Proof. exact (TRANS (@lem1730651) (@lem1730658)). Qed.
Lemma lem1730661 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730662 : term449 = term450.
Proof. exact (MK_COMB (@lem1730661) (@lem1730660)). Qed.
Lemma lem1730663 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730664 : term451 = term452.
Proof. exact (MK_COMB (@lem1730662) (@lem1730663)). Qed.
Lemma lem1730665 : term452 = term452.
Proof. exact (TRANS (@lem1730645) (@lem1730664)). Qed.
Lemma lem1730666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730667 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730666) (@lem1725350 x)). Qed.
Lemma lem1730668 (x : real) : (term506 x) = (term506 x).
Proof. exact (MK_COMB (@lem1730667 x) (@lem1730665)). Qed.
Lemma lem1730669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730670 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730669) (@lem1730644 x)). Qed.
Lemma lem1730671 (x : real) : (term2410 x) = (term2410 x).
Proof. exact (MK_COMB (@lem1730670 x) (@lem1730668 x)). Qed.
Lemma lem1730672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730673 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730672) (@lem1724639 x)). Qed.
Lemma lem1730674 (x : real) : (term2411 x) = (term2411 x).
Proof. exact (MK_COMB (@lem1730673 x) (@lem1730671 x)). Qed.
Lemma lem1730675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730676 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730675) (@lem1724639 x)). Qed.
Lemma lem1730677 (x : real) : (term2422 x) = (term2422 x).
Proof. exact (MK_COMB (@lem1730676 x) (@lem1730674 x)). Qed.
Lemma lem1730678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730679 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730678) (@lem1724639 x)). Qed.
Lemma lem1730680 (x : real) : (term2424 x) = (term2424 x).
Proof. exact (MK_COMB (@lem1730679 x) (@lem1730677 x)). Qed.
Lemma lem1730681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730682 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730681) (@lem1725350 x)). Qed.
Lemma lem1730683 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730682 x) (@lem1724639 x)). Qed.
Lemma lem1730684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730685 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730684) (@lem1725350 x)). Qed.
Lemma lem1730686 (x : real) : (term506 x) = (term506 x).
Proof. exact (MK_COMB (@lem1730685 x) (@lem1730665)). Qed.
Lemma lem1730687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730688 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730687) (@lem1730683 x)). Qed.
Lemma lem1730689 (x : real) : (term2410 x) = (term2410 x).
Proof. exact (MK_COMB (@lem1730688 x) (@lem1730686 x)). Qed.
Lemma lem1730690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730691 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730690) (@lem1724639 x)). Qed.
Lemma lem1730692 (x : real) : (term2411 x) = (term2411 x).
Proof. exact (MK_COMB (@lem1730691 x) (@lem1730689 x)). Qed.
Lemma lem1730693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730694 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730693) (@lem1728062 x)). Qed.
Lemma lem1730695 (x : real) : (term2418 x) = (term2429 x).
Proof. exact (MK_COMB (@lem1730694 x) (@lem1730692 x)). Qed.
Lemma lem1730696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730697 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730696) (@lem1724751 x)). Qed.
Lemma lem1730698 (x : real) : (term2420 x) = (term2430 x).
Proof. exact (MK_COMB (@lem1730697 x) (@lem1730695 x)). Qed.
Lemma lem1730699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730700 (x : real) : (term2426 x) = (term2426 x).
Proof. exact (MK_COMB (@lem1730699) (@lem1730680 x)). Qed.
Lemma lem1730701 (x : real) : (term2427 x) = (term2431 x).
Proof. exact (MK_COMB (@lem1730700 x) (@lem1730698 x)). Qed.
Lemma lem1730702 (x : real) : (term2413 x) = (term2431 x).
Proof. exact (TRANS (@lem1730641 x) (@lem1730701 x)). Qed.
Lemma lem1730704 (x : real) : (term2432 x) = (term2430 x).
Proof. exact (eq_refl (term2432 x)). Qed.
Lemma lem1730705 (x : real) : (term2430 x) = (term2432 x).
Proof. exact (SYM (@lem1730704 x)). Qed.
Lemma lem1730706 (x : real) : (term2432 x) = (term2433 x).
Proof. exact (@lem1482981 (term2434 x) term76). Qed.
Lemma lem1730707 (x : real) : (term2430 x) = (term2433 x).
Proof. exact (TRANS (@lem1730705 x) (@lem1730706 x)). Qed.
Lemma lem1730708 (x : real) : (term2435 x) = (term2436 x).
Proof. exact (eq_refl (term2435 x)). Qed.
Lemma lem1730709 : term999 = term999.
Proof. exact (eq_refl term999). Qed.
Lemma lem1730710 (x : real) : (term2437 x) = (term2438 x).
Proof. exact (MK_COMB (@lem1730709) (@lem1730708 x)). Qed.
Lemma lem1730711 (x : real) : (term2439 x) = (term2440 x).
Proof. exact (eq_refl (term2439 x)). Qed.
Lemma lem1730712 : term1507 = term1507.
Proof. exact (eq_refl term1507). Qed.
Lemma lem1730713 (x : real) : (term2441 x) = (term2442 x).
Proof. exact (MK_COMB (@lem1730712) (@lem1730711 x)). Qed.
Lemma lem1730714 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730715 (x : real) : (term2443 x) = (term2444 x).
Proof. exact (MK_COMB (@lem1730714) (@lem1730713 x)). Qed.
Lemma lem1730716 (x : real) : (term2433 x) = (term2445 x).
Proof. exact (MK_COMB (@lem1730715 x) (@lem1730710 x)). Qed.
Lemma lem1730717 (x : real) : (term2446 x) = (term2446 x).
Proof. exact (eq_refl (term2446 x)). Qed.
Lemma lem1730718 (x : real) : ((term2430 x) = (term2433 x)) = ((term2430 x) = (term2445 x)).
Proof. exact (MK_COMB (@lem1730717 x) (@lem1730716 x)). Qed.
Lemma lem1730719 (x : real) : (term2430 x) = (term2445 x).
Proof. exact (EQ_MP (@lem1730718 x) (@lem1730707 x)). Qed.
Lemma lem1730720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730721 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730720) (@lem1725350 x)). Qed.
Lemma lem1730722 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730721 x) (@lem1724639 x)). Qed.
Lemma lem1730723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730724 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730723) (@lem1725350 x)). Qed.
Lemma lem1730725 (x : real) : (term1127 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1730724 x) (@lem1725193)). Qed.
Lemma lem1730726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730727 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730726) (@lem1730722 x)). Qed.
Lemma lem1730728 (x : real) : (term1314 x) = (term1314 x).
Proof. exact (MK_COMB (@lem1730727 x) (@lem1730725 x)). Qed.
Lemma lem1730729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730730 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730729) (@lem1724639 x)). Qed.
Lemma lem1730731 (x : real) : (term2447 x) = (term2447 x).
Proof. exact (MK_COMB (@lem1730730 x) (@lem1730728 x)). Qed.
Lemma lem1730732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730733 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730732) (@lem1725350 x)). Qed.
Lemma lem1730734 (x : real) : (term2448 x) = (term2448 x).
Proof. exact (MK_COMB (@lem1730733 x) (@lem1730731 x)). Qed.
Lemma lem1730735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730736 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730735) (@lem1724666 x)). Qed.
Lemma lem1730737 (x : real) : (term2440 x) = (term2440 x).
Proof. exact (MK_COMB (@lem1730736 x) (@lem1730734 x)). Qed.
Lemma lem1730738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730739 : term1507 = term1507.
Proof. exact (MK_COMB (@lem1730738) (@lem1727037)). Qed.
Lemma lem1730740 (x : real) : (term2442 x) = (term2442 x).
Proof. exact (MK_COMB (@lem1730739) (@lem1730737 x)). Qed.
Lemma lem1730741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730742 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730741) (@lem1725350 x)). Qed.
Lemma lem1730743 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730742 x) (@lem1724639 x)). Qed.
Lemma lem1730744 : term2449 = term2450.
Proof. exact (@lem1483525 term1537 term76). Qed.
Lemma lem1730745 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730749 : term1537 = term184.
Proof. exact (@lem1483512 term76). Qed.
Lemma lem1730751 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1730752 : term184 = term76.
Proof. exact (@lem1730751 term185). Qed.
Lemma lem1730754 : term1537 = term76.
Proof. exact (TRANS (@lem1730749) (@lem1730752)). Qed.
Lemma lem1730755 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1730756 : term2451 = term889.
Proof. exact (MK_COMB (@lem1730755) (@lem1730754)). Qed.
Lemma lem1730757 : term2452 = term891.
Proof. exact (MK_COMB (@lem1730756) (@lem1730745)). Qed.
Lemma lem1730758 : term891 = term892.
Proof. exact (@lem1483519 term76 term76). Qed.
Lemma lem1730760 (x : nat) : (term183 x) = term76.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1730761 : term184 = term76.
Proof. exact (@lem1730760 term185). Qed.
Lemma lem1730762 : term893 = term893.
Proof. exact (eq_refl term893). Qed.
Lemma lem1730763 : term892 = term894.
Proof. exact (MK_COMB (@lem1730762) (@lem1730761)). Qed.
Lemma lem1730764 : term894 = term76.
Proof. exact (@lem1483448 term76). Qed.
Lemma lem1730765 : term892 = term76.
Proof. exact (TRANS (@lem1730763) (@lem1730764)). Qed.
Lemma lem1730766 : term891 = term76.
Proof. exact (TRANS (@lem1730758) (@lem1730765)). Qed.
Lemma lem1730767 : term2452 = term76.
Proof. exact (TRANS (@lem1730757) (@lem1730766)). Qed.
Lemma lem1730768 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730769 : term2453 = term896.
Proof. exact (MK_COMB (@lem1730768) (@lem1730767)). Qed.
Lemma lem1730770 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730771 : term2450 = term897.
Proof. exact (MK_COMB (@lem1730769) (@lem1730770)). Qed.
Lemma lem1730772 : term2449 = term897.
Proof. exact (TRANS (@lem1730744) (@lem1730771)). Qed.
Lemma lem1730773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730774 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730773) (@lem1725350 x)). Qed.
Lemma lem1730775 (x : real) : (term2454 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1730774 x) (@lem1730772)). Qed.
Lemma lem1730776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730777 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730776) (@lem1730743 x)). Qed.
Lemma lem1730778 (x : real) : (term2455 x) = (term1314 x).
Proof. exact (MK_COMB (@lem1730777 x) (@lem1730775 x)). Qed.
Lemma lem1730779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730780 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730779) (@lem1724639 x)). Qed.
Lemma lem1730781 (x : real) : (term2456 x) = (term2447 x).
Proof. exact (MK_COMB (@lem1730780 x) (@lem1730778 x)). Qed.
Lemma lem1730782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730783 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730782) (@lem1725350 x)). Qed.
Lemma lem1730784 (x : real) : (term2457 x) = (term2448 x).
Proof. exact (MK_COMB (@lem1730783 x) (@lem1730781 x)). Qed.
Lemma lem1730785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730786 (x : real) : (term321 x) = (term321 x).
Proof. exact (MK_COMB (@lem1730785) (@lem1724666 x)). Qed.
Lemma lem1730787 (x : real) : (term2436 x) = (term2440 x).
Proof. exact (MK_COMB (@lem1730786 x) (@lem1730784 x)). Qed.
Lemma lem1730788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730789 : term999 = term999.
Proof. exact (MK_COMB (@lem1730788) (@lem1725193)). Qed.
Lemma lem1730790 (x : real) : (term2438 x) = (term2458 x).
Proof. exact (MK_COMB (@lem1730789) (@lem1730787 x)). Qed.
Lemma lem1730791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730792 (x : real) : (term2444 x) = (term2444 x).
Proof. exact (MK_COMB (@lem1730791) (@lem1730740 x)). Qed.
Lemma lem1730793 (x : real) : (term2445 x) = (term2459 x).
Proof. exact (MK_COMB (@lem1730792 x) (@lem1730790 x)). Qed.
Lemma lem1730805 (x : real) : (term2430 x) = (term2459 x).
Proof. exact (TRANS (@lem1730719 x) (@lem1730793 x)). Qed.
Lemma lem1730807 (x : real) : (term2460 x) = (term2424 x).
Proof. exact (eq_refl (term2460 x)). Qed.
Lemma lem1730808 (x : real) : (term2424 x) = (term2460 x).
Proof. exact (SYM (@lem1730807 x)). Qed.
Lemma lem1730809 (x : real) : (term2460 x) = (term2461 x).
Proof. exact (@lem1482981 (term2462 x) term76). Qed.
Lemma lem1730810 (x : real) : (term2424 x) = (term2461 x).
Proof. exact (TRANS (@lem1730808 x) (@lem1730809 x)). Qed.
Lemma lem1730811 (x : real) : (term2463 x) = (term2464 x).
Proof. exact (eq_refl (term2463 x)). Qed.
Lemma lem1730812 : term999 = term999.
Proof. exact (eq_refl term999). Qed.
Lemma lem1730813 (x : real) : (term2465 x) = (term2466 x).
Proof. exact (MK_COMB (@lem1730812) (@lem1730811 x)). Qed.
Lemma lem1730814 (x : real) : (term2467 x) = (term2468 x).
Proof. exact (eq_refl (term2467 x)). Qed.
Lemma lem1730815 : term1507 = term1507.
Proof. exact (eq_refl term1507). Qed.
Lemma lem1730816 (x : real) : (term2469 x) = (term2470 x).
Proof. exact (MK_COMB (@lem1730815) (@lem1730814 x)). Qed.
Lemma lem1730817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730818 (x : real) : (term2471 x) = (term2472 x).
Proof. exact (MK_COMB (@lem1730817) (@lem1730816 x)). Qed.
Lemma lem1730819 (x : real) : (term2461 x) = (term2473 x).
Proof. exact (MK_COMB (@lem1730818 x) (@lem1730813 x)). Qed.
Lemma lem1730820 (x : real) : (term2474 x) = (term2474 x).
Proof. exact (eq_refl (term2474 x)). Qed.
Lemma lem1730821 (x : real) : ((term2424 x) = (term2461 x)) = ((term2424 x) = (term2473 x)).
Proof. exact (MK_COMB (@lem1730820 x) (@lem1730819 x)). Qed.
Lemma lem1730822 (x : real) : (term2424 x) = (term2473 x).
Proof. exact (EQ_MP (@lem1730821 x) (@lem1730810 x)). Qed.
Lemma lem1730823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730824 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730823) (@lem1725350 x)). Qed.
Lemma lem1730825 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730824 x) (@lem1724639 x)). Qed.
Lemma lem1730826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730827 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730826) (@lem1725350 x)). Qed.
Lemma lem1730828 (x : real) : (term1127 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1730827 x) (@lem1725193)). Qed.
Lemma lem1730829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730830 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730829) (@lem1730825 x)). Qed.
Lemma lem1730831 (x : real) : (term1314 x) = (term1314 x).
Proof. exact (MK_COMB (@lem1730830 x) (@lem1730828 x)). Qed.
Lemma lem1730832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730833 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730832) (@lem1724639 x)). Qed.
Lemma lem1730834 (x : real) : (term2447 x) = (term2447 x).
Proof. exact (MK_COMB (@lem1730833 x) (@lem1730831 x)). Qed.
Lemma lem1730835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730836 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730835) (@lem1724639 x)). Qed.
Lemma lem1730837 (x : real) : (term2475 x) = (term2475 x).
Proof. exact (MK_COMB (@lem1730836 x) (@lem1730834 x)). Qed.
Lemma lem1730838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730839 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730838) (@lem1724639 x)). Qed.
Lemma lem1730840 (x : real) : (term2468 x) = (term2468 x).
Proof. exact (MK_COMB (@lem1730839 x) (@lem1730837 x)). Qed.
Lemma lem1730841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730842 : term1507 = term1507.
Proof. exact (MK_COMB (@lem1730841) (@lem1727037)). Qed.
Lemma lem1730843 (x : real) : (term2470 x) = (term2470 x).
Proof. exact (MK_COMB (@lem1730842) (@lem1730840 x)). Qed.
Lemma lem1730844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730845 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730844) (@lem1725350 x)). Qed.
Lemma lem1730846 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730845 x) (@lem1724639 x)). Qed.
Lemma lem1730847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730848 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730847) (@lem1725350 x)). Qed.
Lemma lem1730849 (x : real) : (term2454 x) = (term1127 x).
Proof. exact (MK_COMB (@lem1730848 x) (@lem1730772)). Qed.
Lemma lem1730850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730851 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730850) (@lem1730846 x)). Qed.
Lemma lem1730852 (x : real) : (term2455 x) = (term1314 x).
Proof. exact (MK_COMB (@lem1730851 x) (@lem1730849 x)). Qed.
Lemma lem1730853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730854 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730853) (@lem1724639 x)). Qed.
Lemma lem1730855 (x : real) : (term2456 x) = (term2447 x).
Proof. exact (MK_COMB (@lem1730854 x) (@lem1730852 x)). Qed.
Lemma lem1730856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730857 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730856) (@lem1724639 x)). Qed.
Lemma lem1730858 (x : real) : (term2476 x) = (term2475 x).
Proof. exact (MK_COMB (@lem1730857 x) (@lem1730855 x)). Qed.
Lemma lem1730859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730860 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730859) (@lem1724639 x)). Qed.
Lemma lem1730861 (x : real) : (term2464 x) = (term2468 x).
Proof. exact (MK_COMB (@lem1730860 x) (@lem1730858 x)). Qed.
Lemma lem1730862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730863 : term999 = term999.
Proof. exact (MK_COMB (@lem1730862) (@lem1725193)). Qed.
Lemma lem1730864 (x : real) : (term2466 x) = (term2477 x).
Proof. exact (MK_COMB (@lem1730863) (@lem1730861 x)). Qed.
Lemma lem1730865 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730866 (x : real) : (term2472 x) = (term2472 x).
Proof. exact (MK_COMB (@lem1730865) (@lem1730843 x)). Qed.
Lemma lem1730867 (x : real) : (term2473 x) = (term2478 x).
Proof. exact (MK_COMB (@lem1730866 x) (@lem1730864 x)). Qed.
Lemma lem1730879 (x : real) : (term2424 x) = (term2478 x).
Proof. exact (TRANS (@lem1730822 x) (@lem1730867 x)). Qed.
Lemma lem1730880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730881 (x : real) : (term2426 x) = (term2479 x).
Proof. exact (MK_COMB (@lem1730880) (@lem1730879 x)). Qed.
Lemma lem1730882 (x : real) : (term2431 x) = (term2480 x).
Proof. exact (MK_COMB (@lem1730881 x) (@lem1730805 x)). Qed.
Lemma lem1730883 (x : real) : (term2413 x) = (term2480 x).
Proof. exact (TRANS (@lem1730702 x) (@lem1730882 x)). Qed.
Lemma lem1730884 (x : real) : (term2412 x) = (term2480 x).
Proof. exact (TRANS (@lem1730625 x) (@lem1730883 x)). Qed.
Lemma lem1730886 (x : real) (r : real) : (term1219 x r) = (term1220 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1730887 (x : real) : (term270 x) = (term1221 x).
Proof. exact (@lem1730886 x term76). Qed.
Lemma lem1730894 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1730895 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1730896 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1730895) (@lem1730894 x)). Qed.
Lemma lem1730897 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730898 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1730896 x) (@lem1730897)). Qed.
Lemma lem1730911 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1730912 (x : real) : (term1221 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730911 x) (@lem1730898 x)). Qed.
Lemma lem1730913 (x : real) : (term270 x) = (term1224 x).
Proof. exact (TRANS (@lem1730887 x) (@lem1730912 x)). Qed.
Lemma lem1730914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730915 (x : real) : (term317 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730914) (@lem1730913 x)). Qed.
Lemma lem1730917 (x : real) (r : real) : (term804 x r) = (term805 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1730918 : term448 = term2481.
Proof. exact (@lem1730917 term76 term76). Qed.
Lemma lem1730925 : term1581 = term76.
Proof. exact (@lem1483458 term24). Qed.
Lemma lem1730926 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730927 : term2482 = term896.
Proof. exact (MK_COMB (@lem1730926) (@lem1730925)). Qed.
Lemma lem1730928 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730929 : term2483 = term897.
Proof. exact (MK_COMB (@lem1730927) (@lem1730928)). Qed.
Lemma lem1730936 : term184 = term76.
Proof. exact (@lem1483458 term73). Qed.
Lemma lem1730937 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1730938 : term2484 = term896.
Proof. exact (MK_COMB (@lem1730937) (@lem1730936)). Qed.
Lemma lem1730939 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1730940 : term2485 = term897.
Proof. exact (MK_COMB (@lem1730938) (@lem1730939)). Qed.
Lemma lem1730941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730942 : term2486 = term999.
Proof. exact (MK_COMB (@lem1730941) (@lem1730940)). Qed.
Lemma lem1730943 : term2481 = term2487.
Proof. exact (MK_COMB (@lem1730942) (@lem1730929)). Qed.
Lemma lem1730944 : term448 = term2487.
Proof. exact (TRANS (@lem1730918) (@lem1730943)). Qed.
Lemma lem1730945 (x : real) : (term260 x) = (term260 x).
Proof. exact (eq_refl (term260 x)). Qed.
Lemma lem1730946 (x : real) : (term507 x) = (term2488 x).
Proof. exact (MK_COMB (@lem1730945 x) (@lem1730944)). Qed.
Lemma lem1730947 (x : real) : (term541 x) = (term2489 x).
Proof. exact (MK_COMB (@lem1730915 x) (@lem1730946 x)). Qed.
Lemma lem1730948 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730949 (x : real) : (term623 x) = (term2490 x).
Proof. exact (MK_COMB (@lem1730948 x) (@lem1730947 x)). Qed.
Lemma lem1730950 (x : real) : (term464 x) = (term464 x).
Proof. exact (eq_refl (term464 x)). Qed.
Lemma lem1730951 (x : real) : (term2491 x) = (term2492 x).
Proof. exact (MK_COMB (@lem1730950 x) (@lem1730949 x)). Qed.
Lemma lem1730952 (x : real) : (term2493 x) = (term2492 x).
Proof. exact (eq_refl (term2493 x)). Qed.
Lemma lem1730953 (x : real) : (term2492 x) = (term2493 x).
Proof. exact (SYM (@lem1730952 x)). Qed.
Lemma lem1730954 (x : real) : (term2493 x) = (term2494 x).
Proof. exact (@lem1482981 (term2495 x) x). Qed.
Lemma lem1730955 (x : real) : (term2492 x) = (term2494 x).
Proof. exact (TRANS (@lem1730953 x) (@lem1730954 x)). Qed.
Lemma lem1730956 (x : real) : (term2496 x) = (term2497 x).
Proof. exact (eq_refl (term2496 x)). Qed.
Lemma lem1730957 (x : real) : (term819 x) = (term819 x).
Proof. exact (eq_refl (term819 x)). Qed.
Lemma lem1730958 (x : real) : (term2498 x) = (term2499 x).
Proof. exact (MK_COMB (@lem1730957 x) (@lem1730956 x)). Qed.
Lemma lem1730959 (x : real) : (term2500 x) = (term2501 x).
Proof. exact (eq_refl (term2500 x)). Qed.
Lemma lem1730960 (x : real) : (term379 x) = (term379 x).
Proof. exact (eq_refl (term379 x)). Qed.
Lemma lem1730961 (x : real) : (term2502 x) = (term2503 x).
Proof. exact (MK_COMB (@lem1730960 x) (@lem1730959 x)). Qed.
Lemma lem1730962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1730963 (x : real) : (term2504 x) = (term2505 x).
Proof. exact (MK_COMB (@lem1730962) (@lem1730961 x)). Qed.
Lemma lem1730964 (x : real) : (term2494 x) = (term2506 x).
Proof. exact (MK_COMB (@lem1730963 x) (@lem1730958 x)). Qed.
Lemma lem1730965 (x : real) : (term2507 x) = (term2507 x).
Proof. exact (eq_refl (term2507 x)). Qed.
Lemma lem1730966 (x : real) : ((term2492 x) = (term2494 x)) = ((term2492 x) = (term2506 x)).
Proof. exact (MK_COMB (@lem1730965 x) (@lem1730964 x)). Qed.
Lemma lem1730967 (x : real) : (term2492 x) = (term2506 x).
Proof. exact (EQ_MP (@lem1730966 x) (@lem1730955 x)). Qed.
Lemma lem1730968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730969 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730968) (@lem1725350 x)). Qed.
Lemma lem1730970 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730969 x) (@lem1724639 x)). Qed.
Lemma lem1730971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730972 : term999 = term999.
Proof. exact (MK_COMB (@lem1730971) (@lem1725193)). Qed.
Lemma lem1730973 : term2487 = term2487.
Proof. exact (MK_COMB (@lem1730972) (@lem1725193)). Qed.
Lemma lem1730974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730975 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730974) (@lem1725350 x)). Qed.
Lemma lem1730976 (x : real) : (term2488 x) = (term2488 x).
Proof. exact (MK_COMB (@lem1730975 x) (@lem1730973)). Qed.
Lemma lem1730977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730978 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730977) (@lem1730970 x)). Qed.
Lemma lem1730979 (x : real) : (term2489 x) = (term2489 x).
Proof. exact (MK_COMB (@lem1730978 x) (@lem1730976 x)). Qed.
Lemma lem1730980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730981 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730980) (@lem1724639 x)). Qed.
Lemma lem1730982 (x : real) : (term2490 x) = (term2490 x).
Proof. exact (MK_COMB (@lem1730981 x) (@lem1730979 x)). Qed.
Lemma lem1730983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730984 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730983) (@lem1724639 x)). Qed.
Lemma lem1730985 (x : real) : (term2501 x) = (term2501 x).
Proof. exact (MK_COMB (@lem1730984 x) (@lem1730982 x)). Qed.
Lemma lem1730986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730987 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1730986) (@lem1724639 x)). Qed.
Lemma lem1730988 (x : real) : (term2503 x) = (term2503 x).
Proof. exact (MK_COMB (@lem1730987 x) (@lem1730985 x)). Qed.
Lemma lem1730989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730990 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730989) (@lem1725350 x)). Qed.
Lemma lem1730991 (x : real) : (term1224 x) = (term1224 x).
Proof. exact (MK_COMB (@lem1730990 x) (@lem1724639 x)). Qed.
Lemma lem1730992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730993 : term999 = term999.
Proof. exact (MK_COMB (@lem1730992) (@lem1725193)). Qed.
Lemma lem1730994 : term2487 = term2487.
Proof. exact (MK_COMB (@lem1730993) (@lem1725193)). Qed.
Lemma lem1730995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730996 (x : real) : (term260 x) = (term260 x).
Proof. exact (MK_COMB (@lem1730995) (@lem1725350 x)). Qed.
Lemma lem1730997 (x : real) : (term2488 x) = (term2488 x).
Proof. exact (MK_COMB (@lem1730996 x) (@lem1730994)). Qed.
Lemma lem1730998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1730999 (x : real) : (term1225 x) = (term1225 x).
Proof. exact (MK_COMB (@lem1730998) (@lem1730991 x)). Qed.
Lemma lem1731000 (x : real) : (term2489 x) = (term2489 x).
Proof. exact (MK_COMB (@lem1730999 x) (@lem1730997 x)). Qed.
Lemma lem1731001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1731002 (x : real) : (term379 x) = (term379 x).
Proof. exact (MK_COMB (@lem1731001) (@lem1724639 x)). Qed.
Lemma lem1731003 (x : real) : (term2490 x) = (term2490 x).
Proof. exact (MK_COMB (@lem1731002 x) (@lem1731000 x)). Qed.
Lemma lem1731004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1731005 (x : real) : (term1745 x) = (term260 x).
Proof. exact (MK_COMB (@lem1731004) (@lem1728062 x)). Qed.
Lemma lem1731006 (x : real) : (term2497 x) = (term2508 x).
Proof. exact (MK_COMB (@lem1731005 x) (@lem1731003 x)). Qed.
Lemma lem1731007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1731008 (x : real) : (term819 x) = (term321 x).
Proof. exact (MK_COMB (@lem1731007) (@lem1724751 x)). Qed.
Lemma lem1731009 (x : real) : (term2499 x) = (term2509 x).
Proof. exact (MK_COMB (@lem1731008 x) (@lem1731006 x)). Qed.
Lemma lem1731010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1731011 (x : real) : (term2505 x) = (term2505 x).
Proof. exact (MK_COMB (@lem1731010) (@lem1730988 x)). Qed.
Lemma lem1731012 (x : real) : (term2506 x) = (term2510 x).
Proof. exact (MK_COMB (@lem1731011 x) (@lem1731009 x)). Qed.
Lemma lem1731023 (x : real) : (term2492 x) = (term2510 x).
Proof. exact (TRANS (@lem1730967 x) (@lem1731012 x)). Qed.
Lemma lem1731024 (x : real) : (term2491 x) = (term2510 x).
Proof. exact (TRANS (@lem1730951 x) (@lem1731023 x)). Qed.
Lemma lem1731025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1731026 (x : real) : (term2511 x) = (term2512 x).
Proof. exact (MK_COMB (@lem1731025) (@lem1730884 x)). Qed.
Lemma lem1731027 (x : real) : (term621 x) = (term2513 x).
Proof. exact (MK_COMB (@lem1731026 x) (@lem1731024 x)). Qed.
Lemma lem1731028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1731029 (x : real) : (term629 x) = (term2514 x).
Proof. exact (MK_COMB (@lem1731028) (@lem1730588 x)). Qed.
Lemma lem1731030 (x : real) : (term630 x) = (term2515 x).
Proof. exact (MK_COMB (@lem1731029 x) (@lem1731027 x)). Qed.
Lemma lem1731031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1731032 (x : real) : (term645 x) = (term2516 x).
Proof. exact (MK_COMB (@lem1731031) (@lem1730199 x)). Qed.
Lemma lem1731033 (x : real) : (term646 x) = (term2517 x).
Proof. exact (MK_COMB (@lem1731032 x) (@lem1731030 x)). Qed.
Lemma lem1731034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1731035 (x : real) : (term679 x) = (term2518 x).
Proof. exact (MK_COMB (@lem1731034) (@lem1729566 x)). Qed.
Lemma lem1731036 (x : real) : (term680 x) = (term2519 x).
Proof. exact (MK_COMB (@lem1731035 x) (@lem1731033 x)). Qed.
Lemma lem1731037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1731038 (x : real) : (term800 x) = (term2520 x).
Proof. exact (MK_COMB (@lem1731037) (@lem1728003 x)). Qed.
Lemma lem1731039 (x : real) : (term801 x) = (term2521 x).
Proof. exact (MK_COMB (@lem1731038 x) (@lem1731036 x)). Qed.
Lemma lem1731040 (x : real) (h1 : term2521 x) : term2521 x.
Proof. exact (h1). Qed.
Lemma lem1731041 (x : real) (h1 : term1725 x) : term1725 x.
Proof. exact (h1). Qed.
Lemma lem1731042 (x : real) (h1 : term1355 x) : term1355 x.
Proof. exact (h1). Qed.
Lemma lem1731043 (x : real) (h1 : term1218 x) : term1218 x.
Proof. exact (h1). Qed.
Lemma lem1731044 (x : real) (h1 : term1040 x) : term1040 x.
Proof. exact (h1). Qed.
Lemma lem1731045 (x : real) (h1 : term984 x) : term984 x.
Proof. exact (h1). Qed.
Lemma lem1731046 (x : real) (h1 : term982 x) : term982 x.
Proof. exact (h1). Qed.
Lemma lem1731047 (x : real) (h1 : term972 x) : term972 x.
Proof. exact (h1). Qed.
Lemma lem1731048 (x : real) (h1 : term972 x) : term971 x.
Proof. exact (proj2 (@lem1731047 x h1)). Qed.
Lemma lem1731050 (x : real) (h1 : term972 x) : term970 x.
Proof. exact (proj2 (@lem1731048 x h1)). Qed.
Lemma lem1731052 (x : real) (h1 : term972 x) : term968 x.
Proof. exact (proj2 (@lem1731050 x h1)). Qed.
Lemma lem1731056 (x : real) (h1 : term972 x) : term966 x.
Proof. exact (proj2 (@lem1731052 x h1)). Qed.
Lemma lem1731058 (x : real) (h1 : term972 x) : term899 x.
Proof. exact (proj2 (@lem1731056 x h1)). Qed.
Lemma lem1731060 (x : real) (h1 : term972 x) : term897.
Proof. exact (proj2 (@lem1731058 x h1)). Qed.
Lemma lem1731063 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731064 : term897 = term2523.
Proof. exact (@lem1731063 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731065 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731066 : term897 = False.
Proof. exact (TRANS (@lem1731064) (@lem1731065)). Qed.
Lemma lem1731067 (x : real) (h1 : term972 x) : False.
Proof. exact (EQ_MP (@lem1731066) (@lem1731060 x h1)). Qed.
Lemma lem1731068 (x : real) (h1 : term980 x) : term980 x.
Proof. exact (h1). Qed.
Lemma lem1731069 (x : real) (h1 : term980 x) : term979 x.
Proof. exact (proj2 (@lem1731068 x h1)). Qed.
Lemma lem1731071 (x : real) (h1 : term980 x) : term978 x.
Proof. exact (proj2 (@lem1731069 x h1)). Qed.
Lemma lem1731073 (x : real) (h1 : term980 x) : term976 x.
Proof. exact (proj2 (@lem1731071 x h1)). Qed.
Lemma lem1731077 (x : real) (h1 : term980 x) : term974 x.
Proof. exact (proj2 (@lem1731073 x h1)). Qed.
Lemma lem1731079 (x : real) (h1 : term980 x) : term938 x.
Proof. exact (proj2 (@lem1731077 x h1)). Qed.
Lemma lem1731081 (x : real) (h1 : term980 x) : term936.
Proof. exact (proj2 (@lem1731079 x h1)). Qed.
Lemma lem1731084 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731085 : term936 = False.
Proof. exact (@lem1731084 term923 (NUMERAL 0)). Qed.
Lemma lem1731086 (x : real) (h1 : term980 x) : False.
Proof. exact (EQ_MP (@lem1731085) (@lem1731081 x h1)). Qed.
Lemma lem1731087 (x : real) (h1 : term982 x) : False.
Proof. exact (or_elim (@lem1731046 x h1) (fun h0 : term972 x => @lem1731067 x h0) (fun h0 : term980 x => @lem1731086 x h0)). Qed.
Lemma lem1731088 (x : real) (h1 : term949 x) : term949 x.
Proof. exact (h1). Qed.
Lemma lem1731089 (x : real) (h1 : term907 x) : term907 x.
Proof. exact (h1). Qed.
Lemma lem1731090 (x : real) (h1 : term907 x) : term906 x.
Proof. exact (proj2 (@lem1731089 x h1)). Qed.
Lemma lem1731092 (x : real) (h1 : term907 x) : term905 x.
Proof. exact (proj2 (@lem1731090 x h1)). Qed.
Lemma lem1731094 (x : real) (h1 : term907 x) : term903 x.
Proof. exact (proj2 (@lem1731092 x h1)). Qed.
Lemma lem1731098 (x : real) (h1 : term907 x) : term901 x.
Proof. exact (proj2 (@lem1731094 x h1)). Qed.
Lemma lem1731100 (x : real) (h1 : term907 x) : term899 x.
Proof. exact (proj2 (@lem1731098 x h1)). Qed.
Lemma lem1731102 (x : real) (h1 : term907 x) : term897.
Proof. exact (proj2 (@lem1731100 x h1)). Qed.
Lemma lem1731105 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731106 : term897 = term2523.
Proof. exact (@lem1731105 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731107 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731108 : term897 = False.
Proof. exact (TRANS (@lem1731106) (@lem1731107)). Qed.
Lemma lem1731109 (x : real) (h1 : term907 x) : False.
Proof. exact (EQ_MP (@lem1731108) (@lem1731102 x h1)). Qed.
Lemma lem1731110 (x : real) (h1 : term947 x) : term947 x.
Proof. exact (h1). Qed.
Lemma lem1731111 (x : real) (h1 : term947 x) : term945 x.
Proof. exact (proj2 (@lem1731110 x h1)). Qed.
Lemma lem1731113 (x : real) (h1 : term947 x) : term944 x.
Proof. exact (proj2 (@lem1731111 x h1)). Qed.
Lemma lem1731115 (x : real) (h1 : term947 x) : term942 x.
Proof. exact (proj2 (@lem1731113 x h1)). Qed.
Lemma lem1731119 (x : real) (h1 : term947 x) : term940 x.
Proof. exact (proj2 (@lem1731115 x h1)). Qed.
Lemma lem1731121 (x : real) (h1 : term947 x) : term938 x.
Proof. exact (proj2 (@lem1731119 x h1)). Qed.
Lemma lem1731123 (x : real) (h1 : term947 x) : term936.
Proof. exact (proj2 (@lem1731121 x h1)). Qed.
Lemma lem1731126 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731127 : term936 = False.
Proof. exact (@lem1731126 term923 (NUMERAL 0)). Qed.
Lemma lem1731128 (x : real) (h1 : term947 x) : False.
Proof. exact (EQ_MP (@lem1731127) (@lem1731123 x h1)). Qed.
Lemma lem1731129 (x : real) (h1 : term949 x) : False.
Proof. exact (or_elim (@lem1731088 x h1) (fun h0 : term907 x => @lem1731109 x h0) (fun h0 : term947 x => @lem1731128 x h0)). Qed.
Lemma lem1731130 (x : real) (h1 : term984 x) : False.
Proof. exact (or_elim (@lem1731045 x h1) (fun h0 : term982 x => @lem1731087 x h0) (fun h0 : term949 x => @lem1731129 x h0)). Qed.
Lemma lem1731131 (x : real) (h1 : term1037 x) : term1037 x.
Proof. exact (h1). Qed.
Lemma lem1731132 (x : real) (h1 : term1016 x) : term1016 x.
Proof. exact (h1). Qed.
Lemma lem1731133 (x : real) (h1 : term1016 x) : term1014 x.
Proof. exact (proj2 (@lem1731132 x h1)). Qed.
Lemma lem1731135 (x : real) (h1 : term1016 x) : term1030 x.
Proof. exact (proj2 (@lem1731133 x h1)). Qed.
Lemma lem1731139 (x : real) (h1 : term1016 x) : term1029 x.
Proof. exact (proj2 (@lem1731135 x h1)). Qed.
Lemma lem1731141 (x : real) (h1 : term1016 x) : term1001 x.
Proof. exact (proj2 (@lem1731139 x h1)). Qed.
Lemma lem1731143 (x : real) (h1 : term1016 x) : term1000.
Proof. exact (proj2 (@lem1731141 x h1)). Qed.
Lemma lem1731146 (x : real) (h1 : term1016 x) : term897.
Proof. exact (proj1 (@lem1731143 x h1)). Qed.
Lemma lem1731148 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731149 : term897 = term2523.
Proof. exact (@lem1731148 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731150 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731151 : term897 = False.
Proof. exact (TRANS (@lem1731149) (@lem1731150)). Qed.
Lemma lem1731152 (x : real) (h1 : term1016 x) : False.
Proof. exact (EQ_MP (@lem1731151) (@lem1731146 x h1)). Qed.
Lemma lem1731153 (x : real) (h1 : term1036 x) : term1036 x.
Proof. exact (h1). Qed.
Lemma lem1731154 (x : real) (h1 : term1036 x) : term1035 x.
Proof. exact (proj2 (@lem1731153 x h1)). Qed.
Lemma lem1731156 (x : real) (h1 : term1036 x) : term1034 x.
Proof. exact (proj2 (@lem1731154 x h1)). Qed.
Lemma lem1731160 (x : real) (h1 : term1036 x) : term1032 x.
Proof. exact (proj2 (@lem1731156 x h1)). Qed.
Lemma lem1731162 (x : real) (h1 : term1036 x) : term1001 x.
Proof. exact (proj2 (@lem1731160 x h1)). Qed.
Lemma lem1731164 (x : real) (h1 : term1036 x) : term1000.
Proof. exact (proj2 (@lem1731162 x h1)). Qed.
Lemma lem1731167 (x : real) (h1 : term1036 x) : term897.
Proof. exact (proj1 (@lem1731164 x h1)). Qed.
Lemma lem1731169 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731170 : term897 = term2523.
Proof. exact (@lem1731169 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731171 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731172 : term897 = False.
Proof. exact (TRANS (@lem1731170) (@lem1731171)). Qed.
Lemma lem1731173 (x : real) (h1 : term1036 x) : False.
Proof. exact (EQ_MP (@lem1731172) (@lem1731167 x h1)). Qed.
Lemma lem1731174 (x : real) (h1 : term1037 x) : False.
Proof. exact (or_elim (@lem1731131 x h1) (fun h0 : term1016 x => @lem1731152 x h0) (fun h0 : term1036 x => @lem1731173 x h0)). Qed.
Lemma lem1731175 (x : real) (h1 : term1040 x) : False.
Proof. exact (or_elim (@lem1731044 x h1) (fun h0 : term984 x => @lem1731130 x h0) (fun h0 : term1037 x => @lem1731174 x h0)). Qed.
Lemma lem1731176 (x : real) (h1 : term1216 x) : term1216 x.
Proof. exact (h1). Qed.
Lemma lem1731177 (x : real) (h1 : term1173 x) : term1173 x.
Proof. exact (h1). Qed.
Lemma lem1731178 (x : real) (h1 : term1171 x) : term1171 x.
Proof. exact (h1). Qed.
Lemma lem1731179 (x : real) (h1 : term1161 x) : term1161 x.
Proof. exact (h1). Qed.
Lemma lem1731180 (x : real) (h1 : term1161 x) : term1160 x.
Proof. exact (proj2 (@lem1731179 x h1)). Qed.
Lemma lem1731182 (x : real) (h1 : term1161 x) : term1159 x.
Proof. exact (proj2 (@lem1731180 x h1)). Qed.
Lemma lem1731184 (x : real) (h1 : term1161 x) : term1157 x.
Proof. exact (proj2 (@lem1731182 x h1)). Qed.
Lemma lem1731188 (x : real) (h1 : term1161 x) : term1155 x.
Proof. exact (proj2 (@lem1731184 x h1)). Qed.
Lemma lem1731190 (x : real) (h1 : term1161 x) : term1101 x.
Proof. exact (proj2 (@lem1731188 x h1)). Qed.
Lemma lem1731192 (x : real) (h1 : term1161 x) : term936.
Proof. exact (proj2 (@lem1731190 x h1)). Qed.
Lemma lem1731195 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731196 : term936 = False.
Proof. exact (@lem1731195 term923 (NUMERAL 0)). Qed.
Lemma lem1731197 (x : real) (h1 : term1161 x) : False.
Proof. exact (EQ_MP (@lem1731196) (@lem1731192 x h1)). Qed.
Lemma lem1731198 (x : real) (h1 : term1169 x) : term1169 x.
Proof. exact (h1). Qed.
Lemma lem1731199 (x : real) (h1 : term1169 x) : term1168 x.
Proof. exact (proj2 (@lem1731198 x h1)). Qed.
Lemma lem1731201 (x : real) (h1 : term1169 x) : term1167 x.
Proof. exact (proj2 (@lem1731199 x h1)). Qed.
Lemma lem1731203 (x : real) (h1 : term1169 x) : term1165 x.
Proof. exact (proj2 (@lem1731201 x h1)). Qed.
Lemma lem1731207 (x : real) (h1 : term1169 x) : term1163 x.
Proof. exact (proj2 (@lem1731203 x h1)). Qed.
Lemma lem1731209 (x : real) (h1 : term1169 x) : term1127 x.
Proof. exact (proj2 (@lem1731207 x h1)). Qed.
Lemma lem1731211 (x : real) (h1 : term1169 x) : term897.
Proof. exact (proj2 (@lem1731209 x h1)). Qed.
Lemma lem1731214 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731215 : term897 = term2523.
Proof. exact (@lem1731214 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731216 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731217 : term897 = False.
Proof. exact (TRANS (@lem1731215) (@lem1731216)). Qed.
Lemma lem1731218 (x : real) (h1 : term1169 x) : False.
Proof. exact (EQ_MP (@lem1731217) (@lem1731211 x h1)). Qed.
Lemma lem1731219 (x : real) (h1 : term1171 x) : False.
Proof. exact (or_elim (@lem1731178 x h1) (fun h0 : term1161 x => @lem1731197 x h0) (fun h0 : term1169 x => @lem1731218 x h0)). Qed.
Lemma lem1731220 (x : real) (h1 : term1138 x) : term1138 x.
Proof. exact (h1). Qed.
Lemma lem1731221 (x : real) (h1 : term1109 x) : term1109 x.
Proof. exact (h1). Qed.
Lemma lem1731222 (x : real) (h1 : term1109 x) : term1108 x.
Proof. exact (proj2 (@lem1731221 x h1)). Qed.
Lemma lem1731224 (x : real) (h1 : term1109 x) : term1107 x.
Proof. exact (proj2 (@lem1731222 x h1)). Qed.
Lemma lem1731226 (x : real) (h1 : term1109 x) : term1105 x.
Proof. exact (proj2 (@lem1731224 x h1)). Qed.
Lemma lem1731230 (x : real) (h1 : term1109 x) : term1103 x.
Proof. exact (proj2 (@lem1731226 x h1)). Qed.
Lemma lem1731232 (x : real) (h1 : term1109 x) : term1101 x.
Proof. exact (proj2 (@lem1731230 x h1)). Qed.
Lemma lem1731234 (x : real) (h1 : term1109 x) : term936.
Proof. exact (proj2 (@lem1731232 x h1)). Qed.
Lemma lem1731237 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731238 : term936 = False.
Proof. exact (@lem1731237 term923 (NUMERAL 0)). Qed.
Lemma lem1731239 (x : real) (h1 : term1109 x) : False.
Proof. exact (EQ_MP (@lem1731238) (@lem1731234 x h1)). Qed.
Lemma lem1731240 (x : real) (h1 : term1136 x) : term1136 x.
Proof. exact (h1). Qed.
Lemma lem1731241 (x : real) (h1 : term1136 x) : term1134 x.
Proof. exact (proj2 (@lem1731240 x h1)). Qed.
Lemma lem1731243 (x : real) (h1 : term1136 x) : term1133 x.
Proof. exact (proj2 (@lem1731241 x h1)). Qed.
Lemma lem1731245 (x : real) (h1 : term1136 x) : term1131 x.
Proof. exact (proj2 (@lem1731243 x h1)). Qed.
Lemma lem1731249 (x : real) (h1 : term1136 x) : term1129 x.
Proof. exact (proj2 (@lem1731245 x h1)). Qed.
Lemma lem1731251 (x : real) (h1 : term1136 x) : term1127 x.
Proof. exact (proj2 (@lem1731249 x h1)). Qed.
Lemma lem1731253 (x : real) (h1 : term1136 x) : term897.
Proof. exact (proj2 (@lem1731251 x h1)). Qed.
Lemma lem1731256 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731257 : term897 = term2523.
Proof. exact (@lem1731256 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731258 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731259 : term897 = False.
Proof. exact (TRANS (@lem1731257) (@lem1731258)). Qed.
Lemma lem1731260 (x : real) (h1 : term1136 x) : False.
Proof. exact (EQ_MP (@lem1731259) (@lem1731253 x h1)). Qed.
Lemma lem1731261 (x : real) (h1 : term1138 x) : False.
Proof. exact (or_elim (@lem1731220 x h1) (fun h0 : term1109 x => @lem1731239 x h0) (fun h0 : term1136 x => @lem1731260 x h0)). Qed.
Lemma lem1731262 (x : real) (h1 : term1173 x) : False.
Proof. exact (or_elim (@lem1731177 x h1) (fun h0 : term1171 x => @lem1731219 x h0) (fun h0 : term1138 x => @lem1731261 x h0)). Qed.
Lemma lem1731263 (x : real) (h1 : term1213 x) : term1213 x.
Proof. exact (h1). Qed.
Lemma lem1731264 (x : real) (h1 : term1200 x) : term1200 x.
Proof. exact (h1). Qed.
Lemma lem1731265 (x : real) (h1 : term1200 x) : term1198 x.
Proof. exact (proj2 (@lem1731264 x h1)). Qed.
Lemma lem1731267 (x : real) (h1 : term1200 x) : term1206 x.
Proof. exact (proj2 (@lem1731265 x h1)). Qed.
Lemma lem1731271 (x : real) (h1 : term1200 x) : term1205 x.
Proof. exact (proj2 (@lem1731267 x h1)). Qed.
Lemma lem1731273 (x : real) (h1 : term1200 x) : term1185 x.
Proof. exact (proj2 (@lem1731271 x h1)). Qed.
Lemma lem1731275 (x : real) (h1 : term1200 x) : term1184.
Proof. exact (proj2 (@lem1731273 x h1)). Qed.
Lemma lem1731277 (x : real) (h1 : term1200 x) : term897.
Proof. exact (proj2 (@lem1731275 x h1)). Qed.
Lemma lem1731280 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731281 : term897 = term2523.
Proof. exact (@lem1731280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731282 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731283 : term897 = False.
Proof. exact (TRANS (@lem1731281) (@lem1731282)). Qed.
Lemma lem1731284 (x : real) (h1 : term1200 x) : False.
Proof. exact (EQ_MP (@lem1731283) (@lem1731277 x h1)). Qed.
Lemma lem1731285 (x : real) (h1 : term1212 x) : term1212 x.
Proof. exact (h1). Qed.
Lemma lem1731286 (x : real) (h1 : term1212 x) : term1211 x.
Proof. exact (proj2 (@lem1731285 x h1)). Qed.
Lemma lem1731288 (x : real) (h1 : term1212 x) : term1210 x.
Proof. exact (proj2 (@lem1731286 x h1)). Qed.
Lemma lem1731292 (x : real) (h1 : term1212 x) : term1208 x.
Proof. exact (proj2 (@lem1731288 x h1)). Qed.
Lemma lem1731294 (x : real) (h1 : term1212 x) : term1185 x.
Proof. exact (proj2 (@lem1731292 x h1)). Qed.
Lemma lem1731296 (x : real) (h1 : term1212 x) : term1184.
Proof. exact (proj2 (@lem1731294 x h1)). Qed.
Lemma lem1731298 (x : real) (h1 : term1212 x) : term897.
Proof. exact (proj2 (@lem1731296 x h1)). Qed.
Lemma lem1731301 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731302 : term897 = term2523.
Proof. exact (@lem1731301 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731303 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731304 : term897 = False.
Proof. exact (TRANS (@lem1731302) (@lem1731303)). Qed.
Lemma lem1731305 (x : real) (h1 : term1212 x) : False.
Proof. exact (EQ_MP (@lem1731304) (@lem1731298 x h1)). Qed.
Lemma lem1731306 (x : real) (h1 : term1213 x) : False.
Proof. exact (or_elim (@lem1731263 x h1) (fun h0 : term1200 x => @lem1731284 x h0) (fun h0 : term1212 x => @lem1731305 x h0)). Qed.
Lemma lem1731307 (x : real) (h1 : term1216 x) : False.
Proof. exact (or_elim (@lem1731176 x h1) (fun h0 : term1173 x => @lem1731262 x h0) (fun h0 : term1213 x => @lem1731306 x h0)). Qed.
Lemma lem1731308 (x : real) (h1 : term1218 x) : False.
Proof. exact (or_elim (@lem1731043 x h1) (fun h0 : term1040 x => @lem1731175 x h0) (fun h0 : term1216 x => @lem1731307 x h0)). Qed.
Lemma lem1731309 (x : real) (h1 : term1353 x) : term1353 x.
Proof. exact (h1). Qed.
Lemma lem1731310 (x : real) (h1 : term1292 x) : term1292 x.
Proof. exact (h1). Qed.
Lemma lem1731311 (x : real) (h1 : term1274 x) : term1274 x.
Proof. exact (h1). Qed.
Lemma lem1731312 (x : real) (h1 : term1258 x) : term1258 x.
Proof. exact (h1). Qed.
Lemma lem1731313 (x : real) (h1 : term1258 x) : term1257 x.
Proof. exact (proj2 (@lem1731312 x h1)). Qed.
Lemma lem1731315 (x : real) (h1 : term1258 x) : term1256 x.
Proof. exact (proj2 (@lem1731313 x h1)). Qed.
Lemma lem1731319 (x : real) (h1 : term1258 x) : term1254 x.
Proof. exact (proj2 (@lem1731315 x h1)). Qed.
Lemma lem1731320 (x : real) (h1 : term1258 x) : term179 x.
Proof. exact (proj1 (@lem1731315 x h1)). Qed.
Lemma lem1731322 (x : real) (h1 : term1258 x) : term1224 x.
Proof. exact (proj1 (@lem1731319 x h1)). Qed.
Lemma lem1731323 (x : real) (h1 : term1258 x) : term326 x.
Proof. exact (proj2 (@lem1731322 x h1)). Qed.
Lemma lem1731328 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731329 : term1117 = term2525.
Proof. exact (@lem1731328 (NUMERAL 0) term185). Qed.
Lemma lem1731330 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731331 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731332 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731331 h1) (fun h1 : term2525 = True => @lem1731330)). Qed.
Lemma lem1731333 : term2525 = True.
Proof. exact (EQ_MP (@lem1731332) (@lem1731330)). Qed.
Lemma lem1731334 : term1117 = True.
Proof. exact (TRANS (@lem1731329) (@lem1731333)). Qed.
Lemma lem1731335 : True = term1117.
Proof. exact (SYM (@lem1731334)). Qed.
Lemma lem1731336 : term1117.
Proof. exact (EQ_MP (@lem1731335) (@lem0)). Qed.
Lemma lem1731337 (x : real) (h1 : term1258 x) : term2527 x.
Proof. exact (conj (@lem1731336) (@lem1731323 x h1)). Qed.
Lemma lem1731339 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1731340 (x : real) : term2529 x.
Proof. exact (@lem1731339 term24 x). Qed.
Lemma lem1731341 (x : real) (h1 : term1258 x) : term1223 x.
Proof. exact (@lem1731340 x (@lem1731337 x h1)). Qed.
Lemma lem1731342 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1731343 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1731344 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1731343) (@lem1731342 x)). Qed.
Lemma lem1731345 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731346 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1731344 x) (@lem1731345)). Qed.
Lemma lem1731347 (x : real) (h1 : term1258 x) : term326 x.
Proof. exact (EQ_MP (@lem1731346 x) (@lem1731341 x h1)). Qed.
Lemma lem1731349 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731350 : term1117 = term2525.
Proof. exact (@lem1731349 (NUMERAL 0) term185). Qed.
Lemma lem1731351 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731352 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731353 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731352 h1) (fun h1 : term2525 = True => @lem1731351)). Qed.
Lemma lem1731354 : term2525 = True.
Proof. exact (EQ_MP (@lem1731353) (@lem1731351)). Qed.
Lemma lem1731355 : term1117 = True.
Proof. exact (TRANS (@lem1731350) (@lem1731354)). Qed.
Lemma lem1731356 : True = term1117.
Proof. exact (SYM (@lem1731355)). Qed.
Lemma lem1731357 : term1117.
Proof. exact (EQ_MP (@lem1731356) (@lem0)). Qed.
Lemma lem1731358 (x : real) (h1 : term1258 x) : term2530 x.
Proof. exact (conj (@lem1731357) (@lem1731320 x h1)). Qed.
Lemma lem1731360 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1731361 (x : real) : term2532 x.
Proof. exact (@lem1731360 term24 (term176 x)). Qed.
Lemma lem1731362 (x : real) (h1 : term1258 x) : term2533 x.
Proof. exact (@lem1731361 x (@lem1731358 x h1)). Qed.
Lemma lem1731363 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1731364 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731365 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1731364) (@lem1731363 x)). Qed.
Lemma lem1731366 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731367 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1731365 x) (@lem1731366)). Qed.
Lemma lem1731368 (x : real) (h1 : term1258 x) : term179 x.
Proof. exact (EQ_MP (@lem1731367 x) (@lem1731362 x h1)). Qed.
Lemma lem1731369 (x : real) (h1 : term1258 x) : term2536 x.
Proof. exact (conj (@lem1731368 x h1) (@lem1731347 x h1)). Qed.
Lemma lem1731371 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1731372 (x : real) : term2538 x.
Proof. exact (@lem1731371 (term176 x) x). Qed.
Lemma lem1731373 (x : real) (h1 : term1258 x) : term2539 x.
Proof. exact (@lem1731372 x (@lem1731369 x h1)). Qed.
Lemma lem1731374 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1731376 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1731377 : term1261 = term76.
Proof. exact (@lem1731376 term185). Qed.
Lemma lem1731378 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1731379 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1731378) (@lem1731377)). Qed.
Lemma lem1731380 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1731381 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1731379) (@lem1731380 x)). Qed.
Lemma lem1731382 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1731374 x) (@lem1731381 x)). Qed.
Lemma lem1731383 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1731384 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1731382 x) (@lem1731383 x)). Qed.
Lemma lem1731385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731386 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1731385) (@lem1731384 x)). Qed.
Lemma lem1731387 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731388 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1731386 x) (@lem1731387)). Qed.
Lemma lem1731389 (x : real) (h1 : term1258 x) : term897.
Proof. exact (EQ_MP (@lem1731388 x) (@lem1731373 x h1)). Qed.
Lemma lem1731391 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731392 : term897 = term2523.
Proof. exact (@lem1731391 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731393 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731394 : term897 = False.
Proof. exact (TRANS (@lem1731392) (@lem1731393)). Qed.
Lemma lem1731395 (x : real) (h1 : term1258 x) : False.
Proof. exact (EQ_MP (@lem1731394) (@lem1731389 x h1)). Qed.
Lemma lem1731396 (x : real) (h1 : term1272 x) : term1272 x.
Proof. exact (h1). Qed.
Lemma lem1731397 (x : real) (h1 : term1272 x) : term1271 x.
Proof. exact (proj2 (@lem1731396 x h1)). Qed.
Lemma lem1731399 (x : real) (h1 : term1272 x) : term1270 x.
Proof. exact (proj2 (@lem1731397 x h1)). Qed.
Lemma lem1731403 (x : real) (h1 : term1272 x) : term1268 x.
Proof. exact (proj2 (@lem1731399 x h1)). Qed.
Lemma lem1731405 (x : real) (h1 : term1272 x) : term899 x.
Proof. exact (proj2 (@lem1731403 x h1)). Qed.
Lemma lem1731409 (x : real) (h1 : term1272 x) : term897.
Proof. exact (proj2 (@lem1731405 x h1)). Qed.
Lemma lem1731412 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731413 : term897 = term2523.
Proof. exact (@lem1731412 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731414 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731415 : term897 = False.
Proof. exact (TRANS (@lem1731413) (@lem1731414)). Qed.
Lemma lem1731416 (x : real) (h1 : term1272 x) : False.
Proof. exact (EQ_MP (@lem1731415) (@lem1731409 x h1)). Qed.
Lemma lem1731417 (x : real) (h1 : term1274 x) : False.
Proof. exact (or_elim (@lem1731311 x h1) (fun h0 : term1258 x => @lem1731395 x h0) (fun h0 : term1272 x => @lem1731416 x h0)). Qed.
Lemma lem1731418 (x : real) (h1 : term1289 x) : term1289 x.
Proof. exact (h1). Qed.
Lemma lem1731419 (x : real) (h1 : term1289 x) : term1287 x.
Proof. exact (proj2 (@lem1731418 x h1)). Qed.
Lemma lem1731423 (x : real) (h1 : term1289 x) : term1286 x.
Proof. exact (proj2 (@lem1731419 x h1)). Qed.
Lemma lem1731425 (x : real) (h1 : term1289 x) : term1285 x.
Proof. exact (proj2 (@lem1731423 x h1)). Qed.
Lemma lem1731429 (x : real) (h1 : term1289 x) : term1284.
Proof. exact (proj2 (@lem1731425 x h1)). Qed.
Lemma lem1731431 (x : real) (h1 : term1289 x) : term897.
Proof. exact (proj2 (@lem1731429 x h1)). Qed.
Lemma lem1731434 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731435 : term897 = term2523.
Proof. exact (@lem1731434 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731436 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731437 : term897 = False.
Proof. exact (TRANS (@lem1731435) (@lem1731436)). Qed.
Lemma lem1731438 (x : real) (h1 : term1289 x) : False.
Proof. exact (EQ_MP (@lem1731437) (@lem1731431 x h1)). Qed.
Lemma lem1731439 (x : real) (h1 : term1292 x) : False.
Proof. exact (or_elim (@lem1731310 x h1) (fun h0 : term1274 x => @lem1731417 x h0) (fun h0 : term1289 x => @lem1731438 x h0)). Qed.
Lemma lem1731440 (x : real) (h1 : term1351 x) : term1351 x.
Proof. exact (h1). Qed.
Lemma lem1731441 (x : real) (h1 : term1334 x) : term1334 x.
Proof. exact (h1). Qed.
Lemma lem1731442 (x : real) (h1 : term1318 x) : term1318 x.
Proof. exact (h1). Qed.
Lemma lem1731443 (x : real) (h1 : term1318 x) : term1317 x.
Proof. exact (proj2 (@lem1731442 x h1)). Qed.
Lemma lem1731445 (x : real) (h1 : term1318 x) : term1316 x.
Proof. exact (proj2 (@lem1731443 x h1)). Qed.
Lemma lem1731449 (x : real) (h1 : term1318 x) : term1314 x.
Proof. exact (proj2 (@lem1731445 x h1)). Qed.
Lemma lem1731451 (x : real) (h1 : term1318 x) : term1127 x.
Proof. exact (proj2 (@lem1731449 x h1)). Qed.
Lemma lem1731455 (x : real) (h1 : term1318 x) : term897.
Proof. exact (proj2 (@lem1731451 x h1)). Qed.
Lemma lem1731458 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731459 : term897 = term2523.
Proof. exact (@lem1731458 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731460 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731461 : term897 = False.
Proof. exact (TRANS (@lem1731459) (@lem1731460)). Qed.
Lemma lem1731462 (x : real) (h1 : term1318 x) : False.
Proof. exact (EQ_MP (@lem1731461) (@lem1731455 x h1)). Qed.
Lemma lem1731463 (x : real) (h1 : term1332 x) : term1332 x.
Proof. exact (h1). Qed.
Lemma lem1731464 (x : real) (h1 : term1332 x) : term1331 x.
Proof. exact (proj2 (@lem1731463 x h1)). Qed.
Lemma lem1731466 (x : real) (h1 : term1332 x) : term1330 x.
Proof. exact (proj2 (@lem1731464 x h1)). Qed.
Lemma lem1731470 (x : real) (h1 : term1332 x) : term1328 x.
Proof. exact (proj2 (@lem1731466 x h1)). Qed.
Lemma lem1731471 (x : real) (h1 : term1332 x) : term179 x.
Proof. exact (proj1 (@lem1731466 x h1)). Qed.
Lemma lem1731473 (x : real) (h1 : term1332 x) : term1224 x.
Proof. exact (proj1 (@lem1731470 x h1)). Qed.
Lemma lem1731474 (x : real) (h1 : term1332 x) : term326 x.
Proof. exact (proj2 (@lem1731473 x h1)). Qed.
Lemma lem1731479 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731480 : term1117 = term2525.
Proof. exact (@lem1731479 (NUMERAL 0) term185). Qed.
Lemma lem1731481 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731482 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731483 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731482 h1) (fun h1 : term2525 = True => @lem1731481)). Qed.
Lemma lem1731484 : term2525 = True.
Proof. exact (EQ_MP (@lem1731483) (@lem1731481)). Qed.
Lemma lem1731485 : term1117 = True.
Proof. exact (TRANS (@lem1731480) (@lem1731484)). Qed.
Lemma lem1731486 : True = term1117.
Proof. exact (SYM (@lem1731485)). Qed.
Lemma lem1731487 : term1117.
Proof. exact (EQ_MP (@lem1731486) (@lem0)). Qed.
Lemma lem1731488 (x : real) (h1 : term1332 x) : term2527 x.
Proof. exact (conj (@lem1731487) (@lem1731474 x h1)). Qed.
Lemma lem1731490 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1731491 (x : real) : term2529 x.
Proof. exact (@lem1731490 term24 x). Qed.
Lemma lem1731492 (x : real) (h1 : term1332 x) : term1223 x.
Proof. exact (@lem1731491 x (@lem1731488 x h1)). Qed.
Lemma lem1731493 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1731494 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1731495 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1731494) (@lem1731493 x)). Qed.
Lemma lem1731496 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731497 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1731495 x) (@lem1731496)). Qed.
Lemma lem1731498 (x : real) (h1 : term1332 x) : term326 x.
Proof. exact (EQ_MP (@lem1731497 x) (@lem1731492 x h1)). Qed.
Lemma lem1731500 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731501 : term1117 = term2525.
Proof. exact (@lem1731500 (NUMERAL 0) term185). Qed.
Lemma lem1731502 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731503 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731504 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731503 h1) (fun h1 : term2525 = True => @lem1731502)). Qed.
Lemma lem1731505 : term2525 = True.
Proof. exact (EQ_MP (@lem1731504) (@lem1731502)). Qed.
Lemma lem1731506 : term1117 = True.
Proof. exact (TRANS (@lem1731501) (@lem1731505)). Qed.
Lemma lem1731507 : True = term1117.
Proof. exact (SYM (@lem1731506)). Qed.
Lemma lem1731508 : term1117.
Proof. exact (EQ_MP (@lem1731507) (@lem0)). Qed.
Lemma lem1731509 (x : real) (h1 : term1332 x) : term2530 x.
Proof. exact (conj (@lem1731508) (@lem1731471 x h1)). Qed.
Lemma lem1731511 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1731512 (x : real) : term2532 x.
Proof. exact (@lem1731511 term24 (term176 x)). Qed.
Lemma lem1731513 (x : real) (h1 : term1332 x) : term2533 x.
Proof. exact (@lem1731512 x (@lem1731509 x h1)). Qed.
Lemma lem1731514 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1731515 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731516 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1731515) (@lem1731514 x)). Qed.
Lemma lem1731517 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731518 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1731516 x) (@lem1731517)). Qed.
Lemma lem1731519 (x : real) (h1 : term1332 x) : term179 x.
Proof. exact (EQ_MP (@lem1731518 x) (@lem1731513 x h1)). Qed.
Lemma lem1731520 (x : real) (h1 : term1332 x) : term2536 x.
Proof. exact (conj (@lem1731519 x h1) (@lem1731498 x h1)). Qed.
Lemma lem1731522 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1731523 (x : real) : term2538 x.
Proof. exact (@lem1731522 (term176 x) x). Qed.
Lemma lem1731524 (x : real) (h1 : term1332 x) : term2539 x.
Proof. exact (@lem1731523 x (@lem1731520 x h1)). Qed.
Lemma lem1731525 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1731527 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1731528 : term1261 = term76.
Proof. exact (@lem1731527 term185). Qed.
Lemma lem1731529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1731530 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1731529) (@lem1731528)). Qed.
Lemma lem1731531 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1731532 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1731530) (@lem1731531 x)). Qed.
Lemma lem1731533 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1731525 x) (@lem1731532 x)). Qed.
Lemma lem1731534 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1731535 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1731533 x) (@lem1731534 x)). Qed.
Lemma lem1731536 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731537 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1731536) (@lem1731535 x)). Qed.
Lemma lem1731538 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731539 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1731537 x) (@lem1731538)). Qed.
Lemma lem1731540 (x : real) (h1 : term1332 x) : term897.
Proof. exact (EQ_MP (@lem1731539 x) (@lem1731524 x h1)). Qed.
Lemma lem1731542 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731543 : term897 = term2523.
Proof. exact (@lem1731542 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731544 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731545 : term897 = False.
Proof. exact (TRANS (@lem1731543) (@lem1731544)). Qed.
Lemma lem1731546 (x : real) (h1 : term1332 x) : False.
Proof. exact (EQ_MP (@lem1731545) (@lem1731540 x h1)). Qed.
Lemma lem1731547 (x : real) (h1 : term1334 x) : False.
Proof. exact (or_elim (@lem1731441 x h1) (fun h0 : term1318 x => @lem1731462 x h0) (fun h0 : term1332 x => @lem1731546 x h0)). Qed.
Lemma lem1731548 (x : real) (h1 : term1348 x) : term1348 x.
Proof. exact (h1). Qed.
Lemma lem1731549 (x : real) (h1 : term1348 x) : term1346 x.
Proof. exact (proj2 (@lem1731548 x h1)). Qed.
Lemma lem1731553 (x : real) (h1 : term1348 x) : term1345 x.
Proof. exact (proj2 (@lem1731549 x h1)). Qed.
Lemma lem1731555 (x : real) (h1 : term1348 x) : term1344 x.
Proof. exact (proj2 (@lem1731553 x h1)). Qed.
Lemma lem1731559 (x : real) (h1 : term1348 x) : term1343.
Proof. exact (proj2 (@lem1731555 x h1)). Qed.
Lemma lem1731561 (x : real) (h1 : term1348 x) : term936.
Proof. exact (proj2 (@lem1731559 x h1)). Qed.
Lemma lem1731564 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731565 : term936 = False.
Proof. exact (@lem1731564 term923 (NUMERAL 0)). Qed.
Lemma lem1731566 (x : real) (h1 : term1348 x) : False.
Proof. exact (EQ_MP (@lem1731565) (@lem1731561 x h1)). Qed.
Lemma lem1731567 (x : real) (h1 : term1351 x) : False.
Proof. exact (or_elim (@lem1731440 x h1) (fun h0 : term1334 x => @lem1731547 x h0) (fun h0 : term1348 x => @lem1731566 x h0)). Qed.
Lemma lem1731568 (x : real) (h1 : term1353 x) : False.
Proof. exact (or_elim (@lem1731309 x h1) (fun h0 : term1292 x => @lem1731439 x h0) (fun h0 : term1351 x => @lem1731567 x h0)). Qed.
Lemma lem1731569 (x : real) (h1 : term1355 x) : False.
Proof. exact (or_elim (@lem1731042 x h1) (fun h0 : term1218 x => @lem1731308 x h0) (fun h0 : term1353 x => @lem1731568 x h0)). Qed.
Lemma lem1731570 (x : real) (h1 : term1723 x) : term1723 x.
Proof. exact (h1). Qed.
Lemma lem1731571 (x : real) (h1 : term1624 x) : term1624 x.
Proof. exact (h1). Qed.
Lemma lem1731572 (x : real) (h1 : term1465 x) : term1465 x.
Proof. exact (h1). Qed.
Lemma lem1731573 (x : real) (h1 : term1438 x) : term1438 x.
Proof. exact (h1). Qed.
Lemma lem1731574 (x : real) (h1 : term1436 x) : term1436 x.
Proof. exact (h1). Qed.
Lemma lem1731575 (x : real) (h1 : term1428 x) : term1428 x.
Proof. exact (h1). Qed.
Lemma lem1731576 (x : real) (h1 : term1428 x) : term1427 x.
Proof. exact (proj2 (@lem1731575 x h1)). Qed.
Lemma lem1731578 (x : real) (h1 : term1428 x) : term1426 x.
Proof. exact (proj2 (@lem1731576 x h1)). Qed.
Lemma lem1731580 (x : real) (h1 : term1428 x) : term1424 x.
Proof. exact (proj2 (@lem1731578 x h1)). Qed.
Lemma lem1731584 (x : real) (h1 : term1428 x) : term966 x.
Proof. exact (proj2 (@lem1731580 x h1)). Qed.
Lemma lem1731586 (x : real) (h1 : term1428 x) : term899 x.
Proof. exact (proj2 (@lem1731584 x h1)). Qed.
Lemma lem1731588 (x : real) (h1 : term1428 x) : term897.
Proof. exact (proj2 (@lem1731586 x h1)). Qed.
Lemma lem1731591 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731592 : term897 = term2523.
Proof. exact (@lem1731591 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731593 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731594 : term897 = False.
Proof. exact (TRANS (@lem1731592) (@lem1731593)). Qed.
Lemma lem1731595 (x : real) (h1 : term1428 x) : False.
Proof. exact (EQ_MP (@lem1731594) (@lem1731588 x h1)). Qed.
Lemma lem1731596 (x : real) (h1 : term1434 x) : term1434 x.
Proof. exact (h1). Qed.
Lemma lem1731597 (x : real) (h1 : term1434 x) : term1433 x.
Proof. exact (proj2 (@lem1731596 x h1)). Qed.
Lemma lem1731599 (x : real) (h1 : term1434 x) : term1432 x.
Proof. exact (proj2 (@lem1731597 x h1)). Qed.
Lemma lem1731601 (x : real) (h1 : term1434 x) : term1430 x.
Proof. exact (proj2 (@lem1731599 x h1)). Qed.
Lemma lem1731605 (x : real) (h1 : term1434 x) : term974 x.
Proof. exact (proj2 (@lem1731601 x h1)). Qed.
Lemma lem1731607 (x : real) (h1 : term1434 x) : term938 x.
Proof. exact (proj2 (@lem1731605 x h1)). Qed.
Lemma lem1731609 (x : real) (h1 : term1434 x) : term936.
Proof. exact (proj2 (@lem1731607 x h1)). Qed.
Lemma lem1731612 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731613 : term936 = False.
Proof. exact (@lem1731612 term923 (NUMERAL 0)). Qed.
Lemma lem1731614 (x : real) (h1 : term1434 x) : False.
Proof. exact (EQ_MP (@lem1731613) (@lem1731609 x h1)). Qed.
Lemma lem1731615 (x : real) (h1 : term1436 x) : False.
Proof. exact (or_elim (@lem1731574 x h1) (fun h0 : term1428 x => @lem1731595 x h0) (fun h0 : term1434 x => @lem1731614 x h0)). Qed.
Lemma lem1731616 (x : real) (h1 : term1407 x) : term1407 x.
Proof. exact (h1). Qed.
Lemma lem1731617 (x : real) (h1 : term1399 x) : term1399 x.
Proof. exact (h1). Qed.
Lemma lem1731618 (x : real) (h1 : term1399 x) : term1398 x.
Proof. exact (proj2 (@lem1731617 x h1)). Qed.
Lemma lem1731620 (x : real) (h1 : term1399 x) : term1397 x.
Proof. exact (proj2 (@lem1731618 x h1)). Qed.
Lemma lem1731622 (x : real) (h1 : term1399 x) : term1395 x.
Proof. exact (proj2 (@lem1731620 x h1)). Qed.
Lemma lem1731626 (x : real) (h1 : term1399 x) : term901 x.
Proof. exact (proj2 (@lem1731622 x h1)). Qed.
Lemma lem1731628 (x : real) (h1 : term1399 x) : term899 x.
Proof. exact (proj2 (@lem1731626 x h1)). Qed.
Lemma lem1731630 (x : real) (h1 : term1399 x) : term897.
Proof. exact (proj2 (@lem1731628 x h1)). Qed.
Lemma lem1731633 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731634 : term897 = term2523.
Proof. exact (@lem1731633 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731635 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731636 : term897 = False.
Proof. exact (TRANS (@lem1731634) (@lem1731635)). Qed.
Lemma lem1731637 (x : real) (h1 : term1399 x) : False.
Proof. exact (EQ_MP (@lem1731636) (@lem1731630 x h1)). Qed.
Lemma lem1731638 (x : real) (h1 : term1405 x) : term1405 x.
Proof. exact (h1). Qed.
Lemma lem1731639 (x : real) (h1 : term1405 x) : term1404 x.
Proof. exact (proj2 (@lem1731638 x h1)). Qed.
Lemma lem1731641 (x : real) (h1 : term1405 x) : term1403 x.
Proof. exact (proj2 (@lem1731639 x h1)). Qed.
Lemma lem1731643 (x : real) (h1 : term1405 x) : term1401 x.
Proof. exact (proj2 (@lem1731641 x h1)). Qed.
Lemma lem1731647 (x : real) (h1 : term1405 x) : term940 x.
Proof. exact (proj2 (@lem1731643 x h1)). Qed.
Lemma lem1731649 (x : real) (h1 : term1405 x) : term938 x.
Proof. exact (proj2 (@lem1731647 x h1)). Qed.
Lemma lem1731651 (x : real) (h1 : term1405 x) : term936.
Proof. exact (proj2 (@lem1731649 x h1)). Qed.
Lemma lem1731654 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731655 : term936 = False.
Proof. exact (@lem1731654 term923 (NUMERAL 0)). Qed.
Lemma lem1731656 (x : real) (h1 : term1405 x) : False.
Proof. exact (EQ_MP (@lem1731655) (@lem1731651 x h1)). Qed.
Lemma lem1731657 (x : real) (h1 : term1407 x) : False.
Proof. exact (or_elim (@lem1731616 x h1) (fun h0 : term1399 x => @lem1731637 x h0) (fun h0 : term1405 x => @lem1731656 x h0)). Qed.
Lemma lem1731658 (x : real) (h1 : term1438 x) : False.
Proof. exact (or_elim (@lem1731573 x h1) (fun h0 : term1436 x => @lem1731615 x h0) (fun h0 : term1407 x => @lem1731657 x h0)). Qed.
Lemma lem1731659 (x : real) (h1 : term1462 x) : term1462 x.
Proof. exact (h1). Qed.
Lemma lem1731660 (x : real) (h1 : term1452 x) : term1452 x.
Proof. exact (h1). Qed.
Lemma lem1731661 (x : real) (h1 : term1452 x) : term1450 x.
Proof. exact (proj2 (@lem1731660 x h1)). Qed.
Lemma lem1731663 (x : real) (h1 : term1452 x) : term1457 x.
Proof. exact (proj2 (@lem1731661 x h1)). Qed.
Lemma lem1731667 (x : real) (h1 : term1452 x) : term1029 x.
Proof. exact (proj2 (@lem1731663 x h1)). Qed.
Lemma lem1731669 (x : real) (h1 : term1452 x) : term1001 x.
Proof. exact (proj2 (@lem1731667 x h1)). Qed.
Lemma lem1731671 (x : real) (h1 : term1452 x) : term1000.
Proof. exact (proj2 (@lem1731669 x h1)). Qed.
Lemma lem1731674 (x : real) (h1 : term1452 x) : term897.
Proof. exact (proj1 (@lem1731671 x h1)). Qed.
Lemma lem1731676 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731677 : term897 = term2523.
Proof. exact (@lem1731676 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731678 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731679 : term897 = False.
Proof. exact (TRANS (@lem1731677) (@lem1731678)). Qed.
Lemma lem1731680 (x : real) (h1 : term1452 x) : False.
Proof. exact (EQ_MP (@lem1731679) (@lem1731674 x h1)). Qed.
Lemma lem1731681 (x : real) (h1 : term1461 x) : term1461 x.
Proof. exact (h1). Qed.
Lemma lem1731682 (x : real) (h1 : term1461 x) : term1460 x.
Proof. exact (proj2 (@lem1731681 x h1)). Qed.
Lemma lem1731684 (x : real) (h1 : term1461 x) : term1459 x.
Proof. exact (proj2 (@lem1731682 x h1)). Qed.
Lemma lem1731688 (x : real) (h1 : term1461 x) : term1032 x.
Proof. exact (proj2 (@lem1731684 x h1)). Qed.
Lemma lem1731690 (x : real) (h1 : term1461 x) : term1001 x.
Proof. exact (proj2 (@lem1731688 x h1)). Qed.
Lemma lem1731692 (x : real) (h1 : term1461 x) : term1000.
Proof. exact (proj2 (@lem1731690 x h1)). Qed.
Lemma lem1731695 (x : real) (h1 : term1461 x) : term897.
Proof. exact (proj1 (@lem1731692 x h1)). Qed.
Lemma lem1731697 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731698 : term897 = term2523.
Proof. exact (@lem1731697 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731699 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731700 : term897 = False.
Proof. exact (TRANS (@lem1731698) (@lem1731699)). Qed.
Lemma lem1731701 (x : real) (h1 : term1461 x) : False.
Proof. exact (EQ_MP (@lem1731700) (@lem1731695 x h1)). Qed.
Lemma lem1731702 (x : real) (h1 : term1462 x) : False.
Proof. exact (or_elim (@lem1731659 x h1) (fun h0 : term1452 x => @lem1731680 x h0) (fun h0 : term1461 x => @lem1731701 x h0)). Qed.
Lemma lem1731703 (x : real) (h1 : term1465 x) : False.
Proof. exact (or_elim (@lem1731572 x h1) (fun h0 : term1438 x => @lem1731658 x h0) (fun h0 : term1462 x => @lem1731702 x h0)). Qed.
Lemma lem1731704 (x : real) (h1 : term1622 x) : term1622 x.
Proof. exact (h1). Qed.
Lemma lem1731705 (x : real) (h1 : term1579 x) : term1579 x.
Proof. exact (h1). Qed.
Lemma lem1731706 (x : real) (h1 : term1577 x) : term1577 x.
Proof. exact (h1). Qed.
Lemma lem1731707 (x : real) (h1 : term1571 x) : term1571 x.
Proof. exact (h1). Qed.
Lemma lem1731708 (x : real) (h1 : term1571 x) : term1570 x.
Proof. exact (proj2 (@lem1731707 x h1)). Qed.
Lemma lem1731710 (x : real) (h1 : term1571 x) : term1569 x.
Proof. exact (proj2 (@lem1731708 x h1)). Qed.
Lemma lem1731712 (x : real) (h1 : term1571 x) : term1567 x.
Proof. exact (proj2 (@lem1731710 x h1)). Qed.
Lemma lem1731716 (x : real) (h1 : term1571 x) : term1565 x.
Proof. exact (proj2 (@lem1731712 x h1)). Qed.
Lemma lem1731718 (x : real) (h1 : term1571 x) : term1525 x.
Proof. exact (proj2 (@lem1731716 x h1)). Qed.
Lemma lem1731720 (x : real) (h1 : term1571 x) : term915.
Proof. exact (proj2 (@lem1731718 x h1)). Qed.
Lemma lem1731723 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731724 : term915 = False.
Proof. exact (@lem1731723 term185 (NUMERAL 0)). Qed.
Lemma lem1731725 (x : real) (h1 : term1571 x) : False.
Proof. exact (EQ_MP (@lem1731724) (@lem1731720 x h1)). Qed.
Lemma lem1731726 (x : real) (h1 : term1575 x) : term1575 x.
Proof. exact (h1). Qed.
Lemma lem1731727 (x : real) (h1 : term1575 x) : term1570 x.
Proof. exact (proj2 (@lem1731726 x h1)). Qed.
Lemma lem1731729 (x : real) (h1 : term1575 x) : term1569 x.
Proof. exact (proj2 (@lem1731727 x h1)). Qed.
Lemma lem1731731 (x : real) (h1 : term1575 x) : term1567 x.
Proof. exact (proj2 (@lem1731729 x h1)). Qed.
Lemma lem1731735 (x : real) (h1 : term1575 x) : term1565 x.
Proof. exact (proj2 (@lem1731731 x h1)). Qed.
Lemma lem1731737 (x : real) (h1 : term1575 x) : term1525 x.
Proof. exact (proj2 (@lem1731735 x h1)). Qed.
Lemma lem1731739 (x : real) (h1 : term1575 x) : term915.
Proof. exact (proj2 (@lem1731737 x h1)). Qed.
Lemma lem1731742 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731743 : term915 = False.
Proof. exact (@lem1731742 term185 (NUMERAL 0)). Qed.
Lemma lem1731744 (x : real) (h1 : term1575 x) : False.
Proof. exact (EQ_MP (@lem1731743) (@lem1731739 x h1)). Qed.
Lemma lem1731745 (x : real) (h1 : term1577 x) : False.
Proof. exact (or_elim (@lem1731706 x h1) (fun h0 : term1571 x => @lem1731725 x h0) (fun h0 : term1575 x => @lem1731744 x h0)). Qed.
Lemma lem1731746 (x : real) (h1 : term1548 x) : term1548 x.
Proof. exact (h1). Qed.
Lemma lem1731747 (x : real) (h1 : term1533 x) : term1533 x.
Proof. exact (h1). Qed.
Lemma lem1731748 (x : real) (h1 : term1533 x) : term1532 x.
Proof. exact (proj2 (@lem1731747 x h1)). Qed.
Lemma lem1731750 (x : real) (h1 : term1533 x) : term1531 x.
Proof. exact (proj2 (@lem1731748 x h1)). Qed.
Lemma lem1731752 (x : real) (h1 : term1533 x) : term1529 x.
Proof. exact (proj2 (@lem1731750 x h1)). Qed.
Lemma lem1731756 (x : real) (h1 : term1533 x) : term1527 x.
Proof. exact (proj2 (@lem1731752 x h1)). Qed.
Lemma lem1731758 (x : real) (h1 : term1533 x) : term1525 x.
Proof. exact (proj2 (@lem1731756 x h1)). Qed.
Lemma lem1731760 (x : real) (h1 : term1533 x) : term915.
Proof. exact (proj2 (@lem1731758 x h1)). Qed.
Lemma lem1731763 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731764 : term915 = False.
Proof. exact (@lem1731763 term185 (NUMERAL 0)). Qed.
Lemma lem1731765 (x : real) (h1 : term1533 x) : False.
Proof. exact (EQ_MP (@lem1731764) (@lem1731760 x h1)). Qed.
Lemma lem1731766 (x : real) (h1 : term1546 x) : term1546 x.
Proof. exact (h1). Qed.
Lemma lem1731767 (x : real) (h1 : term1546 x) : term1532 x.
Proof. exact (proj2 (@lem1731766 x h1)). Qed.
Lemma lem1731769 (x : real) (h1 : term1546 x) : term1531 x.
Proof. exact (proj2 (@lem1731767 x h1)). Qed.
Lemma lem1731771 (x : real) (h1 : term1546 x) : term1529 x.
Proof. exact (proj2 (@lem1731769 x h1)). Qed.
Lemma lem1731775 (x : real) (h1 : term1546 x) : term1527 x.
Proof. exact (proj2 (@lem1731771 x h1)). Qed.
Lemma lem1731777 (x : real) (h1 : term1546 x) : term1525 x.
Proof. exact (proj2 (@lem1731775 x h1)). Qed.
Lemma lem1731779 (x : real) (h1 : term1546 x) : term915.
Proof. exact (proj2 (@lem1731777 x h1)). Qed.
Lemma lem1731782 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1731783 : term915 = False.
Proof. exact (@lem1731782 term185 (NUMERAL 0)). Qed.
Lemma lem1731784 (x : real) (h1 : term1546 x) : False.
Proof. exact (EQ_MP (@lem1731783) (@lem1731779 x h1)). Qed.
Lemma lem1731785 (x : real) (h1 : term1548 x) : False.
Proof. exact (or_elim (@lem1731746 x h1) (fun h0 : term1533 x => @lem1731765 x h0) (fun h0 : term1546 x => @lem1731784 x h0)). Qed.
Lemma lem1731786 (x : real) (h1 : term1579 x) : False.
Proof. exact (or_elim (@lem1731705 x h1) (fun h0 : term1577 x => @lem1731745 x h0) (fun h0 : term1548 x => @lem1731785 x h0)). Qed.
Lemma lem1731787 (x : real) (h1 : term1619 x) : term1619 x.
Proof. exact (h1). Qed.
Lemma lem1731788 (x : real) (h1 : term1604 x) : term1604 x.
Proof. exact (h1). Qed.
Lemma lem1731789 (x : real) (h1 : term1604 x) : term1602 x.
Proof. exact (proj2 (@lem1731788 x h1)). Qed.
Lemma lem1731791 (x : real) (h1 : term1604 x) : term1612 x.
Proof. exact (proj2 (@lem1731789 x h1)). Qed.
Lemma lem1731792 (x : real) (h1 : term1604 x) : term810 x.
Proof. exact (proj1 (@lem1731789 x h1)). Qed.
Lemma lem1731794 (x : real) (h1 : term1604 x) : term179 x.
Proof. exact (proj1 (@lem1731792 x h1)). Qed.
Lemma lem1731796 (x : real) (h1 : term1604 x) : term326 x.
Proof. exact (proj1 (@lem1731791 x h1)). Qed.
Lemma lem1731804 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731805 : term1117 = term2525.
Proof. exact (@lem1731804 (NUMERAL 0) term185). Qed.
Lemma lem1731806 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731807 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731808 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731807 h1) (fun h1 : term2525 = True => @lem1731806)). Qed.
Lemma lem1731809 : term2525 = True.
Proof. exact (EQ_MP (@lem1731808) (@lem1731806)). Qed.
Lemma lem1731810 : term1117 = True.
Proof. exact (TRANS (@lem1731805) (@lem1731809)). Qed.
Lemma lem1731811 : True = term1117.
Proof. exact (SYM (@lem1731810)). Qed.
Lemma lem1731812 : term1117.
Proof. exact (EQ_MP (@lem1731811) (@lem0)). Qed.
Lemma lem1731813 (x : real) (h1 : term1604 x) : term2527 x.
Proof. exact (conj (@lem1731812) (@lem1731796 x h1)). Qed.
Lemma lem1731815 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1731816 (x : real) : term2529 x.
Proof. exact (@lem1731815 term24 x). Qed.
Lemma lem1731817 (x : real) (h1 : term1604 x) : term1223 x.
Proof. exact (@lem1731816 x (@lem1731813 x h1)). Qed.
Lemma lem1731818 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1731819 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1731820 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1731819) (@lem1731818 x)). Qed.
Lemma lem1731821 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731822 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1731820 x) (@lem1731821)). Qed.
Lemma lem1731823 (x : real) (h1 : term1604 x) : term326 x.
Proof. exact (EQ_MP (@lem1731822 x) (@lem1731817 x h1)). Qed.
Lemma lem1731825 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731826 : term1117 = term2525.
Proof. exact (@lem1731825 (NUMERAL 0) term185). Qed.
Lemma lem1731827 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731828 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731829 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731828 h1) (fun h1 : term2525 = True => @lem1731827)). Qed.
Lemma lem1731830 : term2525 = True.
Proof. exact (EQ_MP (@lem1731829) (@lem1731827)). Qed.
Lemma lem1731831 : term1117 = True.
Proof. exact (TRANS (@lem1731826) (@lem1731830)). Qed.
Lemma lem1731832 : True = term1117.
Proof. exact (SYM (@lem1731831)). Qed.
Lemma lem1731833 : term1117.
Proof. exact (EQ_MP (@lem1731832) (@lem0)). Qed.
Lemma lem1731834 (x : real) (h1 : term1604 x) : term2530 x.
Proof. exact (conj (@lem1731833) (@lem1731794 x h1)). Qed.
Lemma lem1731836 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1731837 (x : real) : term2532 x.
Proof. exact (@lem1731836 term24 (term176 x)). Qed.
Lemma lem1731838 (x : real) (h1 : term1604 x) : term2533 x.
Proof. exact (@lem1731837 x (@lem1731834 x h1)). Qed.
Lemma lem1731839 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1731840 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731841 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1731840) (@lem1731839 x)). Qed.
Lemma lem1731842 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731843 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1731841 x) (@lem1731842)). Qed.
Lemma lem1731844 (x : real) (h1 : term1604 x) : term179 x.
Proof. exact (EQ_MP (@lem1731843 x) (@lem1731838 x h1)). Qed.
Lemma lem1731845 (x : real) (h1 : term1604 x) : term2536 x.
Proof. exact (conj (@lem1731844 x h1) (@lem1731823 x h1)). Qed.
Lemma lem1731847 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1731848 (x : real) : term2538 x.
Proof. exact (@lem1731847 (term176 x) x). Qed.
Lemma lem1731849 (x : real) (h1 : term1604 x) : term2539 x.
Proof. exact (@lem1731848 x (@lem1731845 x h1)). Qed.
Lemma lem1731850 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1731852 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1731853 : term1261 = term76.
Proof. exact (@lem1731852 term185). Qed.
Lemma lem1731854 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1731855 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1731854) (@lem1731853)). Qed.
Lemma lem1731856 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1731857 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1731855) (@lem1731856 x)). Qed.
Lemma lem1731858 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1731850 x) (@lem1731857 x)). Qed.
Lemma lem1731859 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1731860 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1731858 x) (@lem1731859 x)). Qed.
Lemma lem1731861 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731862 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1731861) (@lem1731860 x)). Qed.
Lemma lem1731863 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731864 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1731862 x) (@lem1731863)). Qed.
Lemma lem1731865 (x : real) (h1 : term1604 x) : term897.
Proof. exact (EQ_MP (@lem1731864 x) (@lem1731849 x h1)). Qed.
Lemma lem1731867 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731868 : term897 = term2523.
Proof. exact (@lem1731867 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731869 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731870 : term897 = False.
Proof. exact (TRANS (@lem1731868) (@lem1731869)). Qed.
Lemma lem1731871 (x : real) (h1 : term1604 x) : False.
Proof. exact (EQ_MP (@lem1731870) (@lem1731865 x h1)). Qed.
Lemma lem1731872 (x : real) (h1 : term1618 x) : term1618 x.
Proof. exact (h1). Qed.
Lemma lem1731873 (x : real) (h1 : term1618 x) : term1617 x.
Proof. exact (proj2 (@lem1731872 x h1)). Qed.
Lemma lem1731875 (x : real) (h1 : term1618 x) : term1616 x.
Proof. exact (proj2 (@lem1731873 x h1)). Qed.
Lemma lem1731879 (x : real) (h1 : term1618 x) : term1614 x.
Proof. exact (proj2 (@lem1731875 x h1)). Qed.
Lemma lem1731880 (x : real) (h1 : term1618 x) : term326 x.
Proof. exact (proj1 (@lem1731875 x h1)). Qed.
Lemma lem1731882 (x : real) (h1 : term1618 x) : term179 x.
Proof. exact (proj1 (@lem1731879 x h1)). Qed.
Lemma lem1731888 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731889 : term1117 = term2525.
Proof. exact (@lem1731888 (NUMERAL 0) term185). Qed.
Lemma lem1731890 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731891 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731892 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731891 h1) (fun h1 : term2525 = True => @lem1731890)). Qed.
Lemma lem1731893 : term2525 = True.
Proof. exact (EQ_MP (@lem1731892) (@lem1731890)). Qed.
Lemma lem1731894 : term1117 = True.
Proof. exact (TRANS (@lem1731889) (@lem1731893)). Qed.
Lemma lem1731895 : True = term1117.
Proof. exact (SYM (@lem1731894)). Qed.
Lemma lem1731896 : term1117.
Proof. exact (EQ_MP (@lem1731895) (@lem0)). Qed.
Lemma lem1731897 (x : real) (h1 : term1618 x) : term2527 x.
Proof. exact (conj (@lem1731896) (@lem1731880 x h1)). Qed.
Lemma lem1731899 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1731900 (x : real) : term2529 x.
Proof. exact (@lem1731899 term24 x). Qed.
Lemma lem1731901 (x : real) (h1 : term1618 x) : term1223 x.
Proof. exact (@lem1731900 x (@lem1731897 x h1)). Qed.
Lemma lem1731902 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1731903 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1731904 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1731903) (@lem1731902 x)). Qed.
Lemma lem1731905 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731906 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1731904 x) (@lem1731905)). Qed.
Lemma lem1731907 (x : real) (h1 : term1618 x) : term326 x.
Proof. exact (EQ_MP (@lem1731906 x) (@lem1731901 x h1)). Qed.
Lemma lem1731909 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731910 : term1117 = term2525.
Proof. exact (@lem1731909 (NUMERAL 0) term185). Qed.
Lemma lem1731911 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731912 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731913 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731912 h1) (fun h1 : term2525 = True => @lem1731911)). Qed.
Lemma lem1731914 : term2525 = True.
Proof. exact (EQ_MP (@lem1731913) (@lem1731911)). Qed.
Lemma lem1731915 : term1117 = True.
Proof. exact (TRANS (@lem1731910) (@lem1731914)). Qed.
Lemma lem1731916 : True = term1117.
Proof. exact (SYM (@lem1731915)). Qed.
Lemma lem1731917 : term1117.
Proof. exact (EQ_MP (@lem1731916) (@lem0)). Qed.
Lemma lem1731918 (x : real) (h1 : term1618 x) : term2530 x.
Proof. exact (conj (@lem1731917) (@lem1731882 x h1)). Qed.
Lemma lem1731920 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1731921 (x : real) : term2532 x.
Proof. exact (@lem1731920 term24 (term176 x)). Qed.
Lemma lem1731922 (x : real) (h1 : term1618 x) : term2533 x.
Proof. exact (@lem1731921 x (@lem1731918 x h1)). Qed.
Lemma lem1731923 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1731924 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731925 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1731924) (@lem1731923 x)). Qed.
Lemma lem1731926 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731927 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1731925 x) (@lem1731926)). Qed.
Lemma lem1731928 (x : real) (h1 : term1618 x) : term179 x.
Proof. exact (EQ_MP (@lem1731927 x) (@lem1731922 x h1)). Qed.
Lemma lem1731929 (x : real) (h1 : term1618 x) : term2536 x.
Proof. exact (conj (@lem1731928 x h1) (@lem1731907 x h1)). Qed.
Lemma lem1731931 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1731932 (x : real) : term2538 x.
Proof. exact (@lem1731931 (term176 x) x). Qed.
Lemma lem1731933 (x : real) (h1 : term1618 x) : term2539 x.
Proof. exact (@lem1731932 x (@lem1731929 x h1)). Qed.
Lemma lem1731934 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1731936 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1731937 : term1261 = term76.
Proof. exact (@lem1731936 term185). Qed.
Lemma lem1731938 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1731939 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1731938) (@lem1731937)). Qed.
Lemma lem1731940 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1731941 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1731939) (@lem1731940 x)). Qed.
Lemma lem1731942 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1731934 x) (@lem1731941 x)). Qed.
Lemma lem1731943 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1731944 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1731942 x) (@lem1731943 x)). Qed.
Lemma lem1731945 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1731946 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1731945) (@lem1731944 x)). Qed.
Lemma lem1731947 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731948 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1731946 x) (@lem1731947)). Qed.
Lemma lem1731949 (x : real) (h1 : term1618 x) : term897.
Proof. exact (EQ_MP (@lem1731948 x) (@lem1731933 x h1)). Qed.
Lemma lem1731951 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731952 : term897 = term2523.
Proof. exact (@lem1731951 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1731953 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1731954 : term897 = False.
Proof. exact (TRANS (@lem1731952) (@lem1731953)). Qed.
Lemma lem1731955 (x : real) (h1 : term1618 x) : False.
Proof. exact (EQ_MP (@lem1731954) (@lem1731949 x h1)). Qed.
Lemma lem1731956 (x : real) (h1 : term1619 x) : False.
Proof. exact (or_elim (@lem1731787 x h1) (fun h0 : term1604 x => @lem1731871 x h0) (fun h0 : term1618 x => @lem1731955 x h0)). Qed.
Lemma lem1731957 (x : real) (h1 : term1622 x) : False.
Proof. exact (or_elim (@lem1731704 x h1) (fun h0 : term1579 x => @lem1731786 x h0) (fun h0 : term1619 x => @lem1731956 x h0)). Qed.
Lemma lem1731958 (x : real) (h1 : term1624 x) : False.
Proof. exact (or_elim (@lem1731571 x h1) (fun h0 : term1465 x => @lem1731703 x h0) (fun h0 : term1622 x => @lem1731957 x h0)). Qed.
Lemma lem1731959 (x : real) (h1 : term1721 x) : term1721 x.
Proof. exact (h1). Qed.
Lemma lem1731960 (x : real) (h1 : term1658 x) : term1658 x.
Proof. exact (h1). Qed.
Lemma lem1731961 (x : real) (h1 : term1652 x) : term1652 x.
Proof. exact (h1). Qed.
Lemma lem1731962 (x : real) (h1 : term1646 x) : term1646 x.
Proof. exact (h1). Qed.
Lemma lem1731963 (x : real) (h1 : term1646 x) : term1645 x.
Proof. exact (proj2 (@lem1731962 x h1)). Qed.
Lemma lem1731965 (x : real) (h1 : term1646 x) : term1644 x.
Proof. exact (proj2 (@lem1731963 x h1)). Qed.
Lemma lem1731966 (x : real) (h1 : term1646 x) : term810 x.
Proof. exact (proj1 (@lem1731963 x h1)). Qed.
Lemma lem1731968 (x : real) (h1 : term1646 x) : term179 x.
Proof. exact (proj1 (@lem1731966 x h1)). Qed.
Lemma lem1731969 (x : real) (h1 : term1646 x) : term1254 x.
Proof. exact (proj2 (@lem1731965 x h1)). Qed.
Lemma lem1731972 (x : real) (h1 : term1646 x) : term1224 x.
Proof. exact (proj1 (@lem1731969 x h1)). Qed.
Lemma lem1731973 (x : real) (h1 : term1646 x) : term326 x.
Proof. exact (proj2 (@lem1731972 x h1)). Qed.
Lemma lem1731978 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1731979 : term1117 = term2525.
Proof. exact (@lem1731978 (NUMERAL 0) term185). Qed.
Lemma lem1731980 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1731981 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1731982 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1731981 h1) (fun h1 : term2525 = True => @lem1731980)). Qed.
Lemma lem1731983 : term2525 = True.
Proof. exact (EQ_MP (@lem1731982) (@lem1731980)). Qed.
Lemma lem1731984 : term1117 = True.
Proof. exact (TRANS (@lem1731979) (@lem1731983)). Qed.
Lemma lem1731985 : True = term1117.
Proof. exact (SYM (@lem1731984)). Qed.
Lemma lem1731986 : term1117.
Proof. exact (EQ_MP (@lem1731985) (@lem0)). Qed.
Lemma lem1731987 (x : real) (h1 : term1646 x) : term2527 x.
Proof. exact (conj (@lem1731986) (@lem1731973 x h1)). Qed.
Lemma lem1731989 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1731990 (x : real) : term2529 x.
Proof. exact (@lem1731989 term24 x). Qed.
Lemma lem1731991 (x : real) (h1 : term1646 x) : term1223 x.
Proof. exact (@lem1731990 x (@lem1731987 x h1)). Qed.
Lemma lem1731992 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1731993 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1731994 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1731993) (@lem1731992 x)). Qed.
Lemma lem1731995 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1731996 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1731994 x) (@lem1731995)). Qed.
Lemma lem1731997 (x : real) (h1 : term1646 x) : term326 x.
Proof. exact (EQ_MP (@lem1731996 x) (@lem1731991 x h1)). Qed.
Lemma lem1731999 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732000 : term1117 = term2525.
Proof. exact (@lem1731999 (NUMERAL 0) term185). Qed.
Lemma lem1732001 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732002 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732003 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732002 h1) (fun h1 : term2525 = True => @lem1732001)). Qed.
Lemma lem1732004 : term2525 = True.
Proof. exact (EQ_MP (@lem1732003) (@lem1732001)). Qed.
Lemma lem1732005 : term1117 = True.
Proof. exact (TRANS (@lem1732000) (@lem1732004)). Qed.
Lemma lem1732006 : True = term1117.
Proof. exact (SYM (@lem1732005)). Qed.
Lemma lem1732007 : term1117.
Proof. exact (EQ_MP (@lem1732006) (@lem0)). Qed.
Lemma lem1732008 (x : real) (h1 : term1646 x) : term2530 x.
Proof. exact (conj (@lem1732007) (@lem1731968 x h1)). Qed.
Lemma lem1732010 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1732011 (x : real) : term2532 x.
Proof. exact (@lem1732010 term24 (term176 x)). Qed.
Lemma lem1732012 (x : real) (h1 : term1646 x) : term2533 x.
Proof. exact (@lem1732011 x (@lem1732008 x h1)). Qed.
Lemma lem1732013 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1732014 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732015 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1732014) (@lem1732013 x)). Qed.
Lemma lem1732016 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732017 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1732015 x) (@lem1732016)). Qed.
Lemma lem1732018 (x : real) (h1 : term1646 x) : term179 x.
Proof. exact (EQ_MP (@lem1732017 x) (@lem1732012 x h1)). Qed.
Lemma lem1732019 (x : real) (h1 : term1646 x) : term2536 x.
Proof. exact (conj (@lem1732018 x h1) (@lem1731997 x h1)). Qed.
Lemma lem1732021 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1732022 (x : real) : term2538 x.
Proof. exact (@lem1732021 (term176 x) x). Qed.
Lemma lem1732023 (x : real) (h1 : term1646 x) : term2539 x.
Proof. exact (@lem1732022 x (@lem1732019 x h1)). Qed.
Lemma lem1732024 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1732026 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1732027 : term1261 = term76.
Proof. exact (@lem1732026 term185). Qed.
Lemma lem1732028 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1732029 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1732028) (@lem1732027)). Qed.
Lemma lem1732030 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1732031 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1732029) (@lem1732030 x)). Qed.
Lemma lem1732032 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1732024 x) (@lem1732031 x)). Qed.
Lemma lem1732033 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1732034 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1732032 x) (@lem1732033 x)). Qed.
Lemma lem1732035 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732036 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1732035) (@lem1732034 x)). Qed.
Lemma lem1732037 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732038 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1732036 x) (@lem1732037)). Qed.
Lemma lem1732039 (x : real) (h1 : term1646 x) : term897.
Proof. exact (EQ_MP (@lem1732038 x) (@lem1732023 x h1)). Qed.
Lemma lem1732041 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732042 : term897 = term2523.
Proof. exact (@lem1732041 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732043 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732044 : term897 = False.
Proof. exact (TRANS (@lem1732042) (@lem1732043)). Qed.
Lemma lem1732045 (x : real) (h1 : term1646 x) : False.
Proof. exact (EQ_MP (@lem1732044) (@lem1732039 x h1)). Qed.
Lemma lem1732046 (x : real) (h1 : term1650 x) : term1650 x.
Proof. exact (h1). Qed.
Lemma lem1732047 (x : real) (h1 : term1650 x) : term1649 x.
Proof. exact (proj2 (@lem1732046 x h1)). Qed.
Lemma lem1732049 (x : real) (h1 : term1650 x) : term1648 x.
Proof. exact (proj2 (@lem1732047 x h1)). Qed.
Lemma lem1732053 (x : real) (h1 : term1650 x) : term1268 x.
Proof. exact (proj2 (@lem1732049 x h1)). Qed.
Lemma lem1732055 (x : real) (h1 : term1650 x) : term899 x.
Proof. exact (proj2 (@lem1732053 x h1)). Qed.
Lemma lem1732059 (x : real) (h1 : term1650 x) : term897.
Proof. exact (proj2 (@lem1732055 x h1)). Qed.
Lemma lem1732062 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732063 : term897 = term2523.
Proof. exact (@lem1732062 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732064 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732065 : term897 = False.
Proof. exact (TRANS (@lem1732063) (@lem1732064)). Qed.
Lemma lem1732066 (x : real) (h1 : term1650 x) : False.
Proof. exact (EQ_MP (@lem1732065) (@lem1732059 x h1)). Qed.
Lemma lem1732067 (x : real) (h1 : term1652 x) : False.
Proof. exact (or_elim (@lem1731961 x h1) (fun h0 : term1646 x => @lem1732045 x h0) (fun h0 : term1650 x => @lem1732066 x h0)). Qed.
Lemma lem1732068 (x : real) (h1 : term1655 x) : term1655 x.
Proof. exact (h1). Qed.
Lemma lem1732069 (x : real) (h1 : term1655 x) : term1653 x.
Proof. exact (proj2 (@lem1732068 x h1)). Qed.
Lemma lem1732073 (x : real) (h1 : term1655 x) : term1286 x.
Proof. exact (proj2 (@lem1732069 x h1)). Qed.
Lemma lem1732075 (x : real) (h1 : term1655 x) : term1285 x.
Proof. exact (proj2 (@lem1732073 x h1)). Qed.
Lemma lem1732079 (x : real) (h1 : term1655 x) : term1284.
Proof. exact (proj2 (@lem1732075 x h1)). Qed.
Lemma lem1732081 (x : real) (h1 : term1655 x) : term897.
Proof. exact (proj2 (@lem1732079 x h1)). Qed.
Lemma lem1732084 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732085 : term897 = term2523.
Proof. exact (@lem1732084 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732086 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732087 : term897 = False.
Proof. exact (TRANS (@lem1732085) (@lem1732086)). Qed.
Lemma lem1732088 (x : real) (h1 : term1655 x) : False.
Proof. exact (EQ_MP (@lem1732087) (@lem1732081 x h1)). Qed.
Lemma lem1732089 (x : real) (h1 : term1658 x) : False.
Proof. exact (or_elim (@lem1731960 x h1) (fun h0 : term1652 x => @lem1732067 x h0) (fun h0 : term1655 x => @lem1732088 x h0)). Qed.
Lemma lem1732090 (x : real) (h1 : term1719 x) : term1719 x.
Proof. exact (h1). Qed.
Lemma lem1732091 (x : real) (h1 : term1703 x) : term1703 x.
Proof. exact (h1). Qed.
Lemma lem1732092 (x : real) (h1 : term1691 x) : term1691 x.
Proof. exact (h1). Qed.
Lemma lem1732093 (x : real) (h1 : term1691 x) : term1690 x.
Proof. exact (proj2 (@lem1732092 x h1)). Qed.
Lemma lem1732095 (x : real) (h1 : term1691 x) : term1689 x.
Proof. exact (proj2 (@lem1732093 x h1)). Qed.
Lemma lem1732096 (x : real) (h1 : term1691 x) : term810 x.
Proof. exact (proj1 (@lem1732093 x h1)). Qed.
Lemma lem1732098 (x : real) (h1 : term1691 x) : term179 x.
Proof. exact (proj1 (@lem1732096 x h1)). Qed.
Lemma lem1732099 (x : real) (h1 : term1691 x) : term1687 x.
Proof. exact (proj2 (@lem1732095 x h1)). Qed.
Lemma lem1732102 (x : real) (h1 : term1691 x) : term1224 x.
Proof. exact (proj1 (@lem1732099 x h1)). Qed.
Lemma lem1732103 (x : real) (h1 : term1691 x) : term326 x.
Proof. exact (proj2 (@lem1732102 x h1)). Qed.
Lemma lem1732108 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732109 : term1117 = term2525.
Proof. exact (@lem1732108 (NUMERAL 0) term185). Qed.
Lemma lem1732110 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732111 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732112 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732111 h1) (fun h1 : term2525 = True => @lem1732110)). Qed.
Lemma lem1732113 : term2525 = True.
Proof. exact (EQ_MP (@lem1732112) (@lem1732110)). Qed.
Lemma lem1732114 : term1117 = True.
Proof. exact (TRANS (@lem1732109) (@lem1732113)). Qed.
Lemma lem1732115 : True = term1117.
Proof. exact (SYM (@lem1732114)). Qed.
Lemma lem1732116 : term1117.
Proof. exact (EQ_MP (@lem1732115) (@lem0)). Qed.
Lemma lem1732117 (x : real) (h1 : term1691 x) : term2527 x.
Proof. exact (conj (@lem1732116) (@lem1732103 x h1)). Qed.
Lemma lem1732119 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1732120 (x : real) : term2529 x.
Proof. exact (@lem1732119 term24 x). Qed.
Lemma lem1732121 (x : real) (h1 : term1691 x) : term1223 x.
Proof. exact (@lem1732120 x (@lem1732117 x h1)). Qed.
Lemma lem1732122 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1732123 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1732124 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1732123) (@lem1732122 x)). Qed.
Lemma lem1732125 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732126 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1732124 x) (@lem1732125)). Qed.
Lemma lem1732127 (x : real) (h1 : term1691 x) : term326 x.
Proof. exact (EQ_MP (@lem1732126 x) (@lem1732121 x h1)). Qed.
Lemma lem1732129 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732130 : term1117 = term2525.
Proof. exact (@lem1732129 (NUMERAL 0) term185). Qed.
Lemma lem1732131 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732132 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732133 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732132 h1) (fun h1 : term2525 = True => @lem1732131)). Qed.
Lemma lem1732134 : term2525 = True.
Proof. exact (EQ_MP (@lem1732133) (@lem1732131)). Qed.
Lemma lem1732135 : term1117 = True.
Proof. exact (TRANS (@lem1732130) (@lem1732134)). Qed.
Lemma lem1732136 : True = term1117.
Proof. exact (SYM (@lem1732135)). Qed.
Lemma lem1732137 : term1117.
Proof. exact (EQ_MP (@lem1732136) (@lem0)). Qed.
Lemma lem1732138 (x : real) (h1 : term1691 x) : term2530 x.
Proof. exact (conj (@lem1732137) (@lem1732098 x h1)). Qed.
Lemma lem1732140 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1732141 (x : real) : term2532 x.
Proof. exact (@lem1732140 term24 (term176 x)). Qed.
Lemma lem1732142 (x : real) (h1 : term1691 x) : term2533 x.
Proof. exact (@lem1732141 x (@lem1732138 x h1)). Qed.
Lemma lem1732143 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1732144 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732145 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1732144) (@lem1732143 x)). Qed.
Lemma lem1732146 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732147 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1732145 x) (@lem1732146)). Qed.
Lemma lem1732148 (x : real) (h1 : term1691 x) : term179 x.
Proof. exact (EQ_MP (@lem1732147 x) (@lem1732142 x h1)). Qed.
Lemma lem1732149 (x : real) (h1 : term1691 x) : term2536 x.
Proof. exact (conj (@lem1732148 x h1) (@lem1732127 x h1)). Qed.
Lemma lem1732151 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1732152 (x : real) : term2538 x.
Proof. exact (@lem1732151 (term176 x) x). Qed.
Lemma lem1732153 (x : real) (h1 : term1691 x) : term2539 x.
Proof. exact (@lem1732152 x (@lem1732149 x h1)). Qed.
Lemma lem1732154 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1732156 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1732157 : term1261 = term76.
Proof. exact (@lem1732156 term185). Qed.
Lemma lem1732158 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1732159 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1732158) (@lem1732157)). Qed.
Lemma lem1732160 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1732161 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1732159) (@lem1732160 x)). Qed.
Lemma lem1732162 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1732154 x) (@lem1732161 x)). Qed.
Lemma lem1732163 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1732164 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1732162 x) (@lem1732163 x)). Qed.
Lemma lem1732165 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732166 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1732165) (@lem1732164 x)). Qed.
Lemma lem1732167 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732168 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1732166 x) (@lem1732167)). Qed.
Lemma lem1732169 (x : real) (h1 : term1691 x) : term897.
Proof. exact (EQ_MP (@lem1732168 x) (@lem1732153 x h1)). Qed.
Lemma lem1732171 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732172 : term897 = term2523.
Proof. exact (@lem1732171 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732173 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732174 : term897 = False.
Proof. exact (TRANS (@lem1732172) (@lem1732173)). Qed.
Lemma lem1732175 (x : real) (h1 : term1691 x) : False.
Proof. exact (EQ_MP (@lem1732174) (@lem1732169 x h1)). Qed.
Lemma lem1732176 (x : real) (h1 : term1701 x) : term1701 x.
Proof. exact (h1). Qed.
Lemma lem1732178 (x : real) (h1 : term1701 x) : term897.
Proof. exact (proj1 (@lem1732176 x h1)). Qed.
Lemma lem1732192 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732193 : term897 = term2523.
Proof. exact (@lem1732192 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732194 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732195 : term897 = False.
Proof. exact (TRANS (@lem1732193) (@lem1732194)). Qed.
Lemma lem1732196 (x : real) (h1 : term1701 x) : False.
Proof. exact (EQ_MP (@lem1732195) (@lem1732178 x h1)). Qed.
Lemma lem1732197 (x : real) (h1 : term1703 x) : False.
Proof. exact (or_elim (@lem1732091 x h1) (fun h0 : term1691 x => @lem1732175 x h0) (fun h0 : term1701 x => @lem1732196 x h0)). Qed.
Lemma lem1732198 (x : real) (h1 : term1716 x) : term1716 x.
Proof. exact (h1). Qed.
Lemma lem1732199 (x : real) (h1 : term1716 x) : term1714 x.
Proof. exact (proj2 (@lem1732198 x h1)). Qed.
Lemma lem1732203 (x : real) (h1 : term1716 x) : term1713 x.
Proof. exact (proj2 (@lem1732199 x h1)). Qed.
Lemma lem1732205 (x : real) (h1 : term1716 x) : term1712 x.
Proof. exact (proj2 (@lem1732203 x h1)). Qed.
Lemma lem1732209 (x : real) (h1 : term1716 x) : term1711.
Proof. exact (proj2 (@lem1732205 x h1)). Qed.
Lemma lem1732211 (x : real) (h1 : term1716 x) : term915.
Proof. exact (proj2 (@lem1732209 x h1)). Qed.
Lemma lem1732214 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732215 : term915 = False.
Proof. exact (@lem1732214 term185 (NUMERAL 0)). Qed.
Lemma lem1732216 (x : real) (h1 : term1716 x) : False.
Proof. exact (EQ_MP (@lem1732215) (@lem1732211 x h1)). Qed.
Lemma lem1732217 (x : real) (h1 : term1719 x) : False.
Proof. exact (or_elim (@lem1732090 x h1) (fun h0 : term1703 x => @lem1732197 x h0) (fun h0 : term1716 x => @lem1732216 x h0)). Qed.
Lemma lem1732218 (x : real) (h1 : term1721 x) : False.
Proof. exact (or_elim (@lem1731959 x h1) (fun h0 : term1658 x => @lem1732089 x h0) (fun h0 : term1719 x => @lem1732217 x h0)). Qed.
Lemma lem1732219 (x : real) (h1 : term1723 x) : False.
Proof. exact (or_elim (@lem1731570 x h1) (fun h0 : term1624 x => @lem1731958 x h0) (fun h0 : term1721 x => @lem1732218 x h0)). Qed.
Lemma lem1732220 (x : real) (h1 : term1725 x) : False.
Proof. exact (or_elim (@lem1731041 x h1) (fun h0 : term1355 x => @lem1731569 x h0) (fun h0 : term1723 x => @lem1732219 x h0)). Qed.
Lemma lem1732221 (x : real) (h1 : term2519 x) : term2519 x.
Proof. exact (h1). Qed.
Lemma lem1732222 (x : real) (h1 : term2136 x) : term2136 x.
Proof. exact (h1). Qed.
Lemma lem1732223 (x : real) (h1 : term1919 x) : term1919 x.
Proof. exact (h1). Qed.
Lemma lem1732224 (x : real) (h1 : term1823 x) : term1823 x.
Proof. exact (h1). Qed.
Lemma lem1732225 (x : real) (h1 : term1800 x) : term1800 x.
Proof. exact (h1). Qed.
Lemma lem1732226 (x : real) (h1 : term1798 x) : term1798 x.
Proof. exact (h1). Qed.
Lemma lem1732227 (x : real) (h1 : term1792 x) : term1792 x.
Proof. exact (h1). Qed.
Lemma lem1732228 (x : real) (h1 : term1792 x) : term1791 x.
Proof. exact (proj2 (@lem1732227 x h1)). Qed.
Lemma lem1732230 (x : real) (h1 : term1792 x) : term1790 x.
Proof. exact (proj2 (@lem1732228 x h1)). Qed.
Lemma lem1732232 (x : real) (h1 : term1792 x) : term968 x.
Proof. exact (proj2 (@lem1732230 x h1)). Qed.
Lemma lem1732234 (x : real) (h1 : term1792 x) : term966 x.
Proof. exact (proj2 (@lem1732232 x h1)). Qed.
Lemma lem1732236 (x : real) (h1 : term1792 x) : term899 x.
Proof. exact (proj2 (@lem1732234 x h1)). Qed.
Lemma lem1732238 (x : real) (h1 : term1792 x) : term897.
Proof. exact (proj2 (@lem1732236 x h1)). Qed.
Lemma lem1732241 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732242 : term897 = term2523.
Proof. exact (@lem1732241 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732243 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732244 : term897 = False.
Proof. exact (TRANS (@lem1732242) (@lem1732243)). Qed.
Lemma lem1732245 (x : real) (h1 : term1792 x) : False.
Proof. exact (EQ_MP (@lem1732244) (@lem1732238 x h1)). Qed.
Lemma lem1732246 (x : real) (h1 : term1796 x) : term1796 x.
Proof. exact (h1). Qed.
Lemma lem1732247 (x : real) (h1 : term1796 x) : term1795 x.
Proof. exact (proj2 (@lem1732246 x h1)). Qed.
Lemma lem1732249 (x : real) (h1 : term1796 x) : term1794 x.
Proof. exact (proj2 (@lem1732247 x h1)). Qed.
Lemma lem1732251 (x : real) (h1 : term1796 x) : term976 x.
Proof. exact (proj2 (@lem1732249 x h1)). Qed.
Lemma lem1732253 (x : real) (h1 : term1796 x) : term974 x.
Proof. exact (proj2 (@lem1732251 x h1)). Qed.
Lemma lem1732255 (x : real) (h1 : term1796 x) : term938 x.
Proof. exact (proj2 (@lem1732253 x h1)). Qed.
Lemma lem1732257 (x : real) (h1 : term1796 x) : term936.
Proof. exact (proj2 (@lem1732255 x h1)). Qed.
Lemma lem1732260 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732261 : term936 = False.
Proof. exact (@lem1732260 term923 (NUMERAL 0)). Qed.
Lemma lem1732262 (x : real) (h1 : term1796 x) : False.
Proof. exact (EQ_MP (@lem1732261) (@lem1732257 x h1)). Qed.
Lemma lem1732263 (x : real) (h1 : term1798 x) : False.
Proof. exact (or_elim (@lem1732226 x h1) (fun h0 : term1792 x => @lem1732245 x h0) (fun h0 : term1796 x => @lem1732262 x h0)). Qed.
Lemma lem1732264 (x : real) (h1 : term1773 x) : term1773 x.
Proof. exact (h1). Qed.
Lemma lem1732265 (x : real) (h1 : term1767 x) : term1767 x.
Proof. exact (h1). Qed.
Lemma lem1732266 (x : real) (h1 : term1767 x) : term1766 x.
Proof. exact (proj2 (@lem1732265 x h1)). Qed.
Lemma lem1732268 (x : real) (h1 : term1767 x) : term1765 x.
Proof. exact (proj2 (@lem1732266 x h1)). Qed.
Lemma lem1732270 (x : real) (h1 : term1767 x) : term903 x.
Proof. exact (proj2 (@lem1732268 x h1)). Qed.
Lemma lem1732272 (x : real) (h1 : term1767 x) : term901 x.
Proof. exact (proj2 (@lem1732270 x h1)). Qed.
Lemma lem1732274 (x : real) (h1 : term1767 x) : term899 x.
Proof. exact (proj2 (@lem1732272 x h1)). Qed.
Lemma lem1732276 (x : real) (h1 : term1767 x) : term897.
Proof. exact (proj2 (@lem1732274 x h1)). Qed.
Lemma lem1732279 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732280 : term897 = term2523.
Proof. exact (@lem1732279 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732281 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732282 : term897 = False.
Proof. exact (TRANS (@lem1732280) (@lem1732281)). Qed.
Lemma lem1732283 (x : real) (h1 : term1767 x) : False.
Proof. exact (EQ_MP (@lem1732282) (@lem1732276 x h1)). Qed.
Lemma lem1732284 (x : real) (h1 : term1771 x) : term1771 x.
Proof. exact (h1). Qed.
Lemma lem1732285 (x : real) (h1 : term1771 x) : term1770 x.
Proof. exact (proj2 (@lem1732284 x h1)). Qed.
Lemma lem1732287 (x : real) (h1 : term1771 x) : term1769 x.
Proof. exact (proj2 (@lem1732285 x h1)). Qed.
Lemma lem1732289 (x : real) (h1 : term1771 x) : term942 x.
Proof. exact (proj2 (@lem1732287 x h1)). Qed.
Lemma lem1732291 (x : real) (h1 : term1771 x) : term940 x.
Proof. exact (proj2 (@lem1732289 x h1)). Qed.
Lemma lem1732293 (x : real) (h1 : term1771 x) : term938 x.
Proof. exact (proj2 (@lem1732291 x h1)). Qed.
Lemma lem1732295 (x : real) (h1 : term1771 x) : term936.
Proof. exact (proj2 (@lem1732293 x h1)). Qed.
Lemma lem1732298 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732299 : term936 = False.
Proof. exact (@lem1732298 term923 (NUMERAL 0)). Qed.
Lemma lem1732300 (x : real) (h1 : term1771 x) : False.
Proof. exact (EQ_MP (@lem1732299) (@lem1732295 x h1)). Qed.
Lemma lem1732301 (x : real) (h1 : term1773 x) : False.
Proof. exact (or_elim (@lem1732264 x h1) (fun h0 : term1767 x => @lem1732283 x h0) (fun h0 : term1771 x => @lem1732300 x h0)). Qed.
Lemma lem1732302 (x : real) (h1 : term1800 x) : False.
Proof. exact (or_elim (@lem1732225 x h1) (fun h0 : term1798 x => @lem1732263 x h0) (fun h0 : term1773 x => @lem1732301 x h0)). Qed.
Lemma lem1732303 (x : real) (h1 : term1820 x) : term1820 x.
Proof. exact (h1). Qed.
Lemma lem1732304 (x : real) (h1 : term1813 x) : term1813 x.
Proof. exact (h1). Qed.
Lemma lem1732305 (x : real) (h1 : term1813 x) : term1811 x.
Proof. exact (proj2 (@lem1732304 x h1)). Qed.
Lemma lem1732307 (x : real) (h1 : term1813 x) : term1030 x.
Proof. exact (proj2 (@lem1732305 x h1)). Qed.
Lemma lem1732309 (x : real) (h1 : term1813 x) : term1029 x.
Proof. exact (proj2 (@lem1732307 x h1)). Qed.
Lemma lem1732311 (x : real) (h1 : term1813 x) : term1001 x.
Proof. exact (proj2 (@lem1732309 x h1)). Qed.
Lemma lem1732313 (x : real) (h1 : term1813 x) : term1000.
Proof. exact (proj2 (@lem1732311 x h1)). Qed.
Lemma lem1732316 (x : real) (h1 : term1813 x) : term897.
Proof. exact (proj1 (@lem1732313 x h1)). Qed.
Lemma lem1732318 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732319 : term897 = term2523.
Proof. exact (@lem1732318 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732320 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732321 : term897 = False.
Proof. exact (TRANS (@lem1732319) (@lem1732320)). Qed.
Lemma lem1732322 (x : real) (h1 : term1813 x) : False.
Proof. exact (EQ_MP (@lem1732321) (@lem1732316 x h1)). Qed.
Lemma lem1732323 (x : real) (h1 : term1819 x) : term1819 x.
Proof. exact (h1). Qed.
Lemma lem1732324 (x : real) (h1 : term1819 x) : term1818 x.
Proof. exact (proj2 (@lem1732323 x h1)). Qed.
Lemma lem1732326 (x : real) (h1 : term1819 x) : term1034 x.
Proof. exact (proj2 (@lem1732324 x h1)). Qed.
Lemma lem1732328 (x : real) (h1 : term1819 x) : term1032 x.
Proof. exact (proj2 (@lem1732326 x h1)). Qed.
Lemma lem1732330 (x : real) (h1 : term1819 x) : term1001 x.
Proof. exact (proj2 (@lem1732328 x h1)). Qed.
Lemma lem1732332 (x : real) (h1 : term1819 x) : term1000.
Proof. exact (proj2 (@lem1732330 x h1)). Qed.
Lemma lem1732335 (x : real) (h1 : term1819 x) : term897.
Proof. exact (proj1 (@lem1732332 x h1)). Qed.
Lemma lem1732337 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732338 : term897 = term2523.
Proof. exact (@lem1732337 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732339 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732340 : term897 = False.
Proof. exact (TRANS (@lem1732338) (@lem1732339)). Qed.
Lemma lem1732341 (x : real) (h1 : term1819 x) : False.
Proof. exact (EQ_MP (@lem1732340) (@lem1732335 x h1)). Qed.
Lemma lem1732342 (x : real) (h1 : term1820 x) : False.
Proof. exact (or_elim (@lem1732303 x h1) (fun h0 : term1813 x => @lem1732322 x h0) (fun h0 : term1819 x => @lem1732341 x h0)). Qed.
Lemma lem1732343 (x : real) (h1 : term1823 x) : False.
Proof. exact (or_elim (@lem1732224 x h1) (fun h0 : term1800 x => @lem1732302 x h0) (fun h0 : term1820 x => @lem1732342 x h0)). Qed.
Lemma lem1732344 (x : real) (h1 : term1917 x) : term1917 x.
Proof. exact (h1). Qed.
Lemma lem1732345 (x : real) (h1 : term1894 x) : term1894 x.
Proof. exact (h1). Qed.
Lemma lem1732346 (x : real) (h1 : term1892 x) : term1892 x.
Proof. exact (h1). Qed.
Lemma lem1732347 (x : real) (h1 : term1886 x) : term1886 x.
Proof. exact (h1). Qed.
Lemma lem1732348 (x : real) (h1 : term1886 x) : term1885 x.
Proof. exact (proj2 (@lem1732347 x h1)). Qed.
Lemma lem1732350 (x : real) (h1 : term1886 x) : term1884 x.
Proof. exact (proj2 (@lem1732348 x h1)). Qed.
Lemma lem1732352 (x : real) (h1 : term1886 x) : term1157 x.
Proof. exact (proj2 (@lem1732350 x h1)). Qed.
Lemma lem1732354 (x : real) (h1 : term1886 x) : term1155 x.
Proof. exact (proj2 (@lem1732352 x h1)). Qed.
Lemma lem1732356 (x : real) (h1 : term1886 x) : term1101 x.
Proof. exact (proj2 (@lem1732354 x h1)). Qed.
Lemma lem1732358 (x : real) (h1 : term1886 x) : term936.
Proof. exact (proj2 (@lem1732356 x h1)). Qed.
Lemma lem1732361 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732362 : term936 = False.
Proof. exact (@lem1732361 term923 (NUMERAL 0)). Qed.
Lemma lem1732363 (x : real) (h1 : term1886 x) : False.
Proof. exact (EQ_MP (@lem1732362) (@lem1732358 x h1)). Qed.
Lemma lem1732364 (x : real) (h1 : term1890 x) : term1890 x.
Proof. exact (h1). Qed.
Lemma lem1732365 (x : real) (h1 : term1890 x) : term1889 x.
Proof. exact (proj2 (@lem1732364 x h1)). Qed.
Lemma lem1732367 (x : real) (h1 : term1890 x) : term1888 x.
Proof. exact (proj2 (@lem1732365 x h1)). Qed.
Lemma lem1732369 (x : real) (h1 : term1890 x) : term1165 x.
Proof. exact (proj2 (@lem1732367 x h1)). Qed.
Lemma lem1732371 (x : real) (h1 : term1890 x) : term1163 x.
Proof. exact (proj2 (@lem1732369 x h1)). Qed.
Lemma lem1732373 (x : real) (h1 : term1890 x) : term1127 x.
Proof. exact (proj2 (@lem1732371 x h1)). Qed.
Lemma lem1732375 (x : real) (h1 : term1890 x) : term897.
Proof. exact (proj2 (@lem1732373 x h1)). Qed.
Lemma lem1732378 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732379 : term897 = term2523.
Proof. exact (@lem1732378 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732380 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732381 : term897 = False.
Proof. exact (TRANS (@lem1732379) (@lem1732380)). Qed.
Lemma lem1732382 (x : real) (h1 : term1890 x) : False.
Proof. exact (EQ_MP (@lem1732381) (@lem1732375 x h1)). Qed.
Lemma lem1732383 (x : real) (h1 : term1892 x) : False.
Proof. exact (or_elim (@lem1732346 x h1) (fun h0 : term1886 x => @lem1732363 x h0) (fun h0 : term1890 x => @lem1732382 x h0)). Qed.
Lemma lem1732384 (x : real) (h1 : term1867 x) : term1867 x.
Proof. exact (h1). Qed.
Lemma lem1732385 (x : real) (h1 : term1861 x) : term1861 x.
Proof. exact (h1). Qed.
Lemma lem1732386 (x : real) (h1 : term1861 x) : term1860 x.
Proof. exact (proj2 (@lem1732385 x h1)). Qed.
Lemma lem1732388 (x : real) (h1 : term1861 x) : term1859 x.
Proof. exact (proj2 (@lem1732386 x h1)). Qed.
Lemma lem1732390 (x : real) (h1 : term1861 x) : term1105 x.
Proof. exact (proj2 (@lem1732388 x h1)). Qed.
Lemma lem1732392 (x : real) (h1 : term1861 x) : term1103 x.
Proof. exact (proj2 (@lem1732390 x h1)). Qed.
Lemma lem1732394 (x : real) (h1 : term1861 x) : term1101 x.
Proof. exact (proj2 (@lem1732392 x h1)). Qed.
Lemma lem1732396 (x : real) (h1 : term1861 x) : term936.
Proof. exact (proj2 (@lem1732394 x h1)). Qed.
Lemma lem1732399 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732400 : term936 = False.
Proof. exact (@lem1732399 term923 (NUMERAL 0)). Qed.
Lemma lem1732401 (x : real) (h1 : term1861 x) : False.
Proof. exact (EQ_MP (@lem1732400) (@lem1732396 x h1)). Qed.
Lemma lem1732402 (x : real) (h1 : term1865 x) : term1865 x.
Proof. exact (h1). Qed.
Lemma lem1732403 (x : real) (h1 : term1865 x) : term1864 x.
Proof. exact (proj2 (@lem1732402 x h1)). Qed.
Lemma lem1732405 (x : real) (h1 : term1865 x) : term1863 x.
Proof. exact (proj2 (@lem1732403 x h1)). Qed.
Lemma lem1732407 (x : real) (h1 : term1865 x) : term1131 x.
Proof. exact (proj2 (@lem1732405 x h1)). Qed.
Lemma lem1732409 (x : real) (h1 : term1865 x) : term1129 x.
Proof. exact (proj2 (@lem1732407 x h1)). Qed.
Lemma lem1732411 (x : real) (h1 : term1865 x) : term1127 x.
Proof. exact (proj2 (@lem1732409 x h1)). Qed.
Lemma lem1732413 (x : real) (h1 : term1865 x) : term897.
Proof. exact (proj2 (@lem1732411 x h1)). Qed.
Lemma lem1732416 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732417 : term897 = term2523.
Proof. exact (@lem1732416 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732418 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732419 : term897 = False.
Proof. exact (TRANS (@lem1732417) (@lem1732418)). Qed.
Lemma lem1732420 (x : real) (h1 : term1865 x) : False.
Proof. exact (EQ_MP (@lem1732419) (@lem1732413 x h1)). Qed.
Lemma lem1732421 (x : real) (h1 : term1867 x) : False.
Proof. exact (or_elim (@lem1732384 x h1) (fun h0 : term1861 x => @lem1732401 x h0) (fun h0 : term1865 x => @lem1732420 x h0)). Qed.
Lemma lem1732422 (x : real) (h1 : term1894 x) : False.
Proof. exact (or_elim (@lem1732345 x h1) (fun h0 : term1892 x => @lem1732383 x h0) (fun h0 : term1867 x => @lem1732421 x h0)). Qed.
Lemma lem1732423 (x : real) (h1 : term1914 x) : term1914 x.
Proof. exact (h1). Qed.
Lemma lem1732424 (x : real) (h1 : term1907 x) : term1907 x.
Proof. exact (h1). Qed.
Lemma lem1732425 (x : real) (h1 : term1907 x) : term1905 x.
Proof. exact (proj2 (@lem1732424 x h1)). Qed.
Lemma lem1732427 (x : real) (h1 : term1907 x) : term1206 x.
Proof. exact (proj2 (@lem1732425 x h1)). Qed.
Lemma lem1732429 (x : real) (h1 : term1907 x) : term1205 x.
Proof. exact (proj2 (@lem1732427 x h1)). Qed.
Lemma lem1732431 (x : real) (h1 : term1907 x) : term1185 x.
Proof. exact (proj2 (@lem1732429 x h1)). Qed.
Lemma lem1732433 (x : real) (h1 : term1907 x) : term1184.
Proof. exact (proj2 (@lem1732431 x h1)). Qed.
Lemma lem1732435 (x : real) (h1 : term1907 x) : term897.
Proof. exact (proj2 (@lem1732433 x h1)). Qed.
Lemma lem1732438 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732439 : term897 = term2523.
Proof. exact (@lem1732438 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732440 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732441 : term897 = False.
Proof. exact (TRANS (@lem1732439) (@lem1732440)). Qed.
Lemma lem1732442 (x : real) (h1 : term1907 x) : False.
Proof. exact (EQ_MP (@lem1732441) (@lem1732435 x h1)). Qed.
Lemma lem1732443 (x : real) (h1 : term1913 x) : term1913 x.
Proof. exact (h1). Qed.
Lemma lem1732444 (x : real) (h1 : term1913 x) : term1912 x.
Proof. exact (proj2 (@lem1732443 x h1)). Qed.
Lemma lem1732446 (x : real) (h1 : term1913 x) : term1210 x.
Proof. exact (proj2 (@lem1732444 x h1)). Qed.
Lemma lem1732448 (x : real) (h1 : term1913 x) : term1208 x.
Proof. exact (proj2 (@lem1732446 x h1)). Qed.
Lemma lem1732450 (x : real) (h1 : term1913 x) : term1185 x.
Proof. exact (proj2 (@lem1732448 x h1)). Qed.
Lemma lem1732452 (x : real) (h1 : term1913 x) : term1184.
Proof. exact (proj2 (@lem1732450 x h1)). Qed.
Lemma lem1732454 (x : real) (h1 : term1913 x) : term897.
Proof. exact (proj2 (@lem1732452 x h1)). Qed.
Lemma lem1732457 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732458 : term897 = term2523.
Proof. exact (@lem1732457 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732459 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732460 : term897 = False.
Proof. exact (TRANS (@lem1732458) (@lem1732459)). Qed.
Lemma lem1732461 (x : real) (h1 : term1913 x) : False.
Proof. exact (EQ_MP (@lem1732460) (@lem1732454 x h1)). Qed.
Lemma lem1732462 (x : real) (h1 : term1914 x) : False.
Proof. exact (or_elim (@lem1732423 x h1) (fun h0 : term1907 x => @lem1732442 x h0) (fun h0 : term1913 x => @lem1732461 x h0)). Qed.
Lemma lem1732463 (x : real) (h1 : term1917 x) : False.
Proof. exact (or_elim (@lem1732344 x h1) (fun h0 : term1894 x => @lem1732422 x h0) (fun h0 : term1914 x => @lem1732462 x h0)). Qed.
Lemma lem1732464 (x : real) (h1 : term1919 x) : False.
Proof. exact (or_elim (@lem1732223 x h1) (fun h0 : term1823 x => @lem1732343 x h0) (fun h0 : term1917 x => @lem1732463 x h0)). Qed.
Lemma lem1732465 (x : real) (h1 : term2134 x) : term2134 x.
Proof. exact (h1). Qed.
Lemma lem1732466 (x : real) (h1 : term2022 x) : term2022 x.
Proof. exact (h1). Qed.
Lemma lem1732467 (x : real) (h1 : term1989 x) : term1989 x.
Proof. exact (h1). Qed.
Lemma lem1732468 (x : real) (h1 : term1987 x) : term1987 x.
Proof. exact (h1). Qed.
Lemma lem1732469 (x : real) (h1 : term1979 x) : term1979 x.
Proof. exact (h1). Qed.
Lemma lem1732470 (x : real) (h1 : term1979 x) : term1977 x.
Proof. exact (proj2 (@lem1732469 x h1)). Qed.
Lemma lem1732472 (x : real) (h1 : term1979 x) : term1984 x.
Proof. exact (proj2 (@lem1732470 x h1)). Qed.
Lemma lem1732474 (x : real) (h1 : term1979 x) : term1959 x.
Proof. exact (proj2 (@lem1732472 x h1)). Qed.
Lemma lem1732476 (x : real) (h1 : term1979 x) : term1958 x.
Proof. exact (proj2 (@lem1732474 x h1)). Qed.
Lemma lem1732477 (x : real) (h1 : term1979 x) : term179 x.
Proof. exact (proj1 (@lem1732474 x h1)). Qed.
Lemma lem1732479 (x : real) (h1 : term1979 x) : term1224 x.
Proof. exact (proj1 (@lem1732476 x h1)). Qed.
Lemma lem1732480 (x : real) (h1 : term1979 x) : term326 x.
Proof. exact (proj2 (@lem1732479 x h1)). Qed.
Lemma lem1732485 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732486 : term1117 = term2525.
Proof. exact (@lem1732485 (NUMERAL 0) term185). Qed.
Lemma lem1732487 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732488 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732489 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732488 h1) (fun h1 : term2525 = True => @lem1732487)). Qed.
Lemma lem1732490 : term2525 = True.
Proof. exact (EQ_MP (@lem1732489) (@lem1732487)). Qed.
Lemma lem1732491 : term1117 = True.
Proof. exact (TRANS (@lem1732486) (@lem1732490)). Qed.
Lemma lem1732492 : True = term1117.
Proof. exact (SYM (@lem1732491)). Qed.
Lemma lem1732493 : term1117.
Proof. exact (EQ_MP (@lem1732492) (@lem0)). Qed.
Lemma lem1732494 (x : real) (h1 : term1979 x) : term2527 x.
Proof. exact (conj (@lem1732493) (@lem1732480 x h1)). Qed.
Lemma lem1732496 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1732497 (x : real) : term2529 x.
Proof. exact (@lem1732496 term24 x). Qed.
Lemma lem1732498 (x : real) (h1 : term1979 x) : term1223 x.
Proof. exact (@lem1732497 x (@lem1732494 x h1)). Qed.
Lemma lem1732499 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1732500 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1732501 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1732500) (@lem1732499 x)). Qed.
Lemma lem1732502 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732503 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1732501 x) (@lem1732502)). Qed.
Lemma lem1732504 (x : real) (h1 : term1979 x) : term326 x.
Proof. exact (EQ_MP (@lem1732503 x) (@lem1732498 x h1)). Qed.
Lemma lem1732506 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732507 : term1117 = term2525.
Proof. exact (@lem1732506 (NUMERAL 0) term185). Qed.
Lemma lem1732508 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732509 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732510 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732509 h1) (fun h1 : term2525 = True => @lem1732508)). Qed.
Lemma lem1732511 : term2525 = True.
Proof. exact (EQ_MP (@lem1732510) (@lem1732508)). Qed.
Lemma lem1732512 : term1117 = True.
Proof. exact (TRANS (@lem1732507) (@lem1732511)). Qed.
Lemma lem1732513 : True = term1117.
Proof. exact (SYM (@lem1732512)). Qed.
Lemma lem1732514 : term1117.
Proof. exact (EQ_MP (@lem1732513) (@lem0)). Qed.
Lemma lem1732515 (x : real) (h1 : term1979 x) : term2530 x.
Proof. exact (conj (@lem1732514) (@lem1732477 x h1)). Qed.
Lemma lem1732517 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1732518 (x : real) : term2532 x.
Proof. exact (@lem1732517 term24 (term176 x)). Qed.
Lemma lem1732519 (x : real) (h1 : term1979 x) : term2533 x.
Proof. exact (@lem1732518 x (@lem1732515 x h1)). Qed.
Lemma lem1732520 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1732521 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732522 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1732521) (@lem1732520 x)). Qed.
Lemma lem1732523 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732524 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1732522 x) (@lem1732523)). Qed.
Lemma lem1732525 (x : real) (h1 : term1979 x) : term179 x.
Proof. exact (EQ_MP (@lem1732524 x) (@lem1732519 x h1)). Qed.
Lemma lem1732526 (x : real) (h1 : term1979 x) : term2536 x.
Proof. exact (conj (@lem1732525 x h1) (@lem1732504 x h1)). Qed.
Lemma lem1732528 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1732529 (x : real) : term2538 x.
Proof. exact (@lem1732528 (term176 x) x). Qed.
Lemma lem1732530 (x : real) (h1 : term1979 x) : term2539 x.
Proof. exact (@lem1732529 x (@lem1732526 x h1)). Qed.
Lemma lem1732531 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1732533 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1732534 : term1261 = term76.
Proof. exact (@lem1732533 term185). Qed.
Lemma lem1732535 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1732536 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1732535) (@lem1732534)). Qed.
Lemma lem1732537 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1732538 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1732536) (@lem1732537 x)). Qed.
Lemma lem1732539 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1732531 x) (@lem1732538 x)). Qed.
Lemma lem1732540 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1732541 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1732539 x) (@lem1732540 x)). Qed.
Lemma lem1732542 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732543 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1732542) (@lem1732541 x)). Qed.
Lemma lem1732544 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732545 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1732543 x) (@lem1732544)). Qed.
Lemma lem1732546 (x : real) (h1 : term1979 x) : term897.
Proof. exact (EQ_MP (@lem1732545 x) (@lem1732530 x h1)). Qed.
Lemma lem1732548 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732549 : term897 = term2523.
Proof. exact (@lem1732548 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732550 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732551 : term897 = False.
Proof. exact (TRANS (@lem1732549) (@lem1732550)). Qed.
Lemma lem1732552 (x : real) (h1 : term1979 x) : False.
Proof. exact (EQ_MP (@lem1732551) (@lem1732546 x h1)). Qed.
Lemma lem1732553 (x : real) (h1 : term1986 x) : term1986 x.
Proof. exact (h1). Qed.
Lemma lem1732554 (x : real) (h1 : term1986 x) : term1973 x.
Proof. exact (proj2 (@lem1732553 x h1)). Qed.
Lemma lem1732556 (x : real) (h1 : term1986 x) : term1985 x.
Proof. exact (proj2 (@lem1732554 x h1)). Qed.
Lemma lem1732558 (x : real) (h1 : term1986 x) : term1965 x.
Proof. exact (proj2 (@lem1732556 x h1)). Qed.
Lemma lem1732560 (x : real) (h1 : term1986 x) : term1964 x.
Proof. exact (proj2 (@lem1732558 x h1)). Qed.
Lemma lem1732562 (x : real) (h1 : term1986 x) : term1963 x.
Proof. exact (proj2 (@lem1732560 x h1)). Qed.
Lemma lem1732566 (x : real) (h1 : term1986 x) : term915.
Proof. exact (proj2 (@lem1732562 x h1)). Qed.
Lemma lem1732569 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732570 : term915 = False.
Proof. exact (@lem1732569 term185 (NUMERAL 0)). Qed.
Lemma lem1732571 (x : real) (h1 : term1986 x) : False.
Proof. exact (EQ_MP (@lem1732570) (@lem1732566 x h1)). Qed.
Lemma lem1732572 (x : real) (h1 : term1987 x) : False.
Proof. exact (or_elim (@lem1732468 x h1) (fun h0 : term1979 x => @lem1732552 x h0) (fun h0 : term1986 x => @lem1732571 x h0)). Qed.
Lemma lem1732573 (x : real) (h1 : term1968 x) : term1968 x.
Proof. exact (h1). Qed.
Lemma lem1732574 (x : real) (h1 : term1952 x) : term1952 x.
Proof. exact (h1). Qed.
Lemma lem1732575 (x : real) (h1 : term1952 x) : term1950 x.
Proof. exact (proj2 (@lem1732574 x h1)). Qed.
Lemma lem1732577 (x : real) (h1 : term1952 x) : term1960 x.
Proof. exact (proj2 (@lem1732575 x h1)). Qed.
Lemma lem1732579 (x : real) (h1 : term1952 x) : term1959 x.
Proof. exact (proj2 (@lem1732577 x h1)). Qed.
Lemma lem1732581 (x : real) (h1 : term1952 x) : term1958 x.
Proof. exact (proj2 (@lem1732579 x h1)). Qed.
Lemma lem1732582 (x : real) (h1 : term1952 x) : term179 x.
Proof. exact (proj1 (@lem1732579 x h1)). Qed.
Lemma lem1732584 (x : real) (h1 : term1952 x) : term1224 x.
Proof. exact (proj1 (@lem1732581 x h1)). Qed.
Lemma lem1732585 (x : real) (h1 : term1952 x) : term326 x.
Proof. exact (proj2 (@lem1732584 x h1)). Qed.
Lemma lem1732590 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732591 : term1117 = term2525.
Proof. exact (@lem1732590 (NUMERAL 0) term185). Qed.
Lemma lem1732592 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732593 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732594 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732593 h1) (fun h1 : term2525 = True => @lem1732592)). Qed.
Lemma lem1732595 : term2525 = True.
Proof. exact (EQ_MP (@lem1732594) (@lem1732592)). Qed.
Lemma lem1732596 : term1117 = True.
Proof. exact (TRANS (@lem1732591) (@lem1732595)). Qed.
Lemma lem1732597 : True = term1117.
Proof. exact (SYM (@lem1732596)). Qed.
Lemma lem1732598 : term1117.
Proof. exact (EQ_MP (@lem1732597) (@lem0)). Qed.
Lemma lem1732599 (x : real) (h1 : term1952 x) : term2527 x.
Proof. exact (conj (@lem1732598) (@lem1732585 x h1)). Qed.
Lemma lem1732601 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1732602 (x : real) : term2529 x.
Proof. exact (@lem1732601 term24 x). Qed.
Lemma lem1732603 (x : real) (h1 : term1952 x) : term1223 x.
Proof. exact (@lem1732602 x (@lem1732599 x h1)). Qed.
Lemma lem1732604 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1732605 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1732606 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1732605) (@lem1732604 x)). Qed.
Lemma lem1732607 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732608 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1732606 x) (@lem1732607)). Qed.
Lemma lem1732609 (x : real) (h1 : term1952 x) : term326 x.
Proof. exact (EQ_MP (@lem1732608 x) (@lem1732603 x h1)). Qed.
Lemma lem1732611 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732612 : term1117 = term2525.
Proof. exact (@lem1732611 (NUMERAL 0) term185). Qed.
Lemma lem1732613 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732614 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732615 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732614 h1) (fun h1 : term2525 = True => @lem1732613)). Qed.
Lemma lem1732616 : term2525 = True.
Proof. exact (EQ_MP (@lem1732615) (@lem1732613)). Qed.
Lemma lem1732617 : term1117 = True.
Proof. exact (TRANS (@lem1732612) (@lem1732616)). Qed.
Lemma lem1732618 : True = term1117.
Proof. exact (SYM (@lem1732617)). Qed.
Lemma lem1732619 : term1117.
Proof. exact (EQ_MP (@lem1732618) (@lem0)). Qed.
Lemma lem1732620 (x : real) (h1 : term1952 x) : term2530 x.
Proof. exact (conj (@lem1732619) (@lem1732582 x h1)). Qed.
Lemma lem1732622 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1732623 (x : real) : term2532 x.
Proof. exact (@lem1732622 term24 (term176 x)). Qed.
Lemma lem1732624 (x : real) (h1 : term1952 x) : term2533 x.
Proof. exact (@lem1732623 x (@lem1732620 x h1)). Qed.
Lemma lem1732625 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1732626 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732627 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1732626) (@lem1732625 x)). Qed.
Lemma lem1732628 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732629 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1732627 x) (@lem1732628)). Qed.
Lemma lem1732630 (x : real) (h1 : term1952 x) : term179 x.
Proof. exact (EQ_MP (@lem1732629 x) (@lem1732624 x h1)). Qed.
Lemma lem1732631 (x : real) (h1 : term1952 x) : term2536 x.
Proof. exact (conj (@lem1732630 x h1) (@lem1732609 x h1)). Qed.
Lemma lem1732633 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1732634 (x : real) : term2538 x.
Proof. exact (@lem1732633 (term176 x) x). Qed.
Lemma lem1732635 (x : real) (h1 : term1952 x) : term2539 x.
Proof. exact (@lem1732634 x (@lem1732631 x h1)). Qed.
Lemma lem1732636 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1732638 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1732639 : term1261 = term76.
Proof. exact (@lem1732638 term185). Qed.
Lemma lem1732640 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1732641 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1732640) (@lem1732639)). Qed.
Lemma lem1732642 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1732643 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1732641) (@lem1732642 x)). Qed.
Lemma lem1732644 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1732636 x) (@lem1732643 x)). Qed.
Lemma lem1732645 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1732646 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1732644 x) (@lem1732645 x)). Qed.
Lemma lem1732647 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732648 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1732647) (@lem1732646 x)). Qed.
Lemma lem1732649 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732650 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1732648 x) (@lem1732649)). Qed.
Lemma lem1732651 (x : real) (h1 : term1952 x) : term897.
Proof. exact (EQ_MP (@lem1732650 x) (@lem1732635 x h1)). Qed.
Lemma lem1732653 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732654 : term897 = term2523.
Proof. exact (@lem1732653 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732655 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732656 : term897 = False.
Proof. exact (TRANS (@lem1732654) (@lem1732655)). Qed.
Lemma lem1732657 (x : real) (h1 : term1952 x) : False.
Proof. exact (EQ_MP (@lem1732656) (@lem1732651 x h1)). Qed.
Lemma lem1732658 (x : real) (h1 : term1967 x) : term1967 x.
Proof. exact (h1). Qed.
Lemma lem1732659 (x : real) (h1 : term1967 x) : term1946 x.
Proof. exact (proj2 (@lem1732658 x h1)). Qed.
Lemma lem1732661 (x : real) (h1 : term1967 x) : term1966 x.
Proof. exact (proj2 (@lem1732659 x h1)). Qed.
Lemma lem1732663 (x : real) (h1 : term1967 x) : term1965 x.
Proof. exact (proj2 (@lem1732661 x h1)). Qed.
Lemma lem1732665 (x : real) (h1 : term1967 x) : term1964 x.
Proof. exact (proj2 (@lem1732663 x h1)). Qed.
Lemma lem1732667 (x : real) (h1 : term1967 x) : term1963 x.
Proof. exact (proj2 (@lem1732665 x h1)). Qed.
Lemma lem1732671 (x : real) (h1 : term1967 x) : term915.
Proof. exact (proj2 (@lem1732667 x h1)). Qed.
Lemma lem1732674 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732675 : term915 = False.
Proof. exact (@lem1732674 term185 (NUMERAL 0)). Qed.
Lemma lem1732676 (x : real) (h1 : term1967 x) : False.
Proof. exact (EQ_MP (@lem1732675) (@lem1732671 x h1)). Qed.
Lemma lem1732677 (x : real) (h1 : term1968 x) : False.
Proof. exact (or_elim (@lem1732573 x h1) (fun h0 : term1952 x => @lem1732657 x h0) (fun h0 : term1967 x => @lem1732676 x h0)). Qed.
Lemma lem1732678 (x : real) (h1 : term1989 x) : False.
Proof. exact (or_elim (@lem1732467 x h1) (fun h0 : term1987 x => @lem1732572 x h0) (fun h0 : term1968 x => @lem1732677 x h0)). Qed.
Lemma lem1732679 (x : real) (h1 : term2019 x) : term2019 x.
Proof. exact (h1). Qed.
Lemma lem1732680 (x : real) (h1 : term2012 x) : term2012 x.
Proof. exact (h1). Qed.
Lemma lem1732681 (x : real) (h1 : term2012 x) : term2010 x.
Proof. exact (proj2 (@lem1732680 x h1)). Qed.
Lemma lem1732683 (x : real) (h1 : term2012 x) : term1999 x.
Proof. exact (proj2 (@lem1732681 x h1)). Qed.
Lemma lem1732685 (x : real) (h1 : term2012 x) : term1998 x.
Proof. exact (proj2 (@lem1732683 x h1)). Qed.
Lemma lem1732687 (x : real) (h1 : term2012 x) : term1997 x.
Proof. exact (proj2 (@lem1732685 x h1)). Qed.
Lemma lem1732691 (x : real) (h1 : term2012 x) : term1996.
Proof. exact (proj2 (@lem1732687 x h1)). Qed.
Lemma lem1732694 (x : real) (h1 : term2012 x) : term915.
Proof. exact (proj1 (@lem1732691 x h1)). Qed.
Lemma lem1732696 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732697 : term915 = False.
Proof. exact (@lem1732696 term185 (NUMERAL 0)). Qed.
Lemma lem1732698 (x : real) (h1 : term2012 x) : False.
Proof. exact (EQ_MP (@lem1732697) (@lem1732694 x h1)). Qed.
Lemma lem1732699 (x : real) (h1 : term2018 x) : term2018 x.
Proof. exact (h1). Qed.
Lemma lem1732700 (x : real) (h1 : term2018 x) : term2017 x.
Proof. exact (proj2 (@lem1732699 x h1)). Qed.
Lemma lem1732702 (x : real) (h1 : term2018 x) : term1999 x.
Proof. exact (proj2 (@lem1732700 x h1)). Qed.
Lemma lem1732704 (x : real) (h1 : term2018 x) : term1998 x.
Proof. exact (proj2 (@lem1732702 x h1)). Qed.
Lemma lem1732706 (x : real) (h1 : term2018 x) : term1997 x.
Proof. exact (proj2 (@lem1732704 x h1)). Qed.
Lemma lem1732710 (x : real) (h1 : term2018 x) : term1996.
Proof. exact (proj2 (@lem1732706 x h1)). Qed.
Lemma lem1732713 (x : real) (h1 : term2018 x) : term915.
Proof. exact (proj1 (@lem1732710 x h1)). Qed.
Lemma lem1732715 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732716 : term915 = False.
Proof. exact (@lem1732715 term185 (NUMERAL 0)). Qed.
Lemma lem1732717 (x : real) (h1 : term2018 x) : False.
Proof. exact (EQ_MP (@lem1732716) (@lem1732713 x h1)). Qed.
Lemma lem1732718 (x : real) (h1 : term2019 x) : False.
Proof. exact (or_elim (@lem1732679 x h1) (fun h0 : term2012 x => @lem1732698 x h0) (fun h0 : term2018 x => @lem1732717 x h0)). Qed.
Lemma lem1732719 (x : real) (h1 : term2022 x) : False.
Proof. exact (or_elim (@lem1732466 x h1) (fun h0 : term1989 x => @lem1732678 x h0) (fun h0 : term2019 x => @lem1732718 x h0)). Qed.
Lemma lem1732720 (x : real) (h1 : term2132 x) : term2132 x.
Proof. exact (h1). Qed.
Lemma lem1732721 (x : real) (h1 : term2099 x) : term2099 x.
Proof. exact (h1). Qed.
Lemma lem1732722 (x : real) (h1 : term2097 x) : term2097 x.
Proof. exact (h1). Qed.
Lemma lem1732723 (x : real) (h1 : term2087 x) : term2087 x.
Proof. exact (h1). Qed.
Lemma lem1732724 (x : real) (h1 : term2087 x) : term2085 x.
Proof. exact (proj2 (@lem1732723 x h1)). Qed.
Lemma lem1732726 (x : real) (h1 : term2087 x) : term2092 x.
Proof. exact (proj2 (@lem1732724 x h1)). Qed.
Lemma lem1732728 (x : real) (h1 : term2087 x) : term2061 x.
Proof. exact (proj2 (@lem1732726 x h1)). Qed.
Lemma lem1732730 (x : real) (h1 : term2087 x) : term2060 x.
Proof. exact (proj2 (@lem1732728 x h1)). Qed.
Lemma lem1732732 (x : real) (h1 : term2087 x) : term1525 x.
Proof. exact (proj2 (@lem1732730 x h1)). Qed.
Lemma lem1732736 (x : real) (h1 : term2087 x) : term915.
Proof. exact (proj2 (@lem1732732 x h1)). Qed.
Lemma lem1732739 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732740 : term915 = False.
Proof. exact (@lem1732739 term185 (NUMERAL 0)). Qed.
Lemma lem1732741 (x : real) (h1 : term2087 x) : False.
Proof. exact (EQ_MP (@lem1732740) (@lem1732736 x h1)). Qed.
Lemma lem1732742 (x : real) (h1 : term2096 x) : term2096 x.
Proof. exact (h1). Qed.
Lemma lem1732743 (x : real) (h1 : term2096 x) : term2095 x.
Proof. exact (proj2 (@lem1732742 x h1)). Qed.
Lemma lem1732745 (x : real) (h1 : term2096 x) : term2094 x.
Proof. exact (proj2 (@lem1732743 x h1)). Qed.
Lemma lem1732747 (x : real) (h1 : term2096 x) : term2071 x.
Proof. exact (proj2 (@lem1732745 x h1)). Qed.
Lemma lem1732749 (x : real) (h1 : term2096 x) : term1687 x.
Proof. exact (proj2 (@lem1732747 x h1)). Qed.
Lemma lem1732750 (x : real) (h1 : term2096 x) : term179 x.
Proof. exact (proj1 (@lem1732747 x h1)). Qed.
Lemma lem1732752 (x : real) (h1 : term2096 x) : term1224 x.
Proof. exact (proj1 (@lem1732749 x h1)). Qed.
Lemma lem1732753 (x : real) (h1 : term2096 x) : term326 x.
Proof. exact (proj2 (@lem1732752 x h1)). Qed.
Lemma lem1732758 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732759 : term1117 = term2525.
Proof. exact (@lem1732758 (NUMERAL 0) term185). Qed.
Lemma lem1732760 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732761 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732762 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732761 h1) (fun h1 : term2525 = True => @lem1732760)). Qed.
Lemma lem1732763 : term2525 = True.
Proof. exact (EQ_MP (@lem1732762) (@lem1732760)). Qed.
Lemma lem1732764 : term1117 = True.
Proof. exact (TRANS (@lem1732759) (@lem1732763)). Qed.
Lemma lem1732765 : True = term1117.
Proof. exact (SYM (@lem1732764)). Qed.
Lemma lem1732766 : term1117.
Proof. exact (EQ_MP (@lem1732765) (@lem0)). Qed.
Lemma lem1732767 (x : real) (h1 : term2096 x) : term2527 x.
Proof. exact (conj (@lem1732766) (@lem1732753 x h1)). Qed.
Lemma lem1732769 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1732770 (x : real) : term2529 x.
Proof. exact (@lem1732769 term24 x). Qed.
Lemma lem1732771 (x : real) (h1 : term2096 x) : term1223 x.
Proof. exact (@lem1732770 x (@lem1732767 x h1)). Qed.
Lemma lem1732772 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1732773 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1732774 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1732773) (@lem1732772 x)). Qed.
Lemma lem1732775 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732776 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1732774 x) (@lem1732775)). Qed.
Lemma lem1732777 (x : real) (h1 : term2096 x) : term326 x.
Proof. exact (EQ_MP (@lem1732776 x) (@lem1732771 x h1)). Qed.
Lemma lem1732779 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732780 : term1117 = term2525.
Proof. exact (@lem1732779 (NUMERAL 0) term185). Qed.
Lemma lem1732781 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732782 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732783 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732782 h1) (fun h1 : term2525 = True => @lem1732781)). Qed.
Lemma lem1732784 : term2525 = True.
Proof. exact (EQ_MP (@lem1732783) (@lem1732781)). Qed.
Lemma lem1732785 : term1117 = True.
Proof. exact (TRANS (@lem1732780) (@lem1732784)). Qed.
Lemma lem1732786 : True = term1117.
Proof. exact (SYM (@lem1732785)). Qed.
Lemma lem1732787 : term1117.
Proof. exact (EQ_MP (@lem1732786) (@lem0)). Qed.
Lemma lem1732788 (x : real) (h1 : term2096 x) : term2530 x.
Proof. exact (conj (@lem1732787) (@lem1732750 x h1)). Qed.
Lemma lem1732790 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1732791 (x : real) : term2532 x.
Proof. exact (@lem1732790 term24 (term176 x)). Qed.
Lemma lem1732792 (x : real) (h1 : term2096 x) : term2533 x.
Proof. exact (@lem1732791 x (@lem1732788 x h1)). Qed.
Lemma lem1732793 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1732794 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732795 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1732794) (@lem1732793 x)). Qed.
Lemma lem1732796 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732797 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1732795 x) (@lem1732796)). Qed.
Lemma lem1732798 (x : real) (h1 : term2096 x) : term179 x.
Proof. exact (EQ_MP (@lem1732797 x) (@lem1732792 x h1)). Qed.
Lemma lem1732799 (x : real) (h1 : term2096 x) : term2536 x.
Proof. exact (conj (@lem1732798 x h1) (@lem1732777 x h1)). Qed.
Lemma lem1732801 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1732802 (x : real) : term2538 x.
Proof. exact (@lem1732801 (term176 x) x). Qed.
Lemma lem1732803 (x : real) (h1 : term2096 x) : term2539 x.
Proof. exact (@lem1732802 x (@lem1732799 x h1)). Qed.
Lemma lem1732804 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1732806 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1732807 : term1261 = term76.
Proof. exact (@lem1732806 term185). Qed.
Lemma lem1732808 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1732809 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1732808) (@lem1732807)). Qed.
Lemma lem1732810 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1732811 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1732809) (@lem1732810 x)). Qed.
Lemma lem1732812 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1732804 x) (@lem1732811 x)). Qed.
Lemma lem1732813 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1732814 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1732812 x) (@lem1732813 x)). Qed.
Lemma lem1732815 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732816 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1732815) (@lem1732814 x)). Qed.
Lemma lem1732817 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732818 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1732816 x) (@lem1732817)). Qed.
Lemma lem1732819 (x : real) (h1 : term2096 x) : term897.
Proof. exact (EQ_MP (@lem1732818 x) (@lem1732803 x h1)). Qed.
Lemma lem1732821 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732822 : term897 = term2523.
Proof. exact (@lem1732821 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732823 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732824 : term897 = False.
Proof. exact (TRANS (@lem1732822) (@lem1732823)). Qed.
Lemma lem1732825 (x : real) (h1 : term2096 x) : False.
Proof. exact (EQ_MP (@lem1732824) (@lem1732819 x h1)). Qed.
Lemma lem1732826 (x : real) (h1 : term2097 x) : False.
Proof. exact (or_elim (@lem1732722 x h1) (fun h0 : term2087 x => @lem1732741 x h0) (fun h0 : term2096 x => @lem1732825 x h0)). Qed.
Lemma lem1732827 (x : real) (h1 : term2076 x) : term2076 x.
Proof. exact (h1). Qed.
Lemma lem1732828 (x : real) (h1 : term2055 x) : term2055 x.
Proof. exact (h1). Qed.
Lemma lem1732829 (x : real) (h1 : term2055 x) : term2053 x.
Proof. exact (proj2 (@lem1732828 x h1)). Qed.
Lemma lem1732831 (x : real) (h1 : term2055 x) : term2062 x.
Proof. exact (proj2 (@lem1732829 x h1)). Qed.
Lemma lem1732833 (x : real) (h1 : term2055 x) : term2061 x.
Proof. exact (proj2 (@lem1732831 x h1)). Qed.
Lemma lem1732835 (x : real) (h1 : term2055 x) : term2060 x.
Proof. exact (proj2 (@lem1732833 x h1)). Qed.
Lemma lem1732837 (x : real) (h1 : term2055 x) : term1525 x.
Proof. exact (proj2 (@lem1732835 x h1)). Qed.
Lemma lem1732841 (x : real) (h1 : term2055 x) : term915.
Proof. exact (proj2 (@lem1732837 x h1)). Qed.
Lemma lem1732844 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732845 : term915 = False.
Proof. exact (@lem1732844 term185 (NUMERAL 0)). Qed.
Lemma lem1732846 (x : real) (h1 : term2055 x) : False.
Proof. exact (EQ_MP (@lem1732845) (@lem1732841 x h1)). Qed.
Lemma lem1732847 (x : real) (h1 : term2075 x) : term2075 x.
Proof. exact (h1). Qed.
Lemma lem1732848 (x : real) (h1 : term2075 x) : term2074 x.
Proof. exact (proj2 (@lem1732847 x h1)). Qed.
Lemma lem1732850 (x : real) (h1 : term2075 x) : term2073 x.
Proof. exact (proj2 (@lem1732848 x h1)). Qed.
Lemma lem1732852 (x : real) (h1 : term2075 x) : term2071 x.
Proof. exact (proj2 (@lem1732850 x h1)). Qed.
Lemma lem1732854 (x : real) (h1 : term2075 x) : term1687 x.
Proof. exact (proj2 (@lem1732852 x h1)). Qed.
Lemma lem1732855 (x : real) (h1 : term2075 x) : term179 x.
Proof. exact (proj1 (@lem1732852 x h1)). Qed.
Lemma lem1732857 (x : real) (h1 : term2075 x) : term1224 x.
Proof. exact (proj1 (@lem1732854 x h1)). Qed.
Lemma lem1732858 (x : real) (h1 : term2075 x) : term326 x.
Proof. exact (proj2 (@lem1732857 x h1)). Qed.
Lemma lem1732863 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732864 : term1117 = term2525.
Proof. exact (@lem1732863 (NUMERAL 0) term185). Qed.
Lemma lem1732865 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732866 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732867 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732866 h1) (fun h1 : term2525 = True => @lem1732865)). Qed.
Lemma lem1732868 : term2525 = True.
Proof. exact (EQ_MP (@lem1732867) (@lem1732865)). Qed.
Lemma lem1732869 : term1117 = True.
Proof. exact (TRANS (@lem1732864) (@lem1732868)). Qed.
Lemma lem1732870 : True = term1117.
Proof. exact (SYM (@lem1732869)). Qed.
Lemma lem1732871 : term1117.
Proof. exact (EQ_MP (@lem1732870) (@lem0)). Qed.
Lemma lem1732872 (x : real) (h1 : term2075 x) : term2527 x.
Proof. exact (conj (@lem1732871) (@lem1732858 x h1)). Qed.
Lemma lem1732874 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1732875 (x : real) : term2529 x.
Proof. exact (@lem1732874 term24 x). Qed.
Lemma lem1732876 (x : real) (h1 : term2075 x) : term1223 x.
Proof. exact (@lem1732875 x (@lem1732872 x h1)). Qed.
Lemma lem1732877 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1732878 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1732879 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1732878) (@lem1732877 x)). Qed.
Lemma lem1732880 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732881 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1732879 x) (@lem1732880)). Qed.
Lemma lem1732882 (x : real) (h1 : term2075 x) : term326 x.
Proof. exact (EQ_MP (@lem1732881 x) (@lem1732876 x h1)). Qed.
Lemma lem1732884 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732885 : term1117 = term2525.
Proof. exact (@lem1732884 (NUMERAL 0) term185). Qed.
Lemma lem1732886 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1732887 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1732888 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1732887 h1) (fun h1 : term2525 = True => @lem1732886)). Qed.
Lemma lem1732889 : term2525 = True.
Proof. exact (EQ_MP (@lem1732888) (@lem1732886)). Qed.
Lemma lem1732890 : term1117 = True.
Proof. exact (TRANS (@lem1732885) (@lem1732889)). Qed.
Lemma lem1732891 : True = term1117.
Proof. exact (SYM (@lem1732890)). Qed.
Lemma lem1732892 : term1117.
Proof. exact (EQ_MP (@lem1732891) (@lem0)). Qed.
Lemma lem1732893 (x : real) (h1 : term2075 x) : term2530 x.
Proof. exact (conj (@lem1732892) (@lem1732855 x h1)). Qed.
Lemma lem1732895 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1732896 (x : real) : term2532 x.
Proof. exact (@lem1732895 term24 (term176 x)). Qed.
Lemma lem1732897 (x : real) (h1 : term2075 x) : term2533 x.
Proof. exact (@lem1732896 x (@lem1732893 x h1)). Qed.
Lemma lem1732898 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1732899 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732900 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1732899) (@lem1732898 x)). Qed.
Lemma lem1732901 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732902 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1732900 x) (@lem1732901)). Qed.
Lemma lem1732903 (x : real) (h1 : term2075 x) : term179 x.
Proof. exact (EQ_MP (@lem1732902 x) (@lem1732897 x h1)). Qed.
Lemma lem1732904 (x : real) (h1 : term2075 x) : term2536 x.
Proof. exact (conj (@lem1732903 x h1) (@lem1732882 x h1)). Qed.
Lemma lem1732906 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1732907 (x : real) : term2538 x.
Proof. exact (@lem1732906 (term176 x) x). Qed.
Lemma lem1732908 (x : real) (h1 : term2075 x) : term2539 x.
Proof. exact (@lem1732907 x (@lem1732904 x h1)). Qed.
Lemma lem1732909 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1732911 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1732912 : term1261 = term76.
Proof. exact (@lem1732911 term185). Qed.
Lemma lem1732913 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1732914 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1732913) (@lem1732912)). Qed.
Lemma lem1732915 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1732916 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1732914) (@lem1732915 x)). Qed.
Lemma lem1732917 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1732909 x) (@lem1732916 x)). Qed.
Lemma lem1732918 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1732919 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1732917 x) (@lem1732918 x)). Qed.
Lemma lem1732920 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1732921 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1732920) (@lem1732919 x)). Qed.
Lemma lem1732922 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1732923 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1732921 x) (@lem1732922)). Qed.
Lemma lem1732924 (x : real) (h1 : term2075 x) : term897.
Proof. exact (EQ_MP (@lem1732923 x) (@lem1732908 x h1)). Qed.
Lemma lem1732926 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732927 : term897 = term2523.
Proof. exact (@lem1732926 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732928 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732929 : term897 = False.
Proof. exact (TRANS (@lem1732927) (@lem1732928)). Qed.
Lemma lem1732930 (x : real) (h1 : term2075 x) : False.
Proof. exact (EQ_MP (@lem1732929) (@lem1732924 x h1)). Qed.
Lemma lem1732931 (x : real) (h1 : term2076 x) : False.
Proof. exact (or_elim (@lem1732827 x h1) (fun h0 : term2055 x => @lem1732846 x h0) (fun h0 : term2075 x => @lem1732930 x h0)). Qed.
Lemma lem1732932 (x : real) (h1 : term2099 x) : False.
Proof. exact (or_elim (@lem1732721 x h1) (fun h0 : term2097 x => @lem1732826 x h0) (fun h0 : term2076 x => @lem1732931 x h0)). Qed.
Lemma lem1732933 (x : real) (h1 : term2129 x) : term2129 x.
Proof. exact (h1). Qed.
Lemma lem1732934 (x : real) (h1 : term2122 x) : term2122 x.
Proof. exact (h1). Qed.
Lemma lem1732935 (x : real) (h1 : term2122 x) : term2120 x.
Proof. exact (proj2 (@lem1732934 x h1)). Qed.
Lemma lem1732937 (x : real) (h1 : term2122 x) : term2109 x.
Proof. exact (proj2 (@lem1732935 x h1)). Qed.
Lemma lem1732939 (x : real) (h1 : term2122 x) : term2108 x.
Proof. exact (proj2 (@lem1732937 x h1)). Qed.
Lemma lem1732941 (x : real) (h1 : term2122 x) : term2107 x.
Proof. exact (proj2 (@lem1732939 x h1)). Qed.
Lemma lem1732945 (x : real) (h1 : term2122 x) : term2106.
Proof. exact (proj2 (@lem1732941 x h1)). Qed.
Lemma lem1732947 (x : real) (h1 : term2122 x) : term915.
Proof. exact (proj2 (@lem1732945 x h1)). Qed.
Lemma lem1732950 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732951 : term915 = False.
Proof. exact (@lem1732950 term185 (NUMERAL 0)). Qed.
Lemma lem1732952 (x : real) (h1 : term2122 x) : False.
Proof. exact (EQ_MP (@lem1732951) (@lem1732947 x h1)). Qed.
Lemma lem1732953 (x : real) (h1 : term2128 x) : term2128 x.
Proof. exact (h1). Qed.
Lemma lem1732954 (x : real) (h1 : term2128 x) : term2127 x.
Proof. exact (proj2 (@lem1732953 x h1)). Qed.
Lemma lem1732956 (x : real) (h1 : term2128 x) : term2109 x.
Proof. exact (proj2 (@lem1732954 x h1)). Qed.
Lemma lem1732958 (x : real) (h1 : term2128 x) : term2108 x.
Proof. exact (proj2 (@lem1732956 x h1)). Qed.
Lemma lem1732960 (x : real) (h1 : term2128 x) : term2107 x.
Proof. exact (proj2 (@lem1732958 x h1)). Qed.
Lemma lem1732964 (x : real) (h1 : term2128 x) : term2106.
Proof. exact (proj2 (@lem1732960 x h1)). Qed.
Lemma lem1732966 (x : real) (h1 : term2128 x) : term915.
Proof. exact (proj2 (@lem1732964 x h1)). Qed.
Lemma lem1732969 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1732970 : term915 = False.
Proof. exact (@lem1732969 term185 (NUMERAL 0)). Qed.
Lemma lem1732971 (x : real) (h1 : term2128 x) : False.
Proof. exact (EQ_MP (@lem1732970) (@lem1732966 x h1)). Qed.
Lemma lem1732972 (x : real) (h1 : term2129 x) : False.
Proof. exact (or_elim (@lem1732933 x h1) (fun h0 : term2122 x => @lem1732952 x h0) (fun h0 : term2128 x => @lem1732971 x h0)). Qed.
Lemma lem1732973 (x : real) (h1 : term2132 x) : False.
Proof. exact (or_elim (@lem1732720 x h1) (fun h0 : term2099 x => @lem1732932 x h0) (fun h0 : term2129 x => @lem1732972 x h0)). Qed.
Lemma lem1732974 (x : real) (h1 : term2134 x) : False.
Proof. exact (or_elim (@lem1732465 x h1) (fun h0 : term2022 x => @lem1732719 x h0) (fun h0 : term2132 x => @lem1732973 x h0)). Qed.
Lemma lem1732975 (x : real) (h1 : term2136 x) : False.
Proof. exact (or_elim (@lem1732222 x h1) (fun h0 : term1919 x => @lem1732464 x h0) (fun h0 : term2134 x => @lem1732974 x h0)). Qed.
Lemma lem1732976 (x : real) (h1 : term2517 x) : term2517 x.
Proof. exact (h1). Qed.
Lemma lem1732977 (x : real) (h1 : term2322 x) : term2322 x.
Proof. exact (h1). Qed.
Lemma lem1732978 (x : real) (h1 : term2230 x) : term2230 x.
Proof. exact (h1). Qed.
Lemma lem1732979 (x : real) (h1 : term2207 x) : term2207 x.
Proof. exact (h1). Qed.
Lemma lem1732980 (x : real) (h1 : term2205 x) : term2205 x.
Proof. exact (h1). Qed.
Lemma lem1732981 (x : real) (h1 : term2199 x) : term2199 x.
Proof. exact (h1). Qed.
Lemma lem1732982 (x : real) (h1 : term2199 x) : term2198 x.
Proof. exact (proj2 (@lem1732981 x h1)). Qed.
Lemma lem1732984 (x : real) (h1 : term2199 x) : term2197 x.
Proof. exact (proj2 (@lem1732982 x h1)). Qed.
Lemma lem1732986 (x : real) (h1 : term2199 x) : term1424 x.
Proof. exact (proj2 (@lem1732984 x h1)). Qed.
Lemma lem1732988 (x : real) (h1 : term2199 x) : term966 x.
Proof. exact (proj2 (@lem1732986 x h1)). Qed.
Lemma lem1732990 (x : real) (h1 : term2199 x) : term899 x.
Proof. exact (proj2 (@lem1732988 x h1)). Qed.
Lemma lem1732992 (x : real) (h1 : term2199 x) : term897.
Proof. exact (proj2 (@lem1732990 x h1)). Qed.
Lemma lem1732995 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1732996 : term897 = term2523.
Proof. exact (@lem1732995 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1732997 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1732998 : term897 = False.
Proof. exact (TRANS (@lem1732996) (@lem1732997)). Qed.
Lemma lem1732999 (x : real) (h1 : term2199 x) : False.
Proof. exact (EQ_MP (@lem1732998) (@lem1732992 x h1)). Qed.
Lemma lem1733000 (x : real) (h1 : term2203 x) : term2203 x.
Proof. exact (h1). Qed.
Lemma lem1733001 (x : real) (h1 : term2203 x) : term2202 x.
Proof. exact (proj2 (@lem1733000 x h1)). Qed.
Lemma lem1733003 (x : real) (h1 : term2203 x) : term2201 x.
Proof. exact (proj2 (@lem1733001 x h1)). Qed.
Lemma lem1733005 (x : real) (h1 : term2203 x) : term1430 x.
Proof. exact (proj2 (@lem1733003 x h1)). Qed.
Lemma lem1733007 (x : real) (h1 : term2203 x) : term974 x.
Proof. exact (proj2 (@lem1733005 x h1)). Qed.
Lemma lem1733009 (x : real) (h1 : term2203 x) : term938 x.
Proof. exact (proj2 (@lem1733007 x h1)). Qed.
Lemma lem1733011 (x : real) (h1 : term2203 x) : term936.
Proof. exact (proj2 (@lem1733009 x h1)). Qed.
Lemma lem1733014 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733015 : term936 = False.
Proof. exact (@lem1733014 term923 (NUMERAL 0)). Qed.
Lemma lem1733016 (x : real) (h1 : term2203 x) : False.
Proof. exact (EQ_MP (@lem1733015) (@lem1733011 x h1)). Qed.
Lemma lem1733017 (x : real) (h1 : term2205 x) : False.
Proof. exact (or_elim (@lem1732980 x h1) (fun h0 : term2199 x => @lem1732999 x h0) (fun h0 : term2203 x => @lem1733016 x h0)). Qed.
Lemma lem1733018 (x : real) (h1 : term2180 x) : term2180 x.
Proof. exact (h1). Qed.
Lemma lem1733019 (x : real) (h1 : term2174 x) : term2174 x.
Proof. exact (h1). Qed.
Lemma lem1733020 (x : real) (h1 : term2174 x) : term2173 x.
Proof. exact (proj2 (@lem1733019 x h1)). Qed.
Lemma lem1733022 (x : real) (h1 : term2174 x) : term2172 x.
Proof. exact (proj2 (@lem1733020 x h1)). Qed.
Lemma lem1733024 (x : real) (h1 : term2174 x) : term1395 x.
Proof. exact (proj2 (@lem1733022 x h1)). Qed.
Lemma lem1733026 (x : real) (h1 : term2174 x) : term901 x.
Proof. exact (proj2 (@lem1733024 x h1)). Qed.
Lemma lem1733028 (x : real) (h1 : term2174 x) : term899 x.
Proof. exact (proj2 (@lem1733026 x h1)). Qed.
Lemma lem1733030 (x : real) (h1 : term2174 x) : term897.
Proof. exact (proj2 (@lem1733028 x h1)). Qed.
Lemma lem1733033 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733034 : term897 = term2523.
Proof. exact (@lem1733033 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733035 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733036 : term897 = False.
Proof. exact (TRANS (@lem1733034) (@lem1733035)). Qed.
Lemma lem1733037 (x : real) (h1 : term2174 x) : False.
Proof. exact (EQ_MP (@lem1733036) (@lem1733030 x h1)). Qed.
Lemma lem1733038 (x : real) (h1 : term2178 x) : term2178 x.
Proof. exact (h1). Qed.
Lemma lem1733039 (x : real) (h1 : term2178 x) : term2177 x.
Proof. exact (proj2 (@lem1733038 x h1)). Qed.
Lemma lem1733041 (x : real) (h1 : term2178 x) : term2176 x.
Proof. exact (proj2 (@lem1733039 x h1)). Qed.
Lemma lem1733043 (x : real) (h1 : term2178 x) : term1401 x.
Proof. exact (proj2 (@lem1733041 x h1)). Qed.
Lemma lem1733045 (x : real) (h1 : term2178 x) : term940 x.
Proof. exact (proj2 (@lem1733043 x h1)). Qed.
Lemma lem1733047 (x : real) (h1 : term2178 x) : term938 x.
Proof. exact (proj2 (@lem1733045 x h1)). Qed.
Lemma lem1733049 (x : real) (h1 : term2178 x) : term936.
Proof. exact (proj2 (@lem1733047 x h1)). Qed.
Lemma lem1733052 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733053 : term936 = False.
Proof. exact (@lem1733052 term923 (NUMERAL 0)). Qed.
Lemma lem1733054 (x : real) (h1 : term2178 x) : False.
Proof. exact (EQ_MP (@lem1733053) (@lem1733049 x h1)). Qed.
Lemma lem1733055 (x : real) (h1 : term2180 x) : False.
Proof. exact (or_elim (@lem1733018 x h1) (fun h0 : term2174 x => @lem1733037 x h0) (fun h0 : term2178 x => @lem1733054 x h0)). Qed.
Lemma lem1733056 (x : real) (h1 : term2207 x) : False.
Proof. exact (or_elim (@lem1732979 x h1) (fun h0 : term2205 x => @lem1733017 x h0) (fun h0 : term2180 x => @lem1733055 x h0)). Qed.
Lemma lem1733057 (x : real) (h1 : term2227 x) : term2227 x.
Proof. exact (h1). Qed.
Lemma lem1733058 (x : real) (h1 : term2220 x) : term2220 x.
Proof. exact (h1). Qed.
Lemma lem1733059 (x : real) (h1 : term2220 x) : term2218 x.
Proof. exact (proj2 (@lem1733058 x h1)). Qed.
Lemma lem1733061 (x : real) (h1 : term2220 x) : term1457 x.
Proof. exact (proj2 (@lem1733059 x h1)). Qed.
Lemma lem1733063 (x : real) (h1 : term2220 x) : term1029 x.
Proof. exact (proj2 (@lem1733061 x h1)). Qed.
Lemma lem1733065 (x : real) (h1 : term2220 x) : term1001 x.
Proof. exact (proj2 (@lem1733063 x h1)). Qed.
Lemma lem1733067 (x : real) (h1 : term2220 x) : term1000.
Proof. exact (proj2 (@lem1733065 x h1)). Qed.
Lemma lem1733070 (x : real) (h1 : term2220 x) : term897.
Proof. exact (proj1 (@lem1733067 x h1)). Qed.
Lemma lem1733072 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733073 : term897 = term2523.
Proof. exact (@lem1733072 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733074 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733075 : term897 = False.
Proof. exact (TRANS (@lem1733073) (@lem1733074)). Qed.
Lemma lem1733076 (x : real) (h1 : term2220 x) : False.
Proof. exact (EQ_MP (@lem1733075) (@lem1733070 x h1)). Qed.
Lemma lem1733077 (x : real) (h1 : term2226 x) : term2226 x.
Proof. exact (h1). Qed.
Lemma lem1733078 (x : real) (h1 : term2226 x) : term2225 x.
Proof. exact (proj2 (@lem1733077 x h1)). Qed.
Lemma lem1733080 (x : real) (h1 : term2226 x) : term1459 x.
Proof. exact (proj2 (@lem1733078 x h1)). Qed.
Lemma lem1733082 (x : real) (h1 : term2226 x) : term1032 x.
Proof. exact (proj2 (@lem1733080 x h1)). Qed.
Lemma lem1733084 (x : real) (h1 : term2226 x) : term1001 x.
Proof. exact (proj2 (@lem1733082 x h1)). Qed.
Lemma lem1733086 (x : real) (h1 : term2226 x) : term1000.
Proof. exact (proj2 (@lem1733084 x h1)). Qed.
Lemma lem1733089 (x : real) (h1 : term2226 x) : term897.
Proof. exact (proj1 (@lem1733086 x h1)). Qed.
Lemma lem1733091 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733092 : term897 = term2523.
Proof. exact (@lem1733091 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733093 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733094 : term897 = False.
Proof. exact (TRANS (@lem1733092) (@lem1733093)). Qed.
Lemma lem1733095 (x : real) (h1 : term2226 x) : False.
Proof. exact (EQ_MP (@lem1733094) (@lem1733089 x h1)). Qed.
Lemma lem1733096 (x : real) (h1 : term2227 x) : False.
Proof. exact (or_elim (@lem1733057 x h1) (fun h0 : term2220 x => @lem1733076 x h0) (fun h0 : term2226 x => @lem1733095 x h0)). Qed.
Lemma lem1733097 (x : real) (h1 : term2230 x) : False.
Proof. exact (or_elim (@lem1732978 x h1) (fun h0 : term2207 x => @lem1733056 x h0) (fun h0 : term2227 x => @lem1733096 x h0)). Qed.
Lemma lem1733098 (x : real) (h1 : term2320 x) : term2320 x.
Proof. exact (h1). Qed.
Lemma lem1733099 (x : real) (h1 : term2297 x) : term2297 x.
Proof. exact (h1). Qed.
Lemma lem1733100 (x : real) (h1 : term2295 x) : term2295 x.
Proof. exact (h1). Qed.
Lemma lem1733101 (x : real) (h1 : term2291 x) : term2291 x.
Proof. exact (h1). Qed.
Lemma lem1733102 (x : real) (h1 : term2291 x) : term2290 x.
Proof. exact (proj2 (@lem1733101 x h1)). Qed.
Lemma lem1733104 (x : real) (h1 : term2291 x) : term2289 x.
Proof. exact (proj2 (@lem1733102 x h1)). Qed.
Lemma lem1733106 (x : real) (h1 : term2291 x) : term1567 x.
Proof. exact (proj2 (@lem1733104 x h1)). Qed.
Lemma lem1733108 (x : real) (h1 : term2291 x) : term1565 x.
Proof. exact (proj2 (@lem1733106 x h1)). Qed.
Lemma lem1733110 (x : real) (h1 : term2291 x) : term1525 x.
Proof. exact (proj2 (@lem1733108 x h1)). Qed.
Lemma lem1733112 (x : real) (h1 : term2291 x) : term915.
Proof. exact (proj2 (@lem1733110 x h1)). Qed.
Lemma lem1733115 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733116 : term915 = False.
Proof. exact (@lem1733115 term185 (NUMERAL 0)). Qed.
Lemma lem1733117 (x : real) (h1 : term2291 x) : False.
Proof. exact (EQ_MP (@lem1733116) (@lem1733112 x h1)). Qed.
Lemma lem1733118 (x : real) (h1 : term2293 x) : term2293 x.
Proof. exact (h1). Qed.
Lemma lem1733119 (x : real) (h1 : term2293 x) : term2290 x.
Proof. exact (proj2 (@lem1733118 x h1)). Qed.
Lemma lem1733121 (x : real) (h1 : term2293 x) : term2289 x.
Proof. exact (proj2 (@lem1733119 x h1)). Qed.
Lemma lem1733123 (x : real) (h1 : term2293 x) : term1567 x.
Proof. exact (proj2 (@lem1733121 x h1)). Qed.
Lemma lem1733125 (x : real) (h1 : term2293 x) : term1565 x.
Proof. exact (proj2 (@lem1733123 x h1)). Qed.
Lemma lem1733127 (x : real) (h1 : term2293 x) : term1525 x.
Proof. exact (proj2 (@lem1733125 x h1)). Qed.
Lemma lem1733129 (x : real) (h1 : term2293 x) : term915.
Proof. exact (proj2 (@lem1733127 x h1)). Qed.
Lemma lem1733132 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733133 : term915 = False.
Proof. exact (@lem1733132 term185 (NUMERAL 0)). Qed.
Lemma lem1733134 (x : real) (h1 : term2293 x) : False.
Proof. exact (EQ_MP (@lem1733133) (@lem1733129 x h1)). Qed.
Lemma lem1733135 (x : real) (h1 : term2295 x) : False.
Proof. exact (or_elim (@lem1733100 x h1) (fun h0 : term2291 x => @lem1733117 x h0) (fun h0 : term2293 x => @lem1733134 x h0)). Qed.
Lemma lem1733136 (x : real) (h1 : term2272 x) : term2272 x.
Proof. exact (h1). Qed.
Lemma lem1733137 (x : real) (h1 : term2268 x) : term2268 x.
Proof. exact (h1). Qed.
Lemma lem1733138 (x : real) (h1 : term2268 x) : term2267 x.
Proof. exact (proj2 (@lem1733137 x h1)). Qed.
Lemma lem1733140 (x : real) (h1 : term2268 x) : term2266 x.
Proof. exact (proj2 (@lem1733138 x h1)). Qed.
Lemma lem1733142 (x : real) (h1 : term2268 x) : term1529 x.
Proof. exact (proj2 (@lem1733140 x h1)). Qed.
Lemma lem1733144 (x : real) (h1 : term2268 x) : term1527 x.
Proof. exact (proj2 (@lem1733142 x h1)). Qed.
Lemma lem1733146 (x : real) (h1 : term2268 x) : term1525 x.
Proof. exact (proj2 (@lem1733144 x h1)). Qed.
Lemma lem1733148 (x : real) (h1 : term2268 x) : term915.
Proof. exact (proj2 (@lem1733146 x h1)). Qed.
Lemma lem1733151 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733152 : term915 = False.
Proof. exact (@lem1733151 term185 (NUMERAL 0)). Qed.
Lemma lem1733153 (x : real) (h1 : term2268 x) : False.
Proof. exact (EQ_MP (@lem1733152) (@lem1733148 x h1)). Qed.
Lemma lem1733154 (x : real) (h1 : term2270 x) : term2270 x.
Proof. exact (h1). Qed.
Lemma lem1733155 (x : real) (h1 : term2270 x) : term2267 x.
Proof. exact (proj2 (@lem1733154 x h1)). Qed.
Lemma lem1733157 (x : real) (h1 : term2270 x) : term2266 x.
Proof. exact (proj2 (@lem1733155 x h1)). Qed.
Lemma lem1733159 (x : real) (h1 : term2270 x) : term1529 x.
Proof. exact (proj2 (@lem1733157 x h1)). Qed.
Lemma lem1733161 (x : real) (h1 : term2270 x) : term1527 x.
Proof. exact (proj2 (@lem1733159 x h1)). Qed.
Lemma lem1733163 (x : real) (h1 : term2270 x) : term1525 x.
Proof. exact (proj2 (@lem1733161 x h1)). Qed.
Lemma lem1733165 (x : real) (h1 : term2270 x) : term915.
Proof. exact (proj2 (@lem1733163 x h1)). Qed.
Lemma lem1733168 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733169 : term915 = False.
Proof. exact (@lem1733168 term185 (NUMERAL 0)). Qed.
Lemma lem1733170 (x : real) (h1 : term2270 x) : False.
Proof. exact (EQ_MP (@lem1733169) (@lem1733165 x h1)). Qed.
Lemma lem1733171 (x : real) (h1 : term2272 x) : False.
Proof. exact (or_elim (@lem1733136 x h1) (fun h0 : term2268 x => @lem1733153 x h0) (fun h0 : term2270 x => @lem1733170 x h0)). Qed.
Lemma lem1733172 (x : real) (h1 : term2297 x) : False.
Proof. exact (or_elim (@lem1733099 x h1) (fun h0 : term2295 x => @lem1733135 x h0) (fun h0 : term2272 x => @lem1733171 x h0)). Qed.
Lemma lem1733173 (x : real) (h1 : term2317 x) : term2317 x.
Proof. exact (h1). Qed.
Lemma lem1733174 (x : real) (h1 : term2310 x) : term2310 x.
Proof. exact (h1). Qed.
Lemma lem1733175 (x : real) (h1 : term2310 x) : term2308 x.
Proof. exact (proj2 (@lem1733174 x h1)). Qed.
Lemma lem1733177 (x : real) (h1 : term2310 x) : term1612 x.
Proof. exact (proj2 (@lem1733175 x h1)). Qed.
Lemma lem1733179 (x : real) (h1 : term2310 x) : term1611 x.
Proof. exact (proj2 (@lem1733177 x h1)). Qed.
Lemma lem1733181 (x : real) (h1 : term2310 x) : term1589 x.
Proof. exact (proj2 (@lem1733179 x h1)). Qed.
Lemma lem1733182 (x : real) (h1 : term2310 x) : term196 x.
Proof. exact (proj1 (@lem1733179 x h1)). Qed.
Lemma lem1733184 (x : real) (h1 : term2310 x) : term236 x.
Proof. exact (proj1 (@lem1733181 x h1)). Qed.
Lemma lem1733188 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733189 : term1117 = term2525.
Proof. exact (@lem1733188 (NUMERAL 0) term185). Qed.
Lemma lem1733190 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733191 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733192 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733191 h1) (fun h1 : term2525 = True => @lem1733190)). Qed.
Lemma lem1733193 : term2525 = True.
Proof. exact (EQ_MP (@lem1733192) (@lem1733190)). Qed.
Lemma lem1733194 : term1117 = True.
Proof. exact (TRANS (@lem1733189) (@lem1733193)). Qed.
Lemma lem1733195 : True = term1117.
Proof. exact (SYM (@lem1733194)). Qed.
Lemma lem1733196 : term1117.
Proof. exact (EQ_MP (@lem1733195) (@lem0)). Qed.
Lemma lem1733197 (x : real) (h1 : term2310 x) : term2546 x.
Proof. exact (conj (@lem1733196) (@lem1733184 x h1)). Qed.
Lemma lem1733199 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1733200 (x : real) : term2547 x.
Proof. exact (@lem1733199 term24 (term176 x)). Qed.
Lemma lem1733201 (x : real) (h1 : term2310 x) : term2548 x.
Proof. exact (@lem1733200 x (@lem1733197 x h1)). Qed.
Lemma lem1733202 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1733203 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1733204 (x : real) : (term2549 x) = (term235 x).
Proof. exact (MK_COMB (@lem1733203) (@lem1733202 x)). Qed.
Lemma lem1733205 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733206 (x : real) : (term2548 x) = (term236 x).
Proof. exact (MK_COMB (@lem1733204 x) (@lem1733205)). Qed.
Lemma lem1733207 (x : real) (h1 : term2310 x) : term236 x.
Proof. exact (EQ_MP (@lem1733206 x) (@lem1733201 x h1)). Qed.
Lemma lem1733209 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733210 : term1117 = term2525.
Proof. exact (@lem1733209 (NUMERAL 0) term185). Qed.
Lemma lem1733211 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733212 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733213 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733212 h1) (fun h1 : term2525 = True => @lem1733211)). Qed.
Lemma lem1733214 : term2525 = True.
Proof. exact (EQ_MP (@lem1733213) (@lem1733211)). Qed.
Lemma lem1733215 : term1117 = True.
Proof. exact (TRANS (@lem1733210) (@lem1733214)). Qed.
Lemma lem1733216 : True = term1117.
Proof. exact (SYM (@lem1733215)). Qed.
Lemma lem1733217 : term1117.
Proof. exact (EQ_MP (@lem1733216) (@lem0)). Qed.
Lemma lem1733218 (x : real) (h1 : term2310 x) : term2550 x.
Proof. exact (conj (@lem1733217) (@lem1733182 x h1)). Qed.
Lemma lem1733220 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1733221 (x : real) : term2551 x.
Proof. exact (@lem1733220 term24 x). Qed.
Lemma lem1733222 (x : real) (h1 : term2310 x) : term809 x.
Proof. exact (@lem1733221 x (@lem1733218 x h1)). Qed.
Lemma lem1733223 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1733224 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733225 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1733224) (@lem1733223 x)). Qed.
Lemma lem1733226 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733227 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1733225 x) (@lem1733226)). Qed.
Lemma lem1733228 (x : real) (h1 : term2310 x) : term196 x.
Proof. exact (EQ_MP (@lem1733227 x) (@lem1733222 x h1)). Qed.
Lemma lem1733229 (x : real) (h1 : term2310 x) : term2552 x.
Proof. exact (conj (@lem1733228 x h1) (@lem1733207 x h1)). Qed.
Lemma lem1733231 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1733232 (x : real) : term2553 x.
Proof. exact (@lem1733231 x (term176 x)). Qed.
Lemma lem1733233 (x : real) (h1 : term2310 x) : term2554 x.
Proof. exact (@lem1733232 x (@lem1733229 x h1)). Qed.
Lemma lem1733234 (x : real) : (term2555 x) = (term2541 x).
Proof. exact (@lem1483442 term73 x). Qed.
Lemma lem1733236 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1733237 : term1261 = term76.
Proof. exact (@lem1733236 term185). Qed.
Lemma lem1733238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1733239 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1733238) (@lem1733237)). Qed.
Lemma lem1733240 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1733241 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1733239) (@lem1733240 x)). Qed.
Lemma lem1733242 (x : real) : (term2555 x) = (term2544 x).
Proof. exact (TRANS (@lem1733234 x) (@lem1733241 x)). Qed.
Lemma lem1733243 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1733244 (x : real) : (term2555 x) = term76.
Proof. exact (TRANS (@lem1733242 x) (@lem1733243 x)). Qed.
Lemma lem1733245 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733246 (x : real) : (term2556 x) = term896.
Proof. exact (MK_COMB (@lem1733245) (@lem1733244 x)). Qed.
Lemma lem1733247 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733248 (x : real) : (term2554 x) = term897.
Proof. exact (MK_COMB (@lem1733246 x) (@lem1733247)). Qed.
Lemma lem1733249 (x : real) (h1 : term2310 x) : term897.
Proof. exact (EQ_MP (@lem1733248 x) (@lem1733233 x h1)). Qed.
Lemma lem1733251 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733252 : term897 = term2523.
Proof. exact (@lem1733251 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733253 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733254 : term897 = False.
Proof. exact (TRANS (@lem1733252) (@lem1733253)). Qed.
Lemma lem1733255 (x : real) (h1 : term2310 x) : False.
Proof. exact (EQ_MP (@lem1733254) (@lem1733249 x h1)). Qed.
Lemma lem1733256 (x : real) (h1 : term2316 x) : term2316 x.
Proof. exact (h1). Qed.
Lemma lem1733257 (x : real) (h1 : term2316 x) : term2315 x.
Proof. exact (proj2 (@lem1733256 x h1)). Qed.
Lemma lem1733259 (x : real) (h1 : term2316 x) : term1616 x.
Proof. exact (proj2 (@lem1733257 x h1)). Qed.
Lemma lem1733261 (x : real) (h1 : term2316 x) : term1614 x.
Proof. exact (proj2 (@lem1733259 x h1)). Qed.
Lemma lem1733262 (x : real) (h1 : term2316 x) : term326 x.
Proof. exact (proj1 (@lem1733259 x h1)). Qed.
Lemma lem1733264 (x : real) (h1 : term2316 x) : term179 x.
Proof. exact (proj1 (@lem1733261 x h1)). Qed.
Lemma lem1733270 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733271 : term1117 = term2525.
Proof. exact (@lem1733270 (NUMERAL 0) term185). Qed.
Lemma lem1733272 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733273 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733274 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733273 h1) (fun h1 : term2525 = True => @lem1733272)). Qed.
Lemma lem1733275 : term2525 = True.
Proof. exact (EQ_MP (@lem1733274) (@lem1733272)). Qed.
Lemma lem1733276 : term1117 = True.
Proof. exact (TRANS (@lem1733271) (@lem1733275)). Qed.
Lemma lem1733277 : True = term1117.
Proof. exact (SYM (@lem1733276)). Qed.
Lemma lem1733278 : term1117.
Proof. exact (EQ_MP (@lem1733277) (@lem0)). Qed.
Lemma lem1733279 (x : real) (h1 : term2316 x) : term2527 x.
Proof. exact (conj (@lem1733278) (@lem1733262 x h1)). Qed.
Lemma lem1733281 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1733282 (x : real) : term2529 x.
Proof. exact (@lem1733281 term24 x). Qed.
Lemma lem1733283 (x : real) (h1 : term2316 x) : term1223 x.
Proof. exact (@lem1733282 x (@lem1733279 x h1)). Qed.
Lemma lem1733284 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1733285 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1733286 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1733285) (@lem1733284 x)). Qed.
Lemma lem1733287 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733288 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1733286 x) (@lem1733287)). Qed.
Lemma lem1733289 (x : real) (h1 : term2316 x) : term326 x.
Proof. exact (EQ_MP (@lem1733288 x) (@lem1733283 x h1)). Qed.
Lemma lem1733291 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733292 : term1117 = term2525.
Proof. exact (@lem1733291 (NUMERAL 0) term185). Qed.
Lemma lem1733293 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733294 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733295 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733294 h1) (fun h1 : term2525 = True => @lem1733293)). Qed.
Lemma lem1733296 : term2525 = True.
Proof. exact (EQ_MP (@lem1733295) (@lem1733293)). Qed.
Lemma lem1733297 : term1117 = True.
Proof. exact (TRANS (@lem1733292) (@lem1733296)). Qed.
Lemma lem1733298 : True = term1117.
Proof. exact (SYM (@lem1733297)). Qed.
Lemma lem1733299 : term1117.
Proof. exact (EQ_MP (@lem1733298) (@lem0)). Qed.
Lemma lem1733300 (x : real) (h1 : term2316 x) : term2530 x.
Proof. exact (conj (@lem1733299) (@lem1733264 x h1)). Qed.
Lemma lem1733302 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1733303 (x : real) : term2532 x.
Proof. exact (@lem1733302 term24 (term176 x)). Qed.
Lemma lem1733304 (x : real) (h1 : term2316 x) : term2533 x.
Proof. exact (@lem1733303 x (@lem1733300 x h1)). Qed.
Lemma lem1733305 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1733306 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733307 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1733306) (@lem1733305 x)). Qed.
Lemma lem1733308 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733309 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1733307 x) (@lem1733308)). Qed.
Lemma lem1733310 (x : real) (h1 : term2316 x) : term179 x.
Proof. exact (EQ_MP (@lem1733309 x) (@lem1733304 x h1)). Qed.
Lemma lem1733311 (x : real) (h1 : term2316 x) : term2536 x.
Proof. exact (conj (@lem1733310 x h1) (@lem1733289 x h1)). Qed.
Lemma lem1733313 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1733314 (x : real) : term2538 x.
Proof. exact (@lem1733313 (term176 x) x). Qed.
Lemma lem1733315 (x : real) (h1 : term2316 x) : term2539 x.
Proof. exact (@lem1733314 x (@lem1733311 x h1)). Qed.
Lemma lem1733316 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1733318 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1733319 : term1261 = term76.
Proof. exact (@lem1733318 term185). Qed.
Lemma lem1733320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1733321 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1733320) (@lem1733319)). Qed.
Lemma lem1733322 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1733323 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1733321) (@lem1733322 x)). Qed.
Lemma lem1733324 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1733316 x) (@lem1733323 x)). Qed.
Lemma lem1733325 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1733326 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1733324 x) (@lem1733325 x)). Qed.
Lemma lem1733327 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733328 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1733327) (@lem1733326 x)). Qed.
Lemma lem1733329 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733330 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1733328 x) (@lem1733329)). Qed.
Lemma lem1733331 (x : real) (h1 : term2316 x) : term897.
Proof. exact (EQ_MP (@lem1733330 x) (@lem1733315 x h1)). Qed.
Lemma lem1733333 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733334 : term897 = term2523.
Proof. exact (@lem1733333 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733335 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733336 : term897 = False.
Proof. exact (TRANS (@lem1733334) (@lem1733335)). Qed.
Lemma lem1733337 (x : real) (h1 : term2316 x) : False.
Proof. exact (EQ_MP (@lem1733336) (@lem1733331 x h1)). Qed.
Lemma lem1733338 (x : real) (h1 : term2317 x) : False.
Proof. exact (or_elim (@lem1733173 x h1) (fun h0 : term2310 x => @lem1733255 x h0) (fun h0 : term2316 x => @lem1733337 x h0)). Qed.
Lemma lem1733339 (x : real) (h1 : term2320 x) : False.
Proof. exact (or_elim (@lem1733098 x h1) (fun h0 : term2297 x => @lem1733172 x h0) (fun h0 : term2317 x => @lem1733338 x h0)). Qed.
Lemma lem1733340 (x : real) (h1 : term2322 x) : False.
Proof. exact (or_elim (@lem1732977 x h1) (fun h0 : term2230 x => @lem1733097 x h0) (fun h0 : term2320 x => @lem1733339 x h0)). Qed.
Lemma lem1733341 (x : real) (h1 : term2515 x) : term2515 x.
Proof. exact (h1). Qed.
Lemma lem1733342 (x : real) (h1 : term2409 x) : term2409 x.
Proof. exact (h1). Qed.
Lemma lem1733343 (x : real) (h1 : term2385 x) : term2385 x.
Proof. exact (h1). Qed.
Lemma lem1733344 (x : real) (h1 : term2383 x) : term2383 x.
Proof. exact (h1). Qed.
Lemma lem1733345 (x : real) (h1 : term2375 x) : term2375 x.
Proof. exact (h1). Qed.
Lemma lem1733346 (x : real) (h1 : term2375 x) : term2373 x.
Proof. exact (proj2 (@lem1733345 x h1)). Qed.
Lemma lem1733348 (x : real) (h1 : term2375 x) : term2380 x.
Proof. exact (proj2 (@lem1733346 x h1)). Qed.
Lemma lem1733350 (x : real) (h1 : term2375 x) : term2359 x.
Proof. exact (proj2 (@lem1733348 x h1)). Qed.
Lemma lem1733352 (x : real) (h1 : term2375 x) : term1958 x.
Proof. exact (proj2 (@lem1733350 x h1)). Qed.
Lemma lem1733354 (x : real) (h1 : term2375 x) : term1957 x.
Proof. exact (proj2 (@lem1733352 x h1)). Qed.
Lemma lem1733355 (x : real) (h1 : term2375 x) : term1224 x.
Proof. exact (proj1 (@lem1733352 x h1)). Qed.
Lemma lem1733357 (x : real) (h1 : term2375 x) : term236 x.
Proof. exact (proj1 (@lem1733355 x h1)). Qed.
Lemma lem1733359 (x : real) (h1 : term2375 x) : term196 x.
Proof. exact (proj1 (@lem1733354 x h1)). Qed.
Lemma lem1733361 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733362 : term1117 = term2525.
Proof. exact (@lem1733361 (NUMERAL 0) term185). Qed.
Lemma lem1733363 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733364 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733365 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733364 h1) (fun h1 : term2525 = True => @lem1733363)). Qed.
Lemma lem1733366 : term2525 = True.
Proof. exact (EQ_MP (@lem1733365) (@lem1733363)). Qed.
Lemma lem1733367 : term1117 = True.
Proof. exact (TRANS (@lem1733362) (@lem1733366)). Qed.
Lemma lem1733368 : True = term1117.
Proof. exact (SYM (@lem1733367)). Qed.
Lemma lem1733369 : term1117.
Proof. exact (EQ_MP (@lem1733368) (@lem0)). Qed.
Lemma lem1733370 (x : real) (h1 : term2375 x) : term2546 x.
Proof. exact (conj (@lem1733369) (@lem1733357 x h1)). Qed.
Lemma lem1733372 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1733373 (x : real) : term2547 x.
Proof. exact (@lem1733372 term24 (term176 x)). Qed.
Lemma lem1733374 (x : real) (h1 : term2375 x) : term2548 x.
Proof. exact (@lem1733373 x (@lem1733370 x h1)). Qed.
Lemma lem1733375 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1733376 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1733377 (x : real) : (term2549 x) = (term235 x).
Proof. exact (MK_COMB (@lem1733376) (@lem1733375 x)). Qed.
Lemma lem1733378 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733379 (x : real) : (term2548 x) = (term236 x).
Proof. exact (MK_COMB (@lem1733377 x) (@lem1733378)). Qed.
Lemma lem1733380 (x : real) (h1 : term2375 x) : term236 x.
Proof. exact (EQ_MP (@lem1733379 x) (@lem1733374 x h1)). Qed.
Lemma lem1733382 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733383 : term1117 = term2525.
Proof. exact (@lem1733382 (NUMERAL 0) term185). Qed.
Lemma lem1733384 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733385 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733386 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733385 h1) (fun h1 : term2525 = True => @lem1733384)). Qed.
Lemma lem1733387 : term2525 = True.
Proof. exact (EQ_MP (@lem1733386) (@lem1733384)). Qed.
Lemma lem1733388 : term1117 = True.
Proof. exact (TRANS (@lem1733383) (@lem1733387)). Qed.
Lemma lem1733389 : True = term1117.
Proof. exact (SYM (@lem1733388)). Qed.
Lemma lem1733390 : term1117.
Proof. exact (EQ_MP (@lem1733389) (@lem0)). Qed.
Lemma lem1733391 (x : real) (h1 : term2375 x) : term2550 x.
Proof. exact (conj (@lem1733390) (@lem1733359 x h1)). Qed.
Lemma lem1733393 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1733394 (x : real) : term2551 x.
Proof. exact (@lem1733393 term24 x). Qed.
Lemma lem1733395 (x : real) (h1 : term2375 x) : term809 x.
Proof. exact (@lem1733394 x (@lem1733391 x h1)). Qed.
Lemma lem1733396 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1733397 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733398 (x : real) : (term808 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1733397) (@lem1733396 x)). Qed.
Lemma lem1733399 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733400 (x : real) : (term809 x) = (term196 x).
Proof. exact (MK_COMB (@lem1733398 x) (@lem1733399)). Qed.
Lemma lem1733401 (x : real) (h1 : term2375 x) : term196 x.
Proof. exact (EQ_MP (@lem1733400 x) (@lem1733395 x h1)). Qed.
Lemma lem1733402 (x : real) (h1 : term2375 x) : term2552 x.
Proof. exact (conj (@lem1733401 x h1) (@lem1733380 x h1)). Qed.
Lemma lem1733404 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1733405 (x : real) : term2553 x.
Proof. exact (@lem1733404 x (term176 x)). Qed.
Lemma lem1733406 (x : real) (h1 : term2375 x) : term2554 x.
Proof. exact (@lem1733405 x (@lem1733402 x h1)). Qed.
Lemma lem1733407 (x : real) : (term2555 x) = (term2541 x).
Proof. exact (@lem1483442 term73 x). Qed.
Lemma lem1733409 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1733410 : term1261 = term76.
Proof. exact (@lem1733409 term185). Qed.
Lemma lem1733411 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1733412 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1733411) (@lem1733410)). Qed.
Lemma lem1733413 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1733414 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1733412) (@lem1733413 x)). Qed.
Lemma lem1733415 (x : real) : (term2555 x) = (term2544 x).
Proof. exact (TRANS (@lem1733407 x) (@lem1733414 x)). Qed.
Lemma lem1733416 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1733417 (x : real) : (term2555 x) = term76.
Proof. exact (TRANS (@lem1733415 x) (@lem1733416 x)). Qed.
Lemma lem1733418 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733419 (x : real) : (term2556 x) = term896.
Proof. exact (MK_COMB (@lem1733418) (@lem1733417 x)). Qed.
Lemma lem1733420 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733421 (x : real) : (term2554 x) = term897.
Proof. exact (MK_COMB (@lem1733419 x) (@lem1733420)). Qed.
Lemma lem1733422 (x : real) (h1 : term2375 x) : term897.
Proof. exact (EQ_MP (@lem1733421 x) (@lem1733406 x h1)). Qed.
Lemma lem1733424 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733425 : term897 = term2523.
Proof. exact (@lem1733424 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733426 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733427 : term897 = False.
Proof. exact (TRANS (@lem1733425) (@lem1733426)). Qed.
Lemma lem1733428 (x : real) (h1 : term2375 x) : False.
Proof. exact (EQ_MP (@lem1733427) (@lem1733422 x h1)). Qed.
Lemma lem1733429 (x : real) (h1 : term2382 x) : term2382 x.
Proof. exact (h1). Qed.
Lemma lem1733430 (x : real) (h1 : term2382 x) : term2369 x.
Proof. exact (proj2 (@lem1733429 x h1)). Qed.
Lemma lem1733432 (x : real) (h1 : term2382 x) : term2381 x.
Proof. exact (proj2 (@lem1733430 x h1)). Qed.
Lemma lem1733434 (x : real) (h1 : term2382 x) : term2361 x.
Proof. exact (proj2 (@lem1733432 x h1)). Qed.
Lemma lem1733436 (x : real) (h1 : term2382 x) : term1964 x.
Proof. exact (proj2 (@lem1733434 x h1)). Qed.
Lemma lem1733438 (x : real) (h1 : term2382 x) : term1963 x.
Proof. exact (proj2 (@lem1733436 x h1)). Qed.
Lemma lem1733442 (x : real) (h1 : term2382 x) : term915.
Proof. exact (proj2 (@lem1733438 x h1)). Qed.
Lemma lem1733445 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733446 : term915 = False.
Proof. exact (@lem1733445 term185 (NUMERAL 0)). Qed.
Lemma lem1733447 (x : real) (h1 : term2382 x) : False.
Proof. exact (EQ_MP (@lem1733446) (@lem1733442 x h1)). Qed.
Lemma lem1733448 (x : real) (h1 : term2383 x) : False.
Proof. exact (or_elim (@lem1733344 x h1) (fun h0 : term2375 x => @lem1733428 x h0) (fun h0 : term2382 x => @lem1733447 x h0)). Qed.
Lemma lem1733449 (x : real) (h1 : term2364 x) : term2364 x.
Proof. exact (h1). Qed.
Lemma lem1733450 (x : real) (h1 : term2354 x) : term2354 x.
Proof. exact (h1). Qed.
Lemma lem1733451 (x : real) (h1 : term2354 x) : term2352 x.
Proof. exact (proj2 (@lem1733450 x h1)). Qed.
Lemma lem1733453 (x : real) (h1 : term2354 x) : term2360 x.
Proof. exact (proj2 (@lem1733451 x h1)). Qed.
Lemma lem1733454 (x : real) (h1 : term2354 x) : term179 x.
Proof. exact (proj1 (@lem1733451 x h1)). Qed.
Lemma lem1733455 (x : real) (h1 : term2354 x) : term2359 x.
Proof. exact (proj2 (@lem1733453 x h1)). Qed.
Lemma lem1733457 (x : real) (h1 : term2354 x) : term1958 x.
Proof. exact (proj2 (@lem1733455 x h1)). Qed.
Lemma lem1733460 (x : real) (h1 : term2354 x) : term1224 x.
Proof. exact (proj1 (@lem1733457 x h1)). Qed.
Lemma lem1733461 (x : real) (h1 : term2354 x) : term326 x.
Proof. exact (proj2 (@lem1733460 x h1)). Qed.
Lemma lem1733466 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733467 : term1117 = term2525.
Proof. exact (@lem1733466 (NUMERAL 0) term185). Qed.
Lemma lem1733468 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733469 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733470 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733469 h1) (fun h1 : term2525 = True => @lem1733468)). Qed.
Lemma lem1733471 : term2525 = True.
Proof. exact (EQ_MP (@lem1733470) (@lem1733468)). Qed.
Lemma lem1733472 : term1117 = True.
Proof. exact (TRANS (@lem1733467) (@lem1733471)). Qed.
Lemma lem1733473 : True = term1117.
Proof. exact (SYM (@lem1733472)). Qed.
Lemma lem1733474 : term1117.
Proof. exact (EQ_MP (@lem1733473) (@lem0)). Qed.
Lemma lem1733475 (x : real) (h1 : term2354 x) : term2527 x.
Proof. exact (conj (@lem1733474) (@lem1733461 x h1)). Qed.
Lemma lem1733477 (x : real) (y : real) : term2528 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1733478 (x : real) : term2529 x.
Proof. exact (@lem1733477 term24 x). Qed.
Lemma lem1733479 (x : real) (h1 : term2354 x) : term1223 x.
Proof. exact (@lem1733478 x (@lem1733475 x h1)). Qed.
Lemma lem1733480 (x : real) : (term807 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1733481 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1733482 (x : real) : (term1222 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1733481) (@lem1733480 x)). Qed.
Lemma lem1733483 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733484 (x : real) : (term1223 x) = (term326 x).
Proof. exact (MK_COMB (@lem1733482 x) (@lem1733483)). Qed.
Lemma lem1733485 (x : real) (h1 : term2354 x) : term326 x.
Proof. exact (EQ_MP (@lem1733484 x) (@lem1733479 x h1)). Qed.
Lemma lem1733487 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733488 : term1117 = term2525.
Proof. exact (@lem1733487 (NUMERAL 0) term185). Qed.
Lemma lem1733489 : term2526 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1733490 (h1 : term2526 = (BIT1 0)) : term2525 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1733491 : (term2526 = (BIT1 0)) = (term2525 = True).
Proof. exact (prop_ext (fun h1 : term2526 = (BIT1 0) => @lem1733490 h1) (fun h1 : term2525 = True => @lem1733489)). Qed.
Lemma lem1733492 : term2525 = True.
Proof. exact (EQ_MP (@lem1733491) (@lem1733489)). Qed.
Lemma lem1733493 : term1117 = True.
Proof. exact (TRANS (@lem1733488) (@lem1733492)). Qed.
Lemma lem1733494 : True = term1117.
Proof. exact (SYM (@lem1733493)). Qed.
Lemma lem1733495 : term1117.
Proof. exact (EQ_MP (@lem1733494) (@lem0)). Qed.
Lemma lem1733496 (x : real) (h1 : term2354 x) : term2530 x.
Proof. exact (conj (@lem1733495) (@lem1733454 x h1)). Qed.
Lemma lem1733498 (x : real) (y : real) : term2531 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1733499 (x : real) : term2532 x.
Proof. exact (@lem1733498 term24 (term176 x)). Qed.
Lemma lem1733500 (x : real) (h1 : term2354 x) : term2533 x.
Proof. exact (@lem1733499 x (@lem1733496 x h1)). Qed.
Lemma lem1733501 (x : real) : (term2534 x) = (term176 x).
Proof. exact (@lem1483460 (term176 x)). Qed.
Lemma lem1733502 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733503 (x : real) : (term2535 x) = (term178 x).
Proof. exact (MK_COMB (@lem1733502) (@lem1733501 x)). Qed.
Lemma lem1733504 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733505 (x : real) : (term2533 x) = (term179 x).
Proof. exact (MK_COMB (@lem1733503 x) (@lem1733504)). Qed.
Lemma lem1733506 (x : real) (h1 : term2354 x) : term179 x.
Proof. exact (EQ_MP (@lem1733505 x) (@lem1733500 x h1)). Qed.
Lemma lem1733507 (x : real) (h1 : term2354 x) : term2536 x.
Proof. exact (conj (@lem1733506 x h1) (@lem1733485 x h1)). Qed.
Lemma lem1733509 (x : real) (y : real) : term2537 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1733510 (x : real) : term2538 x.
Proof. exact (@lem1733509 (term176 x) x). Qed.
Lemma lem1733511 (x : real) (h1 : term2354 x) : term2539 x.
Proof. exact (@lem1733510 x (@lem1733507 x h1)). Qed.
Lemma lem1733512 (x : real) : (term2540 x) = (term2541 x).
Proof. exact (@lem1483440 term73 x). Qed.
Lemma lem1733514 (m : nat) : (term1262 m) = term76.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1733515 : term1261 = term76.
Proof. exact (@lem1733514 term185). Qed.
Lemma lem1733516 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1733517 : term2542 = term2543.
Proof. exact (MK_COMB (@lem1733516) (@lem1733515)). Qed.
Lemma lem1733518 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1733519 (x : real) : (term2541 x) = (term2544 x).
Proof. exact (MK_COMB (@lem1733517) (@lem1733518 x)). Qed.
Lemma lem1733520 (x : real) : (term2540 x) = (term2544 x).
Proof. exact (TRANS (@lem1733512 x) (@lem1733519 x)). Qed.
Lemma lem1733521 (x : real) : (term2544 x) = term76.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1733522 (x : real) : (term2540 x) = term76.
Proof. exact (TRANS (@lem1733520 x) (@lem1733521 x)). Qed.
Lemma lem1733523 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1733524 (x : real) : (term2545 x) = term896.
Proof. exact (MK_COMB (@lem1733523) (@lem1733522 x)). Qed.
Lemma lem1733525 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1733526 (x : real) : (term2539 x) = term897.
Proof. exact (MK_COMB (@lem1733524 x) (@lem1733525)). Qed.
Lemma lem1733527 (x : real) (h1 : term2354 x) : term897.
Proof. exact (EQ_MP (@lem1733526 x) (@lem1733511 x h1)). Qed.
Lemma lem1733529 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733530 : term897 = term2523.
Proof. exact (@lem1733529 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733531 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733532 : term897 = False.
Proof. exact (TRANS (@lem1733530) (@lem1733531)). Qed.
Lemma lem1733533 (x : real) (h1 : term2354 x) : False.
Proof. exact (EQ_MP (@lem1733532) (@lem1733527 x h1)). Qed.
Lemma lem1733534 (x : real) (h1 : term2363 x) : term2363 x.
Proof. exact (h1). Qed.
Lemma lem1733535 (x : real) (h1 : term2363 x) : term2348 x.
Proof. exact (proj2 (@lem1733534 x h1)). Qed.
Lemma lem1733537 (x : real) (h1 : term2363 x) : term2362 x.
Proof. exact (proj2 (@lem1733535 x h1)). Qed.
Lemma lem1733539 (x : real) (h1 : term2363 x) : term2361 x.
Proof. exact (proj2 (@lem1733537 x h1)). Qed.
Lemma lem1733541 (x : real) (h1 : term2363 x) : term1964 x.
Proof. exact (proj2 (@lem1733539 x h1)). Qed.
Lemma lem1733543 (x : real) (h1 : term2363 x) : term1963 x.
Proof. exact (proj2 (@lem1733541 x h1)). Qed.
Lemma lem1733547 (x : real) (h1 : term2363 x) : term915.
Proof. exact (proj2 (@lem1733543 x h1)). Qed.
Lemma lem1733550 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733551 : term915 = False.
Proof. exact (@lem1733550 term185 (NUMERAL 0)). Qed.
Lemma lem1733552 (x : real) (h1 : term2363 x) : False.
Proof. exact (EQ_MP (@lem1733551) (@lem1733547 x h1)). Qed.
Lemma lem1733553 (x : real) (h1 : term2364 x) : False.
Proof. exact (or_elim (@lem1733449 x h1) (fun h0 : term2354 x => @lem1733533 x h0) (fun h0 : term2363 x => @lem1733552 x h0)). Qed.
Lemma lem1733554 (x : real) (h1 : term2385 x) : False.
Proof. exact (or_elim (@lem1733343 x h1) (fun h0 : term2383 x => @lem1733448 x h0) (fun h0 : term2364 x => @lem1733553 x h0)). Qed.
Lemma lem1733555 (x : real) (h1 : term2406 x) : term2406 x.
Proof. exact (h1). Qed.
Lemma lem1733556 (x : real) (h1 : term2399 x) : term2399 x.
Proof. exact (h1). Qed.
Lemma lem1733557 (x : real) (h1 : term2399 x) : term2397 x.
Proof. exact (proj2 (@lem1733556 x h1)). Qed.
Lemma lem1733559 (x : real) (h1 : term2399 x) : term2386 x.
Proof. exact (proj2 (@lem1733557 x h1)). Qed.
Lemma lem1733561 (x : real) (h1 : term2399 x) : term1998 x.
Proof. exact (proj2 (@lem1733559 x h1)). Qed.
Lemma lem1733563 (x : real) (h1 : term2399 x) : term1997 x.
Proof. exact (proj2 (@lem1733561 x h1)). Qed.
Lemma lem1733567 (x : real) (h1 : term2399 x) : term1996.
Proof. exact (proj2 (@lem1733563 x h1)). Qed.
Lemma lem1733570 (x : real) (h1 : term2399 x) : term915.
Proof. exact (proj1 (@lem1733567 x h1)). Qed.
Lemma lem1733572 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733573 : term915 = False.
Proof. exact (@lem1733572 term185 (NUMERAL 0)). Qed.
Lemma lem1733574 (x : real) (h1 : term2399 x) : False.
Proof. exact (EQ_MP (@lem1733573) (@lem1733570 x h1)). Qed.
Lemma lem1733575 (x : real) (h1 : term2405 x) : term2405 x.
Proof. exact (h1). Qed.
Lemma lem1733576 (x : real) (h1 : term2405 x) : term2404 x.
Proof. exact (proj2 (@lem1733575 x h1)). Qed.
Lemma lem1733578 (x : real) (h1 : term2405 x) : term2386 x.
Proof. exact (proj2 (@lem1733576 x h1)). Qed.
Lemma lem1733580 (x : real) (h1 : term2405 x) : term1998 x.
Proof. exact (proj2 (@lem1733578 x h1)). Qed.
Lemma lem1733582 (x : real) (h1 : term2405 x) : term1997 x.
Proof. exact (proj2 (@lem1733580 x h1)). Qed.
Lemma lem1733586 (x : real) (h1 : term2405 x) : term1996.
Proof. exact (proj2 (@lem1733582 x h1)). Qed.
Lemma lem1733589 (x : real) (h1 : term2405 x) : term915.
Proof. exact (proj1 (@lem1733586 x h1)). Qed.
Lemma lem1733591 (m : nat) (n : nat) : (term2524 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1733592 : term915 = False.
Proof. exact (@lem1733591 term185 (NUMERAL 0)). Qed.
Lemma lem1733593 (x : real) (h1 : term2405 x) : False.
Proof. exact (EQ_MP (@lem1733592) (@lem1733589 x h1)). Qed.
Lemma lem1733594 (x : real) (h1 : term2406 x) : False.
Proof. exact (or_elim (@lem1733555 x h1) (fun h0 : term2399 x => @lem1733574 x h0) (fun h0 : term2405 x => @lem1733593 x h0)). Qed.
Lemma lem1733595 (x : real) (h1 : term2409 x) : False.
Proof. exact (or_elim (@lem1733342 x h1) (fun h0 : term2385 x => @lem1733554 x h0) (fun h0 : term2406 x => @lem1733594 x h0)). Qed.
Lemma lem1733596 (x : real) (h1 : term2513 x) : term2513 x.
Proof. exact (h1). Qed.
Lemma lem1733597 (x : real) (h1 : term2480 x) : term2480 x.
Proof. exact (h1). Qed.
Lemma lem1733598 (x : real) (h1 : term2478 x) : term2478 x.
Proof. exact (h1). Qed.
Lemma lem1733599 (x : real) (h1 : term2470 x) : term2470 x.
Proof. exact (h1). Qed.
Lemma lem1733600 (x : real) (h1 : term2470 x) : term2468 x.
Proof. exact (proj2 (@lem1733599 x h1)). Qed.
Lemma lem1733602 (x : real) (h1 : term2470 x) : term2475 x.
Proof. exact (proj2 (@lem1733600 x h1)). Qed.
Lemma lem1733604 (x : real) (h1 : term2470 x) : term2447 x.
Proof. exact (proj2 (@lem1733602 x h1)). Qed.
Lemma lem1733606 (x : real) (h1 : term2470 x) : term1314 x.
Proof. exact (proj2 (@lem1733604 x h1)). Qed.
Lemma lem1733608 (x : real) (h1 : term2470 x) : term1127 x.
Proof. exact (proj2 (@lem1733606 x h1)). Qed.
Lemma lem1733612 (x : real) (h1 : term2470 x) : term897.
Proof. exact (proj2 (@lem1733608 x h1)). Qed.
Lemma lem1733615 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733616 : term897 = term2523.
Proof. exact (@lem1733615 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733617 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733618 : term897 = False.
Proof. exact (TRANS (@lem1733616) (@lem1733617)). Qed.
Lemma lem1733619 (x : real) (h1 : term2470 x) : False.
Proof. exact (EQ_MP (@lem1733618) (@lem1733612 x h1)). Qed.
Lemma lem1733620 (x : real) (h1 : term2477 x) : term2477 x.
Proof. exact (h1). Qed.
Lemma lem1733621 (x : real) (h1 : term2477 x) : term2468 x.
Proof. exact (proj2 (@lem1733620 x h1)). Qed.
Lemma lem1733623 (x : real) (h1 : term2477 x) : term2475 x.
Proof. exact (proj2 (@lem1733621 x h1)). Qed.
Lemma lem1733625 (x : real) (h1 : term2477 x) : term2447 x.
Proof. exact (proj2 (@lem1733623 x h1)). Qed.
Lemma lem1733627 (x : real) (h1 : term2477 x) : term1314 x.
Proof. exact (proj2 (@lem1733625 x h1)). Qed.
Lemma lem1733629 (x : real) (h1 : term2477 x) : term1127 x.
Proof. exact (proj2 (@lem1733627 x h1)). Qed.
Lemma lem1733633 (x : real) (h1 : term2477 x) : term897.
Proof. exact (proj2 (@lem1733629 x h1)). Qed.
Lemma lem1733636 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733637 : term897 = term2523.
Proof. exact (@lem1733636 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733638 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733639 : term897 = False.
Proof. exact (TRANS (@lem1733637) (@lem1733638)). Qed.
Lemma lem1733640 (x : real) (h1 : term2477 x) : False.
Proof. exact (EQ_MP (@lem1733639) (@lem1733633 x h1)). Qed.
Lemma lem1733641 (x : real) (h1 : term2478 x) : False.
Proof. exact (or_elim (@lem1733598 x h1) (fun h0 : term2470 x => @lem1733619 x h0) (fun h0 : term2477 x => @lem1733640 x h0)). Qed.
Lemma lem1733642 (x : real) (h1 : term2459 x) : term2459 x.
Proof. exact (h1). Qed.
Lemma lem1733643 (x : real) (h1 : term2442 x) : term2442 x.
Proof. exact (h1). Qed.
Lemma lem1733644 (x : real) (h1 : term2442 x) : term2440 x.
Proof. exact (proj2 (@lem1733643 x h1)). Qed.
Lemma lem1733646 (x : real) (h1 : term2442 x) : term2448 x.
Proof. exact (proj2 (@lem1733644 x h1)). Qed.
Lemma lem1733648 (x : real) (h1 : term2442 x) : term2447 x.
Proof. exact (proj2 (@lem1733646 x h1)). Qed.
Lemma lem1733650 (x : real) (h1 : term2442 x) : term1314 x.
Proof. exact (proj2 (@lem1733648 x h1)). Qed.
Lemma lem1733652 (x : real) (h1 : term2442 x) : term1127 x.
Proof. exact (proj2 (@lem1733650 x h1)). Qed.
Lemma lem1733656 (x : real) (h1 : term2442 x) : term897.
Proof. exact (proj2 (@lem1733652 x h1)). Qed.
Lemma lem1733659 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733660 : term897 = term2523.
Proof. exact (@lem1733659 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733661 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733662 : term897 = False.
Proof. exact (TRANS (@lem1733660) (@lem1733661)). Qed.
Lemma lem1733663 (x : real) (h1 : term2442 x) : False.
Proof. exact (EQ_MP (@lem1733662) (@lem1733656 x h1)). Qed.
Lemma lem1733664 (x : real) (h1 : term2458 x) : term2458 x.
Proof. exact (h1). Qed.
Lemma lem1733665 (x : real) (h1 : term2458 x) : term2440 x.
Proof. exact (proj2 (@lem1733664 x h1)). Qed.
Lemma lem1733667 (x : real) (h1 : term2458 x) : term2448 x.
Proof. exact (proj2 (@lem1733665 x h1)). Qed.
Lemma lem1733669 (x : real) (h1 : term2458 x) : term2447 x.
Proof. exact (proj2 (@lem1733667 x h1)). Qed.
Lemma lem1733671 (x : real) (h1 : term2458 x) : term1314 x.
Proof. exact (proj2 (@lem1733669 x h1)). Qed.
Lemma lem1733673 (x : real) (h1 : term2458 x) : term1127 x.
Proof. exact (proj2 (@lem1733671 x h1)). Qed.
Lemma lem1733677 (x : real) (h1 : term2458 x) : term897.
Proof. exact (proj2 (@lem1733673 x h1)). Qed.
Lemma lem1733680 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733681 : term897 = term2523.
Proof. exact (@lem1733680 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733682 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733683 : term897 = False.
Proof. exact (TRANS (@lem1733681) (@lem1733682)). Qed.
Lemma lem1733684 (x : real) (h1 : term2458 x) : False.
Proof. exact (EQ_MP (@lem1733683) (@lem1733677 x h1)). Qed.
Lemma lem1733685 (x : real) (h1 : term2459 x) : False.
Proof. exact (or_elim (@lem1733642 x h1) (fun h0 : term2442 x => @lem1733663 x h0) (fun h0 : term2458 x => @lem1733684 x h0)). Qed.
Lemma lem1733686 (x : real) (h1 : term2480 x) : False.
Proof. exact (or_elim (@lem1733597 x h1) (fun h0 : term2478 x => @lem1733641 x h0) (fun h0 : term2459 x => @lem1733685 x h0)). Qed.
Lemma lem1733687 (x : real) (h1 : term2510 x) : term2510 x.
Proof. exact (h1). Qed.
Lemma lem1733688 (x : real) (h1 : term2503 x) : term2503 x.
Proof. exact (h1). Qed.
Lemma lem1733689 (x : real) (h1 : term2503 x) : term2501 x.
Proof. exact (proj2 (@lem1733688 x h1)). Qed.
Lemma lem1733691 (x : real) (h1 : term2503 x) : term2490 x.
Proof. exact (proj2 (@lem1733689 x h1)). Qed.
Lemma lem1733693 (x : real) (h1 : term2503 x) : term2489 x.
Proof. exact (proj2 (@lem1733691 x h1)). Qed.
Lemma lem1733695 (x : real) (h1 : term2503 x) : term2488 x.
Proof. exact (proj2 (@lem1733693 x h1)). Qed.
Lemma lem1733699 (x : real) (h1 : term2503 x) : term2487.
Proof. exact (proj2 (@lem1733695 x h1)). Qed.
Lemma lem1733701 (x : real) (h1 : term2503 x) : term897.
Proof. exact (proj2 (@lem1733699 x h1)). Qed.
Lemma lem1733704 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733705 : term897 = term2523.
Proof. exact (@lem1733704 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733706 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733707 : term897 = False.
Proof. exact (TRANS (@lem1733705) (@lem1733706)). Qed.
Lemma lem1733708 (x : real) (h1 : term2503 x) : False.
Proof. exact (EQ_MP (@lem1733707) (@lem1733701 x h1)). Qed.
Lemma lem1733709 (x : real) (h1 : term2509 x) : term2509 x.
Proof. exact (h1). Qed.
Lemma lem1733710 (x : real) (h1 : term2509 x) : term2508 x.
Proof. exact (proj2 (@lem1733709 x h1)). Qed.
Lemma lem1733712 (x : real) (h1 : term2509 x) : term2490 x.
Proof. exact (proj2 (@lem1733710 x h1)). Qed.
Lemma lem1733714 (x : real) (h1 : term2509 x) : term2489 x.
Proof. exact (proj2 (@lem1733712 x h1)). Qed.
Lemma lem1733716 (x : real) (h1 : term2509 x) : term2488 x.
Proof. exact (proj2 (@lem1733714 x h1)). Qed.
Lemma lem1733720 (x : real) (h1 : term2509 x) : term2487.
Proof. exact (proj2 (@lem1733716 x h1)). Qed.
Lemma lem1733722 (x : real) (h1 : term2509 x) : term897.
Proof. exact (proj2 (@lem1733720 x h1)). Qed.
Lemma lem1733725 (n : nat) (m : nat) : (term2522 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1733726 : term897 = term2523.
Proof. exact (@lem1733725 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1733727 : term2523 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1733728 : term897 = False.
Proof. exact (TRANS (@lem1733726) (@lem1733727)). Qed.
Lemma lem1733729 (x : real) (h1 : term2509 x) : False.
Proof. exact (EQ_MP (@lem1733728) (@lem1733722 x h1)). Qed.
Lemma lem1733730 (x : real) (h1 : term2510 x) : False.
Proof. exact (or_elim (@lem1733687 x h1) (fun h0 : term2503 x => @lem1733708 x h0) (fun h0 : term2509 x => @lem1733729 x h0)). Qed.
Lemma lem1733731 (x : real) (h1 : term2513 x) : False.
Proof. exact (or_elim (@lem1733596 x h1) (fun h0 : term2480 x => @lem1733686 x h0) (fun h0 : term2510 x => @lem1733730 x h0)). Qed.
Lemma lem1733732 (x : real) (h1 : term2515 x) : False.
Proof. exact (or_elim (@lem1733341 x h1) (fun h0 : term2409 x => @lem1733595 x h0) (fun h0 : term2513 x => @lem1733731 x h0)). Qed.
Lemma lem1733733 (x : real) (h1 : term2517 x) : False.
Proof. exact (or_elim (@lem1732976 x h1) (fun h0 : term2322 x => @lem1733340 x h0) (fun h0 : term2515 x => @lem1733732 x h0)). Qed.
Lemma lem1733734 (x : real) (h1 : term2519 x) : False.
Proof. exact (or_elim (@lem1732221 x h1) (fun h0 : term2136 x => @lem1732975 x h0) (fun h0 : term2517 x => @lem1733733 x h0)). Qed.
Lemma lem1733735 (x : real) (h1 : term2521 x) : False.
Proof. exact (or_elim (@lem1731040 x h1) (fun h0 : term1725 x => @lem1732220 x h0) (fun h0 : term2519 x => @lem1733734 x h0)). Qed.
Lemma lem1733736 (x : real) (h1 : term801 x) : term801 x.
Proof. exact (h1). Qed.
Lemma lem1733737 (x : real) (h1 : term801 x) : term2521 x.
Proof. exact (EQ_MP (@lem1731039 x) (@lem1733736 x h1)). Qed.
Lemma lem1733738 (x : real) (h1 : term801 x) : (term2521 x) = False.
Proof. exact (prop_ext (fun h2 : term2521 x => @lem1733735 x h2) (fun h2 : False => @lem1733737 x h1)). Qed.
Lemma lem1733739 (x : real) (h1 : term801 x) : False.
Proof. exact (EQ_MP (@lem1733738 x h1) (@lem1733737 x h1)). Qed.
Lemma lem1733740 (h1 : term803) : term803.
Proof. exact (h1). Qed.
Lemma lem1733741 (h1 : term803) : False.
Proof. exact (ex_elim (@lem1733740 h1) (fun x : real => fun h0 : term802 x => @lem1733739 x h0)). Qed.
Lemma lem1733742 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1733743 (h1 : term14) : term803.
Proof. exact (EQ_MP (@lem1724569) (@lem1733742 h1)). Qed.
Lemma lem1733744 (h1 : term14) : term803 = False.
Proof. exact (prop_ext (fun h2 : term803 => @lem1733741 h2) (fun h2 : False => @lem1733743 h1)). Qed.
Lemma lem1733745 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1733744 h1) (@lem1733743 h1)). Qed.
Lemma lem1733746 : term2557.
Proof. exact (fun h0 : term14 => @lem1733745 h0). Qed.
Lemma lem1733747 : term2558.
Proof. exact (@lem1386578 term11). Qed.
Lemma lem1733748 : term11.
Proof. exact (@lem1733747 (@lem1733746)). Qed.
Lemma lem1733749 : term10.
Proof. exact (EQ_MP (@lem1720969) (@lem1733748)). Qed.
