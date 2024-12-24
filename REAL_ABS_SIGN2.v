Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_SIGN2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1482704_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483484_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1541882 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17362 (term2 x y) (term3 x)). Qed.
Lemma lem1541883 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1541884 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1541883 (term8 x)). Qed.
Lemma lem1541885 (y : real) (x : real) : (term9 x y) = (term10 y x).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1541886 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1541887 (y : real) (x : real) : (term11 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1541886) (@lem1541885 y x)). Qed.
Lemma lem1541888 (y : real) (x : real) : (term11 x y) = (term1 y x).
Proof. exact (TRANS (@lem1541887 y x) (@lem1541882 y x)). Qed.
Lemma lem1541889 (x : real) : (term12 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1541888 y x)). Qed.
Lemma lem1541890 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541891 (x : real) : (term7 x) = (term14 x).
Proof. exact (MK_COMB (@lem1541890) (@lem1541889 x)). Qed.
Lemma lem1541892 (x : real) : (term6 x) = (term14 x).
Proof. exact (TRANS (@lem1541884 x) (@lem1541891 x)). Qed.
Lemma lem1541893 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1541894 : term15 = term16.
Proof. exact (@lem1541893 term17). Qed.
Lemma lem1541895 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1541896 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1541897 (x : real) : (term20 x) = (term6 x).
Proof. exact (MK_COMB (@lem1541896) (@lem1541895 x)). Qed.
Lemma lem1541898 (x : real) : (term20 x) = (term14 x).
Proof. exact (TRANS (@lem1541897 x) (@lem1541892 x)). Qed.
Lemma lem1541899 : term21 = term22.
Proof. exact (fun_ext (fun x : real => @lem1541898 x)). Qed.
Lemma lem1541900 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541901 : term16 = term23.
Proof. exact (MK_COMB (@lem1541900) (@lem1541899)). Qed.
Lemma lem1541903 : term15 = term23.
Proof. exact (TRANS (@lem1541894) (@lem1541901)). Qed.
Lemma lem1541910 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1541911 (x : real) : (term13 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1541910 y x)). Qed.
Lemma lem1541912 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541913 (x : real) : (term14 x) = (term14 x).
Proof. exact (MK_COMB (@lem1541912) (@lem1541911 x)). Qed.
Lemma lem1541914 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1541913 x)). Qed.
Lemma lem1541915 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541916 : term23 = term23.
Proof. exact (MK_COMB (@lem1541915) (@lem1541914)). Qed.
Lemma lem1541917 : term15 = term23.
Proof. exact (TRANS (@lem1541903) (@lem1541916)). Qed.
Lemma lem1541918 (x : real) (y : real) : (term2 x y) = (term24 x y).
Proof. exact (@lem1483521 (real_neg y) (term25 x y)). Qed.
Lemma lem1541919 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1541926 (y : real) : (real_neg y) = (term26 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1541927 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1541928 (y : real) : (term27 y) = (term28 y).
Proof. exact (MK_COMB (@lem1541927) (@lem1541926 y)). Qed.
Lemma lem1541929 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1541928 y) (@lem1541919 x y)). Qed.
Lemma lem1541936 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483519 (term26 y) (term25 x y)). Qed.
Lemma lem1541937 (x : real) (y : real) : (term29 x y) = (term31 x y).
Proof. exact (TRANS (@lem1541929 x y) (@lem1541936 x y)). Qed.
Lemma lem1541938 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541939 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1541938) (@lem1541937 x y)). Qed.
Lemma lem1541940 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1541941 (x : real) (y : real) : (term24 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1541939 x y) (@lem1541940)). Qed.
Lemma lem1541942 (x : real) (y : real) : (term2 x y) = (term35 x y).
Proof. exact (TRANS (@lem1541918 x y) (@lem1541941 x y)). Qed.
Lemma lem1541943 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483531 x term34). Qed.
Lemma lem1541949 (x : real) : (term38 x) = (term39 x).
Proof. exact (@lem1483519 x term34). Qed.
Lemma lem1541951 (x : nat) : (term40 x) = term34.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1541952 : term41 = term34.
Proof. exact (@lem1541951 term42). Qed.
Lemma lem1541953 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1541954 (x : real) : (term39 x) = (term43 x).
Proof. exact (MK_COMB (@lem1541953 x) (@lem1541952)). Qed.
Lemma lem1541955 (x : real) : (term43 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1541956 (x : real) : (term39 x) = x.
Proof. exact (TRANS (@lem1541954 x) (@lem1541955 x)). Qed.
Lemma lem1541958 (x : real) : (term38 x) = x.
Proof. exact (TRANS (@lem1541949 x) (@lem1541956 x)). Qed.
Lemma lem1541959 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1541960 (x : real) : (term44 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1541959) (@lem1541958 x)). Qed.
Lemma lem1541961 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1541962 (x : real) : (term37 x) = (term45 x).
Proof. exact (MK_COMB (@lem1541960 x) (@lem1541961)). Qed.
Lemma lem1541963 (x : real) : (term36 x) = (term45 x).
Proof. exact (TRANS (@lem1541943 x) (@lem1541962 x)). Qed.
Lemma lem1541964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541965 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1541964) (@lem1541942 x y)). Qed.
Lemma lem1541966 (y : real) (x : real) : (term1 y x) = (term48 y x).
Proof. exact (MK_COMB (@lem1541965 x y) (@lem1541963 x)). Qed.
Lemma lem1541967 (x : real) : (term13 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1541966 y x)). Qed.
Lemma lem1541968 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541969 (x : real) : (term14 x) = (term50 x).
Proof. exact (MK_COMB (@lem1541968) (@lem1541967 x)). Qed.
Lemma lem1541970 : term22 = term51.
Proof. exact (fun_ext (fun x : real => @lem1541969 x)). Qed.
Lemma lem1541971 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541972 : term23 = term52.
Proof. exact (MK_COMB (@lem1541971) (@lem1541970)). Qed.
Lemma lem1541973 : term15 = term52.
Proof. exact (TRANS (@lem1541917) (@lem1541972)). Qed.
Lemma lem1541999 {A : Type'} (P : A -> Prop) (Q : Prop) : (term53 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem1542000 (P : real -> Prop) (Q : Prop) : (term55 P Q) = (term56 P Q).
Proof. exact (@lem1541999 real P Q). Qed.
Lemma lem1542001 (x : real) : (term57 x) = (term58 x).
Proof. exact (@lem1542000 (term59 x) (term45 x)). Qed.
Lemma lem1542002 (x : real) (y : real) : (term60 x y) = (term35 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1542003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542004 (x : real) (y : real) : (term61 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1542003) (@lem1542002 x y)). Qed.
Lemma lem1542005 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1542006 (y : real) (x : real) : (term62 y x) = (term48 y x).
Proof. exact (MK_COMB (@lem1542004 x y) (@lem1542005 x)). Qed.
Lemma lem1542007 (x : real) : (term63 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1542006 y x)). Qed.
Lemma lem1542008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542009 (x : real) : (term57 x) = (term50 x).
Proof. exact (MK_COMB (@lem1542008) (@lem1542007 x)). Qed.
Lemma lem1542010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1542011 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1542010) (@lem1542009 x)). Qed.
Lemma lem1542012 (x : real) (y : real) : (term60 x y) = (term35 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1542013 (x : real) : (term66 x) = (term59 x).
Proof. exact (fun_ext (fun y : real => @lem1542012 x y)). Qed.
Lemma lem1542014 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542015 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1542014) (@lem1542013 x)). Qed.
Lemma lem1542016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542017 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1542016) (@lem1542015 x)). Qed.
Lemma lem1542018 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1542019 (x : real) : (term58 x) = (term71 x).
Proof. exact (MK_COMB (@lem1542017 x) (@lem1542018 x)). Qed.
Lemma lem1542020 (x : real) : ((term57 x) = (term58 x)) = ((term50 x) = (term71 x)).
Proof. exact (MK_COMB (@lem1542011 x) (@lem1542019 x)). Qed.
Lemma lem1542021 (x : real) : (term50 x) = (term71 x).
Proof. exact (EQ_MP (@lem1542020 x) (@lem1542001 x)). Qed.
Lemma lem1542026 : term51 = term72.
Proof. exact (fun_ext (fun x : real => @lem1542021 x)). Qed.
Lemma lem1542027 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542028 : term52 = term73.
Proof. exact (MK_COMB (@lem1542027) (@lem1542026)). Qed.
Lemma lem1542078 {A : Type'} (P : A -> Prop) (Q : Prop) : (term54 A P Q) = (term53 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1542079 (P : real -> Prop) (Q : Prop) : (term56 P Q) = (term55 P Q).
Proof. exact (@lem1542078 real P Q). Qed.
Lemma lem1542080 (x : real) : (term58 x) = (term57 x).
Proof. exact (@lem1542079 (term59 x) (term45 x)). Qed.
Lemma lem1542081 (x : real) (y : real) : (term60 x y) = (term35 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1542082 (x : real) : (term66 x) = (term59 x).
Proof. exact (fun_ext (fun y : real => @lem1542081 x y)). Qed.
Lemma lem1542083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542084 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1542083) (@lem1542082 x)). Qed.
Lemma lem1542085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542086 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1542085) (@lem1542084 x)). Qed.
Lemma lem1542087 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1542088 (x : real) : (term58 x) = (term71 x).
Proof. exact (MK_COMB (@lem1542086 x) (@lem1542087 x)). Qed.
Lemma lem1542089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1542090 (x : real) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1542089) (@lem1542088 x)). Qed.
Lemma lem1542091 (x : real) (y : real) : (term60 x y) = (term35 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1542092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542093 (x : real) (y : real) : (term61 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1542092) (@lem1542091 x y)). Qed.
Lemma lem1542094 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1542095 (y : real) (x : real) : (term62 y x) = (term48 y x).
Proof. exact (MK_COMB (@lem1542093 x y) (@lem1542094 x)). Qed.
Lemma lem1542096 (x : real) : (term63 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1542095 y x)). Qed.
Lemma lem1542097 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542098 (x : real) : (term57 x) = (term50 x).
Proof. exact (MK_COMB (@lem1542097) (@lem1542096 x)). Qed.
Lemma lem1542099 (x : real) : ((term58 x) = (term57 x)) = ((term71 x) = (term50 x)).
Proof. exact (MK_COMB (@lem1542090 x) (@lem1542098 x)). Qed.
Lemma lem1542100 (x : real) : (term71 x) = (term50 x).
Proof. exact (EQ_MP (@lem1542099 x) (@lem1542080 x)). Qed.
Lemma lem1542101 : term72 = term51.
Proof. exact (fun_ext (fun x : real => @lem1542100 x)). Qed.
Lemma lem1542102 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542103 : term73 = term52.
Proof. exact (MK_COMB (@lem1542102) (@lem1542101)). Qed.
Lemma lem1542104 : term52 = term52.
Proof. exact (TRANS (@lem1542028) (@lem1542103)). Qed.
Lemma lem1542107 : term15 = term52.
Proof. exact (TRANS (@lem1541973) (@lem1542104)). Qed.
Lemma lem1542114 (y : real) (x : real) : (term48 y x) = (term48 y x).
Proof. exact (eq_refl (term48 y x)). Qed.
Lemma lem1542115 (x : real) : (term49 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1542114 y x)). Qed.
Lemma lem1542116 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542117 (x : real) : (term50 x) = (term50 x).
Proof. exact (MK_COMB (@lem1542116) (@lem1542115 x)). Qed.
Lemma lem1542118 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1542117 x)). Qed.
Lemma lem1542119 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542120 : term52 = term52.
Proof. exact (MK_COMB (@lem1542119) (@lem1542118)). Qed.
Lemma lem1542121 : term15 = term52.
Proof. exact (TRANS (@lem1542107) (@lem1542120)). Qed.
Lemma lem1542123 (a : real) (x : real) (r : real) : (term76 a x r) = (term77 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1542124 (x : real) (y : real) : (term35 x y) = (term78 x y).
Proof. exact (@lem1542123 (term26 y) (real_sub x y) term34). Qed.
Lemma lem1542137 (x : real) (y : real) : (real_sub x y) = (term79 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1542140 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1542141 (x : real) (y : real) : (term81 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1542140) (@lem1542137 x y)). Qed.
Lemma lem1542142 (x : real) (y : real) : (term82 x y) = (term79 x y).
Proof. exact (@lem1483460 (term79 x y)). Qed.
Lemma lem1542143 (x : real) (y : real) : (term81 x y) = (term79 x y).
Proof. exact (TRANS (@lem1542141 x y) (@lem1542142 x y)). Qed.
Lemma lem1542152 (y : real) : (term83 y) = (term83 y).
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1542153 (x : real) (y : real) : (term84 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1542152 y) (@lem1542143 x y)). Qed.
Lemma lem1542154 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (@lem1483484 x (term26 y) (term26 y)). Qed.
Lemma lem1542155 (y : real) : (term87 y) = (term88 y).
Proof. exact (@lem1483438 term89 term89 y). Qed.
Lemma lem1542156 : term90 = term91.
Proof. exact (@lem1367763 term42 term42). Qed.
Lemma lem1542157 : term92 = term93.
Proof. exact (@lem706885). Qed.
Lemma lem1542158 : (term92 = term93) = (term94 = term95).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term93). Qed.
Lemma lem1542159 : term94 = term95.
Proof. exact (EQ_MP (@lem1542158) (@lem1542157)). Qed.
Lemma lem1542160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1542161 : term96 = term97.
Proof. exact (MK_COMB (@lem1542160) (@lem1542159)). Qed.
Lemma lem1542162 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1542163 : term91 = term98.
Proof. exact (MK_COMB (@lem1542162) (@lem1542161)). Qed.
Lemma lem1542164 : term90 = term98.
Proof. exact (TRANS (@lem1542156) (@lem1542163)). Qed.
Lemma lem1542165 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1542166 : term99 = term100.
Proof. exact (MK_COMB (@lem1542165) (@lem1542164)). Qed.
Lemma lem1542167 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1542168 (y : real) : (term88 y) = (term101 y).
Proof. exact (MK_COMB (@lem1542166) (@lem1542167 y)). Qed.
Lemma lem1542169 (y : real) : (term87 y) = (term101 y).
Proof. exact (TRANS (@lem1542155 y) (@lem1542168 y)). Qed.
Lemma lem1542170 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1542171 (x : real) (y : real) : (term86 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1542170 x) (@lem1542169 y)). Qed.
Lemma lem1542172 (x : real) (y : real) : (term85 x y) = (term102 x y).
Proof. exact (TRANS (@lem1542154 x y) (@lem1542171 x y)). Qed.
Lemma lem1542173 (x : real) (y : real) : (term84 x y) = (term102 x y).
Proof. exact (TRANS (@lem1542153 x y) (@lem1542172 x y)). Qed.
Lemma lem1542174 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542175 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1542174) (@lem1542173 x y)). Qed.
Lemma lem1542176 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1542177 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1542175 x y) (@lem1542176)). Qed.
Lemma lem1542190 (x : real) (y : real) : (real_sub x y) = (term79 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1542193 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem1542194 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1542193) (@lem1542190 x y)). Qed.
Lemma lem1542195 (x : real) (y : real) : (term109 x y) = (term110 x y).
Proof. exact (@lem1483508 x term89 (term26 y)). Qed.
Lemma lem1542196 (y : real) : (term111 y) = (term112 y).
Proof. exact (@lem1483476 term89 term89 y). Qed.
Lemma lem1542198 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1542199 : term115 = term116.
Proof. exact (@lem1542198 term42 term42). Qed.
Lemma lem1542200 : (term117 = (BIT1 0)) = (term118 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1542201 : term118 = term42.
Proof. exact (EQ_MP (@lem1542200) (@lem940073)). Qed.
Lemma lem1542202 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1542203 : term116 = term119.
Proof. exact (MK_COMB (@lem1542202) (@lem1542201)). Qed.
Lemma lem1542204 : term115 = term119.
Proof. exact (TRANS (@lem1542199) (@lem1542203)). Qed.
Lemma lem1542205 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1542206 : term120 = term80.
Proof. exact (MK_COMB (@lem1542205) (@lem1542204)). Qed.
Lemma lem1542207 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1542208 (y : real) : (term112 y) = (term121 y).
Proof. exact (MK_COMB (@lem1542206) (@lem1542207 y)). Qed.
Lemma lem1542209 (y : real) : (term111 y) = (term121 y).
Proof. exact (TRANS (@lem1542196 y) (@lem1542208 y)). Qed.
Lemma lem1542210 (y : real) : (term121 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1542211 (y : real) : (term111 y) = y.
Proof. exact (TRANS (@lem1542209 y) (@lem1542210 y)). Qed.
Lemma lem1542214 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1542215 (x : real) (y : real) : (term110 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1542214 x) (@lem1542211 y)). Qed.
Lemma lem1542216 (x : real) (y : real) : (term109 x y) = (term122 x y).
Proof. exact (TRANS (@lem1542195 x y) (@lem1542215 x y)). Qed.
Lemma lem1542217 (x : real) (y : real) : (term108 x y) = (term122 x y).
Proof. exact (TRANS (@lem1542194 x y) (@lem1542216 x y)). Qed.
Lemma lem1542226 (y : real) : (term83 y) = (term83 y).
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1542227 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1542226 y) (@lem1542217 x y)). Qed.
Lemma lem1542228 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (@lem1483484 (term26 x) (term26 y) y). Qed.
Lemma lem1542229 (y : real) : (term126 y) = (term127 y).
Proof. exact (@lem1483440 term89 y). Qed.
Lemma lem1542231 (m : nat) : (term128 m) = term34.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1542232 : term129 = term34.
Proof. exact (@lem1542231 term42). Qed.
Lemma lem1542233 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1542234 : term130 = term131.
Proof. exact (MK_COMB (@lem1542233) (@lem1542232)). Qed.
Lemma lem1542235 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1542236 (y : real) : (term127 y) = (term132 y).
Proof. exact (MK_COMB (@lem1542234) (@lem1542235 y)). Qed.
Lemma lem1542237 (y : real) : (term126 y) = (term132 y).
Proof. exact (TRANS (@lem1542229 y) (@lem1542236 y)). Qed.
Lemma lem1542238 (y : real) : (term132 y) = term34.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1542239 (y : real) : (term126 y) = term34.
Proof. exact (TRANS (@lem1542237 y) (@lem1542238 y)). Qed.
Lemma lem1542240 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1542241 (y : real) (x : real) : (term125 x y) = (term133 x).
Proof. exact (MK_COMB (@lem1542240 x) (@lem1542239 y)). Qed.
Lemma lem1542242 (y : real) (x : real) : (term124 x y) = (term133 x).
Proof. exact (TRANS (@lem1542228 x y) (@lem1542241 y x)). Qed.
Lemma lem1542243 (x : real) : (term133 x) = (term26 x).
Proof. exact (@lem1483450 (term26 x)). Qed.
Lemma lem1542244 (y : real) (x : real) : (term124 x y) = (term26 x).
Proof. exact (TRANS (@lem1542242 y x) (@lem1542243 x)). Qed.
Lemma lem1542245 (y : real) (x : real) : (term123 x y) = (term26 x).
Proof. exact (TRANS (@lem1542227 x y) (@lem1542244 y x)). Qed.
Lemma lem1542246 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542247 (y : real) (x : real) : (term134 x y) = (term135 x).
Proof. exact (MK_COMB (@lem1542246) (@lem1542245 y x)). Qed.
Lemma lem1542248 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1542249 (y : real) (x : real) : (term136 x y) = (term137 x).
Proof. exact (MK_COMB (@lem1542247 y x) (@lem1542248)). Qed.
Lemma lem1542250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542251 (y : real) (x : real) : (term138 x y) = (term139 x).
Proof. exact (MK_COMB (@lem1542250) (@lem1542249 y x)). Qed.
Lemma lem1542252 (x : real) (y : real) : (term78 x y) = (term140 x y).
Proof. exact (MK_COMB (@lem1542251 y x) (@lem1542177 x y)). Qed.
Lemma lem1542253 (x : real) (y : real) : (term35 x y) = (term140 x y).
Proof. exact (TRANS (@lem1542124 x y) (@lem1542252 x y)). Qed.
Lemma lem1542254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542255 (x : real) (y : real) : (term47 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem1542254) (@lem1542253 x y)). Qed.
Lemma lem1542256 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1542259 (y : real) (x : real) : (term48 y x) = (term142 y x).
Proof. exact (MK_COMB (@lem1542255 x y) (@lem1542256 x)). Qed.
Lemma lem1542260 (y : real) (x : real) (h1 : term142 y x) : term142 y x.
Proof. exact (h1). Qed.
Lemma lem1542261 (y : real) (x : real) (h1 : term142 y x) : term45 x.
Proof. exact (proj2 (@lem1542260 y x h1)). Qed.
Lemma lem1542262 (y : real) (x : real) (h1 : term142 y x) : term140 x y.
Proof. exact (proj1 (@lem1542260 y x h1)). Qed.
Lemma lem1542264 (y : real) (x : real) (h1 : term142 y x) : term137 x.
Proof. exact (proj1 (@lem1542262 y x h1)). Qed.
Lemma lem1542266 (n : nat) (m : nat) : (term143 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1542267 : term144 = term145.
Proof. exact (@lem1542266 (NUMERAL 0) term42). Qed.
Lemma lem1542268 : term146 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1542269 (h1 : term146 = (BIT1 0)) : term145 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1542270 : (term146 = (BIT1 0)) = (term145 = True).
Proof. exact (prop_ext (fun h1 : term146 = (BIT1 0) => @lem1542269 h1) (fun h1 : term145 = True => @lem1542268)). Qed.
Lemma lem1542271 : term145 = True.
Proof. exact (EQ_MP (@lem1542270) (@lem1542268)). Qed.
Lemma lem1542272 : term144 = True.
Proof. exact (TRANS (@lem1542267) (@lem1542271)). Qed.
Lemma lem1542273 : True = term144.
Proof. exact (SYM (@lem1542272)). Qed.
Lemma lem1542274 : term144.
Proof. exact (EQ_MP (@lem1542273) (@lem0)). Qed.
Lemma lem1542275 (y : real) (x : real) (h1 : term142 y x) : term147 x.
Proof. exact (conj (@lem1542274) (@lem1542261 y x h1)). Qed.
Lemma lem1542277 (x : real) (y : real) : term148 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1542278 (x : real) : term149 x.
Proof. exact (@lem1542277 term119 x). Qed.
Lemma lem1542279 (y : real) (x : real) (h1 : term142 y x) : term150 x.
Proof. exact (@lem1542278 x (@lem1542275 y x h1)). Qed.
Lemma lem1542280 (x : real) : (term121 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1542281 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1542282 (x : real) : (term151 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1542281) (@lem1542280 x)). Qed.
Lemma lem1542283 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1542284 (x : real) : (term150 x) = (term45 x).
Proof. exact (MK_COMB (@lem1542282 x) (@lem1542283)). Qed.
Lemma lem1542285 (y : real) (x : real) (h1 : term142 y x) : term45 x.
Proof. exact (EQ_MP (@lem1542284 x) (@lem1542279 y x h1)). Qed.
Lemma lem1542287 (n : nat) (m : nat) : (term143 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1542288 : term144 = term145.
Proof. exact (@lem1542287 (NUMERAL 0) term42). Qed.
Lemma lem1542289 : term146 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1542290 (h1 : term146 = (BIT1 0)) : term145 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1542291 : (term146 = (BIT1 0)) = (term145 = True).
Proof. exact (prop_ext (fun h1 : term146 = (BIT1 0) => @lem1542290 h1) (fun h1 : term145 = True => @lem1542289)). Qed.
Lemma lem1542292 : term145 = True.
Proof. exact (EQ_MP (@lem1542291) (@lem1542289)). Qed.
Lemma lem1542293 : term144 = True.
Proof. exact (TRANS (@lem1542288) (@lem1542292)). Qed.
Lemma lem1542294 : True = term144.
Proof. exact (SYM (@lem1542293)). Qed.
Lemma lem1542295 : term144.
Proof. exact (EQ_MP (@lem1542294) (@lem0)). Qed.
Lemma lem1542296 (y : real) (x : real) (h1 : term142 y x) : term152 x.
Proof. exact (conj (@lem1542295) (@lem1542264 y x h1)). Qed.
Lemma lem1542298 (x : real) (y : real) : term153 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1542299 (x : real) : term154 x.
Proof. exact (@lem1542298 term119 (term26 x)). Qed.
Lemma lem1542300 (y : real) (x : real) (h1 : term142 y x) : term155 x.
Proof. exact (@lem1542299 x (@lem1542296 y x h1)). Qed.
Lemma lem1542301 (x : real) : (term156 x) = (term26 x).
Proof. exact (@lem1483460 (term26 x)). Qed.
Lemma lem1542302 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542303 (x : real) : (term157 x) = (term135 x).
Proof. exact (MK_COMB (@lem1542302) (@lem1542301 x)). Qed.
Lemma lem1542304 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1542305 (x : real) : (term155 x) = (term137 x).
Proof. exact (MK_COMB (@lem1542303 x) (@lem1542304)). Qed.
Lemma lem1542306 (y : real) (x : real) (h1 : term142 y x) : term137 x.
Proof. exact (EQ_MP (@lem1542305 x) (@lem1542300 y x h1)). Qed.
Lemma lem1542307 (y : real) (x : real) (h1 : term142 y x) : term158 x.
Proof. exact (conj (@lem1542306 y x h1) (@lem1542285 y x h1)). Qed.
Lemma lem1542309 (x : real) (y : real) : term159 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1542310 (x : real) : term160 x.
Proof. exact (@lem1542309 (term26 x) x). Qed.
Lemma lem1542311 (y : real) (x : real) (h1 : term142 y x) : term161 x.
Proof. exact (@lem1542310 x (@lem1542307 y x h1)). Qed.
Lemma lem1542312 (x : real) : (term126 x) = (term127 x).
Proof. exact (@lem1483440 term89 x). Qed.
Lemma lem1542314 (m : nat) : (term128 m) = term34.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1542315 : term129 = term34.
Proof. exact (@lem1542314 term42). Qed.
Lemma lem1542316 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1542317 : term130 = term131.
Proof. exact (MK_COMB (@lem1542316) (@lem1542315)). Qed.
Lemma lem1542318 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1542319 (x : real) : (term127 x) = (term132 x).
Proof. exact (MK_COMB (@lem1542317) (@lem1542318 x)). Qed.
Lemma lem1542320 (x : real) : (term126 x) = (term132 x).
Proof. exact (TRANS (@lem1542312 x) (@lem1542319 x)). Qed.
Lemma lem1542321 (x : real) : (term132 x) = term34.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1542322 (x : real) : (term126 x) = term34.
Proof. exact (TRANS (@lem1542320 x) (@lem1542321 x)). Qed.
Lemma lem1542323 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542324 (x : real) : (term162 x) = term163.
Proof. exact (MK_COMB (@lem1542323) (@lem1542322 x)). Qed.
Lemma lem1542325 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1542326 (x : real) : (term161 x) = term164.
Proof. exact (MK_COMB (@lem1542324 x) (@lem1542325)). Qed.
Lemma lem1542327 (y : real) (x : real) (h1 : term142 y x) : term164.
Proof. exact (EQ_MP (@lem1542326 x) (@lem1542311 y x h1)). Qed.
Lemma lem1542329 (n : nat) (m : nat) : (term143 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1542330 : term164 = term165.
Proof. exact (@lem1542329 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1542331 : term165 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1542332 : term164 = False.
Proof. exact (TRANS (@lem1542330) (@lem1542331)). Qed.
Lemma lem1542333 (y : real) (x : real) (h1 : term142 y x) : False.
Proof. exact (EQ_MP (@lem1542332) (@lem1542327 y x h1)). Qed.
Lemma lem1542334 (y : real) (x : real) (h1 : term48 y x) : term48 y x.
Proof. exact (h1). Qed.
Lemma lem1542335 (y : real) (x : real) (h1 : term48 y x) : term142 y x.
Proof. exact (EQ_MP (@lem1542259 y x) (@lem1542334 y x h1)). Qed.
Lemma lem1542336 (y : real) (x : real) (h1 : term48 y x) : (term142 y x) = False.
Proof. exact (prop_ext (fun h2 : term142 y x => @lem1542333 y x h2) (fun h2 : False => @lem1542335 y x h1)). Qed.
Lemma lem1542337 (y : real) (x : real) (h1 : term48 y x) : False.
Proof. exact (EQ_MP (@lem1542336 y x h1) (@lem1542335 y x h1)). Qed.
Lemma lem1542338 (x : real) (h1 : term50 x) : term50 x.
Proof. exact (h1). Qed.
Lemma lem1542339 (x : real) (h1 : term50 x) : False.
Proof. exact (ex_elim (@lem1542338 x h1) (fun y : real => fun h0 : term49 x y => @lem1542337 y x h0)). Qed.
Lemma lem1542340 (h1 : term52) : term52.
Proof. exact (h1). Qed.
Lemma lem1542341 (h1 : term52) : False.
Proof. exact (ex_elim (@lem1542340 h1) (fun x : real => fun h0 : term51 x => @lem1542339 x h0)). Qed.
Lemma lem1542342 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1542343 (h1 : term15) : term52.
Proof. exact (EQ_MP (@lem1542121) (@lem1542342 h1)). Qed.
Lemma lem1542344 (h1 : term15) : term52 = False.
Proof. exact (prop_ext (fun h2 : term52 => @lem1542341 h2) (fun h2 : False => @lem1542343 h1)). Qed.
Lemma lem1542345 (h1 : term15) : False.
Proof. exact (EQ_MP (@lem1542344 h1) (@lem1542343 h1)). Qed.
Lemma lem1542346 : term166.
Proof. exact (fun h0 : term15 => @lem1542345 h0). Qed.
Lemma lem1542347 : term167.
Proof. exact (@lem1386578 term168). Qed.
Lemma lem1542348 : term168.
Proof. exact (@lem1542347 (@lem1542346)). Qed.
