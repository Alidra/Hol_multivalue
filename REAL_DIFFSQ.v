Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIFFSQ_term_abbrevs.
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
Require Import thm1483454_spec.
Require Import thm1483474_spec.
Require Import thm1483476_spec.
Require Import thm1483478_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483490_spec.
Require Import thm1483498_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1523990 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1523991 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1523990 (term4 x)). Qed.
Lemma lem1523992 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (term7 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1523993 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1523995 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1523993) (@lem1523992 x y)). Qed.
Lemma lem1523996 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1523995 x y)). Qed.
Lemma lem1523997 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523998 (x : real) : (term3 x) = (term12 x).
Proof. exact (MK_COMB (@lem1523997) (@lem1523996 x)). Qed.
Lemma lem1523999 (x : real) : (term2 x) = (term12 x).
Proof. exact (TRANS (@lem1523991 x) (@lem1523998 x)). Qed.
Lemma lem1524000 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1524001 : term13 = term14.
Proof. exact (@lem1524000 term15). Qed.
Lemma lem1524002 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1524003 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1524004 (x : real) : (term18 x) = (term2 x).
Proof. exact (MK_COMB (@lem1524003) (@lem1524002 x)). Qed.
Lemma lem1524005 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1524004 x) (@lem1523999 x)). Qed.
Lemma lem1524006 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1524005 x)). Qed.
Lemma lem1524007 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524008 : term14 = term21.
Proof. exact (MK_COMB (@lem1524007) (@lem1524006)). Qed.
Lemma lem1524010 : term13 = term21.
Proof. exact (TRANS (@lem1524001) (@lem1524008)). Qed.
Lemma lem1524013 (x : real) (y : real) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1524014 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1524013 x y)). Qed.
Lemma lem1524015 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524016 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1524015) (@lem1524014 x)). Qed.
Lemma lem1524017 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1524016 x)). Qed.
Lemma lem1524018 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524019 : term21 = term21.
Proof. exact (MK_COMB (@lem1524018) (@lem1524017)). Qed.
Lemma lem1524020 : term13 = term21.
Proof. exact (TRANS (@lem1524010) (@lem1524019)). Qed.
Lemma lem1524021 (x : real) (y : real) : (term9 x y) = (term22 x y).
Proof. exact (@lem1483554 (term6 x y) (term7 x y)). Qed.
Lemma lem1524028 (y : real) : (real_mul y y) = (term23 y).
Proof. exact (@lem1483498 y). Qed.
Lemma lem1524035 (x : real) : (real_mul x x) = (term23 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1524036 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1524037 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1524036) (@lem1524035 x)). Qed.
Lemma lem1524038 (x : real) (y : real) : (term7 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1524037 x) (@lem1524028 y)). Qed.
Lemma lem1524045 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 (term23 x) (term23 y)). Qed.
Lemma lem1524046 (x : real) (y : real) : (term7 x y) = (term27 x y).
Proof. exact (TRANS (@lem1524038 x y) (@lem1524045 x y)). Qed.
Lemma lem1524059 (x : real) (y : real) : (real_sub x y) = (term28 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1524068 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1524069 (x : real) (y : real) : (term6 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1524068 x y) (@lem1524059 x y)). Qed.
Lemma lem1524070 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483454 x y (term28 x y)). Qed.
Lemma lem1524071 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (@lem1483508 x x (term34 y)). Qed.
Lemma lem1524076 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem1483478 term37 x y). Qed.
Lemma lem1524077 (x : real) : (real_mul x x) = (term23 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1524078 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1524079 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1524078) (@lem1524077 x)). Qed.
Lemma lem1524080 (x : real) (y : real) : (term33 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1524079 x) (@lem1524076 x y)). Qed.
Lemma lem1524081 (x : real) (y : real) : (term32 x y) = (term40 x y).
Proof. exact (TRANS (@lem1524071 x y) (@lem1524080 x y)). Qed.
Lemma lem1524082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1524083 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1524082) (@lem1524081 x y)). Qed.
Lemma lem1524084 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1483508 x y (term34 y)). Qed.
Lemma lem1524085 (y : real) : (term45 y) = (term46 y).
Proof. exact (@lem1483478 term37 y y). Qed.
Lemma lem1524086 (y : real) : (real_mul y y) = (term23 y).
Proof. exact (@lem1483498 y). Qed.
Lemma lem1524087 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1524088 (y : real) : (term46 y) = (term48 y).
Proof. exact (MK_COMB (@lem1524087) (@lem1524086 y)). Qed.
Lemma lem1524089 (y : real) : (term45 y) = (term48 y).
Proof. exact (TRANS (@lem1524085 y) (@lem1524088 y)). Qed.
Lemma lem1524090 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1524091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1524092 (x : real) (y : real) : (term49 y x) = (term49 x y).
Proof. exact (MK_COMB (@lem1524091) (@lem1524090 x y)). Qed.
Lemma lem1524093 (x : real) (y : real) : (term44 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1524092 x y) (@lem1524089 y)). Qed.
Lemma lem1524094 (x : real) (y : real) : (term43 x y) = (term50 x y).
Proof. exact (TRANS (@lem1524084 x y) (@lem1524093 x y)). Qed.
Lemma lem1524095 (x : real) (y : real) : (term31 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1524083 x y) (@lem1524094 x y)). Qed.
Lemma lem1524096 (x : real) (y : real) : (term30 x y) = (term51 x y).
Proof. exact (TRANS (@lem1524070 x y) (@lem1524095 x y)). Qed.
Lemma lem1524097 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (@lem1483482 (term23 x) (term36 x y) (term50 x y)). Qed.
Lemma lem1524098 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem1483490 (term36 x y) (real_mul x y) (term48 y)). Qed.
Lemma lem1524099 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (@lem1483440 term37 (real_mul x y)). Qed.
Lemma lem1524101 (m : nat) : (term57 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1524102 : term59 = term58.
Proof. exact (@lem1524101 term60). Qed.
Lemma lem1524103 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524104 : term61 = term62.
Proof. exact (MK_COMB (@lem1524103) (@lem1524102)). Qed.
Lemma lem1524105 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1524106 (x : real) (y : real) : (term56 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1524104) (@lem1524105 x y)). Qed.
Lemma lem1524107 (x : real) (y : real) : (term55 x y) = (term63 x y).
Proof. exact (TRANS (@lem1524099 x y) (@lem1524106 x y)). Qed.
Lemma lem1524108 (x : real) (y : real) : (term63 x y) = term58.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1524109 (x : real) (y : real) : (term55 x y) = term58.
Proof. exact (TRANS (@lem1524107 x y) (@lem1524108 x y)). Qed.
Lemma lem1524110 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1524111 (x : real) (y : real) : (term64 x y) = term65.
Proof. exact (MK_COMB (@lem1524110) (@lem1524109 x y)). Qed.
Lemma lem1524112 (y : real) : (term48 y) = (term48 y).
Proof. exact (eq_refl (term48 y)). Qed.
Lemma lem1524113 (x : real) (y : real) : (term54 x y) = (term66 y).
Proof. exact (MK_COMB (@lem1524111 x y) (@lem1524112 y)). Qed.
Lemma lem1524114 (x : real) (y : real) : (term53 x y) = (term66 y).
Proof. exact (TRANS (@lem1524098 x y) (@lem1524113 x y)). Qed.
Lemma lem1524115 (y : real) : (term66 y) = (term48 y).
Proof. exact (@lem1483448 (term48 y)). Qed.
Lemma lem1524116 (x : real) (y : real) : (term53 x y) = (term48 y).
Proof. exact (TRANS (@lem1524114 x y) (@lem1524115 y)). Qed.
Lemma lem1524117 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1524118 (x : real) (y : real) : (term52 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1524117 x) (@lem1524116 x y)). Qed.
Lemma lem1524119 (x : real) (y : real) : (term51 x y) = (term27 x y).
Proof. exact (TRANS (@lem1524097 x y) (@lem1524118 x y)). Qed.
Lemma lem1524120 (x : real) (y : real) : (term30 x y) = (term27 x y).
Proof. exact (TRANS (@lem1524096 x y) (@lem1524119 x y)). Qed.
Lemma lem1524121 (x : real) (y : real) : (term6 x y) = (term27 x y).
Proof. exact (TRANS (@lem1524069 x y) (@lem1524120 x y)). Qed.
Lemma lem1524122 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1524123 (x : real) (y : real) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1524122) (@lem1524121 x y)). Qed.
Lemma lem1524124 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1524123 x y) (@lem1524046 x y)). Qed.
Lemma lem1524125 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem1483519 (term27 x y) (term27 x y)). Qed.
Lemma lem1524126 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (@lem1483508 (term23 x) term37 (term48 y)). Qed.
Lemma lem1524127 (y : real) : (term74 y) = (term75 y).
Proof. exact (@lem1483476 term37 term37 (term23 y)). Qed.
Lemma lem1524129 (m : nat) (n : nat) : (term76 m n) = (term77 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1524130 : term78 = term79.
Proof. exact (@lem1524129 term60 term60). Qed.
Lemma lem1524131 : (term80 = (BIT1 0)) = (term81 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1524132 : term81 = term60.
Proof. exact (EQ_MP (@lem1524131) (@lem940073)). Qed.
Lemma lem1524133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1524134 : term79 = term82.
Proof. exact (MK_COMB (@lem1524133) (@lem1524132)). Qed.
Lemma lem1524135 : term78 = term82.
Proof. exact (TRANS (@lem1524130) (@lem1524134)). Qed.
Lemma lem1524136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524137 : term83 = term84.
Proof. exact (MK_COMB (@lem1524136) (@lem1524135)). Qed.
Lemma lem1524138 (y : real) : (term23 y) = (term23 y).
Proof. exact (eq_refl (term23 y)). Qed.
Lemma lem1524139 (y : real) : (term75 y) = (term85 y).
Proof. exact (MK_COMB (@lem1524137) (@lem1524138 y)). Qed.
Lemma lem1524140 (y : real) : (term74 y) = (term85 y).
Proof. exact (TRANS (@lem1524127 y) (@lem1524139 y)). Qed.
Lemma lem1524141 (y : real) : (term85 y) = (term23 y).
Proof. exact (@lem1483436 (term23 y)). Qed.
Lemma lem1524142 (y : real) : (term74 y) = (term23 y).
Proof. exact (TRANS (@lem1524140 y) (@lem1524141 y)). Qed.
Lemma lem1524145 (x : real) : (term86 x) = (term86 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1524146 (x : real) (y : real) : (term73 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem1524145 x) (@lem1524142 y)). Qed.
Lemma lem1524147 (x : real) (y : real) : (term72 x y) = (term87 x y).
Proof. exact (TRANS (@lem1524126 x y) (@lem1524146 x y)). Qed.
Lemma lem1524148 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1524149 (x : real) (y : real) : (term71 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1524148 x y) (@lem1524147 x y)). Qed.
Lemma lem1524150 (x : real) (y : real) : (term89 x y) = (term90 x y).
Proof. exact (@lem1483480 (term23 x) (term48 x) (term48 y) (term23 y)). Qed.
Lemma lem1524151 (x : real) : (term91 x) = (term92 x).
Proof. exact (@lem1483442 term37 (term23 x)). Qed.
Lemma lem1524153 (m : nat) : (term57 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1524154 : term59 = term58.
Proof. exact (@lem1524153 term60). Qed.
Lemma lem1524155 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524156 : term61 = term62.
Proof. exact (MK_COMB (@lem1524155) (@lem1524154)). Qed.
Lemma lem1524157 (x : real) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1524158 (x : real) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem1524156) (@lem1524157 x)). Qed.
Lemma lem1524159 (x : real) : (term91 x) = (term93 x).
Proof. exact (TRANS (@lem1524151 x) (@lem1524158 x)). Qed.
Lemma lem1524160 (x : real) : (term93 x) = term58.
Proof. exact (@lem1483446 (term23 x)). Qed.
Lemma lem1524161 (x : real) : (term91 x) = term58.
Proof. exact (TRANS (@lem1524159 x) (@lem1524160 x)). Qed.
Lemma lem1524162 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1524163 (x : real) : (term94 x) = term65.
Proof. exact (MK_COMB (@lem1524162) (@lem1524161 x)). Qed.
Lemma lem1524164 (y : real) : (term95 y) = (term92 y).
Proof. exact (@lem1483440 term37 (term23 y)). Qed.
Lemma lem1524166 (m : nat) : (term57 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1524167 : term59 = term58.
Proof. exact (@lem1524166 term60). Qed.
Lemma lem1524168 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1524169 : term61 = term62.
Proof. exact (MK_COMB (@lem1524168) (@lem1524167)). Qed.
Lemma lem1524170 (y : real) : (term23 y) = (term23 y).
Proof. exact (eq_refl (term23 y)). Qed.
Lemma lem1524171 (y : real) : (term92 y) = (term93 y).
Proof. exact (MK_COMB (@lem1524169) (@lem1524170 y)). Qed.
Lemma lem1524172 (y : real) : (term95 y) = (term93 y).
Proof. exact (TRANS (@lem1524164 y) (@lem1524171 y)). Qed.
Lemma lem1524173 (y : real) : (term93 y) = term58.
Proof. exact (@lem1483446 (term23 y)). Qed.
Lemma lem1524174 (y : real) : (term95 y) = term58.
Proof. exact (TRANS (@lem1524172 y) (@lem1524173 y)). Qed.
Lemma lem1524175 (x : real) (y : real) : (term90 x y) = term96.
Proof. exact (MK_COMB (@lem1524163 x) (@lem1524174 y)). Qed.
Lemma lem1524176 (x : real) (y : real) : (term89 x y) = term96.
Proof. exact (TRANS (@lem1524150 x y) (@lem1524175 x y)). Qed.
Lemma lem1524177 : term96 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1524178 (x : real) (y : real) : (term89 x y) = term58.
Proof. exact (TRANS (@lem1524176 x y) (@lem1524177)). Qed.
Lemma lem1524179 (x : real) (y : real) : (term71 x y) = term58.
Proof. exact (TRANS (@lem1524149 x y) (@lem1524178 x y)). Qed.
Lemma lem1524180 (x : real) (y : real) : (term70 x y) = term58.
Proof. exact (TRANS (@lem1524125 x y) (@lem1524179 x y)). Qed.
Lemma lem1524181 (x : real) (y : real) : (term69 x y) = term58.
Proof. exact (TRANS (@lem1524124 x y) (@lem1524180 x y)). Qed.
Lemma lem1524182 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1524183 (x : real) (y : real) : (term97 x y) = term98.
Proof. exact (MK_COMB (@lem1524182) (@lem1524181 x y)). Qed.
Lemma lem1524184 : term98 = term99.
Proof. exact (@lem1483512 term58). Qed.
Lemma lem1524186 (x : nat) : (term100 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1524187 : term99 = term58.
Proof. exact (@lem1524186 term60). Qed.
Lemma lem1524188 : term98 = term58.
Proof. exact (TRANS (@lem1524184) (@lem1524187)). Qed.
Lemma lem1524189 (x : real) (y : real) : (term101 x y) = (term101 x y).
Proof. exact (eq_refl (term101 x y)). Qed.
Lemma lem1524190 (x : real) (y : real) : ((term97 x y) = term98) = ((term97 x y) = term58).
Proof. exact (MK_COMB (@lem1524189 x y) (@lem1524188)). Qed.
Lemma lem1524191 (x : real) (y : real) : (term97 x y) = term58.
Proof. exact (EQ_MP (@lem1524190 x y) (@lem1524183 x y)). Qed.
Lemma lem1524192 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1524193 (x : real) (y : real) : (term102 x y) = term103.
Proof. exact (MK_COMB (@lem1524192) (@lem1524191 x y)). Qed.
Lemma lem1524194 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1524195 (x : real) (y : real) : (term104 x y) = term105.
Proof. exact (MK_COMB (@lem1524193 x y) (@lem1524194)). Qed.
Lemma lem1524196 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1524197 (x : real) (y : real) : (term106 x y) = term103.
Proof. exact (MK_COMB (@lem1524196) (@lem1524181 x y)). Qed.
Lemma lem1524198 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1524199 (x : real) (y : real) : (term107 x y) = term105.
Proof. exact (MK_COMB (@lem1524197 x y) (@lem1524198)). Qed.
Lemma lem1524200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524201 (x : real) (y : real) : (term108 x y) = term109.
Proof. exact (MK_COMB (@lem1524200) (@lem1524199 x y)). Qed.
Lemma lem1524202 (x : real) (y : real) : (term22 x y) = term110.
Proof. exact (MK_COMB (@lem1524201 x y) (@lem1524195 x y)). Qed.
Lemma lem1524203 (x : real) (y : real) : (term9 x y) = term110.
Proof. exact (TRANS (@lem1524021 x y) (@lem1524202 x y)). Qed.
Lemma lem1524204 (x : real) : (term11 x) = term111.
Proof. exact (fun_ext (fun y : real => @lem1524203 x y)). Qed.
Lemma lem1524205 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524206 (x : real) : (term12 x) = term112.
Proof. exact (MK_COMB (@lem1524205) (@lem1524204 x)). Qed.
Lemma lem1524207 : term20 = term113.
Proof. exact (fun_ext (fun x : real => @lem1524206 x)). Qed.
Lemma lem1524208 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524209 : term21 = term114.
Proof. exact (MK_COMB (@lem1524208) (@lem1524207)). Qed.
Lemma lem1524210 : term13 = term114.
Proof. exact (TRANS (@lem1524020) (@lem1524209)). Qed.
Lemma lem1524212 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1524213 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1524212 real t). Qed.
Lemma lem1524214 : term114 = term112.
Proof. exact (@lem1524213 term112). Qed.
Lemma lem1524216 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1524217 (P : real -> Prop) (Q : real -> Prop) : (term119 P Q) = (term120 P Q).
Proof. exact (@lem1524216 real P Q). Qed.
Lemma lem1524218 : term121 = term122.
Proof. exact (@lem1524217 term123 term123). Qed.
Lemma lem1524219 (y : real) : (term124 y) = term105.
Proof. exact (eq_refl (term124 y)). Qed.
Lemma lem1524220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524221 (y : real) : (term125 y) = term109.
Proof. exact (MK_COMB (@lem1524220) (@lem1524219 y)). Qed.
Lemma lem1524222 (y : real) : (term124 y) = term105.
Proof. exact (eq_refl (term124 y)). Qed.
Lemma lem1524223 (y : real) : (term126 y) = term110.
Proof. exact (MK_COMB (@lem1524221 y) (@lem1524222 y)). Qed.
Lemma lem1524224 : term127 = term111.
Proof. exact (fun_ext (fun y : real => @lem1524223 y)). Qed.
Lemma lem1524225 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524226 : term121 = term112.
Proof. exact (MK_COMB (@lem1524225) (@lem1524224)). Qed.
Lemma lem1524227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1524228 : term128 = term129.
Proof. exact (MK_COMB (@lem1524227) (@lem1524226)). Qed.
Lemma lem1524229 (y : real) : (term124 y) = term105.
Proof. exact (eq_refl (term124 y)). Qed.
Lemma lem1524230 : term130 = term123.
Proof. exact (fun_ext (fun y : real => @lem1524229 y)). Qed.
Lemma lem1524231 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524232 : term131 = term132.
Proof. exact (MK_COMB (@lem1524231) (@lem1524230)). Qed.
Lemma lem1524233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524234 : term133 = term134.
Proof. exact (MK_COMB (@lem1524233) (@lem1524232)). Qed.
Lemma lem1524235 (y : real) : (term124 y) = term105.
Proof. exact (eq_refl (term124 y)). Qed.
Lemma lem1524236 : term130 = term123.
Proof. exact (fun_ext (fun y : real => @lem1524235 y)). Qed.
Lemma lem1524237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1524238 : term131 = term132.
Proof. exact (MK_COMB (@lem1524237) (@lem1524236)). Qed.
Lemma lem1524239 : term122 = term135.
Proof. exact (MK_COMB (@lem1524234) (@lem1524238)). Qed.
Lemma lem1524240 : (term121 = term122) = (term112 = term135).
Proof. exact (MK_COMB (@lem1524228) (@lem1524239)). Qed.
Lemma lem1524241 : term112 = term135.
Proof. exact (EQ_MP (@lem1524240) (@lem1524218)). Qed.
Lemma lem1524242 : term114 = term135.
Proof. exact (TRANS (@lem1524214) (@lem1524241)). Qed.
Lemma lem1524244 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1524245 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1524244 real t). Qed.
Lemma lem1524246 : term132 = term105.
Proof. exact (@lem1524245 term105). Qed.
Lemma lem1524247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1524248 : term134 = term109.
Proof. exact (MK_COMB (@lem1524247) (@lem1524246)). Qed.
Lemma lem1524250 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1524251 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1524250 real t). Qed.
Lemma lem1524252 : term132 = term105.
Proof. exact (@lem1524251 term105). Qed.
Lemma lem1524253 : term135 = term110.
Proof. exact (MK_COMB (@lem1524248) (@lem1524252)). Qed.
Lemma lem1524256 : term114 = term110.
Proof. exact (TRANS (@lem1524242) (@lem1524253)). Qed.
Lemma lem1524265 : term13 = term110.
Proof. exact (TRANS (@lem1524210) (@lem1524256)). Qed.
Lemma lem1524275 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem1524276 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem1524278 (n : nat) (m : nat) : (term136 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1524279 : term105 = term137.
Proof. exact (@lem1524278 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1524280 : term137 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1524281 : term105 = False.
Proof. exact (TRANS (@lem1524279) (@lem1524280)). Qed.
Lemma lem1524282 (h1 : term105) : False.
Proof. exact (EQ_MP (@lem1524281) (@lem1524276 h1)). Qed.
Lemma lem1524283 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem1524285 (n : nat) (m : nat) : (term136 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1524286 : term105 = term137.
Proof. exact (@lem1524285 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1524287 : term137 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1524288 : term105 = False.
Proof. exact (TRANS (@lem1524286) (@lem1524287)). Qed.
Lemma lem1524289 (h1 : term105) : False.
Proof. exact (EQ_MP (@lem1524288) (@lem1524283 h1)). Qed.
Lemma lem1524290 (h1 : term110) : False.
Proof. exact (or_elim (@lem1524275 h1) (fun h0 : term105 => @lem1524282 h0) (fun h0 : term105 => @lem1524289 h0)). Qed.
Lemma lem1524292 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem1524293 (h1 : term110) : term110 = False.
Proof. exact (prop_ext (fun h2 : term110 => @lem1524290 h1) (fun h2 : False => @lem1524292 h1)). Qed.
Lemma lem1524294 (h1 : term110) : False.
Proof. exact (EQ_MP (@lem1524293 h1) (@lem1524292 h1)). Qed.
Lemma lem1524295 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1524296 (h1 : term13) : term110.
Proof. exact (EQ_MP (@lem1524265) (@lem1524295 h1)). Qed.
Lemma lem1524297 (h1 : term13) : term110 = False.
Proof. exact (prop_ext (fun h2 : term110 => @lem1524294 h2) (fun h2 : False => @lem1524296 h1)). Qed.
Lemma lem1524298 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1524297 h1) (@lem1524296 h1)). Qed.
Lemma lem1524299 : term138.
Proof. exact (fun h0 : term13 => @lem1524298 h0). Qed.
Lemma lem1524300 : term139.
Proof. exact (@lem1386578 term140). Qed.
Lemma lem1524301 : term140.
Proof. exact (@lem1524300 (@lem1524299)). Qed.
