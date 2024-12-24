Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_MAX_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482709_spec.
Require Import thm1482716_spec.
Require Import thm1483205_spec.
Require Import thm1483429_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1554996 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1554997 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1554996 (term4 x)). Qed.
Lemma lem1554998 (x : real) (y : real) : (term5 x y) = ((real_min x y) = (term6 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1554999 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1555001 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1554999) (@lem1554998 x y)). Qed.
Lemma lem1555002 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1555001 x y)). Qed.
Lemma lem1555003 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555004 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1555003) (@lem1555002 x)). Qed.
Lemma lem1555005 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1554997 x) (@lem1555004 x)). Qed.
Lemma lem1555006 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1555007 : term12 = term13.
Proof. exact (@lem1555006 term14). Qed.
Lemma lem1555008 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1555009 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1555010 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1555009) (@lem1555008 x)). Qed.
Lemma lem1555011 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1555010 x) (@lem1555005 x)). Qed.
Lemma lem1555012 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1555011 x)). Qed.
Lemma lem1555013 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555014 : term13 = term20.
Proof. exact (MK_COMB (@lem1555013) (@lem1555012)). Qed.
Lemma lem1555016 : term12 = term20.
Proof. exact (TRANS (@lem1555007) (@lem1555014)). Qed.
Lemma lem1555019 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1555020 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1555019 x y)). Qed.
Lemma lem1555021 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555022 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1555021) (@lem1555020 x)). Qed.
Lemma lem1555023 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1555022 x)). Qed.
Lemma lem1555024 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555025 : term20 = term20.
Proof. exact (MK_COMB (@lem1555024) (@lem1555023)). Qed.
Lemma lem1555026 : term12 = term20.
Proof. exact (TRANS (@lem1555016) (@lem1555025)). Qed.
Lemma lem1555027 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (real_min x y) (term6 x y)). Qed.
Lemma lem1555034 (x : real) (y : real) : (term6 x y) = (term22 x y).
Proof. exact (@lem1483512 (term23 x y)). Qed.
Lemma lem1555037 (x : real) (y : real) : (term24 x y) = (term24 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1555038 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1555037 x y) (@lem1555034 x y)). Qed.
Lemma lem1555039 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 (real_min x y) (term22 x y)). Qed.
Lemma lem1555040 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (@lem1483476 term30 term30 (term23 x y)). Qed.
Lemma lem1555042 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1555043 : term33 = term34.
Proof. exact (@lem1555042 term35 term35). Qed.
Lemma lem1555044 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1555045 : term37 = term35.
Proof. exact (EQ_MP (@lem1555044) (@lem940073)). Qed.
Lemma lem1555046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1555047 : term34 = term38.
Proof. exact (MK_COMB (@lem1555046) (@lem1555045)). Qed.
Lemma lem1555048 : term33 = term38.
Proof. exact (TRANS (@lem1555043) (@lem1555047)). Qed.
Lemma lem1555049 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555050 : term39 = term40.
Proof. exact (MK_COMB (@lem1555049) (@lem1555048)). Qed.
Lemma lem1555051 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1555052 (x : real) (y : real) : (term29 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1555050) (@lem1555051 x y)). Qed.
Lemma lem1555053 (x : real) (y : real) : (term28 x y) = (term41 x y).
Proof. exact (TRANS (@lem1555040 x y) (@lem1555052 x y)). Qed.
Lemma lem1555054 (x : real) (y : real) : (term41 x y) = (term23 x y).
Proof. exact (@lem1483436 (term23 x y)). Qed.
Lemma lem1555055 (x : real) (y : real) : (term28 x y) = (term23 x y).
Proof. exact (TRANS (@lem1555053 x y) (@lem1555054 x y)). Qed.
Lemma lem1555056 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1555057 (x : real) (y : real) : (term27 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1555056 x y) (@lem1555055 x y)). Qed.
Lemma lem1555058 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1483488 (term23 x y) (real_min x y)). Qed.
Lemma lem1555059 (x : real) (y : real) : (term27 x y) = (term44 x y).
Proof. exact (TRANS (@lem1555057 x y) (@lem1555058 x y)). Qed.
Lemma lem1555060 (x : real) (y : real) : (term26 x y) = (term44 x y).
Proof. exact (TRANS (@lem1555039 x y) (@lem1555059 x y)). Qed.
Lemma lem1555061 (x : real) (y : real) : (term25 x y) = (term44 x y).
Proof. exact (TRANS (@lem1555038 x y) (@lem1555060 x y)). Qed.
Lemma lem1555062 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1555063 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1555062) (@lem1555061 x y)). Qed.
Lemma lem1555064 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (@lem1483512 (term44 x y)). Qed.
Lemma lem1555071 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (@lem1483508 (term23 x y) term30 (real_min x y)). Qed.
Lemma lem1555072 (x : real) (y : real) : (term46 x y) = (term48 x y).
Proof. exact (TRANS (@lem1555064 x y) (@lem1555071 x y)). Qed.
Lemma lem1555073 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1555074 (x : real) (y : real) : ((term45 x y) = (term46 x y)) = ((term45 x y) = (term48 x y)).
Proof. exact (MK_COMB (@lem1555073 x y) (@lem1555072 x y)). Qed.
Lemma lem1555075 (x : real) (y : real) : (term45 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem1555074 x y) (@lem1555063 x y)). Qed.
Lemma lem1555076 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555077 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1555076) (@lem1555075 x y)). Qed.
Lemma lem1555078 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555079 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1555077 x y) (@lem1555078)). Qed.
Lemma lem1555080 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555081 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1555080) (@lem1555061 x y)). Qed.
Lemma lem1555082 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555083 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1555081 x y) (@lem1555082)). Qed.
Lemma lem1555084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555085 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1555084) (@lem1555083 x y)). Qed.
Lemma lem1555086 (x : real) (y : real) : (term21 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1555085 x y) (@lem1555079 x y)). Qed.
Lemma lem1555087 (x : real) (y : real) : (term8 x y) = (term61 x y).
Proof. exact (TRANS (@lem1555027 x y) (@lem1555086 x y)). Qed.
Lemma lem1555088 (x : real) : (term10 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1555087 x y)). Qed.
Lemma lem1555089 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555090 (x : real) : (term11 x) = (term63 x).
Proof. exact (MK_COMB (@lem1555089) (@lem1555088 x)). Qed.
Lemma lem1555091 : term19 = term64.
Proof. exact (fun_ext (fun x : real => @lem1555090 x)). Qed.
Lemma lem1555092 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555093 : term20 = term65.
Proof. exact (MK_COMB (@lem1555092) (@lem1555091)). Qed.
Lemma lem1555094 : term12 = term65.
Proof. exact (TRANS (@lem1555026) (@lem1555093)). Qed.
Lemma lem1555100 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1555101 (P : real -> Prop) (Q : real -> Prop) : (term68 P Q) = (term69 P Q).
Proof. exact (@lem1555100 real P Q). Qed.
Lemma lem1555102 (x : real) : (term70 x) = (term71 x).
Proof. exact (@lem1555101 (term72 x) (term73 x)). Qed.
Lemma lem1555103 (x : real) (y : real) : (term74 x y) = (term58 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1555104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555105 (x : real) (y : real) : (term75 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1555104) (@lem1555103 x y)). Qed.
Lemma lem1555106 (x : real) (y : real) : (term76 x y) = (term54 x y).
Proof. exact (eq_refl (term76 x y)). Qed.
Lemma lem1555107 (x : real) (y : real) : (term77 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1555105 x y) (@lem1555106 x y)). Qed.
Lemma lem1555108 (x : real) : (term78 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1555107 x y)). Qed.
Lemma lem1555109 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555110 (x : real) : (term70 x) = (term63 x).
Proof. exact (MK_COMB (@lem1555109) (@lem1555108 x)). Qed.
Lemma lem1555111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1555112 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1555111) (@lem1555110 x)). Qed.
Lemma lem1555113 (x : real) (y : real) : (term74 x y) = (term58 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1555114 (x : real) : (term81 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1555113 x y)). Qed.
Lemma lem1555115 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555116 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1555115) (@lem1555114 x)). Qed.
Lemma lem1555117 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555118 (x : real) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1555117) (@lem1555116 x)). Qed.
Lemma lem1555119 (x : real) (y : real) : (term76 x y) = (term54 x y).
Proof. exact (eq_refl (term76 x y)). Qed.
Lemma lem1555120 (x : real) : (term86 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1555119 x y)). Qed.
Lemma lem1555121 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555122 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1555121) (@lem1555120 x)). Qed.
Lemma lem1555123 (x : real) : (term71 x) = (term89 x).
Proof. exact (MK_COMB (@lem1555118 x) (@lem1555122 x)). Qed.
Lemma lem1555124 (x : real) : ((term70 x) = (term71 x)) = ((term63 x) = (term89 x)).
Proof. exact (MK_COMB (@lem1555112 x) (@lem1555123 x)). Qed.
Lemma lem1555125 (x : real) : (term63 x) = (term89 x).
Proof. exact (EQ_MP (@lem1555124 x) (@lem1555102 x)). Qed.
Lemma lem1555134 : term64 = term90.
Proof. exact (fun_ext (fun x : real => @lem1555125 x)). Qed.
Lemma lem1555135 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555136 : term65 = term91.
Proof. exact (MK_COMB (@lem1555135) (@lem1555134)). Qed.
Lemma lem1555138 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1555139 (P : real -> Prop) (Q : real -> Prop) : (term68 P Q) = (term69 P Q).
Proof. exact (@lem1555138 real P Q). Qed.
Lemma lem1555140 : term92 = term93.
Proof. exact (@lem1555139 term94 term95). Qed.
Lemma lem1555141 (x : real) : (term96 x) = (term83 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1555142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555143 (x : real) : (term97 x) = (term85 x).
Proof. exact (MK_COMB (@lem1555142) (@lem1555141 x)). Qed.
Lemma lem1555144 (x : real) : (term98 x) = (term88 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem1555145 (x : real) : (term99 x) = (term89 x).
Proof. exact (MK_COMB (@lem1555143 x) (@lem1555144 x)). Qed.
Lemma lem1555146 : term100 = term90.
Proof. exact (fun_ext (fun x : real => @lem1555145 x)). Qed.
Lemma lem1555147 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555148 : term92 = term91.
Proof. exact (MK_COMB (@lem1555147) (@lem1555146)). Qed.
Lemma lem1555149 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1555150 : term101 = term102.
Proof. exact (MK_COMB (@lem1555149) (@lem1555148)). Qed.
Lemma lem1555151 (x : real) : (term96 x) = (term83 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1555152 : term103 = term94.
Proof. exact (fun_ext (fun x : real => @lem1555151 x)). Qed.
Lemma lem1555153 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555154 : term104 = term105.
Proof. exact (MK_COMB (@lem1555153) (@lem1555152)). Qed.
Lemma lem1555155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555156 : term106 = term107.
Proof. exact (MK_COMB (@lem1555155) (@lem1555154)). Qed.
Lemma lem1555157 (x : real) : (term98 x) = (term88 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem1555158 : term108 = term95.
Proof. exact (fun_ext (fun x : real => @lem1555157 x)). Qed.
Lemma lem1555159 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555160 : term109 = term110.
Proof. exact (MK_COMB (@lem1555159) (@lem1555158)). Qed.
Lemma lem1555161 : term93 = term111.
Proof. exact (MK_COMB (@lem1555156) (@lem1555160)). Qed.
Lemma lem1555162 : (term92 = term93) = (term91 = term111).
Proof. exact (MK_COMB (@lem1555150) (@lem1555161)). Qed.
Lemma lem1555163 : term91 = term111.
Proof. exact (EQ_MP (@lem1555162) (@lem1555140)). Qed.
Lemma lem1555180 : term65 = term111.
Proof. exact (TRANS (@lem1555136) (@lem1555163)). Qed.
Lemma lem1555182 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1555183 (P : real -> Prop) (Q : real -> Prop) : (term69 P Q) = (term68 P Q).
Proof. exact (@lem1555182 real P Q). Qed.
Lemma lem1555184 : term93 = term92.
Proof. exact (@lem1555183 term94 term95). Qed.
Lemma lem1555185 (x : real) : (term96 x) = (term83 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1555186 : term103 = term94.
Proof. exact (fun_ext (fun x : real => @lem1555185 x)). Qed.
Lemma lem1555187 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555188 : term104 = term105.
Proof. exact (MK_COMB (@lem1555187) (@lem1555186)). Qed.
Lemma lem1555189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555190 : term106 = term107.
Proof. exact (MK_COMB (@lem1555189) (@lem1555188)). Qed.
Lemma lem1555191 (x : real) : (term98 x) = (term88 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem1555192 : term108 = term95.
Proof. exact (fun_ext (fun x : real => @lem1555191 x)). Qed.
Lemma lem1555193 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555194 : term109 = term110.
Proof. exact (MK_COMB (@lem1555193) (@lem1555192)). Qed.
Lemma lem1555195 : term93 = term111.
Proof. exact (MK_COMB (@lem1555190) (@lem1555194)). Qed.
Lemma lem1555196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1555197 : term112 = term113.
Proof. exact (MK_COMB (@lem1555196) (@lem1555195)). Qed.
Lemma lem1555198 (x : real) : (term96 x) = (term83 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1555199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555200 (x : real) : (term97 x) = (term85 x).
Proof. exact (MK_COMB (@lem1555199) (@lem1555198 x)). Qed.
Lemma lem1555201 (x : real) : (term98 x) = (term88 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem1555202 (x : real) : (term99 x) = (term89 x).
Proof. exact (MK_COMB (@lem1555200 x) (@lem1555201 x)). Qed.
Lemma lem1555203 : term100 = term90.
Proof. exact (fun_ext (fun x : real => @lem1555202 x)). Qed.
Lemma lem1555204 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555205 : term92 = term91.
Proof. exact (MK_COMB (@lem1555204) (@lem1555203)). Qed.
Lemma lem1555206 : (term93 = term92) = (term111 = term91).
Proof. exact (MK_COMB (@lem1555197) (@lem1555205)). Qed.
Lemma lem1555207 : term111 = term91.
Proof. exact (EQ_MP (@lem1555206) (@lem1555184)). Qed.
Lemma lem1555209 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1555210 (P : real -> Prop) (Q : real -> Prop) : (term69 P Q) = (term68 P Q).
Proof. exact (@lem1555209 real P Q). Qed.
Lemma lem1555211 (x : real) : (term71 x) = (term70 x).
Proof. exact (@lem1555210 (term72 x) (term73 x)). Qed.
Lemma lem1555212 (x : real) (y : real) : (term74 x y) = (term58 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1555213 (x : real) : (term81 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1555212 x y)). Qed.
Lemma lem1555214 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555215 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1555214) (@lem1555213 x)). Qed.
Lemma lem1555216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555217 (x : real) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1555216) (@lem1555215 x)). Qed.
Lemma lem1555218 (x : real) (y : real) : (term76 x y) = (term54 x y).
Proof. exact (eq_refl (term76 x y)). Qed.
Lemma lem1555219 (x : real) : (term86 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1555218 x y)). Qed.
Lemma lem1555220 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555221 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1555220) (@lem1555219 x)). Qed.
Lemma lem1555222 (x : real) : (term71 x) = (term89 x).
Proof. exact (MK_COMB (@lem1555217 x) (@lem1555221 x)). Qed.
Lemma lem1555223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1555224 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1555223) (@lem1555222 x)). Qed.
Lemma lem1555225 (x : real) (y : real) : (term74 x y) = (term58 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1555226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555227 (x : real) (y : real) : (term75 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1555226) (@lem1555225 x y)). Qed.
Lemma lem1555228 (x : real) (y : real) : (term76 x y) = (term54 x y).
Proof. exact (eq_refl (term76 x y)). Qed.
Lemma lem1555229 (x : real) (y : real) : (term77 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1555227 x y) (@lem1555228 x y)). Qed.
Lemma lem1555230 (x : real) : (term78 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1555229 x y)). Qed.
Lemma lem1555231 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555232 (x : real) : (term70 x) = (term63 x).
Proof. exact (MK_COMB (@lem1555231) (@lem1555230 x)). Qed.
Lemma lem1555233 (x : real) : ((term71 x) = (term70 x)) = ((term89 x) = (term63 x)).
Proof. exact (MK_COMB (@lem1555224 x) (@lem1555232 x)). Qed.
Lemma lem1555234 (x : real) : (term89 x) = (term63 x).
Proof. exact (EQ_MP (@lem1555233 x) (@lem1555211 x)). Qed.
Lemma lem1555235 : term90 = term64.
Proof. exact (fun_ext (fun x : real => @lem1555234 x)). Qed.
Lemma lem1555236 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555237 : term91 = term65.
Proof. exact (MK_COMB (@lem1555236) (@lem1555235)). Qed.
Lemma lem1555238 : term111 = term65.
Proof. exact (TRANS (@lem1555207) (@lem1555237)). Qed.
Lemma lem1555239 : term65 = term65.
Proof. exact (TRANS (@lem1555180) (@lem1555238)). Qed.
Lemma lem1555242 : term12 = term65.
Proof. exact (TRANS (@lem1555094) (@lem1555239)). Qed.
Lemma lem1555247 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1555248 (x : real) : (term62 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1555247 x y)). Qed.
Lemma lem1555249 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555250 (x : real) : (term63 x) = (term63 x).
Proof. exact (MK_COMB (@lem1555249) (@lem1555248 x)). Qed.
Lemma lem1555251 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1555250 x)). Qed.
Lemma lem1555252 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555253 : term65 = term65.
Proof. exact (MK_COMB (@lem1555252) (@lem1555251)). Qed.
Lemma lem1555254 : term12 = term65.
Proof. exact (TRANS (@lem1555242) (@lem1555253)). Qed.
Lemma lem1555256 (x : real) (a : real) (y : real) (r : real) : (term116 a x y r) = (term117 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1555257 (x : real) (y : real) : (term58 x y) = (term118 x y).
Proof. exact (@lem1555256 x (term23 x y) y term52). Qed.
Lemma lem1555264 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (@lem1483488 y (term23 x y)). Qed.
Lemma lem1555265 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555266 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1555265) (@lem1555264 x y)). Qed.
Lemma lem1555267 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555268 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1555266 x y) (@lem1555267)). Qed.
Lemma lem1555275 (x : real) (y : real) : (term125 y x) = (term126 x y).
Proof. exact (@lem1483488 x (term23 x y)). Qed.
Lemma lem1555276 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555277 (x : real) (y : real) : (term127 y x) = (term128 x y).
Proof. exact (MK_COMB (@lem1555276) (@lem1555275 x y)). Qed.
Lemma lem1555278 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555279 (x : real) (y : real) : (term129 y x) = (term130 x y).
Proof. exact (MK_COMB (@lem1555277 x y) (@lem1555278)). Qed.
Lemma lem1555280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555281 (x : real) (y : real) : (term131 y x) = (term132 x y).
Proof. exact (MK_COMB (@lem1555280) (@lem1555279 x y)). Qed.
Lemma lem1555282 (x : real) (y : real) : (term118 x y) = (term133 x y).
Proof. exact (MK_COMB (@lem1555281 x y) (@lem1555268 x y)). Qed.
Lemma lem1555283 (x : real) (y : real) : (term58 x y) = (term133 x y).
Proof. exact (TRANS (@lem1555257 x y) (@lem1555282 x y)). Qed.
Lemma lem1555284 (x : real) (y : real) : (term134 x y) = (term133 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1555285 (x : real) (y : real) : (term133 x y) = (term134 x y).
Proof. exact (SYM (@lem1555284 x y)). Qed.
Lemma lem1555286 (y : real) (x : real) : (term134 x y) = (term135 y x).
Proof. exact (@lem1483205 (real_neg y) (term136 x y) (real_neg x)). Qed.
Lemma lem1555287 (y : real) (x : real) : (term133 x y) = (term135 y x).
Proof. exact (TRANS (@lem1555285 x y) (@lem1555286 y x)). Qed.
Lemma lem1555288 (y : real) (x : real) : (term137 y x) = (term138 y x).
Proof. exact (eq_refl (term137 y x)). Qed.
Lemma lem1555289 (x : real) (y : real) : (term139 x y) = (term139 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1555290 (y : real) (x : real) : (term140 y x) = (term141 y x).
Proof. exact (MK_COMB (@lem1555289 x y) (@lem1555288 y x)). Qed.
Lemma lem1555291 (x : real) (y : real) : (term142 x y) = (term143 x y).
Proof. exact (eq_refl (term142 x y)). Qed.
Lemma lem1555292 (y : real) (x : real) : (term144 y x) = (term144 y x).
Proof. exact (eq_refl (term144 y x)). Qed.
Lemma lem1555293 (x : real) (y : real) : (term145 x y) = (term146 x y).
Proof. exact (MK_COMB (@lem1555292 y x) (@lem1555291 x y)). Qed.
Lemma lem1555294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555295 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1555294) (@lem1555293 x y)). Qed.
Lemma lem1555296 (y : real) (x : real) : (term135 y x) = (term149 y x).
Proof. exact (MK_COMB (@lem1555295 x y) (@lem1555290 y x)). Qed.
Lemma lem1555297 (x : real) (y : real) : (term150 x y) = (term150 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1555298 (y : real) (x : real) : ((term133 x y) = (term135 y x)) = ((term133 x y) = (term149 y x)).
Proof. exact (MK_COMB (@lem1555297 x y) (@lem1555296 y x)). Qed.
Lemma lem1555299 (y : real) (x : real) : (term133 x y) = (term149 y x).
Proof. exact (EQ_MP (@lem1555298 y x) (@lem1555287 y x)). Qed.
Lemma lem1555300 (y : real) (x : real) : (term151 y x) = (term152 y x).
Proof. exact (@lem1483527 (real_neg y) (real_neg x)). Qed.
Lemma lem1555307 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1555314 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1555315 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555316 (y : real) : (term154 y) = (term155 y).
Proof. exact (MK_COMB (@lem1555315) (@lem1555314 y)). Qed.
Lemma lem1555317 (y : real) (x : real) : (term156 y x) = (term157 y x).
Proof. exact (MK_COMB (@lem1555316 y) (@lem1555307 x)). Qed.
Lemma lem1555318 (y : real) (x : real) : (term157 y x) = (term158 y x).
Proof. exact (@lem1483519 (term153 y) (term153 x)). Qed.
Lemma lem1555319 (x : real) : (term159 x) = (term160 x).
Proof. exact (@lem1483476 term30 term30 x). Qed.
Lemma lem1555321 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1555322 : term33 = term34.
Proof. exact (@lem1555321 term35 term35). Qed.
Lemma lem1555323 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1555324 : term37 = term35.
Proof. exact (EQ_MP (@lem1555323) (@lem940073)). Qed.
Lemma lem1555325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1555326 : term34 = term38.
Proof. exact (MK_COMB (@lem1555325) (@lem1555324)). Qed.
Lemma lem1555327 : term33 = term38.
Proof. exact (TRANS (@lem1555322) (@lem1555326)). Qed.
Lemma lem1555328 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555329 : term39 = term40.
Proof. exact (MK_COMB (@lem1555328) (@lem1555327)). Qed.
Lemma lem1555330 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1555331 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1555329) (@lem1555330 x)). Qed.
Lemma lem1555332 (x : real) : (term159 x) = (term161 x).
Proof. exact (TRANS (@lem1555319 x) (@lem1555331 x)). Qed.
Lemma lem1555333 (x : real) : (term161 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1555334 (x : real) : (term159 x) = x.
Proof. exact (TRANS (@lem1555332 x) (@lem1555333 x)). Qed.
Lemma lem1555335 (y : real) : (term162 y) = (term162 y).
Proof. exact (eq_refl (term162 y)). Qed.
Lemma lem1555336 (y : real) (x : real) : (term158 y x) = (term163 y x).
Proof. exact (MK_COMB (@lem1555335 y) (@lem1555334 x)). Qed.
Lemma lem1555337 (x : real) (y : real) : (term163 y x) = (term164 x y).
Proof. exact (@lem1483488 x (term153 y)). Qed.
Lemma lem1555338 (x : real) (y : real) : (term158 y x) = (term164 x y).
Proof. exact (TRANS (@lem1555336 y x) (@lem1555337 x y)). Qed.
Lemma lem1555339 (x : real) (y : real) : (term157 y x) = (term164 x y).
Proof. exact (TRANS (@lem1555318 y x) (@lem1555338 x y)). Qed.
Lemma lem1555340 (x : real) (y : real) : (term156 y x) = (term164 x y).
Proof. exact (TRANS (@lem1555317 y x) (@lem1555339 x y)). Qed.
Lemma lem1555341 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1555342 (x : real) (y : real) : (term165 y x) = (term166 x y).
Proof. exact (MK_COMB (@lem1555341) (@lem1555340 x y)). Qed.
Lemma lem1555343 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555344 (x : real) (y : real) : (term152 y x) = (term167 x y).
Proof. exact (MK_COMB (@lem1555342 x y) (@lem1555343)). Qed.
Lemma lem1555345 (x : real) (y : real) : (term151 y x) = (term167 x y).
Proof. exact (TRANS (@lem1555300 y x) (@lem1555344 x y)). Qed.
Lemma lem1555346 (x : real) (y : real) : (term168 x y) = (term169 x y).
Proof. exact (@lem1483525 (term170 x y) term52). Qed.
Lemma lem1555347 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555354 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1555357 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1555360 (x : real) (y : real) : (term170 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1555357 x) (@lem1555354 y)). Qed.
Lemma lem1555361 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555362 (x : real) (y : real) : (term171 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem1555361) (@lem1555360 x y)). Qed.
Lemma lem1555363 (x : real) (y : real) : (term173 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1555362 x y) (@lem1555347)). Qed.
Lemma lem1555364 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483519 (term164 x y) term52). Qed.
Lemma lem1555366 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555367 : term177 = term52.
Proof. exact (@lem1555366 term35). Qed.
Lemma lem1555368 (x : real) (y : real) : (term178 x y) = (term178 x y).
Proof. exact (eq_refl (term178 x y)). Qed.
Lemma lem1555369 (x : real) (y : real) : (term175 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1555368 x y) (@lem1555367)). Qed.
Lemma lem1555370 (x : real) (y : real) : (term179 x y) = (term164 x y).
Proof. exact (@lem1483450 (term164 x y)). Qed.
Lemma lem1555371 (x : real) (y : real) : (term175 x y) = (term164 x y).
Proof. exact (TRANS (@lem1555369 x y) (@lem1555370 x y)). Qed.
Lemma lem1555372 (x : real) (y : real) : (term174 x y) = (term164 x y).
Proof. exact (TRANS (@lem1555364 x y) (@lem1555371 x y)). Qed.
Lemma lem1555373 (x : real) (y : real) : (term173 x y) = (term164 x y).
Proof. exact (TRANS (@lem1555363 x y) (@lem1555372 x y)). Qed.
Lemma lem1555374 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555375 (x : real) (y : real) : (term180 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1555374) (@lem1555373 x y)). Qed.
Lemma lem1555376 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555377 (x : real) (y : real) : (term169 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1555375 x y) (@lem1555376)). Qed.
Lemma lem1555378 (x : real) (y : real) : (term168 x y) = (term182 x y).
Proof. exact (TRANS (@lem1555346 x y) (@lem1555377 x y)). Qed.
Lemma lem1555379 (y : real) : (term183 y) = (term184 y).
Proof. exact (@lem1483525 (term185 y) term52). Qed.
Lemma lem1555380 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555387 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1555390 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1555391 (y : real) : (term185 y) = (term186 y).
Proof. exact (MK_COMB (@lem1555390 y) (@lem1555387 y)). Qed.
Lemma lem1555392 (y : real) : (term186 y) = (term187 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1555394 (m : nat) : (term188 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1555395 : term189 = term52.
Proof. exact (@lem1555394 term35). Qed.
Lemma lem1555396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555397 : term190 = term191.
Proof. exact (MK_COMB (@lem1555396) (@lem1555395)). Qed.
Lemma lem1555398 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1555399 (y : real) : (term187 y) = (term192 y).
Proof. exact (MK_COMB (@lem1555397) (@lem1555398 y)). Qed.
Lemma lem1555400 (y : real) : (term186 y) = (term192 y).
Proof. exact (TRANS (@lem1555392 y) (@lem1555399 y)). Qed.
Lemma lem1555401 (y : real) : (term192 y) = term52.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1555402 (y : real) : (term186 y) = term52.
Proof. exact (TRANS (@lem1555400 y) (@lem1555401 y)). Qed.
Lemma lem1555403 (y : real) : (term185 y) = term52.
Proof. exact (TRANS (@lem1555391 y) (@lem1555402 y)). Qed.
Lemma lem1555404 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555405 (y : real) : (term193 y) = term194.
Proof. exact (MK_COMB (@lem1555404) (@lem1555403 y)). Qed.
Lemma lem1555406 (y : real) : (term195 y) = term196.
Proof. exact (MK_COMB (@lem1555405 y) (@lem1555380)). Qed.
Lemma lem1555407 : term196 = term197.
Proof. exact (@lem1483519 term52 term52). Qed.
Lemma lem1555409 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555410 : term177 = term52.
Proof. exact (@lem1555409 term35). Qed.
Lemma lem1555411 : term198 = term198.
Proof. exact (eq_refl term198). Qed.
Lemma lem1555412 : term197 = term199.
Proof. exact (MK_COMB (@lem1555411) (@lem1555410)). Qed.
Lemma lem1555413 : term199 = term52.
Proof. exact (@lem1483448 term52). Qed.
Lemma lem1555414 : term197 = term52.
Proof. exact (TRANS (@lem1555412) (@lem1555413)). Qed.
Lemma lem1555415 : term196 = term52.
Proof. exact (TRANS (@lem1555407) (@lem1555414)). Qed.
Lemma lem1555416 (y : real) : (term195 y) = term52.
Proof. exact (TRANS (@lem1555406 y) (@lem1555415)). Qed.
Lemma lem1555417 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555418 (y : real) : (term200 y) = term201.
Proof. exact (MK_COMB (@lem1555417) (@lem1555416 y)). Qed.
Lemma lem1555419 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555420 (y : real) : (term184 y) = term202.
Proof. exact (MK_COMB (@lem1555418 y) (@lem1555419)). Qed.
Lemma lem1555421 (y : real) : (term183 y) = term202.
Proof. exact (TRANS (@lem1555379 y) (@lem1555420 y)). Qed.
Lemma lem1555422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555423 (x : real) (y : real) : (term203 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1555422) (@lem1555378 x y)). Qed.
Lemma lem1555424 (x : real) (y : real) : (term143 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1555423 x y) (@lem1555421 y)). Qed.
Lemma lem1555425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555426 (x : real) (y : real) : (term144 y x) = (term206 x y).
Proof. exact (MK_COMB (@lem1555425) (@lem1555345 x y)). Qed.
Lemma lem1555427 (x : real) (y : real) : (term146 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1555426 x y) (@lem1555424 x y)). Qed.
Lemma lem1555428 (x : real) (y : real) : (term208 x y) = (term209 x y).
Proof. exact (@lem1483525 (real_neg x) (real_neg y)). Qed.
Lemma lem1555435 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1555442 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1555443 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555444 (x : real) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1555443) (@lem1555442 x)). Qed.
Lemma lem1555445 (x : real) (y : real) : (term156 x y) = (term157 x y).
Proof. exact (MK_COMB (@lem1555444 x) (@lem1555435 y)). Qed.
Lemma lem1555446 (x : real) (y : real) : (term157 x y) = (term158 x y).
Proof. exact (@lem1483519 (term153 x) (term153 y)). Qed.
Lemma lem1555447 (y : real) : (term159 y) = (term160 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1555449 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1555450 : term33 = term34.
Proof. exact (@lem1555449 term35 term35). Qed.
Lemma lem1555451 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1555452 : term37 = term35.
Proof. exact (EQ_MP (@lem1555451) (@lem940073)). Qed.
Lemma lem1555453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1555454 : term34 = term38.
Proof. exact (MK_COMB (@lem1555453) (@lem1555452)). Qed.
Lemma lem1555455 : term33 = term38.
Proof. exact (TRANS (@lem1555450) (@lem1555454)). Qed.
Lemma lem1555456 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555457 : term39 = term40.
Proof. exact (MK_COMB (@lem1555456) (@lem1555455)). Qed.
Lemma lem1555458 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1555459 (y : real) : (term160 y) = (term161 y).
Proof. exact (MK_COMB (@lem1555457) (@lem1555458 y)). Qed.
Lemma lem1555460 (y : real) : (term159 y) = (term161 y).
Proof. exact (TRANS (@lem1555447 y) (@lem1555459 y)). Qed.
Lemma lem1555461 (y : real) : (term161 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1555462 (y : real) : (term159 y) = y.
Proof. exact (TRANS (@lem1555460 y) (@lem1555461 y)). Qed.
Lemma lem1555463 (x : real) : (term162 x) = (term162 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1555466 (x : real) (y : real) : (term158 x y) = (term163 x y).
Proof. exact (MK_COMB (@lem1555463 x) (@lem1555462 y)). Qed.
Lemma lem1555467 (x : real) (y : real) : (term157 x y) = (term163 x y).
Proof. exact (TRANS (@lem1555446 x y) (@lem1555466 x y)). Qed.
Lemma lem1555468 (x : real) (y : real) : (term156 x y) = (term163 x y).
Proof. exact (TRANS (@lem1555445 x y) (@lem1555467 x y)). Qed.
Lemma lem1555469 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555470 (x : real) (y : real) : (term210 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1555469) (@lem1555468 x y)). Qed.
Lemma lem1555471 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555472 (x : real) (y : real) : (term209 x y) = (term212 x y).
Proof. exact (MK_COMB (@lem1555470 x y) (@lem1555471)). Qed.
Lemma lem1555473 (x : real) (y : real) : (term208 x y) = (term212 x y).
Proof. exact (TRANS (@lem1555428 x y) (@lem1555472 x y)). Qed.
Lemma lem1555474 (x : real) : (term183 x) = (term184 x).
Proof. exact (@lem1483525 (term185 x) term52). Qed.
Lemma lem1555475 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555482 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1555485 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1555486 (x : real) : (term185 x) = (term186 x).
Proof. exact (MK_COMB (@lem1555485 x) (@lem1555482 x)). Qed.
Lemma lem1555487 (x : real) : (term186 x) = (term187 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1555489 (m : nat) : (term188 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1555490 : term189 = term52.
Proof. exact (@lem1555489 term35). Qed.
Lemma lem1555491 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555492 : term190 = term191.
Proof. exact (MK_COMB (@lem1555491) (@lem1555490)). Qed.
Lemma lem1555493 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1555494 (x : real) : (term187 x) = (term192 x).
Proof. exact (MK_COMB (@lem1555492) (@lem1555493 x)). Qed.
Lemma lem1555495 (x : real) : (term186 x) = (term192 x).
Proof. exact (TRANS (@lem1555487 x) (@lem1555494 x)). Qed.
Lemma lem1555496 (x : real) : (term192 x) = term52.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1555497 (x : real) : (term186 x) = term52.
Proof. exact (TRANS (@lem1555495 x) (@lem1555496 x)). Qed.
Lemma lem1555498 (x : real) : (term185 x) = term52.
Proof. exact (TRANS (@lem1555486 x) (@lem1555497 x)). Qed.
Lemma lem1555499 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555500 (x : real) : (term193 x) = term194.
Proof. exact (MK_COMB (@lem1555499) (@lem1555498 x)). Qed.
Lemma lem1555501 (x : real) : (term195 x) = term196.
Proof. exact (MK_COMB (@lem1555500 x) (@lem1555475)). Qed.
Lemma lem1555502 : term196 = term197.
Proof. exact (@lem1483519 term52 term52). Qed.
Lemma lem1555504 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555505 : term177 = term52.
Proof. exact (@lem1555504 term35). Qed.
Lemma lem1555506 : term198 = term198.
Proof. exact (eq_refl term198). Qed.
Lemma lem1555507 : term197 = term199.
Proof. exact (MK_COMB (@lem1555506) (@lem1555505)). Qed.
Lemma lem1555508 : term199 = term52.
Proof. exact (@lem1483448 term52). Qed.
Lemma lem1555509 : term197 = term52.
Proof. exact (TRANS (@lem1555507) (@lem1555508)). Qed.
Lemma lem1555510 : term196 = term52.
Proof. exact (TRANS (@lem1555502) (@lem1555509)). Qed.
Lemma lem1555511 (x : real) : (term195 x) = term52.
Proof. exact (TRANS (@lem1555501 x) (@lem1555510)). Qed.
Lemma lem1555512 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555513 (x : real) : (term200 x) = term201.
Proof. exact (MK_COMB (@lem1555512) (@lem1555511 x)). Qed.
Lemma lem1555514 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555515 (x : real) : (term184 x) = term202.
Proof. exact (MK_COMB (@lem1555513 x) (@lem1555514)). Qed.
Lemma lem1555516 (x : real) : (term183 x) = term202.
Proof. exact (TRANS (@lem1555474 x) (@lem1555515 x)). Qed.
Lemma lem1555517 (y : real) (x : real) : (term168 y x) = (term169 y x).
Proof. exact (@lem1483525 (term170 y x) term52). Qed.
Lemma lem1555518 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555525 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1555528 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1555529 (y : real) (x : real) : (term170 y x) = (term164 y x).
Proof. exact (MK_COMB (@lem1555528 y) (@lem1555525 x)). Qed.
Lemma lem1555530 (x : real) (y : real) : (term164 y x) = (term163 x y).
Proof. exact (@lem1483488 (term153 x) y). Qed.
Lemma lem1555531 (x : real) (y : real) : (term170 y x) = (term163 x y).
Proof. exact (TRANS (@lem1555529 y x) (@lem1555530 x y)). Qed.
Lemma lem1555532 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555533 (x : real) (y : real) : (term171 y x) = (term213 x y).
Proof. exact (MK_COMB (@lem1555532) (@lem1555531 x y)). Qed.
Lemma lem1555534 (x : real) (y : real) : (term173 y x) = (term214 x y).
Proof. exact (MK_COMB (@lem1555533 x y) (@lem1555518)). Qed.
Lemma lem1555535 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483519 (term163 x y) term52). Qed.
Lemma lem1555537 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555538 : term177 = term52.
Proof. exact (@lem1555537 term35). Qed.
Lemma lem1555539 (x : real) (y : real) : (term216 x y) = (term216 x y).
Proof. exact (eq_refl (term216 x y)). Qed.
Lemma lem1555540 (x : real) (y : real) : (term215 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1555539 x y) (@lem1555538)). Qed.
Lemma lem1555541 (x : real) (y : real) : (term217 x y) = (term163 x y).
Proof. exact (@lem1483450 (term163 x y)). Qed.
Lemma lem1555542 (x : real) (y : real) : (term215 x y) = (term163 x y).
Proof. exact (TRANS (@lem1555540 x y) (@lem1555541 x y)). Qed.
Lemma lem1555543 (x : real) (y : real) : (term214 x y) = (term163 x y).
Proof. exact (TRANS (@lem1555535 x y) (@lem1555542 x y)). Qed.
Lemma lem1555544 (x : real) (y : real) : (term173 y x) = (term163 x y).
Proof. exact (TRANS (@lem1555534 x y) (@lem1555543 x y)). Qed.
Lemma lem1555545 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555546 (x : real) (y : real) : (term180 y x) = (term211 x y).
Proof. exact (MK_COMB (@lem1555545) (@lem1555544 x y)). Qed.
Lemma lem1555547 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555548 (x : real) (y : real) : (term169 y x) = (term212 x y).
Proof. exact (MK_COMB (@lem1555546 x y) (@lem1555547)). Qed.
Lemma lem1555549 (x : real) (y : real) : (term168 y x) = (term212 x y).
Proof. exact (TRANS (@lem1555517 y x) (@lem1555548 x y)). Qed.
Lemma lem1555550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555551 (x : real) : (term218 x) = term219.
Proof. exact (MK_COMB (@lem1555550) (@lem1555516 x)). Qed.
Lemma lem1555552 (x : real) (y : real) : (term138 y x) = (term220 x y).
Proof. exact (MK_COMB (@lem1555551 x) (@lem1555549 x y)). Qed.
Lemma lem1555553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555554 (x : real) (y : real) : (term139 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1555553) (@lem1555473 x y)). Qed.
Lemma lem1555555 (x : real) (y : real) : (term141 y x) = (term222 x y).
Proof. exact (MK_COMB (@lem1555554 x y) (@lem1555552 x y)). Qed.
Lemma lem1555556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555557 (x : real) (y : real) : (term148 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1555556) (@lem1555427 x y)). Qed.
Lemma lem1555558 (x : real) (y : real) : (term149 y x) = (term224 x y).
Proof. exact (MK_COMB (@lem1555557 x y) (@lem1555555 x y)). Qed.
Lemma lem1555569 (x : real) (y : real) : (term133 x y) = (term224 x y).
Proof. exact (TRANS (@lem1555299 y x) (@lem1555558 x y)). Qed.
Lemma lem1555570 (x : real) (y : real) : (term58 x y) = (term224 x y).
Proof. exact (TRANS (@lem1555283 x y) (@lem1555569 x y)). Qed.
Lemma lem1555572 (x : real) (a : real) (y : real) (r : real) : (term225 x y a r) = (term226 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1555573 (x : real) (y : real) : (term54 x y) = (term227 x y).
Proof. exact (@lem1555572 (real_neg x) (term228 x y) (real_neg y) term52). Qed.
Lemma lem1555580 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1555583 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem1555584 (y : real) : (term230 y) = (term159 y).
Proof. exact (MK_COMB (@lem1555583) (@lem1555580 y)). Qed.
Lemma lem1555585 (y : real) : (term159 y) = (term160 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1555587 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1555588 : term33 = term34.
Proof. exact (@lem1555587 term35 term35). Qed.
Lemma lem1555589 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1555590 : term37 = term35.
Proof. exact (EQ_MP (@lem1555589) (@lem940073)). Qed.
Lemma lem1555591 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1555592 : term34 = term38.
Proof. exact (MK_COMB (@lem1555591) (@lem1555590)). Qed.
Lemma lem1555593 : term33 = term38.
Proof. exact (TRANS (@lem1555588) (@lem1555592)). Qed.
Lemma lem1555594 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555595 : term39 = term40.
Proof. exact (MK_COMB (@lem1555594) (@lem1555593)). Qed.
Lemma lem1555596 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1555597 (y : real) : (term160 y) = (term161 y).
Proof. exact (MK_COMB (@lem1555595) (@lem1555596 y)). Qed.
Lemma lem1555598 (y : real) : (term159 y) = (term161 y).
Proof. exact (TRANS (@lem1555585 y) (@lem1555597 y)). Qed.
Lemma lem1555599 (y : real) : (term161 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1555600 (y : real) : (term159 y) = y.
Proof. exact (TRANS (@lem1555598 y) (@lem1555599 y)). Qed.
Lemma lem1555601 (y : real) : (term230 y) = y.
Proof. exact (TRANS (@lem1555584 y) (@lem1555600 y)). Qed.
Lemma lem1555610 (x : real) (y : real) : (term231 x y) = (term231 x y).
Proof. exact (eq_refl (term231 x y)). Qed.
Lemma lem1555611 (x : real) (y : real) : (term232 x y) = (term233 x y).
Proof. exact (MK_COMB (@lem1555610 x y) (@lem1555601 y)). Qed.
Lemma lem1555612 (x : real) (y : real) : (term233 x y) = (term234 x y).
Proof. exact (@lem1483488 y (term228 x y)). Qed.
Lemma lem1555613 (x : real) (y : real) : (term232 x y) = (term234 x y).
Proof. exact (TRANS (@lem1555611 x y) (@lem1555612 x y)). Qed.
Lemma lem1555614 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555615 (x : real) (y : real) : (term235 x y) = (term236 x y).
Proof. exact (MK_COMB (@lem1555614) (@lem1555613 x y)). Qed.
Lemma lem1555616 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555617 (x : real) (y : real) : (term237 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1555615 x y) (@lem1555616)). Qed.
Lemma lem1555624 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1555627 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem1555628 (x : real) : (term230 x) = (term159 x).
Proof. exact (MK_COMB (@lem1555627) (@lem1555624 x)). Qed.
Lemma lem1555629 (x : real) : (term159 x) = (term160 x).
Proof. exact (@lem1483476 term30 term30 x). Qed.
Lemma lem1555631 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1555632 : term33 = term34.
Proof. exact (@lem1555631 term35 term35). Qed.
Lemma lem1555633 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1555634 : term37 = term35.
Proof. exact (EQ_MP (@lem1555633) (@lem940073)). Qed.
Lemma lem1555635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1555636 : term34 = term38.
Proof. exact (MK_COMB (@lem1555635) (@lem1555634)). Qed.
Lemma lem1555637 : term33 = term38.
Proof. exact (TRANS (@lem1555632) (@lem1555636)). Qed.
Lemma lem1555638 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555639 : term39 = term40.
Proof. exact (MK_COMB (@lem1555638) (@lem1555637)). Qed.
Lemma lem1555640 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1555641 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1555639) (@lem1555640 x)). Qed.
Lemma lem1555642 (x : real) : (term159 x) = (term161 x).
Proof. exact (TRANS (@lem1555629 x) (@lem1555641 x)). Qed.
Lemma lem1555643 (x : real) : (term161 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1555644 (x : real) : (term159 x) = x.
Proof. exact (TRANS (@lem1555642 x) (@lem1555643 x)). Qed.
Lemma lem1555645 (x : real) : (term230 x) = x.
Proof. exact (TRANS (@lem1555628 x) (@lem1555644 x)). Qed.
Lemma lem1555654 (x : real) (y : real) : (term231 x y) = (term231 x y).
Proof. exact (eq_refl (term231 x y)). Qed.
Lemma lem1555655 (y : real) (x : real) : (term239 y x) = (term240 y x).
Proof. exact (MK_COMB (@lem1555654 x y) (@lem1555645 x)). Qed.
Lemma lem1555656 (x : real) (y : real) : (term240 y x) = (term241 x y).
Proof. exact (@lem1483488 x (term228 x y)). Qed.
Lemma lem1555657 (x : real) (y : real) : (term239 y x) = (term241 x y).
Proof. exact (TRANS (@lem1555655 y x) (@lem1555656 x y)). Qed.
Lemma lem1555658 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555659 (x : real) (y : real) : (term242 y x) = (term243 x y).
Proof. exact (MK_COMB (@lem1555658) (@lem1555657 x y)). Qed.
Lemma lem1555660 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555661 (x : real) (y : real) : (term244 y x) = (term245 x y).
Proof. exact (MK_COMB (@lem1555659 x y) (@lem1555660)). Qed.
Lemma lem1555662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555663 (x : real) (y : real) : (term246 y x) = (term247 x y).
Proof. exact (MK_COMB (@lem1555662) (@lem1555661 x y)). Qed.
Lemma lem1555664 (x : real) (y : real) : (term227 x y) = (term248 x y).
Proof. exact (MK_COMB (@lem1555663 x y) (@lem1555617 x y)). Qed.
Lemma lem1555665 (x : real) (y : real) : (term54 x y) = (term248 x y).
Proof. exact (TRANS (@lem1555573 x y) (@lem1555664 x y)). Qed.
Lemma lem1555666 (x : real) (y : real) : (term249 x y) = (term248 x y).
Proof. exact (eq_refl (term249 x y)). Qed.
Lemma lem1555667 (x : real) (y : real) : (term248 x y) = (term249 x y).
Proof. exact (SYM (@lem1555666 x y)). Qed.
Lemma lem1555668 (x : real) (y : real) : (term249 x y) = (term250 x y).
Proof. exact (@lem1483429 x (term251 x y) y). Qed.
Lemma lem1555669 (x : real) (y : real) : (term248 x y) = (term250 x y).
Proof. exact (TRANS (@lem1555667 x y) (@lem1555668 x y)). Qed.
Lemma lem1555670 (x : real) (y : real) : (term252 x y) = (term253 x y).
Proof. exact (eq_refl (term252 x y)). Qed.
Lemma lem1555671 (x : real) (y : real) : (term254 x y) = (term254 x y).
Proof. exact (eq_refl (term254 x y)). Qed.
Lemma lem1555672 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1555671 x y) (@lem1555670 x y)). Qed.
Lemma lem1555673 (y : real) (x : real) : (term257 y x) = (term258 y x).
Proof. exact (eq_refl (term257 y x)). Qed.
Lemma lem1555674 (y : real) (x : real) : (term259 y x) = (term259 y x).
Proof. exact (eq_refl (term259 y x)). Qed.
Lemma lem1555675 (y : real) (x : real) : (term260 y x) = (term261 y x).
Proof. exact (MK_COMB (@lem1555674 y x) (@lem1555673 y x)). Qed.
Lemma lem1555676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555677 (y : real) (x : real) : (term262 y x) = (term263 y x).
Proof. exact (MK_COMB (@lem1555676) (@lem1555675 y x)). Qed.
Lemma lem1555678 (x : real) (y : real) : (term250 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem1555677 y x) (@lem1555672 x y)). Qed.
Lemma lem1555679 (x : real) (y : real) : (term265 x y) = (term265 x y).
Proof. exact (eq_refl (term265 x y)). Qed.
Lemma lem1555680 (x : real) (y : real) : ((term248 x y) = (term250 x y)) = ((term248 x y) = (term264 x y)).
Proof. exact (MK_COMB (@lem1555679 x y) (@lem1555678 x y)). Qed.
Lemma lem1555681 (x : real) (y : real) : (term248 x y) = (term264 x y).
Proof. exact (EQ_MP (@lem1555680 x y) (@lem1555669 x y)). Qed.
Lemma lem1555682 (y : real) (x : real) : (real_ge y x) = (term266 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1555688 (y : real) (x : real) : (real_sub y x) = (term164 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1555693 (x : real) (y : real) : (term164 y x) = (term163 x y).
Proof. exact (@lem1483488 (term153 x) y). Qed.
Lemma lem1555695 (x : real) (y : real) : (real_sub y x) = (term163 x y).
Proof. exact (TRANS (@lem1555688 y x) (@lem1555693 x y)). Qed.
Lemma lem1555696 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1555697 (x : real) (y : real) : (term267 y x) = (term268 x y).
Proof. exact (MK_COMB (@lem1555696) (@lem1555695 x y)). Qed.
Lemma lem1555698 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555699 (x : real) (y : real) : (term266 y x) = (term269 x y).
Proof. exact (MK_COMB (@lem1555697 x y) (@lem1555698)). Qed.
Lemma lem1555700 (x : real) (y : real) : (real_ge y x) = (term269 x y).
Proof. exact (TRANS (@lem1555682 y x) (@lem1555699 x y)). Qed.
Lemma lem1555701 (x : real) : (term270 x) = (term271 x).
Proof. exact (@lem1483525 (term186 x) term52). Qed.
Lemma lem1555702 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555714 (x : real) : (term186 x) = (term187 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1555716 (m : nat) : (term188 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1555717 : term189 = term52.
Proof. exact (@lem1555716 term35). Qed.
Lemma lem1555718 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555719 : term190 = term191.
Proof. exact (MK_COMB (@lem1555718) (@lem1555717)). Qed.
Lemma lem1555720 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1555721 (x : real) : (term187 x) = (term192 x).
Proof. exact (MK_COMB (@lem1555719) (@lem1555720 x)). Qed.
Lemma lem1555722 (x : real) : (term186 x) = (term192 x).
Proof. exact (TRANS (@lem1555714 x) (@lem1555721 x)). Qed.
Lemma lem1555723 (x : real) : (term192 x) = term52.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1555725 (x : real) : (term186 x) = term52.
Proof. exact (TRANS (@lem1555722 x) (@lem1555723 x)). Qed.
Lemma lem1555726 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555727 (x : real) : (term272 x) = term194.
Proof. exact (MK_COMB (@lem1555726) (@lem1555725 x)). Qed.
Lemma lem1555728 (x : real) : (term273 x) = term196.
Proof. exact (MK_COMB (@lem1555727 x) (@lem1555702)). Qed.
Lemma lem1555729 : term196 = term197.
Proof. exact (@lem1483519 term52 term52). Qed.
Lemma lem1555731 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555732 : term177 = term52.
Proof. exact (@lem1555731 term35). Qed.
Lemma lem1555733 : term198 = term198.
Proof. exact (eq_refl term198). Qed.
Lemma lem1555734 : term197 = term199.
Proof. exact (MK_COMB (@lem1555733) (@lem1555732)). Qed.
Lemma lem1555735 : term199 = term52.
Proof. exact (@lem1483448 term52). Qed.
Lemma lem1555736 : term197 = term52.
Proof. exact (TRANS (@lem1555734) (@lem1555735)). Qed.
Lemma lem1555737 : term196 = term52.
Proof. exact (TRANS (@lem1555729) (@lem1555736)). Qed.
Lemma lem1555738 (x : real) : (term273 x) = term52.
Proof. exact (TRANS (@lem1555728 x) (@lem1555737)). Qed.
Lemma lem1555739 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555740 (x : real) : (term274 x) = term201.
Proof. exact (MK_COMB (@lem1555739) (@lem1555738 x)). Qed.
Lemma lem1555741 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555742 (x : real) : (term271 x) = term202.
Proof. exact (MK_COMB (@lem1555740 x) (@lem1555741)). Qed.
Lemma lem1555743 (x : real) : (term270 x) = term202.
Proof. exact (TRANS (@lem1555701 x) (@lem1555742 x)). Qed.
Lemma lem1555744 (y : real) (x : real) : (term182 y x) = (term275 y x).
Proof. exact (@lem1483525 (term164 y x) term52). Qed.
Lemma lem1555745 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555758 (x : real) (y : real) : (term164 y x) = (term163 x y).
Proof. exact (@lem1483488 (term153 x) y). Qed.
Lemma lem1555759 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555760 (x : real) (y : real) : (term172 y x) = (term213 x y).
Proof. exact (MK_COMB (@lem1555759) (@lem1555758 x y)). Qed.
Lemma lem1555761 (x : real) (y : real) : (term174 y x) = (term214 x y).
Proof. exact (MK_COMB (@lem1555760 x y) (@lem1555745)). Qed.
Lemma lem1555762 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483519 (term163 x y) term52). Qed.
Lemma lem1555764 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555765 : term177 = term52.
Proof. exact (@lem1555764 term35). Qed.
Lemma lem1555766 (x : real) (y : real) : (term216 x y) = (term216 x y).
Proof. exact (eq_refl (term216 x y)). Qed.
Lemma lem1555767 (x : real) (y : real) : (term215 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1555766 x y) (@lem1555765)). Qed.
Lemma lem1555768 (x : real) (y : real) : (term217 x y) = (term163 x y).
Proof. exact (@lem1483450 (term163 x y)). Qed.
Lemma lem1555769 (x : real) (y : real) : (term215 x y) = (term163 x y).
Proof. exact (TRANS (@lem1555767 x y) (@lem1555768 x y)). Qed.
Lemma lem1555770 (x : real) (y : real) : (term214 x y) = (term163 x y).
Proof. exact (TRANS (@lem1555762 x y) (@lem1555769 x y)). Qed.
Lemma lem1555771 (x : real) (y : real) : (term174 y x) = (term163 x y).
Proof. exact (TRANS (@lem1555761 x y) (@lem1555770 x y)). Qed.
Lemma lem1555772 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555773 (x : real) (y : real) : (term276 y x) = (term211 x y).
Proof. exact (MK_COMB (@lem1555772) (@lem1555771 x y)). Qed.
Lemma lem1555774 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555775 (x : real) (y : real) : (term275 y x) = (term212 x y).
Proof. exact (MK_COMB (@lem1555773 x y) (@lem1555774)). Qed.
Lemma lem1555776 (x : real) (y : real) : (term182 y x) = (term212 x y).
Proof. exact (TRANS (@lem1555744 y x) (@lem1555775 x y)). Qed.
Lemma lem1555777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555778 (x : real) : (term277 x) = term219.
Proof. exact (MK_COMB (@lem1555777) (@lem1555743 x)). Qed.
Lemma lem1555779 (x : real) (y : real) : (term258 y x) = (term220 x y).
Proof. exact (MK_COMB (@lem1555778 x) (@lem1555776 x y)). Qed.
Lemma lem1555780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555781 (x : real) (y : real) : (term259 y x) = (term278 x y).
Proof. exact (MK_COMB (@lem1555780) (@lem1555700 x y)). Qed.
Lemma lem1555782 (x : real) (y : real) : (term261 y x) = (term279 x y).
Proof. exact (MK_COMB (@lem1555781 x y) (@lem1555779 x y)). Qed.
Lemma lem1555783 (x : real) (y : real) : (real_gt x y) = (term280 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1555796 (x : real) (y : real) : (real_sub x y) = (term164 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1555797 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555798 (x : real) (y : real) : (term281 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1555797) (@lem1555796 x y)). Qed.
Lemma lem1555799 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555800 (x : real) (y : real) : (term280 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1555798 x y) (@lem1555799)). Qed.
Lemma lem1555801 (x : real) (y : real) : (real_gt x y) = (term182 x y).
Proof. exact (TRANS (@lem1555783 x y) (@lem1555800 x y)). Qed.
Lemma lem1555802 (x : real) (y : real) : (term182 x y) = (term275 x y).
Proof. exact (@lem1483525 (term164 x y) term52). Qed.
Lemma lem1555820 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483519 (term164 x y) term52). Qed.
Lemma lem1555822 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555823 : term177 = term52.
Proof. exact (@lem1555822 term35). Qed.
Lemma lem1555824 (x : real) (y : real) : (term178 x y) = (term178 x y).
Proof. exact (eq_refl (term178 x y)). Qed.
Lemma lem1555825 (x : real) (y : real) : (term175 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1555824 x y) (@lem1555823)). Qed.
Lemma lem1555826 (x : real) (y : real) : (term179 x y) = (term164 x y).
Proof. exact (@lem1483450 (term164 x y)). Qed.
Lemma lem1555827 (x : real) (y : real) : (term175 x y) = (term164 x y).
Proof. exact (TRANS (@lem1555825 x y) (@lem1555826 x y)). Qed.
Lemma lem1555829 (x : real) (y : real) : (term174 x y) = (term164 x y).
Proof. exact (TRANS (@lem1555820 x y) (@lem1555827 x y)). Qed.
Lemma lem1555830 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555831 (x : real) (y : real) : (term276 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1555830) (@lem1555829 x y)). Qed.
Lemma lem1555832 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555833 (x : real) (y : real) : (term275 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1555831 x y) (@lem1555832)). Qed.
Lemma lem1555834 (x : real) (y : real) : (term182 x y) = (term182 x y).
Proof. exact (TRANS (@lem1555802 x y) (@lem1555833 x y)). Qed.
Lemma lem1555835 (y : real) : (term270 y) = (term271 y).
Proof. exact (@lem1483525 (term186 y) term52). Qed.
Lemma lem1555836 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555848 (y : real) : (term186 y) = (term187 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1555850 (m : nat) : (term188 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1555851 : term189 = term52.
Proof. exact (@lem1555850 term35). Qed.
Lemma lem1555852 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1555853 : term190 = term191.
Proof. exact (MK_COMB (@lem1555852) (@lem1555851)). Qed.
Lemma lem1555854 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1555855 (y : real) : (term187 y) = (term192 y).
Proof. exact (MK_COMB (@lem1555853) (@lem1555854 y)). Qed.
Lemma lem1555856 (y : real) : (term186 y) = (term192 y).
Proof. exact (TRANS (@lem1555848 y) (@lem1555855 y)). Qed.
Lemma lem1555857 (y : real) : (term192 y) = term52.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1555859 (y : real) : (term186 y) = term52.
Proof. exact (TRANS (@lem1555856 y) (@lem1555857 y)). Qed.
Lemma lem1555860 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1555861 (y : real) : (term272 y) = term194.
Proof. exact (MK_COMB (@lem1555860) (@lem1555859 y)). Qed.
Lemma lem1555862 (y : real) : (term273 y) = term196.
Proof. exact (MK_COMB (@lem1555861 y) (@lem1555836)). Qed.
Lemma lem1555863 : term196 = term197.
Proof. exact (@lem1483519 term52 term52). Qed.
Lemma lem1555865 (x : nat) : (term176 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1555866 : term177 = term52.
Proof. exact (@lem1555865 term35). Qed.
Lemma lem1555867 : term198 = term198.
Proof. exact (eq_refl term198). Qed.
Lemma lem1555868 : term197 = term199.
Proof. exact (MK_COMB (@lem1555867) (@lem1555866)). Qed.
Lemma lem1555869 : term199 = term52.
Proof. exact (@lem1483448 term52). Qed.
Lemma lem1555870 : term197 = term52.
Proof. exact (TRANS (@lem1555868) (@lem1555869)). Qed.
Lemma lem1555871 : term196 = term52.
Proof. exact (TRANS (@lem1555863) (@lem1555870)). Qed.
Lemma lem1555872 (y : real) : (term273 y) = term52.
Proof. exact (TRANS (@lem1555862 y) (@lem1555871)). Qed.
Lemma lem1555873 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1555874 (y : real) : (term274 y) = term201.
Proof. exact (MK_COMB (@lem1555873) (@lem1555872 y)). Qed.
Lemma lem1555875 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1555876 (y : real) : (term271 y) = term202.
Proof. exact (MK_COMB (@lem1555874 y) (@lem1555875)). Qed.
Lemma lem1555877 (y : real) : (term270 y) = term202.
Proof. exact (TRANS (@lem1555835 y) (@lem1555876 y)). Qed.
Lemma lem1555878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555879 (x : real) (y : real) : (term204 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1555878) (@lem1555834 x y)). Qed.
Lemma lem1555880 (x : real) (y : real) : (term253 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1555879 x y) (@lem1555877 y)). Qed.
Lemma lem1555881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1555882 (x : real) (y : real) : (term254 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1555881) (@lem1555801 x y)). Qed.
Lemma lem1555883 (x : real) (y : real) : (term256 x y) = (term282 x y).
Proof. exact (MK_COMB (@lem1555882 x y) (@lem1555880 x y)). Qed.
Lemma lem1555884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555885 (x : real) (y : real) : (term263 y x) = (term283 x y).
Proof. exact (MK_COMB (@lem1555884) (@lem1555782 x y)). Qed.
Lemma lem1555886 (x : real) (y : real) : (term264 x y) = (term284 x y).
Proof. exact (MK_COMB (@lem1555885 x y) (@lem1555883 x y)). Qed.
Lemma lem1555897 (x : real) (y : real) : (term248 x y) = (term284 x y).
Proof. exact (TRANS (@lem1555681 x y) (@lem1555886 x y)). Qed.
Lemma lem1555898 (x : real) (y : real) : (term54 x y) = (term284 x y).
Proof. exact (TRANS (@lem1555665 x y) (@lem1555897 x y)). Qed.
Lemma lem1555899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1555900 (x : real) (y : real) : (term60 x y) = (term285 x y).
Proof. exact (MK_COMB (@lem1555899) (@lem1555570 x y)). Qed.
Lemma lem1555901 (x : real) (y : real) : (term61 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1555900 x y) (@lem1555898 x y)). Qed.
Lemma lem1555902 (x : real) (y : real) (h1 : term286 x y) : term286 x y.
Proof. exact (h1). Qed.
Lemma lem1555903 (x : real) (y : real) (h1 : term224 x y) : term224 x y.
Proof. exact (h1). Qed.
Lemma lem1555904 (x : real) (y : real) (h1 : term207 x y) : term207 x y.
Proof. exact (h1). Qed.
Lemma lem1555905 (x : real) (y : real) (h1 : term207 x y) : term205 x y.
Proof. exact (proj2 (@lem1555904 x y h1)). Qed.
Lemma lem1555907 (x : real) (y : real) (h1 : term207 x y) : term202.
Proof. exact (proj2 (@lem1555905 x y h1)). Qed.
Lemma lem1555910 (n : nat) (m : nat) : (term287 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1555911 : term202 = term288.
Proof. exact (@lem1555910 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1555912 : term288 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1555913 : term202 = False.
Proof. exact (TRANS (@lem1555911) (@lem1555912)). Qed.
Lemma lem1555914 (x : real) (y : real) (h1 : term207 x y) : False.
Proof. exact (EQ_MP (@lem1555913) (@lem1555907 x y h1)). Qed.
Lemma lem1555915 (x : real) (y : real) (h1 : term222 x y) : term222 x y.
Proof. exact (h1). Qed.
Lemma lem1555916 (x : real) (y : real) (h1 : term222 x y) : term220 x y.
Proof. exact (proj2 (@lem1555915 x y h1)). Qed.
Lemma lem1555919 (x : real) (y : real) (h1 : term222 x y) : term202.
Proof. exact (proj1 (@lem1555916 x y h1)). Qed.
Lemma lem1555921 (n : nat) (m : nat) : (term287 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1555922 : term202 = term288.
Proof. exact (@lem1555921 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1555923 : term288 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1555924 : term202 = False.
Proof. exact (TRANS (@lem1555922) (@lem1555923)). Qed.
Lemma lem1555925 (x : real) (y : real) (h1 : term222 x y) : False.
Proof. exact (EQ_MP (@lem1555924) (@lem1555919 x y h1)). Qed.
Lemma lem1555926 (x : real) (y : real) (h1 : term224 x y) : False.
Proof. exact (or_elim (@lem1555903 x y h1) (fun h0 : term207 x y => @lem1555914 x y h0) (fun h0 : term222 x y => @lem1555925 x y h0)). Qed.
Lemma lem1555927 (x : real) (y : real) (h1 : term284 x y) : term284 x y.
Proof. exact (h1). Qed.
Lemma lem1555928 (x : real) (y : real) (h1 : term279 x y) : term279 x y.
Proof. exact (h1). Qed.
Lemma lem1555929 (x : real) (y : real) (h1 : term279 x y) : term220 x y.
Proof. exact (proj2 (@lem1555928 x y h1)). Qed.
Lemma lem1555932 (x : real) (y : real) (h1 : term279 x y) : term202.
Proof. exact (proj1 (@lem1555929 x y h1)). Qed.
Lemma lem1555934 (n : nat) (m : nat) : (term287 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1555935 : term202 = term288.
Proof. exact (@lem1555934 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1555936 : term288 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1555937 : term202 = False.
Proof. exact (TRANS (@lem1555935) (@lem1555936)). Qed.
Lemma lem1555938 (x : real) (y : real) (h1 : term279 x y) : False.
Proof. exact (EQ_MP (@lem1555937) (@lem1555932 x y h1)). Qed.
Lemma lem1555939 (x : real) (y : real) (h1 : term282 x y) : term282 x y.
Proof. exact (h1). Qed.
Lemma lem1555940 (x : real) (y : real) (h1 : term282 x y) : term205 x y.
Proof. exact (proj2 (@lem1555939 x y h1)). Qed.
Lemma lem1555942 (x : real) (y : real) (h1 : term282 x y) : term202.
Proof. exact (proj2 (@lem1555940 x y h1)). Qed.
Lemma lem1555945 (n : nat) (m : nat) : (term287 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1555946 : term202 = term288.
Proof. exact (@lem1555945 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1555947 : term288 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1555948 : term202 = False.
Proof. exact (TRANS (@lem1555946) (@lem1555947)). Qed.
Lemma lem1555949 (x : real) (y : real) (h1 : term282 x y) : False.
Proof. exact (EQ_MP (@lem1555948) (@lem1555942 x y h1)). Qed.
Lemma lem1555950 (x : real) (y : real) (h1 : term284 x y) : False.
Proof. exact (or_elim (@lem1555927 x y h1) (fun h0 : term279 x y => @lem1555938 x y h0) (fun h0 : term282 x y => @lem1555949 x y h0)). Qed.
Lemma lem1555951 (x : real) (y : real) (h1 : term286 x y) : False.
Proof. exact (or_elim (@lem1555902 x y h1) (fun h0 : term224 x y => @lem1555926 x y h0) (fun h0 : term284 x y => @lem1555950 x y h0)). Qed.
Lemma lem1555952 (x : real) (y : real) (h1 : term61 x y) : term61 x y.
Proof. exact (h1). Qed.
Lemma lem1555953 (x : real) (y : real) (h1 : term61 x y) : term286 x y.
Proof. exact (EQ_MP (@lem1555901 x y) (@lem1555952 x y h1)). Qed.
Lemma lem1555954 (x : real) (y : real) (h1 : term61 x y) : (term286 x y) = False.
Proof. exact (prop_ext (fun h2 : term286 x y => @lem1555951 x y h2) (fun h2 : False => @lem1555953 x y h1)). Qed.
Lemma lem1555955 (x : real) (y : real) (h1 : term61 x y) : False.
Proof. exact (EQ_MP (@lem1555954 x y h1) (@lem1555953 x y h1)). Qed.
Lemma lem1555956 (x : real) (h1 : term63 x) : term63 x.
Proof. exact (h1). Qed.
Lemma lem1555957 (x : real) (h1 : term63 x) : False.
Proof. exact (ex_elim (@lem1555956 x h1) (fun y : real => fun h0 : term62 x y => @lem1555955 x y h0)). Qed.
Lemma lem1555958 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem1555959 (h1 : term65) : False.
Proof. exact (ex_elim (@lem1555958 h1) (fun x : real => fun h0 : term64 x => @lem1555957 x h0)). Qed.
Lemma lem1555960 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1555961 (h1 : term12) : term65.
Proof. exact (EQ_MP (@lem1555254) (@lem1555960 h1)). Qed.
Lemma lem1555962 (h1 : term12) : term65 = False.
Proof. exact (prop_ext (fun h2 : term65 => @lem1555959 h2) (fun h2 : False => @lem1555961 h1)). Qed.
Lemma lem1555963 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1555962 h1) (@lem1555961 h1)). Qed.
Lemma lem1555964 : term289.
Proof. exact (fun h0 : term12 => @lem1555963 h0). Qed.
Lemma lem1555965 : term290.
Proof. exact (@lem1386578 term291). Qed.
Lemma lem1555966 : term291.
Proof. exact (@lem1555965 (@lem1555964)). Qed.
