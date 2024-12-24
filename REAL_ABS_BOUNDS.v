Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_BOUNDS_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482680_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1551010 (x : real) (k : real) : (term0 x k) = (term1 x k).
Proof. exact (@lem17045 (term2 k x) (real_le x k)). Qed.
Lemma lem1551016 (x : real) (k : real) : (term3 x k) = (term3 x k).
Proof. exact (eq_refl (term3 x k)). Qed.
Lemma lem1551018 (x : real) (k : real) : (term4 x k) = (term4 x k).
Proof. exact (eq_refl (term4 x k)). Qed.
Lemma lem1551019 (x : real) (k : real) : (term5 x k) = (term6 x k).
Proof. exact (MK_COMB (@lem1551018 x k) (@lem1551010 x k)). Qed.
Lemma lem1551020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551021 (x : real) (k : real) : (term7 x k) = (term8 x k).
Proof. exact (MK_COMB (@lem1551020) (@lem1551019 x k)). Qed.
Lemma lem1551022 (x : real) (k : real) : (term9 x k) = (term10 x k).
Proof. exact (MK_COMB (@lem1551021 x k) (@lem1551016 x k)). Qed.
Lemma lem1551023 (x : real) (k : real) : (term11 x k) = (term9 x k).
Proof. exact (@lem17646 (term12 x k) (term13 x k)). Qed.
Lemma lem1551024 (x : real) (k : real) : (term11 x k) = (term10 x k).
Proof. exact (TRANS (@lem1551023 x k) (@lem1551022 x k)). Qed.
Lemma lem1551025 (P : real -> Prop) : (term14 P) = (term15 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1551026 (x : real) : (term16 x) = (term17 x).
Proof. exact (@lem1551025 (term18 x)). Qed.
Lemma lem1551027 (x : real) (k : real) : (term19 x k) = ((term12 x k) = (term13 x k)).
Proof. exact (eq_refl (term19 x k)). Qed.
Lemma lem1551028 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1551029 (x : real) (k : real) : (term20 x k) = (term11 x k).
Proof. exact (MK_COMB (@lem1551028) (@lem1551027 x k)). Qed.
Lemma lem1551030 (x : real) (k : real) : (term20 x k) = (term10 x k).
Proof. exact (TRANS (@lem1551029 x k) (@lem1551024 x k)). Qed.
Lemma lem1551031 (x : real) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun k : real => @lem1551030 x k)). Qed.
Lemma lem1551032 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551033 (x : real) : (term17 x) = (term23 x).
Proof. exact (MK_COMB (@lem1551032) (@lem1551031 x)). Qed.
Lemma lem1551034 (x : real) : (term16 x) = (term23 x).
Proof. exact (TRANS (@lem1551026 x) (@lem1551033 x)). Qed.
Lemma lem1551035 (P : real -> Prop) : (term14 P) = (term15 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1551036 : term24 = term25.
Proof. exact (@lem1551035 term26). Qed.
Lemma lem1551037 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1551038 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1551039 (x : real) : (term29 x) = (term16 x).
Proof. exact (MK_COMB (@lem1551038) (@lem1551037 x)). Qed.
Lemma lem1551040 (x : real) : (term29 x) = (term23 x).
Proof. exact (TRANS (@lem1551039 x) (@lem1551034 x)). Qed.
Lemma lem1551041 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1551040 x)). Qed.
Lemma lem1551042 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551043 : term25 = term32.
Proof. exact (MK_COMB (@lem1551042) (@lem1551041)). Qed.
Lemma lem1551045 : term24 = term32.
Proof. exact (TRANS (@lem1551036) (@lem1551043)). Qed.
Lemma lem1551072 (x : real) (k : real) : (term10 x k) = (term10 x k).
Proof. exact (eq_refl (term10 x k)). Qed.
Lemma lem1551073 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun k : real => @lem1551072 x k)). Qed.
Lemma lem1551074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551075 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1551074) (@lem1551073 x)). Qed.
Lemma lem1551076 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1551075 x)). Qed.
Lemma lem1551077 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551078 : term32 = term32.
Proof. exact (MK_COMB (@lem1551077) (@lem1551076)). Qed.
Lemma lem1551079 : term24 = term32.
Proof. exact (TRANS (@lem1551045) (@lem1551078)). Qed.
Lemma lem1551080 (k : real) (x : real) : (term12 x k) = (term33 k x).
Proof. exact (@lem1483523 k (real_abs x)). Qed.
Lemma lem1551093 (k : real) (x : real) : (term34 k x) = (term35 k x).
Proof. exact (@lem1483519 k (real_abs x)). Qed.
Lemma lem1551094 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551095 (k : real) (x : real) : (term36 k x) = (term37 k x).
Proof. exact (MK_COMB (@lem1551094) (@lem1551093 k x)). Qed.
Lemma lem1551096 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551097 (k : real) (x : real) : (term33 k x) = (term39 k x).
Proof. exact (MK_COMB (@lem1551095 k x) (@lem1551096)). Qed.
Lemma lem1551098 (k : real) (x : real) : (term12 x k) = (term39 k x).
Proof. exact (TRANS (@lem1551080 k x) (@lem1551097 k x)). Qed.
Lemma lem1551099 (k : real) (x : real) : (term40 k x) = (term41 k x).
Proof. exact (@lem1483533 (real_neg k) x). Qed.
Lemma lem1551100 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1551107 (k : real) : (real_neg k) = (term42 k).
Proof. exact (@lem1483512 k). Qed.
Lemma lem1551108 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1551109 (k : real) : (term43 k) = (term44 k).
Proof. exact (MK_COMB (@lem1551108) (@lem1551107 k)). Qed.
Lemma lem1551110 (k : real) (x : real) : (term45 k x) = (term46 k x).
Proof. exact (MK_COMB (@lem1551109 k) (@lem1551100 x)). Qed.
Lemma lem1551117 (k : real) (x : real) : (term46 k x) = (term47 k x).
Proof. exact (@lem1483519 (term42 k) x). Qed.
Lemma lem1551118 (k : real) (x : real) : (term45 k x) = (term47 k x).
Proof. exact (TRANS (@lem1551110 k x) (@lem1551117 k x)). Qed.
Lemma lem1551119 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1551120 (k : real) (x : real) : (term48 k x) = (term49 k x).
Proof. exact (MK_COMB (@lem1551119) (@lem1551118 k x)). Qed.
Lemma lem1551121 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551122 (k : real) (x : real) : (term41 k x) = (term50 k x).
Proof. exact (MK_COMB (@lem1551120 k x) (@lem1551121)). Qed.
Lemma lem1551123 (k : real) (x : real) : (term40 k x) = (term50 k x).
Proof. exact (TRANS (@lem1551099 k x) (@lem1551122 k x)). Qed.
Lemma lem1551124 (x : real) (k : real) : (term51 x k) = (term52 x k).
Proof. exact (@lem1483533 x k). Qed.
Lemma lem1551130 (x : real) (k : real) : (real_sub x k) = (term53 x k).
Proof. exact (@lem1483519 x k). Qed.
Lemma lem1551135 (k : real) (x : real) : (term53 x k) = (term54 k x).
Proof. exact (@lem1483488 (term42 k) x). Qed.
Lemma lem1551137 (k : real) (x : real) : (real_sub x k) = (term54 k x).
Proof. exact (TRANS (@lem1551130 x k) (@lem1551135 k x)). Qed.
Lemma lem1551138 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1551139 (k : real) (x : real) : (term55 x k) = (term56 k x).
Proof. exact (MK_COMB (@lem1551138) (@lem1551137 k x)). Qed.
Lemma lem1551140 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551141 (k : real) (x : real) : (term52 x k) = (term57 k x).
Proof. exact (MK_COMB (@lem1551139 k x) (@lem1551140)). Qed.
Lemma lem1551142 (k : real) (x : real) : (term51 x k) = (term57 k x).
Proof. exact (TRANS (@lem1551124 x k) (@lem1551141 k x)). Qed.
Lemma lem1551143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551144 (k : real) (x : real) : (term58 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1551143) (@lem1551123 k x)). Qed.
Lemma lem1551145 (k : real) (x : real) : (term1 x k) = (term60 k x).
Proof. exact (MK_COMB (@lem1551144 k x) (@lem1551142 k x)). Qed.
Lemma lem1551146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551147 (k : real) (x : real) : (term4 x k) = (term61 k x).
Proof. exact (MK_COMB (@lem1551146) (@lem1551098 k x)). Qed.
Lemma lem1551148 (k : real) (x : real) : (term6 x k) = (term62 k x).
Proof. exact (MK_COMB (@lem1551147 k x) (@lem1551145 k x)). Qed.
Lemma lem1551149 (x : real) (k : real) : (term63 x k) = (term64 x k).
Proof. exact (@lem1483533 (real_abs x) k). Qed.
Lemma lem1551155 (x : real) (k : real) : (term65 x k) = (term66 x k).
Proof. exact (@lem1483519 (real_abs x) k). Qed.
Lemma lem1551160 (k : real) (x : real) : (term66 x k) = (term67 k x).
Proof. exact (@lem1483488 (term42 k) (real_abs x)). Qed.
Lemma lem1551162 (k : real) (x : real) : (term65 x k) = (term67 k x).
Proof. exact (TRANS (@lem1551155 x k) (@lem1551160 k x)). Qed.
Lemma lem1551163 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1551164 (k : real) (x : real) : (term68 x k) = (term69 k x).
Proof. exact (MK_COMB (@lem1551163) (@lem1551162 k x)). Qed.
Lemma lem1551165 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551166 (k : real) (x : real) : (term64 x k) = (term70 k x).
Proof. exact (MK_COMB (@lem1551164 k x) (@lem1551165)). Qed.
Lemma lem1551167 (k : real) (x : real) : (term63 x k) = (term70 k x).
Proof. exact (TRANS (@lem1551149 x k) (@lem1551166 k x)). Qed.
Lemma lem1551168 (x : real) (k : real) : (term2 k x) = (term71 x k).
Proof. exact (@lem1483523 x (real_neg k)). Qed.
Lemma lem1551175 (k : real) : (real_neg k) = (term42 k).
Proof. exact (@lem1483512 k). Qed.
Lemma lem1551178 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1551179 (x : real) (k : real) : (term72 x k) = (term73 x k).
Proof. exact (MK_COMB (@lem1551178 x) (@lem1551175 k)). Qed.
Lemma lem1551180 (x : real) (k : real) : (term73 x k) = (term74 x k).
Proof. exact (@lem1483519 x (term42 k)). Qed.
Lemma lem1551181 (k : real) : (term75 k) = (term76 k).
Proof. exact (@lem1483476 term77 term77 k). Qed.
Lemma lem1551183 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1551184 : term80 = term81.
Proof. exact (@lem1551183 term82 term82). Qed.
Lemma lem1551185 : (term83 = (BIT1 0)) = (term84 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1551186 : term84 = term82.
Proof. exact (EQ_MP (@lem1551185) (@lem940073)). Qed.
Lemma lem1551187 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1551188 : term81 = term85.
Proof. exact (MK_COMB (@lem1551187) (@lem1551186)). Qed.
Lemma lem1551189 : term80 = term85.
Proof. exact (TRANS (@lem1551184) (@lem1551188)). Qed.
Lemma lem1551190 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1551191 : term86 = term87.
Proof. exact (MK_COMB (@lem1551190) (@lem1551189)). Qed.
Lemma lem1551192 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1551193 (k : real) : (term76 k) = (term88 k).
Proof. exact (MK_COMB (@lem1551191) (@lem1551192 k)). Qed.
Lemma lem1551194 (k : real) : (term75 k) = (term88 k).
Proof. exact (TRANS (@lem1551181 k) (@lem1551193 k)). Qed.
Lemma lem1551195 (k : real) : (term88 k) = k.
Proof. exact (@lem1483436 k). Qed.
Lemma lem1551196 (k : real) : (term75 k) = k.
Proof. exact (TRANS (@lem1551194 k) (@lem1551195 k)). Qed.
Lemma lem1551197 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1551198 (x : real) (k : real) : (term74 x k) = (real_add x k).
Proof. exact (MK_COMB (@lem1551197 x) (@lem1551196 k)). Qed.
Lemma lem1551199 (k : real) (x : real) : (real_add x k) = (real_add k x).
Proof. exact (@lem1483488 k x). Qed.
Lemma lem1551200 (k : real) (x : real) : (term74 x k) = (real_add k x).
Proof. exact (TRANS (@lem1551198 x k) (@lem1551199 k x)). Qed.
Lemma lem1551201 (k : real) (x : real) : (term73 x k) = (real_add k x).
Proof. exact (TRANS (@lem1551180 x k) (@lem1551200 k x)). Qed.
Lemma lem1551202 (k : real) (x : real) : (term72 x k) = (real_add k x).
Proof. exact (TRANS (@lem1551179 x k) (@lem1551201 k x)). Qed.
Lemma lem1551203 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551204 (k : real) (x : real) : (term89 x k) = (term90 k x).
Proof. exact (MK_COMB (@lem1551203) (@lem1551202 k x)). Qed.
Lemma lem1551205 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551206 (k : real) (x : real) : (term71 x k) = (term91 k x).
Proof. exact (MK_COMB (@lem1551204 k x) (@lem1551205)). Qed.
Lemma lem1551207 (k : real) (x : real) : (term2 k x) = (term91 k x).
Proof. exact (TRANS (@lem1551168 x k) (@lem1551206 k x)). Qed.
Lemma lem1551208 (k : real) (x : real) : (real_le x k) = (term92 k x).
Proof. exact (@lem1483523 k x). Qed.
Lemma lem1551221 (k : real) (x : real) : (real_sub k x) = (term53 k x).
Proof. exact (@lem1483519 k x). Qed.
Lemma lem1551222 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551223 (k : real) (x : real) : (term93 k x) = (term94 k x).
Proof. exact (MK_COMB (@lem1551222) (@lem1551221 k x)). Qed.
Lemma lem1551224 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551225 (k : real) (x : real) : (term92 k x) = (term95 k x).
Proof. exact (MK_COMB (@lem1551223 k x) (@lem1551224)). Qed.
Lemma lem1551226 (k : real) (x : real) : (real_le x k) = (term95 k x).
Proof. exact (TRANS (@lem1551208 k x) (@lem1551225 k x)). Qed.
Lemma lem1551227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551228 (k : real) (x : real) : (term96 k x) = (term97 k x).
Proof. exact (MK_COMB (@lem1551227) (@lem1551207 k x)). Qed.
Lemma lem1551229 (k : real) (x : real) : (term13 x k) = (term98 k x).
Proof. exact (MK_COMB (@lem1551228 k x) (@lem1551226 k x)). Qed.
Lemma lem1551230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551231 (k : real) (x : real) : (term99 x k) = (term100 k x).
Proof. exact (MK_COMB (@lem1551230) (@lem1551167 k x)). Qed.
Lemma lem1551232 (k : real) (x : real) : (term3 x k) = (term101 k x).
Proof. exact (MK_COMB (@lem1551231 k x) (@lem1551229 k x)). Qed.
Lemma lem1551233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551234 (k : real) (x : real) : (term8 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1551233) (@lem1551148 k x)). Qed.
Lemma lem1551235 (k : real) (x : real) : (term10 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1551234 k x) (@lem1551232 k x)). Qed.
Lemma lem1551236 (x : real) : (term22 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1551235 k x)). Qed.
Lemma lem1551237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551238 (x : real) : (term23 x) = (term105 x).
Proof. exact (MK_COMB (@lem1551237) (@lem1551236 x)). Qed.
Lemma lem1551239 : term31 = term106.
Proof. exact (fun_ext (fun x : real => @lem1551238 x)). Qed.
Lemma lem1551240 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551241 : term32 = term107.
Proof. exact (MK_COMB (@lem1551240) (@lem1551239)). Qed.
Lemma lem1551242 : term24 = term107.
Proof. exact (TRANS (@lem1551079) (@lem1551241)). Qed.
Lemma lem1551248 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1551249 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem1551248 real P Q). Qed.
Lemma lem1551250 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem1551249 (term114 x) (term115 x)). Qed.
Lemma lem1551251 (k : real) (x : real) : (term116 x k) = (term62 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1551252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551253 (k : real) (x : real) : (term117 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1551252) (@lem1551251 k x)). Qed.
Lemma lem1551254 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1551255 (k : real) (x : real) : (term119 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1551253 k x) (@lem1551254 k x)). Qed.
Lemma lem1551256 (x : real) : (term120 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1551255 k x)). Qed.
Lemma lem1551257 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551258 (x : real) : (term112 x) = (term105 x).
Proof. exact (MK_COMB (@lem1551257) (@lem1551256 x)). Qed.
Lemma lem1551259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1551260 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1551259) (@lem1551258 x)). Qed.
Lemma lem1551261 (k : real) (x : real) : (term116 x k) = (term62 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1551262 (x : real) : (term123 x) = (term114 x).
Proof. exact (fun_ext (fun k : real => @lem1551261 k x)). Qed.
Lemma lem1551263 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551264 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1551263) (@lem1551262 x)). Qed.
Lemma lem1551265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551266 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1551265) (@lem1551264 x)). Qed.
Lemma lem1551267 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1551268 (x : real) : (term128 x) = (term115 x).
Proof. exact (fun_ext (fun k : real => @lem1551267 k x)). Qed.
Lemma lem1551269 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551270 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1551269) (@lem1551268 x)). Qed.
Lemma lem1551271 (x : real) : (term113 x) = (term131 x).
Proof. exact (MK_COMB (@lem1551266 x) (@lem1551270 x)). Qed.
Lemma lem1551272 (x : real) : ((term112 x) = (term113 x)) = ((term105 x) = (term131 x)).
Proof. exact (MK_COMB (@lem1551260 x) (@lem1551271 x)). Qed.
Lemma lem1551273 (x : real) : (term105 x) = (term131 x).
Proof. exact (EQ_MP (@lem1551272 x) (@lem1551250 x)). Qed.
Lemma lem1551370 : term106 = term132.
Proof. exact (fun_ext (fun x : real => @lem1551273 x)). Qed.
Lemma lem1551371 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551372 : term107 = term133.
Proof. exact (MK_COMB (@lem1551371) (@lem1551370)). Qed.
Lemma lem1551374 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1551375 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem1551374 real P Q). Qed.
Lemma lem1551376 : term134 = term135.
Proof. exact (@lem1551375 term136 term137). Qed.
Lemma lem1551377 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1551378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551379 (x : real) : (term139 x) = (term127 x).
Proof. exact (MK_COMB (@lem1551378) (@lem1551377 x)). Qed.
Lemma lem1551380 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1551381 (x : real) : (term141 x) = (term131 x).
Proof. exact (MK_COMB (@lem1551379 x) (@lem1551380 x)). Qed.
Lemma lem1551382 : term142 = term132.
Proof. exact (fun_ext (fun x : real => @lem1551381 x)). Qed.
Lemma lem1551383 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551384 : term134 = term133.
Proof. exact (MK_COMB (@lem1551383) (@lem1551382)). Qed.
Lemma lem1551385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1551386 : term143 = term144.
Proof. exact (MK_COMB (@lem1551385) (@lem1551384)). Qed.
Lemma lem1551387 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1551388 : term145 = term136.
Proof. exact (fun_ext (fun x : real => @lem1551387 x)). Qed.
Lemma lem1551389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551390 : term146 = term147.
Proof. exact (MK_COMB (@lem1551389) (@lem1551388)). Qed.
Lemma lem1551391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551392 : term148 = term149.
Proof. exact (MK_COMB (@lem1551391) (@lem1551390)). Qed.
Lemma lem1551393 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1551394 : term150 = term137.
Proof. exact (fun_ext (fun x : real => @lem1551393 x)). Qed.
Lemma lem1551395 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551396 : term151 = term152.
Proof. exact (MK_COMB (@lem1551395) (@lem1551394)). Qed.
Lemma lem1551397 : term135 = term153.
Proof. exact (MK_COMB (@lem1551392) (@lem1551396)). Qed.
Lemma lem1551398 : (term134 = term135) = (term133 = term153).
Proof. exact (MK_COMB (@lem1551386) (@lem1551397)). Qed.
Lemma lem1551399 : term133 = term153.
Proof. exact (EQ_MP (@lem1551398) (@lem1551376)). Qed.
Lemma lem1551504 : term107 = term153.
Proof. exact (TRANS (@lem1551372) (@lem1551399)). Qed.
Lemma lem1551506 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1551507 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem1551506 real P Q). Qed.
Lemma lem1551508 : term135 = term134.
Proof. exact (@lem1551507 term136 term137). Qed.
Lemma lem1551509 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1551510 : term145 = term136.
Proof. exact (fun_ext (fun x : real => @lem1551509 x)). Qed.
Lemma lem1551511 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551512 : term146 = term147.
Proof. exact (MK_COMB (@lem1551511) (@lem1551510)). Qed.
Lemma lem1551513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551514 : term148 = term149.
Proof. exact (MK_COMB (@lem1551513) (@lem1551512)). Qed.
Lemma lem1551515 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1551516 : term150 = term137.
Proof. exact (fun_ext (fun x : real => @lem1551515 x)). Qed.
Lemma lem1551517 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551518 : term151 = term152.
Proof. exact (MK_COMB (@lem1551517) (@lem1551516)). Qed.
Lemma lem1551519 : term135 = term153.
Proof. exact (MK_COMB (@lem1551514) (@lem1551518)). Qed.
Lemma lem1551520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1551521 : term154 = term155.
Proof. exact (MK_COMB (@lem1551520) (@lem1551519)). Qed.
Lemma lem1551522 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1551523 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551524 (x : real) : (term139 x) = (term127 x).
Proof. exact (MK_COMB (@lem1551523) (@lem1551522 x)). Qed.
Lemma lem1551525 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1551526 (x : real) : (term141 x) = (term131 x).
Proof. exact (MK_COMB (@lem1551524 x) (@lem1551525 x)). Qed.
Lemma lem1551527 : term142 = term132.
Proof. exact (fun_ext (fun x : real => @lem1551526 x)). Qed.
Lemma lem1551528 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551529 : term134 = term133.
Proof. exact (MK_COMB (@lem1551528) (@lem1551527)). Qed.
Lemma lem1551530 : (term135 = term134) = (term153 = term133).
Proof. exact (MK_COMB (@lem1551521) (@lem1551529)). Qed.
Lemma lem1551531 : term153 = term133.
Proof. exact (EQ_MP (@lem1551530) (@lem1551508)). Qed.
Lemma lem1551533 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1551534 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem1551533 real P Q). Qed.
Lemma lem1551535 (x : real) : (term113 x) = (term112 x).
Proof. exact (@lem1551534 (term114 x) (term115 x)). Qed.
Lemma lem1551536 (k : real) (x : real) : (term116 x k) = (term62 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1551537 (x : real) : (term123 x) = (term114 x).
Proof. exact (fun_ext (fun k : real => @lem1551536 k x)). Qed.
Lemma lem1551538 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551539 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1551538) (@lem1551537 x)). Qed.
Lemma lem1551540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551541 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1551540) (@lem1551539 x)). Qed.
Lemma lem1551542 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1551543 (x : real) : (term128 x) = (term115 x).
Proof. exact (fun_ext (fun k : real => @lem1551542 k x)). Qed.
Lemma lem1551544 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551545 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1551544) (@lem1551543 x)). Qed.
Lemma lem1551546 (x : real) : (term113 x) = (term131 x).
Proof. exact (MK_COMB (@lem1551541 x) (@lem1551545 x)). Qed.
Lemma lem1551547 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1551548 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1551547) (@lem1551546 x)). Qed.
Lemma lem1551549 (k : real) (x : real) : (term116 x k) = (term62 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1551550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551551 (k : real) (x : real) : (term117 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1551550) (@lem1551549 k x)). Qed.
Lemma lem1551552 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1551553 (k : real) (x : real) : (term119 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1551551 k x) (@lem1551552 k x)). Qed.
Lemma lem1551554 (x : real) : (term120 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1551553 k x)). Qed.
Lemma lem1551555 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551556 (x : real) : (term112 x) = (term105 x).
Proof. exact (MK_COMB (@lem1551555) (@lem1551554 x)). Qed.
Lemma lem1551557 (x : real) : ((term113 x) = (term112 x)) = ((term131 x) = (term105 x)).
Proof. exact (MK_COMB (@lem1551548 x) (@lem1551556 x)). Qed.
Lemma lem1551558 (x : real) : (term131 x) = (term105 x).
Proof. exact (EQ_MP (@lem1551557 x) (@lem1551535 x)). Qed.
Lemma lem1551559 : term132 = term106.
Proof. exact (fun_ext (fun x : real => @lem1551558 x)). Qed.
Lemma lem1551560 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551561 : term133 = term107.
Proof. exact (MK_COMB (@lem1551560) (@lem1551559)). Qed.
Lemma lem1551562 : term153 = term107.
Proof. exact (TRANS (@lem1551531) (@lem1551561)). Qed.
Lemma lem1551563 : term107 = term107.
Proof. exact (TRANS (@lem1551504) (@lem1551562)). Qed.
Lemma lem1551566 : term24 = term107.
Proof. exact (TRANS (@lem1551242) (@lem1551563)). Qed.
Lemma lem1551579 (k : real) (x : real) : (term101 k x) = (term101 k x).
Proof. exact (eq_refl (term101 k x)). Qed.
Lemma lem1551596 (k : real) (x : real) : (term62 k x) = (term158 k x).
Proof. exact (@lem19158 (term50 k x) (term39 k x) (term57 k x)). Qed.
Lemma lem1551597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551598 (k : real) (x : real) : (term102 k x) = (term159 k x).
Proof. exact (MK_COMB (@lem1551597) (@lem1551596 k x)). Qed.
Lemma lem1551599 (k : real) (x : real) : (term103 k x) = (term160 k x).
Proof. exact (MK_COMB (@lem1551598 k x) (@lem1551579 k x)). Qed.
Lemma lem1551600 (x : real) : (term104 x) = (term161 x).
Proof. exact (fun_ext (fun k : real => @lem1551599 k x)). Qed.
Lemma lem1551601 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551602 (x : real) : (term105 x) = (term162 x).
Proof. exact (MK_COMB (@lem1551601) (@lem1551600 x)). Qed.
Lemma lem1551603 : term106 = term163.
Proof. exact (fun_ext (fun x : real => @lem1551602 x)). Qed.
Lemma lem1551604 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1551605 : term107 = term164.
Proof. exact (MK_COMB (@lem1551604) (@lem1551603)). Qed.
Lemma lem1551606 : term24 = term164.
Proof. exact (TRANS (@lem1551566) (@lem1551605)). Qed.
Lemma lem1551608 (a : real) (x : real) (r : real) : (term165 a x r) = (term166 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1551609 (k : real) (x : real) : (term39 k x) = (term167 k x).
Proof. exact (@lem1551608 k x term38). Qed.
Lemma lem1551616 (x : real) : (term88 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1551619 (k : real) : (real_add k) = (real_add k).
Proof. exact (eq_refl (real_add k)). Qed.
Lemma lem1551622 (k : real) (x : real) : (term168 k x) = (real_add k x).
Proof. exact (MK_COMB (@lem1551619 k) (@lem1551616 x)). Qed.
Lemma lem1551623 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551624 (k : real) (x : real) : (term169 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1551623) (@lem1551622 k x)). Qed.
Lemma lem1551625 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551626 (k : real) (x : real) : (term170 k x) = (term91 k x).
Proof. exact (MK_COMB (@lem1551624 k x) (@lem1551625)). Qed.
Lemma lem1551645 (k : real) (x : real) : (term171 k x) = (term171 k x).
Proof. exact (eq_refl (term171 k x)). Qed.
Lemma lem1551646 (k : real) (x : real) : (term167 k x) = (term172 k x).
Proof. exact (MK_COMB (@lem1551645 k x) (@lem1551626 k x)). Qed.
Lemma lem1551647 (k : real) (x : real) : (term39 k x) = (term172 k x).
Proof. exact (TRANS (@lem1551609 k x) (@lem1551646 k x)). Qed.
Lemma lem1551648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551649 (k : real) (x : real) : (term61 k x) = (term173 k x).
Proof. exact (MK_COMB (@lem1551648) (@lem1551647 k x)). Qed.
Lemma lem1551650 (k : real) (x : real) : (term50 k x) = (term50 k x).
Proof. exact (eq_refl (term50 k x)). Qed.
Lemma lem1551653 (k : real) (x : real) : (term174 k x) = (term175 k x).
Proof. exact (MK_COMB (@lem1551649 k x) (@lem1551650 k x)). Qed.
Lemma lem1551655 (a : real) (x : real) (r : real) : (term165 a x r) = (term166 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1551656 (k : real) (x : real) : (term39 k x) = (term167 k x).
Proof. exact (@lem1551655 k x term38). Qed.
Lemma lem1551663 (x : real) : (term88 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1551666 (k : real) : (real_add k) = (real_add k).
Proof. exact (eq_refl (real_add k)). Qed.
Lemma lem1551669 (k : real) (x : real) : (term168 k x) = (real_add k x).
Proof. exact (MK_COMB (@lem1551666 k) (@lem1551663 x)). Qed.
Lemma lem1551670 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551671 (k : real) (x : real) : (term169 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1551670) (@lem1551669 k x)). Qed.
Lemma lem1551672 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551673 (k : real) (x : real) : (term170 k x) = (term91 k x).
Proof. exact (MK_COMB (@lem1551671 k x) (@lem1551672)). Qed.
Lemma lem1551692 (k : real) (x : real) : (term171 k x) = (term171 k x).
Proof. exact (eq_refl (term171 k x)). Qed.
Lemma lem1551693 (k : real) (x : real) : (term167 k x) = (term172 k x).
Proof. exact (MK_COMB (@lem1551692 k x) (@lem1551673 k x)). Qed.
Lemma lem1551694 (k : real) (x : real) : (term39 k x) = (term172 k x).
Proof. exact (TRANS (@lem1551656 k x) (@lem1551693 k x)). Qed.
Lemma lem1551695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551696 (k : real) (x : real) : (term61 k x) = (term173 k x).
Proof. exact (MK_COMB (@lem1551695) (@lem1551694 k x)). Qed.
Lemma lem1551697 (k : real) (x : real) : (term57 k x) = (term57 k x).
Proof. exact (eq_refl (term57 k x)). Qed.
Lemma lem1551700 (k : real) (x : real) : (term176 k x) = (term177 k x).
Proof. exact (MK_COMB (@lem1551696 k x) (@lem1551697 k x)). Qed.
Lemma lem1551701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551702 (k : real) (x : real) : (term178 k x) = (term179 k x).
Proof. exact (MK_COMB (@lem1551701) (@lem1551653 k x)). Qed.
Lemma lem1551703 (k : real) (x : real) : (term158 k x) = (term180 k x).
Proof. exact (MK_COMB (@lem1551702 k x) (@lem1551700 k x)). Qed.
Lemma lem1551705 (k : real) (x : real) : (term181 k x) = (term101 k x).
Proof. exact (eq_refl (term181 k x)). Qed.
Lemma lem1551706 (k : real) (x : real) : (term101 k x) = (term181 k x).
Proof. exact (SYM (@lem1551705 k x)). Qed.
Lemma lem1551707 (k : real) (x : real) : (term181 k x) = (term182 k x).
Proof. exact (@lem1482981 (term183 k x) x). Qed.
Lemma lem1551708 (k : real) (x : real) : (term101 k x) = (term182 k x).
Proof. exact (TRANS (@lem1551706 k x) (@lem1551707 k x)). Qed.
Lemma lem1551709 (k : real) (x : real) : (term184 k x) = (term185 k x).
Proof. exact (eq_refl (term184 k x)). Qed.
Lemma lem1551710 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1551711 (k : real) (x : real) : (term187 k x) = (term188 k x).
Proof. exact (MK_COMB (@lem1551710 x) (@lem1551709 k x)). Qed.
Lemma lem1551712 (k : real) (x : real) : (term189 k x) = (term190 k x).
Proof. exact (eq_refl (term189 k x)). Qed.
Lemma lem1551713 (x : real) : (term191 x) = (term191 x).
Proof. exact (eq_refl (term191 x)). Qed.
Lemma lem1551714 (k : real) (x : real) : (term192 k x) = (term193 k x).
Proof. exact (MK_COMB (@lem1551713 x) (@lem1551712 k x)). Qed.
Lemma lem1551715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551716 (k : real) (x : real) : (term194 k x) = (term195 k x).
Proof. exact (MK_COMB (@lem1551715) (@lem1551714 k x)). Qed.
Lemma lem1551717 (k : real) (x : real) : (term182 k x) = (term196 k x).
Proof. exact (MK_COMB (@lem1551716 k x) (@lem1551711 k x)). Qed.
Lemma lem1551718 (k : real) (x : real) : (term197 k x) = (term197 k x).
Proof. exact (eq_refl (term197 k x)). Qed.
Lemma lem1551719 (k : real) (x : real) : ((term101 k x) = (term182 k x)) = ((term101 k x) = (term196 k x)).
Proof. exact (MK_COMB (@lem1551718 k x) (@lem1551717 k x)). Qed.
Lemma lem1551720 (k : real) (x : real) : (term101 k x) = (term196 k x).
Proof. exact (EQ_MP (@lem1551719 k x) (@lem1551708 k x)). Qed.
Lemma lem1551721 (x : real) : (term198 x) = (term199 x).
Proof. exact (@lem1483527 x term38). Qed.
Lemma lem1551727 (x : real) : (term200 x) = (term201 x).
Proof. exact (@lem1483519 x term38). Qed.
Lemma lem1551729 (x : nat) : (term202 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1551730 : term203 = term38.
Proof. exact (@lem1551729 term82). Qed.
Lemma lem1551731 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1551732 (x : real) : (term201 x) = (term204 x).
Proof. exact (MK_COMB (@lem1551731 x) (@lem1551730)). Qed.
Lemma lem1551733 (x : real) : (term204 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1551734 (x : real) : (term201 x) = x.
Proof. exact (TRANS (@lem1551732 x) (@lem1551733 x)). Qed.
Lemma lem1551736 (x : real) : (term200 x) = x.
Proof. exact (TRANS (@lem1551727 x) (@lem1551734 x)). Qed.
Lemma lem1551737 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551738 (x : real) : (term205 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1551737) (@lem1551736 x)). Qed.
Lemma lem1551739 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551740 (x : real) : (term199 x) = (term198 x).
Proof. exact (MK_COMB (@lem1551738 x) (@lem1551739)). Qed.
Lemma lem1551741 (x : real) : (term198 x) = (term198 x).
Proof. exact (TRANS (@lem1551721 x) (@lem1551740 x)). Qed.
Lemma lem1551742 (k : real) (x : real) : (term57 k x) = (term206 k x).
Proof. exact (@lem1483525 (term54 k x) term38). Qed.
Lemma lem1551760 (k : real) (x : real) : (term207 k x) = (term208 k x).
Proof. exact (@lem1483519 (term54 k x) term38). Qed.
Lemma lem1551762 (x : nat) : (term202 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1551763 : term203 = term38.
Proof. exact (@lem1551762 term82). Qed.
Lemma lem1551764 (k : real) (x : real) : (term209 k x) = (term209 k x).
Proof. exact (eq_refl (term209 k x)). Qed.
Lemma lem1551765 (k : real) (x : real) : (term208 k x) = (term210 k x).
Proof. exact (MK_COMB (@lem1551764 k x) (@lem1551763)). Qed.
Lemma lem1551766 (k : real) (x : real) : (term210 k x) = (term54 k x).
Proof. exact (@lem1483450 (term54 k x)). Qed.
Lemma lem1551767 (k : real) (x : real) : (term208 k x) = (term54 k x).
Proof. exact (TRANS (@lem1551765 k x) (@lem1551766 k x)). Qed.
Lemma lem1551769 (k : real) (x : real) : (term207 k x) = (term54 k x).
Proof. exact (TRANS (@lem1551760 k x) (@lem1551767 k x)). Qed.
Lemma lem1551770 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1551771 (k : real) (x : real) : (term211 k x) = (term56 k x).
Proof. exact (MK_COMB (@lem1551770) (@lem1551769 k x)). Qed.
Lemma lem1551772 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551773 (k : real) (x : real) : (term206 k x) = (term57 k x).
Proof. exact (MK_COMB (@lem1551771 k x) (@lem1551772)). Qed.
Lemma lem1551774 (k : real) (x : real) : (term57 k x) = (term57 k x).
Proof. exact (TRANS (@lem1551742 k x) (@lem1551773 k x)). Qed.
Lemma lem1551775 (k : real) (x : real) : (term91 k x) = (term212 k x).
Proof. exact (@lem1483527 (real_add k x) term38). Qed.
Lemma lem1551787 (k : real) (x : real) : (term213 k x) = (term214 k x).
Proof. exact (@lem1483519 (real_add k x) term38). Qed.
Lemma lem1551789 (x : nat) : (term202 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1551790 : term203 = term38.
Proof. exact (@lem1551789 term82). Qed.
Lemma lem1551791 (k : real) (x : real) : (term215 k x) = (term215 k x).
Proof. exact (eq_refl (term215 k x)). Qed.
Lemma lem1551792 (k : real) (x : real) : (term214 k x) = (term216 k x).
Proof. exact (MK_COMB (@lem1551791 k x) (@lem1551790)). Qed.
Lemma lem1551793 (k : real) (x : real) : (term216 k x) = (real_add k x).
Proof. exact (@lem1483450 (real_add k x)). Qed.
Lemma lem1551794 (k : real) (x : real) : (term214 k x) = (real_add k x).
Proof. exact (TRANS (@lem1551792 k x) (@lem1551793 k x)). Qed.
Lemma lem1551796 (k : real) (x : real) : (term213 k x) = (real_add k x).
Proof. exact (TRANS (@lem1551787 k x) (@lem1551794 k x)). Qed.
Lemma lem1551797 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551798 (k : real) (x : real) : (term217 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1551797) (@lem1551796 k x)). Qed.
Lemma lem1551799 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551800 (k : real) (x : real) : (term212 k x) = (term91 k x).
Proof. exact (MK_COMB (@lem1551798 k x) (@lem1551799)). Qed.
Lemma lem1551801 (k : real) (x : real) : (term91 k x) = (term91 k x).
Proof. exact (TRANS (@lem1551775 k x) (@lem1551800 k x)). Qed.
Lemma lem1551802 (k : real) (x : real) : (term95 k x) = (term218 k x).
Proof. exact (@lem1483527 (term53 k x) term38). Qed.
Lemma lem1551820 (k : real) (x : real) : (term219 k x) = (term220 k x).
Proof. exact (@lem1483519 (term53 k x) term38). Qed.
Lemma lem1551822 (x : nat) : (term202 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1551823 : term203 = term38.
Proof. exact (@lem1551822 term82). Qed.
Lemma lem1551824 (k : real) (x : real) : (term221 k x) = (term221 k x).
Proof. exact (eq_refl (term221 k x)). Qed.
Lemma lem1551825 (k : real) (x : real) : (term220 k x) = (term222 k x).
Proof. exact (MK_COMB (@lem1551824 k x) (@lem1551823)). Qed.
Lemma lem1551826 (k : real) (x : real) : (term222 k x) = (term53 k x).
Proof. exact (@lem1483450 (term53 k x)). Qed.
Lemma lem1551827 (k : real) (x : real) : (term220 k x) = (term53 k x).
Proof. exact (TRANS (@lem1551825 k x) (@lem1551826 k x)). Qed.
Lemma lem1551829 (k : real) (x : real) : (term219 k x) = (term53 k x).
Proof. exact (TRANS (@lem1551820 k x) (@lem1551827 k x)). Qed.
Lemma lem1551830 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551831 (k : real) (x : real) : (term223 k x) = (term94 k x).
Proof. exact (MK_COMB (@lem1551830) (@lem1551829 k x)). Qed.
Lemma lem1551832 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551833 (k : real) (x : real) : (term218 k x) = (term95 k x).
Proof. exact (MK_COMB (@lem1551831 k x) (@lem1551832)). Qed.
Lemma lem1551834 (k : real) (x : real) : (term95 k x) = (term95 k x).
Proof. exact (TRANS (@lem1551802 k x) (@lem1551833 k x)). Qed.
Lemma lem1551835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551836 (k : real) (x : real) : (term97 k x) = (term97 k x).
Proof. exact (MK_COMB (@lem1551835) (@lem1551801 k x)). Qed.
Lemma lem1551837 (k : real) (x : real) : (term98 k x) = (term98 k x).
Proof. exact (MK_COMB (@lem1551836 k x) (@lem1551834 k x)). Qed.
Lemma lem1551838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551839 (k : real) (x : real) : (term224 k x) = (term224 k x).
Proof. exact (MK_COMB (@lem1551838) (@lem1551774 k x)). Qed.
Lemma lem1551840 (k : real) (x : real) : (term190 k x) = (term190 k x).
Proof. exact (MK_COMB (@lem1551839 k x) (@lem1551837 k x)). Qed.
Lemma lem1551841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551842 (x : real) : (term191 x) = (term191 x).
Proof. exact (MK_COMB (@lem1551841) (@lem1551741 x)). Qed.
Lemma lem1551843 (k : real) (x : real) : (term193 k x) = (term193 k x).
Proof. exact (MK_COMB (@lem1551842 x) (@lem1551840 k x)). Qed.
Lemma lem1551844 (x : real) : (term225 x) = (term226 x).
Proof. exact (@lem1483525 term38 x). Qed.
Lemma lem1551850 (x : real) : (term227 x) = (term228 x).
Proof. exact (@lem1483519 term38 x). Qed.
Lemma lem1551855 (x : real) : (term228 x) = (term42 x).
Proof. exact (@lem1483448 (term42 x)). Qed.
Lemma lem1551857 (x : real) : (term227 x) = (term42 x).
Proof. exact (TRANS (@lem1551850 x) (@lem1551855 x)). Qed.
Lemma lem1551858 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1551859 (x : real) : (term229 x) = (term230 x).
Proof. exact (MK_COMB (@lem1551858) (@lem1551857 x)). Qed.
Lemma lem1551860 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551861 (x : real) : (term226 x) = (term231 x).
Proof. exact (MK_COMB (@lem1551859 x) (@lem1551860)). Qed.
Lemma lem1551862 (x : real) : (term225 x) = (term231 x).
Proof. exact (TRANS (@lem1551844 x) (@lem1551861 x)). Qed.
Lemma lem1551863 (k : real) (x : real) : (term232 k x) = (term233 k x).
Proof. exact (@lem1483525 (term234 k x) term38). Qed.
Lemma lem1551864 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551871 (x : real) : (real_neg x) = (term42 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1551880 (k : real) : (term235 k) = (term235 k).
Proof. exact (eq_refl (term235 k)). Qed.
Lemma lem1551883 (k : real) (x : real) : (term234 k x) = (term47 k x).
Proof. exact (MK_COMB (@lem1551880 k) (@lem1551871 x)). Qed.
Lemma lem1551884 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1551885 (k : real) (x : real) : (term236 k x) = (term237 k x).
Proof. exact (MK_COMB (@lem1551884) (@lem1551883 k x)). Qed.
Lemma lem1551886 (k : real) (x : real) : (term238 k x) = (term239 k x).
Proof. exact (MK_COMB (@lem1551885 k x) (@lem1551864)). Qed.
Lemma lem1551887 (k : real) (x : real) : (term239 k x) = (term240 k x).
Proof. exact (@lem1483519 (term47 k x) term38). Qed.
Lemma lem1551889 (x : nat) : (term202 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1551890 : term203 = term38.
Proof. exact (@lem1551889 term82). Qed.
Lemma lem1551891 (k : real) (x : real) : (term241 k x) = (term241 k x).
Proof. exact (eq_refl (term241 k x)). Qed.
Lemma lem1551892 (k : real) (x : real) : (term240 k x) = (term242 k x).
Proof. exact (MK_COMB (@lem1551891 k x) (@lem1551890)). Qed.
Lemma lem1551893 (k : real) (x : real) : (term242 k x) = (term47 k x).
Proof. exact (@lem1483450 (term47 k x)). Qed.
Lemma lem1551894 (k : real) (x : real) : (term240 k x) = (term47 k x).
Proof. exact (TRANS (@lem1551892 k x) (@lem1551893 k x)). Qed.
Lemma lem1551895 (k : real) (x : real) : (term239 k x) = (term47 k x).
Proof. exact (TRANS (@lem1551887 k x) (@lem1551894 k x)). Qed.
Lemma lem1551896 (k : real) (x : real) : (term238 k x) = (term47 k x).
Proof. exact (TRANS (@lem1551886 k x) (@lem1551895 k x)). Qed.
Lemma lem1551897 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1551898 (k : real) (x : real) : (term243 k x) = (term49 k x).
Proof. exact (MK_COMB (@lem1551897) (@lem1551896 k x)). Qed.
Lemma lem1551899 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551900 (k : real) (x : real) : (term233 k x) = (term50 k x).
Proof. exact (MK_COMB (@lem1551898 k x) (@lem1551899)). Qed.
Lemma lem1551901 (k : real) (x : real) : (term232 k x) = (term50 k x).
Proof. exact (TRANS (@lem1551863 k x) (@lem1551900 k x)). Qed.
Lemma lem1551902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551903 (k : real) (x : real) : (term97 k x) = (term97 k x).
Proof. exact (MK_COMB (@lem1551902) (@lem1551801 k x)). Qed.
Lemma lem1551904 (k : real) (x : real) : (term98 k x) = (term98 k x).
Proof. exact (MK_COMB (@lem1551903 k x) (@lem1551834 k x)). Qed.
Lemma lem1551905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551906 (k : real) (x : real) : (term244 k x) = (term245 k x).
Proof. exact (MK_COMB (@lem1551905) (@lem1551901 k x)). Qed.
Lemma lem1551907 (k : real) (x : real) : (term185 k x) = (term246 k x).
Proof. exact (MK_COMB (@lem1551906 k x) (@lem1551904 k x)). Qed.
Lemma lem1551908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1551909 (x : real) : (term186 x) = (term247 x).
Proof. exact (MK_COMB (@lem1551908) (@lem1551862 x)). Qed.
Lemma lem1551910 (k : real) (x : real) : (term188 k x) = (term248 k x).
Proof. exact (MK_COMB (@lem1551909 x) (@lem1551907 k x)). Qed.
Lemma lem1551911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551912 (k : real) (x : real) : (term195 k x) = (term195 k x).
Proof. exact (MK_COMB (@lem1551911) (@lem1551843 k x)). Qed.
Lemma lem1551913 (k : real) (x : real) : (term196 k x) = (term249 k x).
Proof. exact (MK_COMB (@lem1551912 k x) (@lem1551910 k x)). Qed.
Lemma lem1551925 (k : real) (x : real) : (term101 k x) = (term249 k x).
Proof. exact (TRANS (@lem1551720 k x) (@lem1551913 k x)). Qed.
Lemma lem1551926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1551927 (k : real) (x : real) : (term159 k x) = (term250 k x).
Proof. exact (MK_COMB (@lem1551926) (@lem1551703 k x)). Qed.
Lemma lem1551928 (k : real) (x : real) : (term160 k x) = (term251 k x).
Proof. exact (MK_COMB (@lem1551927 k x) (@lem1551925 k x)). Qed.
Lemma lem1551929 (k : real) (x : real) (h1 : term251 k x) : term251 k x.
Proof. exact (h1). Qed.
Lemma lem1551930 (k : real) (x : real) (h1 : term180 k x) : term180 k x.
Proof. exact (h1). Qed.
Lemma lem1551931 (k : real) (x : real) (h1 : term175 k x) : term175 k x.
Proof. exact (h1). Qed.
Lemma lem1551932 (k : real) (x : real) (h1 : term175 k x) : term50 k x.
Proof. exact (proj2 (@lem1551931 k x h1)). Qed.
Lemma lem1551933 (k : real) (x : real) (h1 : term175 k x) : term172 k x.
Proof. exact (proj1 (@lem1551931 k x h1)). Qed.
Lemma lem1551934 (k : real) (x : real) (h1 : term175 k x) : term91 k x.
Proof. exact (proj2 (@lem1551933 k x h1)). Qed.
Lemma lem1551937 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1551938 : term253 = term254.
Proof. exact (@lem1551937 (NUMERAL 0) term82). Qed.
Lemma lem1551939 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1551940 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1551941 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1551940 h1) (fun h1 : term254 = True => @lem1551939)). Qed.
Lemma lem1551942 : term254 = True.
Proof. exact (EQ_MP (@lem1551941) (@lem1551939)). Qed.
Lemma lem1551943 : term253 = True.
Proof. exact (TRANS (@lem1551938) (@lem1551942)). Qed.
Lemma lem1551944 : True = term253.
Proof. exact (SYM (@lem1551943)). Qed.
Lemma lem1551945 : term253.
Proof. exact (EQ_MP (@lem1551944) (@lem0)). Qed.
Lemma lem1551946 (k : real) (x : real) (h1 : term175 k x) : term256 k x.
Proof. exact (conj (@lem1551945) (@lem1551934 k x h1)). Qed.
Lemma lem1551948 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1551949 (k : real) (x : real) : term258 k x.
Proof. exact (@lem1551948 term85 (real_add k x)). Qed.
Lemma lem1551950 (k : real) (x : real) (h1 : term175 k x) : term259 k x.
Proof. exact (@lem1551949 k x (@lem1551946 k x h1)). Qed.
Lemma lem1551951 (k : real) (x : real) : (term260 k x) = (real_add k x).
Proof. exact (@lem1483460 (real_add k x)). Qed.
Lemma lem1551952 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1551953 (k : real) (x : real) : (term261 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1551952) (@lem1551951 k x)). Qed.
Lemma lem1551954 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551955 (k : real) (x : real) : (term259 k x) = (term91 k x).
Proof. exact (MK_COMB (@lem1551953 k x) (@lem1551954)). Qed.
Lemma lem1551956 (k : real) (x : real) (h1 : term175 k x) : term91 k x.
Proof. exact (EQ_MP (@lem1551955 k x) (@lem1551950 k x h1)). Qed.
Lemma lem1551958 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1551959 : term253 = term254.
Proof. exact (@lem1551958 (NUMERAL 0) term82). Qed.
Lemma lem1551960 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1551961 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1551962 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1551961 h1) (fun h1 : term254 = True => @lem1551960)). Qed.
Lemma lem1551963 : term254 = True.
Proof. exact (EQ_MP (@lem1551962) (@lem1551960)). Qed.
Lemma lem1551964 : term253 = True.
Proof. exact (TRANS (@lem1551959) (@lem1551963)). Qed.
Lemma lem1551965 : True = term253.
Proof. exact (SYM (@lem1551964)). Qed.
Lemma lem1551966 : term253.
Proof. exact (EQ_MP (@lem1551965) (@lem0)). Qed.
Lemma lem1551967 (k : real) (x : real) (h1 : term175 k x) : term262 k x.
Proof. exact (conj (@lem1551966) (@lem1551932 k x h1)). Qed.
Lemma lem1551969 (x : real) (y : real) : term263 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1551970 (k : real) (x : real) : term264 k x.
Proof. exact (@lem1551969 term85 (term47 k x)). Qed.
Lemma lem1551971 (k : real) (x : real) (h1 : term175 k x) : term265 k x.
Proof. exact (@lem1551970 k x (@lem1551967 k x h1)). Qed.
Lemma lem1551972 (k : real) (x : real) : (term266 k x) = (term47 k x).
Proof. exact (@lem1483460 (term47 k x)). Qed.
Lemma lem1551973 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1551974 (k : real) (x : real) : (term267 k x) = (term49 k x).
Proof. exact (MK_COMB (@lem1551973) (@lem1551972 k x)). Qed.
Lemma lem1551975 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1551976 (k : real) (x : real) : (term265 k x) = (term50 k x).
Proof. exact (MK_COMB (@lem1551974 k x) (@lem1551975)). Qed.
Lemma lem1551977 (k : real) (x : real) (h1 : term175 k x) : term50 k x.
Proof. exact (EQ_MP (@lem1551976 k x) (@lem1551971 k x h1)). Qed.
Lemma lem1551978 (k : real) (x : real) (h1 : term175 k x) : term268 k x.
Proof. exact (conj (@lem1551977 k x h1) (@lem1551956 k x h1)). Qed.
Lemma lem1551980 (x : real) (y : real) : term269 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1551981 (k : real) (x : real) : term270 k x.
Proof. exact (@lem1551980 (term47 k x) (real_add k x)). Qed.
Lemma lem1551982 (k : real) (x : real) (h1 : term175 k x) : term271 k x.
Proof. exact (@lem1551981 k x (@lem1551978 k x h1)). Qed.
Lemma lem1551983 (k : real) (x : real) : (term272 k x) = (term273 k x).
Proof. exact (@lem1483480 (term42 k) k (term42 x) x). Qed.
Lemma lem1551984 (k : real) : (term274 k) = (term275 k).
Proof. exact (@lem1483440 term77 k). Qed.
Lemma lem1551986 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1551987 : term277 = term38.
Proof. exact (@lem1551986 term82). Qed.
Lemma lem1551988 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1551989 : term278 = term279.
Proof. exact (MK_COMB (@lem1551988) (@lem1551987)). Qed.
Lemma lem1551990 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1551991 (k : real) : (term275 k) = (term280 k).
Proof. exact (MK_COMB (@lem1551989) (@lem1551990 k)). Qed.
Lemma lem1551992 (k : real) : (term274 k) = (term280 k).
Proof. exact (TRANS (@lem1551984 k) (@lem1551991 k)). Qed.
Lemma lem1551993 (k : real) : (term280 k) = term38.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1551994 (k : real) : (term274 k) = term38.
Proof. exact (TRANS (@lem1551992 k) (@lem1551993 k)). Qed.
Lemma lem1551995 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1551996 (k : real) : (term281 k) = term282.
Proof. exact (MK_COMB (@lem1551995) (@lem1551994 k)). Qed.
Lemma lem1551997 (x : real) : (term274 x) = (term275 x).
Proof. exact (@lem1483440 term77 x). Qed.
Lemma lem1551999 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1552000 : term277 = term38.
Proof. exact (@lem1551999 term82). Qed.
Lemma lem1552001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552002 : term278 = term279.
Proof. exact (MK_COMB (@lem1552001) (@lem1552000)). Qed.
Lemma lem1552003 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1552004 (x : real) : (term275 x) = (term280 x).
Proof. exact (MK_COMB (@lem1552002) (@lem1552003 x)). Qed.
Lemma lem1552005 (x : real) : (term274 x) = (term280 x).
Proof. exact (TRANS (@lem1551997 x) (@lem1552004 x)). Qed.
Lemma lem1552006 (x : real) : (term280 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1552007 (x : real) : (term274 x) = term38.
Proof. exact (TRANS (@lem1552005 x) (@lem1552006 x)). Qed.
Lemma lem1552008 (k : real) (x : real) : (term273 k x) = term283.
Proof. exact (MK_COMB (@lem1551996 k) (@lem1552007 x)). Qed.
Lemma lem1552009 (k : real) (x : real) : (term272 k x) = term283.
Proof. exact (TRANS (@lem1551983 k x) (@lem1552008 k x)). Qed.
Lemma lem1552010 : term283 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1552011 (k : real) (x : real) : (term272 k x) = term38.
Proof. exact (TRANS (@lem1552009 k x) (@lem1552010)). Qed.
Lemma lem1552012 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552013 (k : real) (x : real) : (term284 k x) = term285.
Proof. exact (MK_COMB (@lem1552012) (@lem1552011 k x)). Qed.
Lemma lem1552014 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552015 (k : real) (x : real) : (term271 k x) = term286.
Proof. exact (MK_COMB (@lem1552013 k x) (@lem1552014)). Qed.
Lemma lem1552016 (k : real) (x : real) (h1 : term175 k x) : term286.
Proof. exact (EQ_MP (@lem1552015 k x) (@lem1551982 k x h1)). Qed.
Lemma lem1552018 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552019 : term286 = term287.
Proof. exact (@lem1552018 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1552020 : term287 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1552021 : term286 = False.
Proof. exact (TRANS (@lem1552019) (@lem1552020)). Qed.
Lemma lem1552022 (k : real) (x : real) (h1 : term175 k x) : False.
Proof. exact (EQ_MP (@lem1552021) (@lem1552016 k x h1)). Qed.
Lemma lem1552023 (k : real) (x : real) (h1 : term177 k x) : term177 k x.
Proof. exact (h1). Qed.
Lemma lem1552024 (k : real) (x : real) (h1 : term177 k x) : term57 k x.
Proof. exact (proj2 (@lem1552023 k x h1)). Qed.
Lemma lem1552025 (k : real) (x : real) (h1 : term177 k x) : term172 k x.
Proof. exact (proj1 (@lem1552023 k x h1)). Qed.
Lemma lem1552027 (k : real) (x : real) (h1 : term177 k x) : term95 k x.
Proof. exact (proj1 (@lem1552025 k x h1)). Qed.
Lemma lem1552029 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552030 : term253 = term254.
Proof. exact (@lem1552029 (NUMERAL 0) term82). Qed.
Lemma lem1552031 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1552032 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1552033 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1552032 h1) (fun h1 : term254 = True => @lem1552031)). Qed.
Lemma lem1552034 : term254 = True.
Proof. exact (EQ_MP (@lem1552033) (@lem1552031)). Qed.
Lemma lem1552035 : term253 = True.
Proof. exact (TRANS (@lem1552030) (@lem1552034)). Qed.
Lemma lem1552036 : True = term253.
Proof. exact (SYM (@lem1552035)). Qed.
Lemma lem1552037 : term253.
Proof. exact (EQ_MP (@lem1552036) (@lem0)). Qed.
Lemma lem1552038 (k : real) (x : real) (h1 : term177 k x) : term288 k x.
Proof. exact (conj (@lem1552037) (@lem1552027 k x h1)). Qed.
Lemma lem1552040 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1552041 (k : real) (x : real) : term289 k x.
Proof. exact (@lem1552040 term85 (term53 k x)). Qed.
Lemma lem1552042 (k : real) (x : real) (h1 : term177 k x) : term290 k x.
Proof. exact (@lem1552041 k x (@lem1552038 k x h1)). Qed.
Lemma lem1552043 (k : real) (x : real) : (term291 k x) = (term53 k x).
Proof. exact (@lem1483460 (term53 k x)). Qed.
Lemma lem1552044 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1552045 (k : real) (x : real) : (term292 k x) = (term94 k x).
Proof. exact (MK_COMB (@lem1552044) (@lem1552043 k x)). Qed.
Lemma lem1552046 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552047 (k : real) (x : real) : (term290 k x) = (term95 k x).
Proof. exact (MK_COMB (@lem1552045 k x) (@lem1552046)). Qed.
Lemma lem1552048 (k : real) (x : real) (h1 : term177 k x) : term95 k x.
Proof. exact (EQ_MP (@lem1552047 k x) (@lem1552042 k x h1)). Qed.
Lemma lem1552050 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552051 : term253 = term254.
Proof. exact (@lem1552050 (NUMERAL 0) term82). Qed.
Lemma lem1552052 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1552053 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1552054 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1552053 h1) (fun h1 : term254 = True => @lem1552052)). Qed.
Lemma lem1552055 : term254 = True.
Proof. exact (EQ_MP (@lem1552054) (@lem1552052)). Qed.
Lemma lem1552056 : term253 = True.
Proof. exact (TRANS (@lem1552051) (@lem1552055)). Qed.
Lemma lem1552057 : True = term253.
Proof. exact (SYM (@lem1552056)). Qed.
Lemma lem1552058 : term253.
Proof. exact (EQ_MP (@lem1552057) (@lem0)). Qed.
Lemma lem1552059 (k : real) (x : real) (h1 : term177 k x) : term293 k x.
Proof. exact (conj (@lem1552058) (@lem1552024 k x h1)). Qed.
Lemma lem1552061 (x : real) (y : real) : term263 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1552062 (k : real) (x : real) : term294 k x.
Proof. exact (@lem1552061 term85 (term54 k x)). Qed.
Lemma lem1552063 (k : real) (x : real) (h1 : term177 k x) : term295 k x.
Proof. exact (@lem1552062 k x (@lem1552059 k x h1)). Qed.
Lemma lem1552064 (k : real) (x : real) : (term296 k x) = (term54 k x).
Proof. exact (@lem1483460 (term54 k x)). Qed.
Lemma lem1552065 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552066 (k : real) (x : real) : (term297 k x) = (term56 k x).
Proof. exact (MK_COMB (@lem1552065) (@lem1552064 k x)). Qed.
Lemma lem1552067 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552068 (k : real) (x : real) : (term295 k x) = (term57 k x).
Proof. exact (MK_COMB (@lem1552066 k x) (@lem1552067)). Qed.
Lemma lem1552069 (k : real) (x : real) (h1 : term177 k x) : term57 k x.
Proof. exact (EQ_MP (@lem1552068 k x) (@lem1552063 k x h1)). Qed.
Lemma lem1552070 (k : real) (x : real) (h1 : term177 k x) : term298 k x.
Proof. exact (conj (@lem1552069 k x h1) (@lem1552048 k x h1)). Qed.
Lemma lem1552072 (x : real) (y : real) : term269 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1552073 (k : real) (x : real) : term299 k x.
Proof. exact (@lem1552072 (term54 k x) (term53 k x)). Qed.
Lemma lem1552074 (k : real) (x : real) (h1 : term177 k x) : term300 k x.
Proof. exact (@lem1552073 k x (@lem1552070 k x h1)). Qed.
Lemma lem1552075 (k : real) (x : real) : (term301 k x) = (term302 k x).
Proof. exact (@lem1483480 (term42 k) k x (term42 x)). Qed.
Lemma lem1552076 (k : real) : (term274 k) = (term275 k).
Proof. exact (@lem1483440 term77 k). Qed.
Lemma lem1552078 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1552079 : term277 = term38.
Proof. exact (@lem1552078 term82). Qed.
Lemma lem1552080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552081 : term278 = term279.
Proof. exact (MK_COMB (@lem1552080) (@lem1552079)). Qed.
Lemma lem1552082 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1552083 (k : real) : (term275 k) = (term280 k).
Proof. exact (MK_COMB (@lem1552081) (@lem1552082 k)). Qed.
Lemma lem1552084 (k : real) : (term274 k) = (term280 k).
Proof. exact (TRANS (@lem1552076 k) (@lem1552083 k)). Qed.
Lemma lem1552085 (k : real) : (term280 k) = term38.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1552086 (k : real) : (term274 k) = term38.
Proof. exact (TRANS (@lem1552084 k) (@lem1552085 k)). Qed.
Lemma lem1552087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1552088 (k : real) : (term281 k) = term282.
Proof. exact (MK_COMB (@lem1552087) (@lem1552086 k)). Qed.
Lemma lem1552089 (x : real) : (term303 x) = (term275 x).
Proof. exact (@lem1483442 term77 x). Qed.
Lemma lem1552091 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1552092 : term277 = term38.
Proof. exact (@lem1552091 term82). Qed.
Lemma lem1552093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552094 : term278 = term279.
Proof. exact (MK_COMB (@lem1552093) (@lem1552092)). Qed.
Lemma lem1552095 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1552096 (x : real) : (term275 x) = (term280 x).
Proof. exact (MK_COMB (@lem1552094) (@lem1552095 x)). Qed.
Lemma lem1552097 (x : real) : (term303 x) = (term280 x).
Proof. exact (TRANS (@lem1552089 x) (@lem1552096 x)). Qed.
Lemma lem1552098 (x : real) : (term280 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1552099 (x : real) : (term303 x) = term38.
Proof. exact (TRANS (@lem1552097 x) (@lem1552098 x)). Qed.
Lemma lem1552100 (k : real) (x : real) : (term302 k x) = term283.
Proof. exact (MK_COMB (@lem1552088 k) (@lem1552099 x)). Qed.
Lemma lem1552101 (k : real) (x : real) : (term301 k x) = term283.
Proof. exact (TRANS (@lem1552075 k x) (@lem1552100 k x)). Qed.
Lemma lem1552102 : term283 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1552103 (k : real) (x : real) : (term301 k x) = term38.
Proof. exact (TRANS (@lem1552101 k x) (@lem1552102)). Qed.
Lemma lem1552104 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552105 (k : real) (x : real) : (term304 k x) = term285.
Proof. exact (MK_COMB (@lem1552104) (@lem1552103 k x)). Qed.
Lemma lem1552106 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552107 (k : real) (x : real) : (term300 k x) = term286.
Proof. exact (MK_COMB (@lem1552105 k x) (@lem1552106)). Qed.
Lemma lem1552108 (k : real) (x : real) (h1 : term177 k x) : term286.
Proof. exact (EQ_MP (@lem1552107 k x) (@lem1552074 k x h1)). Qed.
Lemma lem1552110 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552111 : term286 = term287.
Proof. exact (@lem1552110 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1552112 : term287 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1552113 : term286 = False.
Proof. exact (TRANS (@lem1552111) (@lem1552112)). Qed.
Lemma lem1552114 (k : real) (x : real) (h1 : term177 k x) : False.
Proof. exact (EQ_MP (@lem1552113) (@lem1552108 k x h1)). Qed.
Lemma lem1552115 (k : real) (x : real) (h1 : term180 k x) : False.
Proof. exact (or_elim (@lem1551930 k x h1) (fun h0 : term175 k x => @lem1552022 k x h0) (fun h0 : term177 k x => @lem1552114 k x h0)). Qed.
Lemma lem1552116 (k : real) (x : real) (h1 : term249 k x) : term249 k x.
Proof. exact (h1). Qed.
Lemma lem1552117 (k : real) (x : real) (h1 : term193 k x) : term193 k x.
Proof. exact (h1). Qed.
Lemma lem1552118 (k : real) (x : real) (h1 : term193 k x) : term190 k x.
Proof. exact (proj2 (@lem1552117 k x h1)). Qed.
Lemma lem1552120 (k : real) (x : real) (h1 : term193 k x) : term98 k x.
Proof. exact (proj2 (@lem1552118 k x h1)). Qed.
Lemma lem1552121 (k : real) (x : real) (h1 : term193 k x) : term57 k x.
Proof. exact (proj1 (@lem1552118 k x h1)). Qed.
Lemma lem1552122 (k : real) (x : real) (h1 : term193 k x) : term95 k x.
Proof. exact (proj2 (@lem1552120 k x h1)). Qed.
Lemma lem1552125 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552126 : term253 = term254.
Proof. exact (@lem1552125 (NUMERAL 0) term82). Qed.
Lemma lem1552127 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1552128 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1552129 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1552128 h1) (fun h1 : term254 = True => @lem1552127)). Qed.
Lemma lem1552130 : term254 = True.
Proof. exact (EQ_MP (@lem1552129) (@lem1552127)). Qed.
Lemma lem1552131 : term253 = True.
Proof. exact (TRANS (@lem1552126) (@lem1552130)). Qed.
Lemma lem1552132 : True = term253.
Proof. exact (SYM (@lem1552131)). Qed.
Lemma lem1552133 : term253.
Proof. exact (EQ_MP (@lem1552132) (@lem0)). Qed.
Lemma lem1552134 (k : real) (x : real) (h1 : term193 k x) : term288 k x.
Proof. exact (conj (@lem1552133) (@lem1552122 k x h1)). Qed.
Lemma lem1552136 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1552137 (k : real) (x : real) : term289 k x.
Proof. exact (@lem1552136 term85 (term53 k x)). Qed.
Lemma lem1552138 (k : real) (x : real) (h1 : term193 k x) : term290 k x.
Proof. exact (@lem1552137 k x (@lem1552134 k x h1)). Qed.
Lemma lem1552139 (k : real) (x : real) : (term291 k x) = (term53 k x).
Proof. exact (@lem1483460 (term53 k x)). Qed.
Lemma lem1552140 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1552141 (k : real) (x : real) : (term292 k x) = (term94 k x).
Proof. exact (MK_COMB (@lem1552140) (@lem1552139 k x)). Qed.
Lemma lem1552142 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552143 (k : real) (x : real) : (term290 k x) = (term95 k x).
Proof. exact (MK_COMB (@lem1552141 k x) (@lem1552142)). Qed.
Lemma lem1552144 (k : real) (x : real) (h1 : term193 k x) : term95 k x.
Proof. exact (EQ_MP (@lem1552143 k x) (@lem1552138 k x h1)). Qed.
Lemma lem1552146 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552147 : term253 = term254.
Proof. exact (@lem1552146 (NUMERAL 0) term82). Qed.
Lemma lem1552148 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1552149 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1552150 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1552149 h1) (fun h1 : term254 = True => @lem1552148)). Qed.
Lemma lem1552151 : term254 = True.
Proof. exact (EQ_MP (@lem1552150) (@lem1552148)). Qed.
Lemma lem1552152 : term253 = True.
Proof. exact (TRANS (@lem1552147) (@lem1552151)). Qed.
Lemma lem1552153 : True = term253.
Proof. exact (SYM (@lem1552152)). Qed.
Lemma lem1552154 : term253.
Proof. exact (EQ_MP (@lem1552153) (@lem0)). Qed.
Lemma lem1552155 (k : real) (x : real) (h1 : term193 k x) : term293 k x.
Proof. exact (conj (@lem1552154) (@lem1552121 k x h1)). Qed.
Lemma lem1552157 (x : real) (y : real) : term263 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1552158 (k : real) (x : real) : term294 k x.
Proof. exact (@lem1552157 term85 (term54 k x)). Qed.
Lemma lem1552159 (k : real) (x : real) (h1 : term193 k x) : term295 k x.
Proof. exact (@lem1552158 k x (@lem1552155 k x h1)). Qed.
Lemma lem1552160 (k : real) (x : real) : (term296 k x) = (term54 k x).
Proof. exact (@lem1483460 (term54 k x)). Qed.
Lemma lem1552161 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552162 (k : real) (x : real) : (term297 k x) = (term56 k x).
Proof. exact (MK_COMB (@lem1552161) (@lem1552160 k x)). Qed.
Lemma lem1552163 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552164 (k : real) (x : real) : (term295 k x) = (term57 k x).
Proof. exact (MK_COMB (@lem1552162 k x) (@lem1552163)). Qed.
Lemma lem1552165 (k : real) (x : real) (h1 : term193 k x) : term57 k x.
Proof. exact (EQ_MP (@lem1552164 k x) (@lem1552159 k x h1)). Qed.
Lemma lem1552166 (k : real) (x : real) (h1 : term193 k x) : term298 k x.
Proof. exact (conj (@lem1552165 k x h1) (@lem1552144 k x h1)). Qed.
Lemma lem1552168 (x : real) (y : real) : term269 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1552169 (k : real) (x : real) : term299 k x.
Proof. exact (@lem1552168 (term54 k x) (term53 k x)). Qed.
Lemma lem1552170 (k : real) (x : real) (h1 : term193 k x) : term300 k x.
Proof. exact (@lem1552169 k x (@lem1552166 k x h1)). Qed.
Lemma lem1552171 (k : real) (x : real) : (term301 k x) = (term302 k x).
Proof. exact (@lem1483480 (term42 k) k x (term42 x)). Qed.
Lemma lem1552172 (k : real) : (term274 k) = (term275 k).
Proof. exact (@lem1483440 term77 k). Qed.
Lemma lem1552174 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1552175 : term277 = term38.
Proof. exact (@lem1552174 term82). Qed.
Lemma lem1552176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552177 : term278 = term279.
Proof. exact (MK_COMB (@lem1552176) (@lem1552175)). Qed.
Lemma lem1552178 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1552179 (k : real) : (term275 k) = (term280 k).
Proof. exact (MK_COMB (@lem1552177) (@lem1552178 k)). Qed.
Lemma lem1552180 (k : real) : (term274 k) = (term280 k).
Proof. exact (TRANS (@lem1552172 k) (@lem1552179 k)). Qed.
Lemma lem1552181 (k : real) : (term280 k) = term38.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1552182 (k : real) : (term274 k) = term38.
Proof. exact (TRANS (@lem1552180 k) (@lem1552181 k)). Qed.
Lemma lem1552183 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1552184 (k : real) : (term281 k) = term282.
Proof. exact (MK_COMB (@lem1552183) (@lem1552182 k)). Qed.
Lemma lem1552185 (x : real) : (term303 x) = (term275 x).
Proof. exact (@lem1483442 term77 x). Qed.
Lemma lem1552187 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1552188 : term277 = term38.
Proof. exact (@lem1552187 term82). Qed.
Lemma lem1552189 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552190 : term278 = term279.
Proof. exact (MK_COMB (@lem1552189) (@lem1552188)). Qed.
Lemma lem1552191 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1552192 (x : real) : (term275 x) = (term280 x).
Proof. exact (MK_COMB (@lem1552190) (@lem1552191 x)). Qed.
Lemma lem1552193 (x : real) : (term303 x) = (term280 x).
Proof. exact (TRANS (@lem1552185 x) (@lem1552192 x)). Qed.
Lemma lem1552194 (x : real) : (term280 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1552195 (x : real) : (term303 x) = term38.
Proof. exact (TRANS (@lem1552193 x) (@lem1552194 x)). Qed.
Lemma lem1552196 (k : real) (x : real) : (term302 k x) = term283.
Proof. exact (MK_COMB (@lem1552184 k) (@lem1552195 x)). Qed.
Lemma lem1552197 (k : real) (x : real) : (term301 k x) = term283.
Proof. exact (TRANS (@lem1552171 k x) (@lem1552196 k x)). Qed.
Lemma lem1552198 : term283 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1552199 (k : real) (x : real) : (term301 k x) = term38.
Proof. exact (TRANS (@lem1552197 k x) (@lem1552198)). Qed.
Lemma lem1552200 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552201 (k : real) (x : real) : (term304 k x) = term285.
Proof. exact (MK_COMB (@lem1552200) (@lem1552199 k x)). Qed.
Lemma lem1552202 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552203 (k : real) (x : real) : (term300 k x) = term286.
Proof. exact (MK_COMB (@lem1552201 k x) (@lem1552202)). Qed.
Lemma lem1552204 (k : real) (x : real) (h1 : term193 k x) : term286.
Proof. exact (EQ_MP (@lem1552203 k x) (@lem1552170 k x h1)). Qed.
Lemma lem1552206 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552207 : term286 = term287.
Proof. exact (@lem1552206 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1552208 : term287 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1552209 : term286 = False.
Proof. exact (TRANS (@lem1552207) (@lem1552208)). Qed.
Lemma lem1552210 (k : real) (x : real) (h1 : term193 k x) : False.
Proof. exact (EQ_MP (@lem1552209) (@lem1552204 k x h1)). Qed.
Lemma lem1552211 (k : real) (x : real) (h1 : term248 k x) : term248 k x.
Proof. exact (h1). Qed.
Lemma lem1552212 (k : real) (x : real) (h1 : term248 k x) : term246 k x.
Proof. exact (proj2 (@lem1552211 k x h1)). Qed.
Lemma lem1552214 (k : real) (x : real) (h1 : term248 k x) : term98 k x.
Proof. exact (proj2 (@lem1552212 k x h1)). Qed.
Lemma lem1552215 (k : real) (x : real) (h1 : term248 k x) : term50 k x.
Proof. exact (proj1 (@lem1552212 k x h1)). Qed.
Lemma lem1552217 (k : real) (x : real) (h1 : term248 k x) : term91 k x.
Proof. exact (proj1 (@lem1552214 k x h1)). Qed.
Lemma lem1552219 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552220 : term253 = term254.
Proof. exact (@lem1552219 (NUMERAL 0) term82). Qed.
Lemma lem1552221 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1552222 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1552223 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1552222 h1) (fun h1 : term254 = True => @lem1552221)). Qed.
Lemma lem1552224 : term254 = True.
Proof. exact (EQ_MP (@lem1552223) (@lem1552221)). Qed.
Lemma lem1552225 : term253 = True.
Proof. exact (TRANS (@lem1552220) (@lem1552224)). Qed.
Lemma lem1552226 : True = term253.
Proof. exact (SYM (@lem1552225)). Qed.
Lemma lem1552227 : term253.
Proof. exact (EQ_MP (@lem1552226) (@lem0)). Qed.
Lemma lem1552228 (k : real) (x : real) (h1 : term248 k x) : term256 k x.
Proof. exact (conj (@lem1552227) (@lem1552217 k x h1)). Qed.
Lemma lem1552230 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1552231 (k : real) (x : real) : term258 k x.
Proof. exact (@lem1552230 term85 (real_add k x)). Qed.
Lemma lem1552232 (k : real) (x : real) (h1 : term248 k x) : term259 k x.
Proof. exact (@lem1552231 k x (@lem1552228 k x h1)). Qed.
Lemma lem1552233 (k : real) (x : real) : (term260 k x) = (real_add k x).
Proof. exact (@lem1483460 (real_add k x)). Qed.
Lemma lem1552234 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1552235 (k : real) (x : real) : (term261 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1552234) (@lem1552233 k x)). Qed.
Lemma lem1552236 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552237 (k : real) (x : real) : (term259 k x) = (term91 k x).
Proof. exact (MK_COMB (@lem1552235 k x) (@lem1552236)). Qed.
Lemma lem1552238 (k : real) (x : real) (h1 : term248 k x) : term91 k x.
Proof. exact (EQ_MP (@lem1552237 k x) (@lem1552232 k x h1)). Qed.
Lemma lem1552240 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552241 : term253 = term254.
Proof. exact (@lem1552240 (NUMERAL 0) term82). Qed.
Lemma lem1552242 : term255 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1552243 (h1 : term255 = (BIT1 0)) : term254 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1552244 : (term255 = (BIT1 0)) = (term254 = True).
Proof. exact (prop_ext (fun h1 : term255 = (BIT1 0) => @lem1552243 h1) (fun h1 : term254 = True => @lem1552242)). Qed.
Lemma lem1552245 : term254 = True.
Proof. exact (EQ_MP (@lem1552244) (@lem1552242)). Qed.
Lemma lem1552246 : term253 = True.
Proof. exact (TRANS (@lem1552241) (@lem1552245)). Qed.
Lemma lem1552247 : True = term253.
Proof. exact (SYM (@lem1552246)). Qed.
Lemma lem1552248 : term253.
Proof. exact (EQ_MP (@lem1552247) (@lem0)). Qed.
Lemma lem1552249 (k : real) (x : real) (h1 : term248 k x) : term262 k x.
Proof. exact (conj (@lem1552248) (@lem1552215 k x h1)). Qed.
Lemma lem1552251 (x : real) (y : real) : term263 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1552252 (k : real) (x : real) : term264 k x.
Proof. exact (@lem1552251 term85 (term47 k x)). Qed.
Lemma lem1552253 (k : real) (x : real) (h1 : term248 k x) : term265 k x.
Proof. exact (@lem1552252 k x (@lem1552249 k x h1)). Qed.
Lemma lem1552254 (k : real) (x : real) : (term266 k x) = (term47 k x).
Proof. exact (@lem1483460 (term47 k x)). Qed.
Lemma lem1552255 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552256 (k : real) (x : real) : (term267 k x) = (term49 k x).
Proof. exact (MK_COMB (@lem1552255) (@lem1552254 k x)). Qed.
Lemma lem1552257 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552258 (k : real) (x : real) : (term265 k x) = (term50 k x).
Proof. exact (MK_COMB (@lem1552256 k x) (@lem1552257)). Qed.
Lemma lem1552259 (k : real) (x : real) (h1 : term248 k x) : term50 k x.
Proof. exact (EQ_MP (@lem1552258 k x) (@lem1552253 k x h1)). Qed.
Lemma lem1552260 (k : real) (x : real) (h1 : term248 k x) : term268 k x.
Proof. exact (conj (@lem1552259 k x h1) (@lem1552238 k x h1)). Qed.
Lemma lem1552262 (x : real) (y : real) : term269 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1552263 (k : real) (x : real) : term270 k x.
Proof. exact (@lem1552262 (term47 k x) (real_add k x)). Qed.
Lemma lem1552264 (k : real) (x : real) (h1 : term248 k x) : term271 k x.
Proof. exact (@lem1552263 k x (@lem1552260 k x h1)). Qed.
Lemma lem1552265 (k : real) (x : real) : (term272 k x) = (term273 k x).
Proof. exact (@lem1483480 (term42 k) k (term42 x) x). Qed.
Lemma lem1552266 (k : real) : (term274 k) = (term275 k).
Proof. exact (@lem1483440 term77 k). Qed.
Lemma lem1552268 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1552269 : term277 = term38.
Proof. exact (@lem1552268 term82). Qed.
Lemma lem1552270 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552271 : term278 = term279.
Proof. exact (MK_COMB (@lem1552270) (@lem1552269)). Qed.
Lemma lem1552272 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1552273 (k : real) : (term275 k) = (term280 k).
Proof. exact (MK_COMB (@lem1552271) (@lem1552272 k)). Qed.
Lemma lem1552274 (k : real) : (term274 k) = (term280 k).
Proof. exact (TRANS (@lem1552266 k) (@lem1552273 k)). Qed.
Lemma lem1552275 (k : real) : (term280 k) = term38.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1552276 (k : real) : (term274 k) = term38.
Proof. exact (TRANS (@lem1552274 k) (@lem1552275 k)). Qed.
Lemma lem1552277 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1552278 (k : real) : (term281 k) = term282.
Proof. exact (MK_COMB (@lem1552277) (@lem1552276 k)). Qed.
Lemma lem1552279 (x : real) : (term274 x) = (term275 x).
Proof. exact (@lem1483440 term77 x). Qed.
Lemma lem1552281 (m : nat) : (term276 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1552282 : term277 = term38.
Proof. exact (@lem1552281 term82). Qed.
Lemma lem1552283 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552284 : term278 = term279.
Proof. exact (MK_COMB (@lem1552283) (@lem1552282)). Qed.
Lemma lem1552285 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1552286 (x : real) : (term275 x) = (term280 x).
Proof. exact (MK_COMB (@lem1552284) (@lem1552285 x)). Qed.
Lemma lem1552287 (x : real) : (term274 x) = (term280 x).
Proof. exact (TRANS (@lem1552279 x) (@lem1552286 x)). Qed.
Lemma lem1552288 (x : real) : (term280 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1552289 (x : real) : (term274 x) = term38.
Proof. exact (TRANS (@lem1552287 x) (@lem1552288 x)). Qed.
Lemma lem1552290 (k : real) (x : real) : (term273 k x) = term283.
Proof. exact (MK_COMB (@lem1552278 k) (@lem1552289 x)). Qed.
Lemma lem1552291 (k : real) (x : real) : (term272 k x) = term283.
Proof. exact (TRANS (@lem1552265 k x) (@lem1552290 k x)). Qed.
Lemma lem1552292 : term283 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1552293 (k : real) (x : real) : (term272 k x) = term38.
Proof. exact (TRANS (@lem1552291 k x) (@lem1552292)). Qed.
Lemma lem1552294 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552295 (k : real) (x : real) : (term284 k x) = term285.
Proof. exact (MK_COMB (@lem1552294) (@lem1552293 k x)). Qed.
Lemma lem1552296 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1552297 (k : real) (x : real) : (term271 k x) = term286.
Proof. exact (MK_COMB (@lem1552295 k x) (@lem1552296)). Qed.
Lemma lem1552298 (k : real) (x : real) (h1 : term248 k x) : term286.
Proof. exact (EQ_MP (@lem1552297 k x) (@lem1552264 k x h1)). Qed.
Lemma lem1552300 (n : nat) (m : nat) : (term252 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1552301 : term286 = term287.
Proof. exact (@lem1552300 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1552302 : term287 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1552303 : term286 = False.
Proof. exact (TRANS (@lem1552301) (@lem1552302)). Qed.
Lemma lem1552304 (k : real) (x : real) (h1 : term248 k x) : False.
Proof. exact (EQ_MP (@lem1552303) (@lem1552298 k x h1)). Qed.
Lemma lem1552305 (k : real) (x : real) (h1 : term249 k x) : False.
Proof. exact (or_elim (@lem1552116 k x h1) (fun h0 : term193 k x => @lem1552210 k x h0) (fun h0 : term248 k x => @lem1552304 k x h0)). Qed.
Lemma lem1552306 (k : real) (x : real) (h1 : term251 k x) : False.
Proof. exact (or_elim (@lem1551929 k x h1) (fun h0 : term180 k x => @lem1552115 k x h0) (fun h0 : term249 k x => @lem1552305 k x h0)). Qed.
Lemma lem1552307 (k : real) (x : real) (h1 : term160 k x) : term160 k x.
Proof. exact (h1). Qed.
Lemma lem1552308 (k : real) (x : real) (h1 : term160 k x) : term251 k x.
Proof. exact (EQ_MP (@lem1551928 k x) (@lem1552307 k x h1)). Qed.
Lemma lem1552309 (k : real) (x : real) (h1 : term160 k x) : (term251 k x) = False.
Proof. exact (prop_ext (fun h2 : term251 k x => @lem1552306 k x h2) (fun h2 : False => @lem1552308 k x h1)). Qed.
Lemma lem1552310 (k : real) (x : real) (h1 : term160 k x) : False.
Proof. exact (EQ_MP (@lem1552309 k x h1) (@lem1552308 k x h1)). Qed.
Lemma lem1552311 (x : real) (h1 : term162 x) : term162 x.
Proof. exact (h1). Qed.
Lemma lem1552312 (x : real) (h1 : term162 x) : False.
Proof. exact (ex_elim (@lem1552311 x h1) (fun k : real => fun h0 : term161 x k => @lem1552310 k x h0)). Qed.
Lemma lem1552313 (h1 : term164) : term164.
Proof. exact (h1). Qed.
Lemma lem1552314 (h1 : term164) : False.
Proof. exact (ex_elim (@lem1552313 h1) (fun x : real => fun h0 : term163 x => @lem1552312 x h0)). Qed.
Lemma lem1552315 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1552316 (h1 : term24) : term164.
Proof. exact (EQ_MP (@lem1551606) (@lem1552315 h1)). Qed.
Lemma lem1552317 (h1 : term24) : term164 = False.
Proof. exact (prop_ext (fun h2 : term164 => @lem1552314 h2) (fun h2 : False => @lem1552316 h1)). Qed.
Lemma lem1552318 (h1 : term24) : False.
Proof. exact (EQ_MP (@lem1552317 h1) (@lem1552316 h1)). Qed.
Lemma lem1552319 : term305.
Proof. exact (fun h0 : term24 => @lem1552318 h0). Qed.
Lemma lem1552320 : term306.
Proof. exact (@lem1386578 term307). Qed.
Lemma lem1552321 : term307.
Proof. exact (@lem1552320 (@lem1552319)). Qed.
