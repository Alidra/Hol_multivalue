Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_ADDL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Lemma lem1509996 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17646 (term2 x y) (term3 x)). Qed.
Lemma lem1509997 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1509998 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1509997 (term8 x)). Qed.
Lemma lem1509999 (y : real) (x : real) : (term9 x y) = ((term2 x y) = (term3 x)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1510000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1510001 (y : real) (x : real) : (term10 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1510000) (@lem1509999 y x)). Qed.
Lemma lem1510002 (y : real) (x : real) : (term10 x y) = (term1 y x).
Proof. exact (TRANS (@lem1510001 y x) (@lem1509996 y x)). Qed.
Lemma lem1510003 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1510002 y x)). Qed.
Lemma lem1510004 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510005 (x : real) : (term7 x) = (term13 x).
Proof. exact (MK_COMB (@lem1510004) (@lem1510003 x)). Qed.
Lemma lem1510006 (x : real) : (term6 x) = (term13 x).
Proof. exact (TRANS (@lem1509998 x) (@lem1510005 x)). Qed.
Lemma lem1510007 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1510008 : term14 = term15.
Proof. exact (@lem1510007 term16). Qed.
Lemma lem1510009 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1510010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1510011 (x : real) : (term19 x) = (term6 x).
Proof. exact (MK_COMB (@lem1510010) (@lem1510009 x)). Qed.
Lemma lem1510012 (x : real) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem1510011 x) (@lem1510006 x)). Qed.
Lemma lem1510013 : term20 = term21.
Proof. exact (fun_ext (fun x : real => @lem1510012 x)). Qed.
Lemma lem1510014 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510015 : term15 = term22.
Proof. exact (MK_COMB (@lem1510014) (@lem1510013)). Qed.
Lemma lem1510017 : term14 = term22.
Proof. exact (TRANS (@lem1510008) (@lem1510015)). Qed.
Lemma lem1510034 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1510035 (x : real) : (term12 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1510034 y x)). Qed.
Lemma lem1510036 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510037 (x : real) : (term13 x) = (term13 x).
Proof. exact (MK_COMB (@lem1510036) (@lem1510035 x)). Qed.
Lemma lem1510038 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1510037 x)). Qed.
Lemma lem1510039 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510040 : term22 = term22.
Proof. exact (MK_COMB (@lem1510039) (@lem1510038)). Qed.
Lemma lem1510041 : term14 = term22.
Proof. exact (TRANS (@lem1510017) (@lem1510040)). Qed.
Lemma lem1510042 (x : real) (y : real) : (term2 x y) = (term23 x y).
Proof. exact (@lem1483523 (real_add x y) y). Qed.
Lemma lem1510054 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1483519 (real_add x y) y). Qed.
Lemma lem1510058 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (@lem1483482 x y (term27 y)). Qed.
Lemma lem1510059 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1510061 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1510062 : term33 = term32.
Proof. exact (@lem1510061 term34). Qed.
Lemma lem1510063 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1510064 : term35 = term36.
Proof. exact (MK_COMB (@lem1510063) (@lem1510062)). Qed.
Lemma lem1510065 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1510066 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1510064) (@lem1510065 y)). Qed.
Lemma lem1510067 (y : real) : (term28 y) = (term37 y).
Proof. exact (TRANS (@lem1510059 y) (@lem1510066 y)). Qed.
Lemma lem1510068 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1510069 (y : real) : (term28 y) = term32.
Proof. exact (TRANS (@lem1510067 y) (@lem1510068 y)). Qed.
Lemma lem1510070 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1510071 (y : real) (x : real) : (term26 x y) = (term38 x).
Proof. exact (MK_COMB (@lem1510070 x) (@lem1510069 y)). Qed.
Lemma lem1510072 (y : real) (x : real) : (term25 x y) = (term38 x).
Proof. exact (TRANS (@lem1510058 x y) (@lem1510071 y x)). Qed.
Lemma lem1510073 (x : real) : (term38 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1510075 (y : real) (x : real) : (term25 x y) = x.
Proof. exact (TRANS (@lem1510072 y x) (@lem1510073 x)). Qed.
Lemma lem1510077 (y : real) (x : real) : (term24 x y) = x.
Proof. exact (TRANS (@lem1510054 x y) (@lem1510075 y x)). Qed.
Lemma lem1510078 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1510079 (y : real) (x : real) : (term39 x y) = (real_ge x).
Proof. exact (MK_COMB (@lem1510078) (@lem1510077 y x)). Qed.
Lemma lem1510080 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510081 (y : real) (x : real) : (term23 x y) = (term40 x).
Proof. exact (MK_COMB (@lem1510079 y x) (@lem1510080)). Qed.
Lemma lem1510082 (y : real) (x : real) : (term2 x y) = (term40 x).
Proof. exact (TRANS (@lem1510042 x y) (@lem1510081 y x)). Qed.
Lemma lem1510083 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483533 term32 x). Qed.
Lemma lem1510089 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483519 term32 x). Qed.
Lemma lem1510094 (x : real) : (term44 x) = (term27 x).
Proof. exact (@lem1483448 (term27 x)). Qed.
Lemma lem1510096 (x : real) : (term43 x) = (term27 x).
Proof. exact (TRANS (@lem1510089 x) (@lem1510094 x)). Qed.
Lemma lem1510097 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510098 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1510097) (@lem1510096 x)). Qed.
Lemma lem1510099 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510100 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1510098 x) (@lem1510099)). Qed.
Lemma lem1510101 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1510083 x) (@lem1510100 x)). Qed.
Lemma lem1510102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1510103 (y : real) (x : real) : (term48 x y) = (term49 x).
Proof. exact (MK_COMB (@lem1510102) (@lem1510082 y x)). Qed.
Lemma lem1510104 (y : real) (x : real) : (term50 y x) = (term51 x).
Proof. exact (MK_COMB (@lem1510103 y x) (@lem1510101 x)). Qed.
Lemma lem1510105 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483533 y (real_add x y)). Qed.
Lemma lem1510117 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (@lem1483519 y (real_add x y)). Qed.
Lemma lem1510124 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (@lem1483508 x term30 y). Qed.
Lemma lem1510125 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1510126 (x : real) (y : real) : (term55 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1510125 y) (@lem1510124 x y)). Qed.
Lemma lem1510127 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1483484 (term27 x) y (term27 y)). Qed.
Lemma lem1510128 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1510130 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1510131 : term33 = term32.
Proof. exact (@lem1510130 term34). Qed.
Lemma lem1510132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1510133 : term35 = term36.
Proof. exact (MK_COMB (@lem1510132) (@lem1510131)). Qed.
Lemma lem1510134 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1510135 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1510133) (@lem1510134 y)). Qed.
Lemma lem1510136 (y : real) : (term28 y) = (term37 y).
Proof. exact (TRANS (@lem1510128 y) (@lem1510135 y)). Qed.
Lemma lem1510137 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1510138 (y : real) : (term28 y) = term32.
Proof. exact (TRANS (@lem1510136 y) (@lem1510137 y)). Qed.
Lemma lem1510139 (x : real) : (term60 x) = (term60 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1510140 (y : real) (x : real) : (term59 x y) = (term61 x).
Proof. exact (MK_COMB (@lem1510139 x) (@lem1510138 y)). Qed.
Lemma lem1510141 (y : real) (x : real) : (term58 x y) = (term61 x).
Proof. exact (TRANS (@lem1510127 x y) (@lem1510140 y x)). Qed.
Lemma lem1510142 (x : real) : (term61 x) = (term27 x).
Proof. exact (@lem1483450 (term27 x)). Qed.
Lemma lem1510143 (y : real) (x : real) : (term58 x y) = (term27 x).
Proof. exact (TRANS (@lem1510141 y x) (@lem1510142 x)). Qed.
Lemma lem1510144 (y : real) (x : real) : (term55 x y) = (term27 x).
Proof. exact (TRANS (@lem1510126 x y) (@lem1510143 y x)). Qed.
Lemma lem1510146 (y : real) (x : real) : (term54 x y) = (term27 x).
Proof. exact (TRANS (@lem1510117 x y) (@lem1510144 y x)). Qed.
Lemma lem1510147 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510148 (y : real) (x : real) : (term62 x y) = (term46 x).
Proof. exact (MK_COMB (@lem1510147) (@lem1510146 y x)). Qed.
Lemma lem1510149 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510150 (y : real) (x : real) : (term53 x y) = (term47 x).
Proof. exact (MK_COMB (@lem1510148 y x) (@lem1510149)). Qed.
Lemma lem1510151 (y : real) (x : real) : (term52 x y) = (term47 x).
Proof. exact (TRANS (@lem1510105 x y) (@lem1510150 y x)). Qed.
Lemma lem1510152 (x : real) : (term3 x) = (term63 x).
Proof. exact (@lem1483523 x term32). Qed.
Lemma lem1510158 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1483519 x term32). Qed.
Lemma lem1510160 (x : nat) : (term66 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1510161 : term67 = term32.
Proof. exact (@lem1510160 term34). Qed.
Lemma lem1510162 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1510163 (x : real) : (term65 x) = (term38 x).
Proof. exact (MK_COMB (@lem1510162 x) (@lem1510161)). Qed.
Lemma lem1510164 (x : real) : (term38 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1510165 (x : real) : (term65 x) = x.
Proof. exact (TRANS (@lem1510163 x) (@lem1510164 x)). Qed.
Lemma lem1510167 (x : real) : (term64 x) = x.
Proof. exact (TRANS (@lem1510158 x) (@lem1510165 x)). Qed.
Lemma lem1510168 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1510169 (x : real) : (term68 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1510168) (@lem1510167 x)). Qed.
Lemma lem1510170 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510171 (x : real) : (term63 x) = (term40 x).
Proof. exact (MK_COMB (@lem1510169 x) (@lem1510170)). Qed.
Lemma lem1510172 (x : real) : (term3 x) = (term40 x).
Proof. exact (TRANS (@lem1510152 x) (@lem1510171 x)). Qed.
Lemma lem1510173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1510174 (y : real) (x : real) : (term69 x y) = (term70 x).
Proof. exact (MK_COMB (@lem1510173) (@lem1510151 y x)). Qed.
Lemma lem1510175 (y : real) (x : real) : (term71 y x) = (term72 x).
Proof. exact (MK_COMB (@lem1510174 y x) (@lem1510172 x)). Qed.
Lemma lem1510176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510177 (y : real) (x : real) : (term73 y x) = (term74 x).
Proof. exact (MK_COMB (@lem1510176) (@lem1510104 y x)). Qed.
Lemma lem1510178 (y : real) (x : real) : (term1 y x) = (term75 x).
Proof. exact (MK_COMB (@lem1510177 y x) (@lem1510175 y x)). Qed.
Lemma lem1510179 (x : real) : (term12 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1510178 y x)). Qed.
Lemma lem1510180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510181 (x : real) : (term13 x) = (term77 x).
Proof. exact (MK_COMB (@lem1510180) (@lem1510179 x)). Qed.
Lemma lem1510182 : term21 = term78.
Proof. exact (fun_ext (fun x : real => @lem1510181 x)). Qed.
Lemma lem1510183 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510184 : term22 = term79.
Proof. exact (MK_COMB (@lem1510183) (@lem1510182)). Qed.
Lemma lem1510185 : term14 = term79.
Proof. exact (TRANS (@lem1510041) (@lem1510184)). Qed.
Lemma lem1510191 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1510192 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1510191 real P Q). Qed.
Lemma lem1510193 (x : real) : (term84 x) = (term85 x).
Proof. exact (@lem1510192 (term86 x) (term87 x)). Qed.
Lemma lem1510194 (y : real) (x : real) : (term88 x y) = (term51 x).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1510195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510196 (y : real) (x : real) : (term89 x y) = (term74 x).
Proof. exact (MK_COMB (@lem1510195) (@lem1510194 y x)). Qed.
Lemma lem1510197 (y : real) (x : real) : (term90 x y) = (term72 x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1510198 (y : real) (x : real) : (term91 x y) = (term75 x).
Proof. exact (MK_COMB (@lem1510196 y x) (@lem1510197 y x)). Qed.
Lemma lem1510199 (x : real) : (term92 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1510198 y x)). Qed.
Lemma lem1510200 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510201 (x : real) : (term84 x) = (term77 x).
Proof. exact (MK_COMB (@lem1510200) (@lem1510199 x)). Qed.
Lemma lem1510202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1510203 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1510202) (@lem1510201 x)). Qed.
Lemma lem1510204 (y : real) (x : real) : (term88 x y) = (term51 x).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1510205 (x : real) : (term95 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1510204 y x)). Qed.
Lemma lem1510206 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510207 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1510206) (@lem1510205 x)). Qed.
Lemma lem1510208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510209 (x : real) : (term98 x) = (term99 x).
Proof. exact (MK_COMB (@lem1510208) (@lem1510207 x)). Qed.
Lemma lem1510210 (y : real) (x : real) : (term90 x y) = (term72 x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1510211 (x : real) : (term100 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1510210 y x)). Qed.
Lemma lem1510212 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510213 (x : real) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1510212) (@lem1510211 x)). Qed.
Lemma lem1510214 (x : real) : (term85 x) = (term103 x).
Proof. exact (MK_COMB (@lem1510209 x) (@lem1510213 x)). Qed.
Lemma lem1510215 (x : real) : ((term84 x) = (term85 x)) = ((term77 x) = (term103 x)).
Proof. exact (MK_COMB (@lem1510203 x) (@lem1510214 x)). Qed.
Lemma lem1510216 (x : real) : (term77 x) = (term103 x).
Proof. exact (EQ_MP (@lem1510215 x) (@lem1510193 x)). Qed.
Lemma lem1510218 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1510219 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem1510218 real P Q). Qed.
Lemma lem1510220 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1510219 (term40 x) (term110 x)). Qed.
Lemma lem1510221 (y : real) (x : real) : (term111 x y) = (term47 x).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1510222 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1510223 (y : real) (x : real) : (term112 x y) = (term51 x).
Proof. exact (MK_COMB (@lem1510222 x) (@lem1510221 y x)). Qed.
Lemma lem1510224 (x : real) : (term113 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1510223 y x)). Qed.
Lemma lem1510225 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510226 (x : real) : (term108 x) = (term97 x).
Proof. exact (MK_COMB (@lem1510225) (@lem1510224 x)). Qed.
Lemma lem1510227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1510228 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1510227) (@lem1510226 x)). Qed.
Lemma lem1510229 (y : real) (x : real) : (term111 x y) = (term47 x).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1510230 (x : real) : (term116 x) = (term110 x).
Proof. exact (fun_ext (fun y : real => @lem1510229 y x)). Qed.
Lemma lem1510231 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510232 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1510231) (@lem1510230 x)). Qed.
Lemma lem1510233 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1510234 (x : real) : (term109 x) = (term119 x).
Proof. exact (MK_COMB (@lem1510233 x) (@lem1510232 x)). Qed.
Lemma lem1510235 (x : real) : ((term108 x) = (term109 x)) = ((term97 x) = (term119 x)).
Proof. exact (MK_COMB (@lem1510228 x) (@lem1510234 x)). Qed.
Lemma lem1510236 (x : real) : (term97 x) = (term119 x).
Proof. exact (EQ_MP (@lem1510235 x) (@lem1510220 x)). Qed.
Lemma lem1510238 {A : Type'} (t : Prop) : (term120 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1510239 (t : Prop) : (term121 t) = t.
Proof. exact (@lem1510238 real t). Qed.
Lemma lem1510240 (x : real) : (term118 x) = (term47 x).
Proof. exact (@lem1510239 (term47 x)). Qed.
Lemma lem1510241 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1510242 (x : real) : (term119 x) = (term51 x).
Proof. exact (MK_COMB (@lem1510241 x) (@lem1510240 x)). Qed.
Lemma lem1510243 (x : real) : (term97 x) = (term51 x).
Proof. exact (TRANS (@lem1510236 x) (@lem1510242 x)). Qed.
Lemma lem1510244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510245 (x : real) : (term99 x) = (term74 x).
Proof. exact (MK_COMB (@lem1510244) (@lem1510243 x)). Qed.
Lemma lem1510247 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1510248 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem1510247 real P Q). Qed.
Lemma lem1510249 (x : real) : (term122 x) = (term123 x).
Proof. exact (@lem1510248 (term47 x) (term124 x)). Qed.
Lemma lem1510250 (y : real) (x : real) : (term125 x y) = (term40 x).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1510251 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1510252 (y : real) (x : real) : (term126 x y) = (term72 x).
Proof. exact (MK_COMB (@lem1510251 x) (@lem1510250 y x)). Qed.
Lemma lem1510253 (x : real) : (term127 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1510252 y x)). Qed.
Lemma lem1510254 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510255 (x : real) : (term122 x) = (term102 x).
Proof. exact (MK_COMB (@lem1510254) (@lem1510253 x)). Qed.
Lemma lem1510256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1510257 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1510256) (@lem1510255 x)). Qed.
Lemma lem1510258 (y : real) (x : real) : (term125 x y) = (term40 x).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1510259 (x : real) : (term130 x) = (term124 x).
Proof. exact (fun_ext (fun y : real => @lem1510258 y x)). Qed.
Lemma lem1510260 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510261 (x : real) : (term131 x) = (term132 x).
Proof. exact (MK_COMB (@lem1510260) (@lem1510259 x)). Qed.
Lemma lem1510262 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1510263 (x : real) : (term123 x) = (term133 x).
Proof. exact (MK_COMB (@lem1510262 x) (@lem1510261 x)). Qed.
Lemma lem1510264 (x : real) : ((term122 x) = (term123 x)) = ((term102 x) = (term133 x)).
Proof. exact (MK_COMB (@lem1510257 x) (@lem1510263 x)). Qed.
Lemma lem1510265 (x : real) : (term102 x) = (term133 x).
Proof. exact (EQ_MP (@lem1510264 x) (@lem1510249 x)). Qed.
Lemma lem1510267 {A : Type'} (t : Prop) : (term120 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1510268 (t : Prop) : (term121 t) = t.
Proof. exact (@lem1510267 real t). Qed.
Lemma lem1510269 (x : real) : (term132 x) = (term40 x).
Proof. exact (@lem1510268 (term40 x)). Qed.
Lemma lem1510270 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1510271 (x : real) : (term133 x) = (term72 x).
Proof. exact (MK_COMB (@lem1510270 x) (@lem1510269 x)). Qed.
Lemma lem1510272 (x : real) : (term102 x) = (term72 x).
Proof. exact (TRANS (@lem1510265 x) (@lem1510271 x)). Qed.
Lemma lem1510273 (x : real) : (term103 x) = (term75 x).
Proof. exact (MK_COMB (@lem1510245 x) (@lem1510272 x)). Qed.
Lemma lem1510274 (x : real) : (term77 x) = (term75 x).
Proof. exact (TRANS (@lem1510216 x) (@lem1510273 x)). Qed.
Lemma lem1510275 : term78 = term134.
Proof. exact (fun_ext (fun x : real => @lem1510274 x)). Qed.
Lemma lem1510276 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510277 : term79 = term135.
Proof. exact (MK_COMB (@lem1510276) (@lem1510275)). Qed.
Lemma lem1510279 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1510280 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1510279 real P Q). Qed.
Lemma lem1510281 : term136 = term137.
Proof. exact (@lem1510280 term138 term139). Qed.
Lemma lem1510282 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1510283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510284 (x : real) : (term141 x) = (term74 x).
Proof. exact (MK_COMB (@lem1510283) (@lem1510282 x)). Qed.
Lemma lem1510285 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1510286 (x : real) : (term143 x) = (term75 x).
Proof. exact (MK_COMB (@lem1510284 x) (@lem1510285 x)). Qed.
Lemma lem1510287 : term144 = term134.
Proof. exact (fun_ext (fun x : real => @lem1510286 x)). Qed.
Lemma lem1510288 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510289 : term136 = term135.
Proof. exact (MK_COMB (@lem1510288) (@lem1510287)). Qed.
Lemma lem1510290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1510291 : term145 = term146.
Proof. exact (MK_COMB (@lem1510290) (@lem1510289)). Qed.
Lemma lem1510292 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1510293 : term147 = term138.
Proof. exact (fun_ext (fun x : real => @lem1510292 x)). Qed.
Lemma lem1510294 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510295 : term148 = term149.
Proof. exact (MK_COMB (@lem1510294) (@lem1510293)). Qed.
Lemma lem1510296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510297 : term150 = term151.
Proof. exact (MK_COMB (@lem1510296) (@lem1510295)). Qed.
Lemma lem1510298 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1510299 : term152 = term139.
Proof. exact (fun_ext (fun x : real => @lem1510298 x)). Qed.
Lemma lem1510300 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510301 : term153 = term154.
Proof. exact (MK_COMB (@lem1510300) (@lem1510299)). Qed.
Lemma lem1510302 : term137 = term155.
Proof. exact (MK_COMB (@lem1510297) (@lem1510301)). Qed.
Lemma lem1510303 : (term136 = term137) = (term135 = term155).
Proof. exact (MK_COMB (@lem1510291) (@lem1510302)). Qed.
Lemma lem1510304 : term135 = term155.
Proof. exact (EQ_MP (@lem1510303) (@lem1510281)). Qed.
Lemma lem1510401 : term79 = term155.
Proof. exact (TRANS (@lem1510277) (@lem1510304)). Qed.
Lemma lem1510403 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1510404 (P : real -> Prop) (Q : real -> Prop) : (term83 P Q) = (term82 P Q).
Proof. exact (@lem1510403 real P Q). Qed.
Lemma lem1510405 : term137 = term136.
Proof. exact (@lem1510404 term138 term139). Qed.
Lemma lem1510406 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1510407 : term147 = term138.
Proof. exact (fun_ext (fun x : real => @lem1510406 x)). Qed.
Lemma lem1510408 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510409 : term148 = term149.
Proof. exact (MK_COMB (@lem1510408) (@lem1510407)). Qed.
Lemma lem1510410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510411 : term150 = term151.
Proof. exact (MK_COMB (@lem1510410) (@lem1510409)). Qed.
Lemma lem1510412 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1510413 : term152 = term139.
Proof. exact (fun_ext (fun x : real => @lem1510412 x)). Qed.
Lemma lem1510414 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510415 : term153 = term154.
Proof. exact (MK_COMB (@lem1510414) (@lem1510413)). Qed.
Lemma lem1510416 : term137 = term155.
Proof. exact (MK_COMB (@lem1510411) (@lem1510415)). Qed.
Lemma lem1510417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1510418 : term156 = term157.
Proof. exact (MK_COMB (@lem1510417) (@lem1510416)). Qed.
Lemma lem1510419 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1510420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510421 (x : real) : (term141 x) = (term74 x).
Proof. exact (MK_COMB (@lem1510420) (@lem1510419 x)). Qed.
Lemma lem1510422 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1510423 (x : real) : (term143 x) = (term75 x).
Proof. exact (MK_COMB (@lem1510421 x) (@lem1510422 x)). Qed.
Lemma lem1510424 : term144 = term134.
Proof. exact (fun_ext (fun x : real => @lem1510423 x)). Qed.
Lemma lem1510425 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510426 : term136 = term135.
Proof. exact (MK_COMB (@lem1510425) (@lem1510424)). Qed.
Lemma lem1510427 : (term137 = term136) = (term155 = term135).
Proof. exact (MK_COMB (@lem1510418) (@lem1510426)). Qed.
Lemma lem1510428 : term155 = term135.
Proof. exact (EQ_MP (@lem1510427) (@lem1510405)). Qed.
Lemma lem1510429 : term79 = term135.
Proof. exact (TRANS (@lem1510401) (@lem1510428)). Qed.
Lemma lem1510432 : term14 = term135.
Proof. exact (TRANS (@lem1510185) (@lem1510429)). Qed.
Lemma lem1510449 (x : real) : (term75 x) = (term75 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1510450 : term134 = term134.
Proof. exact (fun_ext (fun x : real => @lem1510449 x)). Qed.
Lemma lem1510451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510452 : term135 = term135.
Proof. exact (MK_COMB (@lem1510451) (@lem1510450)). Qed.
Lemma lem1510453 : term14 = term135.
Proof. exact (TRANS (@lem1510432) (@lem1510452)). Qed.
Lemma lem1510463 (x : real) (h1 : term75 x) : term75 x.
Proof. exact (h1). Qed.
Lemma lem1510464 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem1510465 (x : real) (h1 : term51 x) : term47 x.
Proof. exact (proj2 (@lem1510464 x h1)). Qed.
Lemma lem1510466 (x : real) (h1 : term51 x) : term40 x.
Proof. exact (proj1 (@lem1510464 x h1)). Qed.
Lemma lem1510468 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1510469 : term159 = term160.
Proof. exact (@lem1510468 (NUMERAL 0) term34). Qed.
Lemma lem1510470 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1510471 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1510472 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1510471 h1) (fun h1 : term160 = True => @lem1510470)). Qed.
Lemma lem1510473 : term160 = True.
Proof. exact (EQ_MP (@lem1510472) (@lem1510470)). Qed.
Lemma lem1510474 : term159 = True.
Proof. exact (TRANS (@lem1510469) (@lem1510473)). Qed.
Lemma lem1510475 : True = term159.
Proof. exact (SYM (@lem1510474)). Qed.
Lemma lem1510476 : term159.
Proof. exact (EQ_MP (@lem1510475) (@lem0)). Qed.
Lemma lem1510477 (x : real) (h1 : term51 x) : term162 x.
Proof. exact (conj (@lem1510476) (@lem1510466 x h1)). Qed.
Lemma lem1510479 (x : real) (y : real) : term163 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1510480 (x : real) : term164 x.
Proof. exact (@lem1510479 term165 x). Qed.
Lemma lem1510481 (x : real) (h1 : term51 x) : term166 x.
Proof. exact (@lem1510480 x (@lem1510477 x h1)). Qed.
Lemma lem1510482 (x : real) : (term167 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1510483 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1510484 (x : real) : (term168 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1510483) (@lem1510482 x)). Qed.
Lemma lem1510485 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510486 (x : real) : (term166 x) = (term40 x).
Proof. exact (MK_COMB (@lem1510484 x) (@lem1510485)). Qed.
Lemma lem1510487 (x : real) (h1 : term51 x) : term40 x.
Proof. exact (EQ_MP (@lem1510486 x) (@lem1510481 x h1)). Qed.
Lemma lem1510489 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1510490 : term159 = term160.
Proof. exact (@lem1510489 (NUMERAL 0) term34). Qed.
Lemma lem1510491 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1510492 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1510493 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1510492 h1) (fun h1 : term160 = True => @lem1510491)). Qed.
Lemma lem1510494 : term160 = True.
Proof. exact (EQ_MP (@lem1510493) (@lem1510491)). Qed.
Lemma lem1510495 : term159 = True.
Proof. exact (TRANS (@lem1510490) (@lem1510494)). Qed.
Lemma lem1510496 : True = term159.
Proof. exact (SYM (@lem1510495)). Qed.
Lemma lem1510497 : term159.
Proof. exact (EQ_MP (@lem1510496) (@lem0)). Qed.
Lemma lem1510498 (x : real) (h1 : term51 x) : term169 x.
Proof. exact (conj (@lem1510497) (@lem1510465 x h1)). Qed.
Lemma lem1510500 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1510501 (x : real) : term171 x.
Proof. exact (@lem1510500 term165 (term27 x)). Qed.
Lemma lem1510502 (x : real) (h1 : term51 x) : term172 x.
Proof. exact (@lem1510501 x (@lem1510498 x h1)). Qed.
Lemma lem1510503 (x : real) : (term173 x) = (term27 x).
Proof. exact (@lem1483460 (term27 x)). Qed.
Lemma lem1510504 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510505 (x : real) : (term174 x) = (term46 x).
Proof. exact (MK_COMB (@lem1510504) (@lem1510503 x)). Qed.
Lemma lem1510506 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510507 (x : real) : (term172 x) = (term47 x).
Proof. exact (MK_COMB (@lem1510505 x) (@lem1510506)). Qed.
Lemma lem1510508 (x : real) (h1 : term51 x) : term47 x.
Proof. exact (EQ_MP (@lem1510507 x) (@lem1510502 x h1)). Qed.
Lemma lem1510509 (x : real) (h1 : term51 x) : term72 x.
Proof. exact (conj (@lem1510508 x h1) (@lem1510487 x h1)). Qed.
Lemma lem1510511 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1510512 (x : real) : term176 x.
Proof. exact (@lem1510511 (term27 x) x). Qed.
Lemma lem1510513 (x : real) (h1 : term51 x) : term177 x.
Proof. exact (@lem1510512 x (@lem1510509 x h1)). Qed.
Lemma lem1510514 (x : real) : (term178 x) = (term29 x).
Proof. exact (@lem1483440 term30 x). Qed.
Lemma lem1510516 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1510517 : term33 = term32.
Proof. exact (@lem1510516 term34). Qed.
Lemma lem1510518 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1510519 : term35 = term36.
Proof. exact (MK_COMB (@lem1510518) (@lem1510517)). Qed.
Lemma lem1510520 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1510521 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1510519) (@lem1510520 x)). Qed.
Lemma lem1510522 (x : real) : (term178 x) = (term37 x).
Proof. exact (TRANS (@lem1510514 x) (@lem1510521 x)). Qed.
Lemma lem1510523 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1510524 (x : real) : (term178 x) = term32.
Proof. exact (TRANS (@lem1510522 x) (@lem1510523 x)). Qed.
Lemma lem1510525 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510526 (x : real) : (term179 x) = term180.
Proof. exact (MK_COMB (@lem1510525) (@lem1510524 x)). Qed.
Lemma lem1510527 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510528 (x : real) : (term177 x) = term181.
Proof. exact (MK_COMB (@lem1510526 x) (@lem1510527)). Qed.
Lemma lem1510529 (x : real) (h1 : term51 x) : term181.
Proof. exact (EQ_MP (@lem1510528 x) (@lem1510513 x h1)). Qed.
Lemma lem1510531 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1510532 : term181 = term182.
Proof. exact (@lem1510531 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1510533 : term182 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1510534 : term181 = False.
Proof. exact (TRANS (@lem1510532) (@lem1510533)). Qed.
Lemma lem1510535 (x : real) (h1 : term51 x) : False.
Proof. exact (EQ_MP (@lem1510534) (@lem1510529 x h1)). Qed.
Lemma lem1510536 (x : real) (h1 : term72 x) : term72 x.
Proof. exact (h1). Qed.
Lemma lem1510537 (x : real) (h1 : term72 x) : term40 x.
Proof. exact (proj2 (@lem1510536 x h1)). Qed.
Lemma lem1510538 (x : real) (h1 : term72 x) : term47 x.
Proof. exact (proj1 (@lem1510536 x h1)). Qed.
Lemma lem1510540 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1510541 : term159 = term160.
Proof. exact (@lem1510540 (NUMERAL 0) term34). Qed.
Lemma lem1510542 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1510543 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1510544 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1510543 h1) (fun h1 : term160 = True => @lem1510542)). Qed.
Lemma lem1510545 : term160 = True.
Proof. exact (EQ_MP (@lem1510544) (@lem1510542)). Qed.
Lemma lem1510546 : term159 = True.
Proof. exact (TRANS (@lem1510541) (@lem1510545)). Qed.
Lemma lem1510547 : True = term159.
Proof. exact (SYM (@lem1510546)). Qed.
Lemma lem1510548 : term159.
Proof. exact (EQ_MP (@lem1510547) (@lem0)). Qed.
Lemma lem1510549 (x : real) (h1 : term72 x) : term162 x.
Proof. exact (conj (@lem1510548) (@lem1510537 x h1)). Qed.
Lemma lem1510551 (x : real) (y : real) : term163 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1510552 (x : real) : term164 x.
Proof. exact (@lem1510551 term165 x). Qed.
Lemma lem1510553 (x : real) (h1 : term72 x) : term166 x.
Proof. exact (@lem1510552 x (@lem1510549 x h1)). Qed.
Lemma lem1510554 (x : real) : (term167 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1510555 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1510556 (x : real) : (term168 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1510555) (@lem1510554 x)). Qed.
Lemma lem1510557 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510558 (x : real) : (term166 x) = (term40 x).
Proof. exact (MK_COMB (@lem1510556 x) (@lem1510557)). Qed.
Lemma lem1510559 (x : real) (h1 : term72 x) : term40 x.
Proof. exact (EQ_MP (@lem1510558 x) (@lem1510553 x h1)). Qed.
Lemma lem1510561 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1510562 : term159 = term160.
Proof. exact (@lem1510561 (NUMERAL 0) term34). Qed.
Lemma lem1510563 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1510564 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1510565 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1510564 h1) (fun h1 : term160 = True => @lem1510563)). Qed.
Lemma lem1510566 : term160 = True.
Proof. exact (EQ_MP (@lem1510565) (@lem1510563)). Qed.
Lemma lem1510567 : term159 = True.
Proof. exact (TRANS (@lem1510562) (@lem1510566)). Qed.
Lemma lem1510568 : True = term159.
Proof. exact (SYM (@lem1510567)). Qed.
Lemma lem1510569 : term159.
Proof. exact (EQ_MP (@lem1510568) (@lem0)). Qed.
Lemma lem1510570 (x : real) (h1 : term72 x) : term169 x.
Proof. exact (conj (@lem1510569) (@lem1510538 x h1)). Qed.
Lemma lem1510572 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1510573 (x : real) : term171 x.
Proof. exact (@lem1510572 term165 (term27 x)). Qed.
Lemma lem1510574 (x : real) (h1 : term72 x) : term172 x.
Proof. exact (@lem1510573 x (@lem1510570 x h1)). Qed.
Lemma lem1510575 (x : real) : (term173 x) = (term27 x).
Proof. exact (@lem1483460 (term27 x)). Qed.
Lemma lem1510576 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510577 (x : real) : (term174 x) = (term46 x).
Proof. exact (MK_COMB (@lem1510576) (@lem1510575 x)). Qed.
Lemma lem1510578 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510579 (x : real) : (term172 x) = (term47 x).
Proof. exact (MK_COMB (@lem1510577 x) (@lem1510578)). Qed.
Lemma lem1510580 (x : real) (h1 : term72 x) : term47 x.
Proof. exact (EQ_MP (@lem1510579 x) (@lem1510574 x h1)). Qed.
Lemma lem1510581 (x : real) (h1 : term72 x) : term72 x.
Proof. exact (conj (@lem1510580 x h1) (@lem1510559 x h1)). Qed.
Lemma lem1510583 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1510584 (x : real) : term176 x.
Proof. exact (@lem1510583 (term27 x) x). Qed.
Lemma lem1510585 (x : real) (h1 : term72 x) : term177 x.
Proof. exact (@lem1510584 x (@lem1510581 x h1)). Qed.
Lemma lem1510586 (x : real) : (term178 x) = (term29 x).
Proof. exact (@lem1483440 term30 x). Qed.
Lemma lem1510588 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1510589 : term33 = term32.
Proof. exact (@lem1510588 term34). Qed.
Lemma lem1510590 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1510591 : term35 = term36.
Proof. exact (MK_COMB (@lem1510590) (@lem1510589)). Qed.
Lemma lem1510592 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1510593 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1510591) (@lem1510592 x)). Qed.
Lemma lem1510594 (x : real) : (term178 x) = (term37 x).
Proof. exact (TRANS (@lem1510586 x) (@lem1510593 x)). Qed.
Lemma lem1510595 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1510596 (x : real) : (term178 x) = term32.
Proof. exact (TRANS (@lem1510594 x) (@lem1510595 x)). Qed.
Lemma lem1510597 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510598 (x : real) : (term179 x) = term180.
Proof. exact (MK_COMB (@lem1510597) (@lem1510596 x)). Qed.
Lemma lem1510599 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510600 (x : real) : (term177 x) = term181.
Proof. exact (MK_COMB (@lem1510598 x) (@lem1510599)). Qed.
Lemma lem1510601 (x : real) (h1 : term72 x) : term181.
Proof. exact (EQ_MP (@lem1510600 x) (@lem1510585 x h1)). Qed.
Lemma lem1510603 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1510604 : term181 = term182.
Proof. exact (@lem1510603 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1510605 : term182 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1510606 : term181 = False.
Proof. exact (TRANS (@lem1510604) (@lem1510605)). Qed.
Lemma lem1510607 (x : real) (h1 : term72 x) : False.
Proof. exact (EQ_MP (@lem1510606) (@lem1510601 x h1)). Qed.
Lemma lem1510608 (x : real) (h1 : term75 x) : False.
Proof. exact (or_elim (@lem1510463 x h1) (fun h0 : term51 x => @lem1510535 x h0) (fun h0 : term72 x => @lem1510607 x h0)). Qed.
Lemma lem1510610 (x : real) (h1 : term75 x) : term75 x.
Proof. exact (h1). Qed.
Lemma lem1510611 (x : real) (h1 : term75 x) : (term75 x) = False.
Proof. exact (prop_ext (fun h2 : term75 x => @lem1510608 x h1) (fun h2 : False => @lem1510610 x h1)). Qed.
Lemma lem1510612 (x : real) (h1 : term75 x) : False.
Proof. exact (EQ_MP (@lem1510611 x h1) (@lem1510610 x h1)). Qed.
Lemma lem1510613 (h1 : term135) : term135.
Proof. exact (h1). Qed.
Lemma lem1510614 (h1 : term135) : False.
Proof. exact (ex_elim (@lem1510613 h1) (fun x : real => fun h0 : term134 x => @lem1510612 x h0)). Qed.
Lemma lem1510615 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1510616 (h1 : term14) : term135.
Proof. exact (EQ_MP (@lem1510453) (@lem1510615 h1)). Qed.
Lemma lem1510617 (h1 : term14) : term135 = False.
Proof. exact (prop_ext (fun h2 : term135 => @lem1510614 h2) (fun h2 : False => @lem1510616 h1)). Qed.
Lemma lem1510618 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1510617 h1) (@lem1510616 h1)). Qed.
Lemma lem1510619 : term183.
Proof. exact (fun h0 : term14 => @lem1510618 h0). Qed.
Lemma lem1510620 : term184.
Proof. exact (@lem1386578 term185). Qed.
Lemma lem1510621 : term185.
Proof. exact (@lem1510620 (@lem1510619)). Qed.
