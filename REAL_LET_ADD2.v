Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LET_ADD2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1518040 (w : real) (y : real) (x : real) (z : real) : (term0 w y x z) = (term1 w y x z).
Proof. exact (@lem17362 (term2 w x y z) (term3 w y x z)). Qed.
Lemma lem1518041 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518042 (w : real) (y : real) (x : real) : (term6 w y x) = (term7 w y x).
Proof. exact (@lem1518041 (term8 w y x)). Qed.
Lemma lem1518043 (w : real) (y : real) (x : real) (z : real) : (term9 w y x z) = (term10 w y x z).
Proof. exact (eq_refl (term9 w y x z)). Qed.
Lemma lem1518044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518045 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term0 w y x z).
Proof. exact (MK_COMB (@lem1518044) (@lem1518043 w y x z)). Qed.
Lemma lem1518046 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term1 w y x z).
Proof. exact (TRANS (@lem1518045 w y x z) (@lem1518040 w y x z)). Qed.
Lemma lem1518047 (w : real) (y : real) (x : real) : (term12 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1518046 w y x z)). Qed.
Lemma lem1518048 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518049 (w : real) (y : real) (x : real) : (term7 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1518048) (@lem1518047 w y x)). Qed.
Lemma lem1518050 (w : real) (y : real) (x : real) : (term6 w y x) = (term14 w y x).
Proof. exact (TRANS (@lem1518042 w y x) (@lem1518049 w y x)). Qed.
Lemma lem1518051 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518052 (w : real) (x : real) : (term15 w x) = (term16 w x).
Proof. exact (@lem1518051 (term17 w x)). Qed.
Lemma lem1518053 (w : real) (y : real) (x : real) : (term18 w x y) = (term19 w y x).
Proof. exact (eq_refl (term18 w x y)). Qed.
Lemma lem1518054 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518055 (w : real) (y : real) (x : real) : (term20 w x y) = (term6 w y x).
Proof. exact (MK_COMB (@lem1518054) (@lem1518053 w y x)). Qed.
Lemma lem1518056 (w : real) (y : real) (x : real) : (term20 w x y) = (term14 w y x).
Proof. exact (TRANS (@lem1518055 w y x) (@lem1518050 w y x)). Qed.
Lemma lem1518057 (w : real) (x : real) : (term21 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1518056 w y x)). Qed.
Lemma lem1518058 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518059 (w : real) (x : real) : (term16 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1518058) (@lem1518057 w x)). Qed.
Lemma lem1518060 (w : real) (x : real) : (term15 w x) = (term23 w x).
Proof. exact (TRANS (@lem1518052 w x) (@lem1518059 w x)). Qed.
Lemma lem1518061 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518062 (w : real) : (term24 w) = (term25 w).
Proof. exact (@lem1518061 (term26 w)). Qed.
Lemma lem1518063 (w : real) (x : real) : (term27 w x) = (term28 w x).
Proof. exact (eq_refl (term27 w x)). Qed.
Lemma lem1518064 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518065 (w : real) (x : real) : (term29 w x) = (term15 w x).
Proof. exact (MK_COMB (@lem1518064) (@lem1518063 w x)). Qed.
Lemma lem1518066 (w : real) (x : real) : (term29 w x) = (term23 w x).
Proof. exact (TRANS (@lem1518065 w x) (@lem1518060 w x)). Qed.
Lemma lem1518067 (w : real) : (term30 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1518066 w x)). Qed.
Lemma lem1518068 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518069 (w : real) : (term25 w) = (term32 w).
Proof. exact (MK_COMB (@lem1518068) (@lem1518067 w)). Qed.
Lemma lem1518070 (w : real) : (term24 w) = (term32 w).
Proof. exact (TRANS (@lem1518062 w) (@lem1518069 w)). Qed.
Lemma lem1518071 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518072 : term33 = term34.
Proof. exact (@lem1518071 term35). Qed.
Lemma lem1518073 (w : real) : (term36 w) = (term37 w).
Proof. exact (eq_refl (term36 w)). Qed.
Lemma lem1518074 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518075 (w : real) : (term38 w) = (term24 w).
Proof. exact (MK_COMB (@lem1518074) (@lem1518073 w)). Qed.
Lemma lem1518076 (w : real) : (term38 w) = (term32 w).
Proof. exact (TRANS (@lem1518075 w) (@lem1518070 w)). Qed.
Lemma lem1518077 : term39 = term40.
Proof. exact (fun_ext (fun w : real => @lem1518076 w)). Qed.
Lemma lem1518078 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518079 : term34 = term41.
Proof. exact (MK_COMB (@lem1518078) (@lem1518077)). Qed.
Lemma lem1518081 : term33 = term41.
Proof. exact (TRANS (@lem1518072) (@lem1518079)). Qed.
Lemma lem1518092 (w : real) (y : real) (x : real) (z : real) : (term1 w y x z) = (term1 w y x z).
Proof. exact (eq_refl (term1 w y x z)). Qed.
Lemma lem1518093 (w : real) (y : real) (x : real) : (term13 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1518092 w y x z)). Qed.
Lemma lem1518094 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518095 (w : real) (y : real) (x : real) : (term14 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1518094) (@lem1518093 w y x)). Qed.
Lemma lem1518096 (w : real) (x : real) : (term22 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1518095 w y x)). Qed.
Lemma lem1518097 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518098 (w : real) (x : real) : (term23 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1518097) (@lem1518096 w x)). Qed.
Lemma lem1518099 (w : real) : (term31 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1518098 w x)). Qed.
Lemma lem1518100 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518101 (w : real) : (term32 w) = (term32 w).
Proof. exact (MK_COMB (@lem1518100) (@lem1518099 w)). Qed.
Lemma lem1518102 : term40 = term40.
Proof. exact (fun_ext (fun w : real => @lem1518101 w)). Qed.
Lemma lem1518103 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518104 : term41 = term41.
Proof. exact (MK_COMB (@lem1518103) (@lem1518102)). Qed.
Lemma lem1518105 : term33 = term41.
Proof. exact (TRANS (@lem1518081) (@lem1518104)). Qed.
Lemma lem1518106 (x : real) (w : real) : (real_le w x) = (term42 x w).
Proof. exact (@lem1483523 x w). Qed.
Lemma lem1518112 (x : real) (w : real) : (real_sub x w) = (term43 x w).
Proof. exact (@lem1483519 x w). Qed.
Lemma lem1518117 (w : real) (x : real) : (term43 x w) = (term44 w x).
Proof. exact (@lem1483488 (term45 w) x). Qed.
Lemma lem1518119 (w : real) (x : real) : (real_sub x w) = (term44 w x).
Proof. exact (TRANS (@lem1518112 x w) (@lem1518117 w x)). Qed.
Lemma lem1518120 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518121 (w : real) (x : real) : (term46 x w) = (term47 w x).
Proof. exact (MK_COMB (@lem1518120) (@lem1518119 w x)). Qed.
Lemma lem1518122 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518123 (w : real) (x : real) : (term42 x w) = (term49 w x).
Proof. exact (MK_COMB (@lem1518121 w x) (@lem1518122)). Qed.
Lemma lem1518124 (w : real) (x : real) : (real_le w x) = (term49 w x).
Proof. exact (TRANS (@lem1518106 x w) (@lem1518123 w x)). Qed.
Lemma lem1518125 (z : real) (y : real) : (real_lt y z) = (term50 z y).
Proof. exact (@lem1483521 z y). Qed.
Lemma lem1518131 (z : real) (y : real) : (real_sub z y) = (term43 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1518136 (y : real) (z : real) : (term43 z y) = (term44 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1518138 (y : real) (z : real) : (real_sub z y) = (term44 y z).
Proof. exact (TRANS (@lem1518131 z y) (@lem1518136 y z)). Qed.
Lemma lem1518139 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518140 (y : real) (z : real) : (term51 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1518139) (@lem1518138 y z)). Qed.
Lemma lem1518141 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518142 (y : real) (z : real) : (term50 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1518140 y z) (@lem1518141)). Qed.
Lemma lem1518143 (y : real) (z : real) : (real_lt y z) = (term53 y z).
Proof. exact (TRANS (@lem1518125 z y) (@lem1518142 y z)). Qed.
Lemma lem1518144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1518145 (w : real) (x : real) : (term54 w x) = (term55 w x).
Proof. exact (MK_COMB (@lem1518144) (@lem1518124 w x)). Qed.
Lemma lem1518146 (w : real) (x : real) (y : real) (z : real) : (term2 w x y z) = (term56 w x y z).
Proof. exact (MK_COMB (@lem1518145 w x) (@lem1518143 y z)). Qed.
Lemma lem1518147 (w : real) (y : real) (x : real) (z : real) : (term57 w y x z) = (term58 w y x z).
Proof. exact (@lem1483531 (real_add w y) (real_add x z)). Qed.
Lemma lem1518165 (w : real) (y : real) (x : real) (z : real) : (term59 w y x z) = (term60 w y x z).
Proof. exact (@lem1483519 (real_add w y) (real_add x z)). Qed.
Lemma lem1518172 (x : real) (z : real) : (term61 x z) = (term62 x z).
Proof. exact (@lem1483508 x term63 z). Qed.
Lemma lem1518173 (w : real) (y : real) : (term64 w y) = (term64 w y).
Proof. exact (eq_refl (term64 w y)). Qed.
Lemma lem1518174 (w : real) (y : real) (x : real) (z : real) : (term60 w y x z) = (term65 w y x z).
Proof. exact (MK_COMB (@lem1518173 w y) (@lem1518172 x z)). Qed.
Lemma lem1518175 (w : real) (y : real) (x : real) (z : real) : (term65 w y x z) = (term66 w y x z).
Proof. exact (@lem1483482 w y (term62 x z)). Qed.
Lemma lem1518180 (x : real) (y : real) (z : real) : (term67 y x z) = (term68 x y z).
Proof. exact (@lem1483484 (term45 x) y (term45 z)). Qed.
Lemma lem1518181 (w : real) : (real_add w) = (real_add w).
Proof. exact (eq_refl (real_add w)). Qed.
Lemma lem1518182 (w : real) (x : real) (y : real) (z : real) : (term66 w y x z) = (term69 w x y z).
Proof. exact (MK_COMB (@lem1518181 w) (@lem1518180 x y z)). Qed.
Lemma lem1518183 (w : real) (x : real) (y : real) (z : real) : (term65 w y x z) = (term69 w x y z).
Proof. exact (TRANS (@lem1518175 w y x z) (@lem1518182 w x y z)). Qed.
Lemma lem1518184 (w : real) (x : real) (y : real) (z : real) : (term60 w y x z) = (term69 w x y z).
Proof. exact (TRANS (@lem1518174 w y x z) (@lem1518183 w x y z)). Qed.
Lemma lem1518186 (w : real) (x : real) (y : real) (z : real) : (term59 w y x z) = (term69 w x y z).
Proof. exact (TRANS (@lem1518165 w y x z) (@lem1518184 w x y z)). Qed.
Lemma lem1518187 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518188 (w : real) (x : real) (y : real) (z : real) : (term70 w y x z) = (term71 w x y z).
Proof. exact (MK_COMB (@lem1518187) (@lem1518186 w x y z)). Qed.
Lemma lem1518189 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518190 (w : real) (x : real) (y : real) (z : real) : (term58 w y x z) = (term72 w x y z).
Proof. exact (MK_COMB (@lem1518188 w x y z) (@lem1518189)). Qed.
Lemma lem1518191 (w : real) (x : real) (y : real) (z : real) : (term57 w y x z) = (term72 w x y z).
Proof. exact (TRANS (@lem1518147 w y x z) (@lem1518190 w x y z)). Qed.
Lemma lem1518192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1518193 (w : real) (x : real) (y : real) (z : real) : (term73 w x y z) = (term74 w x y z).
Proof. exact (MK_COMB (@lem1518192) (@lem1518146 w x y z)). Qed.
Lemma lem1518194 (w : real) (x : real) (y : real) (z : real) : (term1 w y x z) = (term75 w x y z).
Proof. exact (MK_COMB (@lem1518193 w x y z) (@lem1518191 w x y z)). Qed.
Lemma lem1518195 (w : real) (x : real) (y : real) : (term13 w y x) = (term76 w x y).
Proof. exact (fun_ext (fun z : real => @lem1518194 w x y z)). Qed.
Lemma lem1518196 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518197 (w : real) (x : real) (y : real) : (term14 w y x) = (term77 w x y).
Proof. exact (MK_COMB (@lem1518196) (@lem1518195 w x y)). Qed.
Lemma lem1518198 (w : real) (x : real) : (term22 w x) = (term78 w x).
Proof. exact (fun_ext (fun y : real => @lem1518197 w x y)). Qed.
Lemma lem1518199 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518200 (w : real) (x : real) : (term23 w x) = (term79 w x).
Proof. exact (MK_COMB (@lem1518199) (@lem1518198 w x)). Qed.
Lemma lem1518201 (w : real) : (term31 w) = (term80 w).
Proof. exact (fun_ext (fun x : real => @lem1518200 w x)). Qed.
Lemma lem1518202 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518203 (w : real) : (term32 w) = (term81 w).
Proof. exact (MK_COMB (@lem1518202) (@lem1518201 w)). Qed.
Lemma lem1518204 : term40 = term82.
Proof. exact (fun_ext (fun w : real => @lem1518203 w)). Qed.
Lemma lem1518205 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518206 : term41 = term83.
Proof. exact (MK_COMB (@lem1518205) (@lem1518204)). Qed.
Lemma lem1518273 : term33 = term83.
Proof. exact (TRANS (@lem1518105) (@lem1518206)). Qed.
Lemma lem1518286 (w : real) (x : real) (y : real) (z : real) : (term75 w x y z) = (term75 w x y z).
Proof. exact (eq_refl (term75 w x y z)). Qed.
Lemma lem1518287 (w : real) (x : real) (y : real) : (term76 w x y) = (term76 w x y).
Proof. exact (fun_ext (fun z : real => @lem1518286 w x y z)). Qed.
Lemma lem1518288 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518289 (w : real) (x : real) (y : real) : (term77 w x y) = (term77 w x y).
Proof. exact (MK_COMB (@lem1518288) (@lem1518287 w x y)). Qed.
Lemma lem1518290 (w : real) (x : real) : (term78 w x) = (term78 w x).
Proof. exact (fun_ext (fun y : real => @lem1518289 w x y)). Qed.
Lemma lem1518291 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518292 (w : real) (x : real) : (term79 w x) = (term79 w x).
Proof. exact (MK_COMB (@lem1518291) (@lem1518290 w x)). Qed.
Lemma lem1518293 (w : real) : (term80 w) = (term80 w).
Proof. exact (fun_ext (fun x : real => @lem1518292 w x)). Qed.
Lemma lem1518294 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518295 (w : real) : (term81 w) = (term81 w).
Proof. exact (MK_COMB (@lem1518294) (@lem1518293 w)). Qed.
Lemma lem1518296 : term82 = term82.
Proof. exact (fun_ext (fun w : real => @lem1518295 w)). Qed.
Lemma lem1518297 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518298 : term83 = term83.
Proof. exact (MK_COMB (@lem1518297) (@lem1518296)). Qed.
Lemma lem1518299 : term33 = term83.
Proof. exact (TRANS (@lem1518273) (@lem1518298)). Qed.
Lemma lem1518303 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term75 w x y z.
Proof. exact (h1). Qed.
Lemma lem1518304 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term72 w x y z.
Proof. exact (proj2 (@lem1518303 w x y z h1)). Qed.
Lemma lem1518305 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term56 w x y z.
Proof. exact (proj1 (@lem1518303 w x y z h1)). Qed.
Lemma lem1518306 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term53 y z.
Proof. exact (proj2 (@lem1518305 w x y z h1)). Qed.
Lemma lem1518307 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term49 w x.
Proof. exact (proj1 (@lem1518305 w x y z h1)). Qed.
Lemma lem1518309 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518310 : term85 = term86.
Proof. exact (@lem1518309 (NUMERAL 0) term87). Qed.
Lemma lem1518311 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518312 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518313 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518312 h1) (fun h1 : term86 = True => @lem1518311)). Qed.
Lemma lem1518314 : term86 = True.
Proof. exact (EQ_MP (@lem1518313) (@lem1518311)). Qed.
Lemma lem1518315 : term85 = True.
Proof. exact (TRANS (@lem1518310) (@lem1518314)). Qed.
Lemma lem1518316 : True = term85.
Proof. exact (SYM (@lem1518315)). Qed.
Lemma lem1518317 : term85.
Proof. exact (EQ_MP (@lem1518316) (@lem0)). Qed.
Lemma lem1518318 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term89 w x.
Proof. exact (conj (@lem1518317) (@lem1518307 w x y z h1)). Qed.
Lemma lem1518320 (x : real) (y : real) : term90 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1518321 (w : real) (x : real) : term91 w x.
Proof. exact (@lem1518320 term92 (term44 w x)). Qed.
Lemma lem1518322 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term93 w x.
Proof. exact (@lem1518321 w x (@lem1518318 w x y z h1)). Qed.
Lemma lem1518323 (w : real) (x : real) : (term94 w x) = (term44 w x).
Proof. exact (@lem1483460 (term44 w x)). Qed.
Lemma lem1518324 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518325 (w : real) (x : real) : (term95 w x) = (term47 w x).
Proof. exact (MK_COMB (@lem1518324) (@lem1518323 w x)). Qed.
Lemma lem1518326 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518327 (w : real) (x : real) : (term93 w x) = (term49 w x).
Proof. exact (MK_COMB (@lem1518325 w x) (@lem1518326)). Qed.
Lemma lem1518328 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term49 w x.
Proof. exact (EQ_MP (@lem1518327 w x) (@lem1518322 w x y z h1)). Qed.
Lemma lem1518330 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518331 : term85 = term86.
Proof. exact (@lem1518330 (NUMERAL 0) term87). Qed.
Lemma lem1518332 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518333 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518334 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518333 h1) (fun h1 : term86 = True => @lem1518332)). Qed.
Lemma lem1518335 : term86 = True.
Proof. exact (EQ_MP (@lem1518334) (@lem1518332)). Qed.
Lemma lem1518336 : term85 = True.
Proof. exact (TRANS (@lem1518331) (@lem1518335)). Qed.
Lemma lem1518337 : True = term85.
Proof. exact (SYM (@lem1518336)). Qed.
Lemma lem1518338 : term85.
Proof. exact (EQ_MP (@lem1518337) (@lem0)). Qed.
Lemma lem1518339 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term96 w x y z.
Proof. exact (conj (@lem1518338) (@lem1518304 w x y z h1)). Qed.
Lemma lem1518341 (x : real) (y : real) : term90 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1518342 (w : real) (x : real) (y : real) (z : real) : term97 w x y z.
Proof. exact (@lem1518341 term92 (term69 w x y z)). Qed.
Lemma lem1518343 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term98 w x y z.
Proof. exact (@lem1518342 w x y z (@lem1518339 w x y z h1)). Qed.
Lemma lem1518344 (w : real) (x : real) (y : real) (z : real) : (term99 w x y z) = (term69 w x y z).
Proof. exact (@lem1483460 (term69 w x y z)). Qed.
Lemma lem1518345 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518346 (w : real) (x : real) (y : real) (z : real) : (term100 w x y z) = (term71 w x y z).
Proof. exact (MK_COMB (@lem1518345) (@lem1518344 w x y z)). Qed.
Lemma lem1518347 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518348 (w : real) (x : real) (y : real) (z : real) : (term98 w x y z) = (term72 w x y z).
Proof. exact (MK_COMB (@lem1518346 w x y z) (@lem1518347)). Qed.
Lemma lem1518349 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term72 w x y z.
Proof. exact (EQ_MP (@lem1518348 w x y z) (@lem1518343 w x y z h1)). Qed.
Lemma lem1518351 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518352 : term85 = term86.
Proof. exact (@lem1518351 (NUMERAL 0) term87). Qed.
Lemma lem1518353 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518354 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518355 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518354 h1) (fun h1 : term86 = True => @lem1518353)). Qed.
Lemma lem1518356 : term86 = True.
Proof. exact (EQ_MP (@lem1518355) (@lem1518353)). Qed.
Lemma lem1518357 : term85 = True.
Proof. exact (TRANS (@lem1518352) (@lem1518356)). Qed.
Lemma lem1518358 : True = term85.
Proof. exact (SYM (@lem1518357)). Qed.
Lemma lem1518359 : term85.
Proof. exact (EQ_MP (@lem1518358) (@lem0)). Qed.
Lemma lem1518360 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term101 y z.
Proof. exact (conj (@lem1518359) (@lem1518306 w x y z h1)). Qed.
Lemma lem1518362 (x : real) (y : real) : term102 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1518363 (y : real) (z : real) : term103 y z.
Proof. exact (@lem1518362 term92 (term44 y z)). Qed.
Lemma lem1518364 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term104 y z.
Proof. exact (@lem1518363 y z (@lem1518360 w x y z h1)). Qed.
Lemma lem1518365 (y : real) (z : real) : (term94 y z) = (term44 y z).
Proof. exact (@lem1483460 (term44 y z)). Qed.
Lemma lem1518366 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518367 (y : real) (z : real) : (term105 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1518366) (@lem1518365 y z)). Qed.
Lemma lem1518368 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518369 (y : real) (z : real) : (term104 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1518367 y z) (@lem1518368)). Qed.
Lemma lem1518370 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1518369 y z) (@lem1518364 w x y z h1)). Qed.
Lemma lem1518371 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term106 w x y z.
Proof. exact (conj (@lem1518370 w x y z h1) (@lem1518349 w x y z h1)). Qed.
Lemma lem1518373 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1518374 (w : real) (x : real) (y : real) (z : real) : term108 w x y z.
Proof. exact (@lem1518373 (term44 y z) (term69 w x y z)). Qed.
Lemma lem1518375 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term109 w x y z.
Proof. exact (@lem1518374 w x y z (@lem1518371 w x y z h1)). Qed.
Lemma lem1518376 (w : real) (x : real) (y : real) (z : real) : (term110 w x y z) = (term111 w x y z).
Proof. exact (@lem1483484 w (term44 y z) (term68 x y z)). Qed.
Lemma lem1518377 (x : real) (y : real) (z : real) : (term112 x y z) = (term113 x y z).
Proof. exact (@lem1483484 (term45 x) (term44 y z) (term43 y z)). Qed.
Lemma lem1518378 (y : real) (z : real) : (term114 y z) = (term115 y z).
Proof. exact (@lem1483480 (term45 y) y z (term45 z)). Qed.
Lemma lem1518379 (y : real) : (term116 y) = (term117 y).
Proof. exact (@lem1483440 term63 y). Qed.
Lemma lem1518381 (m : nat) : (term118 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518382 : term119 = term48.
Proof. exact (@lem1518381 term87). Qed.
Lemma lem1518383 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518384 : term120 = term121.
Proof. exact (MK_COMB (@lem1518383) (@lem1518382)). Qed.
Lemma lem1518385 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1518386 (y : real) : (term117 y) = (term122 y).
Proof. exact (MK_COMB (@lem1518384) (@lem1518385 y)). Qed.
Lemma lem1518387 (y : real) : (term116 y) = (term122 y).
Proof. exact (TRANS (@lem1518379 y) (@lem1518386 y)). Qed.
Lemma lem1518388 (y : real) : (term122 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1518389 (y : real) : (term116 y) = term48.
Proof. exact (TRANS (@lem1518387 y) (@lem1518388 y)). Qed.
Lemma lem1518390 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1518391 (y : real) : (term123 y) = term124.
Proof. exact (MK_COMB (@lem1518390) (@lem1518389 y)). Qed.
Lemma lem1518392 (z : real) : (term125 z) = (term117 z).
Proof. exact (@lem1483442 term63 z). Qed.
Lemma lem1518394 (m : nat) : (term118 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518395 : term119 = term48.
Proof. exact (@lem1518394 term87). Qed.
Lemma lem1518396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518397 : term120 = term121.
Proof. exact (MK_COMB (@lem1518396) (@lem1518395)). Qed.
Lemma lem1518398 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1518399 (z : real) : (term117 z) = (term122 z).
Proof. exact (MK_COMB (@lem1518397) (@lem1518398 z)). Qed.
Lemma lem1518400 (z : real) : (term125 z) = (term122 z).
Proof. exact (TRANS (@lem1518392 z) (@lem1518399 z)). Qed.
Lemma lem1518401 (z : real) : (term122 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1518402 (z : real) : (term125 z) = term48.
Proof. exact (TRANS (@lem1518400 z) (@lem1518401 z)). Qed.
Lemma lem1518403 (y : real) (z : real) : (term115 y z) = term126.
Proof. exact (MK_COMB (@lem1518391 y) (@lem1518402 z)). Qed.
Lemma lem1518404 (y : real) (z : real) : (term114 y z) = term126.
Proof. exact (TRANS (@lem1518378 y z) (@lem1518403 y z)). Qed.
Lemma lem1518405 : term126 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1518406 (y : real) (z : real) : (term114 y z) = term48.
Proof. exact (TRANS (@lem1518404 y z) (@lem1518405)). Qed.
Lemma lem1518407 (x : real) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1518408 (y : real) (z : real) (x : real) : (term113 x y z) = (term128 x).
Proof. exact (MK_COMB (@lem1518407 x) (@lem1518406 y z)). Qed.
Lemma lem1518409 (y : real) (z : real) (x : real) : (term112 x y z) = (term128 x).
Proof. exact (TRANS (@lem1518377 x y z) (@lem1518408 y z x)). Qed.
Lemma lem1518410 (x : real) : (term128 x) = (term45 x).
Proof. exact (@lem1483450 (term45 x)). Qed.
Lemma lem1518411 (y : real) (z : real) (x : real) : (term112 x y z) = (term45 x).
Proof. exact (TRANS (@lem1518409 y z x) (@lem1518410 x)). Qed.
Lemma lem1518412 (w : real) : (real_add w) = (real_add w).
Proof. exact (eq_refl (real_add w)). Qed.
Lemma lem1518413 (y : real) (z : real) (w : real) (x : real) : (term111 w x y z) = (term43 w x).
Proof. exact (MK_COMB (@lem1518412 w) (@lem1518411 y z x)). Qed.
Lemma lem1518414 (y : real) (z : real) (w : real) (x : real) : (term110 w x y z) = (term43 w x).
Proof. exact (TRANS (@lem1518376 w x y z) (@lem1518413 y z w x)). Qed.
Lemma lem1518415 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518416 (y : real) (z : real) (w : real) (x : real) : (term129 w x y z) = (term130 w x).
Proof. exact (MK_COMB (@lem1518415) (@lem1518414 y z w x)). Qed.
Lemma lem1518417 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518418 (y : real) (z : real) (w : real) (x : real) : (term109 w x y z) = (term131 w x).
Proof. exact (MK_COMB (@lem1518416 y z w x) (@lem1518417)). Qed.
Lemma lem1518419 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term131 w x.
Proof. exact (EQ_MP (@lem1518418 y z w x) (@lem1518375 w x y z h1)). Qed.
Lemma lem1518421 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518422 : term85 = term86.
Proof. exact (@lem1518421 (NUMERAL 0) term87). Qed.
Lemma lem1518423 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518424 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518425 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518424 h1) (fun h1 : term86 = True => @lem1518423)). Qed.
Lemma lem1518426 : term86 = True.
Proof. exact (EQ_MP (@lem1518425) (@lem1518423)). Qed.
Lemma lem1518427 : term85 = True.
Proof. exact (TRANS (@lem1518422) (@lem1518426)). Qed.
Lemma lem1518428 : True = term85.
Proof. exact (SYM (@lem1518427)). Qed.
Lemma lem1518429 : term85.
Proof. exact (EQ_MP (@lem1518428) (@lem0)). Qed.
Lemma lem1518430 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term132 w x.
Proof. exact (conj (@lem1518429) (@lem1518419 w x y z h1)). Qed.
Lemma lem1518432 (x : real) (y : real) : term102 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1518433 (w : real) (x : real) : term133 w x.
Proof. exact (@lem1518432 term92 (term43 w x)). Qed.
Lemma lem1518434 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term134 w x.
Proof. exact (@lem1518433 w x (@lem1518430 w x y z h1)). Qed.
Lemma lem1518435 (w : real) (x : real) : (term135 w x) = (term43 w x).
Proof. exact (@lem1483460 (term43 w x)). Qed.
Lemma lem1518436 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518437 (w : real) (x : real) : (term136 w x) = (term130 w x).
Proof. exact (MK_COMB (@lem1518436) (@lem1518435 w x)). Qed.
Lemma lem1518438 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518439 (w : real) (x : real) : (term134 w x) = (term131 w x).
Proof. exact (MK_COMB (@lem1518437 w x) (@lem1518438)). Qed.
Lemma lem1518440 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term131 w x.
Proof. exact (EQ_MP (@lem1518439 w x) (@lem1518434 w x y z h1)). Qed.
Lemma lem1518441 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term137 w x.
Proof. exact (conj (@lem1518440 w x y z h1) (@lem1518328 w x y z h1)). Qed.
Lemma lem1518443 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1518444 (w : real) (x : real) : term138 w x.
Proof. exact (@lem1518443 (term43 w x) (term44 w x)). Qed.
Lemma lem1518445 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term139 w x.
Proof. exact (@lem1518444 w x (@lem1518441 w x y z h1)). Qed.
Lemma lem1518446 (w : real) (x : real) : (term140 w x) = (term141 w x).
Proof. exact (@lem1483480 w (term45 w) (term45 x) x). Qed.
Lemma lem1518447 (w : real) : (term125 w) = (term117 w).
Proof. exact (@lem1483442 term63 w). Qed.
Lemma lem1518449 (m : nat) : (term118 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518450 : term119 = term48.
Proof. exact (@lem1518449 term87). Qed.
Lemma lem1518451 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518452 : term120 = term121.
Proof. exact (MK_COMB (@lem1518451) (@lem1518450)). Qed.
Lemma lem1518453 (w : real) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem1518454 (w : real) : (term117 w) = (term122 w).
Proof. exact (MK_COMB (@lem1518452) (@lem1518453 w)). Qed.
Lemma lem1518455 (w : real) : (term125 w) = (term122 w).
Proof. exact (TRANS (@lem1518447 w) (@lem1518454 w)). Qed.
Lemma lem1518456 (w : real) : (term122 w) = term48.
Proof. exact (@lem1483446 w). Qed.
Lemma lem1518457 (w : real) : (term125 w) = term48.
Proof. exact (TRANS (@lem1518455 w) (@lem1518456 w)). Qed.
Lemma lem1518458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1518459 (w : real) : (term142 w) = term124.
Proof. exact (MK_COMB (@lem1518458) (@lem1518457 w)). Qed.
Lemma lem1518460 (x : real) : (term116 x) = (term117 x).
Proof. exact (@lem1483440 term63 x). Qed.
Lemma lem1518462 (m : nat) : (term118 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518463 : term119 = term48.
Proof. exact (@lem1518462 term87). Qed.
Lemma lem1518464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518465 : term120 = term121.
Proof. exact (MK_COMB (@lem1518464) (@lem1518463)). Qed.
Lemma lem1518466 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1518467 (x : real) : (term117 x) = (term122 x).
Proof. exact (MK_COMB (@lem1518465) (@lem1518466 x)). Qed.
Lemma lem1518468 (x : real) : (term116 x) = (term122 x).
Proof. exact (TRANS (@lem1518460 x) (@lem1518467 x)). Qed.
Lemma lem1518469 (x : real) : (term122 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1518470 (x : real) : (term116 x) = term48.
Proof. exact (TRANS (@lem1518468 x) (@lem1518469 x)). Qed.
Lemma lem1518471 (w : real) (x : real) : (term141 w x) = term126.
Proof. exact (MK_COMB (@lem1518459 w) (@lem1518470 x)). Qed.
Lemma lem1518472 (w : real) (x : real) : (term140 w x) = term126.
Proof. exact (TRANS (@lem1518446 w x) (@lem1518471 w x)). Qed.
Lemma lem1518473 : term126 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1518474 (w : real) (x : real) : (term140 w x) = term48.
Proof. exact (TRANS (@lem1518472 w x) (@lem1518473)). Qed.
Lemma lem1518475 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518476 (w : real) (x : real) : (term143 w x) = term144.
Proof. exact (MK_COMB (@lem1518475) (@lem1518474 w x)). Qed.
Lemma lem1518477 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518478 (w : real) (x : real) : (term139 w x) = term145.
Proof. exact (MK_COMB (@lem1518476 w x) (@lem1518477)). Qed.
Lemma lem1518479 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term145.
Proof. exact (EQ_MP (@lem1518478 w x) (@lem1518445 w x y z h1)). Qed.
Lemma lem1518481 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518482 : term145 = term146.
Proof. exact (@lem1518481 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1518483 : term146 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1518484 : term145 = False.
Proof. exact (TRANS (@lem1518482) (@lem1518483)). Qed.
Lemma lem1518485 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : False.
Proof. exact (EQ_MP (@lem1518484) (@lem1518479 w x y z h1)). Qed.
Lemma lem1518487 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term75 w x y z.
Proof. exact (h1). Qed.
Lemma lem1518488 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : (term75 w x y z) = False.
Proof. exact (prop_ext (fun h2 : term75 w x y z => @lem1518485 w x y z h1) (fun h2 : False => @lem1518487 w x y z h1)). Qed.
Lemma lem1518489 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : False.
Proof. exact (EQ_MP (@lem1518488 w x y z h1) (@lem1518487 w x y z h1)). Qed.
Lemma lem1518490 (w : real) (x : real) (y : real) (h1 : term77 w x y) : term77 w x y.
Proof. exact (h1). Qed.
Lemma lem1518491 (w : real) (x : real) (y : real) (h1 : term77 w x y) : False.
Proof. exact (ex_elim (@lem1518490 w x y h1) (fun z : real => fun h0 : term76 w x y z => @lem1518489 w x y z h0)). Qed.
Lemma lem1518492 (w : real) (x : real) (h1 : term79 w x) : term79 w x.
Proof. exact (h1). Qed.
Lemma lem1518493 (w : real) (x : real) (h1 : term79 w x) : False.
Proof. exact (ex_elim (@lem1518492 w x h1) (fun y : real => fun h0 : term78 w x y => @lem1518491 w x y h0)). Qed.
Lemma lem1518494 (w : real) (h1 : term81 w) : term81 w.
Proof. exact (h1). Qed.
Lemma lem1518495 (w : real) (h1 : term81 w) : False.
Proof. exact (ex_elim (@lem1518494 w h1) (fun x : real => fun h0 : term80 w x => @lem1518493 w x h0)). Qed.
Lemma lem1518496 (h1 : term83) : term83.
Proof. exact (h1). Qed.
Lemma lem1518497 (h1 : term83) : False.
Proof. exact (ex_elim (@lem1518496 h1) (fun w : real => fun h0 : term82 w => @lem1518495 w h0)). Qed.
Lemma lem1518498 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1518499 (h1 : term33) : term83.
Proof. exact (EQ_MP (@lem1518299) (@lem1518498 h1)). Qed.
Lemma lem1518500 (h1 : term33) : term83 = False.
Proof. exact (prop_ext (fun h2 : term83 => @lem1518497 h2) (fun h2 : False => @lem1518499 h1)). Qed.
Lemma lem1518501 (h1 : term33) : False.
Proof. exact (EQ_MP (@lem1518500 h1) (@lem1518499 h1)). Qed.
Lemma lem1518502 : term147.
Proof. exact (fun h0 : term33 => @lem1518501 h0). Qed.
Lemma lem1518503 : term148.
Proof. exact (@lem1386578 term149). Qed.
Lemma lem1518504 : term149.
Proof. exact (@lem1518503 (@lem1518502)). Qed.
