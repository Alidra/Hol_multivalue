Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_EQ_1_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_INV_1_spec.
Require Import REAL_INV_INV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1592043 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1592044 : term1 = term2.
Proof. exact (@lem1592043 term1). Qed.
Lemma lem1592045 : term2 = term1.
Proof. exact (SYM (@lem1592044)). Qed.
Lemma lem1592046 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1592049 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1592050 : term5.
Proof. exact (fun h0 : term4 => @lem1592049 h0). Qed.
Lemma lem1592051 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1592052 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1592053 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1592051 h2 (@lem1592052 h1)). Qed.
Lemma lem1592054 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1592053 h1 h0). Qed.
Lemma lem1592055 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1592056 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1592054 h1 (@lem1592055 h2)). Qed.
Lemma lem1592057 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1592056 h0 h1). Qed.
Lemma lem1592058 : term7.
Proof. exact (fun h0 : term5 => @lem1592057 h0). Qed.
Lemma lem1592061 : term5.
Proof. exact (@lem1592058 (@lem1592050)). Qed.
Lemma lem1592071 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1592072 : term8 = term9.
Proof. exact (@lem1592071 term10). Qed.
Lemma lem1592077 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1592078 : term12 = term13.
Proof. exact (MK_COMB (@lem1592077) (@lem1592072)). Qed.
Lemma lem1592081 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1592088 : term4 = term15.
Proof. exact (MK_COMB (@lem1592081) (@lem1592078)). Qed.
Lemma lem1592089 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1592090 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1592089 x)). Qed.
Lemma lem1592091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1592092 : term10 = term10.
Proof. exact (MK_COMB (@lem1592091) (@lem1592090)). Qed.
Lemma lem1592093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1592094 : term9 = term9.
Proof. exact (MK_COMB (@lem1592093) (@lem1592092)). Qed.
Lemma lem1592097 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1592098 : term13 = term13.
Proof. exact (MK_COMB (@lem1592097) (@lem1592094)). Qed.
Lemma lem1592103 (x : real) : (((real_inv x) = term18) = (x = term18)) = (((real_inv x) = term18) = (x = term18)).
Proof. exact (eq_refl (((real_inv x) = term18) = (x = term18))). Qed.
Lemma lem1592104 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1592103 x)). Qed.
Lemma lem1592105 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1592106 : term1 = term1.
Proof. exact (MK_COMB (@lem1592105) (@lem1592104)). Qed.
Lemma lem1592107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1592108 : term3 = term3.
Proof. exact (MK_COMB (@lem1592107) (@lem1592106)). Qed.
Lemma lem1592109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1592110 : term14 = term14.
Proof. exact (MK_COMB (@lem1592109) (@lem1592108)). Qed.
Lemma lem1592111 : term15 = term15.
Proof. exact (MK_COMB (@lem1592110) (@lem1592098)). Qed.
Lemma lem1592130 : term4 = term15.
Proof. exact (TRANS (@lem1592088) (@lem1592111)). Qed.
Lemma lem1592131 : term15 = term4.
Proof. exact (SYM (@lem1592130)). Qed.
Lemma lem1592132 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1592134 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1592149 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem17646 ((real_inv x) = term18) (x = term18)). Qed.
Lemma lem1592150 (P : real -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1592151 : term3 = term24.
Proof. exact (@lem1592150 term19). Qed.
Lemma lem1592152 (x : real) : (term25 x) = (((real_inv x) = term18) = (x = term18)).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1592153 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1592154 (x : real) : (term26 x) = (term20 x).
Proof. exact (MK_COMB (@lem1592153) (@lem1592152 x)). Qed.
Lemma lem1592155 (x : real) : (term26 x) = (term21 x).
Proof. exact (TRANS (@lem1592154 x) (@lem1592149 x)). Qed.
Lemma lem1592156 : term27 = term28.
Proof. exact (fun_ext (fun x : real => @lem1592155 x)). Qed.
Lemma lem1592157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1592158 : term24 = term29.
Proof. exact (MK_COMB (@lem1592157) (@lem1592156)). Qed.
Lemma lem1592159 : term3 = term29.
Proof. exact (TRANS (@lem1592151) (@lem1592158)). Qed.
Lemma lem1592161 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term30 A P Q) = (term31 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1592162 (P : real -> Prop) (Q : real -> Prop) : (term32 P Q) = (term33 P Q).
Proof. exact (@lem1592161 real P Q). Qed.
Lemma lem1592163 : term34 = term35.
Proof. exact (@lem1592162 term36 term37). Qed.
Lemma lem1592164 (x : real) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1592165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1592166 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1592165) (@lem1592164 x)). Qed.
Lemma lem1592167 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1592168 (x : real) : (term44 x) = (term21 x).
Proof. exact (MK_COMB (@lem1592166 x) (@lem1592167 x)). Qed.
Lemma lem1592169 : term45 = term28.
Proof. exact (fun_ext (fun x : real => @lem1592168 x)). Qed.
Lemma lem1592170 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1592171 : term34 = term29.
Proof. exact (MK_COMB (@lem1592170) (@lem1592169)). Qed.
Lemma lem1592172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1592173 : term46 = term47.
Proof. exact (MK_COMB (@lem1592172) (@lem1592171)). Qed.
Lemma lem1592174 (x : real) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1592175 : term48 = term36.
Proof. exact (fun_ext (fun x : real => @lem1592174 x)). Qed.
Lemma lem1592176 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1592177 : term49 = term50.
Proof. exact (MK_COMB (@lem1592176) (@lem1592175)). Qed.
Lemma lem1592178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1592179 : term51 = term52.
Proof. exact (MK_COMB (@lem1592178) (@lem1592177)). Qed.
Lemma lem1592180 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1592181 : term53 = term37.
Proof. exact (fun_ext (fun x : real => @lem1592180 x)). Qed.
Lemma lem1592182 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1592183 : term54 = term55.
Proof. exact (MK_COMB (@lem1592182) (@lem1592181)). Qed.
Lemma lem1592184 : term35 = term56.
Proof. exact (MK_COMB (@lem1592179) (@lem1592183)). Qed.
Lemma lem1592185 : (term34 = term35) = (term29 = term56).
Proof. exact (MK_COMB (@lem1592173) (@lem1592184)). Qed.
Lemma lem1592186 : term29 = term56.
Proof. exact (EQ_MP (@lem1592185) (@lem1592163)). Qed.
Lemma lem1592284 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term31 A P Q) = (term30 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1592285 (P : real -> Prop) (Q : real -> Prop) : (term33 P Q) = (term32 P Q).
Proof. exact (@lem1592284 real P Q). Qed.
Lemma lem1592286 : term35 = term34.
Proof. exact (@lem1592285 term36 term37). Qed.
Lemma lem1592287 (x : real) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1592288 : term48 = term36.
Proof. exact (fun_ext (fun x : real => @lem1592287 x)). Qed.
Lemma lem1592289 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1592290 : term49 = term50.
Proof. exact (MK_COMB (@lem1592289) (@lem1592288)). Qed.
Lemma lem1592291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1592292 : term51 = term52.
Proof. exact (MK_COMB (@lem1592291) (@lem1592290)). Qed.
Lemma lem1592293 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1592294 : term53 = term37.
Proof. exact (fun_ext (fun x : real => @lem1592293 x)). Qed.
Lemma lem1592295 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1592296 : term54 = term55.
Proof. exact (MK_COMB (@lem1592295) (@lem1592294)). Qed.
Lemma lem1592297 : term35 = term56.
Proof. exact (MK_COMB (@lem1592292) (@lem1592296)). Qed.
Lemma lem1592298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1592299 : term57 = term58.
Proof. exact (MK_COMB (@lem1592298) (@lem1592297)). Qed.
Lemma lem1592300 (x : real) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1592301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1592302 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1592301) (@lem1592300 x)). Qed.
Lemma lem1592303 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1592304 (x : real) : (term44 x) = (term21 x).
Proof. exact (MK_COMB (@lem1592302 x) (@lem1592303 x)). Qed.
Lemma lem1592305 : term45 = term28.
Proof. exact (fun_ext (fun x : real => @lem1592304 x)). Qed.
Lemma lem1592306 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1592307 : term34 = term29.
Proof. exact (MK_COMB (@lem1592306) (@lem1592305)). Qed.
Lemma lem1592308 : (term35 = term34) = (term56 = term29).
Proof. exact (MK_COMB (@lem1592299) (@lem1592307)). Qed.
Lemma lem1592309 : term56 = term29.
Proof. exact (EQ_MP (@lem1592308) (@lem1592286)). Qed.
Lemma lem1592310 : term29 = term29.
Proof. exact (TRANS (@lem1592186) (@lem1592309)). Qed.
Lemma lem1592311 : term3 = term29.
Proof. exact (TRANS (@lem1592159) (@lem1592310)). Qed.
Lemma lem1592312 (h1 : term3) : term29.
Proof. exact (EQ_MP (@lem1592311) (@lem1592132 h1)). Qed.
Lemma lem1592318 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592319 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1592320 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1592319 x)). Qed.
Lemma lem1592321 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1592330 : term10 = term10.
Proof. exact (MK_COMB (@lem1592321) (@lem1592320)). Qed.
Lemma lem1592331 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1592330) (@lem1592134 h1)). Qed.
Lemma lem1592352 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592361 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1592362 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1592361 x)). Qed.
Lemma lem1592363 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1592364 : term10 = term10.
Proof. exact (MK_COMB (@lem1592363) (@lem1592362)). Qed.
Lemma lem1592365 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1592364) (@lem1592331 h1)). Qed.
Lemma lem1592427 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (h1). Qed.
Lemma lem1592428 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1592429 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1592437 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592439 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1592440 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1592439 x)). Qed.
Lemma lem1592441 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1592443 : term10 = term10.
Proof. exact (MK_COMB (@lem1592441) (@lem1592440)). Qed.
Lemma lem1592444 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1592443) (@lem1592365 h1)). Qed.
Lemma lem1592456 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592472 (_25157 : real) (h1 : term10) : term60 _25157.
Proof. exact (@lem1592444 h1 _25157). Qed.
Lemma lem1592473 (_25157 : real) : (term60 _25157) = ((term16 _25157) = _25157).
Proof. exact (eq_refl (term60 _25157)). Qed.
Lemma lem1592479 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592485 (x : real) (h1 : term39 x) : term61 x.
Proof. exact (proj2 (@lem1592428 x h1)). Qed.
Lemma lem1592487 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592491 (x : real) (h1 : term43 x) : term62 x.
Proof. exact (proj1 (@lem1592429 x h1)). Qed.
Lemma lem1592493 (x : real) (h1 : term43 x) : x = term18.
Proof. exact (proj2 (@lem1592429 x h1)). Qed.
Lemma lem1592521 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592536 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem1592537 (x : real) (h1 : term43 x) : (term64 x) = term65.
Proof. exact (MK_COMB (@lem1592536) (@lem1592493 x h1)). Qed.
Lemma lem1592538 : term65 = term66.
Proof. exact (eq_refl term65). Qed.
Lemma lem1592539 (x : real) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1592540 (x : real) : ((term64 x) = term65) = ((term64 x) = term66).
Proof. exact (MK_COMB (@lem1592539 x) (@lem1592538)). Qed.
Lemma lem1592541 (x : real) : (term64 x) = (term62 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1592542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1592543 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1592542) (@lem1592541 x)). Qed.
Lemma lem1592544 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem1592545 (x : real) : ((term64 x) = term66) = ((term62 x) = term66).
Proof. exact (MK_COMB (@lem1592543 x) (@lem1592544)). Qed.
Lemma lem1592546 (x : real) : ((term64 x) = term65) = ((term62 x) = term66).
Proof. exact (TRANS (@lem1592540 x) (@lem1592545 x)). Qed.
Lemma lem1592547 (x : real) (h1 : term43 x) : (term62 x) = term66.
Proof. exact (EQ_MP (@lem1592546 x) (@lem1592537 x h1)). Qed.
Lemma lem1592548 (x : real) (h1 : term43 x) : term66.
Proof. exact (EQ_MP (@lem1592547 x h1) (@lem1592491 x h1)). Qed.
Lemma lem1592549 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1592550 (_25167 : real) (_25168 : real) (h1 : _25167 = _25168) : _25167 = _25168.
Proof. exact (h1). Qed.
Lemma lem1592551 (_25167 : real) (_25168 : real) (h1 : _25167 = _25168) : (real_inv _25167) = (real_inv _25168).
Proof. exact (MK_COMB (@lem1592549) (@lem1592550 _25167 _25168 h1)). Qed.
Lemma lem1592552 (_25167 : real) (_25168 : real) : term69 _25167 _25168.
Proof. exact (fun h0 : _25167 = _25168 => @lem1592551 _25167 _25168 h0). Qed.
Lemma lem1592554 (a : Prop) (b : Prop) : (a -> b) = (term70 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1592555 (_25167 : real) (_25168 : real) : (term69 _25167 _25168) = (term71 _25167 _25168).
Proof. exact (@lem1592554 (_25167 = _25168) ((real_inv _25167) = (real_inv _25168))). Qed.
Lemma lem1592556 (_25167 : real) (_25168 : real) : term71 _25167 _25168.
Proof. exact (EQ_MP (@lem1592555 _25167 _25168) (@lem1592552 _25167 _25168)). Qed.
Lemma lem1592582 (x : real) (y : real) (z : real) : term72 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1592586 (x : real) (h1 : term39 x) : (real_inv x) = term18.
Proof. exact (proj1 (@lem1592428 x h1)). Qed.
Lemma lem1592587 (x : real) (h1 : term39 x) : term73 x.
Proof. exact (fun h0 : term62 x => @lem1592586 x h1). Qed.
Lemma lem1592589 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592590 (x : real) : (term73 x) = ((real_inv x) = term18).
Proof. exact (@lem1592589 ((real_inv x) = term18)). Qed.
Lemma lem1592591 (x : real) (h1 : term39 x) : (real_inv x) = term18.
Proof. exact (EQ_MP (@lem1592590 x) (@lem1592587 x h1)). Qed.
Lemma lem1592597 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1592598 (_25167 : real) (_25168 : real) : (term71 _25167 _25168) = (term75 _25167 _25168).
Proof. exact (@lem1592597 ((real_inv _25167) = (real_inv _25168)) (term76 _25167 _25168)). Qed.
Lemma lem1592608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1592609 (_25167 : real) (_25168 : real) : (term77 _25167 _25168) = (term78 _25167 _25168).
Proof. exact (MK_COMB (@lem1592608) (@lem1592598 _25167 _25168)). Qed.
Lemma lem1592619 (_25167 : real) (_25168 : real) : (term75 _25167 _25168) = (term75 _25167 _25168).
Proof. exact (eq_refl (term75 _25167 _25168)). Qed.
Lemma lem1592620 (_25167 : real) (_25168 : real) : ((term71 _25167 _25168) = (term75 _25167 _25168)) = ((term75 _25167 _25168) = (term75 _25167 _25168)).
Proof. exact (MK_COMB (@lem1592609 _25167 _25168) (@lem1592619 _25167 _25168)). Qed.
Lemma lem1592622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1592623 (x : Prop) : (x = x) = True.
Proof. exact (@lem1592622 Prop x). Qed.
Lemma lem1592624 (_25167 : real) (_25168 : real) : ((term75 _25167 _25168) = (term75 _25167 _25168)) = True.
Proof. exact (@lem1592623 (term75 _25167 _25168)). Qed.
Lemma lem1592625 (_25167 : real) (_25168 : real) : ((term71 _25167 _25168) = (term75 _25167 _25168)) = True.
Proof. exact (TRANS (@lem1592620 _25167 _25168) (@lem1592624 _25167 _25168)). Qed.
Lemma lem1592626 (_25167 : real) (_25168 : real) : True = ((term71 _25167 _25168) = (term75 _25167 _25168)).
Proof. exact (SYM (@lem1592625 _25167 _25168)). Qed.
Lemma lem1592627 (_25167 : real) (_25168 : real) : (term71 _25167 _25168) = (term75 _25167 _25168).
Proof. exact (EQ_MP (@lem1592626 _25167 _25168) (@lem0)). Qed.
Lemma lem1592628 (_25167 : real) (_25168 : real) : term75 _25167 _25168.
Proof. exact (EQ_MP (@lem1592627 _25167 _25168) (@lem1592556 _25167 _25168)). Qed.
Lemma lem1592630 (b : Prop) (a : Prop) : (a \/ b) = (term79 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1592631 (_25167 : real) (_25168 : real) : (term75 _25167 _25168) = (term80 _25167 _25168).
Proof. exact (@lem1592630 (term76 _25167 _25168) ((real_inv _25167) = (real_inv _25168))). Qed.
Lemma lem1592633 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1592634 (_25167 : real) (_25168 : real) : (term82 _25167 _25168) = (_25167 = _25168).
Proof. exact (@lem1592633 (_25167 = _25168)). Qed.
Lemma lem1592635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1592636 (_25167 : real) (_25168 : real) : (term83 _25167 _25168) = (term84 _25167 _25168).
Proof. exact (MK_COMB (@lem1592635) (@lem1592634 _25167 _25168)). Qed.
Lemma lem1592637 (_25167 : real) (_25168 : real) : ((real_inv _25167) = (real_inv _25168)) = ((real_inv _25167) = (real_inv _25168)).
Proof. exact (eq_refl ((real_inv _25167) = (real_inv _25168))). Qed.
Lemma lem1592638 (_25167 : real) (_25168 : real) : (term80 _25167 _25168) = (term69 _25167 _25168).
Proof. exact (MK_COMB (@lem1592636 _25167 _25168) (@lem1592637 _25167 _25168)). Qed.
Lemma lem1592639 (_25167 : real) (_25168 : real) : (term75 _25167 _25168) = (term69 _25167 _25168).
Proof. exact (TRANS (@lem1592631 _25167 _25168) (@lem1592638 _25167 _25168)). Qed.
Lemma lem1592642 (_25167 : real) (_25168 : real) : term69 _25167 _25168.
Proof. exact (EQ_MP (@lem1592639 _25167 _25168) (@lem1592628 _25167 _25168)). Qed.
Lemma lem1592643 (x : real) : term85 x.
Proof. exact (@lem1592642 (real_inv x) term18). Qed.
Lemma lem1592646 (x : real) (h1 : term39 x) : (term16 x) = term59.
Proof. exact (@lem1592643 x (@lem1592591 x h1)). Qed.
Lemma lem1592647 (x : real) (h1 : term39 x) : term86 x.
Proof. exact (fun h0 : term87 x => @lem1592646 x h1). Qed.
Lemma lem1592649 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592650 (x : real) : (term86 x) = ((term16 x) = term59).
Proof. exact (@lem1592649 ((term16 x) = term59)). Qed.
Lemma lem1592651 (x : real) (h1 : term39 x) : (term16 x) = term59.
Proof. exact (EQ_MP (@lem1592650 x) (@lem1592647 x h1)). Qed.
Lemma lem1592653 (_25157 : real) (h1 : term10) : (term16 _25157) = _25157.
Proof. exact (EQ_MP (@lem1592473 _25157) (@lem1592472 _25157 h1)). Qed.
Lemma lem1592654 (x : real) (h1 : term10) : (term16 x) = x.
Proof. exact (@lem1592653 x h1). Qed.
Lemma lem1592655 (x : real) (h1 : term10) : term88 x.
Proof. exact (fun h0 : term89 x => @lem1592654 x h1). Qed.
Lemma lem1592657 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592658 (x : real) : (term88 x) = ((term16 x) = x).
Proof. exact (@lem1592657 ((term16 x) = x)). Qed.
Lemma lem1592659 (x : real) (h1 : term10) : (term16 x) = x.
Proof. exact (EQ_MP (@lem1592658 x) (@lem1592655 x h1)). Qed.
Lemma lem1592677 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1592678 (y : real) (x : real) (z : real) : (term90 x y z) = (term91 y x z).
Proof. exact (@lem1592677 (y = z) (term76 x z)). Qed.
Lemma lem1592688 (x : real) (y : real) : (term92 x y) = (term92 x y).
Proof. exact (eq_refl (term92 x y)). Qed.
Lemma lem1592689 (y : real) (x : real) (z : real) : (term72 x y z) = (term93 y x z).
Proof. exact (MK_COMB (@lem1592688 x y) (@lem1592678 y x z)). Qed.
Lemma lem1592693 (q : Prop) (p : Prop) (r : Prop) : (term94 p q r) = (term94 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1592694 (y : real) (x : real) (z : real) : (term93 y x z) = (term95 y x z).
Proof. exact (@lem1592693 (y = z) (term76 x y) (term76 x z)). Qed.
Lemma lem1592716 (y : real) (x : real) (z : real) : (term72 x y z) = (term95 y x z).
Proof. exact (TRANS (@lem1592689 y x z) (@lem1592694 y x z)). Qed.
Lemma lem1592717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1592718 (y : real) (x : real) (z : real) : (term96 x y z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1592717) (@lem1592716 y x z)). Qed.
Lemma lem1592740 (y : real) (x : real) (z : real) : (term95 y x z) = (term95 y x z).
Proof. exact (eq_refl (term95 y x z)). Qed.
Lemma lem1592741 (y : real) (x : real) (z : real) : ((term72 x y z) = (term95 y x z)) = ((term95 y x z) = (term95 y x z)).
Proof. exact (MK_COMB (@lem1592718 y x z) (@lem1592740 y x z)). Qed.
Lemma lem1592743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1592744 (x : Prop) : (x = x) = True.
Proof. exact (@lem1592743 Prop x). Qed.
Lemma lem1592745 (y : real) (x : real) (z : real) : ((term95 y x z) = (term95 y x z)) = True.
Proof. exact (@lem1592744 (term95 y x z)). Qed.
Lemma lem1592746 (y : real) (x : real) (z : real) : ((term72 x y z) = (term95 y x z)) = True.
Proof. exact (TRANS (@lem1592741 y x z) (@lem1592745 y x z)). Qed.
Lemma lem1592747 (y : real) (x : real) (z : real) : True = ((term72 x y z) = (term95 y x z)).
Proof. exact (SYM (@lem1592746 y x z)). Qed.
Lemma lem1592748 (y : real) (x : real) (z : real) : (term72 x y z) = (term95 y x z).
Proof. exact (EQ_MP (@lem1592747 y x z) (@lem0)). Qed.
Lemma lem1592749 (y : real) (x : real) (z : real) : term95 y x z.
Proof. exact (EQ_MP (@lem1592748 y x z) (@lem1592582 x y z)). Qed.
Lemma lem1592751 (b : Prop) (a : Prop) : (a \/ b) = (term79 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1592752 (x : real) (y : real) (z : real) : (term95 y x z) = (term98 x y z).
Proof. exact (@lem1592751 (term99 y x z) (y = z)). Qed.
Lemma lem1592754 (a : Prop) (b : Prop) : (term100 a b) = (term101 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1592755 (y : real) (x : real) (z : real) : (term102 y x z) = (term103 y x z).
Proof. exact (@lem1592754 (term76 x y) (term76 x z)). Qed.
Lemma lem1592757 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1592758 (x : real) (y : real) : (term82 x y) = (x = y).
Proof. exact (@lem1592757 (x = y)). Qed.
Lemma lem1592759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1592760 (x : real) (y : real) : (term104 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem1592759) (@lem1592758 x y)). Qed.
Lemma lem1592762 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1592763 (x : real) (z : real) : (term82 x z) = (x = z).
Proof. exact (@lem1592762 (x = z)). Qed.
Lemma lem1592764 (y : real) (x : real) (z : real) : (term103 y x z) = (term106 y x z).
Proof. exact (MK_COMB (@lem1592760 x y) (@lem1592763 x z)). Qed.
Lemma lem1592765 (y : real) (x : real) (z : real) : (term102 y x z) = (term106 y x z).
Proof. exact (TRANS (@lem1592755 y x z) (@lem1592764 y x z)). Qed.
Lemma lem1592766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1592767 (y : real) (x : real) (z : real) : (term107 y x z) = (term108 y x z).
Proof. exact (MK_COMB (@lem1592766) (@lem1592765 y x z)). Qed.
Lemma lem1592768 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1592769 (x : real) (y : real) (z : real) : (term98 x y z) = (term109 x y z).
Proof. exact (MK_COMB (@lem1592767 y x z) (@lem1592768 y z)). Qed.
Lemma lem1592770 (x : real) (y : real) (z : real) : (term95 y x z) = (term109 x y z).
Proof. exact (TRANS (@lem1592752 x y z) (@lem1592769 x y z)). Qed.
Lemma lem1592772 (x : real) (h1 : term10) (h2 : term39 x) : term110 x.
Proof. exact (conj (@lem1592651 x h2) (@lem1592659 x h1)). Qed.
Lemma lem1592774 (x : real) (y : real) (z : real) : term109 x y z.
Proof. exact (EQ_MP (@lem1592770 x y z) (@lem1592749 y x z)). Qed.
Lemma lem1592775 (x : real) : term111 x.
Proof. exact (@lem1592774 (term16 x) term59 x). Qed.
Lemma lem1592778 (x : real) (h1 : term10) (h2 : term39 x) : term59 = x.
Proof. exact (@lem1592775 x (@lem1592772 x h1 h2)). Qed.
Lemma lem1592779 (x : real) (h1 : term10) (h2 : term39 x) : term112 x.
Proof. exact (fun h0 : term113 x => @lem1592778 x h1 h2). Qed.
Lemma lem1592781 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592782 (x : real) : (term112 x) = (term59 = x).
Proof. exact (@lem1592781 (term59 = x)). Qed.
Lemma lem1592783 (x : real) (h1 : term10) (h2 : term39 x) : term59 = x.
Proof. exact (EQ_MP (@lem1592782 x) (@lem1592779 x h1 h2)). Qed.
Lemma lem1592785 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592786 (h1 : term59 = term18) : term114.
Proof. exact (fun h0 : term66 => @lem1592785 h1). Qed.
Lemma lem1592788 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592789 : term114 = (term59 = term18).
Proof. exact (@lem1592788 (term59 = term18)). Qed.
Lemma lem1592790 (h1 : term59 = term18) : term59 = term18.
Proof. exact (EQ_MP (@lem1592789) (@lem1592786 h1)). Qed.
Lemma lem1592791 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : term115 x.
Proof. exact (conj (@lem1592783 x h1 h2) (@lem1592790 h3)). Qed.
Lemma lem1592793 (x : real) (y : real) (z : real) : term109 x y z.
Proof. exact (EQ_MP (@lem1592770 x y z) (@lem1592749 y x z)). Qed.
Lemma lem1592794 (x : real) : term116 x.
Proof. exact (@lem1592793 term59 x term18). Qed.
Lemma lem1592797 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : x = term18.
Proof. exact (@lem1592794 x (@lem1592791 x h1 h2 h3)). Qed.
Lemma lem1592798 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : term117 x.
Proof. exact (fun h0 : term61 x => @lem1592797 x h1 h2 h3). Qed.
Lemma lem1592800 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592801 (x : real) : (term117 x) = (x = term18).
Proof. exact (@lem1592800 (x = term18)). Qed.
Lemma lem1592802 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : x = term18.
Proof. exact (EQ_MP (@lem1592801 x) (@lem1592798 x h1 h2 h3)). Qed.
Lemma lem1592805 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1592807 (x : real) : (term61 x) = (term118 x).
Proof. exact (@lem1592805 (x = term18)). Qed.
Lemma lem1592810 (x : real) (h1 : term39 x) : term118 x.
Proof. exact (EQ_MP (@lem1592807 x) (@lem1592485 x h1)). Qed.
Lemma lem1592813 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : False.
Proof. exact (@lem1592810 x h2 (@lem1592802 x h1 h2 h3)). Qed.
Lemma lem1592814 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : term119.
Proof. exact (fun h0 : ~ False => @lem1592813 x h1 h2 h3). Qed.
Lemma lem1592816 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592817 : term119 = False.
Proof. exact (@lem1592816 False). Qed.
Lemma lem1592818 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592817) (@lem1592814 x h1 h2 h3)). Qed.
Lemma lem1592856 (h1 : term59 = term18) : term59 = term18.
Proof. exact (h1). Qed.
Lemma lem1592857 (h1 : term59 = term18) : term114.
Proof. exact (fun h0 : term66 => @lem1592856 h1). Qed.
Lemma lem1592859 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592860 : term114 = (term59 = term18).
Proof. exact (@lem1592859 (term59 = term18)). Qed.
Lemma lem1592861 (h1 : term59 = term18) : term59 = term18.
Proof. exact (EQ_MP (@lem1592860) (@lem1592857 h1)). Qed.
Lemma lem1592864 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1592866 : term66 = term120.
Proof. exact (@lem1592864 (term59 = term18)). Qed.
Lemma lem1592869 (x : real) (h1 : term43 x) : term120.
Proof. exact (EQ_MP (@lem1592866) (@lem1592548 x h1)). Qed.
Lemma lem1592872 (x : real) (h1 : term43 x) (h2 : term59 = term18) : False.
Proof. exact (@lem1592869 x h1 (@lem1592861 h2)). Qed.
Lemma lem1592873 (x : real) (h1 : term43 x) (h2 : term59 = term18) : term119.
Proof. exact (fun h0 : ~ False => @lem1592872 x h1 h2). Qed.
Lemma lem1592875 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1592876 : term119 = False.
Proof. exact (@lem1592875 False). Qed.
Lemma lem1592877 (x : real) (h1 : term43 x) (h2 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592876) (@lem1592873 x h1 h2)). Qed.
Lemma lem1592878 (x : real) (h1 : term43 x) (h2 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h3 : term59 = term18 => @lem1592877 x h1 h2) (fun h3 : False => @lem1592521 h2)). Qed.
Lemma lem1592880 (x : real) (h1 : term43 x) (h2 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592878 x h1 h2) (@lem1592521 h2)). Qed.
Lemma lem1592881 (x : real) (h1 : term43 x) (h2 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h3 : term59 = term18 => @lem1592880 x h1 h2) (fun h3 : False => @lem1592487 h2)). Qed.
Lemma lem1592882 (x : real) (h1 : term43 x) (h2 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592881 x h1 h2) (@lem1592487 h2)). Qed.
Lemma lem1592883 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h4 : term59 = term18 => @lem1592818 x h1 h2 h3) (fun h4 : False => @lem1592479 h3)). Qed.
Lemma lem1592884 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592883 x h1 h2 h3) (@lem1592479 h3)). Qed.
Lemma lem1592885 (x : real) (h1 : term43 x) (h2 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h3 : term59 = term18 => @lem1592882 x h1 h2) (fun h3 : False => @lem1592456 h2)). Qed.
Lemma lem1592886 (x : real) (h1 : term43 x) (h2 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592885 x h1 h2) (@lem1592456 h2)). Qed.
Lemma lem1592887 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h4 : term59 = term18 => @lem1592884 x h1 h2 h3) (fun h4 : False => @lem1592437 h3)). Qed.
Lemma lem1592888 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592887 x h1 h2 h3) (@lem1592437 h3)). Qed.
Lemma lem1592889 (x : real) (h1 : term43 x) (h2 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h3 : term59 = term18 => @lem1592886 x h1 h2) (fun h3 : False => @lem1592456 h2)). Qed.
Lemma lem1592890 (x : real) (h1 : term43 x) (h2 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592889 x h1 h2) (@lem1592456 h2)). Qed.
Lemma lem1592891 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1592888 x h1 h2 h3) (fun h4 : False => @lem1592444 h1)). Qed.
Lemma lem1592892 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592891 x h1 h2 h3) (@lem1592444 h1)). Qed.
Lemma lem1592893 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h4 : term59 = term18 => @lem1592892 x h1 h2 h3) (fun h4 : False => @lem1592437 h3)). Qed.
Lemma lem1592894 (x : real) (h1 : term10) (h2 : term39 x) (h3 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592893 x h1 h2 h3) (@lem1592437 h3)). Qed.
Lemma lem1592895 (x : real) (h1 : term10) (h2 : term59 = term18) (h3 : term21 x) : False.
Proof. exact (or_elim (@lem1592427 x h3) (fun h0 : term39 x => @lem1592894 x h1 h0 h2) (fun h0 : term43 x => @lem1592890 x h0 h2)). Qed.
Lemma lem1592896 (x : real) (h1 : term10) (h2 : term59 = term18) (h3 : term21 x) : (term21 x) = False.
Proof. exact (prop_ext (fun h4 : term21 x => @lem1592895 x h1 h2 h3) (fun h4 : False => @lem1592427 x h3)). Qed.
Lemma lem1592897 (x : real) (h1 : term10) (h2 : term59 = term18) (h3 : term21 x) : False.
Proof. exact (EQ_MP (@lem1592896 x h1 h2 h3) (@lem1592427 x h3)). Qed.
Lemma lem1592898 (x : real) (h1 : term10) (h2 : term59 = term18) (h3 : term21 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1592897 x h1 h2 h3) (fun h4 : False => @lem1592365 h1)). Qed.
Lemma lem1592899 (x : real) (h1 : term10) (h2 : term59 = term18) (h3 : term21 x) : False.
Proof. exact (EQ_MP (@lem1592898 x h1 h2 h3) (@lem1592365 h1)). Qed.
Lemma lem1592900 (x : real) (h1 : term10) (h2 : term59 = term18) (h3 : term21 x) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h4 : term59 = term18 => @lem1592899 x h1 h2 h3) (fun h4 : False => @lem1592352 h2)). Qed.
Lemma lem1592901 (x : real) (h1 : term10) (h2 : term59 = term18) (h3 : term21 x) : False.
Proof. exact (EQ_MP (@lem1592900 x h1 h2 h3) (@lem1592352 h2)). Qed.
Lemma lem1592902 (h1 : term10) (h2 : term3) (h3 : term59 = term18) : False.
Proof. exact (ex_elim (@lem1592312 h2) (fun x : real => fun h0 : term28 x => @lem1592901 x h1 h3 h0)). Qed.
Lemma lem1592903 (h1 : term10) (h2 : term3) (h3 : term59 = term18) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1592902 h1 h2 h3) (fun h4 : False => @lem1592331 h1)). Qed.
Lemma lem1592904 (h1 : term10) (h2 : term3) (h3 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592903 h1 h2 h3) (@lem1592331 h1)). Qed.
Lemma lem1592905 (h1 : term10) (h2 : term3) (h3 : term59 = term18) : (term59 = term18) = False.
Proof. exact (prop_ext (fun h4 : term59 = term18 => @lem1592904 h1 h2 h3) (fun h4 : False => @lem1592318 h3)). Qed.
Lemma lem1592906 (h1 : term10) (h2 : term3) (h3 : term59 = term18) : False.
Proof. exact (EQ_MP (@lem1592905 h1 h2 h3) (@lem1592318 h3)). Qed.
Lemma lem1592907 (h1 : term3) (h2 : term59 = term18) : term8.
Proof. exact (fun h0 : term10 => @lem1592906 h0 h1 h2). Qed.
Lemma lem1592908 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1592909 (h1 : term3) (h2 : term59 = term18) : term9.
Proof. exact (EQ_MP (@lem1592908) (@lem1592907 h1 h2)). Qed.
Lemma lem1592910 (h1 : term3) : term13.
Proof. exact (fun h0 : term59 = term18 => @lem1592909 h1 h0). Qed.
Lemma lem1592911 : term15.
Proof. exact (fun h0 : term3 => @lem1592910 h0). Qed.
Lemma lem1592912 : term4.
Proof. exact (EQ_MP (@lem1592131) (@lem1592911)). Qed.
Lemma lem1592914 : term4.
Proof. exact (@lem1592061 (@lem1592912)). Qed.
Lemma lem1592915 (h1 : term3) : term12.
Proof. exact (@lem1592914 (@lem1592046 h1)). Qed.
Lemma lem1592916 (h1 : term3) : term8.
Proof. exact (@lem1592915 h1 (@lem1592031)). Qed.
Lemma lem1592917 (h1 : term3) : False.
Proof. exact (@lem1592916 h1 (@lem1587920)). Qed.
Lemma lem1592918 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1592917 h1) (fun h2 : False => @lem1592046 h1)). Qed.
Lemma lem1592919 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1592918 h1) (@lem1592046 h1)). Qed.
Lemma lem1592920 : term2.
Proof. exact (fun h0 : term3 => @lem1592919 h0). Qed.
Lemma lem1592921 : term1.
Proof. exact (EQ_MP (@lem1592045) (@lem1592920)). Qed.
