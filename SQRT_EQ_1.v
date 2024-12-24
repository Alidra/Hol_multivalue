Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_EQ_1_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import SQRT_1_spec.
Require Import SQRT_INJ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem1954991 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1954992 : term1 = term2.
Proof. exact (@lem1954991 term1). Qed.
Lemma lem1954993 : term2 = term1.
Proof. exact (SYM (@lem1954992)). Qed.
Lemma lem1954994 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1954997 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1954998 : term5.
Proof. exact (fun h0 : term4 => @lem1954997 h0). Qed.
Lemma lem1954999 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1955000 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1955001 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1954999 h2 (@lem1955000 h1)). Qed.
Lemma lem1955002 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1955001 h1 h0). Qed.
Lemma lem1955003 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1955004 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1955002 h1 (@lem1955003 h2)). Qed.
Lemma lem1955005 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1955004 h0 h1). Qed.
Lemma lem1955006 : term7.
Proof. exact (fun h0 : term5 => @lem1955005 h0). Qed.
Lemma lem1955009 : term5.
Proof. exact (@lem1955006 (@lem1954998)). Qed.
Lemma lem1955019 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1955020 : term8 = term9.
Proof. exact (@lem1955019 term10). Qed.
Lemma lem1955029 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1955030 : term12 = term13.
Proof. exact (MK_COMB (@lem1955029) (@lem1955020)). Qed.
Lemma lem1955033 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1955040 : term4 = term15.
Proof. exact (MK_COMB (@lem1955033) (@lem1955030)). Qed.
Lemma lem1955045 (x : real) (y : real) : (((sqrt x) = (sqrt y)) = (x = y)) = (((sqrt x) = (sqrt y)) = (x = y)).
Proof. exact (eq_refl (((sqrt x) = (sqrt y)) = (x = y))). Qed.
Lemma lem1955046 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1955045 x y)). Qed.
Lemma lem1955047 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955048 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1955047) (@lem1955046 x)). Qed.
Lemma lem1955049 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1955048 x)). Qed.
Lemma lem1955050 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955051 : term10 = term10.
Proof. exact (MK_COMB (@lem1955050) (@lem1955049)). Qed.
Lemma lem1955052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1955053 : term9 = term9.
Proof. exact (MK_COMB (@lem1955052) (@lem1955051)). Qed.
Lemma lem1955056 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1955057 : term13 = term13.
Proof. exact (MK_COMB (@lem1955056) (@lem1955053)). Qed.
Lemma lem1955062 (x : real) : (((sqrt x) = term19) = (x = term19)) = (((sqrt x) = term19) = (x = term19)).
Proof. exact (eq_refl (((sqrt x) = term19) = (x = term19))). Qed.
Lemma lem1955063 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1955062 x)). Qed.
Lemma lem1955064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955065 : term1 = term1.
Proof. exact (MK_COMB (@lem1955064) (@lem1955063)). Qed.
Lemma lem1955066 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1955067 : term3 = term3.
Proof. exact (MK_COMB (@lem1955066) (@lem1955065)). Qed.
Lemma lem1955068 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1955069 : term14 = term14.
Proof. exact (MK_COMB (@lem1955068) (@lem1955067)). Qed.
Lemma lem1955070 : term15 = term15.
Proof. exact (MK_COMB (@lem1955069) (@lem1955057)). Qed.
Lemma lem1955095 : term4 = term15.
Proof. exact (TRANS (@lem1955040) (@lem1955070)). Qed.
Lemma lem1955096 : term15 = term4.
Proof. exact (SYM (@lem1955095)). Qed.
Lemma lem1955097 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1955099 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1955114 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem17646 ((sqrt x) = term19) (x = term19)). Qed.
Lemma lem1955115 (P : real -> Prop) : (term23 P) = (term24 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1955116 : term3 = term25.
Proof. exact (@lem1955115 term20). Qed.
Lemma lem1955117 (x : real) : (term26 x) = (((sqrt x) = term19) = (x = term19)).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1955118 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1955119 (x : real) : (term27 x) = (term21 x).
Proof. exact (MK_COMB (@lem1955118) (@lem1955117 x)). Qed.
Lemma lem1955120 (x : real) : (term27 x) = (term22 x).
Proof. exact (TRANS (@lem1955119 x) (@lem1955114 x)). Qed.
Lemma lem1955121 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1955120 x)). Qed.
Lemma lem1955122 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1955123 : term25 = term30.
Proof. exact (MK_COMB (@lem1955122) (@lem1955121)). Qed.
Lemma lem1955124 : term3 = term30.
Proof. exact (TRANS (@lem1955116) (@lem1955123)). Qed.
Lemma lem1955126 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term31 A P Q) = (term32 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1955127 (P : real -> Prop) (Q : real -> Prop) : (term33 P Q) = (term34 P Q).
Proof. exact (@lem1955126 real P Q). Qed.
Lemma lem1955128 : term35 = term36.
Proof. exact (@lem1955127 term37 term38). Qed.
Lemma lem1955129 (x : real) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1955130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1955131 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1955130) (@lem1955129 x)). Qed.
Lemma lem1955132 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1955133 (x : real) : (term45 x) = (term22 x).
Proof. exact (MK_COMB (@lem1955131 x) (@lem1955132 x)). Qed.
Lemma lem1955134 : term46 = term29.
Proof. exact (fun_ext (fun x : real => @lem1955133 x)). Qed.
Lemma lem1955135 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1955136 : term35 = term30.
Proof. exact (MK_COMB (@lem1955135) (@lem1955134)). Qed.
Lemma lem1955137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1955138 : term47 = term48.
Proof. exact (MK_COMB (@lem1955137) (@lem1955136)). Qed.
Lemma lem1955139 (x : real) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1955140 : term49 = term37.
Proof. exact (fun_ext (fun x : real => @lem1955139 x)). Qed.
Lemma lem1955141 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1955142 : term50 = term51.
Proof. exact (MK_COMB (@lem1955141) (@lem1955140)). Qed.
Lemma lem1955143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1955144 : term52 = term53.
Proof. exact (MK_COMB (@lem1955143) (@lem1955142)). Qed.
Lemma lem1955145 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1955146 : term54 = term38.
Proof. exact (fun_ext (fun x : real => @lem1955145 x)). Qed.
Lemma lem1955147 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1955148 : term55 = term56.
Proof. exact (MK_COMB (@lem1955147) (@lem1955146)). Qed.
Lemma lem1955149 : term36 = term57.
Proof. exact (MK_COMB (@lem1955144) (@lem1955148)). Qed.
Lemma lem1955150 : (term35 = term36) = (term30 = term57).
Proof. exact (MK_COMB (@lem1955138) (@lem1955149)). Qed.
Lemma lem1955151 : term30 = term57.
Proof. exact (EQ_MP (@lem1955150) (@lem1955128)). Qed.
Lemma lem1955249 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term32 A P Q) = (term31 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1955250 (P : real -> Prop) (Q : real -> Prop) : (term34 P Q) = (term33 P Q).
Proof. exact (@lem1955249 real P Q). Qed.
Lemma lem1955251 : term36 = term35.
Proof. exact (@lem1955250 term37 term38). Qed.
Lemma lem1955252 (x : real) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1955253 : term49 = term37.
Proof. exact (fun_ext (fun x : real => @lem1955252 x)). Qed.
Lemma lem1955254 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1955255 : term50 = term51.
Proof. exact (MK_COMB (@lem1955254) (@lem1955253)). Qed.
Lemma lem1955256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1955257 : term52 = term53.
Proof. exact (MK_COMB (@lem1955256) (@lem1955255)). Qed.
Lemma lem1955258 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1955259 : term54 = term38.
Proof. exact (fun_ext (fun x : real => @lem1955258 x)). Qed.
Lemma lem1955260 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1955261 : term55 = term56.
Proof. exact (MK_COMB (@lem1955260) (@lem1955259)). Qed.
Lemma lem1955262 : term36 = term57.
Proof. exact (MK_COMB (@lem1955257) (@lem1955261)). Qed.
Lemma lem1955263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1955264 : term58 = term59.
Proof. exact (MK_COMB (@lem1955263) (@lem1955262)). Qed.
Lemma lem1955265 (x : real) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1955266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1955267 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1955266) (@lem1955265 x)). Qed.
Lemma lem1955268 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1955269 (x : real) : (term45 x) = (term22 x).
Proof. exact (MK_COMB (@lem1955267 x) (@lem1955268 x)). Qed.
Lemma lem1955270 : term46 = term29.
Proof. exact (fun_ext (fun x : real => @lem1955269 x)). Qed.
Lemma lem1955271 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1955272 : term35 = term30.
Proof. exact (MK_COMB (@lem1955271) (@lem1955270)). Qed.
Lemma lem1955273 : (term36 = term35) = (term57 = term30).
Proof. exact (MK_COMB (@lem1955264) (@lem1955272)). Qed.
Lemma lem1955274 : term57 = term30.
Proof. exact (EQ_MP (@lem1955273) (@lem1955251)). Qed.
Lemma lem1955275 : term30 = term30.
Proof. exact (TRANS (@lem1955151) (@lem1955274)). Qed.
Lemma lem1955276 : term3 = term30.
Proof. exact (TRANS (@lem1955124) (@lem1955275)). Qed.
Lemma lem1955277 (h1 : term3) : term30.
Proof. exact (EQ_MP (@lem1955276) (@lem1955097 h1)). Qed.
Lemma lem1955283 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1955298 (x : real) (y : real) : (((sqrt x) = (sqrt y)) = (x = y)) = (term61 x y).
Proof. exact (@lem17784 ((sqrt x) = (sqrt y)) (x = y)). Qed.
Lemma lem1955299 (x : real) : (term16 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1955298 x y)). Qed.
Lemma lem1955300 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955301 (x : real) : (term17 x) = (term63 x).
Proof. exact (MK_COMB (@lem1955300) (@lem1955299 x)). Qed.
Lemma lem1955302 : term18 = term64.
Proof. exact (fun_ext (fun x : real => @lem1955301 x)). Qed.
Lemma lem1955303 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955304 : term10 = term65.
Proof. exact (MK_COMB (@lem1955303) (@lem1955302)). Qed.
Lemma lem1955310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1955311 (P : real -> Prop) (Q : real -> Prop) : (term68 P Q) = (term69 P Q).
Proof. exact (@lem1955310 real P Q). Qed.
Lemma lem1955312 (x : real) : (term70 x) = (term71 x).
Proof. exact (@lem1955311 (term72 x) (term73 x)). Qed.
Lemma lem1955313 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1955314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1955315 (x : real) (y : real) : (term76 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1955314) (@lem1955313 x y)). Qed.
Lemma lem1955316 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1955317 (x : real) (y : real) : (term80 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1955315 x y) (@lem1955316 x y)). Qed.
Lemma lem1955318 (x : real) : (term81 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1955317 x y)). Qed.
Lemma lem1955319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955320 (x : real) : (term70 x) = (term63 x).
Proof. exact (MK_COMB (@lem1955319) (@lem1955318 x)). Qed.
Lemma lem1955321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1955322 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1955321) (@lem1955320 x)). Qed.
Lemma lem1955323 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1955324 (x : real) : (term84 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1955323 x y)). Qed.
Lemma lem1955325 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955326 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem1955325) (@lem1955324 x)). Qed.
Lemma lem1955327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1955328 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1955327) (@lem1955326 x)). Qed.
Lemma lem1955329 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1955330 (x : real) : (term89 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1955329 x y)). Qed.
Lemma lem1955331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955332 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem1955331) (@lem1955330 x)). Qed.
Lemma lem1955333 (x : real) : (term71 x) = (term92 x).
Proof. exact (MK_COMB (@lem1955328 x) (@lem1955332 x)). Qed.
Lemma lem1955334 (x : real) : ((term70 x) = (term71 x)) = ((term63 x) = (term92 x)).
Proof. exact (MK_COMB (@lem1955322 x) (@lem1955333 x)). Qed.
Lemma lem1955335 (x : real) : (term63 x) = (term92 x).
Proof. exact (EQ_MP (@lem1955334 x) (@lem1955312 x)). Qed.
Lemma lem1955432 : term64 = term93.
Proof. exact (fun_ext (fun x : real => @lem1955335 x)). Qed.
Lemma lem1955433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955434 : term65 = term94.
Proof. exact (MK_COMB (@lem1955433) (@lem1955432)). Qed.
Lemma lem1955436 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1955437 (P : real -> Prop) (Q : real -> Prop) : (term68 P Q) = (term69 P Q).
Proof. exact (@lem1955436 real P Q). Qed.
Lemma lem1955438 : term95 = term96.
Proof. exact (@lem1955437 term97 term98). Qed.
Lemma lem1955439 (x : real) : (term99 x) = (term86 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1955440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1955441 (x : real) : (term100 x) = (term88 x).
Proof. exact (MK_COMB (@lem1955440) (@lem1955439 x)). Qed.
Lemma lem1955442 (x : real) : (term101 x) = (term91 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1955443 (x : real) : (term102 x) = (term92 x).
Proof. exact (MK_COMB (@lem1955441 x) (@lem1955442 x)). Qed.
Lemma lem1955444 : term103 = term93.
Proof. exact (fun_ext (fun x : real => @lem1955443 x)). Qed.
Lemma lem1955445 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955446 : term95 = term94.
Proof. exact (MK_COMB (@lem1955445) (@lem1955444)). Qed.
Lemma lem1955447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1955448 : term104 = term105.
Proof. exact (MK_COMB (@lem1955447) (@lem1955446)). Qed.
Lemma lem1955449 (x : real) : (term99 x) = (term86 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1955450 : term106 = term97.
Proof. exact (fun_ext (fun x : real => @lem1955449 x)). Qed.
Lemma lem1955451 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955452 : term107 = term108.
Proof. exact (MK_COMB (@lem1955451) (@lem1955450)). Qed.
Lemma lem1955453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1955454 : term109 = term110.
Proof. exact (MK_COMB (@lem1955453) (@lem1955452)). Qed.
Lemma lem1955455 (x : real) : (term101 x) = (term91 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1955456 : term111 = term98.
Proof. exact (fun_ext (fun x : real => @lem1955455 x)). Qed.
Lemma lem1955457 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955458 : term112 = term113.
Proof. exact (MK_COMB (@lem1955457) (@lem1955456)). Qed.
Lemma lem1955459 : term96 = term114.
Proof. exact (MK_COMB (@lem1955454) (@lem1955458)). Qed.
Lemma lem1955460 : (term95 = term96) = (term94 = term114).
Proof. exact (MK_COMB (@lem1955448) (@lem1955459)). Qed.
Lemma lem1955461 : term94 = term114.
Proof. exact (EQ_MP (@lem1955460) (@lem1955438)). Qed.
Lemma lem1955568 : term65 = term114.
Proof. exact (TRANS (@lem1955434) (@lem1955461)). Qed.
Lemma lem1955569 : term10 = term114.
Proof. exact (TRANS (@lem1955304) (@lem1955568)). Qed.
Lemma lem1955570 (h1 : term10) : term114.
Proof. exact (EQ_MP (@lem1955569) (@lem1955099 h1)). Qed.
Lemma lem1955591 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1955610 (x : real) (y : real) : (term79 x y) = (term79 x y).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1955611 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1955610 x y)). Qed.
Lemma lem1955612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955613 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem1955612) (@lem1955611 x)). Qed.
Lemma lem1955614 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem1955613 x)). Qed.
Lemma lem1955615 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955616 : term113 = term113.
Proof. exact (MK_COMB (@lem1955615) (@lem1955614)). Qed.
Lemma lem1955635 (x : real) (y : real) : (term75 x y) = (term75 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1955636 (x : real) : (term72 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1955635 x y)). Qed.
Lemma lem1955637 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955638 (x : real) : (term86 x) = (term86 x).
Proof. exact (MK_COMB (@lem1955637) (@lem1955636 x)). Qed.
Lemma lem1955639 : term97 = term97.
Proof. exact (fun_ext (fun x : real => @lem1955638 x)). Qed.
Lemma lem1955640 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955641 : term108 = term108.
Proof. exact (MK_COMB (@lem1955640) (@lem1955639)). Qed.
Lemma lem1955642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1955643 : term110 = term110.
Proof. exact (MK_COMB (@lem1955642) (@lem1955641)). Qed.
Lemma lem1955644 : term114 = term114.
Proof. exact (MK_COMB (@lem1955643) (@lem1955616)). Qed.
Lemma lem1955645 (h1 : term10) : term114.
Proof. exact (EQ_MP (@lem1955644) (@lem1955570 h1)). Qed.
Lemma lem1955707 (x : real) (h1 : term22 x) : term22 x.
Proof. exact (h1). Qed.
Lemma lem1955708 (h1 : term10) : term113.
Proof. exact (proj2 (@lem1955645 h1)). Qed.
Lemma lem1955709 (h1 : term10) : term108.
Proof. exact (proj1 (@lem1955645 h1)). Qed.
Lemma lem1955710 (x : real) (h1 : term40 x) : term40 x.
Proof. exact (h1). Qed.
Lemma lem1955711 (x : real) (h1 : term44 x) : term44 x.
Proof. exact (h1). Qed.
Lemma lem1955719 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1955727 (x : real) (y : real) : (term75 x y) = (term75 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1955728 (x : real) : (term72 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1955727 x y)). Qed.
Lemma lem1955729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955730 (x : real) : (term86 x) = (term86 x).
Proof. exact (MK_COMB (@lem1955729) (@lem1955728 x)). Qed.
Lemma lem1955731 : term97 = term97.
Proof. exact (fun_ext (fun x : real => @lem1955730 x)). Qed.
Lemma lem1955732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955734 : term108 = term108.
Proof. exact (MK_COMB (@lem1955732) (@lem1955731)). Qed.
Lemma lem1955735 (h1 : term10) : term108.
Proof. exact (EQ_MP (@lem1955734) (@lem1955709 h1)). Qed.
Lemma lem1955743 (x : real) (y : real) : (term79 x y) = (term79 x y).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1955744 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1955743 x y)). Qed.
Lemma lem1955745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955746 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem1955745) (@lem1955744 x)). Qed.
Lemma lem1955747 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem1955746 x)). Qed.
Lemma lem1955748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1955750 : term113 = term113.
Proof. exact (MK_COMB (@lem1955748) (@lem1955747)). Qed.
Lemma lem1955751 (h1 : term10) : term113.
Proof. exact (EQ_MP (@lem1955750) (@lem1955708 h1)). Qed.
Lemma lem1955763 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1955804 (_27426 : real) (h1 : term10) : term99 _27426.
Proof. exact (@lem1955735 h1 _27426). Qed.
Lemma lem1955805 (_27426 : real) : (term99 _27426) = (term86 _27426).
Proof. exact (eq_refl (term99 _27426)). Qed.
Lemma lem1955806 (_27426 : real) (h1 : term10) : term86 _27426.
Proof. exact (EQ_MP (@lem1955805 _27426) (@lem1955804 _27426 h1)). Qed.
Lemma lem1955807 (_27426 : real) (_27427 : real) (h1 : term10) : term74 _27426 _27427.
Proof. exact (@lem1955806 _27426 h1 _27427). Qed.
Lemma lem1955808 (_27426 : real) (_27427 : real) : (term74 _27426 _27427) = (term75 _27426 _27427).
Proof. exact (eq_refl (term74 _27426 _27427)). Qed.
Lemma lem1955810 (_27428 : real) (h1 : term10) : term101 _27428.
Proof. exact (@lem1955751 h1 _27428). Qed.
Lemma lem1955811 (_27428 : real) : (term101 _27428) = (term91 _27428).
Proof. exact (eq_refl (term101 _27428)). Qed.
Lemma lem1955812 (_27428 : real) (h1 : term10) : term91 _27428.
Proof. exact (EQ_MP (@lem1955811 _27428) (@lem1955810 _27428 h1)). Qed.
Lemma lem1955813 (_27428 : real) (_27429 : real) (h1 : term10) : term78 _27428 _27429.
Proof. exact (@lem1955812 _27428 h1 _27429). Qed.
Lemma lem1955814 (_27428 : real) (_27429 : real) : (term78 _27428 _27429) = (term79 _27428 _27429).
Proof. exact (eq_refl (term78 _27428 _27429)). Qed.
Lemma lem1955829 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1955835 (_27426 : real) (_27427 : real) (h1 : term10) : term75 _27426 _27427.
Proof. exact (EQ_MP (@lem1955808 _27426 _27427) (@lem1955807 _27426 _27427 h1)). Qed.
Lemma lem1955841 (_27428 : real) (_27429 : real) (h1 : term10) : term79 _27428 _27429.
Proof. exact (EQ_MP (@lem1955814 _27428 _27429) (@lem1955813 _27428 _27429 h1)). Qed.
Lemma lem1955845 (x : real) (h1 : term40 x) : term115 x.
Proof. exact (proj2 (@lem1955710 x h1)). Qed.
Lemma lem1955847 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1955861 (x : real) (h1 : term44 x) : term116 x.
Proof. exact (proj1 (@lem1955711 x h1)). Qed.
Lemma lem1955863 (x : real) (h1 : term44 x) : x = term19.
Proof. exact (proj2 (@lem1955711 x h1)). Qed.
Lemma lem1955891 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1955920 : term117 = term117.
Proof. exact (eq_refl term117). Qed.
Lemma lem1955921 (x : real) (h1 : term44 x) : (term118 x) = term119.
Proof. exact (MK_COMB (@lem1955920) (@lem1955863 x h1)). Qed.
Lemma lem1955922 : term119 = term120.
Proof. exact (eq_refl term119). Qed.
Lemma lem1955923 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1955924 (x : real) : ((term118 x) = term119) = ((term118 x) = term120).
Proof. exact (MK_COMB (@lem1955923 x) (@lem1955922)). Qed.
Lemma lem1955925 (x : real) : (term118 x) = (term116 x).
Proof. exact (eq_refl (term118 x)). Qed.
Lemma lem1955926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1955927 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1955926) (@lem1955925 x)). Qed.
Lemma lem1955928 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem1955929 (x : real) : ((term118 x) = term120) = ((term116 x) = term120).
Proof. exact (MK_COMB (@lem1955927 x) (@lem1955928)). Qed.
Lemma lem1955930 (x : real) : ((term118 x) = term119) = ((term116 x) = term120).
Proof. exact (TRANS (@lem1955924 x) (@lem1955929 x)). Qed.
Lemma lem1955931 (x : real) (h1 : term44 x) : (term116 x) = term120.
Proof. exact (EQ_MP (@lem1955930 x) (@lem1955921 x h1)). Qed.
Lemma lem1955932 (x : real) (h1 : term44 x) : term120.
Proof. exact (EQ_MP (@lem1955931 x h1) (@lem1955861 x h1)). Qed.
Lemma lem1955966 (x : real) (y : real) (z : real) : term123 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1955970 (x : real) (h1 : term40 x) : (sqrt x) = term19.
Proof. exact (proj1 (@lem1955710 x h1)). Qed.
Lemma lem1955971 (x : real) (h1 : term40 x) : term124 x.
Proof. exact (fun h0 : term116 x => @lem1955970 x h1). Qed.
Lemma lem1955973 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1955974 (x : real) : (term124 x) = ((sqrt x) = term19).
Proof. exact (@lem1955973 ((sqrt x) = term19)). Qed.
Lemma lem1955975 (x : real) (h1 : term40 x) : (sqrt x) = term19.
Proof. exact (EQ_MP (@lem1955974 x) (@lem1955971 x h1)). Qed.
Lemma lem1955977 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1955978 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (@lem1955977 (sqrt x)). Qed.
Lemma lem1955979 (x : real) : term126 x.
Proof. exact (fun h0 : term127 x => @lem1955978 x). Qed.
Lemma lem1955981 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1955982 (x : real) : (term126 x) = ((sqrt x) = (sqrt x)).
Proof. exact (@lem1955981 ((sqrt x) = (sqrt x))). Qed.
Lemma lem1955983 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (EQ_MP (@lem1955982 x) (@lem1955979 x)). Qed.
Lemma lem1956001 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1956002 (y : real) (x : real) (z : real) : (term128 x y z) = (term129 y x z).
Proof. exact (@lem1956001 (y = z) (term130 x z)). Qed.
Lemma lem1956012 (x : real) (y : real) : (term131 x y) = (term131 x y).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem1956013 (y : real) (x : real) (z : real) : (term123 x y z) = (term132 y x z).
Proof. exact (MK_COMB (@lem1956012 x y) (@lem1956002 y x z)). Qed.
Lemma lem1956017 (q : Prop) (p : Prop) (r : Prop) : (term133 p q r) = (term133 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1956018 (y : real) (x : real) (z : real) : (term132 y x z) = (term134 y x z).
Proof. exact (@lem1956017 (y = z) (term130 x y) (term130 x z)). Qed.
Lemma lem1956040 (y : real) (x : real) (z : real) : (term123 x y z) = (term134 y x z).
Proof. exact (TRANS (@lem1956013 y x z) (@lem1956018 y x z)). Qed.
Lemma lem1956041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1956042 (y : real) (x : real) (z : real) : (term135 x y z) = (term136 y x z).
Proof. exact (MK_COMB (@lem1956041) (@lem1956040 y x z)). Qed.
Lemma lem1956064 (y : real) (x : real) (z : real) : (term134 y x z) = (term134 y x z).
Proof. exact (eq_refl (term134 y x z)). Qed.
Lemma lem1956065 (y : real) (x : real) (z : real) : ((term123 x y z) = (term134 y x z)) = ((term134 y x z) = (term134 y x z)).
Proof. exact (MK_COMB (@lem1956042 y x z) (@lem1956064 y x z)). Qed.
Lemma lem1956067 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1956068 (x : Prop) : (x = x) = True.
Proof. exact (@lem1956067 Prop x). Qed.
Lemma lem1956069 (y : real) (x : real) (z : real) : ((term134 y x z) = (term134 y x z)) = True.
Proof. exact (@lem1956068 (term134 y x z)). Qed.
Lemma lem1956070 (y : real) (x : real) (z : real) : ((term123 x y z) = (term134 y x z)) = True.
Proof. exact (TRANS (@lem1956065 y x z) (@lem1956069 y x z)). Qed.
Lemma lem1956071 (y : real) (x : real) (z : real) : True = ((term123 x y z) = (term134 y x z)).
Proof. exact (SYM (@lem1956070 y x z)). Qed.
Lemma lem1956072 (y : real) (x : real) (z : real) : (term123 x y z) = (term134 y x z).
Proof. exact (EQ_MP (@lem1956071 y x z) (@lem0)). Qed.
Lemma lem1956073 (y : real) (x : real) (z : real) : term134 y x z.
Proof. exact (EQ_MP (@lem1956072 y x z) (@lem1955966 x y z)). Qed.
Lemma lem1956075 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1956076 (x : real) (y : real) (z : real) : (term134 y x z) = (term138 x y z).
Proof. exact (@lem1956075 (term139 y x z) (y = z)). Qed.
Lemma lem1956078 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1956079 (y : real) (x : real) (z : real) : (term142 y x z) = (term143 y x z).
Proof. exact (@lem1956078 (term130 x y) (term130 x z)). Qed.
Lemma lem1956081 (a : Prop) : (term144 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1956082 (x : real) (y : real) : (term145 x y) = (x = y).
Proof. exact (@lem1956081 (x = y)). Qed.
Lemma lem1956083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1956084 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (MK_COMB (@lem1956083) (@lem1956082 x y)). Qed.
Lemma lem1956086 (a : Prop) : (term144 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1956087 (x : real) (z : real) : (term145 x z) = (x = z).
Proof. exact (@lem1956086 (x = z)). Qed.
Lemma lem1956088 (y : real) (x : real) (z : real) : (term143 y x z) = (term148 y x z).
Proof. exact (MK_COMB (@lem1956084 x y) (@lem1956087 x z)). Qed.
Lemma lem1956089 (y : real) (x : real) (z : real) : (term142 y x z) = (term148 y x z).
Proof. exact (TRANS (@lem1956079 y x z) (@lem1956088 y x z)). Qed.
Lemma lem1956090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1956091 (y : real) (x : real) (z : real) : (term149 y x z) = (term150 y x z).
Proof. exact (MK_COMB (@lem1956090) (@lem1956089 y x z)). Qed.
Lemma lem1956092 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1956093 (x : real) (y : real) (z : real) : (term138 x y z) = (term151 x y z).
Proof. exact (MK_COMB (@lem1956091 y x z) (@lem1956092 y z)). Qed.
Lemma lem1956094 (x : real) (y : real) (z : real) : (term134 y x z) = (term151 x y z).
Proof. exact (TRANS (@lem1956076 x y z) (@lem1956093 x y z)). Qed.
Lemma lem1956096 (x : real) (h1 : term40 x) : term152 x.
Proof. exact (conj (@lem1955975 x h1) (@lem1955983 x)). Qed.
Lemma lem1956098 (x : real) (y : real) (z : real) : term151 x y z.
Proof. exact (EQ_MP (@lem1956094 x y z) (@lem1956073 y x z)). Qed.
Lemma lem1956099 (x : real) : term153 x.
Proof. exact (@lem1956098 (sqrt x) term19 (sqrt x)). Qed.
Lemma lem1956102 (x : real) (h1 : term40 x) : term19 = (sqrt x).
Proof. exact (@lem1956099 x (@lem1956096 x h1)). Qed.
Lemma lem1956103 (x : real) (h1 : term40 x) : term154 x.
Proof. exact (fun h0 : term155 x => @lem1956102 x h1). Qed.
Lemma lem1956105 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956106 (x : real) : (term154 x) = (term19 = (sqrt x)).
Proof. exact (@lem1956105 (term19 = (sqrt x))). Qed.
Lemma lem1956107 (x : real) (h1 : term40 x) : term19 = (sqrt x).
Proof. exact (EQ_MP (@lem1956106 x) (@lem1956103 x h1)). Qed.
Lemma lem1956109 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1956110 (h1 : term60 = term19) : term156.
Proof. exact (fun h0 : term120 => @lem1956109 h1). Qed.
Lemma lem1956112 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956113 : term156 = (term60 = term19).
Proof. exact (@lem1956112 (term60 = term19)). Qed.
Lemma lem1956114 (h1 : term60 = term19) : term60 = term19.
Proof. exact (EQ_MP (@lem1956113) (@lem1956110 h1)). Qed.
Lemma lem1956116 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1956117 (_27426 : real) (_27427 : real) : (term75 _27426 _27427) = (term157 _27426 _27427).
Proof. exact (@lem1956116 (term130 _27426 _27427) ((sqrt _27426) = (sqrt _27427))). Qed.
Lemma lem1956119 (a : Prop) : (term144 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1956120 (_27426 : real) (_27427 : real) : (term145 _27426 _27427) = (_27426 = _27427).
Proof. exact (@lem1956119 (_27426 = _27427)). Qed.
Lemma lem1956121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1956122 (_27426 : real) (_27427 : real) : (term158 _27426 _27427) = (term159 _27426 _27427).
Proof. exact (MK_COMB (@lem1956121) (@lem1956120 _27426 _27427)). Qed.
Lemma lem1956123 (_27426 : real) (_27427 : real) : ((sqrt _27426) = (sqrt _27427)) = ((sqrt _27426) = (sqrt _27427)).
Proof. exact (eq_refl ((sqrt _27426) = (sqrt _27427))). Qed.
Lemma lem1956124 (_27426 : real) (_27427 : real) : (term157 _27426 _27427) = (term160 _27426 _27427).
Proof. exact (MK_COMB (@lem1956122 _27426 _27427) (@lem1956123 _27426 _27427)). Qed.
Lemma lem1956125 (_27426 : real) (_27427 : real) : (term75 _27426 _27427) = (term160 _27426 _27427).
Proof. exact (TRANS (@lem1956117 _27426 _27427) (@lem1956124 _27426 _27427)). Qed.
Lemma lem1956128 (_27426 : real) (_27427 : real) (h1 : term10) : term160 _27426 _27427.
Proof. exact (EQ_MP (@lem1956125 _27426 _27427) (@lem1955835 _27426 _27427 h1)). Qed.
Lemma lem1956129 (h1 : term10) : term161.
Proof. exact (@lem1956128 term60 term19 h1). Qed.
Lemma lem1956132 (h1 : term10) (h2 : term60 = term19) : term162 = term60.
Proof. exact (@lem1956129 h1 (@lem1956114 h2)). Qed.
Lemma lem1956133 (h1 : term10) (h2 : term60 = term19) : term163.
Proof. exact (fun h0 : term164 => @lem1956132 h1 h2). Qed.
Lemma lem1956135 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956136 : term163 = (term162 = term60).
Proof. exact (@lem1956135 (term162 = term60)). Qed.
Lemma lem1956137 (h1 : term10) (h2 : term60 = term19) : term162 = term60.
Proof. exact (EQ_MP (@lem1956136) (@lem1956133 h1 h2)). Qed.
Lemma lem1956139 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1956140 : term162 = term162.
Proof. exact (@lem1956139 term162). Qed.
Lemma lem1956141 : term165.
Proof. exact (fun h0 : term166 => @lem1956140). Qed.
Lemma lem1956143 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956144 : term165 = (term162 = term162).
Proof. exact (@lem1956143 (term162 = term162)). Qed.
Lemma lem1956145 : term162 = term162.
Proof. exact (EQ_MP (@lem1956144) (@lem1956141)). Qed.
Lemma lem1956146 (h1 : term10) (h2 : term60 = term19) : term167.
Proof. exact (conj (@lem1956137 h1 h2) (@lem1956145)). Qed.
Lemma lem1956148 (x : real) (y : real) (z : real) : term151 x y z.
Proof. exact (EQ_MP (@lem1956094 x y z) (@lem1956073 y x z)). Qed.
Lemma lem1956149 : term168.
Proof. exact (@lem1956148 term162 term60 term162). Qed.
Lemma lem1956152 (h1 : term10) (h2 : term60 = term19) : term60 = term162.
Proof. exact (@lem1956149 (@lem1956146 h1 h2)). Qed.
Lemma lem1956153 (h1 : term10) (h2 : term60 = term19) : term169.
Proof. exact (fun h0 : term170 => @lem1956152 h1 h2). Qed.
Lemma lem1956155 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956156 : term169 = (term60 = term162).
Proof. exact (@lem1956155 (term60 = term162)). Qed.
Lemma lem1956157 (h1 : term10) (h2 : term60 = term19) : term60 = term162.
Proof. exact (EQ_MP (@lem1956156) (@lem1956153 h1 h2)). Qed.
Lemma lem1956163 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1956164 (_27428 : real) (_27429 : real) : (term79 _27428 _27429) = (term171 _27428 _27429).
Proof. exact (@lem1956163 (_27428 = _27429) (term172 _27428 _27429)). Qed.
Lemma lem1956174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1956175 (_27428 : real) (_27429 : real) : (term173 _27428 _27429) = (term174 _27428 _27429).
Proof. exact (MK_COMB (@lem1956174) (@lem1956164 _27428 _27429)). Qed.
Lemma lem1956185 (_27428 : real) (_27429 : real) : (term171 _27428 _27429) = (term171 _27428 _27429).
Proof. exact (eq_refl (term171 _27428 _27429)). Qed.
Lemma lem1956186 (_27428 : real) (_27429 : real) : ((term79 _27428 _27429) = (term171 _27428 _27429)) = ((term171 _27428 _27429) = (term171 _27428 _27429)).
Proof. exact (MK_COMB (@lem1956175 _27428 _27429) (@lem1956185 _27428 _27429)). Qed.
Lemma lem1956188 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1956189 (x : Prop) : (x = x) = True.
Proof. exact (@lem1956188 Prop x). Qed.
Lemma lem1956190 (_27428 : real) (_27429 : real) : ((term171 _27428 _27429) = (term171 _27428 _27429)) = True.
Proof. exact (@lem1956189 (term171 _27428 _27429)). Qed.
Lemma lem1956191 (_27428 : real) (_27429 : real) : ((term79 _27428 _27429) = (term171 _27428 _27429)) = True.
Proof. exact (TRANS (@lem1956186 _27428 _27429) (@lem1956190 _27428 _27429)). Qed.
Lemma lem1956192 (_27428 : real) (_27429 : real) : True = ((term79 _27428 _27429) = (term171 _27428 _27429)).
Proof. exact (SYM (@lem1956191 _27428 _27429)). Qed.
Lemma lem1956193 (_27428 : real) (_27429 : real) : (term79 _27428 _27429) = (term171 _27428 _27429).
Proof. exact (EQ_MP (@lem1956192 _27428 _27429) (@lem0)). Qed.
Lemma lem1956194 (_27428 : real) (_27429 : real) (h1 : term10) : term171 _27428 _27429.
Proof. exact (EQ_MP (@lem1956193 _27428 _27429) (@lem1955841 _27428 _27429 h1)). Qed.
Lemma lem1956196 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1956197 (_27428 : real) (_27429 : real) : (term171 _27428 _27429) = (term175 _27428 _27429).
Proof. exact (@lem1956196 (term172 _27428 _27429) (_27428 = _27429)). Qed.
Lemma lem1956199 (a : Prop) : (term144 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1956200 (_27428 : real) (_27429 : real) : (term176 _27428 _27429) = ((sqrt _27428) = (sqrt _27429)).
Proof. exact (@lem1956199 ((sqrt _27428) = (sqrt _27429))). Qed.
Lemma lem1956201 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1956202 (_27428 : real) (_27429 : real) : (term177 _27428 _27429) = (term178 _27428 _27429).
Proof. exact (MK_COMB (@lem1956201) (@lem1956200 _27428 _27429)). Qed.
Lemma lem1956203 (_27428 : real) (_27429 : real) : (_27428 = _27429) = (_27428 = _27429).
Proof. exact (eq_refl (_27428 = _27429)). Qed.
Lemma lem1956204 (_27428 : real) (_27429 : real) : (term175 _27428 _27429) = (term179 _27428 _27429).
Proof. exact (MK_COMB (@lem1956202 _27428 _27429) (@lem1956203 _27428 _27429)). Qed.
Lemma lem1956205 (_27428 : real) (_27429 : real) : (term171 _27428 _27429) = (term179 _27428 _27429).
Proof. exact (TRANS (@lem1956197 _27428 _27429) (@lem1956204 _27428 _27429)). Qed.
Lemma lem1956208 (_27428 : real) (_27429 : real) (h1 : term10) : term179 _27428 _27429.
Proof. exact (EQ_MP (@lem1956205 _27428 _27429) (@lem1956194 _27428 _27429 h1)). Qed.
Lemma lem1956209 (h1 : term10) : term180.
Proof. exact (@lem1956208 term19 term60 h1). Qed.
Lemma lem1956212 (h1 : term10) (h2 : term60 = term19) : term19 = term60.
Proof. exact (@lem1956209 h1 (@lem1956157 h1 h2)). Qed.
Lemma lem1956213 (h1 : term10) (h2 : term60 = term19) : term181.
Proof. exact (fun h0 : term182 => @lem1956212 h1 h2). Qed.
Lemma lem1956215 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956216 : term181 = (term19 = term60).
Proof. exact (@lem1956215 (term19 = term60)). Qed.
Lemma lem1956217 (h1 : term10) (h2 : term60 = term19) : term19 = term60.
Proof. exact (EQ_MP (@lem1956216) (@lem1956213 h1 h2)). Qed.
Lemma lem1956218 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : term183 x.
Proof. exact (conj (@lem1956107 x h2) (@lem1956217 h1 h3)). Qed.
Lemma lem1956220 (x : real) (y : real) (z : real) : term151 x y z.
Proof. exact (EQ_MP (@lem1956094 x y z) (@lem1956073 y x z)). Qed.
Lemma lem1956221 (x : real) : term184 x.
Proof. exact (@lem1956220 term19 (sqrt x) term60). Qed.
Lemma lem1956224 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : (sqrt x) = term60.
Proof. exact (@lem1956221 x (@lem1956218 x h1 h2 h3)). Qed.
Lemma lem1956225 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : term185 x.
Proof. exact (fun h0 : term186 x => @lem1956224 x h1 h2 h3). Qed.
Lemma lem1956227 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956228 (x : real) : (term185 x) = ((sqrt x) = term60).
Proof. exact (@lem1956227 ((sqrt x) = term60)). Qed.
Lemma lem1956229 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : (sqrt x) = term60.
Proof. exact (EQ_MP (@lem1956228 x) (@lem1956225 x h1 h2 h3)). Qed.
Lemma lem1956231 (_27428 : real) (_27429 : real) (h1 : term10) : term179 _27428 _27429.
Proof. exact (EQ_MP (@lem1956205 _27428 _27429) (@lem1956194 _27428 _27429 h1)). Qed.
Lemma lem1956232 (x : real) (h1 : term10) : term187 x.
Proof. exact (@lem1956231 x term19 h1). Qed.
Lemma lem1956235 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : x = term19.
Proof. exact (@lem1956232 x h1 (@lem1956229 x h1 h2 h3)). Qed.
Lemma lem1956236 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : term188 x.
Proof. exact (fun h0 : term115 x => @lem1956235 x h1 h2 h3). Qed.
Lemma lem1956238 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956239 (x : real) : (term188 x) = (x = term19).
Proof. exact (@lem1956238 (x = term19)). Qed.
Lemma lem1956240 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : x = term19.
Proof. exact (EQ_MP (@lem1956239 x) (@lem1956236 x h1 h2 h3)). Qed.
Lemma lem1956243 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1956245 (x : real) : (term115 x) = (term189 x).
Proof. exact (@lem1956243 (x = term19)). Qed.
Lemma lem1956248 (x : real) (h1 : term40 x) : term189 x.
Proof. exact (EQ_MP (@lem1956245 x) (@lem1955845 x h1)). Qed.
Lemma lem1956251 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : False.
Proof. exact (@lem1956248 x h2 (@lem1956240 x h1 h2 h3)). Qed.
Lemma lem1956252 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : term190.
Proof. exact (fun h0 : ~ False => @lem1956251 x h1 h2 h3). Qed.
Lemma lem1956254 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956255 : term190 = False.
Proof. exact (@lem1956254 False). Qed.
Lemma lem1956256 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956255) (@lem1956252 x h1 h2 h3)). Qed.
Lemma lem1956294 (h1 : term60 = term19) : term60 = term19.
Proof. exact (h1). Qed.
Lemma lem1956295 (h1 : term60 = term19) : term156.
Proof. exact (fun h0 : term120 => @lem1956294 h1). Qed.
Lemma lem1956297 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956298 : term156 = (term60 = term19).
Proof. exact (@lem1956297 (term60 = term19)). Qed.
Lemma lem1956299 (h1 : term60 = term19) : term60 = term19.
Proof. exact (EQ_MP (@lem1956298) (@lem1956295 h1)). Qed.
Lemma lem1956302 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1956304 : term120 = term191.
Proof. exact (@lem1956302 (term60 = term19)). Qed.
Lemma lem1956307 (x : real) (h1 : term44 x) : term191.
Proof. exact (EQ_MP (@lem1956304) (@lem1955932 x h1)). Qed.
Lemma lem1956310 (x : real) (h1 : term44 x) (h2 : term60 = term19) : False.
Proof. exact (@lem1956307 x h1 (@lem1956299 h2)). Qed.
Lemma lem1956311 (x : real) (h1 : term44 x) (h2 : term60 = term19) : term190.
Proof. exact (fun h0 : ~ False => @lem1956310 x h1 h2). Qed.
Lemma lem1956313 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1956314 : term190 = False.
Proof. exact (@lem1956313 False). Qed.
Lemma lem1956315 (x : real) (h1 : term44 x) (h2 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956314) (@lem1956311 x h1 h2)). Qed.
Lemma lem1956316 (x : real) (h1 : term44 x) (h2 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h3 : term60 = term19 => @lem1956315 x h1 h2) (fun h3 : False => @lem1955891 h2)). Qed.
Lemma lem1956318 (x : real) (h1 : term44 x) (h2 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956316 x h1 h2) (@lem1955891 h2)). Qed.
Lemma lem1956319 (x : real) (h1 : term44 x) (h2 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h3 : term60 = term19 => @lem1956318 x h1 h2) (fun h3 : False => @lem1955847 h2)). Qed.
Lemma lem1956320 (x : real) (h1 : term44 x) (h2 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956319 x h1 h2) (@lem1955847 h2)). Qed.
Lemma lem1956321 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h4 : term60 = term19 => @lem1956256 x h1 h2 h3) (fun h4 : False => @lem1955829 h3)). Qed.
Lemma lem1956322 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956321 x h1 h2 h3) (@lem1955829 h3)). Qed.
Lemma lem1956323 (x : real) (h1 : term44 x) (h2 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h3 : term60 = term19 => @lem1956320 x h1 h2) (fun h3 : False => @lem1955763 h2)). Qed.
Lemma lem1956324 (x : real) (h1 : term44 x) (h2 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956323 x h1 h2) (@lem1955763 h2)). Qed.
Lemma lem1956325 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h4 : term60 = term19 => @lem1956322 x h1 h2 h3) (fun h4 : False => @lem1955719 h3)). Qed.
Lemma lem1956326 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956325 x h1 h2 h3) (@lem1955719 h3)). Qed.
Lemma lem1956327 (x : real) (h1 : term44 x) (h2 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h3 : term60 = term19 => @lem1956324 x h1 h2) (fun h3 : False => @lem1955763 h2)). Qed.
Lemma lem1956328 (x : real) (h1 : term44 x) (h2 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956327 x h1 h2) (@lem1955763 h2)). Qed.
Lemma lem1956329 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h4 : term60 = term19 => @lem1956326 x h1 h2 h3) (fun h4 : False => @lem1955719 h3)). Qed.
Lemma lem1956330 (x : real) (h1 : term10) (h2 : term40 x) (h3 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956329 x h1 h2 h3) (@lem1955719 h3)). Qed.
Lemma lem1956331 (x : real) (h1 : term10) (h2 : term60 = term19) (h3 : term22 x) : False.
Proof. exact (or_elim (@lem1955707 x h3) (fun h0 : term40 x => @lem1956330 x h1 h0 h2) (fun h0 : term44 x => @lem1956328 x h0 h2)). Qed.
Lemma lem1956332 (x : real) (h1 : term10) (h2 : term60 = term19) (h3 : term22 x) : (term22 x) = False.
Proof. exact (prop_ext (fun h4 : term22 x => @lem1956331 x h1 h2 h3) (fun h4 : False => @lem1955707 x h3)). Qed.
Lemma lem1956333 (x : real) (h1 : term10) (h2 : term60 = term19) (h3 : term22 x) : False.
Proof. exact (EQ_MP (@lem1956332 x h1 h2 h3) (@lem1955707 x h3)). Qed.
Lemma lem1956334 (x : real) (h1 : term10) (h2 : term60 = term19) (h3 : term22 x) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h4 : term60 = term19 => @lem1956333 x h1 h2 h3) (fun h4 : False => @lem1955591 h2)). Qed.
Lemma lem1956335 (x : real) (h1 : term10) (h2 : term60 = term19) (h3 : term22 x) : False.
Proof. exact (EQ_MP (@lem1956334 x h1 h2 h3) (@lem1955591 h2)). Qed.
Lemma lem1956336 (h1 : term10) (h2 : term3) (h3 : term60 = term19) : False.
Proof. exact (ex_elim (@lem1955277 h2) (fun x : real => fun h0 : term29 x => @lem1956335 x h1 h3 h0)). Qed.
Lemma lem1956337 (h1 : term10) (h2 : term3) (h3 : term60 = term19) : (term60 = term19) = False.
Proof. exact (prop_ext (fun h4 : term60 = term19 => @lem1956336 h1 h2 h3) (fun h4 : False => @lem1955283 h3)). Qed.
Lemma lem1956338 (h1 : term10) (h2 : term3) (h3 : term60 = term19) : False.
Proof. exact (EQ_MP (@lem1956337 h1 h2 h3) (@lem1955283 h3)). Qed.
Lemma lem1956339 (h1 : term3) (h2 : term60 = term19) : term8.
Proof. exact (fun h0 : term10 => @lem1956338 h0 h1 h2). Qed.
Lemma lem1956340 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1956341 (h1 : term3) (h2 : term60 = term19) : term9.
Proof. exact (EQ_MP (@lem1956340) (@lem1956339 h1 h2)). Qed.
Lemma lem1956342 (h1 : term3) : term13.
Proof. exact (fun h0 : term60 = term19 => @lem1956341 h1 h0). Qed.
Lemma lem1956343 : term15.
Proof. exact (fun h0 : term3 => @lem1956342 h0). Qed.
Lemma lem1956344 : term4.
Proof. exact (EQ_MP (@lem1955096) (@lem1956343)). Qed.
Lemma lem1956346 : term4.
Proof. exact (@lem1955009 (@lem1956344)). Qed.
Lemma lem1956347 (h1 : term3) : term12.
Proof. exact (@lem1956346 (@lem1954994 h1)). Qed.
Lemma lem1956348 (h1 : term3) : term8.
Proof. exact (@lem1956347 h1 (@lem1902755)). Qed.
Lemma lem1956349 (h1 : term3) : False.
Proof. exact (@lem1956348 h1 (@lem1954979)). Qed.
Lemma lem1956350 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1956349 h1) (fun h2 : False => @lem1954994 h1)). Qed.
Lemma lem1956351 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1956350 h1) (@lem1954994 h1)). Qed.
Lemma lem1956352 : term2.
Proof. exact (fun h0 : term3 => @lem1956351 h0). Qed.
Lemma lem1956353 : term1.
Proof. exact (EQ_MP (@lem1954993) (@lem1956352)). Qed.
