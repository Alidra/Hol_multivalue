Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_2_DIVIDES_MUL_term_abbrevs.
Require Import INT_MUL_REM_spec.
Require Import INT_REM_2_CASES_spec.
Require Import INT_REM_2_DIVIDES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1011471_spec.
Require Import thm1011992_spec.
Require Import thm1013352_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2403914_spec.
Require Import thm2404231_spec.
Require Import thm2405481_spec.
Require Import thm2405621_spec.
Require Import thm2405758_spec.
Require Import thm2405764_spec.
Require Import thm2406280_spec.
Require Import thm2406442_spec.
Require Import thm2743639_spec.
Require Import thm706819_spec.
Require Import thm706821_spec.
Require Import thm706883_spec.
Require Import thm912739_spec.
Require Import thm912741_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Lemma lem2745114 (n : int) : term0 n.
Proof. exact (@lem2716252 n). Qed.
Lemma lem2745115 (n : int) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2745116 (n : int) : term1 n.
Proof. exact (EQ_MP (@lem2745115 n) (@lem2745114 n)). Qed.
Lemma lem2745119 (m : int) : term0 m.
Proof. exact (@lem2716252 m). Qed.
Lemma lem2745120 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2745121 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2745120 m) (@lem2745119 m)). Qed.
Lemma lem2745127 (m : int) (n : int) (p : int) (h1 : (term2 m n p) = (term3 m n p)) : (term2 m n p) = (term3 m n p).
Proof. exact (h1). Qed.
Lemma lem2745128 (m : int) (n : int) (p : int) (h1 : (term2 m n p) = (term3 m n p)) : (term3 m n p) = (term2 m n p).
Proof. exact (SYM (@lem2745127 m n p h1)). Qed.
Lemma lem2745129 (m : int) (n : int) (p : int) (h1 : (term3 m n p) = (term2 m n p)) : (term3 m n p) = (term2 m n p).
Proof. exact (h1). Qed.
Lemma lem2745130 (m : int) (n : int) (p : int) (h1 : (term3 m n p) = (term2 m n p)) : (term2 m n p) = (term3 m n p).
Proof. exact (SYM (@lem2745129 m n p h1)). Qed.
Lemma lem2745131 (m : int) (n : int) (p : int) : ((term2 m n p) = (term3 m n p)) = ((term3 m n p) = (term2 m n p)).
Proof. exact (prop_ext (fun h1 : (term2 m n p) = (term3 m n p) => @lem2745128 m n p h1) (fun h1 : (term3 m n p) = (term2 m n p) => @lem2745130 m n p h1)). Qed.
Lemma lem2745132 (m : int) (n : int) : (term4 m n) = (term5 m n).
Proof. exact (fun_ext (fun p : int => @lem2745131 m n p)). Qed.
Lemma lem2745133 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2745134 (m : int) (n : int) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2745133) (@lem2745132 m n)). Qed.
Lemma lem2745135 (m : int) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : int => @lem2745134 m n)). Qed.
Lemma lem2745136 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2745137 (m : int) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem2745136) (@lem2745135 m)). Qed.
Lemma lem2745138 : term12 = term13.
Proof. exact (fun_ext (fun m : int => @lem2745137 m)). Qed.
Lemma lem2745139 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2745140 : term14 = term15.
Proof. exact (MK_COMB (@lem2745139) (@lem2745138)). Qed.
Lemma lem2745141 : term15.
Proof. exact (EQ_MP (@lem2745140) (@lem2537472)). Qed.
Lemma lem2745142 (m : int) : term16 m.
Proof. exact (@lem2745141 m). Qed.
Lemma lem2745143 (m : int) : (term16 m) = (term11 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem2745144 (m : int) : term11 m.
Proof. exact (EQ_MP (@lem2745143 m) (@lem2745142 m)). Qed.
Lemma lem2745145 (m : int) (n : int) : term17 m n.
Proof. exact (@lem2745144 m n). Qed.
Lemma lem2745146 (m : int) (n : int) : (term17 m n) = (term7 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem2745147 (m : int) (n : int) : term7 m n.
Proof. exact (EQ_MP (@lem2745146 m n) (@lem2745145 m n)). Qed.
Lemma lem2745148 (m : int) (n : int) (p : int) : term18 m n p.
Proof. exact (@lem2745147 m n p). Qed.
Lemma lem2745149 (m : int) (n : int) (p : int) : (term18 m n p) = ((term3 m n p) = (term2 m n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem2745153 (n : int) (h1 : ((term19 n) = term20) = (term21 n)) : ((term19 n) = term20) = (term21 n).
Proof. exact (h1). Qed.
Lemma lem2745154 (n : int) (h1 : ((term19 n) = term20) = (term21 n)) : (term21 n) = ((term19 n) = term20).
Proof. exact (SYM (@lem2745153 n h1)). Qed.
Lemma lem2745155 (n : int) (h1 : (term21 n) = ((term19 n) = term20)) : (term21 n) = ((term19 n) = term20).
Proof. exact (h1). Qed.
Lemma lem2745156 (n : int) (h1 : (term21 n) = ((term19 n) = term20)) : ((term19 n) = term20) = (term21 n).
Proof. exact (SYM (@lem2745155 n h1)). Qed.
Lemma lem2745157 (n : int) : (((term19 n) = term20) = (term21 n)) = ((term21 n) = ((term19 n) = term20)).
Proof. exact (prop_ext (fun h1 : ((term19 n) = term20) = (term21 n) => @lem2745154 n h1) (fun h1 : (term21 n) = ((term19 n) = term20) => @lem2745156 n h1)). Qed.
Lemma lem2745158 : term22 = term23.
Proof. exact (fun_ext (fun n : int => @lem2745157 n)). Qed.
Lemma lem2745159 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2745160 : term24 = term25.
Proof. exact (MK_COMB (@lem2745159) (@lem2745158)). Qed.
Lemma lem2745161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2745162 : term26 = term27.
Proof. exact (MK_COMB (@lem2745161) (@lem2745160)). Qed.
Lemma lem2745164 (n : int) (h1 : ((term19 n) = term28) = (term29 n)) : ((term19 n) = term28) = (term29 n).
Proof. exact (h1). Qed.
Lemma lem2745165 (n : int) (h1 : ((term19 n) = term28) = (term29 n)) : (term29 n) = ((term19 n) = term28).
Proof. exact (SYM (@lem2745164 n h1)). Qed.
Lemma lem2745166 (n : int) (h1 : (term29 n) = ((term19 n) = term28)) : (term29 n) = ((term19 n) = term28).
Proof. exact (h1). Qed.
Lemma lem2745167 (n : int) (h1 : (term29 n) = ((term19 n) = term28)) : ((term19 n) = term28) = (term29 n).
Proof. exact (SYM (@lem2745166 n h1)). Qed.
Lemma lem2745168 (n : int) : (((term19 n) = term28) = (term29 n)) = ((term29 n) = ((term19 n) = term28)).
Proof. exact (prop_ext (fun h1 : ((term19 n) = term28) = (term29 n) => @lem2745165 n h1) (fun h1 : (term29 n) = ((term19 n) = term28) => @lem2745167 n h1)). Qed.
Lemma lem2745169 : term30 = term31.
Proof. exact (fun_ext (fun n : int => @lem2745168 n)). Qed.
Lemma lem2745170 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2745171 : term32 = term33.
Proof. exact (MK_COMB (@lem2745170) (@lem2745169)). Qed.
Lemma lem2745172 : term34 = term35.
Proof. exact (MK_COMB (@lem2745162) (@lem2745171)). Qed.
Lemma lem2745173 : term35.
Proof. exact (EQ_MP (@lem2745172) (@lem2725348)). Qed.
Lemma lem2745178 : term25.
Proof. exact (proj1 (@lem2745173)). Qed.
Lemma lem2745179 (n : int) : term36 n.
Proof. exact (@lem2745178 n). Qed.
Lemma lem2745180 (n : int) : (term36 n) = ((term21 n) = ((term19 n) = term20)).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem2745185 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2745180 n) (@lem2745179 n)). Qed.
Lemma lem2745186 (m : int) (n : int) : (term37 m n) = ((term38 m n) = term20).
Proof. exact (@lem2745185 (int_mul m n)). Qed.
Lemma lem2745189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745190 (m : int) (n : int) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2745189) (@lem2745186 m n)). Qed.
Lemma lem2745194 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2745180 n) (@lem2745179 n)). Qed.
Lemma lem2745195 (m : int) : (term21 m) = ((term19 m) = term20).
Proof. exact (@lem2745194 m). Qed.
Lemma lem2745198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2745199 (m : int) : (term41 m) = (term42 m).
Proof. exact (MK_COMB (@lem2745198) (@lem2745195 m)). Qed.
Lemma lem2745201 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2745180 n) (@lem2745179 n)). Qed.
Lemma lem2745204 (m : int) (n : int) : (term43 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem2745199 m) (@lem2745201 n)). Qed.
Lemma lem2745207 (m : int) (n : int) : ((term37 m n) = (term43 m n)) = (((term38 m n) = term20) = (term44 m n)).
Proof. exact (MK_COMB (@lem2745190 m n) (@lem2745204 m n)). Qed.
Lemma lem2745210 (m : int) (n : int) : (((term38 m n) = term20) = (term44 m n)) = ((term37 m n) = (term43 m n)).
Proof. exact (SYM (@lem2745207 m n)). Qed.
Lemma lem2745216 (m : int) (n : int) (p : int) : (term3 m n p) = (term2 m n p).
Proof. exact (EQ_MP (@lem2745149 m n p) (@lem2745148 m n p)). Qed.
Lemma lem2745217 (m : int) (n : int) : (term38 m n) = (term45 m n).
Proof. exact (@lem2745216 m n term46). Qed.
Lemma lem2745218 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745219 (m : int) (n : int) : (term47 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem2745218) (@lem2745217 m n)). Qed.
Lemma lem2745220 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745221 (m : int) (n : int) : ((term38 m n) = term20) = ((term45 m n) = term20).
Proof. exact (MK_COMB (@lem2745219 m n) (@lem2745220)). Qed.
Lemma lem2745222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745223 (m : int) (n : int) : (term40 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem2745222) (@lem2745221 m n)). Qed.
Lemma lem2745230 (m : int) (n : int) : (term44 m n) = (term44 m n).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem2745231 (m : int) (n : int) : (((term38 m n) = term20) = (term44 m n)) = (((term45 m n) = term20) = (term44 m n)).
Proof. exact (MK_COMB (@lem2745223 m n) (@lem2745230 m n)). Qed.
Lemma lem2745232 (m : int) (n : int) : (((term45 m n) = term20) = (term44 m n)) = (((term38 m n) = term20) = (term44 m n)).
Proof. exact (SYM (@lem2745231 m n)). Qed.
Lemma lem2745238 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2745239 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2745240 (m : int) (h1 : (term19 m) = term20) : (term50 m) = term51.
Proof. exact (MK_COMB (@lem2745239) (@lem2745238 m h1)). Qed.
Lemma lem2745242 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2745243 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term52 m n) = term53.
Proof. exact (MK_COMB (@lem2745240 m h1) (@lem2745242 n h2)). Qed.
Lemma lem2745244 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745245 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term54 m n) = term55.
Proof. exact (MK_COMB (@lem2745244) (@lem2745243 m n h1 h2)). Qed.
Lemma lem2745246 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745247 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term45 m n) = term56.
Proof. exact (MK_COMB (@lem2745245 m n h1 h2) (@lem2745246)). Qed.
Lemma lem2745248 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745249 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term48 m n) = term57.
Proof. exact (MK_COMB (@lem2745248) (@lem2745247 m n h1 h2)). Qed.
Lemma lem2745250 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745251 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : ((term45 m n) = term20) = (term56 = term20).
Proof. exact (MK_COMB (@lem2745249 m n h1 h2) (@lem2745250)). Qed.
Lemma lem2745254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745255 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term49 m n) = term58.
Proof. exact (MK_COMB (@lem2745254) (@lem2745251 m n h1 h2)). Qed.
Lemma lem2745261 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2745262 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745263 (m : int) (h1 : (term19 m) = term20) : (term59 m) = term60.
Proof. exact (MK_COMB (@lem2745262) (@lem2745261 m h1)). Qed.
Lemma lem2745264 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745265 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745263 m h1) (@lem2745264)). Qed.
Lemma lem2745267 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745268 (x : int) : (x = x) = True.
Proof. exact (@lem2745267 int x). Qed.
Lemma lem2745269 : (term20 = term20) = True.
Proof. exact (@lem2745268 term20). Qed.
Lemma lem2745270 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = True.
Proof. exact (TRANS (@lem2745265 m h1) (@lem2745269)). Qed.
Lemma lem2745271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2745272 (m : int) (h1 : (term19 m) = term20) : (term42 m) = (or True).
Proof. exact (MK_COMB (@lem2745271) (@lem2745270 m h1)). Qed.
Lemma lem2745276 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2745277 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745278 (n : int) (h1 : (term19 n) = term20) : (term59 n) = term60.
Proof. exact (MK_COMB (@lem2745277) (@lem2745276 n h1)). Qed.
Lemma lem2745279 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745280 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745278 n h1) (@lem2745279)). Qed.
Lemma lem2745282 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745283 (x : int) : (x = x) = True.
Proof. exact (@lem2745282 int x). Qed.
Lemma lem2745284 : (term20 = term20) = True.
Proof. exact (@lem2745283 term20). Qed.
Lemma lem2745285 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = True.
Proof. exact (TRANS (@lem2745280 n h1) (@lem2745284)). Qed.
Lemma lem2745286 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term44 m n) = (True \/ True).
Proof. exact (MK_COMB (@lem2745272 m h1) (@lem2745285 n h2)). Qed.
Lemma lem2745288 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2745289 : (True \/ True) = True.
Proof. exact (@lem2745288 True). Qed.
Lemma lem2745290 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term44 m n) = True.
Proof. exact (TRANS (@lem2745286 m n h1 h2) (@lem2745289)). Qed.
Lemma lem2745291 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term45 m n) = term20) = (term44 m n)) = ((term56 = term20) = True).
Proof. exact (MK_COMB (@lem2745255 m n h1 h2) (@lem2745290 m n h1 h2)). Qed.
Lemma lem2745293 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2745294 : ((term56 = term20) = True) = (term56 = term20).
Proof. exact (@lem2745293 (term56 = term20)). Qed.
Lemma lem2745297 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term45 m n) = term20) = (term44 m n)) = (term56 = term20).
Proof. exact (TRANS (@lem2745291 m n h1 h2) (@lem2745294)). Qed.
Lemma lem2745298 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term56 = term20) = (((term45 m n) = term20) = (term44 m n)).
Proof. exact (SYM (@lem2745297 m n h1 h2)). Qed.
Lemma lem2745304 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2745305 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2745306 (m : int) (h1 : (term19 m) = term20) : (term50 m) = term51.
Proof. exact (MK_COMB (@lem2745305) (@lem2745304 m h1)). Qed.
Lemma lem2745308 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2745309 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term52 m n) = term61.
Proof. exact (MK_COMB (@lem2745306 m h1) (@lem2745308 n h2)). Qed.
Lemma lem2745310 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745311 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term54 m n) = term62.
Proof. exact (MK_COMB (@lem2745310) (@lem2745309 m n h1 h2)). Qed.
Lemma lem2745312 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745313 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term45 m n) = term63.
Proof. exact (MK_COMB (@lem2745311 m n h1 h2) (@lem2745312)). Qed.
Lemma lem2745314 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745315 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term48 m n) = term64.
Proof. exact (MK_COMB (@lem2745314) (@lem2745313 m n h1 h2)). Qed.
Lemma lem2745316 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745317 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term45 m n) = term20) = (term63 = term20).
Proof. exact (MK_COMB (@lem2745315 m n h1 h2) (@lem2745316)). Qed.
Lemma lem2745320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745321 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term49 m n) = term65.
Proof. exact (MK_COMB (@lem2745320) (@lem2745317 m n h1 h2)). Qed.
Lemma lem2745327 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2745328 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745329 (m : int) (h1 : (term19 m) = term20) : (term59 m) = term60.
Proof. exact (MK_COMB (@lem2745328) (@lem2745327 m h1)). Qed.
Lemma lem2745330 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745331 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745329 m h1) (@lem2745330)). Qed.
Lemma lem2745333 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745334 (x : int) : (x = x) = True.
Proof. exact (@lem2745333 int x). Qed.
Lemma lem2745335 : (term20 = term20) = True.
Proof. exact (@lem2745334 term20). Qed.
Lemma lem2745336 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = True.
Proof. exact (TRANS (@lem2745331 m h1) (@lem2745335)). Qed.
Lemma lem2745337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2745338 (m : int) (h1 : (term19 m) = term20) : (term42 m) = (or True).
Proof. exact (MK_COMB (@lem2745337) (@lem2745336 m h1)). Qed.
Lemma lem2745342 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2745343 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745344 (n : int) (h1 : (term19 n) = term28) : (term59 n) = term66.
Proof. exact (MK_COMB (@lem2745343) (@lem2745342 n h1)). Qed.
Lemma lem2745345 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745346 (n : int) (h1 : (term19 n) = term28) : ((term19 n) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2745344 n h1) (@lem2745345)). Qed.
Lemma lem2745349 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term44 m n) = term67.
Proof. exact (MK_COMB (@lem2745338 m h1) (@lem2745346 n h2)). Qed.
Lemma lem2745351 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2745352 : term67 = True.
Proof. exact (@lem2745351 (term28 = term20)). Qed.
Lemma lem2745353 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term44 m n) = True.
Proof. exact (TRANS (@lem2745349 m n h1 h2) (@lem2745352)). Qed.
Lemma lem2745354 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term45 m n) = term20) = (term44 m n)) = ((term63 = term20) = True).
Proof. exact (MK_COMB (@lem2745321 m n h1 h2) (@lem2745353 m n h1 h2)). Qed.
Lemma lem2745356 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2745357 : ((term63 = term20) = True) = (term63 = term20).
Proof. exact (@lem2745356 (term63 = term20)). Qed.
Lemma lem2745360 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term45 m n) = term20) = (term44 m n)) = (term63 = term20).
Proof. exact (TRANS (@lem2745354 m n h1 h2) (@lem2745357)). Qed.
Lemma lem2745361 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term63 = term20) = (((term45 m n) = term20) = (term44 m n)).
Proof. exact (SYM (@lem2745360 m n h1 h2)). Qed.
Lemma lem2745367 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2745368 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2745369 (m : int) (h1 : (term19 m) = term28) : (term50 m) = term68.
Proof. exact (MK_COMB (@lem2745368) (@lem2745367 m h1)). Qed.
Lemma lem2745371 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2745372 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term52 m n) = term69.
Proof. exact (MK_COMB (@lem2745369 m h1) (@lem2745371 n h2)). Qed.
Lemma lem2745373 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745374 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term54 m n) = term70.
Proof. exact (MK_COMB (@lem2745373) (@lem2745372 m n h1 h2)). Qed.
Lemma lem2745375 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745376 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term45 m n) = term71.
Proof. exact (MK_COMB (@lem2745374 m n h1 h2) (@lem2745375)). Qed.
Lemma lem2745377 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745378 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term48 m n) = term72.
Proof. exact (MK_COMB (@lem2745377) (@lem2745376 m n h1 h2)). Qed.
Lemma lem2745379 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745380 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term45 m n) = term20) = (term71 = term20).
Proof. exact (MK_COMB (@lem2745378 m n h1 h2) (@lem2745379)). Qed.
Lemma lem2745383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745384 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term49 m n) = term73.
Proof. exact (MK_COMB (@lem2745383) (@lem2745380 m n h1 h2)). Qed.
Lemma lem2745390 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2745391 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745392 (m : int) (h1 : (term19 m) = term28) : (term59 m) = term66.
Proof. exact (MK_COMB (@lem2745391) (@lem2745390 m h1)). Qed.
Lemma lem2745393 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745394 (m : int) (h1 : (term19 m) = term28) : ((term19 m) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2745392 m h1) (@lem2745393)). Qed.
Lemma lem2745397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2745398 (m : int) (h1 : (term19 m) = term28) : (term42 m) = term74.
Proof. exact (MK_COMB (@lem2745397) (@lem2745394 m h1)). Qed.
Lemma lem2745402 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2745403 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745404 (n : int) (h1 : (term19 n) = term20) : (term59 n) = term60.
Proof. exact (MK_COMB (@lem2745403) (@lem2745402 n h1)). Qed.
Lemma lem2745405 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745406 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745404 n h1) (@lem2745405)). Qed.
Lemma lem2745408 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745409 (x : int) : (x = x) = True.
Proof. exact (@lem2745408 int x). Qed.
Lemma lem2745410 : (term20 = term20) = True.
Proof. exact (@lem2745409 term20). Qed.
Lemma lem2745411 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = True.
Proof. exact (TRANS (@lem2745406 n h1) (@lem2745410)). Qed.
Lemma lem2745412 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term44 m n) = term75.
Proof. exact (MK_COMB (@lem2745398 m h1) (@lem2745411 n h2)). Qed.
Lemma lem2745414 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem2745415 : term75 = True.
Proof. exact (@lem2745414 (term28 = term20)). Qed.
Lemma lem2745416 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term44 m n) = True.
Proof. exact (TRANS (@lem2745412 m n h1 h2) (@lem2745415)). Qed.
Lemma lem2745417 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term45 m n) = term20) = (term44 m n)) = ((term71 = term20) = True).
Proof. exact (MK_COMB (@lem2745384 m n h1 h2) (@lem2745416 m n h1 h2)). Qed.
Lemma lem2745419 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2745420 : ((term71 = term20) = True) = (term71 = term20).
Proof. exact (@lem2745419 (term71 = term20)). Qed.
Lemma lem2745423 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term45 m n) = term20) = (term44 m n)) = (term71 = term20).
Proof. exact (TRANS (@lem2745417 m n h1 h2) (@lem2745420)). Qed.
Lemma lem2745424 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term71 = term20) = (((term45 m n) = term20) = (term44 m n)).
Proof. exact (SYM (@lem2745423 m n h1 h2)). Qed.
Lemma lem2745430 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2745431 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2745432 (m : int) (h1 : (term19 m) = term28) : (term50 m) = term68.
Proof. exact (MK_COMB (@lem2745431) (@lem2745430 m h1)). Qed.
Lemma lem2745434 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2745435 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term52 m n) = term76.
Proof. exact (MK_COMB (@lem2745432 m h1) (@lem2745434 n h2)). Qed.
Lemma lem2745436 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745437 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term54 m n) = term77.
Proof. exact (MK_COMB (@lem2745436) (@lem2745435 m n h1 h2)). Qed.
Lemma lem2745438 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745439 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term45 m n) = term78.
Proof. exact (MK_COMB (@lem2745437 m n h1 h2) (@lem2745438)). Qed.
Lemma lem2745440 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745441 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term48 m n) = term79.
Proof. exact (MK_COMB (@lem2745440) (@lem2745439 m n h1 h2)). Qed.
Lemma lem2745442 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745443 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : ((term45 m n) = term20) = (term78 = term20).
Proof. exact (MK_COMB (@lem2745441 m n h1 h2) (@lem2745442)). Qed.
Lemma lem2745446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745447 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term49 m n) = term80.
Proof. exact (MK_COMB (@lem2745446) (@lem2745443 m n h1 h2)). Qed.
Lemma lem2745453 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2745454 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745455 (m : int) (h1 : (term19 m) = term28) : (term59 m) = term66.
Proof. exact (MK_COMB (@lem2745454) (@lem2745453 m h1)). Qed.
Lemma lem2745456 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745457 (m : int) (h1 : (term19 m) = term28) : ((term19 m) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2745455 m h1) (@lem2745456)). Qed.
Lemma lem2745460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2745461 (m : int) (h1 : (term19 m) = term28) : (term42 m) = term74.
Proof. exact (MK_COMB (@lem2745460) (@lem2745457 m h1)). Qed.
Lemma lem2745465 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2745466 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745467 (n : int) (h1 : (term19 n) = term28) : (term59 n) = term66.
Proof. exact (MK_COMB (@lem2745466) (@lem2745465 n h1)). Qed.
Lemma lem2745468 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745469 (n : int) (h1 : (term19 n) = term28) : ((term19 n) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2745467 n h1) (@lem2745468)). Qed.
Lemma lem2745472 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term44 m n) = term81.
Proof. exact (MK_COMB (@lem2745461 m h1) (@lem2745469 n h2)). Qed.
Lemma lem2745474 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem2745475 : term81 = (term28 = term20).
Proof. exact (@lem2745474 (term28 = term20)). Qed.
Lemma lem2745478 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term44 m n) = (term28 = term20).
Proof. exact (TRANS (@lem2745472 m n h1 h2) (@lem2745475)). Qed.
Lemma lem2745479 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term45 m n) = term20) = (term44 m n)) = ((term78 = term20) = (term28 = term20)).
Proof. exact (MK_COMB (@lem2745447 m n h1 h2) (@lem2745478 m n h1 h2)). Qed.
Lemma lem2745482 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : ((term78 = term20) = (term28 = term20)) = (((term45 m n) = term20) = (term44 m n)).
Proof. exact (SYM (@lem2745479 m n h1 h2)). Qed.
Lemma lem2745484 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745485 : term53 = term20.
Proof. exact (@lem2745484 (NUMERAL 0)). Qed.
Lemma lem2745486 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745487 : term55 = term83.
Proof. exact (MK_COMB (@lem2745486) (@lem2745485)). Qed.
Lemma lem2745488 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745489 : term56 = term84.
Proof. exact (MK_COMB (@lem2745487) (@lem2745488)). Qed.
Lemma lem2745490 : term85.
Proof. exact (@lem2743639 term20 term20 term46 term20). Qed.
Lemma lem2745492 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745493 : term86 = term20.
Proof. exact (@lem2745492 term87). Qed.
Lemma lem2745494 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2745495 : term88 = term89.
Proof. exact (MK_COMB (@lem2745494) (@lem2745493)). Qed.
Lemma lem2745496 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745497 : term90 = term91.
Proof. exact (MK_COMB (@lem2745495) (@lem2745496)). Qed.
Lemma lem2745498 : term91 = term92.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745499 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2745500 : ((Nat.add 0 0) = 0) = (term93 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2745501 : term93 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2745500) (@lem2745499)). Qed.
Lemma lem2745502 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2745503 : term92 = term20.
Proof. exact (MK_COMB (@lem2745502) (@lem2745501)). Qed.
Lemma lem2745504 : term91 = term20.
Proof. exact (TRANS (@lem2745498) (@lem2745503)). Qed.
Lemma lem2745505 : term90 = term20.
Proof. exact (TRANS (@lem2745497) (@lem2745504)). Qed.
Lemma lem2745506 : term94.
Proof. exact (@lem2745490 (@lem2745505)). Qed.
Lemma lem2745508 (m : nat) (n : nat) : (term95 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2745509 : term96 = term97.
Proof. exact (@lem2745508 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745510 : term97 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem2745511 : term96 = True.
Proof. exact (TRANS (@lem2745509) (@lem2745510)). Qed.
Lemma lem2745512 : True = term96.
Proof. exact (SYM (@lem2745511)). Qed.
Lemma lem2745513 : term96.
Proof. exact (EQ_MP (@lem2745512) (@lem0)). Qed.
Lemma lem2745514 : term98.
Proof. exact (@lem2745506 (@lem2745513)). Qed.
Lemma lem2745516 (x : nat) : (term99 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2745517 : term100 = term46.
Proof. exact (@lem2745516 term87). Qed.
Lemma lem2745518 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem2745519 : term102 = term103.
Proof. exact (MK_COMB (@lem2745518) (@lem2745517)). Qed.
Lemma lem2745521 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2745522 : term103 = term105.
Proof. exact (@lem2745521 (NUMERAL 0) term87). Qed.
Lemma lem2745523 : term106 = term107.
Proof. exact (@lem912803). Qed.
Lemma lem2745524 (h1 : term106 = term107) : term105 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term107 h1). Qed.
Lemma lem2745525 : (term106 = term107) = (term105 = True).
Proof. exact (prop_ext (fun h1 : term106 = term107 => @lem2745524 h1) (fun h1 : term105 = True => @lem2745523)). Qed.
Lemma lem2745526 : term105 = True.
Proof. exact (EQ_MP (@lem2745525) (@lem2745523)). Qed.
Lemma lem2745527 : term103 = True.
Proof. exact (TRANS (@lem2745522) (@lem2745526)). Qed.
Lemma lem2745528 : term102 = True.
Proof. exact (TRANS (@lem2745519) (@lem2745527)). Qed.
Lemma lem2745529 : True = term102.
Proof. exact (SYM (@lem2745528)). Qed.
Lemma lem2745530 : term102.
Proof. exact (EQ_MP (@lem2745529) (@lem0)). Qed.
Lemma lem2745531 : term108.
Proof. exact (@lem2745514 (@lem2745530)). Qed.
Lemma lem2745532 : term84 = term20.
Proof. exact (proj2 (@lem2745531)). Qed.
Lemma lem2745533 : term56 = term20.
Proof. exact (TRANS (@lem2745489) (@lem2745532)). Qed.
Lemma lem2745534 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745535 : term57 = term60.
Proof. exact (MK_COMB (@lem2745534) (@lem2745533)). Qed.
Lemma lem2745536 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745537 : (term56 = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745535) (@lem2745536)). Qed.
Lemma lem2745539 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745540 (x : int) : (x = x) = True.
Proof. exact (@lem2745539 int x). Qed.
Lemma lem2745541 : (term20 = term20) = True.
Proof. exact (@lem2745540 term20). Qed.
Lemma lem2745542 : (term56 = term20) = True.
Proof. exact (TRANS (@lem2745537) (@lem2745541)). Qed.
Lemma lem2745543 : True = (term56 = term20).
Proof. exact (SYM (@lem2745542)). Qed.
Lemma lem2745544 : term56 = term20.
Proof. exact (EQ_MP (@lem2745543) (@lem0)). Qed.
Lemma lem2745546 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745547 : term61 = term20.
Proof. exact (@lem2745546 term109). Qed.
Lemma lem2745548 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745549 : term62 = term83.
Proof. exact (MK_COMB (@lem2745548) (@lem2745547)). Qed.
Lemma lem2745550 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745551 : term63 = term84.
Proof. exact (MK_COMB (@lem2745549) (@lem2745550)). Qed.
Lemma lem2745552 : term85.
Proof. exact (@lem2743639 term20 term20 term46 term20). Qed.
Lemma lem2745554 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745555 : term86 = term20.
Proof. exact (@lem2745554 term87). Qed.
Lemma lem2745556 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2745557 : term88 = term89.
Proof. exact (MK_COMB (@lem2745556) (@lem2745555)). Qed.
Lemma lem2745558 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745559 : term90 = term91.
Proof. exact (MK_COMB (@lem2745557) (@lem2745558)). Qed.
Lemma lem2745560 : term91 = term92.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745561 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2745562 : ((Nat.add 0 0) = 0) = (term93 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2745563 : term93 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2745562) (@lem2745561)). Qed.
Lemma lem2745564 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2745565 : term92 = term20.
Proof. exact (MK_COMB (@lem2745564) (@lem2745563)). Qed.
Lemma lem2745566 : term91 = term20.
Proof. exact (TRANS (@lem2745560) (@lem2745565)). Qed.
Lemma lem2745567 : term90 = term20.
Proof. exact (TRANS (@lem2745559) (@lem2745566)). Qed.
Lemma lem2745568 : term94.
Proof. exact (@lem2745552 (@lem2745567)). Qed.
Lemma lem2745570 (m : nat) (n : nat) : (term95 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2745571 : term96 = term97.
Proof. exact (@lem2745570 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745572 : term97 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem2745573 : term96 = True.
Proof. exact (TRANS (@lem2745571) (@lem2745572)). Qed.
Lemma lem2745574 : True = term96.
Proof. exact (SYM (@lem2745573)). Qed.
Lemma lem2745575 : term96.
Proof. exact (EQ_MP (@lem2745574) (@lem0)). Qed.
Lemma lem2745576 : term98.
Proof. exact (@lem2745568 (@lem2745575)). Qed.
Lemma lem2745578 (x : nat) : (term99 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2745579 : term100 = term46.
Proof. exact (@lem2745578 term87). Qed.
Lemma lem2745580 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem2745581 : term102 = term103.
Proof. exact (MK_COMB (@lem2745580) (@lem2745579)). Qed.
Lemma lem2745583 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2745584 : term103 = term105.
Proof. exact (@lem2745583 (NUMERAL 0) term87). Qed.
Lemma lem2745585 : term106 = term107.
Proof. exact (@lem912803). Qed.
Lemma lem2745586 (h1 : term106 = term107) : term105 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term107 h1). Qed.
Lemma lem2745587 : (term106 = term107) = (term105 = True).
Proof. exact (prop_ext (fun h1 : term106 = term107 => @lem2745586 h1) (fun h1 : term105 = True => @lem2745585)). Qed.
Lemma lem2745588 : term105 = True.
Proof. exact (EQ_MP (@lem2745587) (@lem2745585)). Qed.
Lemma lem2745589 : term103 = True.
Proof. exact (TRANS (@lem2745584) (@lem2745588)). Qed.
Lemma lem2745590 : term102 = True.
Proof. exact (TRANS (@lem2745581) (@lem2745589)). Qed.
Lemma lem2745591 : True = term102.
Proof. exact (SYM (@lem2745590)). Qed.
Lemma lem2745592 : term102.
Proof. exact (EQ_MP (@lem2745591) (@lem0)). Qed.
Lemma lem2745593 : term108.
Proof. exact (@lem2745576 (@lem2745592)). Qed.
Lemma lem2745594 : term84 = term20.
Proof. exact (proj2 (@lem2745593)). Qed.
Lemma lem2745595 : term63 = term20.
Proof. exact (TRANS (@lem2745551) (@lem2745594)). Qed.
Lemma lem2745596 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745597 : term64 = term60.
Proof. exact (MK_COMB (@lem2745596) (@lem2745595)). Qed.
Lemma lem2745598 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745599 : (term63 = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745597) (@lem2745598)). Qed.
Lemma lem2745601 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745602 (x : int) : (x = x) = True.
Proof. exact (@lem2745601 int x). Qed.
Lemma lem2745603 : (term20 = term20) = True.
Proof. exact (@lem2745602 term20). Qed.
Lemma lem2745604 : (term63 = term20) = True.
Proof. exact (TRANS (@lem2745599) (@lem2745603)). Qed.
Lemma lem2745605 : True = (term63 = term20).
Proof. exact (SYM (@lem2745604)). Qed.
Lemma lem2745606 : term63 = term20.
Proof. exact (EQ_MP (@lem2745605) (@lem0)). Qed.
Lemma lem2745608 (x : nat) : (term110 x) = term20.
Proof. exact (proj1 (@lem2405764 x)). Qed.
Lemma lem2745609 : term69 = term20.
Proof. exact (@lem2745608 term109). Qed.
Lemma lem2745610 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745611 : term70 = term83.
Proof. exact (MK_COMB (@lem2745610) (@lem2745609)). Qed.
Lemma lem2745612 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745613 : term71 = term84.
Proof. exact (MK_COMB (@lem2745611) (@lem2745612)). Qed.
Lemma lem2745614 : term85.
Proof. exact (@lem2743639 term20 term20 term46 term20). Qed.
Lemma lem2745616 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745617 : term86 = term20.
Proof. exact (@lem2745616 term87). Qed.
Lemma lem2745618 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2745619 : term88 = term89.
Proof. exact (MK_COMB (@lem2745618) (@lem2745617)). Qed.
Lemma lem2745620 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745621 : term90 = term91.
Proof. exact (MK_COMB (@lem2745619) (@lem2745620)). Qed.
Lemma lem2745622 : term91 = term92.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745623 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2745624 : ((Nat.add 0 0) = 0) = (term93 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2745625 : term93 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2745624) (@lem2745623)). Qed.
Lemma lem2745626 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2745627 : term92 = term20.
Proof. exact (MK_COMB (@lem2745626) (@lem2745625)). Qed.
Lemma lem2745628 : term91 = term20.
Proof. exact (TRANS (@lem2745622) (@lem2745627)). Qed.
Lemma lem2745629 : term90 = term20.
Proof. exact (TRANS (@lem2745621) (@lem2745628)). Qed.
Lemma lem2745630 : term94.
Proof. exact (@lem2745614 (@lem2745629)). Qed.
Lemma lem2745632 (m : nat) (n : nat) : (term95 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2745633 : term96 = term97.
Proof. exact (@lem2745632 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745634 : term97 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem2745635 : term96 = True.
Proof. exact (TRANS (@lem2745633) (@lem2745634)). Qed.
Lemma lem2745636 : True = term96.
Proof. exact (SYM (@lem2745635)). Qed.
Lemma lem2745637 : term96.
Proof. exact (EQ_MP (@lem2745636) (@lem0)). Qed.
Lemma lem2745638 : term98.
Proof. exact (@lem2745630 (@lem2745637)). Qed.
Lemma lem2745640 (x : nat) : (term99 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2745641 : term100 = term46.
Proof. exact (@lem2745640 term87). Qed.
Lemma lem2745642 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem2745643 : term102 = term103.
Proof. exact (MK_COMB (@lem2745642) (@lem2745641)). Qed.
Lemma lem2745645 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2745646 : term103 = term105.
Proof. exact (@lem2745645 (NUMERAL 0) term87). Qed.
Lemma lem2745647 : term106 = term107.
Proof. exact (@lem912803). Qed.
Lemma lem2745648 (h1 : term106 = term107) : term105 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term107 h1). Qed.
Lemma lem2745649 : (term106 = term107) = (term105 = True).
Proof. exact (prop_ext (fun h1 : term106 = term107 => @lem2745648 h1) (fun h1 : term105 = True => @lem2745647)). Qed.
Lemma lem2745650 : term105 = True.
Proof. exact (EQ_MP (@lem2745649) (@lem2745647)). Qed.
Lemma lem2745651 : term103 = True.
Proof. exact (TRANS (@lem2745646) (@lem2745650)). Qed.
Lemma lem2745652 : term102 = True.
Proof. exact (TRANS (@lem2745643) (@lem2745651)). Qed.
Lemma lem2745653 : True = term102.
Proof. exact (SYM (@lem2745652)). Qed.
Lemma lem2745654 : term102.
Proof. exact (EQ_MP (@lem2745653) (@lem0)). Qed.
Lemma lem2745655 : term108.
Proof. exact (@lem2745638 (@lem2745654)). Qed.
Lemma lem2745656 : term84 = term20.
Proof. exact (proj2 (@lem2745655)). Qed.
Lemma lem2745657 : term71 = term20.
Proof. exact (TRANS (@lem2745613) (@lem2745656)). Qed.
Lemma lem2745658 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745659 : term72 = term60.
Proof. exact (MK_COMB (@lem2745658) (@lem2745657)). Qed.
Lemma lem2745660 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745661 : (term71 = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745659) (@lem2745660)). Qed.
Lemma lem2745663 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745664 (x : int) : (x = x) = True.
Proof. exact (@lem2745663 int x). Qed.
Lemma lem2745665 : (term20 = term20) = True.
Proof. exact (@lem2745664 term20). Qed.
Lemma lem2745666 : (term71 = term20) = True.
Proof. exact (TRANS (@lem2745661) (@lem2745665)). Qed.
Lemma lem2745667 : True = (term71 = term20).
Proof. exact (SYM (@lem2745666)). Qed.
Lemma lem2745668 : term71 = term20.
Proof. exact (EQ_MP (@lem2745667) (@lem0)). Qed.
Lemma lem2745670 (m : nat) (n : nat) : (term111 m n) = (term112 m n).
Proof. exact (proj1 (@lem2405758 m n)). Qed.
Lemma lem2745671 : term76 = term113.
Proof. exact (@lem2745670 term109 term109). Qed.
Lemma lem2745672 : (term114 = (BIT1 0)) = (term115 = term109).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2745673 : term115 = term109.
Proof. exact (EQ_MP (@lem2745672) (@lem940073)). Qed.
Lemma lem2745674 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2745675 : term113 = term28.
Proof. exact (MK_COMB (@lem2745674) (@lem2745673)). Qed.
Lemma lem2745676 : term76 = term28.
Proof. exact (TRANS (@lem2745671) (@lem2745675)). Qed.
Lemma lem2745677 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745678 : term77 = term116.
Proof. exact (MK_COMB (@lem2745677) (@lem2745676)). Qed.
Lemma lem2745679 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2745680 : term78 = term117.
Proof. exact (MK_COMB (@lem2745678) (@lem2745679)). Qed.
Lemma lem2745681 : term118.
Proof. exact (@lem2743639 term20 term28 term46 term28). Qed.
Lemma lem2745683 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745684 : term86 = term20.
Proof. exact (@lem2745683 term87). Qed.
Lemma lem2745685 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2745686 : term88 = term89.
Proof. exact (MK_COMB (@lem2745685) (@lem2745684)). Qed.
Lemma lem2745687 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2745688 : term119 = term120.
Proof. exact (MK_COMB (@lem2745686) (@lem2745687)). Qed.
Lemma lem2745689 : term120 = term121.
Proof. exact (@lem2406280 (NUMERAL 0) term109). Qed.
Lemma lem2745690 : term122 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem2745691 : (term122 = (BIT1 0)) = (term123 = term109).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2745692 : term123 = term109.
Proof. exact (EQ_MP (@lem2745691) (@lem2745690)). Qed.
Lemma lem2745693 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2745694 : term121 = term28.
Proof. exact (MK_COMB (@lem2745693) (@lem2745692)). Qed.
Lemma lem2745695 : term120 = term28.
Proof. exact (TRANS (@lem2745689) (@lem2745694)). Qed.
Lemma lem2745696 : term119 = term28.
Proof. exact (TRANS (@lem2745688) (@lem2745695)). Qed.
Lemma lem2745697 : term124.
Proof. exact (@lem2745681 (@lem2745696)). Qed.
Lemma lem2745699 (m : nat) (n : nat) : (term95 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2745700 : term125 = term126.
Proof. exact (@lem2745699 (NUMERAL 0) term109). Qed.
Lemma lem2745701 : term127 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2745702 (h1 : term127 = (BIT1 0)) : term126 = True.
Proof. exact (@lem1011471 (BIT1 0) 0 (BIT1 0) h1). Qed.
Lemma lem2745703 : (term127 = (BIT1 0)) = (term126 = True).
Proof. exact (prop_ext (fun h1 : term127 = (BIT1 0) => @lem2745702 h1) (fun h1 : term126 = True => @lem2745701)). Qed.
Lemma lem2745704 : term126 = True.
Proof. exact (EQ_MP (@lem2745703) (@lem2745701)). Qed.
Lemma lem2745705 : term125 = True.
Proof. exact (TRANS (@lem2745700) (@lem2745704)). Qed.
Lemma lem2745706 : True = term125.
Proof. exact (SYM (@lem2745705)). Qed.
Lemma lem2745707 : term125.
Proof. exact (EQ_MP (@lem2745706) (@lem0)). Qed.
Lemma lem2745708 : term128.
Proof. exact (@lem2745697 (@lem2745707)). Qed.
Lemma lem2745710 (x : nat) : (term99 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2745711 : term100 = term46.
Proof. exact (@lem2745710 term87). Qed.
Lemma lem2745712 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem2745713 : term130 = term131.
Proof. exact (MK_COMB (@lem2745712) (@lem2745711)). Qed.
Lemma lem2745715 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2745716 : term131 = term132.
Proof. exact (@lem2745715 term109 term87). Qed.
Lemma lem2745717 : term133 = term107.
Proof. exact (@lem912741). Qed.
Lemma lem2745718 (h1 : term133 = term107) : term132 = True.
Proof. exact (@lem1009824 0 (BIT1 0) term107 h1). Qed.
Lemma lem2745719 : (term133 = term107) = (term132 = True).
Proof. exact (prop_ext (fun h1 : term133 = term107 => @lem2745718 h1) (fun h1 : term132 = True => @lem2745717)). Qed.
Lemma lem2745720 : term132 = True.
Proof. exact (EQ_MP (@lem2745719) (@lem2745717)). Qed.
Lemma lem2745721 : term131 = True.
Proof. exact (TRANS (@lem2745716) (@lem2745720)). Qed.
Lemma lem2745722 : term130 = True.
Proof. exact (TRANS (@lem2745713) (@lem2745721)). Qed.
Lemma lem2745723 : True = term130.
Proof. exact (SYM (@lem2745722)). Qed.
Lemma lem2745724 : term130.
Proof. exact (EQ_MP (@lem2745723) (@lem0)). Qed.
Lemma lem2745725 : term134.
Proof. exact (@lem2745708 (@lem2745724)). Qed.
Lemma lem2745726 : term117 = term28.
Proof. exact (proj2 (@lem2745725)). Qed.
Lemma lem2745727 : term78 = term28.
Proof. exact (TRANS (@lem2745680) (@lem2745726)). Qed.
Lemma lem2745728 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745729 : term79 = term66.
Proof. exact (MK_COMB (@lem2745728) (@lem2745727)). Qed.
Lemma lem2745730 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745731 : (term78 = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2745729) (@lem2745730)). Qed.
Lemma lem2745735 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2745736 : (term28 = term20) = (term109 = (NUMERAL 0)).
Proof. exact (@lem2745735 term109 (NUMERAL 0)). Qed.
Lemma lem2745737 : term135 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2745738 (h1 : term135 = (BIT1 0)) : (term109 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2745739 : (term135 = (BIT1 0)) = ((term109 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term135 = (BIT1 0) => @lem2745738 h1) (fun h1 : (term109 = (NUMERAL 0)) = False => @lem2745737)). Qed.
Lemma lem2745740 : (term109 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2745739) (@lem2745737)). Qed.
Lemma lem2745741 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2745736) (@lem2745740)). Qed.
Lemma lem2745742 : (term78 = term20) = False.
Proof. exact (TRANS (@lem2745731) (@lem2745741)). Qed.
Lemma lem2745743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745744 : term80 = (@eq Prop False).
Proof. exact (MK_COMB (@lem2745743) (@lem2745742)). Qed.
Lemma lem2745748 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2745749 : (term28 = term20) = (term109 = (NUMERAL 0)).
Proof. exact (@lem2745748 term109 (NUMERAL 0)). Qed.
Lemma lem2745750 : term135 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2745751 (h1 : term135 = (BIT1 0)) : (term109 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2745752 : (term135 = (BIT1 0)) = ((term109 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term135 = (BIT1 0) => @lem2745751 h1) (fun h1 : (term109 = (NUMERAL 0)) = False => @lem2745750)). Qed.
Lemma lem2745753 : (term109 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2745752) (@lem2745750)). Qed.
Lemma lem2745754 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2745749) (@lem2745753)). Qed.
Lemma lem2745755 : ((term78 = term20) = (term28 = term20)) = (False = False).
Proof. exact (MK_COMB (@lem2745744) (@lem2745754)). Qed.
Lemma lem2745757 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2745758 : (False = False) = (~ False).
Proof. exact (@lem2745757 False). Qed.
Lemma lem2745760 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2745761 : (False = False) = True.
Proof. exact (TRANS (@lem2745758) (@lem2745760)). Qed.
Lemma lem2745762 : ((term78 = term20) = (term28 = term20)) = True.
Proof. exact (TRANS (@lem2745755) (@lem2745761)). Qed.
Lemma lem2745763 : True = ((term78 = term20) = (term28 = term20)).
Proof. exact (SYM (@lem2745762)). Qed.
Lemma lem2745764 : (term78 = term20) = (term28 = term20).
Proof. exact (EQ_MP (@lem2745763) (@lem0)). Qed.
Lemma lem2745765 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : ((term45 m n) = term20) = (term44 m n).
Proof. exact (EQ_MP (@lem2745482 m n h1 h2) (@lem2745764)). Qed.
Lemma lem2745766 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term45 m n) = term20) = (term44 m n).
Proof. exact (EQ_MP (@lem2745424 m n h1 h2) (@lem2745668)). Qed.
Lemma lem2745767 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term45 m n) = term20) = (term44 m n).
Proof. exact (EQ_MP (@lem2745361 m n h1 h2) (@lem2745606)). Qed.
Lemma lem2745768 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : ((term45 m n) = term20) = (term44 m n).
Proof. exact (EQ_MP (@lem2745298 m n h1 h2) (@lem2745544)). Qed.
Lemma lem2745769 (n : int) (m : int) (h1 : (term19 m) = term28) : ((term45 m n) = term20) = (term44 m n).
Proof. exact (or_elim (@lem2745116 n) (fun h0 : (term19 n) = term20 => @lem2745766 m n h1 h0) (fun h0 : (term19 n) = term28 => @lem2745765 m n h1 h0)). Qed.
Lemma lem2745770 (n : int) (m : int) (h1 : (term19 m) = term20) : ((term45 m n) = term20) = (term44 m n).
Proof. exact (or_elim (@lem2745116 n) (fun h0 : (term19 n) = term20 => @lem2745768 m n h1 h0) (fun h0 : (term19 n) = term28 => @lem2745767 m n h1 h0)). Qed.
Lemma lem2745771 (m : int) (n : int) : ((term45 m n) = term20) = (term44 m n).
Proof. exact (or_elim (@lem2745121 m) (fun h0 : (term19 m) = term20 => @lem2745770 n m h0) (fun h0 : (term19 m) = term28 => @lem2745769 n m h0)). Qed.
Lemma lem2745772 (m : int) (n : int) : ((term38 m n) = term20) = (term44 m n).
Proof. exact (EQ_MP (@lem2745232 m n) (@lem2745771 m n)). Qed.
Lemma lem2745773 (m : int) (n : int) : (term37 m n) = (term43 m n).
Proof. exact (EQ_MP (@lem2745210 m n) (@lem2745772 m n)). Qed.
Lemma lem2745778 (m : int) : term136 m.
Proof. exact (fun n : int => @lem2745773 m n). Qed.
Lemma lem2745783 : term137.
Proof. exact (fun m : int => @lem2745778 m). Qed.
