Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LTE_TRANS_term_abbrevs.
Require Import LE_SUC_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem95174 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem95175 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem95176 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem95175 n) (@lem95174 n)). Qed.
Lemma lem95177 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem95180 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem95181 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem95180 n h1)). Qed.
Lemma lem95182 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem95183 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem95182 n h1)). Qed.
Lemma lem95184 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem95181 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem95183 n h1)). Qed.
Lemma lem95185 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem95186 (n : nat) : (term1 n) = (term3 n).
Proof. exact (MK_COMB (@lem95185) (@lem95184 n)). Qed.
Lemma lem95187 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem95186 n) (@lem95176 n)). Qed.
Lemma lem95188 (n : nat) : term4 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem95190 : term5.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem95191 (m : nat) : term6 m.
Proof. exact (@lem95190 m). Qed.
Lemma lem95192 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem95193 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem95192 m) (@lem95191 m)). Qed.
Lemma lem95194 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem95193 m n). Qed.
Lemma lem95195 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem95197 : term11.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem95198 (m : nat) : term12 m.
Proof. exact (@lem95197 m). Qed.
Lemma lem95199 (m : nat) : (term12 m) = ((term13 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem95208 : term14.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem95209 (m : nat) : term15 m.
Proof. exact (@lem95208 m). Qed.
Lemma lem95210 (m : nat) : (term15 m) = ((term16 m) = False).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem95213 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95214 : term18.
Proof. exact (@lem95213 term19). Qed.
Lemma lem95215 : term20 = term21.
Proof. exact (eq_refl term20). Qed.
Lemma lem95216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95217 : term22 = term23.
Proof. exact (MK_COMB (@lem95216) (@lem95215)). Qed.
Lemma lem95218 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem95219 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95220 (m : nat) : (term26 m) = (term27 m).
Proof. exact (MK_COMB (@lem95219) (@lem95218 m)). Qed.
Lemma lem95221 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem95222 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem95220 m) (@lem95221 m)). Qed.
Lemma lem95223 : term32 = term33.
Proof. exact (fun_ext (fun m : nat => @lem95222 m)). Qed.
Lemma lem95224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95225 : term34 = term35.
Proof. exact (MK_COMB (@lem95224) (@lem95223)). Qed.
Lemma lem95226 : term36 = term37.
Proof. exact (MK_COMB (@lem95217) (@lem95225)). Qed.
Lemma lem95227 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95228 : term38 = term39.
Proof. exact (MK_COMB (@lem95227) (@lem95226)). Qed.
Lemma lem95229 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem95230 : term40 = term19.
Proof. exact (fun_ext (fun m : nat => @lem95229 m)). Qed.
Lemma lem95231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95232 : term41 = term42.
Proof. exact (MK_COMB (@lem95231) (@lem95230)). Qed.
Lemma lem95233 : term18 = term43.
Proof. exact (MK_COMB (@lem95228) (@lem95232)). Qed.
Lemma lem95234 : term43.
Proof. exact (EQ_MP (@lem95233) (@lem95214)). Qed.
Lemma lem95235 (m : nat) (h1 : term25 m) : term25 m.
Proof. exact (h1). Qed.
Lemma lem95237 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95238 : term44.
Proof. exact (@lem95237 term45). Qed.
Lemma lem95239 : term46 = term47.
Proof. exact (eq_refl term46). Qed.
Lemma lem95240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95241 : term48 = term49.
Proof. exact (MK_COMB (@lem95240) (@lem95239)). Qed.
Lemma lem95242 (n : nat) : (term50 n) = (term51 n).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem95243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95244 (n : nat) : (term52 n) = (term53 n).
Proof. exact (MK_COMB (@lem95243) (@lem95242 n)). Qed.
Lemma lem95245 (n : nat) : (term54 n) = (term55 n).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem95246 (n : nat) : (term56 n) = (term57 n).
Proof. exact (MK_COMB (@lem95244 n) (@lem95245 n)). Qed.
Lemma lem95247 : term58 = term59.
Proof. exact (fun_ext (fun n : nat => @lem95246 n)). Qed.
Lemma lem95248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95249 : term60 = term61.
Proof. exact (MK_COMB (@lem95248) (@lem95247)). Qed.
Lemma lem95250 : term62 = term63.
Proof. exact (MK_COMB (@lem95241) (@lem95249)). Qed.
Lemma lem95251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95252 : term64 = term65.
Proof. exact (MK_COMB (@lem95251) (@lem95250)). Qed.
Lemma lem95253 (n : nat) : (term50 n) = (term51 n).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem95254 : term66 = term45.
Proof. exact (fun_ext (fun n : nat => @lem95253 n)). Qed.
Lemma lem95255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95256 : term67 = term21.
Proof. exact (MK_COMB (@lem95255) (@lem95254)). Qed.
Lemma lem95257 : term44 = term68.
Proof. exact (MK_COMB (@lem95252) (@lem95256)). Qed.
Lemma lem95258 : term68.
Proof. exact (EQ_MP (@lem95257) (@lem95238)). Qed.
Lemma lem95261 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95262 : term69.
Proof. exact (@lem95261 term70). Qed.
Lemma lem95263 : term71 = term72.
Proof. exact (eq_refl term71). Qed.
Lemma lem95264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95265 : term73 = term74.
Proof. exact (MK_COMB (@lem95264) (@lem95263)). Qed.
Lemma lem95266 (p : nat) : (term75 p) = (term76 p).
Proof. exact (eq_refl (term75 p)). Qed.
Lemma lem95267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95268 (p : nat) : (term77 p) = (term78 p).
Proof. exact (MK_COMB (@lem95267) (@lem95266 p)). Qed.
Lemma lem95269 (p : nat) : (term79 p) = (term80 p).
Proof. exact (eq_refl (term79 p)). Qed.
Lemma lem95270 (p : nat) : (term81 p) = (term82 p).
Proof. exact (MK_COMB (@lem95268 p) (@lem95269 p)). Qed.
Lemma lem95271 : term83 = term84.
Proof. exact (fun_ext (fun p : nat => @lem95270 p)). Qed.
Lemma lem95272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95273 : term85 = term86.
Proof. exact (MK_COMB (@lem95272) (@lem95271)). Qed.
Lemma lem95274 : term87 = term88.
Proof. exact (MK_COMB (@lem95265) (@lem95273)). Qed.
Lemma lem95275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95276 : term89 = term90.
Proof. exact (MK_COMB (@lem95275) (@lem95274)). Qed.
Lemma lem95277 (p : nat) : (term75 p) = (term76 p).
Proof. exact (eq_refl (term75 p)). Qed.
Lemma lem95278 : term91 = term70.
Proof. exact (fun_ext (fun p : nat => @lem95277 p)). Qed.
Lemma lem95279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95280 : term92 = term47.
Proof. exact (MK_COMB (@lem95279) (@lem95278)). Qed.
Lemma lem95281 : term69 = term93.
Proof. exact (MK_COMB (@lem95276) (@lem95280)). Qed.
Lemma lem95282 : term93.
Proof. exact (EQ_MP (@lem95281) (@lem95262)). Qed.
Lemma lem95289 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95290 (n : nat) : term94 n.
Proof. exact (@lem95289 (term95 n)). Qed.
Lemma lem95291 (n : nat) : (term96 n) = (term97 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem95292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95293 (n : nat) : (term98 n) = (term99 n).
Proof. exact (MK_COMB (@lem95292) (@lem95291 n)). Qed.
Lemma lem95294 (n : nat) (p : nat) : (term100 n p) = (term101 n p).
Proof. exact (eq_refl (term100 n p)). Qed.
Lemma lem95295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95296 (n : nat) (p : nat) : (term102 n p) = (term103 n p).
Proof. exact (MK_COMB (@lem95295) (@lem95294 n p)). Qed.
Lemma lem95297 (n : nat) (p : nat) : (term104 n p) = (term105 n p).
Proof. exact (eq_refl (term104 n p)). Qed.
Lemma lem95298 (n : nat) (p : nat) : (term106 n p) = (term107 n p).
Proof. exact (MK_COMB (@lem95296 n p) (@lem95297 n p)). Qed.
Lemma lem95299 (n : nat) : (term108 n) = (term109 n).
Proof. exact (fun_ext (fun p : nat => @lem95298 n p)). Qed.
Lemma lem95300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95301 (n : nat) : (term110 n) = (term111 n).
Proof. exact (MK_COMB (@lem95300) (@lem95299 n)). Qed.
Lemma lem95302 (n : nat) : (term112 n) = (term113 n).
Proof. exact (MK_COMB (@lem95293 n) (@lem95301 n)). Qed.
Lemma lem95303 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95304 (n : nat) : (term114 n) = (term115 n).
Proof. exact (MK_COMB (@lem95303) (@lem95302 n)). Qed.
Lemma lem95305 (n : nat) (p : nat) : (term100 n p) = (term101 n p).
Proof. exact (eq_refl (term100 n p)). Qed.
Lemma lem95306 (n : nat) : (term116 n) = (term95 n).
Proof. exact (fun_ext (fun p : nat => @lem95305 n p)). Qed.
Lemma lem95307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95308 (n : nat) : (term117 n) = (term55 n).
Proof. exact (MK_COMB (@lem95307) (@lem95306 n)). Qed.
Lemma lem95309 (n : nat) : (term94 n) = (term118 n).
Proof. exact (MK_COMB (@lem95304 n) (@lem95308 n)). Qed.
Lemma lem95310 (n : nat) : term118 n.
Proof. exact (EQ_MP (@lem95309 n) (@lem95290 n)). Qed.
Lemma lem95317 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95318 (m : nat) : term119 m.
Proof. exact (@lem95317 (term120 m)). Qed.
Lemma lem95319 (m : nat) : (term121 m) = (term122 m).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem95320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95321 (m : nat) : (term123 m) = (term124 m).
Proof. exact (MK_COMB (@lem95320) (@lem95319 m)). Qed.
Lemma lem95322 (n : nat) (m : nat) : (term125 m n) = (term126 n m).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem95323 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95324 (n : nat) (m : nat) : (term127 m n) = (term128 n m).
Proof. exact (MK_COMB (@lem95323) (@lem95322 n m)). Qed.
Lemma lem95325 (n : nat) (m : nat) : (term129 m n) = (term130 n m).
Proof. exact (eq_refl (term129 m n)). Qed.
Lemma lem95326 (n : nat) (m : nat) : (term131 m n) = (term132 n m).
Proof. exact (MK_COMB (@lem95324 n m) (@lem95325 n m)). Qed.
Lemma lem95327 (m : nat) : (term133 m) = (term134 m).
Proof. exact (fun_ext (fun n : nat => @lem95326 n m)). Qed.
Lemma lem95328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95329 (m : nat) : (term135 m) = (term136 m).
Proof. exact (MK_COMB (@lem95328) (@lem95327 m)). Qed.
Lemma lem95330 (m : nat) : (term137 m) = (term138 m).
Proof. exact (MK_COMB (@lem95321 m) (@lem95329 m)). Qed.
Lemma lem95331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95332 (m : nat) : (term139 m) = (term140 m).
Proof. exact (MK_COMB (@lem95331) (@lem95330 m)). Qed.
Lemma lem95333 (n : nat) (m : nat) : (term125 m n) = (term126 n m).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem95334 (m : nat) : (term141 m) = (term120 m).
Proof. exact (fun_ext (fun n : nat => @lem95333 n m)). Qed.
Lemma lem95335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95336 (m : nat) : (term142 m) = (term29 m).
Proof. exact (MK_COMB (@lem95335) (@lem95334 m)). Qed.
Lemma lem95337 (m : nat) : (term119 m) = (term143 m).
Proof. exact (MK_COMB (@lem95332 m) (@lem95336 m)). Qed.
Lemma lem95338 (m : nat) : term143 m.
Proof. exact (EQ_MP (@lem95337 m) (@lem95318 m)). Qed.
Lemma lem95341 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95342 (m : nat) : term144 m.
Proof. exact (@lem95341 (term145 m)). Qed.
Lemma lem95343 (m : nat) : (term146 m) = (term147 m).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem95344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95345 (m : nat) : (term148 m) = (term149 m).
Proof. exact (MK_COMB (@lem95344) (@lem95343 m)). Qed.
Lemma lem95346 (m : nat) (p : nat) : (term150 m p) = (term151 m p).
Proof. exact (eq_refl (term150 m p)). Qed.
Lemma lem95347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95348 (m : nat) (p : nat) : (term152 m p) = (term153 m p).
Proof. exact (MK_COMB (@lem95347) (@lem95346 m p)). Qed.
Lemma lem95349 (m : nat) (p : nat) : (term154 m p) = (term155 m p).
Proof. exact (eq_refl (term154 m p)). Qed.
Lemma lem95350 (m : nat) (p : nat) : (term156 m p) = (term157 m p).
Proof. exact (MK_COMB (@lem95348 m p) (@lem95349 m p)). Qed.
Lemma lem95351 (m : nat) : (term158 m) = (term159 m).
Proof. exact (fun_ext (fun p : nat => @lem95350 m p)). Qed.
Lemma lem95352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95353 (m : nat) : (term160 m) = (term161 m).
Proof. exact (MK_COMB (@lem95352) (@lem95351 m)). Qed.
Lemma lem95354 (m : nat) : (term162 m) = (term163 m).
Proof. exact (MK_COMB (@lem95345 m) (@lem95353 m)). Qed.
Lemma lem95355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95356 (m : nat) : (term164 m) = (term165 m).
Proof. exact (MK_COMB (@lem95355) (@lem95354 m)). Qed.
Lemma lem95357 (m : nat) (p : nat) : (term150 m p) = (term151 m p).
Proof. exact (eq_refl (term150 m p)). Qed.
Lemma lem95358 (m : nat) : (term166 m) = (term145 m).
Proof. exact (fun_ext (fun p : nat => @lem95357 m p)). Qed.
Lemma lem95359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95360 (m : nat) : (term167 m) = (term122 m).
Proof. exact (MK_COMB (@lem95359) (@lem95358 m)). Qed.
Lemma lem95361 (m : nat) : (term144 m) = (term168 m).
Proof. exact (MK_COMB (@lem95356 m) (@lem95360 m)). Qed.
Lemma lem95362 (m : nat) : term168 m.
Proof. exact (EQ_MP (@lem95361 m) (@lem95342 m)). Qed.
Lemma lem95369 (P : nat -> Prop) : term17 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95370 (n : nat) (m : nat) : term169 n m.
Proof. exact (@lem95369 (term170 n m)). Qed.
Lemma lem95371 (n : nat) (m : nat) : (term171 n m) = (term172 n m).
Proof. exact (eq_refl (term171 n m)). Qed.
Lemma lem95372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95373 (n : nat) (m : nat) : (term173 n m) = (term174 n m).
Proof. exact (MK_COMB (@lem95372) (@lem95371 n m)). Qed.
Lemma lem95374 (n : nat) (m : nat) (p : nat) : (term175 n m p) = (term176 n m p).
Proof. exact (eq_refl (term175 n m p)). Qed.
Lemma lem95375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95376 (n : nat) (m : nat) (p : nat) : (term177 n m p) = (term178 n m p).
Proof. exact (MK_COMB (@lem95375) (@lem95374 n m p)). Qed.
Lemma lem95377 (n : nat) (m : nat) (p : nat) : (term179 n m p) = (term180 n m p).
Proof. exact (eq_refl (term179 n m p)). Qed.
Lemma lem95378 (n : nat) (m : nat) (p : nat) : (term181 n m p) = (term182 n m p).
Proof. exact (MK_COMB (@lem95376 n m p) (@lem95377 n m p)). Qed.
Lemma lem95379 (n : nat) (m : nat) : (term183 n m) = (term184 n m).
Proof. exact (fun_ext (fun p : nat => @lem95378 n m p)). Qed.
Lemma lem95380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95381 (n : nat) (m : nat) : (term185 n m) = (term186 n m).
Proof. exact (MK_COMB (@lem95380) (@lem95379 n m)). Qed.
Lemma lem95382 (n : nat) (m : nat) : (term187 n m) = (term188 n m).
Proof. exact (MK_COMB (@lem95373 n m) (@lem95381 n m)). Qed.
Lemma lem95383 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95384 (n : nat) (m : nat) : (term189 n m) = (term190 n m).
Proof. exact (MK_COMB (@lem95383) (@lem95382 n m)). Qed.
Lemma lem95385 (n : nat) (m : nat) (p : nat) : (term175 n m p) = (term176 n m p).
Proof. exact (eq_refl (term175 n m p)). Qed.
Lemma lem95386 (n : nat) (m : nat) : (term191 n m) = (term170 n m).
Proof. exact (fun_ext (fun p : nat => @lem95385 n m p)). Qed.
Lemma lem95387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95388 (n : nat) (m : nat) : (term192 n m) = (term130 n m).
Proof. exact (MK_COMB (@lem95387) (@lem95386 n m)). Qed.
Lemma lem95389 (n : nat) (m : nat) : (term169 n m) = (term193 n m).
Proof. exact (MK_COMB (@lem95384 n m) (@lem95388 n m)). Qed.
Lemma lem95390 (n : nat) (m : nat) : term193 n m.
Proof. exact (EQ_MP (@lem95389 n m) (@lem95370 n m)). Qed.
Lemma lem95419 (n : nat) : term194 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem95420 (n : nat) : (term194 n) = (term195 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem95421 (n : nat) : term195 n.
Proof. exact (EQ_MP (@lem95420 n) (@lem95419 n)). Qed.
Lemma lem95422 (n : nat) : (term195 n) = ((term195 n) = True).
Proof. exact (@lem7 (term195 n)). Qed.
Lemma lem95443 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem95422 n) (@lem95421 n)). Qed.
Lemma lem95444 (p : nat) : (term195 p) = True.
Proof. exact (@lem95443 p). Qed.
Lemma lem95445 (p : nat) : (term196 p) = (term196 p).
Proof. exact (eq_refl (term196 p)). Qed.
Lemma lem95446 (p : nat) : (term80 p) = (term197 p).
Proof. exact (MK_COMB (@lem95445 p) (@lem95444 p)). Qed.
Lemma lem95448 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem95449 (p : nat) : (term197 p) = True.
Proof. exact (@lem95448 (term198 p)). Qed.
Lemma lem95450 (p : nat) : (term80 p) = True.
Proof. exact (TRANS (@lem95446 p) (@lem95449 p)). Qed.
Lemma lem95451 (p : nat) : True = (term80 p).
Proof. exact (SYM (@lem95450 p)). Qed.
Lemma lem95452 (p : nat) : term80 p.
Proof. exact (EQ_MP (@lem95451 p) (@lem0)). Qed.
Lemma lem95453 (n : nat) : term194 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem95454 (n : nat) : (term194 n) = (term195 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem95455 (n : nat) : term195 n.
Proof. exact (EQ_MP (@lem95454 n) (@lem95453 n)). Qed.
Lemma lem95456 (n : nat) : (term195 n) = ((term195 n) = True).
Proof. exact (@lem7 (term195 n)). Qed.
Lemma lem95480 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem95456 n) (@lem95455 n)). Qed.
Lemma lem95481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95482 (n : nat) : (term199 n) = (and True).
Proof. exact (MK_COMB (@lem95481) (@lem95480 n)). Qed.
Lemma lem95483 (n : nat) : (term200 n) = (term200 n).
Proof. exact (eq_refl (term200 n)). Qed.
Lemma lem95484 (n : nat) : (term201 n) = (term202 n).
Proof. exact (MK_COMB (@lem95482 n) (@lem95483 n)). Qed.
Lemma lem95486 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem95487 (n : nat) : (term202 n) = (term200 n).
Proof. exact (@lem95486 (term200 n)). Qed.
Lemma lem95488 (n : nat) : (term201 n) = (term200 n).
Proof. exact (TRANS (@lem95484 n) (@lem95487 n)). Qed.
Lemma lem95489 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95490 (n : nat) : (term203 n) = (term204 n).
Proof. exact (MK_COMB (@lem95489) (@lem95488 n)). Qed.
Lemma lem95491 : term205 = term205.
Proof. exact (eq_refl term205). Qed.
Lemma lem95492 (n : nat) : (term97 n) = (term206 n).
Proof. exact (MK_COMB (@lem95490 n) (@lem95491)). Qed.
Lemma lem95495 (n : nat) : (term206 n) = (term97 n).
Proof. exact (SYM (@lem95492 n)). Qed.
Lemma lem95496 (n : nat) : term194 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem95497 (n : nat) : (term194 n) = (term195 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem95498 (n : nat) : term195 n.
Proof. exact (EQ_MP (@lem95497 n) (@lem95496 n)). Qed.
Lemma lem95499 (n : nat) : (term195 n) = ((term195 n) = True).
Proof. exact (@lem7 (term195 n)). Qed.
Lemma lem95507 (m : nat) : term207 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem95508 (m : nat) : (term207 m) = (term208 m).
Proof. exact (eq_refl (term207 m)). Qed.
Lemma lem95509 (m : nat) : term208 m.
Proof. exact (EQ_MP (@lem95508 m) (@lem95507 m)). Qed.
Lemma lem95510 (m : nat) (n : nat) : term209 m n.
Proof. exact (@lem95509 m n). Qed.
Lemma lem95511 (m : nat) (n : nat) : (term209 m n) = ((term210 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term209 m n)). Qed.
Lemma lem95525 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem95499 n) (@lem95498 n)). Qed.
Lemma lem95526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95527 (n : nat) : (term199 n) = (and True).
Proof. exact (MK_COMB (@lem95526) (@lem95525 n)). Qed.
Lemma lem95529 (m : nat) (n : nat) : (term210 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem95511 m n) (@lem95510 m n)). Qed.
Lemma lem95530 (n : nat) (p : nat) : (term210 n p) = (Peano.le n p).
Proof. exact (@lem95529 n p). Qed.
Lemma lem95531 (n : nat) (p : nat) : (term211 n p) = (term212 n p).
Proof. exact (MK_COMB (@lem95527 n) (@lem95530 n p)). Qed.
Lemma lem95533 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem95534 (n : nat) (p : nat) : (term212 n p) = (Peano.le n p).
Proof. exact (@lem95533 (Peano.le n p)). Qed.
Lemma lem95535 (n : nat) (p : nat) : (term211 n p) = (Peano.le n p).
Proof. exact (TRANS (@lem95531 n p) (@lem95534 n p)). Qed.
Lemma lem95536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95537 (n : nat) (p : nat) : (term213 n p) = (term214 n p).
Proof. exact (MK_COMB (@lem95536) (@lem95535 n p)). Qed.
Lemma lem95539 (n : nat) : (term195 n) = True.
Proof. exact (EQ_MP (@lem95499 n) (@lem95498 n)). Qed.
Lemma lem95540 (p : nat) : (term195 p) = True.
Proof. exact (@lem95539 p). Qed.
Lemma lem95541 (n : nat) (p : nat) : (term105 n p) = (term215 n p).
Proof. exact (MK_COMB (@lem95537 n p) (@lem95540 p)). Qed.
Lemma lem95543 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem95544 (n : nat) (p : nat) : (term215 n p) = True.
Proof. exact (@lem95543 (Peano.le n p)). Qed.
Lemma lem95545 (n : nat) (p : nat) : (term105 n p) = True.
Proof. exact (TRANS (@lem95541 n p) (@lem95544 n p)). Qed.
Lemma lem95546 (n : nat) (p : nat) : True = (term105 n p).
Proof. exact (SYM (@lem95545 n p)). Qed.
Lemma lem95547 (n : nat) (p : nat) : term105 n p.
Proof. exact (EQ_MP (@lem95546 n p) (@lem0)). Qed.
Lemma lem95584 (m : nat) : term216 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem95585 (m : nat) : (term216 m) = (term217 m).
Proof. exact (eq_refl (term216 m)). Qed.
Lemma lem95586 (m : nat) : term217 m.
Proof. exact (EQ_MP (@lem95585 m) (@lem95584 m)). Qed.
Lemma lem95587 (m : nat) (n : nat) : term218 m n.
Proof. exact (@lem95586 m n). Qed.
Lemma lem95588 (m : nat) (n : nat) : (term218 m n) = ((term219 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term218 m n)). Qed.
Lemma lem95611 (m : nat) (n : nat) : (term219 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem95588 m n) (@lem95587 m n)). Qed.
Lemma lem95612 (m : nat) (p : nat) : (term219 m p) = (Peano.lt m p).
Proof. exact (@lem95611 m p). Qed.
Lemma lem95613 (m : nat) (p : nat) : (term220 m p) = (term220 m p).
Proof. exact (eq_refl (term220 m p)). Qed.
Lemma lem95614 (m : nat) (p : nat) : (term155 m p) = (term221 m p).
Proof. exact (MK_COMB (@lem95613 m p) (@lem95612 m p)). Qed.
Lemma lem95617 (m : nat) (p : nat) : (term221 m p) = (term155 m p).
Proof. exact (SYM (@lem95614 m p)). Qed.
Lemma lem95623 (m : nat) : term216 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem95624 (m : nat) : (term216 m) = (term217 m).
Proof. exact (eq_refl (term216 m)). Qed.
Lemma lem95625 (m : nat) : term217 m.
Proof. exact (EQ_MP (@lem95624 m) (@lem95623 m)). Qed.
Lemma lem95626 (m : nat) (n : nat) : term218 m n.
Proof. exact (@lem95625 m n). Qed.
Lemma lem95627 (m : nat) (n : nat) : (term218 m n) = ((term219 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term218 m n)). Qed.
Lemma lem95653 (m : nat) (n : nat) : (term219 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem95627 m n) (@lem95626 m n)). Qed.
Lemma lem95654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95655 (m : nat) (n : nat) : (term222 m n) = (term223 m n).
Proof. exact (MK_COMB (@lem95654) (@lem95653 m n)). Qed.
Lemma lem95656 (n : nat) : (term200 n) = (term200 n).
Proof. exact (eq_refl (term200 n)). Qed.
Lemma lem95657 (m : nat) (n : nat) : (term224 m n) = (term225 m n).
Proof. exact (MK_COMB (@lem95655 m n) (@lem95656 n)). Qed.
Lemma lem95660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95661 (m : nat) (n : nat) : (term226 m n) = (term227 m n).
Proof. exact (MK_COMB (@lem95660) (@lem95657 m n)). Qed.
Lemma lem95662 (m : nat) : (term228 m) = (term228 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem95663 (n : nat) (m : nat) : (term172 n m) = (term229 n m).
Proof. exact (MK_COMB (@lem95661 m n) (@lem95662 m)). Qed.
Lemma lem95666 (n : nat) (m : nat) : (term229 n m) = (term172 n m).
Proof. exact (SYM (@lem95663 n m)). Qed.
Lemma lem95672 (m : nat) : term216 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem95673 (m : nat) : (term216 m) = (term217 m).
Proof. exact (eq_refl (term216 m)). Qed.
Lemma lem95674 (m : nat) : term217 m.
Proof. exact (EQ_MP (@lem95673 m) (@lem95672 m)). Qed.
Lemma lem95675 (m : nat) (n : nat) : term218 m n.
Proof. exact (@lem95674 m n). Qed.
Lemma lem95676 (m : nat) (n : nat) : (term218 m n) = ((term219 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term218 m n)). Qed.
Lemma lem95678 (m : nat) : term207 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem95679 (m : nat) : (term207 m) = (term208 m).
Proof. exact (eq_refl (term207 m)). Qed.
Lemma lem95680 (m : nat) : term208 m.
Proof. exact (EQ_MP (@lem95679 m) (@lem95678 m)). Qed.
Lemma lem95681 (m : nat) (n : nat) : term209 m n.
Proof. exact (@lem95680 m n). Qed.
Lemma lem95682 (m : nat) (n : nat) : (term209 m n) = ((term210 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term209 m n)). Qed.
Lemma lem95684 (n : nat) (m : nat) (h1 : term25 m) : term230 m n.
Proof. exact (@lem95235 m h1 n). Qed.
Lemma lem95685 (n : nat) (m : nat) : (term230 m n) = (term231 n m).
Proof. exact (eq_refl (term230 m n)). Qed.
Lemma lem95686 (n : nat) (m : nat) (h1 : term25 m) : term231 n m.
Proof. exact (EQ_MP (@lem95685 n m) (@lem95684 n m h1)). Qed.
Lemma lem95687 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term232 n m p.
Proof. exact (@lem95686 n m h1 p). Qed.
Lemma lem95688 (n : nat) (m : nat) (p : nat) : (term232 n m p) = (term233 n m p).
Proof. exact (eq_refl (term232 n m p)). Qed.
Lemma lem95689 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term233 n m p.
Proof. exact (EQ_MP (@lem95688 n m p) (@lem95687 n p m h1)). Qed.
Lemma lem95690 (n : nat) (m : nat) (p : nat) : (term233 n m p) = ((term233 n m p) = True).
Proof. exact (@lem7 (term233 n m p)). Qed.
Lemma lem95704 (m : nat) (n : nat) : (term219 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem95676 m n) (@lem95675 m n)). Qed.
Lemma lem95705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95706 (m : nat) (n : nat) : (term222 m n) = (term223 m n).
Proof. exact (MK_COMB (@lem95705) (@lem95704 m n)). Qed.
Lemma lem95708 (m : nat) (n : nat) : (term210 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem95682 m n) (@lem95681 m n)). Qed.
Lemma lem95709 (n : nat) (p : nat) : (term210 n p) = (Peano.le n p).
Proof. exact (@lem95708 n p). Qed.
Lemma lem95710 (m : nat) (n : nat) (p : nat) : (term234 m n p) = (term235 m n p).
Proof. exact (MK_COMB (@lem95706 m n) (@lem95709 n p)). Qed.
Lemma lem95713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95714 (m : nat) (n : nat) (p : nat) : (term236 m n p) = (term237 m n p).
Proof. exact (MK_COMB (@lem95713) (@lem95710 m n p)). Qed.
Lemma lem95716 (m : nat) (n : nat) : (term219 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem95676 m n) (@lem95675 m n)). Qed.
Lemma lem95717 (m : nat) (p : nat) : (term219 m p) = (Peano.lt m p).
Proof. exact (@lem95716 m p). Qed.
Lemma lem95718 (n : nat) (m : nat) (p : nat) : (term180 n m p) = (term233 n m p).
Proof. exact (MK_COMB (@lem95714 m n p) (@lem95717 m p)). Qed.
Lemma lem95720 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : (term233 n m p) = True.
Proof. exact (EQ_MP (@lem95690 n m p) (@lem95689 n p m h1)). Qed.
Lemma lem95721 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : (term180 n m p) = True.
Proof. exact (TRANS (@lem95718 n m p) (@lem95720 n p m h1)). Qed.
Lemma lem95722 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : True = (term180 n m p).
Proof. exact (SYM (@lem95721 n p m h1)). Qed.
Lemma lem95723 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term180 n m p.
Proof. exact (EQ_MP (@lem95722 n p m h1) (@lem0)). Qed.
Lemma lem95729 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem95210 m) (@lem95209 m)). Qed.
Lemma lem95730 : term205 = False.
Proof. exact (@lem95729 (NUMERAL 0)). Qed.
Lemma lem95731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95732 : term238 = (and False).
Proof. exact (MK_COMB (@lem95731) (@lem95730)). Qed.
Lemma lem95734 (m : nat) : (term13 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem95199 m) (@lem95198 m)). Qed.
Lemma lem95735 : term239 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem95734 (NUMERAL 0)). Qed.
Lemma lem95737 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem95738 (x : nat) : (x = x) = True.
Proof. exact (@lem95737 nat x). Qed.
Lemma lem95739 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem95738 (NUMERAL 0)). Qed.
Lemma lem95740 : term239 = True.
Proof. exact (TRANS (@lem95735) (@lem95739)). Qed.
Lemma lem95741 : term240 = (False /\ True).
Proof. exact (MK_COMB (@lem95732) (@lem95740)). Qed.
Lemma lem95743 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem95744 : (False /\ True) = False.
Proof. exact (@lem95743 True). Qed.
Lemma lem95745 : term240 = False.
Proof. exact (TRANS (@lem95741) (@lem95744)). Qed.
Lemma lem95746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95747 : term241 = (imp False).
Proof. exact (MK_COMB (@lem95746) (@lem95745)). Qed.
Lemma lem95749 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem95210 m) (@lem95209 m)). Qed.
Lemma lem95750 : term205 = False.
Proof. exact (@lem95749 (NUMERAL 0)). Qed.
Lemma lem95751 : term72 = (False -> False).
Proof. exact (MK_COMB (@lem95747) (@lem95750)). Qed.
Lemma lem95753 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95754 : (False -> False) = True.
Proof. exact (@lem95753 False). Qed.
Lemma lem95755 : term72 = True.
Proof. exact (TRANS (@lem95751) (@lem95754)). Qed.
Lemma lem95756 : True = term72.
Proof. exact (SYM (@lem95755)). Qed.
Lemma lem95761 (m : nat) : (term13 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem95199 m) (@lem95198 m)). Qed.
Lemma lem95762 (n : nat) : (term200 n) = ((S n) = (NUMERAL 0)).
Proof. exact (@lem95761 (S n)). Qed.
Lemma lem95764 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem95177 n (@lem95176 n)). Qed.
Lemma lem95765 (n : nat) : (term200 n) = False.
Proof. exact (TRANS (@lem95762 n) (@lem95764 n)). Qed.
Lemma lem95766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95767 (n : nat) : (term204 n) = (imp False).
Proof. exact (MK_COMB (@lem95766) (@lem95765 n)). Qed.
Lemma lem95769 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem95210 m) (@lem95209 m)). Qed.
Lemma lem95770 : term205 = False.
Proof. exact (@lem95769 (NUMERAL 0)). Qed.
Lemma lem95771 (n : nat) : (term206 n) = (False -> False).
Proof. exact (MK_COMB (@lem95767 n) (@lem95770)). Qed.
Lemma lem95773 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95774 : (False -> False) = True.
Proof. exact (@lem95773 False). Qed.
Lemma lem95775 (n : nat) : (term206 n) = True.
Proof. exact (TRANS (@lem95771 n) (@lem95774)). Qed.
Lemma lem95776 (n : nat) : True = (term206 n).
Proof. exact (SYM (@lem95775 n)). Qed.
Lemma lem95777 (n : nat) : term206 n.
Proof. exact (EQ_MP (@lem95776 n) (@lem0)). Qed.
Lemma lem95783 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem95210 m) (@lem95209 m)). Qed.
Lemma lem95784 (m : nat) : (term228 m) = False.
Proof. exact (@lem95783 (S m)). Qed.
Lemma lem95785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95786 (m : nat) : (term242 m) = (and False).
Proof. exact (MK_COMB (@lem95785) (@lem95784 m)). Qed.
Lemma lem95788 (m : nat) : (term13 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem95199 m) (@lem95198 m)). Qed.
Lemma lem95789 : term239 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem95788 (NUMERAL 0)). Qed.
Lemma lem95791 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem95792 (x : nat) : (x = x) = True.
Proof. exact (@lem95791 nat x). Qed.
Lemma lem95793 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem95792 (NUMERAL 0)). Qed.
Lemma lem95794 : term239 = True.
Proof. exact (TRANS (@lem95789) (@lem95793)). Qed.
Lemma lem95795 (m : nat) : (term243 m) = (False /\ True).
Proof. exact (MK_COMB (@lem95786 m) (@lem95794)). Qed.
Lemma lem95797 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem95798 : (False /\ True) = False.
Proof. exact (@lem95797 True). Qed.
Lemma lem95799 (m : nat) : (term243 m) = False.
Proof. exact (TRANS (@lem95795 m) (@lem95798)). Qed.
Lemma lem95800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95801 (m : nat) : (term244 m) = (imp False).
Proof. exact (MK_COMB (@lem95800) (@lem95799 m)). Qed.
Lemma lem95803 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem95210 m) (@lem95209 m)). Qed.
Lemma lem95804 (m : nat) : (term228 m) = False.
Proof. exact (@lem95803 (S m)). Qed.
Lemma lem95805 (m : nat) : (term147 m) = (False -> False).
Proof. exact (MK_COMB (@lem95801 m) (@lem95804 m)). Qed.
Lemma lem95807 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95808 : (False -> False) = True.
Proof. exact (@lem95807 False). Qed.
Lemma lem95809 (m : nat) : (term147 m) = True.
Proof. exact (TRANS (@lem95805 m) (@lem95808)). Qed.
Lemma lem95810 (m : nat) : True = (term147 m).
Proof. exact (SYM (@lem95809 m)). Qed.
Lemma lem95817 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem95210 m) (@lem95209 m)). Qed.
Lemma lem95818 (m : nat) : (term228 m) = False.
Proof. exact (@lem95817 (S m)). Qed.
Lemma lem95819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95820 (m : nat) : (term242 m) = (and False).
Proof. exact (MK_COMB (@lem95819) (@lem95818 m)). Qed.
Lemma lem95822 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem95195 m n) (@lem95194 m n)). Qed.
Lemma lem95823 (p : nat) : (term245 p) = (term246 p).
Proof. exact (@lem95822 (NUMERAL 0) p). Qed.
Lemma lem95827 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem95188 n (@lem95187 n)). Qed.
Lemma lem95828 (p : nat) : ((NUMERAL 0) = (S p)) = False.
Proof. exact (@lem95827 p). Qed.
Lemma lem95829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem95830 (p : nat) : (term247 p) = (or False).
Proof. exact (MK_COMB (@lem95829) (@lem95828 p)). Qed.
Lemma lem95831 (p : nat) : (term248 p) = (term248 p).
Proof. exact (eq_refl (term248 p)). Qed.
Lemma lem95832 (p : nat) : (term246 p) = (term249 p).
Proof. exact (MK_COMB (@lem95830 p) (@lem95831 p)). Qed.
Lemma lem95834 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem95835 (p : nat) : (term249 p) = (term248 p).
Proof. exact (@lem95834 (term248 p)). Qed.
Lemma lem95836 (p : nat) : (term246 p) = (term248 p).
Proof. exact (TRANS (@lem95832 p) (@lem95835 p)). Qed.
Lemma lem95837 (p : nat) : (term245 p) = (term248 p).
Proof. exact (TRANS (@lem95823 p) (@lem95836 p)). Qed.
Lemma lem95838 (m : nat) (p : nat) : (term250 m p) = (term251 p).
Proof. exact (MK_COMB (@lem95820 m) (@lem95837 p)). Qed.
Lemma lem95840 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem95841 (p : nat) : (term251 p) = False.
Proof. exact (@lem95840 (term248 p)). Qed.
Lemma lem95842 (m : nat) (p : nat) : (term250 m p) = False.
Proof. exact (TRANS (@lem95838 m p) (@lem95841 p)). Qed.
Lemma lem95843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95844 (m : nat) (p : nat) : (term220 m p) = (imp False).
Proof. exact (MK_COMB (@lem95843) (@lem95842 m p)). Qed.
Lemma lem95845 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem95846 (m : nat) (p : nat) : (term221 m p) = (term252 m p).
Proof. exact (MK_COMB (@lem95844 m p) (@lem95845 m p)). Qed.
Lemma lem95848 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95849 (m : nat) (p : nat) : (term252 m p) = True.
Proof. exact (@lem95848 (Peano.lt m p)). Qed.
Lemma lem95850 (m : nat) (p : nat) : (term221 m p) = True.
Proof. exact (TRANS (@lem95846 m p) (@lem95849 m p)). Qed.
Lemma lem95851 (m : nat) (p : nat) : True = (term221 m p).
Proof. exact (SYM (@lem95850 m p)). Qed.
Lemma lem95852 (m : nat) (p : nat) : term221 m p.
Proof. exact (EQ_MP (@lem95851 m p) (@lem0)). Qed.
Lemma lem95858 (m : nat) : (term13 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem95199 m) (@lem95198 m)). Qed.
Lemma lem95859 (n : nat) : (term200 n) = ((S n) = (NUMERAL 0)).
Proof. exact (@lem95858 (S n)). Qed.
Lemma lem95861 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem95177 n (@lem95176 n)). Qed.
Lemma lem95862 (n : nat) : (term200 n) = False.
Proof. exact (TRANS (@lem95859 n) (@lem95861 n)). Qed.
Lemma lem95863 (m : nat) (n : nat) : (term223 m n) = (term223 m n).
Proof. exact (eq_refl (term223 m n)). Qed.
Lemma lem95864 (m : nat) (n : nat) : (term225 m n) = (term253 m n).
Proof. exact (MK_COMB (@lem95863 m n) (@lem95862 n)). Qed.
Lemma lem95866 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem95867 (m : nat) (n : nat) : (term253 m n) = False.
Proof. exact (@lem95866 (Peano.lt m n)). Qed.
Lemma lem95868 (m : nat) (n : nat) : (term225 m n) = False.
Proof. exact (TRANS (@lem95864 m n) (@lem95867 m n)). Qed.
Lemma lem95869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95870 (m : nat) (n : nat) : (term227 m n) = (imp False).
Proof. exact (MK_COMB (@lem95869) (@lem95868 m n)). Qed.
Lemma lem95872 (m : nat) : (term16 m) = False.
Proof. exact (EQ_MP (@lem95210 m) (@lem95209 m)). Qed.
Lemma lem95873 (m : nat) : (term228 m) = False.
Proof. exact (@lem95872 (S m)). Qed.
Lemma lem95874 (n : nat) (m : nat) : (term229 n m) = (False -> False).
Proof. exact (MK_COMB (@lem95870 m n) (@lem95873 m)). Qed.
Lemma lem95876 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem95877 : (False -> False) = True.
Proof. exact (@lem95876 False). Qed.
Lemma lem95878 (n : nat) (m : nat) : (term229 n m) = True.
Proof. exact (TRANS (@lem95874 n m) (@lem95877)). Qed.
Lemma lem95879 (n : nat) (m : nat) : True = (term229 n m).
Proof. exact (SYM (@lem95878 n m)). Qed.
Lemma lem95880 (n : nat) (m : nat) : term229 n m.
Proof. exact (EQ_MP (@lem95879 n m) (@lem0)). Qed.
Lemma lem95881 (n : nat) (m : nat) : term172 n m.
Proof. exact (EQ_MP (@lem95666 n m) (@lem95880 n m)). Qed.
Lemma lem95882 (m : nat) (p : nat) : term155 m p.
Proof. exact (EQ_MP (@lem95617 m p) (@lem95852 m p)). Qed.
Lemma lem95883 (m : nat) : term147 m.
Proof. exact (EQ_MP (@lem95810 m) (@lem0)). Qed.
Lemma lem95884 (n : nat) : term97 n.
Proof. exact (EQ_MP (@lem95495 n) (@lem95777 n)). Qed.
Lemma lem95885 : term72.
Proof. exact (EQ_MP (@lem95756) (@lem0)). Qed.
Lemma lem95886 (n : nat) (p : nat) (m : nat) (h1 : term25 m) : term182 n m p.
Proof. exact (fun h0 : term176 n m p => @lem95723 n p m h1). Qed.
Lemma lem95891 (n : nat) (m : nat) (h1 : term25 m) : term186 n m.
Proof. exact (fun p : nat => @lem95886 n p m h1). Qed.
Lemma lem95892 (n : nat) (m : nat) (h1 : term25 m) : term188 n m.
Proof. exact (conj (@lem95881 n m) (@lem95891 n m h1)). Qed.
Lemma lem95893 (n : nat) (m : nat) (h1 : term25 m) : term130 n m.
Proof. exact (@lem95390 n m (@lem95892 n m h1)). Qed.
Lemma lem95894 (m : nat) (p : nat) : term157 m p.
Proof. exact (fun h0 : term151 m p => @lem95882 m p). Qed.
Lemma lem95899 (m : nat) : term161 m.
Proof. exact (fun p : nat => @lem95894 m p). Qed.
Lemma lem95900 (m : nat) : term163 m.
Proof. exact (conj (@lem95883 m) (@lem95899 m)). Qed.
Lemma lem95901 (m : nat) : term122 m.
Proof. exact (@lem95362 m (@lem95900 m)). Qed.
Lemma lem95902 (n : nat) (m : nat) (h1 : term25 m) : term132 n m.
Proof. exact (fun h0 : term126 n m => @lem95893 n m h1). Qed.
Lemma lem95907 (m : nat) (h1 : term25 m) : term136 m.
Proof. exact (fun n : nat => @lem95902 n m h1). Qed.
Lemma lem95908 (m : nat) (h1 : term25 m) : term138 m.
Proof. exact (conj (@lem95901 m) (@lem95907 m h1)). Qed.
Lemma lem95909 (m : nat) (h1 : term25 m) : term29 m.
Proof. exact (@lem95338 m (@lem95908 m h1)). Qed.
Lemma lem95910 (n : nat) (p : nat) : term107 n p.
Proof. exact (fun h0 : term101 n p => @lem95547 n p). Qed.
Lemma lem95915 (n : nat) : term111 n.
Proof. exact (fun p : nat => @lem95910 n p). Qed.
Lemma lem95916 (n : nat) : term113 n.
Proof. exact (conj (@lem95884 n) (@lem95915 n)). Qed.
Lemma lem95917 (n : nat) : term55 n.
Proof. exact (@lem95310 n (@lem95916 n)). Qed.
Lemma lem95918 (p : nat) : term82 p.
Proof. exact (fun h0 : term76 p => @lem95452 p). Qed.
Lemma lem95923 : term86.
Proof. exact (fun p : nat => @lem95918 p). Qed.
Lemma lem95924 : term88.
Proof. exact (conj (@lem95885) (@lem95923)). Qed.
Lemma lem95925 : term47.
Proof. exact (@lem95282 (@lem95924)). Qed.
Lemma lem95926 (n : nat) : term57 n.
Proof. exact (fun h0 : term51 n => @lem95917 n). Qed.
Lemma lem95931 : term61.
Proof. exact (fun n : nat => @lem95926 n). Qed.
Lemma lem95932 : term63.
Proof. exact (conj (@lem95925) (@lem95931)). Qed.
Lemma lem95933 : term21.
Proof. exact (@lem95258 (@lem95932)). Qed.
Lemma lem95934 (m : nat) : term31 m.
Proof. exact (fun h0 : term25 m => @lem95909 m h0). Qed.
Lemma lem95939 : term35.
Proof. exact (fun m : nat => @lem95934 m). Qed.
Lemma lem95940 : term37.
Proof. exact (conj (@lem95933) (@lem95939)). Qed.
Lemma lem95941 : term42.
Proof. exact (@lem95234 (@lem95940)). Qed.
