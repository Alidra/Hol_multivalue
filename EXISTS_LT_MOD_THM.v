Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_LT_MOD_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LT_spec.
Require Import MOD_EQ_SELF_spec.
Require Import MOD_LT_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem241980 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem241981 : term1 = term2.
Proof. exact (@lem241980 term1). Qed.
Lemma lem241982 : term2 = term1.
Proof. exact (SYM (@lem241981)). Qed.
Lemma lem241983 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem241986 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem241987 : term5.
Proof. exact (fun h0 : term4 => @lem241986 h0). Qed.
Lemma lem241988 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem241989 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem241990 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem241988 h2 (@lem241989 h1)). Qed.
Lemma lem241991 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem241990 h1 h0). Qed.
Lemma lem241992 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem241993 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem241991 h1 (@lem241992 h2)). Qed.
Lemma lem241994 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem241993 h0 h1). Qed.
Lemma lem241995 : term7.
Proof. exact (fun h0 : term5 => @lem241994 h0). Qed.
Lemma lem241998 : term5.
Proof. exact (@lem241995 (@lem241987)). Qed.
Lemma lem242072 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem242073 : term8 = term9.
Proof. exact (@lem242072 term10). Qed.
Lemma lem242081 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem242082 (m : nat) : ((term11 m) = False) = (term12 m).
Proof. exact (@lem242081 (term11 m)). Qed.
Lemma lem242083 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem242082 m)). Qed.
Lemma lem242084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242085 : term15 = term16.
Proof. exact (MK_COMB (@lem242084) (@lem242083)). Qed.
Lemma lem242090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem242091 : term17 = term18.
Proof. exact (MK_COMB (@lem242090) (@lem242085)). Qed.
Lemma lem242102 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem242103 : term10 = term20.
Proof. exact (MK_COMB (@lem242091) (@lem242102)). Qed.
Lemma lem242106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem242107 : term9 = term21.
Proof. exact (MK_COMB (@lem242106) (@lem242103)). Qed.
Lemma lem242108 : term8 = term21.
Proof. exact (TRANS (@lem242073) (@lem242107)). Qed.
Lemma lem242109 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem242110 : term23 = term24.
Proof. exact (MK_COMB (@lem242109) (@lem242108)). Qed.
Lemma lem242113 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem242114 : term26 = term27.
Proof. exact (MK_COMB (@lem242113) (@lem242110)). Qed.
Lemma lem242117 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem242124 : term4 = term29.
Proof. exact (MK_COMB (@lem242117) (@lem242114)). Qed.
Lemma lem242133 (m : nat) (n : nat) : ((term30 m n) = (term31 m n)) = ((term30 m n) = (term31 m n)).
Proof. exact (eq_refl ((term30 m n) = (term31 m n))). Qed.
Lemma lem242134 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem242133 m n)). Qed.
Lemma lem242135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242136 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem242135) (@lem242134 m)). Qed.
Lemma lem242137 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem242136 m)). Qed.
Lemma lem242138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242139 : term19 = term19.
Proof. exact (MK_COMB (@lem242138) (@lem242137)). Qed.
Lemma lem242142 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem242143 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem242142 m)). Qed.
Lemma lem242144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242145 : term16 = term16.
Proof. exact (MK_COMB (@lem242144) (@lem242143)). Qed.
Lemma lem242146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem242147 : term18 = term18.
Proof. exact (MK_COMB (@lem242146) (@lem242145)). Qed.
Lemma lem242148 : term20 = term20.
Proof. exact (MK_COMB (@lem242147) (@lem242139)). Qed.
Lemma lem242149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem242150 : term21 = term21.
Proof. exact (MK_COMB (@lem242149) (@lem242148)). Qed.
Lemma lem242159 (m : nat) (n : nat) : (((Nat.modulo m n) = m) = (term35 m n)) = (((Nat.modulo m n) = m) = (term35 m n)).
Proof. exact (eq_refl (((Nat.modulo m n) = m) = (term35 m n))). Qed.
Lemma lem242160 (m : nat) : (term36 m) = (term36 m).
Proof. exact (fun_ext (fun n : nat => @lem242159 m n)). Qed.
Lemma lem242161 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242162 (m : nat) : (term37 m) = (term37 m).
Proof. exact (MK_COMB (@lem242161) (@lem242160 m)). Qed.
Lemma lem242163 : term38 = term38.
Proof. exact (fun_ext (fun m : nat => @lem242162 m)). Qed.
Lemma lem242164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242165 : term39 = term39.
Proof. exact (MK_COMB (@lem242164) (@lem242163)). Qed.
Lemma lem242166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem242167 : term22 = term22.
Proof. exact (MK_COMB (@lem242166) (@lem242165)). Qed.
Lemma lem242168 : term24 = term24.
Proof. exact (MK_COMB (@lem242167) (@lem242150)). Qed.
Lemma lem242175 (m : nat) (n : nat) : ((term40 m n) = (term41 n)) = ((term40 m n) = (term41 n)).
Proof. exact (eq_refl ((term40 m n) = (term41 n))). Qed.
Lemma lem242176 (m : nat) : (term42 m) = (term42 m).
Proof. exact (fun_ext (fun n : nat => @lem242175 m n)). Qed.
Lemma lem242177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242178 (m : nat) : (term43 m) = (term43 m).
Proof. exact (MK_COMB (@lem242177) (@lem242176 m)). Qed.
Lemma lem242179 : term44 = term44.
Proof. exact (fun_ext (fun m : nat => @lem242178 m)). Qed.
Lemma lem242180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242181 : term45 = term45.
Proof. exact (MK_COMB (@lem242180) (@lem242179)). Qed.
Lemma lem242182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem242183 : term25 = term25.
Proof. exact (MK_COMB (@lem242182) (@lem242181)). Qed.
Lemma lem242184 : term27 = term27.
Proof. exact (MK_COMB (@lem242183) (@lem242168)). Qed.
Lemma lem242185 (P : nat -> Prop) (a : nat) (n : nat) : (term46 P a n) = (term46 P a n).
Proof. exact (eq_refl (term46 P a n)). Qed.
Lemma lem242186 (P : nat -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (fun_ext (fun a : nat => @lem242185 P a n)). Qed.
Lemma lem242187 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242188 (P : nat -> Prop) (n : nat) : (term48 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem242187) (@lem242186 P n)). Qed.
Lemma lem242193 (n : nat) : (term49 n) = (term49 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem242194 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem242193 n) (@lem242188 P n)). Qed.
Lemma lem242199 (n : nat) (P : nat -> Prop) (a : nat) : (term51 n P a) = (term51 n P a).
Proof. exact (eq_refl (term51 n P a)). Qed.
Lemma lem242200 (n : nat) (P : nat -> Prop) : (term52 n P) = (term52 n P).
Proof. exact (fun_ext (fun a : nat => @lem242199 n P a)). Qed.
Lemma lem242201 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242202 (n : nat) (P : nat -> Prop) : (term53 n P) = (term53 n P).
Proof. exact (MK_COMB (@lem242201) (@lem242200 n P)). Qed.
Lemma lem242203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242204 (n : nat) (P : nat -> Prop) : (term54 n P) = (term54 n P).
Proof. exact (MK_COMB (@lem242203) (@lem242202 n P)). Qed.
Lemma lem242205 (P : nat -> Prop) (n : nat) : ((term53 n P) = (term50 P n)) = ((term53 n P) = (term50 P n)).
Proof. exact (MK_COMB (@lem242204 n P) (@lem242194 P n)). Qed.
Lemma lem242206 (P : nat -> Prop) : (term55 P) = (term55 P).
Proof. exact (fun_ext (fun n : nat => @lem242205 P n)). Qed.
Lemma lem242207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242208 (P : nat -> Prop) : (term56 P) = (term56 P).
Proof. exact (MK_COMB (@lem242207) (@lem242206 P)). Qed.
Lemma lem242209 : term57 = term57.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242208 P)). Qed.
Lemma lem242210 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem242211 : term1 = term1.
Proof. exact (MK_COMB (@lem242210) (@lem242209)). Qed.
Lemma lem242212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem242213 : term3 = term3.
Proof. exact (MK_COMB (@lem242212) (@lem242211)). Qed.
Lemma lem242214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem242215 : term28 = term28.
Proof. exact (MK_COMB (@lem242214) (@lem242213)). Qed.
Lemma lem242216 : term29 = term29.
Proof. exact (MK_COMB (@lem242215) (@lem242184)). Qed.
Lemma lem242301 : term4 = term29.
Proof. exact (TRANS (@lem242124) (@lem242216)). Qed.
Lemma lem242302 : term29 = term4.
Proof. exact (SYM (@lem242301)). Qed.
Lemma lem242303 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem242304 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem242305 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem242306 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem242315 (n : nat) (P : nat -> Prop) (a : nat) : (term58 n P a) = (term59 n P a).
Proof. exact (@lem17045 (Peano.lt a n) (P a)). Qed.
Lemma lem242318 (n : nat) (P : nat -> Prop) (a : nat) : (term51 n P a) = (term51 n P a).
Proof. exact (eq_refl (term51 n P a)). Qed.
Lemma lem242319 (P : nat -> Prop) : (term60 P) = (term61 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem242320 (n : nat) (P : nat -> Prop) : (term62 n P) = (term63 n P).
Proof. exact (@lem242319 (term52 n P)). Qed.
Lemma lem242321 (n : nat) (P : nat -> Prop) (a : nat) : (term64 n P a) = (term51 n P a).
Proof. exact (eq_refl (term64 n P a)). Qed.
Lemma lem242322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem242323 (n : nat) (P : nat -> Prop) (a : nat) : (term65 n P a) = (term58 n P a).
Proof. exact (MK_COMB (@lem242322) (@lem242321 n P a)). Qed.
Lemma lem242324 (n : nat) (P : nat -> Prop) (a : nat) : (term65 n P a) = (term59 n P a).
Proof. exact (TRANS (@lem242323 n P a) (@lem242315 n P a)). Qed.
Lemma lem242325 (n : nat) (P : nat -> Prop) : (term66 n P) = (term67 n P).
Proof. exact (fun_ext (fun a : nat => @lem242324 n P a)). Qed.
Lemma lem242326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242327 (n : nat) (P : nat -> Prop) : (term63 n P) = (term68 n P).
Proof. exact (MK_COMB (@lem242326) (@lem242325 n P)). Qed.
Lemma lem242328 (n : nat) (P : nat -> Prop) : (term62 n P) = (term68 n P).
Proof. exact (TRANS (@lem242320 n P) (@lem242327 n P)). Qed.
Lemma lem242329 (n : nat) (P : nat -> Prop) : (term52 n P) = (term52 n P).
Proof. exact (fun_ext (fun a : nat => @lem242318 n P a)). Qed.
Lemma lem242330 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242331 (n : nat) (P : nat -> Prop) : (term53 n P) = (term53 n P).
Proof. exact (MK_COMB (@lem242330) (@lem242329 n P)). Qed.
Lemma lem242335 (n : nat) : (term69 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem242337 (P : nat -> Prop) (a : nat) (n : nat) : (term46 P a n) = (term46 P a n).
Proof. exact (eq_refl (term46 P a n)). Qed.
Lemma lem242338 (P : nat -> Prop) : (term60 P) = (term61 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem242339 (P : nat -> Prop) (n : nat) : (term70 P n) = (term71 P n).
Proof. exact (@lem242338 (term47 P n)). Qed.
Lemma lem242340 (P : nat -> Prop) (a : nat) (n : nat) : (term72 P n a) = (term46 P a n).
Proof. exact (eq_refl (term72 P n a)). Qed.
Lemma lem242341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem242343 (P : nat -> Prop) (a : nat) (n : nat) : (term73 P n a) = (term74 P a n).
Proof. exact (MK_COMB (@lem242341) (@lem242340 P a n)). Qed.
Lemma lem242344 (P : nat -> Prop) (n : nat) : (term75 P n) = (term76 P n).
Proof. exact (fun_ext (fun a : nat => @lem242343 P a n)). Qed.
Lemma lem242345 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem242346 (P : nat -> Prop) (n : nat) : (term71 P n) = (term77 P n).
Proof. exact (MK_COMB (@lem242345) (@lem242344 P n)). Qed.
Lemma lem242347 (P : nat -> Prop) (n : nat) : (term70 P n) = (term77 P n).
Proof. exact (TRANS (@lem242339 P n) (@lem242346 P n)). Qed.
Lemma lem242348 (P : nat -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (fun_ext (fun a : nat => @lem242337 P a n)). Qed.
Lemma lem242349 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242350 (P : nat -> Prop) (n : nat) : (term48 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem242349) (@lem242348 P n)). Qed.
Lemma lem242351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242352 (n : nat) : (term78 n) = (term79 n).
Proof. exact (MK_COMB (@lem242351) (@lem242335 n)). Qed.
Lemma lem242353 (P : nat -> Prop) (n : nat) : (term80 P n) = (term81 P n).
Proof. exact (MK_COMB (@lem242352 n) (@lem242347 P n)). Qed.
Lemma lem242354 (P : nat -> Prop) (n : nat) : (term82 P n) = (term80 P n).
Proof. exact (@lem17045 (term41 n) (term48 P n)). Qed.
Lemma lem242355 (P : nat -> Prop) (n : nat) : (term82 P n) = (term81 P n).
Proof. exact (TRANS (@lem242354 P n) (@lem242353 P n)). Qed.
Lemma lem242357 (n : nat) : (term49 n) = (term49 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem242358 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem242357 n) (@lem242350 P n)). Qed.
Lemma lem242359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem242360 (n : nat) (P : nat -> Prop) : (term83 n P) = (term84 n P).
Proof. exact (MK_COMB (@lem242359) (@lem242328 n P)). Qed.
Lemma lem242361 (P : nat -> Prop) (n : nat) : (term85 P n) = (term86 P n).
Proof. exact (MK_COMB (@lem242360 n P) (@lem242358 P n)). Qed.
Lemma lem242362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem242363 (n : nat) (P : nat -> Prop) : (term87 n P) = (term87 n P).
Proof. exact (MK_COMB (@lem242362) (@lem242331 n P)). Qed.
Lemma lem242364 (P : nat -> Prop) (n : nat) : (term88 P n) = (term89 P n).
Proof. exact (MK_COMB (@lem242363 n P) (@lem242355 P n)). Qed.
Lemma lem242365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242366 (P : nat -> Prop) (n : nat) : (term90 P n) = (term91 P n).
Proof. exact (MK_COMB (@lem242365) (@lem242364 P n)). Qed.
Lemma lem242367 (P : nat -> Prop) (n : nat) : (term92 P n) = (term93 P n).
Proof. exact (MK_COMB (@lem242366 P n) (@lem242361 P n)). Qed.
Lemma lem242368 (P : nat -> Prop) (n : nat) : (term94 P n) = (term92 P n).
Proof. exact (@lem17646 (term53 n P) (term50 P n)). Qed.
Lemma lem242369 (P : nat -> Prop) (n : nat) : (term94 P n) = (term93 P n).
Proof. exact (TRANS (@lem242368 P n) (@lem242367 P n)). Qed.
Lemma lem242370 (P : nat -> Prop) : (term95 P) = (term96 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem242371 (P : nat -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem242370 (term55 P)). Qed.
Lemma lem242372 (P : nat -> Prop) (n : nat) : (term99 P n) = ((term53 n P) = (term50 P n)).
Proof. exact (eq_refl (term99 P n)). Qed.
Lemma lem242373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem242374 (P : nat -> Prop) (n : nat) : (term100 P n) = (term94 P n).
Proof. exact (MK_COMB (@lem242373) (@lem242372 P n)). Qed.
Lemma lem242375 (P : nat -> Prop) (n : nat) : (term100 P n) = (term93 P n).
Proof. exact (TRANS (@lem242374 P n) (@lem242369 P n)). Qed.
Lemma lem242376 (P : nat -> Prop) : (term101 P) = (term102 P).
Proof. exact (fun_ext (fun n : nat => @lem242375 P n)). Qed.
Lemma lem242377 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242378 (P : nat -> Prop) : (term98 P) = (term103 P).
Proof. exact (MK_COMB (@lem242377) (@lem242376 P)). Qed.
Lemma lem242379 (P : nat -> Prop) : (term97 P) = (term103 P).
Proof. exact (TRANS (@lem242371 P) (@lem242378 P)). Qed.
Lemma lem242380 (P : type993) : (term104 P) = (term105 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem242381 : term3 = term106.
Proof. exact (@lem242380 term57). Qed.
Lemma lem242382 (P : nat -> Prop) : (term107 P) = (term56 P).
Proof. exact (eq_refl (term107 P)). Qed.
Lemma lem242383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem242384 (P : nat -> Prop) : (term108 P) = (term97 P).
Proof. exact (MK_COMB (@lem242383) (@lem242382 P)). Qed.
Lemma lem242385 (P : nat -> Prop) : (term108 P) = (term103 P).
Proof. exact (TRANS (@lem242384 P) (@lem242379 P)). Qed.
Lemma lem242386 : term109 = term110.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242385 P)). Qed.
Lemma lem242387 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242388 : term106 = term111.
Proof. exact (MK_COMB (@lem242387) (@lem242386)). Qed.
Lemma lem242389 : term3 = term111.
Proof. exact (TRANS (@lem242381) (@lem242388)). Qed.
Lemma lem242395 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem242396 (P : nat -> Prop) (Q : nat -> Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem242395 nat P Q). Qed.
Lemma lem242397 (P : nat -> Prop) : (term116 P) = (term117 P).
Proof. exact (@lem242396 (term118 P) (term119 P)). Qed.
Lemma lem242398 (P : nat -> Prop) (n : nat) : (term120 P n) = (term89 P n).
Proof. exact (eq_refl (term120 P n)). Qed.
Lemma lem242399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242400 (P : nat -> Prop) (n : nat) : (term121 P n) = (term91 P n).
Proof. exact (MK_COMB (@lem242399) (@lem242398 P n)). Qed.
Lemma lem242401 (P : nat -> Prop) (n : nat) : (term122 P n) = (term86 P n).
Proof. exact (eq_refl (term122 P n)). Qed.
Lemma lem242402 (P : nat -> Prop) (n : nat) : (term123 P n) = (term93 P n).
Proof. exact (MK_COMB (@lem242400 P n) (@lem242401 P n)). Qed.
Lemma lem242403 (P : nat -> Prop) : (term124 P) = (term102 P).
Proof. exact (fun_ext (fun n : nat => @lem242402 P n)). Qed.
Lemma lem242404 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242405 (P : nat -> Prop) : (term116 P) = (term103 P).
Proof. exact (MK_COMB (@lem242404) (@lem242403 P)). Qed.
Lemma lem242406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242407 (P : nat -> Prop) : (term125 P) = (term126 P).
Proof. exact (MK_COMB (@lem242406) (@lem242405 P)). Qed.
Lemma lem242408 (P : nat -> Prop) (n : nat) : (term120 P n) = (term89 P n).
Proof. exact (eq_refl (term120 P n)). Qed.
Lemma lem242409 (P : nat -> Prop) : (term127 P) = (term118 P).
Proof. exact (fun_ext (fun n : nat => @lem242408 P n)). Qed.
Lemma lem242410 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242411 (P : nat -> Prop) : (term128 P) = (term129 P).
Proof. exact (MK_COMB (@lem242410) (@lem242409 P)). Qed.
Lemma lem242412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242413 (P : nat -> Prop) : (term130 P) = (term131 P).
Proof. exact (MK_COMB (@lem242412) (@lem242411 P)). Qed.
Lemma lem242414 (P : nat -> Prop) (n : nat) : (term122 P n) = (term86 P n).
Proof. exact (eq_refl (term122 P n)). Qed.
Lemma lem242415 (P : nat -> Prop) : (term132 P) = (term119 P).
Proof. exact (fun_ext (fun n : nat => @lem242414 P n)). Qed.
Lemma lem242416 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242417 (P : nat -> Prop) : (term133 P) = (term134 P).
Proof. exact (MK_COMB (@lem242416) (@lem242415 P)). Qed.
Lemma lem242418 (P : nat -> Prop) : (term117 P) = (term135 P).
Proof. exact (MK_COMB (@lem242413 P) (@lem242417 P)). Qed.
Lemma lem242419 (P : nat -> Prop) : ((term116 P) = (term117 P)) = ((term103 P) = (term135 P)).
Proof. exact (MK_COMB (@lem242407 P) (@lem242418 P)). Qed.
Lemma lem242420 (P : nat -> Prop) : (term103 P) = (term135 P).
Proof. exact (EQ_MP (@lem242419 P) (@lem242397 P)). Qed.
Lemma lem242605 : term110 = term136.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242420 P)). Qed.
Lemma lem242606 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242607 : term111 = term137.
Proof. exact (MK_COMB (@lem242606) (@lem242605)). Qed.
Lemma lem242609 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem242610 (P : type993) (Q : type993) : (term138 P Q) = (term139 P Q).
Proof. exact (@lem242609 (nat -> Prop) P Q). Qed.
Lemma lem242611 : term140 = term141.
Proof. exact (@lem242610 term142 term143). Qed.
Lemma lem242612 (P : nat -> Prop) : (term144 P) = (term129 P).
Proof. exact (eq_refl (term144 P)). Qed.
Lemma lem242613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242614 (P : nat -> Prop) : (term145 P) = (term131 P).
Proof. exact (MK_COMB (@lem242613) (@lem242612 P)). Qed.
Lemma lem242615 (P : nat -> Prop) : (term146 P) = (term134 P).
Proof. exact (eq_refl (term146 P)). Qed.
Lemma lem242616 (P : nat -> Prop) : (term147 P) = (term135 P).
Proof. exact (MK_COMB (@lem242614 P) (@lem242615 P)). Qed.
Lemma lem242617 : term148 = term136.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242616 P)). Qed.
Lemma lem242618 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242619 : term140 = term137.
Proof. exact (MK_COMB (@lem242618) (@lem242617)). Qed.
Lemma lem242620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242621 : term149 = term150.
Proof. exact (MK_COMB (@lem242620) (@lem242619)). Qed.
Lemma lem242622 (P : nat -> Prop) : (term144 P) = (term129 P).
Proof. exact (eq_refl (term144 P)). Qed.
Lemma lem242623 : term151 = term142.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242622 P)). Qed.
Lemma lem242624 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242625 : term152 = term153.
Proof. exact (MK_COMB (@lem242624) (@lem242623)). Qed.
Lemma lem242626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242627 : term154 = term155.
Proof. exact (MK_COMB (@lem242626) (@lem242625)). Qed.
Lemma lem242628 (P : nat -> Prop) : (term146 P) = (term134 P).
Proof. exact (eq_refl (term146 P)). Qed.
Lemma lem242629 : term156 = term143.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242628 P)). Qed.
Lemma lem242630 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242631 : term157 = term158.
Proof. exact (MK_COMB (@lem242630) (@lem242629)). Qed.
Lemma lem242632 : term141 = term159.
Proof. exact (MK_COMB (@lem242627) (@lem242631)). Qed.
Lemma lem242633 : (term140 = term141) = (term137 = term159).
Proof. exact (MK_COMB (@lem242621) (@lem242632)). Qed.
Lemma lem242634 : term137 = term159.
Proof. exact (EQ_MP (@lem242633) (@lem242611)). Qed.
Lemma lem242827 : term111 = term159.
Proof. exact (TRANS (@lem242607) (@lem242634)). Qed.
Lemma lem242829 {A : Type'} (P : A -> Prop) (Q : Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem242830 (P : nat -> Prop) (Q : Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem242829 nat P Q). Qed.
Lemma lem242831 (P : nat -> Prop) (n : nat) : (term164 P n) = (term165 P n).
Proof. exact (@lem242830 (term52 n P) (term81 P n)). Qed.
Lemma lem242832 (n : nat) (P : nat -> Prop) (a : nat) : (term64 n P a) = (term51 n P a).
Proof. exact (eq_refl (term64 n P a)). Qed.
Lemma lem242833 (n : nat) (P : nat -> Prop) : (term166 n P) = (term52 n P).
Proof. exact (fun_ext (fun a : nat => @lem242832 n P a)). Qed.
Lemma lem242834 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242835 (n : nat) (P : nat -> Prop) : (term167 n P) = (term53 n P).
Proof. exact (MK_COMB (@lem242834) (@lem242833 n P)). Qed.
Lemma lem242836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem242837 (n : nat) (P : nat -> Prop) : (term168 n P) = (term87 n P).
Proof. exact (MK_COMB (@lem242836) (@lem242835 n P)). Qed.
Lemma lem242838 (P : nat -> Prop) (n : nat) : (term81 P n) = (term81 P n).
Proof. exact (eq_refl (term81 P n)). Qed.
Lemma lem242839 (P : nat -> Prop) (n : nat) : (term164 P n) = (term89 P n).
Proof. exact (MK_COMB (@lem242837 n P) (@lem242838 P n)). Qed.
Lemma lem242840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242841 (P : nat -> Prop) (n : nat) : (term169 P n) = (term170 P n).
Proof. exact (MK_COMB (@lem242840) (@lem242839 P n)). Qed.
Lemma lem242842 (n : nat) (P : nat -> Prop) (a : nat) : (term64 n P a) = (term51 n P a).
Proof. exact (eq_refl (term64 n P a)). Qed.
Lemma lem242843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem242844 (n : nat) (P : nat -> Prop) (a : nat) : (term171 n P a) = (term172 n P a).
Proof. exact (MK_COMB (@lem242843) (@lem242842 n P a)). Qed.
Lemma lem242845 (P : nat -> Prop) (n : nat) : (term81 P n) = (term81 P n).
Proof. exact (eq_refl (term81 P n)). Qed.
Lemma lem242846 (a : nat) (P : nat -> Prop) (n : nat) : (term173 a P n) = (term174 a P n).
Proof. exact (MK_COMB (@lem242844 n P a) (@lem242845 P n)). Qed.
Lemma lem242847 (P : nat -> Prop) (n : nat) : (term175 P n) = (term176 P n).
Proof. exact (fun_ext (fun a : nat => @lem242846 a P n)). Qed.
Lemma lem242848 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242849 (P : nat -> Prop) (n : nat) : (term165 P n) = (term177 P n).
Proof. exact (MK_COMB (@lem242848) (@lem242847 P n)). Qed.
Lemma lem242850 (P : nat -> Prop) (n : nat) : ((term164 P n) = (term165 P n)) = ((term89 P n) = (term177 P n)).
Proof. exact (MK_COMB (@lem242841 P n) (@lem242849 P n)). Qed.
Lemma lem242851 (P : nat -> Prop) (n : nat) : (term89 P n) = (term177 P n).
Proof. exact (EQ_MP (@lem242850 P n) (@lem242831 P n)). Qed.
Lemma lem242852 (P : nat -> Prop) : (term118 P) = (term178 P).
Proof. exact (fun_ext (fun n : nat => @lem242851 P n)). Qed.
Lemma lem242853 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242854 (P : nat -> Prop) : (term129 P) = (term179 P).
Proof. exact (MK_COMB (@lem242853) (@lem242852 P)). Qed.
Lemma lem242855 : term142 = term180.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242854 P)). Qed.
Lemma lem242856 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242857 : term153 = term181.
Proof. exact (MK_COMB (@lem242856) (@lem242855)). Qed.
Lemma lem242858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242859 : term155 = term182.
Proof. exact (MK_COMB (@lem242858) (@lem242857)). Qed.
Lemma lem242861 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem242862 (P : Prop) (Q : nat -> Prop) : (term185 P Q) = (term186 P Q).
Proof. exact (@lem242861 nat P Q). Qed.
Lemma lem242863 (P : nat -> Prop) (n : nat) : (term187 P n) = (term188 P n).
Proof. exact (@lem242862 (term41 n) (term47 P n)). Qed.
Lemma lem242864 (P : nat -> Prop) (a : nat) (n : nat) : (term72 P n a) = (term46 P a n).
Proof. exact (eq_refl (term72 P n a)). Qed.
Lemma lem242865 (P : nat -> Prop) (n : nat) : (term189 P n) = (term47 P n).
Proof. exact (fun_ext (fun a : nat => @lem242864 P a n)). Qed.
Lemma lem242866 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242867 (P : nat -> Prop) (n : nat) : (term190 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem242866) (@lem242865 P n)). Qed.
Lemma lem242868 (n : nat) : (term49 n) = (term49 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem242869 (P : nat -> Prop) (n : nat) : (term187 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem242868 n) (@lem242867 P n)). Qed.
Lemma lem242870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242871 (P : nat -> Prop) (n : nat) : (term191 P n) = (term192 P n).
Proof. exact (MK_COMB (@lem242870) (@lem242869 P n)). Qed.
Lemma lem242872 (P : nat -> Prop) (a : nat) (n : nat) : (term72 P n a) = (term46 P a n).
Proof. exact (eq_refl (term72 P n a)). Qed.
Lemma lem242873 (n : nat) : (term49 n) = (term49 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem242874 (P : nat -> Prop) (a : nat) (n : nat) : (term193 P n a) = (term194 P a n).
Proof. exact (MK_COMB (@lem242873 n) (@lem242872 P a n)). Qed.
Lemma lem242875 (P : nat -> Prop) (n : nat) : (term195 P n) = (term196 P n).
Proof. exact (fun_ext (fun a : nat => @lem242874 P a n)). Qed.
Lemma lem242876 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242877 (P : nat -> Prop) (n : nat) : (term188 P n) = (term197 P n).
Proof. exact (MK_COMB (@lem242876) (@lem242875 P n)). Qed.
Lemma lem242878 (P : nat -> Prop) (n : nat) : ((term187 P n) = (term188 P n)) = ((term50 P n) = (term197 P n)).
Proof. exact (MK_COMB (@lem242871 P n) (@lem242877 P n)). Qed.
Lemma lem242879 (P : nat -> Prop) (n : nat) : (term50 P n) = (term197 P n).
Proof. exact (EQ_MP (@lem242878 P n) (@lem242863 P n)). Qed.
Lemma lem242880 (n : nat) (P : nat -> Prop) : (term84 n P) = (term84 n P).
Proof. exact (eq_refl (term84 n P)). Qed.
Lemma lem242881 (P : nat -> Prop) (n : nat) : (term86 P n) = (term198 P n).
Proof. exact (MK_COMB (@lem242880 n P) (@lem242879 P n)). Qed.
Lemma lem242883 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem242884 (P : Prop) (Q : nat -> Prop) : (term185 P Q) = (term186 P Q).
Proof. exact (@lem242883 nat P Q). Qed.
Lemma lem242885 (P : nat -> Prop) (n : nat) : (term199 P n) = (term200 P n).
Proof. exact (@lem242884 (term68 n P) (term196 P n)). Qed.
Lemma lem242886 (P : nat -> Prop) (a : nat) (n : nat) : (term201 P n a) = (term194 P a n).
Proof. exact (eq_refl (term201 P n a)). Qed.
Lemma lem242887 (P : nat -> Prop) (n : nat) : (term202 P n) = (term196 P n).
Proof. exact (fun_ext (fun a : nat => @lem242886 P a n)). Qed.
Lemma lem242888 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242889 (P : nat -> Prop) (n : nat) : (term203 P n) = (term197 P n).
Proof. exact (MK_COMB (@lem242888) (@lem242887 P n)). Qed.
Lemma lem242890 (n : nat) (P : nat -> Prop) : (term84 n P) = (term84 n P).
Proof. exact (eq_refl (term84 n P)). Qed.
Lemma lem242891 (P : nat -> Prop) (n : nat) : (term199 P n) = (term198 P n).
Proof. exact (MK_COMB (@lem242890 n P) (@lem242889 P n)). Qed.
Lemma lem242892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242893 (P : nat -> Prop) (n : nat) : (term204 P n) = (term205 P n).
Proof. exact (MK_COMB (@lem242892) (@lem242891 P n)). Qed.
Lemma lem242894 (P : nat -> Prop) (a : nat) (n : nat) : (term201 P n a) = (term194 P a n).
Proof. exact (eq_refl (term201 P n a)). Qed.
Lemma lem242895 (n : nat) (P : nat -> Prop) : (term84 n P) = (term84 n P).
Proof. exact (eq_refl (term84 n P)). Qed.
Lemma lem242896 (P : nat -> Prop) (a : nat) (n : nat) : (term206 P n a) = (term207 P a n).
Proof. exact (MK_COMB (@lem242895 n P) (@lem242894 P a n)). Qed.
Lemma lem242897 (P : nat -> Prop) (n : nat) : (term208 P n) = (term209 P n).
Proof. exact (fun_ext (fun a : nat => @lem242896 P a n)). Qed.
Lemma lem242898 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242899 (P : nat -> Prop) (n : nat) : (term200 P n) = (term210 P n).
Proof. exact (MK_COMB (@lem242898) (@lem242897 P n)). Qed.
Lemma lem242900 (P : nat -> Prop) (n : nat) : ((term199 P n) = (term200 P n)) = ((term198 P n) = (term210 P n)).
Proof. exact (MK_COMB (@lem242893 P n) (@lem242899 P n)). Qed.
Lemma lem242901 (P : nat -> Prop) (n : nat) : (term198 P n) = (term210 P n).
Proof. exact (EQ_MP (@lem242900 P n) (@lem242885 P n)). Qed.
Lemma lem242902 (P : nat -> Prop) (n : nat) : (term86 P n) = (term210 P n).
Proof. exact (TRANS (@lem242881 P n) (@lem242901 P n)). Qed.
Lemma lem242903 (P : nat -> Prop) : (term119 P) = (term211 P).
Proof. exact (fun_ext (fun n : nat => @lem242902 P n)). Qed.
Lemma lem242904 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242905 (P : nat -> Prop) : (term134 P) = (term212 P).
Proof. exact (MK_COMB (@lem242904) (@lem242903 P)). Qed.
Lemma lem242906 : term143 = term213.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242905 P)). Qed.
Lemma lem242907 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242908 : term158 = term214.
Proof. exact (MK_COMB (@lem242907) (@lem242906)). Qed.
Lemma lem242909 : term159 = term215.
Proof. exact (MK_COMB (@lem242859) (@lem242908)). Qed.
Lemma lem242911 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem242912 (P : type993) (Q : type993) : (term139 P Q) = (term138 P Q).
Proof. exact (@lem242911 (nat -> Prop) P Q). Qed.
Lemma lem242913 : term216 = term217.
Proof. exact (@lem242912 term180 term213). Qed.
Lemma lem242914 (P : nat -> Prop) : (term218 P) = (term179 P).
Proof. exact (eq_refl (term218 P)). Qed.
Lemma lem242915 : term219 = term180.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242914 P)). Qed.
Lemma lem242916 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242917 : term220 = term181.
Proof. exact (MK_COMB (@lem242916) (@lem242915)). Qed.
Lemma lem242918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242919 : term221 = term182.
Proof. exact (MK_COMB (@lem242918) (@lem242917)). Qed.
Lemma lem242920 (P : nat -> Prop) : (term222 P) = (term212 P).
Proof. exact (eq_refl (term222 P)). Qed.
Lemma lem242921 : term223 = term213.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242920 P)). Qed.
Lemma lem242922 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242923 : term224 = term214.
Proof. exact (MK_COMB (@lem242922) (@lem242921)). Qed.
Lemma lem242924 : term216 = term215.
Proof. exact (MK_COMB (@lem242919) (@lem242923)). Qed.
Lemma lem242925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242926 : term225 = term226.
Proof. exact (MK_COMB (@lem242925) (@lem242924)). Qed.
Lemma lem242927 (P : nat -> Prop) : (term218 P) = (term179 P).
Proof. exact (eq_refl (term218 P)). Qed.
Lemma lem242928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242929 (P : nat -> Prop) : (term227 P) = (term228 P).
Proof. exact (MK_COMB (@lem242928) (@lem242927 P)). Qed.
Lemma lem242930 (P : nat -> Prop) : (term222 P) = (term212 P).
Proof. exact (eq_refl (term222 P)). Qed.
Lemma lem242931 (P : nat -> Prop) : (term229 P) = (term230 P).
Proof. exact (MK_COMB (@lem242929 P) (@lem242930 P)). Qed.
Lemma lem242932 : term231 = term232.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242931 P)). Qed.
Lemma lem242933 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242934 : term217 = term233.
Proof. exact (MK_COMB (@lem242933) (@lem242932)). Qed.
Lemma lem242935 : (term216 = term217) = (term215 = term233).
Proof. exact (MK_COMB (@lem242926) (@lem242934)). Qed.
Lemma lem242936 : term215 = term233.
Proof. exact (EQ_MP (@lem242935) (@lem242913)). Qed.
Lemma lem242938 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem242939 (P : nat -> Prop) (Q : nat -> Prop) : (term115 P Q) = (term114 P Q).
Proof. exact (@lem242938 nat P Q). Qed.
Lemma lem242940 (P : nat -> Prop) : (term234 P) = (term235 P).
Proof. exact (@lem242939 (term178 P) (term211 P)). Qed.
Lemma lem242941 (P : nat -> Prop) (n : nat) : (term236 P n) = (term177 P n).
Proof. exact (eq_refl (term236 P n)). Qed.
Lemma lem242942 (P : nat -> Prop) : (term237 P) = (term178 P).
Proof. exact (fun_ext (fun n : nat => @lem242941 P n)). Qed.
Lemma lem242943 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242944 (P : nat -> Prop) : (term238 P) = (term179 P).
Proof. exact (MK_COMB (@lem242943) (@lem242942 P)). Qed.
Lemma lem242945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242946 (P : nat -> Prop) : (term239 P) = (term228 P).
Proof. exact (MK_COMB (@lem242945) (@lem242944 P)). Qed.
Lemma lem242947 (P : nat -> Prop) (n : nat) : (term240 P n) = (term210 P n).
Proof. exact (eq_refl (term240 P n)). Qed.
Lemma lem242948 (P : nat -> Prop) : (term241 P) = (term211 P).
Proof. exact (fun_ext (fun n : nat => @lem242947 P n)). Qed.
Lemma lem242949 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242950 (P : nat -> Prop) : (term242 P) = (term212 P).
Proof. exact (MK_COMB (@lem242949) (@lem242948 P)). Qed.
Lemma lem242951 (P : nat -> Prop) : (term234 P) = (term230 P).
Proof. exact (MK_COMB (@lem242946 P) (@lem242950 P)). Qed.
Lemma lem242952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242953 (P : nat -> Prop) : (term243 P) = (term244 P).
Proof. exact (MK_COMB (@lem242952) (@lem242951 P)). Qed.
Lemma lem242954 (P : nat -> Prop) (n : nat) : (term236 P n) = (term177 P n).
Proof. exact (eq_refl (term236 P n)). Qed.
Lemma lem242955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242956 (P : nat -> Prop) (n : nat) : (term245 P n) = (term246 P n).
Proof. exact (MK_COMB (@lem242955) (@lem242954 P n)). Qed.
Lemma lem242957 (P : nat -> Prop) (n : nat) : (term240 P n) = (term210 P n).
Proof. exact (eq_refl (term240 P n)). Qed.
Lemma lem242958 (P : nat -> Prop) (n : nat) : (term247 P n) = (term248 P n).
Proof. exact (MK_COMB (@lem242956 P n) (@lem242957 P n)). Qed.
Lemma lem242959 (P : nat -> Prop) : (term249 P) = (term250 P).
Proof. exact (fun_ext (fun n : nat => @lem242958 P n)). Qed.
Lemma lem242960 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242961 (P : nat -> Prop) : (term235 P) = (term251 P).
Proof. exact (MK_COMB (@lem242960) (@lem242959 P)). Qed.
Lemma lem242962 (P : nat -> Prop) : ((term234 P) = (term235 P)) = ((term230 P) = (term251 P)).
Proof. exact (MK_COMB (@lem242953 P) (@lem242961 P)). Qed.
Lemma lem242963 (P : nat -> Prop) : (term230 P) = (term251 P).
Proof. exact (EQ_MP (@lem242962 P) (@lem242940 P)). Qed.
Lemma lem242965 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem242966 (P : nat -> Prop) (Q : nat -> Prop) : (term115 P Q) = (term114 P Q).
Proof. exact (@lem242965 nat P Q). Qed.
Lemma lem242967 (P : nat -> Prop) (n : nat) : (term252 P n) = (term253 P n).
Proof. exact (@lem242966 (term176 P n) (term209 P n)). Qed.
Lemma lem242968 (a : nat) (P : nat -> Prop) (n : nat) : (term254 P n a) = (term174 a P n).
Proof. exact (eq_refl (term254 P n a)). Qed.
Lemma lem242969 (P : nat -> Prop) (n : nat) : (term255 P n) = (term176 P n).
Proof. exact (fun_ext (fun a : nat => @lem242968 a P n)). Qed.
Lemma lem242970 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242971 (P : nat -> Prop) (n : nat) : (term256 P n) = (term177 P n).
Proof. exact (MK_COMB (@lem242970) (@lem242969 P n)). Qed.
Lemma lem242972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242973 (P : nat -> Prop) (n : nat) : (term257 P n) = (term246 P n).
Proof. exact (MK_COMB (@lem242972) (@lem242971 P n)). Qed.
Lemma lem242974 (P : nat -> Prop) (a : nat) (n : nat) : (term258 P n a) = (term207 P a n).
Proof. exact (eq_refl (term258 P n a)). Qed.
Lemma lem242975 (P : nat -> Prop) (n : nat) : (term259 P n) = (term209 P n).
Proof. exact (fun_ext (fun a : nat => @lem242974 P a n)). Qed.
Lemma lem242976 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242977 (P : nat -> Prop) (n : nat) : (term260 P n) = (term210 P n).
Proof. exact (MK_COMB (@lem242976) (@lem242975 P n)). Qed.
Lemma lem242978 (P : nat -> Prop) (n : nat) : (term252 P n) = (term248 P n).
Proof. exact (MK_COMB (@lem242973 P n) (@lem242977 P n)). Qed.
Lemma lem242979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem242980 (P : nat -> Prop) (n : nat) : (term261 P n) = (term262 P n).
Proof. exact (MK_COMB (@lem242979) (@lem242978 P n)). Qed.
Lemma lem242981 (a : nat) (P : nat -> Prop) (n : nat) : (term254 P n a) = (term174 a P n).
Proof. exact (eq_refl (term254 P n a)). Qed.
Lemma lem242982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem242983 (a : nat) (P : nat -> Prop) (n : nat) : (term263 P n a) = (term264 a P n).
Proof. exact (MK_COMB (@lem242982) (@lem242981 a P n)). Qed.
Lemma lem242984 (P : nat -> Prop) (a : nat) (n : nat) : (term258 P n a) = (term207 P a n).
Proof. exact (eq_refl (term258 P n a)). Qed.
Lemma lem242985 (P : nat -> Prop) (a : nat) (n : nat) : (term265 P n a) = (term266 P a n).
Proof. exact (MK_COMB (@lem242983 a P n) (@lem242984 P a n)). Qed.
Lemma lem242986 (P : nat -> Prop) (n : nat) : (term267 P n) = (term268 P n).
Proof. exact (fun_ext (fun a : nat => @lem242985 P a n)). Qed.
Lemma lem242987 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242988 (P : nat -> Prop) (n : nat) : (term253 P n) = (term269 P n).
Proof. exact (MK_COMB (@lem242987) (@lem242986 P n)). Qed.
Lemma lem242989 (P : nat -> Prop) (n : nat) : ((term252 P n) = (term253 P n)) = ((term248 P n) = (term269 P n)).
Proof. exact (MK_COMB (@lem242980 P n) (@lem242988 P n)). Qed.
Lemma lem242990 (P : nat -> Prop) (n : nat) : (term248 P n) = (term269 P n).
Proof. exact (EQ_MP (@lem242989 P n) (@lem242967 P n)). Qed.
Lemma lem242991 (P : nat -> Prop) : (term250 P) = (term270 P).
Proof. exact (fun_ext (fun n : nat => @lem242990 P n)). Qed.
Lemma lem242992 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem242993 (P : nat -> Prop) : (term251 P) = (term271 P).
Proof. exact (MK_COMB (@lem242992) (@lem242991 P)). Qed.
Lemma lem242994 (P : nat -> Prop) : (term230 P) = (term271 P).
Proof. exact (TRANS (@lem242963 P) (@lem242993 P)). Qed.
Lemma lem242995 : term232 = term272.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem242994 P)). Qed.
Lemma lem242996 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem242997 : term233 = term273.
Proof. exact (MK_COMB (@lem242996) (@lem242995)). Qed.
Lemma lem242998 : term215 = term273.
Proof. exact (TRANS (@lem242936) (@lem242997)). Qed.
Lemma lem242999 : term159 = term273.
Proof. exact (TRANS (@lem242909) (@lem242998)). Qed.
Lemma lem243000 : term111 = term273.
Proof. exact (TRANS (@lem242827) (@lem242999)). Qed.
Lemma lem243001 : term3 = term273.
Proof. exact (TRANS (@lem242389) (@lem243000)). Qed.
Lemma lem243002 (h1 : term3) : term273.
Proof. exact (EQ_MP (@lem243001) (@lem242303 h1)). Qed.
Lemma lem243008 (n : nat) : (term69 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem243011 (m : nat) (n : nat) : (term274 m n) = (term274 m n).
Proof. exact (eq_refl (term274 m n)). Qed.
Lemma lem243013 (m : nat) (n : nat) : (term275 m n) = (term275 m n).
Proof. exact (eq_refl (term275 m n)). Qed.
Lemma lem243014 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (MK_COMB (@lem243013 m n) (@lem243008 n)). Qed.
Lemma lem243015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243016 (m : nat) (n : nat) : (term278 m n) = (term279 m n).
Proof. exact (MK_COMB (@lem243015) (@lem243014 m n)). Qed.
Lemma lem243017 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (MK_COMB (@lem243016 m n) (@lem243011 m n)). Qed.
Lemma lem243018 (m : nat) (n : nat) : ((term40 m n) = (term41 n)) = (term280 m n).
Proof. exact (@lem17784 (term40 m n) (term41 n)). Qed.
Lemma lem243019 (m : nat) (n : nat) : ((term40 m n) = (term41 n)) = (term281 m n).
Proof. exact (TRANS (@lem243018 m n) (@lem243017 m n)). Qed.
Lemma lem243020 (m : nat) : (term42 m) = (term282 m).
Proof. exact (fun_ext (fun n : nat => @lem243019 m n)). Qed.
Lemma lem243021 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243022 (m : nat) : (term43 m) = (term283 m).
Proof. exact (MK_COMB (@lem243021) (@lem243020 m)). Qed.
Lemma lem243023 : term44 = term284.
Proof. exact (fun_ext (fun m : nat => @lem243022 m)). Qed.
Lemma lem243024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243025 : term45 = term285.
Proof. exact (MK_COMB (@lem243024) (@lem243023)). Qed.
Lemma lem243031 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem243032 (P : nat -> Prop) (Q : nat -> Prop) : (term288 P Q) = (term289 P Q).
Proof. exact (@lem243031 nat P Q). Qed.
Lemma lem243033 (m : nat) : (term290 m) = (term291 m).
Proof. exact (@lem243032 (term292 m) (term293 m)). Qed.
Lemma lem243034 (m : nat) (n : nat) : (term294 m n) = (term277 m n).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem243035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243036 (m : nat) (n : nat) : (term295 m n) = (term279 m n).
Proof. exact (MK_COMB (@lem243035) (@lem243034 m n)). Qed.
Lemma lem243037 (m : nat) (n : nat) : (term296 m n) = (term274 m n).
Proof. exact (eq_refl (term296 m n)). Qed.
Lemma lem243038 (m : nat) (n : nat) : (term297 m n) = (term281 m n).
Proof. exact (MK_COMB (@lem243036 m n) (@lem243037 m n)). Qed.
Lemma lem243039 (m : nat) : (term298 m) = (term282 m).
Proof. exact (fun_ext (fun n : nat => @lem243038 m n)). Qed.
Lemma lem243040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243041 (m : nat) : (term290 m) = (term283 m).
Proof. exact (MK_COMB (@lem243040) (@lem243039 m)). Qed.
Lemma lem243042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem243043 (m : nat) : (term299 m) = (term300 m).
Proof. exact (MK_COMB (@lem243042) (@lem243041 m)). Qed.
Lemma lem243044 (m : nat) (n : nat) : (term294 m n) = (term277 m n).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem243045 (m : nat) : (term301 m) = (term292 m).
Proof. exact (fun_ext (fun n : nat => @lem243044 m n)). Qed.
Lemma lem243046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243047 (m : nat) : (term302 m) = (term303 m).
Proof. exact (MK_COMB (@lem243046) (@lem243045 m)). Qed.
Lemma lem243048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243049 (m : nat) : (term304 m) = (term305 m).
Proof. exact (MK_COMB (@lem243048) (@lem243047 m)). Qed.
Lemma lem243050 (m : nat) (n : nat) : (term296 m n) = (term274 m n).
Proof. exact (eq_refl (term296 m n)). Qed.
Lemma lem243051 (m : nat) : (term306 m) = (term293 m).
Proof. exact (fun_ext (fun n : nat => @lem243050 m n)). Qed.
Lemma lem243052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243053 (m : nat) : (term307 m) = (term308 m).
Proof. exact (MK_COMB (@lem243052) (@lem243051 m)). Qed.
Lemma lem243054 (m : nat) : (term291 m) = (term309 m).
Proof. exact (MK_COMB (@lem243049 m) (@lem243053 m)). Qed.
Lemma lem243055 (m : nat) : ((term290 m) = (term291 m)) = ((term283 m) = (term309 m)).
Proof. exact (MK_COMB (@lem243043 m) (@lem243054 m)). Qed.
Lemma lem243056 (m : nat) : (term283 m) = (term309 m).
Proof. exact (EQ_MP (@lem243055 m) (@lem243033 m)). Qed.
Lemma lem243153 : term284 = term310.
Proof. exact (fun_ext (fun m : nat => @lem243056 m)). Qed.
Lemma lem243154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243155 : term285 = term311.
Proof. exact (MK_COMB (@lem243154) (@lem243153)). Qed.
Lemma lem243157 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem243158 (P : nat -> Prop) (Q : nat -> Prop) : (term288 P Q) = (term289 P Q).
Proof. exact (@lem243157 nat P Q). Qed.
Lemma lem243159 : term312 = term313.
Proof. exact (@lem243158 term314 term315). Qed.
Lemma lem243160 (m : nat) : (term316 m) = (term303 m).
Proof. exact (eq_refl (term316 m)). Qed.
Lemma lem243161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243162 (m : nat) : (term317 m) = (term305 m).
Proof. exact (MK_COMB (@lem243161) (@lem243160 m)). Qed.
Lemma lem243163 (m : nat) : (term318 m) = (term308 m).
Proof. exact (eq_refl (term318 m)). Qed.
Lemma lem243164 (m : nat) : (term319 m) = (term309 m).
Proof. exact (MK_COMB (@lem243162 m) (@lem243163 m)). Qed.
Lemma lem243165 : term320 = term310.
Proof. exact (fun_ext (fun m : nat => @lem243164 m)). Qed.
Lemma lem243166 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243167 : term312 = term311.
Proof. exact (MK_COMB (@lem243166) (@lem243165)). Qed.
Lemma lem243168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem243169 : term321 = term322.
Proof. exact (MK_COMB (@lem243168) (@lem243167)). Qed.
Lemma lem243170 (m : nat) : (term316 m) = (term303 m).
Proof. exact (eq_refl (term316 m)). Qed.
Lemma lem243171 : term323 = term314.
Proof. exact (fun_ext (fun m : nat => @lem243170 m)). Qed.
Lemma lem243172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243173 : term324 = term325.
Proof. exact (MK_COMB (@lem243172) (@lem243171)). Qed.
Lemma lem243174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243175 : term326 = term327.
Proof. exact (MK_COMB (@lem243174) (@lem243173)). Qed.
Lemma lem243176 (m : nat) : (term318 m) = (term308 m).
Proof. exact (eq_refl (term318 m)). Qed.
Lemma lem243177 : term328 = term315.
Proof. exact (fun_ext (fun m : nat => @lem243176 m)). Qed.
Lemma lem243178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243179 : term329 = term330.
Proof. exact (MK_COMB (@lem243178) (@lem243177)). Qed.
Lemma lem243180 : term313 = term331.
Proof. exact (MK_COMB (@lem243175) (@lem243179)). Qed.
Lemma lem243181 : (term312 = term313) = (term311 = term331).
Proof. exact (MK_COMB (@lem243169) (@lem243180)). Qed.
Lemma lem243182 : term311 = term331.
Proof. exact (EQ_MP (@lem243181) (@lem243159)). Qed.
Lemma lem243289 : term285 = term331.
Proof. exact (TRANS (@lem243155) (@lem243182)). Qed.
Lemma lem243290 : term45 = term331.
Proof. exact (TRANS (@lem243025) (@lem243289)). Qed.
Lemma lem243291 (h1 : term45) : term331.
Proof. exact (EQ_MP (@lem243290) (@lem242304 h1)). Qed.
Lemma lem243302 (m : nat) (n : nat) : (term332 m n) = (term333 m n).
Proof. exact (@lem17160 (n = (NUMERAL 0)) (Peano.lt m n)). Qed.
Lemma lem243308 (m : nat) (n : nat) : (term334 m n) = (term334 m n).
Proof. exact (eq_refl (term334 m n)). Qed.
Lemma lem243310 (n : nat) (m : nat) : (term335 n m) = (term335 n m).
Proof. exact (eq_refl (term335 n m)). Qed.
Lemma lem243311 (m : nat) (n : nat) : (term336 m n) = (term337 m n).
Proof. exact (MK_COMB (@lem243310 n m) (@lem243302 m n)). Qed.
Lemma lem243312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243313 (m : nat) (n : nat) : (term338 m n) = (term339 m n).
Proof. exact (MK_COMB (@lem243312) (@lem243311 m n)). Qed.
Lemma lem243314 (m : nat) (n : nat) : (term340 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem243313 m n) (@lem243308 m n)). Qed.
Lemma lem243315 (m : nat) (n : nat) : (((Nat.modulo m n) = m) = (term35 m n)) = (term340 m n).
Proof. exact (@lem17784 ((Nat.modulo m n) = m) (term35 m n)). Qed.
Lemma lem243316 (m : nat) (n : nat) : (((Nat.modulo m n) = m) = (term35 m n)) = (term341 m n).
Proof. exact (TRANS (@lem243315 m n) (@lem243314 m n)). Qed.
Lemma lem243317 (m : nat) : (term36 m) = (term342 m).
Proof. exact (fun_ext (fun n : nat => @lem243316 m n)). Qed.
Lemma lem243318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243319 (m : nat) : (term37 m) = (term343 m).
Proof. exact (MK_COMB (@lem243318) (@lem243317 m)). Qed.
Lemma lem243320 : term38 = term344.
Proof. exact (fun_ext (fun m : nat => @lem243319 m)). Qed.
Lemma lem243321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243322 : term39 = term345.
Proof. exact (MK_COMB (@lem243321) (@lem243320)). Qed.
Lemma lem243328 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem243329 (P : nat -> Prop) (Q : nat -> Prop) : (term288 P Q) = (term289 P Q).
Proof. exact (@lem243328 nat P Q). Qed.
Lemma lem243330 (m : nat) : (term346 m) = (term347 m).
Proof. exact (@lem243329 (term348 m) (term349 m)). Qed.
Lemma lem243331 (m : nat) (n : nat) : (term350 m n) = (term337 m n).
Proof. exact (eq_refl (term350 m n)). Qed.
Lemma lem243332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243333 (m : nat) (n : nat) : (term351 m n) = (term339 m n).
Proof. exact (MK_COMB (@lem243332) (@lem243331 m n)). Qed.
Lemma lem243334 (m : nat) (n : nat) : (term352 m n) = (term334 m n).
Proof. exact (eq_refl (term352 m n)). Qed.
Lemma lem243335 (m : nat) (n : nat) : (term353 m n) = (term341 m n).
Proof. exact (MK_COMB (@lem243333 m n) (@lem243334 m n)). Qed.
Lemma lem243336 (m : nat) : (term354 m) = (term342 m).
Proof. exact (fun_ext (fun n : nat => @lem243335 m n)). Qed.
Lemma lem243337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243338 (m : nat) : (term346 m) = (term343 m).
Proof. exact (MK_COMB (@lem243337) (@lem243336 m)). Qed.
Lemma lem243339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem243340 (m : nat) : (term355 m) = (term356 m).
Proof. exact (MK_COMB (@lem243339) (@lem243338 m)). Qed.
Lemma lem243341 (m : nat) (n : nat) : (term350 m n) = (term337 m n).
Proof. exact (eq_refl (term350 m n)). Qed.
Lemma lem243342 (m : nat) : (term357 m) = (term348 m).
Proof. exact (fun_ext (fun n : nat => @lem243341 m n)). Qed.
Lemma lem243343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243344 (m : nat) : (term358 m) = (term359 m).
Proof. exact (MK_COMB (@lem243343) (@lem243342 m)). Qed.
Lemma lem243345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243346 (m : nat) : (term360 m) = (term361 m).
Proof. exact (MK_COMB (@lem243345) (@lem243344 m)). Qed.
Lemma lem243347 (m : nat) (n : nat) : (term352 m n) = (term334 m n).
Proof. exact (eq_refl (term352 m n)). Qed.
Lemma lem243348 (m : nat) : (term362 m) = (term349 m).
Proof. exact (fun_ext (fun n : nat => @lem243347 m n)). Qed.
Lemma lem243349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243350 (m : nat) : (term363 m) = (term364 m).
Proof. exact (MK_COMB (@lem243349) (@lem243348 m)). Qed.
Lemma lem243351 (m : nat) : (term347 m) = (term365 m).
Proof. exact (MK_COMB (@lem243346 m) (@lem243350 m)). Qed.
Lemma lem243352 (m : nat) : ((term346 m) = (term347 m)) = ((term343 m) = (term365 m)).
Proof. exact (MK_COMB (@lem243340 m) (@lem243351 m)). Qed.
Lemma lem243353 (m : nat) : (term343 m) = (term365 m).
Proof. exact (EQ_MP (@lem243352 m) (@lem243330 m)). Qed.
Lemma lem243450 : term344 = term366.
Proof. exact (fun_ext (fun m : nat => @lem243353 m)). Qed.
Lemma lem243451 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243452 : term345 = term367.
Proof. exact (MK_COMB (@lem243451) (@lem243450)). Qed.
Lemma lem243454 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem243455 (P : nat -> Prop) (Q : nat -> Prop) : (term288 P Q) = (term289 P Q).
Proof. exact (@lem243454 nat P Q). Qed.
Lemma lem243456 : term368 = term369.
Proof. exact (@lem243455 term370 term371). Qed.
Lemma lem243457 (m : nat) : (term372 m) = (term359 m).
Proof. exact (eq_refl (term372 m)). Qed.
Lemma lem243458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243459 (m : nat) : (term373 m) = (term361 m).
Proof. exact (MK_COMB (@lem243458) (@lem243457 m)). Qed.
Lemma lem243460 (m : nat) : (term374 m) = (term364 m).
Proof. exact (eq_refl (term374 m)). Qed.
Lemma lem243461 (m : nat) : (term375 m) = (term365 m).
Proof. exact (MK_COMB (@lem243459 m) (@lem243460 m)). Qed.
Lemma lem243462 : term376 = term366.
Proof. exact (fun_ext (fun m : nat => @lem243461 m)). Qed.
Lemma lem243463 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243464 : term368 = term367.
Proof. exact (MK_COMB (@lem243463) (@lem243462)). Qed.
Lemma lem243465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem243466 : term377 = term378.
Proof. exact (MK_COMB (@lem243465) (@lem243464)). Qed.
Lemma lem243467 (m : nat) : (term372 m) = (term359 m).
Proof. exact (eq_refl (term372 m)). Qed.
Lemma lem243468 : term379 = term370.
Proof. exact (fun_ext (fun m : nat => @lem243467 m)). Qed.
Lemma lem243469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243470 : term380 = term381.
Proof. exact (MK_COMB (@lem243469) (@lem243468)). Qed.
Lemma lem243471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243472 : term382 = term383.
Proof. exact (MK_COMB (@lem243471) (@lem243470)). Qed.
Lemma lem243473 (m : nat) : (term374 m) = (term364 m).
Proof. exact (eq_refl (term374 m)). Qed.
Lemma lem243474 : term384 = term371.
Proof. exact (fun_ext (fun m : nat => @lem243473 m)). Qed.
Lemma lem243475 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243476 : term385 = term386.
Proof. exact (MK_COMB (@lem243475) (@lem243474)). Qed.
Lemma lem243477 : term369 = term387.
Proof. exact (MK_COMB (@lem243472) (@lem243476)). Qed.
Lemma lem243478 : (term368 = term369) = (term367 = term387).
Proof. exact (MK_COMB (@lem243466) (@lem243477)). Qed.
Lemma lem243479 : term367 = term387.
Proof. exact (EQ_MP (@lem243478) (@lem243456)). Qed.
Lemma lem243586 : term345 = term387.
Proof. exact (TRANS (@lem243452) (@lem243479)). Qed.
Lemma lem243587 : term39 = term387.
Proof. exact (TRANS (@lem243322) (@lem243586)). Qed.
Lemma lem243588 (h1 : term39) : term387.
Proof. exact (EQ_MP (@lem243587) (@lem242305 h1)). Qed.
Lemma lem243589 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem243590 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem243589 m)). Qed.
Lemma lem243591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243592 : term16 = term16.
Proof. exact (MK_COMB (@lem243591) (@lem243590)). Qed.
Lemma lem243603 (m : nat) (n : nat) : (term388 m n) = (term389 m n).
Proof. exact (@lem17160 (m = n) (Peano.lt m n)). Qed.
Lemma lem243609 (m : nat) (n : nat) : (term390 m n) = (term390 m n).
Proof. exact (eq_refl (term390 m n)). Qed.
Lemma lem243611 (m : nat) (n : nat) : (term391 m n) = (term391 m n).
Proof. exact (eq_refl (term391 m n)). Qed.
Lemma lem243612 (m : nat) (n : nat) : (term392 m n) = (term393 m n).
Proof. exact (MK_COMB (@lem243611 m n) (@lem243603 m n)). Qed.
Lemma lem243613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243614 (m : nat) (n : nat) : (term394 m n) = (term395 m n).
Proof. exact (MK_COMB (@lem243613) (@lem243612 m n)). Qed.
Lemma lem243615 (m : nat) (n : nat) : (term396 m n) = (term397 m n).
Proof. exact (MK_COMB (@lem243614 m n) (@lem243609 m n)). Qed.
Lemma lem243616 (m : nat) (n : nat) : ((term30 m n) = (term31 m n)) = (term396 m n).
Proof. exact (@lem17784 (term30 m n) (term31 m n)). Qed.
Lemma lem243617 (m : nat) (n : nat) : ((term30 m n) = (term31 m n)) = (term397 m n).
Proof. exact (TRANS (@lem243616 m n) (@lem243615 m n)). Qed.
Lemma lem243618 (m : nat) : (term32 m) = (term398 m).
Proof. exact (fun_ext (fun n : nat => @lem243617 m n)). Qed.
Lemma lem243619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243620 (m : nat) : (term33 m) = (term399 m).
Proof. exact (MK_COMB (@lem243619) (@lem243618 m)). Qed.
Lemma lem243621 : term34 = term400.
Proof. exact (fun_ext (fun m : nat => @lem243620 m)). Qed.
Lemma lem243622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243623 : term19 = term401.
Proof. exact (MK_COMB (@lem243622) (@lem243621)). Qed.
Lemma lem243624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243625 : term18 = term18.
Proof. exact (MK_COMB (@lem243624) (@lem243592)). Qed.
Lemma lem243626 : term20 = term402.
Proof. exact (MK_COMB (@lem243625) (@lem243623)). Qed.
Lemma lem243636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem243637 (P : nat -> Prop) (Q : nat -> Prop) : (term288 P Q) = (term289 P Q).
Proof. exact (@lem243636 nat P Q). Qed.
Lemma lem243638 (m : nat) : (term403 m) = (term404 m).
Proof. exact (@lem243637 (term405 m) (term406 m)). Qed.
Lemma lem243639 (m : nat) (n : nat) : (term407 m n) = (term393 m n).
Proof. exact (eq_refl (term407 m n)). Qed.
Lemma lem243640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243641 (m : nat) (n : nat) : (term408 m n) = (term395 m n).
Proof. exact (MK_COMB (@lem243640) (@lem243639 m n)). Qed.
Lemma lem243642 (m : nat) (n : nat) : (term409 m n) = (term390 m n).
Proof. exact (eq_refl (term409 m n)). Qed.
Lemma lem243643 (m : nat) (n : nat) : (term410 m n) = (term397 m n).
Proof. exact (MK_COMB (@lem243641 m n) (@lem243642 m n)). Qed.
Lemma lem243644 (m : nat) : (term411 m) = (term398 m).
Proof. exact (fun_ext (fun n : nat => @lem243643 m n)). Qed.
Lemma lem243645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243646 (m : nat) : (term403 m) = (term399 m).
Proof. exact (MK_COMB (@lem243645) (@lem243644 m)). Qed.
Lemma lem243647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem243648 (m : nat) : (term412 m) = (term413 m).
Proof. exact (MK_COMB (@lem243647) (@lem243646 m)). Qed.
Lemma lem243649 (m : nat) (n : nat) : (term407 m n) = (term393 m n).
Proof. exact (eq_refl (term407 m n)). Qed.
Lemma lem243650 (m : nat) : (term414 m) = (term405 m).
Proof. exact (fun_ext (fun n : nat => @lem243649 m n)). Qed.
Lemma lem243651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243652 (m : nat) : (term415 m) = (term416 m).
Proof. exact (MK_COMB (@lem243651) (@lem243650 m)). Qed.
Lemma lem243653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243654 (m : nat) : (term417 m) = (term418 m).
Proof. exact (MK_COMB (@lem243653) (@lem243652 m)). Qed.
Lemma lem243655 (m : nat) (n : nat) : (term409 m n) = (term390 m n).
Proof. exact (eq_refl (term409 m n)). Qed.
Lemma lem243656 (m : nat) : (term419 m) = (term406 m).
Proof. exact (fun_ext (fun n : nat => @lem243655 m n)). Qed.
Lemma lem243657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243658 (m : nat) : (term420 m) = (term421 m).
Proof. exact (MK_COMB (@lem243657) (@lem243656 m)). Qed.
Lemma lem243659 (m : nat) : (term404 m) = (term422 m).
Proof. exact (MK_COMB (@lem243654 m) (@lem243658 m)). Qed.
Lemma lem243660 (m : nat) : ((term403 m) = (term404 m)) = ((term399 m) = (term422 m)).
Proof. exact (MK_COMB (@lem243648 m) (@lem243659 m)). Qed.
Lemma lem243661 (m : nat) : (term399 m) = (term422 m).
Proof. exact (EQ_MP (@lem243660 m) (@lem243638 m)). Qed.
Lemma lem243758 : term400 = term423.
Proof. exact (fun_ext (fun m : nat => @lem243661 m)). Qed.
Lemma lem243759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243760 : term401 = term424.
Proof. exact (MK_COMB (@lem243759) (@lem243758)). Qed.
Lemma lem243762 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem243763 (P : nat -> Prop) (Q : nat -> Prop) : (term288 P Q) = (term289 P Q).
Proof. exact (@lem243762 nat P Q). Qed.
Lemma lem243764 : term425 = term426.
Proof. exact (@lem243763 term427 term428). Qed.
Lemma lem243765 (m : nat) : (term429 m) = (term416 m).
Proof. exact (eq_refl (term429 m)). Qed.
Lemma lem243766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243767 (m : nat) : (term430 m) = (term418 m).
Proof. exact (MK_COMB (@lem243766) (@lem243765 m)). Qed.
Lemma lem243768 (m : nat) : (term431 m) = (term421 m).
Proof. exact (eq_refl (term431 m)). Qed.
Lemma lem243769 (m : nat) : (term432 m) = (term422 m).
Proof. exact (MK_COMB (@lem243767 m) (@lem243768 m)). Qed.
Lemma lem243770 : term433 = term423.
Proof. exact (fun_ext (fun m : nat => @lem243769 m)). Qed.
Lemma lem243771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243772 : term425 = term424.
Proof. exact (MK_COMB (@lem243771) (@lem243770)). Qed.
Lemma lem243773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem243774 : term434 = term435.
Proof. exact (MK_COMB (@lem243773) (@lem243772)). Qed.
Lemma lem243775 (m : nat) : (term429 m) = (term416 m).
Proof. exact (eq_refl (term429 m)). Qed.
Lemma lem243776 : term436 = term427.
Proof. exact (fun_ext (fun m : nat => @lem243775 m)). Qed.
Lemma lem243777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243778 : term437 = term438.
Proof. exact (MK_COMB (@lem243777) (@lem243776)). Qed.
Lemma lem243779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243780 : term439 = term440.
Proof. exact (MK_COMB (@lem243779) (@lem243778)). Qed.
Lemma lem243781 (m : nat) : (term431 m) = (term421 m).
Proof. exact (eq_refl (term431 m)). Qed.
Lemma lem243782 : term441 = term428.
Proof. exact (fun_ext (fun m : nat => @lem243781 m)). Qed.
Lemma lem243783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243784 : term442 = term443.
Proof. exact (MK_COMB (@lem243783) (@lem243782)). Qed.
Lemma lem243785 : term426 = term444.
Proof. exact (MK_COMB (@lem243780) (@lem243784)). Qed.
Lemma lem243786 : (term425 = term426) = (term424 = term444).
Proof. exact (MK_COMB (@lem243774) (@lem243785)). Qed.
Lemma lem243787 : term424 = term444.
Proof. exact (EQ_MP (@lem243786) (@lem243764)). Qed.
Lemma lem243892 : term401 = term444.
Proof. exact (TRANS (@lem243760) (@lem243787)). Qed.
Lemma lem243893 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem243896 : term402 = term445.
Proof. exact (MK_COMB (@lem243893) (@lem243892)). Qed.
Lemma lem243897 : term20 = term445.
Proof. exact (TRANS (@lem243626) (@lem243896)). Qed.
Lemma lem243898 (h1 : term20) : term445.
Proof. exact (EQ_MP (@lem243897) (@lem242306 h1)). Qed.
Lemma lem243899 (P : nat -> Prop) (h1 : term271 P) : term271 P.
Proof. exact (h1). Qed.
Lemma lem243900 (P : nat -> Prop) (n : nat) (h1 : term269 P n) : term269 P n.
Proof. exact (h1). Qed.
Lemma lem243901 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term266 P a n) : term266 P a n.
Proof. exact (h1). Qed.
Lemma lem243924 (m : nat) (n : nat) : (term274 m n) = (term274 m n).
Proof. exact (eq_refl (term274 m n)). Qed.
Lemma lem243925 (m : nat) : (term293 m) = (term293 m).
Proof. exact (fun_ext (fun n : nat => @lem243924 m n)). Qed.
Lemma lem243926 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243927 (m : nat) : (term308 m) = (term308 m).
Proof. exact (MK_COMB (@lem243926) (@lem243925 m)). Qed.
Lemma lem243928 : term315 = term315.
Proof. exact (fun_ext (fun m : nat => @lem243927 m)). Qed.
Lemma lem243929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243930 : term330 = term330.
Proof. exact (MK_COMB (@lem243929) (@lem243928)). Qed.
Lemma lem243949 (m : nat) (n : nat) : (term277 m n) = (term277 m n).
Proof. exact (eq_refl (term277 m n)). Qed.
Lemma lem243950 (m : nat) : (term292 m) = (term292 m).
Proof. exact (fun_ext (fun n : nat => @lem243949 m n)). Qed.
Lemma lem243951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243952 (m : nat) : (term303 m) = (term303 m).
Proof. exact (MK_COMB (@lem243951) (@lem243950 m)). Qed.
Lemma lem243953 : term314 = term314.
Proof. exact (fun_ext (fun m : nat => @lem243952 m)). Qed.
Lemma lem243954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243955 : term325 = term325.
Proof. exact (MK_COMB (@lem243954) (@lem243953)). Qed.
Lemma lem243956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem243957 : term327 = term327.
Proof. exact (MK_COMB (@lem243956) (@lem243955)). Qed.
Lemma lem243958 : term331 = term331.
Proof. exact (MK_COMB (@lem243957) (@lem243930)). Qed.
Lemma lem243959 (h1 : term45) : term331.
Proof. exact (EQ_MP (@lem243958) (@lem243291 h1)). Qed.
Lemma lem243988 (m : nat) (n : nat) : (term334 m n) = (term334 m n).
Proof. exact (eq_refl (term334 m n)). Qed.
Lemma lem243989 (m : nat) : (term349 m) = (term349 m).
Proof. exact (fun_ext (fun n : nat => @lem243988 m n)). Qed.
Lemma lem243990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243991 (m : nat) : (term364 m) = (term364 m).
Proof. exact (MK_COMB (@lem243990) (@lem243989 m)). Qed.
Lemma lem243992 : term371 = term371.
Proof. exact (fun_ext (fun m : nat => @lem243991 m)). Qed.
Lemma lem243993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem243994 : term386 = term386.
Proof. exact (MK_COMB (@lem243993) (@lem243992)). Qed.
Lemma lem244025 (m : nat) (n : nat) : (term337 m n) = (term337 m n).
Proof. exact (eq_refl (term337 m n)). Qed.
Lemma lem244026 (m : nat) : (term348 m) = (term348 m).
Proof. exact (fun_ext (fun n : nat => @lem244025 m n)). Qed.
Lemma lem244027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244028 (m : nat) : (term359 m) = (term359 m).
Proof. exact (MK_COMB (@lem244027) (@lem244026 m)). Qed.
Lemma lem244029 : term370 = term370.
Proof. exact (fun_ext (fun m : nat => @lem244028 m)). Qed.
Lemma lem244030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244031 : term381 = term381.
Proof. exact (MK_COMB (@lem244030) (@lem244029)). Qed.
Lemma lem244032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem244033 : term383 = term383.
Proof. exact (MK_COMB (@lem244032) (@lem244031)). Qed.
Lemma lem244034 : term387 = term387.
Proof. exact (MK_COMB (@lem244033) (@lem243994)). Qed.
Lemma lem244035 (h1 : term39) : term387.
Proof. exact (EQ_MP (@lem244034) (@lem243588 h1)). Qed.
Lemma lem244060 (m : nat) (n : nat) : (term390 m n) = (term390 m n).
Proof. exact (eq_refl (term390 m n)). Qed.
Lemma lem244061 (m : nat) : (term406 m) = (term406 m).
Proof. exact (fun_ext (fun n : nat => @lem244060 m n)). Qed.
Lemma lem244062 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244063 (m : nat) : (term421 m) = (term421 m).
Proof. exact (MK_COMB (@lem244062) (@lem244061 m)). Qed.
Lemma lem244064 : term428 = term428.
Proof. exact (fun_ext (fun m : nat => @lem244063 m)). Qed.
Lemma lem244065 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244066 : term443 = term443.
Proof. exact (MK_COMB (@lem244065) (@lem244064)). Qed.
Lemma lem244093 (m : nat) (n : nat) : (term393 m n) = (term393 m n).
Proof. exact (eq_refl (term393 m n)). Qed.
Lemma lem244094 (m : nat) : (term405 m) = (term405 m).
Proof. exact (fun_ext (fun n : nat => @lem244093 m n)). Qed.
Lemma lem244095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244096 (m : nat) : (term416 m) = (term416 m).
Proof. exact (MK_COMB (@lem244095) (@lem244094 m)). Qed.
Lemma lem244097 : term427 = term427.
Proof. exact (fun_ext (fun m : nat => @lem244096 m)). Qed.
Lemma lem244098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244099 : term438 = term438.
Proof. exact (MK_COMB (@lem244098) (@lem244097)). Qed.
Lemma lem244100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem244101 : term440 = term440.
Proof. exact (MK_COMB (@lem244100) (@lem244099)). Qed.
Lemma lem244102 : term444 = term444.
Proof. exact (MK_COMB (@lem244101) (@lem244066)). Qed.
Lemma lem244111 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem244112 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem244111 m)). Qed.
Lemma lem244113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244114 : term16 = term16.
Proof. exact (MK_COMB (@lem244113) (@lem244112)). Qed.
Lemma lem244115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem244116 : term18 = term18.
Proof. exact (MK_COMB (@lem244115) (@lem244114)). Qed.
Lemma lem244117 : term445 = term445.
Proof. exact (MK_COMB (@lem244116) (@lem244102)). Qed.
Lemma lem244118 (h1 : term20) : term445.
Proof. exact (EQ_MP (@lem244117) (@lem243898 h1)). Qed.
Lemma lem244137 (P : nat -> Prop) (a : nat) (n : nat) : (term194 P a n) = (term194 P a n).
Proof. exact (eq_refl (term194 P a n)). Qed.
Lemma lem244152 (n : nat) (P : nat -> Prop) (a : nat) : (term59 n P a) = (term59 n P a).
Proof. exact (eq_refl (term59 n P a)). Qed.
Lemma lem244153 (n : nat) (P : nat -> Prop) : (term67 n P) = (term67 n P).
Proof. exact (fun_ext (fun a : nat => @lem244152 n P a)). Qed.
Lemma lem244154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244155 (n : nat) (P : nat -> Prop) : (term68 n P) = (term68 n P).
Proof. exact (MK_COMB (@lem244154) (@lem244153 n P)). Qed.
Lemma lem244156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem244157 (n : nat) (P : nat -> Prop) : (term84 n P) = (term84 n P).
Proof. exact (MK_COMB (@lem244156) (@lem244155 n P)). Qed.
Lemma lem244158 (P : nat -> Prop) (a : nat) (n : nat) : (term207 P a n) = (term207 P a n).
Proof. exact (MK_COMB (@lem244157 n P) (@lem244137 P a n)). Qed.
Lemma lem244167 (P : nat -> Prop) (a : nat) (n : nat) : (term74 P a n) = (term74 P a n).
Proof. exact (eq_refl (term74 P a n)). Qed.
Lemma lem244168 (P : nat -> Prop) (n : nat) : (term76 P n) = (term76 P n).
Proof. exact (fun_ext (fun a : nat => @lem244167 P a n)). Qed.
Lemma lem244169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244170 (P : nat -> Prop) (n : nat) : (term77 P n) = (term77 P n).
Proof. exact (MK_COMB (@lem244169) (@lem244168 P n)). Qed.
Lemma lem244179 (n : nat) : (term79 n) = (term79 n).
Proof. exact (eq_refl (term79 n)). Qed.
Lemma lem244180 (P : nat -> Prop) (n : nat) : (term81 P n) = (term81 P n).
Proof. exact (MK_COMB (@lem244179 n) (@lem244170 P n)). Qed.
Lemma lem244193 (n : nat) (P : nat -> Prop) (a : nat) : (term172 n P a) = (term172 n P a).
Proof. exact (eq_refl (term172 n P a)). Qed.
Lemma lem244194 (a : nat) (P : nat -> Prop) (n : nat) : (term174 a P n) = (term174 a P n).
Proof. exact (MK_COMB (@lem244193 n P a) (@lem244180 P n)). Qed.
Lemma lem244195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem244196 (a : nat) (P : nat -> Prop) (n : nat) : (term264 a P n) = (term264 a P n).
Proof. exact (MK_COMB (@lem244195) (@lem244194 a P n)). Qed.
Lemma lem244197 (P : nat -> Prop) (a : nat) (n : nat) : (term266 P a n) = (term266 P a n).
Proof. exact (MK_COMB (@lem244196 a P n) (@lem244158 P a n)). Qed.
Lemma lem244198 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term266 P a n) : term266 P a n.
Proof. exact (EQ_MP (@lem244197 P a n) (@lem243901 P a n h1)). Qed.
Lemma lem244200 (h1 : term20) : term16.
Proof. exact (proj1 (@lem244118 h1)). Qed.
Lemma lem244204 (h1 : term39) : term381.
Proof. exact (proj1 (@lem244035 h1)). Qed.
Lemma lem244206 (h1 : term45) : term325.
Proof. exact (proj1 (@lem243959 h1)). Qed.
Lemma lem244207 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : term174 a P n.
Proof. exact (h1). Qed.
Lemma lem244208 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term207 P a n.
Proof. exact (h1). Qed.
Lemma lem244209 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : term81 P n.
Proof. exact (proj2 (@lem244207 a P n h1)). Qed.
Lemma lem244210 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : term51 n P a.
Proof. exact (proj1 (@lem244207 a P n h1)). Qed.
Lemma lem244214 (P : nat -> Prop) (n : nat) (h1 : term77 P n) : term77 P n.
Proof. exact (h1). Qed.
Lemma lem244215 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term194 P a n.
Proof. exact (proj2 (@lem244208 P a n h1)). Qed.
Lemma lem244216 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term68 n P.
Proof. exact (proj1 (@lem244208 P a n h1)). Qed.
Lemma lem244220 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem244221 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem244220 m)). Qed.
Lemma lem244222 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244224 : term16 = term16.
Proof. exact (MK_COMB (@lem244222) (@lem244221)). Qed.
Lemma lem244225 (h1 : term20) : term16.
Proof. exact (EQ_MP (@lem244224) (@lem244200 h1)). Qed.
Lemma lem244365 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem244438 (m : nat) (n : nat) : (term337 m n) = (term446 m n).
Proof. exact (@lem19490 (term41 n) ((Nat.modulo m n) = m) (term447 m n)). Qed.
Lemma lem244439 (m : nat) : (term348 m) = (term448 m).
Proof. exact (fun_ext (fun n : nat => @lem244438 m n)). Qed.
Lemma lem244440 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244441 (m : nat) : (term359 m) = (term449 m).
Proof. exact (MK_COMB (@lem244440) (@lem244439 m)). Qed.
Lemma lem244442 : term370 = term450.
Proof. exact (fun_ext (fun m : nat => @lem244441 m)). Qed.
Lemma lem244443 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244445 : term381 = term451.
Proof. exact (MK_COMB (@lem244443) (@lem244442)). Qed.
Lemma lem244446 (h1 : term39) : term451.
Proof. exact (EQ_MP (@lem244445) (@lem244204 h1)). Qed.
Lemma lem244510 (P : nat -> Prop) (a : nat) (n : nat) : (term74 P a n) = (term74 P a n).
Proof. exact (eq_refl (term74 P a n)). Qed.
Lemma lem244511 (P : nat -> Prop) (n : nat) : (term76 P n) = (term76 P n).
Proof. exact (fun_ext (fun a : nat => @lem244510 P a n)). Qed.
Lemma lem244512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244514 (P : nat -> Prop) (n : nat) : (term77 P n) = (term77 P n).
Proof. exact (MK_COMB (@lem244512) (@lem244511 P n)). Qed.
Lemma lem244515 (P : nat -> Prop) (n : nat) (h1 : term77 P n) : term77 P n.
Proof. exact (EQ_MP (@lem244514 P n) (@lem244214 P n h1)). Qed.
Lemma lem244626 (m : nat) (n : nat) : (term277 m n) = (term277 m n).
Proof. exact (eq_refl (term277 m n)). Qed.
Lemma lem244627 (m : nat) : (term292 m) = (term292 m).
Proof. exact (fun_ext (fun n : nat => @lem244626 m n)). Qed.
Lemma lem244628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244629 (m : nat) : (term303 m) = (term303 m).
Proof. exact (MK_COMB (@lem244628) (@lem244627 m)). Qed.
Lemma lem244630 : term314 = term314.
Proof. exact (fun_ext (fun m : nat => @lem244629 m)). Qed.
Lemma lem244631 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244633 : term325 = term325.
Proof. exact (MK_COMB (@lem244631) (@lem244630)). Qed.
Lemma lem244634 (h1 : term45) : term325.
Proof. exact (EQ_MP (@lem244633) (@lem244206 h1)). Qed.
Lemma lem244658 (n : nat) (P : nat -> Prop) (a : nat) : (term59 n P a) = (term59 n P a).
Proof. exact (eq_refl (term59 n P a)). Qed.
Lemma lem244659 (n : nat) (P : nat -> Prop) : (term67 n P) = (term67 n P).
Proof. exact (fun_ext (fun a : nat => @lem244658 n P a)). Qed.
Lemma lem244660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem244662 (n : nat) (P : nat -> Prop) : (term68 n P) = (term68 n P).
Proof. exact (MK_COMB (@lem244660) (@lem244659 n P)). Qed.
Lemma lem244663 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term68 n P.
Proof. exact (EQ_MP (@lem244662 n P) (@lem244216 P a n h1)). Qed.
Lemma lem244672 (_4765 : nat) (h1 : term20) : term452 _4765.
Proof. exact (@lem244225 h1 _4765). Qed.
Lemma lem244673 (_4765 : nat) : (term452 _4765) = (term12 _4765).
Proof. exact (eq_refl (term452 _4765)). Qed.
Lemma lem244726 (_4783 : nat) (h1 : term39) : term453 _4783.
Proof. exact (@lem244446 h1 _4783). Qed.
Lemma lem244727 (_4783 : nat) : (term453 _4783) = (term449 _4783).
Proof. exact (eq_refl (term453 _4783)). Qed.
Lemma lem244728 (_4783 : nat) (h1 : term39) : term449 _4783.
Proof. exact (EQ_MP (@lem244727 _4783) (@lem244726 _4783 h1)). Qed.
Lemma lem244729 (_4783 : nat) (_4784 : nat) (h1 : term39) : term454 _4783 _4784.
Proof. exact (@lem244728 _4783 h1 _4784). Qed.
Lemma lem244730 (_4783 : nat) (_4784 : nat) : (term454 _4783 _4784) = (term446 _4783 _4784).
Proof. exact (eq_refl (term454 _4783 _4784)). Qed.
Lemma lem244731 (_4783 : nat) (_4784 : nat) (h1 : term39) : term446 _4783 _4784.
Proof. exact (EQ_MP (@lem244730 _4783 _4784) (@lem244729 _4783 _4784 h1)). Qed.
Lemma lem244750 (_4791 : nat) (P : nat -> Prop) (n : nat) (h1 : term77 P n) : term455 P n _4791.
Proof. exact (@lem244515 P n h1 _4791). Qed.
Lemma lem244751 (P : nat -> Prop) (_4791 : nat) (n : nat) : (term455 P n _4791) = (term74 P _4791 n).
Proof. exact (eq_refl (term455 P n _4791)). Qed.
Lemma lem244780 (_4801 : nat) (h1 : term45) : term316 _4801.
Proof. exact (@lem244634 h1 _4801). Qed.
Lemma lem244781 (_4801 : nat) : (term316 _4801) = (term303 _4801).
Proof. exact (eq_refl (term316 _4801)). Qed.
Lemma lem244782 (_4801 : nat) (h1 : term45) : term303 _4801.
Proof. exact (EQ_MP (@lem244781 _4801) (@lem244780 _4801 h1)). Qed.
Lemma lem244783 (_4801 : nat) (_4802 : nat) (h1 : term45) : term294 _4801 _4802.
Proof. exact (@lem244782 _4801 h1 _4802). Qed.
Lemma lem244784 (_4801 : nat) (_4802 : nat) : (term294 _4801 _4802) = (term277 _4801 _4802).
Proof. exact (eq_refl (term294 _4801 _4802)). Qed.
Lemma lem244792 (_4805 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term456 n P _4805.
Proof. exact (@lem244663 P a n h1 _4805). Qed.
Lemma lem244793 (n : nat) (P : nat -> Prop) (_4805 : nat) : (term456 n P _4805) = (term59 n P _4805).
Proof. exact (eq_refl (term456 n P _4805)). Qed.
Lemma lem244842 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : Peano.lt a n.
Proof. exact (proj1 (@lem244210 a P n h1)). Qed.
Lemma lem244846 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem244910 (_4791 : nat) (P : nat -> Prop) (n : nat) (h1 : term77 P n) : term74 P _4791 n.
Proof. exact (EQ_MP (@lem244751 P _4791 n) (@lem244750 _4791 P n h1)). Qed.
Lemma lem244922 (_4783 : nat) (_4784 : nat) (h1 : term39) : term457 _4783 _4784.
Proof. exact (proj2 (@lem244731 _4783 _4784 h1)). Qed.
Lemma lem244962 (_4801 : nat) (_4802 : nat) (h1 : term45) : term277 _4801 _4802.
Proof. exact (EQ_MP (@lem244784 _4801 _4802) (@lem244783 _4801 _4802 h1)). Qed.
Lemma lem244974 (_4805 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term59 n P _4805.
Proof. exact (EQ_MP (@lem244793 n P _4805) (@lem244792 _4805 P a n h1)). Qed.
Lemma lem244976 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term41 n.
Proof. exact (proj1 (@lem244215 P a n h1)). Qed.
Lemma lem245030 (_4765 : nat) (h1 : term20) : term12 _4765.
Proof. exact (EQ_MP (@lem244673 _4765) (@lem244672 _4765 h1)). Qed.
Lemma lem245087 (a : nat) : (term458 a) = (term458 a).
Proof. exact (eq_refl (term458 a)). Qed.
Lemma lem245088 (a : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term459 a n) = (term460 a).
Proof. exact (MK_COMB (@lem245087 a) (@lem244846 n h1)). Qed.
Lemma lem245089 (a : nat) : (term460 a) = (term11 a).
Proof. exact (eq_refl (term460 a)). Qed.
Lemma lem245090 (a : nat) (n : nat) : (term461 a n) = (term461 a n).
Proof. exact (eq_refl (term461 a n)). Qed.
Lemma lem245091 (n : nat) (a : nat) : ((term459 a n) = (term460 a)) = ((term459 a n) = (term11 a)).
Proof. exact (MK_COMB (@lem245090 a n) (@lem245089 a)). Qed.
Lemma lem245092 (a : nat) (n : nat) : (term459 a n) = (Peano.lt a n).
Proof. exact (eq_refl (term459 a n)). Qed.
Lemma lem245093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem245094 (a : nat) (n : nat) : (term461 a n) = (term462 a n).
Proof. exact (MK_COMB (@lem245093) (@lem245092 a n)). Qed.
Lemma lem245095 (a : nat) : (term11 a) = (term11 a).
Proof. exact (eq_refl (term11 a)). Qed.
Lemma lem245096 (n : nat) (a : nat) : ((term459 a n) = (term11 a)) = ((Peano.lt a n) = (term11 a)).
Proof. exact (MK_COMB (@lem245094 a n) (@lem245095 a)). Qed.
Lemma lem245097 (n : nat) (a : nat) : ((term459 a n) = (term460 a)) = ((Peano.lt a n) = (term11 a)).
Proof. exact (TRANS (@lem245091 n a) (@lem245096 n a)). Qed.
Lemma lem245098 (a : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt a n) = (term11 a).
Proof. exact (EQ_MP (@lem245097 n a) (@lem245088 a n h1)). Qed.
Lemma lem245235 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) (h2 : n = (NUMERAL 0)) : term11 a.
Proof. exact (EQ_MP (@lem245098 a n h2) (@lem244842 a P n h1)). Qed.
Lemma lem245236 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) (h2 : n = (NUMERAL 0)) : term463 a.
Proof. exact (fun h0 : term12 a => @lem245235 a P n h1 h2). Qed.
Lemma lem245238 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245239 (a : nat) : (term463 a) = (term11 a).
Proof. exact (@lem245238 (term11 a)). Qed.
Lemma lem245240 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) (h2 : n = (NUMERAL 0)) : term11 a.
Proof. exact (EQ_MP (@lem245239 a) (@lem245236 a P n h1 h2)). Qed.
Lemma lem245243 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem245245 (_4765 : nat) : (term12 _4765) = (term465 _4765).
Proof. exact (@lem245243 (term11 _4765)). Qed.
Lemma lem245248 (_4765 : nat) (h1 : term20) : term465 _4765.
Proof. exact (EQ_MP (@lem245245 _4765) (@lem245030 _4765 h1)). Qed.
Lemma lem245249 (a : nat) (h1 : term20) : term465 a.
Proof. exact (@lem245248 a h1). Qed.
Lemma lem245252 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (@lem245249 a h1 (@lem245240 a P n h2 h3)). Qed.
Lemma lem245253 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : term466.
Proof. exact (fun h0 : ~ False => @lem245252 a P n h1 h2 h3). Qed.
Lemma lem245255 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245256 : term466 = False.
Proof. exact (@lem245255 False). Qed.
Lemma lem245258 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem245259 (_4844 : nat) (_4845 : nat) (h1 : _4844 = _4845) : _4844 = _4845.
Proof. exact (h1). Qed.
Lemma lem245260 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) (h1 : _4844 = _4845) : (P _4844) = (P _4845).
Proof. exact (MK_COMB (@lem245258 P) (@lem245259 _4844 _4845 h1)). Qed.
Lemma lem245262 (b : Prop) (a : Prop) : term467 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem245263 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : term468 _4845 P _4844.
Proof. exact (@lem245262 (P _4845) (P _4844)). Qed.
Lemma lem245264 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) (h1 : _4844 = _4845) : term469 _4845 P _4844.
Proof. exact (@lem245263 _4845 P _4844 (@lem245260 P _4844 _4845 h1)). Qed.
Lemma lem245265 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : term470 _4845 P _4844.
Proof. exact (fun h0 : _4844 = _4845 => @lem245264 P _4844 _4845 h0). Qed.
Lemma lem245267 (a : Prop) (b : Prop) : (a -> b) = (term471 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem245268 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : (term470 _4845 P _4844) = (term472 _4845 P _4844).
Proof. exact (@lem245267 (_4844 = _4845) (term469 _4845 P _4844)). Qed.
Lemma lem245269 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : term472 _4845 P _4844.
Proof. exact (EQ_MP (@lem245268 _4845 P _4844) (@lem245265 _4845 P _4844)). Qed.
Lemma lem245321 (x : nat) (y : nat) (z : nat) : term473 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem245323 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : Peano.lt a n.
Proof. exact (proj1 (@lem244210 a P n h1)). Qed.
Lemma lem245324 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : term474 a n.
Proof. exact (fun h0 : term447 a n => @lem245323 a P n h1). Qed.
Lemma lem245326 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245327 (a : nat) (n : nat) : (term474 a n) = (Peano.lt a n).
Proof. exact (@lem245326 (Peano.lt a n)). Qed.
Lemma lem245328 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : Peano.lt a n.
Proof. exact (EQ_MP (@lem245327 a n) (@lem245324 a P n h1)). Qed.
Lemma lem245330 (b : Prop) (a : Prop) : (a \/ b) = (term475 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem245331 (_4784 : nat) (_4783 : nat) : (term457 _4783 _4784) = (term476 _4784 _4783).
Proof. exact (@lem245330 (term447 _4783 _4784) ((Nat.modulo _4783 _4784) = _4783)). Qed.
Lemma lem245333 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem245334 (_4783 : nat) (_4784 : nat) : (term478 _4783 _4784) = (Peano.lt _4783 _4784).
Proof. exact (@lem245333 (Peano.lt _4783 _4784)). Qed.
Lemma lem245335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem245336 (_4783 : nat) (_4784 : nat) : (term479 _4783 _4784) = (term480 _4783 _4784).
Proof. exact (MK_COMB (@lem245335) (@lem245334 _4783 _4784)). Qed.
Lemma lem245337 (_4784 : nat) (_4783 : nat) : ((Nat.modulo _4783 _4784) = _4783) = ((Nat.modulo _4783 _4784) = _4783).
Proof. exact (eq_refl ((Nat.modulo _4783 _4784) = _4783)). Qed.
Lemma lem245338 (_4784 : nat) (_4783 : nat) : (term476 _4784 _4783) = (term481 _4784 _4783).
Proof. exact (MK_COMB (@lem245336 _4783 _4784) (@lem245337 _4784 _4783)). Qed.
Lemma lem245339 (_4784 : nat) (_4783 : nat) : (term457 _4783 _4784) = (term481 _4784 _4783).
Proof. exact (TRANS (@lem245331 _4784 _4783) (@lem245338 _4784 _4783)). Qed.
Lemma lem245342 (_4784 : nat) (_4783 : nat) (h1 : term39) : term481 _4784 _4783.
Proof. exact (EQ_MP (@lem245339 _4784 _4783) (@lem244922 _4783 _4784 h1)). Qed.
Lemma lem245343 (n : nat) (a : nat) (h1 : term39) : term481 n a.
Proof. exact (@lem245342 n a h1). Qed.
Lemma lem245346 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : (Nat.modulo a n) = a.
Proof. exact (@lem245343 n a h1 (@lem245328 a P n h2)). Qed.
Lemma lem245347 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : term482 n a.
Proof. exact (fun h0 : term483 n a => @lem245346 a P n h1 h2). Qed.
Lemma lem245349 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245350 (n : nat) (a : nat) : (term482 n a) = ((Nat.modulo a n) = a).
Proof. exact (@lem245349 ((Nat.modulo a n) = a)). Qed.
Lemma lem245351 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : (Nat.modulo a n) = a.
Proof. exact (EQ_MP (@lem245350 n a) (@lem245347 a P n h1 h2)). Qed.
Lemma lem245353 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem245354 (a : nat) (n : nat) : (Nat.modulo a n) = (Nat.modulo a n).
Proof. exact (@lem245353 (Nat.modulo a n)). Qed.
Lemma lem245355 (a : nat) (n : nat) : term484 a n.
Proof. exact (fun h0 : term485 a n => @lem245354 a n). Qed.
Lemma lem245357 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245358 (a : nat) (n : nat) : (term484 a n) = ((Nat.modulo a n) = (Nat.modulo a n)).
Proof. exact (@lem245357 ((Nat.modulo a n) = (Nat.modulo a n))). Qed.
Lemma lem245359 (a : nat) (n : nat) : (Nat.modulo a n) = (Nat.modulo a n).
Proof. exact (EQ_MP (@lem245358 a n) (@lem245355 a n)). Qed.
Lemma lem245377 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem245378 (y : nat) (x : nat) (z : nat) : (term486 x y z) = (term487 y x z).
Proof. exact (@lem245377 (y = z) (term488 x z)). Qed.
Lemma lem245388 (x : nat) (y : nat) : (term489 x y) = (term489 x y).
Proof. exact (eq_refl (term489 x y)). Qed.
Lemma lem245389 (y : nat) (x : nat) (z : nat) : (term473 x y z) = (term490 y x z).
Proof. exact (MK_COMB (@lem245388 x y) (@lem245378 y x z)). Qed.
Lemma lem245393 (q : Prop) (p : Prop) (r : Prop) : (term491 p q r) = (term491 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem245394 (y : nat) (x : nat) (z : nat) : (term490 y x z) = (term492 y x z).
Proof. exact (@lem245393 (y = z) (term488 x y) (term488 x z)). Qed.
Lemma lem245416 (y : nat) (x : nat) (z : nat) : (term473 x y z) = (term492 y x z).
Proof. exact (TRANS (@lem245389 y x z) (@lem245394 y x z)). Qed.
Lemma lem245417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem245418 (y : nat) (x : nat) (z : nat) : (term493 x y z) = (term494 y x z).
Proof. exact (MK_COMB (@lem245417) (@lem245416 y x z)). Qed.
Lemma lem245440 (y : nat) (x : nat) (z : nat) : (term492 y x z) = (term492 y x z).
Proof. exact (eq_refl (term492 y x z)). Qed.
Lemma lem245441 (y : nat) (x : nat) (z : nat) : ((term473 x y z) = (term492 y x z)) = ((term492 y x z) = (term492 y x z)).
Proof. exact (MK_COMB (@lem245418 y x z) (@lem245440 y x z)). Qed.
Lemma lem245443 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem245444 (x : Prop) : (x = x) = True.
Proof. exact (@lem245443 Prop x). Qed.
Lemma lem245445 (y : nat) (x : nat) (z : nat) : ((term492 y x z) = (term492 y x z)) = True.
Proof. exact (@lem245444 (term492 y x z)). Qed.
Lemma lem245446 (y : nat) (x : nat) (z : nat) : ((term473 x y z) = (term492 y x z)) = True.
Proof. exact (TRANS (@lem245441 y x z) (@lem245445 y x z)). Qed.
Lemma lem245447 (y : nat) (x : nat) (z : nat) : True = ((term473 x y z) = (term492 y x z)).
Proof. exact (SYM (@lem245446 y x z)). Qed.
Lemma lem245448 (y : nat) (x : nat) (z : nat) : (term473 x y z) = (term492 y x z).
Proof. exact (EQ_MP (@lem245447 y x z) (@lem0)). Qed.
Lemma lem245449 (y : nat) (x : nat) (z : nat) : term492 y x z.
Proof. exact (EQ_MP (@lem245448 y x z) (@lem245321 x y z)). Qed.
Lemma lem245451 (b : Prop) (a : Prop) : (a \/ b) = (term475 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem245452 (x : nat) (y : nat) (z : nat) : (term492 y x z) = (term495 x y z).
Proof. exact (@lem245451 (term496 y x z) (y = z)). Qed.
Lemma lem245454 (a : Prop) (b : Prop) : (term497 a b) = (term498 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem245455 (y : nat) (x : nat) (z : nat) : (term499 y x z) = (term500 y x z).
Proof. exact (@lem245454 (term488 x y) (term488 x z)). Qed.
Lemma lem245457 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem245458 (x : nat) (y : nat) : (term501 x y) = (x = y).
Proof. exact (@lem245457 (x = y)). Qed.
Lemma lem245459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem245460 (x : nat) (y : nat) : (term502 x y) = (term503 x y).
Proof. exact (MK_COMB (@lem245459) (@lem245458 x y)). Qed.
Lemma lem245462 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem245463 (x : nat) (z : nat) : (term501 x z) = (x = z).
Proof. exact (@lem245462 (x = z)). Qed.
Lemma lem245464 (y : nat) (x : nat) (z : nat) : (term500 y x z) = (term504 y x z).
Proof. exact (MK_COMB (@lem245460 x y) (@lem245463 x z)). Qed.
Lemma lem245465 (y : nat) (x : nat) (z : nat) : (term499 y x z) = (term504 y x z).
Proof. exact (TRANS (@lem245455 y x z) (@lem245464 y x z)). Qed.
Lemma lem245466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem245467 (y : nat) (x : nat) (z : nat) : (term505 y x z) = (term506 y x z).
Proof. exact (MK_COMB (@lem245466) (@lem245465 y x z)). Qed.
Lemma lem245468 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem245469 (x : nat) (y : nat) (z : nat) : (term495 x y z) = (term507 x y z).
Proof. exact (MK_COMB (@lem245467 y x z) (@lem245468 y z)). Qed.
Lemma lem245470 (x : nat) (y : nat) (z : nat) : (term492 y x z) = (term507 x y z).
Proof. exact (TRANS (@lem245452 x y z) (@lem245469 x y z)). Qed.
Lemma lem245472 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : term508 a n.
Proof. exact (conj (@lem245351 a P n h1 h2) (@lem245359 a n)). Qed.
Lemma lem245474 (x : nat) (y : nat) (z : nat) : term507 x y z.
Proof. exact (EQ_MP (@lem245470 x y z) (@lem245449 y x z)). Qed.
Lemma lem245475 (a : nat) (n : nat) : term509 a n.
Proof. exact (@lem245474 (Nat.modulo a n) a (Nat.modulo a n)). Qed.
Lemma lem245478 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : a = (Nat.modulo a n).
Proof. exact (@lem245475 a n (@lem245472 a P n h1 h2)). Qed.
Lemma lem245479 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : term510 a n.
Proof. exact (fun h0 : term511 a n => @lem245478 a P n h1 h2). Qed.
Lemma lem245481 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245482 (a : nat) (n : nat) : (term510 a n) = (a = (Nat.modulo a n)).
Proof. exact (@lem245481 (a = (Nat.modulo a n))). Qed.
Lemma lem245483 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : a = (Nat.modulo a n).
Proof. exact (EQ_MP (@lem245482 a n) (@lem245479 a P n h1 h2)). Qed.
Lemma lem245485 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : P a.
Proof. exact (proj2 (@lem244210 a P n h1)). Qed.
Lemma lem245486 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : term512 P a.
Proof. exact (fun h0 : term513 P a => @lem245485 a P n h1). Qed.
Lemma lem245488 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245489 (P : nat -> Prop) (a : nat) : (term512 P a) = (P a).
Proof. exact (@lem245488 (P a)). Qed.
Lemma lem245490 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term174 a P n) : P a.
Proof. exact (EQ_MP (@lem245489 P a) (@lem245486 a P n h1)). Qed.
Lemma lem245496 (q : Prop) (p : Prop) (r : Prop) : (term491 p q r) = (term491 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem245497 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : (term472 _4845 P _4844) = (term514 _4845 P _4844).
Proof. exact (@lem245496 (P _4845) (term488 _4844 _4845) (term513 P _4844)). Qed.
Lemma lem245511 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem245512 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : (term515 _4845 P _4844) = (term516 P _4844 _4845).
Proof. exact (@lem245511 (term513 P _4844) (term488 _4844 _4845)). Qed.
Lemma lem245520 (P : nat -> Prop) (_4845 : nat) : (term517 P _4845) = (term517 P _4845).
Proof. exact (eq_refl (term517 P _4845)). Qed.
Lemma lem245521 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : (term514 _4845 P _4844) = (term518 P _4844 _4845).
Proof. exact (MK_COMB (@lem245520 P _4845) (@lem245512 P _4844 _4845)). Qed.
Lemma lem245532 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : (term472 _4845 P _4844) = (term518 P _4844 _4845).
Proof. exact (TRANS (@lem245497 _4845 P _4844) (@lem245521 P _4844 _4845)). Qed.
Lemma lem245533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem245534 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : (term519 _4845 P _4844) = (term520 P _4844 _4845).
Proof. exact (MK_COMB (@lem245533) (@lem245532 P _4844 _4845)). Qed.
Lemma lem245548 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem245549 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : (term515 _4845 P _4844) = (term516 P _4844 _4845).
Proof. exact (@lem245548 (term513 P _4844) (term488 _4844 _4845)). Qed.
Lemma lem245557 (P : nat -> Prop) (_4845 : nat) : (term517 P _4845) = (term517 P _4845).
Proof. exact (eq_refl (term517 P _4845)). Qed.
Lemma lem245558 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : (term514 _4845 P _4844) = (term518 P _4844 _4845).
Proof. exact (MK_COMB (@lem245557 P _4845) (@lem245549 P _4844 _4845)). Qed.
Lemma lem245569 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : ((term472 _4845 P _4844) = (term514 _4845 P _4844)) = ((term518 P _4844 _4845) = (term518 P _4844 _4845)).
Proof. exact (MK_COMB (@lem245534 P _4844 _4845) (@lem245558 P _4844 _4845)). Qed.
Lemma lem245571 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem245572 (x : Prop) : (x = x) = True.
Proof. exact (@lem245571 Prop x). Qed.
Lemma lem245573 (P : nat -> Prop) (_4844 : nat) (_4845 : nat) : ((term518 P _4844 _4845) = (term518 P _4844 _4845)) = True.
Proof. exact (@lem245572 (term518 P _4844 _4845)). Qed.
Lemma lem245574 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : ((term472 _4845 P _4844) = (term514 _4845 P _4844)) = True.
Proof. exact (TRANS (@lem245569 P _4844 _4845) (@lem245573 P _4844 _4845)). Qed.
Lemma lem245575 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : True = ((term472 _4845 P _4844) = (term514 _4845 P _4844)).
Proof. exact (SYM (@lem245574 _4845 P _4844)). Qed.
Lemma lem245576 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : (term472 _4845 P _4844) = (term514 _4845 P _4844).
Proof. exact (EQ_MP (@lem245575 _4845 P _4844) (@lem0)). Qed.
Lemma lem245577 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : term514 _4845 P _4844.
Proof. exact (EQ_MP (@lem245576 _4845 P _4844) (@lem245269 _4845 P _4844)). Qed.
Lemma lem245579 (b : Prop) (a : Prop) : (a \/ b) = (term475 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem245580 (_4844 : nat) (P : nat -> Prop) (_4845 : nat) : (term514 _4845 P _4844) = (term521 _4844 P _4845).
Proof. exact (@lem245579 (term515 _4845 P _4844) (P _4845)). Qed.
Lemma lem245582 (a : Prop) (b : Prop) : (term497 a b) = (term498 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem245583 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : (term522 _4845 P _4844) = (term523 _4845 P _4844).
Proof. exact (@lem245582 (term488 _4844 _4845) (term513 P _4844)). Qed.
Lemma lem245585 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem245586 (_4844 : nat) (_4845 : nat) : (term501 _4844 _4845) = (_4844 = _4845).
Proof. exact (@lem245585 (_4844 = _4845)). Qed.
Lemma lem245587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem245588 (_4844 : nat) (_4845 : nat) : (term502 _4844 _4845) = (term503 _4844 _4845).
Proof. exact (MK_COMB (@lem245587) (@lem245586 _4844 _4845)). Qed.
Lemma lem245590 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem245591 (P : nat -> Prop) (_4844 : nat) : (term524 P _4844) = (P _4844).
Proof. exact (@lem245590 (P _4844)). Qed.
Lemma lem245592 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : (term523 _4845 P _4844) = (term525 _4845 P _4844).
Proof. exact (MK_COMB (@lem245588 _4844 _4845) (@lem245591 P _4844)). Qed.
Lemma lem245593 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : (term522 _4845 P _4844) = (term525 _4845 P _4844).
Proof. exact (TRANS (@lem245583 _4845 P _4844) (@lem245592 _4845 P _4844)). Qed.
Lemma lem245594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem245595 (_4845 : nat) (P : nat -> Prop) (_4844 : nat) : (term526 _4845 P _4844) = (term527 _4845 P _4844).
Proof. exact (MK_COMB (@lem245594) (@lem245593 _4845 P _4844)). Qed.
Lemma lem245596 (P : nat -> Prop) (_4845 : nat) : (P _4845) = (P _4845).
Proof. exact (eq_refl (P _4845)). Qed.
Lemma lem245597 (_4844 : nat) (P : nat -> Prop) (_4845 : nat) : (term521 _4844 P _4845) = (term528 _4844 P _4845).
Proof. exact (MK_COMB (@lem245595 _4845 P _4844) (@lem245596 P _4845)). Qed.
Lemma lem245598 (_4844 : nat) (P : nat -> Prop) (_4845 : nat) : (term514 _4845 P _4844) = (term528 _4844 P _4845).
Proof. exact (TRANS (@lem245580 _4844 P _4845) (@lem245597 _4844 P _4845)). Qed.
Lemma lem245600 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : term529 n P a.
Proof. exact (conj (@lem245483 a P n h1 h2) (@lem245490 a P n h2)). Qed.
Lemma lem245602 (_4844 : nat) (P : nat -> Prop) (_4845 : nat) : term528 _4844 P _4845.
Proof. exact (EQ_MP (@lem245598 _4844 P _4845) (@lem245577 _4845 P _4844)). Qed.
Lemma lem245603 (P : nat -> Prop) (a : nat) (n : nat) : term530 P a n.
Proof. exact (@lem245602 a P (Nat.modulo a n)). Qed.
Lemma lem245606 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : term46 P a n.
Proof. exact (@lem245603 P a n (@lem245600 a P n h1 h2)). Qed.
Lemma lem245607 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : term531 P a n.
Proof. exact (fun h0 : term74 P a n => @lem245606 a P n h1 h2). Qed.
Lemma lem245609 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245610 (P : nat -> Prop) (a : nat) (n : nat) : (term531 P a n) = (term46 P a n).
Proof. exact (@lem245609 (term46 P a n)). Qed.
Lemma lem245611 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term174 a P n) : term46 P a n.
Proof. exact (EQ_MP (@lem245610 P a n) (@lem245607 a P n h1 h2)). Qed.
Lemma lem245614 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem245616 (P : nat -> Prop) (_4791 : nat) (n : nat) : (term74 P _4791 n) = (term532 P _4791 n).
Proof. exact (@lem245614 (term46 P _4791 n)). Qed.
Lemma lem245619 (_4791 : nat) (P : nat -> Prop) (n : nat) (h1 : term77 P n) : term532 P _4791 n.
Proof. exact (EQ_MP (@lem245616 P _4791 n) (@lem244910 _4791 P n h1)). Qed.
Lemma lem245620 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term77 P n) : term532 P a n.
Proof. exact (@lem245619 a P n h1). Qed.
Lemma lem245623 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term77 P n) (h3 : term174 a P n) : False.
Proof. exact (@lem245620 a P n h2 (@lem245611 a P n h1 h3)). Qed.
Lemma lem245624 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term77 P n) (h3 : term174 a P n) : term466.
Proof. exact (fun h0 : ~ False => @lem245623 a P n h1 h2 h3). Qed.
Lemma lem245626 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245627 : term466 = False.
Proof. exact (@lem245626 False). Qed.
Lemma lem245628 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term77 P n) (h3 : term174 a P n) : False.
Proof. exact (EQ_MP (@lem245627) (@lem245624 a P n h1 h2 h3)). Qed.
Lemma lem245694 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term46 P a n.
Proof. exact (proj2 (@lem244215 P a n h1)). Qed.
Lemma lem245695 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term531 P a n.
Proof. exact (fun h0 : term74 P a n => @lem245694 P a n h1). Qed.
Lemma lem245697 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245698 (P : nat -> Prop) (a : nat) (n : nat) : (term531 P a n) = (term46 P a n).
Proof. exact (@lem245697 (term46 P a n)). Qed.
Lemma lem245699 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term46 P a n.
Proof. exact (EQ_MP (@lem245698 P a n) (@lem245695 P a n h1)). Qed.
Lemma lem245701 (b : Prop) (a : Prop) : (a \/ b) = (term475 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem245702 (P : nat -> Prop) (_4805 : nat) (n : nat) : (term59 n P _4805) = (term533 P _4805 n).
Proof. exact (@lem245701 (term513 P _4805) (term447 _4805 n)). Qed.
Lemma lem245704 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem245705 (P : nat -> Prop) (_4805 : nat) : (term524 P _4805) = (P _4805).
Proof. exact (@lem245704 (P _4805)). Qed.
Lemma lem245706 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem245707 (P : nat -> Prop) (_4805 : nat) : (term534 P _4805) = (term535 P _4805).
Proof. exact (MK_COMB (@lem245706) (@lem245705 P _4805)). Qed.
Lemma lem245708 (_4805 : nat) (n : nat) : (term447 _4805 n) = (term447 _4805 n).
Proof. exact (eq_refl (term447 _4805 n)). Qed.
Lemma lem245709 (P : nat -> Prop) (_4805 : nat) (n : nat) : (term533 P _4805 n) = (term536 P _4805 n).
Proof. exact (MK_COMB (@lem245707 P _4805) (@lem245708 _4805 n)). Qed.
Lemma lem245710 (P : nat -> Prop) (_4805 : nat) (n : nat) : (term59 n P _4805) = (term536 P _4805 n).
Proof. exact (TRANS (@lem245702 P _4805 n) (@lem245709 P _4805 n)). Qed.
Lemma lem245713 (_4805 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term536 P _4805 n.
Proof. exact (EQ_MP (@lem245710 P _4805 n) (@lem244974 _4805 P a n h1)). Qed.
Lemma lem245714 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term537 P a n.
Proof. exact (@lem245713 (Nat.modulo a n) P a n h1). Qed.
Lemma lem245717 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term538 a n.
Proof. exact (@lem245714 P a n h1 (@lem245699 P a n h1)). Qed.
Lemma lem245718 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term539 a n.
Proof. exact (fun h0 : term40 a n => @lem245717 P a n h1). Qed.
Lemma lem245720 (p : Prop) : (term540 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem245721 (a : nat) (n : nat) : (term539 a n) = (term538 a n).
Proof. exact (@lem245720 (term40 a n)). Qed.
Lemma lem245722 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term538 a n.
Proof. exact (EQ_MP (@lem245721 a n) (@lem245718 P a n h1)). Qed.
Lemma lem245735 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem245736 (_4801 : nat) (_4802 : nat) : (term541 _4801 _4802) = (term277 _4801 _4802).
Proof. exact (@lem245735 (term40 _4801 _4802) (_4802 = (NUMERAL 0))). Qed.
Lemma lem245744 (_4801 : nat) (_4802 : nat) : (term542 _4801 _4802) = (term542 _4801 _4802).
Proof. exact (eq_refl (term542 _4801 _4802)). Qed.
Lemma lem245745 (_4801 : nat) (_4802 : nat) : ((term277 _4801 _4802) = (term541 _4801 _4802)) = ((term277 _4801 _4802) = (term277 _4801 _4802)).
Proof. exact (MK_COMB (@lem245744 _4801 _4802) (@lem245736 _4801 _4802)). Qed.
Lemma lem245747 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem245748 (x : Prop) : (x = x) = True.
Proof. exact (@lem245747 Prop x). Qed.
Lemma lem245749 (_4801 : nat) (_4802 : nat) : ((term277 _4801 _4802) = (term277 _4801 _4802)) = True.
Proof. exact (@lem245748 (term277 _4801 _4802)). Qed.
Lemma lem245750 (_4801 : nat) (_4802 : nat) : ((term277 _4801 _4802) = (term541 _4801 _4802)) = True.
Proof. exact (TRANS (@lem245745 _4801 _4802) (@lem245749 _4801 _4802)). Qed.
Lemma lem245751 (_4801 : nat) (_4802 : nat) : True = ((term277 _4801 _4802) = (term541 _4801 _4802)).
Proof. exact (SYM (@lem245750 _4801 _4802)). Qed.
Lemma lem245752 (_4801 : nat) (_4802 : nat) : (term277 _4801 _4802) = (term541 _4801 _4802).
Proof. exact (EQ_MP (@lem245751 _4801 _4802) (@lem0)). Qed.
Lemma lem245753 (_4801 : nat) (_4802 : nat) (h1 : term45) : term541 _4801 _4802.
Proof. exact (EQ_MP (@lem245752 _4801 _4802) (@lem244962 _4801 _4802 h1)). Qed.
Lemma lem245755 (b : Prop) (a : Prop) : (a \/ b) = (term475 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem245758 (_4801 : nat) (_4802 : nat) : (term541 _4801 _4802) = (term543 _4801 _4802).
Proof. exact (@lem245755 (term40 _4801 _4802) (_4802 = (NUMERAL 0))). Qed.
Lemma lem245761 (_4801 : nat) (_4802 : nat) (h1 : term45) : term543 _4801 _4802.
Proof. exact (EQ_MP (@lem245758 _4801 _4802) (@lem245753 _4801 _4802 h1)). Qed.
Lemma lem245762 (a : nat) (n : nat) (h1 : term45) : term543 a n.
Proof. exact (@lem245761 a n h1). Qed.
Lemma lem245765 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term207 P a n) : n = (NUMERAL 0).
Proof. exact (@lem245762 a n h1 (@lem245722 P a n h2)). Qed.
Lemma lem245766 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term207 P a n) : term544 n.
Proof. exact (fun h0 : term41 n => @lem245765 P a n h1 h2). Qed.
Lemma lem245768 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245769 (n : nat) : (term544 n) = (n = (NUMERAL 0)).
Proof. exact (@lem245768 (n = (NUMERAL 0))). Qed.
Lemma lem245770 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term207 P a n) : n = (NUMERAL 0).
Proof. exact (EQ_MP (@lem245769 n) (@lem245766 P a n h1 h2)). Qed.
Lemma lem245773 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem245775 (n : nat) : (term41 n) = (term545 n).
Proof. exact (@lem245773 (n = (NUMERAL 0))). Qed.
Lemma lem245778 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term207 P a n) : term545 n.
Proof. exact (EQ_MP (@lem245775 n) (@lem244976 P a n h1)). Qed.
Lemma lem245781 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term207 P a n) : False.
Proof. exact (@lem245778 P a n h2 (@lem245770 P a n h1 h2)). Qed.
Lemma lem245782 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term207 P a n) : term466.
Proof. exact (fun h0 : ~ False => @lem245781 P a n h1 h2). Qed.
Lemma lem245784 (p : Prop) : (term464 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem245785 : term466 = False.
Proof. exact (@lem245784 False). Qed.
Lemma lem245786 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term207 P a n) : False.
Proof. exact (EQ_MP (@lem245785) (@lem245782 P a n h1 h2)). Qed.
Lemma lem245787 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem245256) (@lem245253 a P n h1 h2 h3)). Qed.
Lemma lem245788 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem245787 a P n h1 h2 h3) (fun h4 : False => @lem244846 n h3)). Qed.
Lemma lem245789 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem245788 a P n h1 h2 h3) (@lem244846 n h3)). Qed.
Lemma lem245790 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem245789 a P n h1 h2 h3) (fun h4 : False => @lem244365 n h3)). Qed.
Lemma lem245791 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem245790 a P n h1 h2 h3) (@lem244365 n h3)). Qed.
Lemma lem245792 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term77 P n) (h3 : term174 a P n) : (term77 P n) = False.
Proof. exact (prop_ext (fun h4 : term77 P n => @lem245628 a P n h1 h2 h3) (fun h4 : False => @lem244515 P n h2)). Qed.
Lemma lem245793 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term77 P n) (h3 : term174 a P n) : False.
Proof. exact (EQ_MP (@lem245792 a P n h1 h2 h3) (@lem244515 P n h2)). Qed.
Lemma lem245794 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem245791 a P n h1 h2 h3) (fun h4 : False => @lem244365 n h3)). Qed.
Lemma lem245795 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term174 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem245794 a P n h1 h2 h3) (@lem244365 n h3)). Qed.
Lemma lem245796 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term20) (h3 : term174 a P n) : False.
Proof. exact (or_elim (@lem244209 a P n h3) (fun h0 : n = (NUMERAL 0) => @lem245795 a P n h2 h3 h0) (fun h0 : term77 P n => @lem245793 a P n h1 h0 h3)). Qed.
Lemma lem245797 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term39) (h3 : term20) (h4 : term266 P a n) : False.
Proof. exact (or_elim (@lem244198 P a n h4) (fun h0 : term174 a P n => @lem245796 a P n h2 h3 h0) (fun h0 : term207 P a n => @lem245786 P a n h1 h0)). Qed.
Lemma lem245798 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term39) (h3 : term20) (h4 : term266 P a n) : (term266 P a n) = False.
Proof. exact (prop_ext (fun h5 : term266 P a n => @lem245797 P a n h1 h2 h3 h4) (fun h5 : False => @lem244198 P a n h4)). Qed.
Lemma lem245799 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term39) (h3 : term20) (h4 : term266 P a n) : False.
Proof. exact (EQ_MP (@lem245798 P a n h1 h2 h3 h4) (@lem244198 P a n h4)). Qed.
Lemma lem245800 (P : nat -> Prop) (n : nat) (h1 : term45) (h2 : term39) (h3 : term269 P n) (h4 : term20) : False.
Proof. exact (ex_elim (@lem243900 P n h3) (fun a : nat => fun h0 : term268 P n a => @lem245799 P a n h1 h2 h4 h0)). Qed.
Lemma lem245801 (P : nat -> Prop) (h1 : term45) (h2 : term39) (h3 : term271 P) (h4 : term20) : False.
Proof. exact (ex_elim (@lem243899 P h3) (fun n : nat => fun h0 : term270 P n => @lem245800 P n h1 h2 h0 h4)). Qed.
Lemma lem245802 (h1 : term45) (h2 : term39) (h3 : term3) (h4 : term20) : False.
Proof. exact (ex_elim (@lem243002 h3) (fun P : nat -> Prop => fun h0 : term272 P => @lem245801 P h1 h2 h0 h4)). Qed.
Lemma lem245803 (h1 : term45) (h2 : term39) (h3 : term3) : term546.
Proof. exact (fun h0 : term20 => @lem245802 h1 h2 h3 h0). Qed.
Lemma lem245804 : term546 = term21.
Proof. exact (@lem69 term20). Qed.
Lemma lem245805 (h1 : term45) (h2 : term39) (h3 : term3) : term21.
Proof. exact (EQ_MP (@lem245804) (@lem245803 h1 h2 h3)). Qed.
Lemma lem245806 (h1 : term45) (h2 : term3) : term24.
Proof. exact (fun h0 : term39 => @lem245805 h1 h0 h2). Qed.
Lemma lem245807 (h1 : term3) : term27.
Proof. exact (fun h0 : term45 => @lem245806 h0 h1). Qed.
Lemma lem245808 : term29.
Proof. exact (fun h0 : term3 => @lem245807 h0). Qed.
Lemma lem245809 : term4.
Proof. exact (EQ_MP (@lem242302) (@lem245808)). Qed.
Lemma lem245811 : term4.
Proof. exact (@lem241998 (@lem245809)). Qed.
Lemma lem245812 (h1 : term3) : term26.
Proof. exact (@lem245811 (@lem241983 h1)). Qed.
Lemma lem245813 (h1 : term3) : term23.
Proof. exact (@lem245812 h1 (@lem165615)). Qed.
Lemma lem245814 (h1 : term3) : term8.
Proof. exact (@lem245813 h1 (@lem173992)). Qed.
Lemma lem245815 (h1 : term3) : False.
Proof. exact (@lem245814 h1 (@lem89997)). Qed.
Lemma lem245816 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem245815 h1) (fun h2 : False => @lem241983 h1)). Qed.
Lemma lem245817 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem245816 h1) (@lem241983 h1)). Qed.
Lemma lem245818 : term2.
Proof. exact (fun h0 : term3 => @lem245817 h0). Qed.
Lemma lem245819 : term1.
Proof. exact (EQ_MP (@lem241982) (@lem245818)). Qed.
