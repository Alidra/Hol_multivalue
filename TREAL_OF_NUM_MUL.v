Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_OF_NUM_MUL_term_abbrevs.
Require Import HREAL_ADD_RID_spec.
Require Import HREAL_MUL_LZERO_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1318990_spec.
Require Import thm1320277_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Require Import treal_mul_spec.
Require Import treal_of_num_spec.
Lemma lem1327158 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1327184 : term1.
Proof. exact (proj1 (@lem1327158)). Qed.
Lemma lem1327185 (m : nat) : term2 m.
Proof. exact (@lem1327184 m). Qed.
Lemma lem1327186 (m : nat) : (term2 m) = ((term3 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1327192 (n : hreal) : term4 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1327193 (n : hreal) : (term4 n) = ((term5 n) = n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem1327195 (x : hreal) : term6 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1327196 (x : hreal) : (term6 x) = ((term7 x) = x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1327201 (m : hreal) : term8 m.
Proof. exact (@lem1321875 m). Qed.
Lemma lem1327202 (m : hreal) : (term8 m) = ((term9 m) = term10).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1327207 (m : nat) : term11 m.
Proof. exact (@lem1318990 m). Qed.
Lemma lem1327208 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem1327209 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1327208 m) (@lem1327207 m)). Qed.
Lemma lem1327210 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem1327209 m n). Qed.
Lemma lem1327211 (m : nat) (n : nat) : (term13 m n) = ((term14 m n) = (term15 m n)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem1327213 (x1 : hreal) : term16 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1327214 (x1 : hreal) : (term16 x1) = (term17 x1).
Proof. exact (eq_refl (term16 x1)). Qed.
Lemma lem1327215 (x1 : hreal) : term17 x1.
Proof. exact (EQ_MP (@lem1327214 x1) (@lem1327213 x1)). Qed.
Lemma lem1327216 (x1 : hreal) (y2 : hreal) : term18 x1 y2.
Proof. exact (@lem1327215 x1 y2). Qed.
Lemma lem1327217 (x1 : hreal) (y2 : hreal) : (term18 x1 y2) = (term19 x1 y2).
Proof. exact (eq_refl (term18 x1 y2)). Qed.
Lemma lem1327218 (x1 : hreal) (y2 : hreal) : term19 x1 y2.
Proof. exact (EQ_MP (@lem1327217 x1 y2) (@lem1327216 x1 y2)). Qed.
Lemma lem1327219 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term20 x1 y2 y1.
Proof. exact (@lem1327218 x1 y2 y1). Qed.
Lemma lem1327220 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term20 x1 y2 y1) = (term21 x1 y2 y1).
Proof. exact (eq_refl (term20 x1 y2 y1)). Qed.
Lemma lem1327221 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term21 x1 y2 y1.
Proof. exact (EQ_MP (@lem1327220 x1 y2 y1) (@lem1327219 x1 y2 y1)). Qed.
Lemma lem1327222 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term22 x1 y2 y1 x2.
Proof. exact (@lem1327221 x1 y2 y1 x2). Qed.
Lemma lem1327223 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term22 x1 y2 y1 x2) = ((term23 x1 y1 x2 y2) = (term24 x1 y2 y1 x2)).
Proof. exact (eq_refl (term22 x1 y2 y1 x2)). Qed.
Lemma lem1327225 (x1 : hreal) : term25 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1327226 (x1 : hreal) : (term25 x1) = (term26 x1).
Proof. exact (eq_refl (term25 x1)). Qed.
Lemma lem1327227 (x1 : hreal) : term26 x1.
Proof. exact (EQ_MP (@lem1327226 x1) (@lem1327225 x1)). Qed.
Lemma lem1327228 (x1 : hreal) (y2 : hreal) : term27 x1 y2.
Proof. exact (@lem1327227 x1 y2). Qed.
Lemma lem1327229 (x1 : hreal) (y2 : hreal) : (term27 x1 y2) = (term28 x1 y2).
Proof. exact (eq_refl (term27 x1 y2)). Qed.
Lemma lem1327230 (x1 : hreal) (y2 : hreal) : term28 x1 y2.
Proof. exact (EQ_MP (@lem1327229 x1 y2) (@lem1327228 x1 y2)). Qed.
Lemma lem1327231 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term29 x1 y2 x2.
Proof. exact (@lem1327230 x1 y2 x2). Qed.
Lemma lem1327232 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term29 x1 y2 x2) = (term30 x1 y2 x2).
Proof. exact (eq_refl (term29 x1 y2 x2)). Qed.
Lemma lem1327233 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term30 x1 y2 x2.
Proof. exact (EQ_MP (@lem1327232 x1 y2 x2) (@lem1327231 x1 y2 x2)). Qed.
Lemma lem1327234 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term31 x1 y2 x2 y1.
Proof. exact (@lem1327233 x1 y2 x2 y1). Qed.
Lemma lem1327235 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term31 x1 y2 x2 y1) = ((term32 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term31 x1 y2 x2 y1)). Qed.
Lemma lem1327237 (n : nat) : term33 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1327238 (n : nat) : (term33 n) = ((treal_of_num n) = (term34 n)).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem1327249 (n : nat) : (treal_of_num n) = (term34 n).
Proof. exact (EQ_MP (@lem1327238 n) (@lem1327237 n)). Qed.
Lemma lem1327250 (m : nat) : (treal_of_num m) = (term34 m).
Proof. exact (@lem1327249 m). Qed.
Lemma lem1327251 : treal_mul = treal_mul.
Proof. exact (eq_refl treal_mul). Qed.
Lemma lem1327252 (m : nat) : (term35 m) = (term36 m).
Proof. exact (MK_COMB (@lem1327251) (@lem1327250 m)). Qed.
Lemma lem1327254 (n : nat) : (treal_of_num n) = (term34 n).
Proof. exact (EQ_MP (@lem1327238 n) (@lem1327237 n)). Qed.
Lemma lem1327255 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem1327252 m) (@lem1327254 n)). Qed.
Lemma lem1327257 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term23 x1 y1 x2 y2) = (term24 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1327223 x1 y2 y1 x2) (@lem1327222 x1 y2 y1 x2)). Qed.
Lemma lem1327258 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (@lem1327257 (hreal_of_num m) term10 term10 (hreal_of_num n)). Qed.
Lemma lem1327260 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (EQ_MP (@lem1327211 m n) (@lem1327210 m n)). Qed.
Lemma lem1327261 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1327262 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem1327261) (@lem1327260 m n)). Qed.
Lemma lem1327264 (m : hreal) : (term9 m) = term10.
Proof. exact (EQ_MP (@lem1327202 m) (@lem1327201 m)). Qed.
Lemma lem1327265 : term42 = term10.
Proof. exact (@lem1327264 term10). Qed.
Lemma lem1327266 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem1327262 m n) (@lem1327265)). Qed.
Lemma lem1327268 (n : hreal) : (term5 n) = n.
Proof. exact (EQ_MP (@lem1327193 n) (@lem1327192 n)). Qed.
Lemma lem1327269 (m : nat) (n : nat) : (term44 m n) = (term15 m n).
Proof. exact (@lem1327268 (term15 m n)). Qed.
Lemma lem1327270 (m : nat) (n : nat) : (term43 m n) = (term15 m n).
Proof. exact (TRANS (@lem1327266 m n) (@lem1327269 m n)). Qed.
Lemma lem1327271 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1327272 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem1327271) (@lem1327270 m n)). Qed.
Lemma lem1327274 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (EQ_MP (@lem1327211 m n) (@lem1327210 m n)). Qed.
Lemma lem1327275 (m : nat) : (term47 m) = (term48 m).
Proof. exact (@lem1327274 m (NUMERAL 0)). Qed.
Lemma lem1327277 (m : nat) : (term3 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1327186 m) (@lem1327185 m)). Qed.
Lemma lem1327278 : hreal_of_num = hreal_of_num.
Proof. exact (eq_refl hreal_of_num). Qed.
Lemma lem1327279 (m : nat) : (term48 m) = term10.
Proof. exact (MK_COMB (@lem1327278) (@lem1327277 m)). Qed.
Lemma lem1327280 (m : nat) : (term47 m) = term10.
Proof. exact (TRANS (@lem1327275 m) (@lem1327279 m)). Qed.
Lemma lem1327281 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1327282 (m : nat) : (term49 m) = term50.
Proof. exact (MK_COMB (@lem1327281) (@lem1327280 m)). Qed.
Lemma lem1327284 (m : hreal) : (term9 m) = term10.
Proof. exact (EQ_MP (@lem1327202 m) (@lem1327201 m)). Qed.
Lemma lem1327285 (n : nat) : (term51 n) = term10.
Proof. exact (@lem1327284 (hreal_of_num n)). Qed.
Lemma lem1327286 (m : nat) (n : nat) : (term52 m n) = term53.
Proof. exact (MK_COMB (@lem1327282 m) (@lem1327285 n)). Qed.
Lemma lem1327288 (x : hreal) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1327196 x) (@lem1327195 x)). Qed.
Lemma lem1327289 : term53 = term10.
Proof. exact (@lem1327288 term10). Qed.
Lemma lem1327290 (m : nat) (n : nat) : (term52 m n) = term10.
Proof. exact (TRANS (@lem1327286 m n) (@lem1327289)). Qed.
Lemma lem1327291 (m : nat) (n : nat) : (term39 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem1327272 m n) (@lem1327290 m n)). Qed.
Lemma lem1327292 (m : nat) (n : nat) : (term38 m n) = (term54 m n).
Proof. exact (TRANS (@lem1327258 m n) (@lem1327291 m n)). Qed.
Lemma lem1327293 (m : nat) (n : nat) : (term37 m n) = (term54 m n).
Proof. exact (TRANS (@lem1327255 m n) (@lem1327292 m n)). Qed.
Lemma lem1327294 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1327295 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem1327294) (@lem1327293 m n)). Qed.
Lemma lem1327297 (n : nat) : (treal_of_num n) = (term34 n).
Proof. exact (EQ_MP (@lem1327238 n) (@lem1327237 n)). Qed.
Lemma lem1327298 (m : nat) (n : nat) : (term57 m n) = (term54 m n).
Proof. exact (@lem1327297 (Nat.mul m n)). Qed.
Lemma lem1327299 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem1327295 m n) (@lem1327298 m n)). Qed.
Lemma lem1327301 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term32 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1327235 x1 y2 x2 y1) (@lem1327234 x1 y2 x2 y1)). Qed.
Lemma lem1327302 (m : nat) (n : nat) : (term59 m n) = ((term44 m n) = (term44 m n)).
Proof. exact (@lem1327301 (term15 m n) term10 (term15 m n) term10). Qed.
Lemma lem1327304 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1327305 (x : hreal) : (x = x) = True.
Proof. exact (@lem1327304 hreal x). Qed.
Lemma lem1327306 (m : nat) (n : nat) : ((term44 m n) = (term44 m n)) = True.
Proof. exact (@lem1327305 (term44 m n)). Qed.
Lemma lem1327307 (m : nat) (n : nat) : (term59 m n) = True.
Proof. exact (TRANS (@lem1327302 m n) (@lem1327306 m n)). Qed.
Lemma lem1327308 (m : nat) (n : nat) : (term58 m n) = True.
Proof. exact (TRANS (@lem1327299 m n) (@lem1327307 m n)). Qed.
Lemma lem1327309 (m : nat) : (term60 m) = term61.
Proof. exact (fun_ext (fun n : nat => @lem1327308 m n)). Qed.
Lemma lem1327310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1327311 (m : nat) : (term62 m) = term63.
Proof. exact (MK_COMB (@lem1327310) (@lem1327309 m)). Qed.
Lemma lem1327313 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327314 (t : Prop) : (term65 t) = t.
Proof. exact (@lem1327313 nat t). Qed.
Lemma lem1327315 : term63 = True.
Proof. exact (@lem1327314 True). Qed.
Lemma lem1327316 (m : nat) : (term62 m) = True.
Proof. exact (TRANS (@lem1327311 m) (@lem1327315)). Qed.
Lemma lem1327317 : term66 = term61.
Proof. exact (fun_ext (fun m : nat => @lem1327316 m)). Qed.
Lemma lem1327318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1327319 : term67 = term63.
Proof. exact (MK_COMB (@lem1327318) (@lem1327317)). Qed.
Lemma lem1327321 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327322 (t : Prop) : (term65 t) = t.
Proof. exact (@lem1327321 nat t). Qed.
Lemma lem1327323 : term63 = True.
Proof. exact (@lem1327322 True). Qed.
Lemma lem1327324 : term67 = True.
Proof. exact (TRANS (@lem1327319) (@lem1327323)). Qed.
Lemma lem1327325 : True = term67.
Proof. exact (SYM (@lem1327324)). Qed.
Lemma lem1327326 : term67.
Proof. exact (EQ_MP (@lem1327325) (@lem0)). Qed.
