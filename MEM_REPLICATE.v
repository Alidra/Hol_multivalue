Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_REPLICATE_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1099511_spec.
Require Import thm1099512_spec.
Require Import thm1099517_spec.
Require Import thm1099518_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem1138212 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1138213 {A : Type'} : term1 A.
Proof. exact (@lem1138212 (term2 A)). Qed.
Lemma lem1138214 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1138215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1138216 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem1138215) (@lem1138214 A)). Qed.
Lemma lem1138217 {A : Type'} (n : nat) : (term7 A n) = (term8 A n).
Proof. exact (eq_refl (term7 A n)). Qed.
Lemma lem1138218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1138219 {A : Type'} (n : nat) : (term9 A n) = (term10 A n).
Proof. exact (MK_COMB (@lem1138218) (@lem1138217 A n)). Qed.
Lemma lem1138220 {A : Type'} (n : nat) : (term11 A n) = (term12 A n).
Proof. exact (eq_refl (term11 A n)). Qed.
Lemma lem1138221 {A : Type'} (n : nat) : (term13 A n) = (term14 A n).
Proof. exact (MK_COMB (@lem1138219 A n) (@lem1138220 A n)). Qed.
Lemma lem1138222 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (fun_ext (fun n : nat => @lem1138221 A n)). Qed.
Lemma lem1138223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1138224 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem1138223) (@lem1138222 A)). Qed.
Lemma lem1138225 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (MK_COMB (@lem1138216 A) (@lem1138224 A)). Qed.
Lemma lem1138226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1138227 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem1138226) (@lem1138225 A)). Qed.
Lemma lem1138228 {A : Type'} (n : nat) : (term7 A n) = (term8 A n).
Proof. exact (eq_refl (term7 A n)). Qed.
Lemma lem1138229 {A : Type'} : (term23 A) = (term2 A).
Proof. exact (fun_ext (fun n : nat => @lem1138228 A n)). Qed.
Lemma lem1138230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1138231 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem1138230) (@lem1138229 A)). Qed.
Lemma lem1138232 {A : Type'} : (term1 A) = (term26 A).
Proof. exact (MK_COMB (@lem1138227 A) (@lem1138231 A)). Qed.
Lemma lem1138233 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem1138232 A) (@lem1138213 A)). Qed.
Lemma lem1138234 {A : Type'} (n : nat) (h1 : term8 A n) : term8 A n.
Proof. exact (h1). Qed.
Lemma lem1138266 {_25272 : Type'} (x : _25272) : (term27 _25272 x) = (@nil _25272).
Proof. exact (EQ_MP (@lem1099512 _25272 x) (@lem1099511 _25272 x)). Qed.
Lemma lem1138267 {A : Type'} (x : A) : (term27 A x) = (@nil A).
Proof. exact (@lem1138266 A x). Qed.
Lemma lem1138268 {A : Type'} (y : A) : (term27 A y) = (@nil A).
Proof. exact (@lem1138267 A y). Qed.
Lemma lem1138269 {A : Type'} (x : A) : (@List.In A x) = (@List.In A x).
Proof. exact (eq_refl (@List.In A x)). Qed.
Lemma lem1138270 {A : Type'} (y : A) (x : A) : (term28 A x y) = (@List.In A x (@nil A)).
Proof. exact (MK_COMB (@lem1138269 A x) (@lem1138268 A y)). Qed.
Lemma lem1138272 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1138273 {A : Type'} (x : A) : (@List.In A x (@nil A)) = False.
Proof. exact (@lem1138272 A x). Qed.
Lemma lem1138274 {A : Type'} (x : A) (y : A) : (term28 A x y) = False.
Proof. exact (TRANS (@lem1138270 A y x) (@lem1138273 A x)). Qed.
Lemma lem1138275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1138276 {A : Type'} (x : A) (y : A) : (term29 A x y) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1138275) (@lem1138274 A x y)). Qed.
Lemma lem1138282 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1138283 (x : nat) : (x = x) = True.
Proof. exact (@lem1138282 nat x). Qed.
Lemma lem1138284 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1138283 (NUMERAL 0)). Qed.
Lemma lem1138285 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1138286 : term30 = (~ True).
Proof. exact (MK_COMB (@lem1138285) (@lem1138284)). Qed.
Lemma lem1138288 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1138289 : term30 = False.
Proof. exact (TRANS (@lem1138286) (@lem1138288)). Qed.
Lemma lem1138290 {A : Type'} (x : A) (y : A) : (term31 A x y) = (term31 A x y).
Proof. exact (eq_refl (term31 A x y)). Qed.
Lemma lem1138291 {A : Type'} (x : A) (y : A) : (term32 A x y) = (term33 A x y).
Proof. exact (MK_COMB (@lem1138290 A x y) (@lem1138289)). Qed.
Lemma lem1138293 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1138294 {A : Type'} (x : A) (y : A) : (term33 A x y) = False.
Proof. exact (@lem1138293 (x = y)). Qed.
Lemma lem1138295 {A : Type'} (x : A) (y : A) : (term32 A x y) = False.
Proof. exact (TRANS (@lem1138291 A x y) (@lem1138294 A x y)). Qed.
Lemma lem1138296 {A : Type'} (x : A) (y : A) : ((term28 A x y) = (term32 A x y)) = (False = False).
Proof. exact (MK_COMB (@lem1138276 A x y) (@lem1138295 A x y)). Qed.
Lemma lem1138298 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1138299 : (False = False) = (~ False).
Proof. exact (@lem1138298 False). Qed.
Lemma lem1138301 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1138302 : (False = False) = True.
Proof. exact (TRANS (@lem1138299) (@lem1138301)). Qed.
Lemma lem1138303 {A : Type'} (x : A) (y : A) : ((term28 A x y) = (term32 A x y)) = True.
Proof. exact (TRANS (@lem1138296 A x y) (@lem1138302)). Qed.
Lemma lem1138304 {A : Type'} (x : A) : (term34 A x) = (term35 A).
Proof. exact (fun_ext (fun y : A => @lem1138303 A x y)). Qed.
Lemma lem1138305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1138306 {A : Type'} (x : A) : (term36 A x) = (term37 A).
Proof. exact (MK_COMB (@lem1138305 A) (@lem1138304 A x)). Qed.
Lemma lem1138308 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1138309 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem1138308 A t). Qed.
Lemma lem1138310 {A : Type'} : (term37 A) = True.
Proof. exact (@lem1138309 A True). Qed.
Lemma lem1138311 {A : Type'} (x : A) : (term36 A x) = True.
Proof. exact (TRANS (@lem1138306 A x) (@lem1138310 A)). Qed.
Lemma lem1138312 {A : Type'} : (term39 A) = (term35 A).
Proof. exact (fun_ext (fun x : A => @lem1138311 A x)). Qed.
Lemma lem1138313 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1138314 {A : Type'} : (term4 A) = (term37 A).
Proof. exact (MK_COMB (@lem1138313 A) (@lem1138312 A)). Qed.
Lemma lem1138316 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1138317 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem1138316 A t). Qed.
Lemma lem1138318 {A : Type'} : (term37 A) = True.
Proof. exact (@lem1138317 A True). Qed.
Lemma lem1138319 {A : Type'} : (term4 A) = True.
Proof. exact (TRANS (@lem1138314 A) (@lem1138318 A)). Qed.
Lemma lem1138320 {A : Type'} : True = (term4 A).
Proof. exact (SYM (@lem1138319 A)). Qed.
Lemma lem1138321 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1138320 A) (@lem0)). Qed.
Lemma lem1138322 (n : nat) : term40 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1138323 (n : nat) : (term40 n) = (term41 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1138324 (n : nat) : term41 n.
Proof. exact (EQ_MP (@lem1138323 n) (@lem1138322 n)). Qed.
Lemma lem1138325 (n : nat) : term42 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1138342 {A : Type'} (x : A) (n : nat) (h1 : term8 A n) : term43 A n x.
Proof. exact (@lem1138234 A n h1 x). Qed.
Lemma lem1138343 {A : Type'} (x : A) (n : nat) : (term43 A n x) = (term44 A x n).
Proof. exact (eq_refl (term43 A n x)). Qed.
Lemma lem1138344 {A : Type'} (x : A) (n : nat) (h1 : term8 A n) : term44 A x n.
Proof. exact (EQ_MP (@lem1138343 A x n) (@lem1138342 A x n h1)). Qed.
Lemma lem1138345 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : term45 A x n y.
Proof. exact (@lem1138344 A x n h1 y). Qed.
Lemma lem1138346 {A : Type'} (x : A) (y : A) (n : nat) : (term45 A x n y) = ((term46 A x n y) = (term47 A x y n)).
Proof. exact (eq_refl (term45 A x n y)). Qed.
Lemma lem1138359 {_25272 : Type'} (n : nat) (x : _25272) : (term48 _25272 n x) = (term49 _25272 n x).
Proof. exact (EQ_MP (@lem1099518 _25272 n x) (@lem1099517 _25272 n x)). Qed.
Lemma lem1138360 {A : Type'} (n : nat) (x : A) : (term48 A n x) = (term49 A n x).
Proof. exact (@lem1138359 A n x). Qed.
Lemma lem1138361 {A : Type'} (n : nat) (y : A) : (term48 A n y) = (term49 A n y).
Proof. exact (@lem1138360 A n y). Qed.
Lemma lem1138362 {A : Type'} (x : A) : (@List.In A x) = (@List.In A x).
Proof. exact (eq_refl (@List.In A x)). Qed.
Lemma lem1138363 {A : Type'} (x : A) (n : nat) (y : A) : (term50 A x n y) = (term51 A x n y).
Proof. exact (MK_COMB (@lem1138362 A x) (@lem1138361 A n y)). Qed.
Lemma lem1138365 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term52 _25376 x h t) = (term53 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1138366 {A : Type'} (h : A) (x : A) (t : list A) : (term52 A x h t) = (term53 A h x t).
Proof. exact (@lem1138365 A h x t). Qed.
Lemma lem1138367 {A : Type'} (x : A) (n : nat) (y : A) : (term51 A x n y) = (term54 A x n y).
Proof. exact (@lem1138366 A y x (@repeat_with_perm_args A n y)). Qed.
Lemma lem1138373 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : (term46 A x n y) = (term47 A x y n).
Proof. exact (EQ_MP (@lem1138346 A x y n) (@lem1138345 A x y n h1)). Qed.
Lemma lem1138374 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : (term46 A x n y) = (term47 A x y n).
Proof. exact (@lem1138373 A x y n h1). Qed.
Lemma lem1138381 {A : Type'} (x : A) (y : A) : (term55 A x y) = (term55 A x y).
Proof. exact (eq_refl (term55 A x y)). Qed.
Lemma lem1138382 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : (term54 A x n y) = (term56 A x y n).
Proof. exact (MK_COMB (@lem1138381 A x y) (@lem1138374 A x y n h1)). Qed.
Lemma lem1138385 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : (term51 A x n y) = (term56 A x y n).
Proof. exact (TRANS (@lem1138367 A x n y) (@lem1138382 A x y n h1)). Qed.
Lemma lem1138386 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : (term50 A x n y) = (term56 A x y n).
Proof. exact (TRANS (@lem1138363 A x n y) (@lem1138385 A x y n h1)). Qed.
Lemma lem1138387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1138388 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : (term57 A x n y) = (term58 A x y n).
Proof. exact (MK_COMB (@lem1138387) (@lem1138386 A x y n h1)). Qed.
Lemma lem1138394 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1138325 n (@lem1138324 n)). Qed.
Lemma lem1138395 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1138396 (n : nat) : (term41 n) = (~ False).
Proof. exact (MK_COMB (@lem1138395) (@lem1138394 n)). Qed.
Lemma lem1138398 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1138399 (n : nat) : (term41 n) = True.
Proof. exact (TRANS (@lem1138396 n) (@lem1138398)). Qed.
Lemma lem1138400 {A : Type'} (x : A) (y : A) : (term31 A x y) = (term31 A x y).
Proof. exact (eq_refl (term31 A x y)). Qed.
Lemma lem1138401 {A : Type'} (n : nat) (x : A) (y : A) : (term59 A x y n) = (term60 A x y).
Proof. exact (MK_COMB (@lem1138400 A x y) (@lem1138399 n)). Qed.
Lemma lem1138403 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1138404 {A : Type'} (x : A) (y : A) : (term60 A x y) = (x = y).
Proof. exact (@lem1138403 (x = y)). Qed.
Lemma lem1138407 {A : Type'} (n : nat) (x : A) (y : A) : (term59 A x y n) = (x = y).
Proof. exact (TRANS (@lem1138401 A n x y) (@lem1138404 A x y)). Qed.
Lemma lem1138408 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term8 A n) : ((term50 A x n y) = (term59 A x y n)) = ((term56 A x y n) = (x = y)).
Proof. exact (MK_COMB (@lem1138388 A x y n h1) (@lem1138407 A n x y)). Qed.
Lemma lem1138411 {A : Type'} (x : A) (n : nat) (h1 : term8 A n) : (term61 A x n) = (term62 A n x).
Proof. exact (fun_ext (fun y : A => @lem1138408 A x y n h1)). Qed.
Lemma lem1138412 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1138413 {A : Type'} (x : A) (n : nat) (h1 : term8 A n) : (term63 A x n) = (term64 A n x).
Proof. exact (MK_COMB (@lem1138412 A) (@lem1138411 A x n h1)). Qed.
Lemma lem1138418 {A : Type'} (n : nat) (h1 : term8 A n) : (term65 A n) = (term66 A n).
Proof. exact (fun_ext (fun x : A => @lem1138413 A x n h1)). Qed.
Lemma lem1138419 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1138420 {A : Type'} (n : nat) (h1 : term8 A n) : (term12 A n) = (term67 A n).
Proof. exact (MK_COMB (@lem1138419 A) (@lem1138418 A n h1)). Qed.
Lemma lem1138425 {A : Type'} (n : nat) (h1 : term8 A n) : (term67 A n) = (term12 A n).
Proof. exact (SYM (@lem1138420 A n h1)). Qed.
Lemma lem1138427 (p : Prop) : p = (term68 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1138428 {A : Type'} (n : nat) : (term67 A n) = (term69 A n).
Proof. exact (@lem1138427 (term67 A n)). Qed.
Lemma lem1138429 {A : Type'} (n : nat) : (term69 A n) = (term67 A n).
Proof. exact (SYM (@lem1138428 A n)). Qed.
Lemma lem1138430 {A : Type'} (n : nat) (h1 : term70 A n) : term70 A n.
Proof. exact (h1). Qed.
Lemma lem1138433 {A : Type'} (n : nat) (h1 : term69 A n) : term69 A n.
Proof. exact (h1). Qed.
Lemma lem1138434 {A : Type'} (n : nat) : term71 A n.
Proof. exact (fun h0 : term69 A n => @lem1138433 A n h0). Qed.
Lemma lem1138435 {A : Type'} (n : nat) (h1 : term71 A n) : term71 A n.
Proof. exact (h1). Qed.
Lemma lem1138436 {A : Type'} (n : nat) (h1 : term69 A n) : term69 A n.
Proof. exact (h1). Qed.
Lemma lem1138437 {A : Type'} (n : nat) (h1 : term69 A n) (h2 : term71 A n) : term69 A n.
Proof. exact (@lem1138435 A n h2 (@lem1138436 A n h1)). Qed.
Lemma lem1138438 {A : Type'} (n : nat) (h1 : term69 A n) : term72 A n.
Proof. exact (fun h0 : term71 A n => @lem1138437 A n h1 h0). Qed.
Lemma lem1138439 {A : Type'} (n : nat) (h1 : term71 A n) : term71 A n.
Proof. exact (h1). Qed.
Lemma lem1138440 {A : Type'} (n : nat) (h1 : term69 A n) (h2 : term71 A n) : term69 A n.
Proof. exact (@lem1138438 A n h1 (@lem1138439 A n h2)). Qed.
Lemma lem1138441 {A : Type'} (n : nat) (h1 : term71 A n) : term71 A n.
Proof. exact (fun h0 : term69 A n => @lem1138440 A n h0 h1). Qed.
Lemma lem1138442 {A : Type'} (n : nat) : term73 A n.
Proof. exact (fun h0 : term71 A n => @lem1138441 A n h0). Qed.
Lemma lem1138445 {A : Type'} (n : nat) : term71 A n.
Proof. exact (@lem1138442 A n (@lem1138434 A n)). Qed.
Lemma lem1138446 {A : Type'} (n : nat) : term71 A n.
Proof. exact (@lem1138445 A n). Qed.
Lemma lem1138452 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1138453 {A : Type'} (n : nat) : (term69 A n) = (term74 A n).
Proof. exact (@lem1138452 (term70 A n)). Qed.
Lemma lem1138455 (t : Prop) : (term75 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1138456 {A : Type'} (n : nat) : (term74 A n) = (term67 A n).
Proof. exact (@lem1138455 (term67 A n)). Qed.
Lemma lem1138461 {A : Type'} (n : nat) : (term69 A n) = (term67 A n).
Proof. exact (TRANS (@lem1138453 A n) (@lem1138456 A n)). Qed.
Lemma lem1138470 {A : Type'} : (term76 A) = (term77 A).
Proof. exact (fun_ext (fun n : nat => @lem1138461 A n)). Qed.
Lemma lem1138471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1138480 {A : Type'} : (term78 A) = (term79 A).
Proof. exact (MK_COMB (@lem1138471) (@lem1138470 A)). Qed.
Lemma lem1138495 {A : Type'} (n : nat) (x : A) (y : A) : ((term56 A x y n) = (x = y)) = ((term56 A x y n) = (x = y)).
Proof. exact (eq_refl ((term56 A x y n) = (x = y))). Qed.
Lemma lem1138496 {A : Type'} (n : nat) (x : A) : (term62 A n x) = (term62 A n x).
Proof. exact (fun_ext (fun y : A => @lem1138495 A n x y)). Qed.
Lemma lem1138497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1138498 {A : Type'} (n : nat) (x : A) : (term64 A n x) = (term64 A n x).
Proof. exact (MK_COMB (@lem1138497 A) (@lem1138496 A n x)). Qed.
Lemma lem1138499 {A : Type'} (n : nat) : (term66 A n) = (term66 A n).
Proof. exact (fun_ext (fun x : A => @lem1138498 A n x)). Qed.
Lemma lem1138500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1138501 {A : Type'} (n : nat) : (term67 A n) = (term67 A n).
Proof. exact (MK_COMB (@lem1138500 A) (@lem1138499 A n)). Qed.
Lemma lem1138502 {A : Type'} : (term77 A) = (term77 A).
Proof. exact (fun_ext (fun n : nat => @lem1138501 A n)). Qed.
Lemma lem1138503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1138504 {A : Type'} : (term79 A) = (term79 A).
Proof. exact (MK_COMB (@lem1138503) (@lem1138502 A)). Qed.
Lemma lem1138529 {A : Type'} : (term78 A) = (term79 A).
Proof. exact (TRANS (@lem1138480 A) (@lem1138504 A)). Qed.
Lemma lem1138530 {A : Type'} : (term79 A) = (term78 A).
Proof. exact (SYM (@lem1138529 A)). Qed.
Lemma lem1138532 (p : Prop) : p = (term68 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1138533 {A : Type'} (n : nat) (x : A) (y : A) : ((term56 A x y n) = (x = y)) = (term80 A n x y).
Proof. exact (@lem1138532 ((term56 A x y n) = (x = y))). Qed.
Lemma lem1138534 {A : Type'} (n : nat) (x : A) (y : A) : (term80 A n x y) = ((term56 A x y n) = (x = y)).
Proof. exact (SYM (@lem1138533 A n x y)). Qed.
Lemma lem1138535 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term81 A n x y) : term81 A n x y.
Proof. exact (h1). Qed.
Lemma lem1138543 (n : nat) : (term82 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem1138545 {A : Type'} (x : A) (y : A) : (term83 A x y) = (term83 A x y).
Proof. exact (eq_refl (term83 A x y)). Qed.
Lemma lem1138546 {A : Type'} (x : A) (y : A) (n : nat) : (term84 A x y n) = (term85 A x y n).
Proof. exact (MK_COMB (@lem1138545 A x y) (@lem1138543 n)). Qed.
Lemma lem1138547 {A : Type'} (x : A) (y : A) (n : nat) : (term86 A x y n) = (term84 A x y n).
Proof. exact (@lem17045 (x = y) (term87 n)). Qed.
Lemma lem1138548 {A : Type'} (x : A) (y : A) (n : nat) : (term86 A x y n) = (term85 A x y n).
Proof. exact (TRANS (@lem1138547 A x y n) (@lem1138546 A x y n)). Qed.
Lemma lem1138553 {A : Type'} (x : A) (y : A) : (term88 A x y) = (term88 A x y).
Proof. exact (eq_refl (term88 A x y)). Qed.
Lemma lem1138554 {A : Type'} (x : A) (y : A) (n : nat) : (term89 A x y n) = (term90 A x y n).
Proof. exact (MK_COMB (@lem1138553 A x y) (@lem1138548 A x y n)). Qed.
Lemma lem1138555 {A : Type'} (x : A) (y : A) (n : nat) : (term91 A x y n) = (term89 A x y n).
Proof. exact (@lem17160 (x = y) (term47 A x y n)). Qed.
Lemma lem1138556 {A : Type'} (x : A) (y : A) (n : nat) : (term91 A x y n) = (term90 A x y n).
Proof. exact (TRANS (@lem1138555 A x y n) (@lem1138554 A x y n)). Qed.
Lemma lem1138561 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1138562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1138563 {A : Type'} (x : A) (y : A) (n : nat) : (term92 A x y n) = (term93 A x y n).
Proof. exact (MK_COMB (@lem1138562) (@lem1138556 A x y n)). Qed.
Lemma lem1138564 {A : Type'} (n : nat) (x : A) (y : A) : (term94 A n x y) = (term95 A n x y).
Proof. exact (MK_COMB (@lem1138563 A x y n) (@lem1138561 A x y)). Qed.
Lemma lem1138569 {A : Type'} (n : nat) (x : A) (y : A) : (term96 A n x y) = (term96 A n x y).
Proof. exact (eq_refl (term96 A n x y)). Qed.
Lemma lem1138570 {A : Type'} (n : nat) (x : A) (y : A) : (term97 A n x y) = (term98 A n x y).
Proof. exact (MK_COMB (@lem1138569 A n x y) (@lem1138564 A n x y)). Qed.
Lemma lem1138571 {A : Type'} (n : nat) (x : A) (y : A) : (term81 A n x y) = (term97 A n x y).
Proof. exact (@lem17646 (term56 A x y n) (x = y)). Qed.
Lemma lem1138576 {A : Type'} (n : nat) (x : A) (y : A) : (term81 A n x y) = (term98 A n x y).
Proof. exact (TRANS (@lem1138571 A n x y) (@lem1138570 A n x y)). Qed.
Lemma lem1138651 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term81 A n x y) : term98 A n x y.
Proof. exact (EQ_MP (@lem1138576 A n x y) (@lem1138535 A n x y h1)). Qed.
Lemma lem1138652 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) : term99 A n x y.
Proof. exact (h1). Qed.
Lemma lem1138653 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term95 A n x y.
Proof. exact (h1). Qed.
Lemma lem1138655 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) : term56 A x y n.
Proof. exact (proj1 (@lem1138652 A n x y h1)). Qed.
Lemma lem1138657 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term47 A x y n) : term47 A x y n.
Proof. exact (h1). Qed.
Lemma lem1138661 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term90 A x y n.
Proof. exact (proj1 (@lem1138653 A n x y h1)). Qed.
Lemma lem1138662 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term85 A x y n.
Proof. exact (proj2 (@lem1138661 A n x y h1)). Qed.
Lemma lem1138673 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1138711 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) : term100 A x y.
Proof. exact (proj2 (@lem1138652 A n x y h1)). Qed.
Lemma lem1138713 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1138715 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) : term100 A x y.
Proof. exact (proj2 (@lem1138652 A n x y h1)). Qed.
Lemma lem1138717 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term47 A x y n) : x = y.
Proof. exact (proj1 (@lem1138657 A x y n h1)). Qed.
Lemma lem1138721 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : x = y.
Proof. exact (proj2 (@lem1138653 A n x y h1)). Qed.
Lemma lem1138723 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term100 A x y.
Proof. exact (proj1 (@lem1138661 A n x y h1)). Qed.
Lemma lem1138725 {A : Type'} (x : A) (y : A) (h1 : term100 A x y) : term100 A x y.
Proof. exact (h1). Qed.
Lemma lem1138746 {A : Type'} (y : A) : (term101 A y) = (term101 A y).
Proof. exact (eq_refl (term101 A y)). Qed.
Lemma lem1138747 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term102 A y x) = (term103 A y).
Proof. exact (MK_COMB (@lem1138746 A y) (@lem1138713 A x y h1)). Qed.
Lemma lem1138748 {A : Type'} (y : A) : (term103 A y) = (term104 A y).
Proof. exact (eq_refl (term103 A y)). Qed.
Lemma lem1138749 {A : Type'} (y : A) (x : A) : (term105 A y x) = (term105 A y x).
Proof. exact (eq_refl (term105 A y x)). Qed.
Lemma lem1138750 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term102 A y x) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138749 A y x) (@lem1138748 A y)). Qed.
Lemma lem1138751 {A : Type'} (x : A) (y : A) : (term102 A y x) = (term100 A x y).
Proof. exact (eq_refl (term102 A y x)). Qed.
Lemma lem1138752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1138753 {A : Type'} (x : A) (y : A) : (term105 A y x) = (term106 A x y).
Proof. exact (MK_COMB (@lem1138752) (@lem1138751 A x y)). Qed.
Lemma lem1138754 {A : Type'} (y : A) : (term104 A y) = (term104 A y).
Proof. exact (eq_refl (term104 A y)). Qed.
Lemma lem1138755 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term104 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138753 A x y) (@lem1138754 A y)). Qed.
Lemma lem1138756 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (TRANS (@lem1138750 A x y) (@lem1138755 A x y)). Qed.
Lemma lem1138757 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term100 A x y) = (term104 A y).
Proof. exact (EQ_MP (@lem1138756 A x y) (@lem1138747 A x y h1)). Qed.
Lemma lem1138758 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : term104 A y.
Proof. exact (EQ_MP (@lem1138757 A x y h2) (@lem1138711 A n x y h1)). Qed.
Lemma lem1138773 {A : Type'} (y : A) : (term101 A y) = (term101 A y).
Proof. exact (eq_refl (term101 A y)). Qed.
Lemma lem1138774 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term47 A x y n) : (term102 A y x) = (term103 A y).
Proof. exact (MK_COMB (@lem1138773 A y) (@lem1138717 A x y n h1)). Qed.
Lemma lem1138775 {A : Type'} (y : A) : (term103 A y) = (term104 A y).
Proof. exact (eq_refl (term103 A y)). Qed.
Lemma lem1138776 {A : Type'} (y : A) (x : A) : (term105 A y x) = (term105 A y x).
Proof. exact (eq_refl (term105 A y x)). Qed.
Lemma lem1138777 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term102 A y x) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138776 A y x) (@lem1138775 A y)). Qed.
Lemma lem1138778 {A : Type'} (x : A) (y : A) : (term102 A y x) = (term100 A x y).
Proof. exact (eq_refl (term102 A y x)). Qed.
Lemma lem1138779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1138780 {A : Type'} (x : A) (y : A) : (term105 A y x) = (term106 A x y).
Proof. exact (MK_COMB (@lem1138779) (@lem1138778 A x y)). Qed.
Lemma lem1138781 {A : Type'} (y : A) : (term104 A y) = (term104 A y).
Proof. exact (eq_refl (term104 A y)). Qed.
Lemma lem1138782 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term104 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138780 A x y) (@lem1138781 A y)). Qed.
Lemma lem1138783 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (TRANS (@lem1138777 A x y) (@lem1138782 A x y)). Qed.
Lemma lem1138784 {A : Type'} (x : A) (y : A) (n : nat) (h1 : term47 A x y n) : (term100 A x y) = (term104 A y).
Proof. exact (EQ_MP (@lem1138783 A x y) (@lem1138774 A x y n h1)). Qed.
Lemma lem1138785 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term47 A x y n) (h2 : term99 A n x y) : term104 A y.
Proof. exact (EQ_MP (@lem1138784 A x y n h1) (@lem1138715 A n x y h2)). Qed.
Lemma lem1138827 {A : Type'} (y : A) : (term101 A y) = (term101 A y).
Proof. exact (eq_refl (term101 A y)). Qed.
Lemma lem1138828 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : (term102 A y x) = (term103 A y).
Proof. exact (MK_COMB (@lem1138827 A y) (@lem1138721 A n x y h1)). Qed.
Lemma lem1138829 {A : Type'} (y : A) : (term103 A y) = (term104 A y).
Proof. exact (eq_refl (term103 A y)). Qed.
Lemma lem1138830 {A : Type'} (y : A) (x : A) : (term105 A y x) = (term105 A y x).
Proof. exact (eq_refl (term105 A y x)). Qed.
Lemma lem1138831 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term102 A y x) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138830 A y x) (@lem1138829 A y)). Qed.
Lemma lem1138832 {A : Type'} (x : A) (y : A) : (term102 A y x) = (term100 A x y).
Proof. exact (eq_refl (term102 A y x)). Qed.
Lemma lem1138833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1138834 {A : Type'} (x : A) (y : A) : (term105 A y x) = (term106 A x y).
Proof. exact (MK_COMB (@lem1138833) (@lem1138832 A x y)). Qed.
Lemma lem1138835 {A : Type'} (y : A) : (term104 A y) = (term104 A y).
Proof. exact (eq_refl (term104 A y)). Qed.
Lemma lem1138836 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term104 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138834 A x y) (@lem1138835 A y)). Qed.
Lemma lem1138837 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (TRANS (@lem1138831 A x y) (@lem1138836 A x y)). Qed.
Lemma lem1138838 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : (term100 A x y) = (term104 A y).
Proof. exact (EQ_MP (@lem1138837 A x y) (@lem1138828 A n x y h1)). Qed.
Lemma lem1138839 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term100 A x y) (h2 : term95 A n x y) : term104 A y.
Proof. exact (EQ_MP (@lem1138838 A n x y h2) (@lem1138725 A x y h1)). Qed.
Lemma lem1138867 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : x = y.
Proof. exact (proj2 (@lem1138653 A n x y h1)). Qed.
Lemma lem1138881 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term100 A x y.
Proof. exact (proj1 (@lem1138661 A n x y h1)). Qed.
Lemma lem1138896 {A : Type'} (y : A) : (term101 A y) = (term101 A y).
Proof. exact (eq_refl (term101 A y)). Qed.
Lemma lem1138897 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : (term102 A y x) = (term103 A y).
Proof. exact (MK_COMB (@lem1138896 A y) (@lem1138867 A n x y h1)). Qed.
Lemma lem1138898 {A : Type'} (y : A) : (term103 A y) = (term104 A y).
Proof. exact (eq_refl (term103 A y)). Qed.
Lemma lem1138899 {A : Type'} (y : A) (x : A) : (term105 A y x) = (term105 A y x).
Proof. exact (eq_refl (term105 A y x)). Qed.
Lemma lem1138900 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term102 A y x) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138899 A y x) (@lem1138898 A y)). Qed.
Lemma lem1138901 {A : Type'} (x : A) (y : A) : (term102 A y x) = (term100 A x y).
Proof. exact (eq_refl (term102 A y x)). Qed.
Lemma lem1138902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1138903 {A : Type'} (x : A) (y : A) : (term105 A y x) = (term106 A x y).
Proof. exact (MK_COMB (@lem1138902) (@lem1138901 A x y)). Qed.
Lemma lem1138904 {A : Type'} (y : A) : (term104 A y) = (term104 A y).
Proof. exact (eq_refl (term104 A y)). Qed.
Lemma lem1138905 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term104 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (MK_COMB (@lem1138903 A x y) (@lem1138904 A y)). Qed.
Lemma lem1138906 {A : Type'} (x : A) (y : A) : ((term102 A y x) = (term103 A y)) = ((term100 A x y) = (term104 A y)).
Proof. exact (TRANS (@lem1138900 A x y) (@lem1138905 A x y)). Qed.
Lemma lem1138907 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : (term100 A x y) = (term104 A y).
Proof. exact (EQ_MP (@lem1138906 A x y) (@lem1138897 A n x y h1)). Qed.
Lemma lem1138908 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term104 A y.
Proof. exact (EQ_MP (@lem1138907 A n x y h1) (@lem1138881 A n x y h1)). Qed.
Lemma lem1138912 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1138913 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1138912 A x). Qed.
Lemma lem1138914 {A : Type'} (y : A) : y = y.
Proof. exact (@lem1138913 A y). Qed.
Lemma lem1138915 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term104 A y => @lem1138914 A y). Qed.
Lemma lem1138917 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1138918 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem1138917 (y = y)). Qed.
Lemma lem1138919 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem1138918 A y) (@lem1138915 A y)). Qed.
Lemma lem1138922 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1138924 {A : Type'} (y : A) : (term104 A y) = (term109 A y).
Proof. exact (@lem1138922 (y = y)). Qed.
Lemma lem1138927 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : term109 A y.
Proof. exact (EQ_MP (@lem1138924 A y) (@lem1138758 A n x y h1 h2)). Qed.
Lemma lem1138930 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : False.
Proof. exact (@lem1138927 A n x y h1 h2 (@lem1138919 A y)). Qed.
Lemma lem1138931 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : term110.
Proof. exact (fun h0 : ~ False => @lem1138930 A n x y h1 h2). Qed.
Lemma lem1138933 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1138934 : term110 = False.
Proof. exact (@lem1138933 False). Qed.
Lemma lem1138949 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1138950 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1138949 A x). Qed.
Lemma lem1138951 {A : Type'} (y : A) : y = y.
Proof. exact (@lem1138950 A y). Qed.
Lemma lem1138952 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term104 A y => @lem1138951 A y). Qed.
Lemma lem1138954 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1138955 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem1138954 (y = y)). Qed.
Lemma lem1138956 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem1138955 A y) (@lem1138952 A y)). Qed.
Lemma lem1138959 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1138961 {A : Type'} (y : A) : (term104 A y) = (term109 A y).
Proof. exact (@lem1138959 (y = y)). Qed.
Lemma lem1138964 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term47 A x y n) (h2 : term99 A n x y) : term109 A y.
Proof. exact (EQ_MP (@lem1138961 A y) (@lem1138785 A n x y h1 h2)). Qed.
Lemma lem1138967 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term47 A x y n) (h2 : term99 A n x y) : False.
Proof. exact (@lem1138964 A n x y h1 h2 (@lem1138956 A y)). Qed.
Lemma lem1138968 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term47 A x y n) (h2 : term99 A n x y) : term110.
Proof. exact (fun h0 : ~ False => @lem1138967 A n x y h1 h2). Qed.
Lemma lem1138970 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1138971 : term110 = False.
Proof. exact (@lem1138970 False). Qed.
Lemma lem1138976 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1138977 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1138976 A x). Qed.
Lemma lem1138978 {A : Type'} (y : A) : y = y.
Proof. exact (@lem1138977 A y). Qed.
Lemma lem1138979 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term104 A y => @lem1138978 A y). Qed.
Lemma lem1138981 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1138982 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem1138981 (y = y)). Qed.
Lemma lem1138983 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem1138982 A y) (@lem1138979 A y)). Qed.
Lemma lem1138986 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1138988 {A : Type'} (y : A) : (term104 A y) = (term109 A y).
Proof. exact (@lem1138986 (y = y)). Qed.
Lemma lem1138991 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term100 A x y) (h2 : term95 A n x y) : term109 A y.
Proof. exact (EQ_MP (@lem1138988 A y) (@lem1138839 A n x y h1 h2)). Qed.
Lemma lem1138994 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term100 A x y) (h2 : term95 A n x y) : False.
Proof. exact (@lem1138991 A n x y h1 h2 (@lem1138983 A y)). Qed.
Lemma lem1138995 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term100 A x y) (h2 : term95 A n x y) : term110.
Proof. exact (fun h0 : ~ False => @lem1138994 A n x y h1 h2). Qed.
Lemma lem1138997 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1138998 : term110 = False.
Proof. exact (@lem1138997 False). Qed.
Lemma lem1139003 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1139004 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1139003 A x). Qed.
Lemma lem1139005 {A : Type'} (y : A) : y = y.
Proof. exact (@lem1139004 A y). Qed.
Lemma lem1139006 {A : Type'} (y : A) : term107 A y.
Proof. exact (fun h0 : term104 A y => @lem1139005 A y). Qed.
Lemma lem1139008 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1139009 {A : Type'} (y : A) : (term107 A y) = (y = y).
Proof. exact (@lem1139008 (y = y)). Qed.
Lemma lem1139010 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem1139009 A y) (@lem1139006 A y)). Qed.
Lemma lem1139013 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1139015 {A : Type'} (y : A) : (term104 A y) = (term109 A y).
Proof. exact (@lem1139013 (y = y)). Qed.
Lemma lem1139018 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term109 A y.
Proof. exact (EQ_MP (@lem1139015 A y) (@lem1138908 A n x y h1)). Qed.
Lemma lem1139021 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : False.
Proof. exact (@lem1139018 A n x y h1 (@lem1139010 A y)). Qed.
Lemma lem1139022 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : term110.
Proof. exact (fun h0 : ~ False => @lem1139021 A n x y h1). Qed.
Lemma lem1139024 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1139025 : term110 = False.
Proof. exact (@lem1139024 False). Qed.
Lemma lem1139028 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : False.
Proof. exact (EQ_MP (@lem1139025) (@lem1139022 A n x y h1)). Qed.
Lemma lem1139029 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term100 A x y) (h2 : term95 A n x y) : False.
Proof. exact (EQ_MP (@lem1138998) (@lem1138995 A n x y h1 h2)). Qed.
Lemma lem1139030 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term47 A x y n) (h2 : term99 A n x y) : False.
Proof. exact (EQ_MP (@lem1138971) (@lem1138968 A n x y h1 h2)). Qed.
Lemma lem1139031 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1138934) (@lem1138931 A n x y h1 h2)). Qed.
Lemma lem1139032 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term100 A x y) (h2 : term95 A n x y) : (term100 A x y) = False.
Proof. exact (prop_ext (fun h3 : term100 A x y => @lem1139029 A n x y h1 h2) (fun h3 : False => @lem1138725 A x y h1)). Qed.
Lemma lem1139033 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term100 A x y) (h2 : term95 A n x y) : False.
Proof. exact (EQ_MP (@lem1139032 A n x y h1 h2) (@lem1138725 A x y h1)). Qed.
Lemma lem1139034 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : (term100 A x y) = False.
Proof. exact (prop_ext (fun h2 : term100 A x y => @lem1139033 A n x y h2 h1) (fun h2 : False => @lem1138723 A n x y h1)). Qed.
Lemma lem1139035 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : False.
Proof. exact (EQ_MP (@lem1139034 A n x y h1) (@lem1138723 A n x y h1)). Qed.
Lemma lem1139036 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1139031 A n x y h1 h2) (fun h3 : False => @lem1138713 A x y h2)). Qed.
Lemma lem1139037 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1139036 A n x y h1 h2) (@lem1138713 A x y h2)). Qed.
Lemma lem1139038 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1139037 A n x y h1 h2) (fun h3 : False => @lem1138673 A x y h2)). Qed.
Lemma lem1139039 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1139038 A n x y h1 h2) (@lem1138673 A x y h2)). Qed.
Lemma lem1139040 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1139039 A n x y h1 h2) (fun h3 : False => @lem1138673 A x y h2)). Qed.
Lemma lem1139041 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1139040 A n x y h1 h2) (@lem1138673 A x y h2)). Qed.
Lemma lem1139042 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term95 A n x y) : False.
Proof. exact (or_elim (@lem1138662 A n x y h1) (fun h0 : term100 A x y => @lem1139035 A n x y h1) (fun h0 : n = (NUMERAL 0) => @lem1139028 A n x y h1)). Qed.
Lemma lem1139043 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term99 A n x y) : False.
Proof. exact (or_elim (@lem1138655 A n x y h1) (fun h0 : x = y => @lem1139041 A n x y h1 h0) (fun h0 : term47 A x y n => @lem1139030 A n x y h0 h1)). Qed.
Lemma lem1139044 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term81 A n x y) : False.
Proof. exact (or_elim (@lem1138651 A n x y h1) (fun h0 : term99 A n x y => @lem1139043 A n x y h0) (fun h0 : term95 A n x y => @lem1139042 A n x y h0)). Qed.
Lemma lem1139045 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term81 A n x y) : (term81 A n x y) = False.
Proof. exact (prop_ext (fun h2 : term81 A n x y => @lem1139044 A n x y h1) (fun h2 : False => @lem1138535 A n x y h1)). Qed.
Lemma lem1139046 {A : Type'} (n : nat) (x : A) (y : A) (h1 : term81 A n x y) : False.
Proof. exact (EQ_MP (@lem1139045 A n x y h1) (@lem1138535 A n x y h1)). Qed.
Lemma lem1139047 {A : Type'} (n : nat) (x : A) (y : A) : term80 A n x y.
Proof. exact (fun h0 : term81 A n x y => @lem1139046 A n x y h0). Qed.
Lemma lem1139048 {A : Type'} (n : nat) (x : A) (y : A) : (term56 A x y n) = (x = y).
Proof. exact (EQ_MP (@lem1138534 A n x y) (@lem1139047 A n x y)). Qed.
Lemma lem1139053 {A : Type'} (n : nat) (x : A) : term64 A n x.
Proof. exact (fun y : A => @lem1139048 A n x y). Qed.
Lemma lem1139058 {A : Type'} (n : nat) : term67 A n.
Proof. exact (fun x : A => @lem1139053 A n x). Qed.
Lemma lem1139063 {A : Type'} : term79 A.
Proof. exact (fun n : nat => @lem1139058 A n). Qed.
Lemma lem1139064 {A : Type'} : term78 A.
Proof. exact (EQ_MP (@lem1138530 A) (@lem1139063 A)). Qed.
Lemma lem1139065 {A : Type'} (n : nat) : term111 A n.
Proof. exact (@lem1139064 A n). Qed.
Lemma lem1139066 {A : Type'} (n : nat) : (term111 A n) = (term69 A n).
Proof. exact (eq_refl (term111 A n)). Qed.
Lemma lem1139067 {A : Type'} (n : nat) : term69 A n.
Proof. exact (EQ_MP (@lem1139066 A n) (@lem1139065 A n)). Qed.
Lemma lem1139069 {A : Type'} (n : nat) : term69 A n.
Proof. exact (@lem1138446 A n (@lem1139067 A n)). Qed.
Lemma lem1139070 {A : Type'} (n : nat) (h1 : term70 A n) : False.
Proof. exact (@lem1139069 A n (@lem1138430 A n h1)). Qed.
Lemma lem1139071 {A : Type'} (n : nat) (h1 : term70 A n) : (term70 A n) = False.
Proof. exact (prop_ext (fun h2 : term70 A n => @lem1139070 A n h1) (fun h2 : False => @lem1138430 A n h1)). Qed.
Lemma lem1139072 {A : Type'} (n : nat) (h1 : term70 A n) : False.
Proof. exact (EQ_MP (@lem1139071 A n h1) (@lem1138430 A n h1)). Qed.
Lemma lem1139073 {A : Type'} (n : nat) : term69 A n.
Proof. exact (fun h0 : term70 A n => @lem1139072 A n h0). Qed.
Lemma lem1139074 {A : Type'} (n : nat) : term67 A n.
Proof. exact (EQ_MP (@lem1138429 A n) (@lem1139073 A n)). Qed.
Lemma lem1139075 {A : Type'} (n : nat) (h1 : term8 A n) : term12 A n.
Proof. exact (EQ_MP (@lem1138425 A n h1) (@lem1139074 A n)). Qed.
Lemma lem1139076 {A : Type'} (n : nat) : term14 A n.
Proof. exact (fun h0 : term8 A n => @lem1139075 A n h0). Qed.
Lemma lem1139081 {A : Type'} : term18 A.
Proof. exact (fun n : nat => @lem1139076 A n). Qed.
Lemma lem1139082 {A : Type'} : term20 A.
Proof. exact (conj (@lem1138321 A) (@lem1139081 A)). Qed.
Lemma lem1139083 {A : Type'} : term25 A.
Proof. exact (@lem1138233 A (@lem1139082 A)). Qed.
