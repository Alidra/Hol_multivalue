Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LDIV_LT_EQ_term_abbrevs.
Require Import LE_LDIV_EQ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem189163 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem189164 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem189163 n m h1)). Qed.
Lemma lem189165 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem189166 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem189165 m n h1)). Qed.
Lemma lem189167 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem189164 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem189166 m n h1)). Qed.
Lemma lem189168 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem189167 m n)). Qed.
Lemma lem189169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189170 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem189169) (@lem189168 m)). Qed.
Lemma lem189171 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem189170 m)). Qed.
Lemma lem189172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189173 : term7 = term8.
Proof. exact (MK_COMB (@lem189172) (@lem189171)). Qed.
Lemma lem189174 : term8.
Proof. exact (EQ_MP (@lem189173) (@lem97961)). Qed.
Lemma lem189175 (a : nat) : term9 a.
Proof. exact (@lem189160 a). Qed.
Lemma lem189176 (a : nat) : (term9 a) = (term10 a).
Proof. exact (eq_refl (term9 a)). Qed.
Lemma lem189177 (a : nat) : term10 a.
Proof. exact (EQ_MP (@lem189176 a) (@lem189175 a)). Qed.
Lemma lem189178 (a : nat) (b : nat) : term11 a b.
Proof. exact (@lem189177 a b). Qed.
Lemma lem189179 (b : nat) (a : nat) : (term11 a b) = (term12 b a).
Proof. exact (eq_refl (term11 a b)). Qed.
Lemma lem189180 (b : nat) (a : nat) : term12 b a.
Proof. exact (EQ_MP (@lem189179 b a) (@lem189178 a b)). Qed.
Lemma lem189181 (b : nat) (a : nat) (n : nat) : term13 b a n.
Proof. exact (@lem189180 b a n). Qed.
Lemma lem189182 (b : nat) (a : nat) (n : nat) : (term13 b a n) = (term14 b a n).
Proof. exact (eq_refl (term13 b a n)). Qed.
Lemma lem189183 (b : nat) (a : nat) (n : nat) : term14 b a n.
Proof. exact (EQ_MP (@lem189182 b a n) (@lem189181 b a n)). Qed.
Lemma lem189184 (a : nat) (h1 : term15 a) : term15 a.
Proof. exact (h1). Qed.
Lemma lem189185 (b : nat) (n : nat) (a : nat) (h1 : term15 a) : (term16 b a n) = (term17 b a n).
Proof. exact (@lem189183 b a n (@lem189184 a h1)). Qed.
Lemma lem189191 (m : nat) : term18 m.
Proof. exact (@lem189174 m). Qed.
Lemma lem189192 (m : nat) : (term18 m) = (term4 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem189193 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem189192 m) (@lem189191 m)). Qed.
Lemma lem189194 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem189193 m n). Qed.
Lemma lem189195 (m : nat) (n : nat) : (term19 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem189212 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem189213 (p : Prop) (q : Prop) (p' : Prop) : term21 p q p'.
Proof. exact (fun q' : Prop => @lem189212 p q p' q'). Qed.
Lemma lem189214 (p : Prop) (q : Prop) : term22 p q.
Proof. exact (fun p' : Prop => @lem189213 p q p'). Qed.
Lemma lem189215 (a : nat) (n : nat) (b : nat) : term23 a n b.
Proof. exact (@lem189214 (term15 a) ((term24 n b a) = (term25 a n b))). Qed.
Lemma lem189216 (a : nat) (n : nat) (b : nat) (p' : Prop) : term26 a n b p'.
Proof. exact (@lem189215 a n b p'). Qed.
Lemma lem189217 (a : nat) (n : nat) (b : nat) (p' : Prop) : (term26 a n b p') = (term27 a n b p').
Proof. exact (eq_refl (term26 a n b p')). Qed.
Lemma lem189218 (a : nat) (n : nat) (b : nat) (p' : Prop) : term27 a n b p'.
Proof. exact (EQ_MP (@lem189217 a n b p') (@lem189216 a n b p')). Qed.
Lemma lem189219 (a : nat) (n : nat) (b : nat) (p' : Prop) (q' : Prop) : term28 a n b p' q'.
Proof. exact (@lem189218 a n b p' q'). Qed.
Lemma lem189220 (a : nat) (n : nat) (b : nat) (p' : Prop) (q' : Prop) : (term28 a n b p' q') = (term29 a n b p' q').
Proof. exact (eq_refl (term28 a n b p' q')). Qed.
Lemma lem189221 (a : nat) (n : nat) (b : nat) (p' : Prop) (q' : Prop) : term29 a n b p' q'.
Proof. exact (EQ_MP (@lem189220 a n b p' q') (@lem189219 a n b p' q')). Qed.
Lemma lem189224 (a : nat) : (term15 a) = (term15 a).
Proof. exact (eq_refl (term15 a)). Qed.
Lemma lem189225 (n : nat) (b : nat) (a : nat) (q' : Prop) : term30 n b a q'.
Proof. exact (@lem189221 a n b (term15 a) q'). Qed.
Lemma lem189226 (n : nat) (b : nat) (a : nat) (q' : Prop) : term31 n b a q'.
Proof. exact (@lem189225 n b a q' (@lem189224 a)). Qed.
Lemma lem189227 (a : nat) (h1 : term15 a) : term15 a.
Proof. exact (h1). Qed.
Lemma lem189228 (a : nat) : term32 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem189244 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem189195 m n) (@lem189194 m n)). Qed.
Lemma lem189245 (b : nat) (a : nat) (n : nat) : (term24 n b a) = (term33 b a n).
Proof. exact (@lem189244 (Nat.div b a) n). Qed.
Lemma lem189247 (b : nat) (a : nat) (n : nat) : term14 b a n.
Proof. exact (fun h0 : term15 a => @lem189185 b n a h0). Qed.
Lemma lem189249 (a : nat) (h1 : term15 a) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem189228 a (@lem189227 a h1)). Qed.
Lemma lem189250 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189251 (a : nat) (h1 : term15 a) : (term15 a) = (~ False).
Proof. exact (MK_COMB (@lem189250) (@lem189249 a h1)). Qed.
Lemma lem189253 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem189254 (a : nat) (h1 : term15 a) : (term15 a) = True.
Proof. exact (TRANS (@lem189251 a h1) (@lem189253)). Qed.
Lemma lem189255 (a : nat) (h1 : term15 a) : True = (term15 a).
Proof. exact (SYM (@lem189254 a h1)). Qed.
Lemma lem189256 (a : nat) (h1 : term15 a) : term15 a.
Proof. exact (EQ_MP (@lem189255 a h1) (@lem0)). Qed.
Lemma lem189257 (b : nat) (n : nat) (a : nat) (h1 : term15 a) : (term16 b a n) = (term17 b a n).
Proof. exact (@lem189247 b a n (@lem189256 a h1)). Qed.
Lemma lem189259 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem189195 m n) (@lem189194 m n)). Qed.
Lemma lem189260 (a : nat) (n : nat) (b : nat) : (term17 b a n) = (term34 a n b).
Proof. exact (@lem189259 (term35 a n) b). Qed.
Lemma lem189261 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term16 b a n) = (term34 a n b).
Proof. exact (TRANS (@lem189257 b n a h1) (@lem189260 a n b)). Qed.
Lemma lem189262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189263 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term33 b a n) = (term36 a n b).
Proof. exact (MK_COMB (@lem189262) (@lem189261 n b a h1)). Qed.
Lemma lem189265 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem189266 (a : nat) (n : nat) (b : nat) : (term36 a n b) = (term25 a n b).
Proof. exact (@lem189265 (term25 a n b)). Qed.
Lemma lem189267 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term33 b a n) = (term25 a n b).
Proof. exact (TRANS (@lem189263 n b a h1) (@lem189266 a n b)). Qed.
Lemma lem189268 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term24 n b a) = (term25 a n b).
Proof. exact (TRANS (@lem189245 b a n) (@lem189267 n b a h1)). Qed.
Lemma lem189269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem189270 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : (term38 n b a) = (term39 a n b).
Proof. exact (MK_COMB (@lem189269) (@lem189268 n b a h1)). Qed.
Lemma lem189271 (a : nat) (n : nat) (b : nat) : (term25 a n b) = (term25 a n b).
Proof. exact (eq_refl (term25 a n b)). Qed.
Lemma lem189272 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : ((term24 n b a) = (term25 a n b)) = ((term25 a n b) = (term25 a n b)).
Proof. exact (MK_COMB (@lem189270 n b a h1) (@lem189271 a n b)). Qed.
Lemma lem189274 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem189275 (x : Prop) : (x = x) = True.
Proof. exact (@lem189274 Prop x). Qed.
Lemma lem189276 (a : nat) (n : nat) (b : nat) : ((term25 a n b) = (term25 a n b)) = True.
Proof. exact (@lem189275 (term25 a n b)). Qed.
Lemma lem189277 (n : nat) (b : nat) (a : nat) (h1 : term15 a) : ((term24 n b a) = (term25 a n b)) = True.
Proof. exact (TRANS (@lem189272 n b a h1) (@lem189276 a n b)). Qed.
Lemma lem189278 (a : nat) (n : nat) (b : nat) : term40 a n b.
Proof. exact (fun h0 : term15 a => @lem189277 n b a h0). Qed.
Lemma lem189279 (n : nat) (b : nat) (a : nat) : term41 n b a.
Proof. exact (@lem189226 n b a True). Qed.
Lemma lem189280 (n : nat) (b : nat) (a : nat) : (term42 a n b) = (term43 a).
Proof. exact (@lem189279 n b a (@lem189278 a n b)). Qed.
Lemma lem189282 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem189283 (a : nat) : (term43 a) = True.
Proof. exact (@lem189282 (term15 a)). Qed.
Lemma lem189284 (a : nat) (n : nat) (b : nat) : (term42 a n b) = True.
Proof. exact (TRANS (@lem189280 n b a) (@lem189283 a)). Qed.
Lemma lem189285 (a : nat) (b : nat) : (term44 a b) = term45.
Proof. exact (fun_ext (fun n : nat => @lem189284 a n b)). Qed.
Lemma lem189286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189287 (a : nat) (b : nat) : (term46 a b) = term47.
Proof. exact (MK_COMB (@lem189286) (@lem189285 a b)). Qed.
Lemma lem189289 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem189290 (t : Prop) : (term49 t) = t.
Proof. exact (@lem189289 nat t). Qed.
Lemma lem189291 : term47 = True.
Proof. exact (@lem189290 True). Qed.
Lemma lem189292 (a : nat) (b : nat) : (term46 a b) = True.
Proof. exact (TRANS (@lem189287 a b) (@lem189291)). Qed.
Lemma lem189293 (a : nat) : (term50 a) = term45.
Proof. exact (fun_ext (fun b : nat => @lem189292 a b)). Qed.
Lemma lem189294 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189295 (a : nat) : (term51 a) = term47.
Proof. exact (MK_COMB (@lem189294) (@lem189293 a)). Qed.
Lemma lem189297 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem189298 (t : Prop) : (term49 t) = t.
Proof. exact (@lem189297 nat t). Qed.
Lemma lem189299 : term47 = True.
Proof. exact (@lem189298 True). Qed.
Lemma lem189300 (a : nat) : (term51 a) = True.
Proof. exact (TRANS (@lem189295 a) (@lem189299)). Qed.
Lemma lem189301 : term52 = term45.
Proof. exact (fun_ext (fun a : nat => @lem189300 a)). Qed.
Lemma lem189302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189303 : term53 = term47.
Proof. exact (MK_COMB (@lem189302) (@lem189301)). Qed.
Lemma lem189305 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem189306 (t : Prop) : (term49 t) = t.
Proof. exact (@lem189305 nat t). Qed.
Lemma lem189307 : term47 = True.
Proof. exact (@lem189306 True). Qed.
Lemma lem189308 : term53 = True.
Proof. exact (TRANS (@lem189303) (@lem189307)). Qed.
Lemma lem189309 : True = term53.
Proof. exact (SYM (@lem189308)). Qed.
Lemma lem189310 : term53.
Proof. exact (EQ_MP (@lem189309) (@lem0)). Qed.
