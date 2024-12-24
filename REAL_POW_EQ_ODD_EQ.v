Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_ODD_EQ_term_abbrevs.
Require Import REAL_POW_LE2_ODD_EQ_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1665175 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (term0 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1665176 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (x = y) = (term0 y x).
Proof. exact (SYM (@lem1665175 x y h1)). Qed.
Lemma lem1665177 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (x = y) = (term0 y x).
Proof. exact (h1). Qed.
Lemma lem1665178 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (term0 y x) = (x = y).
Proof. exact (SYM (@lem1665177 y x h1)). Qed.
Lemma lem1665179 (y : real) (x : real) : ((term0 y x) = (x = y)) = ((x = y) = (term0 y x)).
Proof. exact (prop_ext (fun h1 : (term0 y x) = (x = y) => @lem1665176 x y h1) (fun h1 : (x = y) = (term0 y x) => @lem1665178 y x h1)). Qed.
Lemma lem1665180 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1665179 y x)). Qed.
Lemma lem1665181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665182 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1665181) (@lem1665180 x)). Qed.
Lemma lem1665183 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1665182 x)). Qed.
Lemma lem1665184 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665185 : term7 = term8.
Proof. exact (MK_COMB (@lem1665184) (@lem1665183)). Qed.
Lemma lem1665186 : term8.
Proof. exact (EQ_MP (@lem1665185) (@lem1339379)). Qed.
Lemma lem1665187 (n : nat) : term9 n.
Proof. exact (@lem1665172 n). Qed.
Lemma lem1665188 (n : nat) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem1665189 (n : nat) : term10 n.
Proof. exact (EQ_MP (@lem1665188 n) (@lem1665187 n)). Qed.
Lemma lem1665190 (n : nat) (x : real) : term11 n x.
Proof. exact (@lem1665189 n x). Qed.
Lemma lem1665191 (n : nat) (x : real) : (term11 n x) = (term12 n x).
Proof. exact (eq_refl (term11 n x)). Qed.
Lemma lem1665192 (n : nat) (x : real) : term12 n x.
Proof. exact (EQ_MP (@lem1665191 n x) (@lem1665190 n x)). Qed.
Lemma lem1665193 (n : nat) (x : real) (y : real) : term13 n x y.
Proof. exact (@lem1665192 n x y). Qed.
Lemma lem1665194 (n : nat) (x : real) (y : real) : (term13 n x y) = (term14 n x y).
Proof. exact (eq_refl (term13 n x y)). Qed.
Lemma lem1665195 (n : nat) (x : real) (y : real) : term14 n x y.
Proof. exact (EQ_MP (@lem1665194 n x y) (@lem1665193 n x y)). Qed.
Lemma lem1665196 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem1665197 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term15 x y n) = (real_le x y).
Proof. exact (@lem1665195 n x y (@lem1665196 n h1)). Qed.
Lemma lem1665203 (x : real) : term16 x.
Proof. exact (@lem1665186 x). Qed.
Lemma lem1665204 (x : real) : (term16 x) = (term4 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1665205 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1665204 x) (@lem1665203 x)). Qed.
Lemma lem1665206 (x : real) (y : real) : term17 x y.
Proof. exact (@lem1665205 x y). Qed.
Lemma lem1665207 (y : real) (x : real) : (term17 x y) = ((x = y) = (term0 y x)).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1665224 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term18 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1665225 (p : Prop) (q : Prop) (p' : Prop) : term19 p q p'.
Proof. exact (fun q' : Prop => @lem1665224 p q p' q'). Qed.
Lemma lem1665226 (p : Prop) (q : Prop) : term20 p q.
Proof. exact (fun p' : Prop => @lem1665225 p q p'). Qed.
Lemma lem1665227 (n : nat) (x : real) (y : real) : term21 n x y.
Proof. exact (@lem1665226 (Coq.Arith.PeanoNat.Nat.Odd n) (((real_pow x n) = (real_pow y n)) = (x = y))). Qed.
Lemma lem1665228 (n : nat) (x : real) (y : real) (p' : Prop) : term22 n x y p'.
Proof. exact (@lem1665227 n x y p'). Qed.
Lemma lem1665229 (n : nat) (x : real) (y : real) (p' : Prop) : (term22 n x y p') = (term23 n x y p').
Proof. exact (eq_refl (term22 n x y p')). Qed.
Lemma lem1665230 (n : nat) (x : real) (y : real) (p' : Prop) : term23 n x y p'.
Proof. exact (EQ_MP (@lem1665229 n x y p') (@lem1665228 n x y p')). Qed.
Lemma lem1665231 (n : nat) (x : real) (y : real) (p' : Prop) (q' : Prop) : term24 n x y p' q'.
Proof. exact (@lem1665230 n x y p' q'). Qed.
Lemma lem1665232 (n : nat) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term24 n x y p' q') = (term25 n x y p' q').
Proof. exact (eq_refl (term24 n x y p' q')). Qed.
Lemma lem1665233 (n : nat) (x : real) (y : real) (p' : Prop) (q' : Prop) : term25 n x y p' q'.
Proof. exact (EQ_MP (@lem1665232 n x y p' q') (@lem1665231 n x y p' q')). Qed.
Lemma lem1665234 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1665235 (x : real) (y : real) (n : nat) (q' : Prop) : term26 x y n q'.
Proof. exact (@lem1665233 n x y (Coq.Arith.PeanoNat.Nat.Odd n) q'). Qed.
Lemma lem1665236 (x : real) (y : real) (n : nat) (q' : Prop) : term27 x y n q'.
Proof. exact (@lem1665235 x y n q' (@lem1665234 n)). Qed.
Lemma lem1665237 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem1665238 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1665247 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem1665207 y x) (@lem1665206 x y)). Qed.
Lemma lem1665248 (y : real) (x : real) (n : nat) : ((real_pow x n) = (real_pow y n)) = (term28 y x n).
Proof. exact (@lem1665247 (real_pow y n) (real_pow x n)). Qed.
Lemma lem1665252 (n : nat) (x : real) (y : real) : term14 n x y.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1665197 x y n h0). Qed.
Lemma lem1665254 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (EQ_MP (@lem1665238 n) (@lem1665237 n h1)). Qed.
Lemma lem1665255 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : True = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem1665254 n h1)). Qed.
Lemma lem1665256 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem1665255 n h1) (@lem0)). Qed.
Lemma lem1665257 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term15 x y n) = (real_le x y).
Proof. exact (@lem1665252 n x y (@lem1665256 n h1)). Qed.
Lemma lem1665258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1665259 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term29 x y n) = (term30 x y).
Proof. exact (MK_COMB (@lem1665258) (@lem1665257 x y n h1)). Qed.
Lemma lem1665261 (n : nat) (x : real) (y : real) : term14 n x y.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1665197 x y n h0). Qed.
Lemma lem1665262 (n : nat) (y : real) (x : real) : term14 n y x.
Proof. exact (@lem1665261 n y x). Qed.
Lemma lem1665264 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (EQ_MP (@lem1665238 n) (@lem1665237 n h1)). Qed.
Lemma lem1665265 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : True = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem1665264 n h1)). Qed.
Lemma lem1665266 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem1665265 n h1) (@lem0)). Qed.
Lemma lem1665267 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term15 y x n) = (real_le y x).
Proof. exact (@lem1665262 n y x (@lem1665266 n h1)). Qed.
Lemma lem1665268 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term28 y x n) = (term0 y x).
Proof. exact (MK_COMB (@lem1665259 x y n h1) (@lem1665267 y x n h1)). Qed.
Lemma lem1665271 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : ((real_pow x n) = (real_pow y n)) = (term0 y x).
Proof. exact (TRANS (@lem1665248 y x n) (@lem1665268 y x n h1)). Qed.
Lemma lem1665272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1665273 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term31 x y n) = (term32 y x).
Proof. exact (MK_COMB (@lem1665272) (@lem1665271 y x n h1)). Qed.
Lemma lem1665279 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem1665207 y x) (@lem1665206 x y)). Qed.
Lemma lem1665282 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (((real_pow x n) = (real_pow y n)) = (x = y)) = ((term0 y x) = (term0 y x)).
Proof. exact (MK_COMB (@lem1665273 y x n h1) (@lem1665279 y x)). Qed.
Lemma lem1665284 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1665285 (x : Prop) : (x = x) = True.
Proof. exact (@lem1665284 Prop x). Qed.
Lemma lem1665286 (y : real) (x : real) : ((term0 y x) = (term0 y x)) = True.
Proof. exact (@lem1665285 (term0 y x)). Qed.
Lemma lem1665287 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (((real_pow x n) = (real_pow y n)) = (x = y)) = True.
Proof. exact (TRANS (@lem1665282 y x n h1) (@lem1665286 y x)). Qed.
Lemma lem1665288 (n : nat) (x : real) (y : real) : term33 n x y.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1665287 x y n h0). Qed.
Lemma lem1665289 (x : real) (y : real) (n : nat) : term34 x y n.
Proof. exact (@lem1665236 x y n True). Qed.
Lemma lem1665290 (x : real) (y : real) (n : nat) : (term35 n x y) = (term36 n).
Proof. exact (@lem1665289 x y n (@lem1665288 n x y)). Qed.
Lemma lem1665292 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1665293 (n : nat) : (term36 n) = True.
Proof. exact (@lem1665292 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1665294 (n : nat) (x : real) (y : real) : (term35 n x y) = True.
Proof. exact (TRANS (@lem1665290 x y n) (@lem1665293 n)). Qed.
Lemma lem1665295 (n : nat) (x : real) : (term37 n x) = term38.
Proof. exact (fun_ext (fun y : real => @lem1665294 n x y)). Qed.
Lemma lem1665296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665297 (n : nat) (x : real) : (term39 n x) = term40.
Proof. exact (MK_COMB (@lem1665296) (@lem1665295 n x)). Qed.
Lemma lem1665299 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1665300 (t : Prop) : (term42 t) = t.
Proof. exact (@lem1665299 real t). Qed.
Lemma lem1665301 : term40 = True.
Proof. exact (@lem1665300 True). Qed.
Lemma lem1665302 (n : nat) (x : real) : (term39 n x) = True.
Proof. exact (TRANS (@lem1665297 n x) (@lem1665301)). Qed.
Lemma lem1665303 (n : nat) : (term43 n) = term38.
Proof. exact (fun_ext (fun x : real => @lem1665302 n x)). Qed.
Lemma lem1665304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665305 (n : nat) : (term44 n) = term40.
Proof. exact (MK_COMB (@lem1665304) (@lem1665303 n)). Qed.
Lemma lem1665307 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1665308 (t : Prop) : (term42 t) = t.
Proof. exact (@lem1665307 real t). Qed.
Lemma lem1665309 : term40 = True.
Proof. exact (@lem1665308 True). Qed.
Lemma lem1665310 (n : nat) : (term44 n) = True.
Proof. exact (TRANS (@lem1665305 n) (@lem1665309)). Qed.
Lemma lem1665311 : term45 = term46.
Proof. exact (fun_ext (fun n : nat => @lem1665310 n)). Qed.
Lemma lem1665312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1665313 : term47 = term48.
Proof. exact (MK_COMB (@lem1665312) (@lem1665311)). Qed.
Lemma lem1665315 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1665316 (t : Prop) : (term49 t) = t.
Proof. exact (@lem1665315 nat t). Qed.
Lemma lem1665317 : term48 = True.
Proof. exact (@lem1665316 True). Qed.
Lemma lem1665318 : term47 = True.
Proof. exact (TRANS (@lem1665313) (@lem1665317)). Qed.
Lemma lem1665319 : True = term47.
Proof. exact (SYM (@lem1665318)). Qed.
Lemma lem1665320 : term47.
Proof. exact (EQ_MP (@lem1665319) (@lem0)). Qed.
