Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm124360_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem124258 (ODD' : nat -> Prop) (h1 : (term0 ODD') = False) : (term0 ODD') = False.
Proof. exact (h1). Qed.
Lemma lem124259 (ODD' : nat -> Prop) (h1 : term1 ODD') : term1 ODD'.
Proof. exact (h1). Qed.
Lemma lem124260 (n : nat) (ODD' : nat -> Prop) (h1 : term1 ODD') : term2 ODD' n.
Proof. exact (@lem124259 ODD' h1 n). Qed.
Lemma lem124261 (ODD' : nat -> Prop) (n : nat) : (term2 ODD' n) = ((term3 ODD' n) = (term4 ODD' n)).
Proof. exact (eq_refl (term2 ODD' n)). Qed.
Lemma lem124262 (n : nat) (ODD' : nat -> Prop) (h1 : term1 ODD') : (term3 ODD' n) = (term4 ODD' n).
Proof. exact (EQ_MP (@lem124261 ODD' n) (@lem124260 n ODD' h1)). Qed.
Lemma lem124263 (ODD' : nat -> Prop) (h1 : term1 ODD') : term1 ODD'.
Proof. exact (fun n : nat => @lem124262 n ODD' h1). Qed.
Lemma lem124264 (ODD' : nat -> Prop) (h1 : term5 ODD') : term5 ODD'.
Proof. exact (h1). Qed.
Lemma lem124265 (ODD' : nat -> Prop) (h1 : term5 ODD') : term1 ODD'.
Proof. exact (proj2 (@lem124264 ODD' h1)). Qed.
Lemma lem124266 (ODD' : nat -> Prop) (h1 : term5 ODD') : (term0 ODD') = False.
Proof. exact (proj1 (@lem124264 ODD' h1)). Qed.
Lemma lem124267 (ODD' : nat -> Prop) (h1 : term5 ODD') : ((term0 ODD') = False) = ((term0 ODD') = False).
Proof. exact (prop_ext (fun h2 : (term0 ODD') = False => @lem124258 ODD' h2) (fun h2 : (term0 ODD') = False => @lem124266 ODD' h1)). Qed.
Lemma lem124268 (ODD' : nat -> Prop) (h1 : term5 ODD') : (term0 ODD') = False.
Proof. exact (EQ_MP (@lem124267 ODD' h1) (@lem124266 ODD' h1)). Qed.
Lemma lem124269 (ODD' : nat -> Prop) (h1 : term5 ODD') : (term1 ODD') = (term1 ODD').
Proof. exact (prop_ext (fun h2 : term1 ODD' => @lem124263 ODD' h2) (fun h2 : term1 ODD' => @lem124265 ODD' h1)). Qed.
Lemma lem124270 (ODD' : nat -> Prop) (h1 : term5 ODD') : term1 ODD'.
Proof. exact (EQ_MP (@lem124269 ODD' h1) (@lem124265 ODD' h1)). Qed.
Lemma lem124271 (ODD' : nat -> Prop) (h1 : term5 ODD') : term5 ODD'.
Proof. exact (conj (@lem124268 ODD' h1) (@lem124270 ODD' h1)). Qed.
Lemma lem124272 {A : Type'} (e : A) : term6 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem124273 {A : Type'} (e : A) : (term6 A e) = (term7 A e).
Proof. exact (eq_refl (term6 A e)). Qed.
Lemma lem124274 {A : Type'} (e : A) : term7 A e.
Proof. exact (EQ_MP (@lem124273 A e) (@lem124272 A e)). Qed.
Lemma lem124275 {A : Type'} (e : A) (f : type1423 A) : term8 A e f.
Proof. exact (@lem124274 A e f). Qed.
Lemma lem124276 {A : Type'} (e : A) (f : type1423 A) : (term8 A e f) = (term9 A e f).
Proof. exact (eq_refl (term8 A e f)). Qed.
Lemma lem124277 {A : Type'} (e : A) (f : type1423 A) : term9 A e f.
Proof. exact (EQ_MP (@lem124276 A e f) (@lem124275 A e f)). Qed.
Lemma lem124278 (e : Prop) (f : type1544) : term10 e f.
Proof. exact (@lem124277 Prop e f). Qed.
Lemma lem124279 : term11.
Proof. exact (@lem124278 False term12). Qed.
Lemma lem124280 (fn : nat -> Prop) (n : nat) : (term13 fn n) = (term14 fn n).
Proof. exact (eq_refl (term13 fn n)). Qed.
Lemma lem124281 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem124282 (fn : nat -> Prop) (n : nat) : (term15 fn n) = (term16 fn n).
Proof. exact (MK_COMB (@lem124280 fn n) (@lem124281 n)). Qed.
Lemma lem124283 (fn : nat -> Prop) (n : nat) : (term16 fn n) = (term4 fn n).
Proof. exact (eq_refl (term16 fn n)). Qed.
Lemma lem124284 (fn : nat -> Prop) (n : nat) : (term15 fn n) = (term4 fn n).
Proof. exact (TRANS (@lem124282 fn n) (@lem124283 fn n)). Qed.
Lemma lem124285 (fn : nat -> Prop) (n : nat) : (term17 fn n) = (term17 fn n).
Proof. exact (eq_refl (term17 fn n)). Qed.
Lemma lem124286 (fn : nat -> Prop) (n : nat) : ((term3 fn n) = (term15 fn n)) = ((term3 fn n) = (term4 fn n)).
Proof. exact (MK_COMB (@lem124285 fn n) (@lem124284 fn n)). Qed.
Lemma lem124287 (fn : nat -> Prop) : (term18 fn) = (term19 fn).
Proof. exact (fun_ext (fun n : nat => @lem124286 fn n)). Qed.
Lemma lem124288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124289 (fn : nat -> Prop) : (term20 fn) = (term1 fn).
Proof. exact (MK_COMB (@lem124288) (@lem124287 fn)). Qed.
Lemma lem124290 (fn : nat -> Prop) : (term21 fn) = (term21 fn).
Proof. exact (eq_refl (term21 fn)). Qed.
Lemma lem124291 (fn : nat -> Prop) : (term22 fn) = (term5 fn).
Proof. exact (MK_COMB (@lem124290 fn) (@lem124289 fn)). Qed.
Lemma lem124292 : term23 = term24.
Proof. exact (fun_ext (fun fn : nat -> Prop => @lem124291 fn)). Qed.
Lemma lem124293 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem124294 : term11 = term25.
Proof. exact (MK_COMB (@lem124293) (@lem124292)). Qed.
Lemma lem124295 : term25.
Proof. exact (EQ_MP (@lem124294) (@lem124279)). Qed.
Lemma lem124296 (ODD' : nat -> Prop) (h1 : term5 ODD') : term5 ODD'.
Proof. exact (h1). Qed.
Lemma lem124297 (ODD' : nat -> Prop) (h1 : term5 ODD') : term1 ODD'.
Proof. exact (proj2 (@lem124296 ODD' h1)). Qed.
Lemma lem124298 (ODD' : nat -> Prop) (h1 : term5 ODD') : (term0 ODD') = False.
Proof. exact (proj1 (@lem124296 ODD' h1)). Qed.
Lemma lem124299 (ODD' : nat -> Prop) (h1 : term5 ODD') : term5 ODD'.
Proof. exact (conj (@lem124298 ODD' h1) (@lem124297 ODD' h1)). Qed.
Lemma lem124300 (ODD' : nat -> Prop) (h1 : term5 ODD') : term25.
Proof. exact (ex_intro term24 ODD' (@lem124299 ODD' h1)). Qed.
Lemma lem124301 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem124302 (h1 : term25) : term25.
Proof. exact (ex_elim (@lem124301 h1) (fun ODD' : nat -> Prop => fun h0 : term24 ODD' => @lem124300 ODD' h0)). Qed.
Lemma lem124303 : term25 = term25.
Proof. exact (prop_ext (fun h1 : term25 => @lem124302 h1) (fun h1 : term25 => @lem124295)). Qed.
Lemma lem124304 : term25.
Proof. exact (EQ_MP (@lem124303) (@lem124295)). Qed.
Lemma lem124305 (ODD' : nat -> Prop) (h1 : term5 ODD') : term25.
Proof. exact (ex_intro term24 ODD' (@lem124271 ODD' h1)). Qed.
Lemma lem124306 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem124307 (h1 : term25) : term25.
Proof. exact (ex_elim (@lem124306 h1) (fun ODD' : nat -> Prop => fun h0 : term24 ODD' => @lem124305 ODD' h0)). Qed.
Lemma lem124308 : term25 = term25.
Proof. exact (prop_ext (fun h1 : term25 => @lem124307 h1) (fun h1 : term25 => @lem124304)). Qed.
Lemma lem124309 : term25.
Proof. exact (EQ_MP (@lem124308) (@lem124304)). Qed.
Lemma lem124312 (ODD' : nat -> Prop) (h1 : term5 ODD') : term5 ODD'.
Proof. exact (h1). Qed.
Lemma lem124313 (ODD' : nat -> Prop) (h1 : term5 ODD') : term25.
Proof. exact (ex_intro term24 ODD' (@lem124312 ODD' h1)). Qed.
Lemma lem124314 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem124315 (h1 : term25) : term25.
Proof. exact (ex_elim (@lem124314 h1) (fun ODD' : nat -> Prop => fun h0 : term24 ODD' => @lem124313 ODD' h0)). Qed.
Lemma lem124316 : term25 = term25.
Proof. exact (prop_ext (fun h1 : term25 => @lem124315 h1) (fun h1 : term25 => @lem124309)). Qed.
Lemma lem124317 : term25.
Proof. exact (EQ_MP (@lem124316) (@lem124309)). Qed.
Lemma lem124318 : term26.
Proof. exact (fun _2607 : type1674 => @lem124317). Qed.
Lemma lem124319 {A B : Type'} (P : type1413 A B) : term27 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem124320 {A B : Type'} (P : type1413 A B) : (term27 A B P) = ((term28 A B P) = (term29 A B P)).
Proof. exact (eq_refl (term27 A B P)). Qed.
Lemma lem124323 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem124320 A B P) (@lem124319 A B P)). Qed.
Lemma lem124324 (P : type1301) : (term30 P) = (term31 P).
Proof. exact (@lem124323 type1674 (nat -> Prop) P). Qed.
Lemma lem124325 : term32 = term33.
Proof. exact (@lem124324 term34). Qed.
Lemma lem124326 (_2607 : type1674) : (term35 _2607) = term24.
Proof. exact (eq_refl (term35 _2607)). Qed.
Lemma lem124327 (ODD' : nat -> Prop) : ODD' = ODD'.
Proof. exact (eq_refl ODD'). Qed.
Lemma lem124328 (_2607 : type1674) (ODD' : nat -> Prop) : (term36 _2607 ODD') = (term37 ODD').
Proof. exact (MK_COMB (@lem124326 _2607) (@lem124327 ODD')). Qed.
Lemma lem124329 (ODD' : nat -> Prop) : (term37 ODD') = (term5 ODD').
Proof. exact (eq_refl (term37 ODD')). Qed.
Lemma lem124330 (_2607 : type1674) (ODD' : nat -> Prop) : (term36 _2607 ODD') = (term5 ODD').
Proof. exact (TRANS (@lem124328 _2607 ODD') (@lem124329 ODD')). Qed.
Lemma lem124331 (_2607 : type1674) : (term38 _2607) = term24.
Proof. exact (fun_ext (fun ODD' : nat -> Prop => @lem124330 _2607 ODD')). Qed.
Lemma lem124332 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem124333 (_2607 : type1674) : (term39 _2607) = term25.
Proof. exact (MK_COMB (@lem124332) (@lem124331 _2607)). Qed.
Lemma lem124334 : term40 = term41.
Proof. exact (fun_ext (fun _2607 : type1674 => @lem124333 _2607)). Qed.
Lemma lem124335 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem124336 : term32 = term26.
Proof. exact (MK_COMB (@lem124335) (@lem124334)). Qed.
Lemma lem124337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124338 : term42 = term43.
Proof. exact (MK_COMB (@lem124337) (@lem124336)). Qed.
Lemma lem124339 (_2607 : type1674) : (term35 _2607) = term24.
Proof. exact (eq_refl (term35 _2607)). Qed.
Lemma lem124340 (ODD' : type1307) (_2607 : type1674) : (ODD' _2607) = (ODD' _2607).
Proof. exact (eq_refl (ODD' _2607)). Qed.
Lemma lem124341 (ODD' : type1307) (_2607 : type1674) : (term44 ODD' _2607) = (term45 ODD' _2607).
Proof. exact (MK_COMB (@lem124339 _2607) (@lem124340 ODD' _2607)). Qed.
Lemma lem124342 (ODD' : type1307) (_2607 : type1674) : (term45 ODD' _2607) = (term46 ODD' _2607).
Proof. exact (eq_refl (term45 ODD' _2607)). Qed.
Lemma lem124343 (ODD' : type1307) (_2607 : type1674) : (term44 ODD' _2607) = (term46 ODD' _2607).
Proof. exact (TRANS (@lem124341 ODD' _2607) (@lem124342 ODD' _2607)). Qed.
Lemma lem124344 (ODD' : type1307) : (term47 ODD') = (term48 ODD').
Proof. exact (fun_ext (fun _2607 : type1674 => @lem124343 ODD' _2607)). Qed.
Lemma lem124345 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem124346 (ODD' : type1307) : (term49 ODD') = (term50 ODD').
Proof. exact (MK_COMB (@lem124345) (@lem124344 ODD')). Qed.
Lemma lem124347 : term51 = term52.
Proof. exact (fun_ext (fun ODD' : type1307 => @lem124346 ODD')). Qed.
Lemma lem124348 : (@ex ((prod nat (prod nat nat)) -> nat -> Prop)) = (@ex ((prod nat (prod nat nat)) -> nat -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> nat -> Prop))). Qed.
Lemma lem124349 : term33 = term53.
Proof. exact (MK_COMB (@lem124348) (@lem124347)). Qed.
Lemma lem124350 : (term32 = term33) = (term26 = term53).
Proof. exact (MK_COMB (@lem124338) (@lem124349)). Qed.
Lemma lem124351 : term26 = term53.
Proof. exact (EQ_MP (@lem124350) (@lem124325)). Qed.
Lemma lem124352 : term53.
Proof. exact (EQ_MP (@lem124351) (@lem124318)). Qed.
Lemma lem124354 {A : Type'} : (@ex A) = (term54 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem124355 : (@ex ((prod nat (prod nat nat)) -> nat -> Prop)) = term55.
Proof. exact (@lem124354 type1307). Qed.
Lemma lem124356 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem124357 : term53 = term56.
Proof. exact (MK_COMB (@lem124355) (@lem124356)). Qed.
Lemma lem124358 : term56 = term57.
Proof. exact (eq_refl term56). Qed.
Lemma lem124359 : term53 = term57.
Proof. exact (TRANS (@lem124357) (@lem124358)). Qed.
Lemma lem124360 : term57.
Proof. exact (EQ_MP (@lem124359) (@lem124352)). Qed.
