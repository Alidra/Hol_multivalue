Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import option_RECURSION_term_abbrevs.
Require Import CONSTR_REC_spec.
Require Import thm1066561_spec.
Require Import thm1066562_spec.
Require Import thm1066568_spec.
Require Import thm1066569_spec.
Require Import thm1069367_spec.
Require Import thm1069415_spec.
Require Import thm1069419_spec.
Require Import thm1069766_spec.
Require Import thm1070118_spec.
Require Import thm9102_spec.
Lemma lem1070233 {A Z : Type'} (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : fn = (term0 A Z fn').
Proof. exact (h1). Qed.
Lemma lem1070234 {A Z : Type'} (fn : type1159 A Z) (fn' : type1337 A Z) (NONE' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NONE' = (term1 A)) : (fn (@None A)) = (term2 A Z fn' NONE').
Proof. exact (MK_COMB (@lem1070233 A Z fn fn' h1) (@lem1069766 A NONE' h2)). Qed.
Lemma lem1070235 {A Z : Type'} (a : A) (SOME' : type1432 A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (term5 A Z fn' SOME' a).
Proof. exact (MK_COMB (@lem1070233 A Z fn fn' h2) (@lem1070118 A a SOME' h1)). Qed.
Lemma lem1070236 {A Z : Type'} (fn : type1337 A Z) (NONE' : recspace A) : (term2 A Z fn NONE') = (term6 A Z fn NONE').
Proof. exact (eq_refl (term2 A Z fn NONE')). Qed.
Lemma lem1070237 {A Z : Type'} (fn : type1159 A Z) (fn' : type1337 A Z) (NONE' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NONE' = (term1 A)) : (fn (@None A)) = (term6 A Z fn' NONE').
Proof. exact (TRANS (@lem1070234 A Z fn fn' NONE' h1 h2) (@lem1070236 A Z fn' NONE')). Qed.
Lemma lem1070238 {A Z : Type'} (fn : type1337 A Z) (SOME' : type1432 A) (a : A) : (term5 A Z fn SOME' a) = (term7 A Z fn SOME' a).
Proof. exact (eq_refl (term5 A Z fn SOME' a)). Qed.
Lemma lem1070239 {A Z : Type'} (a : A) (SOME' : type1432 A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (term7 A Z fn' SOME' a).
Proof. exact (TRANS (@lem1070235 A Z a SOME' fn fn' h1 h2) (@lem1070238 A Z fn' SOME' a)). Qed.
Lemma lem1070247 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term8 A NONE' SOME')) : term9 A option' SOME'.
Proof. exact (proj2 (@lem1069367 A option' NONE' SOME' h1)). Qed.
Lemma lem1070250 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term8 A NONE' SOME')) : option' NONE'.
Proof. exact (proj1 (@lem1069367 A option' NONE' SOME' h1)). Qed.
Lemma lem1070252 {A : Type'} (r : recspace A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (option' r) = ((term10 A r) = r).
Proof. exact (TRANS (@lem1069419 A r option' SOME' NONE' h1 h2 h3) (@lem1069415 A r)). Qed.
Lemma lem1070253 {A : Type'} (r : recspace A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (option' r) = ((term10 A r) = r).
Proof. exact (@lem1070252 A r option' SOME' NONE' h1 h2 h3). Qed.
Lemma lem1070254 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (option' NONE') = ((term10 A NONE') = NONE').
Proof. exact (@lem1070253 A NONE' option' SOME' NONE' h1 h2 h3). Qed.
Lemma lem1070255 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (term10 A NONE') = NONE'.
Proof. exact (EQ_MP (@lem1070254 A option' SOME' NONE' h1 h2 h3) (@lem1070250 A option' NONE' SOME' h2)). Qed.
Lemma lem1070256 {A : Type'} (a : A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term8 A NONE' SOME')) : term11 A option' SOME' a.
Proof. exact (@lem1070247 A option' NONE' SOME' h1 a). Qed.
Lemma lem1070257 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (a : A) : (term11 A option' SOME' a) = (term12 A option' SOME' a).
Proof. exact (eq_refl (term11 A option' SOME' a)). Qed.
Lemma lem1070260 {A : Type'} (a : A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term8 A NONE' SOME')) : term12 A option' SOME' a.
Proof. exact (EQ_MP (@lem1070257 A option' SOME' a) (@lem1070256 A a option' NONE' SOME' h1)). Qed.
Lemma lem1070261 {A : Type'} (a : A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term8 A NONE' SOME')) : term12 A option' SOME' a.
Proof. exact (@lem1070260 A a option' NONE' SOME' h1). Qed.
Lemma lem1070263 {A : Type'} (r : recspace A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (option' r) = ((term10 A r) = r).
Proof. exact (TRANS (@lem1069419 A r option' SOME' NONE' h1 h2 h3) (@lem1069415 A r)). Qed.
Lemma lem1070264 {A : Type'} (r : recspace A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (option' r) = ((term10 A r) = r).
Proof. exact (@lem1070263 A r option' SOME' NONE' h1 h2 h3). Qed.
Lemma lem1070265 {A : Type'} (a : A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (term12 A option' SOME' a) = ((term13 A SOME' a) = (SOME' a)).
Proof. exact (@lem1070264 A (SOME' a) option' SOME' NONE' h1 h2 h3). Qed.
Lemma lem1070266 {A : Type'} (a : A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (term13 A SOME' a) = (SOME' a).
Proof. exact (EQ_MP (@lem1070265 A a option' SOME' NONE' h1 h2 h3) (@lem1070261 A a option' NONE' SOME' h2)). Qed.
Lemma lem1070267 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1070268 {A Z : Type'} (fn : type1337 A Z) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (term6 A Z fn NONE') = (fn NONE').
Proof. exact (MK_COMB (@lem1070267 A Z fn) (@lem1070255 A option' SOME' NONE' h1 h2 h3)). Qed.
Lemma lem1070269 {A Z : Type'} (fn : type1159 A Z) (fn' : type1337 A Z) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : option' = (term8 A NONE' SOME')) (h4 : NONE' = (term1 A)) : (fn (@None A)) = (fn' NONE').
Proof. exact (TRANS (@lem1070237 A Z fn fn' NONE' h2 h4) (@lem1070268 A Z fn' option' SOME' NONE' h1 h3 h4)). Qed.
Lemma lem1070270 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1070271 {A Z : Type'} (fn : type1337 A Z) (a : A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : option' = (term8 A NONE' SOME')) (h3 : NONE' = (term1 A)) : (term7 A Z fn SOME' a) = (term14 A Z fn SOME' a).
Proof. exact (MK_COMB (@lem1070270 A Z fn) (@lem1070266 A a option' SOME' NONE' h1 h2 h3)). Qed.
Lemma lem1070272 {A Z : Type'} (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : option' = (term8 A NONE' SOME')) (h4 : NONE' = (term1 A)) : (term4 A Z fn a) = (term14 A Z fn' SOME' a).
Proof. exact (TRANS (@lem1070239 A Z a SOME' fn fn' h1 h2) (@lem1070271 A Z fn' a option' SOME' NONE' h1 h3 h4)). Qed.
Lemma lem1070273 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term1 A)) : NONE' = (term1 A).
Proof. exact (h1). Qed.
Lemma lem1070274 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1070275 {A Z : Type'} (fn : type1337 A Z) (NONE' : recspace A) (h1 : NONE' = (term1 A)) : (fn NONE') = (term15 A Z fn).
Proof. exact (MK_COMB (@lem1070274 A Z fn) (@lem1070273 A NONE' h1)). Qed.
Lemma lem1070276 {A Z : Type'} (fn : type1159 A Z) (fn' : type1337 A Z) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : option' = (term8 A NONE' SOME')) (h4 : NONE' = (term1 A)) : (fn (@None A)) = (term15 A Z fn').
Proof. exact (TRANS (@lem1070269 A Z fn fn' option' SOME' NONE' h1 h2 h3 h4) (@lem1070275 A Z fn' NONE' h4)). Qed.
Lemma lem1070277 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term3 A)) : SOME' = (term3 A).
Proof. exact (h1). Qed.
Lemma lem1070278 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1070279 {A : Type'} (a : A) (SOME' : type1432 A) (h1 : SOME' = (term3 A)) : (SOME' a) = (term16 A a).
Proof. exact (MK_COMB (@lem1070277 A SOME' h1) (@lem1070278 A a)). Qed.
Lemma lem1070280 {A : Type'} (a : A) : (term16 A a) = (term17 A a).
Proof. exact (eq_refl (term16 A a)). Qed.
Lemma lem1070281 {A : Type'} (SOME' : type1432 A) (a : A) : (term18 A SOME' a) = (term18 A SOME' a).
Proof. exact (eq_refl (term18 A SOME' a)). Qed.
Lemma lem1070282 {A : Type'} (SOME' : type1432 A) (a : A) : ((SOME' a) = (term16 A a)) = ((SOME' a) = (term17 A a)).
Proof. exact (MK_COMB (@lem1070281 A SOME' a) (@lem1070280 A a)). Qed.
Lemma lem1070283 {A : Type'} (a : A) (SOME' : type1432 A) (h1 : SOME' = (term3 A)) : (SOME' a) = (term17 A a).
Proof. exact (EQ_MP (@lem1070282 A SOME' a) (@lem1070279 A a SOME' h1)). Qed.
Lemma lem1070284 {A Z : Type'} (fn : type1337 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1070285 {A Z : Type'} (fn : type1337 A Z) (a : A) (SOME' : type1432 A) (h1 : SOME' = (term3 A)) : (term14 A Z fn SOME' a) = (term19 A Z fn a).
Proof. exact (MK_COMB (@lem1070284 A Z fn) (@lem1070283 A a SOME' h1)). Qed.
Lemma lem1070286 {A Z : Type'} (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : option' = (term8 A NONE' SOME')) (h4 : NONE' = (term1 A)) : (term4 A Z fn a) = (term19 A Z fn' a).
Proof. exact (TRANS (@lem1070272 A Z a fn fn' option' SOME' NONE' h1 h2 h3 h4) (@lem1070285 A Z fn' a SOME' h1)). Qed.
Lemma lem1070287 {A Z : Type'} (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : option' = (term8 A NONE' SOME')) (h4 : NONE' = (term1 A)) : term20 A Z fn fn' a.
Proof. exact (conj (@lem1070276 A Z fn fn' option' SOME' NONE' h1 h2 h3 h4) (@lem1070286 A Z a fn fn' option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070288 {A Z : Type'} (option' : type1338 A) (a : A) (SOME' : type1432 A) (fn : type1159 A Z) (fn' : type1337 A Z) (NONE' : recspace A) (h1 : SOME' = (term3 A)) (h2 : fn = (term0 A Z fn')) (h3 : NONE' = (term1 A)) : term21 A Z option' NONE' SOME' fn fn' a.
Proof. exact (fun h0 : option' = (term8 A NONE' SOME') => @lem1070287 A Z a fn fn' option' SOME' NONE' h1 h2 h0 h3). Qed.
Lemma lem1070289 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1070290 {A Z : Type'} (option' : type1338 A) (SOME' : type1432 A) (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (NONE' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NONE' = (term1 A)) : term22 A Z option' NONE' SOME' fn fn' a.
Proof. exact (fun h0 : SOME' = (term3 A) => @lem1070288 A Z option' a SOME' fn fn' NONE' h0 h1 h2). Qed.
Lemma lem1070291 {A Z : Type'} (option' : type1338 A) (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (NONE' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NONE' = (term1 A)) : term23 A Z option' NONE' fn fn' a.
Proof. exact (@lem1070290 A Z option' (term3 A) a fn fn' NONE' h1 h2). Qed.
Lemma lem1070292 {A Z : Type'} (option' : type1338 A) (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (NONE' : recspace A) (h1 : fn = (term0 A Z fn')) (h2 : NONE' = (term1 A)) : term24 A Z option' NONE' fn fn' a.
Proof. exact (@lem1070291 A Z option' a fn fn' NONE' h1 h2 (@lem1070289 A)). Qed.
Lemma lem1070293 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem1070294 {A Z : Type'} (option' : type1338 A) (NONE' : recspace A) (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term25 A Z option' NONE' fn fn' a.
Proof. exact (fun h0 : NONE' = (term1 A) => @lem1070292 A Z option' a fn fn' NONE' h1 h0). Qed.
Lemma lem1070295 {A Z : Type'} (option' : type1338 A) (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term26 A Z option' fn fn' a.
Proof. exact (@lem1070294 A Z option' (term1 A) a fn fn' h1). Qed.
Lemma lem1070296 {A Z : Type'} (option' : type1338 A) (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term27 A Z option' fn fn' a.
Proof. exact (@lem1070295 A Z option' a fn fn' h1 (@lem1070293 A)). Qed.
Lemma lem1070297 {A : Type'} (option' : type1338 A) (h1 : option' = (term28 A)) : option' = (term28 A).
Proof. exact (h1). Qed.
Lemma lem1070298 {A Z : Type'} (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (option' : type1338 A) (h1 : fn = (term0 A Z fn')) (h2 : option' = (term28 A)) : term20 A Z fn fn' a.
Proof. exact (@lem1070296 A Z option' a fn fn' h1 (@lem1070297 A option' h2)). Qed.
Lemma lem1070299 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem1070300 {A Z : Type'} (option' : type1338 A) (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term27 A Z option' fn fn' a.
Proof. exact (fun h0 : option' = (term28 A) => @lem1070298 A Z a fn fn' option' h1 h0). Qed.
Lemma lem1070301 {A Z : Type'} (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term29 A Z fn fn' a.
Proof. exact (@lem1070300 A Z (term28 A) a fn fn' h1). Qed.
Lemma lem1070302 {A Z : Type'} (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : term20 A Z fn fn' a.
Proof. exact (@lem1070301 A Z a fn fn' h1 (@lem1070299 A)). Qed.
Lemma lem1070304 {A Z : Type'} : term30 A Z.
Proof. exact (@lem1065430 A Z). Qed.
Lemma lem1070305 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term31 A Z NONE' SOME'.
Proof. exact (@lem1070304 A Z (term32 A Z NONE' SOME')). Qed.
Lemma lem1070306 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : (term31 A Z NONE' SOME') = (term33 A Z NONE' SOME').
Proof. exact (eq_refl (term31 A Z NONE' SOME')). Qed.
Lemma lem1070307 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term33 A Z NONE' SOME'.
Proof. exact (EQ_MP (@lem1070306 A Z NONE' SOME') (@lem1070305 A Z NONE' SOME')). Qed.
Lemma lem1070308 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term34 A Z NONE' SOME' fn.
Proof. exact (h1). Qed.
Lemma lem1070309 {A Z : Type'} (c : nat) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term35 A Z NONE' SOME' fn c.
Proof. exact (@lem1070308 A Z NONE' SOME' fn h1 c). Qed.
Lemma lem1070310 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (c : nat) (fn : type1337 A Z) : (term35 A Z NONE' SOME' fn c) = (term36 A Z NONE' SOME' c fn).
Proof. exact (eq_refl (term35 A Z NONE' SOME' fn c)). Qed.
Lemma lem1070311 {A Z : Type'} (c : nat) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term36 A Z NONE' SOME' c fn.
Proof. exact (EQ_MP (@lem1070310 A Z NONE' SOME' c fn) (@lem1070309 A Z c NONE' SOME' fn h1)). Qed.
Lemma lem1070312 {A Z : Type'} (c : nat) (i : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term37 A Z NONE' SOME' c fn i.
Proof. exact (@lem1070311 A Z c NONE' SOME' fn h1 i). Qed.
Lemma lem1070313 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (c : nat) (i : A) (fn : type1337 A Z) : (term37 A Z NONE' SOME' c fn i) = (term38 A Z NONE' SOME' c i fn).
Proof. exact (eq_refl (term37 A Z NONE' SOME' c fn i)). Qed.
Lemma lem1070314 {A Z : Type'} (c : nat) (i : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term38 A Z NONE' SOME' c i fn.
Proof. exact (EQ_MP (@lem1070313 A Z NONE' SOME' c i fn) (@lem1070312 A Z c i NONE' SOME' fn h1)). Qed.
Lemma lem1070315 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term39 A Z NONE' SOME' c i fn r.
Proof. exact (@lem1070314 A Z c i NONE' SOME' fn h1 r). Qed.
Lemma lem1070316 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (c : nat) (i : A) (fn : type1337 A Z) (r : type1614 A) : (term39 A Z NONE' SOME' c i fn r) = ((term40 A Z fn c i r) = (term41 A Z NONE' SOME' c i fn r)).
Proof. exact (eq_refl (term39 A Z NONE' SOME' c i fn r)). Qed.
Lemma lem1070361 {A Z : Type'} (a : A) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (term19 A Z fn' a).
Proof. exact (proj2 (@lem1070302 A Z a fn fn' h1)). Qed.
Lemma lem1070362 {A Z : Type'} (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : fn = (term0 A Z fn')) : (fn (@None A)) = (term15 A Z fn').
Proof. exact (proj1 (@lem1070302 A Z (@el A) fn fn' h1)). Qed.
Lemma lem1070364 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : (term40 A Z fn c i r) = (term41 A Z NONE' SOME' c i fn r).
Proof. exact (EQ_MP (@lem1070316 A Z NONE' SOME' c i fn r) (@lem1070315 A Z c i r NONE' SOME' fn h1)). Qed.
Lemma lem1070365 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : (term40 A Z fn c i r) = (term41 A Z NONE' SOME' c i fn r).
Proof. exact (@lem1070364 A Z c i r NONE' SOME' fn h1). Qed.
Lemma lem1070366 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : (term15 A Z fn) = (term42 A Z NONE' SOME' fn).
Proof. exact (@lem1070365 A Z (NUMERAL 0) (term43 A) (term44 A) NONE' SOME' fn h1). Qed.
Lemma lem1070367 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (fn (@None A)) = (term42 A Z NONE' SOME' fn').
Proof. exact (TRANS (@lem1070362 A Z fn fn' h2) (@lem1070366 A Z NONE' SOME' fn' h1)). Qed.
Lemma lem1070369 {A : Type'} (f : nat -> A) (a : A) : (term45 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem1070370 {A Z : Type'} (f : type1592 A Z) (a : type1379 A Z) : (term46 A Z a f) = a.
Proof. exact (@lem1070369 (type1379 A Z) f a). Qed.
Lemma lem1070373 {A Z : Type'} (SOME' : A -> Z) (NONE' : Z) : (term47 A Z NONE' SOME') = (term48 A Z NONE').
Proof. exact (@lem1070370 A Z (term49 A Z SOME') (term48 A Z NONE')). Qed.
Lemma lem1070374 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (eq_refl (term43 A)). Qed.
Lemma lem1070375 {A Z : Type'} (SOME' : A -> Z) (NONE' : Z) : (term50 A Z NONE' SOME') = (term51 A Z NONE').
Proof. exact (MK_COMB (@lem1070373 A Z SOME' NONE') (@lem1070374 A)). Qed.
Lemma lem1070376 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (eq_refl (term44 A)). Qed.
Lemma lem1070377 {A Z : Type'} (SOME' : A -> Z) (NONE' : Z) : (term52 A Z NONE' SOME') = (term53 A Z NONE').
Proof. exact (MK_COMB (@lem1070375 A Z SOME' NONE') (@lem1070376 A)). Qed.
Lemma lem1070378 {A Z : Type'} (fn : type1337 A Z) : (term54 A Z fn) = (term54 A Z fn).
Proof. exact (eq_refl (term54 A Z fn)). Qed.
Lemma lem1070379 {A Z : Type'} (SOME' : A -> Z) (NONE' : Z) (fn : type1337 A Z) : (term42 A Z NONE' SOME' fn) = (term55 A Z NONE' fn).
Proof. exact (MK_COMB (@lem1070377 A Z SOME' NONE') (@lem1070378 A Z fn)). Qed.
Lemma lem1070380 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (fn (@None A)) = (term55 A Z NONE' fn').
Proof. exact (TRANS (@lem1070367 A Z NONE' SOME' fn fn' h1 h2) (@lem1070379 A Z SOME' NONE' fn')). Qed.
Lemma lem1070381 {A Z : Type'} (NONE' : Z) : (term51 A Z NONE') = (term56 A Z NONE').
Proof. exact (eq_refl (term51 A Z NONE')). Qed.
Lemma lem1070382 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (eq_refl (term44 A)). Qed.
Lemma lem1070383 {A Z : Type'} (NONE' : Z) : (term53 A Z NONE') = (term57 A Z NONE').
Proof. exact (MK_COMB (@lem1070381 A Z NONE') (@lem1070382 A)). Qed.
Lemma lem1070384 {A Z : Type'} (fn : type1337 A Z) : (term54 A Z fn) = (term54 A Z fn).
Proof. exact (eq_refl (term54 A Z fn)). Qed.
Lemma lem1070385 {A Z : Type'} (NONE' : Z) (fn : type1337 A Z) : (term55 A Z NONE' fn) = (term58 A Z NONE' fn).
Proof. exact (MK_COMB (@lem1070383 A Z NONE') (@lem1070384 A Z fn)). Qed.
Lemma lem1070386 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (fn (@None A)) = (term58 A Z NONE' fn').
Proof. exact (TRANS (@lem1070380 A Z NONE' SOME' fn fn' h1 h2) (@lem1070385 A Z NONE' fn')). Qed.
Lemma lem1070387 {A Z : Type'} (NONE' : Z) : (term57 A Z NONE') = (term59 Z NONE').
Proof. exact (eq_refl (term57 A Z NONE')). Qed.
Lemma lem1070388 {A Z : Type'} (fn : type1337 A Z) : (term54 A Z fn) = (term54 A Z fn).
Proof. exact (eq_refl (term54 A Z fn)). Qed.
Lemma lem1070389 {A Z : Type'} (NONE' : Z) (fn : type1337 A Z) : (term58 A Z NONE' fn) = (term60 A Z NONE' fn).
Proof. exact (MK_COMB (@lem1070387 A Z NONE') (@lem1070388 A Z fn)). Qed.
Lemma lem1070390 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (fn (@None A)) = (term60 A Z NONE' fn').
Proof. exact (TRANS (@lem1070386 A Z NONE' SOME' fn fn' h1 h2) (@lem1070389 A Z NONE' fn')). Qed.
Lemma lem1070391 {A Z : Type'} (fn : type1337 A Z) (NONE' : Z) : (term60 A Z NONE' fn) = NONE'.
Proof. exact (eq_refl (term60 A Z NONE' fn)). Qed.
Lemma lem1070394 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (fn (@None A)) = NONE'.
Proof. exact (TRANS (@lem1070390 A Z NONE' SOME' fn fn' h1 h2) (@lem1070391 A Z fn' NONE')). Qed.
Lemma lem1070396 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : (term40 A Z fn c i r) = (term41 A Z NONE' SOME' c i fn r).
Proof. exact (EQ_MP (@lem1070316 A Z NONE' SOME' c i fn r) (@lem1070315 A Z c i r NONE' SOME' fn h1)). Qed.
Lemma lem1070397 {A Z : Type'} (c : nat) (i : A) (r : type1614 A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : (term40 A Z fn c i r) = (term41 A Z NONE' SOME' c i fn r).
Proof. exact (@lem1070396 A Z c i r NONE' SOME' fn h1). Qed.
Lemma lem1070398 {A Z : Type'} (a : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : (term19 A Z fn a) = (term61 A Z NONE' SOME' a fn).
Proof. exact (@lem1070397 A Z term62 a (term44 A) NONE' SOME' fn h1). Qed.
Lemma lem1070399 {A Z : Type'} (a : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (term61 A Z NONE' SOME' a fn').
Proof. exact (TRANS (@lem1070361 A Z a fn fn' h2) (@lem1070398 A Z a NONE' SOME' fn' h1)). Qed.
Lemma lem1070401 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term63 A a f n) = (f n).
Proof. exact (EQ_MP (@lem1066562 A a f n) (@lem1066561 A a f n)). Qed.
Lemma lem1070402 {A Z : Type'} (a : type1379 A Z) (f : type1592 A Z) (n : nat) : (term64 A Z a f n) = (f n).
Proof. exact (@lem1070401 (type1379 A Z) a f n). Qed.
Lemma lem1070403 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : (term65 A Z NONE' SOME') = (term66 A Z SOME').
Proof. exact (@lem1070402 A Z (term48 A Z NONE') (term49 A Z SOME') (NUMERAL 0)). Qed.
Lemma lem1070405 {A : Type'} (f : nat -> A) (a : A) : (term45 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem1070406 {A Z : Type'} (f : type1592 A Z) (a : type1379 A Z) : (term46 A Z a f) = a.
Proof. exact (@lem1070405 (type1379 A Z) f a). Qed.
Lemma lem1070409 {A Z : Type'} (SOME' : A -> Z) : (term66 A Z SOME') = (term67 A Z SOME').
Proof. exact (@lem1070406 A Z (@FNIL (A -> (nat -> recspace A) -> (nat -> Z) -> Z)) (term67 A Z SOME')). Qed.
Lemma lem1070410 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : (term65 A Z NONE' SOME') = (term67 A Z SOME').
Proof. exact (TRANS (@lem1070403 A Z NONE' SOME') (@lem1070409 A Z SOME')). Qed.
Lemma lem1070411 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1070412 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (a : A) : (term68 A Z NONE' SOME' a) = (term69 A Z SOME' a).
Proof. exact (MK_COMB (@lem1070410 A Z NONE' SOME') (@lem1070411 A a)). Qed.
Lemma lem1070413 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (eq_refl (term44 A)). Qed.
Lemma lem1070414 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (a : A) : (term70 A Z NONE' SOME' a) = (term71 A Z SOME' a).
Proof. exact (MK_COMB (@lem1070412 A Z NONE' SOME' a) (@lem1070413 A)). Qed.
Lemma lem1070415 {A Z : Type'} (fn : type1337 A Z) : (term54 A Z fn) = (term54 A Z fn).
Proof. exact (eq_refl (term54 A Z fn)). Qed.
Lemma lem1070416 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (a : A) (fn : type1337 A Z) : (term61 A Z NONE' SOME' a fn) = (term72 A Z SOME' a fn).
Proof. exact (MK_COMB (@lem1070414 A Z NONE' SOME' a) (@lem1070415 A Z fn)). Qed.
Lemma lem1070417 {A Z : Type'} (a : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (term72 A Z SOME' a fn').
Proof. exact (TRANS (@lem1070399 A Z a NONE' SOME' fn fn' h1 h2) (@lem1070416 A Z NONE' SOME' a fn')). Qed.
Lemma lem1070418 {A Z : Type'} (SOME' : A -> Z) (a : A) : (term69 A Z SOME' a) = (term73 A Z SOME' a).
Proof. exact (eq_refl (term69 A Z SOME' a)). Qed.
Lemma lem1070419 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (eq_refl (term44 A)). Qed.
Lemma lem1070420 {A Z : Type'} (SOME' : A -> Z) (a : A) : (term71 A Z SOME' a) = (term74 A Z SOME' a).
Proof. exact (MK_COMB (@lem1070418 A Z SOME' a) (@lem1070419 A)). Qed.
Lemma lem1070421 {A Z : Type'} (fn : type1337 A Z) : (term54 A Z fn) = (term54 A Z fn).
Proof. exact (eq_refl (term54 A Z fn)). Qed.
Lemma lem1070422 {A Z : Type'} (SOME' : A -> Z) (a : A) (fn : type1337 A Z) : (term72 A Z SOME' a fn) = (term75 A Z SOME' a fn).
Proof. exact (MK_COMB (@lem1070420 A Z SOME' a) (@lem1070421 A Z fn)). Qed.
Lemma lem1070423 {A Z : Type'} (a : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (term75 A Z SOME' a fn').
Proof. exact (TRANS (@lem1070417 A Z a NONE' SOME' fn fn' h1 h2) (@lem1070422 A Z SOME' a fn')). Qed.
Lemma lem1070424 {A Z : Type'} (SOME' : A -> Z) (a : A) : (term74 A Z SOME' a) = (term76 A Z SOME' a).
Proof. exact (eq_refl (term74 A Z SOME' a)). Qed.
Lemma lem1070425 {A Z : Type'} (fn : type1337 A Z) : (term54 A Z fn) = (term54 A Z fn).
Proof. exact (eq_refl (term54 A Z fn)). Qed.
Lemma lem1070426 {A Z : Type'} (SOME' : A -> Z) (a : A) (fn : type1337 A Z) : (term75 A Z SOME' a fn) = (term77 A Z SOME' a fn).
Proof. exact (MK_COMB (@lem1070424 A Z SOME' a) (@lem1070425 A Z fn)). Qed.
Lemma lem1070427 {A Z : Type'} (a : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (term77 A Z SOME' a fn').
Proof. exact (TRANS (@lem1070423 A Z a NONE' SOME' fn fn' h1 h2) (@lem1070426 A Z SOME' a fn')). Qed.
Lemma lem1070428 {A Z : Type'} (fn : type1337 A Z) (SOME' : A -> Z) (a : A) : (term77 A Z SOME' a fn) = (SOME' a).
Proof. exact (eq_refl (term77 A Z SOME' a fn)). Qed.
Lemma lem1070431 {A Z : Type'} (a : A) (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : (term4 A Z fn a) = (SOME' a).
Proof. exact (TRANS (@lem1070427 A Z a NONE' SOME' fn fn' h1 h2) (@lem1070428 A Z fn' SOME' a)). Qed.
Lemma lem1070432 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : term78 A Z fn SOME'.
Proof. exact (fun a : A => @lem1070431 A Z a NONE' SOME' fn fn' h1 h2). Qed.
Lemma lem1070433 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : term79 A Z NONE' fn SOME'.
Proof. exact (conj (@lem1070394 A Z NONE' SOME' fn fn' h1 h2) (@lem1070432 A Z NONE' SOME' fn fn' h1 h2)). Qed.
Lemma lem1070434 {A Z : Type'} (NONE' : Z) (fn : type1159 A Z) (SOME' : A -> Z) : (term80 A Z NONE' SOME' fn) = (term79 A Z NONE' fn SOME').
Proof. exact (eq_refl (term80 A Z NONE' SOME' fn)). Qed.
Lemma lem1070435 {A Z : Type'} : term81 A Z.
Proof. exact (@lem9102 (type1159 A Z)). Qed.
Lemma lem1070436 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term82 A Z NONE' SOME'.
Proof. exact (@lem1070435 A Z (term83 A Z NONE' SOME')). Qed.
Lemma lem1070437 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : (term82 A Z NONE' SOME') = (term84 A Z NONE' SOME').
Proof. exact (eq_refl (term82 A Z NONE' SOME')). Qed.
Lemma lem1070438 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term84 A Z NONE' SOME'.
Proof. exact (EQ_MP (@lem1070437 A Z NONE' SOME') (@lem1070436 A Z NONE' SOME')). Qed.
Lemma lem1070439 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) : term85 A Z NONE' SOME' fn.
Proof. exact (@lem1070438 A Z NONE' SOME' (term0 A Z fn)). Qed.
Lemma lem1070440 {A Z : Type'} (fn : type1337 A Z) (NONE' : Z) (SOME' : A -> Z) : (term85 A Z NONE' SOME' fn) = (term86 A Z fn NONE' SOME').
Proof. exact (eq_refl (term85 A Z NONE' SOME' fn)). Qed.
Lemma lem1070441 {A Z : Type'} (fn : type1337 A Z) (NONE' : Z) (SOME' : A -> Z) : term86 A Z fn NONE' SOME'.
Proof. exact (EQ_MP (@lem1070440 A Z fn NONE' SOME') (@lem1070439 A Z NONE' SOME' fn)). Qed.
Lemma lem1070442 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) : (term79 A Z NONE' fn SOME') = (term80 A Z NONE' SOME' fn).
Proof. exact (SYM (@lem1070434 A Z NONE' fn SOME')). Qed.
Lemma lem1070443 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1159 A Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') (h2 : fn = (term0 A Z fn')) : term80 A Z NONE' SOME' fn.
Proof. exact (EQ_MP (@lem1070442 A Z NONE' SOME' fn) (@lem1070433 A Z NONE' SOME' fn fn' h1 h2)). Qed.
Lemma lem1070444 {A Z : Type'} (fn : type1159 A Z) (NONE' : Z) (SOME' : A -> Z) (fn' : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn') : term87 A Z fn' NONE' SOME' fn.
Proof. exact (fun h0 : fn = (term0 A Z fn') => @lem1070443 A Z NONE' SOME' fn fn' h1 h0). Qed.
Lemma lem1070445 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term88 A Z fn NONE' SOME'.
Proof. exact (fun fn' : type1159 A Z => @lem1070444 A Z fn' NONE' SOME' fn h1). Qed.
Lemma lem1070446 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) (fn : type1337 A Z) (h1 : term34 A Z NONE' SOME' fn) : term89 A Z NONE' SOME'.
Proof. exact (@lem1070441 A Z fn NONE' SOME' (@lem1070445 A Z NONE' SOME' fn h1)). Qed.
Lemma lem1070447 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term89 A Z NONE' SOME'.
Proof. exact (ex_elim (@lem1070307 A Z NONE' SOME') (fun fn : type1337 A Z => fun h0 : term90 A Z NONE' SOME' fn => @lem1070446 A Z NONE' SOME' fn h0)). Qed.
Lemma lem1070448 {A Z : Type'} (NONE' : Z) : term91 A Z NONE'.
Proof. exact (fun SOME' : A -> Z => @lem1070447 A Z NONE' SOME'). Qed.
Lemma lem1070449 {A Z : Type'} : term92 A Z.
Proof. exact (fun NONE' : Z => @lem1070448 A Z NONE'). Qed.
