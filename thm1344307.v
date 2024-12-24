Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1344307_term_abbrevs.
Require Import thm1343684_spec.
Require Import thm1344256_spec.
Lemma lem1344257 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem1344258 : term1.
Proof. exact (EQ_MP (@lem1344257) (@lem1343684)). Qed.
Lemma lem1344259 : term2.
Proof. exact (@lem1344258 term3). Qed.
Lemma lem1344260 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem1344261 : term4.
Proof. exact (EQ_MP (@lem1344260) (@lem1344259)). Qed.
Lemma lem1344262 (h1 : real_pow = term5) : real_pow = term5.
Proof. exact (h1). Qed.
Lemma lem1344263 (h1 : real_pow = term5) : term5 = real_pow.
Proof. exact (SYM (@lem1344262 h1)). Qed.
Lemma lem1344264 (h1 : term5 = real_pow) : term5 = real_pow.
Proof. exact (h1). Qed.
Lemma lem1344265 (h1 : term5 = real_pow) : real_pow = term5.
Proof. exact (SYM (@lem1344264 h1)). Qed.
Lemma lem1344266 : (real_pow = term5) = (term5 = real_pow).
Proof. exact (prop_ext (fun h1 : real_pow = term5 => @lem1344263 h1) (fun h1 : term5 = real_pow => @lem1344265 h1)). Qed.
Lemma lem1344269 : term5 = real_pow.
Proof. exact (EQ_MP (@lem1344266) (@lem1344256)). Qed.
Lemma lem1344270 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1344271 (x : real) : (term6 x) = (real_pow x).
Proof. exact (MK_COMB (@lem1344269) (@lem1344270 x)). Qed.
Lemma lem1344272 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1344273 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1344271 x) (@lem1344272)). Qed.
Lemma lem1344274 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1344275 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1344274) (@lem1344273 x)). Qed.
Lemma lem1344276 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1344277 (x : real) : ((term7 x) = term11) = ((term8 x) = term11).
Proof. exact (MK_COMB (@lem1344275 x) (@lem1344276)). Qed.
Lemma lem1344278 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1344277 x)). Qed.
Lemma lem1344279 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1344280 : term14 = term15.
Proof. exact (MK_COMB (@lem1344279) (@lem1344278)). Qed.
Lemma lem1344281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1344282 : term16 = term17.
Proof. exact (MK_COMB (@lem1344281) (@lem1344280)). Qed.
Lemma lem1344284 : term5 = real_pow.
Proof. exact (EQ_MP (@lem1344266) (@lem1344256)). Qed.
Lemma lem1344285 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1344286 (x : real) : (term6 x) = (real_pow x).
Proof. exact (MK_COMB (@lem1344284) (@lem1344285 x)). Qed.
Lemma lem1344287 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1344288 (x : real) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem1344286 x) (@lem1344287 n)). Qed.
Lemma lem1344289 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1344290 (x : real) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem1344289) (@lem1344288 x n)). Qed.
Lemma lem1344292 : term5 = real_pow.
Proof. exact (EQ_MP (@lem1344266) (@lem1344256)). Qed.
Lemma lem1344293 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1344294 (x : real) : (term6 x) = (real_pow x).
Proof. exact (MK_COMB (@lem1344292) (@lem1344293 x)). Qed.
Lemma lem1344295 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1344296 (x : real) (n : nat) : (term22 x n) = (real_pow x n).
Proof. exact (MK_COMB (@lem1344294 x) (@lem1344295 n)). Qed.
Lemma lem1344297 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1344298 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (MK_COMB (@lem1344297 x) (@lem1344296 x n)). Qed.
Lemma lem1344299 (x : real) (n : nat) : ((term18 x n) = (term23 x n)) = ((term19 x n) = (term24 x n)).
Proof. exact (MK_COMB (@lem1344290 x n) (@lem1344298 x n)). Qed.
Lemma lem1344300 (x : real) : (term25 x) = (term26 x).
Proof. exact (fun_ext (fun n : nat => @lem1344299 x n)). Qed.
Lemma lem1344301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1344302 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1344301) (@lem1344300 x)). Qed.
Lemma lem1344303 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1344302 x)). Qed.
Lemma lem1344304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1344305 : term31 = term32.
Proof. exact (MK_COMB (@lem1344304) (@lem1344303)). Qed.
Lemma lem1344306 : term4 = term33.
Proof. exact (MK_COMB (@lem1344282) (@lem1344305)). Qed.
Lemma lem1344307 : term33.
Proof. exact (EQ_MP (@lem1344306) (@lem1344261)). Qed.
