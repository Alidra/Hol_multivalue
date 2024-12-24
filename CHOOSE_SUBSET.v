Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CHOOSE_SUBSET_term_abbrevs.
Require Import CHOOSE_SUBSET_STRONG_spec.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4085045 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4085046 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem4085045 (term1 A)). Qed.
Lemma lem4085047 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem4085046 A)). Qed.
Lemma lem4085048 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4085049 {A : Type'} : term4 A.
Proof. exact (@lem4083012 A). Qed.
Lemma lem4085055 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem4085056 {A : Type'} : term6 A.
Proof. exact (fun h0 : term5 A => @lem4085055 A h0). Qed.
Lemma lem4085057 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem4085058 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem4085059 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem4085057 A h2 (@lem4085058 A h1)). Qed.
Lemma lem4085060 {A : Type'} (h1 : term5 A) : term7 A.
Proof. exact (fun h0 : term6 A => @lem4085059 A h1 h0). Qed.
Lemma lem4085061 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem4085062 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem4085060 A h1 (@lem4085061 A h2)). Qed.
Lemma lem4085063 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (fun h0 : term5 A => @lem4085062 A h0 h1). Qed.
Lemma lem4085064 {A : Type'} : term8 A.
Proof. exact (fun h0 : term6 A => @lem4085063 A h0). Qed.
Lemma lem4085067 {A : Type'} : term6 A.
Proof. exact (@lem4085064 A (@lem4085056 A)). Qed.
Lemma lem4085068 {A : Type'} : term6 A.
Proof. exact (@lem4085067 A). Qed.
Lemma lem4085134 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4085135 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem4085134 (term4 A)). Qed.
Lemma lem4085198 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem4085205 {A : Type'} : (term5 A) = (term12 A).
Proof. exact (MK_COMB (@lem4085198 A) (@lem4085135 A)). Qed.
Lemma lem4085210 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term13 A s t n) = (term13 A s t n).
Proof. exact (eq_refl (term13 A s t n)). Qed.
Lemma lem4085211 {A : Type'} (s : A -> Prop) (n : nat) : (term14 A s n) = (term14 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085210 A s t n)). Qed.
Lemma lem4085212 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085213 {A : Type'} (s : A -> Prop) (n : nat) : (term15 A s n) = (term15 A s n).
Proof. exact (MK_COMB (@lem4085212 A) (@lem4085211 A s n)). Qed.
Lemma lem4085220 {A : Type'} (n : nat) (s : A -> Prop) : (term16 A n s) = (term16 A n s).
Proof. exact (eq_refl (term16 A n s)). Qed.
Lemma lem4085221 {A : Type'} (s : A -> Prop) (n : nat) : (term17 A s n) = (term17 A s n).
Proof. exact (MK_COMB (@lem4085220 A n s) (@lem4085213 A s n)). Qed.
Lemma lem4085222 {A : Type'} (n : nat) : (term18 A n) = (term18 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085221 A s n)). Qed.
Lemma lem4085223 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085224 {A : Type'} (n : nat) : (term19 A n) = (term19 A n).
Proof. exact (MK_COMB (@lem4085223 A) (@lem4085222 A n)). Qed.
Lemma lem4085225 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (fun_ext (fun n : nat => @lem4085224 A n)). Qed.
Lemma lem4085226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085227 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem4085226) (@lem4085225 A)). Qed.
Lemma lem4085228 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4085229 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem4085228) (@lem4085227 A)). Qed.
Lemma lem4085234 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term13 A s t n) = (term13 A s t n).
Proof. exact (eq_refl (term13 A s t n)). Qed.
Lemma lem4085235 {A : Type'} (s : A -> Prop) (n : nat) : (term14 A s n) = (term14 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085234 A s t n)). Qed.
Lemma lem4085236 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085237 {A : Type'} (s : A -> Prop) (n : nat) : (term15 A s n) = (term15 A s n).
Proof. exact (MK_COMB (@lem4085236 A) (@lem4085235 A s n)). Qed.
Lemma lem4085240 {A : Type'} (n : nat) (s : A -> Prop) : (term21 A n s) = (term21 A n s).
Proof. exact (eq_refl (term21 A n s)). Qed.
Lemma lem4085241 {A : Type'} (s : A -> Prop) (n : nat) : (term22 A s n) = (term22 A s n).
Proof. exact (MK_COMB (@lem4085240 A n s) (@lem4085237 A s n)). Qed.
Lemma lem4085242 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (fun_ext (fun n : nat => @lem4085241 A s n)). Qed.
Lemma lem4085243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085244 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem4085243) (@lem4085242 A s)). Qed.
Lemma lem4085247 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem4085248 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem4085247 A s) (@lem4085244 A s)). Qed.
Lemma lem4085249 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085248 A s)). Qed.
Lemma lem4085250 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085251 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem4085250 A) (@lem4085249 A)). Qed.
Lemma lem4085252 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4085253 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem4085252) (@lem4085251 A)). Qed.
Lemma lem4085254 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4085255 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem4085254) (@lem4085253 A)). Qed.
Lemma lem4085256 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem4085255 A) (@lem4085229 A)). Qed.
Lemma lem4085309 {A : Type'} : (term5 A) = (term12 A).
Proof. exact (TRANS (@lem4085205 A) (@lem4085256 A)). Qed.
Lemma lem4085310 {A : Type'} : (term12 A) = (term5 A).
Proof. exact (SYM (@lem4085309 A)). Qed.
Lemma lem4085311 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4085312 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem4085321 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term28 A s t n) = (term29 A s t n).
Proof. exact (@lem17045 (@SUBSET A t s) (@HAS_SIZE A t n)). Qed.
Lemma lem4085322 {A : Type'} (P : type686 A) : (term30 A P) = (term31 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4085323 {A : Type'} (s : A -> Prop) (n : nat) : (term32 A s n) = (term33 A s n).
Proof. exact (@lem4085322 A (term14 A s n)). Qed.
Lemma lem4085324 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term34 A s n t) = (term13 A s t n).
Proof. exact (eq_refl (term34 A s n t)). Qed.
Lemma lem4085325 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4085326 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term35 A s n t) = (term28 A s t n).
Proof. exact (MK_COMB (@lem4085325) (@lem4085324 A s t n)). Qed.
Lemma lem4085327 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term35 A s n t) = (term29 A s t n).
Proof. exact (TRANS (@lem4085326 A s t n) (@lem4085321 A s t n)). Qed.
Lemma lem4085328 {A : Type'} (s : A -> Prop) (n : nat) : (term36 A s n) = (term37 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085327 A s t n)). Qed.
Lemma lem4085329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085330 {A : Type'} (s : A -> Prop) (n : nat) : (term33 A s n) = (term38 A s n).
Proof. exact (MK_COMB (@lem4085329 A) (@lem4085328 A s n)). Qed.
Lemma lem4085331 {A : Type'} (s : A -> Prop) (n : nat) : (term32 A s n) = (term38 A s n).
Proof. exact (TRANS (@lem4085323 A s n) (@lem4085330 A s n)). Qed.
Lemma lem4085333 {A : Type'} (n : nat) (s : A -> Prop) : (term39 A n s) = (term39 A n s).
Proof. exact (eq_refl (term39 A n s)). Qed.
Lemma lem4085334 {A : Type'} (s : A -> Prop) (n : nat) : (term40 A s n) = (term41 A s n).
Proof. exact (MK_COMB (@lem4085333 A n s) (@lem4085331 A s n)). Qed.
Lemma lem4085335 {A : Type'} (s : A -> Prop) (n : nat) : (term42 A s n) = (term40 A s n).
Proof. exact (@lem17362 (term43 A n s) (term15 A s n)). Qed.
Lemma lem4085336 {A : Type'} (s : A -> Prop) (n : nat) : (term42 A s n) = (term41 A s n).
Proof. exact (TRANS (@lem4085335 A s n) (@lem4085334 A s n)). Qed.
Lemma lem4085337 (P : nat -> Prop) : (term44 P) = (term45 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4085338 {A : Type'} (s : A -> Prop) : (term46 A s) = (term47 A s).
Proof. exact (@lem4085337 (term23 A s)). Qed.
Lemma lem4085339 {A : Type'} (s : A -> Prop) (n : nat) : (term48 A s n) = (term22 A s n).
Proof. exact (eq_refl (term48 A s n)). Qed.
Lemma lem4085340 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4085341 {A : Type'} (s : A -> Prop) (n : nat) : (term49 A s n) = (term42 A s n).
Proof. exact (MK_COMB (@lem4085340) (@lem4085339 A s n)). Qed.
Lemma lem4085342 {A : Type'} (s : A -> Prop) (n : nat) : (term49 A s n) = (term41 A s n).
Proof. exact (TRANS (@lem4085341 A s n) (@lem4085336 A s n)). Qed.
Lemma lem4085343 {A : Type'} (s : A -> Prop) : (term50 A s) = (term51 A s).
Proof. exact (fun_ext (fun n : nat => @lem4085342 A s n)). Qed.
Lemma lem4085344 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4085345 {A : Type'} (s : A -> Prop) : (term47 A s) = (term52 A s).
Proof. exact (MK_COMB (@lem4085344) (@lem4085343 A s)). Qed.
Lemma lem4085346 {A : Type'} (s : A -> Prop) : (term46 A s) = (term52 A s).
Proof. exact (TRANS (@lem4085338 A s) (@lem4085345 A s)). Qed.
Lemma lem4085348 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem4085349 {A : Type'} (s : A -> Prop) : (term54 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem4085348 A s) (@lem4085346 A s)). Qed.
Lemma lem4085350 {A : Type'} (s : A -> Prop) : (term56 A s) = (term54 A s).
Proof. exact (@lem17362 (@FINITE A s) (term24 A s)). Qed.
Lemma lem4085351 {A : Type'} (s : A -> Prop) : (term56 A s) = (term55 A s).
Proof. exact (TRANS (@lem4085350 A s) (@lem4085349 A s)). Qed.
Lemma lem4085352 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4085353 {A : Type'} : (term3 A) = (term59 A).
Proof. exact (@lem4085352 A (term27 A)). Qed.
Lemma lem4085354 {A : Type'} (s : A -> Prop) : (term60 A s) = (term26 A s).
Proof. exact (eq_refl (term60 A s)). Qed.
Lemma lem4085355 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4085356 {A : Type'} (s : A -> Prop) : (term61 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem4085355) (@lem4085354 A s)). Qed.
Lemma lem4085357 {A : Type'} (s : A -> Prop) : (term61 A s) = (term55 A s).
Proof. exact (TRANS (@lem4085356 A s) (@lem4085351 A s)). Qed.
Lemma lem4085358 {A : Type'} : (term62 A) = (term63 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085357 A s)). Qed.
Lemma lem4085359 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085360 {A : Type'} : (term59 A) = (term64 A).
Proof. exact (MK_COMB (@lem4085359 A) (@lem4085358 A)). Qed.
Lemma lem4085361 {A : Type'} : (term3 A) = (term64 A).
Proof. exact (TRANS (@lem4085353 A) (@lem4085360 A)). Qed.
Lemma lem4085488 {A : Type'} (P : Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4085489 (P : Prop) (Q : nat -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem4085488 nat P Q). Qed.
Lemma lem4085490 {A : Type'} (s : A -> Prop) : (term69 A s) = (term70 A s).
Proof. exact (@lem4085489 (@FINITE A s) (term51 A s)). Qed.
Lemma lem4085491 {A : Type'} (s : A -> Prop) (n : nat) : (term71 A s n) = (term41 A s n).
Proof. exact (eq_refl (term71 A s n)). Qed.
Lemma lem4085492 {A : Type'} (s : A -> Prop) : (term72 A s) = (term51 A s).
Proof. exact (fun_ext (fun n : nat => @lem4085491 A s n)). Qed.
Lemma lem4085493 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4085494 {A : Type'} (s : A -> Prop) : (term73 A s) = (term52 A s).
Proof. exact (MK_COMB (@lem4085493) (@lem4085492 A s)). Qed.
Lemma lem4085495 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem4085496 {A : Type'} (s : A -> Prop) : (term69 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem4085495 A s) (@lem4085494 A s)). Qed.
Lemma lem4085497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4085498 {A : Type'} (s : A -> Prop) : (term74 A s) = (term75 A s).
Proof. exact (MK_COMB (@lem4085497) (@lem4085496 A s)). Qed.
Lemma lem4085499 {A : Type'} (s : A -> Prop) (n : nat) : (term71 A s n) = (term41 A s n).
Proof. exact (eq_refl (term71 A s n)). Qed.
Lemma lem4085500 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem4085501 {A : Type'} (s : A -> Prop) (n : nat) : (term76 A s n) = (term77 A s n).
Proof. exact (MK_COMB (@lem4085500 A s) (@lem4085499 A s n)). Qed.
Lemma lem4085502 {A : Type'} (s : A -> Prop) : (term78 A s) = (term79 A s).
Proof. exact (fun_ext (fun n : nat => @lem4085501 A s n)). Qed.
Lemma lem4085503 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4085504 {A : Type'} (s : A -> Prop) : (term70 A s) = (term80 A s).
Proof. exact (MK_COMB (@lem4085503) (@lem4085502 A s)). Qed.
Lemma lem4085505 {A : Type'} (s : A -> Prop) : ((term69 A s) = (term70 A s)) = ((term55 A s) = (term80 A s)).
Proof. exact (MK_COMB (@lem4085498 A s) (@lem4085504 A s)). Qed.
Lemma lem4085506 {A : Type'} (s : A -> Prop) : (term55 A s) = (term80 A s).
Proof. exact (EQ_MP (@lem4085505 A s) (@lem4085490 A s)). Qed.
Lemma lem4085507 {A : Type'} : (term63 A) = (term81 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085506 A s)). Qed.
Lemma lem4085508 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085510 {A : Type'} : (term64 A) = (term82 A).
Proof. exact (MK_COMB (@lem4085508 A) (@lem4085507 A)). Qed.
Lemma lem4085511 {A : Type'} : (term3 A) = (term82 A).
Proof. exact (TRANS (@lem4085361 A) (@lem4085510 A)). Qed.
Lemma lem4085512 {A : Type'} (h1 : term3 A) : term82 A.
Proof. exact (EQ_MP (@lem4085511 A) (@lem4085311 A h1)). Qed.
Lemma lem4085519 {A : Type'} (n : nat) (s : A -> Prop) : (term83 A n s) = (term84 A n s).
Proof. exact (@lem17362 (@FINITE A s) (term43 A n s)). Qed.
Lemma lem4085524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term13 A s t n) = (term13 A s t n).
Proof. exact (eq_refl (term13 A s t n)). Qed.
Lemma lem4085525 {A : Type'} (s : A -> Prop) (n : nat) : (term14 A s n) = (term14 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085524 A s t n)). Qed.
Lemma lem4085526 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085527 {A : Type'} (s : A -> Prop) (n : nat) : (term15 A s n) = (term15 A s n).
Proof. exact (MK_COMB (@lem4085526 A) (@lem4085525 A s n)). Qed.
Lemma lem4085528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4085529 {A : Type'} (n : nat) (s : A -> Prop) : (term85 A n s) = (term86 A n s).
Proof. exact (MK_COMB (@lem4085528) (@lem4085519 A n s)). Qed.
Lemma lem4085530 {A : Type'} (s : A -> Prop) (n : nat) : (term87 A s n) = (term88 A s n).
Proof. exact (MK_COMB (@lem4085529 A n s) (@lem4085527 A s n)). Qed.
Lemma lem4085531 {A : Type'} (s : A -> Prop) (n : nat) : (term17 A s n) = (term87 A s n).
Proof. exact (@lem17265 (term89 A n s) (term15 A s n)). Qed.
Lemma lem4085532 {A : Type'} (s : A -> Prop) (n : nat) : (term17 A s n) = (term88 A s n).
Proof. exact (TRANS (@lem4085531 A s n) (@lem4085530 A s n)). Qed.
Lemma lem4085533 {A : Type'} (n : nat) : (term18 A n) = (term90 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085532 A s n)). Qed.
Lemma lem4085534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085535 {A : Type'} (n : nat) : (term19 A n) = (term91 A n).
Proof. exact (MK_COMB (@lem4085534 A) (@lem4085533 A n)). Qed.
Lemma lem4085536 {A : Type'} : (term20 A) = (term92 A).
Proof. exact (fun_ext (fun n : nat => @lem4085535 A n)). Qed.
Lemma lem4085537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085538 {A : Type'} : (term4 A) = (term93 A).
Proof. exact (MK_COMB (@lem4085537) (@lem4085536 A)). Qed.
Lemma lem4085641 {A : Type'} (P : Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4085642 {A : Type'} (P : Prop) (Q : type686 A) : (term96 A P Q) = (term97 A P Q).
Proof. exact (@lem4085641 (A -> Prop) P Q). Qed.
Lemma lem4085643 {A : Type'} (s : A -> Prop) (n : nat) : (term98 A s n) = (term99 A s n).
Proof. exact (@lem4085642 A (term84 A n s) (term14 A s n)). Qed.
Lemma lem4085644 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term34 A s n t) = (term13 A s t n).
Proof. exact (eq_refl (term34 A s n t)). Qed.
Lemma lem4085645 {A : Type'} (s : A -> Prop) (n : nat) : (term100 A s n) = (term14 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085644 A s t n)). Qed.
Lemma lem4085646 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085647 {A : Type'} (s : A -> Prop) (n : nat) : (term101 A s n) = (term15 A s n).
Proof. exact (MK_COMB (@lem4085646 A) (@lem4085645 A s n)). Qed.
Lemma lem4085648 {A : Type'} (n : nat) (s : A -> Prop) : (term86 A n s) = (term86 A n s).
Proof. exact (eq_refl (term86 A n s)). Qed.
Lemma lem4085649 {A : Type'} (s : A -> Prop) (n : nat) : (term98 A s n) = (term88 A s n).
Proof. exact (MK_COMB (@lem4085648 A n s) (@lem4085647 A s n)). Qed.
Lemma lem4085650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4085651 {A : Type'} (s : A -> Prop) (n : nat) : (term102 A s n) = (term103 A s n).
Proof. exact (MK_COMB (@lem4085650) (@lem4085649 A s n)). Qed.
Lemma lem4085652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term34 A s n t) = (term13 A s t n).
Proof. exact (eq_refl (term34 A s n t)). Qed.
Lemma lem4085653 {A : Type'} (n : nat) (s : A -> Prop) : (term86 A n s) = (term86 A n s).
Proof. exact (eq_refl (term86 A n s)). Qed.
Lemma lem4085654 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term104 A s n t) = (term105 A s t n).
Proof. exact (MK_COMB (@lem4085653 A n s) (@lem4085652 A s t n)). Qed.
Lemma lem4085655 {A : Type'} (s : A -> Prop) (n : nat) : (term106 A s n) = (term107 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085654 A s t n)). Qed.
Lemma lem4085656 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085657 {A : Type'} (s : A -> Prop) (n : nat) : (term99 A s n) = (term108 A s n).
Proof. exact (MK_COMB (@lem4085656 A) (@lem4085655 A s n)). Qed.
Lemma lem4085658 {A : Type'} (s : A -> Prop) (n : nat) : ((term98 A s n) = (term99 A s n)) = ((term88 A s n) = (term108 A s n)).
Proof. exact (MK_COMB (@lem4085651 A s n) (@lem4085657 A s n)). Qed.
Lemma lem4085659 {A : Type'} (s : A -> Prop) (n : nat) : (term88 A s n) = (term108 A s n).
Proof. exact (EQ_MP (@lem4085658 A s n) (@lem4085643 A s n)). Qed.
Lemma lem4085660 {A : Type'} (n : nat) : (term90 A n) = (term109 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085659 A s n)). Qed.
Lemma lem4085661 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085662 {A : Type'} (n : nat) : (term91 A n) = (term110 A n).
Proof. exact (MK_COMB (@lem4085661 A) (@lem4085660 A n)). Qed.
Lemma lem4085664 {A B : Type'} (P : type1413 A B) : (term111 A B P) = (term112 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4085665 {A : Type'} (P : type639 A) : (term113 A P) = (term114 A P).
Proof. exact (@lem4085664 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem4085666 {A : Type'} (n : nat) : (term115 A n) = (term116 A n).
Proof. exact (@lem4085665 A (term117 A n)). Qed.
Lemma lem4085667 {A : Type'} (s : A -> Prop) (n : nat) : (term118 A n s) = (term107 A s n).
Proof. exact (eq_refl (term118 A n s)). Qed.
Lemma lem4085668 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4085669 {A : Type'} (s : A -> Prop) (n : nat) (t : A -> Prop) : (term119 A n s t) = (term120 A s n t).
Proof. exact (MK_COMB (@lem4085667 A s n) (@lem4085668 A t)). Qed.
Lemma lem4085670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term120 A s n t) = (term105 A s t n).
Proof. exact (eq_refl (term120 A s n t)). Qed.
Lemma lem4085671 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term119 A n s t) = (term105 A s t n).
Proof. exact (TRANS (@lem4085669 A s n t) (@lem4085670 A s t n)). Qed.
Lemma lem4085672 {A : Type'} (s : A -> Prop) (n : nat) : (term121 A n s) = (term107 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085671 A s t n)). Qed.
Lemma lem4085673 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4085674 {A : Type'} (s : A -> Prop) (n : nat) : (term122 A n s) = (term108 A s n).
Proof. exact (MK_COMB (@lem4085673 A) (@lem4085672 A s n)). Qed.
Lemma lem4085675 {A : Type'} (n : nat) : (term123 A n) = (term109 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085674 A s n)). Qed.
Lemma lem4085676 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085677 {A : Type'} (n : nat) : (term115 A n) = (term110 A n).
Proof. exact (MK_COMB (@lem4085676 A) (@lem4085675 A n)). Qed.
Lemma lem4085678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4085679 {A : Type'} (n : nat) : (term124 A n) = (term125 A n).
Proof. exact (MK_COMB (@lem4085678) (@lem4085677 A n)). Qed.
Lemma lem4085680 {A : Type'} (s : A -> Prop) (n : nat) : (term118 A n s) = (term107 A s n).
Proof. exact (eq_refl (term118 A n s)). Qed.
Lemma lem4085681 {A : Type'} (t : type672 A) (s : A -> Prop) : (t s) = (t s).
Proof. exact (eq_refl (t s)). Qed.
Lemma lem4085682 {A : Type'} (n : nat) (t : type672 A) (s : A -> Prop) : (term126 A n t s) = (term127 A n t s).
Proof. exact (MK_COMB (@lem4085680 A s n) (@lem4085681 A t s)). Qed.
Lemma lem4085683 {A : Type'} (t : type672 A) (s : A -> Prop) (n : nat) : (term127 A n t s) = (term128 A t s n).
Proof. exact (eq_refl (term127 A n t s)). Qed.
Lemma lem4085684 {A : Type'} (t : type672 A) (s : A -> Prop) (n : nat) : (term126 A n t s) = (term128 A t s n).
Proof. exact (TRANS (@lem4085682 A n t s) (@lem4085683 A t s n)). Qed.
Lemma lem4085685 {A : Type'} (t : type672 A) (n : nat) : (term129 A n t) = (term130 A t n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085684 A t s n)). Qed.
Lemma lem4085686 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085687 {A : Type'} (t : type672 A) (n : nat) : (term131 A n t) = (term132 A t n).
Proof. exact (MK_COMB (@lem4085686 A) (@lem4085685 A t n)). Qed.
Lemma lem4085688 {A : Type'} (n : nat) : (term133 A n) = (term134 A n).
Proof. exact (fun_ext (fun t : type672 A => @lem4085687 A t n)). Qed.
Lemma lem4085689 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem4085690 {A : Type'} (n : nat) : (term116 A n) = (term135 A n).
Proof. exact (MK_COMB (@lem4085689 A) (@lem4085688 A n)). Qed.
Lemma lem4085691 {A : Type'} (n : nat) : ((term115 A n) = (term116 A n)) = ((term110 A n) = (term135 A n)).
Proof. exact (MK_COMB (@lem4085679 A n) (@lem4085690 A n)). Qed.
Lemma lem4085692 {A : Type'} (n : nat) : (term110 A n) = (term135 A n).
Proof. exact (EQ_MP (@lem4085691 A n) (@lem4085666 A n)). Qed.
Lemma lem4085693 {A : Type'} (n : nat) : (term91 A n) = (term135 A n).
Proof. exact (TRANS (@lem4085662 A n) (@lem4085692 A n)). Qed.
Lemma lem4085694 {A : Type'} : (term92 A) = (term136 A).
Proof. exact (fun_ext (fun n : nat => @lem4085693 A n)). Qed.
Lemma lem4085695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085696 {A : Type'} : (term93 A) = (term137 A).
Proof. exact (MK_COMB (@lem4085695) (@lem4085694 A)). Qed.
Lemma lem4085698 {A B : Type'} (P : type1413 A B) : (term111 A B P) = (term112 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4085699 {A : Type'} (P : type1564 A) : (term138 A P) = (term139 A P).
Proof. exact (@lem4085698 nat (type672 A) P). Qed.
Lemma lem4085700 {A : Type'} : (term140 A) = (term141 A).
Proof. exact (@lem4085699 A (term142 A)). Qed.
Lemma lem4085701 {A : Type'} (n : nat) : (term143 A n) = (term134 A n).
Proof. exact (eq_refl (term143 A n)). Qed.
Lemma lem4085702 {A : Type'} (t : type672 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4085703 {A : Type'} (n : nat) (t : type672 A) : (term144 A n t) = (term145 A n t).
Proof. exact (MK_COMB (@lem4085701 A n) (@lem4085702 A t)). Qed.
Lemma lem4085704 {A : Type'} (t : type672 A) (n : nat) : (term145 A n t) = (term132 A t n).
Proof. exact (eq_refl (term145 A n t)). Qed.
Lemma lem4085705 {A : Type'} (t : type672 A) (n : nat) : (term144 A n t) = (term132 A t n).
Proof. exact (TRANS (@lem4085703 A n t) (@lem4085704 A t n)). Qed.
Lemma lem4085706 {A : Type'} (n : nat) : (term146 A n) = (term134 A n).
Proof. exact (fun_ext (fun t : type672 A => @lem4085705 A t n)). Qed.
Lemma lem4085707 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem4085708 {A : Type'} (n : nat) : (term147 A n) = (term135 A n).
Proof. exact (MK_COMB (@lem4085707 A) (@lem4085706 A n)). Qed.
Lemma lem4085709 {A : Type'} : (term148 A) = (term136 A).
Proof. exact (fun_ext (fun n : nat => @lem4085708 A n)). Qed.
Lemma lem4085710 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085711 {A : Type'} : (term140 A) = (term137 A).
Proof. exact (MK_COMB (@lem4085710) (@lem4085709 A)). Qed.
Lemma lem4085712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4085713 {A : Type'} : (term149 A) = (term150 A).
Proof. exact (MK_COMB (@lem4085712) (@lem4085711 A)). Qed.
Lemma lem4085714 {A : Type'} (n : nat) : (term143 A n) = (term134 A n).
Proof. exact (eq_refl (term143 A n)). Qed.
Lemma lem4085715 {A : Type'} (t : type1573 A) (n : nat) : (t n) = (t n).
Proof. exact (eq_refl (t n)). Qed.
Lemma lem4085716 {A : Type'} (t : type1573 A) (n : nat) : (term151 A t n) = (term152 A t n).
Proof. exact (MK_COMB (@lem4085714 A n) (@lem4085715 A t n)). Qed.
Lemma lem4085717 {A : Type'} (t : type1573 A) (n : nat) : (term152 A t n) = (term153 A t n).
Proof. exact (eq_refl (term152 A t n)). Qed.
Lemma lem4085718 {A : Type'} (t : type1573 A) (n : nat) : (term151 A t n) = (term153 A t n).
Proof. exact (TRANS (@lem4085716 A t n) (@lem4085717 A t n)). Qed.
Lemma lem4085719 {A : Type'} (t : type1573 A) : (term154 A t) = (term155 A t).
Proof. exact (fun_ext (fun n : nat => @lem4085718 A t n)). Qed.
Lemma lem4085720 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085721 {A : Type'} (t : type1573 A) : (term156 A t) = (term157 A t).
Proof. exact (MK_COMB (@lem4085720) (@lem4085719 A t)). Qed.
Lemma lem4085722 {A : Type'} : (term158 A) = (term159 A).
Proof. exact (fun_ext (fun t : type1573 A => @lem4085721 A t)). Qed.
Lemma lem4085723 {A : Type'} : (@ex (nat -> (A -> Prop) -> A -> Prop)) = (@ex (nat -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem4085724 {A : Type'} : (term141 A) = (term160 A).
Proof. exact (MK_COMB (@lem4085723 A) (@lem4085722 A)). Qed.
Lemma lem4085725 {A : Type'} : ((term140 A) = (term141 A)) = ((term137 A) = (term160 A)).
Proof. exact (MK_COMB (@lem4085713 A) (@lem4085724 A)). Qed.
Lemma lem4085726 {A : Type'} : (term137 A) = (term160 A).
Proof. exact (EQ_MP (@lem4085725 A) (@lem4085700 A)). Qed.
Lemma lem4085728 {A : Type'} : (term93 A) = (term160 A).
Proof. exact (TRANS (@lem4085696 A) (@lem4085726 A)). Qed.
Lemma lem4085729 {A : Type'} : (term4 A) = (term160 A).
Proof. exact (TRANS (@lem4085538 A) (@lem4085728 A)). Qed.
Lemma lem4085730 {A : Type'} (h1 : term4 A) : term160 A.
Proof. exact (EQ_MP (@lem4085729 A) (@lem4085312 A h1)). Qed.
Lemma lem4085731 {A : Type'} (t : type1573 A) (h1 : term157 A t) : term157 A t.
Proof. exact (h1). Qed.
Lemma lem4085732 {A : Type'} (s : A -> Prop) (h1 : term80 A s) : term80 A s.
Proof. exact (h1). Qed.
Lemma lem4085733 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term77 A s n.
Proof. exact (h1). Qed.
Lemma lem4085772 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) : (term161 A t s n) = (term161 A t s n).
Proof. exact (eq_refl (term161 A t s n)). Qed.
Lemma lem4085773 {A : Type'} (t : type1573 A) (n : nat) : (term162 A t n) = (term162 A t n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085772 A t s n)). Qed.
Lemma lem4085774 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085775 {A : Type'} (t : type1573 A) (n : nat) : (term153 A t n) = (term153 A t n).
Proof. exact (MK_COMB (@lem4085774 A) (@lem4085773 A t n)). Qed.
Lemma lem4085776 {A : Type'} (t : type1573 A) : (term155 A t) = (term155 A t).
Proof. exact (fun_ext (fun n : nat => @lem4085775 A t n)). Qed.
Lemma lem4085777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085778 {A : Type'} (t : type1573 A) : (term157 A t) = (term157 A t).
Proof. exact (MK_COMB (@lem4085777) (@lem4085776 A t)). Qed.
Lemma lem4085779 {A : Type'} (t : type1573 A) (h1 : term157 A t) : term157 A t.
Proof. exact (EQ_MP (@lem4085778 A t) (@lem4085731 A t h1)). Qed.
Lemma lem4085796 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term29 A s t n) = (term29 A s t n).
Proof. exact (eq_refl (term29 A s t n)). Qed.
Lemma lem4085797 {A : Type'} (s : A -> Prop) (n : nat) : (term37 A s n) = (term37 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085796 A s t n)). Qed.
Lemma lem4085798 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085799 {A : Type'} (s : A -> Prop) (n : nat) : (term38 A s n) = (term38 A s n).
Proof. exact (MK_COMB (@lem4085798 A) (@lem4085797 A s n)). Qed.
Lemma lem4085808 {A : Type'} (n : nat) (s : A -> Prop) : (term39 A n s) = (term39 A n s).
Proof. exact (eq_refl (term39 A n s)). Qed.
Lemma lem4085809 {A : Type'} (s : A -> Prop) (n : nat) : (term41 A s n) = (term41 A s n).
Proof. exact (MK_COMB (@lem4085808 A n s) (@lem4085799 A s n)). Qed.
Lemma lem4085814 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem4085815 {A : Type'} (s : A -> Prop) (n : nat) : (term77 A s n) = (term77 A s n).
Proof. exact (MK_COMB (@lem4085814 A s) (@lem4085809 A s n)). Qed.
Lemma lem4085816 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term77 A s n.
Proof. exact (EQ_MP (@lem4085815 A s n) (@lem4085733 A s n h1)). Qed.
Lemma lem4085817 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term41 A s n.
Proof. exact (proj2 (@lem4085816 A s n h1)). Qed.
Lemma lem4085819 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term38 A s n.
Proof. exact (proj2 (@lem4085817 A s n h1)). Qed.
Lemma lem4085835 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) : (term161 A t s n) = (term163 A t s n).
Proof. exact (@lem19490 (term164 A t n s) (term84 A n s) (term165 A t s n)). Qed.
Lemma lem4085842 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) : (term166 A t s n) = (term167 A t s n).
Proof. exact (@lem19699 (@FINITE A s) (term168 A n s) (term165 A t s n)). Qed.
Lemma lem4085849 {A : Type'} (t : type1573 A) (n : nat) (s : A -> Prop) : (term169 A t n s) = (term170 A t n s).
Proof. exact (@lem19699 (@FINITE A s) (term168 A n s) (term164 A t n s)). Qed.
Lemma lem4085850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4085851 {A : Type'} (t : type1573 A) (n : nat) (s : A -> Prop) : (term171 A t n s) = (term172 A t n s).
Proof. exact (MK_COMB (@lem4085850) (@lem4085849 A t n s)). Qed.
Lemma lem4085852 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) : (term163 A t s n) = (term173 A t s n).
Proof. exact (MK_COMB (@lem4085851 A t n s) (@lem4085842 A t s n)). Qed.
Lemma lem4085854 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) : (term161 A t s n) = (term173 A t s n).
Proof. exact (TRANS (@lem4085835 A t s n) (@lem4085852 A t s n)). Qed.
Lemma lem4085855 {A : Type'} (t : type1573 A) (n : nat) : (term162 A t n) = (term174 A t n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4085854 A t s n)). Qed.
Lemma lem4085856 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085857 {A : Type'} (t : type1573 A) (n : nat) : (term153 A t n) = (term175 A t n).
Proof. exact (MK_COMB (@lem4085856 A) (@lem4085855 A t n)). Qed.
Lemma lem4085858 {A : Type'} (t : type1573 A) : (term155 A t) = (term176 A t).
Proof. exact (fun_ext (fun n : nat => @lem4085857 A t n)). Qed.
Lemma lem4085859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4085861 {A : Type'} (t : type1573 A) : (term157 A t) = (term177 A t).
Proof. exact (MK_COMB (@lem4085859) (@lem4085858 A t)). Qed.
Lemma lem4085862 {A : Type'} (t : type1573 A) (h1 : term157 A t) : term177 A t.
Proof. exact (EQ_MP (@lem4085861 A t) (@lem4085779 A t h1)). Qed.
Lemma lem4085878 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term29 A s t n) = (term29 A s t n).
Proof. exact (eq_refl (term29 A s t n)). Qed.
Lemma lem4085879 {A : Type'} (s : A -> Prop) (n : nat) : (term37 A s n) = (term37 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4085878 A s t n)). Qed.
Lemma lem4085880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4085882 {A : Type'} (s : A -> Prop) (n : nat) : (term38 A s n) = (term38 A s n).
Proof. exact (MK_COMB (@lem4085880 A) (@lem4085879 A s n)). Qed.
Lemma lem4085883 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term38 A s n.
Proof. exact (EQ_MP (@lem4085882 A s n) (@lem4085819 A s n h1)). Qed.
Lemma lem4085884 {A : Type'} (_48221 : nat) (t : type1573 A) (h1 : term157 A t) : term178 A t _48221.
Proof. exact (@lem4085862 A t h1 _48221). Qed.
Lemma lem4085885 {A : Type'} (t : type1573 A) (_48221 : nat) : (term178 A t _48221) = (term175 A t _48221).
Proof. exact (eq_refl (term178 A t _48221)). Qed.
Lemma lem4085886 {A : Type'} (_48221 : nat) (t : type1573 A) (h1 : term157 A t) : term175 A t _48221.
Proof. exact (EQ_MP (@lem4085885 A t _48221) (@lem4085884 A _48221 t h1)). Qed.
Lemma lem4085887 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term179 A t _48221 _48222.
Proof. exact (@lem4085886 A _48221 t h1 _48222). Qed.
Lemma lem4085888 {A : Type'} (t : type1573 A) (_48222 : A -> Prop) (_48221 : nat) : (term179 A t _48221 _48222) = (term173 A t _48222 _48221).
Proof. exact (eq_refl (term179 A t _48221 _48222)). Qed.
Lemma lem4085889 {A : Type'} (_48222 : A -> Prop) (_48221 : nat) (t : type1573 A) (h1 : term157 A t) : term173 A t _48222 _48221.
Proof. exact (EQ_MP (@lem4085888 A t _48222 _48221) (@lem4085887 A _48221 _48222 t h1)). Qed.
Lemma lem4085890 {A : Type'} (_48223 : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term180 A s n _48223.
Proof. exact (@lem4085883 A s n h1 _48223). Qed.
Lemma lem4085891 {A : Type'} (s : A -> Prop) (_48223 : A -> Prop) (n : nat) : (term180 A s n _48223) = (term29 A s _48223 n).
Proof. exact (eq_refl (term180 A s n _48223)). Qed.
Lemma lem4085893 {A : Type'} (_48222 : A -> Prop) (_48221 : nat) (t : type1573 A) (h1 : term157 A t) : term167 A t _48222 _48221.
Proof. exact (proj2 (@lem4085889 A _48222 _48221 t h1)). Qed.
Lemma lem4085894 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term170 A t _48221 _48222.
Proof. exact (proj1 (@lem4085889 A _48222 _48221 t h1)). Qed.
Lemma lem4085908 {A : Type'} (_48223 : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term29 A s _48223 n.
Proof. exact (EQ_MP (@lem4085891 A s _48223 n) (@lem4085890 A _48223 s n h1)). Qed.
Lemma lem4085920 {A : Type'} (_48222 : A -> Prop) (_48221 : nat) (t : type1573 A) (h1 : term157 A t) : term181 A t _48222 _48221.
Proof. exact (proj2 (@lem4085893 A _48222 _48221 t h1)). Qed.
Lemma lem4085932 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term182 A t _48221 _48222.
Proof. exact (proj2 (@lem4085894 A _48221 _48222 t h1)). Qed.
Lemma lem4085934 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term43 A n s.
Proof. exact (proj1 (@lem4085817 A s n h1)). Qed.
Lemma lem4085935 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term183 A n s.
Proof. exact (fun h0 : term168 A n s => @lem4085934 A s n h1). Qed.
Lemma lem4085937 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4085938 {A : Type'} (n : nat) (s : A -> Prop) : (term183 A n s) = (term43 A n s).
Proof. exact (@lem4085937 (term43 A n s)). Qed.
Lemma lem4085939 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term43 A n s.
Proof. exact (EQ_MP (@lem4085938 A n s) (@lem4085935 A s n h1)). Qed.
Lemma lem4085945 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4085946 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term182 A t _48221 _48222) = (term185 A t _48221 _48222).
Proof. exact (@lem4085945 (term164 A t _48221 _48222) (term168 A _48221 _48222)). Qed.
Lemma lem4085952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4085953 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term186 A t _48221 _48222) = (term187 A t _48221 _48222).
Proof. exact (MK_COMB (@lem4085952) (@lem4085946 A t _48221 _48222)). Qed.
Lemma lem4085959 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term185 A t _48221 _48222) = (term185 A t _48221 _48222).
Proof. exact (eq_refl (term185 A t _48221 _48222)). Qed.
Lemma lem4085960 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : ((term182 A t _48221 _48222) = (term185 A t _48221 _48222)) = ((term185 A t _48221 _48222) = (term185 A t _48221 _48222)).
Proof. exact (MK_COMB (@lem4085953 A t _48221 _48222) (@lem4085959 A t _48221 _48222)). Qed.
Lemma lem4085962 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4085963 (x : Prop) : (x = x) = True.
Proof. exact (@lem4085962 Prop x). Qed.
Lemma lem4085964 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : ((term185 A t _48221 _48222) = (term185 A t _48221 _48222)) = True.
Proof. exact (@lem4085963 (term185 A t _48221 _48222)). Qed.
Lemma lem4085965 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : ((term182 A t _48221 _48222) = (term185 A t _48221 _48222)) = True.
Proof. exact (TRANS (@lem4085960 A t _48221 _48222) (@lem4085964 A t _48221 _48222)). Qed.
Lemma lem4085966 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : True = ((term182 A t _48221 _48222) = (term185 A t _48221 _48222)).
Proof. exact (SYM (@lem4085965 A t _48221 _48222)). Qed.
Lemma lem4085967 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term182 A t _48221 _48222) = (term185 A t _48221 _48222).
Proof. exact (EQ_MP (@lem4085966 A t _48221 _48222) (@lem0)). Qed.
Lemma lem4085968 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term185 A t _48221 _48222.
Proof. exact (EQ_MP (@lem4085967 A t _48221 _48222) (@lem4085932 A _48221 _48222 t h1)). Qed.
Lemma lem4085970 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4085971 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term185 A t _48221 _48222) = (term189 A t _48221 _48222).
Proof. exact (@lem4085970 (term168 A _48221 _48222) (term164 A t _48221 _48222)). Qed.
Lemma lem4085973 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4085974 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) : (term191 A _48221 _48222) = (term43 A _48221 _48222).
Proof. exact (@lem4085973 (term43 A _48221 _48222)). Qed.
Lemma lem4085975 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4085976 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) : (term192 A _48221 _48222) = (term21 A _48221 _48222).
Proof. exact (MK_COMB (@lem4085975) (@lem4085974 A _48221 _48222)). Qed.
Lemma lem4085977 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term164 A t _48221 _48222) = (term164 A t _48221 _48222).
Proof. exact (eq_refl (term164 A t _48221 _48222)). Qed.
Lemma lem4085978 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term189 A t _48221 _48222) = (term193 A t _48221 _48222).
Proof. exact (MK_COMB (@lem4085976 A _48221 _48222) (@lem4085977 A t _48221 _48222)). Qed.
Lemma lem4085979 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term185 A t _48221 _48222) = (term193 A t _48221 _48222).
Proof. exact (TRANS (@lem4085971 A t _48221 _48222) (@lem4085978 A t _48221 _48222)). Qed.
Lemma lem4085982 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term193 A t _48221 _48222.
Proof. exact (EQ_MP (@lem4085979 A t _48221 _48222) (@lem4085968 A _48221 _48222 t h1)). Qed.
Lemma lem4085983 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term193 A t _48221 _48222.
Proof. exact (@lem4085982 A _48221 _48222 t h1). Qed.
Lemma lem4085984 {A : Type'} (n : nat) (s : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term193 A t n s.
Proof. exact (@lem4085983 A n s t h1). Qed.
Lemma lem4085987 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term164 A t n s.
Proof. exact (@lem4085984 A n s t h1 (@lem4085939 A s n h2)). Qed.
Lemma lem4085988 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term194 A t n s.
Proof. exact (fun h0 : term195 A t n s => @lem4085987 A t s n h1 h2). Qed.
Lemma lem4085990 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4085991 {A : Type'} (t : type1573 A) (n : nat) (s : A -> Prop) : (term194 A t n s) = (term164 A t n s).
Proof. exact (@lem4085990 (term164 A t n s)). Qed.
Lemma lem4085992 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term164 A t n s.
Proof. exact (EQ_MP (@lem4085991 A t n s) (@lem4085988 A t s n h1 h2)). Qed.
Lemma lem4085994 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term43 A n s.
Proof. exact (proj1 (@lem4085817 A s n h1)). Qed.
Lemma lem4085995 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term183 A n s.
Proof. exact (fun h0 : term168 A n s => @lem4085994 A s n h1). Qed.
Lemma lem4085997 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4085998 {A : Type'} (n : nat) (s : A -> Prop) : (term183 A n s) = (term43 A n s).
Proof. exact (@lem4085997 (term43 A n s)). Qed.
Lemma lem4085999 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term43 A n s.
Proof. exact (EQ_MP (@lem4085998 A n s) (@lem4085995 A s n h1)). Qed.
Lemma lem4086005 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4086006 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term181 A t _48222 _48221) = (term196 A t _48221 _48222).
Proof. exact (@lem4086005 (term165 A t _48222 _48221) (term168 A _48221 _48222)). Qed.
Lemma lem4086012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4086013 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term197 A t _48222 _48221) = (term198 A t _48221 _48222).
Proof. exact (MK_COMB (@lem4086012) (@lem4086006 A t _48221 _48222)). Qed.
Lemma lem4086019 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term196 A t _48221 _48222) = (term196 A t _48221 _48222).
Proof. exact (eq_refl (term196 A t _48221 _48222)). Qed.
Lemma lem4086020 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : ((term181 A t _48222 _48221) = (term196 A t _48221 _48222)) = ((term196 A t _48221 _48222) = (term196 A t _48221 _48222)).
Proof. exact (MK_COMB (@lem4086013 A t _48221 _48222) (@lem4086019 A t _48221 _48222)). Qed.
Lemma lem4086022 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4086023 (x : Prop) : (x = x) = True.
Proof. exact (@lem4086022 Prop x). Qed.
Lemma lem4086024 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : ((term196 A t _48221 _48222) = (term196 A t _48221 _48222)) = True.
Proof. exact (@lem4086023 (term196 A t _48221 _48222)). Qed.
Lemma lem4086025 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : ((term181 A t _48222 _48221) = (term196 A t _48221 _48222)) = True.
Proof. exact (TRANS (@lem4086020 A t _48221 _48222) (@lem4086024 A t _48221 _48222)). Qed.
Lemma lem4086026 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : True = ((term181 A t _48222 _48221) = (term196 A t _48221 _48222)).
Proof. exact (SYM (@lem4086025 A t _48221 _48222)). Qed.
Lemma lem4086027 {A : Type'} (t : type1573 A) (_48221 : nat) (_48222 : A -> Prop) : (term181 A t _48222 _48221) = (term196 A t _48221 _48222).
Proof. exact (EQ_MP (@lem4086026 A t _48221 _48222) (@lem0)). Qed.
Lemma lem4086028 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) (t : type1573 A) (h1 : term157 A t) : term196 A t _48221 _48222.
Proof. exact (EQ_MP (@lem4086027 A t _48221 _48222) (@lem4085920 A _48222 _48221 t h1)). Qed.
Lemma lem4086030 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4086031 {A : Type'} (t : type1573 A) (_48222 : A -> Prop) (_48221 : nat) : (term196 A t _48221 _48222) = (term199 A t _48222 _48221).
Proof. exact (@lem4086030 (term168 A _48221 _48222) (term165 A t _48222 _48221)). Qed.
Lemma lem4086033 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4086034 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) : (term191 A _48221 _48222) = (term43 A _48221 _48222).
Proof. exact (@lem4086033 (term43 A _48221 _48222)). Qed.
Lemma lem4086035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4086036 {A : Type'} (_48221 : nat) (_48222 : A -> Prop) : (term192 A _48221 _48222) = (term21 A _48221 _48222).
Proof. exact (MK_COMB (@lem4086035) (@lem4086034 A _48221 _48222)). Qed.
Lemma lem4086037 {A : Type'} (t : type1573 A) (_48222 : A -> Prop) (_48221 : nat) : (term165 A t _48222 _48221) = (term165 A t _48222 _48221).
Proof. exact (eq_refl (term165 A t _48222 _48221)). Qed.
Lemma lem4086038 {A : Type'} (t : type1573 A) (_48222 : A -> Prop) (_48221 : nat) : (term199 A t _48222 _48221) = (term200 A t _48222 _48221).
Proof. exact (MK_COMB (@lem4086036 A _48221 _48222) (@lem4086037 A t _48222 _48221)). Qed.
Lemma lem4086039 {A : Type'} (t : type1573 A) (_48222 : A -> Prop) (_48221 : nat) : (term196 A t _48221 _48222) = (term200 A t _48222 _48221).
Proof. exact (TRANS (@lem4086031 A t _48222 _48221) (@lem4086038 A t _48222 _48221)). Qed.
Lemma lem4086042 {A : Type'} (_48222 : A -> Prop) (_48221 : nat) (t : type1573 A) (h1 : term157 A t) : term200 A t _48222 _48221.
Proof. exact (EQ_MP (@lem4086039 A t _48222 _48221) (@lem4086028 A _48221 _48222 t h1)). Qed.
Lemma lem4086043 {A : Type'} (_48222 : A -> Prop) (_48221 : nat) (t : type1573 A) (h1 : term157 A t) : term200 A t _48222 _48221.
Proof. exact (@lem4086042 A _48222 _48221 t h1). Qed.
Lemma lem4086044 {A : Type'} (s : A -> Prop) (n : nat) (t : type1573 A) (h1 : term157 A t) : term200 A t s n.
Proof. exact (@lem4086043 A s n t h1). Qed.
Lemma lem4086047 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term165 A t s n.
Proof. exact (@lem4086044 A s n t h1 (@lem4085999 A s n h2)). Qed.
Lemma lem4086048 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term201 A t s n.
Proof. exact (fun h0 : term202 A t s n => @lem4086047 A t s n h1 h2). Qed.
Lemma lem4086050 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4086051 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) : (term201 A t s n) = (term165 A t s n).
Proof. exact (@lem4086050 (term165 A t s n)). Qed.
Lemma lem4086052 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term165 A t s n.
Proof. exact (EQ_MP (@lem4086051 A t s n) (@lem4086048 A t s n h1 h2)). Qed.
Lemma lem4086054 (a : Prop) (b : Prop) : (term203 a b) = (term204 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4086055 {A : Type'} (s : A -> Prop) (_48223 : A -> Prop) (n : nat) : (term29 A s _48223 n) = (term28 A s _48223 n).
Proof. exact (@lem4086054 (@SUBSET A _48223 s) (@HAS_SIZE A _48223 n)). Qed.
Lemma lem4086057 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4086058 {A : Type'} (s : A -> Prop) (_48223 : A -> Prop) (n : nat) : (term28 A s _48223 n) = (term205 A s _48223 n).
Proof. exact (@lem4086057 (term13 A s _48223 n)). Qed.
Lemma lem4086059 {A : Type'} (s : A -> Prop) (_48223 : A -> Prop) (n : nat) : (term29 A s _48223 n) = (term205 A s _48223 n).
Proof. exact (TRANS (@lem4086055 A s _48223 n) (@lem4086058 A s _48223 n)). Qed.
Lemma lem4086061 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term206 A t s n.
Proof. exact (conj (@lem4085992 A t s n h1 h2) (@lem4086052 A t s n h1 h2)). Qed.
Lemma lem4086063 {A : Type'} (_48223 : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term205 A s _48223 n.
Proof. exact (EQ_MP (@lem4086059 A s _48223 n) (@lem4085908 A _48223 s n h1)). Qed.
Lemma lem4086064 {A : Type'} (_48223 : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term205 A s _48223 n.
Proof. exact (@lem4086063 A _48223 s n h1). Qed.
Lemma lem4086065 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term77 A s n) : term207 A t s n.
Proof. exact (@lem4086064 A (t n s) s n h1). Qed.
Lemma lem4086068 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : False.
Proof. exact (@lem4086065 A t s n h2 (@lem4086061 A t s n h1 h2)). Qed.
Lemma lem4086069 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : term208.
Proof. exact (fun h0 : ~ False => @lem4086068 A t s n h1 h2). Qed.
Lemma lem4086071 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4086072 : term208 = False.
Proof. exact (@lem4086071 False). Qed.
Lemma lem4086073 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : False.
Proof. exact (EQ_MP (@lem4086072) (@lem4086069 A t s n h1 h2)). Qed.
Lemma lem4086074 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : (term77 A s n) = False.
Proof. exact (prop_ext (fun h3 : term77 A s n => @lem4086073 A t s n h1 h2) (fun h3 : False => @lem4085816 A s n h2)). Qed.
Lemma lem4086075 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : False.
Proof. exact (EQ_MP (@lem4086074 A t s n h1 h2) (@lem4085816 A s n h2)). Qed.
Lemma lem4086076 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : (term157 A t) = False.
Proof. exact (prop_ext (fun h3 : term157 A t => @lem4086075 A t s n h1 h2) (fun h3 : False => @lem4085779 A t h1)). Qed.
Lemma lem4086077 {A : Type'} (t : type1573 A) (s : A -> Prop) (n : nat) (h1 : term157 A t) (h2 : term77 A s n) : False.
Proof. exact (EQ_MP (@lem4086076 A t s n h1 h2) (@lem4085779 A t h1)). Qed.
Lemma lem4086078 {A : Type'} (t : type1573 A) (s : A -> Prop) (h1 : term157 A t) (h2 : term80 A s) : False.
Proof. exact (ex_elim (@lem4085732 A s h2) (fun n : nat => fun h0 : term79 A s n => @lem4086077 A t s n h1 h0)). Qed.
Lemma lem4086079 {A : Type'} (t : type1573 A) (h1 : term157 A t) (h2 : term3 A) : False.
Proof. exact (ex_elim (@lem4085512 A h2) (fun s : A -> Prop => fun h0 : term81 A s => @lem4086078 A t s h1 h0)). Qed.
Lemma lem4086080 {A : Type'} (h1 : term4 A) (h2 : term3 A) : False.
Proof. exact (ex_elim (@lem4085730 A h1) (fun t : type1573 A => fun h0 : term159 A t => @lem4086079 A t h0 h2)). Qed.
Lemma lem4086081 {A : Type'} (h1 : term3 A) : term9 A.
Proof. exact (fun h0 : term4 A => @lem4086080 A h0 h1). Qed.
Lemma lem4086082 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem4086083 {A : Type'} (h1 : term3 A) : term10 A.
Proof. exact (EQ_MP (@lem4086082 A) (@lem4086081 A h1)). Qed.
Lemma lem4086084 {A : Type'} : term12 A.
Proof. exact (fun h0 : term3 A => @lem4086083 A h0). Qed.
Lemma lem4086085 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem4085310 A) (@lem4086084 A)). Qed.
Lemma lem4086087 {A : Type'} : term5 A.
Proof. exact (@lem4085068 A (@lem4086085 A)). Qed.
Lemma lem4086088 {A : Type'} (h1 : term3 A) : term9 A.
Proof. exact (@lem4086087 A (@lem4085048 A h1)). Qed.
Lemma lem4086089 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem4086088 A h1 (@lem4085049 A)). Qed.
Lemma lem4086090 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem4086089 A h1) (fun h2 : False => @lem4085048 A h1)). Qed.
Lemma lem4086091 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem4086090 A h1) (@lem4085048 A h1)). Qed.
Lemma lem4086092 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem4086091 A h0). Qed.
Lemma lem4086093 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem4085047 A) (@lem4086092 A)). Qed.
