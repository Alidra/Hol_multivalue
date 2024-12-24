Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIR_EXISTS_THM_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm18394_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem44184 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem44185 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (@lem44184 (term1 A B)). Qed.
Lemma lem44186 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (SYM (@lem44185 A B)). Qed.
Lemma lem44187 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem44190 {A B : Type'} (h1 : term2 A B) : term2 A B.
Proof. exact (h1). Qed.
Lemma lem44191 {A B : Type'} : term4 A B.
Proof. exact (fun h0 : term2 A B => @lem44190 A B h0). Qed.
Lemma lem44192 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem44193 {A B : Type'} (h1 : term2 A B) : term2 A B.
Proof. exact (h1). Qed.
Lemma lem44194 {A B : Type'} (h1 : term2 A B) (h2 : term4 A B) : term2 A B.
Proof. exact (@lem44192 A B h2 (@lem44193 A B h1)). Qed.
Lemma lem44195 {A B : Type'} (h1 : term2 A B) : term5 A B.
Proof. exact (fun h0 : term4 A B => @lem44194 A B h1 h0). Qed.
Lemma lem44196 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem44197 {A B : Type'} (h1 : term2 A B) (h2 : term4 A B) : term2 A B.
Proof. exact (@lem44195 A B h1 (@lem44196 A B h2)). Qed.
Lemma lem44198 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (fun h0 : term2 A B => @lem44197 A B h0 h1). Qed.
Lemma lem44199 {A B : Type'} : term6 A B.
Proof. exact (fun h0 : term4 A B => @lem44198 A B h0). Qed.
Lemma lem44202 {A B : Type'} : term4 A B.
Proof. exact (@lem44199 A B (@lem44191 A B)). Qed.
Lemma lem44203 {A B : Type'} : term4 A B.
Proof. exact (@lem44202 A B). Qed.
Lemma lem44205 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem44206 {A B : Type'} : (term2 A B) = (term7 A B).
Proof. exact (@lem44205 (term3 A B)). Qed.
Lemma lem44208 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem44209 {A B : Type'} : (term7 A B) = (term1 A B).
Proof. exact (@lem44208 (term1 A B)). Qed.
Lemma lem44226 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (TRANS (@lem44206 A B) (@lem44209 A B)). Qed.
Lemma lem44227 {A B : Type'} (x : type1413 A B) (a : A) (b : B) : (x = (@mk_pair A B a b)) = (x = (@mk_pair A B a b)).
Proof. exact (eq_refl (x = (@mk_pair A B a b))). Qed.
Lemma lem44228 {A B : Type'} (x : type1413 A B) (a : A) : (term9 A B x a) = (term9 A B x a).
Proof. exact (fun_ext (fun b : B => @lem44227 A B x a b)). Qed.
Lemma lem44229 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem44230 {A B : Type'} (x : type1413 A B) (a : A) : (term10 A B x a) = (term10 A B x a).
Proof. exact (MK_COMB (@lem44229 B) (@lem44228 A B x a)). Qed.
Lemma lem44231 {A B : Type'} (x : type1413 A B) : (term11 A B x) = (term11 A B x).
Proof. exact (fun_ext (fun a : A => @lem44230 A B x a)). Qed.
Lemma lem44232 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44233 {A B : Type'} (x : type1413 A B) : (term12 A B x) = (term12 A B x).
Proof. exact (MK_COMB (@lem44232 A) (@lem44231 A B x)). Qed.
Lemma lem44234 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (fun_ext (fun x : type1413 A B => @lem44233 A B x)). Qed.
Lemma lem44235 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem44236 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (MK_COMB (@lem44235 A B) (@lem44234 A B)). Qed.
Lemma lem44257 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (TRANS (@lem44226 A B) (@lem44236 A B)). Qed.
Lemma lem44258 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (SYM (@lem44257 A B)). Qed.
Lemma lem44260 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem44261 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (@lem44260 (term1 A B)). Qed.
Lemma lem44262 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (SYM (@lem44261 A B)). Qed.
Lemma lem44263 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem44265 {B : Type'} (P : B -> Prop) : (term14 B P) = (term15 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem44266 {A B : Type'} (x : type1413 A B) (a : A) : (term16 A B x a) = (term17 A B x a).
Proof. exact (@lem44265 B (term9 A B x a)). Qed.
Lemma lem44267 {A B : Type'} (x : type1413 A B) (a : A) (b : B) : (term18 A B x a b) = (x = (@mk_pair A B a b)).
Proof. exact (eq_refl (term18 A B x a b)). Qed.
Lemma lem44268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44270 {A B : Type'} (x : type1413 A B) (a : A) (b : B) : (term19 A B x a b) = (term20 A B x a b).
Proof. exact (MK_COMB (@lem44268) (@lem44267 A B x a b)). Qed.
Lemma lem44271 {A B : Type'} (x : type1413 A B) (a : A) : (term21 A B x a) = (term22 A B x a).
Proof. exact (fun_ext (fun b : B => @lem44270 A B x a b)). Qed.
Lemma lem44272 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem44273 {A B : Type'} (x : type1413 A B) (a : A) : (term17 A B x a) = (term23 A B x a).
Proof. exact (MK_COMB (@lem44272 B) (@lem44271 A B x a)). Qed.
Lemma lem44274 {A B : Type'} (x : type1413 A B) (a : A) : (term16 A B x a) = (term23 A B x a).
Proof. exact (TRANS (@lem44266 A B x a) (@lem44273 A B x a)). Qed.
Lemma lem44275 {A : Type'} (P : A -> Prop) : (term14 A P) = (term15 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem44276 {A B : Type'} (x : type1413 A B) : (term24 A B x) = (term25 A B x).
Proof. exact (@lem44275 A (term11 A B x)). Qed.
Lemma lem44277 {A B : Type'} (x : type1413 A B) (a : A) : (term26 A B x a) = (term10 A B x a).
Proof. exact (eq_refl (term26 A B x a)). Qed.
Lemma lem44278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44279 {A B : Type'} (x : type1413 A B) (a : A) : (term27 A B x a) = (term16 A B x a).
Proof. exact (MK_COMB (@lem44278) (@lem44277 A B x a)). Qed.
Lemma lem44280 {A B : Type'} (x : type1413 A B) (a : A) : (term27 A B x a) = (term23 A B x a).
Proof. exact (TRANS (@lem44279 A B x a) (@lem44274 A B x a)). Qed.
Lemma lem44281 {A B : Type'} (x : type1413 A B) : (term28 A B x) = (term29 A B x).
Proof. exact (fun_ext (fun a : A => @lem44280 A B x a)). Qed.
Lemma lem44282 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem44283 {A B : Type'} (x : type1413 A B) : (term25 A B x) = (term30 A B x).
Proof. exact (MK_COMB (@lem44282 A) (@lem44281 A B x)). Qed.
Lemma lem44284 {A B : Type'} (x : type1413 A B) : (term24 A B x) = (term30 A B x).
Proof. exact (TRANS (@lem44276 A B x) (@lem44283 A B x)). Qed.
Lemma lem44285 {A B : Type'} (P : type475 A B) : (term31 A B P) = (term32 A B P).
Proof. exact (@lem18394 (type1413 A B) P). Qed.
Lemma lem44286 {A B : Type'} : (term3 A B) = (term33 A B).
Proof. exact (@lem44285 A B (term13 A B)). Qed.
Lemma lem44287 {A B : Type'} (x : type1413 A B) : (term34 A B x) = (term12 A B x).
Proof. exact (eq_refl (term34 A B x)). Qed.
Lemma lem44288 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44289 {A B : Type'} (x : type1413 A B) : (term35 A B x) = (term24 A B x).
Proof. exact (MK_COMB (@lem44288) (@lem44287 A B x)). Qed.
Lemma lem44290 {A B : Type'} (x : type1413 A B) : (term35 A B x) = (term30 A B x).
Proof. exact (TRANS (@lem44289 A B x) (@lem44284 A B x)). Qed.
Lemma lem44291 {A B : Type'} : (term36 A B) = (term37 A B).
Proof. exact (fun_ext (fun x : type1413 A B => @lem44290 A B x)). Qed.
Lemma lem44292 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44293 {A B : Type'} : (term33 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem44292 A B) (@lem44291 A B)). Qed.
Lemma lem44310 {A B : Type'} : (term3 A B) = (term38 A B).
Proof. exact (TRANS (@lem44286 A B) (@lem44293 A B)). Qed.
Lemma lem44311 {A B : Type'} (h1 : term3 A B) : term38 A B.
Proof. exact (EQ_MP (@lem44310 A B) (@lem44263 A B h1)). Qed.
Lemma lem44322 {A B : Type'} (x : type1413 A B) (a : A) (b : B) : (term20 A B x a b) = (term20 A B x a b).
Proof. exact (eq_refl (term20 A B x a b)). Qed.
Lemma lem44323 {A B : Type'} (x : type1413 A B) (a : A) : (term22 A B x a) = (term22 A B x a).
Proof. exact (fun_ext (fun b : B => @lem44322 A B x a b)). Qed.
Lemma lem44324 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem44325 {A B : Type'} (x : type1413 A B) (a : A) : (term23 A B x a) = (term23 A B x a).
Proof. exact (MK_COMB (@lem44324 B) (@lem44323 A B x a)). Qed.
Lemma lem44326 {A B : Type'} (x : type1413 A B) : (term29 A B x) = (term29 A B x).
Proof. exact (fun_ext (fun a : A => @lem44325 A B x a)). Qed.
Lemma lem44327 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem44328 {A B : Type'} (x : type1413 A B) : (term30 A B x) = (term30 A B x).
Proof. exact (MK_COMB (@lem44327 A) (@lem44326 A B x)). Qed.
Lemma lem44329 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (fun_ext (fun x : type1413 A B => @lem44328 A B x)). Qed.
Lemma lem44330 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44331 {A B : Type'} : (term38 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem44330 A B) (@lem44329 A B)). Qed.
Lemma lem44332 {A B : Type'} (h1 : term3 A B) : term38 A B.
Proof. exact (EQ_MP (@lem44331 A B) (@lem44311 A B h1)). Qed.
Lemma lem44334 {A B : Type'} (x : type1413 A B) (a : A) (b : B) : (term20 A B x a b) = (term20 A B x a b).
Proof. exact (eq_refl (term20 A B x a b)). Qed.
Lemma lem44335 {A B : Type'} (x : type1413 A B) (a : A) : (term22 A B x a) = (term22 A B x a).
Proof. exact (fun_ext (fun b : B => @lem44334 A B x a b)). Qed.
Lemma lem44336 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem44337 {A B : Type'} (x : type1413 A B) (a : A) : (term23 A B x a) = (term23 A B x a).
Proof. exact (MK_COMB (@lem44336 B) (@lem44335 A B x a)). Qed.
Lemma lem44338 {A B : Type'} (x : type1413 A B) : (term29 A B x) = (term29 A B x).
Proof. exact (fun_ext (fun a : A => @lem44337 A B x a)). Qed.
Lemma lem44339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem44340 {A B : Type'} (x : type1413 A B) : (term30 A B x) = (term30 A B x).
Proof. exact (MK_COMB (@lem44339 A) (@lem44338 A B x)). Qed.
Lemma lem44341 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (fun_ext (fun x : type1413 A B => @lem44340 A B x)). Qed.
Lemma lem44342 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44344 {A B : Type'} : (term38 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem44342 A B) (@lem44341 A B)). Qed.
Lemma lem44345 {A B : Type'} (h1 : term3 A B) : term38 A B.
Proof. exact (EQ_MP (@lem44344 A B) (@lem44332 A B h1)). Qed.
Lemma lem44346 {A B : Type'} (_1231 : type1413 A B) (h1 : term3 A B) : term39 A B _1231.
Proof. exact (@lem44345 A B h1 _1231). Qed.
Lemma lem44347 {A B : Type'} (_1231 : type1413 A B) : (term39 A B _1231) = (term30 A B _1231).
Proof. exact (eq_refl (term39 A B _1231)). Qed.
Lemma lem44348 {A B : Type'} (_1231 : type1413 A B) (h1 : term3 A B) : term30 A B _1231.
Proof. exact (EQ_MP (@lem44347 A B _1231) (@lem44346 A B _1231 h1)). Qed.
Lemma lem44349 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (h1 : term3 A B) : term40 A B _1231 _1232.
Proof. exact (@lem44348 A B _1231 h1 _1232). Qed.
Lemma lem44350 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) : (term40 A B _1231 _1232) = (term23 A B _1231 _1232).
Proof. exact (eq_refl (term40 A B _1231 _1232)). Qed.
Lemma lem44351 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (h1 : term3 A B) : term23 A B _1231 _1232.
Proof. exact (EQ_MP (@lem44350 A B _1231 _1232) (@lem44349 A B _1231 _1232 h1)). Qed.
Lemma lem44352 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (_1233 : B) (h1 : term3 A B) : term41 A B _1231 _1232 _1233.
Proof. exact (@lem44351 A B _1231 _1232 h1 _1233). Qed.
Lemma lem44353 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (_1233 : B) : (term41 A B _1231 _1232 _1233) = (term20 A B _1231 _1232 _1233).
Proof. exact (eq_refl (term41 A B _1231 _1232 _1233)). Qed.
Lemma lem44356 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (_1233 : B) (h1 : term3 A B) : term20 A B _1231 _1232 _1233.
Proof. exact (EQ_MP (@lem44353 A B _1231 _1232 _1233) (@lem44352 A B _1231 _1232 _1233 h1)). Qed.
Lemma lem44379 {A B : Type'} (x : type1413 A B) : x = x.
Proof. exact (@lem21386 (type1413 A B) x). Qed.
Lemma lem44380 {A B : Type'} (x : type1413 A B) : x = x.
Proof. exact (@lem44379 A B x). Qed.
Lemma lem44381 {A B : Type'} (_1238 : A) (_1239 : B) : (@mk_pair A B _1238 _1239) = (@mk_pair A B _1238 _1239).
Proof. exact (@lem44380 A B (@mk_pair A B _1238 _1239)). Qed.
Lemma lem44382 {A B : Type'} (_1238 : A) (_1239 : B) : term42 A B _1238 _1239.
Proof. exact (fun h0 : term43 A B _1238 _1239 => @lem44381 A B _1238 _1239). Qed.
Lemma lem44384 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem44385 {A B : Type'} (_1238 : A) (_1239 : B) : (term42 A B _1238 _1239) = ((@mk_pair A B _1238 _1239) = (@mk_pair A B _1238 _1239)).
Proof. exact (@lem44384 ((@mk_pair A B _1238 _1239) = (@mk_pair A B _1238 _1239))). Qed.
Lemma lem44386 {A B : Type'} (_1238 : A) (_1239 : B) : (@mk_pair A B _1238 _1239) = (@mk_pair A B _1238 _1239).
Proof. exact (EQ_MP (@lem44385 A B _1238 _1239) (@lem44382 A B _1238 _1239)). Qed.
Lemma lem44389 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem44391 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (_1233 : B) : (term20 A B _1231 _1232 _1233) = (term45 A B _1231 _1232 _1233).
Proof. exact (@lem44389 (_1231 = (@mk_pair A B _1232 _1233))). Qed.
Lemma lem44394 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (_1233 : B) (h1 : term3 A B) : term45 A B _1231 _1232 _1233.
Proof. exact (EQ_MP (@lem44391 A B _1231 _1232 _1233) (@lem44356 A B _1231 _1232 _1233 h1)). Qed.
Lemma lem44395 {A B : Type'} (_1231 : type1413 A B) (_1232 : A) (_1233 : B) (h1 : term3 A B) : term45 A B _1231 _1232 _1233.
Proof. exact (@lem44394 A B _1231 _1232 _1233 h1). Qed.
Lemma lem44396 {A B : Type'} (_1238 : A) (_1239 : B) (h1 : term3 A B) : term46 A B _1238 _1239.
Proof. exact (@lem44395 A B (@mk_pair A B _1238 _1239) _1238 _1239 h1). Qed.
Lemma lem44399 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (@lem44396 A B (@el A) (@el B) h1 (@lem44386 A B (@el A) (@el B))). Qed.
Lemma lem44400 {A B : Type'} (h1 : term3 A B) : term47.
Proof. exact (fun h0 : ~ False => @lem44399 A B h1). Qed.
Lemma lem44402 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem44403 : term47 = False.
Proof. exact (@lem44402 False). Qed.
Lemma lem44404 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (EQ_MP (@lem44403) (@lem44400 A B h1)). Qed.
Lemma lem44405 {A B : Type'} (h1 : term3 A B) : (term3 A B) = False.
Proof. exact (prop_ext (fun h2 : term3 A B => @lem44404 A B h1) (fun h2 : False => @lem44263 A B h1)). Qed.
Lemma lem44406 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (EQ_MP (@lem44405 A B h1) (@lem44263 A B h1)). Qed.
Lemma lem44407 {A B : Type'} : term2 A B.
Proof. exact (fun h0 : term3 A B => @lem44406 A B h0). Qed.
Lemma lem44408 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem44262 A B) (@lem44407 A B)). Qed.
Lemma lem44409 {A B : Type'} : term2 A B.
Proof. exact (EQ_MP (@lem44258 A B) (@lem44408 A B)). Qed.
Lemma lem44411 {A B : Type'} : term2 A B.
Proof. exact (@lem44203 A B (@lem44409 A B)). Qed.
Lemma lem44412 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (@lem44411 A B (@lem44187 A B h1)). Qed.
Lemma lem44413 {A B : Type'} (h1 : term3 A B) : (term3 A B) = False.
Proof. exact (prop_ext (fun h2 : term3 A B => @lem44412 A B h1) (fun h2 : False => @lem44187 A B h1)). Qed.
Lemma lem44414 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (EQ_MP (@lem44413 A B h1) (@lem44187 A B h1)). Qed.
Lemma lem44415 {A B : Type'} : term2 A B.
Proof. exact (fun h0 : term3 A B => @lem44414 A B h0). Qed.
Lemma lem44416 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem44186 A B) (@lem44415 A B)). Qed.
