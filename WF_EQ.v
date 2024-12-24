Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import WF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Lemma lem303056 {A : Type'} (lt2 : type1402 A) : term0 A lt2.
Proof. exact (@lem303045 A lt2). Qed.
Lemma lem303057 {A : Type'} (lt2 : type1402 A) : (term0 A lt2) = ((@WF A lt2) = (term1 A lt2)).
Proof. exact (eq_refl (term0 A lt2)). Qed.
Lemma lem303062 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (EQ_MP (@lem303057 A lt2) (@lem303056 A lt2)). Qed.
Lemma lem303063 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (@lem303062 A lt2). Qed.
Lemma lem303086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem303087 {A : Type'} (lt2 : type1402 A) : (term2 A lt2) = (term3 A lt2).
Proof. exact (MK_COMB (@lem303086) (@lem303063 A lt2)). Qed.
Lemma lem303110 {A : Type'} (lt2 : type1402 A) : (term4 A lt2) = (term4 A lt2).
Proof. exact (eq_refl (term4 A lt2)). Qed.
Lemma lem303111 {A : Type'} (lt2 : type1402 A) : ((@WF A lt2) = (term4 A lt2)) = ((term1 A lt2) = (term4 A lt2)).
Proof. exact (MK_COMB (@lem303087 A lt2) (@lem303110 A lt2)). Qed.
Lemma lem303114 {A : Type'} (lt2 : type1402 A) : ((term1 A lt2) = (term4 A lt2)) = ((@WF A lt2) = (term4 A lt2)).
Proof. exact (SYM (@lem303111 A lt2)). Qed.
Lemma lem303116 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem303117 {A : Type'} (lt2 : type1402 A) : ((term1 A lt2) = (term4 A lt2)) = (term6 A lt2).
Proof. exact (@lem303116 ((term1 A lt2) = (term4 A lt2))). Qed.
Lemma lem303118 {A : Type'} (lt2 : type1402 A) : (term6 A lt2) = ((term1 A lt2) = (term4 A lt2)).
Proof. exact (SYM (@lem303117 A lt2)). Qed.
Lemma lem303119 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : term7 A lt2.
Proof. exact (h1). Qed.
Lemma lem303122 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) : term6 A lt2.
Proof. exact (h1). Qed.
Lemma lem303123 {A : Type'} (lt2 : type1402 A) : term8 A lt2.
Proof. exact (fun h0 : term6 A lt2 => @lem303122 A lt2 h0). Qed.
Lemma lem303124 {A : Type'} (lt2 : type1402 A) (h1 : term8 A lt2) : term8 A lt2.
Proof. exact (h1). Qed.
Lemma lem303125 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) : term6 A lt2.
Proof. exact (h1). Qed.
Lemma lem303126 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) (h2 : term8 A lt2) : term6 A lt2.
Proof. exact (@lem303124 A lt2 h2 (@lem303125 A lt2 h1)). Qed.
Lemma lem303127 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) : term9 A lt2.
Proof. exact (fun h0 : term8 A lt2 => @lem303126 A lt2 h1 h0). Qed.
Lemma lem303128 {A : Type'} (lt2 : type1402 A) (h1 : term8 A lt2) : term8 A lt2.
Proof. exact (h1). Qed.
Lemma lem303129 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) (h2 : term8 A lt2) : term6 A lt2.
Proof. exact (@lem303127 A lt2 h1 (@lem303128 A lt2 h2)). Qed.
Lemma lem303130 {A : Type'} (lt2 : type1402 A) (h1 : term8 A lt2) : term8 A lt2.
Proof. exact (fun h0 : term6 A lt2 => @lem303129 A lt2 h0 h1). Qed.
Lemma lem303131 {A : Type'} (lt2 : type1402 A) : term10 A lt2.
Proof. exact (fun h0 : term8 A lt2 => @lem303130 A lt2 h0). Qed.
Lemma lem303134 {A : Type'} (lt2 : type1402 A) : term8 A lt2.
Proof. exact (@lem303131 A lt2 (@lem303123 A lt2)). Qed.
Lemma lem303135 {A : Type'} (lt2 : type1402 A) : term8 A lt2.
Proof. exact (@lem303134 A lt2). Qed.
Lemma lem303141 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem303142 {A : Type'} (lt2 : type1402 A) : (term6 A lt2) = (term11 A lt2).
Proof. exact (@lem303141 (term7 A lt2)). Qed.
Lemma lem303144 (t : Prop) : (term12 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem303145 {A : Type'} (lt2 : type1402 A) : (term11 A lt2) = ((term1 A lt2) = (term4 A lt2)).
Proof. exact (@lem303144 ((term1 A lt2) = (term4 A lt2))). Qed.
Lemma lem303146 {A : Type'} (lt2 : type1402 A) : (term6 A lt2) = ((term1 A lt2) = (term4 A lt2)).
Proof. exact (TRANS (@lem303142 A lt2) (@lem303145 A lt2)). Qed.
Lemma lem303237 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem303146 A lt2)). Qed.
Lemma lem303238 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem303247 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem303238 A) (@lem303237 A)). Qed.
Lemma lem303254 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term17 A lt2 x P y) = (term17 A lt2 x P y).
Proof. exact (eq_refl (term17 A lt2 x P y)). Qed.
Lemma lem303255 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term18 A lt2 x P) = (term18 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem303254 A lt2 x P y)). Qed.
Lemma lem303256 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303257 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term19 A lt2 x P) = (term19 A lt2 x P).
Proof. exact (MK_COMB (@lem303256 A) (@lem303255 A lt2 x P)). Qed.
Lemma lem303260 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem303261 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term21 A lt2 x P) = (term21 A lt2 x P).
Proof. exact (MK_COMB (@lem303260 A P x) (@lem303257 A lt2 x P)). Qed.
Lemma lem303262 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term22 A lt2 P) = (term22 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem303261 A lt2 x P)). Qed.
Lemma lem303263 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303264 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term23 A lt2 P) = (term23 A lt2 P).
Proof. exact (MK_COMB (@lem303263 A) (@lem303262 A lt2 P)). Qed.
Lemma lem303265 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem303266 {A : Type'} (P : A -> Prop) : (term24 A P) = (term24 A P).
Proof. exact (fun_ext (fun x : A => @lem303265 A P x)). Qed.
Lemma lem303267 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303268 {A : Type'} (P : A -> Prop) : (term25 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem303267 A) (@lem303266 A P)). Qed.
Lemma lem303269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem303270 {A : Type'} (P : A -> Prop) : (term26 A P) = (term26 A P).
Proof. exact (MK_COMB (@lem303269) (@lem303268 A P)). Qed.
Lemma lem303271 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term25 A P) = (term23 A lt2 P)) = ((term25 A P) = (term23 A lt2 P)).
Proof. exact (MK_COMB (@lem303270 A P) (@lem303264 A lt2 P)). Qed.
Lemma lem303272 {A : Type'} (lt2 : type1402 A) : (term27 A lt2) = (term27 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem303271 A lt2 P)). Qed.
Lemma lem303273 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem303274 {A : Type'} (lt2 : type1402 A) : (term4 A lt2) = (term4 A lt2).
Proof. exact (MK_COMB (@lem303273 A) (@lem303272 A lt2)). Qed.
Lemma lem303281 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term17 A lt2 x P y) = (term17 A lt2 x P y).
Proof. exact (eq_refl (term17 A lt2 x P y)). Qed.
Lemma lem303282 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term18 A lt2 x P) = (term18 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem303281 A lt2 x P y)). Qed.
Lemma lem303283 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303284 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term19 A lt2 x P) = (term19 A lt2 x P).
Proof. exact (MK_COMB (@lem303283 A) (@lem303282 A lt2 x P)). Qed.
Lemma lem303287 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem303288 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term21 A lt2 x P) = (term21 A lt2 x P).
Proof. exact (MK_COMB (@lem303287 A P x) (@lem303284 A lt2 x P)). Qed.
Lemma lem303289 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term22 A lt2 P) = (term22 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem303288 A lt2 x P)). Qed.
Lemma lem303290 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303291 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term23 A lt2 P) = (term23 A lt2 P).
Proof. exact (MK_COMB (@lem303290 A) (@lem303289 A lt2 P)). Qed.
Lemma lem303292 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem303293 {A : Type'} (P : A -> Prop) : (term24 A P) = (term24 A P).
Proof. exact (fun_ext (fun x : A => @lem303292 A P x)). Qed.
Lemma lem303294 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303295 {A : Type'} (P : A -> Prop) : (term25 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem303294 A) (@lem303293 A P)). Qed.
Lemma lem303296 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem303297 {A : Type'} (P : A -> Prop) : (term28 A P) = (term28 A P).
Proof. exact (MK_COMB (@lem303296) (@lem303295 A P)). Qed.
Lemma lem303298 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term29 A lt2 P) = (term29 A lt2 P).
Proof. exact (MK_COMB (@lem303297 A P) (@lem303291 A lt2 P)). Qed.
Lemma lem303299 {A : Type'} (lt2 : type1402 A) : (term30 A lt2) = (term30 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem303298 A lt2 P)). Qed.
Lemma lem303300 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem303301 {A : Type'} (lt2 : type1402 A) : (term1 A lt2) = (term1 A lt2).
Proof. exact (MK_COMB (@lem303300 A) (@lem303299 A lt2)). Qed.
Lemma lem303302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem303303 {A : Type'} (lt2 : type1402 A) : (term3 A lt2) = (term3 A lt2).
Proof. exact (MK_COMB (@lem303302) (@lem303301 A lt2)). Qed.
Lemma lem303304 {A : Type'} (lt2 : type1402 A) : ((term1 A lt2) = (term4 A lt2)) = ((term1 A lt2) = (term4 A lt2)).
Proof. exact (MK_COMB (@lem303303 A lt2) (@lem303274 A lt2)). Qed.
Lemma lem303305 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem303304 A lt2)). Qed.
Lemma lem303306 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem303307 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem303306 A) (@lem303305 A)). Qed.
Lemma lem303374 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (TRANS (@lem303247 A) (@lem303307 A)). Qed.
Lemma lem303375 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem303374 A)). Qed.
Lemma lem303377 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem303378 {A : Type'} (lt2 : type1402 A) : ((term1 A lt2) = (term4 A lt2)) = (term6 A lt2).
Proof. exact (@lem303377 ((term1 A lt2) = (term4 A lt2))). Qed.
Lemma lem303379 {A : Type'} (lt2 : type1402 A) : (term6 A lt2) = ((term1 A lt2) = (term4 A lt2)).
Proof. exact (SYM (@lem303378 A lt2)). Qed.
Lemma lem303380 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : term7 A lt2.
Proof. exact (h1). Qed.
Lemma lem303382 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem303383 {A : Type'} (P : A -> Prop) : (term31 A P) = (term32 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem303384 {A : Type'} (P : A -> Prop) : (term33 A P) = (term34 A P).
Proof. exact (@lem303383 A (term24 A P)). Qed.
Lemma lem303385 {A : Type'} (P : A -> Prop) (x : A) : (term35 A P x) = (P x).
Proof. exact (eq_refl (term35 A P x)). Qed.
Lemma lem303386 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303388 {A : Type'} (P : A -> Prop) (x : A) : (term36 A P x) = (term37 A P x).
Proof. exact (MK_COMB (@lem303386) (@lem303385 A P x)). Qed.
Lemma lem303389 {A : Type'} (P : A -> Prop) : (term38 A P) = (term39 A P).
Proof. exact (fun_ext (fun x : A => @lem303388 A P x)). Qed.
Lemma lem303390 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303391 {A : Type'} (P : A -> Prop) : (term34 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem303390 A) (@lem303389 A P)). Qed.
Lemma lem303392 {A : Type'} (P : A -> Prop) : (term33 A P) = (term32 A P).
Proof. exact (TRANS (@lem303384 A P) (@lem303391 A P)). Qed.
Lemma lem303393 {A : Type'} (P : A -> Prop) : (term24 A P) = (term24 A P).
Proof. exact (fun_ext (fun x : A => @lem303382 A P x)). Qed.
Lemma lem303394 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303395 {A : Type'} (P : A -> Prop) : (term25 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem303394 A) (@lem303393 A P)). Qed.
Lemma lem303403 {A : Type'} (P : A -> Prop) (y : A) : (term40 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem303405 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term41 A lt2 y x) = (term41 A lt2 y x).
Proof. exact (eq_refl (term41 A lt2 y x)). Qed.
Lemma lem303406 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term42 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (MK_COMB (@lem303405 A lt2 y x) (@lem303403 A P y)). Qed.
Lemma lem303407 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term44 A lt2 x P y) = (term42 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term37 A P y)). Qed.
Lemma lem303408 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term44 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (TRANS (@lem303407 A lt2 x P y) (@lem303406 A lt2 x P y)). Qed.
Lemma lem303413 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term17 A lt2 x P y) = (term45 A lt2 x P y).
Proof. exact (@lem17265 (lt2 y x) (term37 A P y)). Qed.
Lemma lem303414 {A : Type'} (P : A -> Prop) : (term46 A P) = (term47 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem303415 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term48 A lt2 x P) = (term49 A lt2 x P).
Proof. exact (@lem303414 A (term18 A lt2 x P)). Qed.
Lemma lem303416 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term50 A lt2 x P y) = (term17 A lt2 x P y).
Proof. exact (eq_refl (term50 A lt2 x P y)). Qed.
Lemma lem303417 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303418 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term44 A lt2 x P y).
Proof. exact (MK_COMB (@lem303417) (@lem303416 A lt2 x P y)). Qed.
Lemma lem303419 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (TRANS (@lem303418 A lt2 x P y) (@lem303408 A lt2 x P y)). Qed.
Lemma lem303420 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term52 A lt2 x P) = (term53 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem303419 A lt2 x P y)). Qed.
Lemma lem303421 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303422 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term49 A lt2 x P) = (term54 A lt2 x P).
Proof. exact (MK_COMB (@lem303421 A) (@lem303420 A lt2 x P)). Qed.
Lemma lem303423 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term48 A lt2 x P) = (term54 A lt2 x P).
Proof. exact (TRANS (@lem303415 A lt2 x P) (@lem303422 A lt2 x P)). Qed.
Lemma lem303424 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term18 A lt2 x P) = (term55 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem303413 A lt2 x P y)). Qed.
Lemma lem303425 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303426 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term19 A lt2 x P) = (term56 A lt2 x P).
Proof. exact (MK_COMB (@lem303425 A) (@lem303424 A lt2 x P)). Qed.
Lemma lem303428 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem303429 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term58 A lt2 x P) = (term59 A lt2 x P).
Proof. exact (MK_COMB (@lem303428 A P x) (@lem303423 A lt2 x P)). Qed.
Lemma lem303430 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term60 A lt2 x P) = (term58 A lt2 x P).
Proof. exact (@lem17045 (P x) (term19 A lt2 x P)). Qed.
Lemma lem303431 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term60 A lt2 x P) = (term59 A lt2 x P).
Proof. exact (TRANS (@lem303430 A lt2 x P) (@lem303429 A lt2 x P)). Qed.
Lemma lem303433 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem303434 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term21 A lt2 x P) = (term61 A lt2 x P).
Proof. exact (MK_COMB (@lem303433 A P x) (@lem303426 A lt2 x P)). Qed.
Lemma lem303435 {A : Type'} (P : A -> Prop) : (term31 A P) = (term32 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem303436 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term62 A lt2 P) = (term63 A lt2 P).
Proof. exact (@lem303435 A (term22 A lt2 P)). Qed.
Lemma lem303437 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term64 A lt2 P x) = (term21 A lt2 x P).
Proof. exact (eq_refl (term64 A lt2 P x)). Qed.
Lemma lem303438 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303439 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 P x) = (term60 A lt2 x P).
Proof. exact (MK_COMB (@lem303438) (@lem303437 A lt2 x P)). Qed.
Lemma lem303440 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 P x) = (term59 A lt2 x P).
Proof. exact (TRANS (@lem303439 A lt2 x P) (@lem303431 A lt2 x P)). Qed.
Lemma lem303441 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term66 A lt2 P) = (term67 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem303440 A lt2 x P)). Qed.
Lemma lem303442 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303443 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term63 A lt2 P) = (term68 A lt2 P).
Proof. exact (MK_COMB (@lem303442 A) (@lem303441 A lt2 P)). Qed.
Lemma lem303444 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term62 A lt2 P) = (term68 A lt2 P).
Proof. exact (TRANS (@lem303436 A lt2 P) (@lem303443 A lt2 P)). Qed.
Lemma lem303445 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term22 A lt2 P) = (term69 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem303434 A lt2 x P)). Qed.
Lemma lem303446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303447 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term23 A lt2 P) = (term70 A lt2 P).
Proof. exact (MK_COMB (@lem303446 A) (@lem303445 A lt2 P)). Qed.
Lemma lem303448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem303449 {A : Type'} (P : A -> Prop) : (term71 A P) = (term71 A P).
Proof. exact (MK_COMB (@lem303448) (@lem303395 A P)). Qed.
Lemma lem303450 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term72 A lt2 P) = (term73 A lt2 P).
Proof. exact (MK_COMB (@lem303449 A P) (@lem303444 A lt2 P)). Qed.
Lemma lem303451 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term74 A lt2 P) = (term72 A lt2 P).
Proof. exact (@lem17362 (term25 A P) (term23 A lt2 P)). Qed.
Lemma lem303452 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term74 A lt2 P) = (term73 A lt2 P).
Proof. exact (TRANS (@lem303451 A lt2 P) (@lem303450 A lt2 P)). Qed.
Lemma lem303453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem303454 {A : Type'} (P : A -> Prop) : (term75 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem303453) (@lem303392 A P)). Qed.
Lemma lem303455 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term77 A lt2 P) = (term78 A lt2 P).
Proof. exact (MK_COMB (@lem303454 A P) (@lem303447 A lt2 P)). Qed.
Lemma lem303456 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term29 A lt2 P) = (term77 A lt2 P).
Proof. exact (@lem17265 (term25 A P) (term23 A lt2 P)). Qed.
Lemma lem303457 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term29 A lt2 P) = (term78 A lt2 P).
Proof. exact (TRANS (@lem303456 A lt2 P) (@lem303455 A lt2 P)). Qed.
Lemma lem303458 {A : Type'} (P : type686 A) : (term79 A P) = (term80 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem303459 {A : Type'} (lt2 : type1402 A) : (term81 A lt2) = (term82 A lt2).
Proof. exact (@lem303458 A (term30 A lt2)). Qed.
Lemma lem303460 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term83 A lt2 P) = (term29 A lt2 P).
Proof. exact (eq_refl (term83 A lt2 P)). Qed.
Lemma lem303461 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303462 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term84 A lt2 P) = (term74 A lt2 P).
Proof. exact (MK_COMB (@lem303461) (@lem303460 A lt2 P)). Qed.
Lemma lem303463 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term84 A lt2 P) = (term73 A lt2 P).
Proof. exact (TRANS (@lem303462 A lt2 P) (@lem303452 A lt2 P)). Qed.
Lemma lem303464 {A : Type'} (lt2 : type1402 A) : (term85 A lt2) = (term86 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem303463 A lt2 P)). Qed.
Lemma lem303465 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem303466 {A : Type'} (lt2 : type1402 A) : (term82 A lt2) = (term87 A lt2).
Proof. exact (MK_COMB (@lem303465 A) (@lem303464 A lt2)). Qed.
Lemma lem303467 {A : Type'} (lt2 : type1402 A) : (term81 A lt2) = (term87 A lt2).
Proof. exact (TRANS (@lem303459 A lt2) (@lem303466 A lt2)). Qed.
Lemma lem303468 {A : Type'} (lt2 : type1402 A) : (term30 A lt2) = (term88 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem303457 A lt2 P)). Qed.
Lemma lem303469 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem303470 {A : Type'} (lt2 : type1402 A) : (term1 A lt2) = (term89 A lt2).
Proof. exact (MK_COMB (@lem303469 A) (@lem303468 A lt2)). Qed.
Lemma lem303472 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem303473 {A : Type'} (P : A -> Prop) : (term31 A P) = (term32 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem303474 {A : Type'} (P : A -> Prop) : (term33 A P) = (term34 A P).
Proof. exact (@lem303473 A (term24 A P)). Qed.
Lemma lem303475 {A : Type'} (P : A -> Prop) (x : A) : (term35 A P x) = (P x).
Proof. exact (eq_refl (term35 A P x)). Qed.
Lemma lem303476 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303478 {A : Type'} (P : A -> Prop) (x : A) : (term36 A P x) = (term37 A P x).
Proof. exact (MK_COMB (@lem303476) (@lem303475 A P x)). Qed.
Lemma lem303479 {A : Type'} (P : A -> Prop) : (term38 A P) = (term39 A P).
Proof. exact (fun_ext (fun x : A => @lem303478 A P x)). Qed.
Lemma lem303480 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303481 {A : Type'} (P : A -> Prop) : (term34 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem303480 A) (@lem303479 A P)). Qed.
Lemma lem303482 {A : Type'} (P : A -> Prop) : (term33 A P) = (term32 A P).
Proof. exact (TRANS (@lem303474 A P) (@lem303481 A P)). Qed.
Lemma lem303483 {A : Type'} (P : A -> Prop) : (term24 A P) = (term24 A P).
Proof. exact (fun_ext (fun x : A => @lem303472 A P x)). Qed.
Lemma lem303484 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303485 {A : Type'} (P : A -> Prop) : (term25 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem303484 A) (@lem303483 A P)). Qed.
Lemma lem303493 {A : Type'} (P : A -> Prop) (y : A) : (term40 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem303495 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term41 A lt2 y x) = (term41 A lt2 y x).
Proof. exact (eq_refl (term41 A lt2 y x)). Qed.
Lemma lem303496 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term42 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (MK_COMB (@lem303495 A lt2 y x) (@lem303493 A P y)). Qed.
Lemma lem303497 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term44 A lt2 x P y) = (term42 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term37 A P y)). Qed.
Lemma lem303498 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term44 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (TRANS (@lem303497 A lt2 x P y) (@lem303496 A lt2 x P y)). Qed.
Lemma lem303503 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term17 A lt2 x P y) = (term45 A lt2 x P y).
Proof. exact (@lem17265 (lt2 y x) (term37 A P y)). Qed.
Lemma lem303504 {A : Type'} (P : A -> Prop) : (term46 A P) = (term47 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem303505 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term48 A lt2 x P) = (term49 A lt2 x P).
Proof. exact (@lem303504 A (term18 A lt2 x P)). Qed.
Lemma lem303506 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term50 A lt2 x P y) = (term17 A lt2 x P y).
Proof. exact (eq_refl (term50 A lt2 x P y)). Qed.
Lemma lem303507 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303508 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term44 A lt2 x P y).
Proof. exact (MK_COMB (@lem303507) (@lem303506 A lt2 x P y)). Qed.
Lemma lem303509 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (TRANS (@lem303508 A lt2 x P y) (@lem303498 A lt2 x P y)). Qed.
Lemma lem303510 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term52 A lt2 x P) = (term53 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem303509 A lt2 x P y)). Qed.
Lemma lem303511 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303512 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term49 A lt2 x P) = (term54 A lt2 x P).
Proof. exact (MK_COMB (@lem303511 A) (@lem303510 A lt2 x P)). Qed.
Lemma lem303513 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term48 A lt2 x P) = (term54 A lt2 x P).
Proof. exact (TRANS (@lem303505 A lt2 x P) (@lem303512 A lt2 x P)). Qed.
Lemma lem303514 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term18 A lt2 x P) = (term55 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem303503 A lt2 x P y)). Qed.
Lemma lem303515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303516 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term19 A lt2 x P) = (term56 A lt2 x P).
Proof. exact (MK_COMB (@lem303515 A) (@lem303514 A lt2 x P)). Qed.
Lemma lem303518 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem303519 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term58 A lt2 x P) = (term59 A lt2 x P).
Proof. exact (MK_COMB (@lem303518 A P x) (@lem303513 A lt2 x P)). Qed.
Lemma lem303520 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term60 A lt2 x P) = (term58 A lt2 x P).
Proof. exact (@lem17045 (P x) (term19 A lt2 x P)). Qed.
Lemma lem303521 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term60 A lt2 x P) = (term59 A lt2 x P).
Proof. exact (TRANS (@lem303520 A lt2 x P) (@lem303519 A lt2 x P)). Qed.
Lemma lem303523 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem303524 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term21 A lt2 x P) = (term61 A lt2 x P).
Proof. exact (MK_COMB (@lem303523 A P x) (@lem303516 A lt2 x P)). Qed.
Lemma lem303525 {A : Type'} (P : A -> Prop) : (term31 A P) = (term32 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem303526 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term62 A lt2 P) = (term63 A lt2 P).
Proof. exact (@lem303525 A (term22 A lt2 P)). Qed.
Lemma lem303527 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term64 A lt2 P x) = (term21 A lt2 x P).
Proof. exact (eq_refl (term64 A lt2 P x)). Qed.
Lemma lem303528 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303529 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 P x) = (term60 A lt2 x P).
Proof. exact (MK_COMB (@lem303528) (@lem303527 A lt2 x P)). Qed.
Lemma lem303530 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 P x) = (term59 A lt2 x P).
Proof. exact (TRANS (@lem303529 A lt2 x P) (@lem303521 A lt2 x P)). Qed.
Lemma lem303531 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term66 A lt2 P) = (term67 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem303530 A lt2 x P)). Qed.
Lemma lem303532 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem303533 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term63 A lt2 P) = (term68 A lt2 P).
Proof. exact (MK_COMB (@lem303532 A) (@lem303531 A lt2 P)). Qed.
Lemma lem303534 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term62 A lt2 P) = (term68 A lt2 P).
Proof. exact (TRANS (@lem303526 A lt2 P) (@lem303533 A lt2 P)). Qed.
Lemma lem303535 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term22 A lt2 P) = (term69 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem303524 A lt2 x P)). Qed.
Lemma lem303536 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem303537 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term23 A lt2 P) = (term70 A lt2 P).
Proof. exact (MK_COMB (@lem303536 A) (@lem303535 A lt2 P)). Qed.
Lemma lem303538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem303539 {A : Type'} (P : A -> Prop) : (term75 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem303538) (@lem303482 A P)). Qed.
Lemma lem303540 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term90 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem303539 A P) (@lem303534 A lt2 P)). Qed.
Lemma lem303541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem303542 {A : Type'} (P : A -> Prop) : (term92 A P) = (term92 A P).
Proof. exact (MK_COMB (@lem303541) (@lem303485 A P)). Qed.
Lemma lem303543 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term93 A lt2 P) = (term94 A lt2 P).
Proof. exact (MK_COMB (@lem303542 A P) (@lem303537 A lt2 P)). Qed.
Lemma lem303544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem303545 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term95 A lt2 P) = (term96 A lt2 P).
Proof. exact (MK_COMB (@lem303544) (@lem303543 A lt2 P)). Qed.
Lemma lem303546 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term97 A lt2 P) = (term98 A lt2 P).
Proof. exact (MK_COMB (@lem303545 A lt2 P) (@lem303540 A lt2 P)). Qed.
Lemma lem303547 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term99 A lt2 P) = (term97 A lt2 P).
Proof. exact (@lem17930 (term25 A P) (term23 A lt2 P)). Qed.
Lemma lem303548 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term99 A lt2 P) = (term98 A lt2 P).
Proof. exact (TRANS (@lem303547 A lt2 P) (@lem303546 A lt2 P)). Qed.
Lemma lem303549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem303550 {A : Type'} (P : A -> Prop) : (term75 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem303549) (@lem303482 A P)). Qed.
Lemma lem303551 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term77 A lt2 P) = (term78 A lt2 P).
Proof. exact (MK_COMB (@lem303550 A P) (@lem303537 A lt2 P)). Qed.
Lemma lem303552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem303553 {A : Type'} (P : A -> Prop) : (term92 A P) = (term92 A P).
Proof. exact (MK_COMB (@lem303552) (@lem303485 A P)). Qed.
Lemma lem303554 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term100 A lt2 P) = (term101 A lt2 P).
Proof. exact (MK_COMB (@lem303553 A P) (@lem303534 A lt2 P)). Qed.
Lemma lem303555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem303556 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term102 A lt2 P) = (term103 A lt2 P).
Proof. exact (MK_COMB (@lem303555) (@lem303554 A lt2 P)). Qed.
Lemma lem303557 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term104 A lt2 P) = (term105 A lt2 P).
Proof. exact (MK_COMB (@lem303556 A lt2 P) (@lem303551 A lt2 P)). Qed.
Lemma lem303558 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term25 A P) = (term23 A lt2 P)) = (term104 A lt2 P).
Proof. exact (@lem17784 (term25 A P) (term23 A lt2 P)). Qed.
Lemma lem303559 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term25 A P) = (term23 A lt2 P)) = (term105 A lt2 P).
Proof. exact (TRANS (@lem303558 A lt2 P) (@lem303557 A lt2 P)). Qed.
Lemma lem303560 {A : Type'} (P : type686 A) : (term79 A P) = (term80 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem303561 {A : Type'} (lt2 : type1402 A) : (term106 A lt2) = (term107 A lt2).
Proof. exact (@lem303560 A (term27 A lt2)). Qed.
Lemma lem303562 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term108 A lt2 P) = ((term25 A P) = (term23 A lt2 P)).
Proof. exact (eq_refl (term108 A lt2 P)). Qed.
Lemma lem303563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem303564 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term109 A lt2 P) = (term99 A lt2 P).
Proof. exact (MK_COMB (@lem303563) (@lem303562 A lt2 P)). Qed.
Lemma lem303565 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term109 A lt2 P) = (term98 A lt2 P).
Proof. exact (TRANS (@lem303564 A lt2 P) (@lem303548 A lt2 P)). Qed.
Lemma lem303566 {A : Type'} (lt2 : type1402 A) : (term110 A lt2) = (term111 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem303565 A lt2 P)). Qed.
Lemma lem303567 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem303568 {A : Type'} (lt2 : type1402 A) : (term107 A lt2) = (term112 A lt2).
Proof. exact (MK_COMB (@lem303567 A) (@lem303566 A lt2)). Qed.
Lemma lem303569 {A : Type'} (lt2 : type1402 A) : (term106 A lt2) = (term112 A lt2).
Proof. exact (TRANS (@lem303561 A lt2) (@lem303568 A lt2)). Qed.
Lemma lem303570 {A : Type'} (lt2 : type1402 A) : (term27 A lt2) = (term113 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem303559 A lt2 P)). Qed.
Lemma lem303571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem303572 {A : Type'} (lt2 : type1402 A) : (term4 A lt2) = (term114 A lt2).
Proof. exact (MK_COMB (@lem303571 A) (@lem303570 A lt2)). Qed.
Lemma lem303573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem303574 {A : Type'} (lt2 : type1402 A) : (term115 A lt2) = (term116 A lt2).
Proof. exact (MK_COMB (@lem303573) (@lem303467 A lt2)). Qed.
Lemma lem303575 {A : Type'} (lt2 : type1402 A) : (term117 A lt2) = (term118 A lt2).
Proof. exact (MK_COMB (@lem303574 A lt2) (@lem303572 A lt2)). Qed.
Lemma lem303576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem303577 {A : Type'} (lt2 : type1402 A) : (term119 A lt2) = (term120 A lt2).
Proof. exact (MK_COMB (@lem303576) (@lem303470 A lt2)). Qed.
Lemma lem303578 {A : Type'} (lt2 : type1402 A) : (term121 A lt2) = (term122 A lt2).
Proof. exact (MK_COMB (@lem303577 A lt2) (@lem303569 A lt2)). Qed.
Lemma lem303579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem303580 {A : Type'} (lt2 : type1402 A) : (term123 A lt2) = (term124 A lt2).
Proof. exact (MK_COMB (@lem303579) (@lem303578 A lt2)). Qed.
Lemma lem303581 {A : Type'} (lt2 : type1402 A) : (term125 A lt2) = (term126 A lt2).
Proof. exact (MK_COMB (@lem303580 A lt2) (@lem303575 A lt2)). Qed.
Lemma lem303582 {A : Type'} (lt2 : type1402 A) : (term7 A lt2) = (term125 A lt2).
Proof. exact (@lem17646 (term1 A lt2) (term4 A lt2)). Qed.
Lemma lem303583 {A : Type'} (lt2 : type1402 A) : (term7 A lt2) = (term126 A lt2).
Proof. exact (TRANS (@lem303582 A lt2) (@lem303581 A lt2)). Qed.
Lemma lem304057 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem304058 {A : Type'} (P : type686 A) (Q : type686 A) : (term129 A P Q) = (term130 A P Q).
Proof. exact (@lem304057 (A -> Prop) P Q). Qed.
Lemma lem304059 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term132 A lt2).
Proof. exact (@lem304058 A (term133 A lt2) (term88 A lt2)). Qed.
Lemma lem304060 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term134 A lt2 P) = (term101 A lt2 P).
Proof. exact (eq_refl (term134 A lt2 P)). Qed.
Lemma lem304061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304062 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term135 A lt2 P) = (term103 A lt2 P).
Proof. exact (MK_COMB (@lem304061) (@lem304060 A lt2 P)). Qed.
Lemma lem304063 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term136 A lt2 P) = (term78 A lt2 P).
Proof. exact (eq_refl (term136 A lt2 P)). Qed.
Lemma lem304064 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term137 A lt2 P) = (term105 A lt2 P).
Proof. exact (MK_COMB (@lem304062 A lt2 P) (@lem304063 A lt2 P)). Qed.
Lemma lem304065 {A : Type'} (lt2 : type1402 A) : (term138 A lt2) = (term113 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304064 A lt2 P)). Qed.
Lemma lem304066 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304067 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term114 A lt2).
Proof. exact (MK_COMB (@lem304066 A) (@lem304065 A lt2)). Qed.
Lemma lem304068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304069 {A : Type'} (lt2 : type1402 A) : (term139 A lt2) = (term140 A lt2).
Proof. exact (MK_COMB (@lem304068) (@lem304067 A lt2)). Qed.
Lemma lem304070 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term134 A lt2 P) = (term101 A lt2 P).
Proof. exact (eq_refl (term134 A lt2 P)). Qed.
Lemma lem304071 {A : Type'} (lt2 : type1402 A) : (term141 A lt2) = (term133 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304070 A lt2 P)). Qed.
Lemma lem304072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304073 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (MK_COMB (@lem304072 A) (@lem304071 A lt2)). Qed.
Lemma lem304074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304075 {A : Type'} (lt2 : type1402 A) : (term144 A lt2) = (term145 A lt2).
Proof. exact (MK_COMB (@lem304074) (@lem304073 A lt2)). Qed.
Lemma lem304076 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term136 A lt2 P) = (term78 A lt2 P).
Proof. exact (eq_refl (term136 A lt2 P)). Qed.
Lemma lem304077 {A : Type'} (lt2 : type1402 A) : (term146 A lt2) = (term88 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304076 A lt2 P)). Qed.
Lemma lem304078 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304079 {A : Type'} (lt2 : type1402 A) : (term147 A lt2) = (term89 A lt2).
Proof. exact (MK_COMB (@lem304078 A) (@lem304077 A lt2)). Qed.
Lemma lem304080 {A : Type'} (lt2 : type1402 A) : (term132 A lt2) = (term148 A lt2).
Proof. exact (MK_COMB (@lem304075 A lt2) (@lem304079 A lt2)). Qed.
Lemma lem304081 {A : Type'} (lt2 : type1402 A) : ((term131 A lt2) = (term132 A lt2)) = ((term114 A lt2) = (term148 A lt2)).
Proof. exact (MK_COMB (@lem304069 A lt2) (@lem304080 A lt2)). Qed.
Lemma lem304082 {A : Type'} (lt2 : type1402 A) : (term114 A lt2) = (term148 A lt2).
Proof. exact (EQ_MP (@lem304081 A lt2) (@lem304059 A lt2)). Qed.
Lemma lem304343 {A : Type'} (lt2 : type1402 A) : (term116 A lt2) = (term116 A lt2).
Proof. exact (eq_refl (term116 A lt2)). Qed.
Lemma lem304344 {A : Type'} (lt2 : type1402 A) : (term118 A lt2) = (term149 A lt2).
Proof. exact (MK_COMB (@lem304343 A lt2) (@lem304082 A lt2)). Qed.
Lemma lem304345 {A : Type'} (lt2 : type1402 A) : (term124 A lt2) = (term124 A lt2).
Proof. exact (eq_refl (term124 A lt2)). Qed.
Lemma lem304346 {A : Type'} (lt2 : type1402 A) : (term126 A lt2) = (term150 A lt2).
Proof. exact (MK_COMB (@lem304345 A lt2) (@lem304344 A lt2)). Qed.
Lemma lem304348 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem304349 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem304348 A P Q). Qed.
Lemma lem304350 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term153 A lt2 P) = (term154 A lt2 P).
Proof. exact (@lem304349 A (term32 A P) (term69 A lt2 P)). Qed.
Lemma lem304351 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 P x) = (term61 A lt2 x P).
Proof. exact (eq_refl (term155 A lt2 P x)). Qed.
Lemma lem304352 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term156 A lt2 P) = (term69 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304351 A lt2 x P)). Qed.
Lemma lem304353 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304354 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term157 A lt2 P) = (term70 A lt2 P).
Proof. exact (MK_COMB (@lem304353 A) (@lem304352 A lt2 P)). Qed.
Lemma lem304355 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem304356 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term153 A lt2 P) = (term78 A lt2 P).
Proof. exact (MK_COMB (@lem304355 A P) (@lem304354 A lt2 P)). Qed.
Lemma lem304357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304358 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term158 A lt2 P) = (term159 A lt2 P).
Proof. exact (MK_COMB (@lem304357) (@lem304356 A lt2 P)). Qed.
Lemma lem304359 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 P x) = (term61 A lt2 x P).
Proof. exact (eq_refl (term155 A lt2 P x)). Qed.
Lemma lem304360 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem304361 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term160 A lt2 P x) = (term161 A lt2 x P).
Proof. exact (MK_COMB (@lem304360 A P) (@lem304359 A lt2 x P)). Qed.
Lemma lem304362 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term162 A lt2 P) = (term163 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304361 A lt2 x P)). Qed.
Lemma lem304363 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304364 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term154 A lt2 P) = (term164 A lt2 P).
Proof. exact (MK_COMB (@lem304363 A) (@lem304362 A lt2 P)). Qed.
Lemma lem304365 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term153 A lt2 P) = (term154 A lt2 P)) = ((term78 A lt2 P) = (term164 A lt2 P)).
Proof. exact (MK_COMB (@lem304358 A lt2 P) (@lem304364 A lt2 P)). Qed.
Lemma lem304366 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term78 A lt2 P) = (term164 A lt2 P).
Proof. exact (EQ_MP (@lem304365 A lt2 P) (@lem304350 A lt2 P)). Qed.
Lemma lem304367 {A : Type'} (lt2 : type1402 A) : (term88 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304366 A lt2 P)). Qed.
Lemma lem304368 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304369 {A : Type'} (lt2 : type1402 A) : (term89 A lt2) = (term166 A lt2).
Proof. exact (MK_COMB (@lem304368 A) (@lem304367 A lt2)). Qed.
Lemma lem304371 {A B : Type'} (P : type1413 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem304372 {A : Type'} (P : type672 A) : (term169 A P) = (term170 A P).
Proof. exact (@lem304371 (A -> Prop) A P). Qed.
Lemma lem304373 {A : Type'} (lt2 : type1402 A) : (term171 A lt2) = (term172 A lt2).
Proof. exact (@lem304372 A (term173 A lt2)). Qed.
Lemma lem304374 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term174 A lt2 P) = (term163 A lt2 P).
Proof. exact (eq_refl (term174 A lt2 P)). Qed.
Lemma lem304375 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem304376 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term175 A lt2 P x) = (term176 A lt2 P x).
Proof. exact (MK_COMB (@lem304374 A lt2 P) (@lem304375 A x)). Qed.
Lemma lem304377 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term176 A lt2 P x) = (term161 A lt2 x P).
Proof. exact (eq_refl (term176 A lt2 P x)). Qed.
Lemma lem304378 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term175 A lt2 P x) = (term161 A lt2 x P).
Proof. exact (TRANS (@lem304376 A lt2 P x) (@lem304377 A lt2 x P)). Qed.
Lemma lem304379 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term177 A lt2 P) = (term163 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304378 A lt2 x P)). Qed.
Lemma lem304380 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304381 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term178 A lt2 P) = (term164 A lt2 P).
Proof. exact (MK_COMB (@lem304380 A) (@lem304379 A lt2 P)). Qed.
Lemma lem304382 {A : Type'} (lt2 : type1402 A) : (term179 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304381 A lt2 P)). Qed.
Lemma lem304383 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304384 {A : Type'} (lt2 : type1402 A) : (term171 A lt2) = (term166 A lt2).
Proof. exact (MK_COMB (@lem304383 A) (@lem304382 A lt2)). Qed.
Lemma lem304385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304386 {A : Type'} (lt2 : type1402 A) : (term180 A lt2) = (term181 A lt2).
Proof. exact (MK_COMB (@lem304385) (@lem304384 A lt2)). Qed.
Lemma lem304387 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term174 A lt2 P) = (term163 A lt2 P).
Proof. exact (eq_refl (term174 A lt2 P)). Qed.
Lemma lem304388 {A : Type'} (x : type684 A) (P : A -> Prop) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem304389 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term182 A lt2 x P) = (term183 A lt2 x P).
Proof. exact (MK_COMB (@lem304387 A lt2 P) (@lem304388 A x P)). Qed.
Lemma lem304390 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term183 A lt2 x P) = (term184 A lt2 x P).
Proof. exact (eq_refl (term183 A lt2 x P)). Qed.
Lemma lem304391 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term182 A lt2 x P) = (term184 A lt2 x P).
Proof. exact (TRANS (@lem304389 A lt2 x P) (@lem304390 A lt2 x P)). Qed.
Lemma lem304392 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term185 A lt2 x) = (term186 A lt2 x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304391 A lt2 x P)). Qed.
Lemma lem304393 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304394 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term187 A lt2 x) = (term188 A lt2 x).
Proof. exact (MK_COMB (@lem304393 A) (@lem304392 A lt2 x)). Qed.
Lemma lem304395 {A : Type'} (lt2 : type1402 A) : (term189 A lt2) = (term190 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304394 A lt2 x)). Qed.
Lemma lem304396 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304397 {A : Type'} (lt2 : type1402 A) : (term172 A lt2) = (term191 A lt2).
Proof. exact (MK_COMB (@lem304396 A) (@lem304395 A lt2)). Qed.
Lemma lem304398 {A : Type'} (lt2 : type1402 A) : ((term171 A lt2) = (term172 A lt2)) = ((term166 A lt2) = (term191 A lt2)).
Proof. exact (MK_COMB (@lem304386 A lt2) (@lem304397 A lt2)). Qed.
Lemma lem304399 {A : Type'} (lt2 : type1402 A) : (term166 A lt2) = (term191 A lt2).
Proof. exact (EQ_MP (@lem304398 A lt2) (@lem304373 A lt2)). Qed.
Lemma lem304400 {A : Type'} (lt2 : type1402 A) : (term89 A lt2) = (term191 A lt2).
Proof. exact (TRANS (@lem304369 A lt2) (@lem304399 A lt2)). Qed.
Lemma lem304401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304402 {A : Type'} (lt2 : type1402 A) : (term120 A lt2) = (term192 A lt2).
Proof. exact (MK_COMB (@lem304401) (@lem304400 A lt2)). Qed.
Lemma lem304404 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem304405 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (@lem304404 A P Q). Qed.
Lemma lem304406 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term195 A lt2 P) = (term196 A lt2 P).
Proof. exact (@lem304405 A P (term69 A lt2 P)). Qed.
Lemma lem304407 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 P x) = (term61 A lt2 x P).
Proof. exact (eq_refl (term155 A lt2 P x)). Qed.
Lemma lem304408 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term156 A lt2 P) = (term69 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304407 A lt2 x P)). Qed.
Lemma lem304409 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304410 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term157 A lt2 P) = (term70 A lt2 P).
Proof. exact (MK_COMB (@lem304409 A) (@lem304408 A lt2 P)). Qed.
Lemma lem304411 {A : Type'} (P : A -> Prop) : (term92 A P) = (term92 A P).
Proof. exact (eq_refl (term92 A P)). Qed.
Lemma lem304412 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term195 A lt2 P) = (term94 A lt2 P).
Proof. exact (MK_COMB (@lem304411 A P) (@lem304410 A lt2 P)). Qed.
Lemma lem304413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304414 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term197 A lt2 P) = (term198 A lt2 P).
Proof. exact (MK_COMB (@lem304413) (@lem304412 A lt2 P)). Qed.
Lemma lem304415 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 P x) = (term61 A lt2 x P).
Proof. exact (eq_refl (term155 A lt2 P x)). Qed.
Lemma lem304416 {A : Type'} (P : A -> Prop) (x : A) : (term199 A P x) = (term199 A P x).
Proof. exact (eq_refl (term199 A P x)). Qed.
Lemma lem304417 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term200 A lt2 P x) = (term201 A lt2 x P).
Proof. exact (MK_COMB (@lem304416 A P x) (@lem304415 A lt2 x P)). Qed.
Lemma lem304418 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term202 A lt2 P) = (term203 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304417 A lt2 x P)). Qed.
Lemma lem304419 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304420 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term196 A lt2 P) = (term204 A lt2 P).
Proof. exact (MK_COMB (@lem304419 A) (@lem304418 A lt2 P)). Qed.
Lemma lem304421 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term195 A lt2 P) = (term196 A lt2 P)) = ((term94 A lt2 P) = (term204 A lt2 P)).
Proof. exact (MK_COMB (@lem304414 A lt2 P) (@lem304420 A lt2 P)). Qed.
Lemma lem304422 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term94 A lt2 P) = (term204 A lt2 P).
Proof. exact (EQ_MP (@lem304421 A lt2 P) (@lem304406 A lt2 P)). Qed.
Lemma lem304423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304424 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term205 A lt2 P).
Proof. exact (MK_COMB (@lem304423) (@lem304422 A lt2 P)). Qed.
Lemma lem304426 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem304427 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem304426 A P Q). Qed.
Lemma lem304428 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term206 A lt2 x P) = (term207 A lt2 x P).
Proof. exact (@lem304427 A (term37 A P x) (term53 A lt2 x P)). Qed.
Lemma lem304429 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term208 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (eq_refl (term208 A lt2 x P y)). Qed.
Lemma lem304430 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term209 A lt2 x P) = (term53 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304429 A lt2 x P y)). Qed.
Lemma lem304431 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304432 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term210 A lt2 x P) = (term54 A lt2 x P).
Proof. exact (MK_COMB (@lem304431 A) (@lem304430 A lt2 x P)). Qed.
Lemma lem304433 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem304434 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term206 A lt2 x P) = (term59 A lt2 x P).
Proof. exact (MK_COMB (@lem304433 A P x) (@lem304432 A lt2 x P)). Qed.
Lemma lem304435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304436 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term211 A lt2 x P) = (term212 A lt2 x P).
Proof. exact (MK_COMB (@lem304435) (@lem304434 A lt2 x P)). Qed.
Lemma lem304437 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term208 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (eq_refl (term208 A lt2 x P y)). Qed.
Lemma lem304438 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem304439 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term213 A lt2 x P y) = (term214 A lt2 x P y).
Proof. exact (MK_COMB (@lem304438 A P x) (@lem304437 A lt2 x P y)). Qed.
Lemma lem304440 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term215 A lt2 x P) = (term216 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304439 A lt2 x P y)). Qed.
Lemma lem304441 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304442 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term207 A lt2 x P) = (term217 A lt2 x P).
Proof. exact (MK_COMB (@lem304441 A) (@lem304440 A lt2 x P)). Qed.
Lemma lem304443 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term206 A lt2 x P) = (term207 A lt2 x P)) = ((term59 A lt2 x P) = (term217 A lt2 x P)).
Proof. exact (MK_COMB (@lem304436 A lt2 x P) (@lem304442 A lt2 x P)). Qed.
Lemma lem304444 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term59 A lt2 x P) = (term217 A lt2 x P).
Proof. exact (EQ_MP (@lem304443 A lt2 x P) (@lem304428 A lt2 x P)). Qed.
Lemma lem304445 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term67 A lt2 P) = (term218 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304444 A lt2 x P)). Qed.
Lemma lem304446 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304447 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term219 A lt2 P).
Proof. exact (MK_COMB (@lem304446 A) (@lem304445 A lt2 P)). Qed.
Lemma lem304449 {A B : Type'} (P : type1413 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem304450 {A : Type'} (P : type1402 A) : (term220 A P) = (term221 A P).
Proof. exact (@lem304449 A A P). Qed.
Lemma lem304451 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term222 A lt2 P) = (term223 A lt2 P).
Proof. exact (@lem304450 A (term224 A lt2 P)). Qed.
Lemma lem304452 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term225 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (eq_refl (term225 A lt2 P x)). Qed.
Lemma lem304453 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem304454 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term226 A lt2 P x y) = (term227 A lt2 x P y).
Proof. exact (MK_COMB (@lem304452 A lt2 x P) (@lem304453 A y)). Qed.
Lemma lem304455 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term227 A lt2 x P y) = (term214 A lt2 x P y).
Proof. exact (eq_refl (term227 A lt2 x P y)). Qed.
Lemma lem304456 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term226 A lt2 P x y) = (term214 A lt2 x P y).
Proof. exact (TRANS (@lem304454 A lt2 x P y) (@lem304455 A lt2 x P y)). Qed.
Lemma lem304457 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term228 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304456 A lt2 x P y)). Qed.
Lemma lem304458 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304459 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term229 A lt2 P x) = (term217 A lt2 x P).
Proof. exact (MK_COMB (@lem304458 A) (@lem304457 A lt2 x P)). Qed.
Lemma lem304460 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term230 A lt2 P) = (term218 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304459 A lt2 x P)). Qed.
Lemma lem304461 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304462 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term222 A lt2 P) = (term219 A lt2 P).
Proof. exact (MK_COMB (@lem304461 A) (@lem304460 A lt2 P)). Qed.
Lemma lem304463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304464 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term231 A lt2 P) = (term232 A lt2 P).
Proof. exact (MK_COMB (@lem304463) (@lem304462 A lt2 P)). Qed.
Lemma lem304465 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term225 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (eq_refl (term225 A lt2 P x)). Qed.
Lemma lem304466 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem304467 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term233 A lt2 P y x) = (term234 A lt2 P y x).
Proof. exact (MK_COMB (@lem304465 A lt2 x P) (@lem304466 A y x)). Qed.
Lemma lem304468 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term234 A lt2 P y x) = (term235 A lt2 P y x).
Proof. exact (eq_refl (term234 A lt2 P y x)). Qed.
Lemma lem304469 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term233 A lt2 P y x) = (term235 A lt2 P y x).
Proof. exact (TRANS (@lem304467 A lt2 P y x) (@lem304468 A lt2 P y x)). Qed.
Lemma lem304470 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term236 A lt2 P y) = (term237 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem304469 A lt2 P y x)). Qed.
Lemma lem304471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304472 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term238 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (MK_COMB (@lem304471 A) (@lem304470 A lt2 P y)). Qed.
Lemma lem304473 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term240 A lt2 P) = (term241 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304472 A lt2 P y)). Qed.
Lemma lem304474 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304475 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term223 A lt2 P) = (term242 A lt2 P).
Proof. exact (MK_COMB (@lem304474 A) (@lem304473 A lt2 P)). Qed.
Lemma lem304476 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term222 A lt2 P) = (term223 A lt2 P)) = ((term219 A lt2 P) = (term242 A lt2 P)).
Proof. exact (MK_COMB (@lem304464 A lt2 P) (@lem304475 A lt2 P)). Qed.
Lemma lem304477 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term219 A lt2 P) = (term242 A lt2 P).
Proof. exact (EQ_MP (@lem304476 A lt2 P) (@lem304451 A lt2 P)). Qed.
Lemma lem304478 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term242 A lt2 P).
Proof. exact (TRANS (@lem304447 A lt2 P) (@lem304477 A lt2 P)). Qed.
Lemma lem304479 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem304480 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term91 A lt2 P) = (term243 A lt2 P).
Proof. exact (MK_COMB (@lem304479 A P) (@lem304478 A lt2 P)). Qed.
Lemma lem304482 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem304483 {A : Type'} (P : Prop) (Q : type488 A) : (term244 A P Q) = (term245 A P Q).
Proof. exact (@lem304482 (A -> A) P Q). Qed.
Lemma lem304484 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term246 A lt2 P) = (term247 A lt2 P).
Proof. exact (@lem304483 A (term32 A P) (term241 A lt2 P)). Qed.
Lemma lem304485 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term248 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (eq_refl (term248 A lt2 P y)). Qed.
Lemma lem304486 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term249 A lt2 P) = (term241 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304485 A lt2 P y)). Qed.
Lemma lem304487 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304488 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term250 A lt2 P) = (term242 A lt2 P).
Proof. exact (MK_COMB (@lem304487 A) (@lem304486 A lt2 P)). Qed.
Lemma lem304489 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem304490 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term246 A lt2 P) = (term243 A lt2 P).
Proof. exact (MK_COMB (@lem304489 A P) (@lem304488 A lt2 P)). Qed.
Lemma lem304491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304492 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term251 A lt2 P) = (term252 A lt2 P).
Proof. exact (MK_COMB (@lem304491) (@lem304490 A lt2 P)). Qed.
Lemma lem304493 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term248 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (eq_refl (term248 A lt2 P y)). Qed.
Lemma lem304494 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem304495 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term253 A lt2 P y) = (term254 A lt2 P y).
Proof. exact (MK_COMB (@lem304494 A P) (@lem304493 A lt2 P y)). Qed.
Lemma lem304496 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term255 A lt2 P) = (term256 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304495 A lt2 P y)). Qed.
Lemma lem304497 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304498 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term247 A lt2 P) = (term257 A lt2 P).
Proof. exact (MK_COMB (@lem304497 A) (@lem304496 A lt2 P)). Qed.
Lemma lem304499 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term246 A lt2 P) = (term247 A lt2 P)) = ((term243 A lt2 P) = (term257 A lt2 P)).
Proof. exact (MK_COMB (@lem304492 A lt2 P) (@lem304498 A lt2 P)). Qed.
Lemma lem304500 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term243 A lt2 P) = (term257 A lt2 P).
Proof. exact (EQ_MP (@lem304499 A lt2 P) (@lem304484 A lt2 P)). Qed.
Lemma lem304501 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term91 A lt2 P) = (term257 A lt2 P).
Proof. exact (TRANS (@lem304480 A lt2 P) (@lem304500 A lt2 P)). Qed.
Lemma lem304502 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term98 A lt2 P) = (term258 A lt2 P).
Proof. exact (MK_COMB (@lem304424 A lt2 P) (@lem304501 A lt2 P)). Qed.
Lemma lem304504 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem304505 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem304504 A P Q). Qed.
Lemma lem304506 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term261 A lt2 P) = (term262 A lt2 P).
Proof. exact (@lem304505 A (term203 A lt2 P) (term257 A lt2 P)). Qed.
Lemma lem304507 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term263 A lt2 P x) = (term201 A lt2 x P).
Proof. exact (eq_refl (term263 A lt2 P x)). Qed.
Lemma lem304508 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term264 A lt2 P) = (term203 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304507 A lt2 x P)). Qed.
Lemma lem304509 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304510 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term265 A lt2 P) = (term204 A lt2 P).
Proof. exact (MK_COMB (@lem304509 A) (@lem304508 A lt2 P)). Qed.
Lemma lem304511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304512 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term266 A lt2 P) = (term205 A lt2 P).
Proof. exact (MK_COMB (@lem304511) (@lem304510 A lt2 P)). Qed.
Lemma lem304513 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term257 A lt2 P) = (term257 A lt2 P).
Proof. exact (eq_refl (term257 A lt2 P)). Qed.
Lemma lem304514 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term261 A lt2 P) = (term258 A lt2 P).
Proof. exact (MK_COMB (@lem304512 A lt2 P) (@lem304513 A lt2 P)). Qed.
Lemma lem304515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304516 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term267 A lt2 P) = (term268 A lt2 P).
Proof. exact (MK_COMB (@lem304515) (@lem304514 A lt2 P)). Qed.
Lemma lem304517 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term263 A lt2 P x) = (term201 A lt2 x P).
Proof. exact (eq_refl (term263 A lt2 P x)). Qed.
Lemma lem304518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304519 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term269 A lt2 P x) = (term270 A lt2 x P).
Proof. exact (MK_COMB (@lem304518) (@lem304517 A lt2 x P)). Qed.
Lemma lem304520 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term257 A lt2 P) = (term257 A lt2 P).
Proof. exact (eq_refl (term257 A lt2 P)). Qed.
Lemma lem304521 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term271 A x lt2 P) = (term272 A x lt2 P).
Proof. exact (MK_COMB (@lem304519 A lt2 x P) (@lem304520 A lt2 P)). Qed.
Lemma lem304522 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term273 A lt2 P) = (term274 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304521 A x lt2 P)). Qed.
Lemma lem304523 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304524 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term262 A lt2 P) = (term275 A lt2 P).
Proof. exact (MK_COMB (@lem304523 A) (@lem304522 A lt2 P)). Qed.
Lemma lem304525 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term261 A lt2 P) = (term262 A lt2 P)) = ((term258 A lt2 P) = (term275 A lt2 P)).
Proof. exact (MK_COMB (@lem304516 A lt2 P) (@lem304524 A lt2 P)). Qed.
Lemma lem304526 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term258 A lt2 P) = (term275 A lt2 P).
Proof. exact (EQ_MP (@lem304525 A lt2 P) (@lem304506 A lt2 P)). Qed.
Lemma lem304528 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem304529 {A : Type'} (P : Prop) (Q : type488 A) : (term278 A P Q) = (term279 A P Q).
Proof. exact (@lem304528 (A -> A) P Q). Qed.
Lemma lem304530 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term280 A x lt2 P) = (term281 A x lt2 P).
Proof. exact (@lem304529 A (term201 A lt2 x P) (term256 A lt2 P)). Qed.
Lemma lem304531 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term282 A lt2 P y) = (term254 A lt2 P y).
Proof. exact (eq_refl (term282 A lt2 P y)). Qed.
Lemma lem304532 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term283 A lt2 P) = (term256 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304531 A lt2 P y)). Qed.
Lemma lem304533 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304534 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term284 A lt2 P) = (term257 A lt2 P).
Proof. exact (MK_COMB (@lem304533 A) (@lem304532 A lt2 P)). Qed.
Lemma lem304535 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term270 A lt2 x P) = (term270 A lt2 x P).
Proof. exact (eq_refl (term270 A lt2 x P)). Qed.
Lemma lem304536 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term280 A x lt2 P) = (term272 A x lt2 P).
Proof. exact (MK_COMB (@lem304535 A lt2 x P) (@lem304534 A lt2 P)). Qed.
Lemma lem304537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304538 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term285 A x lt2 P) = (term286 A x lt2 P).
Proof. exact (MK_COMB (@lem304537) (@lem304536 A x lt2 P)). Qed.
Lemma lem304539 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term282 A lt2 P y) = (term254 A lt2 P y).
Proof. exact (eq_refl (term282 A lt2 P y)). Qed.
Lemma lem304540 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term270 A lt2 x P) = (term270 A lt2 x P).
Proof. exact (eq_refl (term270 A lt2 x P)). Qed.
Lemma lem304541 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term287 A x lt2 P y) = (term288 A x lt2 P y).
Proof. exact (MK_COMB (@lem304540 A lt2 x P) (@lem304539 A lt2 P y)). Qed.
Lemma lem304542 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term289 A x lt2 P) = (term290 A x lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304541 A x lt2 P y)). Qed.
Lemma lem304543 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304544 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term281 A x lt2 P) = (term291 A x lt2 P).
Proof. exact (MK_COMB (@lem304543 A) (@lem304542 A x lt2 P)). Qed.
Lemma lem304545 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : ((term280 A x lt2 P) = (term281 A x lt2 P)) = ((term272 A x lt2 P) = (term291 A x lt2 P)).
Proof. exact (MK_COMB (@lem304538 A x lt2 P) (@lem304544 A x lt2 P)). Qed.
Lemma lem304546 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term272 A x lt2 P) = (term291 A x lt2 P).
Proof. exact (EQ_MP (@lem304545 A x lt2 P) (@lem304530 A x lt2 P)). Qed.
Lemma lem304547 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term274 A lt2 P) = (term292 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304546 A x lt2 P)). Qed.
Lemma lem304548 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304549 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term275 A lt2 P) = (term293 A lt2 P).
Proof. exact (MK_COMB (@lem304548 A) (@lem304547 A lt2 P)). Qed.
Lemma lem304550 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term258 A lt2 P) = (term293 A lt2 P).
Proof. exact (TRANS (@lem304526 A lt2 P) (@lem304549 A lt2 P)). Qed.
Lemma lem304551 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term98 A lt2 P) = (term293 A lt2 P).
Proof. exact (TRANS (@lem304502 A lt2 P) (@lem304550 A lt2 P)). Qed.
Lemma lem304552 {A : Type'} (lt2 : type1402 A) : (term111 A lt2) = (term294 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304551 A lt2 P)). Qed.
Lemma lem304553 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem304554 {A : Type'} (lt2 : type1402 A) : (term112 A lt2) = (term295 A lt2).
Proof. exact (MK_COMB (@lem304553 A) (@lem304552 A lt2)). Qed.
Lemma lem304555 {A : Type'} (lt2 : type1402 A) : (term122 A lt2) = (term296 A lt2).
Proof. exact (MK_COMB (@lem304402 A lt2) (@lem304554 A lt2)). Qed.
Lemma lem304557 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem304558 {A : Type'} (P : type162 A) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (@lem304557 (type684 A) P Q). Qed.
Lemma lem304559 {A : Type'} (lt2 : type1402 A) : (term299 A lt2) = (term300 A lt2).
Proof. exact (@lem304558 A (term190 A lt2) (term295 A lt2)). Qed.
Lemma lem304560 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term301 A lt2 x) = (term188 A lt2 x).
Proof. exact (eq_refl (term301 A lt2 x)). Qed.
Lemma lem304561 {A : Type'} (lt2 : type1402 A) : (term302 A lt2) = (term190 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304560 A lt2 x)). Qed.
Lemma lem304562 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304563 {A : Type'} (lt2 : type1402 A) : (term303 A lt2) = (term191 A lt2).
Proof. exact (MK_COMB (@lem304562 A) (@lem304561 A lt2)). Qed.
Lemma lem304564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304565 {A : Type'} (lt2 : type1402 A) : (term304 A lt2) = (term192 A lt2).
Proof. exact (MK_COMB (@lem304564) (@lem304563 A lt2)). Qed.
Lemma lem304566 {A : Type'} (lt2 : type1402 A) : (term295 A lt2) = (term295 A lt2).
Proof. exact (eq_refl (term295 A lt2)). Qed.
Lemma lem304567 {A : Type'} (lt2 : type1402 A) : (term299 A lt2) = (term296 A lt2).
Proof. exact (MK_COMB (@lem304565 A lt2) (@lem304566 A lt2)). Qed.
Lemma lem304568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304569 {A : Type'} (lt2 : type1402 A) : (term305 A lt2) = (term306 A lt2).
Proof. exact (MK_COMB (@lem304568) (@lem304567 A lt2)). Qed.
Lemma lem304570 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term301 A lt2 x) = (term188 A lt2 x).
Proof. exact (eq_refl (term301 A lt2 x)). Qed.
Lemma lem304571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304572 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term307 A lt2 x) = (term308 A lt2 x).
Proof. exact (MK_COMB (@lem304571) (@lem304570 A lt2 x)). Qed.
Lemma lem304573 {A : Type'} (lt2 : type1402 A) : (term295 A lt2) = (term295 A lt2).
Proof. exact (eq_refl (term295 A lt2)). Qed.
Lemma lem304574 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term309 A x lt2) = (term310 A x lt2).
Proof. exact (MK_COMB (@lem304572 A lt2 x) (@lem304573 A lt2)). Qed.
Lemma lem304575 {A : Type'} (lt2 : type1402 A) : (term311 A lt2) = (term312 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304574 A x lt2)). Qed.
Lemma lem304576 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304577 {A : Type'} (lt2 : type1402 A) : (term300 A lt2) = (term313 A lt2).
Proof. exact (MK_COMB (@lem304576 A) (@lem304575 A lt2)). Qed.
Lemma lem304578 {A : Type'} (lt2 : type1402 A) : ((term299 A lt2) = (term300 A lt2)) = ((term296 A lt2) = (term313 A lt2)).
Proof. exact (MK_COMB (@lem304569 A lt2) (@lem304577 A lt2)). Qed.
Lemma lem304579 {A : Type'} (lt2 : type1402 A) : (term296 A lt2) = (term313 A lt2).
Proof. exact (EQ_MP (@lem304578 A lt2) (@lem304559 A lt2)). Qed.
Lemma lem304581 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem304582 {A : Type'} (P : Prop) (Q : type686 A) : (term314 A P Q) = (term315 A P Q).
Proof. exact (@lem304581 (A -> Prop) P Q). Qed.
Lemma lem304583 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term316 A x lt2) = (term317 A x lt2).
Proof. exact (@lem304582 A (term188 A lt2 x) (term294 A lt2)). Qed.
Lemma lem304584 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term318 A lt2 P) = (term293 A lt2 P).
Proof. exact (eq_refl (term318 A lt2 P)). Qed.
Lemma lem304585 {A : Type'} (lt2 : type1402 A) : (term319 A lt2) = (term294 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304584 A lt2 P)). Qed.
Lemma lem304586 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem304587 {A : Type'} (lt2 : type1402 A) : (term320 A lt2) = (term295 A lt2).
Proof. exact (MK_COMB (@lem304586 A) (@lem304585 A lt2)). Qed.
Lemma lem304588 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term308 A lt2 x) = (term308 A lt2 x).
Proof. exact (eq_refl (term308 A lt2 x)). Qed.
Lemma lem304589 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term316 A x lt2) = (term310 A x lt2).
Proof. exact (MK_COMB (@lem304588 A lt2 x) (@lem304587 A lt2)). Qed.
Lemma lem304590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304591 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term321 A x lt2) = (term322 A x lt2).
Proof. exact (MK_COMB (@lem304590) (@lem304589 A x lt2)). Qed.
Lemma lem304592 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term318 A lt2 P) = (term293 A lt2 P).
Proof. exact (eq_refl (term318 A lt2 P)). Qed.
Lemma lem304593 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term308 A lt2 x) = (term308 A lt2 x).
Proof. exact (eq_refl (term308 A lt2 x)). Qed.
Lemma lem304594 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term323 A x lt2 P) = (term324 A x lt2 P).
Proof. exact (MK_COMB (@lem304593 A lt2 x) (@lem304592 A lt2 P)). Qed.
Lemma lem304595 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term325 A x lt2) = (term326 A x lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304594 A x lt2 P)). Qed.
Lemma lem304596 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem304597 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term317 A x lt2) = (term327 A x lt2).
Proof. exact (MK_COMB (@lem304596 A) (@lem304595 A x lt2)). Qed.
Lemma lem304598 {A : Type'} (x : type684 A) (lt2 : type1402 A) : ((term316 A x lt2) = (term317 A x lt2)) = ((term310 A x lt2) = (term327 A x lt2)).
Proof. exact (MK_COMB (@lem304591 A x lt2) (@lem304597 A x lt2)). Qed.
Lemma lem304599 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term310 A x lt2) = (term327 A x lt2).
Proof. exact (EQ_MP (@lem304598 A x lt2) (@lem304583 A x lt2)). Qed.
Lemma lem304601 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem304602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (@lem304601 A P Q). Qed.
Lemma lem304603 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term328 A x lt2 P) = (term329 A x lt2 P).
Proof. exact (@lem304602 A (term188 A lt2 x) (term292 A lt2 P)). Qed.
Lemma lem304604 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term330 A lt2 P x) = (term291 A x lt2 P).
Proof. exact (eq_refl (term330 A lt2 P x)). Qed.
Lemma lem304605 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term331 A lt2 P) = (term292 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304604 A x lt2 P)). Qed.
Lemma lem304606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304607 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term332 A lt2 P) = (term293 A lt2 P).
Proof. exact (MK_COMB (@lem304606 A) (@lem304605 A lt2 P)). Qed.
Lemma lem304608 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term308 A lt2 x) = (term308 A lt2 x).
Proof. exact (eq_refl (term308 A lt2 x)). Qed.
Lemma lem304609 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term328 A x lt2 P) = (term324 A x lt2 P).
Proof. exact (MK_COMB (@lem304608 A lt2 x) (@lem304607 A lt2 P)). Qed.
Lemma lem304610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304611 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term333 A x lt2 P) = (term334 A x lt2 P).
Proof. exact (MK_COMB (@lem304610) (@lem304609 A x lt2 P)). Qed.
Lemma lem304612 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term330 A lt2 P x) = (term291 A x lt2 P).
Proof. exact (eq_refl (term330 A lt2 P x)). Qed.
Lemma lem304613 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term308 A lt2 x) = (term308 A lt2 x).
Proof. exact (eq_refl (term308 A lt2 x)). Qed.
Lemma lem304614 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term335 A x lt2 P x') = (term336 A x x' lt2 P).
Proof. exact (MK_COMB (@lem304613 A lt2 x) (@lem304612 A x' lt2 P)). Qed.
Lemma lem304615 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term337 A x lt2 P) = (term338 A x lt2 P).
Proof. exact (fun_ext (fun x' : A => @lem304614 A x x' lt2 P)). Qed.
Lemma lem304616 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304617 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term329 A x lt2 P) = (term339 A x lt2 P).
Proof. exact (MK_COMB (@lem304616 A) (@lem304615 A x lt2 P)). Qed.
Lemma lem304618 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : ((term328 A x lt2 P) = (term329 A x lt2 P)) = ((term324 A x lt2 P) = (term339 A x lt2 P)).
Proof. exact (MK_COMB (@lem304611 A x lt2 P) (@lem304617 A x lt2 P)). Qed.
Lemma lem304619 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term324 A x lt2 P) = (term339 A x lt2 P).
Proof. exact (EQ_MP (@lem304618 A x lt2 P) (@lem304603 A x lt2 P)). Qed.
Lemma lem304621 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem304622 {A : Type'} (P : Prop) (Q : type488 A) : (term278 A P Q) = (term279 A P Q).
Proof. exact (@lem304621 (A -> A) P Q). Qed.
Lemma lem304623 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term340 A x x' lt2 P) = (term341 A x x' lt2 P).
Proof. exact (@lem304622 A (term188 A lt2 x) (term290 A x' lt2 P)). Qed.
Lemma lem304624 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term342 A x lt2 P y) = (term288 A x lt2 P y).
Proof. exact (eq_refl (term342 A x lt2 P y)). Qed.
Lemma lem304625 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term343 A x lt2 P) = (term290 A x lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304624 A x lt2 P y)). Qed.
Lemma lem304626 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304627 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term344 A x lt2 P) = (term291 A x lt2 P).
Proof. exact (MK_COMB (@lem304626 A) (@lem304625 A x lt2 P)). Qed.
Lemma lem304628 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term308 A lt2 x) = (term308 A lt2 x).
Proof. exact (eq_refl (term308 A lt2 x)). Qed.
Lemma lem304629 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term340 A x x' lt2 P) = (term336 A x x' lt2 P).
Proof. exact (MK_COMB (@lem304628 A lt2 x) (@lem304627 A x' lt2 P)). Qed.
Lemma lem304630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304631 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term345 A x x' lt2 P) = (term346 A x x' lt2 P).
Proof. exact (MK_COMB (@lem304630) (@lem304629 A x x' lt2 P)). Qed.
Lemma lem304632 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term342 A x lt2 P y) = (term288 A x lt2 P y).
Proof. exact (eq_refl (term342 A x lt2 P y)). Qed.
Lemma lem304633 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term308 A lt2 x) = (term308 A lt2 x).
Proof. exact (eq_refl (term308 A lt2 x)). Qed.
Lemma lem304634 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term347 A x x' lt2 P y) = (term348 A x x' lt2 P y).
Proof. exact (MK_COMB (@lem304633 A lt2 x) (@lem304632 A x' lt2 P y)). Qed.
Lemma lem304635 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term349 A x x' lt2 P) = (term350 A x x' lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304634 A x x' lt2 P y)). Qed.
Lemma lem304636 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304637 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term341 A x x' lt2 P) = (term351 A x x' lt2 P).
Proof. exact (MK_COMB (@lem304636 A) (@lem304635 A x x' lt2 P)). Qed.
Lemma lem304638 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : ((term340 A x x' lt2 P) = (term341 A x x' lt2 P)) = ((term336 A x x' lt2 P) = (term351 A x x' lt2 P)).
Proof. exact (MK_COMB (@lem304631 A x x' lt2 P) (@lem304637 A x x' lt2 P)). Qed.
Lemma lem304639 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term336 A x x' lt2 P) = (term351 A x x' lt2 P).
Proof. exact (EQ_MP (@lem304638 A x x' lt2 P) (@lem304623 A x x' lt2 P)). Qed.
Lemma lem304640 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term338 A x lt2 P) = (term352 A x lt2 P).
Proof. exact (fun_ext (fun x' : A => @lem304639 A x x' lt2 P)). Qed.
Lemma lem304641 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304642 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term339 A x lt2 P) = (term353 A x lt2 P).
Proof. exact (MK_COMB (@lem304641 A) (@lem304640 A x lt2 P)). Qed.
Lemma lem304643 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term324 A x lt2 P) = (term353 A x lt2 P).
Proof. exact (TRANS (@lem304619 A x lt2 P) (@lem304642 A x lt2 P)). Qed.
Lemma lem304644 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term326 A x lt2) = (term354 A x lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304643 A x lt2 P)). Qed.
Lemma lem304645 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem304646 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term327 A x lt2) = (term355 A x lt2).
Proof. exact (MK_COMB (@lem304645 A) (@lem304644 A x lt2)). Qed.
Lemma lem304647 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term310 A x lt2) = (term355 A x lt2).
Proof. exact (TRANS (@lem304599 A x lt2) (@lem304646 A x lt2)). Qed.
Lemma lem304648 {A : Type'} (lt2 : type1402 A) : (term312 A lt2) = (term356 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304647 A x lt2)). Qed.
Lemma lem304649 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304650 {A : Type'} (lt2 : type1402 A) : (term313 A lt2) = (term357 A lt2).
Proof. exact (MK_COMB (@lem304649 A) (@lem304648 A lt2)). Qed.
Lemma lem304651 {A : Type'} (lt2 : type1402 A) : (term296 A lt2) = (term357 A lt2).
Proof. exact (TRANS (@lem304579 A lt2) (@lem304650 A lt2)). Qed.
Lemma lem304652 {A : Type'} (lt2 : type1402 A) : (term122 A lt2) = (term357 A lt2).
Proof. exact (TRANS (@lem304555 A lt2) (@lem304651 A lt2)). Qed.
Lemma lem304653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem304654 {A : Type'} (lt2 : type1402 A) : (term124 A lt2) = (term358 A lt2).
Proof. exact (MK_COMB (@lem304653) (@lem304652 A lt2)). Qed.
Lemma lem304656 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem304657 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem304656 A P Q). Qed.
Lemma lem304658 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term206 A lt2 x P) = (term207 A lt2 x P).
Proof. exact (@lem304657 A (term37 A P x) (term53 A lt2 x P)). Qed.
Lemma lem304659 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term208 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (eq_refl (term208 A lt2 x P y)). Qed.
Lemma lem304660 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term209 A lt2 x P) = (term53 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304659 A lt2 x P y)). Qed.
Lemma lem304661 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304662 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term210 A lt2 x P) = (term54 A lt2 x P).
Proof. exact (MK_COMB (@lem304661 A) (@lem304660 A lt2 x P)). Qed.
Lemma lem304663 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem304664 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term206 A lt2 x P) = (term59 A lt2 x P).
Proof. exact (MK_COMB (@lem304663 A P x) (@lem304662 A lt2 x P)). Qed.
Lemma lem304665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304666 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term211 A lt2 x P) = (term212 A lt2 x P).
Proof. exact (MK_COMB (@lem304665) (@lem304664 A lt2 x P)). Qed.
Lemma lem304667 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term208 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (eq_refl (term208 A lt2 x P y)). Qed.
Lemma lem304668 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem304669 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term213 A lt2 x P y) = (term214 A lt2 x P y).
Proof. exact (MK_COMB (@lem304668 A P x) (@lem304667 A lt2 x P y)). Qed.
Lemma lem304670 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term215 A lt2 x P) = (term216 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304669 A lt2 x P y)). Qed.
Lemma lem304671 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304672 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term207 A lt2 x P) = (term217 A lt2 x P).
Proof. exact (MK_COMB (@lem304671 A) (@lem304670 A lt2 x P)). Qed.
Lemma lem304673 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term206 A lt2 x P) = (term207 A lt2 x P)) = ((term59 A lt2 x P) = (term217 A lt2 x P)).
Proof. exact (MK_COMB (@lem304666 A lt2 x P) (@lem304672 A lt2 x P)). Qed.
Lemma lem304674 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term59 A lt2 x P) = (term217 A lt2 x P).
Proof. exact (EQ_MP (@lem304673 A lt2 x P) (@lem304658 A lt2 x P)). Qed.
Lemma lem304675 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term67 A lt2 P) = (term218 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304674 A lt2 x P)). Qed.
Lemma lem304676 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304677 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term219 A lt2 P).
Proof. exact (MK_COMB (@lem304676 A) (@lem304675 A lt2 P)). Qed.
Lemma lem304679 {A B : Type'} (P : type1413 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem304680 {A : Type'} (P : type1402 A) : (term220 A P) = (term221 A P).
Proof. exact (@lem304679 A A P). Qed.
Lemma lem304681 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term222 A lt2 P) = (term223 A lt2 P).
Proof. exact (@lem304680 A (term224 A lt2 P)). Qed.
Lemma lem304682 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term225 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (eq_refl (term225 A lt2 P x)). Qed.
Lemma lem304683 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem304684 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term226 A lt2 P x y) = (term227 A lt2 x P y).
Proof. exact (MK_COMB (@lem304682 A lt2 x P) (@lem304683 A y)). Qed.
Lemma lem304685 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term227 A lt2 x P y) = (term214 A lt2 x P y).
Proof. exact (eq_refl (term227 A lt2 x P y)). Qed.
Lemma lem304686 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term226 A lt2 P x y) = (term214 A lt2 x P y).
Proof. exact (TRANS (@lem304684 A lt2 x P y) (@lem304685 A lt2 x P y)). Qed.
Lemma lem304687 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term228 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304686 A lt2 x P y)). Qed.
Lemma lem304688 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304689 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term229 A lt2 P x) = (term217 A lt2 x P).
Proof. exact (MK_COMB (@lem304688 A) (@lem304687 A lt2 x P)). Qed.
Lemma lem304690 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term230 A lt2 P) = (term218 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304689 A lt2 x P)). Qed.
Lemma lem304691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304692 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term222 A lt2 P) = (term219 A lt2 P).
Proof. exact (MK_COMB (@lem304691 A) (@lem304690 A lt2 P)). Qed.
Lemma lem304693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304694 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term231 A lt2 P) = (term232 A lt2 P).
Proof. exact (MK_COMB (@lem304693) (@lem304692 A lt2 P)). Qed.
Lemma lem304695 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term225 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (eq_refl (term225 A lt2 P x)). Qed.
Lemma lem304696 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem304697 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term233 A lt2 P y x) = (term234 A lt2 P y x).
Proof. exact (MK_COMB (@lem304695 A lt2 x P) (@lem304696 A y x)). Qed.
Lemma lem304698 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term234 A lt2 P y x) = (term235 A lt2 P y x).
Proof. exact (eq_refl (term234 A lt2 P y x)). Qed.
Lemma lem304699 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term233 A lt2 P y x) = (term235 A lt2 P y x).
Proof. exact (TRANS (@lem304697 A lt2 P y x) (@lem304698 A lt2 P y x)). Qed.
Lemma lem304700 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term236 A lt2 P y) = (term237 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem304699 A lt2 P y x)). Qed.
Lemma lem304701 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304702 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term238 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (MK_COMB (@lem304701 A) (@lem304700 A lt2 P y)). Qed.
Lemma lem304703 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term240 A lt2 P) = (term241 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304702 A lt2 P y)). Qed.
Lemma lem304704 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304705 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term223 A lt2 P) = (term242 A lt2 P).
Proof. exact (MK_COMB (@lem304704 A) (@lem304703 A lt2 P)). Qed.
Lemma lem304706 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term222 A lt2 P) = (term223 A lt2 P)) = ((term219 A lt2 P) = (term242 A lt2 P)).
Proof. exact (MK_COMB (@lem304694 A lt2 P) (@lem304705 A lt2 P)). Qed.
Lemma lem304707 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term219 A lt2 P) = (term242 A lt2 P).
Proof. exact (EQ_MP (@lem304706 A lt2 P) (@lem304681 A lt2 P)). Qed.
Lemma lem304708 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term242 A lt2 P).
Proof. exact (TRANS (@lem304677 A lt2 P) (@lem304707 A lt2 P)). Qed.
Lemma lem304709 {A : Type'} (P : A -> Prop) : (term71 A P) = (term71 A P).
Proof. exact (eq_refl (term71 A P)). Qed.
Lemma lem304710 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term359 A lt2 P).
Proof. exact (MK_COMB (@lem304709 A P) (@lem304708 A lt2 P)). Qed.
Lemma lem304712 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem304713 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem304712 A P Q). Qed.
Lemma lem304714 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term359 A lt2 P) = (term360 A lt2 P).
Proof. exact (@lem304713 A P (term242 A lt2 P)). Qed.
Lemma lem304716 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem304717 {A : Type'} (P : Prop) (Q : type488 A) : (term278 A P Q) = (term279 A P Q).
Proof. exact (@lem304716 (A -> A) P Q). Qed.
Lemma lem304718 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term361 A x lt2 P) = (term362 A x lt2 P).
Proof. exact (@lem304717 A (P x) (term241 A lt2 P)). Qed.
Lemma lem304719 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term248 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (eq_refl (term248 A lt2 P y)). Qed.
Lemma lem304720 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term249 A lt2 P) = (term241 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304719 A lt2 P y)). Qed.
Lemma lem304721 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304722 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term250 A lt2 P) = (term242 A lt2 P).
Proof. exact (MK_COMB (@lem304721 A) (@lem304720 A lt2 P)). Qed.
Lemma lem304723 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem304724 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term361 A x lt2 P) = (term363 A x lt2 P).
Proof. exact (MK_COMB (@lem304723 A P x) (@lem304722 A lt2 P)). Qed.
Lemma lem304725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304726 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term364 A x lt2 P) = (term365 A x lt2 P).
Proof. exact (MK_COMB (@lem304725) (@lem304724 A x lt2 P)). Qed.
Lemma lem304727 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term248 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (eq_refl (term248 A lt2 P y)). Qed.
Lemma lem304728 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem304729 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term366 A x lt2 P y) = (term367 A x lt2 P y).
Proof. exact (MK_COMB (@lem304728 A P x) (@lem304727 A lt2 P y)). Qed.
Lemma lem304730 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term368 A x lt2 P) = (term369 A x lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304729 A x lt2 P y)). Qed.
Lemma lem304731 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304732 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term362 A x lt2 P) = (term370 A x lt2 P).
Proof. exact (MK_COMB (@lem304731 A) (@lem304730 A x lt2 P)). Qed.
Lemma lem304733 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : ((term361 A x lt2 P) = (term362 A x lt2 P)) = ((term363 A x lt2 P) = (term370 A x lt2 P)).
Proof. exact (MK_COMB (@lem304726 A x lt2 P) (@lem304732 A x lt2 P)). Qed.
Lemma lem304734 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term363 A x lt2 P) = (term370 A x lt2 P).
Proof. exact (EQ_MP (@lem304733 A x lt2 P) (@lem304718 A x lt2 P)). Qed.
Lemma lem304735 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term371 A lt2 P) = (term372 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304734 A x lt2 P)). Qed.
Lemma lem304736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304737 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term360 A lt2 P) = (term373 A lt2 P).
Proof. exact (MK_COMB (@lem304736 A) (@lem304735 A lt2 P)). Qed.
Lemma lem304738 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term359 A lt2 P) = (term373 A lt2 P).
Proof. exact (TRANS (@lem304714 A lt2 P) (@lem304737 A lt2 P)). Qed.
Lemma lem304739 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term373 A lt2 P).
Proof. exact (TRANS (@lem304710 A lt2 P) (@lem304738 A lt2 P)). Qed.
Lemma lem304740 {A : Type'} (lt2 : type1402 A) : (term86 A lt2) = (term374 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304739 A lt2 P)). Qed.
Lemma lem304741 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem304742 {A : Type'} (lt2 : type1402 A) : (term87 A lt2) = (term375 A lt2).
Proof. exact (MK_COMB (@lem304741 A) (@lem304740 A lt2)). Qed.
Lemma lem304743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304744 {A : Type'} (lt2 : type1402 A) : (term116 A lt2) = (term376 A lt2).
Proof. exact (MK_COMB (@lem304743) (@lem304742 A lt2)). Qed.
Lemma lem304746 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem304747 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem304746 A P Q). Qed.
Lemma lem304748 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term206 A lt2 x P) = (term207 A lt2 x P).
Proof. exact (@lem304747 A (term37 A P x) (term53 A lt2 x P)). Qed.
Lemma lem304749 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term208 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (eq_refl (term208 A lt2 x P y)). Qed.
Lemma lem304750 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term209 A lt2 x P) = (term53 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304749 A lt2 x P y)). Qed.
Lemma lem304751 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304752 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term210 A lt2 x P) = (term54 A lt2 x P).
Proof. exact (MK_COMB (@lem304751 A) (@lem304750 A lt2 x P)). Qed.
Lemma lem304753 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem304754 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term206 A lt2 x P) = (term59 A lt2 x P).
Proof. exact (MK_COMB (@lem304753 A P x) (@lem304752 A lt2 x P)). Qed.
Lemma lem304755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304756 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term211 A lt2 x P) = (term212 A lt2 x P).
Proof. exact (MK_COMB (@lem304755) (@lem304754 A lt2 x P)). Qed.
Lemma lem304757 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term208 A lt2 x P y) = (term43 A lt2 x P y).
Proof. exact (eq_refl (term208 A lt2 x P y)). Qed.
Lemma lem304758 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term57 A P x).
Proof. exact (eq_refl (term57 A P x)). Qed.
Lemma lem304759 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term213 A lt2 x P y) = (term214 A lt2 x P y).
Proof. exact (MK_COMB (@lem304758 A P x) (@lem304757 A lt2 x P y)). Qed.
Lemma lem304760 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term215 A lt2 x P) = (term216 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304759 A lt2 x P y)). Qed.
Lemma lem304761 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304762 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term207 A lt2 x P) = (term217 A lt2 x P).
Proof. exact (MK_COMB (@lem304761 A) (@lem304760 A lt2 x P)). Qed.
Lemma lem304763 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term206 A lt2 x P) = (term207 A lt2 x P)) = ((term59 A lt2 x P) = (term217 A lt2 x P)).
Proof. exact (MK_COMB (@lem304756 A lt2 x P) (@lem304762 A lt2 x P)). Qed.
Lemma lem304764 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term59 A lt2 x P) = (term217 A lt2 x P).
Proof. exact (EQ_MP (@lem304763 A lt2 x P) (@lem304748 A lt2 x P)). Qed.
Lemma lem304765 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term67 A lt2 P) = (term218 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304764 A lt2 x P)). Qed.
Lemma lem304766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304767 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term219 A lt2 P).
Proof. exact (MK_COMB (@lem304766 A) (@lem304765 A lt2 P)). Qed.
Lemma lem304769 {A B : Type'} (P : type1413 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem304770 {A : Type'} (P : type1402 A) : (term220 A P) = (term221 A P).
Proof. exact (@lem304769 A A P). Qed.
Lemma lem304771 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term222 A lt2 P) = (term223 A lt2 P).
Proof. exact (@lem304770 A (term224 A lt2 P)). Qed.
Lemma lem304772 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term225 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (eq_refl (term225 A lt2 P x)). Qed.
Lemma lem304773 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem304774 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term226 A lt2 P x y) = (term227 A lt2 x P y).
Proof. exact (MK_COMB (@lem304772 A lt2 x P) (@lem304773 A y)). Qed.
Lemma lem304775 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term227 A lt2 x P y) = (term214 A lt2 x P y).
Proof. exact (eq_refl (term227 A lt2 x P y)). Qed.
Lemma lem304776 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term226 A lt2 P x y) = (term214 A lt2 x P y).
Proof. exact (TRANS (@lem304774 A lt2 x P y) (@lem304775 A lt2 x P y)). Qed.
Lemma lem304777 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term228 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem304776 A lt2 x P y)). Qed.
Lemma lem304778 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304779 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term229 A lt2 P x) = (term217 A lt2 x P).
Proof. exact (MK_COMB (@lem304778 A) (@lem304777 A lt2 x P)). Qed.
Lemma lem304780 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term230 A lt2 P) = (term218 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304779 A lt2 x P)). Qed.
Lemma lem304781 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304782 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term222 A lt2 P) = (term219 A lt2 P).
Proof. exact (MK_COMB (@lem304781 A) (@lem304780 A lt2 P)). Qed.
Lemma lem304783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304784 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term231 A lt2 P) = (term232 A lt2 P).
Proof. exact (MK_COMB (@lem304783) (@lem304782 A lt2 P)). Qed.
Lemma lem304785 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term225 A lt2 P x) = (term216 A lt2 x P).
Proof. exact (eq_refl (term225 A lt2 P x)). Qed.
Lemma lem304786 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem304787 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term233 A lt2 P y x) = (term234 A lt2 P y x).
Proof. exact (MK_COMB (@lem304785 A lt2 x P) (@lem304786 A y x)). Qed.
Lemma lem304788 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term234 A lt2 P y x) = (term235 A lt2 P y x).
Proof. exact (eq_refl (term234 A lt2 P y x)). Qed.
Lemma lem304789 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term233 A lt2 P y x) = (term235 A lt2 P y x).
Proof. exact (TRANS (@lem304787 A lt2 P y x) (@lem304788 A lt2 P y x)). Qed.
Lemma lem304790 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term236 A lt2 P y) = (term237 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem304789 A lt2 P y x)). Qed.
Lemma lem304791 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem304792 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term238 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (MK_COMB (@lem304791 A) (@lem304790 A lt2 P y)). Qed.
Lemma lem304793 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term240 A lt2 P) = (term241 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304792 A lt2 P y)). Qed.
Lemma lem304794 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304795 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term223 A lt2 P) = (term242 A lt2 P).
Proof. exact (MK_COMB (@lem304794 A) (@lem304793 A lt2 P)). Qed.
Lemma lem304796 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term222 A lt2 P) = (term223 A lt2 P)) = ((term219 A lt2 P) = (term242 A lt2 P)).
Proof. exact (MK_COMB (@lem304784 A lt2 P) (@lem304795 A lt2 P)). Qed.
Lemma lem304797 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term219 A lt2 P) = (term242 A lt2 P).
Proof. exact (EQ_MP (@lem304796 A lt2 P) (@lem304771 A lt2 P)). Qed.
Lemma lem304798 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term242 A lt2 P).
Proof. exact (TRANS (@lem304767 A lt2 P) (@lem304797 A lt2 P)). Qed.
Lemma lem304799 {A : Type'} (P : A -> Prop) : (term92 A P) = (term92 A P).
Proof. exact (eq_refl (term92 A P)). Qed.
Lemma lem304800 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term101 A lt2 P) = (term377 A lt2 P).
Proof. exact (MK_COMB (@lem304799 A P) (@lem304798 A lt2 P)). Qed.
Lemma lem304804 {A : Type'} (P : A -> Prop) (Q : Prop) : (term378 A P Q) = (term379 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem304805 {A : Type'} (P : A -> Prop) (Q : Prop) : (term378 A P Q) = (term379 A P Q).
Proof. exact (@lem304804 A P Q). Qed.
Lemma lem304806 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term377 A lt2 P) = (term380 A lt2 P).
Proof. exact (@lem304805 A P (term242 A lt2 P)). Qed.
Lemma lem304808 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem304809 {A : Type'} (P : Prop) (Q : type488 A) : (term244 A P Q) = (term245 A P Q).
Proof. exact (@lem304808 (A -> A) P Q). Qed.
Lemma lem304810 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term381 A x lt2 P) = (term382 A x lt2 P).
Proof. exact (@lem304809 A (P x) (term241 A lt2 P)). Qed.
Lemma lem304811 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term248 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (eq_refl (term248 A lt2 P y)). Qed.
Lemma lem304812 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term249 A lt2 P) = (term241 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304811 A lt2 P y)). Qed.
Lemma lem304813 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304814 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term250 A lt2 P) = (term242 A lt2 P).
Proof. exact (MK_COMB (@lem304813 A) (@lem304812 A lt2 P)). Qed.
Lemma lem304815 {A : Type'} (P : A -> Prop) (x : A) : (term199 A P x) = (term199 A P x).
Proof. exact (eq_refl (term199 A P x)). Qed.
Lemma lem304816 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term381 A x lt2 P) = (term383 A x lt2 P).
Proof. exact (MK_COMB (@lem304815 A P x) (@lem304814 A lt2 P)). Qed.
Lemma lem304817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304818 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term384 A x lt2 P) = (term385 A x lt2 P).
Proof. exact (MK_COMB (@lem304817) (@lem304816 A x lt2 P)). Qed.
Lemma lem304819 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term248 A lt2 P y) = (term239 A lt2 P y).
Proof. exact (eq_refl (term248 A lt2 P y)). Qed.
Lemma lem304820 {A : Type'} (P : A -> Prop) (x : A) : (term199 A P x) = (term199 A P x).
Proof. exact (eq_refl (term199 A P x)). Qed.
Lemma lem304821 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term386 A x lt2 P y) = (term387 A x lt2 P y).
Proof. exact (MK_COMB (@lem304820 A P x) (@lem304819 A lt2 P y)). Qed.
Lemma lem304822 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term388 A x lt2 P) = (term389 A x lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304821 A x lt2 P y)). Qed.
Lemma lem304823 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304824 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term382 A x lt2 P) = (term390 A x lt2 P).
Proof. exact (MK_COMB (@lem304823 A) (@lem304822 A x lt2 P)). Qed.
Lemma lem304825 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : ((term381 A x lt2 P) = (term382 A x lt2 P)) = ((term383 A x lt2 P) = (term390 A x lt2 P)).
Proof. exact (MK_COMB (@lem304818 A x lt2 P) (@lem304824 A x lt2 P)). Qed.
Lemma lem304826 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term383 A x lt2 P) = (term390 A x lt2 P).
Proof. exact (EQ_MP (@lem304825 A x lt2 P) (@lem304810 A x lt2 P)). Qed.
Lemma lem304827 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term391 A lt2 P) = (term392 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304826 A x lt2 P)). Qed.
Lemma lem304828 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304829 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term380 A lt2 P) = (term393 A lt2 P).
Proof. exact (MK_COMB (@lem304828 A) (@lem304827 A lt2 P)). Qed.
Lemma lem304830 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term377 A lt2 P) = (term393 A lt2 P).
Proof. exact (TRANS (@lem304806 A lt2 P) (@lem304829 A lt2 P)). Qed.
Lemma lem304831 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term101 A lt2 P) = (term393 A lt2 P).
Proof. exact (TRANS (@lem304800 A lt2 P) (@lem304830 A lt2 P)). Qed.
Lemma lem304832 {A : Type'} (lt2 : type1402 A) : (term133 A lt2) = (term394 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304831 A lt2 P)). Qed.
Lemma lem304833 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304834 {A : Type'} (lt2 : type1402 A) : (term143 A lt2) = (term395 A lt2).
Proof. exact (MK_COMB (@lem304833 A) (@lem304832 A lt2)). Qed.
Lemma lem304836 {A B : Type'} (P : type1413 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem304837 {A : Type'} (P : type672 A) : (term169 A P) = (term170 A P).
Proof. exact (@lem304836 (A -> Prop) A P). Qed.
Lemma lem304838 {A : Type'} (lt2 : type1402 A) : (term396 A lt2) = (term397 A lt2).
Proof. exact (@lem304837 A (term398 A lt2)). Qed.
Lemma lem304839 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term399 A lt2 P) = (term392 A lt2 P).
Proof. exact (eq_refl (term399 A lt2 P)). Qed.
Lemma lem304840 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem304841 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term400 A lt2 P x) = (term401 A lt2 P x).
Proof. exact (MK_COMB (@lem304839 A lt2 P) (@lem304840 A x)). Qed.
Lemma lem304842 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term401 A lt2 P x) = (term390 A x lt2 P).
Proof. exact (eq_refl (term401 A lt2 P x)). Qed.
Lemma lem304843 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term400 A lt2 P x) = (term390 A x lt2 P).
Proof. exact (TRANS (@lem304841 A lt2 P x) (@lem304842 A x lt2 P)). Qed.
Lemma lem304844 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term402 A lt2 P) = (term392 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304843 A x lt2 P)). Qed.
Lemma lem304845 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304846 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term403 A lt2 P) = (term393 A lt2 P).
Proof. exact (MK_COMB (@lem304845 A) (@lem304844 A lt2 P)). Qed.
Lemma lem304847 {A : Type'} (lt2 : type1402 A) : (term404 A lt2) = (term394 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304846 A lt2 P)). Qed.
Lemma lem304848 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304849 {A : Type'} (lt2 : type1402 A) : (term396 A lt2) = (term395 A lt2).
Proof. exact (MK_COMB (@lem304848 A) (@lem304847 A lt2)). Qed.
Lemma lem304850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304851 {A : Type'} (lt2 : type1402 A) : (term405 A lt2) = (term406 A lt2).
Proof. exact (MK_COMB (@lem304850) (@lem304849 A lt2)). Qed.
Lemma lem304852 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term399 A lt2 P) = (term392 A lt2 P).
Proof. exact (eq_refl (term399 A lt2 P)). Qed.
Lemma lem304853 {A : Type'} (x : type684 A) (P : A -> Prop) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem304854 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term407 A lt2 x P) = (term408 A lt2 x P).
Proof. exact (MK_COMB (@lem304852 A lt2 P) (@lem304853 A x P)). Qed.
Lemma lem304855 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term408 A lt2 x P) = (term409 A x lt2 P).
Proof. exact (eq_refl (term408 A lt2 x P)). Qed.
Lemma lem304856 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term407 A lt2 x P) = (term409 A x lt2 P).
Proof. exact (TRANS (@lem304854 A lt2 x P) (@lem304855 A x lt2 P)). Qed.
Lemma lem304857 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term410 A lt2 x) = (term411 A x lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304856 A x lt2 P)). Qed.
Lemma lem304858 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304859 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term412 A lt2 x) = (term413 A x lt2).
Proof. exact (MK_COMB (@lem304858 A) (@lem304857 A x lt2)). Qed.
Lemma lem304860 {A : Type'} (lt2 : type1402 A) : (term414 A lt2) = (term415 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304859 A x lt2)). Qed.
Lemma lem304861 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304862 {A : Type'} (lt2 : type1402 A) : (term397 A lt2) = (term416 A lt2).
Proof. exact (MK_COMB (@lem304861 A) (@lem304860 A lt2)). Qed.
Lemma lem304863 {A : Type'} (lt2 : type1402 A) : ((term396 A lt2) = (term397 A lt2)) = ((term395 A lt2) = (term416 A lt2)).
Proof. exact (MK_COMB (@lem304851 A lt2) (@lem304862 A lt2)). Qed.
Lemma lem304864 {A : Type'} (lt2 : type1402 A) : (term395 A lt2) = (term416 A lt2).
Proof. exact (EQ_MP (@lem304863 A lt2) (@lem304838 A lt2)). Qed.
Lemma lem304866 {A B : Type'} (P : type1413 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem304867 {A : Type'} (P : type624 A) : (term417 A P) = (term418 A P).
Proof. exact (@lem304866 (A -> Prop) (A -> A) P). Qed.
Lemma lem304868 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term419 A x lt2) = (term420 A x lt2).
Proof. exact (@lem304867 A (term421 A x lt2)). Qed.
Lemma lem304869 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term422 A x lt2 P) = (term423 A x lt2 P).
Proof. exact (eq_refl (term422 A x lt2 P)). Qed.
Lemma lem304870 {A : Type'} (y : A -> A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem304871 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term424 A x lt2 P y) = (term425 A x lt2 P y).
Proof. exact (MK_COMB (@lem304869 A x lt2 P) (@lem304870 A y)). Qed.
Lemma lem304872 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term425 A x lt2 P y) = (term426 A x lt2 P y).
Proof. exact (eq_refl (term425 A x lt2 P y)). Qed.
Lemma lem304873 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term424 A x lt2 P y) = (term426 A x lt2 P y).
Proof. exact (TRANS (@lem304871 A x lt2 P y) (@lem304872 A x lt2 P y)). Qed.
Lemma lem304874 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term427 A x lt2 P) = (term423 A x lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem304873 A x lt2 P y)). Qed.
Lemma lem304875 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem304876 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term428 A x lt2 P) = (term409 A x lt2 P).
Proof. exact (MK_COMB (@lem304875 A) (@lem304874 A x lt2 P)). Qed.
Lemma lem304877 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term429 A x lt2) = (term411 A x lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304876 A x lt2 P)). Qed.
Lemma lem304878 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304879 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term419 A x lt2) = (term413 A x lt2).
Proof. exact (MK_COMB (@lem304878 A) (@lem304877 A x lt2)). Qed.
Lemma lem304880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304881 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term430 A x lt2) = (term431 A x lt2).
Proof. exact (MK_COMB (@lem304880) (@lem304879 A x lt2)). Qed.
Lemma lem304882 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term422 A x lt2 P) = (term423 A x lt2 P).
Proof. exact (eq_refl (term422 A x lt2 P)). Qed.
Lemma lem304883 {A : Type'} (y : type670 A) (P : A -> Prop) : (y P) = (y P).
Proof. exact (eq_refl (y P)). Qed.
Lemma lem304884 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) (P : A -> Prop) : (term432 A x lt2 y P) = (term433 A x lt2 y P).
Proof. exact (MK_COMB (@lem304882 A x lt2 P) (@lem304883 A y P)). Qed.
Lemma lem304885 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) (P : A -> Prop) : (term433 A x lt2 y P) = (term434 A x lt2 y P).
Proof. exact (eq_refl (term433 A x lt2 y P)). Qed.
Lemma lem304886 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) (P : A -> Prop) : (term432 A x lt2 y P) = (term434 A x lt2 y P).
Proof. exact (TRANS (@lem304884 A x lt2 y P) (@lem304885 A x lt2 y P)). Qed.
Lemma lem304887 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) : (term435 A x lt2 y) = (term436 A x lt2 y).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304886 A x lt2 y P)). Qed.
Lemma lem304888 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304889 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) : (term437 A x lt2 y) = (term438 A x lt2 y).
Proof. exact (MK_COMB (@lem304888 A) (@lem304887 A x lt2 y)). Qed.
Lemma lem304890 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term439 A x lt2) = (term440 A x lt2).
Proof. exact (fun_ext (fun y : type670 A => @lem304889 A x lt2 y)). Qed.
Lemma lem304891 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem304892 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term420 A x lt2) = (term441 A x lt2).
Proof. exact (MK_COMB (@lem304891 A) (@lem304890 A x lt2)). Qed.
Lemma lem304893 {A : Type'} (x : type684 A) (lt2 : type1402 A) : ((term419 A x lt2) = (term420 A x lt2)) = ((term413 A x lt2) = (term441 A x lt2)).
Proof. exact (MK_COMB (@lem304881 A x lt2) (@lem304892 A x lt2)). Qed.
Lemma lem304894 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term413 A x lt2) = (term441 A x lt2).
Proof. exact (EQ_MP (@lem304893 A x lt2) (@lem304868 A x lt2)). Qed.
Lemma lem304895 {A : Type'} (lt2 : type1402 A) : (term415 A lt2) = (term442 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304894 A x lt2)). Qed.
Lemma lem304896 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304897 {A : Type'} (lt2 : type1402 A) : (term416 A lt2) = (term443 A lt2).
Proof. exact (MK_COMB (@lem304896 A) (@lem304895 A lt2)). Qed.
Lemma lem304898 {A : Type'} (lt2 : type1402 A) : (term395 A lt2) = (term443 A lt2).
Proof. exact (TRANS (@lem304864 A lt2) (@lem304897 A lt2)). Qed.
Lemma lem304899 {A : Type'} (lt2 : type1402 A) : (term143 A lt2) = (term443 A lt2).
Proof. exact (TRANS (@lem304834 A lt2) (@lem304898 A lt2)). Qed.
Lemma lem304900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304901 {A : Type'} (lt2 : type1402 A) : (term145 A lt2) = (term444 A lt2).
Proof. exact (MK_COMB (@lem304900) (@lem304899 A lt2)). Qed.
Lemma lem304903 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem304904 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem304903 A P Q). Qed.
Lemma lem304905 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term153 A lt2 P) = (term154 A lt2 P).
Proof. exact (@lem304904 A (term32 A P) (term69 A lt2 P)). Qed.
Lemma lem304906 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 P x) = (term61 A lt2 x P).
Proof. exact (eq_refl (term155 A lt2 P x)). Qed.
Lemma lem304907 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term156 A lt2 P) = (term69 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304906 A lt2 x P)). Qed.
Lemma lem304908 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304909 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term157 A lt2 P) = (term70 A lt2 P).
Proof. exact (MK_COMB (@lem304908 A) (@lem304907 A lt2 P)). Qed.
Lemma lem304910 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem304911 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term153 A lt2 P) = (term78 A lt2 P).
Proof. exact (MK_COMB (@lem304910 A P) (@lem304909 A lt2 P)). Qed.
Lemma lem304912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304913 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term158 A lt2 P) = (term159 A lt2 P).
Proof. exact (MK_COMB (@lem304912) (@lem304911 A lt2 P)). Qed.
Lemma lem304914 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 P x) = (term61 A lt2 x P).
Proof. exact (eq_refl (term155 A lt2 P x)). Qed.
Lemma lem304915 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem304916 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term160 A lt2 P x) = (term161 A lt2 x P).
Proof. exact (MK_COMB (@lem304915 A P) (@lem304914 A lt2 x P)). Qed.
Lemma lem304917 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term162 A lt2 P) = (term163 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304916 A lt2 x P)). Qed.
Lemma lem304918 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304919 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term154 A lt2 P) = (term164 A lt2 P).
Proof. exact (MK_COMB (@lem304918 A) (@lem304917 A lt2 P)). Qed.
Lemma lem304920 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term153 A lt2 P) = (term154 A lt2 P)) = ((term78 A lt2 P) = (term164 A lt2 P)).
Proof. exact (MK_COMB (@lem304913 A lt2 P) (@lem304919 A lt2 P)). Qed.
Lemma lem304921 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term78 A lt2 P) = (term164 A lt2 P).
Proof. exact (EQ_MP (@lem304920 A lt2 P) (@lem304905 A lt2 P)). Qed.
Lemma lem304922 {A : Type'} (lt2 : type1402 A) : (term88 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304921 A lt2 P)). Qed.
Lemma lem304923 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304924 {A : Type'} (lt2 : type1402 A) : (term89 A lt2) = (term166 A lt2).
Proof. exact (MK_COMB (@lem304923 A) (@lem304922 A lt2)). Qed.
Lemma lem304926 {A B : Type'} (P : type1413 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem304927 {A : Type'} (P : type672 A) : (term169 A P) = (term170 A P).
Proof. exact (@lem304926 (A -> Prop) A P). Qed.
Lemma lem304928 {A : Type'} (lt2 : type1402 A) : (term171 A lt2) = (term172 A lt2).
Proof. exact (@lem304927 A (term173 A lt2)). Qed.
Lemma lem304929 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term174 A lt2 P) = (term163 A lt2 P).
Proof. exact (eq_refl (term174 A lt2 P)). Qed.
Lemma lem304930 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem304931 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term175 A lt2 P x) = (term176 A lt2 P x).
Proof. exact (MK_COMB (@lem304929 A lt2 P) (@lem304930 A x)). Qed.
Lemma lem304932 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term176 A lt2 P x) = (term161 A lt2 x P).
Proof. exact (eq_refl (term176 A lt2 P x)). Qed.
Lemma lem304933 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term175 A lt2 P x) = (term161 A lt2 x P).
Proof. exact (TRANS (@lem304931 A lt2 P x) (@lem304932 A lt2 x P)). Qed.
Lemma lem304934 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term177 A lt2 P) = (term163 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem304933 A lt2 x P)). Qed.
Lemma lem304935 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem304936 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term178 A lt2 P) = (term164 A lt2 P).
Proof. exact (MK_COMB (@lem304935 A) (@lem304934 A lt2 P)). Qed.
Lemma lem304937 {A : Type'} (lt2 : type1402 A) : (term179 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304936 A lt2 P)). Qed.
Lemma lem304938 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304939 {A : Type'} (lt2 : type1402 A) : (term171 A lt2) = (term166 A lt2).
Proof. exact (MK_COMB (@lem304938 A) (@lem304937 A lt2)). Qed.
Lemma lem304940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304941 {A : Type'} (lt2 : type1402 A) : (term180 A lt2) = (term181 A lt2).
Proof. exact (MK_COMB (@lem304940) (@lem304939 A lt2)). Qed.
Lemma lem304942 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term174 A lt2 P) = (term163 A lt2 P).
Proof. exact (eq_refl (term174 A lt2 P)). Qed.
Lemma lem304943 {A : Type'} (x : type684 A) (P : A -> Prop) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem304944 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term182 A lt2 x P) = (term183 A lt2 x P).
Proof. exact (MK_COMB (@lem304942 A lt2 P) (@lem304943 A x P)). Qed.
Lemma lem304945 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term183 A lt2 x P) = (term184 A lt2 x P).
Proof. exact (eq_refl (term183 A lt2 x P)). Qed.
Lemma lem304946 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term182 A lt2 x P) = (term184 A lt2 x P).
Proof. exact (TRANS (@lem304944 A lt2 x P) (@lem304945 A lt2 x P)). Qed.
Lemma lem304947 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term185 A lt2 x) = (term186 A lt2 x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem304946 A lt2 x P)). Qed.
Lemma lem304948 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem304949 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term187 A lt2 x) = (term188 A lt2 x).
Proof. exact (MK_COMB (@lem304948 A) (@lem304947 A lt2 x)). Qed.
Lemma lem304950 {A : Type'} (lt2 : type1402 A) : (term189 A lt2) = (term190 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304949 A lt2 x)). Qed.
Lemma lem304951 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304952 {A : Type'} (lt2 : type1402 A) : (term172 A lt2) = (term191 A lt2).
Proof. exact (MK_COMB (@lem304951 A) (@lem304950 A lt2)). Qed.
Lemma lem304953 {A : Type'} (lt2 : type1402 A) : ((term171 A lt2) = (term172 A lt2)) = ((term166 A lt2) = (term191 A lt2)).
Proof. exact (MK_COMB (@lem304941 A lt2) (@lem304952 A lt2)). Qed.
Lemma lem304954 {A : Type'} (lt2 : type1402 A) : (term166 A lt2) = (term191 A lt2).
Proof. exact (EQ_MP (@lem304953 A lt2) (@lem304928 A lt2)). Qed.
Lemma lem304955 {A : Type'} (lt2 : type1402 A) : (term89 A lt2) = (term191 A lt2).
Proof. exact (TRANS (@lem304924 A lt2) (@lem304954 A lt2)). Qed.
Lemma lem304956 {A : Type'} (lt2 : type1402 A) : (term148 A lt2) = (term445 A lt2).
Proof. exact (MK_COMB (@lem304901 A lt2) (@lem304955 A lt2)). Qed.
Lemma lem304958 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem304959 {A : Type'} (P : type162 A) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (@lem304958 (type684 A) P Q). Qed.
Lemma lem304960 {A : Type'} (lt2 : type1402 A) : (term446 A lt2) = (term447 A lt2).
Proof. exact (@lem304959 A (term442 A lt2) (term191 A lt2)). Qed.
Lemma lem304961 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term448 A lt2 x) = (term441 A x lt2).
Proof. exact (eq_refl (term448 A lt2 x)). Qed.
Lemma lem304962 {A : Type'} (lt2 : type1402 A) : (term449 A lt2) = (term442 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304961 A x lt2)). Qed.
Lemma lem304963 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304964 {A : Type'} (lt2 : type1402 A) : (term450 A lt2) = (term443 A lt2).
Proof. exact (MK_COMB (@lem304963 A) (@lem304962 A lt2)). Qed.
Lemma lem304965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304966 {A : Type'} (lt2 : type1402 A) : (term451 A lt2) = (term444 A lt2).
Proof. exact (MK_COMB (@lem304965) (@lem304964 A lt2)). Qed.
Lemma lem304967 {A : Type'} (lt2 : type1402 A) : (term191 A lt2) = (term191 A lt2).
Proof. exact (eq_refl (term191 A lt2)). Qed.
Lemma lem304968 {A : Type'} (lt2 : type1402 A) : (term446 A lt2) = (term445 A lt2).
Proof. exact (MK_COMB (@lem304966 A lt2) (@lem304967 A lt2)). Qed.
Lemma lem304969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304970 {A : Type'} (lt2 : type1402 A) : (term452 A lt2) = (term453 A lt2).
Proof. exact (MK_COMB (@lem304969) (@lem304968 A lt2)). Qed.
Lemma lem304971 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term448 A lt2 x) = (term441 A x lt2).
Proof. exact (eq_refl (term448 A lt2 x)). Qed.
Lemma lem304972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304973 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term454 A lt2 x) = (term455 A x lt2).
Proof. exact (MK_COMB (@lem304972) (@lem304971 A x lt2)). Qed.
Lemma lem304974 {A : Type'} (lt2 : type1402 A) : (term191 A lt2) = (term191 A lt2).
Proof. exact (eq_refl (term191 A lt2)). Qed.
Lemma lem304975 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term456 A x lt2) = (term457 A x lt2).
Proof. exact (MK_COMB (@lem304973 A x lt2) (@lem304974 A lt2)). Qed.
Lemma lem304976 {A : Type'} (lt2 : type1402 A) : (term458 A lt2) = (term459 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem304975 A x lt2)). Qed.
Lemma lem304977 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem304978 {A : Type'} (lt2 : type1402 A) : (term447 A lt2) = (term460 A lt2).
Proof. exact (MK_COMB (@lem304977 A) (@lem304976 A lt2)). Qed.
Lemma lem304979 {A : Type'} (lt2 : type1402 A) : ((term446 A lt2) = (term447 A lt2)) = ((term445 A lt2) = (term460 A lt2)).
Proof. exact (MK_COMB (@lem304970 A lt2) (@lem304978 A lt2)). Qed.
Lemma lem304980 {A : Type'} (lt2 : type1402 A) : (term445 A lt2) = (term460 A lt2).
Proof. exact (EQ_MP (@lem304979 A lt2) (@lem304960 A lt2)). Qed.
Lemma lem304982 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem304983 {A : Type'} (P : type150 A) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (@lem304982 (type670 A) P Q). Qed.
Lemma lem304984 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term463 A x lt2) = (term464 A x lt2).
Proof. exact (@lem304983 A (term440 A x lt2) (term191 A lt2)). Qed.
Lemma lem304985 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) : (term465 A x lt2 y) = (term438 A x lt2 y).
Proof. exact (eq_refl (term465 A x lt2 y)). Qed.
Lemma lem304986 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term466 A x lt2) = (term440 A x lt2).
Proof. exact (fun_ext (fun y : type670 A => @lem304985 A x lt2 y)). Qed.
Lemma lem304987 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem304988 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term467 A x lt2) = (term441 A x lt2).
Proof. exact (MK_COMB (@lem304987 A) (@lem304986 A x lt2)). Qed.
Lemma lem304989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304990 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term468 A x lt2) = (term455 A x lt2).
Proof. exact (MK_COMB (@lem304989) (@lem304988 A x lt2)). Qed.
Lemma lem304991 {A : Type'} (lt2 : type1402 A) : (term191 A lt2) = (term191 A lt2).
Proof. exact (eq_refl (term191 A lt2)). Qed.
Lemma lem304992 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term463 A x lt2) = (term457 A x lt2).
Proof. exact (MK_COMB (@lem304990 A x lt2) (@lem304991 A lt2)). Qed.
Lemma lem304993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem304994 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term469 A x lt2) = (term470 A x lt2).
Proof. exact (MK_COMB (@lem304993) (@lem304992 A x lt2)). Qed.
Lemma lem304995 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) : (term465 A x lt2 y) = (term438 A x lt2 y).
Proof. exact (eq_refl (term465 A x lt2 y)). Qed.
Lemma lem304996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem304997 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) : (term471 A x lt2 y) = (term472 A x lt2 y).
Proof. exact (MK_COMB (@lem304996) (@lem304995 A x lt2 y)). Qed.
Lemma lem304998 {A : Type'} (lt2 : type1402 A) : (term191 A lt2) = (term191 A lt2).
Proof. exact (eq_refl (term191 A lt2)). Qed.
Lemma lem304999 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term473 A x y lt2) = (term474 A x y lt2).
Proof. exact (MK_COMB (@lem304997 A x lt2 y) (@lem304998 A lt2)). Qed.
Lemma lem305000 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term475 A x lt2) = (term476 A x lt2).
Proof. exact (fun_ext (fun y : type670 A => @lem304999 A x y lt2)). Qed.
Lemma lem305001 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305002 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term464 A x lt2) = (term477 A x lt2).
Proof. exact (MK_COMB (@lem305001 A) (@lem305000 A x lt2)). Qed.
Lemma lem305003 {A : Type'} (x : type684 A) (lt2 : type1402 A) : ((term463 A x lt2) = (term464 A x lt2)) = ((term457 A x lt2) = (term477 A x lt2)).
Proof. exact (MK_COMB (@lem304994 A x lt2) (@lem305002 A x lt2)). Qed.
Lemma lem305004 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term457 A x lt2) = (term477 A x lt2).
Proof. exact (EQ_MP (@lem305003 A x lt2) (@lem304984 A x lt2)). Qed.
Lemma lem305006 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem305007 {A : Type'} (P : Prop) (Q : type162 A) : (term478 A P Q) = (term479 A P Q).
Proof. exact (@lem305006 (type684 A) P Q). Qed.
Lemma lem305008 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term480 A x y lt2) = (term481 A x y lt2).
Proof. exact (@lem305007 A (term438 A x lt2 y) (term190 A lt2)). Qed.
Lemma lem305009 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term301 A lt2 x) = (term188 A lt2 x).
Proof. exact (eq_refl (term301 A lt2 x)). Qed.
Lemma lem305010 {A : Type'} (lt2 : type1402 A) : (term302 A lt2) = (term190 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem305009 A lt2 x)). Qed.
Lemma lem305011 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305012 {A : Type'} (lt2 : type1402 A) : (term303 A lt2) = (term191 A lt2).
Proof. exact (MK_COMB (@lem305011 A) (@lem305010 A lt2)). Qed.
Lemma lem305013 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) : (term472 A x lt2 y) = (term472 A x lt2 y).
Proof. exact (eq_refl (term472 A x lt2 y)). Qed.
Lemma lem305014 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term480 A x y lt2) = (term474 A x y lt2).
Proof. exact (MK_COMB (@lem305013 A x lt2 y) (@lem305012 A lt2)). Qed.
Lemma lem305015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305016 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term482 A x y lt2) = (term483 A x y lt2).
Proof. exact (MK_COMB (@lem305015) (@lem305014 A x y lt2)). Qed.
Lemma lem305017 {A : Type'} (lt2 : type1402 A) (x' : type684 A) : (term301 A lt2 x') = (term188 A lt2 x').
Proof. exact (eq_refl (term301 A lt2 x')). Qed.
Lemma lem305018 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : type670 A) : (term472 A x lt2 y) = (term472 A x lt2 y).
Proof. exact (eq_refl (term472 A x lt2 y)). Qed.
Lemma lem305019 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) (x' : type684 A) : (term484 A x y lt2 x') = (term485 A x y lt2 x').
Proof. exact (MK_COMB (@lem305018 A x lt2 y) (@lem305017 A lt2 x')). Qed.
Lemma lem305020 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term486 A x y lt2) = (term487 A x y lt2).
Proof. exact (fun_ext (fun x' : type684 A => @lem305019 A x y lt2 x')). Qed.
Lemma lem305021 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305022 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term481 A x y lt2) = (term488 A x y lt2).
Proof. exact (MK_COMB (@lem305021 A) (@lem305020 A x y lt2)). Qed.
Lemma lem305023 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : ((term480 A x y lt2) = (term481 A x y lt2)) = ((term474 A x y lt2) = (term488 A x y lt2)).
Proof. exact (MK_COMB (@lem305016 A x y lt2) (@lem305022 A x y lt2)). Qed.
Lemma lem305024 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term474 A x y lt2) = (term488 A x y lt2).
Proof. exact (EQ_MP (@lem305023 A x y lt2) (@lem305008 A x y lt2)). Qed.
Lemma lem305025 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term476 A x lt2) = (term489 A x lt2).
Proof. exact (fun_ext (fun y : type670 A => @lem305024 A x y lt2)). Qed.
Lemma lem305026 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305027 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term477 A x lt2) = (term490 A x lt2).
Proof. exact (MK_COMB (@lem305026 A) (@lem305025 A x lt2)). Qed.
Lemma lem305028 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term457 A x lt2) = (term490 A x lt2).
Proof. exact (TRANS (@lem305004 A x lt2) (@lem305027 A x lt2)). Qed.
Lemma lem305029 {A : Type'} (lt2 : type1402 A) : (term459 A lt2) = (term491 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem305028 A x lt2)). Qed.
Lemma lem305030 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305031 {A : Type'} (lt2 : type1402 A) : (term460 A lt2) = (term492 A lt2).
Proof. exact (MK_COMB (@lem305030 A) (@lem305029 A lt2)). Qed.
Lemma lem305032 {A : Type'} (lt2 : type1402 A) : (term445 A lt2) = (term492 A lt2).
Proof. exact (TRANS (@lem304980 A lt2) (@lem305031 A lt2)). Qed.
Lemma lem305033 {A : Type'} (lt2 : type1402 A) : (term148 A lt2) = (term492 A lt2).
Proof. exact (TRANS (@lem304956 A lt2) (@lem305032 A lt2)). Qed.
Lemma lem305034 {A : Type'} (lt2 : type1402 A) : (term149 A lt2) = (term493 A lt2).
Proof. exact (MK_COMB (@lem304744 A lt2) (@lem305033 A lt2)). Qed.
Lemma lem305036 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem305037 {A : Type'} (P : type686 A) (Q : Prop) : (term494 A P Q) = (term495 A P Q).
Proof. exact (@lem305036 (A -> Prop) P Q). Qed.
Lemma lem305038 {A : Type'} (lt2 : type1402 A) : (term496 A lt2) = (term497 A lt2).
Proof. exact (@lem305037 A (term374 A lt2) (term492 A lt2)). Qed.
Lemma lem305039 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term498 A lt2 P) = (term373 A lt2 P).
Proof. exact (eq_refl (term498 A lt2 P)). Qed.
Lemma lem305040 {A : Type'} (lt2 : type1402 A) : (term499 A lt2) = (term374 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305039 A lt2 P)). Qed.
Lemma lem305041 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem305042 {A : Type'} (lt2 : type1402 A) : (term500 A lt2) = (term375 A lt2).
Proof. exact (MK_COMB (@lem305041 A) (@lem305040 A lt2)). Qed.
Lemma lem305043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305044 {A : Type'} (lt2 : type1402 A) : (term501 A lt2) = (term376 A lt2).
Proof. exact (MK_COMB (@lem305043) (@lem305042 A lt2)). Qed.
Lemma lem305045 {A : Type'} (lt2 : type1402 A) : (term492 A lt2) = (term492 A lt2).
Proof. exact (eq_refl (term492 A lt2)). Qed.
Lemma lem305046 {A : Type'} (lt2 : type1402 A) : (term496 A lt2) = (term493 A lt2).
Proof. exact (MK_COMB (@lem305044 A lt2) (@lem305045 A lt2)). Qed.
Lemma lem305047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305048 {A : Type'} (lt2 : type1402 A) : (term502 A lt2) = (term503 A lt2).
Proof. exact (MK_COMB (@lem305047) (@lem305046 A lt2)). Qed.
Lemma lem305049 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term498 A lt2 P) = (term373 A lt2 P).
Proof. exact (eq_refl (term498 A lt2 P)). Qed.
Lemma lem305050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305051 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term504 A lt2 P) = (term505 A lt2 P).
Proof. exact (MK_COMB (@lem305050) (@lem305049 A lt2 P)). Qed.
Lemma lem305052 {A : Type'} (lt2 : type1402 A) : (term492 A lt2) = (term492 A lt2).
Proof. exact (eq_refl (term492 A lt2)). Qed.
Lemma lem305053 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term506 A P lt2) = (term507 A P lt2).
Proof. exact (MK_COMB (@lem305051 A lt2 P) (@lem305052 A lt2)). Qed.
Lemma lem305054 {A : Type'} (lt2 : type1402 A) : (term508 A lt2) = (term509 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305053 A P lt2)). Qed.
Lemma lem305055 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem305056 {A : Type'} (lt2 : type1402 A) : (term497 A lt2) = (term510 A lt2).
Proof. exact (MK_COMB (@lem305055 A) (@lem305054 A lt2)). Qed.
Lemma lem305057 {A : Type'} (lt2 : type1402 A) : ((term496 A lt2) = (term497 A lt2)) = ((term493 A lt2) = (term510 A lt2)).
Proof. exact (MK_COMB (@lem305048 A lt2) (@lem305056 A lt2)). Qed.
Lemma lem305058 {A : Type'} (lt2 : type1402 A) : (term493 A lt2) = (term510 A lt2).
Proof. exact (EQ_MP (@lem305057 A lt2) (@lem305038 A lt2)). Qed.
Lemma lem305060 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem305061 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem305060 A P Q). Qed.
Lemma lem305062 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term511 A P lt2) = (term512 A P lt2).
Proof. exact (@lem305061 A (term372 A lt2 P) (term492 A lt2)). Qed.
Lemma lem305063 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term513 A lt2 P x) = (term370 A x lt2 P).
Proof. exact (eq_refl (term513 A lt2 P x)). Qed.
Lemma lem305064 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term514 A lt2 P) = (term372 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem305063 A x lt2 P)). Qed.
Lemma lem305065 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem305066 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term515 A lt2 P) = (term373 A lt2 P).
Proof. exact (MK_COMB (@lem305065 A) (@lem305064 A lt2 P)). Qed.
Lemma lem305067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305068 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term516 A lt2 P) = (term505 A lt2 P).
Proof. exact (MK_COMB (@lem305067) (@lem305066 A lt2 P)). Qed.
Lemma lem305069 {A : Type'} (lt2 : type1402 A) : (term492 A lt2) = (term492 A lt2).
Proof. exact (eq_refl (term492 A lt2)). Qed.
Lemma lem305070 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term511 A P lt2) = (term507 A P lt2).
Proof. exact (MK_COMB (@lem305068 A lt2 P) (@lem305069 A lt2)). Qed.
Lemma lem305071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305072 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term517 A P lt2) = (term518 A P lt2).
Proof. exact (MK_COMB (@lem305071) (@lem305070 A P lt2)). Qed.
Lemma lem305073 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term513 A lt2 P x) = (term370 A x lt2 P).
Proof. exact (eq_refl (term513 A lt2 P x)). Qed.
Lemma lem305074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305075 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term519 A lt2 P x) = (term520 A x lt2 P).
Proof. exact (MK_COMB (@lem305074) (@lem305073 A x lt2 P)). Qed.
Lemma lem305076 {A : Type'} (lt2 : type1402 A) : (term492 A lt2) = (term492 A lt2).
Proof. exact (eq_refl (term492 A lt2)). Qed.
Lemma lem305077 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term521 A P x lt2) = (term522 A x P lt2).
Proof. exact (MK_COMB (@lem305075 A x lt2 P) (@lem305076 A lt2)). Qed.
Lemma lem305078 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term523 A P lt2) = (term524 A P lt2).
Proof. exact (fun_ext (fun x : A => @lem305077 A x P lt2)). Qed.
Lemma lem305079 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem305080 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term512 A P lt2) = (term525 A P lt2).
Proof. exact (MK_COMB (@lem305079 A) (@lem305078 A P lt2)). Qed.
Lemma lem305081 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : ((term511 A P lt2) = (term512 A P lt2)) = ((term507 A P lt2) = (term525 A P lt2)).
Proof. exact (MK_COMB (@lem305072 A P lt2) (@lem305080 A P lt2)). Qed.
Lemma lem305082 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term507 A P lt2) = (term525 A P lt2).
Proof. exact (EQ_MP (@lem305081 A P lt2) (@lem305062 A P lt2)). Qed.
Lemma lem305084 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem305085 {A : Type'} (P : type488 A) (Q : Prop) : (term526 A P Q) = (term527 A P Q).
Proof. exact (@lem305084 (A -> A) P Q). Qed.
Lemma lem305086 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term528 A x P lt2) = (term529 A x P lt2).
Proof. exact (@lem305085 A (term369 A x lt2 P) (term492 A lt2)). Qed.
Lemma lem305087 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term530 A x lt2 P y) = (term367 A x lt2 P y).
Proof. exact (eq_refl (term530 A x lt2 P y)). Qed.
Lemma lem305088 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term531 A x lt2 P) = (term369 A x lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem305087 A x lt2 P y)). Qed.
Lemma lem305089 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem305090 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term532 A x lt2 P) = (term370 A x lt2 P).
Proof. exact (MK_COMB (@lem305089 A) (@lem305088 A x lt2 P)). Qed.
Lemma lem305091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305092 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) : (term533 A x lt2 P) = (term520 A x lt2 P).
Proof. exact (MK_COMB (@lem305091) (@lem305090 A x lt2 P)). Qed.
Lemma lem305093 {A : Type'} (lt2 : type1402 A) : (term492 A lt2) = (term492 A lt2).
Proof. exact (eq_refl (term492 A lt2)). Qed.
Lemma lem305094 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term528 A x P lt2) = (term522 A x P lt2).
Proof. exact (MK_COMB (@lem305092 A x lt2 P) (@lem305093 A lt2)). Qed.
Lemma lem305095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305096 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term534 A x P lt2) = (term535 A x P lt2).
Proof. exact (MK_COMB (@lem305095) (@lem305094 A x P lt2)). Qed.
Lemma lem305097 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term530 A x lt2 P y) = (term367 A x lt2 P y).
Proof. exact (eq_refl (term530 A x lt2 P y)). Qed.
Lemma lem305098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305099 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term536 A x lt2 P y) = (term537 A x lt2 P y).
Proof. exact (MK_COMB (@lem305098) (@lem305097 A x lt2 P y)). Qed.
Lemma lem305100 {A : Type'} (lt2 : type1402 A) : (term492 A lt2) = (term492 A lt2).
Proof. exact (eq_refl (term492 A lt2)). Qed.
Lemma lem305101 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term538 A x P y lt2) = (term539 A x P y lt2).
Proof. exact (MK_COMB (@lem305099 A x lt2 P y) (@lem305100 A lt2)). Qed.
Lemma lem305102 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term540 A x P lt2) = (term541 A x P lt2).
Proof. exact (fun_ext (fun y : A -> A => @lem305101 A x P y lt2)). Qed.
Lemma lem305103 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem305104 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term529 A x P lt2) = (term542 A x P lt2).
Proof. exact (MK_COMB (@lem305103 A) (@lem305102 A x P lt2)). Qed.
Lemma lem305105 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : ((term528 A x P lt2) = (term529 A x P lt2)) = ((term522 A x P lt2) = (term542 A x P lt2)).
Proof. exact (MK_COMB (@lem305096 A x P lt2) (@lem305104 A x P lt2)). Qed.
Lemma lem305106 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term522 A x P lt2) = (term542 A x P lt2).
Proof. exact (EQ_MP (@lem305105 A x P lt2) (@lem305086 A x P lt2)). Qed.
Lemma lem305108 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem305109 {A : Type'} (P : Prop) (Q : type162 A) : (term478 A P Q) = (term479 A P Q).
Proof. exact (@lem305108 (type684 A) P Q). Qed.
Lemma lem305110 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term543 A x P y lt2) = (term544 A x P y lt2).
Proof. exact (@lem305109 A (term367 A x lt2 P y) (term491 A lt2)). Qed.
Lemma lem305111 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term545 A lt2 x) = (term490 A x lt2).
Proof. exact (eq_refl (term545 A lt2 x)). Qed.
Lemma lem305112 {A : Type'} (lt2 : type1402 A) : (term546 A lt2) = (term491 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem305111 A x lt2)). Qed.
Lemma lem305113 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305114 {A : Type'} (lt2 : type1402 A) : (term547 A lt2) = (term492 A lt2).
Proof. exact (MK_COMB (@lem305113 A) (@lem305112 A lt2)). Qed.
Lemma lem305115 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term537 A x lt2 P y) = (term537 A x lt2 P y).
Proof. exact (eq_refl (term537 A x lt2 P y)). Qed.
Lemma lem305116 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term543 A x P y lt2) = (term539 A x P y lt2).
Proof. exact (MK_COMB (@lem305115 A x lt2 P y) (@lem305114 A lt2)). Qed.
Lemma lem305117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305118 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term548 A x P y lt2) = (term549 A x P y lt2).
Proof. exact (MK_COMB (@lem305117) (@lem305116 A x P y lt2)). Qed.
Lemma lem305119 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term545 A lt2 x) = (term490 A x lt2).
Proof. exact (eq_refl (term545 A lt2 x)). Qed.
Lemma lem305120 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term537 A x lt2 P y) = (term537 A x lt2 P y).
Proof. exact (eq_refl (term537 A x lt2 P y)). Qed.
Lemma lem305121 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term550 A x P y lt2 x') = (term551 A x P y x' lt2).
Proof. exact (MK_COMB (@lem305120 A x lt2 P y) (@lem305119 A x' lt2)). Qed.
Lemma lem305122 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term552 A x P y lt2) = (term553 A x P y lt2).
Proof. exact (fun_ext (fun x' : type684 A => @lem305121 A x P y x' lt2)). Qed.
Lemma lem305123 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305124 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term544 A x P y lt2) = (term554 A x P y lt2).
Proof. exact (MK_COMB (@lem305123 A) (@lem305122 A x P y lt2)). Qed.
Lemma lem305125 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : ((term543 A x P y lt2) = (term544 A x P y lt2)) = ((term539 A x P y lt2) = (term554 A x P y lt2)).
Proof. exact (MK_COMB (@lem305118 A x P y lt2) (@lem305124 A x P y lt2)). Qed.
Lemma lem305126 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term539 A x P y lt2) = (term554 A x P y lt2).
Proof. exact (EQ_MP (@lem305125 A x P y lt2) (@lem305110 A x P y lt2)). Qed.
Lemma lem305128 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem305129 {A : Type'} (P : Prop) (Q : type150 A) : (term555 A P Q) = (term556 A P Q).
Proof. exact (@lem305128 (type670 A) P Q). Qed.
Lemma lem305130 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term557 A x P y x' lt2) = (term558 A x P y x' lt2).
Proof. exact (@lem305129 A (term367 A x lt2 P y) (term489 A x' lt2)). Qed.
Lemma lem305131 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term559 A x lt2 y) = (term488 A x y lt2).
Proof. exact (eq_refl (term559 A x lt2 y)). Qed.
Lemma lem305132 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term560 A x lt2) = (term489 A x lt2).
Proof. exact (fun_ext (fun y : type670 A => @lem305131 A x y lt2)). Qed.
Lemma lem305133 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305134 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term561 A x lt2) = (term490 A x lt2).
Proof. exact (MK_COMB (@lem305133 A) (@lem305132 A x lt2)). Qed.
Lemma lem305135 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term537 A x lt2 P y) = (term537 A x lt2 P y).
Proof. exact (eq_refl (term537 A x lt2 P y)). Qed.
Lemma lem305136 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term557 A x P y x' lt2) = (term551 A x P y x' lt2).
Proof. exact (MK_COMB (@lem305135 A x lt2 P y) (@lem305134 A x' lt2)). Qed.
Lemma lem305137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305138 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term562 A x P y x' lt2) = (term563 A x P y x' lt2).
Proof. exact (MK_COMB (@lem305137) (@lem305136 A x P y x' lt2)). Qed.
Lemma lem305139 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term559 A x lt2 y) = (term488 A x y lt2).
Proof. exact (eq_refl (term559 A x lt2 y)). Qed.
Lemma lem305140 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term537 A x lt2 P y) = (term537 A x lt2 P y).
Proof. exact (eq_refl (term537 A x lt2 P y)). Qed.
Lemma lem305141 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term564 A x P y x' lt2 y') = (term565 A x P y x' y' lt2).
Proof. exact (MK_COMB (@lem305140 A x lt2 P y) (@lem305139 A x' y' lt2)). Qed.
Lemma lem305142 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term566 A x P y x' lt2) = (term567 A x P y x' lt2).
Proof. exact (fun_ext (fun y' : type670 A => @lem305141 A x P y x' y' lt2)). Qed.
Lemma lem305143 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305144 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term558 A x P y x' lt2) = (term568 A x P y x' lt2).
Proof. exact (MK_COMB (@lem305143 A) (@lem305142 A x P y x' lt2)). Qed.
Lemma lem305145 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : ((term557 A x P y x' lt2) = (term558 A x P y x' lt2)) = ((term551 A x P y x' lt2) = (term568 A x P y x' lt2)).
Proof. exact (MK_COMB (@lem305138 A x P y x' lt2) (@lem305144 A x P y x' lt2)). Qed.
Lemma lem305146 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term551 A x P y x' lt2) = (term568 A x P y x' lt2).
Proof. exact (EQ_MP (@lem305145 A x P y x' lt2) (@lem305130 A x P y x' lt2)). Qed.
Lemma lem305148 {A : Type'} (P : Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem305149 {A : Type'} (P : Prop) (Q : type162 A) : (term478 A P Q) = (term479 A P Q).
Proof. exact (@lem305148 (type684 A) P Q). Qed.
Lemma lem305150 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term569 A x P y x' y' lt2) = (term570 A x P y x' y' lt2).
Proof. exact (@lem305149 A (term367 A x lt2 P y) (term487 A x' y' lt2)). Qed.
Lemma lem305151 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) (x' : type684 A) : (term571 A x y lt2 x') = (term485 A x y lt2 x').
Proof. exact (eq_refl (term571 A x y lt2 x')). Qed.
Lemma lem305152 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term572 A x y lt2) = (term487 A x y lt2).
Proof. exact (fun_ext (fun x' : type684 A => @lem305151 A x y lt2 x')). Qed.
Lemma lem305153 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305154 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) : (term573 A x y lt2) = (term488 A x y lt2).
Proof. exact (MK_COMB (@lem305153 A) (@lem305152 A x y lt2)). Qed.
Lemma lem305155 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term537 A x lt2 P y) = (term537 A x lt2 P y).
Proof. exact (eq_refl (term537 A x lt2 P y)). Qed.
Lemma lem305156 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term569 A x P y x' y' lt2) = (term565 A x P y x' y' lt2).
Proof. exact (MK_COMB (@lem305155 A x lt2 P y) (@lem305154 A x' y' lt2)). Qed.
Lemma lem305157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305158 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term574 A x P y x' y' lt2) = (term575 A x P y x' y' lt2).
Proof. exact (MK_COMB (@lem305157) (@lem305156 A x P y x' y' lt2)). Qed.
Lemma lem305159 {A : Type'} (x : type684 A) (y : type670 A) (lt2 : type1402 A) (x' : type684 A) : (term571 A x y lt2 x') = (term485 A x y lt2 x').
Proof. exact (eq_refl (term571 A x y lt2 x')). Qed.
Lemma lem305160 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term537 A x lt2 P y) = (term537 A x lt2 P y).
Proof. exact (eq_refl (term537 A x lt2 P y)). Qed.
Lemma lem305161 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x'' : type684 A) : (term576 A x P y x' y' lt2 x'') = (term577 A x P y x' y' lt2 x'').
Proof. exact (MK_COMB (@lem305160 A x lt2 P y) (@lem305159 A x' y' lt2 x'')). Qed.
Lemma lem305162 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term578 A x P y x' y' lt2) = (term579 A x P y x' y' lt2).
Proof. exact (fun_ext (fun x'' : type684 A => @lem305161 A x P y x' y' lt2 x'')). Qed.
Lemma lem305163 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305164 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term570 A x P y x' y' lt2) = (term580 A x P y x' y' lt2).
Proof. exact (MK_COMB (@lem305163 A) (@lem305162 A x P y x' y' lt2)). Qed.
Lemma lem305165 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : ((term569 A x P y x' y' lt2) = (term570 A x P y x' y' lt2)) = ((term565 A x P y x' y' lt2) = (term580 A x P y x' y' lt2)).
Proof. exact (MK_COMB (@lem305158 A x P y x' y' lt2) (@lem305164 A x P y x' y' lt2)). Qed.
Lemma lem305166 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term565 A x P y x' y' lt2) = (term580 A x P y x' y' lt2).
Proof. exact (EQ_MP (@lem305165 A x P y x' y' lt2) (@lem305150 A x P y x' y' lt2)). Qed.
Lemma lem305167 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term567 A x P y x' lt2) = (term581 A x P y x' lt2).
Proof. exact (fun_ext (fun y' : type670 A => @lem305166 A x P y x' y' lt2)). Qed.
Lemma lem305168 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305169 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term568 A x P y x' lt2) = (term582 A x P y x' lt2).
Proof. exact (MK_COMB (@lem305168 A) (@lem305167 A x P y x' lt2)). Qed.
Lemma lem305170 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term551 A x P y x' lt2) = (term582 A x P y x' lt2).
Proof. exact (TRANS (@lem305146 A x P y x' lt2) (@lem305169 A x P y x' lt2)). Qed.
Lemma lem305171 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term553 A x P y lt2) = (term583 A x P y lt2).
Proof. exact (fun_ext (fun x' : type684 A => @lem305170 A x P y x' lt2)). Qed.
Lemma lem305172 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305173 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term554 A x P y lt2) = (term584 A x P y lt2).
Proof. exact (MK_COMB (@lem305172 A) (@lem305171 A x P y lt2)). Qed.
Lemma lem305174 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term539 A x P y lt2) = (term584 A x P y lt2).
Proof. exact (TRANS (@lem305126 A x P y lt2) (@lem305173 A x P y lt2)). Qed.
Lemma lem305175 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term541 A x P lt2) = (term585 A x P lt2).
Proof. exact (fun_ext (fun y : A -> A => @lem305174 A x P y lt2)). Qed.
Lemma lem305176 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem305177 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term542 A x P lt2) = (term586 A x P lt2).
Proof. exact (MK_COMB (@lem305176 A) (@lem305175 A x P lt2)). Qed.
Lemma lem305178 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term522 A x P lt2) = (term586 A x P lt2).
Proof. exact (TRANS (@lem305106 A x P lt2) (@lem305177 A x P lt2)). Qed.
Lemma lem305179 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term524 A P lt2) = (term587 A P lt2).
Proof. exact (fun_ext (fun x : A => @lem305178 A x P lt2)). Qed.
Lemma lem305180 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem305181 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term525 A P lt2) = (term588 A P lt2).
Proof. exact (MK_COMB (@lem305180 A) (@lem305179 A P lt2)). Qed.
Lemma lem305182 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term507 A P lt2) = (term588 A P lt2).
Proof. exact (TRANS (@lem305082 A P lt2) (@lem305181 A P lt2)). Qed.
Lemma lem305183 {A : Type'} (lt2 : type1402 A) : (term509 A lt2) = (term589 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305182 A P lt2)). Qed.
Lemma lem305184 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem305185 {A : Type'} (lt2 : type1402 A) : (term510 A lt2) = (term590 A lt2).
Proof. exact (MK_COMB (@lem305184 A) (@lem305183 A lt2)). Qed.
Lemma lem305186 {A : Type'} (lt2 : type1402 A) : (term493 A lt2) = (term590 A lt2).
Proof. exact (TRANS (@lem305058 A lt2) (@lem305185 A lt2)). Qed.
Lemma lem305187 {A : Type'} (lt2 : type1402 A) : (term149 A lt2) = (term590 A lt2).
Proof. exact (TRANS (@lem305034 A lt2) (@lem305186 A lt2)). Qed.
Lemma lem305188 {A : Type'} (lt2 : type1402 A) : (term150 A lt2) = (term591 A lt2).
Proof. exact (MK_COMB (@lem304654 A lt2) (@lem305187 A lt2)). Qed.
Lemma lem305192 {A : Type'} (P : A -> Prop) (Q : Prop) : (term378 A P Q) = (term379 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem305193 {A : Type'} (P : type162 A) (Q : Prop) : (term592 A P Q) = (term593 A P Q).
Proof. exact (@lem305192 (type684 A) P Q). Qed.
Lemma lem305194 {A : Type'} (lt2 : type1402 A) : (term594 A lt2) = (term595 A lt2).
Proof. exact (@lem305193 A (term356 A lt2) (term590 A lt2)). Qed.
Lemma lem305195 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term596 A lt2 x) = (term355 A x lt2).
Proof. exact (eq_refl (term596 A lt2 x)). Qed.
Lemma lem305196 {A : Type'} (lt2 : type1402 A) : (term597 A lt2) = (term356 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem305195 A x lt2)). Qed.
Lemma lem305197 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305198 {A : Type'} (lt2 : type1402 A) : (term598 A lt2) = (term357 A lt2).
Proof. exact (MK_COMB (@lem305197 A) (@lem305196 A lt2)). Qed.
Lemma lem305199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305200 {A : Type'} (lt2 : type1402 A) : (term599 A lt2) = (term358 A lt2).
Proof. exact (MK_COMB (@lem305199) (@lem305198 A lt2)). Qed.
Lemma lem305201 {A : Type'} (lt2 : type1402 A) : (term590 A lt2) = (term590 A lt2).
Proof. exact (eq_refl (term590 A lt2)). Qed.
Lemma lem305202 {A : Type'} (lt2 : type1402 A) : (term594 A lt2) = (term591 A lt2).
Proof. exact (MK_COMB (@lem305200 A lt2) (@lem305201 A lt2)). Qed.
Lemma lem305203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305204 {A : Type'} (lt2 : type1402 A) : (term600 A lt2) = (term601 A lt2).
Proof. exact (MK_COMB (@lem305203) (@lem305202 A lt2)). Qed.
Lemma lem305205 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term596 A lt2 x) = (term355 A x lt2).
Proof. exact (eq_refl (term596 A lt2 x)). Qed.
Lemma lem305206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305207 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term602 A lt2 x) = (term603 A x lt2).
Proof. exact (MK_COMB (@lem305206) (@lem305205 A x lt2)). Qed.
Lemma lem305208 {A : Type'} (lt2 : type1402 A) : (term590 A lt2) = (term590 A lt2).
Proof. exact (eq_refl (term590 A lt2)). Qed.
Lemma lem305209 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term604 A x lt2) = (term605 A x lt2).
Proof. exact (MK_COMB (@lem305207 A x lt2) (@lem305208 A lt2)). Qed.
Lemma lem305210 {A : Type'} (lt2 : type1402 A) : (term606 A lt2) = (term607 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem305209 A x lt2)). Qed.
Lemma lem305211 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305212 {A : Type'} (lt2 : type1402 A) : (term595 A lt2) = (term608 A lt2).
Proof. exact (MK_COMB (@lem305211 A) (@lem305210 A lt2)). Qed.
Lemma lem305213 {A : Type'} (lt2 : type1402 A) : ((term594 A lt2) = (term595 A lt2)) = ((term591 A lt2) = (term608 A lt2)).
Proof. exact (MK_COMB (@lem305204 A lt2) (@lem305212 A lt2)). Qed.
Lemma lem305214 {A : Type'} (lt2 : type1402 A) : (term591 A lt2) = (term608 A lt2).
Proof. exact (EQ_MP (@lem305213 A lt2) (@lem305194 A lt2)). Qed.
Lemma lem305216 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem305217 {A : Type'} (P : type686 A) (Q : type686 A) : (term609 A P Q) = (term610 A P Q).
Proof. exact (@lem305216 (A -> Prop) P Q). Qed.
Lemma lem305218 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term611 A x lt2) = (term612 A x lt2).
Proof. exact (@lem305217 A (term354 A x lt2) (term589 A lt2)). Qed.
Lemma lem305219 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term613 A x lt2 P) = (term353 A x lt2 P).
Proof. exact (eq_refl (term613 A x lt2 P)). Qed.
Lemma lem305220 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term614 A x lt2) = (term354 A x lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305219 A x lt2 P)). Qed.
Lemma lem305221 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem305222 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term615 A x lt2) = (term355 A x lt2).
Proof. exact (MK_COMB (@lem305221 A) (@lem305220 A x lt2)). Qed.
Lemma lem305223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305224 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term616 A x lt2) = (term603 A x lt2).
Proof. exact (MK_COMB (@lem305223) (@lem305222 A x lt2)). Qed.
Lemma lem305225 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term617 A lt2 P) = (term588 A P lt2).
Proof. exact (eq_refl (term617 A lt2 P)). Qed.
Lemma lem305226 {A : Type'} (lt2 : type1402 A) : (term618 A lt2) = (term589 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305225 A P lt2)). Qed.
Lemma lem305227 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem305228 {A : Type'} (lt2 : type1402 A) : (term619 A lt2) = (term590 A lt2).
Proof. exact (MK_COMB (@lem305227 A) (@lem305226 A lt2)). Qed.
Lemma lem305229 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term611 A x lt2) = (term605 A x lt2).
Proof. exact (MK_COMB (@lem305224 A x lt2) (@lem305228 A lt2)). Qed.
Lemma lem305230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305231 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term620 A x lt2) = (term621 A x lt2).
Proof. exact (MK_COMB (@lem305230) (@lem305229 A x lt2)). Qed.
Lemma lem305232 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term613 A x lt2 P) = (term353 A x lt2 P).
Proof. exact (eq_refl (term613 A x lt2 P)). Qed.
Lemma lem305233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305234 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term622 A x lt2 P) = (term623 A x lt2 P).
Proof. exact (MK_COMB (@lem305233) (@lem305232 A x lt2 P)). Qed.
Lemma lem305235 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term617 A lt2 P) = (term588 A P lt2).
Proof. exact (eq_refl (term617 A lt2 P)). Qed.
Lemma lem305236 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term624 A x lt2 P) = (term625 A x P lt2).
Proof. exact (MK_COMB (@lem305234 A x lt2 P) (@lem305235 A P lt2)). Qed.
Lemma lem305237 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term626 A x lt2) = (term627 A x lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305236 A x P lt2)). Qed.
Lemma lem305238 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem305239 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term612 A x lt2) = (term628 A x lt2).
Proof. exact (MK_COMB (@lem305238 A) (@lem305237 A x lt2)). Qed.
Lemma lem305240 {A : Type'} (x : type684 A) (lt2 : type1402 A) : ((term611 A x lt2) = (term612 A x lt2)) = ((term605 A x lt2) = (term628 A x lt2)).
Proof. exact (MK_COMB (@lem305231 A x lt2) (@lem305239 A x lt2)). Qed.
Lemma lem305241 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term605 A x lt2) = (term628 A x lt2).
Proof. exact (EQ_MP (@lem305240 A x lt2) (@lem305218 A x lt2)). Qed.
Lemma lem305243 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem305244 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (@lem305243 A P Q). Qed.
Lemma lem305245 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term629 A x P lt2) = (term630 A x P lt2).
Proof. exact (@lem305244 A (term352 A x lt2 P) (term587 A P lt2)). Qed.
Lemma lem305246 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term631 A x lt2 P x') = (term351 A x x' lt2 P).
Proof. exact (eq_refl (term631 A x lt2 P x')). Qed.
Lemma lem305247 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term632 A x lt2 P) = (term352 A x lt2 P).
Proof. exact (fun_ext (fun x' : A => @lem305246 A x x' lt2 P)). Qed.
Lemma lem305248 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem305249 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term633 A x lt2 P) = (term353 A x lt2 P).
Proof. exact (MK_COMB (@lem305248 A) (@lem305247 A x lt2 P)). Qed.
Lemma lem305250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305251 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) : (term634 A x lt2 P) = (term623 A x lt2 P).
Proof. exact (MK_COMB (@lem305250) (@lem305249 A x lt2 P)). Qed.
Lemma lem305252 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term635 A P lt2 x) = (term586 A x P lt2).
Proof. exact (eq_refl (term635 A P lt2 x)). Qed.
Lemma lem305253 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term636 A P lt2) = (term587 A P lt2).
Proof. exact (fun_ext (fun x : A => @lem305252 A x P lt2)). Qed.
Lemma lem305254 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem305255 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term637 A P lt2) = (term588 A P lt2).
Proof. exact (MK_COMB (@lem305254 A) (@lem305253 A P lt2)). Qed.
Lemma lem305256 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term629 A x P lt2) = (term625 A x P lt2).
Proof. exact (MK_COMB (@lem305251 A x lt2 P) (@lem305255 A P lt2)). Qed.
Lemma lem305257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305258 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term638 A x P lt2) = (term639 A x P lt2).
Proof. exact (MK_COMB (@lem305257) (@lem305256 A x P lt2)). Qed.
Lemma lem305259 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term631 A x lt2 P x') = (term351 A x x' lt2 P).
Proof. exact (eq_refl (term631 A x lt2 P x')). Qed.
Lemma lem305260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305261 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term640 A x lt2 P x') = (term641 A x x' lt2 P).
Proof. exact (MK_COMB (@lem305260) (@lem305259 A x x' lt2 P)). Qed.
Lemma lem305262 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term635 A P lt2 x) = (term586 A x P lt2).
Proof. exact (eq_refl (term635 A P lt2 x)). Qed.
Lemma lem305263 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term642 A x P lt2 x') = (term643 A x x' P lt2).
Proof. exact (MK_COMB (@lem305261 A x x' lt2 P) (@lem305262 A x' P lt2)). Qed.
Lemma lem305264 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term644 A x P lt2) = (term645 A x P lt2).
Proof. exact (fun_ext (fun x' : A => @lem305263 A x x' P lt2)). Qed.
Lemma lem305265 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem305266 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term630 A x P lt2) = (term646 A x P lt2).
Proof. exact (MK_COMB (@lem305265 A) (@lem305264 A x P lt2)). Qed.
Lemma lem305267 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : ((term629 A x P lt2) = (term630 A x P lt2)) = ((term625 A x P lt2) = (term646 A x P lt2)).
Proof. exact (MK_COMB (@lem305258 A x P lt2) (@lem305266 A x P lt2)). Qed.
Lemma lem305268 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term625 A x P lt2) = (term646 A x P lt2).
Proof. exact (EQ_MP (@lem305267 A x P lt2) (@lem305245 A x P lt2)). Qed.
Lemma lem305270 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem305271 {A : Type'} (P : type488 A) (Q : type488 A) : (term647 A P Q) = (term648 A P Q).
Proof. exact (@lem305270 (A -> A) P Q). Qed.
Lemma lem305272 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term649 A x x' P lt2) = (term650 A x x' P lt2).
Proof. exact (@lem305271 A (term350 A x x' lt2 P) (term585 A x' P lt2)). Qed.
Lemma lem305273 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term651 A x x' lt2 P y) = (term348 A x x' lt2 P y).
Proof. exact (eq_refl (term651 A x x' lt2 P y)). Qed.
Lemma lem305274 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term652 A x x' lt2 P) = (term350 A x x' lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem305273 A x x' lt2 P y)). Qed.
Lemma lem305275 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem305276 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term653 A x x' lt2 P) = (term351 A x x' lt2 P).
Proof. exact (MK_COMB (@lem305275 A) (@lem305274 A x x' lt2 P)). Qed.
Lemma lem305277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305278 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) : (term654 A x x' lt2 P) = (term641 A x x' lt2 P).
Proof. exact (MK_COMB (@lem305277) (@lem305276 A x x' lt2 P)). Qed.
Lemma lem305279 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term655 A x P lt2 y) = (term584 A x P y lt2).
Proof. exact (eq_refl (term655 A x P lt2 y)). Qed.
Lemma lem305280 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term656 A x P lt2) = (term585 A x P lt2).
Proof. exact (fun_ext (fun y : A -> A => @lem305279 A x P y lt2)). Qed.
Lemma lem305281 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem305282 {A : Type'} (x : A) (P : A -> Prop) (lt2 : type1402 A) : (term657 A x P lt2) = (term586 A x P lt2).
Proof. exact (MK_COMB (@lem305281 A) (@lem305280 A x P lt2)). Qed.
Lemma lem305283 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term649 A x x' P lt2) = (term643 A x x' P lt2).
Proof. exact (MK_COMB (@lem305278 A x x' lt2 P) (@lem305282 A x' P lt2)). Qed.
Lemma lem305284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305285 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term658 A x x' P lt2) = (term659 A x x' P lt2).
Proof. exact (MK_COMB (@lem305284) (@lem305283 A x x' P lt2)). Qed.
Lemma lem305286 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term651 A x x' lt2 P y) = (term348 A x x' lt2 P y).
Proof. exact (eq_refl (term651 A x x' lt2 P y)). Qed.
Lemma lem305287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305288 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term660 A x x' lt2 P y) = (term661 A x x' lt2 P y).
Proof. exact (MK_COMB (@lem305287) (@lem305286 A x x' lt2 P y)). Qed.
Lemma lem305289 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term655 A x P lt2 y) = (term584 A x P y lt2).
Proof. exact (eq_refl (term655 A x P lt2 y)). Qed.
Lemma lem305290 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term662 A x x' P lt2 y) = (term663 A x x' P y lt2).
Proof. exact (MK_COMB (@lem305288 A x x' lt2 P y) (@lem305289 A x' P y lt2)). Qed.
Lemma lem305291 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term664 A x x' P lt2) = (term665 A x x' P lt2).
Proof. exact (fun_ext (fun y : A -> A => @lem305290 A x x' P y lt2)). Qed.
Lemma lem305292 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem305293 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term650 A x x' P lt2) = (term666 A x x' P lt2).
Proof. exact (MK_COMB (@lem305292 A) (@lem305291 A x x' P lt2)). Qed.
Lemma lem305294 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : ((term649 A x x' P lt2) = (term650 A x x' P lt2)) = ((term643 A x x' P lt2) = (term666 A x x' P lt2)).
Proof. exact (MK_COMB (@lem305285 A x x' P lt2) (@lem305293 A x x' P lt2)). Qed.
Lemma lem305295 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term643 A x x' P lt2) = (term666 A x x' P lt2).
Proof. exact (EQ_MP (@lem305294 A x x' P lt2) (@lem305272 A x x' P lt2)). Qed.
Lemma lem305297 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem305298 {A : Type'} (P : Prop) (Q : type162 A) : (term667 A P Q) = (term668 A P Q).
Proof. exact (@lem305297 (type684 A) P Q). Qed.
Lemma lem305299 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term669 A x x' P y lt2) = (term670 A x x' P y lt2).
Proof. exact (@lem305298 A (term348 A x x' lt2 P y) (term583 A x' P y lt2)). Qed.
Lemma lem305300 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term671 A x P y lt2 x') = (term582 A x P y x' lt2).
Proof. exact (eq_refl (term671 A x P y lt2 x')). Qed.
Lemma lem305301 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term672 A x P y lt2) = (term583 A x P y lt2).
Proof. exact (fun_ext (fun x' : type684 A => @lem305300 A x P y x' lt2)). Qed.
Lemma lem305302 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305303 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term673 A x P y lt2) = (term584 A x P y lt2).
Proof. exact (MK_COMB (@lem305302 A) (@lem305301 A x P y lt2)). Qed.
Lemma lem305304 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term661 A x x' lt2 P y) = (term661 A x x' lt2 P y).
Proof. exact (eq_refl (term661 A x x' lt2 P y)). Qed.
Lemma lem305305 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term669 A x x' P y lt2) = (term663 A x x' P y lt2).
Proof. exact (MK_COMB (@lem305304 A x x' lt2 P y) (@lem305303 A x' P y lt2)). Qed.
Lemma lem305306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305307 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term674 A x x' P y lt2) = (term675 A x x' P y lt2).
Proof. exact (MK_COMB (@lem305306) (@lem305305 A x x' P y lt2)). Qed.
Lemma lem305308 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term671 A x P y lt2 x') = (term582 A x P y x' lt2).
Proof. exact (eq_refl (term671 A x P y lt2 x')). Qed.
Lemma lem305309 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term661 A x x' lt2 P y) = (term661 A x x' lt2 P y).
Proof. exact (eq_refl (term661 A x x' lt2 P y)). Qed.
Lemma lem305310 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term676 A x x' P y lt2 x'') = (term677 A x x' P y x'' lt2).
Proof. exact (MK_COMB (@lem305309 A x x' lt2 P y) (@lem305308 A x' P y x'' lt2)). Qed.
Lemma lem305311 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term678 A x x' P y lt2) = (term679 A x x' P y lt2).
Proof. exact (fun_ext (fun x'' : type684 A => @lem305310 A x x' P y x'' lt2)). Qed.
Lemma lem305312 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305313 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term670 A x x' P y lt2) = (term680 A x x' P y lt2).
Proof. exact (MK_COMB (@lem305312 A) (@lem305311 A x x' P y lt2)). Qed.
Lemma lem305314 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : ((term669 A x x' P y lt2) = (term670 A x x' P y lt2)) = ((term663 A x x' P y lt2) = (term680 A x x' P y lt2)).
Proof. exact (MK_COMB (@lem305307 A x x' P y lt2) (@lem305313 A x x' P y lt2)). Qed.
Lemma lem305315 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term663 A x x' P y lt2) = (term680 A x x' P y lt2).
Proof. exact (EQ_MP (@lem305314 A x x' P y lt2) (@lem305299 A x x' P y lt2)). Qed.
Lemma lem305317 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem305318 {A : Type'} (P : Prop) (Q : type150 A) : (term681 A P Q) = (term682 A P Q).
Proof. exact (@lem305317 (type670 A) P Q). Qed.
Lemma lem305319 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term683 A x x' P y x'' lt2) = (term684 A x x' P y x'' lt2).
Proof. exact (@lem305318 A (term348 A x x' lt2 P y) (term581 A x' P y x'' lt2)). Qed.
Lemma lem305320 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term685 A x P y x' lt2 y') = (term580 A x P y x' y' lt2).
Proof. exact (eq_refl (term685 A x P y x' lt2 y')). Qed.
Lemma lem305321 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term686 A x P y x' lt2) = (term581 A x P y x' lt2).
Proof. exact (fun_ext (fun y' : type670 A => @lem305320 A x P y x' y' lt2)). Qed.
Lemma lem305322 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305323 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (lt2 : type1402 A) : (term687 A x P y x' lt2) = (term582 A x P y x' lt2).
Proof. exact (MK_COMB (@lem305322 A) (@lem305321 A x P y x' lt2)). Qed.
Lemma lem305324 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term661 A x x' lt2 P y) = (term661 A x x' lt2 P y).
Proof. exact (eq_refl (term661 A x x' lt2 P y)). Qed.
Lemma lem305325 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term683 A x x' P y x'' lt2) = (term677 A x x' P y x'' lt2).
Proof. exact (MK_COMB (@lem305324 A x x' lt2 P y) (@lem305323 A x' P y x'' lt2)). Qed.
Lemma lem305326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305327 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term688 A x x' P y x'' lt2) = (term689 A x x' P y x'' lt2).
Proof. exact (MK_COMB (@lem305326) (@lem305325 A x x' P y x'' lt2)). Qed.
Lemma lem305328 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term685 A x P y x' lt2 y') = (term580 A x P y x' y' lt2).
Proof. exact (eq_refl (term685 A x P y x' lt2 y')). Qed.
Lemma lem305329 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term661 A x x' lt2 P y) = (term661 A x x' lt2 P y).
Proof. exact (eq_refl (term661 A x x' lt2 P y)). Qed.
Lemma lem305330 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term690 A x x' P y x'' lt2 y') = (term691 A x x' P y x'' y' lt2).
Proof. exact (MK_COMB (@lem305329 A x x' lt2 P y) (@lem305328 A x' P y x'' y' lt2)). Qed.
Lemma lem305331 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term692 A x x' P y x'' lt2) = (term693 A x x' P y x'' lt2).
Proof. exact (fun_ext (fun y' : type670 A => @lem305330 A x x' P y x'' y' lt2)). Qed.
Lemma lem305332 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305333 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term684 A x x' P y x'' lt2) = (term694 A x x' P y x'' lt2).
Proof. exact (MK_COMB (@lem305332 A) (@lem305331 A x x' P y x'' lt2)). Qed.
Lemma lem305334 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : ((term683 A x x' P y x'' lt2) = (term684 A x x' P y x'' lt2)) = ((term677 A x x' P y x'' lt2) = (term694 A x x' P y x'' lt2)).
Proof. exact (MK_COMB (@lem305327 A x x' P y x'' lt2) (@lem305333 A x x' P y x'' lt2)). Qed.
Lemma lem305335 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term677 A x x' P y x'' lt2) = (term694 A x x' P y x'' lt2).
Proof. exact (EQ_MP (@lem305334 A x x' P y x'' lt2) (@lem305319 A x x' P y x'' lt2)). Qed.
Lemma lem305337 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem305338 {A : Type'} (P : Prop) (Q : type162 A) : (term667 A P Q) = (term668 A P Q).
Proof. exact (@lem305337 (type684 A) P Q). Qed.
Lemma lem305339 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term695 A x x' P y x'' y' lt2) = (term696 A x x' P y x'' y' lt2).
Proof. exact (@lem305338 A (term348 A x x' lt2 P y) (term579 A x' P y x'' y' lt2)). Qed.
Lemma lem305340 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x'' : type684 A) : (term697 A x P y x' y' lt2 x'') = (term577 A x P y x' y' lt2 x'').
Proof. exact (eq_refl (term697 A x P y x' y' lt2 x'')). Qed.
Lemma lem305341 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term698 A x P y x' y' lt2) = (term579 A x P y x' y' lt2).
Proof. exact (fun_ext (fun x'' : type684 A => @lem305340 A x P y x' y' lt2 x'')). Qed.
Lemma lem305342 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305343 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term699 A x P y x' y' lt2) = (term580 A x P y x' y' lt2).
Proof. exact (MK_COMB (@lem305342 A) (@lem305341 A x P y x' y' lt2)). Qed.
Lemma lem305344 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term661 A x x' lt2 P y) = (term661 A x x' lt2 P y).
Proof. exact (eq_refl (term661 A x x' lt2 P y)). Qed.
Lemma lem305345 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term695 A x x' P y x'' y' lt2) = (term691 A x x' P y x'' y' lt2).
Proof. exact (MK_COMB (@lem305344 A x x' lt2 P y) (@lem305343 A x' P y x'' y' lt2)). Qed.
Lemma lem305346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem305347 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term700 A x x' P y x'' y' lt2) = (term701 A x x' P y x'' y' lt2).
Proof. exact (MK_COMB (@lem305346) (@lem305345 A x x' P y x'' y' lt2)). Qed.
Lemma lem305348 {A : Type'} (x : A) (P : A -> Prop) (y : A -> A) (x' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x'' : type684 A) : (term697 A x P y x' y' lt2 x'') = (term577 A x P y x' y' lt2 x'').
Proof. exact (eq_refl (term697 A x P y x' y' lt2 x'')). Qed.
Lemma lem305349 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term661 A x x' lt2 P y) = (term661 A x x' lt2 P y).
Proof. exact (eq_refl (term661 A x x' lt2 P y)). Qed.
Lemma lem305350 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) : (term702 A x x' P y x'' y' lt2 x''') = (term703 A x x' P y x'' y' lt2 x''').
Proof. exact (MK_COMB (@lem305349 A x x' lt2 P y) (@lem305348 A x' P y x'' y' lt2 x''')). Qed.
Lemma lem305351 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term704 A x x' P y x'' y' lt2) = (term705 A x x' P y x'' y' lt2).
Proof. exact (fun_ext (fun x''' : type684 A => @lem305350 A x x' P y x'' y' lt2 x''')). Qed.
Lemma lem305352 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305353 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term696 A x x' P y x'' y' lt2) = (term706 A x x' P y x'' y' lt2).
Proof. exact (MK_COMB (@lem305352 A) (@lem305351 A x x' P y x'' y' lt2)). Qed.
Lemma lem305354 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : ((term695 A x x' P y x'' y' lt2) = (term696 A x x' P y x'' y' lt2)) = ((term691 A x x' P y x'' y' lt2) = (term706 A x x' P y x'' y' lt2)).
Proof. exact (MK_COMB (@lem305347 A x x' P y x'' y' lt2) (@lem305353 A x x' P y x'' y' lt2)). Qed.
Lemma lem305355 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) : (term691 A x x' P y x'' y' lt2) = (term706 A x x' P y x'' y' lt2).
Proof. exact (EQ_MP (@lem305354 A x x' P y x'' y' lt2) (@lem305339 A x x' P y x'' y' lt2)). Qed.
Lemma lem305356 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term693 A x x' P y x'' lt2) = (term707 A x x' P y x'' lt2).
Proof. exact (fun_ext (fun y' : type670 A => @lem305355 A x x' P y x'' y' lt2)). Qed.
Lemma lem305357 {A : Type'} : (@ex ((A -> Prop) -> A -> A)) = (@ex ((A -> Prop) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A))). Qed.
Lemma lem305358 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term694 A x x' P y x'' lt2) = (term708 A x x' P y x'' lt2).
Proof. exact (MK_COMB (@lem305357 A) (@lem305356 A x x' P y x'' lt2)). Qed.
Lemma lem305359 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) : (term677 A x x' P y x'' lt2) = (term708 A x x' P y x'' lt2).
Proof. exact (TRANS (@lem305335 A x x' P y x'' lt2) (@lem305358 A x x' P y x'' lt2)). Qed.
Lemma lem305360 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term679 A x x' P y lt2) = (term709 A x x' P y lt2).
Proof. exact (fun_ext (fun x'' : type684 A => @lem305359 A x x' P y x'' lt2)). Qed.
Lemma lem305361 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305362 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term680 A x x' P y lt2) = (term710 A x x' P y lt2).
Proof. exact (MK_COMB (@lem305361 A) (@lem305360 A x x' P y lt2)). Qed.
Lemma lem305363 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) : (term663 A x x' P y lt2) = (term710 A x x' P y lt2).
Proof. exact (TRANS (@lem305315 A x x' P y lt2) (@lem305362 A x x' P y lt2)). Qed.
Lemma lem305364 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term665 A x x' P lt2) = (term711 A x x' P lt2).
Proof. exact (fun_ext (fun y : A -> A => @lem305363 A x x' P y lt2)). Qed.
Lemma lem305365 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem305366 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term666 A x x' P lt2) = (term712 A x x' P lt2).
Proof. exact (MK_COMB (@lem305365 A) (@lem305364 A x x' P lt2)). Qed.
Lemma lem305367 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) : (term643 A x x' P lt2) = (term712 A x x' P lt2).
Proof. exact (TRANS (@lem305295 A x x' P lt2) (@lem305366 A x x' P lt2)). Qed.
Lemma lem305368 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term645 A x P lt2) = (term713 A x P lt2).
Proof. exact (fun_ext (fun x' : A => @lem305367 A x x' P lt2)). Qed.
Lemma lem305369 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem305370 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term646 A x P lt2) = (term714 A x P lt2).
Proof. exact (MK_COMB (@lem305369 A) (@lem305368 A x P lt2)). Qed.
Lemma lem305371 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) : (term625 A x P lt2) = (term714 A x P lt2).
Proof. exact (TRANS (@lem305268 A x P lt2) (@lem305370 A x P lt2)). Qed.
Lemma lem305372 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term627 A x lt2) = (term715 A x lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305371 A x P lt2)). Qed.
Lemma lem305373 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem305374 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term628 A x lt2) = (term716 A x lt2).
Proof. exact (MK_COMB (@lem305373 A) (@lem305372 A x lt2)). Qed.
Lemma lem305375 {A : Type'} (x : type684 A) (lt2 : type1402 A) : (term605 A x lt2) = (term716 A x lt2).
Proof. exact (TRANS (@lem305241 A x lt2) (@lem305374 A x lt2)). Qed.
Lemma lem305376 {A : Type'} (lt2 : type1402 A) : (term607 A lt2) = (term717 A lt2).
Proof. exact (fun_ext (fun x : type684 A => @lem305375 A x lt2)). Qed.
Lemma lem305377 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem305378 {A : Type'} (lt2 : type1402 A) : (term608 A lt2) = (term718 A lt2).
Proof. exact (MK_COMB (@lem305377 A) (@lem305376 A lt2)). Qed.
Lemma lem305379 {A : Type'} (lt2 : type1402 A) : (term591 A lt2) = (term718 A lt2).
Proof. exact (TRANS (@lem305214 A lt2) (@lem305378 A lt2)). Qed.
Lemma lem305380 {A : Type'} (lt2 : type1402 A) : (term150 A lt2) = (term718 A lt2).
Proof. exact (TRANS (@lem305188 A lt2) (@lem305379 A lt2)). Qed.
Lemma lem305381 {A : Type'} (lt2 : type1402 A) : (term126 A lt2) = (term718 A lt2).
Proof. exact (TRANS (@lem304346 A lt2) (@lem305380 A lt2)). Qed.
Lemma lem305382 {A : Type'} (lt2 : type1402 A) : (term7 A lt2) = (term718 A lt2).
Proof. exact (TRANS (@lem303583 A lt2) (@lem305381 A lt2)). Qed.
Lemma lem305383 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : term718 A lt2.
Proof. exact (EQ_MP (@lem305382 A lt2) (@lem303380 A lt2 h1)). Qed.
Lemma lem305384 {A : Type'} (x : type684 A) (lt2 : type1402 A) (h1 : term716 A x lt2) : term716 A x lt2.
Proof. exact (h1). Qed.
Lemma lem305385 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term714 A x P lt2) : term714 A x P lt2.
Proof. exact (h1). Qed.
Lemma lem305386 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term712 A x x' P lt2) : term712 A x x' P lt2.
Proof. exact (h1). Qed.
Lemma lem305387 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) (h1 : term710 A x x' P y lt2) : term710 A x x' P y lt2.
Proof. exact (h1). Qed.
Lemma lem305388 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) (h1 : term708 A x x' P y x'' lt2) : term708 A x x' P y x'' lt2.
Proof. exact (h1). Qed.
Lemma lem305389 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (h1 : term706 A x x' P y x'' y' lt2) : term706 A x x' P y x'' y' lt2.
Proof. exact (h1). Qed.
Lemma lem305390 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term703 A x x' P y x'' y' lt2 x''') : term703 A x x' P y x'' y' lt2 x'''.
Proof. exact (h1). Qed.
Lemma lem305391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305397 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305396 A Prop f x). Qed.
Lemma lem305399 {A : Type'} (P : A -> Prop) (y : A) : (P y) = (@I (A -> Prop) P y).
Proof. exact (@lem305397 A P y). Qed.
Lemma lem305400 {A : Type'} (P : A -> Prop) (y : A) : (term37 A P y) = (term719 A P y).
Proof. exact (MK_COMB (@lem305391) (@lem305399 A P y)). Qed.
Lemma lem305401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305408 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305409 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem305408 (A -> Prop) A f x). Qed.
Lemma lem305411 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (x''' P) = (@I ((A -> Prop) -> A) x''' P).
Proof. exact (@lem305409 A x''' P). Qed.
Lemma lem305412 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem305413 {A : Type'} (lt2 : type1402 A) (y : A) (x''' : type684 A) (P : A -> Prop) : (term720 A lt2 y x''' P) = (term721 A lt2 y x''' P).
Proof. exact (MK_COMB (@lem305412 A lt2 y) (@lem305411 A x''' P)). Qed.
Lemma lem305415 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305416 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem305415 A (A -> Prop) f x). Qed.
Lemma lem305417 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem305416 A lt2 y). Qed.
Lemma lem305418 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (@I ((A -> Prop) -> A) x''' P) = (@I ((A -> Prop) -> A) x''' P).
Proof. exact (eq_refl (@I ((A -> Prop) -> A) x''' P)). Qed.
Lemma lem305419 {A : Type'} (lt2 : type1402 A) (y : A) (x''' : type684 A) (P : A -> Prop) : (term721 A lt2 y x''' P) = (term722 A lt2 y x''' P).
Proof. exact (MK_COMB (@lem305417 A lt2 y) (@lem305418 A x''' P)). Qed.
Lemma lem305421 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305422 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305421 A Prop f x). Qed.
Lemma lem305423 {A : Type'} (lt2 : type1402 A) (y : A) (x''' : type684 A) (P : A -> Prop) : (term722 A lt2 y x''' P) = (term723 A lt2 y x''' P).
Proof. exact (@lem305422 A (@I (A -> A -> Prop) lt2 y) (@I ((A -> Prop) -> A) x''' P)). Qed.
Lemma lem305424 {A : Type'} (lt2 : type1402 A) (y : A) (x''' : type684 A) (P : A -> Prop) : (term721 A lt2 y x''' P) = (term723 A lt2 y x''' P).
Proof. exact (TRANS (@lem305419 A lt2 y x''' P) (@lem305423 A lt2 y x''' P)). Qed.
Lemma lem305425 {A : Type'} (lt2 : type1402 A) (y : A) (x''' : type684 A) (P : A -> Prop) : (term720 A lt2 y x''' P) = (term723 A lt2 y x''' P).
Proof. exact (TRANS (@lem305413 A lt2 y x''' P) (@lem305424 A lt2 y x''' P)). Qed.
Lemma lem305426 {A : Type'} (lt2 : type1402 A) (y : A) (x''' : type684 A) (P : A -> Prop) : (term724 A lt2 y x''' P) = (term725 A lt2 y x''' P).
Proof. exact (MK_COMB (@lem305401) (@lem305425 A lt2 y x''' P)). Qed.
Lemma lem305427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305428 {A : Type'} (lt2 : type1402 A) (y : A) (x''' : type684 A) (P : A -> Prop) : (term726 A lt2 y x''' P) = (term727 A lt2 y x''' P).
Proof. exact (MK_COMB (@lem305427) (@lem305426 A lt2 y x''' P)). Qed.
Lemma lem305429 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term728 A lt2 x''' P y) = (term729 A lt2 x''' P y).
Proof. exact (MK_COMB (@lem305428 A lt2 y x''' P) (@lem305400 A P y)). Qed.
Lemma lem305430 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term730 A lt2 x''' P) = (term731 A lt2 x''' P).
Proof. exact (fun_ext (fun y : A => @lem305429 A lt2 x''' P y)). Qed.
Lemma lem305431 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305432 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term732 A lt2 x''' P) = (term733 A lt2 x''' P).
Proof. exact (MK_COMB (@lem305431 A) (@lem305430 A lt2 x''' P)). Qed.
Lemma lem305433 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem305438 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305439 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem305438 (A -> Prop) A f x). Qed.
Lemma lem305441 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (x''' P) = (@I ((A -> Prop) -> A) x''' P).
Proof. exact (@lem305439 A x''' P). Qed.
Lemma lem305442 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term734 A x''' P) = (term735 A x''' P).
Proof. exact (MK_COMB (@lem305433 A P) (@lem305441 A x''' P)). Qed.
Lemma lem305444 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305445 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305444 A Prop f x). Qed.
Lemma lem305446 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term735 A x''' P) = (term736 A x''' P).
Proof. exact (@lem305445 A P (@I ((A -> Prop) -> A) x''' P)). Qed.
Lemma lem305447 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term734 A x''' P) = (term736 A x''' P).
Proof. exact (TRANS (@lem305442 A x''' P) (@lem305446 A x''' P)). Qed.
Lemma lem305448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305449 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term737 A x''' P) = (term738 A x''' P).
Proof. exact (MK_COMB (@lem305448) (@lem305447 A x''' P)). Qed.
Lemma lem305450 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term739 A lt2 x''' P) = (term740 A lt2 x''' P).
Proof. exact (MK_COMB (@lem305449 A x''' P) (@lem305432 A lt2 x''' P)). Qed.
Lemma lem305451 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305456 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305457 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305456 A Prop f x). Qed.
Lemma lem305459 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (@I (A -> Prop) P x).
Proof. exact (@lem305457 A P x). Qed.
Lemma lem305460 {A : Type'} (P : A -> Prop) (x : A) : (term37 A P x) = (term719 A P x).
Proof. exact (MK_COMB (@lem305451) (@lem305459 A P x)). Qed.
Lemma lem305461 {A : Type'} (P : A -> Prop) : (term39 A P) = (term741 A P).
Proof. exact (fun_ext (fun x : A => @lem305460 A P x)). Qed.
Lemma lem305462 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305463 {A : Type'} (P : A -> Prop) : (term32 A P) = (term742 A P).
Proof. exact (MK_COMB (@lem305462 A) (@lem305461 A P)). Qed.
Lemma lem305464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305465 {A : Type'} (P : A -> Prop) : (term76 A P) = (term743 A P).
Proof. exact (MK_COMB (@lem305464) (@lem305463 A P)). Qed.
Lemma lem305466 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term184 A lt2 x''' P) = (term744 A lt2 x''' P).
Proof. exact (MK_COMB (@lem305465 A P) (@lem305450 A lt2 x''' P)). Qed.
Lemma lem305467 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) : (term186 A lt2 x''') = (term745 A lt2 x''').
Proof. exact (fun_ext (fun P : A -> Prop => @lem305466 A lt2 x''' P)). Qed.
Lemma lem305468 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem305469 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) : (term188 A lt2 x''') = (term746 A lt2 x''').
Proof. exact (MK_COMB (@lem305468 A) (@lem305467 A lt2 x''')). Qed.
Lemma lem305470 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem305477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305478 {A : Type'} (f : type670 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A) f x).
Proof. exact (@lem305477 (A -> Prop) (A -> A) f x). Qed.
Lemma lem305479 {A : Type'} (y' : type670 A) (P : A -> Prop) : (y' P) = (@I ((A -> Prop) -> A -> A) y' P).
Proof. exact (@lem305478 A y' P). Qed.
Lemma lem305480 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305481 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (y' P x) = (@I ((A -> Prop) -> A -> A) y' P x).
Proof. exact (MK_COMB (@lem305479 A y' P) (@lem305480 A x)). Qed.
Lemma lem305483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305484 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem305483 A A f x). Qed.
Lemma lem305485 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A) y' P x) = (term747 A y' P x).
Proof. exact (@lem305484 A (@I ((A -> Prop) -> A -> A) y' P) x). Qed.
Lemma lem305487 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (y' P x) = (term747 A y' P x).
Proof. exact (TRANS (@lem305481 A y' P x) (@lem305485 A y' P x)). Qed.
Lemma lem305488 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (term748 A y' P x) = (term749 A y' P x).
Proof. exact (MK_COMB (@lem305470 A P) (@lem305487 A y' P x)). Qed.
Lemma lem305490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305491 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305490 A Prop f x). Qed.
Lemma lem305492 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (term749 A y' P x) = (term750 A y' P x).
Proof. exact (@lem305491 A P (term747 A y' P x)). Qed.
Lemma lem305493 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (term748 A y' P x) = (term750 A y' P x).
Proof. exact (TRANS (@lem305488 A y' P x) (@lem305492 A y' P x)). Qed.
Lemma lem305494 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem305501 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305502 {A : Type'} (f : type670 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A) f x).
Proof. exact (@lem305501 (A -> Prop) (A -> A) f x). Qed.
Lemma lem305503 {A : Type'} (y' : type670 A) (P : A -> Prop) : (y' P) = (@I ((A -> Prop) -> A -> A) y' P).
Proof. exact (@lem305502 A y' P). Qed.
Lemma lem305504 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305505 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (y' P x) = (@I ((A -> Prop) -> A -> A) y' P x).
Proof. exact (MK_COMB (@lem305503 A y' P) (@lem305504 A x)). Qed.
Lemma lem305507 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305508 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem305507 A A f x). Qed.
Lemma lem305509 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A) y' P x) = (term747 A y' P x).
Proof. exact (@lem305508 A (@I ((A -> Prop) -> A -> A) y' P) x). Qed.
Lemma lem305511 {A : Type'} (y' : type670 A) (P : A -> Prop) (x : A) : (y' P x) = (term747 A y' P x).
Proof. exact (TRANS (@lem305505 A y' P x) (@lem305509 A y' P x)). Qed.
Lemma lem305512 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305513 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term751 A lt2 y' P x) = (term752 A lt2 y' P x).
Proof. exact (MK_COMB (@lem305494 A lt2) (@lem305511 A y' P x)). Qed.
Lemma lem305514 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term753 A lt2 y' P x) = (term754 A lt2 y' P x).
Proof. exact (MK_COMB (@lem305513 A lt2 y' P x) (@lem305512 A x)). Qed.
Lemma lem305516 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305517 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem305516 A (A -> Prop) f x). Qed.
Lemma lem305518 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term752 A lt2 y' P x) = (term755 A lt2 y' P x).
Proof. exact (@lem305517 A lt2 (term747 A y' P x)). Qed.
Lemma lem305519 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305520 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term754 A lt2 y' P x) = (term756 A lt2 y' P x).
Proof. exact (MK_COMB (@lem305518 A lt2 y' P x) (@lem305519 A x)). Qed.
Lemma lem305522 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305523 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305522 A Prop f x). Qed.
Lemma lem305524 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term756 A lt2 y' P x) = (term757 A lt2 y' P x).
Proof. exact (@lem305523 A (term755 A lt2 y' P x) x). Qed.
Lemma lem305525 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term754 A lt2 y' P x) = (term757 A lt2 y' P x).
Proof. exact (TRANS (@lem305520 A lt2 y' P x) (@lem305524 A lt2 y' P x)). Qed.
Lemma lem305526 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term753 A lt2 y' P x) = (term757 A lt2 y' P x).
Proof. exact (TRANS (@lem305514 A lt2 y' P x) (@lem305525 A lt2 y' P x)). Qed.
Lemma lem305527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305528 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term758 A lt2 y' P x) = (term759 A lt2 y' P x).
Proof. exact (MK_COMB (@lem305527) (@lem305526 A lt2 y' P x)). Qed.
Lemma lem305529 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term760 A lt2 y' P x) = (term761 A lt2 y' P x).
Proof. exact (MK_COMB (@lem305528 A lt2 y' P x) (@lem305493 A y' P x)). Qed.
Lemma lem305530 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305535 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305536 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305535 A Prop f x). Qed.
Lemma lem305538 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (@I (A -> Prop) P x).
Proof. exact (@lem305536 A P x). Qed.
Lemma lem305539 {A : Type'} (P : A -> Prop) (x : A) : (term37 A P x) = (term719 A P x).
Proof. exact (MK_COMB (@lem305530) (@lem305538 A P x)). Qed.
Lemma lem305540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305541 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term762 A P x).
Proof. exact (MK_COMB (@lem305540) (@lem305539 A P x)). Qed.
Lemma lem305542 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) (x : A) : (term763 A lt2 y' P x) = (term764 A lt2 y' P x).
Proof. exact (MK_COMB (@lem305541 A P x) (@lem305529 A lt2 y' P x)). Qed.
Lemma lem305543 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) : (term765 A lt2 y' P) = (term766 A lt2 y' P).
Proof. exact (fun_ext (fun x : A => @lem305542 A lt2 y' P x)). Qed.
Lemma lem305544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305545 {A : Type'} (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) : (term767 A lt2 y' P) = (term768 A lt2 y' P).
Proof. exact (MK_COMB (@lem305544 A) (@lem305543 A lt2 y' P)). Qed.
Lemma lem305546 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem305551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305552 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem305551 (A -> Prop) A f x). Qed.
Lemma lem305554 {A : Type'} (x'' : type684 A) (P : A -> Prop) : (x'' P) = (@I ((A -> Prop) -> A) x'' P).
Proof. exact (@lem305552 A x'' P). Qed.
Lemma lem305555 {A : Type'} (x'' : type684 A) (P : A -> Prop) : (term734 A x'' P) = (term735 A x'' P).
Proof. exact (MK_COMB (@lem305546 A P) (@lem305554 A x'' P)). Qed.
Lemma lem305557 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305558 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305557 A Prop f x). Qed.
Lemma lem305559 {A : Type'} (x'' : type684 A) (P : A -> Prop) : (term735 A x'' P) = (term736 A x'' P).
Proof. exact (@lem305558 A P (@I ((A -> Prop) -> A) x'' P)). Qed.
Lemma lem305560 {A : Type'} (x'' : type684 A) (P : A -> Prop) : (term734 A x'' P) = (term736 A x'' P).
Proof. exact (TRANS (@lem305555 A x'' P) (@lem305559 A x'' P)). Qed.
Lemma lem305561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305562 {A : Type'} (x'' : type684 A) (P : A -> Prop) : (term769 A x'' P) = (term770 A x'' P).
Proof. exact (MK_COMB (@lem305561) (@lem305560 A x'' P)). Qed.
Lemma lem305563 {A : Type'} (x'' : type684 A) (lt2 : type1402 A) (y' : type670 A) (P : A -> Prop) : (term434 A x'' lt2 y' P) = (term771 A x'' lt2 y' P).
Proof. exact (MK_COMB (@lem305562 A x'' P) (@lem305545 A lt2 y' P)). Qed.
Lemma lem305564 {A : Type'} (x'' : type684 A) (lt2 : type1402 A) (y' : type670 A) : (term436 A x'' lt2 y') = (term772 A x'' lt2 y').
Proof. exact (fun_ext (fun P : A -> Prop => @lem305563 A x'' lt2 y' P)). Qed.
Lemma lem305565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem305566 {A : Type'} (x'' : type684 A) (lt2 : type1402 A) (y' : type670 A) : (term438 A x'' lt2 y') = (term773 A x'' lt2 y').
Proof. exact (MK_COMB (@lem305565 A) (@lem305564 A x'' lt2 y')). Qed.
Lemma lem305567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305568 {A : Type'} (x'' : type684 A) (lt2 : type1402 A) (y' : type670 A) : (term472 A x'' lt2 y') = (term774 A x'' lt2 y').
Proof. exact (MK_COMB (@lem305567) (@lem305566 A x'' lt2 y')). Qed.
Lemma lem305569 {A : Type'} (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) : (term485 A x'' y' lt2 x''') = (term775 A x'' y' lt2 x''').
Proof. exact (MK_COMB (@lem305568 A x'' lt2 y') (@lem305469 A lt2 x''')). Qed.
Lemma lem305570 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem305575 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305576 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem305575 A A f x). Qed.
Lemma lem305578 {A : Type'} (y : A -> A) (x : A) : (y x) = (@I (A -> A) y x).
Proof. exact (@lem305576 A y x). Qed.
Lemma lem305579 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term776 A P y x) = (term777 A P y x).
Proof. exact (MK_COMB (@lem305570 A P) (@lem305578 A y x)). Qed.
Lemma lem305581 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305582 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305581 A Prop f x). Qed.
Lemma lem305583 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term777 A P y x) = (term778 A P y x).
Proof. exact (@lem305582 A P (@I (A -> A) y x)). Qed.
Lemma lem305584 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term776 A P y x) = (term778 A P y x).
Proof. exact (TRANS (@lem305579 A P y x) (@lem305583 A P y x)). Qed.
Lemma lem305585 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem305590 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305591 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem305590 A A f x). Qed.
Lemma lem305593 {A : Type'} (y : A -> A) (x : A) : (y x) = (@I (A -> A) y x).
Proof. exact (@lem305591 A y x). Qed.
Lemma lem305594 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305595 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term779 A lt2 y x) = (term780 A lt2 y x).
Proof. exact (MK_COMB (@lem305585 A lt2) (@lem305593 A y x)). Qed.
Lemma lem305596 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term781 A lt2 y x) = (term782 A lt2 y x).
Proof. exact (MK_COMB (@lem305595 A lt2 y x) (@lem305594 A x)). Qed.
Lemma lem305598 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305599 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem305598 A (A -> Prop) f x). Qed.
Lemma lem305600 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term780 A lt2 y x) = (term783 A lt2 y x).
Proof. exact (@lem305599 A lt2 (@I (A -> A) y x)). Qed.
Lemma lem305601 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305602 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term782 A lt2 y x) = (term784 A lt2 y x).
Proof. exact (MK_COMB (@lem305600 A lt2 y x) (@lem305601 A x)). Qed.
Lemma lem305604 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305605 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305604 A Prop f x). Qed.
Lemma lem305606 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term784 A lt2 y x) = (term785 A lt2 y x).
Proof. exact (@lem305605 A (term783 A lt2 y x) x). Qed.
Lemma lem305607 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term782 A lt2 y x) = (term785 A lt2 y x).
Proof. exact (TRANS (@lem305602 A lt2 y x) (@lem305606 A lt2 y x)). Qed.
Lemma lem305608 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term781 A lt2 y x) = (term785 A lt2 y x).
Proof. exact (TRANS (@lem305596 A lt2 y x) (@lem305607 A lt2 y x)). Qed.
Lemma lem305609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305610 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term786 A lt2 y x) = (term787 A lt2 y x).
Proof. exact (MK_COMB (@lem305609) (@lem305608 A lt2 y x)). Qed.
Lemma lem305611 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term788 A lt2 P y x) = (term789 A lt2 P y x).
Proof. exact (MK_COMB (@lem305610 A lt2 y x) (@lem305584 A P y x)). Qed.
Lemma lem305612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305618 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305617 A Prop f x). Qed.
Lemma lem305620 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (@I (A -> Prop) P x).
Proof. exact (@lem305618 A P x). Qed.
Lemma lem305621 {A : Type'} (P : A -> Prop) (x : A) : (term37 A P x) = (term719 A P x).
Proof. exact (MK_COMB (@lem305612) (@lem305620 A P x)). Qed.
Lemma lem305622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305623 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term762 A P x).
Proof. exact (MK_COMB (@lem305622) (@lem305621 A P x)). Qed.
Lemma lem305624 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term235 A lt2 P y x) = (term790 A lt2 P y x).
Proof. exact (MK_COMB (@lem305623 A P x) (@lem305611 A lt2 P y x)). Qed.
Lemma lem305625 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term237 A lt2 P y) = (term791 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem305624 A lt2 P y x)). Qed.
Lemma lem305626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305627 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term239 A lt2 P y) = (term792 A lt2 P y).
Proof. exact (MK_COMB (@lem305626 A) (@lem305625 A lt2 P y)). Qed.
Lemma lem305632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305633 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305632 A Prop f x). Qed.
Lemma lem305635 {A : Type'} (P : A -> Prop) (x' : A) : (P x') = (@I (A -> Prop) P x').
Proof. exact (@lem305633 A P x'). Qed.
Lemma lem305636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305637 {A : Type'} (P : A -> Prop) (x' : A) : (term20 A P x') = (term793 A P x').
Proof. exact (MK_COMB (@lem305636) (@lem305635 A P x')). Qed.
Lemma lem305638 {A : Type'} (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term367 A x' lt2 P y) = (term794 A x' lt2 P y).
Proof. exact (MK_COMB (@lem305637 A P x') (@lem305627 A lt2 P y)). Qed.
Lemma lem305639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305640 {A : Type'} (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term537 A x' lt2 P y) = (term795 A x' lt2 P y).
Proof. exact (MK_COMB (@lem305639) (@lem305638 A x' lt2 P y)). Qed.
Lemma lem305641 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) : (term577 A x' P y x'' y' lt2 x''') = (term796 A x' P y x'' y' lt2 x''').
Proof. exact (MK_COMB (@lem305640 A x' lt2 P y) (@lem305569 A x'' y' lt2 x''')). Qed.
Lemma lem305642 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem305647 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305648 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem305647 A A f x). Qed.
Lemma lem305650 {A : Type'} (y : A -> A) (x : A) : (y x) = (@I (A -> A) y x).
Proof. exact (@lem305648 A y x). Qed.
Lemma lem305651 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term776 A P y x) = (term777 A P y x).
Proof. exact (MK_COMB (@lem305642 A P) (@lem305650 A y x)). Qed.
Lemma lem305653 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305654 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305653 A Prop f x). Qed.
Lemma lem305655 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term777 A P y x) = (term778 A P y x).
Proof. exact (@lem305654 A P (@I (A -> A) y x)). Qed.
Lemma lem305656 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term776 A P y x) = (term778 A P y x).
Proof. exact (TRANS (@lem305651 A P y x) (@lem305655 A P y x)). Qed.
Lemma lem305657 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem305662 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305663 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem305662 A A f x). Qed.
Lemma lem305665 {A : Type'} (y : A -> A) (x : A) : (y x) = (@I (A -> A) y x).
Proof. exact (@lem305663 A y x). Qed.
Lemma lem305666 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305667 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term779 A lt2 y x) = (term780 A lt2 y x).
Proof. exact (MK_COMB (@lem305657 A lt2) (@lem305665 A y x)). Qed.
Lemma lem305668 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term781 A lt2 y x) = (term782 A lt2 y x).
Proof. exact (MK_COMB (@lem305667 A lt2 y x) (@lem305666 A x)). Qed.
Lemma lem305670 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305671 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem305670 A (A -> Prop) f x). Qed.
Lemma lem305672 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term780 A lt2 y x) = (term783 A lt2 y x).
Proof. exact (@lem305671 A lt2 (@I (A -> A) y x)). Qed.
Lemma lem305673 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem305674 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term782 A lt2 y x) = (term784 A lt2 y x).
Proof. exact (MK_COMB (@lem305672 A lt2 y x) (@lem305673 A x)). Qed.
Lemma lem305676 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305677 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305676 A Prop f x). Qed.
Lemma lem305678 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term784 A lt2 y x) = (term785 A lt2 y x).
Proof. exact (@lem305677 A (term783 A lt2 y x) x). Qed.
Lemma lem305679 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term782 A lt2 y x) = (term785 A lt2 y x).
Proof. exact (TRANS (@lem305674 A lt2 y x) (@lem305678 A lt2 y x)). Qed.
Lemma lem305680 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term781 A lt2 y x) = (term785 A lt2 y x).
Proof. exact (TRANS (@lem305668 A lt2 y x) (@lem305679 A lt2 y x)). Qed.
Lemma lem305681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305682 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term786 A lt2 y x) = (term787 A lt2 y x).
Proof. exact (MK_COMB (@lem305681) (@lem305680 A lt2 y x)). Qed.
Lemma lem305683 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term788 A lt2 P y x) = (term789 A lt2 P y x).
Proof. exact (MK_COMB (@lem305682 A lt2 y x) (@lem305656 A P y x)). Qed.
Lemma lem305684 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305690 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305689 A Prop f x). Qed.
Lemma lem305692 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (@I (A -> Prop) P x).
Proof. exact (@lem305690 A P x). Qed.
Lemma lem305693 {A : Type'} (P : A -> Prop) (x : A) : (term37 A P x) = (term719 A P x).
Proof. exact (MK_COMB (@lem305684) (@lem305692 A P x)). Qed.
Lemma lem305694 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305695 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term762 A P x).
Proof. exact (MK_COMB (@lem305694) (@lem305693 A P x)). Qed.
Lemma lem305696 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term235 A lt2 P y x) = (term790 A lt2 P y x).
Proof. exact (MK_COMB (@lem305695 A P x) (@lem305683 A lt2 P y x)). Qed.
Lemma lem305697 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term237 A lt2 P y) = (term791 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem305696 A lt2 P y x)). Qed.
Lemma lem305698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305699 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term239 A lt2 P y) = (term792 A lt2 P y).
Proof. exact (MK_COMB (@lem305698 A) (@lem305697 A lt2 P y)). Qed.
Lemma lem305700 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305706 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305705 A Prop f x). Qed.
Lemma lem305708 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (@I (A -> Prop) P x).
Proof. exact (@lem305706 A P x). Qed.
Lemma lem305709 {A : Type'} (P : A -> Prop) (x : A) : (term37 A P x) = (term719 A P x).
Proof. exact (MK_COMB (@lem305700) (@lem305708 A P x)). Qed.
Lemma lem305710 {A : Type'} (P : A -> Prop) : (term39 A P) = (term741 A P).
Proof. exact (fun_ext (fun x : A => @lem305709 A P x)). Qed.
Lemma lem305711 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305712 {A : Type'} (P : A -> Prop) : (term32 A P) = (term742 A P).
Proof. exact (MK_COMB (@lem305711 A) (@lem305710 A P)). Qed.
Lemma lem305713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305714 {A : Type'} (P : A -> Prop) : (term76 A P) = (term743 A P).
Proof. exact (MK_COMB (@lem305713) (@lem305712 A P)). Qed.
Lemma lem305715 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term254 A lt2 P y) = (term797 A lt2 P y).
Proof. exact (MK_COMB (@lem305714 A P) (@lem305699 A lt2 P y)). Qed.
Lemma lem305716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305722 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305721 A Prop f x). Qed.
Lemma lem305724 {A : Type'} (P : A -> Prop) (y : A) : (P y) = (@I (A -> Prop) P y).
Proof. exact (@lem305722 A P y). Qed.
Lemma lem305725 {A : Type'} (P : A -> Prop) (y : A) : (term37 A P y) = (term719 A P y).
Proof. exact (MK_COMB (@lem305716) (@lem305724 A P y)). Qed.
Lemma lem305726 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305733 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305734 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem305733 A (A -> Prop) f x). Qed.
Lemma lem305735 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem305734 A lt2 y). Qed.
Lemma lem305736 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem305737 {A : Type'} (lt2 : type1402 A) (y : A) (x' : A) : (lt2 y x') = (@I (A -> A -> Prop) lt2 y x').
Proof. exact (MK_COMB (@lem305735 A lt2 y) (@lem305736 A x')). Qed.
Lemma lem305739 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305740 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305739 A Prop f x). Qed.
Lemma lem305741 {A : Type'} (lt2 : type1402 A) (y : A) (x' : A) : (@I (A -> A -> Prop) lt2 y x') = (term798 A lt2 y x').
Proof. exact (@lem305740 A (@I (A -> A -> Prop) lt2 y) x'). Qed.
Lemma lem305743 {A : Type'} (lt2 : type1402 A) (y : A) (x' : A) : (lt2 y x') = (term798 A lt2 y x').
Proof. exact (TRANS (@lem305737 A lt2 y x') (@lem305741 A lt2 y x')). Qed.
Lemma lem305744 {A : Type'} (lt2 : type1402 A) (y : A) (x' : A) : (term799 A lt2 y x') = (term800 A lt2 y x').
Proof. exact (MK_COMB (@lem305726) (@lem305743 A lt2 y x')). Qed.
Lemma lem305745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305746 {A : Type'} (lt2 : type1402 A) (y : A) (x' : A) : (term801 A lt2 y x') = (term802 A lt2 y x').
Proof. exact (MK_COMB (@lem305745) (@lem305744 A lt2 y x')). Qed.
Lemma lem305747 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (y : A) : (term45 A lt2 x' P y) = (term803 A lt2 x' P y).
Proof. exact (MK_COMB (@lem305746 A lt2 y x') (@lem305725 A P y)). Qed.
Lemma lem305748 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term55 A lt2 x' P) = (term804 A lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem305747 A lt2 x' P y)). Qed.
Lemma lem305749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305750 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term56 A lt2 x' P) = (term805 A lt2 x' P).
Proof. exact (MK_COMB (@lem305749 A) (@lem305748 A lt2 x' P)). Qed.
Lemma lem305755 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305756 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305755 A Prop f x). Qed.
Lemma lem305758 {A : Type'} (P : A -> Prop) (x' : A) : (P x') = (@I (A -> Prop) P x').
Proof. exact (@lem305756 A P x'). Qed.
Lemma lem305759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305760 {A : Type'} (P : A -> Prop) (x' : A) : (term20 A P x') = (term793 A P x').
Proof. exact (MK_COMB (@lem305759) (@lem305758 A P x')). Qed.
Lemma lem305761 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term61 A lt2 x' P) = (term806 A lt2 x' P).
Proof. exact (MK_COMB (@lem305760 A P x') (@lem305750 A lt2 x' P)). Qed.
Lemma lem305766 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305767 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305766 A Prop f x). Qed.
Lemma lem305769 {A : Type'} (P : A -> Prop) (x' : A) : (P x') = (@I (A -> Prop) P x').
Proof. exact (@lem305767 A P x'). Qed.
Lemma lem305770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305771 {A : Type'} (P : A -> Prop) (x' : A) : (term199 A P x') = (term807 A P x').
Proof. exact (MK_COMB (@lem305770) (@lem305769 A P x')). Qed.
Lemma lem305772 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term201 A lt2 x' P) = (term808 A lt2 x' P).
Proof. exact (MK_COMB (@lem305771 A P x') (@lem305761 A lt2 x' P)). Qed.
Lemma lem305773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305774 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term270 A lt2 x' P) = (term809 A lt2 x' P).
Proof. exact (MK_COMB (@lem305773) (@lem305772 A lt2 x' P)). Qed.
Lemma lem305775 {A : Type'} (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term288 A x' lt2 P y) = (term810 A x' lt2 P y).
Proof. exact (MK_COMB (@lem305774 A lt2 x' P) (@lem305715 A lt2 P y)). Qed.
Lemma lem305776 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305782 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305781 A Prop f x). Qed.
Lemma lem305784 {A : Type'} (P : A -> Prop) (y : A) : (P y) = (@I (A -> Prop) P y).
Proof. exact (@lem305782 A P y). Qed.
Lemma lem305785 {A : Type'} (P : A -> Prop) (y : A) : (term37 A P y) = (term719 A P y).
Proof. exact (MK_COMB (@lem305776) (@lem305784 A P y)). Qed.
Lemma lem305786 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305794 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem305793 (A -> Prop) A f x). Qed.
Lemma lem305796 {A : Type'} (x : type684 A) (P : A -> Prop) : (x P) = (@I ((A -> Prop) -> A) x P).
Proof. exact (@lem305794 A x P). Qed.
Lemma lem305797 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem305798 {A : Type'} (lt2 : type1402 A) (y : A) (x : type684 A) (P : A -> Prop) : (term720 A lt2 y x P) = (term721 A lt2 y x P).
Proof. exact (MK_COMB (@lem305797 A lt2 y) (@lem305796 A x P)). Qed.
Lemma lem305800 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305801 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem305800 A (A -> Prop) f x). Qed.
Lemma lem305802 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem305801 A lt2 y). Qed.
Lemma lem305803 {A : Type'} (x : type684 A) (P : A -> Prop) : (@I ((A -> Prop) -> A) x P) = (@I ((A -> Prop) -> A) x P).
Proof. exact (eq_refl (@I ((A -> Prop) -> A) x P)). Qed.
Lemma lem305804 {A : Type'} (lt2 : type1402 A) (y : A) (x : type684 A) (P : A -> Prop) : (term721 A lt2 y x P) = (term722 A lt2 y x P).
Proof. exact (MK_COMB (@lem305802 A lt2 y) (@lem305803 A x P)). Qed.
Lemma lem305806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305807 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305806 A Prop f x). Qed.
Lemma lem305808 {A : Type'} (lt2 : type1402 A) (y : A) (x : type684 A) (P : A -> Prop) : (term722 A lt2 y x P) = (term723 A lt2 y x P).
Proof. exact (@lem305807 A (@I (A -> A -> Prop) lt2 y) (@I ((A -> Prop) -> A) x P)). Qed.
Lemma lem305809 {A : Type'} (lt2 : type1402 A) (y : A) (x : type684 A) (P : A -> Prop) : (term721 A lt2 y x P) = (term723 A lt2 y x P).
Proof. exact (TRANS (@lem305804 A lt2 y x P) (@lem305808 A lt2 y x P)). Qed.
Lemma lem305810 {A : Type'} (lt2 : type1402 A) (y : A) (x : type684 A) (P : A -> Prop) : (term720 A lt2 y x P) = (term723 A lt2 y x P).
Proof. exact (TRANS (@lem305798 A lt2 y x P) (@lem305809 A lt2 y x P)). Qed.
Lemma lem305811 {A : Type'} (lt2 : type1402 A) (y : A) (x : type684 A) (P : A -> Prop) : (term724 A lt2 y x P) = (term725 A lt2 y x P).
Proof. exact (MK_COMB (@lem305786) (@lem305810 A lt2 y x P)). Qed.
Lemma lem305812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305813 {A : Type'} (lt2 : type1402 A) (y : A) (x : type684 A) (P : A -> Prop) : (term726 A lt2 y x P) = (term727 A lt2 y x P).
Proof. exact (MK_COMB (@lem305812) (@lem305811 A lt2 y x P)). Qed.
Lemma lem305814 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) (y : A) : (term728 A lt2 x P y) = (term729 A lt2 x P y).
Proof. exact (MK_COMB (@lem305813 A lt2 y x P) (@lem305785 A P y)). Qed.
Lemma lem305815 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term730 A lt2 x P) = (term731 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem305814 A lt2 x P y)). Qed.
Lemma lem305816 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305817 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term732 A lt2 x P) = (term733 A lt2 x P).
Proof. exact (MK_COMB (@lem305816 A) (@lem305815 A lt2 x P)). Qed.
Lemma lem305818 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem305823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305824 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem305823 (A -> Prop) A f x). Qed.
Lemma lem305826 {A : Type'} (x : type684 A) (P : A -> Prop) : (x P) = (@I ((A -> Prop) -> A) x P).
Proof. exact (@lem305824 A x P). Qed.
Lemma lem305827 {A : Type'} (x : type684 A) (P : A -> Prop) : (term734 A x P) = (term735 A x P).
Proof. exact (MK_COMB (@lem305818 A P) (@lem305826 A x P)). Qed.
Lemma lem305829 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305830 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305829 A Prop f x). Qed.
Lemma lem305831 {A : Type'} (x : type684 A) (P : A -> Prop) : (term735 A x P) = (term736 A x P).
Proof. exact (@lem305830 A P (@I ((A -> Prop) -> A) x P)). Qed.
Lemma lem305832 {A : Type'} (x : type684 A) (P : A -> Prop) : (term734 A x P) = (term736 A x P).
Proof. exact (TRANS (@lem305827 A x P) (@lem305831 A x P)). Qed.
Lemma lem305833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305834 {A : Type'} (x : type684 A) (P : A -> Prop) : (term737 A x P) = (term738 A x P).
Proof. exact (MK_COMB (@lem305833) (@lem305832 A x P)). Qed.
Lemma lem305835 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term739 A lt2 x P) = (term740 A lt2 x P).
Proof. exact (MK_COMB (@lem305834 A x P) (@lem305817 A lt2 x P)). Qed.
Lemma lem305836 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem305841 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem305842 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem305841 A Prop f x). Qed.
Lemma lem305844 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (@I (A -> Prop) P x).
Proof. exact (@lem305842 A P x). Qed.
Lemma lem305845 {A : Type'} (P : A -> Prop) (x : A) : (term37 A P x) = (term719 A P x).
Proof. exact (MK_COMB (@lem305836) (@lem305844 A P x)). Qed.
Lemma lem305846 {A : Type'} (P : A -> Prop) : (term39 A P) = (term741 A P).
Proof. exact (fun_ext (fun x : A => @lem305845 A P x)). Qed.
Lemma lem305847 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305848 {A : Type'} (P : A -> Prop) : (term32 A P) = (term742 A P).
Proof. exact (MK_COMB (@lem305847 A) (@lem305846 A P)). Qed.
Lemma lem305849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305850 {A : Type'} (P : A -> Prop) : (term76 A P) = (term743 A P).
Proof. exact (MK_COMB (@lem305849) (@lem305848 A P)). Qed.
Lemma lem305851 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term184 A lt2 x P) = (term744 A lt2 x P).
Proof. exact (MK_COMB (@lem305850 A P) (@lem305835 A lt2 x P)). Qed.
Lemma lem305852 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term186 A lt2 x) = (term745 A lt2 x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem305851 A lt2 x P)). Qed.
Lemma lem305853 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem305854 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term188 A lt2 x) = (term746 A lt2 x).
Proof. exact (MK_COMB (@lem305853 A) (@lem305852 A lt2 x)). Qed.
Lemma lem305855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem305856 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term308 A lt2 x) = (term811 A lt2 x).
Proof. exact (MK_COMB (@lem305855) (@lem305854 A lt2 x)). Qed.
Lemma lem305857 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term348 A x x' lt2 P y) = (term812 A x x' lt2 P y).
Proof. exact (MK_COMB (@lem305856 A lt2 x) (@lem305775 A x' lt2 P y)). Qed.
Lemma lem305858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem305859 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term661 A x x' lt2 P y) = (term813 A x x' lt2 P y).
Proof. exact (MK_COMB (@lem305858) (@lem305857 A x x' lt2 P y)). Qed.
Lemma lem305860 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) : (term703 A x x' P y x'' y' lt2 x''') = (term814 A x x' P y x'' y' lt2 x''').
Proof. exact (MK_COMB (@lem305859 A x x' lt2 P y) (@lem305641 A x' P y x'' y' lt2 x''')). Qed.
Lemma lem305861 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term703 A x x' P y x'' y' lt2 x''') : term814 A x x' P y x'' y' lt2 x'''.
Proof. exact (EQ_MP (@lem305860 A x x' P y x'' y' lt2 x''') (@lem305390 A x x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem305862 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term812 A x x' lt2 P y.
Proof. exact (h1). Qed.
Lemma lem305863 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term796 A x' P y x'' y' lt2 x'''.
Proof. exact (h1). Qed.
Lemma lem305864 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term810 A x' lt2 P y.
Proof. exact (proj2 (@lem305862 A x x' lt2 P y h1)). Qed.
Lemma lem305865 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term746 A lt2 x.
Proof. exact (proj1 (@lem305862 A x x' lt2 P y h1)). Qed.
Lemma lem305866 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term797 A lt2 P y.
Proof. exact (proj2 (@lem305864 A x x' lt2 P y h1)). Qed.
Lemma lem305867 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term808 A lt2 x' P.
Proof. exact (proj1 (@lem305864 A x x' lt2 P y h1)). Qed.
Lemma lem305868 {A : Type'} (P : A -> Prop) (h1 : term742 A P) : term742 A P.
Proof. exact (h1). Qed.
Lemma lem305869 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term792 A lt2 P y.
Proof. exact (h1). Qed.
Lemma lem305871 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term806 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem305875 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term806 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem305876 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term805 A lt2 x' P.
Proof. exact (proj2 (@lem305875 A lt2 x' P h1)). Qed.
Lemma lem305878 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term775 A x'' y' lt2 x'''.
Proof. exact (proj2 (@lem305863 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem305879 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term794 A x' lt2 P y.
Proof. exact (proj1 (@lem305863 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem305880 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term746 A lt2 x'''.
Proof. exact (proj2 (@lem305878 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem305882 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term792 A lt2 P y.
Proof. exact (proj2 (@lem305879 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem305993 {A : Type'} (P : A -> Prop) (x : A) : (term719 A P x) = (term719 A P x).
Proof. exact (eq_refl (term719 A P x)). Qed.
Lemma lem305994 {A : Type'} (P : A -> Prop) : (term741 A P) = (term741 A P).
Proof. exact (fun_ext (fun x : A => @lem305993 A P x)). Qed.
Lemma lem305995 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem305997 {A : Type'} (P : A -> Prop) : (term742 A P) = (term742 A P).
Proof. exact (MK_COMB (@lem305995 A) (@lem305994 A P)). Qed.
Lemma lem305998 {A : Type'} (P : A -> Prop) (h1 : term742 A P) : term742 A P.
Proof. exact (EQ_MP (@lem305997 A P) (@lem305868 A P h1)). Qed.
Lemma lem306002 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem306112 {A : Type'} (P : A -> Prop) (x : A) : (term719 A P x) = (term719 A P x).
Proof. exact (eq_refl (term719 A P x)). Qed.
Lemma lem306113 {A : Type'} (P : A -> Prop) : (term741 A P) = (term741 A P).
Proof. exact (fun_ext (fun x : A => @lem306112 A P x)). Qed.
Lemma lem306114 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306116 {A : Type'} (P : A -> Prop) : (term742 A P) = (term742 A P).
Proof. exact (MK_COMB (@lem306114 A) (@lem306113 A P)). Qed.
Lemma lem306117 {A : Type'} (P : A -> Prop) (h1 : term742 A P) : term742 A P.
Proof. exact (EQ_MP (@lem306116 A P) (@lem305868 A P h1)). Qed.
Lemma lem306136 {A : Type'} (P : Prop) (Q : A -> Prop) : (term815 A P Q) = (term816 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem306137 {A : Type'} (P : Prop) (Q : A -> Prop) : (term815 A P Q) = (term816 A P Q).
Proof. exact (@lem306136 A P Q). Qed.
Lemma lem306138 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term817 A lt2 x P) = (term818 A lt2 x P).
Proof. exact (@lem306137 A (term736 A x P) (term731 A lt2 x P)). Qed.
Lemma lem306139 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) (y : A) : (term819 A lt2 x P y) = (term729 A lt2 x P y).
Proof. exact (eq_refl (term819 A lt2 x P y)). Qed.
Lemma lem306140 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term820 A lt2 x P) = (term731 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem306139 A lt2 x P y)). Qed.
Lemma lem306141 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306142 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term821 A lt2 x P) = (term733 A lt2 x P).
Proof. exact (MK_COMB (@lem306141 A) (@lem306140 A lt2 x P)). Qed.
Lemma lem306143 {A : Type'} (x : type684 A) (P : A -> Prop) : (term738 A x P) = (term738 A x P).
Proof. exact (eq_refl (term738 A x P)). Qed.
Lemma lem306144 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term817 A lt2 x P) = (term740 A lt2 x P).
Proof. exact (MK_COMB (@lem306143 A x P) (@lem306142 A lt2 x P)). Qed.
Lemma lem306145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306146 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term822 A lt2 x P) = (term823 A lt2 x P).
Proof. exact (MK_COMB (@lem306145) (@lem306144 A lt2 x P)). Qed.
Lemma lem306147 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) (y : A) : (term819 A lt2 x P y) = (term729 A lt2 x P y).
Proof. exact (eq_refl (term819 A lt2 x P y)). Qed.
Lemma lem306148 {A : Type'} (x : type684 A) (P : A -> Prop) : (term738 A x P) = (term738 A x P).
Proof. exact (eq_refl (term738 A x P)). Qed.
Lemma lem306149 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) (y : A) : (term824 A lt2 x P y) = (term825 A lt2 x P y).
Proof. exact (MK_COMB (@lem306148 A x P) (@lem306147 A lt2 x P y)). Qed.
Lemma lem306150 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term826 A lt2 x P) = (term827 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem306149 A lt2 x P y)). Qed.
Lemma lem306151 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306152 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term818 A lt2 x P) = (term828 A lt2 x P).
Proof. exact (MK_COMB (@lem306151 A) (@lem306150 A lt2 x P)). Qed.
Lemma lem306153 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : ((term817 A lt2 x P) = (term818 A lt2 x P)) = ((term740 A lt2 x P) = (term828 A lt2 x P)).
Proof. exact (MK_COMB (@lem306146 A lt2 x P) (@lem306152 A lt2 x P)). Qed.
Lemma lem306154 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term740 A lt2 x P) = (term828 A lt2 x P).
Proof. exact (EQ_MP (@lem306153 A lt2 x P) (@lem306138 A lt2 x P)). Qed.
Lemma lem306155 {A : Type'} (P : A -> Prop) : (term743 A P) = (term743 A P).
Proof. exact (eq_refl (term743 A P)). Qed.
Lemma lem306156 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term744 A lt2 x P) = (term829 A lt2 x P).
Proof. exact (MK_COMB (@lem306155 A P) (@lem306154 A lt2 x P)). Qed.
Lemma lem306158 {A : Type'} (P : A -> Prop) (Q : Prop) : (term830 A P Q) = (term831 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem306159 {A : Type'} (P : A -> Prop) (Q : Prop) : (term830 A P Q) = (term831 A P Q).
Proof. exact (@lem306158 A P Q). Qed.
Lemma lem306160 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term832 A lt2 x P) = (term833 A lt2 x P).
Proof. exact (@lem306159 A (term741 A P) (term828 A lt2 x P)). Qed.
Lemma lem306161 {A : Type'} (P : A -> Prop) (x : A) : (term834 A P x) = (term719 A P x).
Proof. exact (eq_refl (term834 A P x)). Qed.
Lemma lem306162 {A : Type'} (P : A -> Prop) : (term835 A P) = (term741 A P).
Proof. exact (fun_ext (fun x : A => @lem306161 A P x)). Qed.
Lemma lem306163 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306164 {A : Type'} (P : A -> Prop) : (term836 A P) = (term742 A P).
Proof. exact (MK_COMB (@lem306163 A) (@lem306162 A P)). Qed.
Lemma lem306165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem306166 {A : Type'} (P : A -> Prop) : (term837 A P) = (term743 A P).
Proof. exact (MK_COMB (@lem306165) (@lem306164 A P)). Qed.
Lemma lem306167 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term828 A lt2 x P) = (term828 A lt2 x P).
Proof. exact (eq_refl (term828 A lt2 x P)). Qed.
Lemma lem306168 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term832 A lt2 x P) = (term829 A lt2 x P).
Proof. exact (MK_COMB (@lem306166 A P) (@lem306167 A lt2 x P)). Qed.
Lemma lem306169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306170 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term838 A lt2 x P) = (term839 A lt2 x P).
Proof. exact (MK_COMB (@lem306169) (@lem306168 A lt2 x P)). Qed.
Lemma lem306171 {A : Type'} (P : A -> Prop) (x : A) : (term834 A P x) = (term719 A P x).
Proof. exact (eq_refl (term834 A P x)). Qed.
Lemma lem306172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem306173 {A : Type'} (P : A -> Prop) (x : A) : (term840 A P x) = (term762 A P x).
Proof. exact (MK_COMB (@lem306172) (@lem306171 A P x)). Qed.
Lemma lem306174 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term828 A lt2 x P) = (term828 A lt2 x P).
Proof. exact (eq_refl (term828 A lt2 x P)). Qed.
Lemma lem306175 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term841 A x lt2 x' P) = (term842 A x lt2 x' P).
Proof. exact (MK_COMB (@lem306173 A P x) (@lem306174 A lt2 x' P)). Qed.
Lemma lem306176 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term843 A lt2 x P) = (term844 A lt2 x P).
Proof. exact (fun_ext (fun x' : A => @lem306175 A x' lt2 x P)). Qed.
Lemma lem306177 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306178 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term833 A lt2 x P) = (term845 A lt2 x P).
Proof. exact (MK_COMB (@lem306177 A) (@lem306176 A lt2 x P)). Qed.
Lemma lem306179 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : ((term832 A lt2 x P) = (term833 A lt2 x P)) = ((term829 A lt2 x P) = (term845 A lt2 x P)).
Proof. exact (MK_COMB (@lem306170 A lt2 x P) (@lem306178 A lt2 x P)). Qed.
Lemma lem306180 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term829 A lt2 x P) = (term845 A lt2 x P).
Proof. exact (EQ_MP (@lem306179 A lt2 x P) (@lem306160 A lt2 x P)). Qed.
Lemma lem306182 {A : Type'} (P : Prop) (Q : A -> Prop) : (term846 A P Q) = (term847 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem306183 {A : Type'} (P : Prop) (Q : A -> Prop) : (term846 A P Q) = (term847 A P Q).
Proof. exact (@lem306182 A P Q). Qed.
Lemma lem306184 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term848 A x lt2 x' P) = (term849 A x lt2 x' P).
Proof. exact (@lem306183 A (term719 A P x) (term827 A lt2 x' P)). Qed.
Lemma lem306185 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) (y : A) : (term850 A lt2 x P y) = (term825 A lt2 x P y).
Proof. exact (eq_refl (term850 A lt2 x P y)). Qed.
Lemma lem306186 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term851 A lt2 x P) = (term827 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem306185 A lt2 x P y)). Qed.
Lemma lem306187 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306188 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term852 A lt2 x P) = (term828 A lt2 x P).
Proof. exact (MK_COMB (@lem306187 A) (@lem306186 A lt2 x P)). Qed.
Lemma lem306189 {A : Type'} (P : A -> Prop) (x : A) : (term762 A P x) = (term762 A P x).
Proof. exact (eq_refl (term762 A P x)). Qed.
Lemma lem306190 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term848 A x lt2 x' P) = (term842 A x lt2 x' P).
Proof. exact (MK_COMB (@lem306189 A P x) (@lem306188 A lt2 x' P)). Qed.
Lemma lem306191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306192 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term853 A x lt2 x' P) = (term854 A x lt2 x' P).
Proof. exact (MK_COMB (@lem306191) (@lem306190 A x lt2 x' P)). Qed.
Lemma lem306193 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) (y : A) : (term850 A lt2 x P y) = (term825 A lt2 x P y).
Proof. exact (eq_refl (term850 A lt2 x P y)). Qed.
Lemma lem306194 {A : Type'} (P : A -> Prop) (x : A) : (term762 A P x) = (term762 A P x).
Proof. exact (eq_refl (term762 A P x)). Qed.
Lemma lem306195 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) (y : A) : (term855 A x lt2 x' P y) = (term856 A x lt2 x' P y).
Proof. exact (MK_COMB (@lem306194 A P x) (@lem306193 A lt2 x' P y)). Qed.
Lemma lem306196 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term857 A x lt2 x' P) = (term858 A x lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem306195 A x lt2 x' P y)). Qed.
Lemma lem306197 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306198 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term849 A x lt2 x' P) = (term859 A x lt2 x' P).
Proof. exact (MK_COMB (@lem306197 A) (@lem306196 A x lt2 x' P)). Qed.
Lemma lem306199 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : ((term848 A x lt2 x' P) = (term849 A x lt2 x' P)) = ((term842 A x lt2 x' P) = (term859 A x lt2 x' P)).
Proof. exact (MK_COMB (@lem306192 A x lt2 x' P) (@lem306198 A x lt2 x' P)). Qed.
Lemma lem306200 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term842 A x lt2 x' P) = (term859 A x lt2 x' P).
Proof. exact (EQ_MP (@lem306199 A x lt2 x' P) (@lem306184 A x lt2 x' P)). Qed.
Lemma lem306201 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term844 A lt2 x P) = (term860 A lt2 x P).
Proof. exact (fun_ext (fun x' : A => @lem306200 A x' lt2 x P)). Qed.
Lemma lem306202 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306203 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term845 A lt2 x P) = (term861 A lt2 x P).
Proof. exact (MK_COMB (@lem306202 A) (@lem306201 A lt2 x P)). Qed.
Lemma lem306204 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term829 A lt2 x P) = (term861 A lt2 x P).
Proof. exact (TRANS (@lem306180 A lt2 x P) (@lem306203 A lt2 x P)). Qed.
Lemma lem306205 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term744 A lt2 x P) = (term861 A lt2 x P).
Proof. exact (TRANS (@lem306156 A lt2 x P) (@lem306204 A lt2 x P)). Qed.
Lemma lem306206 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term745 A lt2 x) = (term862 A lt2 x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem306205 A lt2 x P)). Qed.
Lemma lem306207 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem306208 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term746 A lt2 x) = (term863 A lt2 x).
Proof. exact (MK_COMB (@lem306207 A) (@lem306206 A lt2 x)). Qed.
Lemma lem306231 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) (y : A) : (term856 A x lt2 x' P y) = (term864 A x lt2 x' P y).
Proof. exact (@lem19490 (term736 A x' P) (term719 A P x) (term729 A lt2 x' P y)). Qed.
Lemma lem306232 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term858 A x lt2 x' P) = (term865 A x lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem306231 A x lt2 x' P y)). Qed.
Lemma lem306233 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306234 {A : Type'} (x : A) (lt2 : type1402 A) (x' : type684 A) (P : A -> Prop) : (term859 A x lt2 x' P) = (term866 A x lt2 x' P).
Proof. exact (MK_COMB (@lem306233 A) (@lem306232 A x lt2 x' P)). Qed.
Lemma lem306235 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term860 A lt2 x P) = (term867 A lt2 x P).
Proof. exact (fun_ext (fun x' : A => @lem306234 A x' lt2 x P)). Qed.
Lemma lem306236 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306237 {A : Type'} (lt2 : type1402 A) (x : type684 A) (P : A -> Prop) : (term861 A lt2 x P) = (term868 A lt2 x P).
Proof. exact (MK_COMB (@lem306236 A) (@lem306235 A lt2 x P)). Qed.
Lemma lem306238 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term862 A lt2 x) = (term869 A lt2 x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem306237 A lt2 x P)). Qed.
Lemma lem306239 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem306240 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term863 A lt2 x) = (term870 A lt2 x).
Proof. exact (MK_COMB (@lem306239 A) (@lem306238 A lt2 x)). Qed.
Lemma lem306241 {A : Type'} (lt2 : type1402 A) (x : type684 A) : (term746 A lt2 x) = (term870 A lt2 x).
Proof. exact (TRANS (@lem306208 A lt2 x) (@lem306240 A lt2 x)). Qed.
Lemma lem306242 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term870 A lt2 x.
Proof. exact (EQ_MP (@lem306241 A lt2 x) (@lem305865 A x x' lt2 P y h1)). Qed.
Lemma lem306260 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term790 A lt2 P y x) = (term871 A lt2 P y x).
Proof. exact (@lem19490 (term785 A lt2 y x) (term719 A P x) (term778 A P y x)). Qed.
Lemma lem306261 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term791 A lt2 P y) = (term872 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem306260 A lt2 P y x)). Qed.
Lemma lem306262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306264 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term792 A lt2 P y) = (term873 A lt2 P y).
Proof. exact (MK_COMB (@lem306262 A) (@lem306261 A lt2 P y)). Qed.
Lemma lem306265 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term873 A lt2 P y.
Proof. exact (EQ_MP (@lem306264 A lt2 P y) (@lem305869 A lt2 P y h1)). Qed.
Lemma lem306269 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem306395 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term790 A lt2 P y x) = (term871 A lt2 P y x).
Proof. exact (@lem19490 (term785 A lt2 y x) (term719 A P x) (term778 A P y x)). Qed.
Lemma lem306396 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term791 A lt2 P y) = (term872 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem306395 A lt2 P y x)). Qed.
Lemma lem306397 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306399 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term792 A lt2 P y) = (term873 A lt2 P y).
Proof. exact (MK_COMB (@lem306397 A) (@lem306396 A lt2 P y)). Qed.
Lemma lem306400 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term873 A lt2 P y.
Proof. exact (EQ_MP (@lem306399 A lt2 P y) (@lem305869 A lt2 P y h1)). Qed.
Lemma lem306412 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (y : A) : (term803 A lt2 x' P y) = (term803 A lt2 x' P y).
Proof. exact (eq_refl (term803 A lt2 x' P y)). Qed.
Lemma lem306413 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term804 A lt2 x' P) = (term804 A lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem306412 A lt2 x' P y)). Qed.
Lemma lem306414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306416 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term805 A lt2 x' P) = (term805 A lt2 x' P).
Proof. exact (MK_COMB (@lem306414 A) (@lem306413 A lt2 x' P)). Qed.
Lemma lem306417 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term805 A lt2 x' P.
Proof. exact (EQ_MP (@lem306416 A lt2 x' P) (@lem305876 A lt2 x' P h1)). Qed.
Lemma lem306479 {A : Type'} (P : Prop) (Q : A -> Prop) : (term815 A P Q) = (term816 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem306480 {A : Type'} (P : Prop) (Q : A -> Prop) : (term815 A P Q) = (term816 A P Q).
Proof. exact (@lem306479 A P Q). Qed.
Lemma lem306481 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term817 A lt2 x''' P) = (term818 A lt2 x''' P).
Proof. exact (@lem306480 A (term736 A x''' P) (term731 A lt2 x''' P)). Qed.
Lemma lem306482 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term819 A lt2 x''' P y) = (term729 A lt2 x''' P y).
Proof. exact (eq_refl (term819 A lt2 x''' P y)). Qed.
Lemma lem306483 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term820 A lt2 x''' P) = (term731 A lt2 x''' P).
Proof. exact (fun_ext (fun y : A => @lem306482 A lt2 x''' P y)). Qed.
Lemma lem306484 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306485 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term821 A lt2 x''' P) = (term733 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306484 A) (@lem306483 A lt2 x''' P)). Qed.
Lemma lem306486 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term738 A x''' P) = (term738 A x''' P).
Proof. exact (eq_refl (term738 A x''' P)). Qed.
Lemma lem306487 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term817 A lt2 x''' P) = (term740 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306486 A x''' P) (@lem306485 A lt2 x''' P)). Qed.
Lemma lem306488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306489 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term822 A lt2 x''' P) = (term823 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306488) (@lem306487 A lt2 x''' P)). Qed.
Lemma lem306490 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term819 A lt2 x''' P y) = (term729 A lt2 x''' P y).
Proof. exact (eq_refl (term819 A lt2 x''' P y)). Qed.
Lemma lem306491 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term738 A x''' P) = (term738 A x''' P).
Proof. exact (eq_refl (term738 A x''' P)). Qed.
Lemma lem306492 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term824 A lt2 x''' P y) = (term825 A lt2 x''' P y).
Proof. exact (MK_COMB (@lem306491 A x''' P) (@lem306490 A lt2 x''' P y)). Qed.
Lemma lem306493 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term826 A lt2 x''' P) = (term827 A lt2 x''' P).
Proof. exact (fun_ext (fun y : A => @lem306492 A lt2 x''' P y)). Qed.
Lemma lem306494 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306495 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term818 A lt2 x''' P) = (term828 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306494 A) (@lem306493 A lt2 x''' P)). Qed.
Lemma lem306496 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : ((term817 A lt2 x''' P) = (term818 A lt2 x''' P)) = ((term740 A lt2 x''' P) = (term828 A lt2 x''' P)).
Proof. exact (MK_COMB (@lem306489 A lt2 x''' P) (@lem306495 A lt2 x''' P)). Qed.
Lemma lem306497 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term740 A lt2 x''' P) = (term828 A lt2 x''' P).
Proof. exact (EQ_MP (@lem306496 A lt2 x''' P) (@lem306481 A lt2 x''' P)). Qed.
Lemma lem306498 {A : Type'} (P : A -> Prop) : (term743 A P) = (term743 A P).
Proof. exact (eq_refl (term743 A P)). Qed.
Lemma lem306499 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term744 A lt2 x''' P) = (term829 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306498 A P) (@lem306497 A lt2 x''' P)). Qed.
Lemma lem306501 {A : Type'} (P : A -> Prop) (Q : Prop) : (term830 A P Q) = (term831 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem306502 {A : Type'} (P : A -> Prop) (Q : Prop) : (term830 A P Q) = (term831 A P Q).
Proof. exact (@lem306501 A P Q). Qed.
Lemma lem306503 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term832 A lt2 x''' P) = (term833 A lt2 x''' P).
Proof. exact (@lem306502 A (term741 A P) (term828 A lt2 x''' P)). Qed.
Lemma lem306504 {A : Type'} (P : A -> Prop) (x : A) : (term834 A P x) = (term719 A P x).
Proof. exact (eq_refl (term834 A P x)). Qed.
Lemma lem306505 {A : Type'} (P : A -> Prop) : (term835 A P) = (term741 A P).
Proof. exact (fun_ext (fun x : A => @lem306504 A P x)). Qed.
Lemma lem306506 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306507 {A : Type'} (P : A -> Prop) : (term836 A P) = (term742 A P).
Proof. exact (MK_COMB (@lem306506 A) (@lem306505 A P)). Qed.
Lemma lem306508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem306509 {A : Type'} (P : A -> Prop) : (term837 A P) = (term743 A P).
Proof. exact (MK_COMB (@lem306508) (@lem306507 A P)). Qed.
Lemma lem306510 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term828 A lt2 x''' P) = (term828 A lt2 x''' P).
Proof. exact (eq_refl (term828 A lt2 x''' P)). Qed.
Lemma lem306511 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term832 A lt2 x''' P) = (term829 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306509 A P) (@lem306510 A lt2 x''' P)). Qed.
Lemma lem306512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306513 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term838 A lt2 x''' P) = (term839 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306512) (@lem306511 A lt2 x''' P)). Qed.
Lemma lem306514 {A : Type'} (P : A -> Prop) (x : A) : (term834 A P x) = (term719 A P x).
Proof. exact (eq_refl (term834 A P x)). Qed.
Lemma lem306515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem306516 {A : Type'} (P : A -> Prop) (x : A) : (term840 A P x) = (term762 A P x).
Proof. exact (MK_COMB (@lem306515) (@lem306514 A P x)). Qed.
Lemma lem306517 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term828 A lt2 x''' P) = (term828 A lt2 x''' P).
Proof. exact (eq_refl (term828 A lt2 x''' P)). Qed.
Lemma lem306518 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term841 A x lt2 x''' P) = (term842 A x lt2 x''' P).
Proof. exact (MK_COMB (@lem306516 A P x) (@lem306517 A lt2 x''' P)). Qed.
Lemma lem306519 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term843 A lt2 x''' P) = (term844 A lt2 x''' P).
Proof. exact (fun_ext (fun x : A => @lem306518 A x lt2 x''' P)). Qed.
Lemma lem306520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306521 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term833 A lt2 x''' P) = (term845 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306520 A) (@lem306519 A lt2 x''' P)). Qed.
Lemma lem306522 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : ((term832 A lt2 x''' P) = (term833 A lt2 x''' P)) = ((term829 A lt2 x''' P) = (term845 A lt2 x''' P)).
Proof. exact (MK_COMB (@lem306513 A lt2 x''' P) (@lem306521 A lt2 x''' P)). Qed.
Lemma lem306523 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term829 A lt2 x''' P) = (term845 A lt2 x''' P).
Proof. exact (EQ_MP (@lem306522 A lt2 x''' P) (@lem306503 A lt2 x''' P)). Qed.
Lemma lem306525 {A : Type'} (P : Prop) (Q : A -> Prop) : (term846 A P Q) = (term847 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem306526 {A : Type'} (P : Prop) (Q : A -> Prop) : (term846 A P Q) = (term847 A P Q).
Proof. exact (@lem306525 A P Q). Qed.
Lemma lem306527 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term848 A x lt2 x''' P) = (term849 A x lt2 x''' P).
Proof. exact (@lem306526 A (term719 A P x) (term827 A lt2 x''' P)). Qed.
Lemma lem306528 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term850 A lt2 x''' P y) = (term825 A lt2 x''' P y).
Proof. exact (eq_refl (term850 A lt2 x''' P y)). Qed.
Lemma lem306529 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term851 A lt2 x''' P) = (term827 A lt2 x''' P).
Proof. exact (fun_ext (fun y : A => @lem306528 A lt2 x''' P y)). Qed.
Lemma lem306530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306531 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term852 A lt2 x''' P) = (term828 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306530 A) (@lem306529 A lt2 x''' P)). Qed.
Lemma lem306532 {A : Type'} (P : A -> Prop) (x : A) : (term762 A P x) = (term762 A P x).
Proof. exact (eq_refl (term762 A P x)). Qed.
Lemma lem306533 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term848 A x lt2 x''' P) = (term842 A x lt2 x''' P).
Proof. exact (MK_COMB (@lem306532 A P x) (@lem306531 A lt2 x''' P)). Qed.
Lemma lem306534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306535 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term853 A x lt2 x''' P) = (term854 A x lt2 x''' P).
Proof. exact (MK_COMB (@lem306534) (@lem306533 A x lt2 x''' P)). Qed.
Lemma lem306536 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term850 A lt2 x''' P y) = (term825 A lt2 x''' P y).
Proof. exact (eq_refl (term850 A lt2 x''' P y)). Qed.
Lemma lem306537 {A : Type'} (P : A -> Prop) (x : A) : (term762 A P x) = (term762 A P x).
Proof. exact (eq_refl (term762 A P x)). Qed.
Lemma lem306538 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term855 A x lt2 x''' P y) = (term856 A x lt2 x''' P y).
Proof. exact (MK_COMB (@lem306537 A P x) (@lem306536 A lt2 x''' P y)). Qed.
Lemma lem306539 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term857 A x lt2 x''' P) = (term858 A x lt2 x''' P).
Proof. exact (fun_ext (fun y : A => @lem306538 A x lt2 x''' P y)). Qed.
Lemma lem306540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306541 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term849 A x lt2 x''' P) = (term859 A x lt2 x''' P).
Proof. exact (MK_COMB (@lem306540 A) (@lem306539 A x lt2 x''' P)). Qed.
Lemma lem306542 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : ((term848 A x lt2 x''' P) = (term849 A x lt2 x''' P)) = ((term842 A x lt2 x''' P) = (term859 A x lt2 x''' P)).
Proof. exact (MK_COMB (@lem306535 A x lt2 x''' P) (@lem306541 A x lt2 x''' P)). Qed.
Lemma lem306543 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term842 A x lt2 x''' P) = (term859 A x lt2 x''' P).
Proof. exact (EQ_MP (@lem306542 A x lt2 x''' P) (@lem306527 A x lt2 x''' P)). Qed.
Lemma lem306544 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term844 A lt2 x''' P) = (term860 A lt2 x''' P).
Proof. exact (fun_ext (fun x : A => @lem306543 A x lt2 x''' P)). Qed.
Lemma lem306545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306546 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term845 A lt2 x''' P) = (term861 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306545 A) (@lem306544 A lt2 x''' P)). Qed.
Lemma lem306547 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term829 A lt2 x''' P) = (term861 A lt2 x''' P).
Proof. exact (TRANS (@lem306523 A lt2 x''' P) (@lem306546 A lt2 x''' P)). Qed.
Lemma lem306548 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term744 A lt2 x''' P) = (term861 A lt2 x''' P).
Proof. exact (TRANS (@lem306499 A lt2 x''' P) (@lem306547 A lt2 x''' P)). Qed.
Lemma lem306549 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) : (term745 A lt2 x''') = (term862 A lt2 x''').
Proof. exact (fun_ext (fun P : A -> Prop => @lem306548 A lt2 x''' P)). Qed.
Lemma lem306550 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem306551 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) : (term746 A lt2 x''') = (term863 A lt2 x''').
Proof. exact (MK_COMB (@lem306550 A) (@lem306549 A lt2 x''')). Qed.
Lemma lem306574 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) (y : A) : (term856 A x lt2 x''' P y) = (term864 A x lt2 x''' P y).
Proof. exact (@lem19490 (term736 A x''' P) (term719 A P x) (term729 A lt2 x''' P y)). Qed.
Lemma lem306575 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term858 A x lt2 x''' P) = (term865 A x lt2 x''' P).
Proof. exact (fun_ext (fun y : A => @lem306574 A x lt2 x''' P y)). Qed.
Lemma lem306576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306577 {A : Type'} (x : A) (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term859 A x lt2 x''' P) = (term866 A x lt2 x''' P).
Proof. exact (MK_COMB (@lem306576 A) (@lem306575 A x lt2 x''' P)). Qed.
Lemma lem306578 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term860 A lt2 x''' P) = (term867 A lt2 x''' P).
Proof. exact (fun_ext (fun x : A => @lem306577 A x lt2 x''' P)). Qed.
Lemma lem306579 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306580 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (P : A -> Prop) : (term861 A lt2 x''' P) = (term868 A lt2 x''' P).
Proof. exact (MK_COMB (@lem306579 A) (@lem306578 A lt2 x''' P)). Qed.
Lemma lem306581 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) : (term862 A lt2 x''') = (term869 A lt2 x''').
Proof. exact (fun_ext (fun P : A -> Prop => @lem306580 A lt2 x''' P)). Qed.
Lemma lem306582 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem306583 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) : (term863 A lt2 x''') = (term870 A lt2 x''').
Proof. exact (MK_COMB (@lem306582 A) (@lem306581 A lt2 x''')). Qed.
Lemma lem306584 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) : (term746 A lt2 x''') = (term870 A lt2 x''').
Proof. exact (TRANS (@lem306551 A lt2 x''') (@lem306583 A lt2 x''')). Qed.
Lemma lem306585 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term870 A lt2 x'''.
Proof. exact (EQ_MP (@lem306584 A lt2 x''') (@lem305880 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306607 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term790 A lt2 P y x) = (term871 A lt2 P y x).
Proof. exact (@lem19490 (term785 A lt2 y x) (term719 A P x) (term778 A P y x)). Qed.
Lemma lem306608 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term791 A lt2 P y) = (term872 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem306607 A lt2 P y x)). Qed.
Lemma lem306609 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem306611 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term792 A lt2 P y) = (term873 A lt2 P y).
Proof. exact (MK_COMB (@lem306609 A) (@lem306608 A lt2 P y)). Qed.
Lemma lem306612 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term873 A lt2 P y.
Proof. exact (EQ_MP (@lem306611 A lt2 P y) (@lem305882 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306622 {A : Type'} (_6768 : A) (P : A -> Prop) (h1 : term742 A P) : term834 A P _6768.
Proof. exact (@lem305998 A P h1 _6768). Qed.
Lemma lem306623 {A : Type'} (P : A -> Prop) (_6768 : A) : (term834 A P _6768) = (term719 A P _6768).
Proof. exact (eq_refl (term834 A P _6768)). Qed.
Lemma lem306634 {A : Type'} (_6772 : A) (P : A -> Prop) (h1 : term742 A P) : term834 A P _6772.
Proof. exact (@lem306117 A P h1 _6772). Qed.
Lemma lem306635 {A : Type'} (P : A -> Prop) (_6772 : A) : (term834 A P _6772) = (term719 A P _6772).
Proof. exact (eq_refl (term834 A P _6772)). Qed.
Lemma lem306640 {A : Type'} (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term874 A lt2 x _6774.
Proof. exact (@lem306242 A x x' lt2 P y h1 _6774). Qed.
Lemma lem306641 {A : Type'} (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) : (term874 A lt2 x _6774) = (term868 A lt2 x _6774).
Proof. exact (eq_refl (term874 A lt2 x _6774)). Qed.
Lemma lem306642 {A : Type'} (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term868 A lt2 x _6774.
Proof. exact (EQ_MP (@lem306641 A lt2 x _6774) (@lem306640 A _6774 x x' lt2 P y h1)). Qed.
Lemma lem306643 {A : Type'} (_6774 : A -> Prop) (_6775 : A) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term875 A lt2 x _6774 _6775.
Proof. exact (@lem306642 A _6774 x x' lt2 P y h1 _6775). Qed.
Lemma lem306644 {A : Type'} (_6775 : A) (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) : (term875 A lt2 x _6774 _6775) = (term866 A _6775 lt2 x _6774).
Proof. exact (eq_refl (term875 A lt2 x _6774 _6775)). Qed.
Lemma lem306645 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term866 A _6775 lt2 x _6774.
Proof. exact (EQ_MP (@lem306644 A _6775 lt2 x _6774) (@lem306643 A _6774 _6775 x x' lt2 P y h1)). Qed.
Lemma lem306646 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (_6776 : A) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term876 A _6775 lt2 x _6774 _6776.
Proof. exact (@lem306645 A _6775 _6774 x x' lt2 P y h1 _6776). Qed.
Lemma lem306647 {A : Type'} (_6775 : A) (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) (_6776 : A) : (term876 A _6775 lt2 x _6774 _6776) = (term864 A _6775 lt2 x _6774 _6776).
Proof. exact (eq_refl (term876 A _6775 lt2 x _6774 _6776)). Qed.
Lemma lem306648 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (_6776 : A) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term864 A _6775 lt2 x _6774 _6776.
Proof. exact (EQ_MP (@lem306647 A _6775 lt2 x _6774 _6776) (@lem306646 A _6775 _6774 _6776 x x' lt2 P y h1)). Qed.
Lemma lem306649 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term877 A lt2 P y _6777.
Proof. exact (@lem306265 A lt2 P y h1 _6777). Qed.
Lemma lem306650 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (_6777 : A) : (term877 A lt2 P y _6777) = (term871 A lt2 P y _6777).
Proof. exact (eq_refl (term877 A lt2 P y _6777)). Qed.
Lemma lem306651 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term871 A lt2 P y _6777.
Proof. exact (EQ_MP (@lem306650 A lt2 P y _6777) (@lem306649 A _6777 lt2 P y h1)). Qed.
Lemma lem306661 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term877 A lt2 P y _6781.
Proof. exact (@lem306400 A lt2 P y h1 _6781). Qed.
Lemma lem306662 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (_6781 : A) : (term877 A lt2 P y _6781) = (term871 A lt2 P y _6781).
Proof. exact (eq_refl (term877 A lt2 P y _6781)). Qed.
Lemma lem306663 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term871 A lt2 P y _6781.
Proof. exact (EQ_MP (@lem306662 A lt2 P y _6781) (@lem306661 A _6781 lt2 P y h1)). Qed.
Lemma lem306664 {A : Type'} (_6782 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term878 A lt2 x' P _6782.
Proof. exact (@lem306417 A lt2 x' P h1 _6782). Qed.
Lemma lem306665 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6782 : A) : (term878 A lt2 x' P _6782) = (term803 A lt2 x' P _6782).
Proof. exact (eq_refl (term878 A lt2 x' P _6782)). Qed.
Lemma lem306673 {A : Type'} (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term874 A lt2 x''' _6785.
Proof. exact (@lem306585 A x' P y x'' y' lt2 x''' h1 _6785). Qed.
Lemma lem306674 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) : (term874 A lt2 x''' _6785) = (term868 A lt2 x''' _6785).
Proof. exact (eq_refl (term874 A lt2 x''' _6785)). Qed.
Lemma lem306675 {A : Type'} (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term868 A lt2 x''' _6785.
Proof. exact (EQ_MP (@lem306674 A lt2 x''' _6785) (@lem306673 A _6785 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306676 {A : Type'} (_6785 : A -> Prop) (_6786 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term875 A lt2 x''' _6785 _6786.
Proof. exact (@lem306675 A _6785 x' P y x'' y' lt2 x''' h1 _6786). Qed.
Lemma lem306677 {A : Type'} (_6786 : A) (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) : (term875 A lt2 x''' _6785 _6786) = (term866 A _6786 lt2 x''' _6785).
Proof. exact (eq_refl (term875 A lt2 x''' _6785 _6786)). Qed.
Lemma lem306678 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term866 A _6786 lt2 x''' _6785.
Proof. exact (EQ_MP (@lem306677 A _6786 lt2 x''' _6785) (@lem306676 A _6785 _6786 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306679 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (_6787 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term876 A _6786 lt2 x''' _6785 _6787.
Proof. exact (@lem306678 A _6786 _6785 x' P y x'' y' lt2 x''' h1 _6787). Qed.
Lemma lem306680 {A : Type'} (_6786 : A) (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) (_6787 : A) : (term876 A _6786 lt2 x''' _6785 _6787) = (term864 A _6786 lt2 x''' _6785 _6787).
Proof. exact (eq_refl (term876 A _6786 lt2 x''' _6785 _6787)). Qed.
Lemma lem306681 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (_6787 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term864 A _6786 lt2 x''' _6785 _6787.
Proof. exact (EQ_MP (@lem306680 A _6786 lt2 x''' _6785 _6787) (@lem306679 A _6786 _6785 _6787 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306682 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term877 A lt2 P y _6788.
Proof. exact (@lem306612 A x' P y x'' y' lt2 x''' h1 _6788). Qed.
Lemma lem306683 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (_6788 : A) : (term877 A lt2 P y _6788) = (term871 A lt2 P y _6788).
Proof. exact (eq_refl (term877 A lt2 P y _6788)). Qed.
Lemma lem306684 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term871 A lt2 P y _6788.
Proof. exact (EQ_MP (@lem306683 A lt2 P y _6788) (@lem306682 A _6788 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306704 {A : Type'} (_6768 : A) (P : A -> Prop) (h1 : term742 A P) : term719 A P _6768.
Proof. exact (EQ_MP (@lem306623 A P _6768) (@lem306622 A _6768 P h1)). Qed.
Lemma lem306706 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem306724 {A : Type'} (_6772 : A) (P : A -> Prop) (h1 : term742 A P) : term719 A P _6772.
Proof. exact (EQ_MP (@lem306635 A P _6772) (@lem306634 A _6772 P h1)). Qed.
Lemma lem306750 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem306756 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term879 A P lt2 y _6777.
Proof. exact (proj1 (@lem306651 A _6777 lt2 P y h1)). Qed.
Lemma lem306762 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term880 A P y _6777.
Proof. exact (proj2 (@lem306651 A _6777 lt2 P y h1)). Qed.
Lemma lem306768 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term881 A _6775 x _6774.
Proof. exact (proj1 (@lem306648 A _6775 _6774 (@el A) x x' lt2 P y h1)). Qed.
Lemma lem306778 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (_6776 : A) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term882 A _6775 lt2 x _6774 _6776.
Proof. exact (proj2 (@lem306648 A _6775 _6774 _6776 x x' lt2 P y h1)). Qed.
Lemma lem306786 {A : Type'} (_6782 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term803 A lt2 x' P _6782.
Proof. exact (EQ_MP (@lem306665 A lt2 x' P _6782) (@lem306664 A _6782 lt2 x' P h1)). Qed.
Lemma lem306792 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term879 A P lt2 y _6781.
Proof. exact (proj1 (@lem306663 A _6781 lt2 P y h1)). Qed.
Lemma lem306798 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term880 A P y _6781.
Proof. exact (proj2 (@lem306663 A _6781 lt2 P y h1)). Qed.
Lemma lem306822 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term879 A P lt2 y _6788.
Proof. exact (proj1 (@lem306684 A _6788 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306828 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term880 A P y _6788.
Proof. exact (proj2 (@lem306684 A _6788 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306834 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term881 A _6786 x''' _6785.
Proof. exact (proj1 (@lem306681 A _6786 _6785 (@el A) x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306844 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (_6787 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term882 A _6786 lt2 x''' _6785 _6787.
Proof. exact (proj2 (@lem306681 A _6786 _6785 _6787 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem306866 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem306867 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem306866 A P x' h1). Qed.
Lemma lem306869 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem306870 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem306869 (@I (A -> Prop) P x')). Qed.
Lemma lem306871 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem306870 A P x') (@lem306867 A P x' h1)). Qed.
Lemma lem306874 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem306876 {A : Type'} (P : A -> Prop) (_6768 : A) : (term719 A P _6768) = (term885 A P _6768).
Proof. exact (@lem306874 (@I (A -> Prop) P _6768)). Qed.
Lemma lem306879 {A : Type'} (_6768 : A) (P : A -> Prop) (h1 : term742 A P) : term885 A P _6768.
Proof. exact (EQ_MP (@lem306876 A P _6768) (@lem306704 A _6768 P h1)). Qed.
Lemma lem306880 {A : Type'} (_6768 : A) (P : A -> Prop) (h1 : term742 A P) : term885 A P _6768.
Proof. exact (@lem306879 A _6768 P h1). Qed.
Lemma lem306881 {A : Type'} (x' : A) (P : A -> Prop) (h1 : term742 A P) : term885 A P x'.
Proof. exact (@lem306880 A x' P h1). Qed.
Lemma lem306884 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : False.
Proof. exact (@lem306881 A x' P h1 (@lem306871 A P x' h2)). Qed.
Lemma lem306885 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : term886.
Proof. exact (fun h0 : ~ False => @lem306884 A P x' h1 h2). Qed.
Lemma lem306887 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem306888 : term886 = False.
Proof. exact (@lem306887 False). Qed.
Lemma lem306889 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem306888) (@lem306885 A P x' h1 h2)). Qed.
Lemma lem306891 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : @I (A -> Prop) P x'.
Proof. exact (proj1 (@lem305871 A lt2 x' P h1)). Qed.
Lemma lem306892 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem306891 A lt2 x' P h1). Qed.
Lemma lem306894 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem306895 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem306894 (@I (A -> Prop) P x')). Qed.
Lemma lem306896 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem306895 A P x') (@lem306892 A lt2 x' P h1)). Qed.
Lemma lem306899 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem306901 {A : Type'} (P : A -> Prop) (_6772 : A) : (term719 A P _6772) = (term885 A P _6772).
Proof. exact (@lem306899 (@I (A -> Prop) P _6772)). Qed.
Lemma lem306904 {A : Type'} (_6772 : A) (P : A -> Prop) (h1 : term742 A P) : term885 A P _6772.
Proof. exact (EQ_MP (@lem306901 A P _6772) (@lem306724 A _6772 P h1)). Qed.
Lemma lem306905 {A : Type'} (_6772 : A) (P : A -> Prop) (h1 : term742 A P) : term885 A P _6772.
Proof. exact (@lem306904 A _6772 P h1). Qed.
Lemma lem306906 {A : Type'} (x' : A) (P : A -> Prop) (h1 : term742 A P) : term885 A P x'.
Proof. exact (@lem306905 A x' P h1). Qed.
Lemma lem306909 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term742 A P) (h2 : term806 A lt2 x' P) : False.
Proof. exact (@lem306906 A x' P h1 (@lem306896 A lt2 x' P h2)). Qed.
Lemma lem306910 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term742 A P) (h2 : term806 A lt2 x' P) : term886.
Proof. exact (fun h0 : ~ False => @lem306909 A lt2 x' P h1 h2). Qed.
Lemma lem306912 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem306913 : term886 = False.
Proof. exact (@lem306912 False). Qed.
Lemma lem306914 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term742 A P) (h2 : term806 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem306913) (@lem306910 A lt2 x' P h1 h2)). Qed.
Lemma lem306916 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem306917 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem306916 A P x' h1). Qed.
Lemma lem306919 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem306920 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem306919 (@I (A -> Prop) P x')). Qed.
Lemma lem306921 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem306920 A P x') (@lem306917 A P x' h1)). Qed.
Lemma lem306923 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem306924 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem306923 A P x' h1). Qed.
Lemma lem306926 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem306927 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem306926 (@I (A -> Prop) P x')). Qed.
Lemma lem306928 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem306927 A P x') (@lem306924 A P x' h1)). Qed.
Lemma lem306934 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem306935 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : (term881 A _6775 x _6774) = (term887 A x _6774 _6775).
Proof. exact (@lem306934 (term736 A x _6774) (term719 A _6774 _6775)). Qed.
Lemma lem306941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306942 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : (term888 A _6775 x _6774) = (term889 A x _6774 _6775).
Proof. exact (MK_COMB (@lem306941) (@lem306935 A x _6774 _6775)). Qed.
Lemma lem306948 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : (term887 A x _6774 _6775) = (term887 A x _6774 _6775).
Proof. exact (eq_refl (term887 A x _6774 _6775)). Qed.
Lemma lem306949 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : ((term881 A _6775 x _6774) = (term887 A x _6774 _6775)) = ((term887 A x _6774 _6775) = (term887 A x _6774 _6775)).
Proof. exact (MK_COMB (@lem306942 A x _6774 _6775) (@lem306948 A x _6774 _6775)). Qed.
Lemma lem306951 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem306952 (x : Prop) : (x = x) = True.
Proof. exact (@lem306951 Prop x). Qed.
Lemma lem306953 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : ((term887 A x _6774 _6775) = (term887 A x _6774 _6775)) = True.
Proof. exact (@lem306952 (term887 A x _6774 _6775)). Qed.
Lemma lem306954 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : ((term881 A _6775 x _6774) = (term887 A x _6774 _6775)) = True.
Proof. exact (TRANS (@lem306949 A x _6774 _6775) (@lem306953 A x _6774 _6775)). Qed.
Lemma lem306955 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : True = ((term881 A _6775 x _6774) = (term887 A x _6774 _6775)).
Proof. exact (SYM (@lem306954 A x _6774 _6775)). Qed.
Lemma lem306956 {A : Type'} (x : type684 A) (_6774 : A -> Prop) (_6775 : A) : (term881 A _6775 x _6774) = (term887 A x _6774 _6775).
Proof. exact (EQ_MP (@lem306955 A x _6774 _6775) (@lem0)). Qed.
Lemma lem306957 {A : Type'} (_6774 : A -> Prop) (_6775 : A) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term887 A x _6774 _6775.
Proof. exact (EQ_MP (@lem306956 A x _6774 _6775) (@lem306768 A _6775 _6774 x x' lt2 P y h1)). Qed.
Lemma lem306959 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem306960 {A : Type'} (_6775 : A) (x : type684 A) (_6774 : A -> Prop) : (term887 A x _6774 _6775) = (term891 A _6775 x _6774).
Proof. exact (@lem306959 (term719 A _6774 _6775) (term736 A x _6774)). Qed.
Lemma lem306962 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem306963 {A : Type'} (_6774 : A -> Prop) (_6775 : A) : (term892 A _6774 _6775) = (@I (A -> Prop) _6774 _6775).
Proof. exact (@lem306962 (@I (A -> Prop) _6774 _6775)). Qed.
Lemma lem306964 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem306965 {A : Type'} (_6774 : A -> Prop) (_6775 : A) : (term893 A _6774 _6775) = (term894 A _6774 _6775).
Proof. exact (MK_COMB (@lem306964) (@lem306963 A _6774 _6775)). Qed.
Lemma lem306966 {A : Type'} (x : type684 A) (_6774 : A -> Prop) : (term736 A x _6774) = (term736 A x _6774).
Proof. exact (eq_refl (term736 A x _6774)). Qed.
Lemma lem306967 {A : Type'} (_6775 : A) (x : type684 A) (_6774 : A -> Prop) : (term891 A _6775 x _6774) = (term895 A _6775 x _6774).
Proof. exact (MK_COMB (@lem306965 A _6774 _6775) (@lem306966 A x _6774)). Qed.
Lemma lem306968 {A : Type'} (_6775 : A) (x : type684 A) (_6774 : A -> Prop) : (term887 A x _6774 _6775) = (term895 A _6775 x _6774).
Proof. exact (TRANS (@lem306960 A _6775 x _6774) (@lem306967 A _6775 x _6774)). Qed.
Lemma lem306971 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term895 A _6775 x _6774.
Proof. exact (EQ_MP (@lem306968 A _6775 x _6774) (@lem306957 A _6774 _6775 x x' lt2 P y h1)). Qed.
Lemma lem306972 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term895 A _6775 x _6774.
Proof. exact (@lem306971 A _6775 _6774 x x' lt2 P y h1). Qed.
Lemma lem306973 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term895 A x' x P.
Proof. exact (@lem306972 A x' P x x' lt2 P y h1). Qed.
Lemma lem306976 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term812 A x x' lt2 P y) (h2 : @I (A -> Prop) P x') : term736 A x P.
Proof. exact (@lem306973 A x x' lt2 P y h1 (@lem306928 A P x' h2)). Qed.
Lemma lem306977 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term812 A x x' lt2 P y) (h2 : @I (A -> Prop) P x') : term896 A x P.
Proof. exact (fun h0 : term897 A x P => @lem306976 A x lt2 y P x' h1 h2). Qed.
Lemma lem306979 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem306980 {A : Type'} (x : type684 A) (P : A -> Prop) : (term896 A x P) = (term736 A x P).
Proof. exact (@lem306979 (term736 A x P)). Qed.
Lemma lem306981 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term812 A x x' lt2 P y) (h2 : @I (A -> Prop) P x') : term736 A x P.
Proof. exact (EQ_MP (@lem306980 A x P) (@lem306977 A x lt2 y P x' h1 h2)). Qed.
Lemma lem306987 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem306988 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : (term879 A P lt2 y _6777) = (term898 A lt2 y P _6777).
Proof. exact (@lem306987 (term785 A lt2 y _6777) (term719 A P _6777)). Qed.
Lemma lem306994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem306995 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : (term899 A P lt2 y _6777) = (term900 A lt2 y P _6777).
Proof. exact (MK_COMB (@lem306994) (@lem306988 A lt2 y P _6777)). Qed.
Lemma lem307001 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : (term898 A lt2 y P _6777) = (term898 A lt2 y P _6777).
Proof. exact (eq_refl (term898 A lt2 y P _6777)). Qed.
Lemma lem307002 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : ((term879 A P lt2 y _6777) = (term898 A lt2 y P _6777)) = ((term898 A lt2 y P _6777) = (term898 A lt2 y P _6777)).
Proof. exact (MK_COMB (@lem306995 A lt2 y P _6777) (@lem307001 A lt2 y P _6777)). Qed.
Lemma lem307004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem307005 (x : Prop) : (x = x) = True.
Proof. exact (@lem307004 Prop x). Qed.
Lemma lem307006 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : ((term898 A lt2 y P _6777) = (term898 A lt2 y P _6777)) = True.
Proof. exact (@lem307005 (term898 A lt2 y P _6777)). Qed.
Lemma lem307007 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : ((term879 A P lt2 y _6777) = (term898 A lt2 y P _6777)) = True.
Proof. exact (TRANS (@lem307002 A lt2 y P _6777) (@lem307006 A lt2 y P _6777)). Qed.
Lemma lem307008 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : True = ((term879 A P lt2 y _6777) = (term898 A lt2 y P _6777)).
Proof. exact (SYM (@lem307007 A lt2 y P _6777)). Qed.
Lemma lem307009 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6777 : A) : (term879 A P lt2 y _6777) = (term898 A lt2 y P _6777).
Proof. exact (EQ_MP (@lem307008 A lt2 y P _6777) (@lem0)). Qed.
Lemma lem307010 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term898 A lt2 y P _6777.
Proof. exact (EQ_MP (@lem307009 A lt2 y P _6777) (@lem306756 A _6777 lt2 P y h1)). Qed.
Lemma lem307012 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem307013 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6777 : A) : (term898 A lt2 y P _6777) = (term901 A P lt2 y _6777).
Proof. exact (@lem307012 (term719 A P _6777) (term785 A lt2 y _6777)). Qed.
Lemma lem307015 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem307016 {A : Type'} (P : A -> Prop) (_6777 : A) : (term892 A P _6777) = (@I (A -> Prop) P _6777).
Proof. exact (@lem307015 (@I (A -> Prop) P _6777)). Qed.
Lemma lem307017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307018 {A : Type'} (P : A -> Prop) (_6777 : A) : (term893 A P _6777) = (term894 A P _6777).
Proof. exact (MK_COMB (@lem307017) (@lem307016 A P _6777)). Qed.
Lemma lem307019 {A : Type'} (lt2 : type1402 A) (y : A -> A) (_6777 : A) : (term785 A lt2 y _6777) = (term785 A lt2 y _6777).
Proof. exact (eq_refl (term785 A lt2 y _6777)). Qed.
Lemma lem307020 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6777 : A) : (term901 A P lt2 y _6777) = (term902 A P lt2 y _6777).
Proof. exact (MK_COMB (@lem307018 A P _6777) (@lem307019 A lt2 y _6777)). Qed.
Lemma lem307021 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6777 : A) : (term898 A lt2 y P _6777) = (term902 A P lt2 y _6777).
Proof. exact (TRANS (@lem307013 A P lt2 y _6777) (@lem307020 A P lt2 y _6777)). Qed.
Lemma lem307024 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term902 A P lt2 y _6777.
Proof. exact (EQ_MP (@lem307021 A P lt2 y _6777) (@lem307010 A _6777 lt2 P y h1)). Qed.
Lemma lem307025 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term902 A P lt2 y _6777.
Proof. exact (@lem307024 A _6777 lt2 P y h1). Qed.
Lemma lem307026 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term903 A lt2 y x P.
Proof. exact (@lem307025 A (@I ((A -> Prop) -> A) x P) lt2 P y h1). Qed.
Lemma lem307029 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term904 A lt2 y x P.
Proof. exact (@lem307026 A x lt2 P y h1 (@lem306981 A x lt2 y P x' h2 h3)). Qed.
Lemma lem307030 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term905 A lt2 y x P.
Proof. exact (fun h0 : term906 A lt2 y x P => @lem307029 A x lt2 y P x' h1 h2 h3). Qed.
Lemma lem307032 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307033 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : type684 A) (P : A -> Prop) : (term905 A lt2 y x P) = (term904 A lt2 y x P).
Proof. exact (@lem307032 (term904 A lt2 y x P)). Qed.
Lemma lem307034 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term904 A lt2 y x P.
Proof. exact (EQ_MP (@lem307033 A lt2 y x P) (@lem307030 A x lt2 y P x' h1 h2 h3)). Qed.
Lemma lem307036 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (h1). Qed.
Lemma lem307037 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem307036 A P x' h1). Qed.
Lemma lem307039 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307040 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem307039 (@I (A -> Prop) P x')). Qed.
Lemma lem307041 {A : Type'} (P : A -> Prop) (x' : A) (h1 : @I (A -> Prop) P x') : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem307040 A P x') (@lem307037 A P x' h1)). Qed.
Lemma lem307043 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term895 A _6775 x _6774.
Proof. exact (EQ_MP (@lem306968 A _6775 x _6774) (@lem306957 A _6774 _6775 x x' lt2 P y h1)). Qed.
Lemma lem307044 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term895 A _6775 x _6774.
Proof. exact (@lem307043 A _6775 _6774 x x' lt2 P y h1). Qed.
Lemma lem307045 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term895 A x' x P.
Proof. exact (@lem307044 A x' P x x' lt2 P y h1). Qed.
Lemma lem307048 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term812 A x x' lt2 P y) (h2 : @I (A -> Prop) P x') : term736 A x P.
Proof. exact (@lem307045 A x x' lt2 P y h1 (@lem307041 A P x' h2)). Qed.
Lemma lem307049 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term812 A x x' lt2 P y) (h2 : @I (A -> Prop) P x') : term896 A x P.
Proof. exact (fun h0 : term897 A x P => @lem307048 A x lt2 y P x' h1 h2). Qed.
Lemma lem307051 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307052 {A : Type'} (x : type684 A) (P : A -> Prop) : (term896 A x P) = (term736 A x P).
Proof. exact (@lem307051 (term736 A x P)). Qed.
Lemma lem307053 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term812 A x x' lt2 P y) (h2 : @I (A -> Prop) P x') : term736 A x P.
Proof. exact (EQ_MP (@lem307052 A x P) (@lem307049 A x lt2 y P x' h1 h2)). Qed.
Lemma lem307059 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem307060 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : (term880 A P y _6777) = (term907 A y P _6777).
Proof. exact (@lem307059 (term778 A P y _6777) (term719 A P _6777)). Qed.
Lemma lem307066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307067 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : (term908 A P y _6777) = (term909 A y P _6777).
Proof. exact (MK_COMB (@lem307066) (@lem307060 A y P _6777)). Qed.
Lemma lem307073 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : (term907 A y P _6777) = (term907 A y P _6777).
Proof. exact (eq_refl (term907 A y P _6777)). Qed.
Lemma lem307074 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : ((term880 A P y _6777) = (term907 A y P _6777)) = ((term907 A y P _6777) = (term907 A y P _6777)).
Proof. exact (MK_COMB (@lem307067 A y P _6777) (@lem307073 A y P _6777)). Qed.
Lemma lem307076 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem307077 (x : Prop) : (x = x) = True.
Proof. exact (@lem307076 Prop x). Qed.
Lemma lem307078 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : ((term907 A y P _6777) = (term907 A y P _6777)) = True.
Proof. exact (@lem307077 (term907 A y P _6777)). Qed.
Lemma lem307079 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : ((term880 A P y _6777) = (term907 A y P _6777)) = True.
Proof. exact (TRANS (@lem307074 A y P _6777) (@lem307078 A y P _6777)). Qed.
Lemma lem307080 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : True = ((term880 A P y _6777) = (term907 A y P _6777)).
Proof. exact (SYM (@lem307079 A y P _6777)). Qed.
Lemma lem307081 {A : Type'} (y : A -> A) (P : A -> Prop) (_6777 : A) : (term880 A P y _6777) = (term907 A y P _6777).
Proof. exact (EQ_MP (@lem307080 A y P _6777) (@lem0)). Qed.
Lemma lem307082 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term907 A y P _6777.
Proof. exact (EQ_MP (@lem307081 A y P _6777) (@lem306762 A _6777 lt2 P y h1)). Qed.
Lemma lem307084 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem307085 {A : Type'} (P : A -> Prop) (y : A -> A) (_6777 : A) : (term907 A y P _6777) = (term910 A P y _6777).
Proof. exact (@lem307084 (term719 A P _6777) (term778 A P y _6777)). Qed.
Lemma lem307087 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem307088 {A : Type'} (P : A -> Prop) (_6777 : A) : (term892 A P _6777) = (@I (A -> Prop) P _6777).
Proof. exact (@lem307087 (@I (A -> Prop) P _6777)). Qed.
Lemma lem307089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307090 {A : Type'} (P : A -> Prop) (_6777 : A) : (term893 A P _6777) = (term894 A P _6777).
Proof. exact (MK_COMB (@lem307089) (@lem307088 A P _6777)). Qed.
Lemma lem307091 {A : Type'} (P : A -> Prop) (y : A -> A) (_6777 : A) : (term778 A P y _6777) = (term778 A P y _6777).
Proof. exact (eq_refl (term778 A P y _6777)). Qed.
Lemma lem307092 {A : Type'} (P : A -> Prop) (y : A -> A) (_6777 : A) : (term910 A P y _6777) = (term911 A P y _6777).
Proof. exact (MK_COMB (@lem307090 A P _6777) (@lem307091 A P y _6777)). Qed.
Lemma lem307093 {A : Type'} (P : A -> Prop) (y : A -> A) (_6777 : A) : (term907 A y P _6777) = (term911 A P y _6777).
Proof. exact (TRANS (@lem307085 A P y _6777) (@lem307092 A P y _6777)). Qed.
Lemma lem307096 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term911 A P y _6777.
Proof. exact (EQ_MP (@lem307093 A P y _6777) (@lem307082 A _6777 lt2 P y h1)). Qed.
Lemma lem307097 {A : Type'} (_6777 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term911 A P y _6777.
Proof. exact (@lem307096 A _6777 lt2 P y h1). Qed.
Lemma lem307098 {A : Type'} (x : type684 A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term912 A y x P.
Proof. exact (@lem307097 A (@I ((A -> Prop) -> A) x P) lt2 P y h1). Qed.
Lemma lem307101 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term913 A y x P.
Proof. exact (@lem307098 A x lt2 P y h1 (@lem307053 A x lt2 y P x' h2 h3)). Qed.
Lemma lem307102 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term914 A y x P.
Proof. exact (fun h0 : term915 A y x P => @lem307101 A x lt2 y P x' h1 h2 h3). Qed.
Lemma lem307104 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307105 {A : Type'} (y : A -> A) (x : type684 A) (P : A -> Prop) : (term914 A y x P) = (term913 A y x P).
Proof. exact (@lem307104 (term913 A y x P)). Qed.
Lemma lem307106 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term913 A y x P.
Proof. exact (EQ_MP (@lem307105 A y x P) (@lem307102 A x lt2 y P x' h1 h2 h3)). Qed.
Lemma lem307108 (a : Prop) (b : Prop) : (term916 a b) = (term917 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem307109 {A : Type'} (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) (_6776 : A) : (term729 A lt2 x _6774 _6776) = (term918 A lt2 x _6774 _6776).
Proof. exact (@lem307108 (term723 A lt2 _6776 x _6774) (@I (A -> Prop) _6774 _6776)). Qed.
Lemma lem307110 {A : Type'} (_6774 : A -> Prop) (_6775 : A) : (term762 A _6774 _6775) = (term762 A _6774 _6775).
Proof. exact (eq_refl (term762 A _6774 _6775)). Qed.
Lemma lem307111 {A : Type'} (_6775 : A) (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) (_6776 : A) : (term882 A _6775 lt2 x _6774 _6776) = (term919 A _6775 lt2 x _6774 _6776).
Proof. exact (MK_COMB (@lem307110 A _6774 _6775) (@lem307109 A lt2 x _6774 _6776)). Qed.
Lemma lem307113 (a : Prop) (b : Prop) : (term916 a b) = (term917 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem307114 {A : Type'} (_6775 : A) (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) (_6776 : A) : (term919 A _6775 lt2 x _6774 _6776) = (term920 A _6775 lt2 x _6774 _6776).
Proof. exact (@lem307113 (@I (A -> Prop) _6774 _6775) (term921 A lt2 x _6774 _6776)). Qed.
Lemma lem307115 {A : Type'} (_6775 : A) (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) (_6776 : A) : (term882 A _6775 lt2 x _6774 _6776) = (term920 A _6775 lt2 x _6774 _6776).
Proof. exact (TRANS (@lem307111 A _6775 lt2 x _6774 _6776) (@lem307114 A _6775 lt2 x _6774 _6776)). Qed.
Lemma lem307117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem307118 {A : Type'} (_6775 : A) (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) (_6776 : A) : (term920 A _6775 lt2 x _6774 _6776) = (term922 A _6775 lt2 x _6774 _6776).
Proof. exact (@lem307117 (term923 A _6775 lt2 x _6774 _6776)). Qed.
Lemma lem307119 {A : Type'} (_6775 : A) (lt2 : type1402 A) (x : type684 A) (_6774 : A -> Prop) (_6776 : A) : (term882 A _6775 lt2 x _6774 _6776) = (term922 A _6775 lt2 x _6774 _6776).
Proof. exact (TRANS (@lem307115 A _6775 lt2 x _6774 _6776) (@lem307118 A _6775 lt2 x _6774 _6776)). Qed.
Lemma lem307121 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term924 A lt2 y x P.
Proof. exact (conj (@lem307034 A x lt2 y P x' h1 h2 h3) (@lem307106 A x lt2 y P x' h1 h2 h3)). Qed.
Lemma lem307122 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term925 A x' lt2 y x P.
Proof. exact (conj (@lem306921 A P x' h3) (@lem307121 A x lt2 y P x' h1 h2 h3)). Qed.
Lemma lem307124 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (_6776 : A) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term922 A _6775 lt2 x _6774 _6776.
Proof. exact (EQ_MP (@lem307119 A _6775 lt2 x _6774 _6776) (@lem306778 A _6775 _6774 _6776 x x' lt2 P y h1)). Qed.
Lemma lem307125 {A : Type'} (_6775 : A) (_6774 : A -> Prop) (_6776 : A) (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term922 A _6775 lt2 x _6774 _6776.
Proof. exact (@lem307124 A _6775 _6774 _6776 x x' lt2 P y h1). Qed.
Lemma lem307126 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : term926 A x' lt2 y x P.
Proof. exact (@lem307125 A x' P (term927 A y x P) x x' lt2 P y h1). Qed.
Lemma lem307129 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : False.
Proof. exact (@lem307126 A x x' lt2 P y h2 (@lem307122 A x lt2 y P x' h1 h2 h3)). Qed.
Lemma lem307130 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : term886.
Proof. exact (fun h0 : ~ False => @lem307129 A x lt2 y P x' h1 h2 h3). Qed.
Lemma lem307132 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307133 : term886 = False.
Proof. exact (@lem307132 False). Qed.
Lemma lem307134 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307133) (@lem307130 A x lt2 y P x' h1 h2 h3)). Qed.
Lemma lem307136 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : @I (A -> Prop) P x'.
Proof. exact (proj1 (@lem305875 A lt2 x' P h1)). Qed.
Lemma lem307137 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem307136 A lt2 x' P h1). Qed.
Lemma lem307139 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307140 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem307139 (@I (A -> Prop) P x')). Qed.
Lemma lem307141 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem307140 A P x') (@lem307137 A lt2 x' P h1)). Qed.
Lemma lem307147 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem307148 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : (term879 A P lt2 y _6781) = (term898 A lt2 y P _6781).
Proof. exact (@lem307147 (term785 A lt2 y _6781) (term719 A P _6781)). Qed.
Lemma lem307154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307155 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : (term899 A P lt2 y _6781) = (term900 A lt2 y P _6781).
Proof. exact (MK_COMB (@lem307154) (@lem307148 A lt2 y P _6781)). Qed.
Lemma lem307161 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : (term898 A lt2 y P _6781) = (term898 A lt2 y P _6781).
Proof. exact (eq_refl (term898 A lt2 y P _6781)). Qed.
Lemma lem307162 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : ((term879 A P lt2 y _6781) = (term898 A lt2 y P _6781)) = ((term898 A lt2 y P _6781) = (term898 A lt2 y P _6781)).
Proof. exact (MK_COMB (@lem307155 A lt2 y P _6781) (@lem307161 A lt2 y P _6781)). Qed.
Lemma lem307164 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem307165 (x : Prop) : (x = x) = True.
Proof. exact (@lem307164 Prop x). Qed.
Lemma lem307166 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : ((term898 A lt2 y P _6781) = (term898 A lt2 y P _6781)) = True.
Proof. exact (@lem307165 (term898 A lt2 y P _6781)). Qed.
Lemma lem307167 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : ((term879 A P lt2 y _6781) = (term898 A lt2 y P _6781)) = True.
Proof. exact (TRANS (@lem307162 A lt2 y P _6781) (@lem307166 A lt2 y P _6781)). Qed.
Lemma lem307168 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : True = ((term879 A P lt2 y _6781) = (term898 A lt2 y P _6781)).
Proof. exact (SYM (@lem307167 A lt2 y P _6781)). Qed.
Lemma lem307169 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6781 : A) : (term879 A P lt2 y _6781) = (term898 A lt2 y P _6781).
Proof. exact (EQ_MP (@lem307168 A lt2 y P _6781) (@lem0)). Qed.
Lemma lem307170 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term898 A lt2 y P _6781.
Proof. exact (EQ_MP (@lem307169 A lt2 y P _6781) (@lem306792 A _6781 lt2 P y h1)). Qed.
Lemma lem307172 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem307173 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6781 : A) : (term898 A lt2 y P _6781) = (term901 A P lt2 y _6781).
Proof. exact (@lem307172 (term719 A P _6781) (term785 A lt2 y _6781)). Qed.
Lemma lem307175 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem307176 {A : Type'} (P : A -> Prop) (_6781 : A) : (term892 A P _6781) = (@I (A -> Prop) P _6781).
Proof. exact (@lem307175 (@I (A -> Prop) P _6781)). Qed.
Lemma lem307177 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307178 {A : Type'} (P : A -> Prop) (_6781 : A) : (term893 A P _6781) = (term894 A P _6781).
Proof. exact (MK_COMB (@lem307177) (@lem307176 A P _6781)). Qed.
Lemma lem307179 {A : Type'} (lt2 : type1402 A) (y : A -> A) (_6781 : A) : (term785 A lt2 y _6781) = (term785 A lt2 y _6781).
Proof. exact (eq_refl (term785 A lt2 y _6781)). Qed.
Lemma lem307180 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6781 : A) : (term901 A P lt2 y _6781) = (term902 A P lt2 y _6781).
Proof. exact (MK_COMB (@lem307178 A P _6781) (@lem307179 A lt2 y _6781)). Qed.
Lemma lem307181 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6781 : A) : (term898 A lt2 y P _6781) = (term902 A P lt2 y _6781).
Proof. exact (TRANS (@lem307173 A P lt2 y _6781) (@lem307180 A P lt2 y _6781)). Qed.
Lemma lem307184 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term902 A P lt2 y _6781.
Proof. exact (EQ_MP (@lem307181 A P lt2 y _6781) (@lem307170 A _6781 lt2 P y h1)). Qed.
Lemma lem307185 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term902 A P lt2 y _6781.
Proof. exact (@lem307184 A _6781 lt2 P y h1). Qed.
Lemma lem307186 {A : Type'} (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term902 A P lt2 y x'.
Proof. exact (@lem307185 A x' lt2 P y h1). Qed.
Lemma lem307189 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term785 A lt2 y x'.
Proof. exact (@lem307186 A x' lt2 P y h1 (@lem307141 A lt2 x' P h2)). Qed.
Lemma lem307190 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term928 A lt2 y x'.
Proof. exact (fun h0 : term929 A lt2 y x' => @lem307189 A y lt2 x' P h1 h2). Qed.
Lemma lem307192 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307193 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x' : A) : (term928 A lt2 y x') = (term785 A lt2 y x').
Proof. exact (@lem307192 (term785 A lt2 y x')). Qed.
Lemma lem307194 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term785 A lt2 y x'.
Proof. exact (EQ_MP (@lem307193 A lt2 y x') (@lem307190 A y lt2 x' P h1 h2)). Qed.
Lemma lem307196 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : @I (A -> Prop) P x'.
Proof. exact (proj1 (@lem305875 A lt2 x' P h1)). Qed.
Lemma lem307197 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem307196 A lt2 x' P h1). Qed.
Lemma lem307199 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307200 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem307199 (@I (A -> Prop) P x')). Qed.
Lemma lem307201 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem307200 A P x') (@lem307197 A lt2 x' P h1)). Qed.
Lemma lem307207 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem307208 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : (term880 A P y _6781) = (term907 A y P _6781).
Proof. exact (@lem307207 (term778 A P y _6781) (term719 A P _6781)). Qed.
Lemma lem307214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307215 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : (term908 A P y _6781) = (term909 A y P _6781).
Proof. exact (MK_COMB (@lem307214) (@lem307208 A y P _6781)). Qed.
Lemma lem307221 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : (term907 A y P _6781) = (term907 A y P _6781).
Proof. exact (eq_refl (term907 A y P _6781)). Qed.
Lemma lem307222 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : ((term880 A P y _6781) = (term907 A y P _6781)) = ((term907 A y P _6781) = (term907 A y P _6781)).
Proof. exact (MK_COMB (@lem307215 A y P _6781) (@lem307221 A y P _6781)). Qed.
Lemma lem307224 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem307225 (x : Prop) : (x = x) = True.
Proof. exact (@lem307224 Prop x). Qed.
Lemma lem307226 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : ((term907 A y P _6781) = (term907 A y P _6781)) = True.
Proof. exact (@lem307225 (term907 A y P _6781)). Qed.
Lemma lem307227 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : ((term880 A P y _6781) = (term907 A y P _6781)) = True.
Proof. exact (TRANS (@lem307222 A y P _6781) (@lem307226 A y P _6781)). Qed.
Lemma lem307228 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : True = ((term880 A P y _6781) = (term907 A y P _6781)).
Proof. exact (SYM (@lem307227 A y P _6781)). Qed.
Lemma lem307229 {A : Type'} (y : A -> A) (P : A -> Prop) (_6781 : A) : (term880 A P y _6781) = (term907 A y P _6781).
Proof. exact (EQ_MP (@lem307228 A y P _6781) (@lem0)). Qed.
Lemma lem307230 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term907 A y P _6781.
Proof. exact (EQ_MP (@lem307229 A y P _6781) (@lem306798 A _6781 lt2 P y h1)). Qed.
Lemma lem307232 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem307233 {A : Type'} (P : A -> Prop) (y : A -> A) (_6781 : A) : (term907 A y P _6781) = (term910 A P y _6781).
Proof. exact (@lem307232 (term719 A P _6781) (term778 A P y _6781)). Qed.
Lemma lem307235 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem307236 {A : Type'} (P : A -> Prop) (_6781 : A) : (term892 A P _6781) = (@I (A -> Prop) P _6781).
Proof. exact (@lem307235 (@I (A -> Prop) P _6781)). Qed.
Lemma lem307237 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307238 {A : Type'} (P : A -> Prop) (_6781 : A) : (term893 A P _6781) = (term894 A P _6781).
Proof. exact (MK_COMB (@lem307237) (@lem307236 A P _6781)). Qed.
Lemma lem307239 {A : Type'} (P : A -> Prop) (y : A -> A) (_6781 : A) : (term778 A P y _6781) = (term778 A P y _6781).
Proof. exact (eq_refl (term778 A P y _6781)). Qed.
Lemma lem307240 {A : Type'} (P : A -> Prop) (y : A -> A) (_6781 : A) : (term910 A P y _6781) = (term911 A P y _6781).
Proof. exact (MK_COMB (@lem307238 A P _6781) (@lem307239 A P y _6781)). Qed.
Lemma lem307241 {A : Type'} (P : A -> Prop) (y : A -> A) (_6781 : A) : (term907 A y P _6781) = (term911 A P y _6781).
Proof. exact (TRANS (@lem307233 A P y _6781) (@lem307240 A P y _6781)). Qed.
Lemma lem307244 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term911 A P y _6781.
Proof. exact (EQ_MP (@lem307241 A P y _6781) (@lem307230 A _6781 lt2 P y h1)). Qed.
Lemma lem307245 {A : Type'} (_6781 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term911 A P y _6781.
Proof. exact (@lem307244 A _6781 lt2 P y h1). Qed.
Lemma lem307246 {A : Type'} (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) : term911 A P y x'.
Proof. exact (@lem307245 A x' lt2 P y h1). Qed.
Lemma lem307249 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term778 A P y x'.
Proof. exact (@lem307246 A x' lt2 P y h1 (@lem307201 A lt2 x' P h2)). Qed.
Lemma lem307250 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term930 A P y x'.
Proof. exact (fun h0 : term931 A P y x' => @lem307249 A y lt2 x' P h1 h2). Qed.
Lemma lem307252 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307253 {A : Type'} (P : A -> Prop) (y : A -> A) (x' : A) : (term930 A P y x') = (term778 A P y x').
Proof. exact (@lem307252 (term778 A P y x')). Qed.
Lemma lem307254 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term778 A P y x'.
Proof. exact (EQ_MP (@lem307253 A P y x') (@lem307250 A y lt2 x' P h1 h2)). Qed.
Lemma lem307256 (a : Prop) (b : Prop) : (term916 a b) = (term917 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem307257 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6782 : A) : (term803 A lt2 x' P _6782) = (term932 A lt2 x' P _6782).
Proof. exact (@lem307256 (term798 A lt2 _6782 x') (@I (A -> Prop) P _6782)). Qed.
Lemma lem307259 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem307260 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6782 : A) : (term932 A lt2 x' P _6782) = (term933 A lt2 x' P _6782).
Proof. exact (@lem307259 (term934 A lt2 x' P _6782)). Qed.
Lemma lem307261 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6782 : A) : (term803 A lt2 x' P _6782) = (term933 A lt2 x' P _6782).
Proof. exact (TRANS (@lem307257 A lt2 x' P _6782) (@lem307260 A lt2 x' P _6782)). Qed.
Lemma lem307263 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term789 A lt2 P y x'.
Proof. exact (conj (@lem307194 A y lt2 x' P h1 h2) (@lem307254 A y lt2 x' P h1 h2)). Qed.
Lemma lem307265 {A : Type'} (_6782 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term933 A lt2 x' P _6782.
Proof. exact (EQ_MP (@lem307261 A lt2 x' P _6782) (@lem306786 A _6782 lt2 x' P h1)). Qed.
Lemma lem307266 {A : Type'} (_6782 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term933 A lt2 x' P _6782.
Proof. exact (@lem307265 A _6782 lt2 x' P h1). Qed.
Lemma lem307267 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term806 A lt2 x' P) : term935 A lt2 P y x'.
Proof. exact (@lem307266 A (@I (A -> A) y x') lt2 x' P h1). Qed.
Lemma lem307270 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : False.
Proof. exact (@lem307267 A y lt2 x' P h2 (@lem307263 A y lt2 x' P h1 h2)). Qed.
Lemma lem307271 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : term886.
Proof. exact (fun h0 : ~ False => @lem307270 A y lt2 x' P h1 h2). Qed.
Lemma lem307273 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307274 : term886 = False.
Proof. exact (@lem307273 False). Qed.
Lemma lem307275 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term792 A lt2 P y) (h2 : term806 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem307274) (@lem307271 A y lt2 x' P h1 h2)). Qed.
Lemma lem307277 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : @I (A -> Prop) P x'.
Proof. exact (proj1 (@lem305879 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307278 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem307277 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307280 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307281 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem307280 (@I (A -> Prop) P x')). Qed.
Lemma lem307282 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem307281 A P x') (@lem307278 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307284 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : @I (A -> Prop) P x'.
Proof. exact (proj1 (@lem305879 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307285 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem307284 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307287 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307288 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem307287 (@I (A -> Prop) P x')). Qed.
Lemma lem307289 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem307288 A P x') (@lem307285 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307295 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem307296 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : (term881 A _6786 x''' _6785) = (term887 A x''' _6785 _6786).
Proof. exact (@lem307295 (term736 A x''' _6785) (term719 A _6785 _6786)). Qed.
Lemma lem307302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307303 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : (term888 A _6786 x''' _6785) = (term889 A x''' _6785 _6786).
Proof. exact (MK_COMB (@lem307302) (@lem307296 A x''' _6785 _6786)). Qed.
Lemma lem307309 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : (term887 A x''' _6785 _6786) = (term887 A x''' _6785 _6786).
Proof. exact (eq_refl (term887 A x''' _6785 _6786)). Qed.
Lemma lem307310 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : ((term881 A _6786 x''' _6785) = (term887 A x''' _6785 _6786)) = ((term887 A x''' _6785 _6786) = (term887 A x''' _6785 _6786)).
Proof. exact (MK_COMB (@lem307303 A x''' _6785 _6786) (@lem307309 A x''' _6785 _6786)). Qed.
Lemma lem307312 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem307313 (x : Prop) : (x = x) = True.
Proof. exact (@lem307312 Prop x). Qed.
Lemma lem307314 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : ((term887 A x''' _6785 _6786) = (term887 A x''' _6785 _6786)) = True.
Proof. exact (@lem307313 (term887 A x''' _6785 _6786)). Qed.
Lemma lem307315 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : ((term881 A _6786 x''' _6785) = (term887 A x''' _6785 _6786)) = True.
Proof. exact (TRANS (@lem307310 A x''' _6785 _6786) (@lem307314 A x''' _6785 _6786)). Qed.
Lemma lem307316 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : True = ((term881 A _6786 x''' _6785) = (term887 A x''' _6785 _6786)).
Proof. exact (SYM (@lem307315 A x''' _6785 _6786)). Qed.
Lemma lem307317 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) (_6786 : A) : (term881 A _6786 x''' _6785) = (term887 A x''' _6785 _6786).
Proof. exact (EQ_MP (@lem307316 A x''' _6785 _6786) (@lem0)). Qed.
Lemma lem307318 {A : Type'} (_6785 : A -> Prop) (_6786 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term887 A x''' _6785 _6786.
Proof. exact (EQ_MP (@lem307317 A x''' _6785 _6786) (@lem306834 A _6786 _6785 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307320 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem307321 {A : Type'} (_6786 : A) (x''' : type684 A) (_6785 : A -> Prop) : (term887 A x''' _6785 _6786) = (term891 A _6786 x''' _6785).
Proof. exact (@lem307320 (term719 A _6785 _6786) (term736 A x''' _6785)). Qed.
Lemma lem307323 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem307324 {A : Type'} (_6785 : A -> Prop) (_6786 : A) : (term892 A _6785 _6786) = (@I (A -> Prop) _6785 _6786).
Proof. exact (@lem307323 (@I (A -> Prop) _6785 _6786)). Qed.
Lemma lem307325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307326 {A : Type'} (_6785 : A -> Prop) (_6786 : A) : (term893 A _6785 _6786) = (term894 A _6785 _6786).
Proof. exact (MK_COMB (@lem307325) (@lem307324 A _6785 _6786)). Qed.
Lemma lem307327 {A : Type'} (x''' : type684 A) (_6785 : A -> Prop) : (term736 A x''' _6785) = (term736 A x''' _6785).
Proof. exact (eq_refl (term736 A x''' _6785)). Qed.
Lemma lem307328 {A : Type'} (_6786 : A) (x''' : type684 A) (_6785 : A -> Prop) : (term891 A _6786 x''' _6785) = (term895 A _6786 x''' _6785).
Proof. exact (MK_COMB (@lem307326 A _6785 _6786) (@lem307327 A x''' _6785)). Qed.
Lemma lem307329 {A : Type'} (_6786 : A) (x''' : type684 A) (_6785 : A -> Prop) : (term887 A x''' _6785 _6786) = (term895 A _6786 x''' _6785).
Proof. exact (TRANS (@lem307321 A _6786 x''' _6785) (@lem307328 A _6786 x''' _6785)). Qed.
Lemma lem307332 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term895 A _6786 x''' _6785.
Proof. exact (EQ_MP (@lem307329 A _6786 x''' _6785) (@lem307318 A _6785 _6786 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307333 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term895 A _6786 x''' _6785.
Proof. exact (@lem307332 A _6786 _6785 x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307334 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term895 A x' x''' P.
Proof. exact (@lem307333 A x' P x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307337 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term736 A x''' P.
Proof. exact (@lem307334 A x' P y x'' y' lt2 x''' h1 (@lem307289 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307338 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term896 A x''' P.
Proof. exact (fun h0 : term897 A x''' P => @lem307337 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307340 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307341 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term896 A x''' P) = (term736 A x''' P).
Proof. exact (@lem307340 (term736 A x''' P)). Qed.
Lemma lem307342 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term736 A x''' P.
Proof. exact (EQ_MP (@lem307341 A x''' P) (@lem307338 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307348 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem307349 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : (term879 A P lt2 y _6788) = (term898 A lt2 y P _6788).
Proof. exact (@lem307348 (term785 A lt2 y _6788) (term719 A P _6788)). Qed.
Lemma lem307355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307356 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : (term899 A P lt2 y _6788) = (term900 A lt2 y P _6788).
Proof. exact (MK_COMB (@lem307355) (@lem307349 A lt2 y P _6788)). Qed.
Lemma lem307362 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : (term898 A lt2 y P _6788) = (term898 A lt2 y P _6788).
Proof. exact (eq_refl (term898 A lt2 y P _6788)). Qed.
Lemma lem307363 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : ((term879 A P lt2 y _6788) = (term898 A lt2 y P _6788)) = ((term898 A lt2 y P _6788) = (term898 A lt2 y P _6788)).
Proof. exact (MK_COMB (@lem307356 A lt2 y P _6788) (@lem307362 A lt2 y P _6788)). Qed.
Lemma lem307365 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem307366 (x : Prop) : (x = x) = True.
Proof. exact (@lem307365 Prop x). Qed.
Lemma lem307367 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : ((term898 A lt2 y P _6788) = (term898 A lt2 y P _6788)) = True.
Proof. exact (@lem307366 (term898 A lt2 y P _6788)). Qed.
Lemma lem307368 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : ((term879 A P lt2 y _6788) = (term898 A lt2 y P _6788)) = True.
Proof. exact (TRANS (@lem307363 A lt2 y P _6788) (@lem307367 A lt2 y P _6788)). Qed.
Lemma lem307369 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : True = ((term879 A P lt2 y _6788) = (term898 A lt2 y P _6788)).
Proof. exact (SYM (@lem307368 A lt2 y P _6788)). Qed.
Lemma lem307370 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6788 : A) : (term879 A P lt2 y _6788) = (term898 A lt2 y P _6788).
Proof. exact (EQ_MP (@lem307369 A lt2 y P _6788) (@lem0)). Qed.
Lemma lem307371 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term898 A lt2 y P _6788.
Proof. exact (EQ_MP (@lem307370 A lt2 y P _6788) (@lem306822 A _6788 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307373 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem307374 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6788 : A) : (term898 A lt2 y P _6788) = (term901 A P lt2 y _6788).
Proof. exact (@lem307373 (term719 A P _6788) (term785 A lt2 y _6788)). Qed.
Lemma lem307376 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem307377 {A : Type'} (P : A -> Prop) (_6788 : A) : (term892 A P _6788) = (@I (A -> Prop) P _6788).
Proof. exact (@lem307376 (@I (A -> Prop) P _6788)). Qed.
Lemma lem307378 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307379 {A : Type'} (P : A -> Prop) (_6788 : A) : (term893 A P _6788) = (term894 A P _6788).
Proof. exact (MK_COMB (@lem307378) (@lem307377 A P _6788)). Qed.
Lemma lem307380 {A : Type'} (lt2 : type1402 A) (y : A -> A) (_6788 : A) : (term785 A lt2 y _6788) = (term785 A lt2 y _6788).
Proof. exact (eq_refl (term785 A lt2 y _6788)). Qed.
Lemma lem307381 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6788 : A) : (term901 A P lt2 y _6788) = (term902 A P lt2 y _6788).
Proof. exact (MK_COMB (@lem307379 A P _6788) (@lem307380 A lt2 y _6788)). Qed.
Lemma lem307382 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6788 : A) : (term898 A lt2 y P _6788) = (term902 A P lt2 y _6788).
Proof. exact (TRANS (@lem307374 A P lt2 y _6788) (@lem307381 A P lt2 y _6788)). Qed.
Lemma lem307385 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term902 A P lt2 y _6788.
Proof. exact (EQ_MP (@lem307382 A P lt2 y _6788) (@lem307371 A _6788 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307386 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term902 A P lt2 y _6788.
Proof. exact (@lem307385 A _6788 x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307387 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term903 A lt2 y x''' P.
Proof. exact (@lem307386 A (@I ((A -> Prop) -> A) x''' P) x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307390 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term904 A lt2 y x''' P.
Proof. exact (@lem307387 A x' P y x'' y' lt2 x''' h1 (@lem307342 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307391 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term905 A lt2 y x''' P.
Proof. exact (fun h0 : term906 A lt2 y x''' P => @lem307390 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307393 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307394 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x''' : type684 A) (P : A -> Prop) : (term905 A lt2 y x''' P) = (term904 A lt2 y x''' P).
Proof. exact (@lem307393 (term904 A lt2 y x''' P)). Qed.
Lemma lem307395 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term904 A lt2 y x''' P.
Proof. exact (EQ_MP (@lem307394 A lt2 y x''' P) (@lem307391 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307397 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : @I (A -> Prop) P x'.
Proof. exact (proj1 (@lem305879 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307398 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term883 A P x'.
Proof. exact (fun h0 : term719 A P x' => @lem307397 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307400 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307401 {A : Type'} (P : A -> Prop) (x' : A) : (term883 A P x') = (@I (A -> Prop) P x').
Proof. exact (@lem307400 (@I (A -> Prop) P x')). Qed.
Lemma lem307402 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : @I (A -> Prop) P x'.
Proof. exact (EQ_MP (@lem307401 A P x') (@lem307398 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307404 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term895 A _6786 x''' _6785.
Proof. exact (EQ_MP (@lem307329 A _6786 x''' _6785) (@lem307318 A _6785 _6786 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307405 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term895 A _6786 x''' _6785.
Proof. exact (@lem307404 A _6786 _6785 x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307406 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term895 A x' x''' P.
Proof. exact (@lem307405 A x' P x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307409 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term736 A x''' P.
Proof. exact (@lem307406 A x' P y x'' y' lt2 x''' h1 (@lem307402 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307410 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term896 A x''' P.
Proof. exact (fun h0 : term897 A x''' P => @lem307409 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307412 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307413 {A : Type'} (x''' : type684 A) (P : A -> Prop) : (term896 A x''' P) = (term736 A x''' P).
Proof. exact (@lem307412 (term736 A x''' P)). Qed.
Lemma lem307414 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term736 A x''' P.
Proof. exact (EQ_MP (@lem307413 A x''' P) (@lem307410 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307420 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem307421 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : (term880 A P y _6788) = (term907 A y P _6788).
Proof. exact (@lem307420 (term778 A P y _6788) (term719 A P _6788)). Qed.
Lemma lem307427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307428 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : (term908 A P y _6788) = (term909 A y P _6788).
Proof. exact (MK_COMB (@lem307427) (@lem307421 A y P _6788)). Qed.
Lemma lem307434 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : (term907 A y P _6788) = (term907 A y P _6788).
Proof. exact (eq_refl (term907 A y P _6788)). Qed.
Lemma lem307435 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : ((term880 A P y _6788) = (term907 A y P _6788)) = ((term907 A y P _6788) = (term907 A y P _6788)).
Proof. exact (MK_COMB (@lem307428 A y P _6788) (@lem307434 A y P _6788)). Qed.
Lemma lem307437 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem307438 (x : Prop) : (x = x) = True.
Proof. exact (@lem307437 Prop x). Qed.
Lemma lem307439 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : ((term907 A y P _6788) = (term907 A y P _6788)) = True.
Proof. exact (@lem307438 (term907 A y P _6788)). Qed.
Lemma lem307440 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : ((term880 A P y _6788) = (term907 A y P _6788)) = True.
Proof. exact (TRANS (@lem307435 A y P _6788) (@lem307439 A y P _6788)). Qed.
Lemma lem307441 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : True = ((term880 A P y _6788) = (term907 A y P _6788)).
Proof. exact (SYM (@lem307440 A y P _6788)). Qed.
Lemma lem307442 {A : Type'} (y : A -> A) (P : A -> Prop) (_6788 : A) : (term880 A P y _6788) = (term907 A y P _6788).
Proof. exact (EQ_MP (@lem307441 A y P _6788) (@lem0)). Qed.
Lemma lem307443 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term907 A y P _6788.
Proof. exact (EQ_MP (@lem307442 A y P _6788) (@lem306828 A _6788 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307445 (b : Prop) (a : Prop) : (a \/ b) = (term890 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem307446 {A : Type'} (P : A -> Prop) (y : A -> A) (_6788 : A) : (term907 A y P _6788) = (term910 A P y _6788).
Proof. exact (@lem307445 (term719 A P _6788) (term778 A P y _6788)). Qed.
Lemma lem307448 (a : Prop) : (term12 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem307449 {A : Type'} (P : A -> Prop) (_6788 : A) : (term892 A P _6788) = (@I (A -> Prop) P _6788).
Proof. exact (@lem307448 (@I (A -> Prop) P _6788)). Qed.
Lemma lem307450 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307451 {A : Type'} (P : A -> Prop) (_6788 : A) : (term893 A P _6788) = (term894 A P _6788).
Proof. exact (MK_COMB (@lem307450) (@lem307449 A P _6788)). Qed.
Lemma lem307452 {A : Type'} (P : A -> Prop) (y : A -> A) (_6788 : A) : (term778 A P y _6788) = (term778 A P y _6788).
Proof. exact (eq_refl (term778 A P y _6788)). Qed.
Lemma lem307453 {A : Type'} (P : A -> Prop) (y : A -> A) (_6788 : A) : (term910 A P y _6788) = (term911 A P y _6788).
Proof. exact (MK_COMB (@lem307451 A P _6788) (@lem307452 A P y _6788)). Qed.
Lemma lem307454 {A : Type'} (P : A -> Prop) (y : A -> A) (_6788 : A) : (term907 A y P _6788) = (term911 A P y _6788).
Proof. exact (TRANS (@lem307446 A P y _6788) (@lem307453 A P y _6788)). Qed.
Lemma lem307457 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term911 A P y _6788.
Proof. exact (EQ_MP (@lem307454 A P y _6788) (@lem307443 A _6788 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307458 {A : Type'} (_6788 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term911 A P y _6788.
Proof. exact (@lem307457 A _6788 x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307459 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term912 A y x''' P.
Proof. exact (@lem307458 A (@I ((A -> Prop) -> A) x''' P) x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307462 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term913 A y x''' P.
Proof. exact (@lem307459 A x' P y x'' y' lt2 x''' h1 (@lem307414 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307463 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term914 A y x''' P.
Proof. exact (fun h0 : term915 A y x''' P => @lem307462 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307465 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307466 {A : Type'} (y : A -> A) (x''' : type684 A) (P : A -> Prop) : (term914 A y x''' P) = (term913 A y x''' P).
Proof. exact (@lem307465 (term913 A y x''' P)). Qed.
Lemma lem307467 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term913 A y x''' P.
Proof. exact (EQ_MP (@lem307466 A y x''' P) (@lem307463 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307469 (a : Prop) (b : Prop) : (term916 a b) = (term917 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem307470 {A : Type'} (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) (_6787 : A) : (term729 A lt2 x''' _6785 _6787) = (term918 A lt2 x''' _6785 _6787).
Proof. exact (@lem307469 (term723 A lt2 _6787 x''' _6785) (@I (A -> Prop) _6785 _6787)). Qed.
Lemma lem307471 {A : Type'} (_6785 : A -> Prop) (_6786 : A) : (term762 A _6785 _6786) = (term762 A _6785 _6786).
Proof. exact (eq_refl (term762 A _6785 _6786)). Qed.
Lemma lem307472 {A : Type'} (_6786 : A) (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) (_6787 : A) : (term882 A _6786 lt2 x''' _6785 _6787) = (term919 A _6786 lt2 x''' _6785 _6787).
Proof. exact (MK_COMB (@lem307471 A _6785 _6786) (@lem307470 A lt2 x''' _6785 _6787)). Qed.
Lemma lem307474 (a : Prop) (b : Prop) : (term916 a b) = (term917 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem307475 {A : Type'} (_6786 : A) (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) (_6787 : A) : (term919 A _6786 lt2 x''' _6785 _6787) = (term920 A _6786 lt2 x''' _6785 _6787).
Proof. exact (@lem307474 (@I (A -> Prop) _6785 _6786) (term921 A lt2 x''' _6785 _6787)). Qed.
Lemma lem307476 {A : Type'} (_6786 : A) (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) (_6787 : A) : (term882 A _6786 lt2 x''' _6785 _6787) = (term920 A _6786 lt2 x''' _6785 _6787).
Proof. exact (TRANS (@lem307472 A _6786 lt2 x''' _6785 _6787) (@lem307475 A _6786 lt2 x''' _6785 _6787)). Qed.
Lemma lem307478 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem307479 {A : Type'} (_6786 : A) (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) (_6787 : A) : (term920 A _6786 lt2 x''' _6785 _6787) = (term922 A _6786 lt2 x''' _6785 _6787).
Proof. exact (@lem307478 (term923 A _6786 lt2 x''' _6785 _6787)). Qed.
Lemma lem307480 {A : Type'} (_6786 : A) (lt2 : type1402 A) (x''' : type684 A) (_6785 : A -> Prop) (_6787 : A) : (term882 A _6786 lt2 x''' _6785 _6787) = (term922 A _6786 lt2 x''' _6785 _6787).
Proof. exact (TRANS (@lem307476 A _6786 lt2 x''' _6785 _6787) (@lem307479 A _6786 lt2 x''' _6785 _6787)). Qed.
Lemma lem307482 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term924 A lt2 y x''' P.
Proof. exact (conj (@lem307395 A x' P y x'' y' lt2 x''' h1) (@lem307467 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307483 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term925 A x' lt2 y x''' P.
Proof. exact (conj (@lem307282 A x' P y x'' y' lt2 x''' h1) (@lem307482 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307485 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (_6787 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term922 A _6786 lt2 x''' _6785 _6787.
Proof. exact (EQ_MP (@lem307480 A _6786 lt2 x''' _6785 _6787) (@lem306844 A _6786 _6785 _6787 x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307486 {A : Type'} (_6786 : A) (_6785 : A -> Prop) (_6787 : A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term922 A _6786 lt2 x''' _6785 _6787.
Proof. exact (@lem307485 A _6786 _6785 _6787 x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307487 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term926 A x' lt2 y x''' P.
Proof. exact (@lem307486 A x' P (term927 A y x''' P) x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307490 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : False.
Proof. exact (@lem307487 A x' P y x'' y' lt2 x''' h1 (@lem307483 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307491 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : term886.
Proof. exact (fun h0 : ~ False => @lem307490 A x' P y x'' y' lt2 x''' h1). Qed.
Lemma lem307493 (p : Prop) : (term884 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem307494 : term886 = False.
Proof. exact (@lem307493 False). Qed.
Lemma lem307495 {A : Type'} (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term796 A x' P y x'' y' lt2 x''') : False.
Proof. exact (EQ_MP (@lem307494) (@lem307491 A x' P y x'' y' lt2 x''' h1)). Qed.
Lemma lem307496 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : (@I (A -> Prop) P x') = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) P x' => @lem307134 A x lt2 y P x' h1 h2 h3) (fun h4 : False => @lem306750 A P x' h3)). Qed.
Lemma lem307497 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307496 A x lt2 y P x' h1 h2 h3) (@lem306750 A P x' h3)). Qed.
Lemma lem307498 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : (@I (A -> Prop) P x') = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) P x' => @lem306889 A P x' h1 h2) (fun h3 : False => @lem306706 A P x' h2)). Qed.
Lemma lem307499 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307498 A P x' h1 h2) (@lem306706 A P x' h2)). Qed.
Lemma lem307500 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : (@I (A -> Prop) P x') = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) P x' => @lem307497 A x lt2 y P x' h1 h2 h3) (fun h4 : False => @lem306269 A P x' h3)). Qed.
Lemma lem307501 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307500 A x lt2 y P x' h1 h2 h3) (@lem306269 A P x' h3)). Qed.
Lemma lem307502 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : (@I (A -> Prop) P x') = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) P x' => @lem307499 A P x' h1 h2) (fun h3 : False => @lem306002 A P x' h2)). Qed.
Lemma lem307503 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307502 A P x' h1 h2) (@lem306002 A P x' h2)). Qed.
Lemma lem307504 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : (@I (A -> Prop) P x') = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) P x' => @lem307501 A x lt2 y P x' h1 h2 h3) (fun h4 : False => @lem306269 A P x' h3)). Qed.
Lemma lem307505 {A : Type'} (x : type684 A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) (h3 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307504 A x lt2 y P x' h1 h2 h3) (@lem306269 A P x' h3)). Qed.
Lemma lem307506 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term742 A P) (h2 : term806 A lt2 x' P) : (term742 A P) = False.
Proof. exact (prop_ext (fun h3 : term742 A P => @lem306914 A lt2 x' P h1 h2) (fun h3 : False => @lem306117 A P h1)). Qed.
Lemma lem307507 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term742 A P) (h2 : term806 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem307506 A lt2 x' P h1 h2) (@lem306117 A P h1)). Qed.
Lemma lem307508 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : (@I (A -> Prop) P x') = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) P x' => @lem307503 A P x' h1 h2) (fun h3 : False => @lem306002 A P x' h2)). Qed.
Lemma lem307509 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307508 A P x' h1 h2) (@lem306002 A P x' h2)). Qed.
Lemma lem307510 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : (term742 A P) = False.
Proof. exact (prop_ext (fun h3 : term742 A P => @lem307509 A P x' h1 h2) (fun h3 : False => @lem305998 A P h1)). Qed.
Lemma lem307511 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term742 A P) (h2 : @I (A -> Prop) P x') : False.
Proof. exact (EQ_MP (@lem307510 A P x' h1 h2) (@lem305998 A P h1)). Qed.
Lemma lem307512 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term792 A lt2 P y) (h2 : term812 A x x' lt2 P y) : False.
Proof. exact (or_elim (@lem305867 A x x' lt2 P y h2) (fun h0 : @I (A -> Prop) P x' => @lem307505 A x lt2 y P x' h1 h2 h0) (fun h0 : term806 A lt2 x' P => @lem307275 A y lt2 x' P h1 h0)). Qed.
Lemma lem307513 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term742 A P) (h2 : term812 A x x' lt2 P y) : False.
Proof. exact (or_elim (@lem305867 A x x' lt2 P y h2) (fun h0 : @I (A -> Prop) P x' => @lem307511 A P x' h1 h0) (fun h0 : term806 A lt2 x' P => @lem307507 A lt2 x' P h1 h0)). Qed.
Lemma lem307514 {A : Type'} (x : type684 A) (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term812 A x x' lt2 P y) : False.
Proof. exact (or_elim (@lem305866 A x x' lt2 P y h1) (fun h0 : term742 A P => @lem307513 A x x' lt2 P y h0 h1) (fun h0 : term792 A lt2 P y => @lem307512 A x x' lt2 P y h0 h1)). Qed.
Lemma lem307515 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (x''' : type684 A) (h1 : term703 A x x' P y x'' y' lt2 x''') : False.
Proof. exact (or_elim (@lem305861 A x x' P y x'' y' lt2 x''' h1) (fun h0 : term812 A x x' lt2 P y => @lem307514 A x x' lt2 P y h0) (fun h0 : term796 A x' P y x'' y' lt2 x''' => @lem307495 A x' P y x'' y' lt2 x''' h0)). Qed.
Lemma lem307516 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (y' : type670 A) (lt2 : type1402 A) (h1 : term706 A x x' P y x'' y' lt2) : False.
Proof. exact (ex_elim (@lem305389 A x x' P y x'' y' lt2 h1) (fun x''' : type684 A => fun h0 : term705 A x x' P y x'' y' lt2 x''' => @lem307515 A x x' P y x'' y' lt2 x''' h0)). Qed.
Lemma lem307517 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (x'' : type684 A) (lt2 : type1402 A) (h1 : term708 A x x' P y x'' lt2) : False.
Proof. exact (ex_elim (@lem305388 A x x' P y x'' lt2 h1) (fun y' : type670 A => fun h0 : term707 A x x' P y x'' lt2 y' => @lem307516 A x x' P y x'' y' lt2 h0)). Qed.
Lemma lem307518 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (y : A -> A) (lt2 : type1402 A) (h1 : term710 A x x' P y lt2) : False.
Proof. exact (ex_elim (@lem305387 A x x' P y lt2 h1) (fun x'' : type684 A => fun h0 : term709 A x x' P y lt2 x'' => @lem307517 A x x' P y x'' lt2 h0)). Qed.
Lemma lem307519 {A : Type'} (x : type684 A) (x' : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term712 A x x' P lt2) : False.
Proof. exact (ex_elim (@lem305386 A x x' P lt2 h1) (fun y : A -> A => fun h0 : term711 A x x' P lt2 y => @lem307518 A x x' P y lt2 h0)). Qed.
Lemma lem307520 {A : Type'} (x : type684 A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term714 A x P lt2) : False.
Proof. exact (ex_elim (@lem305385 A x P lt2 h1) (fun x' : A => fun h0 : term713 A x P lt2 x' => @lem307519 A x x' P lt2 h0)). Qed.
Lemma lem307521 {A : Type'} (x : type684 A) (lt2 : type1402 A) (h1 : term716 A x lt2) : False.
Proof. exact (ex_elim (@lem305384 A x lt2 h1) (fun P : A -> Prop => fun h0 : term715 A x lt2 P => @lem307520 A x P lt2 h0)). Qed.
Lemma lem307522 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : False.
Proof. exact (ex_elim (@lem305383 A lt2 h1) (fun x : type684 A => fun h0 : term717 A lt2 x => @lem307521 A x lt2 h0)). Qed.
Lemma lem307523 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : (term7 A lt2) = False.
Proof. exact (prop_ext (fun h2 : term7 A lt2 => @lem307522 A lt2 h1) (fun h2 : False => @lem303380 A lt2 h1)). Qed.
Lemma lem307524 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : False.
Proof. exact (EQ_MP (@lem307523 A lt2 h1) (@lem303380 A lt2 h1)). Qed.
Lemma lem307525 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (fun h0 : term7 A lt2 => @lem307524 A lt2 h0). Qed.
Lemma lem307526 {A : Type'} (lt2 : type1402 A) : (term1 A lt2) = (term4 A lt2).
Proof. exact (EQ_MP (@lem303379 A lt2) (@lem307525 A lt2)). Qed.
Lemma lem307531 {A : Type'} : term16 A.
Proof. exact (fun lt2 : type1402 A => @lem307526 A lt2). Qed.
Lemma lem307532 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem303375 A) (@lem307531 A)). Qed.
Lemma lem307533 {A : Type'} (lt2 : type1402 A) : term936 A lt2.
Proof. exact (@lem307532 A lt2). Qed.
Lemma lem307534 {A : Type'} (lt2 : type1402 A) : (term936 A lt2) = (term6 A lt2).
Proof. exact (eq_refl (term936 A lt2)). Qed.
Lemma lem307535 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (EQ_MP (@lem307534 A lt2) (@lem307533 A lt2)). Qed.
Lemma lem307537 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (@lem303135 A lt2 (@lem307535 A lt2)). Qed.
Lemma lem307538 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : False.
Proof. exact (@lem307537 A lt2 (@lem303119 A lt2 h1)). Qed.
Lemma lem307539 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : (term7 A lt2) = False.
Proof. exact (prop_ext (fun h2 : term7 A lt2 => @lem307538 A lt2 h1) (fun h2 : False => @lem303119 A lt2 h1)). Qed.
Lemma lem307540 {A : Type'} (lt2 : type1402 A) (h1 : term7 A lt2) : False.
Proof. exact (EQ_MP (@lem307539 A lt2 h1) (@lem303119 A lt2 h1)). Qed.
Lemma lem307541 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (fun h0 : term7 A lt2 => @lem307540 A lt2 h0). Qed.
Lemma lem307542 {A : Type'} (lt2 : type1402 A) : (term1 A lt2) = (term4 A lt2).
Proof. exact (EQ_MP (@lem303118 A lt2) (@lem307541 A lt2)). Qed.
Lemma lem307543 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term4 A lt2).
Proof. exact (EQ_MP (@lem303114 A lt2) (@lem307542 A lt2)). Qed.
