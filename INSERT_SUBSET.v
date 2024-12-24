Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3286114 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3286115 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3286114 A s t). Qed.
Lemma lem3286116 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term1 A x s t) = (term2 A x s t).
Proof. exact (@lem3286115 A (@INSERT A x s) t). Qed.
Lemma lem3286123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3286124 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term3 A x s t) = (term4 A x s t).
Proof. exact (MK_COMB (@lem3286123) (@lem3286116 A x s t)). Qed.
Lemma lem3286128 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3286129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3286128 A s t). Qed.
Lemma lem3286136 {A : Type'} (x : A) (t : A -> Prop) : (term5 A x t) = (term5 A x t).
Proof. exact (eq_refl (term5 A x t)). Qed.
Lemma lem3286137 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term6 A x s t) = (term7 A x s t).
Proof. exact (MK_COMB (@lem3286136 A x t) (@lem3286129 A s t)). Qed.
Lemma lem3286140 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term1 A x s t) = (term6 A x s t)) = ((term2 A x s t) = (term7 A x s t)).
Proof. exact (MK_COMB (@lem3286124 A x s t) (@lem3286137 A x s t)). Qed.
Lemma lem3286145 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term9 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3286140 A x s t)). Qed.
Lemma lem3286146 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3286147 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term11 A x s).
Proof. exact (MK_COMB (@lem3286146 A) (@lem3286145 A x s)). Qed.
Lemma lem3286152 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3286147 A x s)). Qed.
Lemma lem3286153 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3286154 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem3286153 A) (@lem3286152 A x)). Qed.
Lemma lem3286159 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (fun_ext (fun x : A => @lem3286154 A x)). Qed.
Lemma lem3286160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286161 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem3286160 A) (@lem3286159 A)). Qed.
Lemma lem3286166 {A : Type'} : (term19 A) = (term18 A).
Proof. exact (SYM (@lem3286161 A)). Qed.
Lemma lem3286188 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term20 A x y s) = (term21 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3286189 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term20 A x y s) = (term21 A y x s).
Proof. exact (@lem3286188 A y x s). Qed.
Lemma lem3286190 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term20 A x' x s) = (term21 A x x' s).
Proof. exact (@lem3286189 A x x' s). Qed.
Lemma lem3286196 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3286197 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3286196 A P x). Qed.
Lemma lem3286198 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3286197 A s x'). Qed.
Lemma lem3286199 {A : Type'} (x' : A) (x : A) : (term22 A x' x) = (term22 A x' x).
Proof. exact (eq_refl (term22 A x' x)). Qed.
Lemma lem3286200 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term21 A x x' s) = (term23 A x s x').
Proof. exact (MK_COMB (@lem3286199 A x' x) (@lem3286198 A s x')). Qed.
Lemma lem3286203 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term20 A x' x s) = (term23 A x s x').
Proof. exact (TRANS (@lem3286190 A x x' s) (@lem3286200 A x s x')). Qed.
Lemma lem3286204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3286205 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term24 A x' x s) = (term25 A x s x').
Proof. exact (MK_COMB (@lem3286204) (@lem3286203 A x s x')). Qed.
Lemma lem3286207 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3286208 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3286207 A P x). Qed.
Lemma lem3286209 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3286208 A t x'). Qed.
Lemma lem3286210 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term26 A x s x' t) = (term27 A x s t x').
Proof. exact (MK_COMB (@lem3286205 A x s x') (@lem3286209 A t x')). Qed.
Lemma lem3286213 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term28 A x s t) = (term29 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286210 A x s t x')). Qed.
Lemma lem3286214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286215 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term2 A x s t) = (term30 A x s t).
Proof. exact (MK_COMB (@lem3286214 A) (@lem3286213 A x s t)). Qed.
Lemma lem3286220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3286221 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term4 A x s t) = (term31 A x s t).
Proof. exact (MK_COMB (@lem3286220) (@lem3286215 A x s t)). Qed.
Lemma lem3286225 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3286226 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3286225 A P x). Qed.
Lemma lem3286227 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3286226 A t x). Qed.
Lemma lem3286228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3286229 {A : Type'} (t : A -> Prop) (x : A) : (term5 A x t) = (term32 A t x).
Proof. exact (MK_COMB (@lem3286228) (@lem3286227 A t x)). Qed.
Lemma lem3286237 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3286238 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3286237 A P x). Qed.
Lemma lem3286239 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3286238 A s x). Qed.
Lemma lem3286240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3286241 {A : Type'} (s : A -> Prop) (x : A) : (term33 A x s) = (term34 A s x).
Proof. exact (MK_COMB (@lem3286240) (@lem3286239 A s x)). Qed.
Lemma lem3286243 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3286244 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3286243 A P x). Qed.
Lemma lem3286245 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3286244 A t x). Qed.
Lemma lem3286246 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term35 A s x t) = (term36 A s t x).
Proof. exact (MK_COMB (@lem3286241 A s x) (@lem3286245 A t x)). Qed.
Lemma lem3286249 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term37 A s t) = (term38 A s t).
Proof. exact (fun_ext (fun x : A => @lem3286246 A s t x)). Qed.
Lemma lem3286250 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286251 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem3286250 A) (@lem3286249 A s t)). Qed.
Lemma lem3286256 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term7 A x s t) = (term40 A x s t).
Proof. exact (MK_COMB (@lem3286229 A t x) (@lem3286251 A s t)). Qed.
Lemma lem3286259 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term2 A x s t) = (term7 A x s t)) = ((term30 A x s t) = (term40 A x s t)).
Proof. exact (MK_COMB (@lem3286221 A x s t) (@lem3286256 A x s t)). Qed.
Lemma lem3286262 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term41 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3286259 A x s t)). Qed.
Lemma lem3286263 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3286264 {A : Type'} (x : A) (s : A -> Prop) : (term11 A x s) = (term42 A x s).
Proof. exact (MK_COMB (@lem3286263 A) (@lem3286262 A x s)). Qed.
Lemma lem3286269 {A : Type'} (x : A) : (term13 A x) = (term43 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3286264 A x s)). Qed.
Lemma lem3286270 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3286271 {A : Type'} (x : A) : (term15 A x) = (term44 A x).
Proof. exact (MK_COMB (@lem3286270 A) (@lem3286269 A x)). Qed.
Lemma lem3286276 {A : Type'} : (term17 A) = (term45 A).
Proof. exact (fun_ext (fun x : A => @lem3286271 A x)). Qed.
Lemma lem3286277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286278 {A : Type'} : (term19 A) = (term46 A).
Proof. exact (MK_COMB (@lem3286277 A) (@lem3286276 A)). Qed.
Lemma lem3286283 {A : Type'} : (term46 A) = (term19 A).
Proof. exact (SYM (@lem3286278 A)). Qed.
Lemma lem3286285 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3286286 {A : Type'} : (term46 A) = (term48 A).
Proof. exact (@lem3286285 (term46 A)). Qed.
Lemma lem3286287 {A : Type'} : (term48 A) = (term46 A).
Proof. exact (SYM (@lem3286286 A)). Qed.
Lemma lem3286288 {A : Type'} (h1 : term49 A) : term49 A.
Proof. exact (h1). Qed.
Lemma lem3286291 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3286292 {A : Type'} : term50 A.
Proof. exact (fun h0 : term48 A => @lem3286291 A h0). Qed.
Lemma lem3286293 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (h1). Qed.
Lemma lem3286294 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3286295 {A : Type'} (h1 : term48 A) (h2 : term50 A) : term48 A.
Proof. exact (@lem3286293 A h2 (@lem3286294 A h1)). Qed.
Lemma lem3286296 {A : Type'} (h1 : term48 A) : term51 A.
Proof. exact (fun h0 : term50 A => @lem3286295 A h1 h0). Qed.
Lemma lem3286297 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (h1). Qed.
Lemma lem3286298 {A : Type'} (h1 : term48 A) (h2 : term50 A) : term48 A.
Proof. exact (@lem3286296 A h1 (@lem3286297 A h2)). Qed.
Lemma lem3286299 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (fun h0 : term48 A => @lem3286298 A h0 h1). Qed.
Lemma lem3286300 {A : Type'} : term52 A.
Proof. exact (fun h0 : term50 A => @lem3286299 A h0). Qed.
Lemma lem3286303 {A : Type'} : term50 A.
Proof. exact (@lem3286300 A (@lem3286292 A)). Qed.
Lemma lem3286304 {A : Type'} : term50 A.
Proof. exact (@lem3286303 A). Qed.
Lemma lem3286306 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3286307 {A : Type'} : (term48 A) = (term53 A).
Proof. exact (@lem3286306 (term49 A)). Qed.
Lemma lem3286309 (t : Prop) : (term54 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3286310 {A : Type'} : (term53 A) = (term46 A).
Proof. exact (@lem3286309 (term46 A)). Qed.
Lemma lem3286343 {A : Type'} : (term48 A) = (term46 A).
Proof. exact (TRANS (@lem3286307 A) (@lem3286310 A)). Qed.
Lemma lem3286348 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term36 A s t x) = (term36 A s t x).
Proof. exact (eq_refl (term36 A s t x)). Qed.
Lemma lem3286349 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term38 A s t).
Proof. exact (fun_ext (fun x : A => @lem3286348 A s t x)). Qed.
Lemma lem3286350 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286351 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem3286350 A) (@lem3286349 A s t)). Qed.
Lemma lem3286354 {A : Type'} (t : A -> Prop) (x : A) : (term32 A t x) = (term32 A t x).
Proof. exact (eq_refl (term32 A t x)). Qed.
Lemma lem3286355 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term40 A x s t) = (term40 A x s t).
Proof. exact (MK_COMB (@lem3286354 A t x) (@lem3286351 A s t)). Qed.
Lemma lem3286364 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term27 A x s t x') = (term27 A x s t x').
Proof. exact (eq_refl (term27 A x s t x')). Qed.
Lemma lem3286365 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term29 A x s t) = (term29 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286364 A x s t x')). Qed.
Lemma lem3286366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286367 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term30 A x s t) = (term30 A x s t).
Proof. exact (MK_COMB (@lem3286366 A) (@lem3286365 A x s t)). Qed.
Lemma lem3286368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3286369 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term31 A x s t) = (term31 A x s t).
Proof. exact (MK_COMB (@lem3286368) (@lem3286367 A x s t)). Qed.
Lemma lem3286370 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term30 A x s t) = (term40 A x s t)) = ((term30 A x s t) = (term40 A x s t)).
Proof. exact (MK_COMB (@lem3286369 A x s t) (@lem3286355 A x s t)). Qed.
Lemma lem3286371 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term41 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3286370 A x s t)). Qed.
Lemma lem3286372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3286373 {A : Type'} (x : A) (s : A -> Prop) : (term42 A x s) = (term42 A x s).
Proof. exact (MK_COMB (@lem3286372 A) (@lem3286371 A x s)). Qed.
Lemma lem3286374 {A : Type'} (x : A) : (term43 A x) = (term43 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3286373 A x s)). Qed.
Lemma lem3286375 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3286376 {A : Type'} (x : A) : (term44 A x) = (term44 A x).
Proof. exact (MK_COMB (@lem3286375 A) (@lem3286374 A x)). Qed.
Lemma lem3286377 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (fun_ext (fun x : A => @lem3286376 A x)). Qed.
Lemma lem3286378 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286379 {A : Type'} : (term46 A) = (term46 A).
Proof. exact (MK_COMB (@lem3286378 A) (@lem3286377 A)). Qed.
Lemma lem3286420 {A : Type'} : (term48 A) = (term46 A).
Proof. exact (TRANS (@lem3286343 A) (@lem3286379 A)). Qed.
Lemma lem3286421 {A : Type'} : (term46 A) = (term48 A).
Proof. exact (SYM (@lem3286420 A)). Qed.
Lemma lem3286423 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3286424 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term30 A x s t) = (term40 A x s t)) = (term55 A x s t).
Proof. exact (@lem3286423 ((term30 A x s t) = (term40 A x s t))). Qed.
Lemma lem3286425 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term55 A x s t) = ((term30 A x s t) = (term40 A x s t)).
Proof. exact (SYM (@lem3286424 A x s t)). Qed.
Lemma lem3286426 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term56 A x s t) : term56 A x s t.
Proof. exact (h1). Qed.
Lemma lem3286435 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term57 A x s x') = (term58 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3286440 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (t x').
Proof. exact (eq_refl (t x')). Qed.
Lemma lem3286445 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term59 A x s t x') = (term60 A x s t x').
Proof. exact (@lem17362 (term23 A x s x') (t x')). Qed.
Lemma lem3286446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3286447 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term61 A x s x') = (term62 A x s x').
Proof. exact (MK_COMB (@lem3286446) (@lem3286435 A x s x')). Qed.
Lemma lem3286448 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term63 A x s t x') = (term64 A x s t x').
Proof. exact (MK_COMB (@lem3286447 A x s x') (@lem3286440 A t x')). Qed.
Lemma lem3286449 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term27 A x s t x') = (term63 A x s t x').
Proof. exact (@lem17265 (term23 A x s x') (t x')). Qed.
Lemma lem3286450 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term27 A x s t x') = (term64 A x s t x').
Proof. exact (TRANS (@lem3286449 A x s t x') (@lem3286448 A x s t x')). Qed.
Lemma lem3286451 {A : Type'} (P : A -> Prop) : (term65 A P) = (term66 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3286452 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term67 A x s t) = (term68 A x s t).
Proof. exact (@lem3286451 A (term29 A x s t)). Qed.
Lemma lem3286453 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term69 A x s t x') = (term27 A x s t x').
Proof. exact (eq_refl (term69 A x s t x')). Qed.
Lemma lem3286454 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3286455 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term70 A x s t x') = (term59 A x s t x').
Proof. exact (MK_COMB (@lem3286454) (@lem3286453 A x s t x')). Qed.
Lemma lem3286456 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term70 A x s t x') = (term60 A x s t x').
Proof. exact (TRANS (@lem3286455 A x s t x') (@lem3286445 A x s t x')). Qed.
Lemma lem3286457 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term71 A x s t) = (term72 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286456 A x s t x')). Qed.
Lemma lem3286458 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286459 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term68 A x s t) = (term73 A x s t).
Proof. exact (MK_COMB (@lem3286458 A) (@lem3286457 A x s t)). Qed.
Lemma lem3286460 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term67 A x s t) = (term73 A x s t).
Proof. exact (TRANS (@lem3286452 A x s t) (@lem3286459 A x s t)). Qed.
Lemma lem3286461 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term29 A x s t) = (term74 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286450 A x s t x')). Qed.
Lemma lem3286462 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286463 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term30 A x s t) = (term75 A x s t).
Proof. exact (MK_COMB (@lem3286462 A) (@lem3286461 A x s t)). Qed.
Lemma lem3286474 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term77 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3286479 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term36 A s t x) = (term78 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3286480 {A : Type'} (P : A -> Prop) : (term65 A P) = (term66 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3286481 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term80 A s t).
Proof. exact (@lem3286480 A (term38 A s t)). Qed.
Lemma lem3286482 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term81 A s t x) = (term36 A s t x).
Proof. exact (eq_refl (term81 A s t x)). Qed.
Lemma lem3286483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3286484 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term82 A s t x) = (term76 A s t x).
Proof. exact (MK_COMB (@lem3286483) (@lem3286482 A s t x)). Qed.
Lemma lem3286485 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term82 A s t x) = (term77 A s t x).
Proof. exact (TRANS (@lem3286484 A s t x) (@lem3286474 A s t x)). Qed.
Lemma lem3286486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3286485 A s t x)). Qed.
Lemma lem3286487 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286488 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3286487 A) (@lem3286486 A s t)). Qed.
Lemma lem3286489 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term85 A s t).
Proof. exact (TRANS (@lem3286481 A s t) (@lem3286488 A s t)). Qed.
Lemma lem3286490 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3286479 A s t x)). Qed.
Lemma lem3286491 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286492 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3286491 A) (@lem3286490 A s t)). Qed.
Lemma lem3286494 {A : Type'} (t : A -> Prop) (x : A) : (term88 A t x) = (term88 A t x).
Proof. exact (eq_refl (term88 A t x)). Qed.
Lemma lem3286495 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term89 A x s t) = (term90 A x s t).
Proof. exact (MK_COMB (@lem3286494 A t x) (@lem3286489 A s t)). Qed.
Lemma lem3286496 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term91 A x s t) = (term89 A x s t).
Proof. exact (@lem17045 (t x) (term39 A s t)). Qed.
Lemma lem3286497 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term91 A x s t) = (term90 A x s t).
Proof. exact (TRANS (@lem3286496 A x s t) (@lem3286495 A x s t)). Qed.
Lemma lem3286499 {A : Type'} (t : A -> Prop) (x : A) : (term32 A t x) = (term32 A t x).
Proof. exact (eq_refl (term32 A t x)). Qed.
Lemma lem3286500 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term40 A x s t) = (term92 A x s t).
Proof. exact (MK_COMB (@lem3286499 A t x) (@lem3286492 A s t)). Qed.
Lemma lem3286501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3286502 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term93 A x s t) = (term94 A x s t).
Proof. exact (MK_COMB (@lem3286501) (@lem3286460 A x s t)). Qed.
Lemma lem3286503 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term95 A x s t) = (term96 A x s t).
Proof. exact (MK_COMB (@lem3286502 A x s t) (@lem3286500 A x s t)). Qed.
Lemma lem3286504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3286505 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term97 A x s t) = (term98 A x s t).
Proof. exact (MK_COMB (@lem3286504) (@lem3286463 A x s t)). Qed.
Lemma lem3286506 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term99 A x s t) = (term100 A x s t).
Proof. exact (MK_COMB (@lem3286505 A x s t) (@lem3286497 A x s t)). Qed.
Lemma lem3286507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3286508 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term101 A x s t) = (term102 A x s t).
Proof. exact (MK_COMB (@lem3286507) (@lem3286506 A x s t)). Qed.
Lemma lem3286509 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term103 A x s t) = (term104 A x s t).
Proof. exact (MK_COMB (@lem3286508 A x s t) (@lem3286503 A x s t)). Qed.
Lemma lem3286510 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term103 A x s t).
Proof. exact (@lem17646 (term30 A x s t) (term40 A x s t)). Qed.
Lemma lem3286511 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term104 A x s t).
Proof. exact (TRANS (@lem3286510 A x s t) (@lem3286509 A x s t)). Qed.
Lemma lem3286654 {A : Type'} (P : Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3286655 {A : Type'} (P : Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (@lem3286654 A P Q). Qed.
Lemma lem3286656 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term107 A x s t) = (term108 A x s t).
Proof. exact (@lem3286655 A (term109 A t x) (term84 A s t)). Qed.
Lemma lem3286657 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term110 A s t x) = (term77 A s t x).
Proof. exact (eq_refl (term110 A s t x)). Qed.
Lemma lem3286658 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3286657 A s t x)). Qed.
Lemma lem3286659 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286660 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3286659 A) (@lem3286658 A s t)). Qed.
Lemma lem3286661 {A : Type'} (t : A -> Prop) (x : A) : (term88 A t x) = (term88 A t x).
Proof. exact (eq_refl (term88 A t x)). Qed.
Lemma lem3286662 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term107 A x s t) = (term90 A x s t).
Proof. exact (MK_COMB (@lem3286661 A t x) (@lem3286660 A s t)). Qed.
Lemma lem3286663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3286664 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term113 A x s t) = (term114 A x s t).
Proof. exact (MK_COMB (@lem3286663) (@lem3286662 A x s t)). Qed.
Lemma lem3286665 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term110 A s t x') = (term77 A s t x').
Proof. exact (eq_refl (term110 A s t x')). Qed.
Lemma lem3286666 {A : Type'} (t : A -> Prop) (x : A) : (term88 A t x) = (term88 A t x).
Proof. exact (eq_refl (term88 A t x)). Qed.
Lemma lem3286667 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term115 A x s t x') = (term116 A x s t x').
Proof. exact (MK_COMB (@lem3286666 A t x) (@lem3286665 A s t x')). Qed.
Lemma lem3286668 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term117 A x s t) = (term118 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286667 A x s t x')). Qed.
Lemma lem3286669 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286670 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term108 A x s t) = (term119 A x s t).
Proof. exact (MK_COMB (@lem3286669 A) (@lem3286668 A x s t)). Qed.
Lemma lem3286671 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term107 A x s t) = (term108 A x s t)) = ((term90 A x s t) = (term119 A x s t)).
Proof. exact (MK_COMB (@lem3286664 A x s t) (@lem3286670 A x s t)). Qed.
Lemma lem3286672 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term90 A x s t) = (term119 A x s t).
Proof. exact (EQ_MP (@lem3286671 A x s t) (@lem3286656 A x s t)). Qed.
Lemma lem3286673 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term98 A x s t) = (term98 A x s t).
Proof. exact (eq_refl (term98 A x s t)). Qed.
Lemma lem3286674 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term100 A x s t) = (term120 A x s t).
Proof. exact (MK_COMB (@lem3286673 A x s t) (@lem3286672 A x s t)). Qed.
Lemma lem3286676 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3286677 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem3286676 A P Q). Qed.
Lemma lem3286678 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term123 A x s t) = (term124 A x s t).
Proof. exact (@lem3286677 A (term75 A x s t) (term118 A x s t)). Qed.
Lemma lem3286679 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term125 A x s t x') = (term116 A x s t x').
Proof. exact (eq_refl (term125 A x s t x')). Qed.
Lemma lem3286680 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term126 A x s t) = (term118 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286679 A x s t x')). Qed.
Lemma lem3286681 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286682 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term127 A x s t) = (term119 A x s t).
Proof. exact (MK_COMB (@lem3286681 A) (@lem3286680 A x s t)). Qed.
Lemma lem3286683 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term98 A x s t) = (term98 A x s t).
Proof. exact (eq_refl (term98 A x s t)). Qed.
Lemma lem3286684 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term123 A x s t) = (term120 A x s t).
Proof. exact (MK_COMB (@lem3286683 A x s t) (@lem3286682 A x s t)). Qed.
Lemma lem3286685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3286686 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term128 A x s t) = (term129 A x s t).
Proof. exact (MK_COMB (@lem3286685) (@lem3286684 A x s t)). Qed.
Lemma lem3286687 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term125 A x s t x') = (term116 A x s t x').
Proof. exact (eq_refl (term125 A x s t x')). Qed.
Lemma lem3286688 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term98 A x s t) = (term98 A x s t).
Proof. exact (eq_refl (term98 A x s t)). Qed.
Lemma lem3286689 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term130 A x s t x') = (term131 A x s t x').
Proof. exact (MK_COMB (@lem3286688 A x s t) (@lem3286687 A x s t x')). Qed.
Lemma lem3286690 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term132 A x s t) = (term133 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286689 A x s t x')). Qed.
Lemma lem3286691 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286692 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term124 A x s t) = (term134 A x s t).
Proof. exact (MK_COMB (@lem3286691 A) (@lem3286690 A x s t)). Qed.
Lemma lem3286693 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term123 A x s t) = (term124 A x s t)) = ((term120 A x s t) = (term134 A x s t)).
Proof. exact (MK_COMB (@lem3286686 A x s t) (@lem3286692 A x s t)). Qed.
Lemma lem3286694 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term120 A x s t) = (term134 A x s t).
Proof. exact (EQ_MP (@lem3286693 A x s t) (@lem3286678 A x s t)). Qed.
Lemma lem3286695 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term100 A x s t) = (term134 A x s t).
Proof. exact (TRANS (@lem3286674 A x s t) (@lem3286694 A x s t)). Qed.
Lemma lem3286696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3286697 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term102 A x s t) = (term135 A x s t).
Proof. exact (MK_COMB (@lem3286696) (@lem3286695 A x s t)). Qed.
Lemma lem3286699 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3286700 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem3286699 A P Q). Qed.
Lemma lem3286701 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term138 A x s t) = (term139 A x s t).
Proof. exact (@lem3286700 A (term72 A x s t) (term92 A x s t)). Qed.
Lemma lem3286702 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term140 A x s t x') = (term60 A x s t x').
Proof. exact (eq_refl (term140 A x s t x')). Qed.
Lemma lem3286703 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term141 A x s t) = (term72 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286702 A x s t x')). Qed.
Lemma lem3286704 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286705 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term142 A x s t) = (term73 A x s t).
Proof. exact (MK_COMB (@lem3286704 A) (@lem3286703 A x s t)). Qed.
Lemma lem3286706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3286707 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term143 A x s t) = (term94 A x s t).
Proof. exact (MK_COMB (@lem3286706) (@lem3286705 A x s t)). Qed.
Lemma lem3286708 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term92 A x s t) = (term92 A x s t).
Proof. exact (eq_refl (term92 A x s t)). Qed.
Lemma lem3286709 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term138 A x s t) = (term96 A x s t).
Proof. exact (MK_COMB (@lem3286707 A x s t) (@lem3286708 A x s t)). Qed.
Lemma lem3286710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3286711 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term144 A x s t) = (term145 A x s t).
Proof. exact (MK_COMB (@lem3286710) (@lem3286709 A x s t)). Qed.
Lemma lem3286712 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term140 A x s t x') = (term60 A x s t x').
Proof. exact (eq_refl (term140 A x s t x')). Qed.
Lemma lem3286713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3286714 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term146 A x s t x') = (term147 A x s t x').
Proof. exact (MK_COMB (@lem3286713) (@lem3286712 A x s t x')). Qed.
Lemma lem3286715 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term92 A x s t) = (term92 A x s t).
Proof. exact (eq_refl (term92 A x s t)). Qed.
Lemma lem3286716 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term148 A x' x s t) = (term149 A x' x s t).
Proof. exact (MK_COMB (@lem3286714 A x s t x') (@lem3286715 A x s t)). Qed.
Lemma lem3286717 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term150 A x s t) = (term151 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286716 A x' x s t)). Qed.
Lemma lem3286718 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286719 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term139 A x s t) = (term152 A x s t).
Proof. exact (MK_COMB (@lem3286718 A) (@lem3286717 A x s t)). Qed.
Lemma lem3286720 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term138 A x s t) = (term139 A x s t)) = ((term96 A x s t) = (term152 A x s t)).
Proof. exact (MK_COMB (@lem3286711 A x s t) (@lem3286719 A x s t)). Qed.
Lemma lem3286721 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term96 A x s t) = (term152 A x s t).
Proof. exact (EQ_MP (@lem3286720 A x s t) (@lem3286701 A x s t)). Qed.
Lemma lem3286722 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term104 A x s t) = (term153 A x s t).
Proof. exact (MK_COMB (@lem3286697 A x s t) (@lem3286721 A x s t)). Qed.
Lemma lem3286724 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3286725 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (@lem3286724 A P Q). Qed.
Lemma lem3286726 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term156 A x s t) = (term157 A x s t).
Proof. exact (@lem3286725 A (term133 A x s t) (term151 A x s t)). Qed.
Lemma lem3286727 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term158 A x s t x') = (term131 A x s t x').
Proof. exact (eq_refl (term158 A x s t x')). Qed.
Lemma lem3286728 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term159 A x s t) = (term133 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286727 A x s t x')). Qed.
Lemma lem3286729 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286730 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term160 A x s t) = (term134 A x s t).
Proof. exact (MK_COMB (@lem3286729 A) (@lem3286728 A x s t)). Qed.
Lemma lem3286731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3286732 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term161 A x s t) = (term135 A x s t).
Proof. exact (MK_COMB (@lem3286731) (@lem3286730 A x s t)). Qed.
Lemma lem3286733 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term162 A x s t x') = (term149 A x' x s t).
Proof. exact (eq_refl (term162 A x s t x')). Qed.
Lemma lem3286734 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term163 A x s t) = (term151 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286733 A x' x s t)). Qed.
Lemma lem3286735 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286736 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term164 A x s t) = (term152 A x s t).
Proof. exact (MK_COMB (@lem3286735 A) (@lem3286734 A x s t)). Qed.
Lemma lem3286737 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term156 A x s t) = (term153 A x s t).
Proof. exact (MK_COMB (@lem3286732 A x s t) (@lem3286736 A x s t)). Qed.
Lemma lem3286738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3286739 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term165 A x s t) = (term166 A x s t).
Proof. exact (MK_COMB (@lem3286738) (@lem3286737 A x s t)). Qed.
Lemma lem3286740 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term158 A x s t x') = (term131 A x s t x').
Proof. exact (eq_refl (term158 A x s t x')). Qed.
Lemma lem3286741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3286742 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term167 A x s t x') = (term168 A x s t x').
Proof. exact (MK_COMB (@lem3286741) (@lem3286740 A x s t x')). Qed.
Lemma lem3286743 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term162 A x s t x') = (term149 A x' x s t).
Proof. exact (eq_refl (term162 A x s t x')). Qed.
Lemma lem3286744 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term169 A x s t x') = (term170 A x' x s t).
Proof. exact (MK_COMB (@lem3286742 A x s t x') (@lem3286743 A x' x s t)). Qed.
Lemma lem3286745 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term171 A x s t) = (term172 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286744 A x' x s t)). Qed.
Lemma lem3286746 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3286747 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term157 A x s t) = (term173 A x s t).
Proof. exact (MK_COMB (@lem3286746 A) (@lem3286745 A x s t)). Qed.
Lemma lem3286748 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term156 A x s t) = (term157 A x s t)) = ((term153 A x s t) = (term173 A x s t)).
Proof. exact (MK_COMB (@lem3286739 A x s t) (@lem3286747 A x s t)). Qed.
Lemma lem3286749 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term153 A x s t) = (term173 A x s t).
Proof. exact (EQ_MP (@lem3286748 A x s t) (@lem3286726 A x s t)). Qed.
Lemma lem3286751 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term104 A x s t) = (term173 A x s t).
Proof. exact (TRANS (@lem3286722 A x s t) (@lem3286749 A x s t)). Qed.
Lemma lem3286752 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term173 A x s t).
Proof. exact (TRANS (@lem3286511 A x s t) (@lem3286751 A x s t)). Qed.
Lemma lem3286753 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term56 A x s t) : term173 A x s t.
Proof. exact (EQ_MP (@lem3286752 A x s t) (@lem3286426 A x s t h1)). Qed.
Lemma lem3286754 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x' x s t) : term170 A x' x s t.
Proof. exact (h1). Qed.
Lemma lem3286765 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term78 A s t x) = (term78 A s t x).
Proof. exact (eq_refl (term78 A s t x)). Qed.
Lemma lem3286766 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3286765 A s t x)). Qed.
Lemma lem3286767 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286768 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3286767 A) (@lem3286766 A s t)). Qed.
Lemma lem3286773 {A : Type'} (t : A -> Prop) (x : A) : (term32 A t x) = (term32 A t x).
Proof. exact (eq_refl (term32 A t x)). Qed.
Lemma lem3286774 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term92 A x s t) = (term92 A x s t).
Proof. exact (MK_COMB (@lem3286773 A t x) (@lem3286768 A s t)). Qed.
Lemma lem3286795 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term147 A x s t x') = (term147 A x s t x').
Proof. exact (eq_refl (term147 A x s t x')). Qed.
Lemma lem3286796 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term149 A x' x s t) = (term149 A x' x s t).
Proof. exact (MK_COMB (@lem3286795 A x s t x') (@lem3286774 A x s t)). Qed.
Lemma lem3286815 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term116 A x s t x') = (term116 A x s t x').
Proof. exact (eq_refl (term116 A x s t x')). Qed.
Lemma lem3286836 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term64 A x s t x') = (term64 A x s t x').
Proof. exact (eq_refl (term64 A x s t x')). Qed.
Lemma lem3286837 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term74 A x s t) = (term74 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286836 A x s t x')). Qed.
Lemma lem3286838 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286839 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term75 A x s t) = (term75 A x s t).
Proof. exact (MK_COMB (@lem3286838 A) (@lem3286837 A x s t)). Qed.
Lemma lem3286840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3286841 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term98 A x s t) = (term98 A x s t).
Proof. exact (MK_COMB (@lem3286840) (@lem3286839 A x s t)). Qed.
Lemma lem3286842 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term131 A x s t x') = (term131 A x s t x').
Proof. exact (MK_COMB (@lem3286841 A x s t) (@lem3286815 A x s t x')). Qed.
Lemma lem3286843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3286844 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term168 A x s t x') = (term168 A x s t x').
Proof. exact (MK_COMB (@lem3286843) (@lem3286842 A x s t x')). Qed.
Lemma lem3286845 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term170 A x' x s t) = (term170 A x' x s t).
Proof. exact (MK_COMB (@lem3286844 A x s t x') (@lem3286796 A x' x s t)). Qed.
Lemma lem3286846 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x' x s t) : term170 A x' x s t.
Proof. exact (EQ_MP (@lem3286845 A x' x s t) (@lem3286754 A x' x s t h1)). Qed.
Lemma lem3286847 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term131 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3286848 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term149 A x' x s t.
Proof. exact (h1). Qed.
Lemma lem3286849 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term116 A x s t x'.
Proof. exact (proj2 (@lem3286847 A x s t x' h1)). Qed.
Lemma lem3286850 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term75 A x s t.
Proof. exact (proj1 (@lem3286847 A x s t x' h1)). Qed.
Lemma lem3286852 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term77 A s t x') : term77 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3286855 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term92 A x s t.
Proof. exact (proj2 (@lem3286848 A x' x s t h1)). Qed.
Lemma lem3286856 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term60 A x s t x'.
Proof. exact (proj1 (@lem3286848 A x' x s t h1)). Qed.
Lemma lem3286857 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term87 A s t.
Proof. exact (proj2 (@lem3286855 A x' x s t h1)). Qed.
Lemma lem3286860 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term23 A x s x'.
Proof. exact (proj1 (@lem3286856 A x' x s t h1)). Qed.
Lemma lem3286880 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term64 A x s t x') = (term174 A x s t x').
Proof. exact (@lem19699 (term175 A x' x) (term109 A s x') (t x')). Qed.
Lemma lem3286881 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term74 A x s t) = (term176 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286880 A x s t x')). Qed.
Lemma lem3286882 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286884 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term75 A x s t) = (term177 A x s t).
Proof. exact (MK_COMB (@lem3286882 A) (@lem3286881 A x s t)). Qed.
Lemma lem3286885 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term177 A x s t.
Proof. exact (EQ_MP (@lem3286884 A x s t) (@lem3286850 A x s t x' h1)). Qed.
Lemma lem3286889 {A : Type'} (t : A -> Prop) (x : A) (h1 : term109 A t x) : term109 A t x.
Proof. exact (h1). Qed.
Lemma lem3286907 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term64 A x s t x') = (term174 A x s t x').
Proof. exact (@lem19699 (term175 A x' x) (term109 A s x') (t x')). Qed.
Lemma lem3286908 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term74 A x s t) = (term176 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3286907 A x s t x')). Qed.
Lemma lem3286909 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286911 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term75 A x s t) = (term177 A x s t).
Proof. exact (MK_COMB (@lem3286909 A) (@lem3286908 A x s t)). Qed.
Lemma lem3286912 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term177 A x s t.
Proof. exact (EQ_MP (@lem3286911 A x s t) (@lem3286850 A x s t x' h1)). Qed.
Lemma lem3286945 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3286957 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term78 A s t x) = (term78 A s t x).
Proof. exact (eq_refl (term78 A s t x)). Qed.
Lemma lem3286958 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3286957 A s t x)). Qed.
Lemma lem3286959 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3286961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3286959 A) (@lem3286958 A s t)). Qed.
Lemma lem3286962 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term87 A s t.
Proof. exact (EQ_MP (@lem3286961 A s t) (@lem3286857 A x' x s t h1)). Qed.
Lemma lem3286970 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3286971 {A : Type'} (_33794 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term178 A x s t _33794.
Proof. exact (@lem3286885 A x s t x' h1 _33794). Qed.
Lemma lem3286972 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_33794 : A) : (term178 A x s t _33794) = (term174 A x s t _33794).
Proof. exact (eq_refl (term178 A x s t _33794)). Qed.
Lemma lem3286973 {A : Type'} (_33794 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term174 A x s t _33794.
Proof. exact (EQ_MP (@lem3286972 A x s t _33794) (@lem3286971 A _33794 x s t x' h1)). Qed.
Lemma lem3286974 {A : Type'} (_33795 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term178 A x s t _33795.
Proof. exact (@lem3286912 A x s t x' h1 _33795). Qed.
Lemma lem3286975 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_33795 : A) : (term178 A x s t _33795) = (term174 A x s t _33795).
Proof. exact (eq_refl (term178 A x s t _33795)). Qed.
Lemma lem3286976 {A : Type'} (_33795 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term174 A x s t _33795.
Proof. exact (EQ_MP (@lem3286975 A x s t _33795) (@lem3286974 A _33795 x s t x' h1)). Qed.
Lemma lem3286980 {A : Type'} (_33797 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term179 A s t _33797.
Proof. exact (@lem3286962 A x' x s t h1 _33797). Qed.
Lemma lem3286981 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33797 : A) : (term179 A s t _33797) = (term78 A s t _33797).
Proof. exact (eq_refl (term179 A s t _33797)). Qed.
Lemma lem3286988 {A : Type'} (t : A -> Prop) (x : A) (h1 : term109 A t x) : term109 A t x.
Proof. exact (h1). Qed.
Lemma lem3286994 {A : Type'} (_33794 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term180 A x t _33794.
Proof. exact (proj1 (@lem3286973 A _33794 x s t x' h1)). Qed.
Lemma lem3287004 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term77 A s t x') : term109 A t x'.
Proof. exact (proj2 (@lem3286852 A s t x' h1)). Qed.
Lemma lem3287016 {A : Type'} (_33795 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term78 A s t _33795.
Proof. exact (proj2 (@lem3286976 A _33795 x s t x' h1)). Qed.
Lemma lem3287026 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term109 A t x'.
Proof. exact (proj2 (@lem3286856 A x' x s t h1)). Qed.
Lemma lem3287028 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3287036 {A : Type'} (_33797 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term78 A s t _33797.
Proof. exact (EQ_MP (@lem3286981 A s t _33797) (@lem3286980 A _33797 x' x s t h1)). Qed.
Lemma lem3287038 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term109 A t x'.
Proof. exact (proj2 (@lem3286856 A x' x s t h1)). Qed.
Lemma lem3287040 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3287083 {A : Type'} (t : A -> Prop) : (term181 A t) = (term181 A t).
Proof. exact (eq_refl (term181 A t)). Qed.
Lemma lem3287084 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term182 A t x') = (term182 A t x).
Proof. exact (MK_COMB (@lem3287083 A t) (@lem3287028 A x' x h1)). Qed.
Lemma lem3287085 {A : Type'} (t : A -> Prop) (x : A) : (term182 A t x) = (term109 A t x).
Proof. exact (eq_refl (term182 A t x)). Qed.
Lemma lem3287086 {A : Type'} (t : A -> Prop) (x' : A) : (term183 A t x') = (term183 A t x').
Proof. exact (eq_refl (term183 A t x')). Qed.
Lemma lem3287087 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term182 A t x') = (term182 A t x)) = ((term182 A t x') = (term109 A t x)).
Proof. exact (MK_COMB (@lem3287086 A t x') (@lem3287085 A t x)). Qed.
Lemma lem3287088 {A : Type'} (t : A -> Prop) (x' : A) : (term182 A t x') = (term109 A t x').
Proof. exact (eq_refl (term182 A t x')). Qed.
Lemma lem3287089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3287090 {A : Type'} (t : A -> Prop) (x' : A) : (term183 A t x') = (term184 A t x').
Proof. exact (MK_COMB (@lem3287089) (@lem3287088 A t x')). Qed.
Lemma lem3287091 {A : Type'} (t : A -> Prop) (x : A) : (term109 A t x) = (term109 A t x).
Proof. exact (eq_refl (term109 A t x)). Qed.
Lemma lem3287092 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term182 A t x') = (term109 A t x)) = ((term109 A t x') = (term109 A t x)).
Proof. exact (MK_COMB (@lem3287090 A t x') (@lem3287091 A t x)). Qed.
Lemma lem3287093 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term182 A t x') = (term182 A t x)) = ((term109 A t x') = (term109 A t x)).
Proof. exact (TRANS (@lem3287087 A x' t x) (@lem3287092 A x' t x)). Qed.
Lemma lem3287094 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term109 A t x') = (term109 A t x).
Proof. exact (EQ_MP (@lem3287093 A x' t x) (@lem3287084 A t x' x h1)). Qed.
Lemma lem3287095 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : term109 A t x.
Proof. exact (EQ_MP (@lem3287094 A t x' x h2) (@lem3287026 A x' x s t h1)). Qed.
Lemma lem3287123 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3287124 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3287123 A x). Qed.
Lemma lem3287125 {A : Type'} (x : A) : term185 A x.
Proof. exact (fun h0 : term186 A x => @lem3287124 A x). Qed.
Lemma lem3287127 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287128 {A : Type'} (x : A) : (term185 A x) = (x = x).
Proof. exact (@lem3287127 (x = x)). Qed.
Lemma lem3287129 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3287128 A x) (@lem3287125 A x)). Qed.
Lemma lem3287135 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3287136 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : (term180 A x t _33794) = (term188 A t _33794 x).
Proof. exact (@lem3287135 (t _33794) (term175 A _33794 x)). Qed.
Lemma lem3287144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3287145 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : (term189 A x t _33794) = (term190 A t _33794 x).
Proof. exact (MK_COMB (@lem3287144) (@lem3287136 A t _33794 x)). Qed.
Lemma lem3287153 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : (term188 A t _33794 x) = (term188 A t _33794 x).
Proof. exact (eq_refl (term188 A t _33794 x)). Qed.
Lemma lem3287154 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : ((term180 A x t _33794) = (term188 A t _33794 x)) = ((term188 A t _33794 x) = (term188 A t _33794 x)).
Proof. exact (MK_COMB (@lem3287145 A t _33794 x) (@lem3287153 A t _33794 x)). Qed.
Lemma lem3287156 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3287157 (x : Prop) : (x = x) = True.
Proof. exact (@lem3287156 Prop x). Qed.
Lemma lem3287158 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : ((term188 A t _33794 x) = (term188 A t _33794 x)) = True.
Proof. exact (@lem3287157 (term188 A t _33794 x)). Qed.
Lemma lem3287159 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : ((term180 A x t _33794) = (term188 A t _33794 x)) = True.
Proof. exact (TRANS (@lem3287154 A t _33794 x) (@lem3287158 A t _33794 x)). Qed.
Lemma lem3287160 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : True = ((term180 A x t _33794) = (term188 A t _33794 x)).
Proof. exact (SYM (@lem3287159 A t _33794 x)). Qed.
Lemma lem3287161 {A : Type'} (t : A -> Prop) (_33794 : A) (x : A) : (term180 A x t _33794) = (term188 A t _33794 x).
Proof. exact (EQ_MP (@lem3287160 A t _33794 x) (@lem0)). Qed.
Lemma lem3287162 {A : Type'} (_33794 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term188 A t _33794 x.
Proof. exact (EQ_MP (@lem3287161 A t _33794 x) (@lem3286994 A _33794 x s t x' h1)). Qed.
Lemma lem3287164 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3287165 {A : Type'} (x : A) (t : A -> Prop) (_33794 : A) : (term188 A t _33794 x) = (term192 A x t _33794).
Proof. exact (@lem3287164 (term175 A _33794 x) (t _33794)). Qed.
Lemma lem3287167 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3287168 {A : Type'} (_33794 : A) (x : A) : (term193 A _33794 x) = (_33794 = x).
Proof. exact (@lem3287167 (_33794 = x)). Qed.
Lemma lem3287169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3287170 {A : Type'} (_33794 : A) (x : A) : (term194 A _33794 x) = (term195 A _33794 x).
Proof. exact (MK_COMB (@lem3287169) (@lem3287168 A _33794 x)). Qed.
Lemma lem3287171 {A : Type'} (t : A -> Prop) (_33794 : A) : (t _33794) = (t _33794).
Proof. exact (eq_refl (t _33794)). Qed.
Lemma lem3287172 {A : Type'} (x : A) (t : A -> Prop) (_33794 : A) : (term192 A x t _33794) = (term196 A x t _33794).
Proof. exact (MK_COMB (@lem3287170 A _33794 x) (@lem3287171 A t _33794)). Qed.
Lemma lem3287173 {A : Type'} (x : A) (t : A -> Prop) (_33794 : A) : (term188 A t _33794 x) = (term196 A x t _33794).
Proof. exact (TRANS (@lem3287165 A x t _33794) (@lem3287172 A x t _33794)). Qed.
Lemma lem3287176 {A : Type'} (_33794 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term196 A x t _33794.
Proof. exact (EQ_MP (@lem3287173 A x t _33794) (@lem3287162 A _33794 x s t x' h1)). Qed.
Lemma lem3287177 {A : Type'} (_33794 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term196 A x t _33794.
Proof. exact (@lem3287176 A _33794 x s t x' h1). Qed.
Lemma lem3287178 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term197 A t x.
Proof. exact (@lem3287177 A x x s t x' h1). Qed.
Lemma lem3287181 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : t x.
Proof. exact (@lem3287178 A x s t x' h1 (@lem3287129 A x)). Qed.
Lemma lem3287182 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term198 A t x.
Proof. exact (fun h0 : term109 A t x => @lem3287181 A x s t x' h1). Qed.
Lemma lem3287184 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287185 {A : Type'} (t : A -> Prop) (x : A) : (term198 A t x) = (t x).
Proof. exact (@lem3287184 (t x)). Qed.
Lemma lem3287186 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : t x.
Proof. exact (EQ_MP (@lem3287185 A t x) (@lem3287182 A x s t x' h1)). Qed.
Lemma lem3287189 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3287191 {A : Type'} (t : A -> Prop) (x : A) : (term109 A t x) = (term199 A t x).
Proof. exact (@lem3287189 (t x)). Qed.
Lemma lem3287194 {A : Type'} (t : A -> Prop) (x : A) (h1 : term109 A t x) : term199 A t x.
Proof. exact (EQ_MP (@lem3287191 A t x) (@lem3286988 A t x h1)). Qed.
Lemma lem3287197 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : False.
Proof. exact (@lem3287194 A t x h1 (@lem3287186 A x s t x' h2)). Qed.
Lemma lem3287198 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : term200.
Proof. exact (fun h0 : ~ False => @lem3287197 A x s t x' h1 h2). Qed.
Lemma lem3287200 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287201 : term200 = False.
Proof. exact (@lem3287200 False). Qed.
Lemma lem3287202 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : False.
Proof. exact (EQ_MP (@lem3287201) (@lem3287198 A x s t x' h1 h2)). Qed.
Lemma lem3287230 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term77 A s t x') : s x'.
Proof. exact (proj1 (@lem3286852 A s t x' h1)). Qed.
Lemma lem3287231 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term77 A s t x') : term198 A s x'.
Proof. exact (fun h0 : term109 A s x' => @lem3287230 A s t x' h1). Qed.
Lemma lem3287233 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287234 {A : Type'} (s : A -> Prop) (x' : A) : (term198 A s x') = (s x').
Proof. exact (@lem3287233 (s x')). Qed.
Lemma lem3287235 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term77 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3287234 A s x') (@lem3287231 A s t x' h1)). Qed.
Lemma lem3287241 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3287242 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : (term78 A s t _33795) = (term201 A t s _33795).
Proof. exact (@lem3287241 (t _33795) (term109 A s _33795)). Qed.
Lemma lem3287248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3287249 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : (term202 A s t _33795) = (term203 A t s _33795).
Proof. exact (MK_COMB (@lem3287248) (@lem3287242 A t s _33795)). Qed.
Lemma lem3287255 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : (term201 A t s _33795) = (term201 A t s _33795).
Proof. exact (eq_refl (term201 A t s _33795)). Qed.
Lemma lem3287256 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : ((term78 A s t _33795) = (term201 A t s _33795)) = ((term201 A t s _33795) = (term201 A t s _33795)).
Proof. exact (MK_COMB (@lem3287249 A t s _33795) (@lem3287255 A t s _33795)). Qed.
Lemma lem3287258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3287259 (x : Prop) : (x = x) = True.
Proof. exact (@lem3287258 Prop x). Qed.
Lemma lem3287260 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : ((term201 A t s _33795) = (term201 A t s _33795)) = True.
Proof. exact (@lem3287259 (term201 A t s _33795)). Qed.
Lemma lem3287261 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : ((term78 A s t _33795) = (term201 A t s _33795)) = True.
Proof. exact (TRANS (@lem3287256 A t s _33795) (@lem3287260 A t s _33795)). Qed.
Lemma lem3287262 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : True = ((term78 A s t _33795) = (term201 A t s _33795)).
Proof. exact (SYM (@lem3287261 A t s _33795)). Qed.
Lemma lem3287263 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33795 : A) : (term78 A s t _33795) = (term201 A t s _33795).
Proof. exact (EQ_MP (@lem3287262 A t s _33795) (@lem0)). Qed.
Lemma lem3287264 {A : Type'} (_33795 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term201 A t s _33795.
Proof. exact (EQ_MP (@lem3287263 A t s _33795) (@lem3287016 A _33795 x s t x' h1)). Qed.
Lemma lem3287266 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3287267 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33795 : A) : (term201 A t s _33795) = (term204 A s t _33795).
Proof. exact (@lem3287266 (term109 A s _33795) (t _33795)). Qed.
Lemma lem3287269 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3287270 {A : Type'} (s : A -> Prop) (_33795 : A) : (term205 A s _33795) = (s _33795).
Proof. exact (@lem3287269 (s _33795)). Qed.
Lemma lem3287271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3287272 {A : Type'} (s : A -> Prop) (_33795 : A) : (term206 A s _33795) = (term34 A s _33795).
Proof. exact (MK_COMB (@lem3287271) (@lem3287270 A s _33795)). Qed.
Lemma lem3287273 {A : Type'} (t : A -> Prop) (_33795 : A) : (t _33795) = (t _33795).
Proof. exact (eq_refl (t _33795)). Qed.
Lemma lem3287274 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33795 : A) : (term204 A s t _33795) = (term36 A s t _33795).
Proof. exact (MK_COMB (@lem3287272 A s _33795) (@lem3287273 A t _33795)). Qed.
Lemma lem3287275 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33795 : A) : (term201 A t s _33795) = (term36 A s t _33795).
Proof. exact (TRANS (@lem3287267 A s t _33795) (@lem3287274 A s t _33795)). Qed.
Lemma lem3287278 {A : Type'} (_33795 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term36 A s t _33795.
Proof. exact (EQ_MP (@lem3287275 A s t _33795) (@lem3287264 A _33795 x s t x' h1)). Qed.
Lemma lem3287279 {A : Type'} (_33795 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term36 A s t _33795.
Proof. exact (@lem3287278 A _33795 x s t x' h1). Qed.
Lemma lem3287280 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term36 A s t x'.
Proof. exact (@lem3287279 A x' x s t x' h1). Qed.
Lemma lem3287283 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') (h2 : term77 A s t x') : t x'.
Proof. exact (@lem3287280 A x s t x' h1 (@lem3287235 A s t x' h2)). Qed.
Lemma lem3287284 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') (h2 : term77 A s t x') : term198 A t x'.
Proof. exact (fun h0 : term109 A t x' => @lem3287283 A x s t x' h1 h2). Qed.
Lemma lem3287286 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287287 {A : Type'} (t : A -> Prop) (x' : A) : (term198 A t x') = (t x').
Proof. exact (@lem3287286 (t x')). Qed.
Lemma lem3287288 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') (h2 : term77 A s t x') : t x'.
Proof. exact (EQ_MP (@lem3287287 A t x') (@lem3287284 A x s t x' h1 h2)). Qed.
Lemma lem3287291 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3287293 {A : Type'} (t : A -> Prop) (x' : A) : (term109 A t x') = (term199 A t x').
Proof. exact (@lem3287291 (t x')). Qed.
Lemma lem3287296 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term77 A s t x') : term199 A t x'.
Proof. exact (EQ_MP (@lem3287293 A t x') (@lem3287004 A s t x' h1)). Qed.
Lemma lem3287299 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') (h2 : term77 A s t x') : False.
Proof. exact (@lem3287296 A s t x' h2 (@lem3287288 A x s t x' h1 h2)). Qed.
Lemma lem3287300 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') (h2 : term77 A s t x') : term200.
Proof. exact (fun h0 : ~ False => @lem3287299 A x s t x' h1 h2). Qed.
Lemma lem3287302 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287303 : term200 = False.
Proof. exact (@lem3287302 False). Qed.
Lemma lem3287304 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') (h2 : term77 A s t x') : False.
Proof. exact (EQ_MP (@lem3287303) (@lem3287300 A x s t x' h1 h2)). Qed.
Lemma lem3287306 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : t x.
Proof. exact (proj1 (@lem3286855 A x' x s t h1)). Qed.
Lemma lem3287307 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term198 A t x.
Proof. exact (fun h0 : term109 A t x => @lem3287306 A x' x s t h1). Qed.
Lemma lem3287309 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287310 {A : Type'} (t : A -> Prop) (x : A) : (term198 A t x) = (t x).
Proof. exact (@lem3287309 (t x)). Qed.
Lemma lem3287311 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : t x.
Proof. exact (EQ_MP (@lem3287310 A t x) (@lem3287307 A x' x s t h1)). Qed.
Lemma lem3287314 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3287316 {A : Type'} (t : A -> Prop) (x : A) : (term109 A t x) = (term199 A t x).
Proof. exact (@lem3287314 (t x)). Qed.
Lemma lem3287319 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : term199 A t x.
Proof. exact (EQ_MP (@lem3287316 A t x) (@lem3287095 A s t x' x h1 h2)). Qed.
Lemma lem3287322 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : False.
Proof. exact (@lem3287319 A s t x' x h1 h2 (@lem3287311 A x' x s t h1)). Qed.
Lemma lem3287323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : term200.
Proof. exact (fun h0 : ~ False => @lem3287322 A s t x' x h1 h2). Qed.
Lemma lem3287325 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287326 : term200 = False.
Proof. exact (@lem3287325 False). Qed.
Lemma lem3287329 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3287330 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term198 A s x'.
Proof. exact (fun h0 : term109 A s x' => @lem3287329 A s x' h1). Qed.
Lemma lem3287332 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287333 {A : Type'} (s : A -> Prop) (x' : A) : (term198 A s x') = (s x').
Proof. exact (@lem3287332 (s x')). Qed.
Lemma lem3287334 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3287333 A s x') (@lem3287330 A s x' h1)). Qed.
Lemma lem3287340 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3287341 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : (term78 A s t _33797) = (term201 A t s _33797).
Proof. exact (@lem3287340 (t _33797) (term109 A s _33797)). Qed.
Lemma lem3287347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3287348 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : (term202 A s t _33797) = (term203 A t s _33797).
Proof. exact (MK_COMB (@lem3287347) (@lem3287341 A t s _33797)). Qed.
Lemma lem3287354 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : (term201 A t s _33797) = (term201 A t s _33797).
Proof. exact (eq_refl (term201 A t s _33797)). Qed.
Lemma lem3287355 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : ((term78 A s t _33797) = (term201 A t s _33797)) = ((term201 A t s _33797) = (term201 A t s _33797)).
Proof. exact (MK_COMB (@lem3287348 A t s _33797) (@lem3287354 A t s _33797)). Qed.
Lemma lem3287357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3287358 (x : Prop) : (x = x) = True.
Proof. exact (@lem3287357 Prop x). Qed.
Lemma lem3287359 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : ((term201 A t s _33797) = (term201 A t s _33797)) = True.
Proof. exact (@lem3287358 (term201 A t s _33797)). Qed.
Lemma lem3287360 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : ((term78 A s t _33797) = (term201 A t s _33797)) = True.
Proof. exact (TRANS (@lem3287355 A t s _33797) (@lem3287359 A t s _33797)). Qed.
Lemma lem3287361 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : True = ((term78 A s t _33797) = (term201 A t s _33797)).
Proof. exact (SYM (@lem3287360 A t s _33797)). Qed.
Lemma lem3287362 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33797 : A) : (term78 A s t _33797) = (term201 A t s _33797).
Proof. exact (EQ_MP (@lem3287361 A t s _33797) (@lem0)). Qed.
Lemma lem3287363 {A : Type'} (_33797 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term201 A t s _33797.
Proof. exact (EQ_MP (@lem3287362 A t s _33797) (@lem3287036 A _33797 x' x s t h1)). Qed.
Lemma lem3287365 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3287366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33797 : A) : (term201 A t s _33797) = (term204 A s t _33797).
Proof. exact (@lem3287365 (term109 A s _33797) (t _33797)). Qed.
Lemma lem3287368 (a : Prop) : (term54 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3287369 {A : Type'} (s : A -> Prop) (_33797 : A) : (term205 A s _33797) = (s _33797).
Proof. exact (@lem3287368 (s _33797)). Qed.
Lemma lem3287370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3287371 {A : Type'} (s : A -> Prop) (_33797 : A) : (term206 A s _33797) = (term34 A s _33797).
Proof. exact (MK_COMB (@lem3287370) (@lem3287369 A s _33797)). Qed.
Lemma lem3287372 {A : Type'} (t : A -> Prop) (_33797 : A) : (t _33797) = (t _33797).
Proof. exact (eq_refl (t _33797)). Qed.
Lemma lem3287373 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33797 : A) : (term204 A s t _33797) = (term36 A s t _33797).
Proof. exact (MK_COMB (@lem3287371 A s _33797) (@lem3287372 A t _33797)). Qed.
Lemma lem3287374 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33797 : A) : (term201 A t s _33797) = (term36 A s t _33797).
Proof. exact (TRANS (@lem3287366 A s t _33797) (@lem3287373 A s t _33797)). Qed.
Lemma lem3287377 {A : Type'} (_33797 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term36 A s t _33797.
Proof. exact (EQ_MP (@lem3287374 A s t _33797) (@lem3287363 A _33797 x' x s t h1)). Qed.
Lemma lem3287378 {A : Type'} (_33797 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term36 A s t _33797.
Proof. exact (@lem3287377 A _33797 x' x s t h1). Qed.
Lemma lem3287379 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term36 A s t x'.
Proof. exact (@lem3287378 A x' x' x s t h1). Qed.
Lemma lem3287382 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : t x'.
Proof. exact (@lem3287379 A x' x s t h2 (@lem3287334 A s x' h1)). Qed.
Lemma lem3287383 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : term198 A t x'.
Proof. exact (fun h0 : term109 A t x' => @lem3287382 A x' x s t h1 h2). Qed.
Lemma lem3287385 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287386 {A : Type'} (t : A -> Prop) (x' : A) : (term198 A t x') = (t x').
Proof. exact (@lem3287385 (t x')). Qed.
Lemma lem3287387 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : t x'.
Proof. exact (EQ_MP (@lem3287386 A t x') (@lem3287383 A x' x s t h1 h2)). Qed.
Lemma lem3287390 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3287392 {A : Type'} (t : A -> Prop) (x' : A) : (term109 A t x') = (term199 A t x').
Proof. exact (@lem3287390 (t x')). Qed.
Lemma lem3287395 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : term199 A t x'.
Proof. exact (EQ_MP (@lem3287392 A t x') (@lem3287038 A x' x s t h1)). Qed.
Lemma lem3287398 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : False.
Proof. exact (@lem3287395 A x' x s t h2 (@lem3287387 A x' x s t h1 h2)). Qed.
Lemma lem3287399 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : term200.
Proof. exact (fun h0 : ~ False => @lem3287398 A x' x s t h1 h2). Qed.
Lemma lem3287401 (p : Prop) : (term187 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3287402 : term200 = False.
Proof. exact (@lem3287401 False). Qed.
Lemma lem3287403 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3287402) (@lem3287399 A x' x s t h1 h2)). Qed.
Lemma lem3287404 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3287326) (@lem3287323 A s t x' x h1 h2)). Qed.
Lemma lem3287405 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3287403 A x' x s t h1 h2) (fun h3 : False => @lem3287040 A s x' h1)). Qed.
Lemma lem3287406 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3287405 A x' x s t h1 h2) (@lem3287040 A s x' h1)). Qed.
Lemma lem3287407 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3287404 A s t x' x h1 h2) (fun h3 : False => @lem3287028 A x' x h2)). Qed.
Lemma lem3287408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3287407 A s t x' x h1 h2) (@lem3287028 A x' x h2)). Qed.
Lemma lem3287409 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : (term109 A t x) = False.
Proof. exact (prop_ext (fun h3 : term109 A t x => @lem3287202 A x s t x' h1 h2) (fun h3 : False => @lem3286988 A t x h1)). Qed.
Lemma lem3287410 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : False.
Proof. exact (EQ_MP (@lem3287409 A x s t x' h1 h2) (@lem3286988 A t x h1)). Qed.
Lemma lem3287411 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3287406 A x' x s t h1 h2) (fun h3 : False => @lem3286970 A s x' h1)). Qed.
Lemma lem3287412 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3287411 A x' x s t h1 h2) (@lem3286970 A s x' h1)). Qed.
Lemma lem3287413 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3287408 A s t x' x h1 h2) (fun h3 : False => @lem3286945 A x' x h2)). Qed.
Lemma lem3287414 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3287413 A s t x' x h1 h2) (@lem3286945 A x' x h2)). Qed.
Lemma lem3287415 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : (term109 A t x) = False.
Proof. exact (prop_ext (fun h3 : term109 A t x => @lem3287410 A x s t x' h1 h2) (fun h3 : False => @lem3286889 A t x h1)). Qed.
Lemma lem3287416 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : False.
Proof. exact (EQ_MP (@lem3287415 A x s t x' h1 h2) (@lem3286889 A t x h1)). Qed.
Lemma lem3287417 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3287412 A x' x s t h1 h2) (fun h3 : False => @lem3286970 A s x' h1)). Qed.
Lemma lem3287418 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : s x') (h2 : term149 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3287417 A x' x s t h1 h2) (@lem3286970 A s x' h1)). Qed.
Lemma lem3287419 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3287414 A s t x' x h1 h2) (fun h3 : False => @lem3286945 A x' x h2)). Qed.
Lemma lem3287420 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term149 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3287419 A s t x' x h1 h2) (@lem3286945 A x' x h2)). Qed.
Lemma lem3287421 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : (term109 A t x) = False.
Proof. exact (prop_ext (fun h3 : term109 A t x => @lem3287416 A x s t x' h1 h2) (fun h3 : False => @lem3286889 A t x h1)). Qed.
Lemma lem3287422 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term109 A t x) (h2 : term131 A x s t x') : False.
Proof. exact (EQ_MP (@lem3287421 A x s t x' h1 h2) (@lem3286889 A t x h1)). Qed.
Lemma lem3287423 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x' x s t) : False.
Proof. exact (or_elim (@lem3286860 A x' x s t h1) (fun h0 : x' = x => @lem3287420 A s t x' x h1 h0) (fun h0 : s x' => @lem3287418 A x' x s t h0 h1)). Qed.
Lemma lem3287424 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : False.
Proof. exact (or_elim (@lem3286849 A x s t x' h1) (fun h0 : term109 A t x => @lem3287422 A x s t x' h0 h1) (fun h0 : term77 A s t x' => @lem3287304 A x s t x' h1 h0)). Qed.
Lemma lem3287425 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x' x s t) : False.
Proof. exact (or_elim (@lem3286846 A x' x s t h1) (fun h0 : term131 A x s t x' => @lem3287424 A x s t x' h0) (fun h0 : term149 A x' x s t => @lem3287423 A x' x s t h0)). Qed.
Lemma lem3287426 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x' x s t) : (term170 A x' x s t) = False.
Proof. exact (prop_ext (fun h2 : term170 A x' x s t => @lem3287425 A x' x s t h1) (fun h2 : False => @lem3286846 A x' x s t h1)). Qed.
Lemma lem3287427 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3287426 A x' x s t h1) (@lem3286846 A x' x s t h1)). Qed.
Lemma lem3287428 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term56 A x s t) : False.
Proof. exact (ex_elim (@lem3286753 A x s t h1) (fun x' : A => fun h0 : term172 A x s t x' => @lem3287427 A x' x s t h0)). Qed.
Lemma lem3287429 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term56 A x s t) : (term56 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term56 A x s t => @lem3287428 A x s t h1) (fun h2 : False => @lem3286426 A x s t h1)). Qed.
Lemma lem3287430 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term56 A x s t) : False.
Proof. exact (EQ_MP (@lem3287429 A x s t h1) (@lem3286426 A x s t h1)). Qed.
Lemma lem3287431 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term55 A x s t.
Proof. exact (fun h0 : term56 A x s t => @lem3287430 A x s t h0). Qed.
Lemma lem3287432 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term30 A x s t) = (term40 A x s t).
Proof. exact (EQ_MP (@lem3286425 A x s t) (@lem3287431 A x s t)). Qed.
Lemma lem3287437 {A : Type'} (x : A) (s : A -> Prop) : term42 A x s.
Proof. exact (fun t : A -> Prop => @lem3287432 A x s t). Qed.
Lemma lem3287442 {A : Type'} (x : A) : term44 A x.
Proof. exact (fun s : A -> Prop => @lem3287437 A x s). Qed.
Lemma lem3287447 {A : Type'} : term46 A.
Proof. exact (fun x : A => @lem3287442 A x). Qed.
Lemma lem3287448 {A : Type'} : term48 A.
Proof. exact (EQ_MP (@lem3286421 A) (@lem3287447 A)). Qed.
Lemma lem3287450 {A : Type'} : term48 A.
Proof. exact (@lem3286304 A (@lem3287448 A)). Qed.
Lemma lem3287451 {A : Type'} (h1 : term49 A) : False.
Proof. exact (@lem3287450 A (@lem3286288 A h1)). Qed.
Lemma lem3287452 {A : Type'} (h1 : term49 A) : (term49 A) = False.
Proof. exact (prop_ext (fun h2 : term49 A => @lem3287451 A h1) (fun h2 : False => @lem3286288 A h1)). Qed.
Lemma lem3287453 {A : Type'} (h1 : term49 A) : False.
Proof. exact (EQ_MP (@lem3287452 A h1) (@lem3286288 A h1)). Qed.
Lemma lem3287454 {A : Type'} : term48 A.
Proof. exact (fun h0 : term49 A => @lem3287453 A h0). Qed.
Lemma lem3287455 {A : Type'} : term46 A.
Proof. exact (EQ_MP (@lem3286287 A) (@lem3287454 A)). Qed.
Lemma lem3287456 {A : Type'} : term19 A.
Proof. exact (EQ_MP (@lem3286283 A) (@lem3287455 A)). Qed.
Lemma lem3287457 {A : Type'} : term18 A.
Proof. exact (EQ_MP (@lem3286166 A) (@lem3287456 A)). Qed.
