Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DELETE_NON_ELEMENT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3303108 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3303109 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3303108 A s t). Qed.
Lemma lem3303110 {A : Type'} (x : A) (s : A -> Prop) : ((@DELETE A s x) = s) = (term1 A x s).
Proof. exact (@lem3303109 A (@DELETE A s x) s). Qed.
Lemma lem3303119 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term2 A x s).
Proof. exact (eq_refl (term2 A x s)). Qed.
Lemma lem3303120 {A : Type'} (x : A) (s : A -> Prop) : ((term3 A x s) = ((@DELETE A s x) = s)) = ((term3 A x s) = (term1 A x s)).
Proof. exact (MK_COMB (@lem3303119 A x s) (@lem3303110 A x s)). Qed.
Lemma lem3303125 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3303120 A x s)). Qed.
Lemma lem3303126 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3303127 {A : Type'} (x : A) : (term6 A x) = (term7 A x).
Proof. exact (MK_COMB (@lem3303126 A) (@lem3303125 A x)). Qed.
Lemma lem3303132 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (fun_ext (fun x : A => @lem3303127 A x)). Qed.
Lemma lem3303133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303134 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem3303133 A) (@lem3303132 A)). Qed.
Lemma lem3303139 {A : Type'} : (term11 A) = (term10 A).
Proof. exact (SYM (@lem3303134 A)). Qed.
Lemma lem3303151 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3303152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3303151 A P x). Qed.
Lemma lem3303153 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3303152 A s x). Qed.
Lemma lem3303154 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3303155 {A : Type'} (s : A -> Prop) (x : A) : (term3 A x s) = (term12 A s x).
Proof. exact (MK_COMB (@lem3303154) (@lem3303153 A s x)). Qed.
Lemma lem3303156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3303157 {A : Type'} (s : A -> Prop) (x : A) : (term2 A x s) = (term13 A s x).
Proof. exact (MK_COMB (@lem3303156) (@lem3303155 A s x)). Qed.
Lemma lem3303165 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term14 A x s y) = (term15 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3303166 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term14 A x s y) = (term15 A s x y).
Proof. exact (@lem3303165 A s x y). Qed.
Lemma lem3303167 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term14 A x' s x) = (term15 A s x' x).
Proof. exact (@lem3303166 A s x' x). Qed.
Lemma lem3303171 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3303172 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3303171 A P x). Qed.
Lemma lem3303173 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3303172 A s x'). Qed.
Lemma lem3303174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3303175 {A : Type'} (s : A -> Prop) (x' : A) : (term16 A x' s) = (term17 A s x').
Proof. exact (MK_COMB (@lem3303174) (@lem3303173 A s x')). Qed.
Lemma lem3303178 {A : Type'} (x' : A) (x : A) : (term18 A x' x) = (term18 A x' x).
Proof. exact (eq_refl (term18 A x' x)). Qed.
Lemma lem3303179 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term15 A s x' x) = (term19 A s x' x).
Proof. exact (MK_COMB (@lem3303175 A s x') (@lem3303178 A x' x)). Qed.
Lemma lem3303182 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term14 A x' s x) = (term19 A s x' x).
Proof. exact (TRANS (@lem3303167 A s x' x) (@lem3303179 A s x' x)). Qed.
Lemma lem3303183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3303184 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term20 A x' s x) = (term21 A s x' x).
Proof. exact (MK_COMB (@lem3303183) (@lem3303182 A s x' x)). Qed.
Lemma lem3303186 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3303187 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3303186 A P x). Qed.
Lemma lem3303188 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3303187 A s x'). Qed.
Lemma lem3303189 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term14 A x' s x) = (@IN A x' s)) = ((term19 A s x' x) = (s x')).
Proof. exact (MK_COMB (@lem3303184 A s x' x) (@lem3303188 A s x')). Qed.
Lemma lem3303192 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (term23 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303189 A x s x')). Qed.
Lemma lem3303193 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303194 {A : Type'} (x : A) (s : A -> Prop) : (term1 A x s) = (term24 A x s).
Proof. exact (MK_COMB (@lem3303193 A) (@lem3303192 A x s)). Qed.
Lemma lem3303199 {A : Type'} (x : A) (s : A -> Prop) : ((term3 A x s) = (term1 A x s)) = ((term12 A s x) = (term24 A x s)).
Proof. exact (MK_COMB (@lem3303157 A s x) (@lem3303194 A x s)). Qed.
Lemma lem3303202 {A : Type'} (x : A) : (term5 A x) = (term25 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3303199 A x s)). Qed.
Lemma lem3303203 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3303204 {A : Type'} (x : A) : (term7 A x) = (term26 A x).
Proof. exact (MK_COMB (@lem3303203 A) (@lem3303202 A x)). Qed.
Lemma lem3303209 {A : Type'} : (term9 A) = (term27 A).
Proof. exact (fun_ext (fun x : A => @lem3303204 A x)). Qed.
Lemma lem3303210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303211 {A : Type'} : (term11 A) = (term28 A).
Proof. exact (MK_COMB (@lem3303210 A) (@lem3303209 A)). Qed.
Lemma lem3303216 {A : Type'} : (term28 A) = (term11 A).
Proof. exact (SYM (@lem3303211 A)). Qed.
Lemma lem3303218 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3303219 {A : Type'} : (term28 A) = (term30 A).
Proof. exact (@lem3303218 (term28 A)). Qed.
Lemma lem3303220 {A : Type'} : (term30 A) = (term28 A).
Proof. exact (SYM (@lem3303219 A)). Qed.
Lemma lem3303221 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3303224 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3303225 {A : Type'} : term32 A.
Proof. exact (fun h0 : term30 A => @lem3303224 A h0). Qed.
Lemma lem3303226 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3303227 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3303228 {A : Type'} (h1 : term30 A) (h2 : term32 A) : term30 A.
Proof. exact (@lem3303226 A h2 (@lem3303227 A h1)). Qed.
Lemma lem3303229 {A : Type'} (h1 : term30 A) : term33 A.
Proof. exact (fun h0 : term32 A => @lem3303228 A h1 h0). Qed.
Lemma lem3303230 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3303231 {A : Type'} (h1 : term30 A) (h2 : term32 A) : term30 A.
Proof. exact (@lem3303229 A h1 (@lem3303230 A h2)). Qed.
Lemma lem3303232 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (fun h0 : term30 A => @lem3303231 A h0 h1). Qed.
Lemma lem3303233 {A : Type'} : term34 A.
Proof. exact (fun h0 : term32 A => @lem3303232 A h0). Qed.
Lemma lem3303236 {A : Type'} : term32 A.
Proof. exact (@lem3303233 A (@lem3303225 A)). Qed.
Lemma lem3303237 {A : Type'} : term32 A.
Proof. exact (@lem3303236 A). Qed.
Lemma lem3303239 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3303240 {A : Type'} : (term30 A) = (term35 A).
Proof. exact (@lem3303239 (term31 A)). Qed.
Lemma lem3303242 (t : Prop) : (term36 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3303243 {A : Type'} : (term35 A) = (term28 A).
Proof. exact (@lem3303242 (term28 A)). Qed.
Lemma lem3303262 {A : Type'} : (term30 A) = (term28 A).
Proof. exact (TRANS (@lem3303240 A) (@lem3303243 A)). Qed.
Lemma lem3303273 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term19 A s x' x) = (s x')) = ((term19 A s x' x) = (s x')).
Proof. exact (eq_refl ((term19 A s x' x) = (s x'))). Qed.
Lemma lem3303274 {A : Type'} (x : A) (s : A -> Prop) : (term23 A x s) = (term23 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303273 A x s x')). Qed.
Lemma lem3303275 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303276 {A : Type'} (x : A) (s : A -> Prop) : (term24 A x s) = (term24 A x s).
Proof. exact (MK_COMB (@lem3303275 A) (@lem3303274 A x s)). Qed.
Lemma lem3303281 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term13 A s x).
Proof. exact (eq_refl (term13 A s x)). Qed.
Lemma lem3303282 {A : Type'} (x : A) (s : A -> Prop) : ((term12 A s x) = (term24 A x s)) = ((term12 A s x) = (term24 A x s)).
Proof. exact (MK_COMB (@lem3303281 A s x) (@lem3303276 A x s)). Qed.
Lemma lem3303283 {A : Type'} (x : A) : (term25 A x) = (term25 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3303282 A x s)). Qed.
Lemma lem3303284 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3303285 {A : Type'} (x : A) : (term26 A x) = (term26 A x).
Proof. exact (MK_COMB (@lem3303284 A) (@lem3303283 A x)). Qed.
Lemma lem3303286 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun x : A => @lem3303285 A x)). Qed.
Lemma lem3303287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303288 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3303287 A) (@lem3303286 A)). Qed.
Lemma lem3303311 {A : Type'} : (term30 A) = (term28 A).
Proof. exact (TRANS (@lem3303262 A) (@lem3303288 A)). Qed.
Lemma lem3303312 {A : Type'} : (term28 A) = (term30 A).
Proof. exact (SYM (@lem3303311 A)). Qed.
Lemma lem3303314 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3303315 {A : Type'} (x : A) (s : A -> Prop) : ((term12 A s x) = (term24 A x s)) = (term37 A x s).
Proof. exact (@lem3303314 ((term12 A s x) = (term24 A x s))). Qed.
Lemma lem3303316 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = ((term12 A s x) = (term24 A x s)).
Proof. exact (SYM (@lem3303315 A x s)). Qed.
Lemma lem3303317 {A : Type'} (x : A) (s : A -> Prop) (h1 : term38 A x s) : term38 A x s.
Proof. exact (h1). Qed.
Lemma lem3303321 {A : Type'} (s : A -> Prop) (x : A) : (term39 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3303327 {A : Type'} (x' : A) (x : A) : (term40 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3303329 {A : Type'} (s : A -> Prop) (x' : A) : (term41 A s x') = (term41 A s x').
Proof. exact (eq_refl (term41 A s x')). Qed.
Lemma lem3303330 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term42 A s x' x) = (term43 A s x' x).
Proof. exact (MK_COMB (@lem3303329 A s x') (@lem3303327 A x' x)). Qed.
Lemma lem3303331 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term44 A s x' x) = (term42 A s x' x).
Proof. exact (@lem17045 (s x') (term18 A x' x)). Qed.
Lemma lem3303332 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term44 A s x' x) = (term43 A s x' x).
Proof. exact (TRANS (@lem3303331 A s x' x) (@lem3303330 A s x' x)). Qed.
Lemma lem3303336 {A : Type'} (s : A -> Prop) (x' : A) : (term12 A s x') = (term12 A s x').
Proof. exact (eq_refl (term12 A s x')). Qed.
Lemma lem3303337 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3303338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3303339 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term46 A s x' x).
Proof. exact (MK_COMB (@lem3303338) (@lem3303332 A s x' x)). Qed.
Lemma lem3303340 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term47 A x s x') = (term48 A x s x').
Proof. exact (MK_COMB (@lem3303339 A s x' x) (@lem3303336 A s x')). Qed.
Lemma lem3303345 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term49 A x s x') = (term49 A x s x').
Proof. exact (eq_refl (term49 A x s x')). Qed.
Lemma lem3303346 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term50 A x s x') = (term51 A x s x').
Proof. exact (MK_COMB (@lem3303345 A x s x') (@lem3303340 A x s x')). Qed.
Lemma lem3303347 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term52 A x s x') = (term50 A x s x').
Proof. exact (@lem17930 (term19 A s x' x) (s x')). Qed.
Lemma lem3303348 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term52 A x s x') = (term51 A x s x').
Proof. exact (TRANS (@lem3303347 A x s x') (@lem3303346 A x s x')). Qed.
Lemma lem3303349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3303350 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term46 A s x' x).
Proof. exact (MK_COMB (@lem3303349) (@lem3303332 A s x' x)). Qed.
Lemma lem3303351 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term53 A x s x') = (term54 A x s x').
Proof. exact (MK_COMB (@lem3303350 A s x' x) (@lem3303337 A s x')). Qed.
Lemma lem3303356 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term55 A x s x') = (term55 A x s x').
Proof. exact (eq_refl (term55 A x s x')). Qed.
Lemma lem3303357 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term56 A x s x') = (term57 A x s x').
Proof. exact (MK_COMB (@lem3303356 A x s x') (@lem3303351 A x s x')). Qed.
Lemma lem3303358 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term19 A s x' x) = (s x')) = (term56 A x s x').
Proof. exact (@lem17784 (term19 A s x' x) (s x')). Qed.
Lemma lem3303359 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term19 A s x' x) = (s x')) = (term57 A x s x').
Proof. exact (TRANS (@lem3303358 A x s x') (@lem3303357 A x s x')). Qed.
Lemma lem3303360 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3303361 {A : Type'} (x : A) (s : A -> Prop) : (term60 A x s) = (term61 A x s).
Proof. exact (@lem3303360 A (term23 A x s)). Qed.
Lemma lem3303362 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term62 A x s x') = ((term19 A s x' x) = (s x')).
Proof. exact (eq_refl (term62 A x s x')). Qed.
Lemma lem3303363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3303364 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term63 A x s x') = (term52 A x s x').
Proof. exact (MK_COMB (@lem3303363) (@lem3303362 A x s x')). Qed.
Lemma lem3303365 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term63 A x s x') = (term51 A x s x').
Proof. exact (TRANS (@lem3303364 A x s x') (@lem3303348 A x s x')). Qed.
Lemma lem3303366 {A : Type'} (x : A) (s : A -> Prop) : (term64 A x s) = (term65 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303365 A x s x')). Qed.
Lemma lem3303367 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3303368 {A : Type'} (x : A) (s : A -> Prop) : (term61 A x s) = (term66 A x s).
Proof. exact (MK_COMB (@lem3303367 A) (@lem3303366 A x s)). Qed.
Lemma lem3303369 {A : Type'} (x : A) (s : A -> Prop) : (term60 A x s) = (term66 A x s).
Proof. exact (TRANS (@lem3303361 A x s) (@lem3303368 A x s)). Qed.
Lemma lem3303370 {A : Type'} (x : A) (s : A -> Prop) : (term23 A x s) = (term67 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303359 A x s x')). Qed.
Lemma lem3303371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303372 {A : Type'} (x : A) (s : A -> Prop) : (term24 A x s) = (term68 A x s).
Proof. exact (MK_COMB (@lem3303371 A) (@lem3303370 A x s)). Qed.
Lemma lem3303373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3303374 {A : Type'} (s : A -> Prop) (x : A) : (term69 A s x) = (term17 A s x).
Proof. exact (MK_COMB (@lem3303373) (@lem3303321 A s x)). Qed.
Lemma lem3303375 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem3303374 A s x) (@lem3303372 A x s)). Qed.
Lemma lem3303377 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term72 A s x).
Proof. exact (eq_refl (term72 A s x)). Qed.
Lemma lem3303378 {A : Type'} (x : A) (s : A -> Prop) : (term73 A x s) = (term74 A x s).
Proof. exact (MK_COMB (@lem3303377 A s x) (@lem3303369 A x s)). Qed.
Lemma lem3303379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3303380 {A : Type'} (x : A) (s : A -> Prop) : (term75 A x s) = (term76 A x s).
Proof. exact (MK_COMB (@lem3303379) (@lem3303378 A x s)). Qed.
Lemma lem3303381 {A : Type'} (x : A) (s : A -> Prop) : (term77 A x s) = (term78 A x s).
Proof. exact (MK_COMB (@lem3303380 A x s) (@lem3303375 A x s)). Qed.
Lemma lem3303382 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term77 A x s).
Proof. exact (@lem17646 (term12 A s x) (term24 A x s)). Qed.
Lemma lem3303383 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term78 A x s).
Proof. exact (TRANS (@lem3303382 A x s) (@lem3303381 A x s)). Qed.
Lemma lem3303433 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3303434 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (@lem3303433 A P Q). Qed.
Lemma lem3303435 {A : Type'} (x : A) (s : A -> Prop) : (term81 A x s) = (term82 A x s).
Proof. exact (@lem3303434 A (term83 A x s) (term84 A x s)). Qed.
Lemma lem3303436 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term85 A x s x') = (term86 A x s x').
Proof. exact (eq_refl (term85 A x s x')). Qed.
Lemma lem3303437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3303438 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term87 A x s x') = (term55 A x s x').
Proof. exact (MK_COMB (@lem3303437) (@lem3303436 A x s x')). Qed.
Lemma lem3303439 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term88 A x s x') = (term54 A x s x').
Proof. exact (eq_refl (term88 A x s x')). Qed.
Lemma lem3303440 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term89 A x s x') = (term57 A x s x').
Proof. exact (MK_COMB (@lem3303438 A x s x') (@lem3303439 A x s x')). Qed.
Lemma lem3303441 {A : Type'} (x : A) (s : A -> Prop) : (term90 A x s) = (term67 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303440 A x s x')). Qed.
Lemma lem3303442 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303443 {A : Type'} (x : A) (s : A -> Prop) : (term81 A x s) = (term68 A x s).
Proof. exact (MK_COMB (@lem3303442 A) (@lem3303441 A x s)). Qed.
Lemma lem3303444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3303445 {A : Type'} (x : A) (s : A -> Prop) : (term91 A x s) = (term92 A x s).
Proof. exact (MK_COMB (@lem3303444) (@lem3303443 A x s)). Qed.
Lemma lem3303446 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term85 A x s x') = (term86 A x s x').
Proof. exact (eq_refl (term85 A x s x')). Qed.
Lemma lem3303447 {A : Type'} (x : A) (s : A -> Prop) : (term93 A x s) = (term83 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303446 A x s x')). Qed.
Lemma lem3303448 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303449 {A : Type'} (x : A) (s : A -> Prop) : (term94 A x s) = (term95 A x s).
Proof. exact (MK_COMB (@lem3303448 A) (@lem3303447 A x s)). Qed.
Lemma lem3303450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3303451 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = (term97 A x s).
Proof. exact (MK_COMB (@lem3303450) (@lem3303449 A x s)). Qed.
Lemma lem3303452 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term88 A x s x') = (term54 A x s x').
Proof. exact (eq_refl (term88 A x s x')). Qed.
Lemma lem3303453 {A : Type'} (x : A) (s : A -> Prop) : (term98 A x s) = (term84 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303452 A x s x')). Qed.
Lemma lem3303454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303455 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term100 A x s).
Proof. exact (MK_COMB (@lem3303454 A) (@lem3303453 A x s)). Qed.
Lemma lem3303456 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term101 A x s).
Proof. exact (MK_COMB (@lem3303451 A x s) (@lem3303455 A x s)). Qed.
Lemma lem3303457 {A : Type'} (x : A) (s : A -> Prop) : ((term81 A x s) = (term82 A x s)) = ((term68 A x s) = (term101 A x s)).
Proof. exact (MK_COMB (@lem3303445 A x s) (@lem3303456 A x s)). Qed.
Lemma lem3303458 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term101 A x s).
Proof. exact (EQ_MP (@lem3303457 A x s) (@lem3303435 A x s)). Qed.
Lemma lem3303539 {A : Type'} (s : A -> Prop) (x : A) : (term17 A s x) = (term17 A s x).
Proof. exact (eq_refl (term17 A s x)). Qed.
Lemma lem3303540 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term102 A x s).
Proof. exact (MK_COMB (@lem3303539 A s x) (@lem3303458 A x s)). Qed.
Lemma lem3303541 {A : Type'} (x : A) (s : A -> Prop) : (term76 A x s) = (term76 A x s).
Proof. exact (eq_refl (term76 A x s)). Qed.
Lemma lem3303542 {A : Type'} (x : A) (s : A -> Prop) : (term78 A x s) = (term103 A x s).
Proof. exact (MK_COMB (@lem3303541 A x s) (@lem3303540 A x s)). Qed.
Lemma lem3303544 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3303545 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (@lem3303544 A P Q). Qed.
Lemma lem3303546 {A : Type'} (x : A) (s : A -> Prop) : (term106 A x s) = (term107 A x s).
Proof. exact (@lem3303545 A (term12 A s x) (term65 A x s)). Qed.
Lemma lem3303547 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term108 A x s x') = (term51 A x s x').
Proof. exact (eq_refl (term108 A x s x')). Qed.
Lemma lem3303548 {A : Type'} (x : A) (s : A -> Prop) : (term109 A x s) = (term65 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303547 A x s x')). Qed.
Lemma lem3303549 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3303550 {A : Type'} (x : A) (s : A -> Prop) : (term110 A x s) = (term66 A x s).
Proof. exact (MK_COMB (@lem3303549 A) (@lem3303548 A x s)). Qed.
Lemma lem3303551 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term72 A s x).
Proof. exact (eq_refl (term72 A s x)). Qed.
Lemma lem3303552 {A : Type'} (x : A) (s : A -> Prop) : (term106 A x s) = (term74 A x s).
Proof. exact (MK_COMB (@lem3303551 A s x) (@lem3303550 A x s)). Qed.
Lemma lem3303553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3303554 {A : Type'} (x : A) (s : A -> Prop) : (term111 A x s) = (term112 A x s).
Proof. exact (MK_COMB (@lem3303553) (@lem3303552 A x s)). Qed.
Lemma lem3303555 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term108 A x s x') = (term51 A x s x').
Proof. exact (eq_refl (term108 A x s x')). Qed.
Lemma lem3303556 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term72 A s x).
Proof. exact (eq_refl (term72 A s x)). Qed.
Lemma lem3303557 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term113 A x s x') = (term114 A x s x').
Proof. exact (MK_COMB (@lem3303556 A s x) (@lem3303555 A x s x')). Qed.
Lemma lem3303558 {A : Type'} (x : A) (s : A -> Prop) : (term115 A x s) = (term116 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303557 A x s x')). Qed.
Lemma lem3303559 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3303560 {A : Type'} (x : A) (s : A -> Prop) : (term107 A x s) = (term117 A x s).
Proof. exact (MK_COMB (@lem3303559 A) (@lem3303558 A x s)). Qed.
Lemma lem3303561 {A : Type'} (x : A) (s : A -> Prop) : ((term106 A x s) = (term107 A x s)) = ((term74 A x s) = (term117 A x s)).
Proof. exact (MK_COMB (@lem3303554 A x s) (@lem3303560 A x s)). Qed.
Lemma lem3303562 {A : Type'} (x : A) (s : A -> Prop) : (term74 A x s) = (term117 A x s).
Proof. exact (EQ_MP (@lem3303561 A x s) (@lem3303546 A x s)). Qed.
Lemma lem3303563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3303564 {A : Type'} (x : A) (s : A -> Prop) : (term76 A x s) = (term118 A x s).
Proof. exact (MK_COMB (@lem3303563) (@lem3303562 A x s)). Qed.
Lemma lem3303565 {A : Type'} (x : A) (s : A -> Prop) : (term102 A x s) = (term102 A x s).
Proof. exact (eq_refl (term102 A x s)). Qed.
Lemma lem3303566 {A : Type'} (x : A) (s : A -> Prop) : (term103 A x s) = (term119 A x s).
Proof. exact (MK_COMB (@lem3303564 A x s) (@lem3303565 A x s)). Qed.
Lemma lem3303568 {A : Type'} (P : A -> Prop) (Q : Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3303569 {A : Type'} (P : A -> Prop) (Q : Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (@lem3303568 A P Q). Qed.
Lemma lem3303570 {A : Type'} (x : A) (s : A -> Prop) : (term122 A x s) = (term123 A x s).
Proof. exact (@lem3303569 A (term116 A x s) (term102 A x s)). Qed.
Lemma lem3303571 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term124 A x s x') = (term114 A x s x').
Proof. exact (eq_refl (term124 A x s x')). Qed.
Lemma lem3303572 {A : Type'} (x : A) (s : A -> Prop) : (term125 A x s) = (term116 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303571 A x s x')). Qed.
Lemma lem3303573 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3303574 {A : Type'} (x : A) (s : A -> Prop) : (term126 A x s) = (term117 A x s).
Proof. exact (MK_COMB (@lem3303573 A) (@lem3303572 A x s)). Qed.
Lemma lem3303575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3303576 {A : Type'} (x : A) (s : A -> Prop) : (term127 A x s) = (term118 A x s).
Proof. exact (MK_COMB (@lem3303575) (@lem3303574 A x s)). Qed.
Lemma lem3303577 {A : Type'} (x : A) (s : A -> Prop) : (term102 A x s) = (term102 A x s).
Proof. exact (eq_refl (term102 A x s)). Qed.
Lemma lem3303578 {A : Type'} (x : A) (s : A -> Prop) : (term122 A x s) = (term119 A x s).
Proof. exact (MK_COMB (@lem3303576 A x s) (@lem3303577 A x s)). Qed.
Lemma lem3303579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3303580 {A : Type'} (x : A) (s : A -> Prop) : (term128 A x s) = (term129 A x s).
Proof. exact (MK_COMB (@lem3303579) (@lem3303578 A x s)). Qed.
Lemma lem3303581 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term124 A x s x') = (term114 A x s x').
Proof. exact (eq_refl (term124 A x s x')). Qed.
Lemma lem3303582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3303583 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term130 A x s x') = (term131 A x s x').
Proof. exact (MK_COMB (@lem3303582) (@lem3303581 A x s x')). Qed.
Lemma lem3303584 {A : Type'} (x : A) (s : A -> Prop) : (term102 A x s) = (term102 A x s).
Proof. exact (eq_refl (term102 A x s)). Qed.
Lemma lem3303585 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term132 A x' x s) = (term133 A x' x s).
Proof. exact (MK_COMB (@lem3303583 A x s x') (@lem3303584 A x s)). Qed.
Lemma lem3303586 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term135 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303585 A x' x s)). Qed.
Lemma lem3303587 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3303588 {A : Type'} (x : A) (s : A -> Prop) : (term123 A x s) = (term136 A x s).
Proof. exact (MK_COMB (@lem3303587 A) (@lem3303586 A x s)). Qed.
Lemma lem3303589 {A : Type'} (x : A) (s : A -> Prop) : ((term122 A x s) = (term123 A x s)) = ((term119 A x s) = (term136 A x s)).
Proof. exact (MK_COMB (@lem3303580 A x s) (@lem3303588 A x s)). Qed.
Lemma lem3303590 {A : Type'} (x : A) (s : A -> Prop) : (term119 A x s) = (term136 A x s).
Proof. exact (EQ_MP (@lem3303589 A x s) (@lem3303570 A x s)). Qed.
Lemma lem3303591 {A : Type'} (x : A) (s : A -> Prop) : (term103 A x s) = (term136 A x s).
Proof. exact (TRANS (@lem3303566 A x s) (@lem3303590 A x s)). Qed.
Lemma lem3303592 {A : Type'} (x : A) (s : A -> Prop) : (term78 A x s) = (term136 A x s).
Proof. exact (TRANS (@lem3303542 A x s) (@lem3303591 A x s)). Qed.
Lemma lem3303593 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term136 A x s).
Proof. exact (TRANS (@lem3303383 A x s) (@lem3303592 A x s)). Qed.
Lemma lem3303594 {A : Type'} (x : A) (s : A -> Prop) (h1 : term38 A x s) : term136 A x s.
Proof. exact (EQ_MP (@lem3303593 A x s) (@lem3303317 A x s h1)). Qed.
Lemma lem3303595 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term133 A x' x s) : term133 A x' x s.
Proof. exact (h1). Qed.
Lemma lem3303614 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term54 A x s x') = (term54 A x s x').
Proof. exact (eq_refl (term54 A x s x')). Qed.
Lemma lem3303615 {A : Type'} (x : A) (s : A -> Prop) : (term84 A x s) = (term84 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303614 A x s x')). Qed.
Lemma lem3303616 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303617 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (term100 A x s).
Proof. exact (MK_COMB (@lem3303616 A) (@lem3303615 A x s)). Qed.
Lemma lem3303638 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term86 A x s x') = (term86 A x s x').
Proof. exact (eq_refl (term86 A x s x')). Qed.
Lemma lem3303639 {A : Type'} (x : A) (s : A -> Prop) : (term83 A x s) = (term83 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303638 A x s x')). Qed.
Lemma lem3303640 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303641 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term95 A x s).
Proof. exact (MK_COMB (@lem3303640 A) (@lem3303639 A x s)). Qed.
Lemma lem3303642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3303643 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (term97 A x s).
Proof. exact (MK_COMB (@lem3303642) (@lem3303641 A x s)). Qed.
Lemma lem3303644 {A : Type'} (x : A) (s : A -> Prop) : (term101 A x s) = (term101 A x s).
Proof. exact (MK_COMB (@lem3303643 A x s) (@lem3303617 A x s)). Qed.
Lemma lem3303649 {A : Type'} (s : A -> Prop) (x : A) : (term17 A s x) = (term17 A s x).
Proof. exact (eq_refl (term17 A s x)). Qed.
Lemma lem3303650 {A : Type'} (x : A) (s : A -> Prop) : (term102 A x s) = (term102 A x s).
Proof. exact (MK_COMB (@lem3303649 A s x) (@lem3303644 A x s)). Qed.
Lemma lem3303703 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term131 A x s x') = (term131 A x s x').
Proof. exact (eq_refl (term131 A x s x')). Qed.
Lemma lem3303704 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term133 A x' x s) = (term133 A x' x s).
Proof. exact (MK_COMB (@lem3303703 A x s x') (@lem3303650 A x s)). Qed.
Lemma lem3303705 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term133 A x' x s) : term133 A x' x s.
Proof. exact (EQ_MP (@lem3303704 A x' x s) (@lem3303595 A x' x s h1)). Qed.
Lemma lem3303706 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term114 A x s x') : term114 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3303707 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term102 A x s.
Proof. exact (h1). Qed.
Lemma lem3303708 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term114 A x s x') : term51 A x s x'.
Proof. exact (proj2 (@lem3303706 A x s x' h1)). Qed.
Lemma lem3303710 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term114 A x s x') : term48 A x s x'.
Proof. exact (proj2 (@lem3303708 A x s x' h1)). Qed.
Lemma lem3303711 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term114 A x s x') : term137 A x s x'.
Proof. exact (proj1 (@lem3303708 A x s x' h1)). Qed.
Lemma lem3303712 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term43 A s x' x) : term43 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3303716 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : term19 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3303720 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : term19 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3303724 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : term19 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3303728 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term101 A x s.
Proof. exact (proj2 (@lem3303707 A x s h1)). Qed.
Lemma lem3303731 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term95 A x s.
Proof. exact (proj1 (@lem3303728 A x s h1)). Qed.
Lemma lem3303739 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303755 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303759 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3303767 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3303783 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3303787 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3303795 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303811 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303815 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3303837 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term86 A x s x') = (term138 A x s x').
Proof. exact (@lem19699 (s x') (term18 A x' x) (term12 A s x')). Qed.
Lemma lem3303838 {A : Type'} (x : A) (s : A -> Prop) : (term83 A x s) = (term139 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3303837 A x s x')). Qed.
Lemma lem3303839 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3303841 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term140 A x s).
Proof. exact (MK_COMB (@lem3303839 A) (@lem3303838 A x s)). Qed.
Lemma lem3303842 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term140 A x s.
Proof. exact (EQ_MP (@lem3303841 A x s) (@lem3303731 A x s h1)). Qed.
Lemma lem3303862 {A : Type'} (_33906 : A) (x : A) (s : A -> Prop) (h1 : term102 A x s) : term141 A x s _33906.
Proof. exact (@lem3303842 A x s h1 _33906). Qed.
Lemma lem3303863 {A : Type'} (x : A) (s : A -> Prop) (_33906 : A) : (term141 A x s _33906) = (term138 A x s _33906).
Proof. exact (eq_refl (term141 A x s _33906)). Qed.
Lemma lem3303864 {A : Type'} (_33906 : A) (x : A) (s : A -> Prop) (h1 : term102 A x s) : term138 A x s _33906.
Proof. exact (EQ_MP (@lem3303863 A x s _33906) (@lem3303862 A _33906 x s h1)). Qed.
Lemma lem3303873 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303881 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303883 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3303887 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3303891 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : term18 A x' x.
Proof. exact (proj2 (@lem3303720 A s x' x h1)). Qed.
Lemma lem3303895 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3303897 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3303901 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303909 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term12 A s x'.
Proof. exact (h1). Qed.
Lemma lem3303911 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3303937 {A : Type'} (_33906 : A) (x : A) (s : A -> Prop) (h1 : term102 A x s) : term142 A x s _33906.
Proof. exact (proj2 (@lem3303864 A _33906 x s h1)). Qed.
Lemma lem3303979 {A : Type'} (x : A) : (term143 A x) = (term143 A x).
Proof. exact (eq_refl (term143 A x)). Qed.
Lemma lem3303980 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term144 A x x') = (term145 A x).
Proof. exact (MK_COMB (@lem3303979 A x) (@lem3303887 A x' x h1)). Qed.
Lemma lem3303981 {A : Type'} (x : A) : (term145 A x) = (term146 A x).
Proof. exact (eq_refl (term145 A x)). Qed.
Lemma lem3303982 {A : Type'} (x : A) (x' : A) : (term147 A x x') = (term147 A x x').
Proof. exact (eq_refl (term147 A x x')). Qed.
Lemma lem3303983 {A : Type'} (x' : A) (x : A) : ((term144 A x x') = (term145 A x)) = ((term144 A x x') = (term146 A x)).
Proof. exact (MK_COMB (@lem3303982 A x x') (@lem3303981 A x)). Qed.
Lemma lem3303984 {A : Type'} (x' : A) (x : A) : (term144 A x x') = (term18 A x' x).
Proof. exact (eq_refl (term144 A x x')). Qed.
Lemma lem3303985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3303986 {A : Type'} (x' : A) (x : A) : (term147 A x x') = (term148 A x' x).
Proof. exact (MK_COMB (@lem3303985) (@lem3303984 A x' x)). Qed.
Lemma lem3303987 {A : Type'} (x : A) : (term146 A x) = (term146 A x).
Proof. exact (eq_refl (term146 A x)). Qed.
Lemma lem3303988 {A : Type'} (x' : A) (x : A) : ((term144 A x x') = (term146 A x)) = ((term18 A x' x) = (term146 A x)).
Proof. exact (MK_COMB (@lem3303986 A x' x) (@lem3303987 A x)). Qed.
Lemma lem3303989 {A : Type'} (x' : A) (x : A) : ((term144 A x x') = (term145 A x)) = ((term18 A x' x) = (term146 A x)).
Proof. exact (TRANS (@lem3303983 A x' x) (@lem3303988 A x' x)). Qed.
Lemma lem3303990 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term18 A x' x) = (term146 A x).
Proof. exact (EQ_MP (@lem3303989 A x' x) (@lem3303980 A x' x h1)). Qed.
Lemma lem3303991 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : term146 A x.
Proof. exact (EQ_MP (@lem3303990 A x' x h2) (@lem3303891 A s x' x h1)). Qed.
Lemma lem3304019 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term114 A x s x') : term12 A s x.
Proof. exact (proj1 (@lem3303706 A x s x' h1)). Qed.
Lemma lem3304020 {A : Type'} (s : A -> Prop) : (term149 A s) = (term149 A s).
Proof. exact (eq_refl (term149 A s)). Qed.
Lemma lem3304021 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term150 A s x') = (term150 A s x).
Proof. exact (MK_COMB (@lem3304020 A s) (@lem3303895 A x' x h1)). Qed.
Lemma lem3304022 {A : Type'} (s : A -> Prop) (x : A) : (term150 A s x) = (s x).
Proof. exact (eq_refl (term150 A s x)). Qed.
Lemma lem3304023 {A : Type'} (s : A -> Prop) (x' : A) : (term151 A s x') = (term151 A s x').
Proof. exact (eq_refl (term151 A s x')). Qed.
Lemma lem3304024 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term150 A s x') = (term150 A s x)) = ((term150 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3304023 A s x') (@lem3304022 A s x)). Qed.
Lemma lem3304025 {A : Type'} (s : A -> Prop) (x' : A) : (term150 A s x') = (s x').
Proof. exact (eq_refl (term150 A s x')). Qed.
Lemma lem3304026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3304027 {A : Type'} (s : A -> Prop) (x' : A) : (term151 A s x') = (term152 A s x').
Proof. exact (MK_COMB (@lem3304026) (@lem3304025 A s x')). Qed.
Lemma lem3304028 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3304029 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term150 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3304027 A s x') (@lem3304028 A s x)). Qed.
Lemma lem3304030 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term150 A s x') = (term150 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3304024 A x' s x) (@lem3304029 A x' s x)). Qed.
Lemma lem3304031 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3304030 A x' s x) (@lem3304021 A s x' x h1)). Qed.
Lemma lem3304048 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : s x'.
Proof. exact (proj1 (@lem3303716 A s x' x h1)). Qed.
Lemma lem3304049 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : term153 A s x'.
Proof. exact (fun h0 : term12 A s x' => @lem3304048 A s x' x h1). Qed.
Lemma lem3304051 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304052 {A : Type'} (s : A -> Prop) (x' : A) : (term153 A s x') = (s x').
Proof. exact (@lem3304051 (s x')). Qed.
Lemma lem3304053 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3304052 A s x') (@lem3304049 A s x' x h1)). Qed.
Lemma lem3304056 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3304058 {A : Type'} (s : A -> Prop) (x' : A) : (term12 A s x') = (term155 A s x').
Proof. exact (@lem3304056 (s x')). Qed.
Lemma lem3304061 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term155 A s x'.
Proof. exact (EQ_MP (@lem3304058 A s x') (@lem3303873 A s x' h1)). Qed.
Lemma lem3304064 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (@lem3304061 A s x' h1 (@lem3304053 A s x' x h2)). Qed.
Lemma lem3304065 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : term156.
Proof. exact (fun h0 : ~ False => @lem3304064 A s x' x h1 h2). Qed.
Lemma lem3304067 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304068 : term156 = False.
Proof. exact (@lem3304067 False). Qed.
Lemma lem3304069 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304068) (@lem3304065 A s x' x h1 h2)). Qed.
Lemma lem3304071 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3304072 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term153 A s x'.
Proof. exact (fun h0 : term12 A s x' => @lem3304071 A s x' h1). Qed.
Lemma lem3304074 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304075 {A : Type'} (s : A -> Prop) (x' : A) : (term153 A s x') = (s x').
Proof. exact (@lem3304074 (s x')). Qed.
Lemma lem3304076 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3304075 A s x') (@lem3304072 A s x' h1)). Qed.
Lemma lem3304079 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3304081 {A : Type'} (s : A -> Prop) (x' : A) : (term12 A s x') = (term155 A s x').
Proof. exact (@lem3304079 (s x')). Qed.
Lemma lem3304084 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term155 A s x'.
Proof. exact (EQ_MP (@lem3304081 A s x') (@lem3303881 A s x' h1)). Qed.
Lemma lem3304087 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (@lem3304084 A s x' h1 (@lem3304076 A s x' h2)). Qed.
Lemma lem3304088 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : term156.
Proof. exact (fun h0 : ~ False => @lem3304087 A s x' h1 h2). Qed.
Lemma lem3304090 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304091 : term156 = False.
Proof. exact (@lem3304090 False). Qed.
Lemma lem3304092 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304091) (@lem3304088 A s x' h1 h2)). Qed.
Lemma lem3304108 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3304109 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3304108 A x). Qed.
Lemma lem3304110 {A : Type'} (x : A) : term157 A x.
Proof. exact (fun h0 : term146 A x => @lem3304109 A x). Qed.
Lemma lem3304112 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304113 {A : Type'} (x : A) : (term157 A x) = (x = x).
Proof. exact (@lem3304112 (x = x)). Qed.
Lemma lem3304114 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3304113 A x) (@lem3304110 A x)). Qed.
Lemma lem3304117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3304119 {A : Type'} (x : A) : (term146 A x) = (term158 A x).
Proof. exact (@lem3304117 (x = x)). Qed.
Lemma lem3304122 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : term158 A x.
Proof. exact (EQ_MP (@lem3304119 A x) (@lem3303991 A s x' x h1 h2)). Qed.
Lemma lem3304125 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3304122 A s x' x h1 h2 (@lem3304114 A x)). Qed.
Lemma lem3304126 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : term156.
Proof. exact (fun h0 : ~ False => @lem3304125 A s x' x h1 h2). Qed.
Lemma lem3304128 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304129 : term156 = False.
Proof. exact (@lem3304128 False). Qed.
Lemma lem3304132 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3304031 A s x' x h2) (@lem3303897 A s x' h1)). Qed.
Lemma lem3304133 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : x' = x) : term153 A s x.
Proof. exact (fun h0 : term12 A s x => @lem3304132 A s x' x h1 h2). Qed.
Lemma lem3304135 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304136 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (s x).
Proof. exact (@lem3304135 (s x)). Qed.
Lemma lem3304137 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3304136 A s x) (@lem3304133 A s x' x h1 h2)). Qed.
Lemma lem3304140 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3304142 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = (term155 A s x).
Proof. exact (@lem3304140 (s x)). Qed.
Lemma lem3304145 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term114 A x s x') : term155 A s x.
Proof. exact (EQ_MP (@lem3304142 A s x) (@lem3304019 A x s x' h1)). Qed.
Lemma lem3304148 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3304145 A x s x' h2 (@lem3304137 A s x' x h1 h3)). Qed.
Lemma lem3304149 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : term156.
Proof. exact (fun h0 : ~ False => @lem3304148 A s x' x h1 h2 h3). Qed.
Lemma lem3304151 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304152 : term156 = False.
Proof. exact (@lem3304151 False). Qed.
Lemma lem3304169 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : s x'.
Proof. exact (proj1 (@lem3303724 A s x' x h1)). Qed.
Lemma lem3304170 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : term153 A s x'.
Proof. exact (fun h0 : term12 A s x' => @lem3304169 A s x' x h1). Qed.
Lemma lem3304172 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304173 {A : Type'} (s : A -> Prop) (x' : A) : (term153 A s x') = (s x').
Proof. exact (@lem3304172 (s x')). Qed.
Lemma lem3304174 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3304173 A s x') (@lem3304170 A s x' x h1)). Qed.
Lemma lem3304177 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3304179 {A : Type'} (s : A -> Prop) (x' : A) : (term12 A s x') = (term155 A s x').
Proof. exact (@lem3304177 (s x')). Qed.
Lemma lem3304182 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term155 A s x'.
Proof. exact (EQ_MP (@lem3304179 A s x') (@lem3303901 A s x' h1)). Qed.
Lemma lem3304185 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (@lem3304182 A s x' h1 (@lem3304174 A s x' x h2)). Qed.
Lemma lem3304186 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : term156.
Proof. exact (fun h0 : ~ False => @lem3304185 A s x' x h1 h2). Qed.
Lemma lem3304188 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304189 : term156 = False.
Proof. exact (@lem3304188 False). Qed.
Lemma lem3304190 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304189) (@lem3304186 A s x' x h1 h2)). Qed.
Lemma lem3304192 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3304193 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term153 A s x'.
Proof. exact (fun h0 : term12 A s x' => @lem3304192 A s x' h1). Qed.
Lemma lem3304195 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304196 {A : Type'} (s : A -> Prop) (x' : A) : (term153 A s x') = (s x').
Proof. exact (@lem3304195 (s x')). Qed.
Lemma lem3304197 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3304196 A s x') (@lem3304193 A s x' h1)). Qed.
Lemma lem3304200 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3304202 {A : Type'} (s : A -> Prop) (x' : A) : (term12 A s x') = (term155 A s x').
Proof. exact (@lem3304200 (s x')). Qed.
Lemma lem3304205 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') : term155 A s x'.
Proof. exact (EQ_MP (@lem3304202 A s x') (@lem3303909 A s x' h1)). Qed.
Lemma lem3304208 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (@lem3304205 A s x' h1 (@lem3304197 A s x' h2)). Qed.
Lemma lem3304209 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : term156.
Proof. exact (fun h0 : ~ False => @lem3304208 A s x' h1 h2). Qed.
Lemma lem3304211 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304212 : term156 = False.
Proof. exact (@lem3304211 False). Qed.
Lemma lem3304213 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304212) (@lem3304209 A s x' h1 h2)). Qed.
Lemma lem3304229 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3304230 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3304229 A x). Qed.
Lemma lem3304231 {A : Type'} (x : A) : term157 A x.
Proof. exact (fun h0 : term146 A x => @lem3304230 A x). Qed.
Lemma lem3304233 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304234 {A : Type'} (x : A) : (term157 A x) = (x = x).
Proof. exact (@lem3304233 (x = x)). Qed.
Lemma lem3304235 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3304234 A x) (@lem3304231 A x)). Qed.
Lemma lem3304237 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : s x.
Proof. exact (proj1 (@lem3303707 A x s h1)). Qed.
Lemma lem3304238 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term153 A s x.
Proof. exact (fun h0 : term12 A s x => @lem3304237 A x s h1). Qed.
Lemma lem3304240 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304241 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (s x).
Proof. exact (@lem3304240 (s x)). Qed.
Lemma lem3304242 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : s x.
Proof. exact (EQ_MP (@lem3304241 A s x) (@lem3304238 A x s h1)). Qed.
Lemma lem3304244 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3304245 {A : Type'} (x : A) (s : A -> Prop) (_33906 : A) : (term142 A x s _33906) = (term161 A x s _33906).
Proof. exact (@lem3304244 (_33906 = x) (s _33906)). Qed.
Lemma lem3304247 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3304248 {A : Type'} (x : A) (s : A -> Prop) (_33906 : A) : (term161 A x s _33906) = (term162 A x s _33906).
Proof. exact (@lem3304247 (term163 A x s _33906)). Qed.
Lemma lem3304249 {A : Type'} (x : A) (s : A -> Prop) (_33906 : A) : (term142 A x s _33906) = (term162 A x s _33906).
Proof. exact (TRANS (@lem3304245 A x s _33906) (@lem3304248 A x s _33906)). Qed.
Lemma lem3304251 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term164 A s x.
Proof. exact (conj (@lem3304235 A x) (@lem3304242 A x s h1)). Qed.
Lemma lem3304253 {A : Type'} (_33906 : A) (x : A) (s : A -> Prop) (h1 : term102 A x s) : term162 A x s _33906.
Proof. exact (EQ_MP (@lem3304249 A x s _33906) (@lem3303937 A _33906 x s h1)). Qed.
Lemma lem3304254 {A : Type'} (_33906 : A) (x : A) (s : A -> Prop) (h1 : term102 A x s) : term162 A x s _33906.
Proof. exact (@lem3304253 A _33906 x s h1). Qed.
Lemma lem3304255 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term165 A s x.
Proof. exact (@lem3304254 A x x s h1). Qed.
Lemma lem3304258 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : False.
Proof. exact (@lem3304255 A x s h1 (@lem3304251 A x s h1)). Qed.
Lemma lem3304259 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : term156.
Proof. exact (fun h0 : ~ False => @lem3304258 A x s h1). Qed.
Lemma lem3304261 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3304262 : term156 = False.
Proof. exact (@lem3304261 False). Qed.
Lemma lem3304263 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A x s) : False.
Proof. exact (EQ_MP (@lem3304262) (@lem3304259 A x s h1)). Qed.
Lemma lem3304264 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304152) (@lem3304149 A s x' x h1 h2 h3)). Qed.
Lemma lem3304265 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304129) (@lem3304126 A s x' x h1 h2)). Qed.
Lemma lem3304266 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3304213 A s x' h1 h2) (fun h3 : False => @lem3303911 A s x' h2)). Qed.
Lemma lem3304267 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304266 A s x' h1 h2) (@lem3303911 A s x' h2)). Qed.
Lemma lem3304268 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304267 A s x' h1 h2) (fun h3 : False => @lem3303909 A s x' h1)). Qed.
Lemma lem3304269 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304268 A s x' h1 h2) (@lem3303909 A s x' h1)). Qed.
Lemma lem3304270 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304190 A s x' x h1 h2) (fun h3 : False => @lem3303901 A s x' h1)). Qed.
Lemma lem3304271 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304270 A s x' x h1 h2) (@lem3303901 A s x' h1)). Qed.
Lemma lem3304272 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3304264 A s x' x h1 h2 h3) (fun h4 : False => @lem3303897 A s x' h1)). Qed.
Lemma lem3304273 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304272 A s x' x h1 h2 h3) (@lem3303897 A s x' h1)). Qed.
Lemma lem3304274 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3304273 A s x' x h1 h2 h3) (fun h4 : False => @lem3303895 A x' x h3)). Qed.
Lemma lem3304275 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304274 A s x' x h1 h2 h3) (@lem3303895 A x' x h3)). Qed.
Lemma lem3304276 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3304265 A s x' x h1 h2) (fun h3 : False => @lem3303887 A x' x h2)). Qed.
Lemma lem3304277 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304276 A s x' x h1 h2) (@lem3303887 A x' x h2)). Qed.
Lemma lem3304278 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3304092 A s x' h1 h2) (fun h3 : False => @lem3303883 A s x' h2)). Qed.
Lemma lem3304279 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304278 A s x' h1 h2) (@lem3303883 A s x' h2)). Qed.
Lemma lem3304280 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304279 A s x' h1 h2) (fun h3 : False => @lem3303881 A s x' h1)). Qed.
Lemma lem3304281 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304280 A s x' h1 h2) (@lem3303881 A s x' h1)). Qed.
Lemma lem3304282 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304069 A s x' x h1 h2) (fun h3 : False => @lem3303873 A s x' h1)). Qed.
Lemma lem3304283 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304282 A s x' x h1 h2) (@lem3303873 A s x' h1)). Qed.
Lemma lem3304284 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3304269 A s x' h1 h2) (fun h3 : False => @lem3303815 A s x' h2)). Qed.
Lemma lem3304285 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304284 A s x' h1 h2) (@lem3303815 A s x' h2)). Qed.
Lemma lem3304286 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304285 A s x' h1 h2) (fun h3 : False => @lem3303811 A s x' h1)). Qed.
Lemma lem3304287 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304286 A s x' h1 h2) (@lem3303811 A s x' h1)). Qed.
Lemma lem3304288 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304271 A s x' x h1 h2) (fun h3 : False => @lem3303795 A s x' h1)). Qed.
Lemma lem3304289 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304288 A s x' x h1 h2) (@lem3303795 A s x' h1)). Qed.
Lemma lem3304290 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3304275 A s x' x h1 h2 h3) (fun h4 : False => @lem3303787 A s x' h1)). Qed.
Lemma lem3304291 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304290 A s x' x h1 h2 h3) (@lem3303787 A s x' h1)). Qed.
Lemma lem3304292 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3304291 A s x' x h1 h2 h3) (fun h4 : False => @lem3303783 A x' x h3)). Qed.
Lemma lem3304293 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304292 A s x' x h1 h2 h3) (@lem3303783 A x' x h3)). Qed.
Lemma lem3304294 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3304277 A s x' x h1 h2) (fun h3 : False => @lem3303767 A x' x h2)). Qed.
Lemma lem3304295 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304294 A s x' x h1 h2) (@lem3303767 A x' x h2)). Qed.
Lemma lem3304296 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3304281 A s x' h1 h2) (fun h3 : False => @lem3303759 A s x' h2)). Qed.
Lemma lem3304297 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304296 A s x' h1 h2) (@lem3303759 A s x' h2)). Qed.
Lemma lem3304298 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304297 A s x' h1 h2) (fun h3 : False => @lem3303755 A s x' h1)). Qed.
Lemma lem3304299 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304298 A s x' h1 h2) (@lem3303755 A s x' h1)). Qed.
Lemma lem3304300 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304283 A s x' x h1 h2) (fun h3 : False => @lem3303739 A s x' h1)). Qed.
Lemma lem3304301 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304300 A s x' x h1 h2) (@lem3303739 A s x' h1)). Qed.
Lemma lem3304302 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3304287 A s x' h1 h2) (fun h3 : False => @lem3303815 A s x' h2)). Qed.
Lemma lem3304303 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304302 A s x' h1 h2) (@lem3303815 A s x' h2)). Qed.
Lemma lem3304304 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304303 A s x' h1 h2) (fun h3 : False => @lem3303811 A s x' h1)). Qed.
Lemma lem3304305 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304304 A s x' h1 h2) (@lem3303811 A s x' h1)). Qed.
Lemma lem3304306 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304289 A s x' x h1 h2) (fun h3 : False => @lem3303795 A s x' h1)). Qed.
Lemma lem3304307 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304306 A s x' x h1 h2) (@lem3303795 A s x' h1)). Qed.
Lemma lem3304308 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3304293 A s x' x h1 h2 h3) (fun h4 : False => @lem3303787 A s x' h1)). Qed.
Lemma lem3304309 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304308 A s x' x h1 h2 h3) (@lem3303787 A s x' h1)). Qed.
Lemma lem3304310 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3304309 A s x' x h1 h2 h3) (fun h4 : False => @lem3303783 A x' x h3)). Qed.
Lemma lem3304311 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x') (h2 : term114 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304310 A s x' x h1 h2 h3) (@lem3303783 A x' x h3)). Qed.
Lemma lem3304312 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3304295 A s x' x h1 h2) (fun h3 : False => @lem3303767 A x' x h2)). Qed.
Lemma lem3304313 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term19 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3304312 A s x' x h1 h2) (@lem3303767 A x' x h2)). Qed.
Lemma lem3304314 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3304299 A s x' h1 h2) (fun h3 : False => @lem3303759 A s x' h2)). Qed.
Lemma lem3304315 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304314 A s x' h1 h2) (@lem3303759 A s x' h2)). Qed.
Lemma lem3304316 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304315 A s x' h1 h2) (fun h3 : False => @lem3303755 A s x' h1)). Qed.
Lemma lem3304317 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3304316 A s x' h1 h2) (@lem3303755 A s x' h1)). Qed.
Lemma lem3304318 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : (term12 A s x') = False.
Proof. exact (prop_ext (fun h3 : term12 A s x' => @lem3304301 A s x' x h1 h2) (fun h3 : False => @lem3303739 A s x' h1)). Qed.
Lemma lem3304319 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term12 A s x') (h2 : term19 A s x' x) : False.
Proof. exact (EQ_MP (@lem3304318 A s x' x h1 h2) (@lem3303739 A s x' h1)). Qed.
Lemma lem3304320 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : term114 A x s x') : False.
Proof. exact (or_elim (@lem3303711 A x s x' h2) (fun h0 : term19 A s x' x => @lem3304307 A s x' x h1 h0) (fun h0 : s x' => @lem3304305 A s x' h1 h0)). Qed.
Lemma lem3304321 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term114 A x s x') (h2 : x' = x) : False.
Proof. exact (or_elim (@lem3303711 A x s x' h1) (fun h0 : term19 A s x' x => @lem3304313 A s x' x h0 h2) (fun h0 : s x' => @lem3304311 A s x' x h0 h1 h2)). Qed.
Lemma lem3304322 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term12 A s x') (h2 : term114 A x s x') : False.
Proof. exact (or_elim (@lem3303711 A x s x' h2) (fun h0 : term19 A s x' x => @lem3304319 A s x' x h1 h0) (fun h0 : s x' => @lem3304317 A s x' h1 h0)). Qed.
Lemma lem3304323 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term114 A x s x') (h2 : term43 A s x' x) : False.
Proof. exact (or_elim (@lem3303712 A s x' x h2) (fun h0 : term12 A s x' => @lem3304322 A x s x' h0 h1) (fun h0 : x' = x => @lem3304321 A s x' x h1 h0)). Qed.
Lemma lem3304324 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term114 A x s x') : False.
Proof. exact (or_elim (@lem3303710 A x s x' h1) (fun h0 : term43 A s x' x => @lem3304323 A s x' x h1 h0) (fun h0 : term12 A s x' => @lem3304320 A x s x' h0 h1)). Qed.
Lemma lem3304325 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term133 A x' x s) : False.
Proof. exact (or_elim (@lem3303705 A x' x s h1) (fun h0 : term114 A x s x' => @lem3304324 A x s x' h0) (fun h0 : term102 A x s => @lem3304263 A x s h0)). Qed.
Lemma lem3304326 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term133 A x' x s) : (term133 A x' x s) = False.
Proof. exact (prop_ext (fun h2 : term133 A x' x s => @lem3304325 A x' x s h1) (fun h2 : False => @lem3303705 A x' x s h1)). Qed.
Lemma lem3304327 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term133 A x' x s) : False.
Proof. exact (EQ_MP (@lem3304326 A x' x s h1) (@lem3303705 A x' x s h1)). Qed.
Lemma lem3304328 {A : Type'} (x : A) (s : A -> Prop) (h1 : term38 A x s) : False.
Proof. exact (ex_elim (@lem3303594 A x s h1) (fun x' : A => fun h0 : term135 A x s x' => @lem3304327 A x' x s h0)). Qed.
Lemma lem3304329 {A : Type'} (x : A) (s : A -> Prop) (h1 : term38 A x s) : (term38 A x s) = False.
Proof. exact (prop_ext (fun h2 : term38 A x s => @lem3304328 A x s h1) (fun h2 : False => @lem3303317 A x s h1)). Qed.
Lemma lem3304330 {A : Type'} (x : A) (s : A -> Prop) (h1 : term38 A x s) : False.
Proof. exact (EQ_MP (@lem3304329 A x s h1) (@lem3303317 A x s h1)). Qed.
Lemma lem3304331 {A : Type'} (x : A) (s : A -> Prop) : term37 A x s.
Proof. exact (fun h0 : term38 A x s => @lem3304330 A x s h0). Qed.
Lemma lem3304332 {A : Type'} (x : A) (s : A -> Prop) : (term12 A s x) = (term24 A x s).
Proof. exact (EQ_MP (@lem3303316 A x s) (@lem3304331 A x s)). Qed.
Lemma lem3304337 {A : Type'} (x : A) : term26 A x.
Proof. exact (fun s : A -> Prop => @lem3304332 A x s). Qed.
Lemma lem3304342 {A : Type'} : term28 A.
Proof. exact (fun x : A => @lem3304337 A x). Qed.
Lemma lem3304343 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem3303312 A) (@lem3304342 A)). Qed.
Lemma lem3304345 {A : Type'} : term30 A.
Proof. exact (@lem3303237 A (@lem3304343 A)). Qed.
Lemma lem3304346 {A : Type'} (h1 : term31 A) : False.
Proof. exact (@lem3304345 A (@lem3303221 A h1)). Qed.
Lemma lem3304347 {A : Type'} (h1 : term31 A) : (term31 A) = False.
Proof. exact (prop_ext (fun h2 : term31 A => @lem3304346 A h1) (fun h2 : False => @lem3303221 A h1)). Qed.
Lemma lem3304348 {A : Type'} (h1 : term31 A) : False.
Proof. exact (EQ_MP (@lem3304347 A h1) (@lem3303221 A h1)). Qed.
Lemma lem3304349 {A : Type'} : term30 A.
Proof. exact (fun h0 : term31 A => @lem3304348 A h0). Qed.
Lemma lem3304350 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem3303220 A) (@lem3304349 A)). Qed.
Lemma lem3304351 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem3303216 A) (@lem3304350 A)). Qed.
Lemma lem3304352 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3303139 A) (@lem3304351 A)). Qed.
